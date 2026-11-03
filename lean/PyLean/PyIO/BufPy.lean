import PyLean.PyIO.BufRaw

/-!
`Lib/_pyio.py`: `_BufferedIOMixin` (:765-873), `BufferedReader` (:1038-1236),
`BufferedWriter` (:1238-1340), `BufferedRandom` (:1416-1487) over the scripted,
re-entrant `Raw` (`kind` 0, 1, 2), with `RawIOBase.read`/`readall` of the raw
(:610-638).

The locks are `_thread.allocate_lock()` (:1060, :1256), which is not re-entrant:
a call that takes a lock this thread already holds blocks forever. That is
`hangErr`, and `hung` records it (the harness swaps `_pyio.Lock` for one that
raises instead of blocking). After `detach`, `self.raw` is `None`, so every
`self.raw.attr` raises `AttributeError`.
-/

namespace PyLean.PyIO

open PyLean

structure BufP where
  raw : Raw
  detached : Bool
  kind : Nat
  size : Nat
  readBuf : List Nat
  readPos : Nat
  writeBuf : List Nat
  /-- `_read_lock` is held. -/
  rl : Bool
  /-- `_write_lock` is held. -/
  wl : Bool
  /-- A lock was taken twice: the thread hangs. -/
  hung : Bool
  deriving Repr, DecidableEq, Inhabited

abbrev PH := BfOp → SM BufP Val

/-- A Python method body: state and exceptions, plus the handler for re-entry. -/
def PM (α : Type) := PH → BufP → BufP × Py α

instance : Monad PM where
  pure a := fun _ s => (s, .ok a)
  bind m f := fun R s =>
    match m R s with
    | (s', .ok a) => f a R s'
    | (s', .error e) => (s', .error e)

namespace BP2

def get : PM BufP := fun _ s => (s, .ok s)
def put (s : BufP) : PM Unit := fun _ _ => (s, .ok ())
def mod (f : BufP → BufP) : PM Unit := fun _ s => (f s, .ok ())
def thr {α : Type} (e : PyExc) : PM α := fun _ s => (s, .error e)
def attempt {α : Type} (m : PM α) : PM (Py α) := fun R s => let (s', r) := m R s; (s', .ok r)
def ofPy {α : Type} (r : Py α) : PM α := fun _ s => (s, r)

def noneAttr (a : String) : PyExc := .named "AttributeError" s!"'NoneType' object has no attribute '{a}'"

/-- The start of a callback into the raw stream (see `BC2.callback`). -/
def callback (c : RCall) : PM Unit := fun R s =>
  let (r, h) := s.raw.enter c
  let s := { s with raw := r }
  match h with
  | none => (s, .ok ())
  | some op =>
    let (s, v) := R op s
    let s := { s with raw := s.raw.note v }
    if s.hung then (s, .error hangErr) else (s, .ok ())

/-- `self.raw.attr(...)`: `self.raw` is `None` after `detach`. -/
def onRaw {α : Type} (attr : String) (c : RCall) (f : Raw → Raw × α) : PM α := do
  let s ← get
  if s.detached then thr (noneAttr attr)
  callback c
  let s ← get
  let (r, a) := f s.raw
  put { s with raw := r }
  pure a

/-- A call on the raw object a caller already holds (not through `self.raw`). -/
def onRawObj {α : Type} (c : RCall) (f : Raw → Raw × α) : PM α := do
  callback c
  let s ← get
  let (r, a) := f s.raw
  put { s with raw := r }
  pure a

/-- `self.raw.readable()`, `writable()`, `seekable()`: a callback answering any object. -/
def inquiry (attr : String) (c : RCall) (flag : Raw → Bool) : PM QAns := do
  let r ← onRaw attr c (fun r => r.inquire (flag r))
  ofPy r

/-- The same call on the `raw` argument of a constructor. -/
def inquiryObj (c : RCall) (flag : Raw → Bool) : PM QAns := do
  let r ← onRawObj c (fun r => r.inquire (flag r))
  ofPy r

/-- `with self._read_lock:` / `with self._write_lock:` around `m`. -/
def withLock {α : Type} (w : Bool) (m : PM α) : PM α := fun R s =>
  if (if w then s.wl else s.rl) then ({ s with hung := true }, .error hangErr) else
  let (s2, r) := m R (if w then { s with wl := true } else { s with rl := true })
  ((if w then { s2 with wl := false } else { s2 with rl := false }), r)

/-- `_BufferedIOMixin.closed`, _pyio.py:838-840: `self.raw.closed`. -/
def closed : PM Bool := do
  let r ← onRaw "closed" .closed Raw.closedAttr
  ofPy r

/-- `IOBase._checkClosed`, _pyio.py:473-478. -/
def checkClosed (msg : String) : PM Unit := do
  let c ← closed
  if c then thr (.valueError msg)

/-- `BufferedReader._reset_read_buf`, _pyio.py:1065-1067. -/
def resetRead : PM Unit := mod fun s => { s with readBuf := [], readPos := 0 }

/-- `RawIOBase.read(n)` for `n >= 0`, _pyio.py:610-627: the bytearray starts zeroed. -/
def rawRead (n : Nat) (viaSelf : Bool := true) : PM (Option (List Nat)) := do
  -- `self.raw.read` is looked up first; then `bytearray(size.__index__())` (:620),
  -- and `buffer_size` can be huge after `__init__(raw, 2**48)`, which _pyio accepts
  if viaSelf then
    let s ← get
    if s.detached then thr (noneAttr "read")
  if n ≥ memLimit then thr memoryError
  let res ← if viaSelf then onRaw "read" (.readinto n) (fun r => r.readinto n)
    else onRawObj (.readinto n) (fun r => r.readinto n)
  match res with
  | .exc e _ _ => thr e
  | .none => pure none
  | .data d => pure (some d)
  | .count _ => pure (some [])
  | .wrong => thr (strLtErr "<")
  | .bad v =>
    if v < 0 ∨ v > n then thr (.valueError s!"readinto returned {v} outside buffer size {n}")
    else pure (some (List.replicate v.toNat 0))

/-- `RawIOBase.readall`, _pyio.py:629-638: its `self.read` is the raw's own. -/
def rawReadall : Nat → List Nat → PM (Option (List Nat))
  | 0, _ => thr .modelFuel
  | fuel + 1, res => do
    let r ← rawRead 131072 false
    match r with
    | none => if res ≠ [] then pure (some res) else pure none
    | some d => if d = [] then pure (some res) else rawReadall fuel (res ++ d)

def tail (s : BufP) : List Nat := s.readBuf.drop s.readPos

def fuelOf (s : BufP) : Nat :=
  s.raw.rs.length + s.raw.ws.length + s.raw.hooks.length + s.raw.data.length + s.writeBuf.length + 4

/-- The `while avail < n` loop of `_read_unlocked`, _pyio.py:1119-1125:
`(chunks, avail, nodata)`, with `nodata = none` for `None`. -/
def readMore (n : Int) (wanted : Nat) : Nat → List Nat → Int → PM (List Nat × Int × Option (List Nat))
  | 0, _, _ => thr .modelFuel
  | fuel + 1, chunks, avail => do
    if avail < n then
      let c ← rawRead wanted
      match c with
      | none => pure (chunks, avail, none)
      | some d =>
        if d = [] then pure (chunks, avail, some [])
        else readMore n wanted fuel (chunks ++ d) (avail + d.length)
    else pure (chunks, avail, some [])

/-- `_read_unlocked`, _pyio.py:1082-1132 (`n = -1` for "all"): `none` is `None`. -/
def readUnlocked (n : Int) : PM (Option (List Nat)) := do
  let s ← get
  let t := tail s
  if n = -1 then
    resetRead
    let s' ← get
    -- `hasattr(self.raw, 'readall')` is False for `None`; the loop then reads `self.raw.read`
    if s'.detached then thr (noneAttr "read")
    let chunk ← rawReadall (fuelOf s') []
    match chunk with
    | none => pure (if t ≠ [] then some t else none)
    | some c => pure (some (t ++ c))
  else
    let avail : Int := t.length
    if n ≤ avail then
      mod fun s => { s with readPos := s.readPos + n.toNat }
      pure (some (t.take n.toNat))
    else
      let wanted := max s.size n.toNat
      let (out, avail, nodata) ← readMore n wanted (fuelOf s) t avail
      let k := min n avail
      mod fun s => { s with readBuf := out.drop k.toNat, readPos := 0 }
      if out ≠ [] then pure (some (out.take k.toNat)) else pure nodata

/-- `_peek_unlocked`, _pyio.py:1145-1154. -/
def peekUnlocked (n : Nat) : PM (List Nat) := do
  let s ← get
  let want := min n s.size
  let have' := (tail s).length
  if have' < want ∨ have' = 0 then
    let cur ← rawRead (s.size - have')
    match cur with
    | some d =>
      if d ≠ [] then mod fun s => { s with readBuf := tail s ++ d, readPos := 0 }
    | none => pure ()
  let s ← get
  pure (tail s)

/-- The loop of `BufferedWriter._flush_unlocked`, _pyio.py:1303-1315. -/
def flushLoop : Nat → PM Unit
  | 0 => thr .modelFuel
  | fuel + 1 => do
    let s ← get
    if s.writeBuf = [] then pure () else
    let res ← onRaw "write" (.write s.writeBuf) (fun r => r.write s.writeBuf)
    match res with
    | .exc e _ mro =>
      -- `except BlockingIOError:` matches subclasses too
      if mro.contains "BlockingIOError" then
        thr (.named "RuntimeError" "self.raw should implement RawIOBase: it should not raise BlockingIOError")
      else thr e
    | .none => thr (.named "BlockingIOError" "write could not complete without blocking|0")
    | .data _ => flushLoop fuel
    | .wrong => thr (strLtErr ">")
    | .bad v =>
      let s ← get
      if v > s.writeBuf.length ∨ v < 0 then thr (osError "write() returned incorrect number of bytes")
      mod fun s => { s with writeBuf := s.writeBuf.drop v.toNat }
      flushLoop fuel
    | .count n =>
      let s ← get
      if n > s.writeBuf.length then thr (osError "write() returned incorrect number of bytes")
      mod fun s => { s with writeBuf := s.writeBuf.drop n }
      flushLoop fuel

/-- `BufferedWriter._flush_unlocked`, _pyio.py:1300-1315: `closed` is read once. -/
def flushUnlocked (fuel : Nat) : PM Unit := do
  let c ← closed
  if c then thr (.valueError "flush on closed file")
  flushLoop fuel

/-- `flush()`: `BufferedWriter.flush` (:1296-1298) or the mixin's (:808-811). -/
def flush : PM Val := do
  let s ← get
  if s.kind = 0 then
    let c ← closed
    if c then thr (.valueError "flush on closed file")
    let r ← onRaw "flush" .flush Raw.flush
    -- the mixin drops what `raw.flush()` returns
    let _ ← ofPy r
    pure .none
  else
    withLock true (do let s ← get; flushUnlocked (fuelOf s))
    pure .none

def flushIfRandom : PM Unit := do
  let s ← get
  if s.kind = 2 then let _ ← flush

def optBytes (r : Option (List Nat)) : Val := match r with
  | some d => .bytes d
  | none => .none

/-- `BufferedReader.read`, _pyio.py:1069-1080; `BufferedRandom.read`, :1459-1463. -/
def read (size : Option Int) : PM Val := do
  flushIfRandom
  let n := size.getD (-1)
  if n < -1 then thr (.valueError "invalid number of bytes to read")
  let r ← withLock false (readUnlocked n)
  pure (optBytes r)

/-- `BufferedReader.read1`, _pyio.py:1156-1168; `BufferedRandom.read1`, :1473-1475. -/
def read1 (size : Int) : PM Val := do
  flushIfRandom
  checkClosed "read of closed file"
  let s ← get
  let n : Int := if size < 0 then s.size else size
  if n = 0 then pure (.bytes []) else
  withLock false do
    let _ ← peekUnlocked 1
    let s ← get
    let r ← readUnlocked (min n (tail s).length)
    pure (optBytes r)

/-- `BufferedReader.peek`, _pyio.py:1134-1143; `BufferedRandom.peek`, :1469-1471. -/
def peek (n : Int) : PM Val := do
  flushIfRandom
  checkClosed "peek of closed file"
  let r ← withLock false (peekUnlocked n.toNat)
  pure (.bytes r)

/-- The loop of `_readinto`, _pyio.py:1191-1219, over `written` and `out`. -/
def readintoLoop (len : Nat) (one : Bool) : Nat → Int → List Nat → PM (Int × List Nat)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, written, out => do
    if written < len then
      let s ← get
      -- `avail` is bounded by `len(buf)`, not by the space left, so the slice
      -- `buf[written:written+avail]` can be shorter than the bytes assigned to it
      let avail := min (tail s).length len
      if avail > len - written.toNat then
        thr (.valueError "memoryview assignment: lvalue and rvalue have different structures")
      let cp := (tail s).take avail
      let (written, out) := if avail > 0 then (written + cp.length, out ++ cp) else (written, out)
      if avail > 0 then mod fun s => { s with readPos := s.readPos + avail }
      if avail > 0 ∧ written = len then pure (written, out) else
      let s ← get
      if (len : Int) - written > s.size then
        let k := len - written.toNat
        let res ← onRaw "readinto" (.readinto k) (fun r => r.readinto k)
        match res with
        | .exc e _ _ => thr e
        | .none | .count 0 | .data [] => pure (written, out)
        | .count _ => pure (written, out)
        | .wrong => thr (.typeError "unsupported operand type(s) for +=: 'int' and 'str'")
        | .bad v =>
          -- an int answer that stored nothing: those bytes of `buf` stay `0xff`
          -- (the harness never answers a negative int here, see the difftest)
          if v = 0 then pure (written, out) else
          let out := if v > 0 ∧ written + v ≤ len then out ++ List.replicate v.toNat 255 else out
          let written := written + v
          if one ∧ written ≠ 0 then pure (written, out) else readintoLoop len one fuel written out
        | .data d =>
          let written := written + d.length
          let out := out ++ d
          if one ∧ written ≠ 0 then pure (written, out) else readintoLoop len one fuel written out
      else
        if !(one && decide (written ≠ 0)) then
          let p ← peekUnlocked 1
          if p = [] then pure (written, out)
          else if one ∧ written ≠ 0 then pure (written, out)
          else readintoLoop len one fuel written out
        else if one ∧ written ≠ 0 then pure (written, out)
        else readintoLoop len one fuel written out
    else pure (written, out)

/-- `_readinto`, _pyio.py:1175-1221, with a buffer of `len` bytes `0xff`;
`BufferedRandom.readinto(1)` flushes first (:1465-1467, :1477-1479). -/
def readinto (len : Nat) (one : Bool) : PM Val := do
  flushIfRandom
  checkClosed "readinto of closed file"
  if len = 0 then pure (.list [.int 0, .bytes []]) else
  let s ← get
  let (w, out) ← withLock false (readintoLoop len one (fuelOf s + len) 0 [])
  pure (.list [.int w, .bytes (out ++ List.replicate (len - out.length) 255)])

/-- `nreadahead()` with `peek`, _pyio.py:525-532, with `len` bytes already in `res`. -/
def nreadahead (size : Int) (len : Nat) (ra : List Nat) : Nat :=
  if ra = [] then 1
  else
    let m := match findIdx? ra 10 with
      | some i => i + 1
      | none => ra.length
    if size ≥ 0 then min m (size - len).toNat else m

/-- `self.peek(1)` then `self.read(n)` in the loop of `IOBase.readline`,
_pyio.py:525-532, :546-553. -/
def readlineLoop (size : Int) : Nat → List Nat → PM (List Nat)
  | 0, _ => thr .modelFuel
  | fuel + 1, res => do
    if size < 0 ∨ (res.length : Int) < size then
      let r ← peek 1
      let ra := r.bytesOf
      let n : Nat := nreadahead size res.length ra
      let b ← read (some n)
      let b := b.bytesOf
      if b = [] then pure res else
      let res := res ++ b
      if res.getLast? = some 10 then pure res else readlineLoop size fuel res
    else pure res

def readlineRaw (size : Option Int) : PM (List Nat) := do
  let s ← get
  readlineLoop (size.getD (-1)) (fuelOf s + (tail s).length) []

/-- `self.raw.tell()`, with `pos < 0` checked by the caller. -/
def rawTellPlain : PM IRes := do
  let r ← onRaw "tell" .tell Raw.tell
  ofPy r

/-- `_BufferedIOMixin.tell`, _pyio.py:785-789. -/
def mixTell : PM Int := do
  let r ← rawTellPlain
  match r with
  | .wrong => thr (strLtErr "<")
  | .int n => if n < 0 then thr (osError "tell() returned an invalid position") else pure n

def rawSeekRaw (p w : Int) : PM IRes := do
  let r ← onRaw "seek" (.seek p w) (fun r => r.seek p w)
  ofPy r

/-- `_BufferedIOMixin.seek`, _pyio.py:779-783. -/
def mixSeek (p w : Int) : PM Int := do
  let r ← rawSeekRaw p w
  match r with
  | .wrong => thr (strLtErr "<")
  | .int n => if n < 0 then thr (osError "seek() returned an invalid position") else pure n

/-- `valid_seek_flags`, _pyio.py:21-24 on Linux: `{0, 1, 2, SEEK_HOLE, SEEK_DATA}`. -/
def validWhence (w : Int) : Bool := w == 0 || w == 1 || w == 2 || w == 3 || w == 4

/-- `BufferedReader.tell`, _pyio.py:1223-1225. -/
def tellR : PM Val := do
  let t ← mixTell
  let s ← get
  pure (.int (max (t - s.readBuf.length + s.readPos) 0))

/-- `BufferedWriter.tell`, _pyio.py:1317-1318. -/
def tellW : PM Val := do
  let t ← mixTell
  let s ← get
  pure (.int (t + s.writeBuf.length))

/-- `tell`: :1223-1225, :1317-1318, `BufferedRandom.tell` :1447-1451. -/
def tell : PM Val := do
  let s ← get
  if s.kind = 0 then tellR else if s.kind = 1 then tellW
  else if s.writeBuf ≠ [] then tellW else tellR

/-- `seek`: `BufferedReader.seek` (:1227-1236), `BufferedWriter.seek`
(:1320-1325), `BufferedRandom.seek` (:1430-1445). -/
def seek (p w : Int) : PM Val := do
  if !validWhence w then thr (.valueError "invalid whence value")
  let s ← get
  if s.kind = 0 then
    checkClosed "seek of closed file"
    withLock false do
      let s ← get
      let p := if w = 1 then p - (tail s).length else p
      let r ← mixSeek p w
      resetRead
      pure (.int r)
  else if s.kind = 1 then
    withLock true do
      let s ← get
      flushUnlocked (fuelOf s)
      let r ← mixSeek p w
      pure (.int r)
  else
    let _ ← flush
    let s ← get
    if s.readBuf ≠ [] then
      withLock false do
        let s ← get
        let _ ← rawSeekRaw ((s.readPos : Int) - s.readBuf.length) 1
    let r ← rawSeekRaw p w
    withLock false resetRead
    match r with
    | .wrong => thr (strLtErr "<")
    | .int r =>
      if r < 0 then thr (osError "seek() returned invalid position")
      pure (.int r)

def rawTruncate (p : Option Int) : PM Val := do
  let r ← onRaw "truncate" (.truncate p) (fun r => r.truncate p)
  let v ← ofPy r
  pure (.int v)

/-- `BufferedWriter.truncate`, _pyio.py:1289-1294. -/
def truncateW (p : Option Int) : PM Val :=
  withLock true do
    let s ← get
    flushUnlocked (fuelOf s)
    match p with
    | some v => rawTruncate (some v)
    | none =>
      let t ← rawTellPlain
      match t with
      | .int t => rawTruncate (some t)
      -- `self.raw.truncate('x')`: the harness raw logs a `str` as `None`, then its
      -- `n < 0` raises
      | .wrong => do
        let r ← onRaw "truncate" (.truncate none) (fun r =>
          (r, (.error (if r.closed then rawClosedErr else strLtErr "<") : Py Unit)))
        ofPy r
        pure .none

/-- `truncate`: mixin (:791-804, a reader here), `BufferedWriter.truncate`
(:1289-1294), `BufferedRandom.truncate` (:1453-1457). -/
def truncate (p : Option Int) : PM Val := do
  let s ← get
  if s.kind = 0 then
    checkClosed "I/O operation on closed file."
    thr (unsupportedOp "File or stream is not writable.")
  else if s.kind = 2 ∧ p.isNone then
    let t ← tell
    match t with
    | .int v => truncateW (some v)
    | _ => truncateW p
  else truncateW p

def rawClose : PM Unit := do
  let r ← onRaw "close" .close Raw.close
  ofPy r

/-- `close`: mixin (:813-819), `BufferedWriter.close` (:1327-1340). -/
def close : PM Val := do
  let s ← get
  if s.kind = 0 then
    if s.detached then pure .none else
    let c ← closed
    if c then pure .none else
    let fl ← attempt flush
    let c ← attempt rawClose
    match c, fl with
    | .error e, _ => thr e
    | .ok (), .error e => thr e
    | .ok (), .ok _ => pure .none
  else
    let stop ← withLock true do
      let s ← get
      if s.detached then pure true else closed
    if stop then pure .none else
    let fl ← attempt flush
    let c ← attempt (withLock true rawClose)
    match c, fl with
    | .error e, _ => thr e
    | .ok (), .error e => thr e
    | .ok (), .ok _ => pure .none

/-- `BufferedWriter.write`, _pyio.py:1261-1287 (under the write lock). -/
def writeW (b : List Nat) : PM Val :=
  withLock true do
    let c ← closed
    if c then thr (.valueError "write to closed file")
    let s ← get
    if s.writeBuf.length > s.size then flushUnlocked (fuelOf s)
    mod fun s => { s with writeBuf := s.writeBuf ++ b }
    let s ← get
    let written : Int := b.length
    if s.writeBuf.length > s.size then
      let r ← attempt (flushUnlocked (fuelOf s))
      match r with
      | .ok () => pure (.int written)
      | .error e =>
        if e.className == "BlockingIOError" then
          let s ← get
          -- the `except` only cuts back while still over size; otherwise it falls through
          if s.writeBuf.length > s.size then
            let overage : Int := (s.writeBuf.length : Int) - s.size
            mod fun s => { s with writeBuf := s.writeBuf.take s.size }
            thr (.named "BlockingIOError"
              s!"write could not complete without blocking|{written - overage}")
          else pure (.int written)
        else thr e
    else pure (.int written)

/-- `write`, with `BufferedRandom.write` (:1481-1487) first undoing read-ahead. -/
def write (b : List Nat) : PM Val := do
  let s ← get
  if s.kind = 2 ∧ s.readBuf ≠ [] then
    withLock false do
      let s ← get
      let _ ← rawSeekRaw ((s.readPos : Int) - s.readBuf.length) 1
      resetRead
  writeW b

/-- `_BufferedIOMixin.detach`, _pyio.py:821-827. -/
def detach : PM Val := do
  let s ← get
  if s.detached then thr (.valueError "raw stream already detached")
  let _ ← flush
  mod fun s => { s with detached := true }
  pure .none

/-- The constructors, _pyio.py:1049-1060, :1247-1256, :1425-1428, on the object as it
is: `__init__` may run again on one in use. -/
def init (kind : Nat) (size : Int) : PM Unit := do
  -- `raw._checkSeekable()`, _pyio.py:1426 and :430-435: `if not self.seekable()`
  if kind = 2 then
    let a ← inquiryObj .seekable Raw.canSeek
    if !a.truthy then thr (unsupportedOp "File or stream is not seekable.")
  if kind = 0 ∨ kind = 2 then
    let a ← inquiryObj .readable Raw.canRead
    if !a.truthy then thr (osError "\"raw\" argument must be readable.")
    mod fun s => { s with detached := false }
    if size ≤ 0 then thr (.valueError "invalid buffer size")
    -- :1058-1060: a new read buffer and a new `_read_lock`
    mod fun s => { s with size := size.toNat, readBuf := [], readPos := 0, rl := false }
  if kind = 1 ∨ kind = 2 then
    let a ← inquiryObj .writable Raw.canWrite
    if !a.truthy then thr (osError "\"raw\" argument must be writable.")
    mod fun s => { s with detached := false }
    if size ≤ 0 then thr (.valueError "invalid buffer size")
    -- :1254-1256: a new write buffer and a new `_write_lock`
    mod fun s => { s with size := size.toNat, writeBuf := [], wl := false }

end BP2

end PyLean.PyIO
