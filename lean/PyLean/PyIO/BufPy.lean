import PyLean.PyIO.BufRaw

/-!
`Lib/_pyio.py`: `_BufferedIOMixin` (:765-873), `BufferedReader` (:1019-1217),
`BufferedWriter` (:1219-1321), `BufferedRandom` (:1397-1468) over the scripted
`Raw` (`kind` 0, 1, 2), with `RawIOBase.read`/`readall` of the raw (:610-638).
-/

namespace PyLean.PyIO

open PyLean SM

structure BufP where
  raw : Raw
  detached : Bool
  kind : Nat
  size : Nat
  readBuf : List Nat
  readPos : Nat
  writeBuf : List Nat
  deriving Repr, DecidableEq, Inhabited

abbrev PM := SM BufP

namespace BP2

def closed (s : BufP) : Bool := s.raw.closed

/-- `IOBase._checkClosed`, _pyio.py:473-478. -/
def checkClosed (msg : String) : PM Unit := do
  let s ← SM.get
  if closed s then thr (.valueError msg)

def resetRead : PM Unit := SM.mod fun s => { s with readBuf := [], readPos := 0 }

/-- `RawIOBase.read(n)` for `n >= 0`, _pyio.py:610-627. -/
def rawRead (n : Nat) : PM (Option (List Nat)) := do
  let s ← SM.get
  let (r, res) := s.raw.readinto n
  SM.put { s with raw := r }
  match res with
  | .exc e => thr e
  | .none => pure none
  | .data d => pure (some d)
  | .count _ => pure (some [])
  | .bad v => thr (.valueError s!"readinto returned {v} outside buffer size {n}")

/-- `RawIOBase.readall`, _pyio.py:629-638. -/
def rawReadall : Nat → List Nat → PM (Option (List Nat))
  | 0, _ => thr .modelFuel
  | fuel + 1, res => do
    let r ← rawRead 131072
    match r with
    | none => if res ≠ [] then pure (some res) else pure none
    | some d => if d = [] then pure (some res) else rawReadall fuel (res ++ d)

def tail (s : BufP) : List Nat := s.readBuf.drop s.readPos

/-- The `while avail < n` loop of `_read_unlocked`, _pyio.py:1100-1106:
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

/-- `_read_unlocked`, _pyio.py:1063-1113 (`n = -1` for "all"): `none` is `None`. -/
def readUnlocked (n : Int) : PM (Option (List Nat)) := do
  let s ← SM.get
  let t := tail s
  if n = -1 then
    resetRead
    let s' ← SM.get
    let chunk ← rawReadall (s'.raw.rs.length + s'.raw.data.length + 2) []
    match chunk with
    | none => pure (if t ≠ [] then some t else none)
    | some c => pure (some (t ++ c))
  else
    let avail : Int := t.length
    if n ≤ avail then
      SM.mod fun s => { s with readPos := s.readPos + n.toNat }
      pure (some (t.take n.toNat))
    else
      let wanted := max s.size n.toNat
      let (out, avail, nodata) ← readMore n wanted (s.raw.rs.length + s.raw.data.length + 2) t avail
      let k := min n avail
      SM.mod fun s => { s with readBuf := out.drop k.toNat, readPos := 0 }
      if out ≠ [] then pure (some (out.take k.toNat)) else pure nodata

/-- `_peek_unlocked`, _pyio.py:1112-1122. -/
def peekUnlocked (n : Nat) : PM (List Nat) := do
  let s ← SM.get
  let want := min n s.size
  let have' := (tail s).length
  if have' < want ∨ have' = 0 then
    let cur ← rawRead (s.size - have')
    match cur with
    | some d =>
      if d ≠ [] then SM.mod fun s => { s with readBuf := tail s ++ d, readPos := 0 }
    | none => pure ()
  let s ← SM.get
  pure (tail s)

/-- `BufferedWriter._flush_unlocked`, _pyio.py:1281-1296. -/
def flushUnlocked : Nat → PM Unit
  | 0 => thr .modelFuel
  | fuel + 1 => do
    let s ← SM.get
    if closed s then thr (.valueError "flush on closed file")
    if s.writeBuf = [] then pure () else
    let (r, res) := s.raw.write s.writeBuf
    SM.put { s with raw := r }
    match res with
    | .exc e =>
      if e.className == "BlockingIOError" then
        thr (.named "RuntimeError" "self.raw should implement RawIOBase: it should not raise BlockingIOError")
      else thr e
    | .none => thr (.named "BlockingIOError" "write could not complete without blocking|0")
    | .data _ => pure ()
    | .bad _ => thr (osError "write() returned incorrect number of bytes")
    | .count n =>
      SM.mod fun s => { s with writeBuf := s.writeBuf.drop n }
      flushUnlocked fuel

def fuelF (s : BufP) : Nat := s.raw.ws.length + s.writeBuf.length + 3

/-- `flush()`: `BufferedWriter.flush` (:1277-1279) or the mixin's (:808-811). -/
def flush : PM Val := do
  let s ← SM.get
  if s.kind = 0 then
    if closed s then thr (.valueError "flush on closed file")
    let (r, res) := s.raw.flush
    SM.put { s with raw := r }
    match res with
    | .error e => thr e
    | .ok () => pure .none
  else
    flushUnlocked (fuelF s)
    pure .none

def flushIfRandom : PM Unit := do
  let s ← SM.get
  if s.kind = 2 then let _ ← flush

/-- `BufferedReader.read`, _pyio.py:1050-1061; `BufferedRandom.read`, :1440-1444. -/
def read (size : Option Int) : PM Val := do
  flushIfRandom
  let n := size.getD (-1)
  if n < -1 then thr (.valueError "invalid number of bytes to read")
  let r ← readUnlocked n
  pure (match r with
    | some d => .bytes d
    | none => .none)

/-- `BufferedReader.read1`, _pyio.py:1137-1149. -/
def read1 (size : Int) : PM Val := do
  flushIfRandom
  checkClosed "read of closed file"
  let s ← SM.get
  let n : Int := if size < 0 then s.size else size
  if n = 0 then pure (.bytes []) else
  let _ ← peekUnlocked 1
  let s ← SM.get
  let r ← readUnlocked (min n (tail s).length)
  pure (match r with
    | some d => .bytes d
    | none => .none)

/-- `BufferedReader.peek`, _pyio.py:1115-1124. -/
def peek (n : Int) : PM Val := do
  flushIfRandom
  checkClosed "peek of closed file"
  let r ← peekUnlocked n.toNat
  pure (.bytes r)

/-- The loop of `_readinto`, _pyio.py:1172-1200, over `written` and `out`. -/
def readintoLoop (len : Nat) (one : Bool) : Nat → Int → List Nat → PM (Int × List Nat)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, written, out => do
    if written < len then
      let s ← SM.get
      -- `avail` is bounded by `len(buf)`, not by the space left, so the slice
      -- `buf[written:written+avail]` can be shorter than the bytes assigned to it
      let avail := min (tail s).length len
      if avail > len - written.toNat then
        thr (.valueError "memoryview assignment: lvalue and rvalue have different structures")
      let cp := (tail s).take avail
      let (written, out) := if avail > 0 then (written + cp.length, out ++ cp) else (written, out)
      if avail > 0 then SM.mod fun s => { s with readPos := s.readPos + avail }
      if avail > 0 ∧ written = len then pure (written, out) else
      let s ← SM.get
      if (len : Int) - written > s.size then
        let (r, res) := s.raw.readinto (len - written.toNat)
        SM.put { s with raw := r }
        match res with
        | .exc e => thr e
        | .none | .count 0 | .data [] => pure (written, out)
        | .count _ => pure (written, out)
        | .bad v =>
          if v = 0 then pure (written, out) else
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

/-- `_readinto`, _pyio.py:1156-1202, with a buffer of `len` bytes `0xff`;
`BufferedRandom.readinto(1)` flushes first (:1446-1448, :1458-1460). -/
def readinto (len : Nat) (one : Bool) : PM Val := do
  flushIfRandom
  checkClosed "readinto of closed file"
  if len = 0 then pure (.list [.int 0, .bytes []]) else
  let s ← SM.get
  let (w, out) ← readintoLoop len one (s.raw.rs.length + s.raw.data.length + len + 3) 0 []
  pure (.list [.int w, .bytes (out ++ List.replicate (len - out.length) 255)])

/-- `self.peek(1)` then `self.read(n)` in the loop of `IOBase.readline`,
_pyio.py:525-532, :546-553. -/
def readlineLoop (size : Int) : Nat → List Nat → PM (List Nat)
  | 0, _ => thr .modelFuel
  | fuel + 1, res => do
    if size < 0 ∨ (res.length : Int) < size then
      let r ← peek 1
      let ra := r.bytesOf
      let n : Nat :=
        if ra = [] then 1
        else
          let m := match findIdx? ra 10 with
            | some i => i + 1
            | none => ra.length
          if size ≥ 0 then min m size.toNat else m
      let b ← read (some n)
      let b := b.bytesOf
      if b = [] then pure res else
      let res := res ++ b
      if res.getLast? = some 10 then pure res else readlineLoop size fuel res
    else pure res

def readlineRaw (size : Option Int) : PM (List Nat) := do
  let s ← SM.get
  readlineLoop (size.getD (-1)) (s.raw.rs.length + s.raw.data.length + (tail s).length + 3) []

def mixTell : PM Int := do
  let s ← SM.get
  let (r, res) := s.raw.tell
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok n => if n < 0 then thr (osError "tell() returned an invalid position") else pure n

def rawSeekRaw (p w : Int) : PM Int := do
  let s ← SM.get
  let (r, res) := s.raw.seek p w
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok n => pure n

/-- `_BufferedIOMixin.seek`, _pyio.py:779-783. -/
def mixSeek (p w : Int) : PM Int := do
  let n ← rawSeekRaw p w
  if n < 0 then thr (osError "seek() returned an invalid position") else pure n

def validWhence (w : Int) : Bool := w == 0 || w == 1 || w == 2 || w == 3 || w == 4

def tellR : PM Val := do
  let t ← mixTell
  let s ← SM.get
  pure (.int (max (t - s.readBuf.length + s.readPos) 0))

def tellW : PM Val := do
  let t ← mixTell
  let s ← SM.get
  pure (.int (t + s.writeBuf.length))

/-- `tell`: :1204-1206, :1298-1299, :1428-1432. -/
def tell : PM Val := do
  let s ← SM.get
  if s.kind = 0 then tellR else if s.kind = 1 then tellW
  else if s.writeBuf ≠ [] then tellW else tellR

/-- `seek`: `BufferedReader.seek` (:1208-1217), `BufferedWriter.seek`
(:1301-1306), `BufferedRandom.seek` (:1411-1426). -/
def seek (p w : Int) : PM Val := do
  if !validWhence w then thr (.valueError "invalid whence value")
  let s ← SM.get
  if s.kind = 0 then
    checkClosed "seek of closed file"
    let p := if w = 1 then p - (tail s).length else p
    let r ← mixSeek p w
    resetRead
    pure (.int r)
  else if s.kind = 1 then
    flushUnlocked (fuelF s)
    let r ← mixSeek p w
    pure (.int r)
  else
    let _ ← flush
    let s ← SM.get
    if s.readBuf ≠ [] then
      let _ ← rawSeekRaw ((s.readPos : Int) - s.readBuf.length) 1
    let r ← rawSeekRaw p w
    resetRead
    if r < 0 then thr (osError "seek() returned invalid position")
    pure (.int r)

def rawTruncate (p : Option Int) : PM Val := do
  let s ← SM.get
  let (r, res) := s.raw.truncate p
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok v => pure (.int v)

def rawTellPlain : PM Int := do
  let s ← SM.get
  let (r, res) := s.raw.tell
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok n => pure n

/-- `truncate`: mixin (:791-804, read-only here), `BufferedWriter.truncate`
(:1270-1275), `BufferedRandom.truncate` (:1434-1438). -/
def truncate (p : Option Int) : PM Val := do
  let s ← SM.get
  if s.kind = 0 then
    if closed s then thr (.valueError "I/O operation on closed file.")
    thr (unsupportedOp "File or stream is not writable.")
  else
    let p : Option Int ←
      if s.kind = 2 ∧ p.isNone then do
        let t ← tell
        match t with
        | .int v => pure (some v)
        | _ => pure p
      else pure p
    let s ← SM.get
    flushUnlocked (fuelF s)
    match p with
    | some v => rawTruncate (some v)
    | none =>
      let t ← rawTellPlain
      rawTruncate (some t)

def rawClose : PM Unit := do
  let s ← SM.get
  let (r, res) := s.raw.close
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok () => pure ()

/-- `close`: mixin (:813-819), `BufferedWriter.close` (:1308-1321). -/
def close : PM Val := do
  let s ← SM.get
  if closed s then pure .none else
  let fl ← SM.attempt flush
  let c ← SM.attempt rawClose
  match c, fl with
  | .error e, _ => thr e
  | .ok (), .error e => thr e
  | .ok (), .ok _ => pure .none

/-- `BufferedWriter.write`, _pyio.py:1242-1268. -/
def writeW (b : List Nat) : PM Val := do
  let s ← SM.get
  if closed s then thr (.valueError "write to closed file")
  if s.writeBuf.length > s.size then flushUnlocked (fuelF s)
  SM.mod fun s => { s with writeBuf := s.writeBuf ++ b }
  let s ← SM.get
  let written : Int := b.length
  if s.writeBuf.length > s.size then
    let r ← SM.attempt (flushUnlocked (fuelF s))
    match r with
    | .ok () => pure (.int written)
    | .error e =>
      if e.className == "BlockingIOError" then
        let s ← SM.get
        -- the `except` only cuts back while still over size; otherwise it falls through
        if s.writeBuf.length > s.size then
          let overage : Int := (s.writeBuf.length : Int) - s.size
          SM.mod fun s => { s with writeBuf := s.writeBuf.take s.size }
          thr (.named "BlockingIOError"
            s!"write could not complete without blocking|{written - overage}")
        else pure (.int written)
      else thr e
  else pure (.int written)

/-- `write`, with `BufferedRandom.write` (:1462-1468) first undoing read-ahead. -/
def write (b : List Nat) : PM Val := do
  let s ← SM.get
  if s.kind = 2 ∧ s.readBuf ≠ [] then
    let _ ← rawSeekRaw ((s.readPos : Int) - s.readBuf.length) 1
    resetRead
  writeW b

/-- `_BufferedIOMixin.detach`, _pyio.py:821-827. -/
def detach : PM Val := do
  let _ ← flush
  SM.mod fun s => { s with detached := true }
  pure .none

/-- The constructors, _pyio.py:1030-1041, :1228-1237, :1406-1409. -/
def init (kind : Nat) (raw : Raw) (size : Int) : Py BufP :=
  if kind = 2 ∧ !raw.canSeek then .error (unsupportedOp "File or stream is not seekable.") else
  if kind = 0 ∨ kind = 2 then
    if !raw.canRead then .error (osError "\"raw\" argument must be readable.") else
    if size ≤ 0 then .error (.valueError "invalid buffer size") else
    if kind = 2 ∧ !raw.canWrite then .error (osError "\"raw\" argument must be writable.") else
    .ok ⟨raw, false, kind, size.toNat, [], 0, []⟩
  else
    if !raw.canWrite then .error (osError "\"raw\" argument must be writable.") else
    if size ≤ 0 then .error (.valueError "invalid buffer size") else
    .ok ⟨raw, false, kind, size.toNat, [], 0, []⟩

end BP2

end PyLean.PyIO
