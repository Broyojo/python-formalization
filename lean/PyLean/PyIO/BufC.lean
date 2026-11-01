import PyLean.PyIO.BufRaw

/-!
`Modules/_io/bufferedio.c`: `BufferedReader`, `BufferedWriter`, `BufferedRandom`
over the scripted `Raw`, CPython 3.14.7. `BufS` holds the fields of `buffered`
(bufferedio.c:220-262); positions are `Py_off_t`. The lock is not modelled
(single-threaded use has no re-entrant call from these raws).
-/

namespace PyLean.PyIO

open PyLean SM

structure BufS where
  raw : Raw
  ok : Bool
  detached : Bool
  readable : Bool
  writable : Bool
  absPos : Int
  /-- `self->buffer != NULL`. -/
  hasBuf : Bool
  buffer : List Nat
  pos : Int
  rawPos : Int
  readEnd : Int
  writePos : Int
  writeEnd : Int
  size : Nat
  deriving Repr, DecidableEq, Inhabited

abbrev BM := SM BufS

namespace BC2

def validRead (s : BufS) : Bool := s.readable && s.readEnd != -1
def validWrite (s : BufS) : Bool := s.writable && s.writeEnd != -1

/-- `READAHEAD`, bufferedio.c:377-379. -/
def readahead (s : BufS) : Int := if validRead s then s.readEnd - s.pos else 0

/-- `RAW_OFFSET`, bufferedio.c:381-383. -/
def rawOffset (s : BufS) : Int :=
  if (validRead s || validWrite s) && decide (s.rawPos ≥ 0) then s.rawPos - s.pos else 0

/-- `ADJUST_POSITION`, bufferedio.c:370-375. -/
def adjust (s : BufS) (n : Int) : BufS :=
  let s := { s with pos := n }
  if validRead s && decide (s.readEnd < s.pos) then { s with readEnd := s.pos } else s

/-- `CHECK_INITIALIZED`, bufferedio.c:339-348. -/
def checkInit : BM Unit := do
  let s ← SM.get
  if !s.ok then
    thr (.valueError (if s.detached then "raw stream has been detached"
      else "I/O operation on uninitialized object"))

/-- `IS_CLOSED`, bufferedio.c:351-355. -/
def isClosed (s : BufS) : Bool := !s.hasBuf || s.raw.closed

/-- `CHECK_CLOSED`, bufferedio.c:357-361. -/
def checkClosed (msg : String) : BM Unit := do
  let s ← SM.get
  if isClosed s && decide (readahead s = 0) then thr (.valueError msg)

def resetRead : BM Unit := SM.mod fun s => { s with readEnd := -1 }
def resetWrite : BM Unit := SM.mod fun s => { s with writePos := 0, writeEnd := -1 }

/-- `PyNumber_AsOff_t(res, PyExc_ValueError)` on LP64. -/
def asOff (v : Int) : BM Int :=
  if InSsize v then pure v
  else thr (.valueError "cannot fit 'int' into an offset-sized integer")

/-- The tail of `_buffered_raw_tell`/`_buffered_raw_seek`, bufferedio.c:781-792. -/
def checkPos (n : Int) : BM Int := do
  let n ← asOff n
  if n < 0 then thr (osError s!"Raw stream returned invalid position {n}")
  SM.mod fun s => { s with absPos := n }
  pure n

/-- `_buffered_raw_tell`, bufferedio.c:775-793. -/
def rawTell : BM Int := do
  let s ← SM.get
  let (r, res) := s.raw.tell
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok n => checkPos n

/-- `_buffered_raw_seek`, bufferedio.c:796-826. -/
def rawSeek (t w : Int) : BM Int := do
  let s ← SM.get
  let (r, res) := s.raw.seek t w
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok n => checkPos n

def trapEintr (e : PyExc) : Bool := e.className == "InterruptedError"

/-- `_bufferedreader_raw_read`, bufferedio.c:1611-1658: the count (`-2` for
`None`) and the bytes read. -/
def rawRead (len : Int) : Nat → BM (Int × List Nat)
  | 0 => thr .modelFuel
  | fuel + 1 => do
    let s ← SM.get
    let (r, res) := s.raw.readinto len.toNat
    SM.put { s with raw := r }
    match res with
    | .exc e => if trapEintr e then rawRead len fuel else thr e
    | .none => pure ((-2 : Int), ([] : List Nat))
    | .data d =>
      if d.length > 0 ∧ s.absPos ≠ -1 then SM.mod fun s => { s with absPos := s.absPos + d.length }
      pure ((d.length : Int), d)
    | .count n => pure ((n : Int), ([] : List Nat))
    | .bad v =>
      if !InSsize v then thr (osError "raw readinto() failed")
      else thr (osError s!"raw readinto() returned invalid length {v} (should have been between 0 and {len})")

def fuelR (s : BufS) : Nat := s.raw.rs.length + 2

/-- `_bufferedreader_fill_buffer`, bufferedio.c:1661-1675. -/
def fillBuffer : BM Int := do
  let s ← SM.get
  let start : Int := if validRead s then s.readEnd else 0
  let (n, d) ← rawRead (s.size - start) (fuelR s)
  if n ≤ 0 then pure n else
  SM.mod fun s => { s with buffer := writeAt s.buffer start.toNat d, readEnd := start + n, rawPos := start + n }
  pure n

/-- `_bufferedwriter_raw_write`, bufferedio.c:1969-2013. -/
def rawWrite (b : List Nat) : Nat → BM Int
  | 0 => thr .modelFuel
  | fuel + 1 => do
    let s ← SM.get
    let (r, res) := s.raw.write b
    SM.put { s with raw := r }
    match res with
    | .exc e => if trapEintr e then rawWrite b fuel else thr e
    | .none => pure (-2)
    | .count n =>
      if n > 0 ∧ s.absPos ≠ -1 then SM.mod fun s => { s with absPos := s.absPos + n }
      pure n
    | .data _ => pure 0
    | .bad v =>
      if !InSsize v then thr (.valueError "cannot fit 'int' into an index-sized integer") else
      thr (osError s!"raw write() returned invalid length {v} (should have been between 0 and {b.length})")

def blocking (written : Nat) : PyExc :=
  .named "BlockingIOError" s!"write could not complete without blocking|{written}"

def fuelW (s : BufS) : Nat := s.raw.ws.length + 2

/-- The loop of `_bufferedwriter_flush_unlocked`, bufferedio.c:2031-2052. -/
def flushLoop : Nat → BM Unit
  | 0 => thr .modelFuel
  | fuel + 1 => do
    let s ← SM.get
    if s.writePos < s.writeEnd then
      let n ← rawWrite (slice s.buffer s.writePos.toNat (s.writeEnd - s.writePos).toNat) (fuelW s)
      if n = -2 then thr (blocking 0)
      SM.mod fun s => { s with writePos := s.writePos + n, rawPos := s.writePos + n }
      flushLoop fuel

/-- `_bufferedwriter_flush_unlocked`, bufferedio.c:2016-2069. -/
def flushUnlocked : BM Unit := do
  let s ← SM.get
  if !validWrite s || s.writePos == s.writeEnd then
    resetWrite
  else
    let rewind := rawOffset s + (s.pos - s.writePos)
    if rewind ≠ 0 then
      let _ ← rawSeek (-rewind) 1
      SM.mod fun s => { s with rawPos := s.rawPos - rewind }
    -- a zero-length write repeats until the script runs out: the raw is called again
    let s ← SM.get
    flushLoop (s.raw.ws.length + (s.writeEnd - s.writePos).toNat + 3)
    resetWrite

/-- `buffered_flush_and_rewind_unlocked`, bufferedio.c:899-918. -/
def flushRewind : BM Unit := do
  flushUnlocked
  let s ← SM.get
  if s.readable then
    let r ← SM.attempt (rawSeek (-rawOffset s) 1)
    resetRead
    match r with
    | .error e => thr e
    | .ok _ => pure ()

/-- `_io__Buffered_flush_impl`, bufferedio.c:926-940. -/
def flush : BM Val := do
  checkInit
  checkClosed "flush of closed file"
  flushRewind
  pure .none

/-- `_bufferedreader_read_fast`, bufferedio.c:1770-1783. -/
def readFast (n : Int) : BM (Option (List Nat)) := do
  let s ← SM.get
  if n ≤ readahead s then
    SM.mod fun s => { s with pos := s.pos + n }
    pure (some (slice s.buffer s.pos.toNat n.toNat))
  else pure none

/-- The first loop of `_bufferedreader_read_generic`, bufferedio.c:1824-1845:
`some out` is an early return. -/
def genericBlocks : Nat → Int → List Nat → BM (Int × List Nat × Option Val)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, out => do
    if remaining > 0 then
      let s ← SM.get
      let r : Int := s.size * (remaining / s.size)
      if r = 0 then pure (remaining, out, (none : Option Val)) else
      let (n, d) ← rawRead r (fuelR s)
      if n = 0 ∨ n = -2 then
        if n = 0 ∨ out.length > 0 then pure (remaining, out, some (Val.bytes out))
        else pure (remaining, out, some Val.none)
      else genericBlocks fuel (remaining - n) (out ++ d)
    else pure (remaining, out, (none : Option Val))

/-- The second loop of `_bufferedreader_read_generic`, bufferedio.c:1852-1879. -/
def genericFill : Nat → Int → List Nat → BM Val
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, out => do
    let s ← SM.get
    if remaining > 0 ∧ s.readEnd < s.size then
      let r ← fillBuffer
      if r = 0 ∨ r = -2 then
        if r = 0 ∨ out.length > 0 then pure (.bytes out) else pure .none
      else
        let s ← SM.get
        let k := min r remaining
        SM.mod fun s => { s with pos := s.pos + k }
        let out := out ++ slice s.buffer s.pos.toNat k.toNat
        let remaining := remaining - k
        if remaining = 0 then pure (.bytes out) else genericFill fuel remaining out
    else pure (.bytes out)

/-- `_bufferedreader_read_generic`, bufferedio.c:1789-1883. -/
def readGeneric (n : Int) : BM Val := do
  let s ← SM.get
  let cur := readahead s
  if n ≤ cur then
    let r ← readFast n
    pure (.bytes (r.getD []))
  else
    let out0 : List Nat := if cur > 0 then slice s.buffer s.pos.toNat cur.toNat else []
    let rem0 : Int := if cur > 0 then n - cur else n
    if cur > 0 then SM.mod fun s => { s with pos := s.pos + cur }
    let s ← SM.get
    if s.writable then flushRewind
    resetRead
    let s ← SM.get
    let (remaining, out, early) ← genericBlocks (s.raw.rs.length + rem0.toNat + 3) rem0 out0
    match early with
    | some v => pure v
    | none =>
      SM.mod fun s => { s with pos := 0, rawPos := 0, readEnd := 0 }
      let s ← SM.get
      genericFill (s.raw.rs.length + remaining.toNat + 3) remaining out

/-- `_io__RawIOBase_read_impl`, iobase.c:922-960, on the raw (`n >= 0`). -/
def rawBaseRead (n : Nat) : BM (Option (List Nat)) := do
  let s ← SM.get
  let (r, res) := s.raw.readinto n
  SM.put { s with raw := r }
  match res with
  | .exc e => thr e
  | .none => pure none
  | .data d => pure (some d)
  | .count _ => pure (some [])
  | .bad v =>
    if !InSsize v then thr (.valueError "cannot fit 'int' into an index-sized integer")
    else thr (.valueError s!"readinto returned {v} outside buffer size {n}")

/-- `_io__RawIOBase_readall_impl`, iobase.c:970-1021, on the raw. -/
def rawReadall : Nat → List Nat → Bool → BM Val
  | 0, _, _ => thr .modelFuel
  | fuel + 1, acc, any => do
    let r ← SM.attempt (rawBaseRead 131072)
    match r with
    | .error e => if trapEintr e then rawReadall fuel acc any else thr e
    | .ok none => if !any then pure .none else pure (.bytes acc)
    | .ok (some d) => if d = [] then pure (.bytes acc) else rawReadall fuel (acc ++ d) true

/-- `_bufferedreader_read_all`, bufferedio.c:1678-1765 (`raw.readall` exists). -/
def readAll : BM Val := do
  let s ← SM.get
  let cur := readahead s
  let data := if cur ≠ 0 then slice s.buffer s.pos.toNat cur.toNat else []
  SM.mod fun s => { s with pos := s.pos + cur }
  if s.writable then flushRewind
  resetRead
  let s ← SM.get
  let tmp ← rawReadall (s.raw.rs.length + s.raw.data.length + 2) [] false
  if cur = 0 then pure tmp
  else pure (.bytes (data ++ tmp.bytesOf))

/-- `_io__Buffered_read_impl`, bufferedio.c:983-1015. -/
def read (n : Int) : BM Val := do
  checkInit
  if n < -1 then thr (.valueError "read length must be non-negative or -1")
  checkClosed "read of closed file"
  if n = -1 then readAll
  else
    let r ← readFast n
    match r with
    | some d => pure (.bytes d)
    | none => readGeneric n

/-- `_io__Buffered_read1_impl`, bufferedio.c:1025-1080. -/
def read1 (n : Int) : BM Val := do
  checkInit
  let s ← SM.get
  let n : Int := if n < 0 then s.size else n
  checkClosed "read of closed file"
  if n = 0 then pure (.bytes []) else
  let have' := readahead s
  if have' > 0 then
    let r ← readFast (min have' n)
    pure (.bytes (r.getD []))
  else
    if s.writable then flushRewind
    resetRead
    let s ← SM.get
    let (r, d) ← rawRead n (fuelR s)
    pure (.bytes (if r = -2 then [] else d))

/-- The loop of `_buffered_readinto_generic`, bufferedio.c:1118-1152: the
final `written` bytes, or `none` for the `None` result. -/
def readintoLoop (one : Bool) : Nat → Int → List Nat → BM (Option (List Nat))
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, out => do
    if remaining > 0 then
      let s ← SM.get
      let written := out.length
      if remaining > s.size then
        let (n, d) ← rawRead remaining (fuelR s)
        if n = 0 ∨ (n = -2 ∧ written > 0) then pure (some out)
        else if n = -2 then pure none
        else if one then pure (some (out ++ d))
        else readintoLoop one fuel (remaining - n) (out ++ d)
      else if !(one && decide (written > 0)) then
        let n ← fillBuffer
        if n > 0 then
          let s ← SM.get
          let k := min n remaining
          SM.mod fun s => { s with pos := s.pos + k }
          readintoLoop one fuel (remaining - k) (out ++ slice s.buffer s.pos.toNat k.toNat)
        else if n = 0 ∨ (n = -2 ∧ written > 0) then pure (some out)
        else if n = -2 then pure none
        else pure (some out)
      else pure (some out)
    else pure (some out)

/-- `_buffered_readinto_generic`, bufferedio.c:1083-1162, with a buffer of `len`
bytes `0xff`; the result is `[count, buffer]`. -/
def readinto (len : Nat) (one : Bool) : BM Val := do
  checkInit
  checkClosed "readinto of closed file"
  let s ← SM.get
  let n := readahead s
  let fin (out : List Nat) (c : Atom) : BM Val :=
    pure (.list [c, .bytes (out ++ List.replicate (len - out.length) 255)])
  if n > 0 ∧ n ≥ len then
    SM.mod fun s => { s with pos := s.pos + len }
    fin (slice s.buffer s.pos.toNat len) (.int len)
  else
    let out := if n > 0 then slice s.buffer s.pos.toNat n.toNat else []
    if n > 0 then SM.mod fun s => { s with pos := s.pos + n }
    if s.writable then flushRewind
    resetRead
    SM.mod fun s => { s with pos := 0 }
    let s ← SM.get
    let r ← readintoLoop one (s.raw.rs.length + len + 3) (len - out.length) out
    match r with
    | some o => fin o (.int o.length)
    | none => fin out .none

/-- The loop of `_buffered_readline`, bufferedio.c:1249-1291. -/
def readlineLoop : Nat → Int → List Nat → BM (List Nat)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, limit, acc => do
    resetRead
    let n ← fillBuffer
    if n ≤ 0 then pure acc else
    let n := if limit ≥ 0 ∧ n > limit then limit else n
    let s ← SM.get
    let seg := slice s.buffer 0 n.toNat
    match findIdx? seg 10 with
    | some i =>
      SM.mod fun s => { s with pos := i + 1 }
      pure (acc ++ seg.take (i + 1))
    | none =>
      if n = limit then
        SM.mod fun s => { s with pos := n }
        pure (acc ++ seg)
      else
        readlineLoop fuel (if limit ≥ 0 then limit - n else limit) (acc ++ seg)

/-- `_buffered_readline`, bufferedio.c:1194-1299. -/
def readlineRaw (limit : Int) : BM (List Nat) := do
  checkClosed "readline of closed file"
  let s ← SM.get
  let n := readahead s
  let n := if limit ≥ 0 ∧ n > limit then limit else n
  let seg := slice s.buffer s.pos.toNat n.toNat
  match findIdx? seg 10 with
  | some i =>
    SM.mod fun s => { s with pos := s.pos + i + 1 }
    pure (seg.take (i + 1))
  | none =>
    if n = limit then
      SM.mod fun s => { s with pos := s.pos + n }
      pure seg
    else
      let acc := if n > 0 then seg else []
      let limit := if n > 0 ∧ limit ≥ 0 then limit - n else limit
      if n > 0 then SM.mod fun s => { s with pos := s.pos + n }
      if s.writable then flushRewind
      let s ← SM.get
      readlineLoop (s.raw.rs.length + s.raw.data.length + 2) limit acc

/-- `_io__Buffered_peek_impl` (bufferedio.c:951-973) and
`_bufferedreader_peek_unlocked` (:1886-1910). -/
def peek : BM Val := do
  checkInit
  checkClosed "peek of closed file"
  let s ← SM.get
  if s.writable then flushRewind
  let s ← SM.get
  let h := readahead s
  if h > 0 then pure (.bytes (slice s.buffer s.pos.toNat h.toNat)) else
  resetRead
  let r ← fillBuffer
  let r := if r = -2 then 0 else r
  SM.mod fun s => { s with pos := 0 }
  let s ← SM.get
  pure (.bytes (slice s.buffer 0 r.toNat))

/-- `_io__Buffered_tell_impl`, bufferedio.c:1323-1339. -/
def tell : BM Val := do
  checkInit
  let p ← rawTell
  let s ← SM.get
  let p := p - rawOffset s
  pure (.int (if p < 0 then 0 else p))

/-- `_PyIOBase_check_seekable(state, raw, Py_True)`, iobase.c:414-428. -/
def checkRawSeekable : BM Unit := do
  let s ← SM.get
  if !s.raw.canSeek then thr (unsupportedOp "File or stream is not seekable.")

/-- `_io__Buffered_seek_impl`, bufferedio.c:1350-1442, after `whence` is converted. -/
def seek (target whence : Int) : BM Val := do
  checkInit
  if whence < 0 ∨ (whence > 2 ∧ whence ≠ 3 ∧ whence ≠ 4) then
    thr (.valueError s!"whence value {whence} unsupported")
  checkClosed "seek of closed file"
  checkRawSeekable
  let target ← asOff target
  let s ← SM.get
  let fast : Option Int ←
    if (whence = 0 ∨ whence = 1) ∧ s.readable then do
      let current ← if s.absPos ≠ -1 then pure s.absPos else rawTell
      let s ← SM.get
      let avail := readahead s
      if avail > 0 then
        let offset := if whence = 0 then target - (current - rawOffset s) else target
        if offset ≥ -s.pos ∧ offset ≤ avail then
          SM.mod fun s => { s with pos := s.pos + offset }
          pure (some (if current - avail + offset < 0 then 0 else current - avail + offset))
        else pure none
      else pure none
    else pure none
  match fast with
  | some v => pure (.int v)
  | none =>
    let s ← SM.get
    if s.writable then flushUnlocked
    let s ← SM.get
    let target := if whence = 1 then target - rawOffset s else target
    let n ← rawSeek target whence
    SM.mod fun s => { s with rawPos := -1 }
    let s ← SM.get
    if s.readable then resetRead
    pure (.int n)

/-- `_io__Buffered_truncate_impl`, bufferedio.c:1453-1483. -/
def truncate (p : Option Int) : BM Val := do
  checkInit
  checkClosed "truncate of closed file"
  let s ← SM.get
  if !s.writable then thr (unsupportedOp "truncate")
  flushRewind
  let s ← SM.get
  let (r, res) := s.raw.truncate p
  SM.put { s with raw := r }
  match res with
  | .error e => thr e
  | .ok v =>
    let _ ← SM.attempt rawTell
    pure (.int v)

/-- `_io__Buffered_close_impl`, bufferedio.c:545-600. -/
def close : BM Val := do
  checkInit
  let s ← SM.get
  if s.raw.closed then pure .none else
  let fl ← SM.attempt flush
  let s ← SM.get
  let (r, res) := s.raw.close
  SM.put { s with raw := r, hasBuf := false, readEnd := 0, pos := 0 }
  match res, fl with
  | .error e, _ => thr e
  | .ok (), .error e => thr e
  | .ok (), .ok _ => pure .none

/-- `_io__Buffered_detach_impl`, bufferedio.c:608-621. -/
def detach : BM Val := do
  checkInit
  let _ ← flush
  SM.mod fun s => { s with detached := true, ok := false }
  pure .none

/-- The write loop of `_io_BufferedWriter_write_impl`, bufferedio.c:2178-2205:
`(written, remaining)`. -/
def writeLoop (b : List Nat) : Nat → Int → Int → BM (Int × Int)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, written, remaining => do
    let s ← SM.get
    if remaining ≥ s.size then
      let n ← rawWrite (b.drop written.toNat) (fuelW s)
      if n = -2 then
        if remaining > s.size then
          SM.mod fun s => { s with buffer := writeAt s.buffer 0 ((b.drop written.toNat).take s.size), rawPos := 0 }
          SM.mod fun s => adjust s s.size
          SM.mod fun s => { s with writeEnd := s.size }
          thr (blocking (written + s.size).toNat)
        else pure (written, remaining)
      else writeLoop b fuel (written + n) (remaining - n)
    else pure (written, remaining)

/-- `_io_BufferedWriter_write_impl`, bufferedio.c:2079-2221. -/
def write (b : List Nat) : BM Val := do
  checkInit
  let s ← SM.get
  if isClosed s then thr (.valueError "write to closed file")
  if !validRead s && !validWrite s then SM.mod fun s => { s with pos := 0, rawPos := 0 }
  let s ← SM.get
  let avail := s.size - s.pos
  let len : Int := b.length
  if len ≤ avail ∧ len < s.size then
    SM.mod fun s => { s with buffer := writeAt s.buffer s.pos.toNat b }
    if !validWrite s || decide (s.writePos > s.pos) then SM.mod fun s => { s with writePos := s.pos }
    SM.mod fun s => adjust s (s.pos + len)
    SM.mod fun s => if s.pos > s.writeEnd then { s with writeEnd := s.pos } else s
    pure (.int len)
  else
    let r ← SM.attempt flushUnlocked
    match r with
    | .error e =>
      if e.className != "BlockingIOError" then thr e else
      let s ← SM.get
      if s.readable then resetRead
      let s ← SM.get
      let moved := slice s.buffer s.writePos.toNat (s.writeEnd - s.writePos).toNat
      SM.mod fun t => { t with buffer := writeAt t.buffer 0 moved }
      SM.mod fun t => { t with writeEnd := s.writeEnd - s.writePos, rawPos := s.rawPos - s.writePos }
      SM.mod fun t => { t with pos := s.pos - s.writePos, writePos := 0 }
      let s ← SM.get
      let avail := s.size - s.writeEnd
      if len ≤ avail then
        SM.mod fun s => { s with buffer := writeAt s.buffer s.writeEnd.toNat b }
        SM.mod fun s => { s with writeEnd := s.writeEnd + len, pos := s.pos + len }
        pure (.int len)
      else
        SM.mod fun s => { s with buffer := writeAt s.buffer s.writeEnd.toNat (b.take avail.toNat) }
        SM.mod fun s => { s with writeEnd := s.writeEnd + avail, pos := s.pos + avail }
        thr (blocking avail.toNat)
    | .ok () =>
      let s ← SM.get
      let offset := rawOffset s
      if offset ≠ 0 then
        let _ ← rawSeek (-offset) 1
        SM.mod fun s => { s with rawPos := s.rawPos - offset }
      let s ← SM.get
      let (written, remaining) ← writeLoop b (s.raw.ws.length + b.length + 3) 0 len
      let s ← SM.get
      if s.readable then resetRead
      if remaining > 0 then
        SM.mod fun s => { s with buffer := writeAt s.buffer 0 (b.drop written.toNat) }
      SM.mod fun s => { s with writePos := 0, writeEnd := remaining }
      SM.mod fun s => adjust s remaining
      SM.mod fun s => { s with rawPos := 0 }
      pure (.int (written + (if remaining > 0 then remaining else 0)))

/-- `_buffered_init`, bufferedio.c:829-863, as far as it is observable. -/
def init (kind : Nat) (raw : Raw) (size : Int) : Py BufS :=
  -- kind 0: reader, 1: writer, 2: random
  if kind = 2 ∧ !raw.canSeek then .error (unsupportedOp "File or stream is not seekable.") else
  if (kind = 0 ∨ kind = 2) ∧ !raw.canRead then .error (unsupportedOp "File or stream is not readable.") else
  if (kind = 1 ∨ kind = 2) ∧ !raw.canWrite then .error (unsupportedOp "File or stream is not writable.") else
  if size ≤ 0 then .error (.valueError "buffer size must be strictly positive") else
  if size ≥ memLimit then .error memoryError else
  let s : BufS :=
    { raw := raw, ok := false, detached := false, readable := kind ≠ 1, writable := kind ≠ 0
      absPos := -1, hasBuf := true, buffer := [], pos := 0, rawPos := 0, readEnd := -1
      writePos := 0, writeEnd := -1, size := size.toNat }
  let (s, _) := (SM.attempt rawTell) s
  .ok { s with ok := true }

end BC2

end PyLean.PyIO
