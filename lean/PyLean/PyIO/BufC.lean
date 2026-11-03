import PyLean.PyIO.BufRaw

/-!
`Modules/_io/bufferedio.c`: `BufferedReader`, `BufferedWriter`, `BufferedRandom`
over the scripted, re-entrant `Raw`, CPython 3.15.2.

`BufS` holds the fields of `buffered` (bufferedio.c:223-265); positions are
`Py_off_t`. Every call on the raw stream is a Python callback that can raise,
answer anything, or re-enter the buffered object: `BM` carries the handler `CH`
that runs a re-entered operation, so the lock (`ENTER_BUFFERED`, :329-338, and
`_enter_buffered_busy`, :294-327), the checks done before it is taken, and the
fields re-read after each callback are all part of the model.

* `self->raw == NULL` after `detach` is `detached`; a method call or attribute
  read on it dereferences `Py_TYPE(NULL)`, which is `crashErr` (the process dies).
* `self->buffer == NULL` after `close` is `!hasBuf`.
* Uninitialized memory (the `PyMem_Malloc`ed buffer, an unfilled
  `PyBytesWriter`) holds `uninit`.
* The interpreter is not finalizing and the raw is not exactly `FileIO`, so
  `_enter_buffered_busy` only raises and `fast_closed_checks` is 0.
-/

namespace PyLean.PyIO

open PyLean

structure BufS where
  raw : Raw
  ok : Bool
  detached : Bool
  readable : Bool
  writable : Bool
  /-- `self->owner` is this thread: the lock is held. -/
  locked : Bool
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
  /-- The process died. -/
  crashed : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A byte of memory nobody wrote. -/
def uninit : Nat := 256

/-- The handler for a re-entered operation. -/
abbrev CH := BfOp → SM BufS Val

/-- A C method body: state and exceptions, plus the handler for re-entry. -/
def BM (α : Type) := CH → BufS → BufS × Py α

instance : Monad BM where
  pure a := fun _ s => (s, .ok a)
  bind m f := fun R s =>
    match m R s with
    | (s', .ok a) => f a R s'
    | (s', .error e) => (s', .error e)

namespace BC2

def get : BM BufS := fun _ s => (s, .ok s)
def put (s : BufS) : BM Unit := fun _ _ => (s, .ok ())
def mod (f : BufS → BufS) : BM Unit := fun _ s => (f s, .ok ())
def thr {α : Type} (e : PyExc) : BM α := fun _ s => (s, .error e)
/-- Run `m` and hand its outcome to the caller even when it raised, as the C code
does with `PyErr_GetRaisedException`. A crash is not an exception: nothing after it runs. -/
def attempt {α : Type} (m : BM α) : BM (Py α) := fun R s =>
  let (s', r) := m R s
  if s'.crashed then (s', match r with | .ok _ => .error crashErr | .error e => .error e)
  else (s', .ok r)
def ofPy {α : Type} (r : Py α) : BM α := fun _ s => (s, r)

def className (s : BufS) : String :=
  if !s.readable then "BufferedWriter" else if !s.writable then "BufferedReader" else "BufferedRandom"

def validRead (s : BufS) : Bool := s.readable && s.readEnd != -1
def validWrite (s : BufS) : Bool := s.writable && s.writeEnd != -1

/-- `READAHEAD`, bufferedio.c:397-399. -/
def readahead (s : BufS) : Int := if s.readable && validRead s then s.readEnd - s.pos else 0

/-- `RAW_OFFSET`, bufferedio.c:401-403. -/
def rawOffset (s : BufS) : Int :=
  if (validRead s || validWrite s) && decide (s.rawPos ≥ 0) then s.rawPos - s.pos else 0

/-- `ADJUST_POSITION`, bufferedio.c:390-395. -/
def adjust (s : BufS) (n : Int) : BufS :=
  let s := { s with pos := n }
  if validRead s && decide (s.readEnd < s.pos) then { s with readEnd := s.pos } else s

def initErr (s : BufS) : PyExc :=
  .valueError (if s.detached then "raw stream has been detached" else "I/O operation on uninitialized object")

/-- `CHECK_INITIALIZED`, bufferedio.c:340-350 (and `_INT`, :352-362). -/
def checkInit : BM Unit := do
  let s ← get
  if !s.ok then thr (initErr s)

/-- `buffered_repr` (:1540-1572) of our objects: the raw has no `name`, and a
detached object's `name` raises the `ValueError` that is cleared. -/
def reprC (s : BufS) : String := s!"<_io.{className s}>"

/-- `ENTER_BUFFERED`, bufferedio.c:329-332, with `_enter_buffered_busy` (:294-327):
the lock held by this thread is a re-entrant call. -/
def enter : BM Unit := do
  let s ← get
  if s.locked then thr (.named "RuntimeError" s!"reentrant call inside {reprC s}")
  put { s with locked := true }

/-- `LEAVE_BUFFERED`, bufferedio.c:334-338. -/
def leave : BM Unit := mod fun s => { s with locked := false }

/-- The process died. -/
def crash {α : Type} : BM α := do
  mod fun s => { s with crashed := true }
  thr crashErr

/-- The start of a callback into the raw stream: the harness raw logs the call
and may first re-enter the buffered object (through the handler). -/
def callback (c : RCall) : BM Unit := fun R s =>
  let (r, h) := s.raw.enter c
  let s := { s with raw := r }
  match h with
  | none => (s, .ok ())
  | some op =>
    let (s, v) := R op s
    let s := { s with raw := s.raw.note v }
    if s.crashed then (s, .error crashErr) else (s, .ok ())

/-- A method call or attribute read on `self->raw` through `PyObject_CallMethod*`
or `PyObject_GetAttr`: with `self->raw == NULL` (`detach`) these read
`Py_TYPE(NULL)`. -/
def onRaw {α : Type} (c : RCall) (f : Raw → Raw × α) : BM α := do
  let s ← get
  if s.detached then crash
  callback c
  let s ← get
  let (r, a) := f s.raw
  put { s with raw := r }
  pure a

/-- A call on the raw object a caller already holds (not read from `self->raw`). -/
def onRawObj {α : Type} (c : RCall) (f : Raw → Raw × α) : BM α := do
  callback c
  let s ← get
  let (r, a) := f s.raw
  put { s with raw := r }
  pure a

/-- `PyObject_CallMethodObjArgs(self->raw, ...)`: it checks for `NULL`
(Objects/call.c:941-943, `null_error`). -/
def onRawObjArgs {α : Type} (c : RCall) (f : Raw → Raw × α) : BM α := do
  let s ← get
  if s.detached then thr (.named "SystemError" "null argument to internal routine")
  onRaw c f

/-- `raw.readable()`, `raw.writable()` or `raw.seekable()` through
`PyObject_CallMethodNoArgs(self->raw, ...)`: a callback whose answer is any object. -/
def inquiry (c : RCall) (flag : Raw → Bool) : BM QAns := do
  let r ← onRaw c (fun r => r.inquire (flag r))
  ofPy r

/-- The same call on the `raw` argument of a constructor (not `self->raw`). -/
def inquiryObj (c : RCall) (flag : Raw → Bool) : BM QAns := do
  let r ← onRawObj c (fun r => r.inquire (flag r))
  ofPy r

/-- `_PyIOBase_check_seekable`/`_readable`/`_writable(state, raw, Py_True)`,
Modules/_io/iobase.c:413-428, :446-461, :479-494: the answer must be `True` itself
(`res != Py_True` refuses `1`). -/
def checkInq (a : QAns) (msg : String) : BM Unit :=
  if a = .bool true then pure () else thr (unsupportedOp msg)

/-- `buffered_closed`, bufferedio.c:520-532: `PyObject_IsTrue(raw.closed)`. -/
def bufferedClosed : BM Bool := do
  checkInit
  let r ← onRaw .closed Raw.closedAttr
  ofPy r

/-- `IS_CLOSED`, bufferedio.c:364-368. -/
def isClosed : BM Bool := do
  let s ← get
  if !s.hasBuf then pure true else bufferedClosed

/-- `CHECK_CLOSED`, bufferedio.c:370-382: `READAHEAD` is read after `IS_CLOSED`. -/
def checkClosed (msg : String) : BM Unit := do
  let c ← isClosed
  let s ← get
  if c && decide (readahead s = 0) then thr (.valueError msg)

/-- `_bufferedreader_reset_buf`, bufferedio.c:1578-1581. -/
def resetRead : BM Unit := mod fun s => { s with readEnd := -1 }
/-- `_bufferedwriter_reset_buf`, bufferedio.c:1925-1929. -/
def resetWrite : BM Unit := mod fun s => { s with writePos := 0, writeEnd := -1 }

/-- `PyNumber_AsOff_t(res, PyExc_ValueError)` on LP64. -/
def asOff (v : Int) : BM Int :=
  if InSsize v then pure v
  else thr (.valueError "cannot fit 'int' into an offset-sized integer")

/-- The tail of `_buffered_raw_tell`/`_buffered_raw_seek`, bufferedio.c:791-801, :824-834. -/
def checkPos : IRes → BM Int
  | .wrong => thr strIndexErr
  | .int n => do
    let n ← asOff n
    if n < 0 then thr (osError s!"Raw stream returned invalid position {n}")
    mod fun s => { s with absPos := n }
    pure n

/-- `_buffered_raw_tell`, bufferedio.c:783-802. -/
def rawTell : BM Int := do
  let r ← onRaw .tell Raw.tell
  match r with
  | .error e => thr e
  | .ok v => checkPos v

/-- `_buffered_raw_seek`, bufferedio.c:804-835. -/
def rawSeek (t w : Int) : BM Int := do
  let r ← onRawObjArgs (.seek t w) (fun r => r.seek t w)
  match r with
  | .error e => thr e
  | .ok v => checkPos v

/-- The `OSError` subclasses a raw stream of the harness can raise. -/
def isOSErrorCls (c : String) : Bool :=
  c == "OSError" || c == "InterruptedError" || c == "PermissionError" || c == "BlockingIOError"
    || c == "FileNotFoundError" || c == "BrokenPipeError" || c == "ConnectionError" || c == "TimeoutError"

/-- `_PyIO_trap_eintr`, bufferedio.c:878-901: the exception is an `OSError`
(`PyErr_ExceptionMatches`, :881) whose `errno` is `EINTR` (4 on Linux, :887-895); the
class name plays no part: `InterruptedError('x')` has no `errno`. -/
def trapEintr (e : PyExc) (eno : Option Nat) : Bool := isOSErrorCls e.className && eno == some 4

/-- Where a raw callback reads or writes: `ptr` says whether the start pointer
is `NULL` (`some true`), inside a freed buffer (`some false`), or valid (`none`). -/
def bufPtr (s : BufS) (off : Int) : Option Bool :=
  if s.hasBuf then none else some (decide (off = 0))

/-- `PyMemoryView_FromBuffer` on a `NULL` start, Objects/memoryobject.c. -/
def nullView : PyExc := .valueError "PyMemoryView_FromBuffer(): info->buf must not be NULL"

/-- `_bufferedreader_raw_read`, bufferedio.c:1622-1670: the count (`-2` for `None`)
and the bytes `readinto` stored (fewer than the count when it lied). -/
def rawRead (ptr : Option Bool) (len : Int) : Nat → BM (Int × List Nat)
  | 0 => thr .modelFuel
  | fuel + 1 => do
    if ptr = some true then thr nullView
    let res ← onRaw (.readinto len) (fun r => r.readinto len.toNat)
    match res with
    | .exc e eno => if trapEintr e eno then rawRead ptr len fuel else thr e
    | .none => pure ((-2 : Int), ([] : List Nat))
    | .data d =>
      -- storing through a pointer into freed memory
      if ptr = some false ∧ d ≠ [] then crash
      if d.length > 0 then mod fun s => if s.absPos ≠ -1 then { s with absPos := s.absPos + d.length } else s
      pure ((d.length : Int), d)
    | .count n => pure ((n : Int), ([] : List Nat))
    | .wrong => thr (osError "raw readinto() failed")
    | .bad v =>
      if !InSsize v then thr (osError "raw readinto() failed")
      else if v < 0 ∨ v > len then
        thr (osError s!"raw readinto() returned invalid length {v} (should have been between 0 and {len})")
      else
        if v > 0 then mod fun s => if s.absPos ≠ -1 then { s with absPos := s.absPos + v } else s
        pure (v, [])

/-- The first `n` bytes of a region that `readinto` stored `d` into, `fill`
standing for the bytes it left alone. -/
def pad (n : Int) (d : List Nat) (fill : Nat) : List Nat := d ++ List.replicate (n.toNat - d.length) fill

def fuelOf (s : BufS) : Nat :=
  s.raw.rs.length + s.raw.ws.length + s.raw.hooks.length + s.raw.data.length + 4

/-- `_bufferedreader_fill_buffer`, bufferedio.c:1672-1687. -/
def fillBuffer : BM Int := do
  let s ← get
  let start : Int := if validRead s then s.readEnd else 0
  let (n, d) ← rawRead (bufPtr s start) (s.size - start) (fuelOf s)
  if n ≤ 0 then pure n else
  mod fun s => { s with buffer := writeAt s.buffer start.toNat d, readEnd := start + n, rawPos := start + n }
  pure n

/-- `_bufferedwriter_raw_write`, bufferedio.c:1976-2021. -/
def rawWrite (ptr : Option Bool) (b : List Nat) : Nat → BM Int
  | 0 => thr .modelFuel
  | fuel + 1 => do
    if ptr = some true then thr nullView
    let res ← onRaw (.write b) (fun r => r.write b)
    -- `raw.write` reads the view first (the harness copies it)
    if ptr = some false then crash
    match res with
    | .exc e eno => if trapEintr e eno then rawWrite ptr b fuel else thr e
    | .none => pure (-2)
    | .count n =>
      if n > 0 then mod fun s => if s.absPos ≠ -1 then { s with absPos := s.absPos + n } else s
      pure n
    | .data _ => pure 0
    | .wrong =>
      -- :2010-2017: a failed conversion leaves `n == -1`, and `n < 0` replaces its error
      thr (osError s!"raw write() returned invalid length -1 (should have been between 0 and {b.length})")
    | .bad v =>
      let n : Int := if InSsize v then v else -1
      if n < 0 ∨ n > b.length then
        thr (osError s!"raw write() returned invalid length {n} (should have been between 0 and {b.length})")
      else
        if n > 0 then mod fun s => if s.absPos ≠ -1 then { s with absPos := s.absPos + n } else s
        pure n

/-- `_set_BlockingIOError`, bufferedio.c:755-765. -/
def blocking (written : Int) : PyExc :=
  .named "BlockingIOError" s!"write could not complete without blocking|{written}"

/-- The loop of `_bufferedwriter_flush_unlocked`, bufferedio.c:2039-2059. -/
def flushLoop : Nat → BM Unit
  | 0 => thr .modelFuel
  | fuel + 1 => do
    let s ← get
    if s.writePos < s.writeEnd then
      let n ← rawWrite (bufPtr s s.writePos)
        (slice s.buffer s.writePos.toNat (s.writeEnd - s.writePos).toNat) (fuelOf s)
      if n = -2 then thr (blocking 0)
      mod fun s => { s with writePos := s.writePos + n, rawPos := s.writePos + n }
      flushLoop fuel

/-- `_bufferedwriter_flush_unlocked`, bufferedio.c:2023-2077. -/
def flushUnlocked : BM Unit := do
  let s ← get
  if !validWrite s || s.writePos == s.writeEnd then
    resetWrite
  else
    let rewind := rawOffset s + (s.pos - s.writePos)
    if rewind ≠ 0 then
      let _ ← rawSeek (-rewind) 1
      mod fun s => { s with rawPos := s.rawPos - rewind }
    -- a zero-length write repeats until the script runs out: the raw is called again
    let s ← get
    flushLoop (fuelOf s + (s.writeEnd - s.writePos).toNat)
    resetWrite

/-- `buffered_flush_and_rewind_unlocked`, bufferedio.c:907-927. -/
def flushRewind : BM Unit := do
  flushUnlocked
  let s ← get
  if s.readable then
    let r ← attempt (rawSeek (-rawOffset s) 1)
    resetRead
    match r with
    | .error e => thr e
    | .ok _ => pure ()

/-- Run `m` with the lock held: `ENTER_BUFFERED` ... `LEAVE_BUFFERED` on every path. -/
def locked {α : Type} (m : BM α) : BM α := do
  enter
  let r ← attempt m
  leave
  ofPy r

/-- `_io__Buffered_flush_impl`, bufferedio.c:934-949. -/
def flush : BM Val := do
  checkInit
  checkClosed "flush of closed file"
  locked flushRewind
  pure .none

/-- `_io__Buffered_simple_flush_impl`, bufferedio.c:512-518: `BufferedReader.flush`
forwards to the raw stream, with no closed check of its own and no rewind, and
returns whatever `raw.flush()` returns. -/
def simpleFlush : BM Val := do
  checkInit
  let r ← onRaw .flush Raw.flush
  ofPy r

/-- `_PyFile_Flush(self)`, Objects/fileobject.c:539-548: the `flush` of the type
(bufferedio.c:2553 for a reader, :2626 and :2734 for the others). -/
def flushMethod : BM Val := do
  let s ← get
  if s.writable then flush else simpleFlush

/-- `_bufferedreader_read_fast`, bufferedio.c:1779-1795. -/
def readFast (n : Int) : BM (Option (List Nat)) := do
  let s ← get
  if n ≤ readahead s then
    mod fun s => { s with pos := s.pos + n }
    pure (some (slice s.buffer s.pos.toNat n.toNat))
  else pure none

/-- `MINUS_LAST_BLOCK`, bufferedio.c:408-411 (both branches compute this). -/
def minusLastBlock (s : BufS) (n : Int) : Int := s.size * (n / s.size)

/-- The first loop of `_bufferedreader_read_generic`, bufferedio.c:1831-1850:
`some out` is an early return. -/
def genericBlocks : Nat → Int → List Nat → BM (Int × List Nat × Option Val)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, out => do
    if remaining > 0 then
      let s ← get
      let r := minusLastBlock s remaining
      if r = 0 then pure (remaining, out, (none : Option Val)) else
      let (n, d) ← rawRead none r (fuelOf s)
      if n = 0 ∨ n = -2 then
        if n = 0 ∨ out.length > 0 then pure (remaining, out, some (Val.bytes out))
        else pure (remaining, out, some Val.none)
      else genericBlocks fuel (remaining - n) (out ++ pad n d uninit)
    else pure (remaining, out, (none : Option Val))

/-- The second loop of `_bufferedreader_read_generic`, bufferedio.c:1858-1884. -/
def genericFill : Nat → Int → List Nat → BM Val
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, out => do
    let s ← get
    if remaining > 0 ∧ s.readEnd < s.size then
      let r ← fillBuffer
      if r = 0 ∨ r = -2 then
        if r = 0 ∨ out.length > 0 then pure (.bytes out) else pure .none
      else
        let s ← get
        let k := min r remaining
        mod fun s => { s with pos := s.pos + k }
        let out := out ++ slice s.buffer s.pos.toNat k.toNat
        let remaining := remaining - k
        if remaining = 0 then pure (.bytes out) else genericFill fuel remaining out
    else pure (.bytes out)

/-- `PyBytesWriter_Create(n)`, Objects/bytesobject.c: a `bytes` of `n` bytes, or
the exception of `allocBytes`. -/
def newWriter (n : Int) : BM Unit := ofPy (allocBytes n)

/-- `_bufferedreader_read_generic`, bufferedio.c:1800-1891. -/
def readGeneric (n : Int) : BM Val := do
  let s ← get
  let cur := readahead s
  if n ≤ cur then
    let r ← readFast n
    pure (.bytes (r.getD []))
  else
    newWriter n
    let out0 : List Nat := if cur > 0 then slice s.buffer s.pos.toNat cur.toNat else []
    let rem0 : Int := if cur > 0 then n - cur else n
    if cur > 0 then mod fun s => { s with pos := s.pos + cur }
    let s ← get
    if s.writable then flushRewind
    resetRead
    let s ← get
    let (remaining, out, early) ← genericBlocks (fuelOf s + rem0.toNat) rem0 out0
    match early with
    | some v => pure v
    | none =>
      mod fun s => { s with pos := 0, rawPos := 0, readEnd := 0 }
      let s ← get
      genericFill (fuelOf s + remaining.toNat) remaining out

/-- `_io__RawIOBase_read_impl`, Modules/_io/iobase.c:922-961, on the raw (`n >= 0`):
the bytearray it reads into starts uninitialized. A failure comes back as a value with
the `errno` of the exception (`none` for the `ValueError`/`TypeError` it raises itself). -/
def rawBaseRead (n : Nat) : BM (Except (PyExc × Option Nat) (Option (List Nat))) := do
  let res ← onRawObj (.readinto n) (fun r => r.readinto n)
  match res with
  | .exc e eno => pure (.error (e, eno))
  | .none => pure (.ok none)
  | .data d => pure (.ok (some d))
  | .count _ => pure (.ok (some []))
  | .wrong => pure (.error (strIndexErr, none))
  | .bad v =>
    if !InSsize v then pure (.error (.valueError "cannot fit 'int' into an index-sized integer", none))
    else if v < 0 ∨ v > n then pure (.error (.valueError s!"readinto returned {v} outside buffer size {n}", none))
    else pure (.ok (some (List.replicate v.toNat uninit)))

/-- `_io__RawIOBase_readall_impl`, Modules/_io/iobase.c:970-1020, on the raw. -/
def rawReadall : Nat → List Nat → Bool → BM Val
  | 0, _, _ => thr .modelFuel
  | fuel + 1, acc, any => do
    let r ← rawBaseRead 131072
    match r with
    | .error (e, eno) => if trapEintr e eno then rawReadall fuel acc any else thr e
    | .ok none => if !any then pure .none else pure (.bytes acc)
    | .ok (some d) => if d = [] then pure (.bytes acc) else rawReadall fuel (acc ++ d) true

/-- `_bufferedreader_read_all`, bufferedio.c:1689-1777 (`raw.readall` exists). -/
def readAll : BM Val := do
  let s ← get
  let cur := readahead s
  let data := if cur ≠ 0 then slice s.buffer s.pos.toNat cur.toNat else []
  mod fun s => { s with pos := s.pos + cur }
  if s.writable then flushRewind
  resetRead
  -- `PyObject_GetOptionalAttr(self->raw, &_Py_ID(readall), ...)`
  let s ← get
  if s.detached then crash
  let tmp ← rawReadall (fuelOf s) [] false
  if cur = 0 then pure tmp
  else pure (.bytes (data ++ tmp.bytesOf))

/-- `_io__Buffered_read_impl`, bufferedio.c:991-1024. -/
def read (n : Int) : BM Val := do
  checkInit
  if n < -1 then thr (.valueError "read length must be non-negative or -1")
  checkClosed "read of closed file"
  if n = -1 then locked readAll
  else
    let r ← readFast n
    match r with
    | some d => pure (.bytes d)
    | none => locked (readGeneric n)

/-- `_io__Buffered_read1_impl`, bufferedio.c:1033-1092. -/
def read1 (n : Int) : BM Val := do
  checkInit
  let s ← get
  let n : Int := if n < 0 then s.size else n
  checkClosed "read of closed file"
  if n = 0 then pure (.bytes []) else
  let s ← get
  let have' := readahead s
  if have' > 0 then
    let r ← readFast (min have' n)
    pure (.bytes (r.getD []))
  else
    locked do
      let s ← get
      if s.writable then flushRewind
      resetRead
      newWriter n
      let (r, d) ← rawRead none n (fuelOf s)
      pure (.bytes (if r = -2 then [] else pad r d uninit))

/-- The loop of `_buffered_readinto_generic`, bufferedio.c:1128-1168: the
final bytes written, or `none` for the `None` result. Bytes of the caller's
buffer that `readinto` left alone stay `0xff` (the harness fills it). -/
def readintoLoop (one : Bool) : Nat → Int → List Nat → BM (Option (List Nat))
  | 0, _, _ => thr .modelFuel
  | fuel + 1, remaining, out => do
    if remaining > 0 then
      let s ← get
      let written := out.length
      if remaining > s.size then
        let (n, d) ← rawRead none remaining (fuelOf s)
        if n = 0 ∨ (n = -2 ∧ written > 0) then pure (some out)
        else if n = -2 then pure none
        else if one then pure (some (out ++ pad n d 255))
        else readintoLoop one fuel (remaining - n) (out ++ pad n d 255)
      else if !(one && decide (written > 0)) then
        let n ← fillBuffer
        if n > 0 then
          let s ← get
          let k := min n remaining
          mod fun s => { s with pos := s.pos + k }
          readintoLoop one fuel (remaining - k) (out ++ slice s.buffer s.pos.toNat k.toNat)
        else if n = 0 ∨ (n = -2 ∧ written > 0) then pure (some out)
        else if n = -2 then pure none
        else pure (some out)
      else pure (some out)
    else pure (some out)

/-- `_buffered_readinto_generic`, bufferedio.c:1094-1174, with a buffer of `len`
bytes `0xff`; the result is `[count, buffer]`. The bytes already buffered are
copied before the lock is taken (:1103-1113). -/
def readinto (len : Nat) (one : Bool) : BM Val := do
  checkInit
  checkClosed "readinto of closed file"
  let s ← get
  let n := readahead s
  let fin (out : List Nat) (c : Atom) : BM Val :=
    pure (.list [c, .bytes (out ++ List.replicate (len - out.length) 255)])
  if n > 0 ∧ n ≥ len then
    mod fun s => { s with pos := s.pos + len }
    fin (slice s.buffer s.pos.toNat len) (.int len)
  else
    let out := if n > 0 then slice s.buffer s.pos.toNat n.toNat else []
    if n > 0 then mod fun s => { s with pos := s.pos + n }
    locked do
      let s ← get
      if s.writable then flushRewind
      resetRead
      mod fun s => { s with pos := 0 }
      let s ← get
      let r ← readintoLoop one (fuelOf s + len) (len - out.length) out
      match r with
      | some o => fin o (.int o.length)
      | none => fin out .none

/-- The loop of `_buffered_readline`, bufferedio.c:1263-1298. -/
def readlineLoop : Nat → Int → List Nat → BM (List Nat)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, limit, acc => do
    resetRead
    let n ← fillBuffer
    if n ≤ 0 then pure acc else
    let n := if limit ≥ 0 ∧ n > limit then limit else n
    let s ← get
    let seg := slice s.buffer 0 n.toNat
    match findIdx? seg 10 with
    | some i =>
      mod fun s => { s with pos := i + 1 }
      pure (acc ++ seg.take (i + 1))
    | none =>
      if n = limit then
        mod fun s => { s with pos := n }
        pure (acc ++ seg)
      else
        readlineLoop fuel (if limit ≥ 0 then limit - n else limit) (acc ++ seg)

/-- `_buffered_readline`, bufferedio.c:1205-1311: the buffered part is scanned
before the lock is taken. -/
def readlineRaw (limit : Int) : BM (List Nat) := do
  checkClosed "readline of closed file"
  let s ← get
  let n := readahead s
  let n := if limit ≥ 0 ∧ n > limit then limit else n
  let seg := slice s.buffer s.pos.toNat n.toNat
  match findIdx? seg 10 with
  | some i =>
    mod fun s => { s with pos := s.pos + i + 1 }
    pure (seg.take (i + 1))
  | none =>
    if n = limit then
      mod fun s => { s with pos := s.pos + n }
      pure seg
    else
      locked do
        let acc := if n > 0 then seg else []
        let limit := if n > 0 ∧ limit ≥ 0 then limit - n else limit
        if n > 0 then mod fun s => { s with pos := s.pos + n }
        let s ← get
        if s.writable then flushRewind
        let s ← get
        readlineLoop (fuelOf s) limit acc

/-- `_bufferedreader_peek_unlocked`, bufferedio.c:1893-1918. -/
def peekUnlocked : BM Val := do
  let s ← get
  let h := readahead s
  if h > 0 then pure (.bytes (slice s.buffer s.pos.toNat h.toNat)) else
  resetRead
  let r ← fillBuffer
  let r := if r = -2 then 0 else r
  mod fun s => { s with pos := 0 }
  let s ← get
  pure (.bytes (slice s.buffer 0 r.toNat))

/-- `_io__Buffered_peek_impl`, bufferedio.c:959-982. -/
def peek : BM Val := do
  checkInit
  checkClosed "peek of closed file"
  locked do
    let s ← get
    if s.writable then flushRewind
    peekUnlocked

/-- `_io__Buffered_tell_impl`, bufferedio.c:1334-1351: no lock. -/
def tell : BM Val := do
  checkInit
  let p ← rawTell
  let s ← get
  let p := p - rawOffset s
  pure (.int (if p < 0 then 0 else p))

/-- `_PyIOBase_check_seekable(state, raw, Py_True)`, Modules/_io/iobase.c:413-428. -/
def checkRawSeekable : BM Unit := do
  let a ← inquiry .seekable Raw.canSeek
  checkInq a "File or stream is not seekable."

/-- `_io__Buffered_seek_impl`, bufferedio.c:1361-1454, after `whence` is converted.
`abs_pos` is only ever assigned a value `>= 0` (:800, :833) or incremented, so
`RAW_TELL` (:405-406) never calls the raw and its unchecked failure cannot arise. -/
def seek (target whence : Int) : BM Val := do
  checkInit
  if whence < 0 ∨ (whence > 2 ∧ whence ≠ 3 ∧ whence ≠ 4) then
    thr (.valueError s!"whence value {whence} unsupported")
  checkClosed "seek of closed file"
  checkRawSeekable
  let target ← asOff target
  let s ← get
  let fast : Option Int ←
    if (whence = 0 ∨ whence = 1) ∧ s.readable then do
      let current ← if s.absPos ≠ -1 then pure s.absPos else rawTell
      let s ← get
      let avail := readahead s
      if avail > 0 then
        let offset := if whence = 0 then target - (current - rawOffset s) else target
        if offset ≥ -s.pos ∧ offset ≤ avail then
          mod fun s => { s with pos := s.pos + offset }
          pure (some (if current - avail + offset < 0 then 0 else current - avail + offset))
        else pure none
      else pure none
    else pure none
  match fast with
  | some v => pure (.int v)
  | none =>
    locked do
      let s ← get
      if s.writable then flushUnlocked
      let s ← get
      let target := if whence = 1 then target - rawOffset s else target
      let n ← rawSeek target whence
      mod fun s => { s with rawPos := -1 }
      let s ← get
      if s.readable then resetRead
      pure (.int n)

/-- `_io__Buffered_truncate_impl`, bufferedio.c:1464-1495. -/
def truncate (p : Option Int) : BM Val := do
  checkInit
  checkClosed "truncate of closed file"
  let s ← get
  if !s.writable then thr (unsupportedOp "truncate")
  locked do
    flushRewind
    let res ← onRaw (.truncate p) (fun r => r.truncate p)
    match res with
    | .error e => thr e
    | .ok v =>
      let _ ← attempt rawTell
      pure (.int v)

/-- `_io__Buffered_close_impl`, bufferedio.c:553-609: the lock is dropped around
`flush()` and taken again for `raw.close()`. -/
def close : BM Val := do
  checkInit
  -- :561-581: ENTER, IS_CLOSED (an error or True goes to `end`, which leaves), LEAVE
  let c ← locked (attempt isClosed)
  match c with
  | .error e => thr e
  | .ok true => pure .none
  | .ok false =>
    let fl ← attempt flushMethod
    -- :583-607: ENTER (a failure returns at once), raw.close(), free, LEAVE
    let res ← locked do
      let s ← get
      if s.detached then crash
      let res ← attempt (onRaw .close Raw.close)
      mod fun s => { s with hasBuf := false, readEnd := 0, pos := 0 }
      pure res
    match res, fl with
    | .error e, _ => thr e
    | .ok (.error e), _ => thr e
    | .ok (.ok ()), .error e => thr e
    | .ok (.ok ()), .ok _ => pure .none

/-- `_io__Buffered_detach_impl`, bufferedio.c:616-630. -/
def detach : BM Val := do
  checkInit
  let _ ← flushMethod
  let s ← get
  -- a `flush` that detached re-entrantly leaves `self->raw == NULL`: `detach`
  -- returns NULL with no exception set, which the call machinery reports as a
  -- `SystemError` whose text depends on whether the call site was specialized
  -- (`_Py_CheckFunctionResult` or the eval loop's "error return without exception set")
  if s.detached then thr (.named "SystemError" "~NULL without an exception")
  mod fun s => { s with detached := true, ok := false }
  pure .none

/-- The write loop of `_io_BufferedWriter_write_impl`, bufferedio.c:2184-2215:
`(written, remaining)`. -/
def writeLoop (b : List Nat) : Nat → Int → Int → BM (Int × Int)
  | 0, _, _ => thr .modelFuel
  | fuel + 1, written, remaining => do
    let s ← get
    if remaining ≥ s.size then
      let n ← rawWrite none (b.drop written.toNat) (fuelOf s)
      if n = -2 then
        if remaining > s.size then
          mod fun s => { s with buffer := writeAt s.buffer 0 ((b.drop written.toNat).take s.size), rawPos := 0 }
          mod fun s => adjust s s.size
          mod fun s => { s with writeEnd := s.size }
          let s ← get
          thr (blocking (written + s.size))
        else pure (written, remaining)
      else writeLoop b fuel (written + n) (remaining - n)
    else pure (written, remaining)

/-- The body of `_io_BufferedWriter_write_impl` under the lock, bufferedio.c:2100-2228. -/
def writeLocked (b : List Nat) : BM Val := do
  let c ← isClosed
  if c then thr (.valueError "write to closed file")
  let s ← get
  if !validRead s && !validWrite s then mod fun s => { s with pos := 0, rawPos := 0 }
  let s ← get
  let avail := s.size - s.pos
  let len : Int := b.length
  if len ≤ avail ∧ len < s.size then
    mod fun s => { s with buffer := writeAt s.buffer s.pos.toNat b }
    if !validWrite s || decide (s.writePos > s.pos) then mod fun s => { s with writePos := s.pos }
    mod fun s => adjust s (s.pos + len)
    mod fun s => if s.pos > s.writeEnd then { s with writeEnd := s.pos } else s
    pure (.int len)
  else
    let r ← attempt flushUnlocked
    match r with
    | .error e =>
      -- `_buffered_check_blocking_error`, :769-781
      if e.className != "BlockingIOError" then thr e else
      let s ← get
      if s.readable then resetRead
      let s ← get
      let moved := slice s.buffer s.writePos.toNat (s.writeEnd - s.writePos).toNat
      mod fun t => { t with buffer := writeAt t.buffer 0 moved }
      mod fun t => { t with writeEnd := s.writeEnd - s.writePos, rawPos := s.rawPos - s.writePos }
      mod fun t => { t with pos := s.pos - s.writePos, writePos := 0 }
      let s ← get
      let avail := s.size - s.writeEnd
      if len ≤ avail then
        mod fun s => { s with buffer := writeAt s.buffer s.writeEnd.toNat b }
        mod fun s => { s with writeEnd := s.writeEnd + len, pos := s.pos + len }
        pure (.int len)
      else
        mod fun s => { s with buffer := writeAt s.buffer s.writeEnd.toNat (b.take avail.toNat) }
        mod fun s => { s with writeEnd := s.writeEnd + avail, pos := s.pos + avail }
        thr (blocking avail)
    | .ok () =>
      let s ← get
      let offset := rawOffset s
      if offset ≠ 0 then
        let _ ← rawSeek (-offset) 1
        mod fun s => { s with rawPos := s.rawPos - offset }
      let s ← get
      let (written, remaining) ← writeLoop b (fuelOf s + b.length) 0 len
      let s ← get
      if s.readable then resetRead
      if remaining > 0 then
        mod fun s => { s with buffer := writeAt s.buffer 0 (b.drop written.toNat) }
      mod fun s => { s with writePos := 0, writeEnd := remaining }
      mod fun s => adjust s remaining
      mod fun s => { s with rawPos := 0 }
      pure (.int (written + (if remaining > 0 then remaining else 0)))

/-- `_io_BufferedWriter_write_impl`, bufferedio.c:2086-2234. -/
def write (b : List Nat) : BM Val := do
  checkInit
  locked (writeLocked b)

/-- `_buffered_init`, bufferedio.c:837-872, as far as it is observable. Nothing
sets `abs_pos` before the first `_buffered_raw_tell` (assignments are at :800 and
:833 only), so if that call fails it stays at `tp_alloc`'s 0, not the -1 that
means unknown, and `RAW_TELL` (:405-406) trusts it. The raw's `tell` runs while
`ok` is 0, so a hook that re-enters is refused by `CHECK_INITIALIZED`. -/
def init (kind : Nat) (raw : Raw) (size : Int) : BM BufS := do
  -- the object `tp_alloc` made: `ok` 0 and no buffer; `readable`/`writable` here
  -- stand for its type, which decides which methods a re-entered call finds
  put { raw := raw, ok := false, detached := false, readable := kind ≠ 1, writable := kind ≠ 0
        locked := false, absPos := 0, hasBuf := false, buffer := [], pos := 0, rawPos := 0,
        readEnd := 0, writePos := 0, writeEnd := 0, size := 0, crashed := false }
  -- kind 0: reader (:1591-1620), 1: writer (:1943-1974), 2: random (:2484-2520)
  if kind = 2 then
    let a ← inquiryObj .seekable Raw.canSeek
    checkInq a "File or stream is not seekable."
  if kind = 0 ∨ kind = 2 then
    let a ← inquiryObj .readable Raw.canRead
    checkInq a "File or stream is not readable."
  if kind = 1 ∨ kind = 2 then
    let a ← inquiryObj .writable Raw.canWrite
    checkInq a "File or stream is not writable."
  mod fun s => { s with size := size.toNat }
  if size ≤ 0 then thr (.valueError "buffer size must be strictly positive")
  if size ≥ memLimit then thr memoryError
  mod fun s => { s with hasBuf := true, buffer := List.replicate size.toNat uninit }
  let _ ← attempt rawTell
  mod fun s => { s with readEnd := -1, writePos := 0, writeEnd := -1, pos := 0, ok := true }
  get

end BC2

end PyLean.PyIO
