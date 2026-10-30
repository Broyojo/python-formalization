import PyLean.PyIO.Basic

/-!
`BytesIO`: the C implementation (`Modules/_io/bytesio.c`) and the pure-Python
twin (`Lib/_pyio.py:876-1000`, plus the `IOBase`/`BufferedIOBase` methods it
inherits, `Lib/_pyio.py:306-600`), CPython 3.14.7.

State: the buffer contents (`string_size` bytes in C, the `bytearray` in
Python), the position, the closed flag and the number of live `getbuffer()`
views. C's over-allocation, copy-on-write sharing and the free-threading
critical sections are unobservable here and not modelled. C keeps
`0 <= pos <= PY_SSIZE_T_MAX`; Python's position is an unbounded int.
-/

namespace PyLean.PyIO

open PyLean

structure BState where
  buf : List Nat
  pos : Nat
  closed : Bool
  exports : Nat
  /-- C only: `SHARED_BUF(self)` (bytesio.c:76-80), i.e. the internal bytes
  object is referenced elsewhere. The model assumes the caller keeps no
  reference to the objects passed in or returned (as the difftest does), so
  the buffer is shared exactly while it is the initial object and that object
  is one of the immortal empty/one-byte `bytes` singletons. -/
  shared : Bool
  deriving Repr, DecidableEq, Inhabited

/-- A BytesIO operation. `readinto n` passes `bytearray(b'\xff' * n)`;
`release` releases the most recent `getbuffer()` view; `next` is `next(f)`;
`closed` reads the `closed` attribute. -/
inductive BOp where
  | read (size : Option Int)
  | read1 (size : Option Int)
  | readline (size : Option Int)
  | readlines (hint : Option Int)
  | readinto (n : Nat)
  | write (b : List Nat)
  | seek (pos : Int) (whence : Int)
  | tell
  | truncate (size : Option Int)
  | getvalue
  | getbuffer
  | release
  | close
  | next
  | closed
  deriving Repr, DecidableEq, Inhabited

/-- `BytesIO(initial_bytes)`: both twins store the bytes and set the position to 0
(bytesio.c:1035-1062, _pyio.py:884-889). -/
def bInit (init : List Nat) : BState := ⟨init, 0, false, 0, init.length ≤ 1⟩

/-- `release`: drop one export (both twins: `memoryview.release()`). -/
def bRelease (s : BState) : BState := { s with exports := s.exports - 1 }

/-! ## The C implementation -/

namespace C

def closedErr : PyExc := .valueError "I/O operation on closed file."

/-- `scan_eol_lock_held`, bytesio.c:117-149. -/
def scanEol (s : BState) (len : Int) : Nat :=
  if s.pos ≥ s.buf.length then 0 else
  let maxlen : Nat := s.buf.length - s.pos
  let len : Nat := if len < 0 ∨ len > maxlen then maxlen else len.toNat
  if len = 0 then 0 else
  match findIdx? (slice s.buf s.pos len) 10 with
  | some i => i + 1
  | none => len

/-- `read_bytes_lock_held`, bytesio.c:460-486 (`size <= string_size - pos`). -/
def readBytes (s : BState) (size : Nat) : BState × List Nat :=
  ({ s with pos := s.pos + size }, slice s.buf s.pos size)

/-- `_io_BytesIO_read_impl`, bytesio.c:500-515 (`read1` is identical, :531-535). -/
def read (s : BState) (size : Option Int) : BState × Py Val :=
  match optSsize (-1) size with
  | .error e => (s, .error e)
  | .ok size =>
    if s.closed then (s, .error closedErr) else
    let n : Int := (s.buf.length : Int) - s.pos
    let size : Int := if size < 0 ∨ size > n then (if n < 0 then 0 else n) else size
    let (s', b) := readBytes s size.toNat
    (s', .ok (.bytes b))

/-- `_io_BytesIO_readline_impl`, bytesio.c:552-562. -/
def readline (s : BState) (size : Option Int) : BState × Py Val :=
  match optSsize (-1) size with
  | .error e => (s, .error e)
  | .ok size =>
    if s.closed then (s, .error closedErr) else
    let (s', b) := readBytes s (scanEol s size)
    (s', .ok (.bytes b))

/-- The loop of `_io_BytesIO_readlines_impl`, bytesio.c:609-622. -/
def readlinesLoop (maxsize : Int) : BState → Nat → List Atom → Nat → BState × Py Val
  | s, _, acc, 0 => (s, .ok (.list acc.reverse))  -- unreachable with the fuel below
  | s, size, acc, fuel + 1 =>
    let n := scanEol s (-1)
    if n = 0 then (s, .ok (.list acc.reverse)) else
    let line := slice s.buf s.pos n
    let s := { s with pos := s.pos + n }
    let size := size + n
    if maxsize > 0 ∧ size ≥ maxsize then (s, .ok (.list (Atom.bytes line :: acc).reverse))
    else readlinesLoop maxsize s size (Atom.bytes line :: acc) fuel

/-- `_io_BytesIO_readlines_impl`, bytesio.c:576-628: `CHECK_CLOSED` comes
before the `PyLong_AsSsize_t` conversion of the hint. -/
def readlines (s : BState) (hint : Option Int) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  let maxsize : Py Int := match hint with
    | none => .ok (-1)
    | some v => argSsize v
  match maxsize with
  | .error e => (s, .error e)
  | .ok maxsize => readlinesLoop maxsize s 0 [] (s.buf.length + 1)

/-- `_io_BytesIO_readinto_impl`, bytesio.c:639-664, with a buffer of `n`
bytes `0xff`; returns `[count, buffer]`. -/
def readinto (s : BState) (n : Nat) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  let avail : Int := (s.buf.length : Int) - s.pos
  let len : Int := if (n : Int) > avail then avail else n
  if len < 0 then (s, .ok (.list [.int 0, .bytes (List.replicate n 255)])) else
  let data := slice s.buf s.pos len.toNat
  ({ s with pos := s.pos + len.toNat },
   .ok (.list [.int len, .bytes (data ++ List.replicate (n - len.toNat) 255)]))

/-- `write_bytes_lock_held`, bytesio.c:233-293, through `_io_BytesIO_write_impl`.
`resize_buffer_lock_held` (:181-226) raises `OverflowError` above
`PY_SSIZE_T_MAX`; for a request of exactly `PY_SSIZE_T_MAX` it computes
`alloc = size + 1 = 2**63`, which becomes negative as a `Py_ssize_t`. A
shared buffer is copied (`unshare_buffer_lock_held`, :156-176:
`PyBytes_FromStringAndSize` fails, Objects/bytesobject.c:138-145, and the
buffer survives); an unshared one is
resized with `_PyBytes_Resize` (:101-115), which on failure frees the
buffer and sets `self->buf = NULL` (Objects/bytesobject.c:3218-3277), so
the stream is closed afterwards. -/
def write (s : BState) (b : List Nat) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  if s.exports > 0 then (s, .error bufferError) else
  let len := b.length
  if len = 0 then (s, .ok (.int 0)) else
  let endpos := s.pos + len
  let lost : BState := { s with closed := true, buf := [] }
  if endpos > s.buf.length ∧ (endpos : Int) > ssizeMax then
    (s, .error (.overflowError "new buffer size too large")) else
  if endpos > s.buf.length ∧ (endpos : Int) = ssizeMax then
    if s.shared then (s, .error (.named "SystemError" "Negative size passed to PyBytes_FromStringAndSize"))
    else (lost, .error (.named "SystemError" "Objects/bytesobject.c:3227: bad argument to internal function")) else
  if endpos > s.buf.length ∧ endpos ≥ memLimit then
    -- `_PyBytes_FromSize` (bytesobject.c:115-119) rejects sizes above
    -- `PY_SSIZE_T_MAX - PyBytesObject_SIZE` (33 on LP64) before allocating
    if s.shared then
      (s, .error (if (endpos + 1 : Int) > ssizeMax - 33 then .overflowError "byte string is too large"
                  else memoryError))
    else (lost, .error memoryError) else
  ({ s with buf := writeAt s.buf s.pos b, pos := endpos, shared := false }, .ok (.int len))

/-- `_io_BytesIO_seek_impl`, bytesio.c:768-808, after Argument Clinic
converted `pos` (`Py_ssize_t`) and `whence` (`int`). -/
def seek (s : BState) (pos whence : Int) : BState × Py Val :=
  match argSsize pos with
  | .error e => (s, .error e)
  | .ok pos =>
  match argCInt whence with
  | .error e => (s, .error e)
  | .ok whence =>
  if s.closed then (s, .error closedErr) else
  if pos < 0 ∧ whence = 0 then (s, .error (.valueError s!"negative seek value {pos}")) else
  let r : Py Int :=
    if whence = 1 then
      if pos > ssizeMax - s.pos then .error (.overflowError "new position too large")
      else .ok (pos + s.pos)
    else if whence = 2 then
      if pos > ssizeMax - s.buf.length then .error (.overflowError "new position too large")
      else .ok (pos + s.buf.length)
    else if whence ≠ 0 then .error (.valueError s!"invalid whence ({whence}, should be 0, 1 or 2)")
    else .ok pos
  match r with
  | .error e => (s, .error e)
  | .ok pos =>
    let pos := if pos < 0 then 0 else pos
    ({ s with pos := pos.toNat }, .ok (.int pos))

/-- `_io_BytesIO_truncate_impl`, bytesio.c:680-711. -/
def truncate (s : BState) (size : Option Int) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  if s.exports > 0 then (s, .error bufferError) else
  let n : Py Int := match size with
    | none => .ok s.pos
    | some v => asLong v
  match n with
  | .error e => (s, .error e)
  | .ok n =>
    if n < 0 then (s, .error (.valueError s!"negative size value {n}")) else
    let s := if n < s.buf.length then { s with buf := s.buf.take n.toNat } else s
    (s, .ok (.int n))

/-- `bytesio_iternext_lock_held`, bytesio.c:713-729; `none` is `StopIteration`. -/
def next (s : BState) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  let n := scanEol s (-1)
  if n = 0 then (s, .error .stopIteration) else
  let (s', b) := readBytes s n
  (s', .ok (.bytes b))

def step (s : BState) : BOp → BState × Py Val
  | .read n | .read1 n => read s n
  | .readline n => readline s n
  | .readlines h => readlines s h
  | .readinto n => readinto s n
  | .write b => write s b
  | .seek p w => seek s p w
  | .tell => if s.closed then (s, .error closedErr) else (s, .ok (.int s.pos))
  | .truncate n => truncate s n
  | .getvalue => if s.closed then (s, .error closedErr) else (s, .ok (.bytes s.buf))
  | .getbuffer => if s.closed then (s, .error closedErr)
      -- bytesiobuf_getbuffer_lock_held (bytesio.c:1229-1247) unshares first
      else ({ s with exports := s.exports + 1, shared := false }, .ok .none)
  | .release => (bRelease s, .ok .none)
  | .close => if s.exports > 0 then (s, .error bufferError)
      else ({ s with closed := true, buf := [] }, .ok .none)
  | .next => next s
  | .closed => (s, .ok (.bool s.closed))

end C

/-! ## The pure-Python twin (`_pyio.BytesIO`) -/

namespace P

/-- `BytesIO.read`, _pyio.py:915-933 (`read1` calls it, :935-938). -/
def readRaw (s : BState) (size : Option Int) : BState × Py (List Nat) :=
  if s.closed then (s, .error (.valueError "read from closed file")) else
  let size : Int := size.getD (-1)
  let size : Int := if size < 0 then s.buf.length else size
  if s.buf.length ≤ s.pos then (s, .ok []) else
  let newpos := min s.buf.length (s.pos + size.toNat)
  ({ s with pos := newpos }, .ok (slice s.buf s.pos (newpos - s.pos)))

def read (s : BState) (size : Option Int) : BState × Py Val :=
  let (s', r) := readRaw s size
  (s', r.map .bytes)

/-- The loop of `IOBase.readline`, _pyio.py:539-553: `BytesIO` has no `peek`,
so `nreadahead()` is 1 and the loop reads one byte at a time. -/
def readlineLoop (size : Int) : BState → List Nat → Nat → BState × Py (List Nat)
  | s, _, 0 => (s, .error .modelFuel)
  | s, res, fuel + 1 =>
    if size < 0 ∨ (res.length : Int) < size then
      match readRaw s (some 1) with
      | (s', .error e) => (s', .error e)
      | (s', .ok b) =>
        if b = [] then (s', .ok res) else
        let res := res ++ b
        if res.getLast? = some 10 then (s', .ok res) else readlineLoop size s' res fuel
    else (s, .ok res)

/-- `IOBase.readline`, _pyio.py:516-554. -/
def readlineRaw (s : BState) (size : Option Int) : BState × Py (List Nat) :=
  readlineLoop (size.getD (-1)) s [] (s.buf.length - s.pos + 2)

def readline (s : BState) (size : Option Int) : BState × Py Val :=
  let (s', r) := readlineRaw s size
  (s', r.map .bytes)

/-- `IOBase.__next__`, _pyio.py:560-564. -/
def next (s : BState) : BState × Py Val :=
  match readlineRaw s none with
  | (s', .error e) => (s', .error e)
  | (s', .ok l) => if l = [] then (s', .error .stopIteration) else (s', .ok (.bytes l))

/-- `for line in self` inside `IOBase.readlines`, _pyio.py:566-580. -/
def readlinesLoop (hint : Option Int) : BState → Int → List Atom → Nat → BState × Py Val
  | s, _, _, 0 => (s, .error .modelFuel)
  | s, n, acc, fuel + 1 =>
    match readlineRaw s none with
    | (s', .error e) => (s', .error e)
    | (s', .ok l) =>
      if l = [] then (s', .ok (.list acc.reverse)) else
      let acc := Atom.bytes l :: acc
      let n := n + l.length
      match hint with
      | some h => if n ≥ h then (s', .ok (.list acc.reverse)) else readlinesLoop hint s' n acc fuel
      | none => readlinesLoop hint s' n acc fuel

/-- `IOBase.readlines`, _pyio.py:566-580: `list(self)` for `hint is None or
hint <= 0`, otherwise stop once the total length reaches `hint`. Both start
with `IOBase.__iter__` (:556-558), which checks `closed`. -/
def readlines (s : BState) (hint : Option Int) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "I/O operation on closed file.")) else
  let hint := match hint with
    | some h => if h ≤ 0 then none else some h
    | none => none
  readlinesLoop hint s 0 [] (s.buf.length - s.pos + 2)

/-- `BufferedIOBase._readinto`, _pyio.py:666-679, with `bytearray(b'\xff' * n)`. -/
def readinto (s : BState) (n : Nat) : BState × Py Val :=
  match readRaw s (some n) with
  | (s', .error e) => (s', .error e)
  | (s', .ok d) => (s', .ok (.list [.int d.length, .bytes (d ++ List.replicate (n - d.length) 255)]))

/-- `BytesIO.write`, _pyio.py:940-958. `bytearray.resize(pos)` converts `pos`
to `Py_ssize_t`, refuses to resize an exported buffer and allocates; the
slice assignment does the same when it grows the buffer. -/
def write (s : BState) (b : List Nat) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "write to closed file")) else
  let n := b.length
  if n = 0 then (s, .ok (.int 0)) else
  let r : Py BState :=
    if s.pos > s.buf.length then
      if (s.pos : Int) > ssizeMax then .error (.overflowError "Python int too large to convert to C ssize_t")
      else if s.exports > 0 then .error bufferError
      else if s.pos ≥ memLimit then .error memoryError
      else .ok { s with buf := s.buf ++ List.replicate (s.pos - s.buf.length) 0 }
    else .ok s
  match r with
  | .error e => (s, .error e)
  | .ok s =>
    if s.pos + n > s.buf.length ∧ s.exports > 0 then (s, .error bufferError) else
    if s.pos + n > s.buf.length ∧ s.pos + n ≥ memLimit then (s, .error memoryError) else
    ({ s with buf := writeAt s.buf s.pos b, pos := s.pos + n }, .ok (.int n))

/-- `BytesIO.seek`, _pyio.py:960-980. -/
def seek (s : BState) (pos whence : Int) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "seek on closed file")) else
  let r : Py Int :=
    if whence = 0 then
      if pos < 0 then .error (.valueError s!"negative seek position {pos}") else .ok pos
    else if whence = 1 then .ok (max 0 (s.pos + pos))
    else if whence = 2 then .ok (max 0 (s.buf.length + pos))
    else .error (.valueError "unsupported whence value")
  match r with
  | .error e => (s, .error e)
  | .ok p => ({ s with pos := p.toNat }, .ok (.int p))

/-- `BytesIO.truncate`, _pyio.py:987-1001: `del self._buffer[pos:]` resizes
(and so checks exports) only when it removes bytes. -/
def truncate (s : BState) (size : Option Int) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "truncate on closed file")) else
  let pos : Py Int := match size with
    | none => .ok s.pos
    | some v => if v < 0 then .error (.valueError s!"negative truncate position {v}") else .ok v
  match pos with
  | .error e => (s, .error e)
  | .ok pos =>
    if pos < s.buf.length then
      if s.exports > 0 then (s, .error bufferError)
      else ({ s with buf := s.buf.take pos.toNat }, .ok (.int pos))
    else (s, .ok (.int pos))

/-- `BytesIO.close`, _pyio.py:909-913: `bytearray.clear()` resizes (and so
checks exports) only a non-empty buffer; then `IOBase.close` sets the flag. -/
def close (s : BState) : BState × Py Val :=
  if s.buf ≠ [] ∧ s.exports > 0 then (s, .error bufferError)
  else ({ s with buf := [], closed := true }, .ok .none)

def step (s : BState) : BOp → BState × Py Val
  | .read n | .read1 n => read s n
  | .readline n => readline s n
  | .readlines h => readlines s h
  | .readinto n => readinto s n
  | .write b => write s b
  | .seek p w => seek s p w
  | .tell => if s.closed then (s, .error (.valueError "tell on closed file")) else (s, .ok (.int s.pos))
  | .truncate n => truncate s n
  | .getvalue => if s.closed then (s, .error (.valueError "getvalue on closed file"))
      else (s, .ok (.bytes s.buf))
  | .getbuffer => if s.closed then (s, .error (.valueError "getbuffer on closed file"))
      else ({ s with exports := s.exports + 1 }, .ok .none)
  | .release => (bRelease s, .ok .none)
  | .close => close s
  | .next => next s
  | .closed => (s, .ok (.bool s.closed))

end P

/-- Run a sequence of operations, collecting every result. -/
def runOps {σ ω : Type} (step : σ → ω → σ × Py Val) : σ → List ω → σ × List (Py Val)
  | s, [] => (s, [])
  | s, o :: os =>
    let (s', r) := step s o
    let (s'', rs) := runOps step s' os
    (s'', r :: rs)

def runBC (init : List Nat) (ops : List BOp) : List (Py Val) := (runOps C.step (bInit init) ops).2
def runBPy (init : List Nat) (ops : List BOp) : List (Py Val) := (runOps P.step (bInit init) ops).2

end PyLean.PyIO
