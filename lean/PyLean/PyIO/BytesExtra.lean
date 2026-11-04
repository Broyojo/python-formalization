import PyLean.PyIO.BytesDocs
import PyLean.Binary64.Float

/-!
The remaining `BytesIO` methods of both twins: the inquiries, `flush`,
`isatty`, `writelines`, and pickling (`bytesio.c`, `Lib/_pyio.py`), and the
arguments that are not `None` or an `int`: an object with or without `__index__` for
`read`, `readline` and `seek`, a float hint for `readlines`, and a `str` or a
non-buffer for `write`.
-/

namespace PyLean.PyIO

open PyLean

/-- `readable`..`isatty` take no argument; `writelines ls` passes a list of
bytes; `getstate` is `__getstate__()` (the dict slot is `None`);
`setstate b p` is `__setstate__((b, p, None))` in C and
`__setstate__({'_buffer': bytearray(b), '_pos': p})` in Python, for `p >= 0`;
`readintoSelf off n` is `readinto` of `getbuffer()[off:off+n]`, a view of the
stream's own buffer; `reinit b` calls `__init__` again, with `b` or no argument;
`reinitObj b` calls it with `bytearray(b)`, or with the int 1 for `none`;
`truncateObj a` is `truncate` of an object that is not an `int`; `readObj a`,
`readlineObj a` and `seekObj a w` pass such an object as the size or position;
`readlinesFloat x` passes the float `x` as the hint; `writeObj w` passes `w`. -/
inductive XOp where
  | readable | writable | seekable | flush | isatty
  | writelines (ls : List (List Nat))
  | getstate
  | setstate (b : List Nat) (pos : Int)
  | readintoSelf (off n : Nat)
  | reinit (b : Option (List Nat))
  | reinitObj (b : Option (List Nat))
  | truncateObj (a : TArg)
  | readObj (a : TArg)
  | readlineObj (a : TArg)
  | seekObj (a : TArg) (whence : Int)
  | readlinesFloat (x : Binary64.F64)
  | writeObj (w : WArg)
  deriving Repr, DecidableEq, Inhabited

namespace C

/-- `_io_BytesIO_writelines_impl`, bytesio.c:850-876: `CHECK_CLOSED`, then
`write_bytes_lock_held` per item, stopping at the first failure. -/
def writelinesLoop : BState → List (List Nat) → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, l :: ls =>
    match write s l with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => writelinesLoop s' ls

/-- `bytesio_setstate_lock_held`, bytesio.c:948-1023, for a 3-tuple: exports
are checked, the buffer is reset and `state[0]` is written, then the position
is converted and range-checked. -/
def setstate (s : BState) (b : List Nat) (pos : Int) : BState × Py Val :=
  if s.exports > 0 then (s, .error bufferError) else
  match write { s with buf := [], pos := 0 } b with
  | (s', .error e) => (s', .error e)
  | (s', .ok _) =>
    match argSsize pos with
    | .error e => (s', .error e)
    | .ok p =>
      if p < 0 then (s', .error (.valueError "position value cannot be negative"))
      else ({ s' with pos := p.toNat }, .ok .none)

/-- `buf` overwritten from `off` by `d`, which fits. -/
def overwrite (buf : List Nat) (off : Nat) (d : List Nat) : List Nat :=
  if d = [] then buf else writeAt buf off d

/-- `readinto` of `getbuffer()[off:off+n]`: taking the view may unshare the buffer
(`takeView`), then `_io_BytesIO_readinto_impl` (:652-677) copies with `memmove` from
the old contents into the part of the view that exists. The view is released
afterwards, so only the sharing outlasts it. -/
def readintoSelf (s : BState) (off n : Nat) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  let s := { s with shared := (takeView s).shared }
  let w : Nat := min n (s.buf.length - off)
  let avail : Int := (s.buf.length : Int) - s.pos
  let len : Int := if (w : Int) > avail then avail else w
  if len < 0 then (s, .ok (.int 0)) else
  ({ s with buf := overwrite s.buf off (slice s.buf s.pos len.toNat), pos := s.pos + len.toNat }, .ok (.int len))

/-- `_io_BytesIO___init___impl`, bytesio.c:1084-1114, called again: exports are
checked before anything changes (:1087-1091). An `initvalue` replaces the buffer,
which also reopens a closed stream; without one `self->buf` stays, so a closed
stream stays closed. -/
def reinit (s : BState) (b : Option (List Nat)) : BState × Py Val :=
  if s.exports > 0 then (s, .error bufferError) else
  match b with
  | some b => ({ s with buf := b, pos := 0, closed := false, shared := decide (b.length ≤ 1) }, .ok .none)
  | none => ({ s with buf := [], pos := 0 }, .ok .none)

/-- `__init__` with anything but an exact `bytes`: the size and position are reset
(:1094-1095) before `_io_BytesIO_write_impl` (:1105) can fail, so a failure leaves
an empty stream, and a closed stream raises even for an empty value. -/
def reinitObj (s : BState) (b : Option (List Nat)) : BState × Py Val :=
  if s.exports > 0 then (s, .error bufferError) else
  let s := { s with buf := [], pos := 0 }
  match b with
  | none => (s, .error (.typeError "a bytes-like object is required, not 'int'"))
  | some d =>
    match write s d with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => ({ s' with pos := 0 }, .ok .none)

/-- One action of `__index__`; an exception it raises is swallowed. -/
def hookStep (s : BState) : Hook → BState
  | .close => (step s .close).1
  | .getbuffer => (step s .getbuffer).1
  | .tell => s
  | .seekAbs p => (step s (.seek p 0)).1
  | .seekCur => (step s (.seek 0 1)).1
  | .write b => (step s (.write b)).1

/-- `_io_BytesIO_truncate_impl`, bytesio.c:692-727, for an object: `PyLong_AsLong`
(:704) calls `__index__`, which can close the stream or take a view, so
`CHECK_CLOSED` and `CHECK_EXPORTS` run again (:713-714) before the buffer is used. -/
def truncateObj (s : BState) (a : TArg) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  if s.exports > 0 then (s, .error bufferError) else
  match a with
  | .noIndex t _ => (s, .error (notIndexable t))
  | .index hook r =>
    let s := hook.foldl hookStep s
    match r with
    | none => (s, .error boomErr)
    | some v =>
      match asLong v with
      | .error e => (s, .error e)
      | .ok n =>
        if n < 0 then (s, .error (.valueError s!"negative size value {n}")) else
        if s.closed then (s, .error closedErr) else
        if s.exports > 0 then (s, .error bufferError) else
        let s := if n < s.buf.length then { s with buf := s.buf.take n.toNat } else s
        (s, .ok (.int n))

/-- `_Py_convert_optional_to_ssize_t`, Python/modsupport.c:15-35, on an object that is
not `None` (the converter of `read`, `read1` and `readline`, clinic/bytesio.c.h:239,
:278, :318): an object with no `__index__` is refused by type name (:27-31); otherwise
`PyNumber_AsSsize_t(obj, PyExc_OverflowError)` (:21-25) calls `__index__`, whose actions
on the stream run first, and refuses a result outside `Py_ssize_t`. Returns the state
`__index__` left. -/
def convOptSsize (s : BState) (a : TArg) : BState × Py Int :=
  match a with
  | .noIndex t _ => (s, .error (.typeError s!"argument should be integer or None, not '{t}'"))
  | .index hook r =>
    let s := hook.foldl hookStep s
    match r with
    | none => (s, .error boomErr)
    | some v =>
      -- `PyNumber_AsSsize_t` (Objects/abstract.c:1505-1510) names the argument's type, not `int`
      if InSsize v then (s, .ok v)
      else (s, .error (.overflowError s!"cannot fit '{indexTypeName}' into an index-sized integer"))

/-- `read(a)`: the clinic conversion (clinic/bytesio.c.h `_io_BytesIO_read`), then
`_io_BytesIO_read_impl` (bytesio.c:509-525), whose `CHECK_CLOSED` (:514) sees what
`__index__` did. -/
def readObj (s : BState) (a : TArg) : BState × Py Val :=
  match convOptSsize s a with
  | (s, .error e) => (s, .error e)
  | (s, .ok v) => read s (some v)

/-- `readline(a)`: the same converter, then `_io_BytesIO_readline_impl` (:561-571). -/
def readlineObj (s : BState) (a : TArg) : BState × Py Val :=
  match convOptSsize s a with
  | (s, .error e) => (s, .error e)
  | (s, .ok v) => readline s (some v)

/-- `seek(a, whence)`: clinic/bytesio.c.h:471-482 calls `_PyNumber_Index` (which runs
`__index__`, or refuses an object without it, Objects/abstract.c:1410-1424) and
`PyLong_AsSsize_t`, then converts `whence` (:486) and runs `_io_BytesIO_seek_impl`
(bytesio.c:774-815), whose `CHECK_CLOSED` (:777) comes after both. -/
def seekObj (s : BState) (a : TArg) (whence : Int) : BState × Py Val :=
  match a with
  | .noIndex t _ => (s, .error (notIndexable t))
  | .index hook r =>
    let s := hook.foldl hookStep s
    match r with
    | none => (s, .error boomErr)
    | some v => seek s v whence

/-- `readlines(x)` for a float `x`: `CHECK_CLOSED` (bytesio.c:594), then a hint that is
neither an `int` nor `None` is refused by type name (:605-608). -/
def readlinesFloat (s : BState) : BState × Py Val :=
  if s.closed then (s, .error closedErr)
  else (s, .error (.typeError "integer argument expected, got 'float'"))

/-- `write(w)` for a `str` or an object without the buffer interface:
`write_bytes_lock_held` (bytesio.c:236-244) asks for the buffer before
`check_closed` (:246), and `PyObject_GetBuffer` refuses it (Objects/abstract.c:447-453). -/
def writeObj (s : BState) (w : WArg) : BState × Py Val :=
  (s, .error (.typeError s!"a bytes-like object is required, not '{w.typeName}'"))

/-- bytesio.c:323-328, :338-343, :353-358, :368-373, :445-450, :850-876,
:938-945, :948-1023. -/
def xstep (s : BState) : XOp → BState × Py Val
  | .readable | .writable | .seekable =>
    if s.closed then (s, .error closedErr) else (s, .ok (.bool true))
  | .flush => if s.closed then (s, .error closedErr) else (s, .ok .none)
  | .isatty => if s.closed then (s, .error closedErr) else (s, .ok (.bool false))
  | .writelines ls => if s.closed then (s, .error closedErr) else writelinesLoop s ls
  | .getstate =>
    if s.closed then (s, .error closedErr)
    else (s, .ok (.list [.bytes s.buf, .int s.pos, .none]))
  | .setstate b p => setstate s b p
  | .readintoSelf off n => readintoSelf s off n
  | .reinit b => reinit s b
  | .reinitObj b => reinitObj s b
  | .truncateObj a => truncateObj s a
  | .readObj a => readObj s a
  | .readlineObj a => readlineObj s a
  | .seekObj a w => seekObj s a w
  | .readlinesFloat _ => readlinesFloat s
  | .writeObj w => writeObj s w

end C

namespace P

def closedDot : PyExc := .valueError "I/O operation on closed file."

/-- `for line in lines: self.write(line)`, _pyio.py:589-590. -/
def writelinesLoop : BState → List (List Nat) → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, l :: ls =>
    match write s l with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => writelinesLoop s' ls

/-- `readinto` of `getbuffer()[off:off+n]`: `BufferedIOBase._readinto`
(_pyio.py:727-740) reads a copy and assigns it into the view. -/
def readintoSelf (s : BState) (off n : Nat) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "getbuffer on closed file")) else
  match readRaw s (some (min n (s.buf.length - off) : Nat)) with
  | (s', .error e) => (s', .error e)
  | (s', .ok d) => ({ s' with buf := C.overwrite s'.buf off d }, .ok (.int d.length))

/-- `BytesIO.__init__`, _pyio.py:884-894, called again: it replaces `_buffer`, so a
view of the old buffer no longer counts, and `IOBase`'s closed flag stays. -/
def reinit (s : BState) (b : Option (List Nat)) : BState × Py Val :=
  ({ s with buf := b.getD [], pos := 0, exports := 0 }, .ok .none)

/-- `BytesIO.__setstate__`, _pyio.py:904-906: the dict replaces `_buffer` and `_pos`
with no check, on an open or a closed stream. -/
def setstate (s : BState) (b : List Nat) (pos : Int) : BState × Py Val :=
  ({ s with buf := b, pos := pos.toNat, exports := 0 }, .ok .none)

/-- What the thread would do forever: `__index__` runs under `self._lock`, which is
not re-entrant. -/
def deadlock : PyExc := .named "Deadlock" ""

/-- One action of `__index__` while `self._lock` is held: the new state, and whether
the action blocks on the lock. An exception it raises first is swallowed. `tell`,
`getbuffer`, `close` and `seek(p)` do not take the lock (_pyio.py:915-925, :982-987,
:998-1001); `seek(0, 1)` (:988-990) and a non-empty `write` (:966) do. -/
def hookStep (s : BState) : Hook → BState × Bool
  | .close => ((close s).1, false)
  | .getbuffer => ((step s .getbuffer).1, false)
  | .tell => (s, false)
  | .seekAbs p => ((seek s p 0).1, false)
  | .seekCur => (s, !s.closed)
  | .write b => (s, !s.closed && !b.isEmpty)

/-- Run the actions until one blocks. -/
def runHooks (s : BState) : List Hook → BState × Bool
  | [] => (s, false)
  | h :: t =>
    match hookStep s h with
    | (s, true) => (s, true)
    | (s, false) => runHooks s t

/-- `BytesIO.truncate`, _pyio.py:1003-1020, for an object: `pos.__index__()` runs
with `self._lock` held, and nothing re-checks `closed` afterwards. -/
def truncateObj (s : BState) (a : TArg) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "truncate on closed file")) else
  match a with
  | .noIndex _ r => (s, .error (.typeError s!"{r} is not an integer"))
  | .index hook r =>
    match runHooks s hook with
    | (s, true) => (s, .error deadlock)
    | (s, false) =>
      match r with
      | none => (s, .error boomErr)
      | some v =>
        if v < 0 then (s, .error (.valueError s!"negative truncate position {v}")) else
        if v < s.buf.length then
          if s.exports > 0 then (s, .error bufferError)
          else ({ s with buf := s.buf.take v.toNat }, .ok (.int v))
        else (s, .ok (.int v))

/-- One action of an `__index__` that `read`, `readline` or `seek` calls: no lock is held
then (`read` calls it at _pyio.py:938, before `with self._lock` at :940; `seek` at :983
and `IOBase.readline` at :544 hold none), so each action is the method itself. An
exception it raises is swallowed. -/
def hookStepFree (s : BState) : Hook → BState
  | .close => (close s).1
  | .getbuffer => (step s .getbuffer).1
  | .tell => s
  | .seekAbs p => (seek s p 0).1
  | .seekCur => (seek s 0 1).1
  | .write b => (write s b).1

/-- The body of `BytesIO.read` once `size` is an int, _pyio.py:940-948: nothing here
looks at `closed`. -/
def readBody (s : BState) (size : Int) : BState × Py (List Nat) :=
  let size : Int := if size < 0 then s.buf.length else size
  if s.buf.length ≤ s.pos then (s, .ok []) else
  let newpos := min s.buf.length (s.pos + size.toNat)
  ({ s with pos := newpos }, .ok (slice s.buf s.pos (newpos - s.pos)))

/-- On an open stream `read(v)` of an int is the body: `readRaw` and `readBody` are the
same code. -/
theorem readRaw_eq_readBody (s : BState) (v : Int) (h : s.closed = false) :
    readRaw s (some v) = readBody s v := by
  simp [readRaw, readBody, h]

/-- `BytesIO.read(a)` for an object `a`, _pyio.py:927-948: `closed` is checked first
(:928-929), then `size.__index__` is looked up (:933-936, `TypeError(f"{size!r} is not an
integer")` without it) and called (:938), and the body runs with no second look at
`closed`. -/
def readObj (s : BState) (a : TArg) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "read from closed file")) else
  match a with
  | .noIndex _ r => (s, .error (.typeError s!"{r} is not an integer"))
  | .index hook r =>
    let s := hook.foldl hookStepFree s
    match r with
    | none => (s, .error boomErr)
    | some v =>
      let (s, b) := readBody s v
      (s, b.map .bytes)

/-- The body of `BytesIO.seek` once `pos` is an int, _pyio.py:984-996: nothing here
looks at `closed`. -/
def seekBody (s : BState) (pos whence : Int) : BState × Py Val :=
  let r : Py Int :=
    if whence = 0 then
      if pos < 0 then .error (.valueError s!"negative seek position {pos}") else .ok pos
    else if whence = 1 then .ok (max 0 (s.pos + pos))
    else if whence = 2 then .ok (max 0 (s.buf.length + pos))
    else .error (.valueError "unsupported whence value")
  match r with
  | .error e => (s, .error e)
  | .ok p => ({ s with pos := p.toNat }, .ok (.int p))

theorem seek_eq_seekBody (s : BState) (p w : Int) (h : s.closed = false) :
    seek s p w = seekBody s p w := by
  have h' : ¬ s.closed = true := by simp [h]
  unfold seek; rw [if_neg h']; rfl

/-- `BytesIO.seek(a, whence)` for an object `a`, _pyio.py:975-996: `closed` first
(:976-977), then `pos.__index__` looked up (:978-981) and called (:983), then the body,
which sets `_pos` and returns it whether or not `__index__` closed the stream. -/
def seekObj (s : BState) (a : TArg) (whence : Int) : BState × Py Val :=
  if s.closed then (s, .error (.valueError "seek on closed file")) else
  match a with
  | .noIndex _ r => (s, .error (.typeError s!"{r} is not an integer"))
  | .index hook r =>
    let s := hook.foldl hookStepFree s
    match r with
    | none => (s, .error boomErr)
    | some v => seekBody s v whence

/-- `IOBase.readline(a)` for an object `a` on a `BytesIO`, _pyio.py:513-553: `BytesIO` has
no `peek`, so `nreadahead` is 1 (:533-535); `size.__index__` is looked up and called
(:539-544) before the loop, whose `read(1)` calls (:547) check `closed`. -/
def readlineObj (s : BState) (a : TArg) : BState × Py Val :=
  match a with
  | .noIndex _ r => (s, .error (.typeError s!"{r} is not an integer"))
  | .index hook r =>
    let s := hook.foldl hookStepFree s
    match r with
    | none => (s, .error boomErr)
    | some v => readline s (some v)

/-- `hint <= n` for a float `hint` and an int `n`: `float_richcompare`
(Objects/floatobject.c:372-532) with `Py_LE`. `n >= hint` is the same call: `int.__ge__`
returns `NotImplemented` for a float and Python tries the reflected `hint.__le__(n)`. -/
def floatLe (x : Binary64.F64) (n : Int) : Bool :=
  Binary64.float_richcompare x (.int n) .le == some true

/-- The `for line in self` loop of `IOBase.readlines` (_pyio.py:576-581) with a hint
compared by `stop`: append, add the length, stop once `stop n` (`n >= hint`). -/
def readlinesStopLoop (stop : Int → Bool) : BState → Int → List Atom → Nat → BState × Py Val
  | s, _, _, 0 => (s, .error .modelFuel)
  | s, n, acc, fuel + 1 =>
    match readlineRaw s none with
    | (s', .error e) => (s', .error e)
    | (s', .ok l) =>
      if l = [] then (s', .ok (.list acc.reverse)) else
      let acc := Atom.bytes l :: acc
      let n := n + l.length
      if stop n then (s', .ok (.list acc.reverse)) else readlinesStopLoop stop s' n acc fuel

/-- `IOBase.readlines(x)` for a float `x`, _pyio.py:565-581: `hint <= 0` (:572) is
compared before `__iter__` (:555-557) checks `closed`; then `list(self)` or the loop. -/
def readlinesFloat (s : BState) (x : Binary64.F64) : BState × Py Val :=
  if floatLe x 0 then readlines s none else
  if s.closed then (s, .error (.valueError "I/O operation on closed file.")) else
  readlinesStopLoop (floatLe x) s 0 [] (s.buf.length - s.pos + 2)

/-- `BytesIO.write(w)` for a `str` or a non-buffer, _pyio.py:955-960: a `str` is refused
(:956-957), and `memoryview(b)` (:958) refuses an object without the buffer interface
(Objects/memoryobject.c:821-823), both before `closed` is checked (:959-960). -/
def writeObj (s : BState) (w : WArg) : BState × Py Val :=
  match w with
  | .str _ => (s, .error (.typeError "can't write str to binary stream"))
  | .obj t => (s, .error (.typeError s!"memoryview: a bytes-like object is required, not '{t}'"))

/-- `BytesIO.readable/writable/seekable` (_pyio.py:1022-1035), `IOBase.flush`
(:380-385), `IOBase.isatty` (:503-509), `IOBase.writelines` (:583-591),
`BytesIO.__getstate__` (:896-902, the instance dict without `_lock`, as
`[buffer, pos]`). -/
def xstep (s : BState) : XOp → BState × Py Val
  | .readable | .writable | .seekable =>
    if s.closed then (s, .error closedDot) else (s, .ok (.bool true))
  | .flush => if s.closed then (s, .error closedDot) else (s, .ok .none)
  | .isatty => if s.closed then (s, .error closedDot) else (s, .ok (.bool false))
  | .writelines ls => if s.closed then (s, .error closedDot) else writelinesLoop s ls
  | .getstate =>
    if s.closed then (s, .error (.valueError "__getstate__ on closed file"))
    else (s, .ok (.list [.bytes s.buf, .int s.pos]))
  | .setstate b p => setstate s b p
  | .readintoSelf off n => readintoSelf s off n
  | .reinit b => reinit s b
  | .reinitObj (some d) => reinit s (some d)
  -- `buf += initial_bytes` fails before `_buffer` is replaced
  | .reinitObj none => (s, .error (.typeError "can't concat int to bytearray"))
  | .truncateObj a => truncateObj s a
  | .readObj a => readObj s a
  | .readlineObj a => readlineObj s a
  | .seekObj a w => seekObj s a w
  | .readlinesFloat x => readlinesFloat s x
  | .writeObj w => writeObj s w

end P

def stepAnyC (s : BState) : BOp ⊕ XOp → BState × Py Val
  | .inl o => C.step s o
  | .inr o => C.xstep s o

def stepAnyP (s : BState) : BOp ⊕ XOp → BState × Py Val
  | .inl o => P.step s o
  | .inr o => P.xstep s o

/-- On an open BytesIO `readable`, `writable`, `seekable` are true, `flush`
returns `None` and `isatty` false; on a closed one each raises `ValueError`
with the message of `IOBase._checkClosed` (both twins, every state). -/
def BytesIOInquiries : Prop := ∀ (s : BState) (o : XOp),
  (o = .readable ∨ o = .writable ∨ o = .seekable ∨ o = .flush ∨ o = .isatty) →
  (if s.closed then (C.xstep s o).2 = .error (.valueError "I/O operation on closed file.") ∧
      (P.xstep s o).2 = .error (.valueError "I/O operation on closed file.")
    else (C.xstep s o).2 = (P.xstep s o).2 ∧
      (C.xstep s o).2 = (if o = .flush then .ok .none else .ok (.bool (o ≠ .isatty)))) ∧
  (C.xstep s o).1 = s ∧ (P.xstep s o).1 = s

theorem bytesIOInquiries_proven : BytesIOInquiries := by
  intro s o ho
  rcases ho with rfl | rfl | rfl | rfl | rfl <;> cases hc : s.closed <;>
    simp [C.xstep, P.xstep, hc, C.closedErr, P.closedDot]

/-- `writelines(ls)` on an open BytesIO is `write(l)` for each `l` in turn,
stopping at the first failure ("equivalent to calling write() for each
element", bytesio.c:846-847): same final state and outcome as the run of
`write` operations (both twins). -/
def BytesIOWritelines : Prop := ∀ (s : BState) (ls : List (List Nat)), s.closed = false →
  ∃ (rs : List (Py Val)),
    (runOps C.step s (ls.map .write)).2 = rs ∧
    ((∀ r ∈ rs, r.toBool = true) →
      (C.xstep s (.writelines ls)).1 = (runOps C.step s (ls.map .write)).1 ∧
      (C.xstep s (.writelines ls)).2 = .ok .none) ∧
  ((∀ r ∈ (runOps P.step s (ls.map .write)).2, r.toBool = true) →
    (P.xstep s (.writelines ls)).1 = (runOps P.step s (ls.map .write)).1 ∧
    (P.xstep s (.writelines ls)).2 = .ok .none)

theorem C_writelines_ok : ∀ (ls : List (List Nat)) (s : BState),
    (∀ r ∈ (runOps C.step s (ls.map .write)).2, r.toBool = true) →
    C.writelinesLoop s ls = ((runOps C.step s (ls.map .write)).1, .ok .none) := by
  intro ls
  induction ls with
  | nil => intro s _; simp [C.writelinesLoop, runOps]
  | cons l ls ih =>
    intro s h
    simp only [List.map_cons, runOps, C.step] at h ⊢
    simp only [C.writelinesLoop]
    rcases hw : C.write s l with ⟨s', r⟩
    rw [hw] at h
    cases r with
    | error e => simp [Except.toBool] at h
    | ok v =>
      simp only at h ⊢
      exact ih s' (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem P_writelines_ok : ∀ (ls : List (List Nat)) (s : BState),
    (∀ r ∈ (runOps P.step s (ls.map .write)).2, r.toBool = true) →
    P.writelinesLoop s ls = ((runOps P.step s (ls.map .write)).1, .ok .none) := by
  intro ls
  induction ls with
  | nil => intro s _; simp [P.writelinesLoop, runOps]
  | cons l ls ih =>
    intro s h
    simp only [List.map_cons, runOps, P.step] at h ⊢
    simp only [P.writelinesLoop]
    rcases hw : P.write s l with ⟨s', r⟩
    rw [hw] at h
    cases r with
    | error e => simp [Except.toBool] at h
    | ok v =>
      simp only at h ⊢
      exact ih s' (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem bytesIOWritelines_proven : BytesIOWritelines := by
  intro s ls hc
  refine ⟨_, rfl, ?_, ?_⟩
  · intro h; simp only [C.xstep, hc, Bool.false_eq_true, ite_false]; rw [C_writelines_ok ls s h]; simp
  · intro h; simp only [P.xstep, hc, Bool.false_eq_true, ite_false]; rw [P_writelines_ok ls s h]; simp

/-- Pickling round trip: the state of an open BytesIO, restored into any open
BytesIO without exports, reproduces contents and position (C). Hypotheses: the
position fits `Py_ssize_t` (a type invariant of the C object) and the contents
are below the allocation bound. `_pyio`'s `__getstate__` and `__setstate__` round
trip on every open stream, with `_lock` left out of the state and a fresh one made. -/
def BytesIOPickleRoundTrip : Prop := ∀ (s t : BState),
  s.closed = false → t.closed = false → t.exports = 0 → (s.pos : Int) ≤ ssizeMax → s.buf.length < memLimit →
  (C.xstep s .getstate).2 = .ok (.list [.bytes s.buf, .int s.pos, .none]) ∧
  (C.xstep t (.setstate s.buf s.pos)).2 = .ok .none ∧
  (C.xstep t (.setstate s.buf s.pos)).1.buf = s.buf ∧ (C.xstep t (.setstate s.buf s.pos)).1.pos = s.pos ∧
  (P.xstep s .getstate).2 = .ok (.list [.bytes s.buf, .int s.pos]) ∧
  (P.xstep t (.setstate s.buf s.pos)).2 = .ok .none ∧
  (P.xstep t (.setstate s.buf s.pos)).1.buf = s.buf ∧ (P.xstep t (.setstate s.buf s.pos)).1.pos = s.pos

theorem bytesIOPickleRoundTrip_proven : BytesIOPickleRoundTrip := by
  intro s t hs ht he hp hm
  have hmax : memLimit ≤ ssizeMax := by decide
  have hz : ssizeMin ≤ 0 := by decide
  have hsz : InSsize (s.pos : Int) := ⟨by omega, hp⟩
  have hw : C.write { t with buf := [], pos := 0 } s.buf =
      (if s.buf = [] then { t with buf := [], pos := 0 }
       else { t with buf := s.buf, pos := s.buf.length, shared := false }, .ok (.int s.buf.length)) := by
    obtain ⟨tb, tp, tc, te, ts⟩ := t
    simp only at ht he; subst ht he
    by_cases hb : s.buf = []
    · simp [C.write, hb]
    · have hl : s.buf.length ≠ 0 := fun e => hb (List.eq_nil_of_length_eq_zero e)
      have c1 : ¬ ((0 + s.buf.length : Nat) > 0 ∧ (((0 + s.buf.length : Nat)) : Int) > ssizeMax) := by omega
      have c2 : ¬ ((0 + s.buf.length : Nat) > 0 ∧ (((0 + s.buf.length : Nat)) : Int) = ssizeMax) := by omega
      have c3 : ¬ ((0 + s.buf.length : Nat) > 0 ∧ (0 + s.buf.length : Nat) ≥ memLimit) := by omega
      simp only [C.write, Bool.false_eq_true, ite_false, Nat.lt_irrefl, gt_iff_lt, hl, List.length_nil]
      simp only [gt_iff_lt] at c1 c2 c3
      simp only [c1, c2, c3, ite_false, hb]
      simp [writeAt]
  have hpn : ¬ (s.pos : Int) < 0 := by omega
  rw [he] at hw
  have hP : (P.xstep s .getstate).2 = .ok (.list [.bytes s.buf, .int s.pos]) ∧
      (P.xstep t (.setstate s.buf s.pos)).2 = .ok .none ∧
      (P.xstep t (.setstate s.buf s.pos)).1.buf = s.buf ∧ (P.xstep t (.setstate s.buf s.pos)).1.pos = s.pos := by
    simp [P.xstep, P.setstate, hs]
  have hC : (C.xstep t (.setstate s.buf s.pos)).2 = .ok .none ∧
      (C.xstep t (.setstate s.buf s.pos)).1.buf = s.buf ∧ (C.xstep t (.setstate s.buf s.pos)).1.pos = s.pos := by
    simp only [C.xstep, C.setstate, he, Nat.lt_irrefl, gt_iff_lt, Nat.not_lt_zero, ite_false, hw, argSsize, hsz, ite_true, hpn]
    by_cases hb : s.buf = [] <;> simp [hb] at hw ⊢ <;> simp [hw]
  exact ⟨by simp [C.xstep, hs], hC.1, hC.2.1, hC.2.2, hP⟩

/-- `getbuffer()` followed by releasing the view restores the export count, so
a resize is possible again (C `bytesiobuf_getbuffer`/`releasebuffer`, Python
`memoryview` over the `bytearray`); position and contents do not change. -/
def BytesIOReleaseExports : Prop := ∀ (s : BState), s.closed = false →
  (C.step (C.step s .getbuffer).1 .release).1.exports = s.exports ∧
  (C.step (C.step s .getbuffer).1 .release).1.buf = s.buf ∧
  (C.step (C.step s .getbuffer).1 .release).1.pos = s.pos ∧
  (C.step s .getbuffer).1.exports > 0 ∧
  (P.step (P.step s .getbuffer).1 .release).1 = s

theorem bytesIOReleaseExports_proven : BytesIOReleaseExports := by
  intro s hc
  obtain ⟨buf, pos, cl, ex, sh⟩ := s
  simp only at hc; subst hc
  simp [C.step, P.step, bRelease, C.takeView]

end PyLean.PyIO
