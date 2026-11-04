import PyLean.PyIO.BytesExtra

/-!
Python code that `io.BytesIO` and `_pyio.BytesIO` call while they run: the `__buffer__`
of a `write()` or `__init__()` argument, and the iterator of `writelines()`. Each may
raise or act on the stream itself (close it, take a view, seek, write). Also the
remaining branches of `seek` and `__init__` (CPython 3.15.2).

The callbacks are the harness's (difftest/pyio_callback_diff.py): class `Buf`, whose
`__buffer__` runs a list of `Hook` actions on the stream, swallowing their exceptions,
then returns `memoryview(bytes(d))` or raises `ValueError('boom')`; and an iterator whose
`__next__` runs actions and then returns an item or raises `KeyError('k')`.
-/

namespace PyLean.PyIO

open PyLean

/-- A `write()` or `__init__()` argument. -/
inductive WItem where
  /-- A `bytes` object. -/
  | data (d : List Nat)
  /-- A `Buf`: `__buffer__` runs `hook`, then returns a view of `d`, or raises
  `ValueError('boom')` for `none`. -/
  | hooked (hook : List Hook) (r : Option (List Nat))
  /-- A `str`, or an object of the named type without the buffer interface. -/
  | bad (w : WArg)
  deriving Repr, DecidableEq, Inhabited

/-- One `__next__` of the iterator given to `writelines`: run `hook`, then return the
item or raise `KeyError('k')`. -/
inductive IStep where
  | item (hook : List Hook) (x : WItem)
  | raise (hook : List Hook)
  deriving Repr, DecidableEq, Inhabited

/-- The argument of `writelines`: an iterator, or an object of the named type that is not
iterable. -/
inductive WLArg where
  | iter (steps : List IStep)
  | notIter (typeName : String)
  deriving Repr, DecidableEq, Inhabited

inductive CBOp where
  | writeItem (x : WItem)
  | writelinesIt (a : WLArg)
  | reinitItem (x : WItem)
  deriving Repr, DecidableEq, Inhabited

def keyErr : PyExc := .keyError "'k'"

/-- `type(x).__name__` of the harness's buffer class. -/
def bufTypeName : String := "Buf"

def notIterable (t : String) : PyExc := .typeError s!"'{t}' object is not iterable"

namespace C

/-- `write_bytes_lock_held`, bytesio.c:236-297, for any argument: `PyObject_GetBuffer`
(:242) runs first, so a `__buffer__` acts on the stream (each action is the method itself,
`hookStep`) and may raise before anything is checked; `check_closed` and `check_exports`
(:246) and the reads of `pos` (:257) then see the state it left. A `str` or a non-buffer
is refused by `PyObject_GetBuffer` (`writeObj`). -/
def writeItem (s : BState) : WItem → BState × Py Val
  | .data d => write s d
  | .hooked hook r =>
    let s := hook.foldl hookStep s
    match r with
    | none => (s, .error boomErr)
    | some d => write s d
  | .bad w => writeObj s w

/-- The loop of `_io_BytesIO_writelines_impl`, bytesio.c:861-873: `PyIO_Next` runs
`__next__` (which may act on the stream), an exception from it ends the loop and is
returned (:871-873), otherwise `write_bytes_lock_held` writes the item (:862) and a
failure is returned at once (:864-867). -/
def writelinesSteps : BState → List IStep → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, .raise hook :: _ => (hook.foldl hookStep s, .error keyErr)
  | s, .item hook x :: rest =>
    match writeItem (hook.foldl hookStep s) x with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => writelinesSteps s' rest

/-- `_io_BytesIO_writelines_impl`, bytesio.c:850-876: `CHECK_CLOSED` (:855), then
`PyObject_GetIter` (:857-859), whose failure is `TypeError("'T' object is not
iterable")` (Objects/abstract.c `PyObject_GetIter`), then the loop. -/
def writelinesIt (s : BState) (a : WLArg) : BState × Py Val :=
  if s.closed then (s, .error closedErr) else
  match a with
  | .notIter t => (s, .error (notIterable t))
  | .iter steps => writelinesSteps s steps

/-- `_io_BytesIO___init___impl`, bytesio.c:1084-1114: the exports refusal (:1087-1091),
the reset of `string_size` and `pos` (:1094-1095), then an exact `bytes` is stored
(:1097-1101) and anything else goes through `_io_BytesIO_write_impl` (:1105), whose
`__buffer__` runs on the reset stream, after which `pos` is set to 0 again (:1109). -/
def reinitItem (s : BState) (x : WItem) : BState × Py Val :=
  match x with
  | .data d => reinit s (some d)
  -- `initvalue != Py_None` (:1097): `None` is no initial value
  | .bad (.obj "NoneType") => reinit s none
  | x =>
    if s.exports > 0 then (s, .error bufferError) else
    match writeItem { s with buf := [], pos := 0 } x with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => ({ s' with pos := 0 }, .ok .none)

def cbstep (s : BState) : CBOp → BState × Py Val
  | .writeItem x => writeItem s x
  | .writelinesIt a => writelinesIt s a
  | .reinitItem x => reinitItem s x

end C

namespace P

/-- `BytesIO.write`, _pyio.py:955-973, for any argument: a `str` is refused first
(:956-957), then `memoryview(b)` (:958) runs `__buffer__` (no lock is held, so each
action is the method itself, `hookStepFree`) and propagates its exception; only then is
`closed` checked (:959-960) and `_pos` read (:967). -/
def writeItem (s : BState) : WItem → BState × Py Val
  | .data d => write s d
  | .hooked hook r =>
    let s := hook.foldl hookStepFree s
    match r with
    | none => (s, .error boomErr)
    | some d => write s d
  | .bad w => writeObj s w

/-- `for line in lines: self.write(line)`, _pyio.py:590-591: `__next__` runs, an exception
from it propagates, and each item goes through `write`. -/
def writelinesSteps : BState → List IStep → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, .raise hook :: _ => (hook.foldl hookStepFree s, .error keyErr)
  | s, .item hook x :: rest =>
    match writeItem (hook.foldl hookStepFree s) x with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => writelinesSteps s' rest

/-- `IOBase.writelines`, _pyio.py:583-591: `_checkClosed()` (:589), then `iter(lines)`. -/
def writelinesIt (s : BState) (a : WLArg) : BState × Py Val :=
  if s.closed then (s, .error closedDot) else
  match a with
  | .notIter t => (s, .error (notIterable t))
  | .iter steps => writelinesSteps s steps

/-- `BytesIO.__init__`, _pyio.py:884-894: `buf += initial_bytes` (:890-891) asks for the
argument's buffer while `_buffer` is still the old one, so a `__buffer__` acts on the old
stream; `bytearray.__iadd__` turns any failure to get a buffer, a raising `__buffer__`
included, into `TypeError("can't concat T to bytearray")`; then `_buffer` and `_pos` are
replaced (:893-894), which drops the old views, and the closed flag stays. -/
def reinitItem (s : BState) (x : WItem) : BState × Py Val :=
  match x with
  | .data d => reinit s (some d)
  | .hooked hook r =>
    let s := hook.foldl hookStepFree s
    match r with
    | none => (s, .error (.typeError s!"can't concat {bufTypeName} to bytearray"))
    | some d => reinit s (some d)
  -- `if initial_bytes is not None` (:890)
  | .bad (.obj "NoneType") => reinit s none
  | .bad w => (s, .error (.typeError s!"can't concat {w.typeName} to bytearray"))

def cbstep (s : BState) : CBOp → BState × Py Val
  | .writeItem x => writeItem s x
  | .writelinesIt a => writelinesIt s a
  | .reinitItem x => reinitItem s x

end P

def stepCbC (s : BState) : BOp ⊕ CBOp → BState × Py Val
  | .inl o => C.step s o
  | .inr o => C.cbstep s o

def stepCbP (s : BState) : BOp ⊕ CBOp → BState × Py Val
  | .inl o => P.step s o
  | .inr o => P.cbstep s o

/-! ## `write` of an object whose `__buffer__` runs code -/

/-- `write(x)` where `x.__buffer__` runs actions on the stream: in both twins the closed
check, the export check and the position come from the state the actions left, not the
state before the call (C asks for the buffer at bytesio.c:242, before :246 and :257;
`_pyio` calls `memoryview(b)` at _pyio.py:958 before :959 and :967). A raising
`__buffer__` propagates with the actions' effects kept and nothing written. If the actions
closed the stream, C raises `ValueError('I/O operation on closed file.')` and `_pyio`
`ValueError('write to closed file')`; if they left a view, C raises `BufferError`;
otherwise the bytes are written exactly as `write(bytes)` writes them on that state. -/
def BytesIOWriteCallback : Prop := ∀ (s : BState) (hook : List Hook),
  let c := hook.foldl C.hookStep s
  let p := hook.foldl P.hookStepFree s
  C.writeItem s (.hooked hook none) = (c, .error boomErr) ∧
  P.writeItem s (.hooked hook none) = (p, .error boomErr) ∧
  ∀ d : List Nat,
    (c.closed = true → C.writeItem s (.hooked hook (some d)) = (c, .error C.closedErr)) ∧
    (p.closed = true → P.writeItem s (.hooked hook (some d)) = (p, .error (.valueError "write to closed file"))) ∧
    (c.closed = false → c.exports > 0 → C.writeItem s (.hooked hook (some d)) = (c, .error bufferError)) ∧
    C.writeItem s (.hooked hook (some d)) = C.step c (.write d) ∧
    P.writeItem s (.hooked hook (some d)) = P.step p (.write d)

theorem bytesIOWriteCallback_proven : BytesIOWriteCallback := by
  intro s hook
  refine ⟨rfl, rfl, fun d => ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_, rfl, rfl⟩⟩
  · simp only [C.writeItem, C.write, h, ite_true]
  · simp only [P.writeItem, P.write, h, ite_true]
  · simp only [C.writeItem, C.write, h1, h2, Bool.false_eq_true, ite_false, ite_true]

/-! ## `writelines` over a fallible iterator -/

/-- The operations `writelines` is equivalent to, run one after another: each `__next__`
(its actions as method calls, then the item or `KeyError`), each item through `write`,
stopping at the first exception. -/
def C.seqWrites : BState → List IStep → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, .raise hook :: _ => (hook.foldl C.hookStep s, .error keyErr)
  | s, .item hook x :: rest =>
    let (s', r) := C.writeItem (hook.foldl C.hookStep s) x
    if r.toBool then C.seqWrites s' rest else (s', r)

def P.seqWrites : BState → List IStep → BState × Py Val
  | s, [] => (s, .ok .none)
  | s, .raise hook :: _ => (hook.foldl P.hookStepFree s, .error keyErr)
  | s, .item hook x :: rest =>
    let (s', r) := P.writeItem (hook.foldl P.hookStepFree s) x
    if r.toBool then P.seqWrites s' rest else (s', r)

/-- `writelines(it)` on every stream, for every iterator, is "equivalent to calling write()
for each element" (bytesio.c:845-846, Doc/library/io.rst IOBase.writelines) in both twins:
on an open stream it is the run of `next(it)` and `write(item)` one after another, which
stops at the first exception, whether `__next__` raised it (`KeyError`), `write` refused
the item (a `str`, a non-buffer, a raising `__buffer__`), or an earlier `__next__` or
`__buffer__` closed the stream or took a view; a non-iterable raises
`TypeError("'T' object is not iterable")` and changes nothing; a closed stream raises
the closed-file `ValueError` before `iter()` is called. With items that are plain `bytes`
and no actions it is the list-based `writelines` of `PyIO/BytesExtra.lean`. -/
def BytesIOWritelinesIter : Prop := ∀ (s : BState),
  (s.closed = true → ∀ a, C.writelinesIt s a = (s, .error C.closedErr) ∧
    P.writelinesIt s a = (s, .error P.closedDot)) ∧
  (s.closed = false →
    (∀ t, C.writelinesIt s (.notIter t) = (s, .error (notIterable t)) ∧
      P.writelinesIt s (.notIter t) = (s, .error (notIterable t))) ∧
    (∀ steps, C.writelinesIt s (.iter steps) = C.seqWrites s steps ∧
      P.writelinesIt s (.iter steps) = P.seqWrites s steps) ∧
    (∀ ls : List (List Nat), C.writelinesIt s (.iter (ls.map fun d => .item [] (.data d))) = C.xstep s (.writelines ls) ∧
      P.writelinesIt s (.iter (ls.map fun d => .item [] (.data d))) = P.xstep s (.writelines ls)))

theorem C_writelinesSteps_seq : ∀ (steps : List IStep) (s : BState),
    C.writelinesSteps s steps = C.seqWrites s steps
  | [], _ => rfl
  | .raise _ :: _, _ => rfl
  | .item hook x :: rest, s => by
    simp only [C.writelinesSteps, C.seqWrites]
    rcases C.writeItem (hook.foldl C.hookStep s) x with ⟨s', r⟩
    cases r with
    | error e => rfl
    | ok v => simp only [Except.toBool, ite_true]; exact C_writelinesSteps_seq rest s'

theorem P_writelinesSteps_seq : ∀ (steps : List IStep) (s : BState),
    P.writelinesSteps s steps = P.seqWrites s steps
  | [], _ => rfl
  | .raise _ :: _, _ => rfl
  | .item hook x :: rest, s => by
    simp only [P.writelinesSteps, P.seqWrites]
    rcases P.writeItem (hook.foldl P.hookStepFree s) x with ⟨s', r⟩
    cases r with
    | error e => rfl
    | ok v => simp only [Except.toBool, ite_true]; exact P_writelinesSteps_seq rest s'

theorem C_writelinesSteps_plain : ∀ (ls : List (List Nat)) (s : BState),
    C.writelinesSteps s (ls.map fun d => .item [] (.data d)) = C.writelinesLoop s ls
  | [], _ => rfl
  | l :: ls, s => by
    simp only [List.map_cons, C.writelinesSteps, C.writelinesLoop, List.foldl_nil, C.writeItem]
    rcases C.write s l with ⟨s', r⟩
    cases r with
    | error e => rfl
    | ok v => exact C_writelinesSteps_plain ls s'

theorem P_writelinesSteps_plain : ∀ (ls : List (List Nat)) (s : BState),
    P.writelinesSteps s (ls.map fun d => .item [] (.data d)) = P.writelinesLoop s ls
  | [], _ => rfl
  | l :: ls, s => by
    simp only [List.map_cons, P.writelinesSteps, P.writelinesLoop, List.foldl_nil, P.writeItem]
    rcases P.write s l with ⟨s', r⟩
    cases r with
    | error e => rfl
    | ok v => exact P_writelinesSteps_plain ls s'

theorem bytesIOWritelinesIter_proven : BytesIOWritelinesIter := by
  intro s
  refine ⟨fun h a => ⟨by simp [C.writelinesIt, h], by simp [P.writelinesIt, h]⟩, fun h => ⟨fun t => ?_, fun steps => ?_,
    fun ls => ?_⟩⟩
  · simp [C.writelinesIt, P.writelinesIt, h]
  · simp only [C.writelinesIt, P.writelinesIt, h, Bool.false_eq_true, ite_false]
    exact ⟨C_writelinesSteps_seq steps s, P_writelinesSteps_seq steps s⟩
  · simp only [C.writelinesIt, P.writelinesIt, C.xstep, P.xstep, h, Bool.false_eq_true, ite_false]
    exact ⟨C_writelinesSteps_plain ls s, P_writelinesSteps_plain ls s⟩

/-! ## `__init__` with anything but an exact `bytes` -/

/-- `__init__(v)` with a bytes-like `v` that is not an exact `bytes` (a `bytearray` here) on
an `io.BytesIO` with no view: it goes through `write` (bytesio.c:1103-1110), so on an open
stream the contents become `v`, the position 0 (:1109) and the stream stays open; on a
closed stream the write refuses with the closed-file `ValueError`, after the reset has
emptied it, even for an empty `v`. `_pyio` replaces `_buffer` and `_pos` in every state,
closed included (_pyio.py:890-894). With a `__buffer__` that acts on the stream, C runs it
on the reset stream and writes `v` where it left the position, then rewinds; `_pyio` runs
it on the old stream, then replaces the buffer. -/
def BytesIOReinitObj : Prop := ∀ (s : BState) (d : List Nat), s.exports = 0 → d.length < memLimit →
  (s.closed = true → C.xstep s (.reinitObj (some d)) = ({ s with buf := [], pos := 0 }, .error C.closedErr)) ∧
  (s.closed = false → (C.xstep s (.reinitObj (some d))).2 = .ok .none ∧ (C.xstep s (.reinitObj (some d))).1.buf = d ∧
    (C.xstep s (.reinitObj (some d))).1.pos = 0 ∧ (C.xstep s (.reinitObj (some d))).1.closed = false) ∧
  P.xstep s (.reinitObj (some d)) = ({ s with buf := d, pos := 0, exports := 0 }, .ok .none) ∧
  (∀ hook r, C.reinitItem s (.hooked hook r) =
    match C.writeItem { s with buf := [], pos := 0 } (.hooked hook r) with
    | (s', .error e) => (s', .error e)
    | (s', .ok _) => ({ s' with pos := 0 }, .ok .none)) ∧
  (∀ hook d', P.reinitItem s (.hooked hook (some d')) =
    ({ hook.foldl P.hookStepFree s with buf := d', pos := 0, exports := 0 }, .ok .none))

theorem bytesIOReinitObj_proven : BytesIOReinitObj := by
  intro s d he hm
  have hne : ¬ s.exports > 0 := by omega
  have hmax : (memLimit : Int) ≤ ssizeMax := by decide
  refine ⟨fun hc => ?_, fun hc => ?_, rfl, fun hook r => ?_, fun hook d' => rfl⟩
  · simp [C.xstep, C.reinitObj, hne, C.write, hc]
  · by_cases hd : d = []
    · subst hd; simp [C.xstep, C.reinitObj, hne, C.write, hc]
    · have hl : d.length ≠ 0 := fun e => hd (List.eq_nil_of_length_eq_zero e)
      have c1 : ¬ ((0 + d.length : Nat) > 0 ∧ (((0 + d.length : Nat)) : Int) > ssizeMax) := by omega
      have c2 : ¬ ((0 + d.length : Nat) > 0 ∧ (((0 + d.length : Nat)) : Int) = ssizeMax) := by omega
      have c3 : ¬ ((0 + d.length : Nat) > 0 ∧ (0 + d.length : Nat) ≥ memLimit) := by omega
      simp only [C.xstep, C.reinitObj, ite_false, C.write, hc, Bool.false_eq_true, he, Nat.lt_irrefl,
        gt_iff_lt, hl, List.length_nil]
      simp only [gt_iff_lt] at c1 c2 c3
      simp only [c1, c2, c3, ite_false]
      simp [writeAt]
  · cases r <;> simp [C.reinitItem, hne]

/-! ## `seek`: the two "new position too large" guards -/

/-- `_io_BytesIO_seek_impl` (bytesio.c:774-815) after the clinic conversions, on every
stream whose position and size fit `Py_ssize_t` (type invariants of the C object), for every
`pos` and `whence` in range: `OverflowError('new position too large')` exactly when the new
position `pos + current position` (whence 1, :789-793) or `pos + size` (whence 2,
:797-801) exceeds `PY_SSIZE_T_MAX` (C tests `pos > PY_SSIZE_T_MAX - base`, which cannot
overflow); otherwise the position becomes that sum, or `pos` for whence 0, clamped at 0
(:810-811), and is returned. The closed check, the negative whence-0 refusal and the bad
whence refusal come first, between and last, in source order. -/
def BytesIOSeekSpec : Prop := ∀ (s : BState) (p w : Int),
  (s.pos : Int) ≤ ssizeMax → (s.buf.length : Int) ≤ ssizeMax → InSsize p → InCInt w →
  C.seek s p w =
    if s.closed then (s, .error C.closedErr)
    else if p < 0 ∧ w = 0 then (s, .error (.valueError s!"negative seek value {p}"))
    else if w = 1 ∧ p + s.pos > ssizeMax then (s, .error (.overflowError "new position too large"))
    else if w = 2 ∧ p + s.buf.length > ssizeMax then (s, .error (.overflowError "new position too large"))
    else if w ≠ 0 ∧ w ≠ 1 ∧ w ≠ 2 then (s, .error (.valueError s!"invalid whence ({w}, should be 0, 1 or 2)"))
    else
      let np : Int := max 0 (p + (if w = 1 then (s.pos : Int) else if w = 2 then (s.buf.length : Int) else 0))
      ({ s with pos := np.toNat }, .ok (.int np))

theorem bytesIOSeekSpec_proven : BytesIOSeekSpec := by
  intro s p w hp hl hps hw
  have hm : ∀ x : Int, (if x < 0 then 0 else x) = max 0 x := fun x => by split <;> omega
  unfold C.seek
  simp only [argSsize, hps, ite_true, argCInt, hw]
  by_cases hc : s.closed = true
  · simp [hc]
  · simp only [hc, ite_false, Bool.false_eq_true]
    by_cases h0 : p < 0 ∧ w = 0
    · simp only [h0, ite_true, and_self]
    · simp only [h0, ite_false]
      by_cases h1 : w = 1
      · subst h1
        by_cases ho : p + s.pos > ssizeMax
        · have : p > ssizeMax - s.pos := by omega
          simp [this, ho]
        · have : ¬ p > ssizeMax - s.pos := by omega
          simp [this, ho, hm]
      · by_cases h2 : w = 2
        · subst h2
          by_cases ho : p + s.buf.length > ssizeMax
          · have : p > ssizeMax - s.buf.length := by omega
            simp [this, ho]
          · have : ¬ p > ssizeMax - s.buf.length := by omega
            simp [this, ho, hm]
        · by_cases h3 : w = 0
          · subst h3
            have hp0 : ¬ p < 0 := by simpa using h0
            simp only [h1, h2, ite_false, false_and, ne_eq, not_true_eq_false, and_false, Int.reduceEq,
              not_false_eq_true, true_and]
            have : max 0 p = p := by omega
            simp [hp0, this]
          · simp [h1, h2, h3]

/-- For every open stream with its position in `Py_ssize_t` and every `pos` and `whence` in
the range of the C converters, `io.BytesIO.seek` and `_pyio.BytesIO.seek` agree on the value
or the exception class. -/
def BytesIOSeekTwins : Prop := ∀ (s : BState) (p w : Int), s.closed = false → (s.pos : Int) ≤ ssizeMax →
  InSsize p → InCInt w → sameClass (C.seek s p w).2 (P.seek s p w).2 = true

/-- `seek(sys.maxsize)` then `seek(sys.maxsize, 1)`: C's whence-1 guard (bytesio.c:789-793)
raises `OverflowError('new position too large')`; `_pyio` (_pyio.py:988-990) has no bound
and moves to `2 * sys.maxsize`. -/
theorem bytesIOSeekTwins_refuted : ¬BytesIOSeekTwins := by
  intro h
  have := h { (default : BState) with pos := 2 ^ 63 - 1 } (2 ^ 63 - 1) 1 rfl (by decide) (by decide) (by decide)
  revert this
  decide

end PyLean.PyIO
