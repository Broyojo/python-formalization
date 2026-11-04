import PyLean.PyIO.BytesExtra
import PyLean.PyIO.StringExtra
import PyLean.PyIO.StringTwins

/-!
Arguments that are not `None` or an `int`, and the order in which each twin looks at
them and at `closed` (`Modules/_io/bytesio.c`, `Modules/_io/stringio.c`,
`Lib/_pyio.py`, CPython 3.15.2).

C converts its arguments (Argument Clinic, or an explicit type test) before the body
checks `closed`; `_pyio` checks `closed` first and converts afterwards, and never looks
at `closed` again. Each difference is stated twice: the exact behaviour of each twin
(proven), and the agreement it breaks (refuted).
-/

namespace PyLean.PyIO

open PyLean

/-! ## `_pyio`: what an `__index__` can do to the stream -/

/-- On a `_pyio.BytesIO`, a closed stream has an empty `_buffer` (`close` clears it
before setting the flag, _pyio.py:922-925). -/
def ClosedEmpty (s : BState) : Prop := s.closed = true → s.buf = []

theorem P_write_closed (s : BState) (b : List Nat) : (P.write s b).1.closed = s.closed := by
  obtain ⟨buf, pos, cl, ex, sh⟩ := s
  unfold P.write
  cases cl
  · simp only [Bool.false_eq_true, ite_false]
    by_cases hn : b.length = 0
    · simp [hn]
    · simp only [hn, ite_false]
      by_cases h1 : pos > buf.length
      · by_cases h2 : (pos : Int) > ssizeMax
        · simp [h1, h2]
        · by_cases h3 : ex > 0
          · simp [h1, h2, h3]
          · by_cases h4 : pos ≥ memLimit
            · simp [h1, h2, h3, h4]
            · simp only [h1, h2, h3, h4, ite_true, ite_false]
              (repeat' split) <;> rfl
      · simp only [h1, ite_false]
        (repeat' split) <;> rfl
  · simp

theorem P_seek_closed (s : BState) (p w : Int) : (P.seek s p w).1.closed = s.closed := by
  unfold P.seek
  by_cases hcl : s.closed = true
  · rw [if_pos hcl]
  · rw [if_neg hcl]; dsimp only; split <;> rfl

theorem P_hookStepFree_inv (s : BState) (h : Hook) (hs : ClosedEmpty s) :
    ClosedEmpty (P.hookStepFree s h) := by
  intro hc
  cases h with
  | close =>
    simp only [P.hookStepFree, P.close] at hc ⊢
    by_cases hb : s.buf ≠ [] ∧ s.exports > 0
    · rw [if_pos hb] at hc ⊢; exact hs hc
    · rw [if_neg hb]
  | getbuffer =>
    simp only [P.hookStepFree, P.step] at hc ⊢
    by_cases hcl : s.closed = true
    · rw [if_pos hcl] at hc ⊢; exact hs hc
    · rw [if_neg hcl] at hc; exact absurd hc hcl
  | tell => exact hs hc
  | seekAbs p =>
    simp only [P.hookStepFree] at hc ⊢
    rw [P_seek_closed] at hc
    have : (P.seek s p 0).1 = s := by unfold P.seek; simp [hc]
    rw [this]; exact hs hc
  | seekCur =>
    simp only [P.hookStepFree] at hc ⊢
    rw [P_seek_closed] at hc
    have : (P.seek s 0 1).1 = s := by unfold P.seek; simp [hc]
    rw [this]; exact hs hc
  | write b =>
    simp only [P.hookStepFree] at hc ⊢
    rw [P_write_closed] at hc
    have : (P.write s b).1 = s := by unfold P.write; simp [hc]
    rw [this]; exact hs hc

theorem P_hooks_inv (hook : List Hook) : ∀ (s : BState), ClosedEmpty s →
    ClosedEmpty (hook.foldl P.hookStepFree s) := by
  induction hook with
  | nil => intro s hs; exact hs
  | cons h t ih => intro s hs; exact ih _ (P_hookStepFree_inv s h hs)

/-! ## `BytesIO.read`, `readline` and `seek` of an object -/

/-- The exact behaviour of each twin for `read(a)`, `readline(a)` and `seek(a, whence)`
when `a` is not `None` or an `int`, on every state.

C (clinic conversion, then the body): an object with no `__index__` is refused by type
name, `TypeError("argument should be integer or None, not 'T'")` for `read` and
`readline` and `TypeError("'T' object cannot be interpreted as an integer")` for `seek`,
leaving the stream as it was; otherwise `__index__` runs first, in every state, and the
method then runs on the state it left, as `read(v)`, `readline(v)` or `seek(v, whence)`
would; an `__index__` that raises propagates its exception after its actions.

`_pyio`: on a closed stream `read` and `seek` raise
`ValueError('read from closed file')` / `ValueError('seek on closed file')` without
calling `__index__`; on an open one an object with no `__index__` raises
`TypeError(f"{a!r} is not an integer")` (also `readline`, whose loop has not started),
and once `__index__` returns `v` the body runs with no second look at `closed`: if
`__index__` closed the stream, `read(v)` returns `b''` and `seek(v)` with `v >= 0` sets
the position to `v` and returns it. -/
def BytesIOIndexArgSpec : Prop := ∀ (s : BState) (w : Int),
  (∀ t r, C.xstep s (.readObj (.noIndex t r)) =
      (s, .error (.typeError s!"argument should be integer or None, not '{t}'")) ∧
    C.xstep s (.readlineObj (.noIndex t r)) =
      (s, .error (.typeError s!"argument should be integer or None, not '{t}'")) ∧
    C.xstep s (.seekObj (.noIndex t r) w) =
      (s, .error (.typeError s!"'{t}' object cannot be interpreted as an integer"))) ∧
  (∀ hook, C.xstep s (.readObj (.index hook none)) = (hook.foldl C.hookStep s, .error boomErr) ∧
    C.xstep s (.seekObj (.index hook none) w) = (hook.foldl C.hookStep s, .error boomErr)) ∧
  (∀ hook v, InSsize v →
    C.xstep s (.readObj (.index hook (some v))) = C.step (hook.foldl C.hookStep s) (.read (some v)) ∧
    C.xstep s (.readlineObj (.index hook (some v))) =
      C.step (hook.foldl C.hookStep s) (.readline (some v)) ∧
    C.xstep s (.seekObj (.index hook (some v)) w) = C.step (hook.foldl C.hookStep s) (.seek v w)) ∧
  (s.closed = true → ∀ a,
    P.xstep s (.readObj a) = (s, .error (.valueError "read from closed file")) ∧
    P.xstep s (.seekObj a w) = (s, .error (.valueError "seek on closed file"))) ∧
  (s.closed = false → ∀ t r,
    P.xstep s (.readObj (.noIndex t r)) = (s, .error (.typeError s!"{r} is not an integer")) ∧
    P.xstep s (.readlineObj (.noIndex t r)) = (s, .error (.typeError s!"{r} is not an integer")) ∧
    P.xstep s (.seekObj (.noIndex t r) w) = (s, .error (.typeError s!"{r} is not an integer"))) ∧
  (s.closed = false → ∀ hook,
    P.xstep s (.readObj (.index hook none)) = (hook.foldl P.hookStepFree s, .error boomErr) ∧
    P.xstep s (.seekObj (.index hook none) w) = (hook.foldl P.hookStepFree s, .error boomErr)) ∧
  (s.closed = false → ∀ hook v, (hook.foldl P.hookStepFree s).closed = true →
    P.xstep s (.readObj (.index hook (some v))) = (hook.foldl P.hookStepFree s, .ok (.bytes [])) ∧
    (v ≥ 0 → P.xstep s (.seekObj (.index hook (some v)) 0) =
      ({ hook.foldl P.hookStepFree s with pos := v.toNat }, .ok (.int v)))) ∧
  (s.closed = false → ∀ hook v, (hook.foldl P.hookStepFree s).closed = false →
    P.xstep s (.readObj (.index hook (some v))) = P.step (hook.foldl P.hookStepFree s) (.read (some v)) ∧
    P.xstep s (.seekObj (.index hook (some v)) w) = P.step (hook.foldl P.hookStepFree s) (.seek v w)) ∧
  (∀ hook v, P.xstep s (.readlineObj (.index hook (some v))) =
    P.step (hook.foldl P.hookStepFree s) (.readline (some v)))

theorem bytesIOIndexArgSpec_proven : BytesIOIndexArgSpec := by
  intro s w
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t r
    exact ⟨rfl, rfl, rfl⟩
  · intro hook
    exact ⟨rfl, rfl⟩
  · intro hook v hv
    refine ⟨?_, ?_, rfl⟩
    · simp [C.xstep, C.readObj, C.convOptSsize, optSsize, hv, C.step]
    · simp [C.xstep, C.readlineObj, C.convOptSsize, optSsize, hv, C.step]
  · intro hc a
    exact ⟨by simp [P.xstep, P.readObj, hc], by simp [P.xstep, P.seekObj, hc]⟩
  · intro hc t r
    exact ⟨by simp [P.xstep, P.readObj, hc], rfl, by simp [P.xstep, P.seekObj, hc]⟩
  · intro hc hook
    exact ⟨by simp [P.xstep, P.readObj, hc], by simp [P.xstep, P.seekObj, hc]⟩
  · intro hc hook v hc'
    have hinv := P_hooks_inv hook s (by intro h; simp [hc] at h) hc'
    refine ⟨?_, ?_⟩
    · simp [P.xstep, P.readObj, hc, P.readBody, hinv]; rfl
    · intro hv
      have hn : ¬ v < 0 := by omega
      simp [P.xstep, P.seekObj, hc, P.seekBody, hn]
  · intro hc hook v hc'
    refine ⟨?_, ?_⟩
    · simp only [P.xstep, P.readObj, hc, Bool.false_eq_true, ite_false, P.step, P.read]
      rw [P.readRaw_eq_readBody _ _ hc']
    · simp only [P.xstep, P.seekObj, hc, Bool.false_eq_true, ite_false, P.step]
      rw [P.seek_eq_seekBody _ _ _ hc']
  · intro hook v
    rfl

/-- `io.BytesIO.read` and `_pyio.BytesIO.read` agree on the value or the exception class
for every state and every argument object. -/
def BytesIOReadIndexTwins : Prop := ∀ (s : BState) (a : TArg),
  sameClass (C.xstep s (.readObj a)).2 (P.xstep s (.readObj a)).2 = true

/-- `f = BytesIO(b'abc'); f.read(x)` where `x.__index__` closes `f` and returns 1: C runs
`__index__` in the clinic converter and then `CHECK_CLOSED` raises `ValueError`; `_pyio`
checked `closed` before calling `__index__` and returns `b''`. -/
theorem bytesIOReadIndexTwins_refuted : ¬BytesIOReadIndexTwins := by
  intro h
  have := h (bInit [97, 98, 99]) (.index [.close] (some 1))
  revert this
  decide

/-- `io.BytesIO.seek` and `_pyio.BytesIO.seek` agree on the value or the exception class
for every state, argument object and `whence`. -/
def BytesIOSeekIndexTwins : Prop := ∀ (s : BState) (a : TArg) (w : Int),
  sameClass (C.xstep s (.seekObj a w)).2 (P.xstep s (.seekObj a w)).2 = true

/-- `f = BytesIO(b'abc'); f.seek(x)` where `x.__index__` closes `f` and returns 2: C raises
`ValueError`; `_pyio` sets `_pos` on the closed stream and returns 2. -/
theorem bytesIOSeekIndexTwins_refuted : ¬BytesIOSeekIndexTwins := by
  intro h
  have := h (bInit [97, 98, 99]) (.index [.close] (some 2)) 0
  revert this
  decide

/-! ## `readlines` with a float hint -/

/-- `0.5`. -/
def half : Binary64.F64 := Binary64.F64.ofBits 0x3fe0000000000000

/-- `io.BytesIO.readlines` and `_pyio.BytesIO.readlines` agree on the value or the
exception class for every open stream and every float hint. -/
def BytesIOReadlinesFloatTwins : Prop := ∀ (s : BState) (x : Binary64.F64), s.closed = false →
  sameClass (C.xstep s (.readlinesFloat x)).2 (P.xstep s (.readlinesFloat x)).2 = true

/-- `BytesIO(b'a\nb\n').readlines(0.5)`: C refuses a hint that is not an `int` or `None`
(`TypeError: integer argument expected, got 'float'`); `_pyio` compares `0.5 <= 0`
(False) and stops once `n >= 0.5`, returning `[b'a\n']`. -/
theorem bytesIOReadlinesFloatTwins_refuted : ¬BytesIOReadlinesFloatTwins := by
  intro h
  have := h (bInit [97, 10, 98, 10]) half rfl
  revert this
  decide +kernel

/-! ## `BytesIO.write` of a `str` or a non-buffer -/

/-- `write(w)` of a `str` or of an object without the buffer interface raises `TypeError`
in both twins on every stream, open or closed, and changes nothing: C
`TypeError("a bytes-like object is required, not 'T'")` from `PyObject_GetBuffer`, `_pyio`
`TypeError("can't write str to binary stream")` for a `str` and
`TypeError("memoryview: a bytes-like object is required, not 'T'")` otherwise. Both
refuse before looking at `closed`. -/
def BytesIOWriteObj : Prop := ∀ (s : BState),
  (∀ w : WArg, C.xstep s (.writeObj w) =
    (s, .error (.typeError s!"a bytes-like object is required, not '{w.typeName}'"))) ∧
  (∀ x, P.xstep s (.writeObj (.str x)) = (s, .error (.typeError "can't write str to binary stream"))) ∧
  (∀ t, P.xstep s (.writeObj (.obj t)) =
    (s, .error (.typeError s!"memoryview: a bytes-like object is required, not '{t}'")))

theorem bytesIOWriteObj_proven : BytesIOWriteObj := by
  intro s
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## `StringIO.write` of a non-`str` -/

/-- The exact refusals of `write` in both twins, on every state. C (stringio.c:561-579)
type-checks first: an object that is not a `str` raises
`TypeError("string argument expected, got 'T'")` whether or not the stream is closed, and
a `str` on a closed stream raises `ValueError('I/O operation on closed file')`. `_pyio`
(`TextIOWrapper.write`, _pyio.py:2280-2286) checks `closed` first: every argument on a
closed stream raises `ValueError('write to closed file')`, and a non-`str` on an open one
raises `TypeError("can't write T to text stream")`. No refusal changes the stream. -/
def StringIOWriteRefusals : Prop := ∀ (s : SCState) (t : TState),
  (∀ ty, SC.xstep s (.writeObj ty) = (s, .error (.typeError s!"string argument expected, got '{ty}'"))) ∧
  (s.closed = true → ∀ x, SC.step s (.write x) = (s, .error (.valueError "I/O operation on closed file"))) ∧
  (t.b.closed = true → (∀ ty, TP.xstep t (.writeObj ty) = (t, .error (.valueError "write to closed file"))) ∧
    ∀ x, TP.step t (.write x) = (t, .error (.valueError "write to closed file"))) ∧
  (t.b.closed = false → ∀ ty,
    TP.xstep t (.writeObj ty) = (t, .error (.typeError s!"can't write {ty} to text stream")))

theorem stringIOWriteRefusals_proven : StringIOWriteRefusals := by
  intro s t
  refine ⟨fun _ => rfl, ?_, ?_, ?_⟩
  · intro hc x; simp [SC.step, hc, SC.closedErr]
  · intro hc
    exact ⟨fun ty => by simp [TP.xstep, hc], fun x => by simp [TP.step, TP.write, hc]⟩
  · intro hc ty; simp [TP.xstep, hc]

/-- `io.StringIO.write` and `_pyio.StringIO.write` raise exceptions of the same class for a
non-`str` argument whenever both streams are open or both are closed. -/
def StringIOWriteCheckOrderTwins : Prop := ∀ (s : SCState) (t : TState) (ty : String),
  s.closed = t.b.closed →
  sameClass (SC.xstep s (.writeObj ty)).2 (TP.xstep t (.writeObj ty)).2 = true

/-- `s.close(); s.write(1)`: C raises `TypeError` (type test first), `_pyio` raises
`ValueError` (closed test first). -/
theorem stringIOWriteCheckOrderTwins_refuted : ¬StringIOWriteCheckOrderTwins := by
  intro h
  have := h { (default : SCState) with closed := true }
    { (default : TState) with b := { (default : BState) with closed := true } } "int" rfl
  revert this
  decide

/-! ## `BytesIO.__init__`, `__getstate__` and `getbuffer` -/

/-- `io.BytesIO(b)`: `bytesio_new` (bytesio.c:1054-1073) makes an empty object whose
buffer is the shared empty `bytes`, then `_io_BytesIO___init___impl` (:1084-1114) runs
on it. -/
def C.construct (b : Option (List Nat)) : BState := (C.reinit ⟨[], 0, false, 0, true⟩ b).1

/-- `_pyio.BytesIO(b)`, _pyio.py:884-894 on a new object: `IOBase`'s flag starts `False`
(:388), `buf = bytearray()`, `buf += initial_bytes` when it is not `None`, then `_buffer`
and `_pos = 0`; no view exists. `shared` is C's field, which no `P` function reads; it is
set as `bInit` sets it so that the states compare equal. -/
def P.construct (b : Option (List Nat)) : BState :=
  { buf := [] ++ b.getD [], pos := 0, closed := false, exports := 0, shared := decide ((b.getD []).length ≤ 1) }

/-- The two constructors, each from its own body: both give the initial bytes at
position 0, open, with no view, so every run of the core agreement theorem starts from
what the real constructors build, and on those starts the twins agree on every value and
exception class (the core hypotheses). A second `__init__` with an int fails in both, but
`_pyio` fails at `buf += 1` before touching the stream, while C has already emptied it
(bytesio.c:1094-1095 run before the write at :1105). -/
def BytesIOInitTwins : Prop :=
  (∀ b : Option (List Nat), C.construct b = bInit (b.getD []) ∧ P.construct b = bInit (b.getD [])) ∧
  (∀ init ops, (∀ o ∈ ops, BOp.InRange o ∧ BOp.NoExport o) →
    PyRunAll (fun s o => BOp.Small s o ∧ BOp.NoReadline0Closed s o) (P.construct (some init)) ops →
    AllSameClass (runOps C.step (C.construct (some init)) ops).2 (runOps P.step (P.construct (some init)) ops).2) ∧
  (∀ s : BState, P.xstep s (.reinitObj none) = (s, .error (.typeError "can't concat int to bytearray")) ∧
    (s.exports = 0 → C.xstep s (.reinitObj none) =
      ({ s with buf := [], pos := 0 }, .error (.typeError "a bytes-like object is required, not 'int'"))))

theorem bytesIOInitTwins_proven : BytesIOInitTwins := by
  have hb : ∀ b : Option (List Nat), C.construct b = bInit (b.getD []) ∧ P.construct b = bInit (b.getD []) := by
    intro b; cases b <;> simp [C.construct, P.construct, C.reinit, bInit]
  refine ⟨hb, ?_, ?_⟩
  · intro init ops hops hrun
    rw [(hb (some init)).1, (hb (some init)).2] at *
    exact bytesIOTwinsSameClassCore_proven init ops hops hrun
  · intro s
    refine ⟨rfl, ?_⟩
    intro he
    have : ¬ s.exports > 0 := by omega
    simp [C.xstep, C.reinitObj, this]

/-- `__getstate__` refuses a closed stream before reading it, with
`ValueError('I/O operation on closed file.')` from `getvalue` in C (bytesio.c:910-920, :938-945)
and `ValueError('__getstate__ on closed file')` in `_pyio` (_pyio.py:896-898); on an
open stream it returns the contents and the position, as `(bytes, pos, dict)` in C and
the instance dict without `_lock` in `_pyio` (:899-902). No call changes the stream. -/
def BytesIOGetstate : Prop := ∀ s : BState,
  (s.closed = true →
    C.xstep s .getstate = (s, .error (.valueError "I/O operation on closed file.")) ∧
    P.xstep s .getstate = (s, .error (.valueError "__getstate__ on closed file"))) ∧
  (s.closed = false →
    C.xstep s .getstate = (s, .ok (.list [.bytes s.buf, .int s.pos, .none])) ∧
    P.xstep s .getstate = (s, .ok (.list [.bytes s.buf, .int s.pos])))

theorem bytesIOGetstate_proven : BytesIOGetstate := by
  intro s
  constructor
  · intro h; simp [C.xstep, P.xstep, h, C.closedErr]
  · intro h; simp [C.xstep, P.xstep, h]

/-- `getbuffer()` on `_pyio.BytesIO` (_pyio.py:915-920) refuses a closed stream with
`ValueError('getbuffer on closed file')`; on an open one it returns a view of `_buffer`
that leaves contents and position as they were and, while it lives, blocks every resize
("As long as the view exists, the BytesIO object cannot be resized or closed"): closing a
non-empty stream, truncating it to 0, and a write past the end each raise `BufferError`.
C refuses a closed stream with its own message and blocks the same operations. -/
def BytesIOGetbuffer : Prop := ∀ s : BState,
  (s.closed = true →
    P.step s .getbuffer = (s, .error (.valueError "getbuffer on closed file")) ∧
    C.step s .getbuffer = (s, .error (.valueError "I/O operation on closed file."))) ∧
  (s.closed = false →
    let p := (P.step s .getbuffer).1
    let c := (C.step s .getbuffer).1
    (P.step s .getbuffer).2 = .ok .none ∧ p.buf = s.buf ∧ p.pos = s.pos ∧ p.exports = s.exports + 1 ∧
    (C.step s .getbuffer).2 = .ok .none ∧ c.buf = s.buf ∧ c.pos = s.pos ∧ c.exports = s.exports + 1 ∧
    (s.buf ≠ [] →
      (P.step p .close).2 = .error bufferError ∧ (P.step p (.truncate (some 0))).2 = .error bufferError ∧
      (C.step c .close).2 = .error bufferError ∧ (C.step c (.truncate (some 0))).2 = .error bufferError) ∧
    (∀ b : List Nat, b ≠ [] → s.pos ≤ s.buf.length → s.pos + b.length > s.buf.length →
      (P.step p (.write b)).2 = .error bufferError ∧ (C.step c (.write b)).2 = .error bufferError))

theorem bytesIOGetbuffer_proven : BytesIOGetbuffer := by
  intro s
  constructor
  · intro h; simp [P.step, C.step, h, C.closedErr]
  · intro h
    have hz : ssizeMin ≤ 0 := by decide
    refine ⟨by simp [P.step, h], by simp [P.step, h], by simp [P.step, h], by simp [P.step, h],
      by simp [C.step, h], by simp [C.step, h, C.takeView], by simp [C.step, h, C.takeView],
      by simp [C.step, h, C.takeView], ?_, ?_⟩
    · intro hb
      have hl : 0 < s.buf.length := List.length_pos_iff.mpr hb
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [P.step, P.close, h, hb]
      · simp [P.step, P.truncate, h, hl]
      · simp [C.step, h, C.takeView]
      · simp [C.step, C.truncate, h, C.takeView]
    · intro b hb hle hgt
      have hn : b.length ≠ 0 := fun e => hb (List.eq_nil_of_length_eq_zero e)
      have hng : ¬ s.pos > s.buf.length := by omega
      constructor
      · simp [P.step, P.write, h, hn, hng, hgt]
      · simp [C.step, C.write, h, C.takeView]

/-! ## `StringIO(value, newline)`: the newline check -/

/-- `TextIOWrapper._check_newline` as `_pyio.StringIO` runs it (_pyio.py:2122-2126,
called first by `TextIOWrapper.__init__`, :2092): a `newline` that is not a `str` or
`None` raises `TypeError("illegal newline type: <class 'T'>")`, and a `str` outside
`None, '', '\n', '\r', '\r\n'` raises `ValueError(f"illegal newline value: {newline!r}")`,
whatever the initial value, before anything is written; only a legal `newline` lets
`StringIO.__init__` refuse a non-`str` initial value with
`TypeError("initial_value must be str or None, not T")` (:2756-2759). C checks in the
same order (stringio.c:693-721), with `TypeError("newline must be str or None, not T")`
for the type. -/
def PyStringIONewlineCheck : Prop :=
  (∀ ty, TP.initNlObj ty = .error (.typeError s!"illegal newline type: <class '{ty}'>") ∧
    SC.initNlObj ty = .error (.typeError s!"newline must be str or None, not {ty}")) ∧
  (∀ v nl, ¬ LegalNewline (some nl) → TP.init v (some nl) = .error (illegalNewline nl)) ∧
  (∀ nl ty, ¬ LegalNewline (some nl) → TP.initValObj (some nl) ty = .error (illegalNewline nl)) ∧
  (∀ nl ty, LegalNewline nl →
    TP.initValObj nl ty = .error (.typeError s!"initial_value must be str or None, not {ty}"))

theorem pyStringIONewlineCheck_proven : PyStringIONewlineCheck := by
  have hill : ∀ v nl, ¬ LegalNewline (some nl) → TP.init v (some nl) = .error (illegalNewline nl) := by
    intro v nl h
    have hl : ¬ (nl = [] ∨ nl = [10] ∨ nl = [13] ∨ nl = [13, 10]) := by
      intro h'; apply h; unfold LegalNewline; simp only [reduceCtorEq, false_or, Option.some.injEq]; exact h'
    simp [TP.init, hl]
  refine ⟨fun _ => ⟨rfl, rfl⟩, hill, ?_, ?_⟩
  · intro nl ty h
    simp [TP.initValObj, hill none nl h]
  · intro nl ty h
    have := (pyStringIONewlineLegal_proven nl).2 h
    unfold TP.initValObj
    cases hi : TP.init none nl with
    | error e => rw [hi] at this; simp [Except.toBool] at this
    | ok t => rfl

end PyLean.PyIO
