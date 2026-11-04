import PyLean.Datetime.TwinsProps
import PyLean.Binary64.RatioProps

/-!
`timedelta * float`, `timedelta / float` and `timedelta / timedelta`, on exact binary64
operands (`PyLean.Binary64.F64`).
-/

namespace PyLean.Datetime

open PyLean

/-- `timedelta * x` and `timedelta / x` for every float `x`: the twins agree in value and
exception class; for a finite `x` with `x.as_integer_ratio() == (n, d)` (exact, `d > 0`),
`t * x` is the timedelta of `t._to_microseconds() * n / d` microseconds rounded half to even,
and `t / x` that of `t._to_microseconds() * d / n` (`ZeroDivisionError` for `x == 0`), each
`OverflowError` when outside the timedelta range; an infinity raises `OverflowError` and a
NaN `ValueError`, from `as_integer_ratio`. Precondition: `t` valid (the type invariant). -/
def TimedeltaFloatOps : Prop :=
  ∀ (a : Delta) (x : Binary64.F64), a.Valid →
    SameOutcome (a.mulFloatPy x) (a.mulFloatC x) ∧
    SameOutcome (a.truedivFloatPy x) (a.truedivFloatC x) ∧
    (x.isFinite = true → ∃ n d : Int, asRatio x = .ok (n, d) ∧ 0 < d ∧ (n : Rat) / d = x.toRat ∧
      (∀ t, a.mulFloatPy x = .ok t → t.Valid ∧ RoundsHalfEven (a.toUs * n) d t.toUs) ∧
      ((∃ t, a.mulFloatPy x = .ok t) ∨ (a.mulFloatPy x).raises "OverflowError") ∧
      (n ≠ 0 → (∀ t, a.truedivFloatPy x = .ok t → t.Valid ∧ RoundsHalfEven (d * a.toUs) n t.toUs) ∧
        ((∃ t, a.truedivFloatPy x = .ok t) ∨ (a.truedivFloatPy x).raises "OverflowError")) ∧
      (n = 0 → (a.truedivFloatPy x).raises "ZeroDivisionError")) ∧
    (x.isInf = true → (a.mulFloatPy x).raises "OverflowError" ∧ (a.truedivFloatPy x).raises "OverflowError") ∧
    (x.isNaN = true → (a.mulFloatPy x).raises "ValueError" ∧ (a.truedivFloatPy x).raises "ValueError")

theorem usToDeltaPy_spec (q : Int) :
    (∀ t, usToDeltaPy q = .ok t → t.Valid ∧ t.toUs = q) ∧
    ((∃ t, usToDeltaPy q = .ok t) ∨ (usToDeltaPy q).raises "OverflowError") := by
  rw [usToDeltaPy_eq]
  obtain ⟨h1, -, h3⟩ := mkDeltaPy_spec q
  exact ⟨h1, h3⟩

theorem round_then_delta (p d : Int) (hd : d ≠ 0) :
    (∀ t, (do usToDeltaPy (← divideAndRound p d)) = .ok t → t.Valid ∧ RoundsHalfEven p d t.toUs) ∧
    ((∃ t, (do usToDeltaPy (← divideAndRound p d)) = .ok t) ∨
      (do usToDeltaPy (← divideAndRound p d) : Py Delta).raises "OverflowError") := by
  obtain ⟨q, hq, hr⟩ := (divideAndRound_proven p d).2.2 hd
  rw [hq]
  simp only [bind, Except.bind]
  obtain ⟨s1, s2⟩ := usToDeltaPy_spec q
  refine ⟨fun t ht => ?_, s2⟩
  have := s1 t ht
  rw [this.2]; exact ⟨this.1, hr⟩

theorem timedeltaFloatOps_proven : TimedeltaFloatOps := by
  intro a x ha
  obtain ⟨hfin, hinf, hnan⟩ := Binary64.asIntegerRatioExact_proven x
  refine ⟨?_, ?_, fun hx => ?_, fun hi => ?_, fun hn => ?_⟩
  · unfold Delta.mulFloatPy Delta.mulFloatC
    apply sameOutcome_bind
    intro ⟨n, d⟩
    simp only
    rw [(divideAndRound_proven (a.toUs * n) d).1]
    apply sameOutcome_bind
    intro q; rw [usToDeltaPy_eq]; exact sameOutcome_mk q
  · unfold Delta.truedivFloatPy Delta.truedivFloatC
    apply sameOutcome_bind
    intro ⟨n, d⟩
    simp only
    rw [Int.mul_comm d a.toUs, (divideAndRound_proven (a.toUs * d) n).1]
    apply sameOutcome_bind
    intro q; rw [usToDeltaPy_eq]; exact sameOutcome_mk q
  · obtain ⟨n, d, hr, hd, hq, -⟩ := hfin hx
    refine ⟨n, d, hr, hd, hq, ?_, ?_, fun hn0 => ?_, fun hn0 => ?_⟩
    · unfold Delta.mulFloatPy asRatio; rw [hr]; exact (round_then_delta _ d (by omega)).1
    · unfold Delta.mulFloatPy asRatio; rw [hr]; exact (round_then_delta _ d (by omega)).2
    · unfold Delta.truedivFloatPy asRatio; rw [hr]; exact round_then_delta _ n hn0
    · unfold Delta.truedivFloatPy asRatio; rw [hr, hn0]
      exact ⟨_, rfl, rfl⟩
  · have e := hinf hi
    unfold Delta.mulFloatPy Delta.truedivFloatPy
    unfold asRatio
    rw [e]
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  · have e := hnan hn
    unfold Delta.mulFloatPy Delta.truedivFloatPy
    unfold asRatio
    rw [e]
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-! ### Float subclasses with their own `as_integer_ratio` -/

/-- `timedelta * x` and `timedelta / x` agree between the twins for every float operand,
including a float subclass whose `as_integer_ratio` is overridden. -/
def TimedeltaFloatRatioTwins : Prop :=
  ∀ (a : Delta) (x : FloatOperand), a.Valid →
    SameOutcome (a.mulFloatObjPy x) (a.mulFloatObjC x) ∧
    SameOutcome (a.truedivFloatObjPy x) (a.truedivFloatObjC x)

/-- `timedelta(1) * F(1.5)` where `F.as_integer_ratio` returns the list `[3, 2]`: Python's
`a, b = ...` unpacks it and gives `timedelta(days=1, seconds=43200)`; C's
`get_float_as_integer_ratio` raises `TypeError` for a non-tuple. -/
theorem timedeltaFloatRatioTwins_refuted : ¬TimedeltaFloatRatioTwins := by
  intro h
  have := (h ⟨1, 0, 0⟩ (.sub (.ok (.list [3, 2]))) (by unfold Delta.Valid MAX_DELTA_DAYS; decide)).1
  exact not_sameOutcome_ok_err _ _ ⟨1, 43200, 0⟩ (by rfl) (by rfl) this

/-- `timedelta * x` and `timedelta / x` for every float operand: a plain float is the
`float.as_integer_ratio` model of `TimedeltaFloatOps`; for a float subclass whose
`as_integer_ratio` returns a 2-tuple of ints `(n, d)` the twins agree and the result is
`t_us * n / d` (and `d * t_us / n`) rounded half to even; a 2-list `[n, d]` gives that same
result in Python and `TypeError` in C (C wants a tuple, Python unpacks any iterable); a
tuple of another length is a `ValueError` in both, a list of another length a `ValueError`
in Python and a `TypeError` in C; a non-iterable is a `TypeError` in both; an exception of
the method propagates in both. Precondition: `t` valid. -/
def TimedeltaFloatRatio : Prop :=
  ∀ (a : Delta) (x : Binary64.F64) (n d : Int) (l : List Int) (e : PyExc), a.Valid →
    a.mulFloatObjPy (.exact x) = a.mulFloatPy x ∧ a.mulFloatObjC (.exact x) = a.mulFloatC x ∧
    a.truedivFloatObjPy (.exact x) = a.truedivFloatPy x ∧ a.truedivFloatObjC (.exact x) = a.truedivFloatC x ∧
    SameOutcome (a.mulFloatObjPy (.sub (.ok (.tuple [n, d])))) (a.mulFloatObjC (.sub (.ok (.tuple [n, d])))) ∧
    SameOutcome (a.truedivFloatObjPy (.sub (.ok (.tuple [n, d]))))
      (a.truedivFloatObjC (.sub (.ok (.tuple [n, d])))) ∧
    a.mulFloatObjPy (.sub (.ok (.tuple [n, d]))) = (do usToDeltaPy (← divideAndRound (a.toUs * n) d)) ∧
    a.truedivFloatObjPy (.sub (.ok (.tuple [n, d]))) = (do usToDeltaPy (← divideAndRound (d * a.toUs) n)) ∧
    a.mulFloatObjPy (.sub (.ok (.list [n, d]))) = a.mulFloatObjPy (.sub (.ok (.tuple [n, d]))) ∧
    a.truedivFloatObjPy (.sub (.ok (.list [n, d]))) = a.truedivFloatObjPy (.sub (.ok (.tuple [n, d]))) ∧
    (a.mulFloatObjC (.sub (.ok (.list l)))).raises "TypeError" ∧
    (a.truedivFloatObjC (.sub (.ok (.list l)))).raises "TypeError" ∧
    (l.length ≠ 2 →
      (a.mulFloatObjPy (.sub (.ok (.tuple l)))).raises "ValueError" ∧
      (a.mulFloatObjC (.sub (.ok (.tuple l)))).raises "ValueError" ∧
      (a.mulFloatObjPy (.sub (.ok (.list l)))).raises "ValueError" ∧
      (a.truedivFloatObjPy (.sub (.ok (.tuple l)))).raises "ValueError" ∧
      (a.truedivFloatObjC (.sub (.ok (.tuple l)))).raises "ValueError" ∧
      (a.truedivFloatObjPy (.sub (.ok (.list l)))).raises "ValueError") ∧
    (a.mulFloatObjPy (.sub (.ok .notIter))).raises "TypeError" ∧
    (a.mulFloatObjC (.sub (.ok .notIter))).raises "TypeError" ∧
    a.mulFloatObjPy (.sub (.error e)) = .error e ∧ a.mulFloatObjC (.sub (.error e)) = .error e ∧
    a.truedivFloatObjPy (.sub (.error e)) = .error e ∧ a.truedivFloatObjC (.sub (.error e)) = .error e

theorem unpack_ne_two (l : List Int) (h : l.length ≠ 2) :
    (unpackRatioPy (.tuple l)).raises "ValueError" ∧ (unpackRatioPy (.list l)).raises "ValueError" ∧
    (getFloatAsIntegerRatioC (.tuple l)).raises "ValueError" := by
  match l, h with
  | [], _ => exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  | [_], _ => exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  | [_, _], h => exact absurd rfl h
  | _ :: _ :: _ :: _, _ => exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

theorem getRatioC_list (l : List Int) : (getFloatAsIntegerRatioC (.list l)).raises "TypeError" :=
  ⟨_, rfl, rfl⟩

theorem timedeltaFloatRatio_proven : TimedeltaFloatRatio := by
  intro a x n d l e ha
  have hm : ∀ r : Py (Int × Int), (do let (n, d) ← r; usToDeltaPy (← divideAndRound (a.toUs * n) d)) =
      (do let p ← r; usToDeltaPy (← divideAndRound (a.toUs * p.1) p.2)) := by
    intro r; cases r <;> rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, ?_, fun hl => ?_, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · unfold Delta.mulFloatObjPy Delta.mulFloatPy
    simp only [FloatOperand.ratioCall]
    cases h : asRatio x with
    | error e => simp [bind, Except.bind, Functor.map, Except.map]
    | ok p => obtain ⟨n, d⟩ := p; simp [bind, Except.bind, Functor.map, Except.map, unpackRatioPy, getFloatAsIntegerRatioC]
  · unfold Delta.mulFloatObjC Delta.mulFloatC
    simp only [FloatOperand.ratioCall]
    cases h : asRatio x with
    | error e => simp [bind, Except.bind, Functor.map, Except.map]
    | ok p => obtain ⟨n, d⟩ := p; simp [bind, Except.bind, Functor.map, Except.map, unpackRatioPy, getFloatAsIntegerRatioC]
  · unfold Delta.truedivFloatObjPy Delta.truedivFloatPy
    simp only [FloatOperand.ratioCall]
    cases h : asRatio x with
    | error e => simp [bind, Except.bind, Functor.map, Except.map]
    | ok p => obtain ⟨n, d⟩ := p; simp [bind, Except.bind, Functor.map, Except.map, unpackRatioPy, getFloatAsIntegerRatioC]
  · unfold Delta.truedivFloatObjC Delta.truedivFloatC
    simp only [FloatOperand.ratioCall]
    cases h : asRatio x with
    | error e => simp [bind, Except.bind, Functor.map, Except.map]
    | ok p => obtain ⟨n, d⟩ := p; simp [bind, Except.bind, Functor.map, Except.map, unpackRatioPy, getFloatAsIntegerRatioC]
  · show SameOutcome (do usToDeltaPy (← divideAndRound (a.toUs * n) d))
      (do usToDeltaC (← divideNearestC (a.toUs * n) d))
    rw [(divideAndRound_proven (a.toUs * n) d).1]
    apply sameOutcome_bind
    intro q; rw [usToDeltaPy_eq]; exact sameOutcome_mk q
  · show SameOutcome (do usToDeltaPy (← divideAndRound (d * a.toUs) n))
      (do usToDeltaC (← divideNearestC (a.toUs * d) n))
    rw [Int.mul_comm d a.toUs, (divideAndRound_proven (a.toUs * d) n).1]
    apply sameOutcome_bind
    intro q; rw [usToDeltaPy_eq]; exact sameOutcome_mk q
  · obtain ⟨e1, he1, hc1⟩ := getRatioC_list l
    exact ⟨e1, by simp [Delta.mulFloatObjC, FloatOperand.ratioCall, he1, bind, Except.bind], hc1⟩
  · obtain ⟨e1, he1, hc1⟩ := getRatioC_list l
    exact ⟨e1, by simp [Delta.truedivFloatObjC, FloatOperand.ratioCall, he1, bind, Except.bind], hc1⟩
  · obtain ⟨⟨e1, he1, hc1⟩, ⟨e2, he2, hc2⟩, ⟨e3, he3, hc3⟩⟩ := unpack_ne_two l hl
    exact ⟨⟨e1, by simp [Delta.mulFloatObjPy, FloatOperand.ratioCall, he1, bind, Except.bind], hc1⟩,
      ⟨e3, by simp [Delta.mulFloatObjC, FloatOperand.ratioCall, he3, bind, Except.bind], hc3⟩,
      ⟨e2, by simp [Delta.mulFloatObjPy, FloatOperand.ratioCall, he2, bind, Except.bind], hc2⟩,
      ⟨e1, by simp [Delta.truedivFloatObjPy, FloatOperand.ratioCall, he1, bind, Except.bind], hc1⟩,
      ⟨e3, by simp [Delta.truedivFloatObjC, FloatOperand.ratioCall, he3, bind, Except.bind], hc3⟩,
      ⟨e2, by simp [Delta.truedivFloatObjPy, FloatOperand.ratioCall, he2, bind, Except.bind], hc2⟩⟩
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-- `timedelta / timedelta` is the correctly rounded quotient of the two microsecond counts
in both twins (`usec / other._to_microseconds()` in Python, `PyNumber_TrueDivide` in C, both
`long_true_divide`), for every nonzero divisor; the quotient is below `2**67` in magnitude,
so it never overflows. Open: needs the rounding theory of `long_true_divide`
(`longobj-true-divide-rounds`). -/
def TimedeltaTruedivDelta : Prop :=
  ∀ a b : Delta, a.Valid → b.Valid → b.toUs ≠ 0 →
    a.truedivDeltaPy b = a.truedivDeltaC b ∧
    a.truedivDeltaPy b =
      .ok (LongObj.Cplx.Dbl.roundQ (decide (a.toUs < 0) != decide (b.toUs < 0)) a.toUs.natAbs b.toUs.natAbs)

end PyLean.Datetime
