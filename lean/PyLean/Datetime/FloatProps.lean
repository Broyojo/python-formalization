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
