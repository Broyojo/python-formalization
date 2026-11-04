import PyLean.Datetime.TdFloat
import PyLean.Binary64.Props2

/-!
`timedelta.__new__` (Lib/_pydatetime.py:657-768) on exact binary64 floats: the int path of
`deltaNumPy` is the int model `deltaPy` (so `TimedeltaCtorTwins` and `TimedeltaCtorExact` hold
for it), and the twins agree for every combination of ints and integral-valued floats of
moderate size, the case the refuted `TimedeltaFloatCtorTwins` leaves standing. CPython 3.15.2.
-/

namespace PyLean.Datetime

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-! ### Integral doubles -/

theorem floor_half_add (k : Int) : ((k : Rat) + mkRat 1 2).floor = k := by
  rw [Rat.add_comm, Rat.floor_add_intCast]
  have : (mkRat 1 2).floor = 0 := by decide
  rw [this, Int.zero_add]

/-- C `round` of an integral double is itself. -/
theorem roundAway_int {y : F64} {t : Int} (hy : y.isFinite = true) (ht : y.toRat = t) (hb : t.natAbs < 2 ^ 53) :
    (F64.roundAway y).isFinite = true ∧ (F64.roundAway y).toRat = t := by
  have hn := isNaN_false_of_finite hy
  by_cases hz : y.isZero = true
  · have e : F64.roundAway y = y := by simp [F64.roundAway, hn, hy, hz]
    rw [e]; exact ⟨hy, ht⟩
  · have hz' : y.isZero = false := by simpa using hz
    have ht0 : t ≠ 0 := by
      intro h0
      have : y.isZero = true := (isZero_iff_toRat hy).2 (by rw [ht, h0]; rfl)
      rw [this] at hz'; cases hz'
    have e : F64.roundAway y = F64.ofIntS y.sign t := by
      simp only [F64.roundAway, hn, hy, hz', Bool.not_true, Bool.false_or, Bool.false_eq_true, ite_false]
      rw [ht]
      cases y.sign
      · simp only [Bool.false_eq_true, ite_false]
        rw [floor_half_add t]
      · simp only [ite_true]
        rw [← Rat.intCast_neg, floor_half_add (-t), Int.neg_neg]
    rw [e]
    unfold F64.ofIntS
    rw [if_neg ht0]
    exact ofInt_small hb

theorem dHalf_facts : dHalf.isFinite = true ∧ dHalf.toRat ≠ 0 := by decide +kernel

/-- Python's `round()` of an integral double (`float_round_int`: C `round`, then the
half-way correction, which does not fire) is the integer. -/
theorem round_int_value {y : F64} {t : Int} (hy : y.isFinite = true) (ht : y.toRat = t) (hb : t.natAbs < 2 ^ 53) :
    float_round_int y = .ok t := by
  obtain ⟨hrf, hrv⟩ := roundAway_int hy ht hb
  have hnf : (F64.roundAway y).neg.isFinite = true := by rw [neg_isFinite]; exact hrf
  have hsub : (F64.sub y (F64.roundAway y)).isFinite = true ∧ (F64.sub y (F64.roundAway y)).toRat = 0 := by
    unfold F64.sub
    rw [add_of_finite hy hnf, toRat_neg, ht, hrv]
    simp only [Rat.add_neg_cancel, ite_true]
    exact ⟨zero_isFinite _, zero_toRat _⟩
  have habs : (F64.sub y (F64.roundAway y)).abs.isFinite = true ∧ (F64.sub y (F64.roundAway y)).abs.toRat = 0 := by
    unfold F64.abs
    split
    · rw [neg_isFinite, toRat_neg, hsub.2]; exact ⟨hsub.1, by decide⟩
    · exact hsub
  have heq : F64.eq (F64.sub y (F64.roundAway y)).abs dHalf = false := by
    rw [eq_of_finite habs.1 dHalf_facts.1, habs.2]
    exact decide_eq_false (fun h => dHalf_facts.2 h.symm)
  unfold float_round_int
  simp only [heq, Bool.false_eq_true, ite_false]
  simp [PyLong_FromDouble, isInf_false_of_finite hrf, isNaN_false_of_finite hrf, truncInt_of_int hrv]

theorem tdToFloat_small {m : Int} (hb : m.natAbs < 2 ^ 53) : tdToFloat m = .ok (F64.ofInt m) := by
  have h := ofInt_small hb
  simp [tdToFloat, PyLong_AsDouble, isInf_false_of_finite h.1]

theorem mul_zero_f1e6 : F64.mul (F64.zero false) f1e6 = F64.zero false := by decide +kernel

theorem add_ofInt_zero {m : Int} (hb : m.natAbs < 2 ^ 53) :
    (F64.add (F64.ofInt m) (F64.zero false)).isFinite = true ∧ (F64.add (F64.ofInt m) (F64.zero false)).toRat = m := by
  have h := ofInt_small hb
  rw [add_of_finite h.1 (zero_isFinite false), h.2, zero_toRat]
  split
  · rename_i h0
    rw [Rat.add_zero] at h0
    exact ⟨zero_isFinite _, by rw [zero_toRat, h0]⟩
  · rw [Rat.add_zero]
    exact ofInt_small hb

/-- `round(microseconds + usdouble)` on the int branch (Py:744): `microseconds` is
`m % 10**6` and `usdouble` is `0.0 * 1e6`. -/
theorem round_mod (n : Int) :
    (do float_round_int (F64.add (← tdToFloat (n % 1000000)) (F64.mul (F64.zero false) f1e6))) =
      (.ok (n % 1000000) : Py Int) := by
  have h0 : 0 ≤ n % 1000000 := Int.emod_nonneg _ (by decide)
  have h1 : n % 1000000 < 1000000 := Int.emod_lt_of_pos _ (by decide)
  have hb : (n % 1000000).natAbs < 2 ^ 53 := by omega
  rw [tdToFloat_small hb, mul_zero_f1e6]
  obtain ⟨hf, hv⟩ := add_ofInt_zero hb
  exact round_int_value hf hv hb

/-- `deltaNumPy` with int arguments is the int-only model `deltaPy`, whose twin agreement and
exactness are `TimedeltaCtorTwins` and `TimedeltaCtorExact`: on ints the type loop passes, the
float branches (:692-698, :708-713, :732-737) are not taken, and `round(microseconds +
usdouble)` (:744) adds `0.0 * 1e6` to an int below `10**6`, which `round` gives back. -/
theorem timedeltaNumPyInt_proven : TimedeltaNumPyInt := by
  intro days seconds microseconds milliseconds minutes hours weeks
  have hr := round_mod (microseconds + milliseconds * 1000)
  simp only [bind, Except.bind] at hr
  simp only [deltaNumPy, deltaPy, tdTypeCheckPy, tdMul, tdAdd, bind, Except.bind, pure, Except.pure]
  split at hr
  · cases hr
  · rename_i x hx
    rw [hr]
    simp only [Int.add_assoc]
    rfl

end PyLean.Datetime
