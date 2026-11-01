import PyLean.Binary64.Dtoa
import PyLean.Binary64.Lemmas

/-!
Properties of the foundation and of the arithmetic half of `Objects/floatobject.c`.
Each property quantifies over all `F64`. A hypothesis `x.isFinite = true` only
selects the branch the statement is about; the NaN and infinity branches have
their own statements or follow IEEE 754 by the definitions in `Model.lean`.
-/

namespace PyLean.Binary64

open F64

/-! ## Rounding -/

/-- `r` is the IEEE 754 round-to-nearest-even of the exact value `q`: no NaN, at least
as close as every finite float, the even mantissa on a tie, and an infinity exactly
past the overflow limit. -/
structure IsRounding (q : Rat) (r : F64) : Prop where
  notNaN : r.isNaN = false
  nearest : r.isFinite = true → ∀ y : F64, y.isFinite = true →
    Rat.abs (q - r.toRat) ≤ Rat.abs (q - y.toRat)
  tie : r.isFinite = true → ∀ y : F64, y.isFinite = true →
    Rat.abs (q - r.toRat) = Rat.abs (q - y.toRat) → y.toRat ≠ r.toRat → r.mant % 2 = 0
  inf : r.isInf = true ↔ overflowLimit ≤ Rat.abs q

theorem ofRat_isRounding (q : Rat) : IsRounding q (ofRat q) where
  notNaN := ofRat_isNaN q
  nearest := fun h _ hy => ofRat_nearest q h hy
  tie := fun h _ hy heq hne => ofRat_tie q h hy heq hne
  inf := ofRat_isInf q

theorem zero_isRounding (s : Bool) : IsRounding 0 (zero s) where
  notNaN := isNaN_false_of_finite (zero_isFinite s)
  nearest := fun _ y _ => by
    rw [zero_toRat, Rat.sub_self, abs_of_nonneg (a := 0) (by decide)]
    exact abs_nonneg _
  tie := fun _ y _ heq hne => by
    exfalso
    rw [zero_toRat, Rat.sub_self, abs_of_nonneg (a := 0) (by decide)] at heq
    have := abs_le_zero (a := 0 - y.toRat) (by rw [← heq]; exact Rat.le_refl)
    rw [zero_toRat] at hne
    grind
  inf := by
    rw [isInf_false_of_finite (zero_isFinite s), abs_of_nonneg (a := 0) (by decide)]
    constructor
    · intro h; cases h
    · intro h; exact absurd h (Rat.not_le.2 overflowLimit_pos)

/-- Every rational rounds to a correct IEEE result. -/
def RoundToNearestEven : Prop := ∀ q : Rat, IsRounding q (ofRat q)

theorem roundToNearestEven_proven : RoundToNearestEven := ofRat_isRounding

/-- A datum is its bit pattern, and a nonzero finite datum is its exact value. -/
def BitsAndValueRoundTrip : Prop :=
  (∀ x : F64, ofBits x.bits = x) ∧
    ∀ x : F64, x.isFinite = true → x.isZero = false → ofRat x.toRat = x

theorem bitsAndValueRoundTrip_proven : BitsAndValueRoundTrip :=
  ⟨ofBits_bits, fun _ hx hz => ofRat_toRat hx hz⟩

/-! ## Arithmetic on finite operands -/

theorem not_nan2 {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    (x.isNaN || y.isNaN) = false := by
  simp [isNaN_false_of_finite hx, isNaN_false_of_finite hy]

theorem add_of_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    add x y = if x.toRat + y.toRat = 0 then zero (x.sign && y.sign) else ofRat (x.toRat + y.toRat) := by
  simp only [add, not_nan2 hx hy, isInf_false_of_finite hx, isInf_false_of_finite hy]
  rfl

theorem mul_of_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    mul x y = if x.toRat * y.toRat = 0 then zero (x.sign != y.sign) else ofRat (x.toRat * y.toRat) := by
  simp only [mul, not_nan2 hx hy, isInf_false_of_finite hx, isInf_false_of_finite hy]
  rfl

theorem isZero_iff_toRat {x : F64} (hx : x.isFinite = true) : x.isZero = true ↔ x.toRat = 0 := by
  constructor
  · exact toRat_of_isZero
  · intro h
    cases hz : x.isZero
    · exfalso
      have hm := mant_pos_of_not_zero hz
      have hxv : 0 < (x.mant : Rat) * pw x.lsbExp := Rat.mul_pos (natCast_pos' hm) (pw_pos _)
      rw [toRat_of_finite hx] at h
      split at h <;> grind
    · rfl

theorem div_of_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true)
    (hz : y.isZero = false) :
    div x y = if x.toRat / y.toRat = 0 then zero (x.sign != y.sign) else ofRat (x.toRat / y.toRat) := by
  simp only [div, not_nan2 hx hy, isInf_false_of_finite hx, isInf_false_of_finite hy, hz]
  rfl

theorem d0_isFinite : d0.isFinite = true := zero_isFinite false

theorem d0_toRat : d0.toRat = 0 := zero_toRat false

theorem eq_of_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    F64.eq x y = decide (x.toRat = y.toRat) := by
  simp only [F64.eq, not_nan2 hx hy, isInf_false_of_finite hx, isInf_false_of_finite hy]
  rfl

theorem lt_of_finite {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    F64.lt x y = decide (x.toRat < y.toRat) := by
  simp only [F64.lt, not_nan2 hx hy, isInf_false_of_finite hx, isInf_false_of_finite hy]
  rfl

/-- `x + y` on floats is the exact sum, rounded; an exact zero is `-0.0` only when
both operands are negative. -/
def FloatAddCorrect : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true →
    ∃ r, float_add (.float x) (.float y) = .ok (some r) ∧ IsRounding (x.toRat + y.toRat) r ∧
      (x.toRat + y.toRat = 0 → r.sign = (x.sign && y.sign))

theorem floatAddCorrect_proven : FloatAddCorrect := by
  intro x y hx hy
  refine ⟨add x y, rfl, ?_, ?_⟩
  · rw [add_of_finite hx hy]
    split
    · rename_i h; rw [h]; exact zero_isRounding _
    · exact ofRat_isRounding _
  · intro h
    rw [add_of_finite hx hy, if_pos h, zero_sign]

/-- `x - y` on floats is the exact difference, rounded. -/
def FloatSubCorrect : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true →
    ∃ r, float_sub (.float x) (.float y) = .ok (some r) ∧ IsRounding (x.toRat - y.toRat) r

theorem floatSubCorrect_proven : FloatSubCorrect := by
  intro x y hx hy
  refine ⟨sub x y, rfl, ?_⟩
  have hy' : y.neg.isFinite = true := by rw [neg_isFinite]; exact hy
  unfold sub
  rw [add_of_finite hx hy', toRat_neg]
  have e : x.toRat + -y.toRat = x.toRat - y.toRat := by grind
  rw [e]
  split
  · rename_i h; rw [h]; exact zero_isRounding _
  · exact ofRat_isRounding _

/-- `x * y` on floats is the exact product, rounded, and a zero result carries the
exclusive or of the signs. -/
def FloatMulCorrect : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true →
    ∃ r, float_mul (.float x) (.float y) = .ok (some r) ∧ IsRounding (x.toRat * y.toRat) r ∧
      (x.toRat * y.toRat = 0 → r.sign = (x.sign != y.sign))

theorem floatMulCorrect_proven : FloatMulCorrect := by
  intro x y hx hy
  refine ⟨mul x y, rfl, ?_, ?_⟩
  · rw [mul_of_finite hx hy]
    split
    · rename_i h; rw [h]; exact zero_isRounding _
    · exact ofRat_isRounding _
  · intro h
    rw [mul_of_finite hx hy, if_pos h, zero_sign]

/-- `x / y` raises `ZeroDivisionError` for a zero `y` (even for a NaN or infinite
`x`), and otherwise is the exact quotient, rounded. -/
def FloatDivCorrect : Prop :=
  ∀ x y : F64,
    (y.isZero = true → float_div (.float x) (.float y) = .error (.zeroDivisionError "division by zero")) ∧
    (x.isFinite = true → y.isFinite = true → y.isZero = false →
      ∃ r, float_div (.float x) (.float y) = .ok (some r) ∧ IsRounding (x.toRat / y.toRat) r)

theorem floatDivCorrect_proven : FloatDivCorrect := by
  intro x y
  constructor
  · intro hz
    have hy := isFinite_of_isZero hz
    have : F64.eq y d0 = true := by
      rw [eq_of_finite hy d0_isFinite, d0_toRat, toRat_of_isZero hz]; rfl
    simp only [float_div, withDoubles, convertToDouble]
    simp [this, bind, Except.bind, zeroDiv, pure, Except.pure]
  · intro hx hy hz
    refine ⟨div x y, ?_, ?_⟩
    · have : F64.eq y d0 = false := by
        rw [eq_of_finite hy d0_isFinite, d0_toRat]
        have : y.toRat ≠ 0 := fun h => by
          rw [(isZero_iff_toRat hy).2 h] at hz; cases hz
        simp [this]
      simp only [float_div, withDoubles, convertToDouble]
      simp [this, bind, Except.bind, pure, Except.pure]
    · rw [div_of_finite hx hy hz]
      split
      · rename_i h; rw [h]; exact zero_isRounding _
      · exact ofRat_isRounding _

/-- `x * y + z` with a single rounding. -/
def FmaCorrect : Prop :=
  ∀ x y z : F64, x.isFinite = true → y.isFinite = true → z.isFinite = true →
    IsRounding (x.toRat * y.toRat + z.toRat) (fma x y z)

theorem fmaCorrect_proven : FmaCorrect := by
  intro x y z hx hy hz
  have e : fma x y z = if x.toRat * y.toRat + z.toRat = 0
      then zero ((x.sign != y.sign) && z.sign) else ofRat (x.toRat * y.toRat + z.toRat) := by
    simp only [fma, isNaN_false_of_finite hx, isNaN_false_of_finite hy, isNaN_false_of_finite hz,
      isInf_false_of_finite hx, isInf_false_of_finite hy, isInf_false_of_finite hz]
    rfl
  rw [e]
  split
  · rename_i h; rw [h]; exact zero_isRounding _
  · exact ofRat_isRounding _

/-- An int converts to its exact value rounded, and `OverflowError` is raised exactly
for the ints that round past `DBL_MAX`. -/
def IntToFloatCorrect : Prop :=
  ∀ n : Int,
    (overflowLimit ≤ Rat.abs n ↔
      PyLong_AsDouble n = .error (.overflowError "int too large to convert to float")) ∧
    (Rat.abs n < overflowLimit →
      ∃ r, r.isFinite = true ∧ PyLong_AsDouble n = .ok r ∧ IsRounding n r ∧
        convertToDouble (.int n) = .ok (some r))

theorem intToFloatCorrect_proven : IntToFloatCorrect := by
  intro n
  have hdef : PyLong_AsDouble n = if (ofInt n).isInf then
      .error (.overflowError "int too large to convert to float") else .ok (ofInt n) := rfl
  constructor
  · constructor
    · intro h
      have hi : (ofInt n).isInf = true := (ofRat_isInf (n : Rat)).2 h
      rw [hdef, hi]; rfl
    · intro h
      rw [hdef] at h
      cases hi : (ofInt n).isInf
      · rw [hi] at h; simp at h
      · exact (ofRat_isInf (n : Rat)).1 hi
  · intro hlt
    have hf : (ofInt n).isFinite = true := (ofRat_isFinite (n : Rat)).2 hlt
    have hok : PyLong_AsDouble n = .ok (ofInt n) := by
      rw [hdef, isInf_false_of_finite hf]; rfl
    refine ⟨ofInt n, hf, hok, ofRat_isRounding _, ?_⟩
    simp only [convertToDouble, hok]; rfl

end PyLean.Binary64
