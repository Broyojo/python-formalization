import PyLean.MathInt.FltClassify
import PyLean.Binary64.CompareProps

/-!
Lemmas about rounding used by the `Modules/mathmodule.c` properties: what `ofRat` does past
the overflow limit and below half the smallest subnormal, the sign of a rounded value.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

theorem toRat_neg_iff_sign {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) :
    (x.toRat < 0) = (x.sign = true) := by
  have hm := mant_pos_of_not_zero hz
  have hv : 0 < (x.mant : Rat) * pw x.lsbExp := Rat.mul_pos (natCast_pos' hm) (pw_pos _)
  rw [toRat_of_finite hf]
  cases x.sign
  · simp only [Bool.false_eq_true, ↓reduceIte, eq_iff_iff, iff_false]
    exact Rat.not_lt.2 (Rat.le_of_lt hv)
  · simp only [↓reduceIte, eq_iff_iff, iff_true]
    grind

/-- The smallest nonzero magnitude. -/
theorem abs_toRat_ge_tiny {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) :
    pw (-1074) ≤ Rat.abs x.toRat := by
  have hm := mant_pos_of_not_zero hz
  have hm0 : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  have habs : Rat.abs x.toRat = (x.mant : Rat) * pw x.lsbExp := by
    rw [toRat_of_finite hf]
    split
    · rw [abs_neg, abs_of_nonneg hm0]
    · rw [abs_of_nonneg hm0]
  rw [habs]
  have h1 : (1 : Rat) ≤ (x.mant : Rat) := by
    have : ((1 : Nat) : Rat) ≤ (x.mant : Rat) := Rat.natCast_le_natCast.2 hm
    simpa using this
  have h2 : pw (-1074) ≤ pw x.lsbExp := pw_le (lsbExp_ge x)
  have a1 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (pw_pos x.lsbExp))
  rw [Rat.one_mul] at a1
  exact Rat.le_trans h2 a1

/-- Past the overflow limit, `ofRat` is the infinity of the sign. -/
theorem ofRat_big {q : Rat} (h : overflowLimit ≤ Rat.abs q) : ofRat q = F64.inf (decide (q < 0)) := by
  have hq : q ≠ 0 := by
    intro h0; subst h0
    rw [abs_of_nonneg (a := 0) (by decide)] at h
    exact absurd h (Rat.not_le.2 overflowLimit_pos)
  rcases ofRat_cases hq with ⟨_, hinf⟩ | ⟨m, e, hdec, _, _⟩
  · exact hinf
  · exfalso
    have := (ofRat_isInf q).2 h
    rw [isInf_false_of_finite hdec.finite] at this
    cases this

/-- Below half the smallest subnormal, `ofRat` is the zero of the sign. -/
theorem ofRat_tiny {q : Rat} (hq : q ≠ 0) (h : Rat.abs q < pw (-1075)) :
    ofRat q = F64.zero (decide (q < 0)) := by
  have hlim : Rat.abs q < overflowLimit := by
    have : pw (-1075) < overflowLimit := by
      have a : pw (-1075) < pw 970 := pw_lt (by omega)
      have b : pw 970 ≤ overflowLimit := by
        unfold overflowLimit
        have : (1 : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := by
          have : ((1 : Nat) : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := Rat.natCast_le_natCast.2 (by decide)
          simpa using this
        have := Rat.mul_le_mul_of_nonneg_right this (Rat.le_of_lt (pw_pos 970))
        rwa [Rat.one_mul] at this
      grind
    grind
  have hf := (ofRat_isFinite q).2 hlim
  rcases ofRat_cases hq with ⟨hge, _⟩ | ⟨m, e, hdec, _, _⟩
  · exfalso
    rw [← abs_eq_ite] at hge
    exact absurd hlim (Rat.not_lt.2 hge)
  · have hz : (ofRat q).isZero = true := by
      apply Classical.byContradiction
      intro hz
      have hz' : (ofRat q).isZero = false := by simpa using hz
      have hge := abs_toRat_ge_tiny hf hz'
      have hnear := ofRat_nearest q hf (zero_isFinite false)
      rw [zero_toRat, show q - 0 = q by grind] at hnear
      -- |q - r| >= |r| - |q| > 2^-1075 > |q|
      have h2 : pw (-1074) = 2 * pw (-1075) := by
        have := pw_succ (-1075); simpa using this
      have tri : Rat.abs (ofRat q).toRat ≤ Rat.abs (q - (ofRat q).toRat) + Rat.abs q := by
        rw [abs_eq_ite (ofRat q).toRat, abs_eq_ite (q - (ofRat q).toRat), abs_eq_ite q]
        split <;> split <;> split <;> grind
      grind
    have := eq_zero_of_isZero hz
    rw [this, hdec.sign]

/-- A rounded nonzero rational keeps its sign. -/
theorem ofRat_sign {q : Rat} (hq : q ≠ 0) : (ofRat q).sign = decide (q < 0) := by
  rcases ofRat_cases hq with ⟨_, hinf⟩ | ⟨m, e, hdec, _, _⟩
  · rw [hinf]; exact (inf_bits _).2
  · exact hdec.sign

theorem isZeroC_eq (x : F64) : isZeroC x = x.isZero := eq_c0_iff

theorem longAsDouble_ok {n : Int} {x : F64} (h : PyLong_AsDouble n = .ok x) :
    x = F64.ofInt n ∧ x.isFinite = true := by
  unfold PyLong_AsDouble at h
  simp only [] at h
  by_cases hi : (F64.ofInt n).isInf = true
  · rw [if_pos hi] at h; cases h
  · rw [if_neg hi] at h
    cases h
    refine ⟨rfl, ?_⟩
    rcases classify (F64.ofInt n) with h | h | h
    · exact h
    · exact absurd h hi
    · rw [show F64.ofInt n = ofRat n from rfl, ofRat_isNaN] at h; cases h

theorem longAsDouble_err {n : Int} {e : PyExc} (h : PyLong_AsDouble n = .error e) :
    e = .overflowError "int too large to convert to float" := by
  unfold PyLong_AsDouble at h
  simp only [] at h
  by_cases hi : (F64.ofInt n).isInf = true
  · rw [if_pos hi] at h; cases h; rfl
  · rw [if_neg hi] at h; cases h

/-- Rounding is monotone. -/
theorem ofRat_mono {q1 q2 : Rat} (h : q1 ≤ q2) (h1 : (ofRat q1).isFinite = true)
    (h2 : (ofRat q2).isFinite = true) : (ofRat q1).toRat ≤ (ofRat q2).toRat := by
  apply Classical.byContradiction
  intro hlt
  have hlt' : (ofRat q2).toRat < (ofRat q1).toRat := Rat.not_le.1 hlt
  have n1 := ofRat_nearest q1 h1 h2
  have n2 := ofRat_nearest q2 h2 h1
  generalize (ofRat q1).toRat = a at n1 n2 hlt'
  generalize (ofRat q2).toRat = b at n1 n2 hlt'
  rw [abs_eq_ite (q1 - a), abs_eq_ite (q1 - b)] at n1
  rw [abs_eq_ite (q2 - b), abs_eq_ite (q2 - a)] at n2
  have heq : q1 = q2 := by
    split at n1 <;> split at n1 <;> split at n2 <;> split at n2 <;> grind
  subst heq
  grind

/-- `ofRat` of a rational `>= 1` that stays finite is `>= 1`. -/
theorem ofRat_ge_one {q : Rat} (h : 1 ≤ q) (hf : (ofRat q).isFinite = true) :
    1 ≤ (ofRat q).toRat := by
  have h1 : ofRat 1 = F64.one := by decide +kernel
  have hf1 : (ofRat 1).isFinite = true := by rw [h1]; decide +kernel
  have := ofRat_mono h hf1 hf
  rwa [h1, show F64.one.toRat = 1 by decide +kernel] at this

end PyLean.MathInt
