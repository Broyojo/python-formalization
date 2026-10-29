import PyLean.MathInt.IntOps

/-!
`divmod` on ints: all three code paths of `l_divmod` (the single-digit fast
path, the `_pylong.int_divmod` twin for huge operands, and `long_divrem` plus
sign fix-up) return the floor quotient and remainder.
-/

namespace PyLean.MathInt

open PyLean

/-- `(q, r)` is Python's `divmod(v, w)`: `q*w + r == v` and `r` has the sign
of `w` with `abs(r) < abs(w)`. -/
def IsFloorDivmod (v w q r : Int) : Prop :=
  q * w + r = v ∧ (0 < w → 0 ≤ r ∧ r < w) ∧ (w < 0 → w < r ∧ r ≤ 0)

/-- Python language reference, "Binary arithmetic operations": `x == (x//y)*y
+ (x%y)`, the modulo result has the sign of the second operand and is smaller
in absolute value; division by zero raises `ZeroDivisionError`. Covers the
single-digit fast path, the `_pylong.int_divmod` path and `long_divrem`. -/
def DivmodFloor : Prop :=
  ∀ v w : Int, (w = 0 → (divmod v w).raises "ZeroDivisionError") ∧
    (w ≠ 0 → ∃ q r, divmod v w = .ok (q, r) ∧ IsFloorDivmod v w q r)

theorem digitCount_zero : digitCount 0 = 0 := by decide

theorem natAbs_cases (v : Int) : ∃ A : Nat, v = A ∨ v = -(A : Int) :=
  ⟨v.natAbs, Int.natAbs_eq v⟩

/-- The single-digit fast path, longobject.c:4275-4315. -/
theorem fastDivmod_floor (v w : Int) (hv : v ≠ 0) (hw : w ≠ 0) :
    IsFloorDivmod v w (fastDivmod v w).1 (fastDivmod v w).2 := by
  obtain ⟨A, hA | hA⟩ := natAbs_cases v <;> obtain ⟨B, hB | hB⟩ := natAbs_cases w <;>
    subst hA hB
  all_goals
    have hA0 : 0 < A := by omega
    have hB0 : 0 < B := by omega
    have e1 := Nat.div_add_mod A B
    have e2 := Nat.div_add_mod (A - 1) B
    have m1 := Nat.mod_lt A hB0
    have m2 := Nat.mod_lt (A - 1) hB0
    have hc : ((A : Int) - 1) = ((A - 1 : Nat) : Int) := by omega
    simp only [fastDivmod, IsFloorDivmod, Int.natAbs_neg, Int.natAbs_natCast, hc,
      ← Int.ofNat_tdiv, ← Int.ofNat_tmod]
    generalize A / B = Q at *
    generalize A % B = R at *
    generalize (A - 1) / B = Q' at *
    generalize (A - 1) % B = R' at *
    have s1 : ¬ ((A : Int) < 0) := by omega
    have s2 : -(A : Int) < 0 := by omega
    have s3 : ¬ ((B : Int) < 0) := by omega
    have s4 : -(B : Int) < 0 := by omega
    simp only [s1, s2, s3, s4, iff_self, iff_true, iff_false, true_iff, false_iff, not_true,
      not_false_eq_true, ite_true, ite_false]
    refine ⟨?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind

theorem pylongDivmodPos_floor (v w : Int) (hw : 0 < w) :
    IsFloorDivmod v w (pylongDivmodPos v w).1 (pylongDivmodPos v w).2 := by
  obtain ⟨B, rfl⟩ : ∃ B : Nat, w = B := ⟨w.toNat, by omega⟩
  have hB0 : 0 < B := by omega
  have t2 : ((B : Int)).toNat = B := by omega
  unfold pylongDivmodPos
  by_cases hv : v < 0
  · obtain ⟨A, rfl⟩ : ∃ A : Nat, v = -(A : Int) - 1 := ⟨(-v - 1).toNat, by omega⟩
    have t : (-(-(A : Int) - 1) - 1).toNat = A := by omega
    simp only [hv, ite_true, t, t2]
    have e1 := Nat.div_add_mod A B
    have m1 := Nat.mod_lt A hB0
    generalize A / B = Q at *
    generalize A % B = R at *
    refine ⟨?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind
  · obtain ⟨A, rfl⟩ : ∃ A : Nat, v = (A : Int) := ⟨v.toNat, by omega⟩
    have t : ((A : Int)).toNat = A := by omega
    simp only [hv, ite_false, t, t2]
    have e1 := Nat.div_add_mod A B
    have m1 := Nat.mod_lt A hB0
    generalize A / B = Q at *
    generalize A % B = R at *
    refine ⟨?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind

/-- `_pylong.int_divmod`, Lib/_pylong.py:528-541. -/
theorem pylongIntDivmod_floor (v w : Int) (hw : w ≠ 0) :
    IsFloorDivmod v w (pylongIntDivmod v w).1 (pylongIntDivmod v w).2 := by
  unfold pylongIntDivmod
  by_cases h : w < 0
  · have := pylongDivmodPos_floor (-v) (-w) (by omega)
    simp only [h, ite_true]
    generalize pylongDivmodPos (-v) (-w) = p at *
    obtain ⟨q, r⟩ := p
    obtain ⟨h1, h2, -⟩ := this
    have := h2 (by omega)
    refine ⟨?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind
  · simp only [h, ite_false]
    exact pylongDivmodPos_floor v w (by omega)

theorem tdiv_tmod_floor (v w : Int) (hw : w ≠ 0) :
    IsFloorDivmod v w (v.tdiv w) (v.tmod w) ∨
    ((v.tmod w < 0 ∧ w > 0) ∨ (v.tmod w > 0 ∧ w < 0)) ∧ IsFloorDivmod v w (v.tdiv w - 1) (v.tmod w + w) := by
  obtain ⟨A, hA | hA⟩ := natAbs_cases v <;> obtain ⟨B, hB | hB⟩ := natAbs_cases w <;>
    subst hA hB
  all_goals
    have hB0 : 0 < B := by omega
    have e1 := Nat.div_add_mod A B
    have m1 := Nat.mod_lt A hB0
    simp only [IsFloorDivmod, Int.neg_tdiv, Int.tdiv_neg, Int.neg_tmod, Int.tmod_neg,
      ← Int.ofNat_tdiv, ← Int.ofNat_tmod]
    generalize A / B = Q at *
    generalize A % B = R at *
    by_cases hR : R = 0
    · subst hR; left; refine ⟨?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind
    · first
      | (left; refine ⟨?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind)
      | (right; refine ⟨by omega, ?_, ?_, ?_⟩ <;> (try intro) <;> (try constructor) <;> grind)

theorem divmod_floor_proven : DivmodFloor := by
  intro v w
  refine ⟨fun h => ?_, fun h => ?_⟩
  · subst h
    refine ⟨.zeroDivisionError "division by zero", ?_, rfl⟩
    simp [divmod, digitCount_zero]
  · unfold divmod
    by_cases h1 : digitCount v.natAbs = 1 ∧ digitCount w.natAbs = 1
    · rw [if_pos h1]
      have hv : v ≠ 0 := by intro h0; subst h0; simp [digitCount_zero] at h1
      exact ⟨_, _, rfl, fastDivmod_floor v w hv h⟩
    · rw [if_neg h1]
      by_cases h2 : digitCount w.natAbs > 300 ∧
          (digitCount v.natAbs : Int) - (digitCount w.natAbs : Int) > 150
      · rw [if_pos h2]
        exact ⟨_, _, rfl, pylongIntDivmod_floor v w h⟩
      · rw [if_neg h2, if_neg h]
        rcases tdiv_tmod_floor v w h with hf | ⟨hc, hf⟩
        · by_cases hc : (v.tmod w < 0 ∧ w > 0) ∨ (v.tmod w > 0 ∧ w < 0)
          · exfalso
            obtain ⟨e, h1', h2'⟩ := hf
            have := Int.tmod_add_tdiv_mul v w
            rcases hc with hc | hc
            · have := h1' hc.2; omega
            · have := h2' hc.2; omega
          · exact ⟨_, _, by simp only [hc, ite_false], hf⟩
        · exact ⟨_, _, by simp only [hc, ite_true], hf⟩

end PyLean.MathInt
