import PyLean.MathInt.IntOps
import PyLean.MathInt.Divmod

/-!
`round(int, ndigits)`: exact, round-half-to-even to a multiple of
`10**-ndigits`.
-/

namespace PyLean.MathInt

open PyLean

/-- `_PyLong_DivmodNear(a, b)` for `b > 0`: `a == q*b + r`, `abs(r) <= b/2`,
and on a tie `q` is even (longobject.c:6008-6012). -/
theorem divmodNear_spec (a b : Int) (hb : 0 < b) :
    a = (divmodNear a b).1 * b + (divmodNear a b).2 ∧
    2 * (divmodNear a b).2.natAbs ≤ b ∧
    (2 * ((divmodNear a b).2.natAbs : Int) = b → (divmodNear a b).1 % 2 = 0) := by
  obtain ⟨B, rfl⟩ : ∃ B : Nat, b = B := ⟨b.toNat, by omega⟩
  have hB0 : 0 < B := by omega
  have nb : ¬ ((B : Int) < 0) := by omega
  obtain ⟨A, hA | hA⟩ := natAbs_cases a <;> subst hA
  all_goals
    have e1 := Nat.div_add_mod A B
    have m1 := Nat.mod_lt A hB0
    unfold divmodNear
    simp only [Int.neg_tdiv, Int.neg_tmod, ← Int.ofNat_tdiv, ← Int.ofNat_tmod, nb,
      decide_false, Int.natAbs_neg, Int.natAbs_natCast, ite_false]
    generalize A / B = Q at *
    generalize A % B = R at *
  · -- a = A ≥ 0
    have : decide ((A : Int) < 0) = false := by simp
    simp only [this, ne_eq, not_true_eq_false, ite_false]
    by_cases hc : 2 * (R : Int) > B ∨ (2 * (R : Int) = B ∧ Q % 2 = 1)
    · simp only [hc, ite_true]
      try simp only [Int.natAbs_natCast]
      refine ⟨by grind, ?_, ?_⟩ <;> omega
    · simp only [hc, ite_false]
      try simp only [Int.natAbs_natCast]
      refine ⟨by grind, ?_, ?_⟩ <;> omega
  · -- a = -A
    by_cases hA0 : A = 0
    · subst hA0
      simp at e1
      obtain ⟨h1, rfl⟩ := e1
      have hQ : Q = 0 := by rcases Nat.mul_eq_zero.mp h1 with h | h <;> omega
      subst hQ
      simp [nb]
    have : decide (-(A : Int) < 0) = true := by simp; omega
    have h2 : -(2 * -(R : Int)) = 2 * R := by omega
    simp only [this, ne_eq, decide_false, Bool.true_eq_false, not_false_eq_true, ite_true,
      Int.neg_neg, h2]
    by_cases hc : 2 * (R : Int) > B ∨ (2 * (R : Int) = B ∧ Q % 2 = 1)
    · simp only [hc, ite_true]
      refine ⟨by grind, ?_, ?_⟩ <;> omega
    · simp only [hc, ite_false]
      refine ⟨by grind, ?_, ?_⟩ <;> omega

/-- Built-in `round()` docs: "values are rounded to the closest multiple of 10
to the power minus ndigits; if two multiples are equally close, rounding is
done toward the even choice", with an int result for an int argument; for
`ndigits >= 0` or `None` an int is returned unchanged. -/
def RoundIntHalfEven : Prop :=
  ∀ (x : Int) (nd : Option Int),
    (∀ d, nd = some d → d < 0 →
      let p : Int := 10 ^ (-d).toNat
      ∃ q, roundInt x nd = q * p ∧ 2 * (x - roundInt x nd).natAbs ≤ p ∧
        (2 * ((x - roundInt x nd).natAbs : Int) = p → q % 2 = 0)) ∧
    ((∀ d, nd = some d → 0 ≤ d) → roundInt x nd = x)

theorem roundIntHalfEven_proven : RoundIntHalfEven := by
  intro x nd
  refine ⟨fun d hd hneg => ?_, fun h => ?_⟩
  · subst hd
    have hp : (0 : Int) < 10 ^ (-d).toNat := Int.pow_pos (by decide)
    obtain ⟨e, h2, h3⟩ := divmodNear_spec x (10 ^ (-d).toNat) hp
    have hr : roundInt x (some d) = x - (divmodNear x (10 ^ (-d).toNat)).2 := by
      simp [roundInt, show ¬ (0 ≤ d) by omega]
    refine ⟨(divmodNear x (10 ^ (-d).toNat)).1, ?_, ?_, ?_⟩
    · rw [hr]; omega
    · rw [hr, show x - (x - (divmodNear x (10 ^ (-d).toNat)).2) = (divmodNear x (10 ^ (-d).toNat)).2 by omega]
      exact h2
    · rw [hr, show x - (x - (divmodNear x (10 ^ (-d).toNat)).2) = (divmodNear x (10 ^ (-d).toNat)).2 by omega]
      exact h3
  · cases nd with
    | none => rfl
    | some d => simp [roundInt, h d rfl]

end PyLean.MathInt
