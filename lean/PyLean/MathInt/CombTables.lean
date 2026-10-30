import PyLean.MathInt.Model
import PyLean.MathInt.Combinatorics

/-!
Finite checks of the lookup tables behind the fast paths of
`perm_comb_small`, evaluated by the kernel (`decide`).
-/

namespace PyLean.MathInt

/-- Every fast path of `perm_comb_small` that fires for `n <= 127` returns the
exact binomial coefficient / falling factorial. -/
def smallFastOk : Bool :=
  (List.range 128).all fun n => (List.range 128).all fun k =>
    (!(1 ≤ k && 2 * k ≤ n) ||
      match permCombFast n k true with
      | some r => r * fact k == descFact n k
      | none => true) &&
    (!(1 ≤ k && k ≤ n) ||
      match permCombFast n k false with
      | some r => r == descFact n k
      | none => true)

theorem smallFastOk_eq : smallFastOk = true := by decide +kernel

/-- `fast_comb_limits2[k]` bounds `C(n, k) * k` below `2^64` (k = 1..13). -/
def combLimits2Ok : Bool :=
  (List.range 14).all fun k => !(1 ≤ k) || descFact (fastCombLimits2.getD k 0) k * k < 2 ^ 64 * fact k

theorem combLimits2Ok_eq : combLimits2Ok = true := by decide +kernel

/-- `fast_perm_limits[k]` bounds `P(n, k)` below `2^64` (k = 1..20). -/
def permLimitsOk : Bool :=
  (List.range 21).all fun k => !(1 ≤ k) || descFact (fastPermLimits.getD k 0) k < 2 ^ 64

theorem permLimitsOk_eq : permLimitsOk = true := by decide +kernel

theorem combLimits1_le : ∀ k, fastCombLimits1.getD k 0 ≤ 127 := by
  intro k
  have h : (List.range 40).all (fun k => fastCombLimits1.getD k 0 ≤ 127) = true := by decide +kernel
  by_cases hk : k < 40
  · have := (List.all_eq_true.mp h) k (List.mem_range.mpr hk)
    simpa using this
  · simp [List.getD, List.getElem?_eq_none (show fastCombLimits1.length ≤ k by
      simp [fastCombLimits1]; omega)]

theorem combLimits2_lengths : fastCombLimits2.length = 14 := rfl
theorem combLimits1_length : fastCombLimits1.length = 35 := rfl
theorem permLimits_length : fastPermLimits.length = 21 := rfl
theorem combLimits2_one : fastCombLimits2.getD 1 0 = 2 ^ 64 - 1 := rfl
theorem permLimits_one : fastPermLimits.getD 1 0 = 2 ^ 64 - 1 := rfl

end PyLean.MathInt
