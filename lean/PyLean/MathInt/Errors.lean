import PyLean.MathInt.Model

/-!
Documented argument errors and the `k > n` case of `comb` / `perm`.
-/

namespace PyLean.MathInt

open PyLean

/-- `math.isqrt` docs: the argument must be nonnegative; mathintegermodule.c:367-372
raises `ValueError` otherwise. -/
def IsqrtRejectsNegative : Prop :=
  ∀ n : Int, n < 0 → (isqrt n).raises "ValueError"

theorem isqrtRejectsNegative_proven : IsqrtRejectsNegative := by
  intro n h
  exact ⟨_, by simp [isqrt, h]; rfl, rfl⟩

/-- `math.comb` / `math.perm` docstrings: "Raises ValueError if either of the
arguments are negative." -/
def CombPermRejectNegative : Prop :=
  ∀ n k : Int, (n < 0 ∨ k < 0) →
    (comb n k).raises "ValueError" ∧ (perm n (some k)).raises "ValueError"

theorem combPermRejectNegative_proven : CombPermRejectNegative := by
  intro n k h
  by_cases hn : n < 0
  · exact ⟨⟨_, by simp [comb, hn]; rfl, rfl⟩, ⟨_, by simp [perm, hn]; rfl, rfl⟩⟩
  · have hk : k < 0 := by omega
    exact ⟨⟨_, by simp [comb, hn, hk]; rfl, rfl⟩, ⟨_, by simp [perm, hn, hk]; rfl, rfl⟩⟩

/-- `math.comb` / `math.perm` docstrings: they evaluate "to zero when k > n",
for every size of `n` and `k` (no `OverflowError` here). -/
def CombPermZeroAbove : Prop :=
  ∀ n k : Int, 0 ≤ n → n < k → comb n k = .ok 0 ∧ perm n (some k) = .ok 0

theorem combPermZeroAbove_proven : CombPermZeroAbove := by
  intro n k hn hk
  refine ⟨?_, ?_⟩
  · unfold comb
    simp only [show ¬ n < 0 by omega, show ¬ k < 0 by omega, ite_false]
    split
    · simp [show k > n by omega]
    · simp [show n - k < 0 by omega]
  · simp [perm, show ¬ n < 0 by omega, show ¬ k < 0 by omega, hk]

/-- `math.factorial` docs: "Raises ValueError if n is not integral or is
negative"; arguments above `LONG_MAX` raise `OverflowError`
(mathintegermodule.c:702-706). -/
def FactorialArgErrors : Prop :=
  ∀ n : Int, (n < 0 → (factorial n).raises "ValueError") ∧
    (n > llongMax → (factorial n).raises "OverflowError")

theorem factorialArgErrors_proven : FactorialArgErrors := by
  intro n
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have : ¬ n > (llongMax : Int) := by unfold llongMax; omega
    exact ⟨_, by simp [factorial, this, h]; rfl, rfl⟩
  · exact ⟨_, by simp [factorial, h]; rfl, rfl⟩

end PyLean.MathInt
