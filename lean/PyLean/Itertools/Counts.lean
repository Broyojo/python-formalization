import PyLean.Itertools.Combinatorics

/-!
The count functions used by the enumeration specs (`choose` by Pascal's rule,
`perm` as a falling factorial) are the documented factorial formulas.
-/

namespace PyLean.Itertools

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem choose_zero (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem choose_above : ∀ n k, n < k → choose n k = 0
  | 0, k + 1, _ => by simp [choose]
  | n + 1, k + 1, h => by
    simp [choose, choose_above n k (by omega), choose_above n (k + 1) (by omega)]

theorem perm_fact : ∀ n r, r ≤ n → perm n r * fact (n - r) = fact n
  | n, 0, _ => by cases n <;> simp [perm]
  | 0, r + 1, h => by omega
  | n + 1, r + 1, h => by
    have ih := perm_fact n r (by omega)
    simp only [perm, fact, Nat.add_sub_add_right]
    rw [Nat.mul_assoc, ih]

theorem choose_fact : ∀ n r, r ≤ n → choose n r * fact r * fact (n - r) = fact n
  | n, 0, _ => by simp [choose_zero, fact]
  | 0, r + 1, h => by omega
  | n + 1, r + 1, h => by
    simp only [choose, fact, Nat.add_sub_add_right]
    by_cases hr : r = n
    · subst hr
      have ih := choose_fact r r (by omega)
      rw [choose_above r (r + 1) (by omega)]
      simp only [Nat.sub_self, fact, Nat.add_zero, Nat.mul_one] at ih ⊢
      grind
    · obtain ⟨d, hd⟩ : ∃ d, n - r = d + 1 := ⟨n - r - 1, by omega⟩
      have ih1 := choose_fact n r (by omega)
      have ih2 := choose_fact n (r + 1) (by omega)
      rw [show n - (r + 1) = d by omega] at ih2
      rw [hd] at ih1 ⊢
      simp only [fact] at ih1 ih2 ⊢
      have hn : n = r + d + 1 := by omega
      subst hn
      grind

/-- `perm` is `n!/(n-r)!`, `choose` is `n!/r!/(n-r)!`, and the
`combinations_with_replacement` count is `(n+r-1)!/r!/(n-1)!`
(rst:224-228, :268-270, :541-544), written without division. -/
def CountFormulas : Prop :=
  (∀ n r, r ≤ n → perm n r * fact (n - r) = fact n) ∧
  (∀ n r, r ≤ n → choose n r * fact r * fact (n - r) = fact n) ∧
  (∀ n r, 0 < n → choose (n + r - 1) r * fact r * fact (n - 1) = fact (n + r - 1))

theorem countFormulas_proven : CountFormulas := by
  refine ⟨perm_fact, choose_fact, ?_⟩
  intro n r hn
  have := choose_fact (n + r - 1) r (by omega)
  rwa [show n + r - 1 - r = n - 1 by omega] at this

end PyLean.Itertools
