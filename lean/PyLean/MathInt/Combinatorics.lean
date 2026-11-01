/-!
Factorials, binomial coefficients and falling factorials on `Nat`, with the
identities the `comb` / `perm` / `factorial` proofs need. (Core Lean has no
`Nat.factorial` / `Nat.choose`.)
-/

namespace PyLean.MathInt

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Falling factorial `n * (n-1) * ... * (n-k+1)`. -/
def descFact (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => descFact n k * (n - k)

theorem fact_pos : ∀ n, 0 < fact n
  | 0 => by decide
  | n + 1 => Nat.mul_pos (Nat.succ_pos n) (fact_pos n)

theorem fact_succ (n : Nat) : fact (n + 1) = (n + 1) * fact n := rfl

@[simp] theorem choose_zero_right (n : Nat) : choose n 0 = 1 := by cases n <;> rfl

theorem choose_succ_succ (n k : Nat) : choose (n + 1) (k + 1) = choose n k + choose n (k + 1) := rfl

theorem choose_eq_zero_of_lt : ∀ {n k : Nat}, n < k → choose n k = 0
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [choose_succ_succ, choose_eq_zero_of_lt (by omega), choose_eq_zero_of_lt (by omega)]

theorem choose_one_right : ∀ n, choose n 1 = n
  | 0 => rfl
  | n + 1 => by rw [choose_succ_succ, choose_one_right n, choose_zero_right]; omega

/-- `choose n (k+1) * (k+1) = choose n k * (n - k)`. -/
theorem choose_succ_mul : ∀ n k : Nat, choose n (k + 1) * (k + 1) = choose n k * (n - k)
  | 0, k => by simp [choose_eq_zero_of_lt (Nat.succ_pos k)]
  | n + 1, 0 => by simp [choose_one_right]
  | n + 1, k + 1 => by
    have ih1 := choose_succ_mul n k
    have ih2 := choose_succ_mul n (k + 1)
    rw [choose_succ_succ, choose_succ_succ n k, Nat.add_mul, Nat.add_mul]
    by_cases h : k + 1 ≤ n
    · have e1 : n - k = (n - (k + 1)) + 1 := by omega
      have e2 : n + 1 - (k + 1) = (n - (k + 1)) + 1 := by omega
      rw [e1] at ih1; rw [e2, ih2]
      rw [show choose n (k + 1) * (k + 1 + 1) = choose n (k + 1) * (k + 1) + choose n (k + 1) by
        rw [Nat.mul_add, Nat.mul_one]]
      rw [ih1]
      simp only [Nat.mul_add, Nat.mul_one]
      omega
    · rw [choose_eq_zero_of_lt (show n < k + 1 by omega),
        choose_eq_zero_of_lt (show n < k + 1 + 1 by omega)]
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add]
      have : n - k = 0 ∨ n = k := by omega
      rcases this with h' | h'
      · rw [show n + 1 - (k + 1) = 0 by omega]; simp
      · subst h'; simp

theorem descFact_eq_choose_mul_fact (n : Nat) : ∀ k, descFact n k = choose n k * fact k
  | 0 => by simp [descFact, fact]
  | k + 1 => by
    rw [descFact, descFact_eq_choose_mul_fact n k, fact_succ, ← Nat.mul_assoc,
      choose_succ_mul n k]
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem descFact_mul_fact (n : Nat) : ∀ k, k ≤ n → descFact n k * fact (n - k) = fact n
  | 0, _ => by simp [descFact]
  | k + 1, h => by
    have ih := descFact_mul_fact n k (by omega)
    rw [descFact, Nat.mul_assoc]
    have : (n - k) * fact (n - (k + 1)) = fact (n - k) := by
      rw [show n - k = (n - (k + 1)) + 1 by omega, fact_succ]
    rw [this, ih]

theorem choose_mul_fact_mul_fact (n k : Nat) (h : k ≤ n) :
    choose n k * (fact k * fact (n - k)) = fact n := by
  rw [← Nat.mul_assoc, ← descFact_eq_choose_mul_fact, descFact_mul_fact n k h]

theorem choose_pos {n k : Nat} (h : k ≤ n) : 0 < choose n k := by
  have h1 := choose_mul_fact_mul_fact n k h
  have h2 := fact_pos n
  apply Nat.pos_of_ne_zero
  intro h0
  rw [h0, Nat.zero_mul] at h1
  omega

/-- The documented formula `n! / (k! * (n - k)!)`. -/
theorem choose_eq_div (n k : Nat) (h : k ≤ n) : choose n k = fact n / (fact k * fact (n - k)) := by
  rw [← choose_mul_fact_mul_fact n k h, Nat.mul_div_cancel _ (Nat.mul_pos (fact_pos _) (fact_pos _))]

theorem descFact_eq_div (n k : Nat) (h : k ≤ n) : descFact n k = fact n / fact (n - k) := by
  rw [← descFact_mul_fact n k h, Nat.mul_div_cancel _ (fact_pos _)]

theorem choose_symm (n k : Nat) (h : k ≤ n) : choose n (n - k) = choose n k := by
  have h1 := choose_mul_fact_mul_fact n k h
  have h2 := choose_mul_fact_mul_fact n (n - k) (by omega)
  rw [show n - (n - k) = k by omega, Nat.mul_comm (fact (n - k))] at h2
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (fact_pos _) (fact_pos _)) (h2.trans h1.symm)

theorem descFact_add (n j : Nat) : ∀ m, descFact n (j + m) = descFact n j * descFact (n - j) m
  | 0 => by simp [descFact]
  | m + 1 => by
    rw [← Nat.add_assoc, descFact, descFact_add n j m, descFact, Nat.mul_assoc,
      show n - (j + m) = n - j - m by omega]

/-- `C(n, j) * C(n-j, k-j) == C(n, k) * C(k, j)`, the identity behind the
recursion of `perm_comb_small` / `perm_comb` (mathmodule.c@3.14.7:3639-3660). -/
theorem choose_mul_choose (n k j : Nat) (hj : j ≤ k) (hk : k ≤ n) :
    choose n j * choose (n - j) (k - j) = choose n k * choose k j := by
  have hpos : 0 < fact j * fact (k - j) := Nat.mul_pos (fact_pos _) (fact_pos _)
  apply Nat.eq_of_mul_eq_mul_right hpos
  have l : choose n j * choose (n - j) (k - j) * (fact j * fact (k - j)) = descFact n k := by
    rw [show choose n j * choose (n - j) (k - j) * (fact j * fact (k - j)) =
        (choose n j * fact j) * (choose (n - j) (k - j) * fact (k - j)) by
      simp only [Nat.mul_assoc, Nat.mul_left_comm]]
    rw [← descFact_eq_choose_mul_fact, ← descFact_eq_choose_mul_fact, ← descFact_add,
      show j + (k - j) = k by omega]
  have r : choose n k * choose k j * (fact j * fact (k - j)) = descFact n k := by
    rw [Nat.mul_assoc, choose_mul_fact_mul_fact k j hj, ← descFact_eq_choose_mul_fact]
  rw [l, r]

/-- `C(n, j) * j` is nondecreasing in `j` while `j <= n / 2`. -/
theorem choose_mul_self_mono (n : Nat) :
    ∀ j k, j ≤ k → 2 * k ≤ n → choose n j * j ≤ choose n k * k := by
  intro j k hjk hk
  induction k with
  | zero => have : j = 0 := by omega
            subst this; simp
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have := ih (by omega) (by omega)
      have step : choose n k * k ≤ choose n (k + 1) * (k + 1) := by
        rw [choose_succ_mul]; exact Nat.mul_le_mul_left _ (by omega)
      omega
    · have : j = k + 1 := by omega
      subst this; exact Nat.le_refl _

theorem choose_mono_left (k : Nat) : ∀ n m, n ≤ m → choose n k ≤ choose m k := by
  intro n m h
  induction m with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with h' | h'
    · have := ih (by omega)
      cases k with
      | zero => simp
      | succ k => rw [choose_succ_succ]; omega
    · have : n = m + 1 := by omega
      subst this; exact Nat.le_refl _

theorem descFact_mono_left : ∀ k n m, n ≤ m → descFact n k ≤ descFact m k
  | 0, _, _, _ => Nat.le_refl _
  | k + 1, n, m, h => Nat.mul_le_mul (descFact_mono_left k n m h) (by omega)

theorem descFact_mono_right (n : Nat) : ∀ j k, j ≤ k → k ≤ n → descFact n j ≤ descFact n k := by
  intro j k hjk hk
  induction k with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have := ih (by omega) (by omega)
      have : descFact n k ≤ descFact n (k + 1) := by
        rw [descFact]; exact Nat.le_mul_of_pos_right _ (by omega)
      omega
    · have : j = k + 1 := by omega
      subst this; exact Nat.le_refl _

end PyLean.MathInt
