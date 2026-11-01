import PyLean.Decimal.Arith

/-! Arithmetic facts about `numDigits` and the rounding helper. -/

namespace PyLean.Decimal

open PyLean

theorem numDigits_pos (n : Nat) : 0 < numDigits n := Nat.length_toDigits_pos

theorem numDigits_le_iff {n k : Nat} (hk : 0 < k) : numDigits n ≤ k ↔ n < 10 ^ k :=
  Nat.length_toDigits_le_iff (by decide) hk

theorem lt_pow_numDigits (n : Nat) : n < 10 ^ numDigits n :=
  (numDigits_le_iff (numDigits_pos n)).mp (Nat.le_refl _)

theorem pow_numDigits_le {n : Nat} (hn : n ≠ 0) : 10 ^ (numDigits n - 1) ≤ n := by
  rcases Nat.lt_or_ge n (10 ^ (numDigits n - 1)) with h | h
  · by_cases h1 : numDigits n - 1 = 0
    · rw [h1] at h; omega
    · have := (numDigits_le_iff (by omega)).mpr h
      omega
  · exact h

theorem numDigits_zero : numDigits 0 = 1 := rfl

/-- `10^k = 2 * (5 * 10^(k-1))` for `k ≥ 1`. -/
theorem pow_ten_eq_two_half {k : Nat} (hk : 1 ≤ k) : 10 ^ k = 2 * (5 * 10 ^ (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.pow_succ]
  omega

end PyLean.Decimal
