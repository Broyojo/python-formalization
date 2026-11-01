import PyLean.ListSort.Model

/-!
# `merge_compute_minrun`

`merge_compute_minrun(n)` (`listobject.c@3.14.7:2700-2711`) keeps the top 6 bits of
`n` and adds 1 if any bit shifted off is set: it is `⌈n / 2^e⌉` for the `e` with
`32 <= n / 2^e < 64` (`listsort.txt:313-318`).
-/

namespace PyLean.ListSort

theorem or_bit (r b : Nat) (hr : r ≤ 1) (hb : b ≤ 1) : r ||| b = max r b := by
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> rfl

theorem minrunLoop_spec (n : Nat) :
    ∀ (fuel i : Nat), n / 2 ^ i < 64 * 2 ^ fuel →
      ∃ e, i ≤ e ∧ n / 2 ^ e < 64 ∧ (i < e → 64 ≤ n / 2 ^ (e - 1)) ∧
        minrunLoop fuel (n / 2 ^ i) (if n % 2 ^ i = 0 then 0 else 1) =
          n / 2 ^ e + (if n % 2 ^ e = 0 then 0 else 1)
  | 0, i, h => ⟨i, Nat.le_refl _, by simpa using h, by omega, rfl⟩
  | fuel + 1, i, h => by
    simp only [minrunLoop, MAX_MINRUN]
    by_cases hge : n / 2 ^ i ≥ 64
    · simp only [hge, ↓reduceIte]
      have hdiv : n / 2 ^ i / 2 = n / 2 ^ (i + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hmod : ((if n % 2 ^ i = 0 then 0 else 1) ||| n / 2 ^ i % 2) =
          (if n % 2 ^ (i + 1) = 0 then 0 else 1) := by
        rw [Nat.mod_pow_succ]
        have hr : (if n % 2 ^ i = 0 then 0 else 1) ≤ 1 := by split <;> omega
        have hp := Nat.two_pow_pos i
        rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ i) with h2 | h2 <;> rw [h2, or_bit _ _ hr (by omega)]
        · rw [Nat.mul_zero, Nat.add_zero]; split <;> omega
        · rw [Nat.mul_one]; split <;> split <;> omega
      rw [hdiv, hmod]
      obtain ⟨e, he1, he2, he3, he4⟩ := minrunLoop_spec n fuel (i + 1)
        (by rw [← hdiv]; rw [Nat.pow_succ] at h; omega)
      refine ⟨e, by omega, he2, fun hie => ?_, he4⟩
      by_cases hie' : i + 1 < e
      · exact he3 hie'
      · rw [show e - 1 = i by omega]; omega
    · simp only [hge, ↓reduceIte]
      exact ⟨i, Nat.le_refl _, by omega, by omega, rfl⟩

/-- For `n < 64`, `minrun = n`; otherwise `minrun = ⌈n / 2^e⌉` with
`32 * 2^e <= n < 64 * 2^e`, so `32 <= minrun <= 64` and `n / minrun <= 2^e`
(equal exactly when `2^e` divides `n`). -/
theorem computeMinrun_spec (n : Nat) :
    (n < 64 → computeMinrun n = n) ∧
    (64 ≤ n → ∃ e, 32 * 2 ^ e ≤ n ∧ n < 64 * 2 ^ e ∧
      (computeMinrun n - 1) * 2 ^ e < n ∧ n ≤ computeMinrun n * 2 ^ e ∧
      32 ≤ computeMinrun n ∧ computeMinrun n ≤ 64) := by
  have h0 := minrunLoop_spec n n 0 (by
    simp only [Nat.pow_zero, Nat.div_one]
    have := Nat.lt_two_pow_self (n := n); omega)
  obtain ⟨e, _, he2, he3, he4⟩ := h0
  simp only [Nat.pow_zero, Nat.div_one, Nat.mod_one, ↓reduceIte] at he4
  unfold computeMinrun
  rw [he4]
  have hp : 0 < 2 ^ e := Nat.two_pow_pos e
  have hdm := Nat.div_add_mod n (2 ^ e)
  have hml := Nat.mod_lt n hp
  constructor
  · intro hn
    have he0 : e = 0 := by
      rcases Nat.eq_zero_or_pos e with h | h
      · exact h
      · have := he3 h; have := Nat.div_le_self n (2 ^ (e - 1)); omega
    subst he0; simp [Nat.mod_one]
  · intro hn
    have hepos : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · subst h; simp at he2; omega
      · exact h
    have h64 := he3 hepos
    have hq : n / 2 ^ (e - 1) / 2 = n / 2 ^ e := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]; congr 2; omega
    have h32 : 32 ≤ n / 2 ^ e := by omega
    have hlt64 : n / 2 ^ e < 64 := he2
    refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> generalize n / 2 ^ e = q at * <;>
      generalize n % 2 ^ e = rem at * <;> generalize 2 ^ e = P at * <;> rw [Nat.mul_comm] at hdm
    · have := Nat.mul_le_mul_right P h32; omega
    · have := Nat.mul_le_mul_right P (show q + 1 ≤ 64 by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    · split
      · have : (q + 0 - 1) * P = q * P - P := by rw [Nat.add_zero, Nat.sub_mul, Nat.one_mul]
        rw [this]
        have := Nat.mul_le_mul_right P (show 1 ≤ q by omega)
        rw [Nat.one_mul] at this; omega
      · rw [Nat.add_sub_cancel]; omega
    · split
      · rw [Nat.add_zero]; omega
      · rw [Nat.add_mul, Nat.one_mul]; omega
    · split <;> omega
    · split <;> omega

end PyLean.ListSort
