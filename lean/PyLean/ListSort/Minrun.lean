import PyLean.ListSort.Model

/-!
# The minrun generator

`merge_init` (`listobject.c:2282-2288`) picks `mr_e`, the smallest `e` with
`N >> e < MAX_MINRUN`, and `minrun_next` (:2767-2775) adds `N` to a counter
modulo `2^e`, returning what it carries. So call number `k` (from 0) returns
`⌊(k+1)N / 2^e⌋ - ⌊kN / 2^e⌋`, the Bresenham line of slope `N / 2^e`
(`listsort.txt:356-392`), which is the source of every claim at
`listsort.txt:311-316`.
-/

namespace PyLean.ListSort

/-- The generator after `k` calls of `minrun_next`. -/
def mrAfter (mr : MrState) : Nat → MrState
  | 0 => mr
  | k + 1 => (minrunNext (mrAfter mr k)).2

/-- `ms->mr_e` for a list of length `N`. -/
def mrE (N : Nat) : Nat := (mergeInitMr N).e

/-- What call number `k` (from 0) of `minrun_next` returns. -/
def minrunAt (N k : Nat) : Nat := (minrunNext (mrAfter (mergeInitMr N) k)).1

/-- The total of `m` consecutive values from call `k`: the length of a run of the
merge tree, when every natural run is short. -/
def minrunSum (N k m : Nat) : Nat := ((List.range m).map fun i => minrunAt N (k + i)).sum

theorem mrELoop_spec (n : Nat) : ∀ (fuel e : Nat), n / 2 ^ e < 64 * 2 ^ fuel →
    e ≤ mrELoop n fuel e ∧ n / 2 ^ mrELoop n fuel e < 64 ∧
      (e < mrELoop n fuel e → 64 ≤ n / 2 ^ (mrELoop n fuel e - 1))
  | 0, e, h => by simpa [mrELoop] using h
  | fuel + 1, e, h => by
    simp only [mrELoop, MAX_MINRUN, Nat.shiftRight_eq_div_pow]
    by_cases hge : n / 2 ^ e ≥ 64
    · simp only [hge, ↓reduceIte]
      have hdiv : n / 2 ^ e / 2 = n / 2 ^ (e + 1) := by rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
      have hlt : n / 2 ^ (e + 1) < 64 * 2 ^ fuel := by
        rw [← hdiv]; rw [Nat.pow_succ] at h; omega
      obtain ⟨h1, h2, h3⟩ := mrELoop_spec n fuel (e + 1) hlt
      refine ⟨by omega, h2, fun hie => ?_⟩
      by_cases hie' : e + 1 < mrELoop n fuel (e + 1)
      · exact h3 hie'
      · rw [show mrELoop n fuel (e + 1) - 1 = e by omega]; exact hge
    · simp only [hge, ↓reduceIte]
      exact ⟨Nat.le_refl _, by omega, fun h => absurd h (Nat.lt_irrefl _)⟩

/-- `mr_e`: 0 for `N < 64`, and otherwise `32 * 2^e <= N < 64 * 2^e`. -/
theorem mrE_bounds (N : Nat) :
    (N < 64 → mrE N = 0) ∧ (64 ≤ N → 32 * 2 ^ mrE N ≤ N ∧ N < 64 * 2 ^ mrE N) := by
  have hN : N / 2 ^ 0 < 64 * 2 ^ N := by
    have := Nat.lt_two_pow_self (n := N)
    simp only [Nat.pow_zero, Nat.div_one]
    omega
  obtain ⟨-, h2, h3⟩ := mrELoop_spec N N 0 hN
  have he : mrE N = mrELoop N N 0 := rfl
  rw [← he] at h2 h3
  constructor
  · intro hlt
    rcases Nat.eq_zero_or_pos (mrE N) with h | h
    · exact h
    · have := h3 h
      have := Nat.div_le_self N (2 ^ (mrE N - 1))
      omega
  · intro hge
    have hpos : 0 < mrE N := by
      rcases Nat.eq_zero_or_pos (mrE N) with h | h
      · rw [h] at h2; simp at h2; omega
      · exact h
    have h64 := h3 hpos
    have hP : 2 ^ mrE N = 2 * 2 ^ (mrE N - 1) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hc : 0 < 2 ^ (mrE N - 1) := Nat.two_pow_pos _
    have hle : 64 * 2 ^ (mrE N - 1) ≤ N := (Nat.le_div_iff_mul_le hc).1 h64
    have hlt : N < 64 * 2 ^ mrE N := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).1 h2
    exact ⟨by rw [hP]; omega, hlt⟩

theorem mergeInitMr_mask (N : Nat) : (mergeInitMr N).mask = 2 ^ mrE N - 1 := by
  simp [mergeInitMr, mrE, Nat.shiftLeft_eq]

theorem mrAfter_fixed (mr : MrState) : ∀ k, (mrAfter mr k).listlen = mr.listlen ∧
    (mrAfter mr k).e = mr.e ∧ (mrAfter mr k).mask = mr.mask
  | 0 => ⟨rfl, rfl, rfl⟩
  | k + 1 => by simpa [mrAfter, minrunNext] using mrAfter_fixed mr k

/-- `mr_current` after `k` calls is `kN mod 2^e`. -/
theorem mrAfter_current (N : Nat) : ∀ k, (mrAfter (mergeInitMr N) k).current = k * N % 2 ^ mrE N
  | 0 => by simp [mrAfter, mergeInitMr]
  | k + 1 => by
    obtain ⟨h1, _, h3⟩ := mrAfter_fixed (mergeInitMr N) k
    have hl : (mergeInitMr N).listlen = N := rfl
    simp only [mrAfter, minrunNext]
    rw [h1, h3, hl, mergeInitMr_mask, mrAfter_current N k, Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_add_mod, Nat.add_mul, Nat.one_mul]

theorem div_step (a N P : Nat) (hP : 0 < P) : (a + N) / P = a / P + (a % P + N) / P := by
  have h := Nat.div_add_mod a P
  have e : a + N = (a % P + N) + P * (a / P) := by omega
  calc (a + N) / P = ((a % P + N) + P * (a / P)) / P := by rw [← e]
    _ = (a % P + N) / P + a / P := Nat.add_mul_div_left _ _ hP
    _ = a / P + (a % P + N) / P := Nat.add_comm _ _

theorem minrunAt_eq (N k : Nat) : minrunAt N k = (k * N % 2 ^ mrE N + N) / 2 ^ mrE N := by
  obtain ⟨h1, h2, _⟩ := mrAfter_fixed (mergeInitMr N) k
  simp only [minrunAt, minrunNext]
  rw [h1, h2, mrAfter_current, Nat.shiftRight_eq_div_pow]
  rfl

/-- The closed form: the difference of consecutive multiples of `N / 2^e`, floored. -/
theorem minrunAt_formula (N k : Nat) :
    minrunAt N k = (k + 1) * N / 2 ^ mrE N - k * N / 2 ^ mrE N := by
  have h := div_step (k * N) N (2 ^ mrE N) (Nat.two_pow_pos _)
  rw [Nat.add_mul, Nat.one_mul, h, minrunAt_eq, Nat.add_sub_cancel_left]

theorem minrunSum_succ (N k m : Nat) : minrunSum N k (m + 1) = minrunSum N k m + minrunAt N (k + m) := by
  simp [minrunSum, List.range_succ, List.map_append, List.sum_append]

/-- `m` consecutive values add up to a difference of floors. -/
theorem minrunSum_eq (N k : Nat) : ∀ m, minrunSum N k m = (k + m) * N / 2 ^ mrE N - k * N / 2 ^ mrE N
  | 0 => by simp [minrunSum]
  | m + 1 => by
    rw [minrunSum_succ, minrunSum_eq N k m, minrunAt_formula]
    have h1 : k * N / 2 ^ mrE N ≤ (k + m) * N / 2 ^ mrE N :=
      Nat.div_le_div_right (Nat.mul_le_mul_right N (by omega))
    have h2 : (k + m) * N / 2 ^ mrE N ≤ (k + m + 1) * N / 2 ^ mrE N :=
      Nat.div_le_div_right (Nat.mul_le_mul_right N (by omega))
    rw [show k + (m + 1) = k + m + 1 from rfl]
    generalize k * N / 2 ^ mrE N = X at *
    generalize (k + m) * N / 2 ^ mrE N = Y at *
    generalize (k + m + 1) * N / 2 ^ mrE N = Z at *
    omega

theorem add_div_bounds (a b P : Nat) (hP : 0 < P) :
    b / P ≤ (a + b) / P - a / P ∧ (a + b) / P - a / P ≤ b / P + 1 := by
  have h1 := div_step a b P hP
  have h2 := div_step b (a % P) P hP
  have h3 : (b % P + a % P) / P < 2 := Nat.div_lt_of_lt_mul (by
    have := Nat.mod_lt a hP
    have := Nat.mod_lt b hP
    omega)
  rw [Nat.add_comm b (a % P)] at h2
  generalize (a + b) / P = X at *
  generalize a / P = Y at *
  generalize (a % P + b) / P = Z at *
  generalize b / P = W at *
  generalize (b % P + a % P) / P = V at *
  omega

/-- "The lengths of run pairs merged never differ by more than one", at every level:
any `m` consecutive values add up to `⌊mN / 2^e⌋` or one more. -/
theorem minrunSum_bounds (N k m : Nat) :
    m * N / 2 ^ mrE N ≤ minrunSum N k m ∧ minrunSum N k m ≤ m * N / 2 ^ mrE N + 1 := by
  rw [minrunSum_eq, Nat.add_mul]
  exact add_div_bounds _ _ _ (Nat.two_pow_pos _)

theorem minrunAt_bounds (N k : Nat) :
    N / 2 ^ mrE N ≤ minrunAt N k ∧ minrunAt N k ≤ N / 2 ^ mrE N + 1 := by
  rw [minrunAt_formula, Nat.add_mul, Nat.one_mul]
  exact add_div_bounds _ _ _ (Nat.two_pow_pos _)

/-- The first `2^e` values add up to exactly `N`: when every natural run is short the
sort makes a power of two of runs and covers the list. -/
theorem minrunSum_full (N : Nat) : minrunSum N 0 (2 ^ mrE N) = N := by
  rw [minrunSum_eq]
  simp [Nat.mul_div_cancel_left _ (Nat.two_pow_pos (mrE N))]

theorem minrunAt_of_dvd (N d : Nat) (h : N = 2 ^ mrE N * d) (k : Nat) : minrunAt N k = d := by
  rw [minrunAt_formula]
  have hP : 0 < 2 ^ mrE N := Nat.two_pow_pos _
  generalize 2 ^ mrE N = P at h hP ⊢
  have e1 : (k + 1) * N = P * ((k + 1) * d) := by rw [h, Nat.mul_left_comm]
  have e2 : k * N = P * (k * d) := by rw [h, Nat.mul_left_comm]
  rw [e1, e2, Nat.mul_div_cancel_left _ hP, Nat.mul_div_cancel_left _ hP, Nat.add_mul, Nat.one_mul]
  omega

/-- For `N = 2^j >= 64` every minrun is 32 (`listsort.txt:277-282`). -/
theorem minrunAt_pow (j : Nat) (hj : 6 ≤ j) (k : Nat) : minrunAt (2 ^ j) k = MAX_MINRUN / 2 := by
  have h64 : 64 ≤ 2 ^ j := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hj
    simpa using this
  obtain ⟨h1, h2⟩ := (mrE_bounds (2 ^ j)).2 h64
  generalize he : mrE (2 ^ j) = e at h1 h2
  have a1 : 2 ^ (e + 5) ≤ 2 ^ j := by rw [Nat.pow_add]; simpa [Nat.mul_comm] using h1
  have a2 : 2 ^ j < 2 ^ (e + 6) := by rw [Nat.pow_add]; simpa [Nat.mul_comm] using h2
  have b1 := (Nat.pow_le_pow_iff_right (by decide)).1 a1
  have b2 := (Nat.pow_lt_pow_iff_right (by decide)).1 a2
  have hj' : j = e + 5 := by omega
  apply minrunAt_of_dvd
  rw [he, hj', Nat.pow_add]
  rfl

/-- `ms->mr_current += ms->listlen` stays in `Py_ssize_t` for every `N <= 2**62`,
so `assert(ms->mr_current >= 0)` (:2771) holds. -/
theorem current_add_lt (N k : Nat) (h : N ≤ 2 ^ 62) :
    (mrAfter (mergeInitMr N) k).current + N < 2 ^ 63 := by
  rw [mrAfter_current]
  have hm := Nat.mod_lt (k * N) (Nat.two_pow_pos (mrE N))
  obtain ⟨h1, h2⟩ := mrE_bounds N
  by_cases hN : N < 64
  · rw [h1 hN] at hm ⊢
    simp at hm ⊢
    omega
  · have := (h2 (by omega)).1
    generalize 2 ^ mrE N = P at *
    generalize k * N % P = r at *
    omega

end PyLean.ListSort
