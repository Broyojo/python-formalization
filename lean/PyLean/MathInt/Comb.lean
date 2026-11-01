import PyLean.MathInt.CombTables

/-!
`math.comb` and `math.perm` are exact for all arguments: every fast path of
`perm_comb_small` (the 64-bit odd-part tables and the two unsigned loops)
stays within `uint64_t`, and both divide-and-conquer recursions are exact.
-/

namespace PyLean.MathInt

open PyLean

theorem u64_of_lt {x : Nat} (h : x < 2 ^ 64) : u64 x = x := Nat.mod_eq_of_lt h

theorem u64_pred {n : Nat} (h1 : 1 ≤ n) (h2 : n ≤ 2 ^ 64) : u64 (n + 2 ^ 64 - 1) = n - 1 := by
  unfold u64
  rw [show n + 2 ^ 64 - 1 = (n - 1) + 2 ^ 64 by omega, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (by omega)

/-- The `C(n, k) = C(n, k-1) * (n-k+1) / k` loop, mathmodule.c@3.14.7:3603-3607,
when `C(n0, K) * K < 2^64` and `2K <= n0`. -/
theorem smallLoop_comb (n0 K : Nat) (hK : 2 * K ≤ n0) (hb : choose n0 K * K < 2 ^ 64) :
    ∀ rem t, t + 1 + rem = K →
      smallLoop true rem (choose n0 (t + 1)) (n0 - t) (t + 1) = choose n0 K := by
  intro rem
  induction rem with
  | zero => intro t h; simp [smallLoop]; rw [show t + 1 = K by omega]
  | succ r ih =>
    intro t h
    have hn0 : n0 < 2 ^ 64 := by
      have := choose_mul_self_mono n0 1 K (by omega) hK
      rw [choose_one_right] at this; omega
    have hstep : choose n0 (t + 1) * (n0 - t - 1) = choose n0 (t + 2) * (t + 2) := by
      rw [show n0 - t - 1 = n0 - (t + 1) by omega, ← choose_succ_mul]
    have hle : choose n0 (t + 2) * (t + 2) ≤ choose n0 K * K :=
      choose_mul_self_mono n0 (t + 2) K (by omega) hK
    simp only [smallLoop]
    rw [u64_pred (by omega) (by omega), u64_of_lt (by rw [hstep]; omega), ite_true, hstep,
      Nat.mul_div_cancel _ (by omega), show n0 - t - 1 = n0 - (t + 1) by omega,
      show t + 1 + 1 = (t + 1) + 1 from rfl]
    exact ih (t + 1) (by omega)

/-- The `P(n, k) = P(n, k-1) * (n-k+1)` loop, mathmodule.c@3.14.7:3630-3634, when
`P(n0, K) < 2^64` and `K <= n0`. -/
theorem smallLoop_perm (n0 K : Nat) (hK : K ≤ n0) (hb : descFact n0 K < 2 ^ 64) :
    ∀ rem t, t + 1 + rem = K →
      smallLoop false rem (descFact n0 (t + 1)) (n0 - t) (t + 1) = descFact n0 K := by
  intro rem
  induction rem with
  | zero => intro t h; simp [smallLoop]; rw [show t + 1 = K by omega]
  | succ r ih =>
    intro t h
    have hn0 : n0 < 2 ^ 64 := by
      have := descFact_mono_right n0 1 K (by omega) hK
      simp [descFact] at this; omega
    have hstep : descFact n0 (t + 1) * (n0 - t - 1) = descFact n0 (t + 2) := by
      rw [show n0 - t - 1 = n0 - (t + 1) by omega]; rfl
    have hle : descFact n0 (t + 2) ≤ descFact n0 K := descFact_mono_right n0 _ _ (by omega) hK
    simp only [smallLoop]
    rw [u64_pred (by omega) (by omega), u64_of_lt (by rw [hstep]; omega)]
    simp only [Bool.false_eq_true, ite_false]
    rw [hstep, show n0 - t - 1 = n0 - (t + 1) by omega]
    exact ih (t + 1) (by omega)

/-- Unpack the kernel-checked table `smallFastOk` at one `(n, k)`. -/
theorem smallFastOk_at (n k : Nat) (hn : n < 128) (hk : k < 128) :
    (!(1 ≤ k && 2 * k ≤ n) ||
      match permCombFast n k true with
      | some r => r * fact k == descFact n k
      | none => true) = true ∧
    (!(1 ≤ k && k ≤ n) ||
      match permCombFast n k false with
      | some r => r == descFact n k
      | none => true) = true := by
  have h := smallFastOk_eq
  unfold smallFastOk at h
  have h1 := (List.all_eq_true.mp h) n (List.mem_range.mpr hn)
  have h2 := (List.all_eq_true.mp h1) k (List.mem_range.mpr hk)
  exact Bool.and_eq_true_iff.mp h2

/-- Fast paths for `comb`: whatever they return is `C(n, k)`, and `k = 1`
always takes one. -/
theorem permCombFast_comb (n k : Nat) (hk : 1 ≤ k) (h2 : 2 * k ≤ n) (hn : n < 2 ^ 64) :
    (∀ r, permCombFast n k true = some r → r = choose n k) ∧
    (k = 1 → ∃ r, permCombFast n k true = some r) := by
  refine ⟨fun r hr => ?_, fun h1 => ?_⟩
  · by_cases hn128 : n < 128
    · have := (smallFastOk_at n k hn128 (by omega)).1
      have c : (1 ≤ k && 2 * k ≤ n) = true := by simp; omega
      rw [c, hr] at this
      simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at this
      rw [descFact_eq_choose_mul_fact] at this
      exact Nat.eq_of_mul_eq_mul_right (fact_pos k) this
    · have l1 := combLimits1_le k
      unfold permCombFast at hr
      simp only [ite_true, show ¬ (k < fastCombLimits1.length ∧ n ≤ fastCombLimits1.getD k 0) by
        omega, ite_false] at hr
      split at hr
      · rename_i hc
        cases hr
        have hk14 : k < 14 := by rw [← combLimits2_lengths]; exact hc.1
        have tb := (List.all_eq_true.mp combLimits2Ok_eq) k (List.mem_range.mpr hk14)
        simp only [show (1 ≤ k) = True by simp; omega, decide_true, Bool.not_true,
          Bool.false_or, decide_eq_true_eq] at tb
        rw [descFact_eq_choose_mul_fact] at tb
        have hL : choose (fastCombLimits2.getD k 0) k * k < 2 ^ 64 := by
          have : choose (fastCombLimits2.getD k 0) k * k * fact k < 2 ^ 64 * fact k := by
            rw [Nat.mul_right_comm]; exact tb
          exact Nat.lt_of_mul_lt_mul_right this
        have hm : choose n k * k ≤ choose (fastCombLimits2.getD k 0) k * k :=
          Nat.mul_le_mul_right _ (choose_mono_left k _ _ hc.2)
        have := smallLoop_comb n k h2 (by omega) (k - 1) 0 (by omega)
        simpa [choose_one_right] using this
      · cases hr
  · subst h1
    unfold permCombFast
    by_cases hc : 1 < fastCombLimits1.length ∧ n ≤ fastCombLimits1.getD 1 0
    · simp only [ite_true, hc, and_self]; exact ⟨_, rfl⟩
    · simp only [ite_true, hc, ite_false, combLimits2_lengths, combLimits2_one]
      exact ⟨_, if_pos (show 1 < 14 ∧ n ≤ 2 ^ 64 - 1 by omega)⟩

/-- Fast paths for `perm`: whatever they return is `P(n, k)`, and `k = 1`
always takes one. -/
theorem permCombFast_perm (n k : Nat) (hk : 1 ≤ k) (h2 : k ≤ n) (hn : n < 2 ^ 64) :
    (∀ r, permCombFast n k false = some r → r = descFact n k) ∧
    (k = 1 → ∃ r, permCombFast n k false = some r) := by
  refine ⟨fun r hr => ?_, fun h1 => ?_⟩
  · by_cases hn128 : n < 128
    · have := (smallFastOk_at n k hn128 (by omega)).2
      have c : (1 ≤ k && k ≤ n) = true := by simp; omega
      rw [c, hr] at this
      simpa using this
    · unfold permCombFast at hr
      simp only [Bool.false_eq_true, ite_false, show ¬ n ≤ 127 by omega] at hr
      split at hr
      · rename_i hc
        cases hr
        have hk21 : k < 21 := by rw [← permLimits_length]; exact hc.1
        have tb := (List.all_eq_true.mp permLimitsOk_eq) k (List.mem_range.mpr hk21)
        simp only [show (1 ≤ k) = True by simp; omega, decide_true, Bool.not_true,
          Bool.false_or, decide_eq_true_eq] at tb
        have hm : descFact n k ≤ descFact (fastPermLimits.getD k 0) k :=
          descFact_mono_left k _ _ hc.2
        have := smallLoop_perm n k h2 (by omega) (k - 1) 0 (by omega)
        simpa [descFact] using this
      · cases hr
  · subst h1
    unfold permCombFast
    simp only [Bool.false_eq_true, ite_false, permLimits_length, permLimits_one]
    rw [if_pos (show 1 < 21 ∧ n ≤ 2 ^ 64 - 1 by omega)]
    split <;> exact ⟨_, rfl⟩

/-- `perm_comb_small(n, k, 1)` is `C(n, k)` for `1 <= k`, `2k <= n < 2^64`
(the callers always pass `k <= n/2`). -/
theorem permCombSmall_comb :
    ∀ fuel n k, 1 ≤ k → 2 * k ≤ n → n < 2 ^ 64 → k ≤ fuel →
      permCombSmall fuel n k true = .ok (choose n k) := by
  intro fuel
  induction fuel with
  | zero => intro n k h1 _ _ h; omega
  | succ f ih =>
    intro n k h1 h2 hn hf
    obtain ⟨hfast, hone⟩ := permCombFast_comb n k h1 h2 hn
    unfold permCombSmall
    cases hc : permCombFast n k true with
    | some r => simp only [hfast r hc]
    | none =>
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · obtain ⟨r, hr⟩ := hone (by omega); rw [hr] at hc; cases hc
        · exact h
      have e1 := ih n (k / 2) (by omega) (by omega) hn (by omega)
      have e2 := ih (n - k / 2) (k - k / 2) (by omega) (by omega) (by omega) (by omega)
      have e3 := ih k (k / 2) (by omega) (by omega) (by omega) (by omega)
      simp only [e1, e2, e3, bind, Except.bind, ite_true, pure, Except.pure]
      rw [choose_mul_choose n k (k / 2) (by omega) (by omega),
        Nat.mul_div_cancel _ (choose_pos (by omega))]

/-- `perm_comb_small(n, k, 0)` is `P(n, k)` for `1 <= k <= n < 2^64`. -/
theorem permCombSmall_perm :
    ∀ fuel n k, 1 ≤ k → k ≤ n → n < 2 ^ 64 → k ≤ fuel →
      permCombSmall fuel n k false = .ok (descFact n k) := by
  intro fuel
  induction fuel with
  | zero => intro n k h1 _ _ h; omega
  | succ f ih =>
    intro n k h1 h2 hn hf
    obtain ⟨hfast, hone⟩ := permCombFast_perm n k h1 h2 hn
    unfold permCombSmall
    cases hc : permCombFast n k false with
    | some r => simp only [hfast r hc]
    | none =>
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · obtain ⟨r, hr⟩ := hone (by omega); rw [hr] at hc; cases hc
        · exact h
      have e1 := ih n (k / 2) (by omega) (by omega) hn (by omega)
      have e2 := ih (n - k / 2) (k - k / 2) (by omega) (by omega) (by omega) (by omega)
      simp only [e1, e2, bind, Except.bind, Bool.false_eq_true, ite_false, pure, Except.pure]
      rw [← descFact_add, show k / 2 + (k - k / 2) = k by omega]

/-- `perm_comb(n, k, iscomb)` for a Python int `n >= k` and `k < 2^64`. -/
theorem permComb_spec :
    ∀ fuel n k, k ≤ n → k < 2 ^ 64 → k < fuel →
      permComb fuel n k true = .ok (choose n k) ∧ permComb fuel n k false = .ok (descFact n k) := by
  intro fuel
  induction fuel with
  | zero => intro n k _ _ h; omega
  | succ f ih =>
    intro n k h1 h2 hf
    unfold permComb
    by_cases hk0 : k = 0
    · subst hk0; simp [descFact]
    by_cases hk1 : k = 1
    · subst hk1; simp [choose_one_right, descFact]
    simp only [hk0, hk1, ite_false]
    obtain ⟨c1, p1⟩ := ih n (k / 2) (by omega) (by omega) (by omega)
    obtain ⟨c2, p2⟩ := ih (n - k / 2) (k - k / 2) (by omega) (by omega) (by omega)
    have e3 := permCombSmall_comb (k + 1) k (k / 2) (by omega) (by omega) h2 (by omega)
    refine ⟨?_, ?_⟩
    · simp only [c1, c2, e3, bind, Except.bind, ite_true, pure, Except.pure]
      rw [choose_mul_choose n k (k / 2) (by omega) (by omega),
        Nat.mul_div_cancel _ (choose_pos (by omega))]
    · simp only [p1, p2, bind, Except.bind, Bool.false_eq_true, ite_false, pure, Except.pure]
      rw [← descFact_add, show k / 2 + (k - k / 2) = k by omega]

/-- `math.comb` docstring: "Evaluates to n! / (k! * (n - k)!) when k <= n".
The result is exact for every size of `n`; the only exception is the
`OverflowError` of mathmodule.c@3.14.7:3912-3917 when `min(k, n - k)` exceeds
`LLONG_MAX` (a result with more than `2^63` factors). -/
def CombFormula : Prop :=
  ∀ n k : Int, 0 ≤ k → k ≤ n →
    (min k (n - k) ≤ llongMax →
      comb n k = .ok (fact n.toNat / (fact k.toNat * fact (n - k).toNat))) ∧
    (min k (n - k) > llongMax → (comb n k).raises "OverflowError")

theorem combFormula_proven : CombFormula := by
  intro n k hk hkn
  obtain ⟨N, rfl⟩ : ∃ N : Nat, n = N := ⟨n.toNat, by omega⟩
  obtain ⟨K, rfl⟩ : ∃ K : Nat, k = K := ⟨k.toNat, by omega⟩
  have hKN : K ≤ N := by omega
  have t1 : (N : Int).toNat = N := by omega
  have t2 : (K : Int).toNat = K := by omega
  have t3 : ((N : Int) - K).toNat = N - K := by omega
  rw [t1, t2, t3, ← choose_eq_div N K hKN]
  have hL : (llongMax : Int) = 2 ^ 63 - 1 := by simp [llongMax]
  unfold comb
  simp only [show ¬ (N : Int) < 0 by omega, show ¬ (K : Int) < 0 by omega, ite_false, t1, t2]
  by_cases hN : (N : Int) ≤ llongMax
  · simp only [hN, ite_true, show ¬ ((K : Int) > llongMax ∨ (K : Int) > N) by omega, ite_false]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    have hsym : choose N (min K (N - K)) = choose N K := by
      rcases Nat.le_total K (N - K) with h | h
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right h, choose_symm N K hKN]
    rw [← hsym]
    split
    · exact permCombSmall_comb _ _ _ (by omega) (by omega) (by omega) (by omega)
    · exact (permComb_spec _ _ _ (by omega) (by omega) (by omega)).1
  · simp only [hN, ite_false, show ¬ ((N : Int) - K < 0) by omega]
    have hm : (if (N : Int) - K < K then (N : Int) - K else K) = ((min K (N - K) : Nat) : Int) := by
      split <;> omega
    rw [hm]
    have hsym : choose N (min K (N - K)) = choose N K := by
      rcases Nat.le_total K (N - K) with h | h
      · rw [Nat.min_eq_left h]
      · rw [Nat.min_eq_right h, choose_symm N K hKN]
    have hmin : min (K : Int) (N - K) = ((min K (N - K) : Nat) : Int) := by omega
    rw [hmin]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simp only [show ¬ (((min K (N - K) : Nat) : Int) > llongMax) by omega, ite_false]
      rw [← hsym]
      exact (permComb_spec _ _ _ (by omega) (by omega) (by omega)).1
    · simp only [h, ite_true]
      exact ⟨_, rfl, rfl⟩

/-- `math.perm` docstring: "Evaluates to n! / (n - k)! when k <= n". Exact
for every `n`; `k > LLONG_MAX` raises `OverflowError` (mathmodule.c@3.14.7:3784-3790). -/
def PermFormula : Prop :=
  ∀ n k : Int, 0 ≤ k → k ≤ n →
    (k ≤ llongMax → perm n (some k) = .ok (fact n.toNat / fact (n - k).toNat)) ∧
    (k > llongMax → (perm n (some k)).raises "OverflowError")

theorem permFormula_proven : PermFormula := by
  intro n k hk hkn
  obtain ⟨N, rfl⟩ : ∃ N : Nat, n = N := ⟨n.toNat, by omega⟩
  obtain ⟨K, rfl⟩ : ∃ K : Nat, k = K := ⟨k.toNat, by omega⟩
  have hKN : K ≤ N := by omega
  have t1 : (N : Int).toNat = N := by omega
  have t2 : (K : Int).toNat = K := by omega
  have t3 : ((N : Int) - K).toNat = N - K := by omega
  rw [t1, t3, ← descFact_eq_div N K hKN]
  have hL : (llongMax : Int) = 2 ^ 63 - 1 := by simp [llongMax]
  unfold perm
  simp only [show ¬ (N : Int) < 0 by omega, show ¬ (K : Int) < 0 by omega,
    show ¬ (N : Int) < K by omega, ite_false]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · simp only [show ¬ ((K : Int) > llongMax) by omega, ite_false, t1, t2]
    split
    · exact permCombSmall_perm _ _ _ (by omega) hKN (by omega) (by omega)
    · exact (permComb_spec _ _ _ hKN (by omega) (by omega)).2
  · simp only [h, ite_true]
    exact ⟨_, rfl, rfl⟩

end PyLean.MathInt
