import PyLean.MathInt.Model
import PyLean.MathInt.Combinatorics

/-!
`math.factorial` is exact for `0 <= n <= LONG_MAX`: the `SmallFactorials`
table, the binary-split odd part with its `unsigned long` tight loop, and the
two-valuation `n - popcount(n)`.
-/

namespace PyLean.MathInt

open PyLean

/-! ### Bit helpers -/

theorem lt_two_pow_bitLength' (b : Nat) : b < 2 ^ bitLength b := by
  unfold bitLength; split
  · omega
  · exact Nat.lt_log2_self

theorem bitLength_le_of_lt' {x k : Nat} (h : x < 2 ^ k) : bitLength x ≤ k := by
  unfold bitLength; split
  · omega
  · have := (Nat.log2_lt (n := x) (k := k) (by omega)).mpr h; omega

theorem or_one_eq (x : Nat) : x ||| 1 = 2 * (x / 2) + 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases i with
  | zero => simp [Nat.testBit_zero]
  | succ j =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [show (2 * (x / 2) + 1) / 2 = x / 2 by omega]
    simp

/-- Popcount, by halving. -/
def pc (n : Nat) : Nat := if n = 0 then 0 else pc (n / 2) + n % 2
decreasing_by omega

theorem pc_eq (n : Nat) : pc n = pc (n / 2) + n % 2 := by
  rw [pc]; split
  · subst_vars; rw [pc]; simp
  · rfl

theorem pc_le : ∀ k n, n < 2 ^ k → pc n ≤ k := by
  intro k
  induction k with
  | zero => intro n h; have : n = 0 := by simp at h; omega
            subst this; rw [pc]; simp
  | succ k ih =>
    intro n h
    rw [pc_eq]
    have := ih (n / 2) (by rw [Nat.pow_succ] at h; omega)
    omega

theorem pc_le_self : ∀ n, pc n ≤ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [pc_eq]
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [pc]
    · have := ih (n / 2) (by omega); omega

theorem pc_and_pred : ∀ n, 0 < n → pc (n &&& (n - 1)) + 1 = pc n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    have hd : (n &&& (n - 1)) / 2 = n / 2 &&& (n - 1) / 2 := Nat.and_div_two
    have hm : (n &&& (n - 1)) % 2 = 0 := by
      have : ¬ ((n &&& (n - 1)) % 2 = 1) := fun h => by
        have := Nat.and_mod_two_eq_one.mp h; omega
      omega
    rw [pc_eq (n &&& (n - 1)), hd, hm, pc_eq n]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hm2 : 0 < n / 2 := by omega
      rw [show (n - 1) / 2 = n / 2 - 1 by omega, h]
      have := ih (n / 2) (by omega) hm2
      omega
    · rw [show (n - 1) / 2 = n / 2 by omega, Nat.and_self, h]

/-- `count_set_bits`, mathmodule.c:1484-1492, is the popcount. -/
theorem countSetBits_eq : ∀ fuel n, pc n ≤ fuel → countSetBits fuel n = pc n := by
  intro fuel
  induction fuel with
  | zero => intro n h; simp [countSetBits]; omega
  | succ f ih =>
    intro n h
    unfold countSetBits
    by_cases h0 : n = 0
    · subst h0; simp [pc]
    · have := pc_and_pred n (by omega)
      simp only [h0, ne_eq, not_false_eq_true, ite_true]
      rw [ih _ (by omega)]; omega

/-! ### Products of odd numbers -/

/-- `s * (s+2) * ... * (s + 2(m-1))`. -/
def stepProd (s : Nat) : Nat → Nat
  | 0 => 1
  | m + 1 => stepProd s m * (s + 2 * m)

theorem stepProd_add (s a : Nat) : ∀ b, stepProd s (a + b) = stepProd s a * stepProd (s + 2 * a) b
  | 0 => by simp [stepProd]
  | b + 1 => by
    rw [← Nat.add_assoc, stepProd, stepProd_add s a b, stepProd, Nat.mul_assoc,
      show s + 2 * (a + b) = s + 2 * a + 2 * b by omega]

theorem stepProd_lt (s m B : Nat) (hB : ∀ i, i < m → s + 2 * i < 2 ^ B) :
    stepProd s m < 2 ^ (m * B) ∨ m = 0 := by
  induction m with
  | zero => right; rfl
  | succ m ih =>
    left
    have h1 : stepProd s m ≤ 2 ^ (m * B) := by
      rcases ih (fun i hi => hB i (by omega)) with h | h
      · omega
      · subst h; simp [stepProd, Nat.one_le_two_pow]
    have h2 := hB m (by omega)
    rw [stepProd, show (m + 1) * B = m * B + B by rw [Nat.add_mul, Nat.one_mul], Nat.pow_add]
    calc stepProd s m * (s + 2 * m) ≤ 2 ^ (m * B) * (s + 2 * m) := Nat.mul_le_mul_right _ h1
      _ < 2 ^ (m * B) * 2 ^ B := Nat.mul_lt_mul_of_pos_left h2 (Nat.two_pow_pos _)

/-- The tight loop of `factorial_partial_product`, mathmodule.c:1917-1918,
with all products below `2^64`. -/
theorem fppLoop_spec (start stop m : Nat) (hm : stop = start + 2 * m)
    (hb : stepProd start m < 2 ^ 64) :
    ∀ rem t, 1 ≤ t → t ≤ m → m - t ≤ rem →
      fppLoop stop rem (stepProd start t) (start + 2 * t) = stepProd start m := by
  intro rem
  induction rem with
  | zero => intro t h1 h2 h3; have : t = m := by omega
            subst this; simp [fppLoop]
  | succ r ih =>
    intro t h1 h2 h3
    unfold fppLoop
    by_cases ht : t = m
    · subst ht; simp only [show ¬ start + 2 * t < stop by omega, ite_false]
    · simp only [show start + 2 * t < stop by omega, ite_true]
      have hle : stepProd start (t + 1) ≤ stepProd start m := by
        have := stepProd_add start (t + 1) (m - (t + 1))
        rw [show t + 1 + (m - (t + 1)) = m by omega] at this
        rw [this]
        apply Nat.le_mul_of_pos_right
        clear this ih
        generalize m - (t + 1) = q
        induction q with
        | zero => simp [stepProd]
        | succ q ihq => rw [stepProd]; exact Nat.mul_pos ihq (by omega)
      rw [show stepProd start t * (start + 2 * t) = stepProd start (t + 1) from rfl,
        u64_of_lt' (by omega), show start + 2 * t + 2 = start + 2 * (t + 1) by omega]
      exact ih (t + 1) (by omega) (by omega) (by omega)
where
  u64_of_lt' {x : Nat} (h : x < 2 ^ 64) : u64 x = x := Nat.mod_eq_of_lt h

theorem stepProd_pos (s : Nat) (hs : 0 < s) : ∀ m, 0 < stepProd s m
  | 0 => by simp [stepProd]
  | m + 1 => Nat.mul_pos (stepProd_pos s hs m) (by omega)

/-- `factorial_partial_product(start, stop, max_bits)`, mathmodule.c:1893-1941:
the product of the odd numbers in `[start, stop)`. -/
theorem fpp_spec : ∀ fuel start stop maxBits,
    start % 2 = 1 → stop % 2 = 1 → start < stop → stop < 2 ^ 64 →
    bitLength (stop - 2) ≤ maxBits → maxBits ≤ 64 → stop - start ≤ fuel →
    factorialPartialProduct fuel start stop maxBits = .ok (stepProd start ((stop - start) / 2)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ _ h; omega
  | succ f ih =>
    intro start stop maxBits h1 h2 h3 h4 h5 h6 h7
    unfold factorialPartialProduct
    dsimp only
    have hm : stop = start + 2 * ((stop - start) / 2) := by omega
    generalize hM : (stop - start) / 2 = m at *
    split
    · rename_i hc
      have hmb : m * maxBits ≤ 64 := by
        have := hc.2; unfold u64 at this
        rwa [Nat.mod_eq_of_lt (by have := Nat.mul_le_mul hc.1 h6; omega)] at this
      have hfac : ∀ i, i < m → start + 2 * i < 2 ^ maxBits := by
        intro i hi
        have := lt_two_pow_bitLength' (stop - 2)
        have := Nat.pow_le_pow_right (show 0 < 2 by decide) h5
        omega
      have hb : stepProd start m < 2 ^ 64 := by
        rcases stepProd_lt start m maxBits hfac with h | h
        · exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hmb)
        · subst h; simp [stepProd]
      congr 1
      have := fppLoop_spec start stop m hm hb (stop - start) 1 (by omega) (by omega) (by omega)
      simpa [stepProd] using this
    · rename_i hc
      have hm2 : 2 ≤ m := by
        rcases Nat.lt_or_ge m 2 with h | h
        · exfalso; apply hc
          have : m = 1 := by omega
          subst this
          refine ⟨by omega, ?_⟩
          unfold u64; rw [Nat.one_mul, Nat.mod_eq_of_lt (by omega)]; omega
        · exact h
      have hmid : (start + m) ||| 1 = start + 2 * (m / 2 + (if m % 2 = 1 then 1 else 0)) - 0 := by
        rw [or_one_eq]; split <;> omega
      generalize ha : m / 2 + (if m % 2 = 1 then 1 else 0) = a at hmid
      have ha1 : 1 ≤ a := by split at ha <;> omega
      have ha2 : a < m := by split at ha <;> omega
      rw [hmid, Nat.sub_zero]
      have e1 := ih start (start + 2 * a) (bitLength (start + 2 * a - 2)) h1 (by omega) (by omega)
        (by omega) (Nat.le_refl _) (bitLength_le_of_lt' (by omega)) (by omega)
      have e2 := ih (start + 2 * a) stop maxBits (by omega) h2 (by omega) h4 h5 h6 (by omega)
      rw [e1, e2]
      simp only [bind, Except.bind, pure, Except.pure]
      rw [show (start + 2 * a - start) / 2 = a by omega,
        show (stop - (start + 2 * a)) / 2 = m - a by omega, ← stepProd_add,
        show a + (m - a) = m by omega]

/-! ### The odd part of `n!` -/

/-- Product of the odd numbers `<= v`. -/
def oddUpTo (v : Nat) : Nat := stepProd 1 ((v + 1) / 2)

/-- `product_{i >= 0} oddUpTo (v >> i)`, the formula of mathmodule.c:1840-1842. -/
def oddPartF (v : Nat) : Nat := if v = 0 then 1 else oddUpTo v * oddPartF (v / 2)
decreasing_by omega

theorem oddPartF_zero : oddPartF 0 = 1 := by rw [oddPartF]; simp

theorem oddPartF_eq (v : Nat) (h : v ≠ 0) : oddPartF v = oddUpTo v * oddPartF (v / 2) := by
  rw [oddPartF]; simp [h]

theorem oddUpTo_succ (v : Nat) :
    oddUpTo (v + 1) = if v % 2 = 0 then oddUpTo v * (v + 1) else oddUpTo v := by
  unfold oddUpTo
  split
  · rw [show (v + 1 + 1) / 2 = (v + 1) / 2 + 1 by omega, stepProd]
    congr 1; omega
  · rw [show (v + 1 + 1) / 2 = (v + 1) / 2 by omega]

/-- `n! = oddUpTo(n) * 2^(n/2) * (n/2)!`: split `1..n` into odds and evens. -/
theorem fact_split : ∀ n, fact n = oddUpTo n * 2 ^ (n / 2) * fact (n / 2)
  | 0 => by simp [fact, oddUpTo, stepProd]
  | n + 1 => by
    rw [fact_succ, fact_split n, oddUpTo_succ]
    split
    · rw [show (n + 1) / 2 = n / 2 by omega]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    · rw [show (n + 1) / 2 = n / 2 + 1 by omega, fact_succ, Nat.pow_succ,
        show n + 1 = 2 * (n / 2 + 1) by omega]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- `n! == odd_part << (n - popcount(n))`, mathmodule.c:1877-1884. -/
theorem oddPartF_mul_two_pow : ∀ n, oddPartF n * 2 ^ (n - pc n) = fact n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [oddPartF, pc, fact]
    · rw [oddPartF_eq n (by omega), fact_split n, pc_eq n]
      have h1 := pc_le_self (n / 2)
      rw [show n - (pc (n / 2) + n % 2) = n / 2 + (n / 2 - pc (n / 2)) by omega, Nat.pow_add,
        ← ih (n / 2) (by omega)]
      simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- `upper` as maintained by `factorial_odd_part`: `3` until `v > 2`. -/
def oddUp (v : Nat) : Nat := if v ≤ 2 then 3 else (v + 1) ||| 1

theorem oddUpTo_le2 (v : Nat) (h : v ≤ 2) : oddUpTo v = 1 := by
  unfold oddUpTo
  rcases (show (v + 1) / 2 = 0 ∨ (v + 1) / 2 = 1 by omega) with e | e <;> rw [e] <;> rfl

theorem shiftRight_succ_eq (n c : Nat) : n >>> (c + 1) = (n >>> c) / 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]

/-- The loop of `factorial_odd_part`, mathmodule.c:1958-1986. -/
theorem factorialOddPartLoop_spec (n : Nat) (hn : n < 2 ^ 63) :
    ∀ c upper inner outer, upper = oddUp (n >>> c) → inner = oddUpTo (n >>> c) →
      outer = oddPartF (n >>> c) → factorialOddPartLoop n c upper inner outer = .ok (oddPartF n) := by
  intro c
  induction c with
  | zero => intro u i o _ _ ho; simp [factorialOddPartLoop, ho]
  | succ c ih =>
    intro upper inner outer hu hi ho
    unfold factorialOddPartLoop
    rw [shiftRight_succ_eq] at hu hi ho
    generalize hv : n >>> c = v' at *
    have hv'n : v' ≤ n := by rw [← hv, Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
    by_cases h2 : v' ≤ 2
    · simp only [h2, ite_true]
      apply ih
      · rw [hu]; unfold oddUp; simp [h2, show v' / 2 ≤ 2 by omega]
      · rw [hi, oddUpTo_le2 _ h2, oddUpTo_le2 _ (by omega)]
      · rw [ho]
        by_cases h0 : v' = 0
        · subst h0; rfl
        · rw [oddPartF_eq v' h0, oddUpTo_le2 _ h2, Nat.one_mul]
    · simp only [h2, ite_false]
      -- lower = upper = oddUp (v'/2); new upper = (v' + 1) ||| 1
      have hup : (v' + 1) ||| 1 = 2 * ((v' + 1) / 2) + 1 := by rw [or_one_eq]
      have hlow : upper = 2 * ((upper - 1) / 2) + 1 ∧ 3 ≤ upper ∧ upper < (v' + 1) ||| 1 := by
        rw [hu, hup]; unfold oddUp
        split
        · omega
        · rw [or_one_eq]; omega
      have hinner : inner = stepProd 1 ((upper - 1) / 2) := by
        rw [hi, hu]; unfold oddUp
        split
        · rw [oddUpTo_le2 _ (by omega)]; rfl
        · unfold oddUpTo; rw [or_one_eq]; congr 1; omega
      generalize hU : (v' + 1) ||| 1 = U at *
      have e1 := fpp_spec (U + 1) upper U (bitLength (U - 2)) (by omega) (by omega) hlow.2.2
        (by omega) (Nat.le_refl _) (bitLength_le_of_lt' (by omega)) (by omega)
      have hs : stepProd 1 ((upper - 1) / 2) * stepProd upper ((U - upper) / 2) = oddUpTo v' := by
        have := stepProd_add 1 ((upper - 1) / 2) ((U - upper) / 2)
        rw [show 1 + 2 * ((upper - 1) / 2) = upper by omega,
          show (upper - 1) / 2 + (U - upper) / 2 = (v' + 1) / 2 by omega] at this
        exact this.symm
      rw [e1]
      simp only [bind, Except.bind]
      apply ih
      · unfold oddUp; simp [h2, hU]
      · rw [hinner, hs]
      · rw [oddPartF_eq v' (by omega), ho, hinner, hs, Nat.mul_comm]

theorem smallFactorials_ok : ∀ x, x < 21 → smallFactorials.getD x 0 = fact x := by
  have h : (List.range 21).all (fun x => smallFactorials.getD x 0 == fact x) = true := by
    decide +kernel
  intro x hx
  have := (List.all_eq_true.mp h) x (List.mem_range.mpr hx)
  simpa using this

/-- `math.factorial` docs: "Return n factorial as an integer"; and `perm(n)`
(`k=None`) "returns n!". Exact for every `0 <= n <= LONG_MAX`. -/
def FactorialExact : Prop :=
  ∀ n : Int, 0 ≤ n → n ≤ llongMax →
    factorial n = .ok (fact n.toNat) ∧ perm n none = .ok (fact n.toNat)

theorem factorialExact_proven : FactorialExact := by
  intro n h0 h1
  have hp : perm n none = factorial n := rfl
  rw [hp]
  suffices factorial n = .ok (fact n.toNat) from ⟨this, this⟩
  obtain ⟨N, rfl⟩ : ∃ N : Nat, n = N := ⟨n.toNat, by omega⟩
  have hN : N < 2 ^ 63 := by simp [llongMax] at h1; omega
  unfold factorial
  simp only [show ¬ ((N : Int) > llongMax) by omega, show ¬ ((N : Int) < 0) by omega, ite_false,
    Int.toNat_natCast]
  by_cases hs : N < smallFactorials.length
  · simp only [hs, ite_true]
    rw [smallFactorials_ok N (by simpa [smallFactorials] using hs)]
  · simp only [hs, ite_false]
    have hN21 : 21 ≤ N := by simp [smallFactorials] at hs; omega
    have hbl : 5 ≤ bitLength N := by
      have := lt_two_pow_bitLength' N
      rcases Nat.lt_or_ge (bitLength N) 5 with h | h
      · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show bitLength N ≤ 4 by omega)
        omega
      · exact h
    have htop : N >>> (bitLength N - 2 + 1) = 1 := by
      rw [show bitLength N - 2 + 1 = bitLength N - 1 by omega, Nat.shiftRight_eq_div_pow]
      unfold bitLength at hbl ⊢
      simp only [show N ≠ 0 by omega, ite_false] at hbl ⊢
      rw [Nat.add_sub_cancel]
      have a1 := Nat.log2_self_le (show N ≠ 0 by omega)
      have a2 := @Nat.lt_log2_self N
      apply Nat.le_antisymm
      · apply Nat.le_of_lt_succ
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        rw [Nat.pow_succ] at a2; omega
      · exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr (by omega)
    have hodd := factorialOddPartLoop_spec N hN (bitLength N - 2 + 1) 3 1 1
      (by rw [htop]; rfl) (by rw [htop]; rfl)
      (by rw [htop, oddPartF_eq 1 (by decide), oddPartF_zero]; rfl)
    unfold factorialOddPart
    rw [hodd]
    simp only [bind, Except.bind, pure, Except.pure]
    rw [countSetBits_eq 64 N (pc_le 64 N (by omega)), Nat.shiftLeft_eq, oddPartF_mul_two_pow]

end PyLean.MathInt
