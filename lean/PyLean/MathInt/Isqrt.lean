import PyLean.MathInt.Model
import PyLean.MathInt.IsqrtAlg

/-!
`math.isqrt` returns the integer square root for every `n >= 0`: the 64-bit
fast path (`_approximate_isqrt` with its 192-entry table and `uint32_t`
arithmetic) and the slow path (five iterations in C, then Python ints).
-/

namespace PyLean.MathInt

open PyLean

/-- Each entry of `_approximate_isqrt_tab` approximates the square root of
every 16-bit `t` it serves (`t >> 8 == i + 64`), and lies in `[128, 255]`. -/
def isqrtTabOk : Bool :=
  (List.range 192).all fun i =>
    let a := isqrtTab.getD i 0
    let lo := (i + 64) * 256
    (a - 1) * (a - 1) < lo && lo + 255 < (a + 1) * (a + 1) && 128 ≤ a && a ≤ 255

theorem isqrtTabOk_eq : isqrtTabOk = true := by decide +kernel

theorem shr_shr (n a b : Nat) : n >>> a >>> b = n >>> (a + b) := by
  rw [Nat.shiftRight_add]

theorem approx_tab (N : Nat) (h1 : 2 ^ 62 ≤ N) (h2 : N < 2 ^ 64) :
    Approx (isqrtTab.getD ((N >>> 56) - 64) 0) (N >>> 48) ∧
      128 ≤ isqrtTab.getD ((N >>> 56) - 64) 0 ∧ isqrtTab.getD ((N >>> 56) - 64) 0 ≤ 255 := by
  have e56 : N >>> 56 = (N >>> 48) / 256 := by
    rw [show 56 = 48 + 8 from rfl, ← shr_shr, Nat.shiftRight_eq_div_pow (N >>> 48) 8]
  have ht1 : 2 ^ 14 ≤ N >>> 48 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have ht2 : N >>> 48 < 2 ^ 16 := by rw [Nat.shiftRight_eq_div_pow]; omega
  rw [e56]
  generalize N >>> 48 = t at *
  have hi : t / 256 - 64 < 192 := by omega
  have := (List.all_eq_true.mp isqrtTabOk_eq) (t / 256 - 64) (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := this
  rw [show t / 256 - 64 + 64 = t / 256 by omega] at c1 c2
  refine ⟨⟨?_, ?_⟩, c3, c4⟩
  · have : t / 256 * 256 ≤ t := Nat.div_mul_le_self t 256
    omega
  · have : t < t / 256 * 256 + 256 := by omega
    omega

theorem approx_bounds_of {a m lo hi : Nat} (h : Approx a m) (h1 : lo * lo ≤ m) (h2 : m < hi * hi) :
    lo ≤ a + 1 ∧ a ≤ hi := by
  obtain ⟨k1, k2⟩ := h
  constructor
  · refine Classical.byContradiction fun hc => ?_
    have := Nat.mul_self_lt_mul_self (show a + 1 < lo by omega); omega
  · refine Classical.byContradiction fun hc => ?_
    have := Nat.mul_self_le_mul_self (show hi ≤ a - 1 by omega); omega

theorem u32_of_lt {x : Nat} (h : x < 2 ^ 32) : u32 x = x := Nat.mod_eq_of_lt h

/-- `_approximate_isqrt(n)` for `2^62 <= n < 2^64`, mathmodule.c:1671-1681:
"return `a` satisfying `(a - 1)**2 < n < (a + 1)**2`", with no `uint32_t`
wraparound. -/
theorem approxIsqrt_spec (N : Nat) (h1 : 2 ^ 62 ≤ N) (h2 : N < 2 ^ 64) :
    Approx (approxIsqrt N) N ∧ approxIsqrt N < 2 ^ 32 := by
  obtain ⟨hA0, hlo, hhi⟩ := approx_tab N h1 h2
  generalize hu0 : isqrtTab.getD ((N >>> 56) - 64) 0 = u0 at *
  -- first Newton step, k = 8, on m = N >> 32
  have s1 := newton_step (N >>> 32) u0 8 (by decide)
    (by rw [shr_shr]; exact hA0) (by simp; omega)
  rw [shr_shr] at s1
  simp only [show 8 - 1 = 7 from rfl, show 32 + (8 + 1) = 41 from rfl] at s1
  have e41 : N >>> 41 < 2 ^ 23 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hq1 : (N >>> 41) / u0 ≤ 2 ^ 16 := by
    have := Nat.div_le_div_left (a := N >>> 41) hlo (show 0 < 128 by decide)
    omega
  have hu1eq : u32 (u32 (u0 <<< 7) + u32 (N >>> 41) / u0) = (u0 <<< 7) + (N >>> 41) / u0 := by
    have : u0 <<< 7 < 2 ^ 15 := by rw [Nat.shiftLeft_eq]; omega
    rw [u32_of_lt (x := u0 <<< 7) (by omega), u32_of_lt (x := N >>> 41) (by omega),
      u32_of_lt (x := (u0 <<< 7) + (N >>> 41) / u0) (by omega)]
  generalize hu1 : (u0 <<< 7) + (N >>> 41) / u0 = u1 at *
  have hm32a : 2 ^ 15 * 2 ^ 15 ≤ N >>> 32 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hm32b : N >>> 32 < 65536 * 65536 := by rw [Nat.shiftRight_eq_div_pow]; omega
  obtain ⟨b1, b2⟩ := approx_bounds_of s1 hm32a hm32b
  have hu1lo : 2 ^ 15 ≤ u1 := by
    refine Classical.byContradiction fun hc => ?_
    have : u1 + 1 ≤ 2 ^ 15 := by omega
    have := Nat.mul_self_le_mul_self this
    have := s1.2
    omega
  -- second Newton step, k = 16, on m = N
  have s2 := newton_step N u1 16 (by decide) (by exact s1) (by simp; omega)
  simp only [show 16 - 1 = 15 from rfl, show 16 + 1 = 17 from rfl] at s2
  have hq2 : (N >>> 17) / u1 < 2 ^ 32 := by
    have e17 : N >>> 17 < 2 ^ 47 := by rw [Nat.shiftRight_eq_div_pow]; omega
    have := Nat.div_le_div_left (a := N >>> 17) hu1lo (show 0 < 2 ^ 15 by decide)
    have : (N >>> 17) / 2 ^ 15 < 2 ^ 32 := by
      rw [Nat.div_lt_iff_lt_mul (by decide)]; omega
    omega
  have hs1 : u1 <<< 15 ≤ 2 ^ 31 := by
    rw [Nat.shiftLeft_eq]
    have := Nat.mul_le_mul_right (2 ^ 15) b2
    have e : 65536 * 2 ^ 15 = 2 ^ 31 := by decide
    omega
  -- the result does not wrap: b < 2^32
  have hb : (u1 <<< 15) + (N >>> 17) / u1 < 2 ^ 32 := by
    refine Classical.byContradiction fun hc => ?_
    have hle : (u1 <<< 15) + (N >>> 17) / u1 ≤ 2 ^ 32 := by
      have := s2.1
      refine Classical.byContradiction fun hc2 => ?_
      have := Nat.mul_self_le_mul_self (show 2 ^ 32 ≤ (u1 <<< 15) + (N >>> 17) / u1 - 1 by omega)
      omega
    have heq : (u1 <<< 15) + (N >>> 17) / u1 = 2 ^ 32 := by omega
    have htop : (2 ^ 32 - 1) * (2 ^ 32 - 1) < N := by have := s2.1; rw [heq] at this; exact this
    have h56 : N >>> 56 = 255 := by rw [Nat.shiftRight_eq_div_pow]; omega
    have h41 : N >>> 41 = 2 ^ 23 - 1 := by rw [Nat.shiftRight_eq_div_pow]; omega
    rw [h56] at hu0
    have : u0 = 255 := by rw [← hu0]; rfl
    subst this
    rw [h41] at hu1
    have : u1 = 65536 := by rw [← hu1, Nat.shiftLeft_eq] <;> omega
    subst this
    have : (65536 <<< 15) + (N >>> 17) / 65536 < 2 ^ 32 := by
      rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
    omega
  unfold approxIsqrt
  rw [hu0]
  simp only
  rw [hu1eq, u32_of_lt (x := u1 <<< 15) (by omega), u32_of_lt (x := (N >>> 17) / u1) hq2,
    u32_of_lt (x := (u1 <<< 15) + (N >>> 17) / u1) hb]
  exact ⟨s2, hb⟩

theorem bitLength_bounds (n : Nat) (h : 1 ≤ n) :
    2 ^ (bitLength n - 1) ≤ n ∧ n < 2 ^ bitLength n := by
  unfold bitLength
  simp only [show n ≠ 0 by omega, ite_false, Nat.add_sub_cancel]
  exact ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

theorem two_pow_le_iff_lt_bitLength (c k : Nat) (hc : 1 ≤ c) : 2 ^ k ≤ c ↔ k < bitLength c := by
  obtain ⟨b1, b2⟩ := bitLength_bounds c hc
  constructor
  · intro h
    refine Classical.byContradiction fun hk => ?_
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show bitLength c ≤ k by omega)
    omega
  · intro h
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) b1

/-- The `c_bit_length` loop computes `c.bit_length()`, mathmodule.c:1745-1748. -/
theorem cBitLength_eq (c : Nat) (hc : 1 ≤ c) :
    ∀ fuel k, k ≤ bitLength c → bitLength c ≤ k + fuel → cBitLength c fuel k = bitLength c := by
  intro fuel
  induction fuel with
  | zero => intro k h1 h2; simp [cBitLength]; omega
  | succ f ih =>
    intro k h1 h2
    unfold cBitLength
    by_cases hk : k < bitLength c
    · have : c >>> k > 0 := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_pos ((two_pow_le_iff_lt_bitLength c k hc).mpr hk) (Nat.two_pow_pos _)
      simp only [this, ite_true]
      exact ih (k + 1) (by omega) (by omega)
    · have : ¬ c >>> k > 0 := by
        rw [Nat.shiftRight_eq_div_pow]
        have := mt (two_pow_le_iff_lt_bitLength c k hc).mp hk
        rw [Nat.div_eq_of_lt (by omega)]; omega
      simp only [this, ite_false]; omega

theorem shr_succ (n c : Nat) : n >>> (c + 1) = (n >>> c) / 2 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem shr_lower (n c t : Nat) (hn : 2 ^ (2 * c) ≤ n) (ht : t ≤ c) : 2 ^ (2 * t) ≤ n >>> (2 * (c - t)) := by
  rw [Nat.shiftRight_eq_div_pow]
  apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
  rw [← Nat.pow_add, show 2 * t + 2 * (c - t) = 2 * c by omega]; exact hn

/-- The Newton loop of the slow path keeps `(a-1)^2 < n >> 2(c-d) < (a+1)^2`,
mathmodule.c:1764-1791. -/
theorem isqrtLoop_spec (n c : Nat) (hn : 2 ^ (2 * c) ≤ n) (hc : 1 ≤ c) :
    ∀ j d a, d = c >>> j → j + 5 ≤ bitLength c → Approx a (n >>> (2 * (c - d))) →
      Approx (isqrtLoop n c j d a) n := by
  intro j
  induction j with
  | zero => intro d a hd _ ha; simp only [isqrtLoop]; simpa [hd] using ha
  | succ j ih =>
    intro e a he hj ha
    simp only [isqrtLoop]
    have hcj : 2 ^ (bitLength c - 1) ≤ c := (bitLength_bounds c hc).1
    have hdc : c >>> j ≤ c := by rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
    have he2 : e = (c >>> j) / 2 := by rw [he, shr_succ]
    have he16 : 16 ≤ e := by
      rw [he, Nat.shiftRight_eq_div_pow]
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      have : 16 * 2 ^ (j + 1) ≤ 2 ^ (bitLength c - 1) := by
        rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add]
        exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    generalize hd : c >>> j = d at *
    -- newton step with k = d - e
    have hk1 : 1 ≤ d - e := by omega
    have hshift : n >>> (2 * (c - d)) >>> (2 * (d - e)) = n >>> (2 * (c - e)) := by
      rw [shr_shr]; congr 1; omega
    have hpow : 2 ^ (d - e - 1) ≤ a := by
      have hlow := shr_lower n c e hn (by omega)
      have h2 := ha.2
      refine Classical.byContradiction fun hc2 => ?_
      have := Nat.mul_self_le_mul_self (show a + 1 ≤ 2 ^ (d - e - 1) by omega)
      have : 2 ^ (d - e - 1) * 2 ^ (d - e - 1) ≤ 2 ^ (2 * e) := by
        rw [← Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (by omega)
      omega
    have step := newton_step (n >>> (2 * (c - d))) a (d - e) hk1 (by rw [hshift]; exact ha) hpow
    rw [shr_shr, show 2 * (c - d) + (d - e + 1) = 2 * c - d - e + 1 by omega,
      show d - e - 1 = d - 1 - e by omega] at step
    exact ih d _ rfl (by omega) step

/-- `math.isqrt` docs: "Return the integer square root of the nonnegative
integer n. This is the floor of the exact square root of n, or equivalently
the greatest integer a such that a**2 <= n." -/
def IsqrtFloorSqrt : Prop :=
  ∀ n : Nat, ∃ r, isqrt n = .ok r ∧ r * r ≤ n ∧ n < (r + 1) * (r + 1)

theorem isqrtFloorSqrt_proven : IsqrtFloorSqrt := by
  intro n
  by_cases h0 : n = 0
  · subst h0; exact ⟨0, rfl, by decide, by decide⟩
  have hn1 : 1 ≤ n := by omega
  obtain ⟨bl1, bl2⟩ := bitLength_bounds n hn1
  unfold isqrt
  simp only [show ¬ ((n : Int) < 0) by omega, show ¬ ((n : Int) = 0) by omega, ite_false,
    Int.toNat_natCast]
  generalize hc : (bitLength n - 1) / 2 = c
  have hlo : 2 ^ (2 * c) ≤ n := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) bl1
  have hhi : n < 2 ^ (2 * c + 2) := Nat.lt_of_lt_of_le bl2 (Nat.pow_le_pow_right (by decide) (by omega))
  by_cases hfast : c ≤ 31
  · simp only [hfast, ite_true]
    -- fast path
    have hN : n <<< (2 * (31 - c)) = n * 2 ^ (2 * (31 - c)) := Nat.shiftLeft_eq _ _
    have hNlt : n * 2 ^ (2 * (31 - c)) < 2 ^ 64 := by
      have := Nat.mul_lt_mul_of_pos_right hhi (Nat.two_pow_pos (2 * (31 - c)))
      rw [← Nat.pow_add, show 2 * c + 2 + 2 * (31 - c) = 64 by omega] at this; exact this
    have hNge : 2 ^ 62 ≤ n * 2 ^ (2 * (31 - c)) := by
      have := Nat.mul_le_mul_right (2 ^ (2 * (31 - c))) hlo
      rw [← Nat.pow_add, show 2 * c + 2 * (31 - c) = 62 by omega] at this; exact this
    rw [hN, show u64 (n * 2 ^ (2 * (31 - c))) = n * 2 ^ (2 * (31 - c)) from Nat.mod_eq_of_lt hNlt]
    obtain ⟨hA, hAlt⟩ := approxIsqrt_spec _ hNge hNlt
    have hA31 : 2 ^ 31 ≤ approxIsqrt (n * 2 ^ (2 * (31 - c))) := by
      refine Classical.byContradiction fun h => ?_
      have := Nat.mul_self_le_mul_self (show approxIsqrt (n * 2 ^ (2 * (31 - c))) + 1 ≤ 2 ^ 31 by omega)
      have := hA.2
      omega
    have hsh := approx_shift _ _ (31 - c) hA (Or.inr ⟨by
      rw [← two_pow_two_mul]; exact Nat.mul_mod_left _ _, by
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      rw [Nat.one_mul]; exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hA31⟩)
    rw [Nat.shiftRight_eq_div_pow (n * _), Nat.mul_div_cancel _ (Nat.two_pow_pos _)] at hsh
    have := approx_correct _ _ hsh
    refine ⟨_, rfl, ?_⟩
    simp only [gt_iff_lt] at this ⊢
    exact this
  · simp only [hfast, ite_false]
    -- slow path
    have hc1 : 32 ≤ c := by omega
    have hcb : 6 ≤ bitLength c := by
      have := (two_pow_le_iff_lt_bitLength c 5 (by omega)).mp (by omega); omega
    have hcbl : cBitLength c (c + 1) 6 = bitLength c := by
      apply cBitLength_eq c (by omega) _ _ hcb
      have := (bitLength_bounds c (by omega)).1
      have : bitLength c - 1 < 2 ^ (bitLength c - 1) := Nat.lt_two_pow_self
      omega
    simp only [hcbl]
    obtain ⟨cb1, cb2⟩ := bitLength_bounds c (by omega)
    -- d0 = top five bits of c
    have hd0a : 16 ≤ c >>> (bitLength c - 5) := by
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      rw [show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add, show 4 + (bitLength c - 5) = bitLength c - 1 by omega]
      exact cb1
    have hd0b : c >>> (bitLength c - 5) ≤ 31 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply Nat.le_of_lt_succ
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      have : 2 ^ 5 * 2 ^ (bitLength c - 5) = 2 ^ bitLength c := by
        rw [← Nat.pow_add, show 5 + (bitLength c - 5) = bitLength c by omega]
      show c < 32 * 2 ^ (bitLength c - 5)
      rw [show (32 : Nat) = 2 ^ 5 from rfl, this]; exact cb2
    have hd0c : c >>> (bitLength c - 5) ≤ c := by
      rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
    generalize hd0 : c >>> (bitLength c - 5) = d0 at *
    -- b = n >> (2c - 62) lies in [2^62, 2^64)
    have hb1 : 2 ^ 62 ≤ n >>> (2 * c - 62) := by
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      rw [← Nat.pow_add, show 62 + (2 * c - 62) = 2 * c by omega]; exact hlo
    have hb2 : n >>> (2 * c - 62) < 2 ^ 64 := by
      rw [Nat.shiftRight_eq_div_pow]
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
      rw [← Nat.pow_add, show 64 + (2 * c - 62) = 2 * c + 2 by omega]; exact hhi
    simp only [show ¬ (n >>> (2 * c - 62) ≥ 2 ^ 64) by omega, ite_false]
    generalize hB : n >>> (2 * c - 62) = B at *
    obtain ⟨hA, hAlt⟩ := approxIsqrt_spec B hb1 hb2
    have hA31 : 2 ^ 31 ≤ approxIsqrt B := by
      refine Classical.byContradiction fun h => ?_
      have := Nat.mul_self_le_mul_self (show approxIsqrt B + 1 ≤ 2 ^ 31 by omega)
      have := hA.2
      omega
    have hsh := approx_shift _ _ (31 - d0) hA (Or.inl (by
      apply (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).mpr
      have : 2 * 2 ^ (31 - d0) ≤ 2 ^ 31 := by
        rw [← Nat.pow_succ']; exact Nat.pow_le_pow_right (by decide) (by omega)
      omega))
    have hBs : B >>> (2 * (31 - d0)) = n >>> (2 * (c - d0)) := by
      rw [← hB, shr_shr]; congr 1; omega
    rw [hBs] at hsh
    have hloop := isqrtLoop_spec n c hlo (by omega) (bitLength c - 6 + 1) d0 _
      (by rw [← hd0]; congr 1; omega) (by omega) hsh
    have := approx_correct _ _ hloop
    exact ⟨_, rfl, this⟩

end PyLean.MathInt
