import PyLean.TextLibs.StructProps

/-!
Integer round trip through the real dispatch: every integer entry of every format
table, `runPack` then `runUnpack`, for every in-range value. This is what credits the
`np_*`, `nu_*`, `bp_*`, `bu_*`, `lp_*`, `lu_*` integer routines, so it includes
the pre-swap `lilendianTable0`, whose `lu_short` etc. CPython replaces at start-up on
a little-endian build and the difftest therefore cannot reach.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

/-! ### The C sign extension -/

theorem xor_low (k x : Nat) (h : x < 2 ^ k) : x ^^^ 2 ^ k = 2 ^ k + x := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hi : i = k
  · subst hi
    simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h]
  · by_cases hlt : i < k
    · rw [Nat.testBit_two_pow_add_gt hlt]
      simp [Ne.symm hi]
    · have hgt : k < i := by omega
      have h1 : x.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hgt)))
      have h2 : (2 ^ k + x).testBit i = false := by
        apply Nat.testBit_lt_two_pow
        have : 2 ^ (k + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hgt
        rw [Nat.pow_succ] at this
        omega
      simp [h1, h2, Ne.symm hi]

theorem xor_high (k r : Nat) (h : r < 2 ^ k) : (2 ^ k + r) ^^^ 2 ^ k = r := by
  rw [← xor_low k r h, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem and_low (k x : Nat) (h : x < 2 ^ k) : x &&& 2 ^ k = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
  by_cases hi : i = k
  · subst hi
    simp [Nat.testBit_lt_two_pow h]
  · simp [Ne.symm hi]

/-- `signExtC` on a value below the sign bit returns it unchanged. -/
theorem signExtC_low (k x : Nat) (hk : k < 64) (h : x < 2 ^ k) :
    signExtC (2 ^ k) x = x := by
  have hw : (2 : Nat) ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hk)
  have hy : ((x ^^^ 2 ^ k) + 2 ^ 64 - 2 ^ k) % 2 ^ 64 = x := by
    rw [xor_low k x h]
    have e : 2 ^ k + x + 2 ^ 64 - 2 ^ k = x + 2 ^ 64 := by omega
    rw [e, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  simp only [signExtC]
  rw [hy, and_low k x h]
  simp

/-- `signExtC` at the three widths the C uses, on a value with the sign bit set. -/
theorem signExtC_high (k r : Nat) (hk : k = 15 ∨ k = 31 ∨ k = 63) (h : r < 2 ^ k) :
    signExtC (2 ^ k) (2 ^ k + r) = (r : Int) - 2 ^ k := by
  have hy : (((2 ^ k + r) ^^^ 2 ^ k) + 2 ^ 64 - 2 ^ k) % 2 ^ 64 = r + 2 ^ 64 - 2 ^ k := by
    rw [xor_high k r h]
    rcases hk with rfl | rfl | rfl <;> exact Nat.mod_eq_of_lt (by omega)
  have hbit : (r + 2 ^ 64 - 2 ^ k).testBit k = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases hk with rfl | rfl | rfl <;> (simp only [decide_eq_true_eq]; omega)
  simp only [signExtC]
  rw [hy]
  have hne : (r + 2 ^ 64 - 2 ^ k) &&& 2 ^ k ≠ 0 := by
    intro h0
    have := congrArg (fun v => v.testBit k) h0
    simp [Nat.testBit_and, hbit] at this
  rw [if_pos hne]
  rcases hk with rfl | rfl | rfl <;> omega

/-! ### Decoding what the pack loops wrote -/

theorem leBytes_length : ∀ (i x : Nat), (leBytes i x).length = i
  | 0, _ => rfl
  | i + 1, x => by simp [leBytes, leBytes_length i]

theorem twos_length (s : Nat) (x : Int) : (twos s x).length = s := leBytes_length _ _

theorem lpLoop_length : ∀ (i : Nat) (x : Int), (lpLoop i x).length = i
  | 0, _ => rfl
  | i + 1, x => by simp [lpLoop, lpLoop_length i]

theorem bpLoop_length : ∀ (i : Nat) (x : Int), (bpLoop i x).length = i
  | 0, _ => rfl
  | i + 1, x => by simp [bpLoop, bpLoop_length i]

/-- One step of `x & 0xff; x >>= 8`: `x % (256 * P)` from the byte and the shifted rest. -/
theorem emod_step (x P : Int) (hP : 0 < P) :
    x % (256 * P) = x % 256 + 256 * ((x / 256) % P) := by
  have h1 := Int.emod_add_mul_ediv x 256
  have h2 := Int.emod_add_mul_ediv (x / 256) P
  have h3 := Int.emod_nonneg (x / 256) (Int.ne_of_gt hP)
  have h4 := Int.emod_lt_of_pos (x / 256) hP
  have h5 : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
  have h6 : x % 256 < 256 := Int.emod_lt_of_pos _ (by decide)
  generalize hu : (x / 256) % P = u at *
  generalize hv : (x / 256) / P = t at *
  generalize hb : x % 256 = b at *
  generalize hq : x / 256 = q at *
  have hx : x = (b + 256 * u) + (256 * P) * t := by
    rw [← h1, ← h2, Int.mul_add, Int.mul_assoc]
    omega
  rw [hx, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt <;> omega

theorem pow8_succ (i : Nat) : (2 : Int) ^ (8 * (i + 1)) = 256 * 2 ^ (8 * i) := by
  rw [Nat.mul_add, Int.pow_add, Int.mul_comm]
  rfl

theorem leVal_lpLoop : ∀ (i : Nat) (x : Int), (leVal (lpLoop i x) : Int) = x % 2 ^ (8 * i)
  | 0, x => by simp [lpLoop, leVal, Int.emod_one]
  | i + 1, x => by
    have hb : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
    simp only [lpLoop, leVal, Int.natCast_add, Int.natCast_mul, leVal_lpLoop i (x / 256)]
    rw [pow8_succ, emod_step x _ (Int.pow_pos (by decide))]
    rw [Int.toNat_of_nonneg hb]
    rfl

theorem beVal_snoc (l : List Nat) (b : Nat) : beVal (l ++ [b]) = beVal l * 256 + b := by
  simp [beVal, List.foldl_append]

theorem beVal_bpLoop : ∀ (i : Nat) (x : Int), (beVal (bpLoop i x) : Int) = x % 2 ^ (8 * i)
  | 0, x => by simp [bpLoop, beVal, Int.emod_one]
  | i + 1, x => by
    have hb : 0 ≤ x % 256 := Int.emod_nonneg _ (by decide)
    simp only [bpLoop, beVal_snoc, Int.natCast_add, Int.natCast_mul, beVal_bpLoop i (x / 256)]
    rw [pow8_succ, emod_step x _ (Int.pow_pos (by decide)), Int.toNat_of_nonneg hb]
    show _ * 256 + _ = _
    omega

end PyLean.TextLibs.Struct
