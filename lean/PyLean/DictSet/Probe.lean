import PyLean.DictSet.Common

/-!
The probe sequence reaches every slot. `Objects/dictobject.c:363-365` cites this as folklore:
"repeating that 2**i times generates each int in range(2**i) exactly once". Here it is
proved from scratch: `j -> 5*j + 1` has full period modulo every power of two, and `perturb`,
a 64-bit value shifted right by 5, is 0 after 13 steps.
-/

namespace PyLean.DictSet

/-- The unreduced recurrence `x, 5x+1, 5(5x+1)+1, ...`. -/
def lcg (x : Nat) : Nat → Nat
  | 0 => x
  | k + 1 => 5 * lcg x k + 1

theorem lcg_add (x a b : Nat) : lcg x (a + b) = lcg (lcg x a) b := by
  induction b with
  | zero => rfl
  | succ b ih => simp [← Nat.add_assoc, lcg, ih]

/-- `lcg x k = x + (lcg 0 k) * (4x + 1)`: the closed form that makes the period visible. -/
theorem lcg_closed (x k : Nat) : lcg x k = x + lcg 0 k * (4 * x + 1) := by
  induction k with
  | zero => simp [lcg]
  | succ k ih =>
    simp only [lcg, ih]
    generalize lcg 0 k = a
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
    have : 5 * (a * (4 * x)) = (5 * a) * (4 * x) := by simp [Nat.mul_assoc, Nat.mul_left_comm]
    omega

theorem lcg_zero_double (k : Nat) : lcg 0 (k + k) = 2 * lcg 0 k * (2 * lcg 0 k + 1) := by
  rw [lcg_add, lcg_closed]
  generalize lcg 0 k = a
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one]
  have h1 : 2 * a * (2 * a) = a * (4 * a) := by
    simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  omega

/-- `lcg 0 (2^n)` is exactly divisible by `2^n`: `2^n` times an odd number. -/
theorem lcg_pow_two (n : Nat) : ∃ o, lcg 0 (2 ^ n) = 2 ^ n * (2 * o + 1) := by
  induction n with
  | zero => exact ⟨0, by simp [lcg]⟩
  | succ n ih =>
    obtain ⟨o, ho⟩ := ih
    have e : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [Nat.pow_succ]; omega
    rw [e, lcg_zero_double, ho]
    generalize hA : 2 ^ n * (2 * o + 1) = A
    -- `(2o+1)(2A+1)` is odd
    refine ⟨o * (2 * A + 1) + A, ?_⟩
    rw [← hA]
    generalize hB : 2 ^ n * (2 * o + 1) = B
    have : (2 ^ n + 2 ^ n) * (2 * (o * (2 * B + 1) + B) + 1)
        = 2 * (2 ^ n * ((2 * o + 1) * (2 * B + 1))) := by
      have h : (2 * (o * (2 * B + 1) + B) + 1) = (2 * o + 1) * (2 * B + 1) := by
        simp only [Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
        have : 2 * (o * (2 * B)) = 2 * o * (2 * B) := by simp [Nat.mul_assoc]
        omega
      rw [h]
      generalize (2 * o + 1) * (2 * B + 1) = c
      rw [Nat.add_mul, Nat.two_mul]
    rw [this, ← hB]
    simp [Nat.mul_assoc]

/-- `2^n` steps add `2^n` times an odd number. -/
theorem lcg_period (n z : Nat) : ∃ w, lcg z (2 ^ n) = z + 2 ^ n * (2 * w + 1) := by
  obtain ⟨o, ho⟩ := lcg_pow_two n
  refine ⟨o * (4 * z + 1) + 2 * z, ?_⟩
  rw [lcg_closed, ho, Nat.mul_assoc]
  congr 2
  have : (2 * o + 1) * (4 * z + 1) = 2 * o * (4 * z + 1) + (4 * z + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [this]
  have h2 : 2 * (o * (4 * z + 1) + 2 * z) = 2 * o * (4 * z + 1) + 4 * z := by
    simp [Nat.mul_add, Nat.mul_assoc]
    omega
  omega

private theorem mod_double (P a r : Nat) (hr : r < P) :
    (P * a + r) % (2 * P) = P * (a % 2) + r := by
  have hP : 0 < P := by omega
  have ha : a = 2 * (a / 2) + a % 2 := (Nat.div_add_mod a 2).symm
  have hb : a % 2 < 2 := Nat.mod_lt _ (by omega)
  have : P * a + r = (2 * P) * (a / 2) + (P * (a % 2) + r) := by
    conv => lhs; rw [ha]
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm P 2]
    omega
  rw [this, Nat.mul_add_mod]
  apply Nat.mod_eq_of_lt
  have : P * (a % 2) ≤ P * 1 := Nat.mul_le_mul_left _ (by omega)
  omega

private theorem parity_flip (a b w : Nat) (h : ¬ a % 2 = b % 2) :
    (a + (2 * w + 1)) % 2 = b % 2 := by omega

/-- Full period: from any `x`, every residue mod `2^n` turns up within `2^n` steps. -/
theorem lcg_full_period (n x y : Nat) : ∃ k, k < 2 ^ n ∧ lcg x k % 2 ^ n = y % 2 ^ n := by
  induction n generalizing x y with
  | zero => exact ⟨0, by simp, by simp [Nat.mod_one]⟩
  | succ n ih =>
    obtain ⟨k, hk, he⟩ := ih x y
    have hP : 0 < 2 ^ n := Nat.pow_pos (by omega)
    have e : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [Nat.pow_succ]; omega
    generalize hPd : 2 ^ n = P at *
    generalize hz : lcg x k = z at *
    have hzd := Nat.div_add_mod z P
    have hyd := Nat.div_add_mod y P
    have hr : z % P < P := Nat.mod_lt _ hP
    have hz2 : z % (2 * P) = P * ((z / P) % 2) + z % P := by
      conv => lhs; rw [← hzd]
      exact mod_double P _ _ hr
    have hy2 : y % (2 * P) = P * ((y / P) % 2) + z % P := by
      conv => lhs; rw [← hyd, ← he]
      exact mod_double P _ _ hr
    rw [e]
    by_cases hpar : (z / P) % 2 = (y / P) % 2
    · exact ⟨k, by omega, by rw [hz, hz2, hy2, hpar]⟩
    · obtain ⟨w, hw⟩ := lcg_period n z
      rw [hPd] at hw
      refine ⟨k + P, by omega, ?_⟩
      rw [← hPd, lcg_add, hz, hPd, hw, hy2]
      have : z + P * (2 * w + 1) = P * (z / P + (2 * w + 1)) + z % P := by
        rw [Nat.mul_add P (z / P)]
        generalize P * (2 * w + 1) = X
        omega
      rw [this, mod_double P _ _ hr, parity_flip _ _ w hpar]

theorem probeState_succ (mask u n : Nat) :
    probeState mask u (n + 1) =
      probeStep mask (probeState mask u n).1 (probeState mask u n).2 := rfl

theorem probe_perturb (mask u k : Nat) : (probeState mask u k).2 = u >>> (5 * k) := by
  induction k with
  | zero => simp [probeState]
  | succ k ih =>
    rw [probeState_succ]
    simp only [probeStep, PERTURB_SHIFT, ih]
    rw [show 5 * (k + 1) = 5 * k + 5 by omega, Nat.shiftRight_add]

/-- A 64-bit `perturb` is 0 after 13 shifts (`dictobject.c:394-396`), and stays 0. -/
theorem probe_perturb_zero (mask u k : Nat) (hu : u < 2 ^ 64) (hk : 13 ≤ k) :
    (probeState mask u k).2 = 0 := by
  rw [probe_perturb, Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  calc u < 2 ^ 64 := hu
    _ ≤ 2 ^ (5 * k) := Nat.pow_le_pow_right (by omega) (by omega)

theorem and_mask (x n : Nat) : (2 ^ n - 1) &&& x = x % 2 ^ n := by
  rw [Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]

/-- Every probe position is in range. -/
theorem probe_lt (n u j : Nat) : (probeState (2 ^ n - 1) u j).1 < 2 ^ n := by
  have hp : 0 < 2 ^ n := Nat.pow_pos (by omega)
  cases j with
  | zero =>
    show u &&& (2 ^ n - 1) < 2 ^ n
    rw [Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ hp
  | succ j =>
    rw [probeState_succ]
    simp only [probeStep, and_mask]
    exact Nat.mod_lt _ hp

/-- Once `perturb` is 0, the slots follow `lcg`. -/
theorem probe_lcg (n u k : Nat) (hu : u < 2 ^ 64) :
    (probeState (2 ^ n - 1) u (13 + k)).1 = lcg (probeState (2 ^ n - 1) u 13).1 k % 2 ^ n := by
  induction k with
  | zero => simpa [lcg] using (Nat.mod_eq_of_lt (probe_lt n u 13)).symm
  | succ k ih =>
    have h0 := probe_perturb_zero (2 ^ n - 1) u (13 + k) hu (by omega)
    have e : 13 + (k + 1) = (13 + k) + 1 := by omega
    rw [e, probeState_succ]
    simp only [probeStep, and_mask, h0, PERTURB_SHIFT, Nat.zero_shiftRight, Nat.add_zero]
    rw [ih]
    simp only [lcg]
    generalize lcg _ k = a
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod, Nat.mul_comm a 5]

/-- Every slot lies on the probe sequence of every hash, within `2^n + 13` steps. This is the
termination argument at `dictobject.c:397-398`. -/
theorem probe_reaches_all (n u s : Nat) (hu : u < 2 ^ 64) (hs : s < 2 ^ n) :
    ∃ j, j < 2 ^ n + 13 ∧ (probeState (2 ^ n - 1) u j).1 = s := by
  obtain ⟨k, hk, he⟩ := lcg_full_period n (probeState (2 ^ n - 1) u 13).1 s
  refine ⟨13 + k, by omega, ?_⟩
  rw [probe_lcg n u k hu, he, Nat.mod_eq_of_lt hs]

/-- `(size_t)hash` fits 64 bits. -/
theorem toU64_lt (h : Int) : toU64 h < 2 ^ 64 := by
  unfold toU64
  have h1 : (0 : Int) ≤ h % (2 ^ 64 : Int) := Int.emod_nonneg _ (by decide)
  have h2 : h % (2 ^ 64 : Int) < (2 ^ 64 : Int) := Int.emod_lt_of_pos _ (by decide)
  omega

end PyLean.DictSet
