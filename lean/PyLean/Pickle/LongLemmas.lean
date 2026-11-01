import PyLean.Pickle.Long

/-! Lemmas about the little-endian and two's-complement helpers. -/

namespace PyLean.Pickle

open PyLean

theorem leBytes_length (m k : Nat) : (leBytes m k).length = k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp [leBytes, ih]

theorem leNat_leBytes (m k : Nat) : leNat (leBytes m k) = m % 256 ^ k := by
  induction k generalizing m with
  | zero => simp [leBytes, leNat]; omega
  | succ k ih =>
    simp only [leBytes, leNat, ih]
    have h1 : ((m % 256).toUInt8).toNat = m % 256 := by
      simp [Nat.toUInt8]
    rw [h1, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]

theorem leNat_lt (bs : Bytes) : leNat bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := b.toNat_lt
    have : 256 * leNat bs ≤ 256 * (256 ^ bs.length - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 256 ^ bs.length ≥ 1 := Nat.pow_pos (by omega)
    rw [Nat.mul_comm (256 ^ bs.length)]
    rw [Nat.mul_sub, Nat.mul_one] at *
    omega

theorem leNat_append_single (l : Bytes) (c : UInt8) :
    leNat (l ++ [c]) = leNat l + c.toNat * 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b l ih =>
    simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add]
    have : 256 * (c.toNat * 256 ^ l.length) = c.toNat * (256 ^ l.length * 256) := by
      rw [Nat.mul_comm 256, Nat.mul_assoc]
    omega

/-- `toBytesSigned x n` decodes back to `x` when `x` fits in `n` signed bytes. -/
theorem leInt_toBytesSigned (x : Int) (n : Nat) (hn : 0 < n)
    (hlo : -(2 : Int) ^ (8 * n - 1) ≤ x) (hhi : x < (2 : Int) ^ (8 * n - 1)) :
    leInt (toBytesSigned x n) = x := by
  have hpow : (2 : Int) ^ (8 * n) = 2 * 2 ^ (8 * n - 1) := by
    rw [← Int.pow_succ']; congr 1; omega
  have hpos : (0 : Int) < 2 ^ (8 * n - 1) := Int.pow_pos (by omega)
  have hm0 : 0 ≤ x % (2 : Int) ^ (8 * n) := Int.emod_nonneg _ (by omega)
  have hm1 : x % (2 : Int) ^ (8 * n) < (2 : Int) ^ (8 * n) := Int.emod_lt_of_pos _ (by omega)
  have h256 : (256 : Nat) ^ n = 2 ^ (8 * n) := by
    rw [show (256 : Nat) = 2 ^ 8 by rfl, ← Nat.pow_mul]
  unfold leInt toBytesSigned
  rw [leNat_leBytes, leBytes_length]
  have hcast : (((2 : Nat) ^ (8 * n - 1) : Nat) : Int) = (2 : Int) ^ (8 * n - 1) := by simp
  have hcast2 : (((2 : Nat) ^ (8 * n) : Nat) : Int) = (2 : Int) ^ (8 * n) := by simp
  have hlt : (x % (2 : Int) ^ (8 * n)).toNat < 256 ^ n := by
    rw [h256]; omega
  rw [Nat.mod_eq_of_lt hlt]
  have hne : ∀ m, leBytes m n ≠ [] := by
    intro m h; have := congrArg List.length h; simp [leBytes_length] at this; omega
  by_cases hx : 0 ≤ x
  · have hm : x % (2 : Int) ^ (8 * n) = x := Int.emod_eq_of_lt hx (by omega)
    rw [hm]
    have : ¬ (x.toNat ≥ 2 ^ (8 * n - 1)) := by omega
    simp [hne, this]; omega
  · have hm : x % (2 : Int) ^ (8 * n) = x + 2 ^ (8 * n) := by
      have h1 : (x + (2 : Int) ^ (8 * n)) % 2 ^ (8 * n) = x + 2 ^ (8 * n) :=
        Int.emod_eq_of_lt (by omega) (by omega)
      rw [← h1, ← Int.emod_eq_add_self_emod]
    rw [hm]
    have : (x + (2 : Int) ^ (8 * n)).toNat ≥ 2 ^ (8 * n - 1) := by omega
    simp [hne, this]; omega

end PyLean.Pickle
