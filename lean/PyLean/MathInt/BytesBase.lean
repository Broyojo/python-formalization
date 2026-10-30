import PyLean.MathInt.IntOps

/-!
Arithmetic vocabulary for `int.to_bytes` / `int.from_bytes`: the value of a
little-endian byte list, and bit-twiddling facts about `|||`, `^^^` used by
`_PyLong_AsByteArray` / `_PyLong_FromByteArray`.
-/

namespace PyLean.MathInt

open PyLean

/-- Unsigned value of a little-endian list of bytes. -/
def bytesVal : List Nat → Nat
  | [] => 0
  | b :: bs => b + 256 * bytesVal bs

def AllBytes (bs : List Nat) : Prop := ∀ b ∈ bs, b < 256

theorem bytesVal_append (xs ys : List Nat) :
    bytesVal (xs ++ ys) = bytesVal xs + 256 ^ xs.length * bytesVal ys := by
  induction xs with
  | nil => simp [bytesVal]
  | cons x xs ih =>
    simp only [List.cons_append, bytesVal, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm (256 ^ xs.length) 256, Nat.mul_assoc]

theorem bytesVal_lt (bs : List Nat) (h : AllBytes bs) : bytesVal bs < 256 ^ bs.length := by
  induction bs with
  | nil => simp [bytesVal]
  | cons b bs ih =>
    have hb := h b (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [bytesVal, List.length_cons, Nat.pow_succ]
    have : 256 * bytesVal bs ≤ 256 * (256 ^ bs.length - 1) := Nat.mul_le_mul_left _ (by omega)
    have : 256 * (256 ^ bs.length - 1) = 256 ^ bs.length * 256 - 256 := by
      rw [Nat.mul_sub, Nat.mul_one, Nat.mul_comm]
    have : 256 ≤ 256 ^ bs.length * 256 := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by decide))
    omega

theorem bytesVal_replicate_zero (i : Nat) : bytesVal (List.replicate i 0) = 0 := by
  induction i with
  | zero => rfl
  | succ i ih => simp [List.replicate_succ, bytesVal, ih]

theorem bytesVal_replicate_255 (i : Nat) : bytesVal (List.replicate i 255) + 1 = 256 ^ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    simp only [List.replicate_succ, bytesVal, Nat.pow_succ]
    omega

/-- Disjoint bits add. -/
theorem or_eq_add_of_and_eq_zero : ∀ x y : Nat, x &&& y = 0 → x ||| y = x + y := by
  intro x
  induction x using Nat.strongRecOn with
  | _ x ih =>
    intro y h
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx; simp
    have h1 : x / 2 &&& y / 2 = 0 := by rw [← Nat.and_div_two, h]
    have h2 : ¬ (x % 2 = 1 ∧ y % 2 = 1) := fun h' => by
      have := Nat.and_mod_two_eq_one.mpr h'; rw [h] at this; simp at this
    have e := ih (x / 2) (by omega) (y / 2) h1
    have d1 := Nat.div_add_mod (x ||| y) 2
    rw [Nat.or_div_two, e] at d1
    have m : (x ||| y) % 2 = x % 2 + y % 2 := by
      rcases Nat.mod_two_eq_zero_or_one x with a | a <;>
      rcases Nat.mod_two_eq_zero_or_one y with b | b
      · have : ¬ ((x ||| y) % 2 = 1) := fun h' => by
          have := (@Nat.or_mod_two_eq_one x y).mp h'; omega
        omega
      · have := (@Nat.or_mod_two_eq_one x y).mpr (by omega); omega
      · have := (@Nat.or_mod_two_eq_one x y).mpr (by omega); omega
      · exact absurd ⟨a, b⟩ h2
    omega

theorem or_shift_eq_add (x y k : Nat) (h : x < 2 ^ k) : x ||| (y <<< k) = x + y * 2 ^ k := by
  rw [Nat.shiftLeft_eq]
  apply or_eq_add_of_and_eq_zero
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i < k
  · have : (y * 2 ^ k).testBit i = false := by
      rw [Nat.mul_comm]
      have := Nat.testBit_two_pow_mul_add y (show 0 < 2 ^ k from Nat.two_pow_pos k) (j := i)
      simp only [Nat.add_zero] at this; rw [this]; simp [hi]
    simp [this]
  · have : x.testBit i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

/-- Complementing a `k`-bit number. -/
theorem xor_mask (k : Nat) : ∀ b, b < 2 ^ k → (2 ^ k - 1) ^^^ b = 2 ^ k - 1 - b := by
  induction k with
  | zero => intro b h; have : b = 0 := by simp at h; omega
            subst this; rfl
  | succ k ih =>
    intro b h
    have hb2 : b / 2 < 2 ^ k := by rw [Nat.pow_succ] at h; omega
    have e := ih (b / 2) hb2
    have d := Nat.div_add_mod ((2 ^ (k + 1) - 1) ^^^ b) 2
    rw [Nat.xor_div_two, show (2 ^ (k + 1) - 1) / 2 = 2 ^ k - 1 by rw [Nat.pow_succ]; omega, e] at d
    have hm : ((2 ^ (k + 1) - 1) ^^^ b) % 2 = 1 - b % 2 := by
      have h1 : (2 ^ (k + 1) - 1) % 2 = 1 := by
        rw [Nat.pow_succ]; have := Nat.two_pow_pos k; omega
      rcases Nat.mod_two_eq_zero_or_one b with a | a
      · have := (@Nat.xor_mod_two_eq_one (2 ^ (k + 1) - 1) b).mpr (by omega); omega
      · have : ¬ (((2 ^ (k + 1) - 1) ^^^ b) % 2 = 1) := fun h' => by
          have := (@Nat.xor_mod_two_eq_one (2 ^ (k + 1) - 1) b).mp h'; omega
        omega
    have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have := Nat.two_pow_pos k
    omega

theorem and_mask_eq_mod (x k : Nat) : x &&& (2 ^ k - 1) = x % 2 ^ k := Nat.and_two_pow_sub_one_eq_mod x k

end PyLean.MathInt
