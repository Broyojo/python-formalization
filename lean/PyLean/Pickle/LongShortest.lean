import PyLean.Pickle.SaveLongProps

/-!
`encode_long` is a bijection between ints and their shortest two's-complement
encodings: with `decodeEncodeLong_proven`, the encoding is the unique shortest
byte string that decodes to the int.
-/

namespace PyLean.Pickle

open PyLean

theorem leNat_inj (a b : Bytes) (hl : a.length = b.length) (h : leNat a = leNat b) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons x a ih =>
    cases b with
    | nil => simp at hl
    | cons y b =>
      simp only [leNat] at h
      have hx := x.toNat_lt
      have hy := y.toNat_lt
      have e1 : x.toNat = y.toNat := by omega
      have e2 : leNat a = leNat b := by omega
      rw [UInt8.toNat_inj.mp e1, ih b (by simpa using hl) e2]

/-- The unsigned value is the signed value modulo `256^n`. -/
theorem leInt_mod (b : Bytes) : leInt b % ((256 ^ b.length : Nat) : Int) = (leNat b : Int) := by
  have hlt := leNat_lt b
  have hpos : (0 : Int) < ((256 ^ b.length : Nat) : Int) := by
    have : 0 < 256 ^ b.length := Nat.pow_pos (by omega)
    omega
  have hp : (2 : Int) ^ (8 * b.length) = ((256 ^ b.length : Nat) : Int) := two_pow_8 _
  unfold leInt
  split
  · rw [hp]
    have h1 : (leNat b : Int) - ((256 ^ b.length : Nat) : Int) + ((256 ^ b.length : Nat) : Int) = leNat b := by
      omega
    rw [Int.emod_eq_add_self_emod, h1]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · exact Int.emod_eq_of_lt (by omega) (by omega)

theorem leInt_inj (a b : Bytes) (hl : a.length = b.length) (h : leInt a = leInt b) : a = b := by
  have e1 := leInt_mod a
  have e2 := leInt_mod b
  rw [h, hl, e2] at e1
  exact leNat_inj a b hl (by omega)

/-- Bounds of the signed value. -/
theorem leInt_bounds (b : Bytes) (hb : b ≠ []) :
    -((2 : Int) ^ (8 * b.length - 1)) ≤ leInt b ∧ leInt b < (2 : Int) ^ (8 * b.length - 1) := by
  have hlt := leNat_lt b
  have hk : b.length ≠ 0 := by simpa using hb
  obtain ⟨k, hk'⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by omega⟩
  have h1 := two_pow_8m1 k
  have h2 : (256 : Nat) ^ (k + 1) = 256 * 256 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
  have h3 : (2 : Int) ^ (8 * (k + 1)) = ((256 ^ (k + 1) : Nat) : Int) := two_pow_8 _
  have h4 : (2 : Int) ^ (8 * (k + 1) - 1) = ((2 ^ (8 * (k + 1) - 1) : Nat) : Int) := by simp
  unfold leInt
  rw [hk'] at hlt ⊢
  rw [h4, h1]
  rw [h3, h2]
  rw [h2] at hlt
  split
  · rename_i hc
    obtain ⟨_, hc⟩ := hc
    omega
  · rename_i hc
    have : ¬ (leNat b ≥ 128 * 256 ^ k) := by
      intro hge
      apply hc
      exact ⟨hb, hge⟩
    omega

theorem leBytes_shift (c j : Nat) (n : Nat) :
    leBytes (c * 256 ^ j) (j + n) = List.replicate j 0 ++ leBytes c n := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
    rw [show j + 1 + n = (j + n) + 1 by omega]
    simp only [leBytes]
    have e1 : c * 256 ^ (j + 1) % 256 = 0 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    have e2 : c * 256 ^ (j + 1) / 256 = c * 256 ^ j := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]; omega
    rw [e1, e2, ih c, List.replicate_succ]
    rfl

/-- `encode_long(-(2**(8*(j+1) - 1)))` drops the sign byte. -/
theorem encodeLong_extreme (j : Nat) (hbl : bitLength (2 ^ (8 * (j + 1) - 1)) = 8 * (j + 1)) :
    (encodeLong (-((2 : Int) ^ (8 * (j + 1) - 1)))).length = j + 1 := by
  have hp1 : (2 : Nat) ^ (8 * (j + 1) - 1) = 128 * 256 ^ j := two_pow_8m1 j
  have hP : 0 < 256 ^ j := Nat.pow_pos (by omega)
  have hcast : (2 : Int) ^ (8 * (j + 1) - 1) = ((128 * 256 ^ j : Nat) : Int) := by
    rw [← hp1]; simp
  have hM : (2 : Int) ^ (8 * (j + 2)) = ((65536 * 256 ^ j : Nat) : Int) := by
    rw [two_pow_8, show j + 2 = j + 1 + 1 by omega, Nat.pow_succ, Nat.pow_succ]
    congr 1
    omega
  have hne : -((2 : Int) ^ (8 * (j + 1) - 1)) ≠ 0 := by rw [hcast]; omega
  have hneg : -((2 : Int) ^ (8 * (j + 1) - 1)) < 0 := by rw [hcast]; omega
  have hab : (-((2 : Int) ^ (8 * (j + 1) - 1))).natAbs = 2 ^ (8 * (j + 1) - 1) := by
    rw [Int.natAbs_neg, Int.natAbs_pow]; rfl
  have hn : bitLength (-((2 : Int) ^ (8 * (j + 1) - 1))).natAbs / 8 + 1 = j + 2 := by
    rw [hab, hbl]; omega
  have hres : toBytesSigned (-((2 : Int) ^ (8 * (j + 1) - 1))) (j + 2) =
      List.replicate j 0 ++ [128, 255] := by
    unfold toBytesSigned
    rw [hM, hcast]
    have hm : (-((128 * 256 ^ j : Nat) : Int)) % ((65536 * 256 ^ j : Nat) : Int) =
        ((65408 * 256 ^ j : Nat) : Int) := by
      have h1 : (((65408 * 256 ^ j : Nat) : Int)) % ((65536 * 256 ^ j : Nat) : Int) =
          ((65408 * 256 ^ j : Nat) : Int) := Int.emod_eq_of_lt (by omega) (by omega)
      rw [← h1]
      have : ((65408 * 256 ^ j : Nat) : Int) = -((128 * 256 ^ j : Nat) : Int) + ((65536 * 256 ^ j : Nat) : Int) := by
        omega
      rw [this, ← Int.emod_eq_add_self_emod]
    rw [hm, Int.toNat_natCast, leBytes_shift]
    rfl
  unfold encodeLong
  rw [if_neg hne]
  dsimp only
  rw [hn, hres]
  have hlast : (List.replicate j (0 : UInt8) ++ [(128 : UInt8), 255]).getLast? = some 255 := by simp
  have hget : (List.replicate j (0 : UInt8) ++ [(128 : UInt8), 255]).getD (j + 2 - 2) 0 = 128 := by
    simp [List.getD_eq_getElem?_getD]
  rw [if_pos ⟨hneg, by omega⟩, if_pos ⟨hlast, by rw [hget]; decide⟩]
  simp

/-- `encode_long(x)` is the unique shortest byte string that `decode_long`
maps to `x`: every other one is longer, including for the sign-trimmed
`-(2**(8*j - 1))`. With `decode_long(encode_long(x)) == x` this makes
`encode_long` a bijection onto the shortest encodings. -/
def EncodeLongShortest : Prop :=
  ∀ (x : Int) (b : Bytes), decodeLong b = x → b.length ≤ (encodeLong x).length → b = encodeLong x

theorem encodeLongShortest_proven : EncodeLongShortest := by
  intro x b hb hle
  have hrt := decodeEncodeLong_proven x
  have hlen : (encodeLong x).length ≤ b.length := by
    by_cases hnil : b = []
    · subst hnil
      have hx : x = 0 := by rw [← hb]; simp [decodeLong, leInt, leNat]
      subst hx
      simp [encodeLong]
    obtain ⟨k, hk⟩ : ∃ k, b.length = k + 1 := ⟨b.length - 1, by
      have : b.length ≠ 0 := by simpa using hnil
      omega⟩
    have hbd := leInt_bounds b hnil
    rw [show leInt b = x from hb, hk] at hbd
    have hbl := lt_two_pow_bitLength x.natAbs
    by_cases hn : bitLength x.natAbs / 8 + 1 ≤ k + 1
    · have := encodeLong_length_le x
      omega
    · -- `x` needs the full width: it is -(2**(8*(k+1)-1))
      have hx0 : x ≠ 0 := by
        intro h0; subst h0; simp [bitLength] at hn
      have hl2 : 8 * (k + 1) ≤ bitLength x.natAbs := by omega
      have hge : 2 ^ (8 * (k + 1) - 1) ≤ x.natAbs := by
        have hne : x.natAbs ≠ 0 := by omega
        have h1 := Nat.log2_self_le hne
        have h2 : bitLength x.natAbs = Nat.log2 x.natAbs + 1 := by simp [bitLength, hne]
        exact Nat.le_trans (Nat.pow_le_pow_right (by omega) (by omega)) h1
      have hcast : (2 : Int) ^ (8 * (k + 1) - 1) = ((2 ^ (8 * (k + 1) - 1) : Nat) : Int) := by simp
      rw [hcast] at hbd
      have hxv : x = -((2 : Int) ^ (8 * (k + 1) - 1)) := by rw [hcast]; omega
      have hbl2 : bitLength (2 ^ (8 * (k + 1) - 1)) = 8 * (k + 1) := by
        rw [bitLength_two_pow]; omega
      rw [hxv, encodeLong_extreme k hbl2]
      omega
  exact leInt_inj b (encodeLong x) (by omega) (by
    show decodeLong b = decodeLong (encodeLong x)
    rw [hb, hrt])

end PyLean.Pickle
