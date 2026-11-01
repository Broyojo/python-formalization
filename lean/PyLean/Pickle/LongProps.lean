import PyLean.Pickle.LongLemmas

/-!
Properties of the integer encodings.
-/

namespace PyLean.Pickle

open PyLean

theorem lt_two_pow_bitLength (n : Nat) : n < 2 ^ bitLength n := by
  unfold bitLength; split
  · omega
  · exact Nat.lt_log2_self

theorem bitLength_two_pow (k : Nat) : bitLength (2 ^ k) = k + 1 := by
  unfold bitLength; simp [Nat.log2_two_pow]

set_option maxRecDepth 20000 in
theorem high_bit_ge : ∀ n < 256, (n &&& 128 ≠ 0) → 128 ≤ n := by decide

theorem uint8_high_bit {d : UInt8} (h : (d &&& 0x80) ≠ 0) : 128 ≤ d.toNat := by
  apply high_bit_ge _ d.toNat_lt
  intro h0; apply h
  apply UInt8.toNat_inj.mp
  simp [UInt8.toNat_and, h0]

theorem two_pow_8 (k : Nat) : (2 : Int) ^ (8 * k) = ((256 ^ k : Nat) : Int) := by
  rw [Int.pow_mul, Int.natCast_pow]; rfl

theorem two_pow_8m1 (k : Nat) : (2 : Nat) ^ (8 * (k + 1) - 1) = 128 * 256 ^ k := by
  rw [show 8 * (k + 1) - 1 = 7 + 8 * k by omega, Nat.pow_add, Nat.pow_mul]

/-- Dropping a redundant sign byte keeps the signed value. -/
theorem leInt_trim (l : Bytes) (d : UInt8) (hd : 128 ≤ d.toNat) :
    leInt (l ++ [d] ++ [0xff]) = leInt (l ++ [d]) := by
  have e1 := leNat_append_single (l ++ [d]) 0xff
  have e2 := leNat_append_single l d
  have h255 : (0xff : UInt8).toNat = 255 := rfl
  simp only [List.length_append, List.length_cons, List.length_nil, h255] at e1
  rw [e2] at e1
  generalize hL : leNat l = L at *
  generalize hn : l.length = n at *
  have hP : (256 : Nat) ^ (n + 1) = 256 * 256 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
  generalize hPP : (256 : Nat) ^ n = P at *
  have hlen1 : (l ++ [d]).length = n + 1 := by simp [hn]
  have hlen2 : (l ++ [d] ++ [(0xff : UInt8)]).length = n + 1 + 1 := by simp [hn]
  unfold leInt
  rw [hlen1, hlen2, e1, e2, two_pow_8m1, two_pow_8m1, two_pow_8, two_pow_8]
  have hP2 : (256 : Nat) ^ (n + 1 + 1) = 256 * (256 * P) := by rw [Nat.pow_succ, hP]; omega
  rw [hP2, hP]
  have c1 : (l ++ [d] ++ [(0xff : UInt8)]) ≠ [] := by simp
  have c2 : (l ++ [d]) ≠ [] := by simp
  have hdP : 128 * P ≤ d.toNat * P := Nat.mul_le_mul_right _ hd
  rw [if_pos ⟨c1, by omega⟩, if_pos ⟨c2, by omega⟩]
  omega

/-- `decode_long(encode_long(x)) == x` for every int (`Lib/pickle.py:372-420`). -/
def DecodeEncodeLong : Prop := ∀ x : Int, decodeLong (encodeLong x) = x

theorem decodeEncodeLong_proven : DecodeEncodeLong := by
  intro x
  unfold decodeLong encodeLong
  by_cases hx : x = 0
  · simp [hx, leInt, leNat]
  simp only [hx, ite_false]
  generalize hn : bitLength x.natAbs / 8 + 1 = n
  have hlt := lt_two_pow_bitLength x.natAbs
  have hb : bitLength x.natAbs ≤ 8 * n - 1 := by omega
  have hpow : 2 ^ bitLength x.natAbs ≤ 2 ^ (8 * n - 1) := Nat.pow_le_pow_right (by omega) hb
  have hn0 : 0 < n := by omega
  have hfit : leInt (toBytesSigned x n) = x := by
    apply leInt_toBytesSigned x n hn0
    · have : (x.natAbs : Int) < (2 : Int) ^ (8 * n - 1) := by exact_mod_cast (Nat.lt_of_lt_of_le hlt hpow)
      omega
    · have : (x.natAbs : Int) < (2 : Int) ^ (8 * n - 1) := by exact_mod_cast (Nat.lt_of_lt_of_le hlt hpow)
      omega
  split
  · split
    · rename_i h1 h2
      obtain ⟨hlast, hbit⟩ := h2
      have hlen : (toBytesSigned x n).length = n := leBytes_length _ _
      generalize hr : toBytesSigned x n = r at *
      -- r = l ++ [d] ++ [0xff]
      obtain ⟨r1, c, hr1⟩ : ∃ r1 c, r = r1 ++ [c] := ⟨r.dropLast, r.getLast (by intro h; simp [h] at hlen; omega),
        (List.dropLast_concat_getLast _).symm⟩
      subst hr1
      have hc : c = 0xff := by simpa using hlast
      subst hc
      have hlen1 : r1.length = n - 1 := by simp at hlen; omega
      obtain ⟨l, d, hl⟩ : ∃ l d, r1 = l ++ [d] := ⟨r1.dropLast, r1.getLast (by intro h; simp [h] at hlen1; omega),
        (List.dropLast_concat_getLast _).symm⟩
      subst hl
      have hidx : (l ++ [d] ++ [(0xff : UInt8)]).getD (n - 2) 0 = d := by
        simp at hlen1
        rw [show n - 2 = l.length by omega]
        simp
      rw [hidx] at hbit
      simp only [List.dropLast_concat]
      rw [← hfit, leInt_trim l d (uint8_high_bit hbit)]
    · exact hfit
  · exact hfit

end PyLean.Pickle
