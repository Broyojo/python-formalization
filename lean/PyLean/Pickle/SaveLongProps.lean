import PyLean.Pickle.LongProps

/-! ## C `save_long` vs Python `save_long` -/

namespace PyLean.Pickle

open PyLean

theorem int_two_pow_le {a b : Nat} (h : a ≤ b) : (2:Int) ^ a ≤ 2 ^ b := by
  have := Nat.pow_le_pow_right (show 0 < 2 by omega) h
  have e1 : ((2 ^ a : Nat) : Int) = (2 : Int) ^ a := by simp
  have e2 : ((2 ^ b : Nat) : Int) = (2 : Int) ^ b := by simp
  omega

theorem pySaveLong_not_overflow (p : Nat) (x : Int) (m : String) :
    pySaveLong p x ≠ .error (.overflowError m) := by
  unfold pySaveLong
  intro h
  dsimp only at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · split at h
    · simp at h
    · unfold packI32 at h
      split at h <;> simp [bind, Except.bind, structError] at h
  split at h
  · simp at h
  · unfold reprInt at h
    split at h <;> simp [bind, Except.bind, structError] at h

/-- `pickle.dumps(x)` and `pickle._dumps(x)` encode every int identically
(protocols 0-5). Source: twin agreement; `save_long` at `Lib/pickle.py:822-851`
and `Modules/_pickle.c:2338-2501`. -/
def SaveLongTwinsAgree : Prop :=
  ∀ (proto : Nat) (x : Int), proto ≤ 5 → cSaveLong proto x = pySaveLong proto x

/-- The C pickler checks the untrimmed byte count `nbits / 8 + 1` against
`0x7fffffff`, so it refuses `-(2 ** (8 * (2**31 - 1) - 1))`, whose
two's-complement encoding is `2**31 - 1` bytes after trimming; the Python
pickler encodes it. -/
theorem cSaveLong_neg_two_pow (K : Nat) (hK1 : 32 ≤ K) (hK2 : (K + 1) / 8 + 1 > 0x7fffffff) :
    cSaveLong 2 (-(2 ^ K)) = .error (.overflowError "int too large to pickle") := by
  have hnat : (-(2 : Int) ^ K).natAbs = 2 ^ K := by
    rw [Int.natAbs_neg, Int.natAbs_pow]; rfl
  have hbig : (2 : Int) ^ 32 ≤ 2 ^ K := int_two_pow_le (by omega)
  unfold cSaveLong cLongBytes
  rw [if_neg (by omega), if_pos (by omega)]
  simp only [hnat, bitLength_two_pow]
  rw [if_pos (by omega)]
  rfl

theorem saveLongTwinsAgree_refuted : ¬ SaveLongTwinsAgree := by
  intro h
  have hk := h 2 (-(2 ^ 17179869175)) (by omega)
  rw [cSaveLong_neg_two_pow 17179869175 (by omega) (by omega)] at hk
  exact pySaveLong_not_overflow 2 _ _ hk.symm

theorem leBytes_four (m : Nat) : leBytes m 4 =
    [(m % 256).toUInt8, (m / 256 % 256).toUInt8, (m / 65536 % 256).toUInt8, (m / 16777216 % 256).toUInt8] := by
  simp [leBytes, Nat.div_div_eq_div_mul]

theorem toUInt8_eq_zero (n : Nat) : n.toUInt8 = 0 ↔ n % 256 = 0 := by
  constructor
  · intro h; have := congrArg UInt8.toNat h; simpa using this
  · intro h; apply UInt8.toNat_inj.mp; simp [h]

theorem toBytesSigned_four (x : Int) (h1 : -0x80000000 ≤ x) (h2 : x ≤ 0x7fffffff) :
    toBytesSigned x 4 = leBytes (if 0 ≤ x then x.toNat else (x + 4294967296).toNat) 4 := by
  unfold toBytesSigned
  have hp : (2:Int) ^ (8 * 4) = 4294967296 := by rfl
  rw [hp]
  congr 1
  split
  · rw [Int.emod_eq_of_lt (by omega) (by omega)]
  · have h3 : (x + 4294967296) % 4294967296 = x + 4294967296 := Int.emod_eq_of_lt (by omega) (by omega)
    rw [← h3, ← Int.emod_eq_add_self_emod]

theorem small_case (proto : Nat) (x : Int) (h32 : -0x80000000 ≤ x ∧ x ≤ 0x7fffffff) :
    cSaveLong proto x = pySaveLong proto x := by
  unfold cSaveLong pySaveLong
  dsimp only
  rw [if_pos h32]
  by_cases hb : proto ≥ 1
  · rw [if_pos hb, toBytesSigned_four x h32.1 h32.2]
    by_cases hx0 : 0 ≤ x
    · rw [if_pos hx0, leBytes_four]
      by_cases hA : x ≤ 0xff
      · have e1 : x.toNat / 256 % 256 = 0 := by omega
        have e2 : x.toNat / 65536 % 256 = 0 := by omega
        have e3 : x.toNat / 16777216 % 256 = 0 := by omega
        simp [e1, e2, e3, hb, hx0, hA, leBytes]
      · by_cases hB : x ≤ 0xffff
        · have e1 : x.toNat / 256 % 256 ≠ 0 := by omega
          have e2 : x.toNat / 65536 % 256 = 0 := by omega
          have e3 : x.toNat / 16777216 % 256 = 0 := by omega
          simp [e1, e2, e3, hb, hx0, hA, hB, leBytes, toUInt8_eq_zero]
        · have hpy1 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 255) := by omega
          have hpy2 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 65535) := by omega
          have hpy3 : proto ≥ 1 ∧ -2147483648 ≤ x ∧ x ≤ 2147483647 := ⟨hb, h32⟩
          rw [if_neg hpy1, if_neg hpy2, if_pos hpy3]
          have : ((x.toNat / 16777216 % 256).toUInt8 ≠ 0 ∨ (x.toNat / 65536 % 256).toUInt8 ≠ 0) := by
            simp only [ne_eq, toUInt8_eq_zero]; omega
          simp [this]
    · rw [if_neg hx0, leBytes_four]
      have hpy1 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 255) := by omega
      have hpy2 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 65535) := by omega
      have hpy3 : proto ≥ 1 ∧ -2147483648 ≤ x ∧ x ≤ 2147483647 := ⟨hb, h32⟩
      rw [if_neg hpy1, if_neg hpy2, if_pos hpy3]
      have : ((x + 4294967296).toNat / 16777216 % 256).toUInt8 ≠ 0 := by
        simp only [ne_eq, toUInt8_eq_zero]; omega
      simp [this]
  · rw [if_neg hb]
    have hpy1 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 255) := by omega
    have hpy2 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 65535) := by omega
    have hpy3 : ¬ (proto ≥ 1 ∧ -0x80000000 ≤ x ∧ x ≤ 0x7fffffff) := by omega
    have hp2 : ¬ proto ≥ 2 := by omega
    rw [if_neg hpy1, if_neg hpy2, if_neg hpy3, if_neg hp2, if_pos h32]

theorem cLongBytes_eq (x : Int) (hx : x ≠ 0) (hsz : bitLength x.natAbs / 8 + 1 ≤ 0x7fffffff) :
    cLongBytes x = .ok (encodeLong x) := by
  unfold cLongBytes encodeLong
  dsimp only
  rw [if_neg (by omega), if_neg hx]
  generalize hn : bitLength x.natAbs / 8 + 1 = n at *
  have hlen : (toBytesSigned x n).length = n := leBytes_length _ _
  generalize toBytesSigned x n = r at *
  have hn1 : 1 ≤ n := by omega
  have hlast : (r.getLast? = some 0xff) ↔ (r.getD (n - 1) 0 = 0xff) := by
    rw [List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, hlen]
    have : n - 1 < r.length := by omega
    rw [List.getElem?_eq_getElem this]; simp
  have htake : r.take (n - 1) = r.dropLast := by rw [List.dropLast_eq_take, hlen]
  by_cases hc : x < 0 ∧ n > 1
  · rw [if_pos hc]
    by_cases hd : r.getD (n - 1) 0 = 0xff ∧ (r.getD (n - 2) 0 &&& 0x80) ≠ 0
    · rw [if_pos ⟨hc.1, hc.2, hd⟩, if_pos ⟨hlast.mpr hd.1, hd.2⟩, htake]
    · rw [if_neg (fun h => hd ⟨h.2.2.1, h.2.2.2⟩), if_neg (fun h => hd ⟨hlast.mp h.1, h.2⟩)]
  · rw [if_neg hc, if_neg (fun h => hc ⟨h.1, h.2.1⟩)]

theorem encodeLong_length_le (x : Int) : (encodeLong x).length ≤ bitLength x.natAbs / 8 + 1 := by
  unfold encodeLong
  dsimp only
  split
  · simp
  · have := leBytes_length ((x % (2 : Int) ^ (8 * (bitLength x.natAbs / 8 + 1))).toNat) (bitLength x.natAbs / 8 + 1)
    unfold toBytesSigned
    split
    · split <;> simp [this]
    · simp [this]

theorem big_case (proto : Nat) (x : Int) (h32 : ¬(-0x80000000 ≤ x ∧ x ≤ 0x7fffffff))
    (hsz : bitLength x.natAbs / 8 + 1 ≤ 0x7fffffff) : cSaveLong proto x = pySaveLong proto x := by
  unfold cSaveLong pySaveLong
  dsimp only
  rw [if_neg h32]
  have hpy1 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 255) := by omega
  have hpy2 : ¬ (proto ≥ 1 ∧ x ≥ 0 ∧ x ≤ 65535) := by omega
  have hpy3 : ¬ (proto ≥ 1 ∧ -0x80000000 ≤ x ∧ x ≤ 0x7fffffff) := by omega
  rw [if_neg hpy1, if_neg hpy2, if_neg hpy3]
  by_cases hp2 : proto ≥ 2
  · rw [if_pos hp2, if_pos hp2, cLongBytes_eq x (by omega) hsz]
    have hlen := encodeLong_length_le x
    simp only [bind, Except.bind]
    split
    · rfl
    · unfold packI32
      rw [if_pos (by omega)]
      simp only [Except.ok.injEq, List.cons.injEq, List.append_cancel_right_eq, true_and]
      unfold toBytesSigned
      congr 1
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp
  · rw [if_neg hp2, if_neg hp2, if_neg h32]

/-- `SaveLongTwinsAgree` restricted to ints whose C byte count
`bit_length / 8 + 1` is at most `0x7fffffff` (the C check that the refutation
trips; every int below 2**(2**34 - 8) in absolute value qualifies). Covers the
choice among BININT1/BININT2/BININT/LONG1/LONG4/INT/LONG at every boundary. -/
def SaveLongTwinsAgreeSized : Prop :=
  ∀ (proto : Nat) (x : Int), proto ≤ 5 → bitLength x.natAbs / 8 + 1 ≤ 0x7fffffff →
    cSaveLong proto x = pySaveLong proto x

theorem saveLongTwinsAgreeSized_proven : SaveLongTwinsAgreeSized := by
  intro proto x _ hsz
  by_cases h32 : -0x80000000 ≤ x ∧ x ≤ 0x7fffffff
  · exact small_case proto x h32
  · exact big_case proto x h32 hsz

end PyLean.Pickle
