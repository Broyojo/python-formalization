import PyLean.Sequences.FloatBits

/-!
`array.array` items of the typecodes `e`, `f`, `d`, `Zf` and `Zd` (`Modules/arraymodule.c`,
CPython 3.15.2): the argument conversion of their setitems, the round trip of every stored bit
pattern through getitem and setitem, and the comparison of `e` and `f` with the `struct`
packing of the same value.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.deprecated false

/-! #### `(float)(double)y` for every binary32 pattern `y` -/

theorem bitLength_bounds (f : Nat) (h0 : f ≠ 0) :
    2 ^ (bitLength f - 1) ≤ f ∧ f < 2 ^ bitLength f ∧ 1 ≤ bitLength f := by
  unfold bitLength
  rw [if_neg h0]
  refine ⟨?_, Nat.lt_log2_self, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact Nat.log2_self_le h0

theorem bitLength_le (f k : Nat) (h0 : f ≠ 0) (h : f < 2 ^ k) : bitLength f ≤ k := by
  unfold bitLength
  rw [if_neg h0]
  have := (Nat.log2_lt h0).2 h
  omega

theorem fTrip_nan_mag (f : Nat) (hf : f < 8388608) (hf0 : f ≠ 0) :
    f2dMag 255 f = 2047 * 4503599627370496 + (4194304 + f % 4194304) * 536870912 := by
  have hor := or22 f hf
  unfold f2dMag
  rw [if_pos rfl, if_neg hf0, hor]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]

theorem fTrip_nan (f : Nat) :
    d2fMag ((2047 * 4503599627370496 + (4194304 + f % 4194304) * 536870912) >>> 52)
      ((2047 * 4503599627370496 + (4194304 + f % 4194304) * 536870912) % two52) = 2143289344 + f % 4194304 := by
  have h1 : (2047 * 4503599627370496 + (4194304 + f % 4194304) * 536870912) >>> 52 = 2047 := by
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]; omega
  have h2 : (2047 * 4503599627370496 + (4194304 + f % 4194304) * 536870912) % two52 =
      (4194304 + f % 4194304) * 536870912 := by unfold two52; omega
  have h3 : ((4194304 + f % 4194304) * 536870912) >>> 29 = 4194304 + f % 4194304 := by
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]
    exact Nat.mul_div_cancel _ (by decide)
  rw [h1, h2]
  unfold d2fMag
  rw [if_pos rfl, if_neg (by omega), h3]
  omega

theorem fTrip_sub_mag (f : Nat) (hf : f < 8388608) (hf0 : f ≠ 0) :
    ∃ L M, f2dMag 0 f = (L + 873) * 4503599627370496 + (M - 4503599627370496) ∧
      1 ≤ L ∧ L ≤ 23 ∧ 4503599627370496 ≤ M ∧ M < 9007199254740992 ∧ M = f * 2 ^ (53 - L) := by
  obtain ⟨hlo, hhi, hL1⟩ := bitLength_bounds f hf0
  have hL : bitLength f ≤ 23 := bitLength_le f 23 hf0 (by simp only [Nat.reducePow]; omega)
  refine ⟨bitLength f, f * 2 ^ (53 - bitLength f), ?_, hL1, hL, ?_, ?_, rfl⟩
  · have h0 : (0 : Nat) ≠ 255 := by decide
    simp only [f2dMag, h0, hf0, if_false, if_true, Nat.shiftLeft_eq, two52, Nat.reducePow]
  · have hp1 : 2 ^ (bitLength f - 1) * 2 ^ (53 - bitLength f) = 2 ^ 52 := by
      rw [← Nat.pow_add, show bitLength f - 1 + (53 - bitLength f) = 52 by omega]
    have := Nat.mul_le_mul_right (2 ^ (53 - bitLength f)) hlo
    rw [hp1] at this
    simpa only [Nat.reducePow] using this
  · have hp2 : 2 ^ bitLength f * 2 ^ (53 - bitLength f) = 2 ^ 53 := by
      rw [← Nat.pow_add, show bitLength f + (53 - bitLength f) = 53 by omega]
    have := Nat.mul_lt_mul_of_pos_right hhi (Nat.pos_of_ne_zero (by simp) : 0 < 2 ^ (53 - bitLength f))
    rw [hp2] at this
    simpa only [Nat.reducePow] using this

theorem d2fMag_sub (e f : Nat) (h1 : e ≠ 2047) (h2 : e ≠ 0) (h3 : ¬ e ≥ 897) :
    d2fMag e f = roundShift (two52 + f) (29 + (897 - e)) := by
  simp only [d2fMag, h1, h2, h3, if_false]

theorem fTrip_sub (f L M : Nat) (hL1 : 1 ≤ L) (hL : L ≤ 23) (hm1 : 4503599627370496 ≤ M)
    (hm2 : M < 9007199254740992) (hM : M = f * 2 ^ (53 - L)) :
    d2fMag (((L + 873) * 4503599627370496 + (M - 4503599627370496)) >>> 52)
      (((L + 873) * 4503599627370496 + (M - 4503599627370496)) % two52) = f := by
  generalize hE : L + 873 = E
  have hk : 53 - L = 29 + (897 - E) := by omega
  rw [hk] at hM
  have h1 : (E * 4503599627370496 + (M - 4503599627370496)) >>> 52 = E := by
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]; omega
  have h2 : (E * 4503599627370496 + (M - 4503599627370496)) % two52 = M - 4503599627370496 := by
    unfold two52; omega
  have h4 : two52 + (M - 4503599627370496) = M := by unfold two52; omega
  rw [h1, h2, d2fMag_sub E _ (by omega) (by omega) (by omega), h4, hM]
  exact roundShift_exact f _

theorem d2fMag_norm (e f : Nat) (h1 : e ≠ 2047) (h2 : e ≠ 0) (h3 : e ≥ 897)
    (hq : roundShift (two52 + f) 29 ≠ 16777216) (h4 : ¬ e ≥ 1151) :
    d2fMag e f = ((e - 896) <<< 23) + (roundShift (two52 + f) 29 - 8388608) := by
  simp only [d2fMag, h1, h2, h3, hq, h4, if_false, if_true]

theorem fTrip_norm (e f : Nat) (he1 : 1 ≤ e) (he2 : e ≤ 254) (hf : f < 8388608) :
    d2fMag (((e + 896) * 4503599627370496 + f * 536870912) >>> 52)
      (((e + 896) * 4503599627370496 + f * 536870912) % two52) = e * 8388608 + f := by
  have h1 : ((e + 896) * 4503599627370496 + f * 536870912) >>> 52 = e + 896 := by
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]; omega
  have h2 : ((e + 896) * 4503599627370496 + f * 536870912) % two52 = f * 536870912 := by
    unfold two52; omega
  have h3 : roundShift (two52 + f * 536870912) 29 = 8388608 + f := by
    have := roundShift_exact (8388608 + f) 29
    rwa [show (8388608 + f) * 2 ^ 29 = two52 + f * 536870912 by unfold two52; simp only [Nat.reducePow]; omega] at this
  rw [h1, h2, d2fMag_norm (e + 896) _ (by omega) (by omega) (by omega) (by rw [h3]; omega) (by omega), h3]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- The magnitude of a binary32 pattern after `(double)` then `(float)`. -/
theorem fTripMag (e f : Nat) (he : e < 256) (hf : f < 8388608) :
    f2dMag e f < two63 ∧
    d2fMag ((f2dMag e f) >>> 52) ((f2dMag e f) % two52) =
      (if e = 255 ∧ f ≠ 0 ∧ f < 4194304 then e * 8388608 + f + 4194304 else e * 8388608 + f) := by
  by_cases h255 : e = 255
  · subst h255
    by_cases hf0 : f = 0
    · subst hf0; decide +kernel
    · rw [fTrip_nan_mag f hf hf0, fTrip_nan f]
      refine ⟨by unfold two63; omega, ?_⟩
      split <;> omega
  · by_cases he0 : e = 0
    · subst he0
      by_cases hf0 : f = 0
      · subst hf0; decide +kernel
      · obtain ⟨L, M, hM, h1, h2, h3, h4, h5⟩ := fTrip_sub_mag f hf hf0
        rw [hM, fTrip_sub f L M h1 h2 h3 h4 h5]
        refine ⟨by unfold two63; omega, ?_⟩
        rw [if_neg (by omega)]; omega
    · have hM : f2dMag e f = (e + 896) * 4503599627370496 + f * 536870912 := by
        unfold f2dMag
        rw [if_neg h255, if_neg he0]
        simp only [Nat.shiftLeft_eq, Nat.reducePow]
      rw [hM, fTrip_norm e f (by omega) (by omega) hf]
      refine ⟨by unfold two63; omega, ?_⟩
      rw [if_neg (by omega)]

/-- A binary32 pattern with its quiet bit set if it is a signalling NaN. -/
def quiet32 (b : Nat) : Nat :=
  if 2139095040 < b % 2147483648 ∧ b % 8388608 < 4194304 then b + 4194304 else b

theorem fTrip (b : Nat) (hb : b < 4294967296) : doubleToFloat (floatToDouble b) = quiet32 b := by
  rw [floatToDouble_eq]
  have he : (b % 2147483648) >>> 23 < 256 := by
    rw [Nat.shiftRight_eq_div_pow]; simp only [Nat.reducePow]; omega
  have hf : b % 8388608 < 8388608 := Nat.mod_lt _ (by decide)
  obtain ⟨hlt, hmag⟩ := fTripMag _ _ he hf
  generalize hE : (b % 2147483648) >>> 23 = e at he hmag hlt
  generalize hF : b % 8388608 = f at hf hmag hlt
  rw [doubleToFloat_eq]
  generalize hM : f2dMag e f = M at hlt hmag
  by_cases hs : b ≥ 2147483648
  · rw [if_pos hs, if_pos (by unfold two63 at *; omega)]
    have h1 : (two63 + M) % two63 = M := by unfold two63 at *; omega
    have h2 : (two63 + M) % two52 = M % two52 := by unfold two63 two52 at *; omega
    rw [h1, h2, hmag]
    unfold quiet32
    split <;> split <;> omega
  · rw [if_neg hs, if_neg (by unfold two63 at *; omega)]
    simp only [Nat.zero_add]
    have h1 : M % two63 = M := Nat.mod_eq_of_lt hlt
    rw [h1, hmag]
    unfold quiet32
    split <;> split <;> omega

end PyLean.Sequences
