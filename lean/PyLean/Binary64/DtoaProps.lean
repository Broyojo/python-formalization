import PyLean.Binary64.StrtodProps
import PyLean.Binary64.BigintProps2

/-!
`_Py_dg_dtoa` on the values it returns early for, the float words dtoa.c reads, and what
follows for `repr` and `round`.
-/

namespace PyLean.Binary64

open F64

theorem word0_lt (x : F64) : word0 x < 2 ^ 32 := by
  have := x.isLt; unfold word0; omega

theorem word_parts (x : F64) :
    word0 x = (if x.sign then 2 ^ 31 else 0) + x.bexp * 2 ^ 20 + x.frac / 2 ^ 32 ∧
      word1 x = x.frac % 2 ^ 32 ∧ x.frac / 2 ^ 32 < 2 ^ 20 := by
  have h := bits_decomp x
  have hf := frac_lt x
  have hb := bexp_lt x
  unfold word0 word1
  split at h <;> (simp only [*]; omega)

theorem sign_word (x : F64) : (word0 x &&& Sign_bit != 0) = x.sign := by
  have h := land_high_mask (x := word0 x) (n := 32) (k := 31) (word0_lt x) (by omega)
  have e : (2 ^ 32 - 2 ^ 31 : Nat) = Sign_bit := by decide
  rw [e] at h
  rw [h]
  obtain ⟨h1, _, h3⟩ := word_parts x
  have hb := bexp_lt x
  cases hs : x.sign
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h1
    have : word0 x / 2 ^ 31 = 0 := by omega
    simp [this]
  · simp only [hs, ↓reduceIte] at h1
    have : word0 x / 2 ^ 31 = 1 := by omega
    simp [this]

theorem exp_word {x : F64} (hs : x.sign = false) : word0 x &&& Exp_mask = x.bexp * 2 ^ 20 := by
  obtain ⟨h1, _, h3⟩ := word_parts x
  have hb := bexp_lt x
  simp only [hs, Bool.false_eq_true, ↓reduceIte] at h1
  have hlt : word0 x < 2 ^ 31 := by omega
  have h := land_high_mask (x := word0 x) (n := 31) (k := 20) hlt (by omega)
  have e : (2 ^ 31 - 2 ^ 20 : Nat) = Exp_mask := by decide
  rw [e] at h
  rw [h]; omega

theorem frac_word (x : F64) : word0 x &&& Frac_mask = x.frac / 2 ^ 32 := by
  obtain ⟨h1, _, h3⟩ := word_parts x
  have hm : Frac_mask = 2 ^ 20 - 1 := by decide
  rw [hm, Nat.and_two_pow_sub_one_eq_mod]
  have hb := bexp_lt x
  split at h1 <;> omega

/-- The start of `_Py_dg_dtoa` clears the sign bit, dtoa.c:2249-2255. -/
theorem clear_sign (dd : F64) :
    (if (word0 dd &&& Sign_bit != 0) = true then setWord0 dd (word0 dd - Sign_bit) else dd) = dd.abs := by
  rw [sign_word]
  unfold F64.abs
  cases hs : dd.sign
  · simp
  · simp only [↓reduceIte]
    apply F64.ext
    obtain ⟨h1, h2, h3⟩ := word_parts dd
    have hb := bexp_lt dd
    have hd := bits_decomp dd
    simp only [hs, ↓reduceIte] at h1 hd
    have hlt := dd.isLt
    have hn : (F64.neg dd).bits = dd.bits - 2 ^ 63 := by
      unfold F64.neg
      have hge : 2 ^ 63 ≤ dd.bits := by simpa [F64.sign] using hs
      simp only [hge, ↓reduceIte]
      exact bits_ofBits_of_lt (by omega)
    rw [hn]
    unfold setWord0 mkWords word1
    rw [bits_ofBits]
    have hS : Sign_bit = 2147483648 := rfl
    rw [hS]
    unfold word0 at h1 ⊢
    omega

theorem abs_fields (x : F64) :
    x.abs.sign = false ∧ x.abs.bexp = x.bexp ∧ x.abs.frac = x.frac := by
  obtain ⟨h1, h2, h3⟩ := neg_fields x
  unfold F64.abs
  cases hs : x.sign
  · simp [hs]
  · simp [h1, h2, h3, hs]

/-- `_Py_dg_dtoa` on infinities, NaNs and zeros, dtoa.c:2257-2269: the digit strings
`Infinity`, `NaN` and `0`, the sign of the input, and `decpt` 9999, 9999 and 1. -/
def DtoaSpecial : Prop :=
  ∀ (dd : F64) (mode : Nat) (n : Int),
    (dd.isInf = true → _Py_dg_dtoa dd mode n =
      some { digits := [73, 110, 102, 105, 110, 105, 116, 121], decpt := 9999, sign := dd.sign }) ∧
    (dd.isNaN = true → _Py_dg_dtoa dd mode n =
      some { digits := [78, 97, 78], decpt := 9999, sign := dd.sign }) ∧
    (dd.isZero = true → _Py_dg_dtoa dd mode n =
      some { digits := [48], decpt := 1, sign := dd.sign })

theorem dtoaSpecial_proven : DtoaSpecial := by
  intro dd mode n
  obtain ⟨u1, u2, u3⟩ := abs_fields dd
  have hE : (word0 dd.abs &&& Exp_mask) = dd.bexp * 2 ^ 20 := by
    rw [exp_word u1, u2]
  have hEx : Exp_mask = 2047 * 2 ^ 20 := by decide
  have hfz : (word1 dd.abs == 0 && (word0 dd.abs &&& 0xfffff) == 0) = (dd.frac == 0) := by
    obtain ⟨_, h2, h3⟩ := word_parts dd.abs
    have e := frac_word dd.abs
    have hm : (0xfffff : Nat) = Frac_mask := rfl
    rw [hm, e, h2, u3]
    have hf := frac_lt dd
    by_cases hz : dd.frac = 0
    · simp [hz]
    · have : ¬ (dd.frac % 2 ^ 32 = 0 ∧ dd.frac / 2 ^ 32 = 0) := by omega
      simp only [hz, beq_iff_eq, Bool.and_eq_true, Bool.false_eq, Bool.and_eq_false_iff]
      by_cases h4 : dd.frac % 2 ^ 32 = 0
      · right; simp; omega
      · left; simpa using h4
  refine ⟨fun hi => ?_, fun hn' => ?_, fun hz => ?_⟩
  · rw [isInf_eq] at hi
    have c1 : (word0 dd.abs &&& Exp_mask == Exp_mask) = true := by
      rw [hE, hi.1]; simp [hEx]
    have c2 : (dd.frac == 0) = true := by simp [hi.2]
    unfold _Py_dg_dtoa
    simp only [sign_word, clear_sign, c1, ↓reduceIte, hfz, c2]
  · rw [isNaN_eq] at hn'
    have c1 : (word0 dd.abs &&& Exp_mask == Exp_mask) = true := by
      rw [hE, hn'.1]; simp [hEx]
    have c2 : (dd.frac == 0) = false := by simp [hn'.2]
    unfold _Py_dg_dtoa
    simp only [sign_word, clear_sign, c1, ↓reduceIte, hfz, c2, Bool.false_eq_true]
  · rw [isZero_eq] at hz
    have c1 : (word0 dd.abs &&& Exp_mask == Exp_mask) = false := by
      rw [hE, hz.1]; simp [hEx]
    have c2 : dd.abs.isZero = true := by
      rw [isZero_eq, u2, u3]; exact hz
    unfold _Py_dg_dtoa
    simp only [sign_word, clear_sign, c1, c2, ↓reduceIte, Bool.false_eq_true]

/-- `repr` of NaNs, infinities and zeros. -/
def ReprSpecial : Prop :=
  ∀ x : F64,
    (x.isNaN = true → float_repr x = some [110, 97, 110]) ∧
    (x.isInf = true → float_repr x = some (if x.sign then [45, 105, 110, 102] else [105, 110, 102])) ∧
    (x.isZero = true → float_repr x = some (if x.sign then [45, 48, 46, 48] else [48, 46, 48]))

theorem reprSpecial_proven : ReprSpecial := by
  intro x
  have hdef : float_repr x = (format_float_short x 114 0 0 { add_dot_0 := true } false).map
      fun r => render r.1 := rfl
  obtain ⟨h1, h2, h3⟩ := dtoaSpecial_proven x 0 0
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hdef]; unfold format_float_short; rw [h1 h |> fun _ => h2 h]
    cases x.sign <;> rfl
  · rw [hdef]; unfold format_float_short; rw [h1 h]
    cases x.sign <;> rfl
  · rw [hdef]; unfold format_float_short; rw [h3 h]
    cases x.sign <;> rfl

/-- `round(x, n)` on what it settles without decimal arithmetic: NaNs and infinities
round to themselves, `n > 323` gives `x`, `n < -308` gives a zero with the sign of `x`, and
a zero rounds to itself at every `n`. -/
def FloatRoundExtremes : Prop :=
  ∀ (x : F64) (n : Int),
    (x.isFinite = false → float_round_ndigits x n = .ok x) ∧
    (x.isFinite = true → 323 < n → float_round_ndigits x n = .ok x) ∧
    (x.isFinite = true → n < -308 → float_round_ndigits x n = .ok (zero x.sign)) ∧
    (x.isZero = true → -308 ≤ n → n ≤ 323 → double_round x n = .ok x)

theorem double_round_zero (s : Bool) (n : Int) : double_round (zero s) n = .ok (zero s) := by
  have hz := zero_isZero s
  have h := (dtoaSpecial_proven (zero s) 3 n).2.2 hz
  unfold double_round
  rw [h, zero_sign]
  cases s <;> decide +kernel

theorem floatRoundExtremes_proven : FloatRoundExtremes := by
  intro x n
  refine ⟨fun h => ?_, fun h hn => ?_, fun h hn => ?_, fun h _ _ => ?_⟩
  · simp [float_round_ndigits, h]
  · have : (323 : Int) < clipSsize n := by
      unfold clipSsize ssizeMax ssizeMin; omega
    simp [float_round_ndigits, h, this]
  · have h1 : ¬ (323 : Int) < clipSsize n := by
      unfold clipSsize ssizeMax ssizeMin; omega
    have h2 : clipSsize n < -308 := by
      unfold clipSsize ssizeMax ssizeMin; omega
    have hm : F64.mul d0 x = zero x.sign := by
      rw [mul_of_finite d0_isFinite h, d0_toRat]
      have hs : d0.sign = false := by decide +kernel
      simp [hs]
    simp [float_round_ndigits, h, h1, h2, hm]
  · rw [eq_zero_of_isZero h]; exact double_round_zero _ n

/-- Word-level `ulp` on a positive float with a large enough exponent gives the gap above
it, and `sulp` agrees when no scaling is active. -/
def UlpSpec : Prop :=
  ∀ x : F64, x.sign = false → 53 ≤ x.bexp → x.isFinite = true →
    (ulpD x).toRat = pw x.lsbExp ∧ sulp x 0 = ulpD x

theorem ulpSpec_proven : UlpSpec := by
  intro x hs hb hf
  rw [isFinite_eq] at hf
  have hlt := bexp_lt x
  have hbits : (ulpD x).bits = (x.bexp - 52) * 2 ^ 52 := by
    unfold ulpD mkWords
    rw [exp_word hs, bits_ofBits]
    have hE : P = 53 := rfl
    have hM : Exp_msk1 = 2 ^ 20 := rfl
    rw [hE, hM]
    omega
  have e1 : (ulpD x).sign = false := by
    unfold F64.sign; rw [hbits]; simp; omega
  have e2 : (ulpD x).bexp = x.bexp - 52 := by
    unfold F64.bexp; rw [hbits]; omega
  have e3 : (ulpD x).frac = 0 := by
    unfold F64.frac; rw [hbits]; omega
  have hfin : (ulpD x).isFinite = true := by
    rw [isFinite_eq, e2]; omega
  constructor
  · rw [toRat_of_finite hfin, e1]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hm : (ulpD x).mant = 2 ^ 52 := by
      unfold F64.mant; rw [e2, e3]
      have : x.bexp - 52 ≠ 0 := by omega
      simp [this]
    have hl : (ulpD x).lsbExp = (x.bexp : Int) - 52 - 1075 := by
      unfold F64.lsbExp; rw [e2]; omega
    have hl2 : x.lsbExp = (x.bexp : Int) - 1075 := by
      unfold F64.lsbExp; omega
    rw [hm, hl, hl2, ← pw_natCast 52 |> fun h => (by simpa using h : ((2 ^ 52 : Nat) : Rat) = pw 52)]
    rw [← pw_add]; congr 1; omega
  · simp [sulp]

/-- `sd2b` with no scaling reads a positive float as its mantissa and exponent. -/
def Sd2bSpec : Prop :=
  ∀ x : F64, x.sign = false → x.isFinite = true →
    (sd2b x 0).1.val = x.mant ∧ (sd2b x 0).2 = x.lsbExp

theorem sd2bSpec_proven : Sd2bSpec := by
  intro x hs hf
  rw [isFinite_eq] at hf
  obtain ⟨h1, h2, h3⟩ := word_parts x
  have hfl := frac_lt x
  have hb := bexp_lt x
  have hE : (word0 x &&& Exp_mask) / 2 ^ Exp_shift = x.bexp := by
    rw [exp_word hs]; unfold Exp_shift; omega
  have hF := frac_word x
  have hsplit : x.frac = x.frac % 2 ^ 32 + 2 ^ 32 * (x.frac / 2 ^ 32) := by omega
  have hval : ∀ a t : Nat, Bigint.val { x := if t == 0 then [a] else [a, t] } = a + 2 ^ 32 * t := by
    intro a t
    by_cases ht : t = 0
    · simp [ht, Bigint.val, Bigint.limbsVal]
    · simp [ht, Bigint.val, Bigint.limbsVal]
  unfold sd2b
  simp only [hE, hF, h2]
  simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  by_cases hb0 : x.bexp = 0
  · have hlt : (Etiny - 1 + ((x.bexp : Nat) : Int)) < Etiny := by rw [hb0]; decide
    simp only [hlt, ↓reduceIte]
    rw [hval]
    constructor
    · unfold F64.mant; simp only [hb0, ↓reduceIte]; omega
    · unfold F64.lsbExp Etiny; rw [hb0]; rfl
  · have hlt : ¬ (Etiny - 1 + ((x.bexp : Nat) : Int)) < Etiny := by unfold Etiny; omega
    simp only [hlt, ↓reduceIte]
    have hor : x.frac / 2 ^ 32 ||| Exp_msk1 = x.frac / 2 ^ 32 + 2 ^ 20 := by
      have := Nat.two_pow_add_eq_or_of_lt (i := 20) h3 1
      rw [Nat.or_comm]
      have e : (Exp_msk1 : Nat) = 2 ^ 20 * 1 := rfl
      rw [e, ← this]; omega
    rw [hor, hval]
    constructor
    · unfold F64.mant; simp only [hb0, ↓reduceIte]; omega
    · unfold F64.lsbExp Etiny; omega

end PyLean.Binary64
