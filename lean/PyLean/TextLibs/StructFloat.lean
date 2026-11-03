import PyLean.TextLibs.StructRange

/-!
Values of the float codecs of `Modules/_struct.c:264-312`: what `PyFloat_Unpack2`,
`PyFloat_Unpack4` and `PyFloat_Unpack8` return for every bit pattern, the round trips through
`PyFloat_Pack2` and `PyFloat_Pack4`, and the exact overflow boundary of `PyFloat_Pack2`
(`Objects/floatobject.c:1895-2240`). A float is its 64-bit pattern, so each statement is an equality
of bit patterns, signalling NaNs included.
-/

namespace PyLean.TextLibs.Struct

open PyLean PyLean.TextLibs

set_option linter.unusedSimpArgs false

/-! ### Arithmetic on the fields -/

theorem log2_eq (m k : Nat) (h1 : 2 ^ k ≤ m) (h2 : m < 2 ^ (k + 1)) : Nat.log2 m = k := by
  have hm : m ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
  have a := (Nat.le_log2 hm).2 h1
  have b := (Nat.log2_lt hm).2 h2
  omega

theorem pow_split (K : Nat) (hK : K ≤ 52) : 2 ^ K * 2 ^ (52 - K) = 2 ^ 52 := by
  rw [← Nat.pow_add]; congr 1; omega

/-- The fields of a double built from its sign, exponent and fraction. -/
theorem f64_fields (s E F : Nat) (hs : s < 2) (hE : E < 2048) (hF : F < 2 ^ 52) :
    f64.sign (s * 2 ^ 63 + E * 2 ^ 52 + F) = s ∧ f64.expOf (s * 2 ^ 63 + E * 2 ^ 52 + F) = E ∧
      f64.frac (s * 2 ^ 63 + E * 2 ^ 52 + F) = F := by
  simp only [Fmt.sign, Fmt.expOf, Fmt.frac, f64, Nat.reducePow, Nat.reduceAdd] at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The fields of a single built from its sign, exponent and fraction. -/
theorem f32_fields (s E F : Nat) (hs : s < 2) (hE : E < 256) (hF : F < 2 ^ 23) :
    f32.sign (s * 2 ^ 31 + E * 2 ^ 23 + F) = s ∧ f32.expOf (s * 2 ^ 31 + E * 2 ^ 23 + F) = E ∧
      f32.frac (s * 2 ^ 31 + E * 2 ^ 23 + F) = F := by
  simp only [Fmt.sign, Fmt.expOf, Fmt.frac, f32, Nat.reducePow, Nat.reduceAdd] at *
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem f64_fracBits : f64.fracBits = 52 := rfl
theorem f64_expBits : f64.expBits = 11 := rfl
theorem f64_bias : f64.bias = 1023 := by decide
theorem f64_expMax : f64.expMax = 2047 := by decide
theorem f32_fracBits : f32.fracBits = 23 := rfl
theorem f32_expBits : f32.expBits = 8 := rfl
theorem f32_bias : f32.bias = 127 := by decide
theorem f32_expMax : f32.expMax = 255 := by decide

theorem roundShift_le (m : Nat) (s : Int) (h : s ≤ 0) : roundShift m s = m * 2 ^ (-s).toNat := by
  unfold roundShift; rw [if_pos h]

/-- `encodeRounded` into binary64 of a value with at most 53 significant bits and a normal
exponent: exact, no rounding. `m` has its top bit at `K`. -/
theorem enc64_exact (s m K : Nat) (ex : Int) (hm1 : 2 ^ K ≤ m) (hm2 : m < 2 ^ (K + 1)) (hK : K ≤ 52)
    (h1 : -1022 ≤ (K : Int) + ex) (h2 : (K : Int) + ex ≤ 1023) :
    f64.encodeRounded s m ex =
      some (s * 2 ^ 63 + ((K : Int) + ex + 1023).toNat * 2 ^ 52 + (m - 2 ^ K) * 2 ^ (52 - K)) := by
  have hm0 : m ≠ 0 := by have := Nat.one_le_two_pow (n := K); omega
  have hl := log2_eq m K hm1 hm2
  have hsplit := pow_split K hK
  have hr : m - 2 ^ K < 2 ^ K := by rw [Nat.pow_succ] at hm2; omega
  have hA : (m - 2 ^ K) * 2 ^ (52 - K) < 2 ^ 52 := by
    rw [← hsplit]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
  have hmul : m * 2 ^ (52 - K) = 2 ^ 52 + (m - 2 ^ K) * 2 ^ (52 - K) := by
    rw [← hsplit, ← Nat.add_mul]; congr 1; omega
  simp only [Fmt.encodeRounded, hm0, if_false, hl, f64_fracBits, f64_expBits, f64_bias, f64_expMax]
  have e1 : ¬ ((K : Int) + ex < 1 - ((1023 : Nat) : Int)) := by omega
  have e2 : (K : Int) + ex - ((52 : Nat) : Int) - ex ≤ 0 := by omega
  have e3 : (-((K : Int) + ex - ((52 : Nat) : Int) - ex)).toNat = 52 - K := by omega
  have e4 : ((K : Int) + ex - (1 - ((1023 : Nat) : Int))).toNat = ((K : Int) + ex + 1023).toNat - 1 := by
    omega
  rw [if_neg e1, roundShift_le _ _ e2, e3, e4, hmul]
  have e5 : ((K : Int) + ex + 1023).toNat ≥ 1 := by omega
  have e6 : ((K : Int) + ex + 1023).toNat ≤ 2046 := by omega
  generalize ((K : Int) + ex + 1023).toNat = T at e5 e6 ⊢
  generalize (m - 2 ^ K) * 2 ^ (52 - K) = A at hA ⊢
  have hT : (T - 1) * 2 ^ 52 + (2 ^ 52 + A) = T * 2 ^ 52 + A := by
    have : T = (T - 1) + 1 := by omega
    conv => rhs; rw [this, Nat.add_mul, Nat.one_mul]
    omega
  rw [hT]
  have hlt : ¬ (T * 2 ^ 52 + A ≥ 2047 * 2 ^ 52) := by
    have : T * 2 ^ 52 + A < (T + 1) * 2 ^ 52 := by rw [Nat.add_mul, Nat.one_mul]; omega
    have : (T + 1) * 2 ^ 52 ≤ 2047 * 2 ^ 52 := Nat.mul_le_mul_right _ (by omega)
    omega
  rw [if_neg hlt]
  apply congrArg some
  rw [show 52 + 11 = 63 from rfl]
  generalize 2 ^ 63 = P
  generalize 2 ^ 52 = Q
  rw [Nat.add_assoc]

/-! ### `PyFloat_Unpack2`: the double for every half-float pattern -/

/-- `unpack_halffloat` returns the double with the half's value for every 16-bit pattern: a normal
half moves its exponent by `1023 - 15` and its fraction up 42 bits; a subnormal one, with top bit
`k`, becomes the normal double `2^k * (1 + r/2^k) * 2^-24`; `±0` and `±inf` stay what they are; and a
NaN keeps its sign and its whole payload, the quiet bit included
(`Objects/floatobject.c:2090-2143`). The last part ties every `e` entry of the three tables to it,
with its byte order. A constant decoder, or one that quieted a signalling NaN, fails this. -/
def HalfUnpackExact : Prop :=
  (∀ s e f : Nat, s < 2 → 1 ≤ e → e ≤ 30 → f < 1024 →
    pyFloatUnpack2Bits (s * 32768 + e * 1024 + f) = s * 2 ^ 63 + (e + 1008) * 2 ^ 52 + f * 2 ^ 42) ∧
  (∀ s k r : Nat, s < 2 → k < 10 → r < 2 ^ k →
    pyFloatUnpack2Bits (s * 32768 + (2 ^ k + r)) = s * 2 ^ 63 + (k + 999) * 2 ^ 52 + r * 2 ^ (52 - k)) ∧
  (∀ s : Nat, s < 2 → pyFloatUnpack2Bits (s * 32768) = s * 2 ^ 63) ∧
  (∀ s f : Nat, s < 2 → f < 1024 →
    pyFloatUnpack2Bits (s * 32768 + 31 * 1024 + f) = s * 2 ^ 63 + 2047 * 2 ^ 52 + f * 2 ^ 42) ∧
  (∀ (t : Tab) (e : FormatDef), e ∈ t.table → e.format = ['e'] → ∀ a b : Nat,
    runUnpack e [a, b] = .ok (.float (pyFloatUnpack2Bits (if t = .big then a * 256 + b else a + 256 * b))))

theorem half_tables : ∀ t : Tab, ∀ e ∈ t.table, e.format = ['e'] →
    e.size = 2 ∧ (if t = .big then e.unpack = .buHalffloat else e.unpack = .nuHalffloat ∨ e.unpack = .luHalffloat) := by
  intro t
  cases t <;> decide +kernel

theorem unpack2_eq (h : Nat) : pyFloatUnpack2Bits h =
    if h / 1024 % 32 = 31 then
      (if h % 1024 = 0 then f64.infBits (h / 32768 % 2) else f64.infBits (h / 32768 % 2) + h % 1024 * 2 ^ 42)
    else if h / 1024 % 32 = 0 then (f64.encodeRounded (h / 32768 % 2) (h % 1024) (-24)).getD 0
    else (f64.encodeRounded (h / 32768 % 2) (h % 1024 + 1024) (((h / 1024 % 32 : Nat) : Int) - 25)).getD 0 := by
  simp only [pyFloatUnpack2Bits]
  split
  · rfl
  · split <;> rfl

theorem half_normal (s e f : Nat) (hs : s < 2) (he1 : 1 ≤ e) (he2 : e ≤ 30) (hf : f < 1024) :
    pyFloatUnpack2Bits (s * 32768 + e * 1024 + f) = s * 2 ^ 63 + (e + 1008) * 2 ^ 52 + f * 2 ^ 42 := by
  have h1 : (s * 32768 + e * 1024 + f) / 32768 % 2 = s := by omega
  have h2 : (s * 32768 + e * 1024 + f) / 1024 % 32 = e := by omega
  have h3 : (s * 32768 + e * 1024 + f) % 1024 = f := by omega
  rw [unpack2_eq, h1, h2, h3, if_neg (by omega), if_neg (by omega)]
  have g1 : 2 ^ 10 ≤ f + 1024 := by simp only [Nat.reducePow]; omega
  have g2 : f + 1024 < 2 ^ (10 + 1) := by simp only [Nat.reducePow, Nat.reduceAdd]; omega
  have g4 : -1022 ≤ ((10 : Nat) : Int) + ((e : Int) - 25) := by omega
  have g5 : ((10 : Nat) : Int) + ((e : Int) - 25) ≤ 1023 := by omega
  rw [enc64_exact s (f + 1024) 10 ((e : Int) - 25) g1 g2 (by decide) g4 g5, Option.getD_some]
  have : ((10 : Nat) + ((e : Int) - 25) + 1023).toNat = e + 1008 := by omega
  rw [this, show f + 1024 - 2 ^ 10 = f by simp only [Nat.reducePow]; omega]

theorem half_sub (s k r : Nat) (hs : s < 2) (hk : k < 10) (hr : r < 2 ^ k) :
    pyFloatUnpack2Bits (s * 32768 + (2 ^ k + r)) = s * 2 ^ 63 + (k + 999) * 2 ^ 52 + r * 2 ^ (52 - k) := by
  have hk2 : 2 ^ k * 2 ≤ 1024 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k + 1 ≤ 10 by omega)
    rw [Nat.pow_succ] at this
    simpa using this
  have h1 : (s * 32768 + (2 ^ k + r)) / 32768 % 2 = s := by omega
  have h2 : (s * 32768 + (2 ^ k + r)) / 1024 % 32 = 0 := by omega
  have h3 : (s * 32768 + (2 ^ k + r)) % 1024 = 2 ^ k + r := by omega
  have g1 : 2 ^ k ≤ 2 ^ k + r := by omega
  have g2 : 2 ^ k + r < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  have g3 : k ≤ 52 := by omega
  have g4 : -1022 ≤ (k : Int) + -24 := by omega
  have g5 : (k : Int) + -24 ≤ 1023 := by omega
  rw [unpack2_eq, h1, h2, h3, if_neg (by omega), if_pos rfl,
    enc64_exact s (2 ^ k + r) k (-24) g1 g2 g3 g4 g5, Option.getD_some]
  have : ((k : Int) + -24 + 1023).toNat = k + 999 := by omega
  rw [this, Nat.add_sub_cancel_left]

theorem half_zero (s : Nat) (hs : s < 2) : pyFloatUnpack2Bits (s * 32768) = s * 2 ^ 63 := by
  have h1 : (s * 32768) / 32768 % 2 = s := by omega
  have h2 : (s * 32768) / 1024 % 32 = 0 := by omega
  have h3 : (s * 32768) % 1024 = 0 := by omega
  rw [unpack2_eq, h1, h2, h3, if_neg (by omega), if_pos rfl]
  have : f64.encodeRounded s 0 (-24) = some (s * 2 ^ 63) := by
    unfold Fmt.encodeRounded
    rw [if_pos rfl]
    rfl
  rw [this, Option.getD_some]

theorem half_top (s f : Nat) (hs : s < 2) (hf : f < 1024) :
    pyFloatUnpack2Bits (s * 32768 + 31 * 1024 + f) = s * 2 ^ 63 + 2047 * 2 ^ 52 + f * 2 ^ 42 := by
  have h1 : (s * 32768 + 31 * 1024 + f) / 32768 % 2 = s := by omega
  have h2 : (s * 32768 + 31 * 1024 + f) / 1024 % 32 = 31 := by omega
  have h3 : (s * 32768 + 31 * 1024 + f) % 1024 = f := by omega
  have hi : f64.infBits s = s * 2 ^ 63 + 2047 * 2 ^ 52 := by
    simp only [Fmt.infBits, f64_fracBits, f64_expBits, f64_expMax]
  rw [unpack2_eq, h1, h2, h3, if_pos rfl, hi]
  by_cases h0 : f = 0
  · subst h0; rw [if_pos rfl]
  · rw [if_neg h0]

theorem half_tab (t : Tab) (e : FormatDef) (he : e ∈ t.table) (hfm : e.format = ['e']) (a b : Nat) :
    runUnpack e [a, b] = .ok (.float (pyFloatUnpack2Bits (if t = .big then a * 256 + b else a + 256 * b))) := by
  obtain ⟨hs, hu⟩ := half_tables t e he hfm
  have hl : leVal [a, b] = a + 256 * b := by simp [leVal]
  have hb : beVal [a, b] = a * 256 + b := by simp [beVal]
  cases t with
  | big => simp only [if_true] at hu ⊢; simp [runUnpack, hu, hs, hb]
  | native => simp only [reduceCtorEq, if_false] at hu ⊢; rcases hu with hu | hu <;> simp [runUnpack, hu, hs, hl]
  | little => simp only [reduceCtorEq, if_false] at hu ⊢; rcases hu with hu | hu <;> simp [runUnpack, hu, hs, hl]

theorem halfUnpackExact_proven : HalfUnpackExact :=
  ⟨half_normal, half_sub, half_zero, half_top, half_tab⟩

/-! ### `PyFloat_Pack2` on the doubles `PyFloat_Unpack2` returns -/

theorem lor_mul_add (a b k : Nat) (ha : a < 2 ^ k) : a ||| b * 2 ^ k = a + b * 2 ^ k := by
  have := Nat.shiftLeft_add_eq_or_of_lt ha b
  rw [Nat.shiftLeft_eq] at this
  rw [Nat.or_comm, ← this, Nat.add_comm]

/-- The 16-bit pattern from its fields. -/
theorem half_bits (s e f : Nat) (hs : s < 2) (he : e < 32) (hf : f < 1024) :
    (f ||| e * 1024) ||| s * 32768 = s * 32768 + e * 1024 + f := by
  rw [show (1024 : Nat) = 2 ^ 10 from rfl, lor_mul_add f e 10 hf]
  rw [show (32768 : Nat) = 2 ^ 15 from rfl, lor_mul_add _ s 15 (by simp only [Nat.reducePow]; omega)]
  omega

/-- `pack2Round` when the scaled fraction is an exact integer `q`: no rounding. -/
theorem pack2Round_exact (sign fn fd e q : Nat) (hfd : 0 < fd) (h : fn * 1024 = q * fd) :
    pack2Round sign fn fd e = .ok ((q ||| e * 1024) ||| sign * 32768) := by
  simp [pack2Round, h, Nat.mul_div_cancel q hfd, Nat.ne_of_gt hfd, Nat.ne_of_lt hfd]

theorem f64_isInf_eq (x : Nat) : f64.isInf x = (f64.expOf x == 2047 && f64.frac x == 0) := by
  simp only [Fmt.isInf, f64_expMax]

theorem f64_isNaN_eq (x : Nat) : f64.isNaN x = (f64.expOf x == 2047 && f64.frac x != 0) := by
  simp only [Fmt.isNaN, f64_expMax]

theorem f64_mag_normal (x : Nat) (h : f64.expOf x ≠ 0) :
    f64.mag x = (f64.frac x + 2 ^ 52, (f64.expOf x : Int) - 1023 - 52) := by
  simp only [Fmt.mag, h, if_false, f64_fracBits, f64_bias]
  rfl

theorem f64_mag_sub (x : Nat) (h : f64.expOf x = 0) : f64.mag x = (f64.frac x, -1074) := by
  simp only [Fmt.mag, h, if_true, f64_fracBits, f64_bias]
  rfl

def ovfE : PyExc := .overflowError "float too large to pack with e format"

/-- `PyFloat_Pack2` on a normal, finite, non-zero double, after `frexp`: the branches by exponent. -/
theorem pack2_normal (s E F : Nat) (hs : s < 2) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046) (hF : F < 2 ^ 52) :
    pyFloatPack2Bits (s * 2 ^ 63 + E * 2 ^ 52 + F) =
      if (E : Int) - 1023 ≥ 16 then .error ovfE
      else if (E : Int) - 1023 < -25 then pack2Round s 0 1 0
      else if (E : Int) - 1023 < -14 then
        pack2Round s (F + 2 ^ 52) (2 ^ 52 * 2 ^ (-(14 + ((E : Int) - 1023))).toNat) 0
      else pack2Round s F (2 ^ 52) ((E : Int) - 1023 + 15).toNat := by
  obtain ⟨h1, h2, h3⟩ := f64_fields s E F hs (by omega) hF
  have hx0 : f64.expOf (s * 2 ^ 63 + E * 2 ^ 52 + F) ≠ 0 := by rw [h2]; omega
  have hl : Nat.log2 (F + 2 ^ 52) = 52 := log2_eq _ _ (by omega) (by rw [Nat.pow_succ]; omega)
  have hb : (E == 2047) = false := by simp only [beq_eq_false_iff_ne]; omega
  unfold pyFloatPack2Bits
  rw [f64_mag_normal _ hx0]
  simp only [h1, h2, h3, f64_isInf_eq, f64_isNaN_eq, hb, Bool.false_and, Bool.false_eq_true, if_false, hl]
  rw [if_neg (by omega)]
  have e1 : (E : Int) - 1023 - 52 + ((52 : Nat) : Int) = (E : Int) - 1023 := by omega
  rw [e1, show F + 2 ^ 52 - 2 ^ 52 = F by omega]
  rfl

/-- `PyFloat_Pack2` on an infinity. -/
theorem pack2_top (x : Nat) (h2 : f64.expOf x = 2047) (h3 : f64.frac x = 0) :
    pyFloatPack2Bits x = .ok (0x1f * 1024 + f64.sign x * 32768) := by
  unfold pyFloatPack2Bits
  simp [h2, h3, Fmt.isInf, f64_expMax]

/-- `PyFloat_Pack2` on a zero. -/
theorem pack2_zero (x : Nat) (h2 : f64.expOf x = 0) (h3 : f64.frac x = 0) :
    pyFloatPack2Bits x = .ok (f64.sign x * 32768) := by
  unfold pyFloatPack2Bits
  simp [h2, h3]

theorem rt_top (s : Nat) (hs : s < 2) :
    pyFloatPack2Bits (pyFloatUnpack2Bits (s * 32768 + 31 * 1024 + 0)) = .ok (s * 32768 + 31 * 1024 + 0) := by
  rw [half_top s 0 hs (by decide)]
  obtain ⟨h1, h2, h3⟩ := f64_fields s 2047 (0 * 2 ^ 42) hs (by decide)
    (by rw [Nat.zero_mul]; exact Nat.two_pow_pos _)
  rw [pack2_top _ h2 (by rw [h3, Nat.zero_mul]), h1]
  apply congrArg Except.ok
  clear h1 h2 h3
  omega

theorem rt_zero (s : Nat) (hs : s < 2) :
    pyFloatPack2Bits (pyFloatUnpack2Bits (s * 32768)) = .ok (s * 32768) := by
  rw [half_zero s hs]
  obtain ⟨h1, h2, h3⟩ := f64_fields s 0 0 hs (by decide) (Nat.two_pow_pos _)
  simp only [Nat.zero_mul, Nat.add_zero] at h1 h2 h3
  rw [pack2_zero _ h2 h3, h1]

theorem rt_sub (s k r : Nat) (hs : s < 2) (hk10 : k < 10) (hr : r < 2 ^ k) :
    pyFloatPack2Bits (pyFloatUnpack2Bits (s * 32768 + (2 ^ k + r))) = .ok (s * 32768 + (2 ^ k + r)) := by
  rw [half_sub s k r hs hk10 hr]
  have hsplit := pow_split k (by omega)
  have hA : r * 2 ^ (52 - k) < 2 ^ 52 := by
    rw [← hsplit]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
  rw [pack2_normal s (k + 999) _ hs (by omega) (by omega) hA]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have e1 : (-(14 + (((k + 999 : Nat) : Int) - 1023))).toNat = 10 - k := by omega
  rw [e1]
  have hq : (r * 2 ^ (52 - k) + 2 ^ 52) * 1024 = (2 ^ k + r) * (2 ^ 52 * 2 ^ (10 - k)) := by
    have p1 : 2 ^ 52 * 2 ^ (10 - k) = 2 ^ (52 - k) * 1024 := by
      rw [show (1024 : Nat) = 2 ^ 10 from rfl, ← Nat.pow_add, ← Nat.pow_add,
        show 52 + (10 - k) = 52 - k + 10 by omega]
    rw [p1, ← hsplit, ← Nat.add_mul, Nat.add_comm r, Nat.mul_assoc]
  have hf : 2 ^ k + r < 1024 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k + 1 ≤ 10 by omega)
    rw [Nat.pow_succ] at this
    have h1024 : (2 : Nat) ^ 10 = 1024 := rfl
    omega
  rw [pack2Round_exact s _ _ 0 (2 ^ k + r) (Nat.mul_pos (Nat.two_pow_pos _) (Nat.two_pow_pos _)) hq,
    half_bits s 0 (2 ^ k + r) hs (by decide) hf]
  simp only [Nat.zero_mul, Nat.add_zero]

theorem rt_normal (s e f : Nat) (hs : s < 2) (he1 : 1 ≤ e) (he2 : e ≤ 30) (hfv : f < 1024) :
    pyFloatPack2Bits (pyFloatUnpack2Bits (s * 32768 + e * 1024 + f)) = .ok (s * 32768 + e * 1024 + f) := by
  rw [half_normal s e f hs he1 he2 hfv]
  have hA : f * 2 ^ 42 < 2 ^ 52 := by
    have : f * 2 ^ 42 < 1024 * 2 ^ 42 := Nat.mul_lt_mul_of_pos_right hfv (Nat.two_pow_pos _)
    exact Nat.lt_of_lt_of_le this (by decide)
  rw [pack2_normal s (e + 1008) _ hs (by omega) (by omega) hA]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have e1 : (((e + 1008 : Nat) : Int) - 1023 + 15).toNat = e := by omega
  have hq : f * 2 ^ 42 * 1024 = f * 2 ^ 52 := by rw [Nat.mul_assoc]
  rw [e1, pack2Round_exact s _ _ e f (Nat.two_pow_pos _) hq, half_bits s e f hs (by omega) hfv]

/-- Packing the double of a half-float pattern that is not a NaN gives the pattern back. -/
theorem halfRoundTrip_proven : HalfRoundTrip := by
  intro h hh hnan
  have hs : h / 32768 < 2 := by omega
  have hdec : h = h / 32768 * 32768 + h / 1024 % 32 * 1024 + h % 1024 := by omega
  generalize h / 32768 = s at hs hdec
  have hev : h / 1024 % 32 < 32 := Nat.mod_lt _ (by decide)
  have hfv : h % 1024 < 1024 := Nat.mod_lt _ (by decide)
  generalize h / 1024 % 32 = e at hnan hdec hev
  generalize h % 1024 = f at hnan hdec hfv
  subst hdec
  clear hh
  by_cases he31 : e = 31
  · subst he31
    have hf0 : f = 0 := by omega
    subst hf0
    exact rt_top s hs
  by_cases he0 : e = 0
  · subst he0
    by_cases hf0 : f = 0
    · subst hf0
      rw [show s * 32768 + 0 * 1024 + 0 = s * 32768 by omega]
      exact rt_zero s hs
    · have hk := Nat.lt_log2_self (n := f)
      have hk2 := Nat.log2_self_le hf0
      have hk10 : Nat.log2 f < 10 := (Nat.log2_lt hf0).2 (by simp only [Nat.reducePow]; omega)
      generalize Nat.log2 f = k at hk hk2 hk10
      have hr : f - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hk; omega
      rw [show s * 32768 + 0 * 1024 + f = s * 32768 + (2 ^ k + (f - 2 ^ k)) by omega]
      exact rt_sub s k (f - 2 ^ k) hs hk10 hr
  · exact rt_normal s e f hs (by omega) (by omega) hfv

/-! ### `PyFloat_Unpack4`: the double for every single-precision pattern -/

theorem f32_mag_normal (y : Nat) (h : f32.expOf y ≠ 0) :
    f32.mag y = (f32.frac y + 2 ^ 23, (f32.expOf y : Int) - 127 - 23) := by
  simp only [Fmt.mag, h, if_false, f32_fracBits, f32_bias]
  rfl

theorem f32_mag_sub (y : Nat) (h : f32.expOf y = 0) : f32.mag y = (f32.frac y, -149) := by
  simp only [Fmt.mag, h, if_true, f32_fracBits, f32_bias]
  rfl

/-- `(double)y` on a normal single: exact. -/
theorem cast_normal (y s E F : Nat) (h1 : f32.sign y = s) (h2 : f32.expOf y = E) (h3 : f32.frac y = F)
    (hE1 : 1 ≤ E) (hE2 : E ≤ 254) (hF : F < 2 ^ 23) :
    castFloatToDouble y = s * 2 ^ 63 + (E + 896) * 2 ^ 52 + F * 2 ^ 29 := by
  have hx0 : f32.expOf y ≠ 0 := by rw [h2]; omega
  unfold castFloatToDouble
  rw [f32_mag_normal y hx0]
  have hn : f32.isNaN y = false := by simp [Fmt.isNaN, f32_expMax, h2]; omega
  have hi : f32.isInf y = false := by simp [Fmt.isInf, f32_expMax, h2]; omega
  simp only [hn, hi, Bool.false_eq_true, if_false, h1, h2, h3]
  have g1 : 2 ^ 23 ≤ F + 2 ^ 23 := by omega
  have g2 : F + 2 ^ 23 < 2 ^ (23 + 1) := by rw [Nat.pow_succ]; omega
  have g4 : -1022 ≤ ((23 : Nat) : Int) + ((E : Int) - 127 - 23) := by omega
  have g5 : ((23 : Nat) : Int) + ((E : Int) - 127 - 23) ≤ 1023 := by omega
  rw [enc64_exact s (F + 2 ^ 23) 23 _ g1 g2 (by decide) g4 g5, Option.getD_some]
  have e1 : (((23 : Nat) : Int) + ((E : Int) - 127 - 23) + 1023).toNat = E + 896 := by omega
  rw [e1, Nat.add_sub_cancel]

/-- `(double)y` on a subnormal single with top bit `k`: exact, and normal as a double. -/
theorem cast_sub (y s k r : Nat) (h1 : f32.sign y = s) (h2 : f32.expOf y = 0) (h3 : f32.frac y = 2 ^ k + r)
    (hk : k < 23) (hr : r < 2 ^ k) :
    castFloatToDouble y = s * 2 ^ 63 + (k + 874) * 2 ^ 52 + r * 2 ^ (52 - k) := by
  unfold castFloatToDouble
  rw [f32_mag_sub y h2]
  have hn : f32.isNaN y = false := by simp [Fmt.isNaN, f32_expMax, h2]
  have hi : f32.isInf y = false := by simp [Fmt.isInf, f32_expMax, h2]
  simp only [hn, hi, Bool.false_eq_true, if_false, h1, h3]
  have g2 : 2 ^ k + r < 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
  rw [enc64_exact s (2 ^ k + r) k (-149) (by omega) g2 (by omega) (by omega) (by omega), Option.getD_some]
  have e1 : ((k : Int) + -149 + 1023).toNat = k + 874 := by omega
  rw [e1, Nat.add_sub_cancel_left]

theorem cast_zero (y s : Nat) (h1 : f32.sign y = s) (h2 : f32.expOf y = 0) (h3 : f32.frac y = 0) :
    castFloatToDouble y = s * 2 ^ 63 := by
  unfold castFloatToDouble
  rw [f32_mag_sub y h2]
  have hn : f32.isNaN y = false := by simp [Fmt.isNaN, f32_expMax, h2]
  have hi : f32.isInf y = false := by simp [Fmt.isInf, f32_expMax, h2]
  simp only [hn, hi, Bool.false_eq_true, if_false, h1, h3]
  have : f64.encodeRounded s 0 (-149) = some (s * 2 ^ 63) := by
    unfold Fmt.encodeRounded
    rw [if_pos rfl]
    rfl
  rw [this, Option.getD_some]

theorem f64_infBits_eq (s : Nat) : f64.infBits s = s * 2 ^ 63 + 2047 * 2 ^ 52 := by
  simp only [Fmt.infBits, f64_fracBits, f64_expBits, f64_expMax]

theorem f32_infBits_eq (s : Nat) : f32.infBits s = s * 2 ^ 31 + 255 * 2 ^ 23 := by
  simp only [Fmt.infBits, f32_fracBits, f32_expBits, f32_expMax]

theorem and_two_pow_zero (n i : Nat) : n &&& 2 ^ i = 0 ↔ n / 2 ^ i % 2 = 0 := by
  constructor
  · intro h
    have := congrArg (fun v => v.testBit i) h
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, Bool.and_true, Nat.zero_testBit] at this
    rw [Nat.testBit_eq_decide_div_mod_eq] at this
    simp only [decide_eq_false_iff_not] at this
    omega
  · intro h
    apply Nat.eq_of_testBit_eq
    intro j
    simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases hj : i = j
    · subst hj
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp [h]
    · simp [hj]

/-- The NaN payload of `(double)y`, after `PyFloat_Unpack4` has put a signalling NaN back. -/
theorem nan_payload (F : Nat) (hF : F < 2 ^ 23) :
    (if F < 2 ^ 22 then (2 ^ 51 ||| F * 2 ^ 29) - 2 ^ 51 else 2 ^ 51 ||| F * 2 ^ 29) = F * 2 ^ 29 := by
  by_cases h : F < 2 ^ 22
  · rw [if_pos h]
    have hlt : F * 2 ^ 29 < 2 ^ 51 := by
      have : F * 2 ^ 29 < 2 ^ 22 * 2 ^ 29 := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)
      exact Nat.lt_of_lt_of_le this (by decide)
    have := lor_mul_add (F * 2 ^ 29) 1 51 hlt
    rw [Nat.one_mul] at this
    rw [Nat.or_comm, this, Nat.add_sub_cancel]
  · rw [if_neg h]
    have hG : F - 2 ^ 22 < 2 ^ 22 := by
      have : (2 : Nat) ^ 23 = 2 ^ 22 * 2 := rfl
      omega
    have hlt : (F - 2 ^ 22) * 2 ^ 29 < 2 ^ 51 := by
      have : (F - 2 ^ 22) * 2 ^ 29 < 2 ^ 22 * 2 ^ 29 := Nat.mul_lt_mul_of_pos_right hG (Nat.two_pow_pos _)
      exact Nat.lt_of_lt_of_le this (by decide)
    have hsplit : F * 2 ^ 29 = (F - 2 ^ 22) * 2 ^ 29 + 1 * 2 ^ 51 := by
      have e : F = (F - 2 ^ 22) + 2 ^ 22 := by omega
      conv => lhs; rw [e, Nat.add_mul]
    rw [hsplit, ← lor_mul_add _ 1 51 hlt, Nat.one_mul, Nat.or_comm, Nat.or_assoc, Nat.or_self]

/-- `unpack_float`, the routine of `bu_float` and `lu_float`, returns the double with the single's
value for every 32-bit pattern: a normal single moves its exponent by `1023 - 127` and its fraction up
29 bits, a subnormal one with top bit `k` becomes the normal double `(2^k + r) * 2^-149`, `±0` and
`±inf` stay, and a NaN keeps its sign and whole payload, a signalling NaN staying signalling
(`Objects/floatobject.c:2146-2201`, the sNaN repair at 2166-2177). A constant decoder, or the native
`nu_float`, which quiets a signalling NaN, fails this. -/
def FloatUnpackExact : Prop :=
  (∀ s E F : Nat, s < 2 → 1 ≤ E → E ≤ 254 → F < 2 ^ 23 →
    pyFloatUnpack4Bits (s * 2 ^ 31 + E * 2 ^ 23 + F) = s * 2 ^ 63 + (E + 896) * 2 ^ 52 + F * 2 ^ 29) ∧
  (∀ s k r : Nat, s < 2 → k < 23 → r < 2 ^ k →
    pyFloatUnpack4Bits (s * 2 ^ 31 + (2 ^ k + r)) = s * 2 ^ 63 + (k + 874) * 2 ^ 52 + r * 2 ^ (52 - k)) ∧
  (∀ s : Nat, s < 2 → pyFloatUnpack4Bits (s * 2 ^ 31) = s * 2 ^ 63) ∧
  (∀ s F : Nat, s < 2 → F < 2 ^ 23 →
    pyFloatUnpack4Bits (s * 2 ^ 31 + 255 * 2 ^ 23 + F) = s * 2 ^ 63 + 2047 * 2 ^ 52 + F * 2 ^ 29) ∧
  (∀ p : List Nat,
    runUnpack ⟨['f'], 4, 0, .buFloat, .bpFloat⟩ p = .ok (.float (pyFloatUnpack4Bits (beVal (p.take 4)))) ∧
    runUnpack ⟨['f'], 4, 0, .luFloat, .lpFloat⟩ p = .ok (.float (pyFloatUnpack4Bits (leVal (p.take 4)))))

theorem notnan_unpack4 (y : Nat) (h : f32.isNaN y = false) : pyFloatUnpack4Bits y = castFloatToDouble y := by
  unfold pyFloatUnpack4Bits
  simp [h]

theorem f32_isNaN_false (y : Nat) (h : f32.expOf y ≠ 255) : f32.isNaN y = false := by
  simp [Fmt.isNaN, f32_expMax, h]

theorem float_normal (s E F : Nat) (hs : s < 2) (hE1 : 1 ≤ E) (hE2 : E ≤ 254) (hF : F < 2 ^ 23) :
    pyFloatUnpack4Bits (s * 2 ^ 31 + E * 2 ^ 23 + F) = s * 2 ^ 63 + (E + 896) * 2 ^ 52 + F * 2 ^ 29 := by
  obtain ⟨h1, h2, h3⟩ := f32_fields s E F hs (by omega) hF
  rw [notnan_unpack4 _ (f32_isNaN_false _ (by rw [h2]; omega)), cast_normal _ s E F h1 h2 h3 hE1 hE2 hF]

theorem float_sub (s k r : Nat) (hs : s < 2) (hk : k < 23) (hr : r < 2 ^ k) :
    pyFloatUnpack4Bits (s * 2 ^ 31 + (2 ^ k + r)) = s * 2 ^ 63 + (k + 874) * 2 ^ 52 + r * 2 ^ (52 - k) := by
  have hf : 2 ^ k + r < 2 ^ 23 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k + 1 ≤ 23 by omega)
    rw [Nat.pow_succ] at this
    omega
  obtain ⟨h1, h2, h3⟩ := f32_fields s 0 (2 ^ k + r) hs (by decide) hf
  rw [Nat.zero_mul, Nat.add_zero] at h1 h2 h3
  rw [notnan_unpack4 _ (f32_isNaN_false _ (by rw [h2]; omega)), cast_sub _ s k r h1 h2 h3 hk hr]

theorem float_zero (s : Nat) (hs : s < 2) : pyFloatUnpack4Bits (s * 2 ^ 31) = s * 2 ^ 63 := by
  obtain ⟨h1, h2, h3⟩ := f32_fields s 0 0 hs (by decide) (Nat.two_pow_pos _)
  simp only [Nat.zero_mul, Nat.add_zero] at h1 h2 h3
  rw [notnan_unpack4 _ (f32_isNaN_false _ (by rw [h2]; omega)), cast_zero _ s h1 h2 h3]

/-- `PyFloat_Unpack4` on an infinity or a NaN, by its fields. -/
theorem unpack4_top (y s F : Nat) (h1 : f32.sign y = s) (h2 : f32.expOf y = 255) (h3 : f32.frac y = F)
    (hF : F < 2 ^ 23) (hb : y &&& 2 ^ 22 = 0 ↔ F < 2 ^ 22) :
    pyFloatUnpack4Bits y = s * 2 ^ 63 + 2047 * 2 ^ 52 + F * 2 ^ 29 := by
  by_cases h0 : F = 0
  · subst h0
    have hn : f32.isNaN y = false := by simp [Fmt.isNaN, h3]
    have hi : f32.isInf y = true := by simp [Fmt.isInf, f32_expMax, h2, h3]
    rw [notnan_unpack4 _ hn]
    unfold castFloatToDouble
    simp only [hn, hi, Bool.false_eq_true, if_false, if_true, h1, f64_infBits_eq, Nat.zero_mul, Nat.add_zero]
  · have hn : f32.isNaN y = true := by simp [Fmt.isNaN, f32_expMax, h2, h3, h0]
    have hc : castFloatToDouble y = s * 2 ^ 63 + 2047 * 2 ^ 52 + (2 ^ 51 ||| F * 2 ^ 29) := by
      unfold castFloatToDouble
      simp only [hn, if_true, h1, h3, f64_infBits_eq]
    have hp := nan_payload F hF
    unfold pyFloatUnpack4Bits
    rw [hc]
    by_cases hlt : F < 2 ^ 22
    · rw [if_pos ⟨hn, hb.2 hlt⟩]
      rw [if_pos hlt] at hp
      have hge : 2 ^ 51 ≤ (2 ^ 51 ||| F * 2 ^ 29) := Nat.left_le_or
      rw [Nat.add_sub_assoc hge, hp]
    · rw [if_neg (fun h => hlt (hb.1 h.2))]
      rw [if_neg hlt] at hp
      rw [hp]

theorem float_top (s F : Nat) (hs : s < 2) (hF : F < 2 ^ 23) :
    pyFloatUnpack4Bits (s * 2 ^ 31 + 255 * 2 ^ 23 + F) = s * 2 ^ 63 + 2047 * 2 ^ 52 + F * 2 ^ 29 := by
  obtain ⟨h1, h2, h3⟩ := f32_fields s 255 F hs (by decide) hF
  have hb : (s * 2 ^ 31 + 255 * 2 ^ 23 + F) &&& 2 ^ 22 = 0 ↔ F < 2 ^ 22 := by
    rw [and_two_pow_zero]
    have e : s * 2 ^ 31 + 255 * 2 ^ 23 + F = (s * 2 ^ 9 + 255 * 2) * 2 ^ 22 + F := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add]
    rw [e, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _)]
    have hF2 : F / 2 ^ 22 < 2 := Nat.div_lt_of_lt_mul (by rw [← Nat.pow_succ]; exact hF)
    have hF3 : F / 2 ^ 22 = 0 ↔ F < 2 ^ 22 := Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)
    have h0 : (s * 2 ^ 9 + 255 * 2) % 2 = 0 := by
      rw [show s * 2 ^ 9 + 255 * 2 = (s * 2 ^ 8 + 255) * 2 by rw [Nat.add_mul, Nat.mul_assoc]]
      exact Nat.mul_mod_left _ _
    rw [Nat.add_mod, h0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hF2, hF3]
  exact unpack4_top _ s F h1 h2 h3 hF hb

theorem floatUnpackExact_proven : FloatUnpackExact :=
  ⟨float_normal, float_sub, float_zero, float_top, fun _ => ⟨rfl, rfl⟩⟩

/-! ### `PyFloat_Pack4` on the doubles `PyFloat_Unpack4` returns -/

theorem roundShift_exact (q j : Nat) (hj : 0 < j) : roundShift (q * 2 ^ j) (j : Int) = q := by
  unfold roundShift
  rw [if_neg (by omega)]
  have e : (j : Int).toNat = j := by omega
  simp only [e, Nat.mul_div_cancel _ (Nat.two_pow_pos j), Nat.mul_mod_left]
  simp [Nat.ne_of_gt (Nat.two_pow_pos j), Nat.ne_of_lt (Nat.two_pow_pos j)]

theorem log2_mid (A : Nat) (hA : A < 2 ^ 52) : Nat.log2 (A + 2 ^ 52) = 52 :=
  log2_eq _ _ (Nat.le_add_left _ _) (by rw [Nat.pow_succ, Nat.mul_two]; exact Nat.add_lt_add_right hA _)

theorem arith_T (E F : Nat) (hE1 : 1 ≤ E) : (E - 1) * 2 ^ 23 + (F + 2 ^ 23) = E * 2 ^ 23 + F := by
  have : E = (E - 1) + 1 := by omega
  conv => rhs; rw [this, Nat.add_mul, Nat.one_mul]
  omega

theorem arith_lt (E F : Nat) (hE2 : E ≤ 254) (hF : F < 2 ^ 23) : ¬ (E * 2 ^ 23 + F ≥ 255 * 2 ^ 23) := by
  have h1 : E * 2 ^ 23 + F < (E + 1) * 2 ^ 23 := by rw [Nat.add_mul, Nat.one_mul]; omega
  have h2 : (E + 1) * 2 ^ 23 ≤ 255 * 2 ^ 23 := Nat.mul_le_mul_right _ (by omega)
  omega

theorem mul29_lt (F : Nat) (hF : F < 2 ^ 23) : F * 2 ^ 29 < 2 ^ 52 := by
  have : F * 2 ^ 29 < 2 ^ 23 * 2 ^ 29 := Nat.mul_lt_mul_of_pos_right hF (Nat.two_pow_pos _)
  exact Nat.lt_of_lt_of_le this (by decide)

/-- `encodeRounded` into binary32 of a binary64 value that is a normal single: exact. -/
theorem enc32_normal (s E F : Nat) (hE1 : 1 ≤ E) (hE2 : E ≤ 254) (hF : F < 2 ^ 23) :
    f32.encodeRounded s (F * 2 ^ 29 + 2 ^ 52) (((E + 896 : Nat) : Int) - 1023 - 52) =
      some (s * 2 ^ 31 + (E * 2 ^ 23 + F)) := by
  have hm : F * 2 ^ 29 + 2 ^ 52 = (F + 2 ^ 23) * 2 ^ 29 := by rw [Nat.add_mul, ← Nat.pow_add]
  have hl := log2_mid _ (mul29_lt F hF)
  have hm0 : F * 2 ^ 29 + 2 ^ 52 ≠ 0 := Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos 52) (Nat.le_add_left _ _))
  simp only [Fmt.encodeRounded, hm0, if_false, hl, f32_fracBits, f32_expBits, f32_bias, f32_expMax]
  have e1 : ¬ (((52 : Nat) : Int) + (((E + 896 : Nat) : Int) - 1023 - 52) < 1 - ((127 : Nat) : Int)) := by
    omega
  have e2 : ((52 : Nat) : Int) + (((E + 896 : Nat) : Int) - 1023 - 52) - ((23 : Nat) : Int) -
      (((E + 896 : Nat) : Int) - 1023 - 52) = ((29 : Nat) : Int) := by omega
  have e3 : (((52 : Nat) : Int) + (((E + 896 : Nat) : Int) - 1023 - 52) - (1 - ((127 : Nat) : Int))).toNat
      = E - 1 := by omega
  rw [if_neg e1, e2, e3, hm, roundShift_exact _ 29 (by decide), arith_T E F hE1, if_neg (arith_lt E F hE2 hF)]

/-- `encodeRounded` into binary32 of a binary64 value that is a subnormal single: exact. -/
theorem enc32_sub (s k r : Nat) (hk : k ≤ 22) (hr : r < 2 ^ k) :
    f32.encodeRounded s (r * 2 ^ (52 - k) + 2 ^ 52) (((k + 874 : Nat) : Int) - 1023 - 52) =
      some (s * 2 ^ 31 + (2 ^ k + r)) := by
  have hsplit := pow_split k (by omega)
  have hA : r * 2 ^ (52 - k) < 2 ^ 52 := by
    rw [← hsplit]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
  have hm : r * 2 ^ (52 - k) + 2 ^ 52 = (2 ^ k + r) * 2 ^ (52 - k) := by
    rw [← hsplit, ← Nat.add_mul, Nat.add_comm]
  have hl := log2_mid _ hA
  have hm0 : r * 2 ^ (52 - k) + 2 ^ 52 ≠ 0 :=
    Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.two_pow_pos 52) (Nat.le_add_left _ _))
  have hf : 2 ^ k + r < 2 ^ 23 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k + 1 ≤ 23 by omega)
    rw [Nat.pow_succ] at this
    omega
  simp only [Fmt.encodeRounded, hm0, if_false, hl, f32_fracBits, f32_expBits, f32_bias, f32_expMax]
  have e1 : ((52 : Nat) : Int) + (((k + 874 : Nat) : Int) - 1023 - 52) < 1 - ((127 : Nat) : Int) := by
    omega
  have e2 : 1 - ((127 : Nat) : Int) - ((23 : Nat) : Int) - (((k + 874 : Nat) : Int) - 1023 - 52) =
      ((52 - k : Nat) : Int) := by omega
  rw [if_pos e1, e2, hm, roundShift_exact _ (52 - k) (by omega)]
  have hlt : ¬ (2 ^ k + r ≥ 255 * 2 ^ 23) := by
    have : (2 : Nat) ^ 23 ≤ 255 * 2 ^ 23 := Nat.le_mul_of_pos_left _ (by decide)
    omega
  rw [if_neg hlt]

theorem c2f_finite (x : Nat) (hn : f64.isNaN x = false) (hi : f64.isInf x = false) :
    castDoubleToFloat x = (f32.encodeRounded (f64.sign x) (f64.mag x).1 (f64.mag x).2).getD
      (f32.infBits (f64.sign x)) := by
  unfold castDoubleToFloat
  simp only [hn, hi, Bool.false_eq_true, if_false]

theorem pack4_ok (x : Nat) (hn : f64.isNaN x = false)
    (hc : f32.isInf (castDoubleToFloat x) = false ∨ f64.isInf x = true) :
    pyFloatPack4Bits x = .ok (castDoubleToFloat x) := by
  unfold pyFloatPack4Bits
  rcases hc with hc | hc <;> simp [hc, hn]

theorem f32_isInf_of (y : Nat) (h : f32.expOf y ≠ 255) : f32.isInf y = false := by
  simp [Fmt.isInf, f32_expMax, h]

theorem f64_isNaN_of (x : Nat) (h : f64.expOf x ≠ 2047) : f64.isNaN x = false := by
  simp [Fmt.isNaN, f64_expMax, h]

theorem f64_isNaN_frac0 (x : Nat) (h : f64.frac x = 0) : f64.isNaN x = false := by
  simp [Fmt.isNaN, h]

theorem f64_isInf_top (x : Nat) (h2 : f64.expOf x = 2047) (h3 : f64.frac x = 0) : f64.isInf x = true := by
  simp [Fmt.isInf, f64_expMax, h2, h3]

theorem f64_isInf_of (x : Nat) (h : f64.expOf x ≠ 2047) : f64.isInf x = false := by
  simp [Fmt.isInf, f64_expMax, h]

theorem frt_normal (s E F : Nat) (hs : s < 2) (hE1 : 1 ≤ E) (hE2 : E ≤ 254) (hF : F < 2 ^ 23) :
    pyFloatPack4Bits (pyFloatUnpack4Bits (s * 2 ^ 31 + E * 2 ^ 23 + F)) = .ok (s * 2 ^ 31 + E * 2 ^ 23 + F) := by
  rw [float_normal s E F hs hE1 hE2 hF]
  have hA := mul29_lt F hF
  obtain ⟨h1, h2, h3⟩ := f64_fields s (E + 896) (F * 2 ^ 29) hs (by omega) hA
  have hx0 : f64.expOf (s * 2 ^ 63 + (E + 896) * 2 ^ 52 + F * 2 ^ 29) ≠ 0 := by rw [h2]; omega
  have hn := f64_isNaN_of _ (by rw [h2]; omega)
  have hi := f64_isInf_of _ (by rw [h2]; omega)
  have hc : castDoubleToFloat (s * 2 ^ 63 + (E + 896) * 2 ^ 52 + F * 2 ^ 29) = s * 2 ^ 31 + E * 2 ^ 23 + F := by
    rw [c2f_finite _ hn hi, f64_mag_normal _ hx0, h1, h2, h3]
    simp only
    rw [enc32_normal s E F hE1 hE2 hF, Option.getD_some, Nat.add_assoc]
  obtain ⟨_, g2, _⟩ := f32_fields s E F hs (by omega) hF
  rw [pack4_ok _ hn (Or.inl (by rw [hc]; exact f32_isInf_of _ (by rw [g2]; omega))), hc]

theorem frt_sub (s k r : Nat) (hs : s < 2) (hk : k < 23) (hr : r < 2 ^ k) :
    pyFloatPack4Bits (pyFloatUnpack4Bits (s * 2 ^ 31 + (2 ^ k + r))) = .ok (s * 2 ^ 31 + (2 ^ k + r)) := by
  rw [float_sub s k r hs hk hr]
  have hsplit := pow_split k (by omega)
  have hA : r * 2 ^ (52 - k) < 2 ^ 52 := by
    rw [← hsplit]; exact Nat.mul_lt_mul_of_pos_right hr (Nat.two_pow_pos _)
  obtain ⟨h1, h2, h3⟩ := f64_fields s (k + 874) (r * 2 ^ (52 - k)) hs (by omega) hA
  have hx0 : f64.expOf (s * 2 ^ 63 + (k + 874) * 2 ^ 52 + r * 2 ^ (52 - k)) ≠ 0 := by rw [h2]; omega
  have hn := f64_isNaN_of _ (by rw [h2]; omega)
  have hi := f64_isInf_of _ (by rw [h2]; omega)
  have hc : castDoubleToFloat (s * 2 ^ 63 + (k + 874) * 2 ^ 52 + r * 2 ^ (52 - k)) = s * 2 ^ 31 + (2 ^ k + r) := by
    rw [c2f_finite _ hn hi, f64_mag_normal _ hx0, h1, h2, h3]
    simp only
    rw [enc32_sub s k r (by omega) hr, Option.getD_some]
  have hf : 2 ^ k + r < 2 ^ 23 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show k + 1 ≤ 23 by omega)
    rw [Nat.pow_succ] at this
    omega
  obtain ⟨_, g2, _⟩ := f32_fields s 0 (2 ^ k + r) hs (by decide) hf
  rw [Nat.zero_mul, Nat.add_zero] at g2
  rw [pack4_ok _ hn (Or.inl (by rw [hc]; exact f32_isInf_of _ (by rw [g2]; omega))), hc]

theorem frt_zero (s : Nat) (hs : s < 2) :
    pyFloatPack4Bits (pyFloatUnpack4Bits (s * 2 ^ 31)) = .ok (s * 2 ^ 31) := by
  rw [float_zero s hs]
  obtain ⟨h1, h2, h3⟩ := f64_fields s 0 0 hs (by decide) (Nat.two_pow_pos _)
  simp only [Nat.zero_mul, Nat.add_zero] at h1 h2 h3
  have hn := f64_isNaN_of _ (by rw [h2]; omega)
  have hi := f64_isInf_of _ (by rw [h2]; omega)
  have hc : castDoubleToFloat (s * 2 ^ 63) = s * 2 ^ 31 := by
    rw [c2f_finite _ hn hi, f64_mag_sub _ h2, h1, h3]
    have : f32.encodeRounded s 0 (-1074) = some (s * 2 ^ 31) := by
      unfold Fmt.encodeRounded
      rw [if_pos rfl]
      rfl
    rw [this, Option.getD_some]
  obtain ⟨_, g2, _⟩ := f32_fields s 0 0 hs (by decide) (Nat.two_pow_pos _)
  simp only [Nat.zero_mul, Nat.add_zero] at g2
  rw [pack4_ok _ hn (Or.inl (by rw [hc]; exact f32_isInf_of _ (by rw [g2]; omega))), hc]

theorem c2f_inf (x : Nat) (hn : f64.isNaN x = false) (hi : f64.isInf x = true) :
    castDoubleToFloat x = f32.infBits (f64.sign x) := by
  unfold castDoubleToFloat
  simp only [hn, hi, Bool.false_eq_true, if_false, if_true]

theorem frt_inf (s : Nat) (hs : s < 2) :
    pyFloatPack4Bits (pyFloatUnpack4Bits (s * 2 ^ 31 + 255 * 2 ^ 23 + 0)) =
      .ok (s * 2 ^ 31 + 255 * 2 ^ 23 + 0) := by
  rw [float_top s 0 hs (Nat.two_pow_pos _), Nat.zero_mul, Nat.add_zero, Nat.add_zero]
  obtain ⟨h1, h2, h3⟩ := f64_fields s 2047 0 hs (by decide) (Nat.two_pow_pos _)
  rw [Nat.add_zero] at h1 h2 h3
  have hn := f64_isNaN_frac0 _ h3
  have hi := f64_isInf_top _ h2 h3
  rw [pack4_ok _ hn (Or.inr hi), c2f_inf _ hn hi, h1, f32_infBits_eq]

/-- Every single-precision pattern that is not a NaN survives `unpack('>f')` then `pack('>f')`. -/
theorem floatRoundTrip_proven : FloatRoundTrip := by
  intro y hy hnan
  have hs : y / 2 ^ 31 < 2 := by
    have : y < 2 * 2 ^ 31 := by simpa using hy
    exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact this)
  have hdec : y = y / 2 ^ 31 * 2 ^ 31 + y / 2 ^ 23 % 2 ^ 8 * 2 ^ 23 + y % 2 ^ 23 := by
    simp only [Nat.reducePow]; omega
  have hE : y / 2 ^ 23 % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hF : y % 2 ^ 23 < 2 ^ 23 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hnan' : ¬ (y / 2 ^ 23 % 2 ^ 8 = 255 ∧ y % 2 ^ 23 ≠ 0) := by
    intro ⟨a, b⟩
    have : f32.isNaN y = true := by
      simp [Fmt.isNaN, Fmt.expOf, Fmt.frac, f32_expMax, f32_fracBits, f32_expBits, a, b]
    rw [hnan] at this
    exact Bool.false_ne_true this
  generalize y / 2 ^ 31 = s at hs hdec
  generalize y / 2 ^ 23 % 2 ^ 8 = E at hE hdec hnan'
  generalize y % 2 ^ 23 = F at hF hdec hnan'
  subst hdec
  clear hy hnan
  have hE' : E < 256 := hE
  by_cases h255 : E = 255
  · subst h255
    have hf0 : F = 0 := by omega
    subst hf0
    exact frt_inf s hs
  by_cases he0 : E = 0
  · subst he0
    by_cases hf0 : F = 0
    · subst hf0
      rw [show s * 2 ^ 31 + 0 * 2 ^ 23 + 0 = s * 2 ^ 31 by simp]
      exact frt_zero s hs
    · have hk := Nat.lt_log2_self (n := F)
      have hk2 := Nat.log2_self_le hf0
      have hk23 : Nat.log2 F < 23 := (Nat.log2_lt hf0).2 hF
      generalize Nat.log2 F = k at hk hk2 hk23
      have hr : F - 2 ^ k < 2 ^ k := by rw [Nat.pow_succ] at hk; omega
      rw [show s * 2 ^ 31 + 0 * 2 ^ 23 + F = s * 2 ^ 31 + (2 ^ k + (F - 2 ^ k)) by
        rw [Nat.zero_mul, Nat.add_zero, Nat.add_sub_cancel' hk2]]
      exact frt_sub s k (F - 2 ^ k) hs hk23 hr
  · exact frt_normal s E F hs (by omega) (by omega) hF

/-! ### Where `PyFloat_Pack2` overflows -/

/-- `pack2Round` fails only through the carry out of the top exponent. -/
theorem pack2Round_err (sign fn fd e : Nat) (x : PyExc) (h : pack2Round sign fn fd e = .error x) :
    e + 1 = 31 ∧ x = ovfE := by
  unfold pack2Round at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | exact ⟨by assumption, by cases h; rfl⟩

/-- At the top exponent, `pack2Round` carries out, and so overflows, exactly when the fraction rounds to
`1024 / 1024`, which for `fn / 2^52` is from `2047 * 2^41` up. -/
theorem pack2Round_top (s F : Nat) (hF : F < 2 ^ 52) :
    pack2Round s F (2 ^ 52) 30 = .error ovfE ↔ 2047 * 2 ^ 41 ≤ F := by
  have hdec : F = F / 2 ^ 42 * 2 ^ 42 + F % 2 ^ 42 := (Nat.div_add_mod' F _).symm
  have hr : F % 2 ^ 42 < 2 ^ 42 := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h52 : (2 : Nat) ^ 52 = 1024 * 2 ^ 42 := by
    rw [show (1024 : Nat) = 2 ^ 10 from rfl, ← Nat.pow_add]
  have hq : F / 2 ^ 42 < 1024 := Nat.div_lt_of_lt_mul (by rw [← h52]; exact hF)
  generalize F / 2 ^ 42 = q at hdec hq
  generalize F % 2 ^ 42 = r at hdec hr
  subst hdec
  clear hF h52
  have p52 : (2 : Nat) ^ 52 = 2048 * 2 ^ 41 := by
    rw [show (2048 : Nat) = 2 ^ 11 from rfl, ← Nat.pow_add]
  have p42 : (2 : Nat) ^ 42 = 2 * 2 ^ 41 := by
    rw [show (2 : Nat) = 2 ^ 1 from rfl, ← Nat.pow_add]
  rw [p52, p42]
  rw [p42] at hr
  have hA : 0 < 2 ^ 41 := Nat.two_pow_pos _
  generalize 2 ^ 41 = A at hA hr ⊢
  have hnum : (q * (2 * A) + r) * 1024 = q * (2048 * A) + r * 1024 := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm (2 * A) 1024, ← Nat.mul_assoc 1024 2 A]
  have hb : (q * (2048 * A) + r * 1024) / (2048 * A) = q := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]
  unfold pack2Round
  simp only [hnum, hb, Nat.add_sub_cancel_left]
  by_cases hup : 2 * (r * 1024) > 2048 * A ∨ (2 * (r * 1024) = 2048 * A ∧ q % 2 = 1)
  · rw [if_pos hup, if_neg (by omega)]
    by_cases h1 : q + 1 = 1024
    · have hq' : q = 1023 := by omega
      subst hq'
      simp only [if_true, ovfE, true_iff]
      omega
    · rw [if_neg h1]
      simp only [reduceCtorEq, false_iff, Nat.not_le]
      have : q * (2 * A) ≤ 1022 * (2 * A) := Nat.mul_le_mul_right _ (by omega)
      omega
  · rw [if_neg hup, if_pos rfl]
    simp only [reduceCtorEq, false_iff, Nat.not_le]
    by_cases h1 : q = 1023
    · subst h1
      omega
    · have : q * (2 * A) ≤ 1022 * (2 * A) := Nat.mul_le_mul_right _ (by omega)
      omega

/-- `pack_halffloat` raises `OverflowError("float too large to pack with e format")` for exactly the
finite doubles whose magnitude is at least 65520, the halfway point between the largest half 65504 and
65536, which rounds to even and so up (`Objects/floatobject.c:1940-1942, 1964-1974`), and this is the
only exception it raises on a float. In bits: `0x40EFFE0000000000 <= |x| < 0x7FF0000000000000`.
Infinities pack to infinities. A pack that wrote `[0, 0]`, or overflowed at 65504 or at 65536, fails
this; with `HalfRoundTrip` it pins what `pack_halffloat` writes. The last part is the same boundary for
every `e` entry of the three tables, which `struct.pack` reaches for a `float` (an exact `int` has its
`OverflowError` replaced, `Modules/_struct.c:2402-2406`). -/
def HalfPackOverflow : Prop :=
  (∀ x : Nat, x < 2 ^ 64 → f64.isNaN x = false →
    (pyFloatPack2Bits x = .error ovfE ↔
      (0x40EFFE0000000000 ≤ x % 2 ^ 63 ∧ x % 2 ^ 63 < 0x7FF0000000000000)) ∧
    (∀ e, pyFloatPack2Bits x = .error e → e = ovfE)) ∧
  (∀ (t : Tab) (e : FormatDef), e ∈ t.table → e.format = ['e'] → ∀ x : Nat,
    runPack e (.float x) = (pyFloatPack2Bits x).map (ordered (t != .big) 2))

theorem halfEntry_tables : ∀ t : Tab, ∀ e ∈ t.table, e.format = ['e'] →
    (if t = .big then e.pack = .bpHalffloat else e.pack = .npHalffloat ∨ e.pack = .lpHalffloat) := by
  intro t
  cases t <;> decide +kernel

theorem pack2_fields (x : Nat) (hx : x < 2 ^ 64) :
    x = x / 2 ^ 63 * 2 ^ 63 + x / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 + x % 2 ^ 52 ∧ x / 2 ^ 63 < 2 ∧
    x % 2 ^ 63 = x / 2 ^ 52 % 2 ^ 11 * 2 ^ 52 + x % 2 ^ 52 := by
  simp only [Nat.reducePow] at *
  omega

theorem bound_fields (E F : Nat) (hE : E < 2048) (hF : F < 2 ^ 52) :
    (0x40EFFE0000000000 ≤ E * 2 ^ 52 + F ∧ E * 2 ^ 52 + F < 0x7FF0000000000000) ↔
      ((1039 ≤ E ∧ E < 2047) ∨ (E = 1038 ∧ 2047 * 2 ^ 41 ≤ F)) := by
  simp only [Nat.reducePow] at *
  omega

/-- `PyFloat_Pack2` on a subnormal double: the `|x| < 2**-25` branch. -/
theorem pack2_subdouble (x : Nat) (h2 : f64.expOf x = 0) (h3 : f64.frac x ≠ 0) (hF : f64.frac x < 2 ^ 52) :
    pyFloatPack2Bits x = pack2Round (f64.sign x) 0 1 0 := by
  have hk : Nat.log2 (f64.frac x) < 52 := (Nat.log2_lt h3).2 hF
  have hn := f64_isNaN_of x (by rw [h2]; decide)
  have hi := f64_isInf_of x (by rw [h2]; decide)
  unfold pyFloatPack2Bits
  rw [f64_mag_sub x h2]
  simp only [h2, h3, and_false, if_false, hn, hi, Bool.false_eq_true]
  rw [if_neg (by omega), if_pos (by omega)]

theorem pack2_core (x : Nat) (hx : x < 2 ^ 64) (hn : f64.isNaN x = false) :
    (pyFloatPack2Bits x = .error ovfE ↔
      (0x40EFFE0000000000 ≤ x % 2 ^ 63 ∧ x % 2 ^ 63 < 0x7FF0000000000000)) ∧
    (∀ e, pyFloatPack2Bits x = .error e → e = ovfE) := by
  obtain ⟨hdec, hs, hmod⟩ := pack2_fields x hx
  have hE : x / 2 ^ 52 % 2 ^ 11 < 2048 := Nat.mod_lt _ (by decide)
  have hF : x % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [hmod, bound_fields _ _ hE hF]
  generalize x / 2 ^ 63 = s at hdec hs
  generalize x / 2 ^ 52 % 2 ^ 11 = E at hdec hE
  generalize x % 2 ^ 52 = F at hdec hF
  subst hdec
  clear hmod hx
  obtain ⟨h1, h2, h3⟩ := f64_fields s E F hs hE hF
  by_cases h2047 : E = 2047
  · subst h2047
    have hF0 : F = 0 := by
      have := hn
      simp only [f64_isNaN_eq, h2, h3, beq_self_eq_true, Bool.true_and, bne_eq_false_iff_eq] at this
      exact this
    subst hF0
    rw [pack2_top _ h2 h3]
    refine ⟨?_, fun e h => by cases h⟩
    simp only [reduceCtorEq, false_iff]
    omega
  by_cases h0 : E = 0
  · subst h0
    by_cases hF0 : F = 0
    · subst hF0
      rw [pack2_zero _ h2 h3]
      refine ⟨?_, fun e h => by cases h⟩
      simp only [reduceCtorEq, false_iff]
      omega
    · rw [pack2_subdouble _ h2 (by rw [h3]; exact hF0) (by rw [h3]; exact hF), h1]
      refine ⟨?_, fun e h => (pack2Round_err _ _ _ _ _ h).2⟩
      constructor
      · intro h; exact absurd (pack2Round_err _ _ _ _ _ h).1 (by decide)
      · intro h; omega
  · rw [pack2_normal s E F hs (by omega) (by omega) hF]
    by_cases hbig : (E : Int) - 1023 ≥ 16
    · rw [if_pos hbig]
      refine ⟨⟨fun _ => by omega, fun _ => rfl⟩, fun e h => by cases h; rfl⟩
    rw [if_neg hbig]
    by_cases hlow : (E : Int) - 1023 < -25
    · rw [if_pos hlow]
      refine ⟨⟨fun h => absurd (pack2Round_err _ _ _ _ _ h).1 (by decide), fun _ => by omega⟩,
        fun e h => (pack2Round_err _ _ _ _ _ h).2⟩
    rw [if_neg hlow]
    by_cases hsub : (E : Int) - 1023 < -14
    · rw [if_pos hsub]
      refine ⟨⟨fun h => absurd (pack2Round_err _ _ _ _ _ h).1 (by decide), fun _ => by omega⟩,
        fun e h => (pack2Round_err _ _ _ _ _ h).2⟩
    rw [if_neg hsub]
    refine ⟨?_, fun e h => (pack2Round_err _ _ _ _ _ h).2⟩
    by_cases h1038 : E = 1038
    · subst h1038
      rw [show (((1038 : Nat) : Int) - 1023 + 15).toNat = 30 by decide, pack2Round_top s F hF]
      constructor
      · intro h; exact Or.inr ⟨rfl, h⟩
      · intro h; rcases h with h | h
        · omega
        · exact h.2
    · constructor
      · intro h
        have := (pack2Round_err _ _ _ _ _ h).1
        omega
      · intro h; omega

theorem halfPackOverflow_proven : HalfPackOverflow := by
  refine ⟨pack2_core, fun t e he hfm x => ?_⟩
  have hp := halfEntry_tables t e he hfm
  have hcase : ∀ le : Bool, packHalffloat (.float x) le = (pyFloatPack2Bits x).map (ordered le 2) := by
    intro le
    simp only [packHalffloat, asDouble]
    cases pyFloatPack2Bits x <;> rfl
  cases t with
  | big => simp only [if_true] at hp; simp only [runPack, hp]; exact hcase false
  | native =>
    simp only [reduceCtorEq, if_false] at hp
    rcases hp with hp | hp <;> simp only [runPack, hp] <;> exact hcase true
  | little =>
    simp only [reduceCtorEq, if_false] at hp
    rcases hp with hp | hp <;> simp only [runPack, hp] <;> exact hcase true

/-! ### `PyFloat_Unpack8` and `PyFloat_Pack8` -/

theorem leBytes_leVal : ∀ p : List Nat, (∀ b ∈ p, b < 256) → leBytes p.length (leVal p) = p
  | [], _ => rfl
  | b :: bs, h => by
    have hb : b < 256 := h b (by simp)
    have ih := leBytes_leVal bs (fun c hc => h c (by simp [hc]))
    simp only [List.length_cons, leBytes, leVal]
    have e1 : (b + 256 * leVal bs) % 256 = b := by omega
    have e2 : (b + 256 * leVal bs) / 256 = leVal bs := by omega
    rw [e1, e2, ih]

/-- `unpack_double` returns the 8-byte pattern itself, signalling NaNs included, read in the table's
byte order (`PyFloat_Unpack8`, `Objects/floatobject.c:2204-2223`, a `memcpy`), and packing that float
writes the same 8 bytes back (`PyFloat_Pack8`, 2069-2087), for every buffer and every `d` entry of the
three tables. A constant decoder, or one that read the bytes in the other order, fails this. -/
def DoubleBytes : Prop :=
  ∀ (t : Tab) (e : FormatDef), e ∈ t.table → e.format = ['d'] →
    ∀ p : List Nat, p.length = 8 → (∀ b ∈ p, b < 256) →
      runUnpack e p = .ok (.float (if t = .big then beVal p else leVal p)) ∧
      runPack e (.float (if t = .big then beVal p else leVal p)) = .ok p

theorem double_tables : ∀ t : Tab, ∀ e ∈ t.table, e.format = ['d'] →
    e.size = 8 ∧ (if t = .big then e.unpack = .buDouble ∧ e.pack = .bpDouble
      else e.unpack = .nuDouble ∧ e.pack = .npDouble) := by
  intro t
  cases t <;> decide +kernel

theorem doubleBytes_proven : DoubleBytes := by
  intro t e he hfm p hl hb
  obtain ⟨hs, hc⟩ := double_tables t e he hfm
  have hle : leBytes 8 (leVal p) = p := by rw [← hl]; exact leBytes_leVal p hb
  have hbe : (leBytes 8 (beVal p)).reverse = p := by
    have hrb : ∀ b ∈ p.reverse, b < 256 := fun b h => hb b (List.mem_reverse.1 h)
    have h1 : leVal p.reverse = beVal p := by
      rw [leVal_eq_beVal_reverse, List.reverse_reverse]
    have h2 := leBytes_leVal p.reverse hrb
    rw [List.length_reverse, hl, h1] at h2
    rw [h2, List.reverse_reverse]
  have htake : p.take 8 = p := List.take_of_length_le (by omega)
  cases t with
  | big =>
    simp only [if_true] at hc ⊢
    obtain ⟨hu, hp⟩ := hc
    refine ⟨by simp only [runUnpack, hu, hs, htake], ?_⟩
    simp only [runPack, hp, packDoubleStd, asDouble, ordered, Bool.false_eq_true, if_false, hbe]
  | native =>
    simp only [reduceCtorEq, if_false] at hc ⊢
    obtain ⟨hu, hp⟩ := hc
    refine ⟨by simp only [runUnpack, hu, hs, htake], ?_⟩
    simp only [runPack, hp, packDoubleStd, asDouble, ordered, if_true, hle]
  | little =>
    simp only [reduceCtorEq, if_false] at hc ⊢
    obtain ⟨hu, hp⟩ := hc
    refine ⟨by simp only [runUnpack, hu, hs, htake], ?_⟩
    simp only [runPack, hp, packDoubleStd, asDouble, ordered, if_true, hle]

end PyLean.TextLibs.Struct
