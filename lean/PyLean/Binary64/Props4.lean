import PyLean.Binary64.Props3

/-!
Refutations in the decimal and hexadecimal paths, and the pack/unpack routines.
-/

namespace PyLean.Binary64

open F64

/-! ## Precision near `INT_MAX` -/

/-- Rounding a float of magnitude at least one to `ndigits ≥ 0` places keeps its integer
part, so the decimal point of the result is to the right of the first digit. -/
def DtoaFixedKeepsIntegerPart : Prop :=
  ∀ (x : F64) (ndigits : Int), x.isFinite = true → 1 ≤ Rat.abs x.toRat →
    0 ≤ ndigits → ndigits ≤ 2147483647 →
    ((_Py_dg_dtoa x 3 ndigits).map (·.decpt)).all (1 ≤ ·) = true

/-- `format(123.456, '.2147483647f')`: `ndigits + k + 1` wraps at dtoa.c:2389. -/
theorem dtoaFixedKeepsIntegerPart_refuted : ¬ DtoaFixedKeepsIntegerPart := by
  intro h
  have := h (ofBits 0x405edd2f1a9fbe77) 2147483647 (by decide +kernel) (by decide +kernel)
    (by decide) (by decide)
  revert this
  decide +kernel

/-- Digits before the exponent marker. -/
def mantissaDigits : List Piece → Nat
  | [] => 0
  | .zeros n :: ps => n + mantissaDigits ps
  | .chars c :: ps =>
    let pre := c.takeWhile (fun ch => ch != 101 && ch != 69)
    (pre.filter isDigit).length + (if pre.length == c.length then mantissaDigits ps else 0)

/-- `'%.{p}e' % x` has `p + 1` significant digits, for every `p` the format parsers
accept. -/
def EFormatDigitCount : Prop :=
  ∀ (x : F64) (p : Nat), x.isFinite = true → p ≤ 2147483647 →
    (PyOS_double_to_string x 101 p {}).map (fun r => mantissaDigits r.1) = some (p + 1)

/-- `format(1.5, '.2147483647e')` is `'2e+00'`: `precision++` wraps at pystrtod.c:1263. -/
theorem eFormatDigitCount_refuted : ¬ EFormatDigitCount := by
  intro h
  have := h (ofBits 0x3ff8000000000000) 2147483647 (by decide +kernel) (by decide)
  revert this
  decide +kernel

/-! ## `float.fromhex` -/

/-- No valid hexadecimal float ends in `x`, so `float.fromhex` must raise `ValueError` for
every string that does. -/
def FromhexRejectsTrailingGarbage : Prop :=
  ∀ s : List Nat, float_fromhex (s ++ [120]) = hexParseError

/-- `float.fromhex('1p2000x')` raises `OverflowError`: `hexValue` overflows before
`finished:` looks at the rest of the string. -/
theorem fromhexRejectsTrailingGarbage_refuted : ¬ FromhexRejectsTrailingGarbage := by
  intro h
  have := h [49, 112, 50, 48, 48, 48]
  revert this
  decide +kernel

/-! ## `float.hex` -/

theorem lt_d0_of_neg {x : F64} (hx : x.isFinite = true) (hs : x.sign = true) (hz : x.isZero = false) :
    F64.lt x d0 = true := by
  rw [lt_of_finite hx d0_isFinite, d0_toRat, toRat_of_finite hx, hs]
  have hm := mant_pos_of_not_zero hz
  have hxv : 0 < (x.mant : Rat) * pw x.lsbExp := Rat.mul_pos (natCast_pos' hm) (pw_pos _)
  simp only [↓reduceIte, decide_eq_true_eq]
  grind

theorem not_lt_d0_of_pos {x : F64} (hx : x.isFinite = true) (hs : x.sign = false) :
    F64.lt x d0 = false := by
  rw [lt_of_finite hx d0_isFinite, d0_toRat, toRat_of_finite hx, hs]
  have := mantVal_nonneg x
  have h : ¬ (x.mant : Rat) * pw x.lsbExp < 0 := by grind
  simp [h]

/-- `(-x).hex()` is `'-' + x.hex()` for a positive finite `x`, and only the sign differs. -/
def FloatHexSign : Prop :=
  ∀ x : F64, x.isFinite = true → x.isZero = false → x.sign = false →
    float_hex x.neg = "-" ++ float_hex x

theorem floatHexSign_proven : FloatHexSign := by
  intro x hx hz hs
  have hfn : x.neg.isFinite = true := by rw [neg_isFinite]; exact hx
  have hzn : x.neg.isZero = false := by rw [neg_isZero]; exact hz
  have hsn : x.neg.sign = true := by rw [(neg_fields x).1, hs]; rfl
  have habs : x.neg.abs = x := by
    simp [F64.abs, hsn, neg_neg]
  have habs2 : x.abs = x := by simp [F64.abs, hs]
  unfold float_hex
  simp only [isNaN_false_of_finite hfn, isInf_false_of_finite hfn, isNaN_false_of_finite hx,
    isInf_false_of_finite hx, eq_d0_of_not_zero hfn hzn, eq_d0_of_not_zero hx hz, habs, habs2,
    lt_d0_of_neg hfn hsn hzn, not_lt_d0_of_pos hx hs]
  rfl

/-! ## Pack and unpack -/

theorem byte_layout8 (v : Nat) (h : v < 2 ^ 64) (le : Bool) : unlayout (layout 8 v le) le = v := by
  cases le <;> simp [unlayout, layout, List.range, List.range.loop] <;> omega

/-- `struct.pack('d', x)` round-trips every bit pattern, in both byte orders. -/
def Pack8RoundTrip : Prop :=
  ∀ (x : F64) (le : Bool), ∃ b, PyFloat_Pack8 x le = .ok b ∧ PyFloat_Unpack8 b le = x

theorem pack8RoundTrip_proven : Pack8RoundTrip := by
  intro x le
  refine ⟨layout 8 x.bits le, rfl, ?_⟩
  unfold PyFloat_Unpack8
  rw [byte_layout8 _ x.isLt, ofBits_bits]

end PyLean.Binary64
