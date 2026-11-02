import PyLean.Binary64.Props3

/-!
Refutations in the decimal and hexadecimal paths, and the pack/unpack routines.
-/

namespace PyLean.Binary64

open F64

/-! ## Precision near `INT_MAX` -/

/-- Rounding a float of magnitude at least one to `ndigits ≥ 0` places keeps its integer
part, so the decimal point of the result is to the right of the first digit. Refuted on
3.14.7 by `format(123.456, '.2147483647f')`, where `ndigits + k + 1` wrapped; open now. -/
def DtoaFixedKeepsIntegerPart : Prop :=
  ∀ (x : F64) (ndigits : Int), x.isFinite = true → 1 ≤ Rat.abs x.toRat →
    0 ≤ ndigits → ndigits ≤ 2147483647 →
    ((_Py_dg_dtoa x 3 ndigits).map (·.decpt)).all (1 ≤ ·) = true

/-- What 3.15's clamp gives: in mode 3, for every `ndigits` that fits an `int` and every
`k` a finite double can have (`-330 < k < 330`, the comment at dtoa.c:2380), `ndigits`
becomes the clamped value and `i = ndigits + k + 1` does not wrap. A positive `ndigits`
with `k >= 0`, which is `|x| >= 1`, leaves `ilim` positive. -/
def Mode3NoWrap : Prop :=
  ∀ ndigits k : Int, -(2 : Int) ^ 31 ≤ ndigits → ndigits < 2 ^ 31 → -330 < k → k < 330 →
    mode3Limits ndigits k =
      (clampNdigits ndigits + k + 1, clampNdigits ndigits + k, clampNdigits ndigits) ∧
    (0 ≤ ndigits → 0 ≤ k → 0 < (mode3Limits ndigits k).1)

theorem mode3NoWrap_proven : Mode3NoWrap := by
  intro ndigits k h1 h2 h3 h4
  have hc : -(2147483647 - 1024 : Int) ≤ clampNdigits ndigits ∧
      clampNdigits ndigits ≤ 2147483647 - 1024 ∧ (0 ≤ ndigits → 0 ≤ clampNdigits ndigits) := by
    unfold clampNdigits precisionMax
    by_cases c1 : ndigits > 2147483647 - 1024
    · simp only [if_pos c1]; omega
    · by_cases c2 : ndigits < -(2147483647 - 1024)
      · simp only [if_neg c1, if_pos c2]; omega
      · simp only [if_neg c1, if_neg c2]; omega
  have hw : ∀ n : Int, -(2 : Int) ^ 31 ≤ n → n < 2 ^ 31 → wrap32 n = n := by
    intro n h5 h6
    simp only [wrap32]
    omega
  have e : mode3Limits ndigits k =
      (clampNdigits ndigits + k + 1, clampNdigits ndigits + k, clampNdigits ndigits) := by
    simp only [mode3Limits]
    rw [hw (k + 1) (by omega) (by omega),
      hw (clampNdigits ndigits + (k + 1)) (by omega) (by omega),
      hw (clampNdigits ndigits + (k + 1) - 1) (by omega) (by omega)]
    simp only [Prod.mk.injEq, and_true]
    constructor <;> omega
  refine ⟨e, fun h5 h6 => ?_⟩
  rw [e]
  have := hc.2.2 h5
  simp only
  omega

/-- Digits before the exponent marker. -/
def mantissaDigits : List Piece → Nat
  | [] => 0
  | .zeros n :: ps => n + mantissaDigits ps
  | .chars c :: ps =>
    let pre := c.takeWhile (fun ch => ch != 101 && ch != 69)
    (pre.filter isDigit).length + (if pre.length == c.length then mantissaDigits ps else 0)

/-- `'%.{p}e' % x` has `p + 1` significant digits, for every `p` that
`PyOS_double_to_string` accepts. Refuted on 3.14.7 by `format(1.5, '.2147483647e')`,
which was `'2e+00'`; 3.15 refuses those `p`, and this statement is open for the rest. -/
def EFormatDigitCount : Prop :=
  ∀ (x : F64) (p : Nat), x.isFinite = true → (p : Int) ≤ precisionMax →
    (PyOS_double_to_string x 101 p {}).map (fun r => mantissaDigits r.1) = some (p + 1)

/-- The guard of `PyOS_double_to_string`: a precision beyond `INT_MAX - 1024` either way is
`ValueError`, for every value and format code, and `format_float_short` is never reached.
Any other precision goes on, and the `precision++` for `'e'` is exact. -/
def PrecisionGuard : Prop :=
  ∀ (x : F64) (code : Nat) (p : Int) (fl : DtsFlags),
    ((p > precisionMax ∨ p < -precisionMax) →
      PyOS_double_to_string_checked x code p fl = .error (.valueError "precision too big")) ∧
    (-precisionMax ≤ p → p ≤ precisionMax →
      PyOS_double_to_string_checked x code p fl = .ok (PyOS_double_to_string x code p fl) ∧
      PyOS_double_to_string_checked x 101 p fl = .ok (format_float_short x 101 2 (p + 1) fl false))

theorem precisionGuard_proven : PrecisionGuard := by
  intro x code p fl
  refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
  · simp only [PyOS_double_to_string_checked, if_pos h]
  · have hn : ¬ (p > precisionMax ∨ p < -precisionMax) := by omega
    have hw : wrap32 (p + 1) = p + 1 := by
      simp only [precisionMax] at h1 h2
      simp only [wrap32]
      omega
    refine ⟨by simp only [PyOS_double_to_string_checked, if_neg hn], ?_⟩
    simp [PyOS_double_to_string_checked, if_neg hn, PyOS_double_to_string, hw]

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
