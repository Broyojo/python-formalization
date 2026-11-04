import PyLean.Binary64.ComplexProps
import PyLean.Binary64.FloatArith
import PyLean.Binary64.FloatPow

/-!
Exact statements about the float paths of `Objects/complexobject.c` (CPython 3.15.2).

Each part of a complex result is pinned by an IEEE 754 relation that fixes it bit for bit,
except for which NaN: `AddSpec`, `MulSpec`, `DivSpec` and `NegSpec` say what IEEE 754 requires
of `x + y`, `x * y`, `x / y` and `-x`, signs of zeros and of overflowed infinities included.
They are stated from the standard, not from `F64.add` and friends, and `add_spec`,
`mul_spec`, `div_spec` and `neg_spec` show the model's operations meet them.
-/

namespace PyLean.Binary64

open F64

/-! ## IEEE 754 operations as relations -/

/-- `r` is the IEEE 754 sum `x + y` (round to nearest even): a NaN operand or infinities of
opposite signs give a NaN, an infinity otherwise wins, and finite operands give the exact sum
rounded, with the sign of the exact sum (so an overflow keeps it), and an exact zero sum is
`-0.0` only when both operands are negative (IEEE 754 §6.3). With `IsRounding`, these fix `r`
bit for bit except for which NaN. -/
structure AddSpec (x y r : F64) : Prop where
  nan : (x.isNaN || y.isNaN) = true → r.isNaN = true
  infOpp : x.isInf = true → y.isInf = true → x.sign ≠ y.sign → r.isNaN = true
  infL : x.isInf = true → y.isNaN = false → (y.isInf = true → x.sign = y.sign) → r = x
  infR : x.isFinite = true → y.isInf = true → r = y
  round : x.isFinite = true → y.isFinite = true → IsRounding (x.toRat + y.toRat) r
  sign : x.isFinite = true → y.isFinite = true → x.toRat + y.toRat ≠ 0 →
    r.sign = decide (x.toRat + y.toRat < 0)
  zero : x.isFinite = true → y.isFinite = true → x.toRat + y.toRat = 0 →
    r = F64.zero (x.sign && y.sign)

/-- IEEE 754 §5.4.1 defines `x - y` as `x + (-y)`. -/
def SubSpec (x y r : F64) : Prop := AddSpec x y.neg r

/-- `r` is the IEEE 754 product `x * y`: NaN for a NaN operand and for an infinity times a
zero, otherwise an infinity times anything is the infinity with the exclusive or of the signs,
and finite operands give the exact product rounded, with that sign whether or not it is zero
or overflows. -/
structure MulSpec (x y r : F64) : Prop where
  nan : (x.isNaN || y.isNaN) = true → r.isNaN = true
  infZero : (x.isInf && y.isZero || x.isZero && y.isInf) = true → r.isNaN = true
  inf : (x.isInf || y.isInf) = true → x.isNaN = false → y.isNaN = false → x.isZero = false →
    y.isZero = false → r = F64.inf (x.sign != y.sign)
  round : x.isFinite = true → y.isFinite = true → IsRounding (x.toRat * y.toRat) r
  sign : x.isFinite = true → y.isFinite = true → r.sign = (x.sign != y.sign)

/-- `r` is the IEEE 754 quotient `x / y` for a divisor that is not a zero (`complexobject.c`
tests for zero divisors itself): NaN for a NaN operand or two infinities, an infinite dividend
gives the signed infinity, an infinite divisor the signed zero, and finite operands the exact
quotient rounded, with the exclusive or of the signs. -/
structure DivSpec (x y r : F64) : Prop where
  nan : (x.isNaN || y.isNaN) = true → r.isNaN = true
  infInf : x.isInf = true → y.isInf = true → r.isNaN = true
  infL : x.isInf = true → y.isFinite = true → r = F64.inf (x.sign != y.sign)
  infR : x.isFinite = true → y.isInf = true → r = F64.zero (x.sign != y.sign)
  round : x.isFinite = true → y.isFinite = true → IsRounding (x.toRat / y.toRat) r
  sign : x.isFinite = true → y.isFinite = true → r.sign = (x.sign != y.sign)

/-- `r` is `-x`: the sign bit flipped and nothing else, NaNs included (IEEE 754 §5.5.1). -/
def NegSpec (x r : F64) : Prop := r.sign = !x.sign ∧ r.abs = x.abs

theorem add_spec (x y : F64) : AddSpec x y (F64.add x y) := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := addIEEE x y
  refine ⟨a1, a2, a3, a4, fun hx hy => (a5 hx hy).1, fun hx hy hq => ?_, fun hx hy hq => ?_⟩
  · rw [add_of_finite hx hy, if_neg hq]
    exact MathInt.ofRat_sign hq
  · rw [add_of_finite hx hy, if_pos hq]

theorem mul_spec (x y : F64) : MulSpec x y (F64.mul x y) := by
  obtain ⟨_, m⟩ := floatMulSpec_proven
  obtain ⟨m1, m2, m3, m4⟩ := m x y
  simp only [float_mul_floats] at m1 m2 m3 m4
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 h3 h4 h5 => ?_, fun hx hy => ?_, fun hx hy => ?_⟩
  · obtain ⟨z, hz, hn⟩ := m1 h; cases hz; exact hn
  · obtain ⟨z, hz, hn⟩ := m2 h; cases hz; exact hn
  · exact Option.some.inj (Except.ok.inj (m3 h1 h2 h3 h4 h5))
  · obtain ⟨z, hz, hr, _⟩ := m4 hx hy; cases hz; exact hr
  · obtain ⟨z, hz, _, hs⟩ := m4 hx hy; cases hz; exact hs

theorem div_spec (x y : F64) (hy : y.isZero = false) : DivSpec x y (F64.div x y) := by
  obtain ⟨_, d⟩ := floatDivSpec_proven
  obtain ⟨_, d2, d3, d4, d5, d6⟩ := d x y
  have hne : F64.eq y d0 = false := eq_d0_of_nonzero_any hy
  have hf : float_div (.float x) (.float y) = .ok (some (F64.div x y)) := by
    rw [float_div_floats, hne]; rfl
  rw [hf] at d2 d3 d4 d5 d6
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_,
    fun h1 h2 => ?_⟩
  · obtain ⟨z, hz, hn⟩ := d2 hy h; cases hz; exact hn
  · obtain ⟨z, hz, hn⟩ := d3 h1 h2; cases hz; exact hn
  · exact Option.some.inj (Except.ok.inj (d4 h1 h2 hy))
  · exact Option.some.inj (Except.ok.inj (d5 h1 h2))
  · obtain ⟨z, hz, hr, _⟩ := d6 h1 h2 hy; cases hz; exact hr
  · obtain ⟨z, hz, _, hs⟩ := d6 h1 h2 hy; cases hz; exact hs

theorem neg_spec (x : F64) : NegSpec x x.neg := by
  have h1 := (neg_fields x).1
  refine ⟨h1, ?_⟩
  unfold F64.abs
  rw [h1]
  cases hs : x.sign
  · simp [neg_neg]
  · simp

/-! ## Sums, differences, negation, conjugation -/

/-- Each part of `_Py_c_sum` and `_Py_c_diff` is the IEEE 754 operation on the matching parts,
for every pair of complex numbers, so `-0.0 + -0.0` is `-0.0` and `inf + 1` is `inf` in each
part. The mixed forms of complexobject.c:681-694 combine a float with the real part only and
keep the complex operand's imaginary part bit for bit, so a `-0.0` or a NaN there survives;
`_Py_rc_diff` negates it. `_Py_rc_sum(x, a)` is `a.real + x`, the operand order of `:51`. -/
def ComplexSumDiffExact : Prop :=
  ∀ (a b : C) (x : F64),
    AddSpec a.re b.re (_Py_c_sum a b).re ∧ AddSpec a.im b.im (_Py_c_sum a b).im ∧
    SubSpec a.re b.re (_Py_c_diff a b).re ∧ SubSpec a.im b.im (_Py_c_diff a b).im ∧
    AddSpec a.re x (_Py_cr_sum a x).re ∧ (_Py_cr_sum a x).im = a.im ∧
    AddSpec a.re x (_Py_rc_sum x a).re ∧ (_Py_rc_sum x a).im = a.im ∧
    SubSpec a.re x (_Py_cr_diff a x).re ∧ (_Py_cr_diff a x).im = a.im ∧
    SubSpec x a.re (_Py_rc_diff x a).re ∧ NegSpec a.im (_Py_rc_diff x a).im

theorem complexSumDiffExact_proven : ComplexSumDiffExact := by
  intro a b x
  exact ⟨add_spec _ _, add_spec _ _, add_spec _ _, add_spec _ _, add_spec _ _, rfl, add_spec _ _,
    rfl, add_spec _ _, rfl, add_spec _ _, neg_spec _⟩

/-- `-z` flips the sign bit of both parts, NaNs included, and nothing else; `z.conjugate()`
keeps the real part bit for bit and flips the sign bit of the imaginary part. `complex_neg`
(complexobject.c:776-783) negates on its own, not through `_Py_c_neg` (:81-87). -/
def ComplexNegConjExact : Prop :=
  ∀ a : C,
    NegSpec a.re (_Py_c_neg a).re ∧ NegSpec a.im (_Py_c_neg a).im ∧
    NegSpec a.re (complex_neg a).re ∧ NegSpec a.im (complex_neg a).im ∧
    (complex_conjugate a).re = a.re ∧ NegSpec a.im (complex_conjugate a).im

theorem complexNegConjExact_proven : ComplexNegConjExact := fun a =>
  ⟨neg_spec _, neg_spec _, neg_spec _, neg_spec _, rfl, neg_spec _⟩

/-! ## Mixed products and quotients -/

/-- `_Py_cr_prod(a, x)` and `_Py_rc_prod(x, a)` multiply each part of `a` by the float `x`,
each an IEEE 754 product, so `2.0 * complex(inf, 0.0)` is `inf+0j` where the complex product
would make the imaginary part a NaN. -/
def ComplexMixedProdExact : Prop :=
  ∀ (a : C) (x : F64),
    MulSpec a.re x (_Py_cr_prod a x).re ∧ MulSpec a.im x (_Py_cr_prod a x).im ∧
    MulSpec a.re x (_Py_rc_prod x a).re ∧ MulSpec a.im x (_Py_rc_prod x a).im

theorem complexMixedProdExact_proven : ComplexMixedProdExact := fun _ _ =>
  ⟨mul_spec _ _, mul_spec _ _, mul_spec _ _, mul_spec _ _⟩

/-- `_Py_cr_quot(a, x)`, complexobject.c:249-261: a zero `x` of either sign sets `EDOM` and
gives `0`; any other `x`, a NaN included (`if (b)` is `b != 0`), divides each part, an IEEE
754 quotient, and leaves `errno` alone. -/
def ComplexCrQuotExact : Prop :=
  ∀ (a : C) (x : F64),
    (x.isZero = true → _Py_cr_quot a x = (⟨d0, d0⟩, true)) ∧
    (x.isZero = false → (_Py_cr_quot a x).2 = false ∧
      DivSpec a.re x (_Py_cr_quot a x).1.re ∧ DivSpec a.im x (_Py_cr_quot a x).1.im)

theorem complexCrQuotExact_proven : ComplexCrQuotExact := by
  intro a x
  refine ⟨fun h => by simp [_Py_cr_quot, h], fun h => ?_⟩
  have e : _Py_cr_quot a x = (⟨fdiv a.re x, fdiv a.im x⟩, false) := by simp [_Py_cr_quot, h]
  rw [e]
  exact ⟨rfl, div_spec _ _ h, div_spec _ _ h⟩

/-! ## Real operands -/

/-- `real_to_double` and `real_to_complex`, complexobject.c:661-679, on every object: a
`float` or `float` subclass instance gives its value, an `int` its value rounded to nearest
even or `OverflowError` from `DBL_MAX + 2**970` on (`_Py_convert_int_to_double`,
floatobject.c:319-336), and anything else `NotImplemented`; `real_to_complex` adds a `+0.0`
imaginary part. `operandSpec` names the overflow threshold itself. -/
def ComplexRealOperandExact : Prop :=
  ∀ o : Obj,
    real_to_double o = operandSpec o ∧
    real_to_complex o = (operandSpec o).map (Option.map fun r => (⟨r, d0⟩ : C))

theorem complexRealOperandExact_proven : ComplexRealOperandExact := by
  intro o
  have h := convert_eq_spec o
  refine ⟨h, ?_⟩
  unfold real_to_complex real_to_double
  rw [h]
  cases o with
  | int n =>
    simp only [operandSpec]
    split <;> rfl
  | float x => rfl
  | floatSub _ x => rfl
  | other _ _ _ => rfl

end PyLean.Binary64
