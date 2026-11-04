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

/-! ## `_Py_c_pow` on a positive real base -/

theorem d1_toRat : d1.toRat = 1 := by decide +kernel

theorem d1_sign : d1.sign = false := by decide +kernel

theorem d0_sign : d0.sign = false := by decide +kernel

/-- `p * 1.0` is `p` for every non-NaN `p`. -/
theorem mul_d1 {p : F64} (hn : p.isNaN = false) : F64.mul p d1 = p := by
  obtain ⟨f1, f2, f3, f4, _⟩ := d1_facts
  rcases classify p with hf | hi | hnn
  · rw [mul_of_finite hf f3, d1_toRat, Rat.mul_one]
    split
    · rename_i h
      have hz := (isZero_iff_toRat hf).2 h
      rw [d1_sign, Bool.bne_false]
      exact (eq_zero_of_isZero hz).symm
    · rename_i h
      have hz : p.isZero = false := by
        cases hc : p.isZero
        · rfl
        · exact absurd (toRat_of_isZero hc) h
      exact ofRat_toRat hf hz
  · have : F64.mul p d1 = F64.inf (p.sign != d1.sign) := by
      simp [F64.mul, hn, f1, hi, f4]
    rw [this, d1_sign, Bool.bne_false]
    exact (eq_inf_of_isInf hi).symm
  · rw [hn] at hnn; cases hnn

/-- A finite `p` times a zero is the zero with the exclusive or of the signs. -/
theorem mul_zero_of_finite {p : F64} (hf : p.isFinite = true) (t : Bool) :
    F64.mul p (F64.zero t) = F64.zero (p.sign != t) := by
  rw [mul_of_finite hf (zero_isFinite t), zero_toRat, Rat.mul_zero, if_pos rfl, zero_sign]

/-- An infinite `p` times a zero is a NaN. -/
theorem mul_zero_of_inf {p : F64} (hi : p.isInf = true) (t : Bool) :
    (F64.mul p (F64.zero t)).isNaN = true := by
  have hn := not_nan_of_inf hi
  have hz := isNaN_false_of_finite (zero_isFinite t)
  simp [F64.mul, hn, hz, hi, zero_isZero, qnan_isNaN]

/-- The values a correct C library gives at the points `_Py_c_pow` reaches for a positive
real base, C99 Annex F: `hypot(x, ±0)` is `|x|` (F.10.4.3), `atan2(+0, x)` is `+0` for `x > 0`
(F.10.1.4), `cos(±0)` is `1` and `sin(±0)` is `±0` (F.10.1.5-6) with no domain error, and
`pow(x, y)` of a positive finite `x` and a finite `y` is not a NaN and not negative, with
`pow(+1, y) == 1` (F.10.4.4). -/
structure AnnexFPow (m : Libm) : Prop where
  hypot0 : ∀ x : F64, x.isFinite = true → x.sign = false → m.hypot x d0 = x
  atan2_0 : ∀ x : F64, x.isFinite = true → x.isZero = false → x.sign = false → m.atan2 d0 x = d0
  cos0 : ∀ t, m.cos (F64.zero t) = d1
  sin0 : ∀ t, m.sin (F64.zero t) = F64.zero t
  trig0 : ∀ t, m.trigEdom (F64.zero t) = false
  powPos : ∀ x y : F64, x.isFinite = true → x.isZero = false → x.sign = false → y.isFinite = true →
    (m.pow x y).isNaN = false ∧ (m.pow x y).sign = false
  pow1 : ∀ y, m.pow d1 y = d1

/-- `complex(x, 0) ** complex(y, ±0)` for a positive finite `x` and a finite nonzero `y` that
is not a small integer (so `complex_pow` takes `_Py_c_pow`, complexobject.c:759): the general
branch of `_Py_c_pow` (:325-336) gives `pow(x, y)` and a zero imaginary part with the sign of
`y` (the phase is `+0 * y`), and an infinite `pow(x, y)` is `ERANGE` from `_Py_ADJUST_ERANGE2`
(:336), so `OverflowError` (:766-769). That is `float.__pow__` on the same `x` and `y` with the
same C library (floatobject.c:686-803), up to the message: the twin of the float power. -/
def ComplexPowRealTwin : Prop :=
  ∀ m : Libm, AnnexFPow m → ∀ (x y : F64) (s : Bool),
    x.isFinite = true → x.isZero = false → x.sign = false → y.isFinite = true → y.isZero = false →
    (F64.eq y (F64.floor y) && F64.le y.abs (F64.ofInt 100)) = false →
    _Py_c_pow m ⟨x, d0⟩ ⟨y, F64.zero s⟩ =
      (if (m.pow x y).isInf then (⟨m.pow x y, F64.mul (m.pow x y) (F64.zero y.sign)⟩, .erange)
       else (⟨m.pow x y, F64.zero y.sign⟩, .none)) ∧
    complex_pow m (.complex ⟨x, d0⟩) (.complex ⟨y, F64.zero s⟩) =
      (if (m.pow x y).isInf then .error (.overflowError "complex exponentiation")
       else .ok (some ⟨m.pow x y, F64.zero y.sign⟩)) ∧
    floatPowCoreE (fun a b => (m.pow a b, 0)) x y =
      (if (m.pow x y).isInf then .error (errnoError ERANGE) else .ok (.float (m.pow x y)))

theorem complexPowRealTwin_proven : ComplexPowRealTwin := by
  intro m hm x y s hxf hxz hxs hyf hyz hsmall
  obtain ⟨pn, ps⟩ := hm.powPos x y hxf hxz hxs hyf
  have hb0 : (F64.eq y d0 && F64.eq (F64.zero s) d0) = false := by
    rw [eq_d0_of_nonzero_any hyz]; rfl
  have ha0 : (F64.eq x d0 && F64.eq d0 d0) = false := by
    rw [eq_d0_of_nonzero_any hxz]; rfl
  have hne : F64.ne (F64.zero s) d0 = false := by
    simp [F64.ne, eq_d0_of_zero (zero_isZero s)]
  have hphase : F64.mul d0 y = F64.zero y.sign := by
    have := mul_zero_of_finite hyf false
    rw [mul_of_finite d0_isFinite hyf, d0_toRat, Rat.zero_mul, if_pos rfl, d0_sign]
    simp
  have hcore : _Py_c_pow m ⟨x, d0⟩ ⟨y, F64.zero s⟩ =
      (if (m.pow x y).isInf then (⟨m.pow x y, F64.mul (m.pow x y) (F64.zero y.sign)⟩, .erange)
       else (⟨m.pow x y, F64.zero y.sign⟩, .none)) := by
    simp only [_Py_c_pow, hb0, ha0, Bool.false_eq_true, ite_false, hm.hypot0 x hxf hxs,
      hm.atan2_0 x hxf hxz hxs, hphase, hne, hm.cos0, hm.sin0, hm.trig0, mul_d1 pn]
    by_cases hi : (m.pow x y).isInf = true
    · simp [hi, adjustErange2]
    · have hi' : (m.pow x y).isInf = false := by simpa using hi
      have hpf : (m.pow x y).isFinite = true := by
        rcases classify (m.pow x y) with h | h | h
        · exact h
        · rw [hi'] at h; cases h
        · rw [pn] at h; cases h
      have hz : (F64.zero y.sign).isInf = false := isInf_false_of_finite (zero_isFinite _)
      simp only [fmul, mul_zero_of_finite hpf, ps, Bool.false_bne]
      simp [hi', adjustErange2, hz]
  refine ⟨hcore, ?_, ?_⟩
  · have hcond : (F64.eq (F64.zero s) d0 && F64.eq y (F64.floor y) &&
        F64.le y.abs (F64.ofInt 100)) = false := by
      rw [eq_d0_of_zero (zero_isZero s), Bool.true_and, hsmall]
    simp only [complex_pow, toComplex, bind, Except.bind, pure, Except.pure, hcond,
      Bool.false_eq_true, ite_false, hcore]
    by_cases hi : (m.pow x y).isInf = true <;> simp [hi]
  · have hpos := (powSpec_proven (fun a b => (m.pow a b, 0)) x y).2.2.2.2.2.2.2.2 hxf hxz hxs hyf hyz
    rw [hpos]
    by_cases h1 : x.toRat = 1
    · have hx1 : x = d1 := by
        have := ofRat_toRat hxf hxz
        rw [h1] at this
        rw [← this]; decide +kernel
      subst hx1
      rw [if_pos h1, hm.pow1]
      have : d1.isInf = false := by decide +kernel
      simp [this]
    · rw [if_neg h1]
      simp only [libmOutcome, ite_true]
      split <;> rfl

end PyLean.Binary64
