import PyLean.Binary64.Complex
import PyLean.Binary64.CompareProps
import PyLean.Binary64.DtoaProps

/-!
Properties of the float paths of `Objects/complexobject.c`, for any C library.
-/

namespace PyLean.Binary64

open F64

/-- Complex addition and subtraction work part by part with correctly rounded results, the
mixed forms leave the other part alone (so a signed zero there survives), and negation
and conjugation only touch signs. -/
def ComplexParts : Prop :=
  ∀ (a b : C) (r : F64),
    (a.re.isFinite = true → b.re.isFinite = true → IsRounding (a.re.toRat + b.re.toRat) (_Py_c_sum a b).re) ∧
    (a.im.isFinite = true → b.im.isFinite = true → IsRounding (a.im.toRat + b.im.toRat) (_Py_c_sum a b).im) ∧
    (a.re.isFinite = true → b.re.isFinite = true → IsRounding (a.re.toRat - b.re.toRat) (_Py_c_diff a b).re) ∧
    (a.im.isFinite = true → b.im.isFinite = true → IsRounding (a.im.toRat - b.im.toRat) (_Py_c_diff a b).im) ∧
    (_Py_cr_sum a r).im = a.im ∧ _Py_rc_sum r a = _Py_cr_sum a r ∧ (_Py_cr_diff a r).im = a.im ∧
    (_Py_rc_diff r a).im = a.im.neg ∧ _Py_c_neg (_Py_c_neg a) = a ∧ complex_neg a = _Py_c_neg a ∧
    complex_pos a = a ∧ complex_conjugate (complex_conjugate a) = a ∧
    complex_getnewargs a = (a.re, a.im) ∧ complex_complex a = a

theorem rounding_add {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    IsRounding (x.toRat + y.toRat) (F64.add x y) := by
  rw [add_of_finite hx hy]
  split
  · rename_i h; rw [h]; exact zero_isRounding _
  · exact ofRat_isRounding _

theorem rounding_sub {x y : F64} (hx : x.isFinite = true) (hy : y.isFinite = true) :
    IsRounding (x.toRat - y.toRat) (F64.sub x y) := by
  have hy' : y.neg.isFinite = true := by rw [neg_isFinite]; exact hy
  have := rounding_add hx hy'
  rw [toRat_neg] at this
  have e : x.toRat + -y.toRat = x.toRat - y.toRat := by grind
  rwa [e] at this

theorem complexParts_proven : ComplexParts := by
  intro a b r
  refine ⟨fun h1 h2 => rounding_add h1 h2, fun h1 h2 => rounding_add h1 h2,
    fun h1 h2 => rounding_sub h1 h2, fun h1 h2 => rounding_sub h1 h2, rfl, rfl, rfl, rfl, ?_, rfl, rfl,
    ?_, rfl, rfl⟩
  · simp [_Py_c_neg, neg_neg]
  · simp [complex_conjugate, neg_neg]

/-- `_Py_c_prod` only departs from the textbook formula when both parts of that formula
are NaN, and multiplication by a real scales both parts. -/
def ComplexProdShape : Prop :=
  ∀ (z w : C) (r : F64),
    (¬ ((F64.sub (F64.mul z.re w.re) (F64.mul z.im w.im)).isNaN = true ∧
        (F64.add (F64.mul z.re w.im) (F64.mul z.im w.re)).isNaN = true) →
      _Py_c_prod z w = ⟨F64.sub (F64.mul z.re w.re) (F64.mul z.im w.im),
        F64.add (F64.mul z.re w.im) (F64.mul z.im w.re)⟩) ∧
    _Py_cr_prod z r = ⟨F64.mul z.re r, F64.mul z.im r⟩ ∧ _Py_rc_prod r z = _Py_cr_prod z r

theorem complexProdShape_proven : ComplexProdShape := by
  intro z w r
  refine ⟨fun h => ?_, rfl, rfl⟩
  have hc : ((F64.sub (F64.mul z.re w.re) (F64.mul z.im w.im)).isNaN &&
      (F64.add (F64.mul z.re w.im) (F64.mul z.im w.re)).isNaN) = false := by
    simpa using h
  unfold _Py_c_prod
  simp only [hc, Bool.false_eq_true, ↓reduceIte]

theorem zero_cases {b : F64} (h : b.isZero = true) : b = zero false ∨ b = zero true := by
  rw [eq_zero_of_isZero h]
  cases b.sign <;> simp

/-- Division by a complex or real zero raises `ZeroDivisionError`, for every dividend. -/
def ComplexDivZero : Prop :=
  ∀ (a : C) (x : F64) (p q : Bool),
    (_Py_c_quot a ⟨zero p, zero q⟩).2 = true ∧ (_Py_rc_quot x ⟨zero p, zero q⟩).2 = true ∧
    (_Py_cr_quot a (zero p)).2 = true ∧
    complex_div (.complex a) (.complex ⟨zero p, zero q⟩) =
      .error (.zeroDivisionError "division by zero")

theorem zero_facts (p q : Bool) :
    F64.ge (absLt (zero p)) (absLt (zero q)) = true ∧ F64.eq (absLt (zero p)) d0 = true := by
  cases p <;> cases q <;> decide +kernel

theorem complexDivZero_proven : ComplexDivZero := by
  intro a x p q
  obtain ⟨h1, h2⟩ := zero_facts p q
  have e1 : (_Py_c_quot a ⟨zero p, zero q⟩).2 = true := by
    have d0n : d0.isNaN = false := by decide +kernel
    simp only [_Py_c_quot, h1, h2, ↓reduceIte, d0n, Bool.false_and, Bool.false_eq_true]
  refine ⟨e1, ?_, ?_, ?_⟩
  · have d0n : d0.isNaN = false := by decide +kernel
    simp only [_Py_rc_quot, h1, h2, ↓reduceIte, d0n, Bool.false_and, Bool.false_eq_true]
  · simp [_Py_cr_quot, zero_isZero]
  · simp only [complex_div, complexBinop, e1, ↓reduceIte]

/-- `abs(z)` follows C99 for infinities, and raises `OverflowError` exactly when `hypot` does
not give a finite result on finite parts, whatever `errno` held before. -/
def ComplexAbs : Prop :=
  ∀ (m : Libm) (stale : Bool) (z : C),
    (z.re.isInf = true → complex_abs m stale z = .ok z.re.abs) ∧
    (z.re.isInf = false → z.im.isInf = true → complex_abs m stale z = .ok z.im.abs) ∧
    (z.re.isFinite = true → z.im.isFinite = true →
      complex_abs m stale z = if (m.hypot z.re z.im).isFinite then .ok (m.hypot z.re z.im)
        else .error (.overflowError "absolute value too large"))

theorem complexAbs_proven : ComplexAbs := by
  intro m stale z
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h1 h2 => ?_⟩
  · have hf := not_finite_of_inf h
    simp [complex_abs, _Py_c_abs, hf, h]
  · have hf := not_finite_of_inf h2
    simp [complex_abs, _Py_c_abs, hf, h1, h2]
  · cases hr : (m.hypot z.re z.im).isFinite <;> simp [complex_abs, _Py_c_abs, h1, h2, hr]

/-- `abs` of a complex with a NaN part and no infinite part is a NaN, whatever `errno` held
before the call. -/
def ComplexAbsNaN : Prop :=
  ∀ (m : Libm) (stale : Bool) (z : C), z.re.isNaN = true → z.im.isFinite = true →
    complex_abs m stale z = .ok F64.qnan

/-- Refuted on 3.14.7, where `ERANGE` left over from an earlier overflow made
`abs(complex(nan, 1.0))` raise; `errno = 0` at complexobject.c:801 closes that. -/
theorem complexAbsNaN_proven : ComplexAbsNaN := by
  intro m stale z hn hf
  have hni : z.re.isInf = false := by
    rw [F64.isNaN_eq] at hn
    cases h : z.re.isInf
    · rfl
    · rw [F64.isInf_eq] at h; omega
  have h1 : z.re.isFinite = false := by
    rw [F64.isNaN_eq] at hn
    cases h : z.re.isFinite
    · rfl
    · rw [F64.isFinite_eq] at h; omega
  have h2 : z.im.isInf = false := F64.isInf_false_of_finite hf
  simp [complex_abs, _Py_c_abs, h1, hni, h2]

/-- `bool(z)` is false exactly when both parts are zero. -/
def ComplexBool : Prop :=
  ∀ z : C, complex_bool z = false ↔ z.re.isZero = true ∧ z.im.isZero = true

theorem float_bool_ne (x : F64) : F64.ne x d0 = false ↔ x.isZero = true := by
  have := (floatUnary_proven x).2.2.2.2.2.2.2
  exact this

theorem complexBool_proven : ComplexBool := by
  intro z
  unfold complex_bool
  rw [Bool.or_eq_false_iff, float_bool_ne, float_bool_ne]

/-- Complex comparison: order comparisons are `NotImplemented`, `==` with a float needs a
zero imaginary part, and with an int a zero imaginary part leaves the exact float-int
comparison. -/
def ComplexCompare : Prop :=
  ∀ (v : C) (x : F64) (n : Int),
    complex_richcompare v (.real (.float x)) .lt = none ∧
    complex_richcompare v (.real (.float x)) .eq = some (F64.eq v.re x && F64.eq v.im d0) ∧
    (F64.eq v.im d0 = true → v.re.isFinite = true →
      complex_richcompare v (.real (.int n)) .eq = some (exactCompare .eq v.re.toRat n)) ∧
    (F64.eq v.im d0 = false → complex_richcompare v (.real (.int n)) .eq = some false)

theorem complexCompare_proven : ComplexCompare := by
  intro v x n
  refine ⟨rfl, ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · simp [complex_richcompare]
  · simp only [complex_richcompare]
    simp only [h1, ↓reduceIte]
    exact (floatIntCompareExact_proven v.re n .eq).1 h2 |>.trans rfl
  · simp [complex_richcompare, h]

/-- `z ** 0` is `1` for every `z`, a zero base raises `ZeroDivisionError` for a negative or
complex exponent outside the small-integer path, and `_Py_c_pow` hands every other input
to the C library. -/
def ComplexPowSpecial : Prop :=
  ∀ (m : Libm) (a b : C),
    (∀ p q : Bool, c_powi a 0 = (⟨d1, d0⟩, false) ∧
      complex_pow m (.complex a) (.complex ⟨zero false, zero false⟩) = .ok (some ⟨d1, d0⟩)) ∧
    (F64.eq b.re d0 = true → F64.eq b.im d0 = true → _Py_c_pow m a b = (⟨d1, d0⟩, .none)) ∧
    (F64.eq a.re d0 = true → F64.eq a.im d0 = true →
      (F64.eq b.re d0 && F64.eq b.im d0) = false → F64.ne b.im d0 = true →
      _Py_c_pow m a b = (⟨d0, d0⟩, .edom))

theorem quot_one_one : _Py_c_quot c_1 c_1 = (⟨d1, d0⟩, false) := by decide +kernel

theorem c_powu_zero (a : C) : c_powu a 0 = c_1 := by
  unfold c_powu
  rw [show (64 : Nat) = 63 + 1 from rfl]
  simp [c_powuLoop]

theorem c_powi_zero (a : C) : c_powi a 0 = (⟨d1, d0⟩, false) := by
  have e : c_powi a 0 = _Py_c_quot c_1 (c_powu a 0) := by
    simp [c_powi]
  rw [e, c_powu_zero, quot_one_one]

theorem pow_zero_cond : ((F64.eq (zero false) d0 && F64.eq (zero false) (F64.floor (zero false))) &&
    F64.le (zero false).abs (F64.ofInt 100)) = true := by decide +kernel

theorem pow_zero_trunc : (zero false).truncInt = 0 := by decide +kernel

theorem pow_zero_adjust : adjustErange2 ⟨d1, d0⟩ .none = .none := by decide +kernel

theorem complex_pow_zero (m : Libm) (a : C) :
    complex_pow m (.complex a) (.complex ⟨zero false, zero false⟩) = .ok (some ⟨d1, d0⟩) := by
  unfold complex_pow
  simp only [toComplex, bind, Except.bind, pure, Except.pure]
  simp only [pow_zero_cond, pow_zero_trunc, c_powi_zero, ↓reduceIte, pow_zero_adjust,
    Bool.false_eq_true]

theorem complexPowSpecial_proven : ComplexPowSpecial := by
  intro m a b
  refine ⟨fun _ _ => ⟨c_powi_zero a, complex_pow_zero m a⟩, fun h1 h2 => ?_, fun h1 h2 h3 h4 => ?_⟩
  · simp [_Py_c_pow, h1, h2]
  · simp [_Py_c_pow, h1, h2, h3, h4]

/-- A real operand of a complex power or comparison is a complex with imaginary part `0.0`. -/
def ComplexRealOperand : Prop :=
  (∀ x : F64, real_to_double (.float x) = .ok (some x)) ∧
  (∀ x : F64, real_to_complex (.float x) = .ok (some ⟨x, d0⟩)) ∧
  (∀ n : Int, real_to_double (.int n) = convertToDouble (.int n))

theorem complexRealOperand_proven : ComplexRealOperand :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

/-- A nonzero base never gets `EDOM`, the error `complex_pow` reports as "zero to a negative
or complex power". -/
def ComplexPowEdomOnlyForZero : Prop :=
  ∀ (m : Libm) (a b : C), F64.ne a.re d0 = true → (_Py_c_pow m a b).2 ≠ .edom

/-- `(1+1j) ** complex(1, inf)` on a C library that follows POSIX: the phase is infinite and
`cos` sets `EDOM`. The other functions are placeholders with the right signs. -/
theorem complexPowEdomOnlyForZero_refuted : ¬ ComplexPowEdomOnlyForZero := by
  intro h
  let m : Libm := { hypot := fun _ _ => d1, pow := fun _ _ => d1, atan2 := fun _ _ => d1, exp := fun _ => d1,
                    log := fun _ => d1, cos := fun _ => d1, sin := fun _ => d1, trigEdom := F64.isInf }
  have := h m ⟨d1, d1⟩ ⟨d1, F64.inf false⟩ (by decide +kernel)
  exact this (by decide +kernel)

/-- `complex_repr` drops the parentheses and the real part for a positive zero real part. -/
def ComplexRepr : Prop :=
  ∀ y : F64, complex_repr ⟨zero false, y⟩ =
    (PyOS_double_to_string y 114 0 {}).map fun r => render r.1 ++ [106]

theorem complexRepr_proven : ComplexRepr := by
  intro y
  have h : (F64.eq (zero false) d0 && !(zero false).sign) = true := by decide +kernel
  simp [complex_repr, h]

/-- `complex()` of an empty string, or of one that is only spaces, raises `ValueError`. -/
def ComplexBlankRaises : Prop :=
  ∀ n : Nat, (complex_subtype_from_string (List.replicate n 32)).raises "ValueError"

theorem scan_blank (n : Nat) : ∀ (f i : Nat), i ≤ n → n + 1 ≤ i + f →
    scan (List.replicate n 32) isSpace f i = n := by
  intro f
  induction f with
  | zero => intro i h1 h2; omega
  | succ f ih =>
    intro i h1 h2
    unfold scan
    by_cases hi : i < n
    · have hs : isSpace 32 = true := by decide
      simp only [at_replicate hi, hs, ↓reduceIte]
      exact ih (i + 1) (by omega) (by omega)
    · have he : i = n := by omega
      subst he
      have h0 : at_ (List.replicate i 32) i = 0 := by simp [at_]
      have hs : isSpace 0 = false := by decide
      simp [h0, hs]

theorem complexBlankRaises_proven : ComplexBlankRaises := by
  intro n
  have h0 : at_ (List.replicate n 32) n = 0 := by simp [at_]
  have hs0 : scanFrom (List.replicate n 32) isSpace 0 = n := by
    unfold scanFrom
    exact scan_blank n _ 0 (by omega) (by simp)
  have ht : transformDecimalAndSpace (List.replicate n 32) = List.replicate n 32 := by
    unfold transformDecimalAndSpace
    have : (List.replicate n 32).all (· < 128) = true := by simp
    simp [this]
  have hd := strtodNoNumber_proven (List.replicate n 32) n (by rw [h0]; decide)
    (by rw [h0]; decide) (by rw [h0]; decide) (by rw [h0]; decide)
  have hp : _Py_parse_inf_or_nan (List.replicate n 32) n = (dm1, n) := by
    unfold _Py_parse_inf_or_nan
    simp [h0, case_insensitive_match, toLower]
  have hs1 : _PyOS_ascii_strtod (List.replicate n 32) n = some (dm1, n, false) := by
    simp [_PyOS_ascii_strtod, hd, hp]
  have hv : ∃ r, PyOS_string_to_double (List.replicate n 32) n true none = some (r, n) := by
    simp [PyOS_string_to_double, hs1]
  obtain ⟨r, hr⟩ := hv
  unfold complex_subtype_from_string
  rw [ht]
  unfold _Py_string_to_number_with_underscores
  simp only [blank_no_underscore n, Bool.not_false, ↓reduceIte, List.length_replicate]
  refine ⟨.valueError "complex() arg is a malformed string", ?_, rfl⟩
  unfold complex_from_string_inner
  simp [hs0, h0, hr, isSpace]

end PyLean.Binary64
