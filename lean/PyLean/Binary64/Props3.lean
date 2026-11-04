import PyLean.Binary64.Props2

/-!
`pow`, `hash`, the small methods of `Objects/floatobject.c`, and the refutations in the
decimal and hexadecimal paths.
-/

namespace PyLean.Binary64

open F64

theorem d1_facts : d1.isNaN = false ∧ d1.isInf = false ∧ d1.isFinite = true ∧ d1.isZero = false ∧
    F64.eq d1 d0 = false ∧ F64.lt d1 d0 = false ∧ d1.abs = d1 ∧ F64.eq d1 d1 = true := by
  decide +kernel

/-- `F64.eq` with a finite right operand: the left one is finite too, with equal value. -/
theorem eq_finite_right {x y : F64} (hy : y.isFinite = true) (h : F64.eq x y = true) :
    x.isFinite = true ∧ x.toRat = y.toRat := by
  have hnx : x.isNaN = false := by
    cases hn : x.isNaN
    · rfl
    · simp [F64.eq, hn] at h
  have hix : x.isInf = false := by
    cases hi : x.isInf
    · rfl
    · simp [F64.eq, hi, isNaN_false_of_finite hy, isInf_false_of_finite hy] at h
  have hfx : x.isFinite = true := by
    rcases classify x with h1 | h1 | h1
    · exact h1
    · rw [hix] at h1; cases h1
    · rw [hnx] at h1; cases h1
  rw [eq_of_finite hfx hy] at h
  exact ⟨hfx, by simpa using h⟩

theorem eq_d1_iff {x : F64} (h : F64.eq x d1 = true) : x = d1 := by
  obtain ⟨hf, hv⟩ := eq_finite_right d1_facts.2.2.1 h
  have hz : x.isZero = false := by
    cases hc : x.isZero
    · rfl
    · exfalso
      rw [toRat_of_isZero hc] at hv
      have : (0 : Rat) ≠ d1.toRat := by decide +kernel
      exact this hv
  exact toRat_inj hf d1_facts.2.2.1 hz hv

theorem pow_one_base (cpow : F64 → F64 → F64) (y : F64) :
    floatPowCore cpow d1 y = .ok (.float d1) := by
  obtain ⟨h1, h2, _, _, h5, h6, h7, h8⟩ := d1_facts
  simp only [floatPowCore, h1, h2, h5, h6, h7, h8]
  repeat' first | rfl | (split <;> try rfl)

/-- The special cases `float_pow` settles itself, for any C library `pow`: `x ** 0` and
`1 ** y` are `1`, even for NaNs, `nan ** y` is a NaN otherwise, `0.0 ** y` with a
finite negative `y` raises `ZeroDivisionError`, a negative base with a finite
non-integer exponent goes to `complex`, and two positive finite operands reach `pow`,
whose infinite result becomes `OverflowError`. -/
def PowSpecialValues : Prop :=
  ∀ (cpow : F64 → F64 → F64) (x y : F64),
    (y.isZero = true → floatPowCore cpow x y = .ok (.float d1)) ∧
    (F64.eq x d1 = true → floatPowCore cpow x y = .ok (.float d1)) ∧
    (x.isNaN = true → y.isZero = false → floatPowCore cpow x y = .ok (.float x)) ∧
    (x.isZero = true → y.isFinite = true → y.toRat < 0 →
      floatPowCore cpow x y = .error (.zeroDivisionError "zero to a negative power")) ∧
    (x.isFinite = true → x.toRat < 0 → y.isFinite = true → (¬ ∃ n : Int, y.toRat = n) →
      floatPowCore cpow x y = .ok (.complexPow x y)) ∧
    (x.isFinite = true → 0 < x.toRat → F64.eq x d1 = false → y.isFinite = true →
      y.isZero = false →
      floatPowCore cpow x y = if (cpow x y).isInf
        then .error (.overflowError "~[Errno 34] Numerical result out of range")
        else .ok (.float (cpow x y)))

theorem eq_d0_of_zero {y : F64} (h : y.isZero = true) : F64.eq y d0 = true := by
  have hy := isFinite_of_isZero h
  rw [eq_of_finite hy d0_isFinite, d0_toRat, toRat_of_isZero h]; rfl

theorem eq_d0_of_not_zero {y : F64} (hy : y.isFinite = true) (h : y.isZero = false) :
    F64.eq y d0 = false := by
  rw [eq_of_finite hy d0_isFinite, d0_toRat]
  have : y.toRat ≠ 0 := fun h0 => by
    rw [(isZero_iff_toRat hy).2 h0] at h; cases h
  simp [this]

theorem eq_d0_nan {y : F64} (h : y.isNaN = true) : F64.eq y d0 = false := by
  simp [F64.eq, h]

theorem eq_d0_inf {y : F64} (h : y.isInf = true) : F64.eq y d0 = false := by
  have h0 := isNaN_false_of_finite d0_isFinite
  simp [F64.eq, h, h0, not_nan_of_inf h, isInf_false_of_finite d0_isFinite]

theorem eq_d0_of_nonzero_any {y : F64} (h : y.isZero = false) : F64.eq y d0 = false := by
  rcases classify y with h1 | h1 | h1
  · exact eq_d0_of_not_zero h1 h
  · exact eq_d0_inf h1
  · exact eq_d0_nan h1

theorem powSpecialValues_proven : PowSpecialValues := by
  intro cpow x y
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hz
    simp [floatPowCore, eq_d0_of_zero hz]
  · intro h
    rw [eq_d1_iff h]; exact pow_one_base cpow y
  · intro hn hz
    simp [floatPowCore, eq_d0_of_nonzero_any hz, hn]
  · intro hx hy hneg
    have hyz : y.isZero = false := by
      cases hc : y.isZero
      · rfl
      · rw [toRat_of_isZero hc] at hneg; exact absurd hneg (by decide)
    have h1 : F64.eq x d0 = true := eq_d0_of_zero hx
    have h2 : F64.lt y d0 = true := by
      rw [lt_of_finite hy d0_isFinite, d0_toRat]; simpa using hneg
    have hfx := isFinite_of_isZero hx
    simp [floatPowCore, eq_d0_of_not_zero hy hyz, isNaN_false_of_finite hfx,
      isNaN_false_of_finite hy, isInf_false_of_finite hy, isInf_false_of_finite hfx, h1, h2]
  · intro hx hneg hy hnon
    have hyz : y.isZero = false := by
      cases hc : y.isZero
      · rfl
      · exact absurd ⟨0, by rw [toRat_of_isZero hc]; rfl⟩ hnon
    have hxz : x.isZero = false := by
      cases hc : x.isZero
      · rfl
      · rw [toRat_of_isZero hc] at hneg; exact absurd hneg (by decide)
    have h2 : F64.lt x d0 = true := by
      rw [lt_of_finite hx d0_isFinite, d0_toRat]; simpa using hneg
    obtain ⟨hf1, hf2⟩ := floor_value hy
    have h3 : F64.ne y (F64.floor y) = true := by
      unfold F64.ne
      rw [eq_of_finite hy hf1, hf2]
      have : y.toRat ≠ (y.floorInt : Rat) := fun h => hnon ⟨_, h⟩
      simp [this]
    simp [floatPowCore, eq_d0_of_not_zero hy hyz, eq_d0_of_not_zero hx hxz,
      isNaN_false_of_finite hx, isNaN_false_of_finite hy, isInf_false_of_finite hy,
      isInf_false_of_finite hx, h2, h3]
  · intro hx hpos hne1 hy hyz
    have hxz : x.isZero = false := by
      cases hc : x.isZero
      · rfl
      · rw [toRat_of_isZero hc] at hpos; exact absurd hpos (by decide)
    have h2 : F64.lt x d0 = false := by
      rw [lt_of_finite hx d0_isFinite, d0_toRat]
      have : ¬ x.toRat < 0 := by grind
      simp [this]
    simp [floatPowCore, eq_d0_of_not_zero hy hyz, eq_d0_of_not_zero hx hxz,
      isNaN_false_of_finite hx, isNaN_false_of_finite hy, isInf_false_of_finite hy,
      isInf_false_of_finite hx, h2, hne1]

/-! ## Hash -/

theorem toSigned_ne (x2 : Nat) :
    toSigned64 (if x2 = 2 ^ 64 - 1 then 2 ^ 64 - 2 else x2) ≠ -1 := by
  unfold toSigned64
  split
  · rename_i h; subst h; decide
  · split <;> omega

theorem zero_hash (s : Bool) : float_hash (zero s) = some 0 := by
  cases s <;> decide +kernel

/-- `hash` never returns `-1`, infinities hash to `±314159`, a NaN hashes by identity,
and floats that compare equal hash equal. -/
def FloatHashBasics : Prop :=
  (∀ x : F64, float_hash x ≠ some (-1)) ∧
  (∀ x : F64, x.isNaN = true → float_hash x = none) ∧
  (∀ x : F64, x.isInf = true → float_hash x = some (if x.sign then -314159 else 314159)) ∧
  (∀ x y : F64, F64.eq x y = true → float_hash x = float_hash y)

theorem hash_inf (s : Bool) : float_hash (F64.inf s) = some (if s then -314159 else 314159) := by
  cases s <;> decide +kernel

theorem eq_inf_of_isInf {x : F64} (hi : x.isInf = true) : x = F64.inf x.sign := by
  rw [isInf_eq] at hi
  have h1 := (F64.inf_isInf x.sign)
  rw [isInf_eq] at h1
  apply eq_of_fields
  · cases hs : x.sign <;> decide +kernel
  · omega
  · omega

theorem eq_zero_of_isZero {x : F64} (hz : x.isZero = true) : x = F64.zero x.sign := by
  rw [isZero_eq] at hz
  have h1 := zero_isZero x.sign
  rw [isZero_eq] at h1
  apply eq_of_fields
  · rw [zero_sign]
  · omega
  · omega

theorem floatHashBasics_proven : FloatHashBasics := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    rcases classify x with h | h | h
    · simp only [float_hash, _Py_HashDouble, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      intro hc
      simp only [Option.some.injEq] at hc
      exact toSigned_ne _ hc
    · rw [eq_inf_of_isInf h, hash_inf]
      intro hc
      simp only [Option.some.injEq] at hc
      split at hc <;> omega
    · simp [float_hash, _Py_HashDouble, not_inf_of_nan h]
      intro hc
      have := isNaN_false_of_finite hc
      rw [h] at this; cases this
  · intro x h
    have hf : x.isFinite = false := by
      cases hc : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite hc] at h; cases h
    simp [float_hash, _Py_HashDouble, not_inf_of_nan h, hf]
  · intro x h
    have hs : (F64.inf x.sign).sign = x.sign := by cases hs : x.sign <;> decide +kernel
    rw [eq_inf_of_isInf h, hs, hash_inf]
  · intro x y h
    have hnx : x.isNaN = false := by
      cases hn : x.isNaN
      · rfl
      · simp [F64.eq, hn] at h
    have hny : y.isNaN = false := by
      cases hn : y.isNaN
      · rfl
      · simp [F64.eq, hn, hnx] at h
    by_cases hi : x.isInf = true ∨ y.isInf = true
    · have h' : (x.isInf = true ∧ y.isInf = true) ∧ x.sign = y.sign := by
        simpa [F64.eq, hnx, hny, hi] using h
      rw [eq_inf_of_isInf h'.1.1, eq_inf_of_isInf h'.1.2, h'.2]
    · have hix : x.isInf = false := by
        cases hc : x.isInf
        · rfl
        · exact absurd (Or.inl hc) hi
      have hiy : y.isInf = false := by
        cases hc : y.isInf
        · rfl
        · exact absurd (Or.inr hc) hi
      have hfx : x.isFinite = true := by
        rcases classify x with h1 | h1 | h1
        · exact h1
        · rw [hix] at h1; cases h1
        · rw [hnx] at h1; cases h1
      have hfy : y.isFinite = true := by
        rcases classify y with h1 | h1 | h1
        · exact h1
        · rw [hiy] at h1; cases h1
        · rw [hny] at h1; cases h1
      have hv : x.toRat = y.toRat := by
        rw [eq_of_finite hfx hfy] at h; simpa using h
      cases hz : x.isZero
      · rw [toRat_inj hfx hfy hz hv]
      · have hyz : y.isZero = true := (isZero_iff_toRat hfy).2 (by rw [← hv]; exact toRat_of_isZero hz)
        rw [eq_zero_of_isZero hz, eq_zero_of_isZero hyz, zero_hash, zero_hash]

/-! ## Small methods -/

/-- `-x` flips the sign bit and keeps the 11 exponent bits and the 52 fraction bits, so it
changes only bit 63, NaN payloads included; `abs(x)` clears the sign bit and keeps the
rest; and `bool(x)` is false exactly for the two zeros. -/
def FloatUnary : Prop :=
  ∀ x : F64,
    float_neg (float_neg x) = x ∧ (float_neg x).sign = !x.sign ∧
    (float_neg x).bexp = x.bexp ∧ (float_neg x).frac = x.frac ∧
    (float_abs x).sign = false ∧ (float_abs x).bexp = x.bexp ∧ (float_abs x).frac = x.frac ∧
    (float_bool x = false ↔ x.isZero = true)

theorem floatUnary_proven : FloatUnary := by
  intro x
  obtain ⟨h1, h2, h3⟩ := neg_fields x
  refine ⟨neg_neg x, h1, h2, h3, ?_, ?_, ?_, ?_⟩
  · simp only [float_abs, F64.abs]
    cases hs : x.sign
    · simp [hs]
    · simp [h1, hs]
  · simp only [float_abs, F64.abs]
    split
    · exact h2
    · rfl
  · simp only [float_abs, F64.abs]
    split
    · exact h3
    · rfl
  · unfold float_bool F64.ne
    constructor
    · intro h
      cases hz : x.isZero
      · rw [eq_d0_of_nonzero_any hz] at h; cases h
      · rfl
    · intro h
      rw [eq_d0_of_zero h]; rfl

/-- `float.conjugate`, `.real`, `__float__`, `__getnewargs__` and `float.from_number` on a
float keep the value, and `.imag` is `0.0`. -/
def FloatIdentities : Prop :=
  ∀ x : F64, float_conjugate x = x ∧ float_getreal x = x ∧ float_float x = x ∧
    float_getnewargs x = x ∧ float_getimag x = F64.zero false ∧
    float_from_number (.float x) = .ok x ∧ float_new_number (some (.float x)) = .ok x ∧
    float_subtype_new (some (.float x)) = .ok x ∧ float_vectorcall [.float x] = .ok x ∧
    float_new_number none = .ok (F64.zero false) ∧ float_vectorcall [] = .ok (F64.zero false)

theorem floatIdentities_proven : FloatIdentities := fun _ =>
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `PyFloat_AsDouble` on floats, ints and objects with or without `__float__`. -/
def FloatAsDouble : Prop :=
  (∀ x : F64, PyFloat_AsDouble (.float x) = .ok x) ∧
  (∀ (t : String) (x : F64), PyFloat_AsDouble (.floatSub t x) = .ok x) ∧
  (∀ n : Int, PyFloat_AsDouble (.int n) = PyLong_AsDouble n) ∧
  (∀ (t q : String) (i : Int), PyFloat_AsDouble (.other t none (some i) q) = PyLong_AsDouble i) ∧
  (∀ t q : String, PyFloat_AsDouble (.other t none none q) =
    .error (.typeError s!"must be real number, not {t}")) ∧
  (∀ (t q : String) (x : F64) (i : Option Int),
    PyFloat_AsDouble (.other t (some (.float x)) i q) = .ok x) ∧
  (∀ (t q s : String) (x : F64) (i : Option Int),
    PyFloat_AsDouble (.other t (some (.floatSub s x)) i q) = .ok x) ∧
  (∀ (t q : String) (n : Int) (i : Option Int), PyFloat_AsDouble (.other t (some (.int n)) i q) =
    .error (.typeError s!"{q}.__float__() must return a float, not int")) ∧
  (∀ (t q rt rq : String) (f : Option Obj) (j i : Option Int),
    PyFloat_AsDouble (.other t (some (.other rt f j rq)) i q) =
      .error (.typeError s!"{q}.__float__() must return a float, not {rq}"))

theorem floatAsDouble_proven : FloatAsDouble :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- `float.__getformat__` answers for `'double'` and `'float'` and raises `ValueError`
for anything else. -/
def GetFormat : Prop :=
  ∀ t : String, float_getformat t =
    if t = "double" ∨ t = "float" then .ok "IEEE, little-endian"
    else .error (.valueError "__getformat__() argument 1 must be 'double' or 'float'")

theorem getFormat_proven : GetFormat := by
  intro t
  unfold float_getformat
  by_cases h1 : t = "double"
  · simp [h1]
  · by_cases h2 : t = "float"
    · simp [h2]
    · simp [h1, h2]

/-- `sys.float_info`: `max` is the largest finite float and exceeds no other limit,
`min` the smallest normal one, and `epsilon` the gap between `1.0` and the next float. -/
def FloatInfoCorrect : Prop :=
  (∀ x : F64, x.isFinite = true → Rat.abs x.toRat ≤ PyFloat_GetMax.toRat) ∧
  PyFloat_GetInfo.max = PyFloat_GetMax ∧ PyFloat_GetInfo.min = PyFloat_GetMin ∧
  PyFloat_GetMin.toRat = pw (-1022) ∧ PyFloat_GetMin.bexp = 1 ∧ PyFloat_GetMin.frac = 0 ∧
  PyFloat_GetInfo.epsilon = F64.sub (F64.ofBits 0x3ff0000000000001) d1 ∧
  PyFloat_GetInfo.mant_dig = 53 ∧ PyFloat_GetInfo.max_exp = 1024 ∧ PyFloat_GetInfo.min_exp = -1021 ∧
  -- max_exp: 2 ** (max_exp - 1) is finite and 2 ** max_exp is not
  pw (PyFloat_GetInfo.max_exp - 1) ≤ PyFloat_GetMax.toRat ∧ PyFloat_GetMax.toRat < pw PyFloat_GetInfo.max_exp ∧
  -- min_exp: 2 ** (min_exp - 1) is the smallest normal
  pw (PyFloat_GetInfo.min_exp - 1) = PyFloat_GetMin.toRat ∧
  -- max_10_exp: the largest n with 10 ** n finite
  ((10 ^ PyFloat_GetInfo.max_10_exp.toNat : Nat) : Rat) ≤ PyFloat_GetMax.toRat ∧
  PyFloat_GetMax.toRat < ((10 ^ (PyFloat_GetInfo.max_10_exp.toNat + 1) : Nat) : Rat) ∧
  -- min_10_exp: the smallest n with 10 ** n normal (n is negative)
  0 < -PyFloat_GetInfo.min_10_exp ∧
  PyFloat_GetMin.toRat ≤ mkRat 1 (10 ^ (-PyFloat_GetInfo.min_10_exp).toNat) ∧
  mkRat 1 (10 ^ ((-PyFloat_GetInfo.min_10_exp).toNat + 1)) < PyFloat_GetMin.toRat ∧
  -- dig: floor((mant_dig - 1) * log10(2)), as DBL_DIG is defined for radix 2
  10 ^ PyFloat_GetInfo.dig.toNat ≤ 2 ^ (PyFloat_GetInfo.mant_dig.toNat - 1) ∧
  2 ^ (PyFloat_GetInfo.mant_dig.toNat - 1) < 10 ^ (PyFloat_GetInfo.dig.toNat + 1) ∧
  -- radix and rounds: binary, round to nearest (the rounding `RoundToNearestEven` proves)
  PyFloat_GetInfo.radix = 2 ∧ PyFloat_GetInfo.rounds = 1 ∧
  PyFloat_GetInfo.max_10_exp = 308 ∧ PyFloat_GetInfo.min_10_exp = -307 ∧ PyFloat_GetInfo.dig = 15

theorem floatInfoCorrect_proven : FloatInfoCorrect := by
  refine ⟨?_, rfl, rfl, ?_, by decide +kernel, by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    ?_, ?_, ?_, ?_, ?_, by decide, ?_, ?_, by decide +kernel, by decide +kernel, rfl, rfl, rfl, rfl, rfl⟩
  · intro x hx
    have h1 : x.mant ≤ 9007199254740991 := by have := mant_lt x; omega
    have h2 : (x.mant : Rat) ≤ 9007199254740991 := by
      exact_mod_cast Rat.natCast_le_natCast.2 h1
    have h3 : pw x.lsbExp ≤ pw 971 := pw_le (lsbExp_le x hx)
    have h4 : (x.mant : Rat) * pw x.lsbExp ≤ 9007199254740991 * pw 971 := by
      have a1 := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt (pw_pos x.lsbExp))
      have a2 := Rat.mul_le_mul_of_nonneg_left h3 (by decide : (0 : Rat) ≤ 9007199254740991)
      exact Rat.le_trans a1 a2
    have hmax : PyFloat_GetMax.toRat = 9007199254740991 * pw 971 := by
      have e : PyFloat_GetMax.toRat = (PyFloat_GetMax.mant : Rat) * pw PyFloat_GetMax.lsbExp := by
        rw [toRat_of_finite (by decide +kernel)]
        simp [show PyFloat_GetMax.sign = false by decide +kernel]
      rw [e, show PyFloat_GetMax.mant = 9007199254740991 by decide +kernel,
        show PyFloat_GetMax.lsbExp = 971 by decide +kernel]
      rfl
    rw [hmax, toRat_of_finite hx]
    split
    · rw [abs_neg, abs_of_nonneg (mantVal_nonneg x)]; exact h4
    · rw [abs_of_nonneg (mantVal_nonneg x)]; exact h4
  all_goals decide +kernel

end PyLean.Binary64
