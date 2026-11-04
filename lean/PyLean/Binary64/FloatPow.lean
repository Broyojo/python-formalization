import PyLean.Binary64.FloatSmall

/-!
`float_pow`, `Objects/floatobject.c:686-803` (CPython 3.15.2), with the C library `pow`
returning a value and an `errno`.

`floatPowCore` in `Float.lean` takes a `pow` that never sets `errno`, which is how the
other modules use it; `floatPowCore_eq` shows it is `floatPowCoreE` with such a `pow`.
-/

namespace PyLean.Binary64

open PyLean F64

def ERANGE : Nat := 34

/-- `_Py_ADJUST_ERANGE1(x)`, Include/internal/pycore_pymath.h:33-43: set `ERANGE` on an
infinite result, and clear an `ERANGE` that only reports underflow to zero. -/
def adjustErange1 (x : F64) (errno : Nat) : Nat :=
  if errno == 0 then (if x.isInf then ERANGE else 0)
  else if errno == ERANGE && F64.eq x d0 then 0
  else errno

/-- `PyErr_SetFromErrno(errno == ERANGE ? PyExc_OverflowError : PyExc_ValueError)`,
floatobject.c:798-799, with the `strerror` text of the C library. -/
def errnoError (errno : Nat) : PyExc :=
  if errno == ERANGE then .overflowError "~[Errno 34] Numerical result out of range"
  else .valueError s!"~[Errno {errno}] (strerror)"

/-- `float_pow` after the `CONVERT_TO_DOUBLE` lines, floatobject.c:699-802, for a C
library `pow` that returns its value and the `errno` it leaves. -/
def floatPowCoreE (libm : F64 → F64 → F64 × Nat) (iv0 iw : F64) : Py PowResult :=
  if F64.eq iw d0 then .ok (.float d1)
  else if iv0.isNaN then .ok (.float iv0)
  else if iw.isNaN then .ok (.float (if F64.eq iv0 d1 then d1 else iw))
  else if iw.isInf then
    let iv := iv0.abs
    if F64.eq iv d1 then .ok (.float d1)
    else if F64.gt iw d0 == F64.gt iv d1 then .ok (.float iw.abs)
    else .ok (.float d0)
  else if iv0.isInf then
    let iw_is_odd := isOddInteger iw
    if F64.gt iw d0 then .ok (.float (if iw_is_odd then iv0 else iv0.abs))
    else .ok (.float (if iw_is_odd then F64.copysign d0 iv0 else d0))
  else if F64.eq iv0 d0 then
    let iw_is_odd := isOddInteger iw
    if F64.lt iw d0 then .error (.zeroDivisionError "zero to a negative power")
    else .ok (.float (if iw_is_odd then iv0 else d0))
  else
    let step : Option (F64 × Bool) :=
      if F64.lt iv0 d0 then
        if F64.ne iw (F64.floor iw) then none
        else some (iv0.neg, isOddInteger iw)
      else some (iv0, false)
    match step with
    | none => .ok (.complexPow iv0 iw)
    | some (iv, negate_result) =>
      if F64.eq iv d1 then .ok (.float (if negate_result then dm1 else d1))
      else
        -- errno = 0; ix = pow(iv, iw); _Py_ADJUST_ERANGE1(ix); if (negate_result) ix = -ix;
        let r := libm iv iw
        let errno := adjustErange1 r.1 r.2
        let ix := if negate_result then r.1.neg else r.1
        if errno != 0 then .error (errnoError errno) else .ok (.float ix)

/-- `float_pow`, floatobject.c:686-803. -/
def float_powE (libm : F64 → F64 → F64 × Nat) (v w : Obj) (z : Option Obj) : Py (Option PowResult) :=
  match z with
  | some _ =>
    .error (.typeError "pow() 3rd argument not allowed unless all arguments are integers")
  | none => withDoubles v w (floatPowCoreE libm)

theorem floatPowCore_eq (cpow : F64 → F64 → F64) (x y : F64) :
    floatPowCore cpow x y = floatPowCoreE (fun a b => (cpow a b, 0)) x y := by
  unfold floatPowCore floatPowCoreE
  repeat' (first | rfl | (split <;> try rfl))
  all_goals simp_all [adjustErange1, errnoError, ERANGE]

/-! ## The specification -/

/-- A finite float with an integer value. -/
def IsInt (y : F64) : Prop := ∃ n : Int, y.toRat = n

/-- A finite float with an odd integer value. -/
def IsOddInt (y : F64) : Prop := ∃ n : Int, y.toRat = 2 * n + 1

/-- What the last step of `float_pow` makes of `pow`'s value and `errno`
(floatobject.c:788-802): with no `errno`, an infinity is `OverflowError`; an `ERANGE` with a
zero result is underflow and is dropped; any other `errno` is raised; otherwise the value,
negated for `negate_result`. -/
def libmOutcome (r : F64 × Nat) (neg : Bool) : Py PowResult :=
  if r.2 = 0 then
    (if r.1.isInf then .error (errnoError ERANGE) else .ok (.float (if neg then r.1.neg else r.1)))
  else if r.2 = ERANGE ∧ r.1.isZero = true then .ok (.float (if neg then r.1.neg else r.1))
  else .error (errnoError r.2)

open Classical in
/-- `x ** y` for floats, for every C library `pow` and every `errno` it leaves: the C99
Annex F special values `float_pow` settles itself (floatobject.c:701-787) and the call to
`pow` for the rest.

* `x ** 0` is `1.0` even for a NaN `x`; `nan ** y` is that NaN otherwise; `x ** nan` is
  that NaN unless `x == 1.0`.
* `x ** ±inf` is `1.0` for `|x| == 1`, `+inf` when `y > 0` and `|x| > 1` agree (an
  infinite `x` counts as `|x| > 1`), and `+0.0` otherwise.
* `(±inf) ** y` is `±inf` for an odd integer `y > 0`, `+inf` for other `y > 0`, and a
  zero with the sign of `x` for an odd integer `y < 0`, `+0.0` for other `y < 0`.
* `(±0.0) ** y` raises `ZeroDivisionError` for `y < 0`, and is `x` itself for an odd
  integer `y > 0`, `+0.0` for other `y > 0`.
* A negative finite `x` with a non-integer `y` goes to `complex.__pow__`; with an
  integer `y` it is `±1.0` for `x == -1.0`, and otherwise `pow(-x, y)`, negated when `y`
  is odd (`negate_result`), so `(-2.0) ** 3 == -8.0`.
* A positive finite `x` gives `1.0` for `x == 1.0` and `pow(x, y)` otherwise.

`float_floor`'s and `fmod`'s use in `DOUBLE_IS_ODD_INTEGER` is stated through `IsInt` and
`IsOddInt`, the exact value. -/
def PowSpec : Prop :=
  ∀ (libm : F64 → F64 → F64 × Nat) (x y : F64),
    (y.isZero = true → floatPowCoreE libm x y = .ok (.float d1)) ∧
    (y.isZero = false → x.isNaN = true → floatPowCoreE libm x y = .ok (.float x)) ∧
    (y.isNaN = true → x.isNaN = false →
      floatPowCoreE libm x y = .ok (.float (if x.isFinite = true ∧ x.toRat = 1 then d1 else y))) ∧
    (y.isInf = true → x.isNaN = false →
      floatPowCoreE libm x y = .ok (.float
        (if x.isFinite = true ∧ Rat.abs x.toRat = 1 then d1
         else if (y.sign = false ↔ (x.isInf = true ∨ 1 < Rat.abs x.toRat)) then F64.inf false
         else F64.zero false))) ∧
    (x.isInf = true → y.isFinite = true → y.isZero = false →
      floatPowCoreE libm x y = .ok (.float
        (if y.sign = false then (if IsOddInt y then x else F64.inf false)
         else (if IsOddInt y then F64.zero x.sign else F64.zero false)))) ∧
    (x.isZero = true → y.isFinite = true → y.isZero = false →
      floatPowCoreE libm x y =
        if y.sign = true then .error (.zeroDivisionError "zero to a negative power")
        else .ok (.float (if IsOddInt y then x else F64.zero false))) ∧
    (x.isFinite = true → x.isZero = false → x.sign = true → y.isFinite = true → y.isZero = false →
      ¬ IsInt y → floatPowCoreE libm x y = .ok (.complexPow x y)) ∧
    (x.isFinite = true → x.isZero = false → x.sign = true → y.isFinite = true → y.isZero = false →
      IsInt y →
      floatPowCoreE libm x y =
        if x.toRat = -1 then .ok (.float (if IsOddInt y then dm1 else d1))
        else libmOutcome (libm x.neg y) (decide (IsOddInt y))) ∧
    (x.isFinite = true → x.isZero = false → x.sign = false → y.isFinite = true → y.isZero = false →
      floatPowCoreE libm x y = if x.toRat = 1 then .ok (.float d1) else libmOutcome (libm x y) false)

/-- `float_pow` on every operand: a third argument other than `None` raises `TypeError`
before any conversion, and otherwise the `CONVERT_TO_DOUBLE` dispatch leads to `PowSpec`;
`floatPowCore`, which the other modules use, is the case of a `pow` that never sets
`errno`. -/
def FloatPowSpec : Prop :=
  (∀ libm v w (z : Obj), float_powE libm v w (some z) =
    .error (.typeError "pow() 3rd argument not allowed unless all arguments are integers")) ∧
  (∀ libm, BinDispatch (fun v w => float_powE libm v w none)) ∧
  (∀ libm x y, float_powE libm (.float x) (.float y) none = (floatPowCoreE libm x y).map some) ∧
  PowSpec ∧
  (∀ cpow x y, floatPowCore cpow x y = floatPowCoreE (fun a b => (cpow a b, 0)) x y)

/-! ## Lemmas -/

theorem d2_facts : d2.isFinite = true ∧ d2.isZero = false ∧ d2.toRat = 2 ∧ d2.sign = false := by
  decide +kernel

theorem dm1_facts : dm1.isFinite = true ∧ dm1.toRat = -1 := by decide +kernel

theorem gt_d0_sign {x : F64} (hx : x.isFinite = true) (hz : x.isZero = false) :
    F64.gt x d0 = !x.sign := by
  unfold F64.gt
  rw [lt_of_finite d0_isFinite hx, d0_toRat]
  have e := MathInt.toRat_neg_iff_sign hx hz
  have n : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hx).2 h] at hz; cases hz
  cases hs : x.sign <;> rw [hs] at e <;> simp only [eq_iff_iff, Bool.false_eq_true, iff_false,
    iff_true] at e <;> simp only [Bool.not_false, Bool.not_true, decide_eq_true_eq,
    decide_eq_false_iff_not] <;> grind

theorem eq_d1_val {x : F64} (hx : x.isFinite = true) : F64.eq x d1 = decide (x.toRat = 1) := by
  rw [eq_of_finite hx d1_facts.2.2.1]
  have : d1.toRat = 1 := by decide +kernel
  rw [this]

theorem floor_two (n : Int) (h : 0 ≤ n) : (((2 * n + 1 : Int) : Rat) / 2).floor = n := by
  apply floor_eq_of
  · apply Rat.not_lt.1
    rw [Rat.div_lt_iff (by decide)]
    push_cast; grind
  · rw [Rat.div_lt_iff (by decide)]
    push_cast; grind

/-- `DOUBLE_IS_ODD_INTEGER(x)`, `fmod(fabs(x), 2.0) == 1.0`, is exactly "an odd integer". -/
theorem isOddInteger_iff {y : F64} (hy : y.isFinite = true) : isOddInteger y = true ↔ IsOddInt y := by
  obtain ⟨f2, z2, v2, s2⟩ := d2_facts
  have hya : y.abs.isFinite = true := by rw [MathInt.abs_isFinite]; exact hy
  have hA : Rat.abs y.abs.toRat = Rat.abs y.toRat := by
    rw [MathInt.abs_toRat]; exact abs_of_nonneg (abs_nonneg _)
  obtain ⟨hrep, hr0, hrB, _⟩ := MathInt.fmod_rem hya f2 z2
  have hfm := fmod_finite hya f2 z2
  rw [hA, v2, show Rat.abs (2 : Rat) = 2 by decide] at hfm hrep hr0 hrB
  have hsa : y.abs.sign = false := by
    unfold F64.abs; split
    · rename_i h; rw [(neg_fields y).1, h]; rfl
    · rename_i h; simpa using h
  rw [hsa] at hfm
  simp only [Bool.false_eq_true, ↓reduceIte] at hfm
  generalize hr : Rat.abs y.toRat - 2 * ((Rat.abs y.toRat / 2).floor : Rat) = r at hfm hrep hr0 hrB
  have key : isOddInteger y = decide (r = 1) := by
    unfold isOddInteger
    rw [hfm]
    split
    · rename_i h0
      rw [h0]
      have : F64.eq (zero false) d1 = false := by decide +kernel
      rw [this]; simp
    · have hlt : Rat.abs r < overflowLimit := by
        rw [abs_of_nonneg hr0]
        have : (2 : Rat) < overflowLimit := by decide +kernel
        grind
      rw [eq_d1_val ((ofRat_isFinite _).2 hlt), ofRat_exact hrep hlt]
  rw [key, decide_eq_true_iff]
  have ey := MathInt.sign_val hy
  constructor
  · intro h1
    generalize hk : (Rat.abs y.toRat / 2).floor = k at hr
    have hA1 : Rat.abs y.toRat = 2 * k + 1 := by grind
    rw [hA1] at ey
    split at ey
    · exact ⟨-k - 1, by rw [ey]; push_cast; grind⟩
    · exact ⟨k, ey⟩
  · rintro ⟨n, hn⟩
    rw [← hr]
    by_cases h0 : 0 ≤ n
    · have hA1 : Rat.abs y.toRat = ((2 * n + 1 : Int) : Rat) := by
        rw [hn, abs_of_nonneg]
        · push_cast; rfl
        · have : (0 : Rat) ≤ (n : Rat) := by exact_mod_cast h0
          grind
      rw [hA1, floor_two n h0]; push_cast; grind
    · have hA1 : Rat.abs y.toRat = ((2 * (-n - 1) + 1 : Int) : Rat) := by
        rw [hn, abs_of_nonpos]
        · push_cast; grind
        · have h1 : ((n : Int) : Rat) ≤ ((-1 : Int) : Rat) := Rat.intCast_le_intCast.2 (by omega)
          have : (n : Rat) ≤ -1 := by simpa using h1
          grind
      rw [hA1, floor_two (-n - 1) (by omega)]; push_cast; grind

theorem isInt_iff {y : F64} (hy : y.isFinite = true) : F64.ne y (F64.floor y) = false ↔ IsInt y := by
  obtain ⟨hf1, hf2⟩ := floor_value hy
  unfold F64.ne
  rw [eq_of_finite hy hf1, hf2]
  constructor
  · intro h; exact ⟨_, by simpa using h⟩
  · rintro ⟨n, hn⟩
    rw [floor_of_int hn, hn]; simp

theorem odd_imp_int {y : F64} (h : IsOddInt y) : IsInt y := by
  obtain ⟨n, hn⟩ := h
  exact ⟨2 * n + 1, by rw [hn]; push_cast; rfl⟩

theorem eq_d0_finite_iff {x : F64} (hx : x.isFinite = true) : F64.eq x d0 = x.isZero := by
  cases hz : x.isZero
  · exact eq_d0_of_not_zero hx hz
  · exact eq_d0_of_zero hz

theorem libm_step (libm : F64 → F64 → F64 × Nat) (a y : F64) (neg : Bool) :
    (let r := libm a y
     let errno := adjustErange1 r.1 r.2
     let ix := if neg then r.1.neg else r.1
     if errno != 0 then (.error (errnoError errno) : Py PowResult) else .ok (.float ix)) =
      libmOutcome (libm a y) neg := by
  simp only [libmOutcome, adjustErange1]
  generalize libm a y = r
  obtain ⟨v, e⟩ := r
  simp only []
  by_cases he : e = 0
  · subst he; cases hi : v.isInf <;> simp [ERANGE]
  · have he' : (e == 0) = false := by simpa using he
    rw [he']
    by_cases h34 : e = ERANGE
    · subst h34
      rcases classify v with hv | hv | hv
      · rw [eq_d0_finite_iff hv]
        cases hz : v.isZero <;> simp [ERANGE]
      · rw [eq_d0_inf hv, inf_not_zero hv]; simp [ERANGE]
      · have hz : v.isZero = false := by
          cases hc : v.isZero
          · rfl
          · rw [isNaN_false_of_finite (isFinite_of_isZero hc)] at hv; cases hv
        rw [eq_d0_nan hv, hz]; simp [ERANGE]
    · have : (e == ERANGE) = false := by simpa using h34
      simp [this, he, h34]

end PyLean.Binary64
