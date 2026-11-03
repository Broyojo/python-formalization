import PyLean.MathInt.CmathModel
import PyLean.MathInt.FltWrap
import PyLean.MathInt.FltClassify
import PyLean.MathInt.FltLogProps

/-!
# Properties of `Modules/cmathmodule.c`
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-! ## `special_type` -/

/-- `special_type(d)` is the class the enum's comments give (cmathmodule.c:105-113): `ST_NAN` for a
NaN, `ST_PINF`/`ST_NINF` for the infinities, `ST_PZERO`/`ST_NZERO` for `+0.0`/`-0.0`, `ST_POS`/`ST_NEG`
for the other finite numbers by sign. -/
def SpecialTypeDoc : Prop :=
  ∀ d : F64,
    (special_type d = .nan ↔ d.isNaN = true) ∧
    (special_type d = .pinf ↔ d = F64.inf false) ∧
    (special_type d = .ninf ↔ d = F64.inf true) ∧
    (special_type d = .pzero ↔ d = F64.zero false) ∧
    (special_type d = .nzero ↔ d = F64.zero true) ∧
    (special_type d = .pos ↔ d.isFinite = true ∧ 0 < d.toRat) ∧
    (special_type d = .neg ↔ d.isFinite = true ∧ d.toRat < 0)

theorem eq_copysign_c1 (d : F64) : F64.eq (F64.copysign c1 d) c1 = !d.sign := by
  have h : c1.sign = false := by decide +kernel
  unfold F64.copysign
  cases hd : d.sign
  · simp [h]; decide +kernel
  · simp [h]; decide +kernel

theorem specialTypeDoc_proven : SpecialTypeDoc := by
  intro d
  rcases classify d with hf | hi | hn
  · have hn := isNaN_false_of_finite hf
    have hni : d ≠ F64.inf false ∧ d ≠ F64.inf true := by
      constructor <;> intro h <;> rw [h] at hf <;> exact absurd hf (by decide +kernel)
    by_cases hz : d.isZero = true
    · have hd := eq_zero_of_isZero hz
      have hzc : isZeroC d = true := by rw [isZeroC_eq]; exact hz
      have h0 := toRat_of_isZero hz
      cases hs : d.sign
      · rw [hs] at hd
        simp only [special_type, hf, hzc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          eq_copysign_c1, hs, Bool.not_false]
        refine ⟨by simp [hn], by simp; exact hni.1, by simp; exact hni.2, by simp; exact hd,
          ?_, ?_, ?_⟩
        · simp; intro h; rw [h] at hd; exact absurd hd (by decide +kernel)
        · simp [h0]
        · simp [h0]
      · rw [hs] at hd
        simp only [special_type, hf, hzc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          eq_copysign_c1, hs, Bool.not_true]
        refine ⟨by simp [hn], by simp; exact hni.1, by simp; exact hni.2, ?_, by simp; exact hd,
          ?_, ?_⟩
        · simp; intro h; rw [h] at hd; exact absurd hd (by decide +kernel)
        · simp [h0]
        · simp [h0]
    · have hz' : d.isZero = false := by simpa using hz
      have hzc : isZeroC d = false := by rw [isZeroC_eq]; exact hz'
      have hsg := toRat_neg_iff_sign hf hz'
      have hne0 : d.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hf).2 h] at hz'; cases hz'
      have hnz : d ≠ F64.zero false ∧ d ≠ F64.zero true := by
        constructor <;> intro h <;> rw [h] at hz' <;> exact absurd hz' (by decide +kernel)
      cases hs : d.sign
      · rw [hs] at hsg
        have hp : 0 < d.toRat := by simp at hsg; grind
        simp only [special_type, hf, hzc, Bool.not_false, ↓reduceIte, eq_copysign_c1, hs]
        refine ⟨by simp [hn], by simp; exact hni.1, by simp; exact hni.2, by simp; exact hnz.1,
          by simp; exact hnz.2, by simp [hf, hp], ?_⟩
        simp; intro _; grind
      · rw [hs] at hsg
        have hp : d.toRat < 0 := by simp at hsg; exact hsg
        simp only [special_type, hf, hzc, Bool.not_false, ↓reduceIte, eq_copysign_c1, hs,
          Bool.not_true, Bool.false_eq_true]
        refine ⟨by simp [hn], by simp; exact hni.1, by simp; exact hni.2, by simp; exact hnz.1,
          by simp; exact hnz.2, ?_, by simp [hf, hp]⟩
        simp; intro _; grind
  · have hd := eq_inf_of_isInf hi
    have hn := not_nan_of_inf hi
    have hf := not_finite_of_inf hi
    cases hs : d.sign
    · rw [hs] at hd; subst hd
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, ?_, ?_⟩ <;> simp [hf] <;> decide +kernel
    · rw [hs] at hd; subst hd
      refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
        by decide +kernel, ?_, ?_⟩ <;> simp [hf] <;> decide +kernel
  · have hf : d.isFinite = false := by
      cases h : d.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hn; cases hn
    have hni : d ≠ F64.inf false ∧ d ≠ F64.inf true ∧ d ≠ F64.zero false ∧ d ≠ F64.zero true := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> rw [h] at hn <;> exact absurd hn (by decide +kernel)
    simp only [special_type, hf, hn, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hf, hni.1, hni.2.1, hni.2.2.1, hni.2.2.2]

/-! ## The error glue -/

/-- The `Py_complex_protected` return conversion (cmathmodule.c:36-46) and `math_error`
(:979-989): both turn `EDOM` into `ValueError('math domain error')` and `ERANGE` into
`OverflowError('math range error')`; for any other nonzero `errno` `math_error` raises
`ValueError` from `PyErr_SetFromErrno` while the return conversion returns the result, as it does
for `errno == 0`. -/
def CmathErrGlue : Prop :=
  ∀ (r : C) (e : Errno),
    (protectedRet r e = .error (.valueError "math domain error") ↔ e = .edom) ∧
    (protectedRet r e = .error (.overflowError "math range error") ↔ e = .erange) ∧
    (e ≠ .edom → e ≠ .erange → protectedRet r e = .ok r) ∧
    (e = .edom → cmath_math_error e = .valueError "math domain error") ∧
    (e = .erange → cmath_math_error e = .overflowError "math range error") ∧
    (∀ n, e = .other n → cmath_math_error e = .valueError s!"~[Errno {n}]")

theorem cmathErrGlue_proven : CmathErrGlue := by
  intro r e
  cases e <;> simp [protectedRet, cmath_math_error, Errno.num]

/-! ## `phase` and `polar` -/

/-- A C `atan2` as C99 Annex F has it: no `errno`, never an infinity, and a NaN only from a NaN
argument (F.9.1.4). -/
def Atan2AnnexF (atan2 : CFun2) : Prop :=
  ∀ y x : F64, (atan2 y x).2 = .zero ∧ (atan2 y x).1.isInf = false ∧
    ((atan2 y x).1.isNaN = true → y.isNaN = true ∨ x.isNaN = true)

/-- `phase(z)` is equivalent to `math.atan2(z.imag, z.real)` (Doc/library/cmath.rst, "phase"), for
every C `atan2` that follows C99 Annex F; and for any `atan2`, `phase` raises exactly when `atan2`
sets `errno`, through `math_error`. `polar(z)` is equivalent to `(abs(z), phase(z))`
(Doc/library/cmath.rst, "polar") except for the message when `abs` overflows: `abs` raises
`OverflowError('absolute value too large')`, `polar` `OverflowError('math range error')`; and
`polar` ignores the `errno` of its `atan2` (3.15 sets `errno = 0` after it). -/
def PhasePolar : Prop :=
  (∀ atan2 : CFun2, Atan2AnnexF atan2 → ∀ z : C,
    cmath_phase atan2 z = math_2 [.float z.im, .float z.re] atan2 "atan2") ∧
  (∀ (atan2 : CFun2) (z : C), (atan2 z.im z.re).2 ≠ .zero →
    cmath_phase atan2 z = .error (cmath_math_error (atan2 z.im z.re).2)) ∧
  (∀ (atan2 : CFun2) (m : Libm) (z : C),
    cmath_polar atan2 m z =
      match complex_abs m false z with
      | .ok r => .ok (r, (atan2 z.im z.re).1)
      | .error _ => .error (.overflowError "math range error")) ∧
  (∀ (atan2 : CFun2) (m : Libm) (z : C), (atan2 z.im z.re).2 = .zero →
    ∀ r, complex_abs m false z = .ok r → cmath_phase atan2 z = .ok (atan2 z.im z.re).1 ∧
      cmath_polar atan2 m z = .ok (r, (atan2 z.im z.re).1))

theorem phasePolar_proven : PhasePolar := by
  refine ⟨fun atan2 hA z => ?_, fun atan2 z he => ?_, fun atan2 m z => ?_,
    fun atan2 m z he r hr => ?_⟩
  · obtain ⟨he, hi, hn⟩ := hA z.im z.re
    have rules := ((math2Rules_proven atan2 "atan2" [.float z.im, .float z.re]).2 (.float z.im)
      (.float z.re) rfl).2.2 z.im z.re rfl rfl
    obtain ⟨_, _, _, hnan, _, _, _, hzero, _⟩ := rules
    have hph : cmath_phase atan2 z = .ok (atan2 z.im z.re).1 := by
      simp [cmath_phase, he]
    rw [hph]
    rcases classify (atan2 z.im z.re).1 with h | h | h
    · exact (hzero h he).symm
    · rw [hi] at h; cases h
    · have : (z.im.isNaN || z.re.isNaN) = true := by
        rcases hn h with h' | h' <;> simp [h']
      exact (hnan h this).symm
  · simp only [cmath_phase]
    simp [he]
  · simp only [cmath_polar, complex_abs]
    cases (_Py_c_abs m false z).2 <;> rfl
  · refine ⟨by simp [cmath_phase, he], ?_⟩
    simp only [complex_abs] at hr
    simp only [cmath_polar]
    revert hr
    cases (_Py_c_abs m false z).2 <;> simp

/-- `DBL_MIN`. -/
def cDblMin : F64 := F64.ofBits 0x0010000000000000

/-- A C `atan2` as C23 7.12.4.4 allows it: no `errno` except a range error (`ERANGE`) when the
result underflows, i.e. is below `DBL_MIN` in magnitude (glibc sets it when `atan2(y, x)`
underflows to zero, e.g. `atan2(1e-300, 1e300)`). -/
def Atan2C23 (atan2 : CFun2) : Prop :=
  ∀ y x : F64, (atan2 y x).2 = .zero ∨
    ((atan2 y x).2 = .erange ∧ F64.lt (F64.abs (atan2 y x).1) cDblMin = true)

/-- "`phase(z)` is equivalent to `math.atan2(z.imag, z.real)`" (Doc/library/cmath.rst), for every C
`atan2` that C23 allows. -/
def PhaseAtan2C23 : Prop :=
  ∀ atan2 : CFun2, Atan2C23 atan2 → ∀ z : C,
    cmath_phase atan2 z = math_2 [.float z.im, .float z.re] atan2 "atan2"

/-- `1e300`, `1e-300`. -/
def c1e300 : F64 := F64.ofRat ((10 : Rat) ^ 300)
def c1em300 : F64 := F64.ofRat (1 / (10 : Rat) ^ 300)

/-- An `atan2` that underflows to `0.0` with `ERANGE` at `(1e-300, 1e300)`, as glibc's does. -/
def atan2Witness : CFun2 := fun y x =>
  if y = c1em300 ∧ x = c1e300 then (c0, .erange) else (c0, .zero)

/-- Refuted: `cmath.phase(complex(1e300, 1e-300))` raises `OverflowError('math range error')`
(python3 3.15.2 with glibc), while `math.atan2(1e-300, 1e300)` returns `0.0`: `math_2` ignores
`ERANGE` on results below 1.5 (`is_error`, mathmodule.c:742-743) but `cmath_phase_impl` hands any
`errno` to `math_error` (cmathmodule.c:1009-1010). -/
theorem phaseAtan2C23_refuted : ¬ PhaseAtan2C23 := by
  intro h
  have hw : Atan2C23 atan2Witness := by
    intro y x
    unfold atan2Witness
    split
    · right; exact ⟨rfl, by decide +kernel⟩
    · left; rfl
  have := h atan2Witness hw ⟨c1e300, c1em300⟩
  revert this
  decide +kernel

/-! ## `rect` -/

/-- `rect(r, phi)` (Doc/library/cmath.rst, "rect": "equivalent to `complex(r * math.cos(phi), r *
math.sin(phi))`"):

* for finite `r` and `phi` it is `complex(r * cos(phi), r * sin(phi))` with the C library's `cos`
  and `sin`, for every library with `cos(+-0) = 1` and `sin(+-0) = +-0` (C99 F.9.1.6-7: the
  `phi == 0` branch at :1097-1102 computes `(r, r*phi)` instead);
* it raises `ValueError('math domain error')` exactly when `r` is nonzero, not a NaN and `phi` is
  infinite (:1088-1093);
* for an infinite `r` and finite nonzero `phi` it is the infinity with the signs of `r*cos(phi)`
  and `r*sin(phi)` (:1078-1086). -/
def RectDoc : Prop :=
  (∀ L : RectLibm, (∀ s, L.cos (F64.zero s) = c1) → (∀ s, L.sin (F64.zero s) = F64.zero s) →
    ∀ r phi : F64, r.isFinite = true → phi.isFinite = true →
      cmath_rect L r phi = .ok ⟨F64.mul r (L.cos phi), F64.mul r (L.sin phi)⟩) ∧
  (∀ (L : RectLibm) (r phi : F64),
    (cmath_rect L r phi).raises "ValueError" ↔
      (r.isZero = false ∧ r.isNaN = false ∧ phi.isInf = true)) ∧
  (∀ (L : RectLibm) (s : Bool) (phi : F64), phi.isFinite = true → phi.isZero = false →
    cmath_rect L (F64.inf s) phi =
      .ok (if s then ⟨F64.neg (F64.copysign cInf (L.cos phi)), F64.neg (F64.copysign cInf (L.sin phi))⟩
           else ⟨F64.copysign cInf (L.cos phi), F64.copysign cInf (L.sin phi)⟩))

theorem mul_one_exact {r : F64} (hr : r.isFinite = true) : F64.mul r c1 = r := by
  have h1 : c1.isFinite = true ∧ c1.toRat = 1 ∧ c1.sign = false := by decide +kernel
  rw [mul_of_finite hr h1.1, h1.2.1, Rat.mul_one]
  split
  · rename_i h0
    have hz := (isZero_iff_toRat hr).2 h0
    rw [eq_zero_of_isZero hz, h1.2.2]
    cases r.sign <;> rfl
  · rename_i h0
    have hz : r.isZero = false := by
      cases h : r.isZero
      · rfl
      · exact absurd (toRat_of_isZero h) h0
    exact ofRat_toRat hr hz

theorem rectDoc_proven : RectDoc := by
  refine ⟨fun L hc hs r phi hr hp => ?_, fun L r phi => ?_, fun L s phi hp hz => ?_⟩
  · simp only [cmath_rect, hr, hp, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i hz
      rw [isZeroC_eq] at hz
      rw [eq_zero_of_isZero hz, hc, hs, mul_one_exact hr]
    · rfl
  · unfold cmath_rect
    by_cases hnf : (!r.isFinite || !phi.isFinite) = true
    · simp only [hnf, ↓reduceIte]
      by_cases he : (!isZeroC r && !r.isNaN && phi.isInf) = true
      · simp only [he, ↓reduceIte, bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true]
        simp [isZeroC_eq] at he
        refine ⟨fun _ => ⟨he.1.1, he.1.2, he.2⟩, fun _ => ⟨_, rfl, ?_⟩⟩
        simp [cmath_math_error, PyExc.className]
      · simp only [he, Bool.false_eq_true, ↓reduceIte, bne_self_eq_false]
        simp [isZeroC_eq] at he
        constructor
        · rintro ⟨e, h, _⟩; cases h
        · rintro ⟨h1, h2, h3⟩; exact absurd h3 (by simp [he h1 h2])
    · simp only [Bool.not_eq_true] at hnf
      simp only [hnf, Bool.false_eq_true, ↓reduceIte]
      simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hnf
      have hpi := isInf_false_of_finite hnf.2
      constructor
      · rintro ⟨e, h, _⟩; split at h <;> cases h
      · rintro ⟨_, _, h3⟩; rw [hpi] at h3; cases h3
  · have hinf : (F64.inf s).isFinite = false ∧ (F64.inf s).isInf = true ∧
        (F64.inf s).isNaN = false ∧ isZeroC (F64.inf s) = false := by
      cases s <;> decide +kernel
    have hpi := isInf_false_of_finite hp
    have hzc : isZeroC phi = false := by rw [isZeroC_eq]; exact hz
    simp only [cmath_rect, hinf, hp, hpi, hzc, Bool.not_false, Bool.true_or, Bool.not_true,
      Bool.and_true, Bool.and_false, Bool.true_and, ↓reduceIte, Bool.false_eq_true,
      bne_self_eq_false]
    have hl : F64.lt c0 (F64.inf false) = true ∧ F64.lt c0 (F64.inf true) = false := by decide +kernel
    cases s <;> simp [hl]

/-! ## The predicates -/

/-- `cmath.isfinite`, `isnan`, `isinf` (cmathmodule.c:1132-1163) test the parts as `math.isfinite`,
`math.isnan`, `math.isinf` do, and a complex number is finite exactly when it is neither infinite
nor a NaN (Doc/library/cmath.rst: "isfinite: Return True if both the real and imaginary parts of
x are finite"; "isinf: if either the real or the imaginary part of x is an infinity"; "isnan: if
either ... is a NaN"). -/
def CmathPredicates : Prop :=
  ∀ z : C,
    (math_isfinite (.float z.re) = .ok z.re.isFinite ∧ math_isfinite (.float z.im) = .ok z.im.isFinite ∧
      cmath_isfinite z = (z.re.isFinite && z.im.isFinite)) ∧
    cmath_isnan z = (z.re.isNaN || z.im.isNaN) ∧
    cmath_isinf z = (z.re.isInf || z.im.isInf) ∧
    cmath_isfinite z = (!cmath_isinf z && !cmath_isnan z) ∧
    (cmath_isinf z = true → cmath_isfinite z = false)

theorem fin_iff (x : F64) : x.isFinite = (!x.isInf && !x.isNaN) := by
  rcases classify x with h | h | h
  · simp [h, isInf_false_of_finite h, isNaN_false_of_finite h]
  · simp [h, not_finite_of_inf h]
  · have : x.isFinite = false := by
      cases hf : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite hf] at h; cases h
    simp [h, this]

theorem cmathPredicates_proven : CmathPredicates := by
  intro z
  refine ⟨⟨rfl, rfl, rfl⟩, rfl, rfl, ?_, ?_⟩
  · simp only [cmath_isfinite, cmath_isinf, cmath_isnan, fin_iff z.re, fin_iff z.im]
    cases z.re.isInf <;> cases z.im.isInf <;> cases z.re.isNaN <;> cases z.im.isNaN <;> rfl
  · intro h
    simp only [cmath_isfinite, cmath_isinf] at h ⊢
    rcases Bool.or_eq_true_iff.1 h with h' | h' <;> simp [not_finite_of_inf h']

/-! ## `isclose` -/

/-- `cmath.isclose(a, b, rel_tol=rt, abs_tol=at)` (Doc/library/cmath.rst, "isclose", and its
docstring): `ValueError('tolerances must be non-negative')` for a negative tolerance; with
nonnegative tolerances, equal numbers are close, a number with an infinite part is close only to
itself ("inf and -inf are only close to themselves"), and otherwise "the difference between them
must be smaller than at least one of the tolerances": `abs(a-b) <= rt*abs(b)`, or `<= rt*abs(a)`,
or `<= at`, with `abs` the complex modulus `_Py_c_abs` computes. -/
def CmathIsClose : Prop :=
  ∀ (m : Libm) (a b : C) (rt at_ : F64),
    ((F64.lt rt c0 || F64.lt at_ c0) = true →
      cmath_isclose m a b rt at_ = .error (.valueError "tolerances must be non-negative")) ∧
    ((F64.lt rt c0 || F64.lt at_ c0) = false →
      ((F64.eq a.re b.re && F64.eq a.im b.im) = true → cmath_isclose m a b rt at_ = .ok true) ∧
      ((a.re.isInf || a.im.isInf || b.re.isInf || b.im.isInf) = true →
        cmath_isclose m a b rt at_ = .ok (F64.eq a.re b.re && F64.eq a.im b.im)) ∧
      ((F64.eq a.re b.re && F64.eq a.im b.im) = false →
        (a.re.isInf || a.im.isInf || b.re.isInf || b.im.isInf) = false →
        cmath_isclose m a b rt at_ =
          .ok (F64.le (_Py_c_abs m false (_Py_c_diff a b)).1 (F64.mul rt (_Py_c_abs m false b).1) ||
            F64.le (_Py_c_abs m false (_Py_c_diff a b)).1 (F64.mul rt (_Py_c_abs m false a).1) ||
            F64.le (_Py_c_abs m false (_Py_c_diff a b)).1 at_)))

theorem cmathIsClose_proven : CmathIsClose := by
  intro m a b rt at_
  refine ⟨fun h => by simp [cmath_isclose, h], fun h => ⟨fun he => ?_, fun hi => ?_, fun he hi => ?_⟩⟩
  · simp [cmath_isclose, h, he]
  · simp only [cmath_isclose, h, hi, Bool.false_eq_true, ↓reduceIte]
    cases (F64.eq a.re b.re && F64.eq a.im b.im) <;> rfl
  · unfold cmath_isclose
    rw [h, he, hi]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_assoc]

/-- "NaN is not close to anything, even itself" (the `cmath.isclose` docstring and
Doc/library/cmath.rst): for every C library and nonnegative tolerances, a number with a NaN part is
never close to another. -/
def CmathIsCloseNaN : Prop :=
  ∀ (m : Libm) (a b : C) (rt at_ : F64), (F64.lt rt c0 || F64.lt at_ c0) = false →
    (a.re.isNaN || a.im.isNaN) = true → cmath_isclose m a b rt at_ = .ok false

/-- `1e308`. -/
def c1e308 : F64 := F64.ofRat ((10 : Rat) ^ 308)

/-- Refuted for every C library: `isclose(complex(nan, 1e308), complex(0.0, -1e308),
abs_tol=inf)` is `True`. The imaginary difference overflows to `inf`, and `_Py_c_abs` returns
`inf` for `(nan, inf)` (complexobject.c:376-380, C99's `hypot(inf, nan) = inf`) without calling
`hypot`; then `inf <= inf`. -/
theorem cmathIsCloseNaN_refuted : ¬ CmathIsCloseNaN := by
  intro h
  let m : Libm := ⟨fun _ _ => F64.qnan, fun _ _ => F64.qnan, fun _ _ => F64.qnan, id, id, id, id,
    fun _ => false⟩
  have := h m ⟨F64.qnan, c1e308⟩ ⟨c0, F64.neg c1e308⟩ c0 cInf (by decide +kernel) (by decide +kernel)
  revert this
  decide +kernel

/-! ## `log` -/

/-- What CPython's own `c_log` code fixes, whatever the C library: `c_log(0j)` is
`(-inf, atan2(0., 0.))` with `errno = EDOM` (cmathmodule.c:615-622; C99 F.9.1.4 gives
`atan2(+0, +0) = +0`), and for any finite argument other than a zero `c_log` ends with `errno = 0`
(:635-637). -/
def CLogFacts (K : CmathCore) : Prop :=
  K.clog ⟨c0, c0⟩ = (⟨F64.inf true, c0⟩, .edom) ∧
  ∀ z : C, z.re.isFinite = true → z.im.isFinite = true →
    (z.re.isZero = false ∨ z.im.isZero = false) → (K.clog z).2 = .zero

/-- `cmath.log(x, base)` "returns the logarithm of x to the given base", and `log(0)` is a domain
error: whenever `cmath.log(x)` raises `ValueError`, `cmath.log(x, base)` raises `ValueError` too,
for every `base` (as `math.log(0, 2)` does), for every `c_log` with CPython's facts. -/
def CmathLogBaseDomain : Prop :=
  ∀ K : CmathCore, CLogFacts K → ∀ (x b : C),
    (cmath_log K x none).raises "ValueError" → (cmath_log K x (some (.ok b))).raises "ValueError"

/-- `log(2.0)` as glibc returns it. -/
def cLn2 : F64 := F64.ofBits 0x3FE62E42FEFA39EF

/-- A `c_log` with CPython's facts: `(-inf, 0)` and `EDOM` at `0j`, `(log 2, 0)` and no `errno`
elsewhere. -/
def clogWitness : CImpl := fun z =>
  if z = ⟨c0, c0⟩ then (⟨F64.inf true, c0⟩, .edom) else (⟨cLn2, c0⟩, .zero)

def coreWitness : CmathCore := ⟨clogWitness, clogWitness, clogWitness, clogWitness, clogWitness,
  clogWitness⟩

/-- Refuted: `cmath.log(0)` raises `ValueError('math domain error')`, but `cmath.log(0, 2)` returns
`(-inf+nanj)`: the second `c_log` call resets `errno` to `0` (:636), so the `EDOM` of the first is
lost before the check at :971. -/
theorem cmathLogBaseDomain_refuted : ¬ CmathLogBaseDomain := by
  intro h
  have hK : CLogFacts coreWitness := by
    refine ⟨by decide +kernel, fun z h1 h2 hz => ?_⟩
    have : z ≠ ⟨c0, c0⟩ := by
      intro hz0; subst hz0
      rcases hz with h | h <;> exact absurd h (by decide +kernel)
    simp [coreWitness, clogWitness, this]
  have := h coreWitness hK ⟨c0, c0⟩ ⟨c2, c0⟩ ⟨.valueError "math domain error", by decide +kernel, rfl⟩
  obtain ⟨e, he, _⟩ := this
  have hok : (cmath_log coreWitness ⟨c0, c0⟩ (some (.ok ⟨c2, c0⟩))).toBool = true := by
    decide +kernel
  rw [he] at hok
  simp [Except.toBool] at hok

/-- `cmath.log` with and without a base (cmathmodule.c:955-974), for every `c_log`:

* without a base: `log(x)` is `c_log(x)`, or `math_error()` when `c_log` sets `errno`;
* a base whose conversion raises raises that, after `c_log(x)` (whatever its `errno`);
* a base whose `c_log` is `+-0 +-0j` (`base = 1`) gives `ValueError('math domain error')` from the
  division (complexobject.c:180-183), whatever `x` is;
* otherwise, when the base's `c_log` sets no `errno`, `log(x, base)` is `c_log(x) / c_log(base)`
  divided as Python divides complex numbers (`complex_div`), whatever `errno` `c_log(x)` left. -/
def CmathLogBase : Prop :=
  ∀ (K : CmathCore) (x : C),
    cmath_log K x none =
      (if (K.clog x).2 != .zero then .error (cmath_math_error (K.clog x).2) else .ok (K.clog x).1) ∧
    (∀ e, cmath_log K x (some (.error e)) = .error e) ∧
    (∀ b s1 s2, (K.clog b).1 = ⟨F64.zero s1, F64.zero s2⟩ →
      cmath_log K x (some (.ok b)) = .error (.valueError "math domain error")) ∧
    (∀ b, (K.clog b).2 = .zero → (_Py_c_quot (K.clog x).1 (K.clog b).1).2 = false →
      cmath_log K x (some (.ok b)) =
        match complex_div (.complex (K.clog x).1) (.complex (K.clog b).1) with
        | .ok (some q) => .ok q
        | .ok none => .error (.typeError "unreachable")
        | .error e => .error e)

theorem quot_zero (a : C) (s1 s2 : Bool) : (_Py_c_quot a ⟨F64.zero s1, F64.zero s2⟩).2 = true := by
  have e1 : F64.ge (absLt (F64.zero s1)) (absLt (F64.zero s2)) = true ∧
      F64.eq (absLt (F64.zero s1)) d0 = true ∧ d0.isNaN = false := by
    cases s1 <;> cases s2 <;> decide +kernel
  simp only [_Py_c_quot, e1.1, e1.2.1, ↓reduceIte, e1.2.2, Bool.false_and, Bool.false_eq_true]

theorem cmathLogBase_proven : CmathLogBase := by
  intro K x
  refine ⟨?_, fun e => ?_, fun b s1 s2 hb => ?_, fun b he hq => ?_⟩
  · unfold cmath_log
    generalize K.clog x = l
    obtain ⟨lx, e1⟩ := l
    rfl
  · unfold cmath_log
    generalize K.clog x = l
    obtain ⟨lx, e1⟩ := l
    rfl
  · have hq := quot_zero (K.clog x).1 s1 s2
    rw [← hb] at hq
    obtain ⟨_, _, _, _, _, clog⟩ := K
    simp only at hq ⊢
    unfold cmath_log
    simp only
    generalize clog x = l at hq ⊢
    obtain ⟨lx, e1⟩ := l
    simp only [bind, Except.bind]
    generalize clog b = l2 at hq ⊢
    obtain ⟨ly, e2⟩ := l2
    simp only at hq
    generalize _Py_c_quot lx ly = q at hq ⊢
    obtain ⟨qv, zd⟩ := q
    simp only at hq; subst hq
    simp [cmath_math_error]
  · obtain ⟨_, _, _, _, _, clog⟩ := K
    simp only at he hq ⊢
    unfold cmath_log
    simp only [complex_div, complexBinop]
    generalize clog x = l at hq ⊢
    obtain ⟨lx, e1⟩ := l
    simp only [bind, Except.bind]
    generalize clog b = l2 at he hq ⊢
    obtain ⟨ly, e2⟩ := l2
    simp only at he hq; subst he
    generalize _Py_c_quot lx ly = q at hq ⊢
    obtain ⟨qv, zd⟩ := q
    simp only at hq; subst hq
    simp

