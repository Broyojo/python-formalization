import PyLean.MathInt.FltFmod

/-!
# Property: `pow`

`math_pow_impl` (Modules/mathmodule.c:2366-2432) against `float.__pow__` (`float_pow`,
Objects/floatobject.c:686-803, modelled in `Binary64/Float.lean`): the two handle IEEE special
values with separate code, and for every C library `pow` that follows C99 Annex F they agree
wherever both return a float. Where they differ they differ as documented: `math.pow` raises
`ValueError` where `**` raises `ZeroDivisionError` (`0.0 ** -1`) or returns a complex number
(`(-8.0) ** (1/3)`), and both raise `OverflowError` on overflow.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- A C library `pow` that follows C99 Annex F (F.9.4.4) on finite arguments and reports only
range errors through `errno`:
* `pow(1, y)` and `pow(x, ±0)` are `1`;
* `pow(±0, y)` is `±0` for an odd integer `y > 0`, `+0` for other `y > 0`, and an infinity for
  `y < 0`;
* for `x > 0` the result is never a NaN, and `errno` is `0`, or `ERANGE` on an overflow to
  infinity or an underflow below `1.5`;
* `pow(-x, y) = ±pow(x, y)` for an integer `y` (negated when `y` is odd), with the same `errno`;
* `pow(x, y)` is a NaN for `x < 0` and a non-integer `y`. -/
structure AnnexFPow (cpow : CFun2) : Prop where
  one_base : ∀ y, y.isFinite = true → cpow c1 y = (c1, .zero)
  zero_exp : ∀ x s, x.isFinite = true → cpow x (F64.zero s) = (c1, .zero)
  zero_base_pos : ∀ s y, y.isFinite = true → F64.lt c0 y = true →
    (cpow (F64.zero s) y).1 = (if isOddInteger y then F64.zero s else F64.zero false) ∧
    ((cpow (F64.zero s) y).2 = .zero ∨ (cpow (F64.zero s) y).2 = .erange)
  zero_base_neg : ∀ s y, y.isFinite = true → F64.lt y c0 = true → (cpow (F64.zero s) y).1.isInf = true
  pos_base : ∀ x y, x.isFinite = true → y.isFinite = true → F64.lt c0 x = true → y.isZero = false →
    (cpow x y).1.isNaN = false ∧ ((cpow x y).2 = .zero ∨ ((cpow x y).2 = .erange ∧
      ((cpow x y).1.isInf = true ∨ F64.lt (F64.abs (cpow x y).1) c1p5 = true)))
  neg_base_int : ∀ x y, x.isFinite = true → y.isFinite = true → F64.lt c0 x = true →
    y.isZero = false → F64.eq y (F64.floor y) = true →
    cpow x.neg y = (if isOddInteger y then (cpow x y).1.neg else (cpow x y).1, (cpow x y).2)
  neg_base_frac : ∀ x y, x.isFinite = true → y.isFinite = true → F64.lt x c0 = true →
    F64.eq y (F64.floor y) = false → (cpow x y).1.isNaN = true

/-- For every Annex F `pow`: where `x ** y` (float `__pow__`) returns a float, `math.pow(x, y)`
returns the same float (or a NaN where it is a NaN); where `**` hands over to complex
exponentiation or raises `ZeroDivisionError`, `math.pow` raises `ValueError`; where `**` raises
`OverflowError`, so does `math.pow`. -/
def PowTwin : Prop :=
  ∀ cpow : CFun2, AnnexFPow cpow → ∀ x y : F64,
    let m := math_pow cpow (.float x) (.float y)
    match floatPowCore (fun a b => (cpow a b).1) x y with
    | .ok (.float v) => ∃ a, m = .ok a ∧ (a = v ∨ (a.isNaN = true ∧ v.isNaN = true))
    | .ok (.complexPow _ _) => m.raises "ValueError"
    | .error (.zeroDivisionError _) => m.raises "ValueError"
    | .error (.overflowError _) => m.raises "OverflowError"
    | .error _ => False

/-! ## Proof -/

theorem math_pow_eq (cpow : CFun2) (x y : F64) :
    math_pow cpow (.float x) (.float y) = finishErrno (math_pow_core cpow x y).1 (math_pow_core cpow x y).2 := by
  simp [math_pow, convDouble, bind, Except.bind]

theorem finish_ok_zero (r : F64) : finishErrno r .zero = .ok r := by simp [finishErrno]

theorem finish_edom (r : F64) : (finishErrno r .edom).raises "ValueError" :=
  ⟨.valueError "math domain error", by simp [finishErrno, is_error], rfl⟩

theorem finish_erange_inf {r : F64} (h : r.isInf = true) : (finishErrno r .erange).raises "OverflowError" := by
  refine ⟨.overflowError "math range error", ?_, rfl⟩
  rw [eq_inf_of_isInf h]
  cases r.sign <;> decide +kernel

theorem finish_erange_small {r : F64} (h : F64.lt (F64.abs r) c1p5 = true) : finishErrno r .erange = .ok r := by
  simp [finishErrno, is_error, h]

theorem c1_eq_d1 : c1 = d1 := rfl
theorem c0_eq_d0 : c0 = d0 := rfl
theorem c2_eq_d2 : c2 = d2 := rfl

theorem powTwin_proven : PowTwin := by
  intro cpow hA x y
  simp only []
  rw [math_pow_eq]
  have eqz : ∀ w : F64, F64.eq w d0 = w.isZero := fun w => eq_c0_iff
  -- 1. y == 0
  by_cases hy0 : y.isZero = true
  · have hyf := isFinite_of_isZero hy0
    have hfp : floatPowCore (fun a b => (cpow a b).1) x y = .ok (.float d1) := by
      unfold floatPowCore; simp [eqz, hy0]
    rw [hfp]
    refine ⟨d1, ?_, Or.inl rfl⟩
    unfold math_pow_core
    have hd1 : d1.isFinite = true := by decide +kernel
    rcases classify x with hx | hx | hx
    · rw [eq_zero_of_isZero hy0, hA.zero_exp x _ hx]
      simp [hx, isFinite_of_isZero (zero_isZero _), zero_isFinite, finish_ok_zero, c1_eq_d1, hd1]
    · simp [not_finite_of_inf hx, not_nan_of_inf hx, hx, isZeroC_eq, hy0, finish_ok_zero, c1_eq_d1,
        isNaN_false_of_finite hyf, (lt_c0_of_zero hy0).1]
    · have : x.isFinite = false := by
        cases h : x.isFinite
        · rfl
        · rw [isNaN_false_of_finite h] at hx; cases hx
      simp [this, hx, isZeroC_eq, hy0, finish_ok_zero, c1_eq_d1]
  have hy0' : y.isZero = false := by simpa using hy0
  -- 2. x is a NaN
  by_cases hxn : x.isNaN = true
  · have hfp : floatPowCore (fun a b => (cpow a b).1) x y = .ok (.float x) := by
      unfold floatPowCore; simp [eqz, hy0', hxn]
    rw [hfp]
    refine ⟨x, ?_, Or.inl rfl⟩
    have : x.isFinite = false := by
      cases h : x.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hxn; cases hxn
    unfold math_pow_core
    simp [this, hxn, isZeroC_eq, hy0', finish_ok_zero]
  have hxn' : x.isNaN = false := by simpa using hxn
  -- 3. y is a NaN
  by_cases hyn : y.isNaN = true
  · have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
        .ok (.float (if F64.eq x d1 then d1 else y)) := by
      unfold floatPowCore; simp [eqz, hy0', hxn', hyn]
    rw [hfp]
    have : y.isFinite = false := by
      cases h : y.isFinite
      · rfl
      · rw [isNaN_false_of_finite h] at hyn; cases hyn
    refine ⟨if F64.eq x d1 then d1 else y, ?_, Or.inl rfl⟩
    unfold math_pow_core
    simp [this, hxn', hyn, finish_ok_zero, c1_eq_d1]
    try rfl
  have hyn' : y.isNaN = false := by simpa using hyn
  have hd : d1.isFinite = true ∧ d1.isNaN = false ∧ d1.isInf = false := by decide +kernel
  -- 4. y is infinite
  by_cases hyi : y.isInf = true
  · have hyf : y.isFinite = false := not_finite_of_inf hyi
    have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
        .ok (.float (if F64.eq x.abs d1 then d1
          else if F64.gt y d0 == F64.gt x.abs d1 then y.abs else d0)) := by
      unfold floatPowCore; simp [eqz, hy0', hxn', hyn', hyi]
      split <;> (try split) <;> rfl
    rw [hfp]
    simp only []
    rcases classify x with hx | hx | hx
    · -- finite base
      have hxi := isInf_false_of_finite hx
      have hax : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact hx
      refine ⟨_, ?_, Or.inl rfl⟩
      unfold math_pow_core
      simp only [hx, hyf, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_true, ↓reduceIte,
        hxn', hyn', hxi, Bool.false_eq_true]
      rw [finish_ok_zero]
      congr 1
      rw [← c1_eq_d1, ← c0_eq_d0]
      have hy := eq_inf_of_isInf hyi
      cases hs : y.sign
      · rw [hs] at hy; subst hy
        have h1 : F64.lt c0 (F64.inf false) = true := by decide +kernel
        have h2 : F64.gt (F64.inf false) c0 = true := by decide +kernel
        have h3 : F64.lt (F64.inf false) c0 = false := by decide +kernel
        simp only [h1, h3, h2, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          F64.gt]
        by_cases he : F64.eq x.abs c1 = true
        · simp [he]
        · simp only [he, Bool.false_eq_true, ↓reduceIte]
          cases hl : F64.lt c1 x.abs
          · simp
          · simp [show (F64.inf false).abs = F64.inf false by decide +kernel]
      · rw [hs] at hy; subst hy
        have h1 : F64.lt c0 (F64.inf true) = false := by decide +kernel
        have h2 : F64.gt (F64.inf true) c0 = false := by decide +kernel
        have h3 : F64.lt (F64.inf true) c0 = true := by decide +kernel
        simp only [h1, h3, h2, Bool.true_and, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
          F64.gt]
        by_cases he : F64.eq x.abs c1 = true
        · simp [he]
        · simp only [he, Bool.false_eq_true, ↓reduceIte]
          cases hl : F64.lt x.abs c1
          · -- `|x| > 1`
            have hgt : F64.lt c1 x.abs = true := by
              have hc1 : c1.isFinite = true ∧ c1.toRat = 1 := by decide +kernel
              rw [lt_of_finite hax hc1.1] at hl
              rw [lt_of_finite hc1.1 hax]
              rw [eq_of_finite hax hc1.1] at he
              simp at hl he ⊢; grind
            simp [hgt]
          · have hng : F64.lt c1 x.abs = false := by
              have hc1 : c1.isFinite = true ∧ c1.toRat = 1 := by decide +kernel
              rw [lt_of_finite hax hc1.1] at hl
              rw [lt_of_finite hc1.1 hax]
              simp at hl ⊢; grind
            simp [hng, show (F64.inf true).neg = F64.inf false by decide +kernel,
              show (F64.inf true).abs = F64.inf false by decide +kernel]
    · -- infinite base and exponent
      refine ⟨_, ?_, Or.inl rfl⟩
      unfold math_pow_core
      simp only [not_finite_of_inf hx, hyf, Bool.not_false, Bool.true_or, ↓reduceIte, hxn', hyn', hx,
        Bool.false_eq_true]
      rw [finish_ok_zero]
      congr 1
      have hxe := eq_inf_of_isInf hx
      have hye := eq_inf_of_isInf hyi
      generalize x.sign = sx at hxe
      generalize y.sign = sy at hye
      subst hxe; subst hye
      cases sx <;> cases sy <;> decide +kernel
    · rw [hxn'] at hx; cases hx
  have hyi' : y.isInf = false := by simpa using hyi
  have hyf : y.isFinite = true := by
    rcases classify y with h | h | h
    · exact h
    · rw [hyi'] at h; cases h
    · rw [hyn'] at h; cases h
  have hlt0 : ∀ w : F64, w.isFinite = true → w.isZero = false →
      (F64.lt c0 w = true ∧ F64.lt w c0 = false) ∨ (F64.lt c0 w = false ∧ F64.lt w c0 = true) := by
    intro w hw hz
    have hne : w.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hw).2 h] at hz; cases hz
    rw [lt_of_finite c0_facts.1 hw, lt_of_finite hw c0_facts.1, c0_facts.2.2.1]
    by_cases h : 0 < w.toRat
    · left; simp [h]; grind
    · right; simp [h]; grind
  -- 5. x is infinite
  by_cases hxi : x.isInf = true
  · have hxf := not_finite_of_inf hxi
    have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
        .ok (.float (if F64.gt y d0 then (if isOddInteger y then x else x.abs)
          else (if isOddInteger y then F64.copysign d0 x else d0))) := by
      unfold floatPowCore; simp [eqz, hy0', hxn', hyn', hyi', hxi]
      split <;> (try split) <;> rfl
    rw [hfp]
    refine ⟨_, ?_, Or.inl rfl⟩
    unfold math_pow_core
    simp only [hxf, Bool.not_false, Bool.true_or, ↓reduceIte, hxn', hyn', hxi, Bool.false_eq_true,
      hyf, Bool.true_and, isZeroC_eq, hy0']
    rw [finish_ok_zero]
    congr 1
    try simp only [F64.gt, isOddInteger, ← c1_eq_d1, ← c0_eq_d0, ← c2_eq_d2]
  have hxi' : x.isInf = false := by simpa using hxi
  have hxf : x.isFinite = true := by
    rcases classify x with h | h | h
    · exact h
    · rw [hxi'] at h; cases h
    · rw [hxn'] at h; cases h
  have hfinite : math_pow_core cpow x y =
      (let (r, e0) := cpow x y
       let errno : Errno :=
         if !r.isFinite then (if r.isNaN then .edom else if isZeroC x then .edom else .erange) else e0
       (r, errno)) := by
    unfold math_pow_core; simp [hxf, hyf]
  rw [hfinite]
  simp only []
  -- 6. x is a zero
  by_cases hxz : x.isZero = true
  · have hxe := eq_zero_of_isZero hxz
    rcases hlt0 y hyf hy0' with ⟨hp, _⟩ | ⟨_, hn⟩
    · have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
          .ok (.float (if isOddInteger y then x else d0)) := by
        unfold floatPowCore
        have : F64.lt y d0 = false := by
          rcases hlt0 y hyf hy0' with ⟨_, h⟩ | ⟨h, _⟩
          · exact h
          · rw [hp] at h; cases h
        simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz, this]
      rw [hfp]
      obtain ⟨hv, he⟩ := hA.zero_base_pos x.sign y hyf hp
      rw [← hxe] at hv he
      refine ⟨_, ?_, Or.inl rfl⟩
      have hrf : (cpow x y).1.isFinite = true := by
        rw [hv]; split
        · rw [hxe]; exact zero_isFinite _
        · exact zero_isFinite _
      simp only [hrf, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases he with he | he
      · rw [he, finish_ok_zero, hv]; rfl
      · rw [he, finish_erange_small, hv]
        · rfl
        · rw [hv]; split
          · rw [hxe]; cases x.sign <;> decide +kernel
          · decide +kernel
    · have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
          .error (.zeroDivisionError "zero to a negative power") := by
        unfold floatPowCore
        have hn' : F64.lt y d0 = true := hn
        simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz, hn']
      rw [hfp]
      have hinf := hA.zero_base_neg x.sign y hyf hn
      rw [← hxe] at hinf
      simp only [not_finite_of_inf hinf, Bool.not_false, ↓reduceIte, not_nan_of_inf hinf,
        Bool.false_eq_true, isZeroC_eq, hxz]
      exact finish_edom _
  have hxz' : x.isZero = false := by simpa using hxz
  -- the result of the C pow on a positive base, through `finishErrno`
  have posOut : ∀ (b : F64), b.isFinite = true → F64.lt c0 b = true → ∀ (neg : Bool),
      let r := (cpow b y).1
      let r' := if neg then r.neg else r
      let errno : Errno :=
        if !r'.isFinite then (if r'.isNaN then .edom else if isZeroC x then .edom else .erange)
        else (cpow b y).2
      (r.isInf = true → (finishErrno r' errno).raises "OverflowError") ∧
      (r.isInf = false → finishErrno r' errno = .ok r') := by
    intro b hb hbp neg
    obtain ⟨hnn, herr⟩ := hA.pos_base b y hb hyf hbp hy0'
    simp only []
    have hxz0 : isZeroC x = false := by rw [isZeroC_eq]; exact hxz'
    constructor
    · intro hi
      have hi' : (if neg then (cpow b y).1.neg else (cpow b y).1).isInf = true := by
        split
        · rw [neg_isInf]; exact hi
        · exact hi
      simp only [not_finite_of_inf hi', Bool.not_false, ↓reduceIte, not_nan_of_inf hi',
        Bool.false_eq_true, hxz0]
      exact finish_erange_inf hi'
    · intro hi
      have hf : (cpow b y).1.isFinite = true := by
        rcases classify (cpow b y).1 with h | h | h
        · exact h
        · rw [hi] at h; cases h
        · rw [hnn] at h; cases h
      have hf' : (if neg then (cpow b y).1.neg else (cpow b y).1).isFinite = true := by
        split
        · rw [neg_isFinite]; exact hf
        · exact hf
      simp only [hf', Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rcases herr with he | ⟨he, hsmall | hsmall⟩
      · rw [he, finish_ok_zero]
      · rw [hsmall] at hi; cases hi
      · rw [he, finish_erange_small]
        split
        · rw [show F64.abs (cpow b y).1.neg = F64.abs (cpow b y).1 by
            unfold F64.abs; rw [(neg_fields _).1, neg_neg]
            cases (cpow b y).1.sign <;> rfl]
          exact hsmall
        · exact hsmall
  rcases hlt0 x hxf hxz' with ⟨hxp, hxn0⟩ | ⟨hxp, hxn0⟩
  · -- positive base
    have hxn0' : F64.lt x d0 = false := hxn0
    by_cases h1 : F64.eq x d1 = true
    · have hxe : x = c1 := by
        have hc : c1.isFinite = true ∧ c1.toRat = 1 ∧ c1.isZero = false := by decide +kernel
        rw [eq_of_finite hxf hd.1] at h1
        apply toRat_inj hxf hc.1 hxz'
        rw [hc.2.1]; simpa [show d1.toRat = 1 by decide +kernel] using h1
      have hfp : floatPowCore (fun a b => (cpow a b).1) x y = .ok (.float d1) := by
        unfold floatPowCore
        simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz', hxn0', h1]
      rw [hfp]
      refine ⟨d1, ?_, Or.inl rfl⟩
      rw [hxe, hA.one_base y hyf]
      simp [hd.1, finish_ok_zero, c1_eq_d1]
    · have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
          (if (cpow x y).1.isInf then .error (.overflowError "~[Errno 34] Numerical result out of range")
           else .ok (.float (cpow x y).1)) := by
        unfold floatPowCore
        simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz', hxn0', h1]
      rw [hfp]
      obtain ⟨o1, o2⟩ := posOut x hxf hxp false
      simp only [Bool.false_eq_true, ↓reduceIte] at o1 o2
      cases hi : (cpow x y).1.isInf
      · exact ⟨_, o2 hi, Or.inl rfl⟩
      · exact o1 hi
  · -- negative base
    have hxn0' : F64.lt x d0 = true := hxn0
    have hiv : (F64.neg x).isFinite = true ∧ F64.lt c0 (F64.neg x) = true ∧ (F64.neg x).isZero = false := by
      refine ⟨by rw [neg_isFinite]; exact hxf, ?_, by rw [neg_isZero]; exact hxz'⟩
      rw [lt_of_finite c0_facts.1 (by rw [neg_isFinite]; exact hxf), toRat_neg, c0_facts.2.2.1]
      rw [lt_of_finite hxf c0_facts.1, c0_facts.2.2.1] at hxn0
      simp at hxn0 ⊢; grind
    by_cases hint : F64.eq y (F64.floor y) = true
    · have hne : F64.ne y (F64.floor y) = false := by simp [F64.ne, hint]
      have hcp := hA.neg_base_int (F64.neg x) y hiv.1 hyf hiv.2.1 hy0' hint
      rw [neg_neg] at hcp
      rw [hcp]
      simp only []
      by_cases h1 : F64.eq (F64.neg x) d1 = true
      · have hxe : F64.neg x = c1 := by
          have hc : c1.isFinite = true ∧ c1.toRat = 1 ∧ c1.isZero = false := by decide +kernel
          rw [eq_of_finite hiv.1 hd.1] at h1
          apply toRat_inj hiv.1 hc.1 hiv.2.2
          rw [hc.2.1]; simpa [show d1.toRat = 1 by decide +kernel] using h1
        have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
            .ok (.float (if isOddInteger y then dm1 else d1)) := by
          unfold floatPowCore
          simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz', hxn0', hne, h1]
        rw [hfp]
        refine ⟨_, ?_, Or.inl rfl⟩
        rw [hxe, hA.one_base y hyf]
        have : (if isOddInteger y = true then c1.neg else c1).isFinite = true := by
          split <;> decide +kernel
        simp only [this, Bool.not_true, Bool.false_eq_true, ↓reduceIte, finish_ok_zero]
        split <;> rfl
      · have hfp : floatPowCore (fun a b => (cpow a b).1) x y =
            (if (cpow (F64.neg x) y).1.isInf then
              .error (.overflowError "~[Errno 34] Numerical result out of range")
             else .ok (.float (if isOddInteger y then (cpow (F64.neg x) y).1.neg
               else (cpow (F64.neg x) y).1))) := by
          unfold floatPowCore
          simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz', hxn0', hne, h1]
        rw [hfp]
        obtain ⟨o1, o2⟩ := posOut (F64.neg x) hiv.1 hiv.2.1 (isOddInteger y)
        cases hi : (cpow (F64.neg x) y).1.isInf
        · simp only [Bool.false_eq_true, ↓reduceIte]
          exact ⟨_, o2 hi, Or.inl rfl⟩
        · simp only [↓reduceIte]
          exact o1 hi
    · have hint' : F64.eq y (F64.floor y) = false := by simpa using hint
      have hne : F64.ne y (F64.floor y) = true := by simp [F64.ne, hint']
      have hfp : floatPowCore (fun a b => (cpow a b).1) x y = .ok (.complexPow x y) := by
        unfold floatPowCore
        simp [eqz, hy0', hxn', hyn', hyi', hxi', hxz', hxn0', hne]
      rw [hfp]
      have hn := hA.neg_base_frac x y hxf hyf hxn0 hint'
      have hnf : (cpow x y).1.isFinite = false := by
        cases h : (cpow x y).1.isFinite
        · rfl
        · rw [isNaN_false_of_finite h] at hn; cases hn
      simp only [hnf, Bool.not_false, ↓reduceIte, hn]
      exact finish_edom _


end PyLean.MathInt
