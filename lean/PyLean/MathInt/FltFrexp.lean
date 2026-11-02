import PyLean.MathInt.FltLemmas

/-!
# Properties: `frexp` and `ldexp`

`math_frexp_impl` and `math_ldexp_impl` (Modules/mathmodule.c:1446-1541) against
Doc/library/math.rst: `frexp` splits `x` into `m * 2**e` with `0.5 <= abs(m) < 1`, `ldexp(x, i)`
is `x * 2**i` for every int `i` (the clamping of huge exponents to `LONG_MIN`/`LONG_MAX` and to
the `int` range included), and `ldexp` inverts `frexp`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- `x * 2**i`, rounded once, as the documentation describes `ldexp(x, i)`: zeros, infinities
and NaNs unchanged, an `OverflowError` when the rounded value is infinite. -/
def ldexpSpec (x : F64) (i : Int) : Py F64 :=
  if x.isZero || !x.isFinite then .ok x
  else
    let r := F64.ofRat (x.toRat * pw i)
    if r.isInf then .error (.overflowError "math range error") else .ok r

/-- `frexp` and `ldexp` for every argument object.

* Conversion errors of `x` are raised by both, before `i` is looked at.
* `ldexp(x, i)` for an `int` (or `bool`) `i` is `x * 2**i` rounded once (`ldexpSpec`), for every
  `i`, however large; any other `i` raises
  `TypeError("Expected an int as second argument to ldexp.")`.
* `frexp(x)` is `(m, e)` with `0.5 <= abs(m) < 1.0` and `x == m * 2**e` exactly for finite
  nonzero `x`, and `(x, 0)` otherwise (Doc/library/math.rst, "frexp").
* `ldexp(*frexp(x))` gives back `x`, bit for bit ("essentially the inverse"). -/
def FrexpLdexp : Prop :=
  (∀ o e, convDouble o = .error e → math_frexp o = .error e ∧ ∀ oi, math_ldexp o oi = .error e) ∧
  (∀ o x, convDouble o = .ok x → ∀ oi i, oi.intVal = some i → math_ldexp o oi = ldexpSpec x i) ∧
  (∀ o x, convDouble o = .ok x → ∀ oi, oi.intVal = none →
    math_ldexp o oi = .error (.typeError "Expected an int as second argument to ldexp.")) ∧
  (∀ o x, convDouble o = .ok x → ∃ m e, math_frexp o = .ok (m, e) ∧
    (x.isFinite = true → x.isZero = false →
      1 / 2 ≤ Rat.abs m.toRat ∧ Rat.abs m.toRat < 1 ∧ m.toRat * pw e = x.toRat) ∧
    ((x.isFinite = false ∨ x.isZero = true) → m = x ∧ e = 0) ∧
    math_ldexp (.float m) (.int e) = .ok x)

theorem clampLong_gt {i : Int} : (INT_MAX < clampLong i) = (INT_MAX < i) := by
  unfold clampLong LONG_MAX LONG_MIN INT_MAX
  apply propext
  split
  · omega
  · split <;> omega

theorem clampLong_lt {i : Int} : (clampLong i < INT_MIN) = (i < INT_MIN) := by
  unfold clampLong LONG_MAX LONG_MIN INT_MIN
  apply propext
  split
  · omega
  · split <;> omega

theorem clampLong_mid {i : Int} (h1 : ¬ INT_MAX < i) (h2 : ¬ i < INT_MIN) : clampLong i = i := by
  unfold clampLong LONG_MAX LONG_MIN
  unfold INT_MAX at h1; unfold INT_MIN at h2
  split
  · omega
  · split <;> omega

theorem abs_scale (a : Rat) (i : Int) : Rat.abs (a * pw i) = Rat.abs a * pw i :=
  abs_mul_pos a (pw_pos i)

theorem copysign_c0 (x : F64) : F64.copysign c0 x = F64.zero x.sign := by
  unfold F64.copysign
  cases hs : x.sign <;> decide +kernel

theorem copysign_inf (x : F64) : F64.copysign cInf x = F64.inf x.sign := by
  unfold F64.copysign
  cases hs : x.sign <;> decide +kernel

theorem finishErrno_zero (r : F64) : finishErrno r .zero = .ok r := by
  simp [finishErrno]

theorem finishErrno_inf (s : Bool) :
    finishErrno (F64.inf s) .erange = .error (.overflowError "math range error") := by
  cases s <;> decide +kernel

theorem ofRat_ne_inf_of_tiny {q : Rat} (hq : q ≠ 0) (h : Rat.abs q < pw (-1075)) :
    (ofRat q).isInf = false := by
  rw [ofRat_tiny hq h]; exact isInf_false_of_finite (zero_isFinite _)

/-- The value of a finite nonzero `x` scaled by `2 ** i`, for `i` past the `int` range. -/
theorem big_scale {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) {i : Int}
    (hi : 2200 < i) : overflowLimit ≤ Rat.abs (x.toRat * pw i) := by
  rw [abs_scale]
  have h1 := abs_toRat_ge_tiny hf hz
  have h2 : pw 1126 ≤ pw (-1074) * pw i := by rw [← pw_add]; exact pw_le (by omega)
  have h3 : pw (-1074) * pw i ≤ Rat.abs x.toRat * pw i :=
    Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (pw_pos i))
  have h4 : overflowLimit ≤ pw 1126 := Rat.le_trans limit_le_pw1024 (pw_le (by omega))
  exact Rat.le_trans h4 (Rat.le_trans h2 h3)

theorem tiny_scale {x : F64} (hf : x.isFinite = true) {i : Int} (hi : i < -2200) :
    Rat.abs (x.toRat * pw i) < pw (-1075) := by
  rw [abs_scale]
  have h1 : Rat.abs x.toRat < pw 1024 := qlt_le (abs_toRat_lt hf) limit_le_pw1024
  have h2 : Rat.abs x.toRat * pw i < pw 1024 * pw i := (Rat.mul_lt_mul_right (pw_pos i)).2 h1
  have h3 : pw 1024 * pw i ≤ pw (-1176) := by rw [← pw_add]; exact pw_le (by omega)
  have h4 : pw (-1176) ≤ pw (-1075) := pw_le (by omega)
  exact qlt_le h2 (Rat.le_trans h3 h4)

theorem scale_ne_zero {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) (i : Int) :
    x.toRat * pw i ≠ 0 := by
  have h : x.toRat ≠ 0 := fun h0 => by rw [(isZero_iff_toRat hf).2 h0] at hz; cases hz
  intro h0
  rcases Rat.mul_eq_zero.1 h0 with h1 | h1
  · exact h h1
  · exact pw_ne i h1

theorem scale_neg {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) (i : Int) :
    decide (x.toRat * pw i < 0) = x.sign := by
  have hs := toRat_neg_iff_sign hf hz
  have hp := pw_pos i
  cases hsx : x.sign
  · have : ¬ x.toRat < 0 := by rw [hs, hsx]; simp
    have : ¬ x.toRat * pw i < 0 := by
      intro h
      have := Rat.mul_nonneg (Rat.not_lt.1 this) (Rat.le_of_lt hp)
      exact absurd h (Rat.not_lt.2 this)
    simp [this]
  · have h1 : x.toRat < 0 := by rw [hs, hsx]
    have : x.toRat * pw i < 0 := by
      have := Rat.mul_lt_mul_of_pos_right h1 hp
      rwa [Rat.zero_mul] at this
    simp [this]

/-- The core of `math_ldexp_impl` on a finite nonzero `x`. -/
theorem ldexp_core {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) (i : Int) :
    (let exp := clampLong i
     let (r, errno) : F64 × Errno :=
       if isZeroC x || !x.isFinite then (x, .zero)
       else if INT_MAX < exp then (F64.copysign cInf x, .erange)
       else if exp < INT_MIN then (F64.copysign c0 x, .zero)
       else
         let r := F64.ldexp x exp
         (r, if r.isInf then .erange else .zero)
     finishErrno r errno) = ldexpSpec x i := by
  have hnz : (isZeroC x || !x.isFinite) = false := by rw [isZeroC_eq, hz, hf]; rfl
  have hspec : (x.isZero || !x.isFinite) = false := by rw [hz, hf]; rfl
  have hne := scale_ne_zero hf hz i
  have hsg := scale_neg hf hz i
  simp only [hnz, Bool.false_eq_true, ↓reduceIte, clampLong_gt, clampLong_lt, ldexpSpec, hspec]
  by_cases h1 : INT_MAX < i
  · have hb : 2200 < i := by unfold INT_MAX at h1; omega
    have hr := ofRat_big (big_scale hf hz hb)
    rw [hsg] at hr
    simp only [h1, ↓reduceIte, copysign_inf, finishErrno_inf, hr, (inf_bits _).1]
  · by_cases h2 : i < INT_MIN
    · have hb : i < -2200 := by unfold INT_MIN at h2; omega
      have hr := ofRat_tiny hne (tiny_scale hf hb)
      rw [hsg] at hr
      simp only [h1, h2, ↓reduceIte, copysign_c0, finishErrno_zero, hr,
        isInf_false_of_finite (zero_isFinite _), Bool.false_eq_true]
    · simp only [h1, h2, ↓reduceIte, clampLong_mid h1 h2]
      have hl : F64.ldexp x i = ofRat (x.toRat * pw i) := by
        unfold F64.ldexp
        have hn1 : (!x.isFinite || x.isZero) = false := by rw [hf, hz]; rfl
        simp only [hn1, Bool.false_eq_true, ↓reduceIte]
        by_cases hb : 2200 < i
        · simp only [hb, decide_true, ↓reduceIte]
          rw [ofRat_big (big_scale hf hz hb), hsg]
        · by_cases hc : i < -2200
          · simp only [hb, hc, decide_true, decide_false, ↓reduceIte]
            rw [ofRat_tiny hne (tiny_scale hf hc), hsg]
          · simp only [hb, hc, decide_false, ↓reduceIte, dyadic_eq]
            congr 2
            show ((1 : Nat) : Rat) * pw i = pw i
            rw [show ((1 : Nat) : Rat) = 1 from rfl, Rat.one_mul]
      rw [hl]
      cases hi : (ofRat (x.toRat * pw i)).isInf
      · simp [finishErrno]
      · have : ofRat (x.toRat * pw i) = F64.inf x.sign := by
          rw [← hsg]
          exact ofRat_big ((ofRat_isInf _).1 hi)
        simp only [↓reduceIte]
        rw [this, finishErrno_inf]

theorem ldexp_of_int {o : Arg} {x : F64} (hx : convDouble o = .ok x) {oi : Arg} {i : Int}
    (hi : oi.intVal = some i) : math_ldexp o oi = ldexpSpec x i := by
  unfold math_ldexp
  rw [hx]
  simp only [bind, Except.bind, hi, pure, Except.pure]
  by_cases hs : (x.isZero || !x.isFinite) = true
  · have hz : (isZeroC x || !x.isFinite) = true := by rw [isZeroC_eq]; exact hs
    simp only [hz, ↓reduceIte, ldexpSpec, hs, finishErrno_zero]
  · have hs' : (x.isZero || !x.isFinite) = false := by simpa using hs
    have hf : x.isFinite = true := by
      cases h : x.isFinite
      · rw [h] at hs'; simp at hs'
      · rfl
    have hz : x.isZero = false := by
      cases h : x.isZero
      · rfl
      · rw [h] at hs'; simp at hs'
    exact ldexp_core hf hz i

theorem frexp_parts {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) :
    let p := F64.frexp x
    p.1.isFinite = true ∧ p.1.isZero = false ∧ p.1.toRat * pw p.2 = x.toRat ∧
    p.1.toRat = x.toRat * pw (-p.2) ∧ -1073 ≤ p.2 ∧ p.2 ≤ 1024 := by
  have hm := mant_pos_of_not_zero hz
  have hb1 : 1 ≤ Nat.log2 x.mant + 1 := by omega
  have hb2 : Nat.log2 x.mant + 1 ≤ 53 := by
    have := mant_lt x
    have : Nat.log2 x.mant < 53 := (Nat.log2_lt (by omega)).2 this
    omega
  generalize hb : Nat.log2 x.mant + 1 = b at hb1 hb2
  have hp : F64.frexp x =
      (ofRat (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b)), x.lsbExp + b) := by
    simp [F64.frexp, hf, hz, hb]
  have hv : mkRat x.mant (2 ^ b) = (x.mant : Rat) * pw (-(b : Int)) := by
    rw [Rat.mkRat_eq_div, pw_neg, pw_natCast]
    push_cast
    rfl
  have hrep : Rep binary64 (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b)) := by
    refine ⟨x.mant, -(b : Int), mant_lt x, by simp [Fmt.etiny, binary64]; omega, ?_⟩
    rw [hv]; split
    · right; rfl
    · left; rfl
  have hval_nonneg : 0 ≤ (x.mant : Rat) * pw (-(b : Int)) :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  have hsmall : Rat.abs (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b)) <
      overflowLimit := by
    have hlt : (x.mant : Rat) * pw (-(b : Int)) < 1 := by
      have h2 : (x.mant : Rat) < ((2 ^ b : Nat) : Rat) := by
        apply Rat.natCast_lt_natCast.2
        rw [← hb]; exact Nat.lt_log2_self
      rw [← pw_natCast] at h2
      have := (Rat.mul_lt_mul_right (pw_pos (-(b : Int)))).2 h2
      rwa [← pw_add, show ((b : Nat) : Int) + -(b : Int) = 0 by omega, pw_zero] at this
    have h1 : (1 : Rat) ≤ overflowLimit := by
      have := limit_le_pw1024
      unfold overflowLimit
      have a : (1 : Rat) ≤ pw 970 := by
        have := pw_le (show (0 : Int) ≤ 970 by omega); rwa [pw_zero] at this
      have b' : (1 : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := by
        have : ((1 : Nat) : Rat) ≤ ((2 ^ 54 - 1 : Nat) : Rat) := Rat.natCast_le_natCast.2 (by decide)
        simpa using this
      have := Rat.mul_le_mul_of_nonneg_left a (Rat.le_trans (by decide) b')
      rw [Rat.mul_one] at this
      exact Rat.le_trans b' this
    rw [hv]
    split
    · rw [abs_neg, abs_of_nonneg hval_nonneg]; grind
    · rw [abs_of_nonneg hval_nonneg]; grind
  have hex := ofRat_exact hrep hsmall
  have hmf := (ofRat_isFinite _).2 hsmall
  have hxv := toRat_of_finite hf
  have hlsb1 := lsbExp_ge x
  have hlsb2 := lsbExp_le x hf
  rw [hp]
  simp only []
  have hsc : x.toRat * pw (-(x.lsbExp + b)) =
      (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b)) := by
    rw [hxv, hv]
    have e : pw x.lsbExp * pw (-(x.lsbExp + b)) = pw (-(b : Int)) := by
      rw [← pw_add]; congr 1; omega
    split
    · rw [Rat.neg_mul, Rat.mul_assoc, e]
    · rw [Rat.mul_assoc, e]
  have hm1 : (ofRat (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b))).toRat =
      x.toRat * pw (-(x.lsbExp + b)) := by rw [hex, hsc]
  refine ⟨hmf, ?_, ?_, hm1, by omega, by omega⟩
  · cases hc : (ofRat (if x.sign then -mkRat x.mant (2 ^ b) else mkRat x.mant (2 ^ b))).isZero
    · rfl
    · exfalso
      have h0 := toRat_of_isZero hc
      rw [hm1] at h0
      exact scale_ne_zero hf hz _ h0
  · rw [hm1, Rat.mul_assoc, ← pw_add, show -(x.lsbExp + (b : Int)) + (x.lsbExp + b) = 0 by omega,
      pw_zero, Rat.mul_one]

theorem frexpLdexp_proven : FrexpLdexp := by
  refine ⟨?_, fun o x hx oi i hi => ldexp_of_int hx hi, ?_, ?_⟩
  · intro o e he
    refine ⟨?_, fun oi => ?_⟩
    · simp [math_frexp, he, bind, Except.bind]
    · simp [math_ldexp, he, bind, Except.bind]
  · intro o x hx oi hi
    simp [math_ldexp, hx, hi, bind, Except.bind]
  · intro o x hx
    by_cases hs : (x.isNaN || x.isInf || isZeroC x) = true
    · refine ⟨x, 0, ?_, ?_, fun _ => ⟨rfl, rfl⟩, ?_⟩
      · simp [math_frexp, hx, hs, bind, Except.bind, pure, Except.pure]
      · intro hf hz
        rw [isZeroC_eq, isNaN_false_of_finite hf, isInf_false_of_finite hf, hz] at hs
        simp at hs
      · rw [ldexp_of_int (o := .float x) rfl (oi := .int 0) rfl]
        unfold ldexpSpec
        have : (x.isZero || !x.isFinite) = true := by
          rw [isZeroC_eq] at hs
          rcases classify x with h | h | h
          · rw [isNaN_false_of_finite h, isInf_false_of_finite h] at hs
            simp at hs; simp [hs]
          · rw [not_finite_of_inf h]; simp
          · have : x.isFinite = false := by
              cases hc : x.isFinite
              · rfl
              · rw [isNaN_false_of_finite hc] at h; cases h
            rw [this]; simp
        simp [this]
    · have hs' : (x.isNaN || x.isInf || isZeroC x) = false := by simpa using hs
      have hf : x.isFinite = true := by
        rcases classify x with h | h | h
        · exact h
        · rw [h] at hs'; simp at hs'
        · rw [h] at hs'; simp at hs'
      have hz : x.isZero = false := by
        rw [isZeroC_eq] at hs'; simp at hs'; exact hs'.2
      obtain ⟨hmf, hmz, hmul, hm, he1, he2⟩ := frexp_parts hf hz
      refine ⟨(F64.frexp x).1, (F64.frexp x).2, ?_, ?_, ?_, ?_⟩
      · simp [math_frexp, hx, hs', bind, Except.bind, pure, Except.pure]
      · intro _ _
        obtain ⟨b1, b2⟩ := frexp_exp_bounds hf hz
        refine ⟨?_, ?_, hmul⟩
        · rw [hm, abs_scale]
          have := Rat.mul_le_mul_of_nonneg_right b1 (Rat.le_of_lt (pw_pos (-(F64.frexp x).2)))
          rwa [← pw_add, show (F64.frexp x).2 - 1 + -(F64.frexp x).2 = -1 by omega,
            show pw (-1) = 1 / 2 by rw [pw_neg, pw_one]; decide +kernel] at this
        · rw [hm, abs_scale]
          have := (Rat.mul_lt_mul_right (pw_pos (-(F64.frexp x).2))).2 b2
          rwa [← pw_add, show (F64.frexp x).2 + -(F64.frexp x).2 = 0 by omega, pw_zero] at this
      · intro h
        rcases h with h | h
        · rw [hf] at h; cases h
        · rw [hz] at h; cases h
      · rw [ldexp_of_int (o := .float (F64.frexp x).1) rfl (oi := .int (F64.frexp x).2) rfl]
        unfold ldexpSpec
        have hn : ((F64.frexp x).1.isZero || !(F64.frexp x).1.isFinite) = false := by
          rw [hmz, hmf]; rfl
        simp only [hn, Bool.false_eq_true, ↓reduceIte, hmul, ofRat_toRat hf hz,
          isInf_false_of_finite hf]

end PyLean.MathInt
