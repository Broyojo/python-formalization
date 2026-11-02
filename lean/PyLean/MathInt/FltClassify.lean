import PyLean.MathInt.FltFns
import PyLean.Binary64.Props3

/-!
# Properties: `isfinite`, `isnan`, `isinf`, `isnormal`, `issubnormal`, `signbit`

The six classification functions of `Modules/mathmodule.c` against the documentation
(Doc/library/math.rst): what each says in terms of values, that they partition the
floats, that the two `#if` branches of `issubnormal` agree, and that `signbit` agrees
with `copysign`.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

theorem eq_self_of_not_nan {x : F64} (h : x.isNaN = false) : F64.eq x x = true := by
  unfold F64.eq
  cases hi : x.isInf <;> simp [h, hi]

theorem eq_self_of_nan {x : F64} (h : x.isNaN = true) : F64.eq x x = false := by
  unfold F64.eq; simp [h]

theorem inf_bits (s : Bool) : (F64.inf s).isInf = true ∧ (F64.inf s).sign = s := by
  cases s <;> decide +kernel

theorem eq_inf_iff (x : F64) (s : Bool) : F64.eq x (F64.inf s) = (x.isInf && x.sign == s) := by
  obtain ⟨h1, h2⟩ := inf_bits s
  have hn : (F64.inf s).isNaN = false := not_nan_of_inf h1
  unfold F64.eq
  rw [hn, h1, h2]
  cases hxn : x.isNaN
  · simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte, Bool.or_true, Bool.true_and]
    cases hxi : x.isInf
    · simp
    · simp
  · have : x.isInf = false := not_inf_of_nan hxn
    simp [this]

/-- The value of a finite nonzero float lies below `2 ** -1022` exactly when its biased
exponent is `0`. -/
theorem subnormal_iff {x : F64} (hf : x.isFinite = true) (hz : x.isZero = false) :
    x.bexp = 0 ↔ Rat.abs x.toRat < pw (-1022) := by
  have hm0 : 0 ≤ (x.mant : Rat) * pw x.lsbExp :=
    Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  have habs : Rat.abs x.toRat = (x.mant : Rat) * pw x.lsbExp := by
    rw [toRat_of_finite hf]
    split
    · rw [abs_neg, abs_of_nonneg hm0]
    · rw [abs_of_nonneg hm0]
  rw [habs]
  have h52 : pw (-1022) = ((2 ^ 52 : Nat) : Rat) * pw (-1074) := by
    rw [← pw_natCast, ← pw_add]; rfl
  have hfr := frac_lt x
  constructor
  · intro hb
    have hm : x.mant = x.frac := by unfold mant; simp [hb]
    have hl : x.lsbExp = -1074 := by unfold lsbExp; rw [hb]; rfl
    rw [hm, hl, h52]
    apply Rat.mul_lt_mul_of_pos_right _ (pw_pos _)
    exact Rat.natCast_lt_natCast.2 hfr
  · intro hlt
    apply Classical.byContradiction
    intro hb
    have hm : x.mant = 2 ^ 52 + x.frac := by unfold mant; simp [hb]
    have hl : -1074 ≤ x.lsbExp := lsbExp_ge x
    have h1 : ((2 ^ 52 : Nat) : Rat) ≤ (x.mant : Rat) := by
      rw [hm]; exact Rat.natCast_le_natCast.2 (by omega)
    have h2 : pw (-1074) ≤ pw x.lsbExp := pw_le hl
    have h3 : ((2 ^ 52 : Nat) : Rat) * pw (-1074) ≤ (x.mant : Rat) * pw x.lsbExp := by
      have a1 := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt (pw_pos (-1074)))
      have a2 := Rat.mul_le_mul_of_nonneg_left h2 (Rat.natCast_nonneg : (0 : Rat) ≤ (x.mant : Rat))
      exact Rat.le_trans a1 a2
    rw [h52] at hlt
    exact absurd hlt (Rat.not_lt.2 h3)

theorem eq_c0_iff {x : F64} : F64.eq x c0 = x.isZero := by
  have h0 : c0.isFinite = true ∧ c0.isZero = true ∧ c0.isNaN = false ∧ c0.isInf = false := by
    decide +kernel
  unfold F64.eq
  rw [h0.2.2.1, h0.2.2.2]
  cases hn : x.isNaN
  · simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    cases hi : x.isInf
    · simp only [Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      have hf : x.isFinite = true := by
        rcases classify x with h | h | h
        · exact h
        · rw [hi] at h; cases h
        · rw [hn] at h; cases h
      rw [toRat_of_isZero h0.2.1]
      cases hz : x.isZero
      · have : x.toRat ≠ 0 := fun h => by rw [(isZero_iff_toRat hf).2 h] at hz; cases hz
        simp [this]
      · rw [(isZero_iff_toRat hf).1 hz]; simp
    · simp only [Bool.or_true, ↓reduceIte, Bool.false_and]
      have := not_finite_of_inf hi
      cases hz : x.isZero
      · rfl
      · rw [isFinite_of_isZero hz] at this; cases this
  · simp only [Bool.true_or, ↓reduceIte]
    cases hz : x.isZero
    · rfl
    · have := isFinite_of_isZero hz
      rw [isNaN_false_of_finite this] at hn; cases hn

/-- The classification functions of `math`, for every argument object.

A conversion error (`__float__` or `__index__` raising or returning the wrong type, an
int too large for a float, an object that is not a number) is raised unchanged by all
six. Otherwise, with `x` the converted value (Doc/library/math.rst):
* `isnan(x)` is whether `x != x`; `isinf(x)` whether `x` is `inf` or `-inf`; `isfinite(x)`
  whether it is neither ("Return True if x is neither an infinity nor a NaN");
* `issubnormal(x)` is "a finite nonzero number with a magnitude smaller than
  `sys.float_info.min`" (`2 ** -1022`), and `isnormal(x)` "a finite nonzero number that is
  not a subnormal";
* the C11 `#else` branch of `math_issubnormal_impl` the 3.15.2 build compiles and the C23
  `issubnormal` branch agree;
* `signbit(x)` is `copysign(1.0, x) < 0`, for NaNs and zeros too. -/
def MathClassify : Prop := ∀ o : Arg,
  (∀ e, convDouble o = .error e →
    math_isfinite o = .error e ∧ math_isnan o = .error e ∧ math_isinf o = .error e ∧
    math_isnormal o = .error e ∧ math_issubnormal o = .error e ∧ math_signbit o = .error e) ∧
  (∀ x, convDouble o = .ok x →
    let inf := F64.eq x (F64.inf false) || F64.eq x (F64.inf true)
    math_isnan o = .ok (!F64.eq x x) ∧
    math_isinf o = .ok inf ∧
    math_isfinite o = .ok (F64.eq x x && !inf) ∧
    math_issubnormal o =
      .ok (F64.eq x x && !inf && !F64.eq x c0 && decide (Rat.abs x.toRat < pw (-1022))) ∧
    math_isnormal o =
      .ok (F64.eq x x && !inf && !F64.eq x c0 && decide (pw (-1022) ≤ Rat.abs x.toRat)) ∧
    math_issubnormal_c23 o = math_issubnormal o ∧
    math_signbit o = (math_copysign [.float c1, o]).map (fun r => F64.lt r c0))

theorem asDouble_eq_conv (o : Arg) : asDouble o = convDouble o := by
  cases o <;> rfl

theorem inf_or (x : F64) :
    (F64.eq x (F64.inf false) || F64.eq x (F64.inf true)) = x.isInf := by
  rw [eq_inf_iff, eq_inf_iff]
  cases x.isInf <;> cases x.sign <;> rfl

theorem c1_facts : c1.isNaN = false ∧ c1.isInf = false ∧ c1.sign = false ∧ c1.isFinite = true := by
  decide +kernel

theorem copysign_c1_lt (x : F64) : F64.lt (F64.copysign c1 x) c0 = x.sign := by
  unfold F64.copysign
  cases hs : x.sign
  · simp only [c1_facts.2.2.1, beq_self_eq_true, ↓reduceIte]
    decide +kernel
  · have : (c1.sign == true) = false := by rw [c1_facts.2.2.1]; rfl
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    decide +kernel

theorem copysign_c1_facts (x : F64) :
    (F64.copysign c1 x).isNaN = false ∧ (F64.copysign c1 x).isInf = false := by
  unfold F64.copysign
  split
  · exact ⟨c1_facts.1, c1_facts.2.1⟩
  · rw [neg_isNaN, neg_isInf]; exact ⟨c1_facts.1, c1_facts.2.1⟩

theorem copysign_c1_obj {o : Arg} {x : F64} (hx : convDouble o = .ok x) :
    math_copysign [.float c1, o] = .ok (F64.copysign c1 x) := by
  have h1 : asDouble o = .ok x := by rw [asDouble_eq_conv]; exact hx
  obtain ⟨hn, hi⟩ := copysign_c1_facts x
  have e1 : checkPositional "copysign" [Arg.float c1, o].length 2 2 = .ok () := rfl
  have e2 : asDouble ([Arg.float c1, o].getD 0 default) = .ok c1 := rfl
  have e3 : asDouble ([Arg.float c1, o].getD 1 default) = .ok x := h1
  have hn' : (F64.copysign c1 x).isNaN = false := hn
  unfold math_copysign math_2
  rw [e1]
  simp only [bind, Except.bind]
  rw [e2, e3]
  simp only [hn', hi, Bool.false_eq_true, ↓reduceIte]
  rfl

theorem mathClassify_proven : MathClassify := by
  intro o
  refine ⟨fun e he => ?_, fun x hx => ?_⟩
  · simp [math_isfinite, math_isnan, math_isinf, math_isnormal, math_issubnormal, math_signbit,
      he, bind, Except.bind]
  · simp only [inf_or]
    have hfin : x.isFinite = (!x.isNaN && !x.isInf) := by
      rcases classify x with h | h | h
      · rw [h, isNaN_false_of_finite h, isInf_false_of_finite h]; rfl
      · rw [not_finite_of_inf h, h]; simp
      · rw [not_inf_of_nan h, h]
        have : x.isFinite = false := by
          cases hc : x.isFinite
          · rfl
          · rw [isNaN_false_of_finite hc] at h; cases h
        rw [this]; simp
    have hself : F64.eq x x = !x.isNaN := by
      cases hn : x.isNaN
      · exact eq_self_of_not_nan hn
      · exact eq_self_of_nan hn
    rw [hself, eq_c0_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [math_isnan, hx, bind, Except.bind, pure, Except.pure]
    · simp [math_isinf, hx, bind, Except.bind, pure, Except.pure]
    · simp [math_isfinite, hx, bind, Except.bind, pure, Except.pure, hfin]
    · simp only [math_issubnormal, hx, bind, Except.bind, pure, Except.pure, eq_c0_iff, isZeroC]
      congr 1
      rw [hfin]
      cases hn : x.isNaN <;> cases hi : x.isInf <;> simp only [Bool.not_false, Bool.true_and,
        Bool.not_true, Bool.false_and, Bool.and_false]
      have hf : x.isFinite = true := by rw [hfin, hn, hi]; rfl
      cases hz : x.isZero
      · simp only [Bool.not_false, Bool.true_and, cIsNormal]
        have := subnormal_iff hf hz
        have hb := bexp_lt x
        have hne : x.bexp ≠ 2047 := (isFinite_eq x).1 hf
        by_cases h0 : x.bexp = 0
        · simp [h0, this.1 h0]
        · have : ¬ Rat.abs x.toRat < pw (-1022) := fun h => h0 (this.2 h)
          simp [h0, hne, this]
      · simp
    · simp only [math_isnormal, hx, bind, Except.bind, pure, Except.pure]
      congr 1
      unfold cIsNormal
      cases hn : x.isNaN <;> cases hi : x.isInf
      · have hf : x.isFinite = true := by rw [hfin, hn, hi]; rfl
        have hne : x.bexp ≠ 2047 := (isFinite_eq x).1 hf
        cases hz : x.isZero
        · have := subnormal_iff hf hz
          by_cases h0 : x.bexp = 0
          · have h1 := this.1 h0
            simp [h0, Rat.not_le.2 h1]
          · have : ¬ Rat.abs x.toRat < pw (-1022) := fun h => h0 (this.2 h)
            simp [h0, hne, Rat.not_lt.1 this]
        · have := (isZero_eq x).1 hz
          simp [this.1]
      · have := (isInf_eq x).1 hi
        simp [this.1]
      · have := (isNaN_eq x).1 hn
        simp [this.1]
      · have := (isNaN_eq x).1 hn
        simp [this.1]
    · simp only [math_issubnormal_c23, math_issubnormal, hx, bind, Except.bind, pure, Except.pure,
        cIsSubnormal, cIsNormal, isZeroC, eq_c0_iff]
      congr 1
      have hb := bexp_lt x
      cases hf : x.isFinite
      · have : x.bexp = 2047 := by
          apply Classical.byContradiction
          intro h; rw [(isFinite_eq x).2 h] at hf; cases hf
        simp [this]
      · have hne : x.bexp ≠ 2047 := (isFinite_eq x).1 hf
        have A : (x.bexp == 2047) = false := by simp [hne]
        unfold F64.isZero
        simp only [bne, A, Bool.or_false]
        cases (x.bexp == 0) <;> cases (x.frac == 0) <;> rfl
    · rw [copysign_c1_obj hx]
      simp [math_signbit, hx, bind, Except.bind, pure, Except.pure, Except.map, copysign_c1_lt]

end PyLean.MathInt
