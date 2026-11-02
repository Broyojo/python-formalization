import PyLean.MathInt.FltLogProps

/-!
# Properties: `nextafter`, `ulp`

`math_nextafter_impl` and `math_ulp_impl` (Modules/mathmodule.c:2853-2996).

`nextafter(x, y)` and `nextafter(x, y, steps=1)` are documented to be the same call ("If
steps is not specified or is None, it defaults to 1"), but the `steps` path returns `y` once
the walk reaches `y`'s value, so one step from `-5e-324` towards `0.0` gives `0.0` with
`steps=1` and `-0.0` (the C library's answer) without: refuted, bug
`mathint-nextafter-steps-zero-sign`.

`ulp(x)` is the value of the least significant bit of `x`, as documented.
-/

namespace PyLean.MathInt

open PyLean PyLean.Binary64 PyLean.Binary64.F64

/-- Two results are the same float: equal bit patterns, or both NaNs (the model does not
track NaN payloads). -/
def sameFloat (a b : Py F64) : Prop :=
  match a, b with
  | .ok x, .ok y => x = y ∨ (x.isNaN = true ∧ y.isNaN = true)
  | .error e, .error f => e = f
  | _, _ => False

/-- "If steps is not specified or is None, it defaults to 1" (the `math.nextafter`
docstring): for every pair of floats, `nextafter(x, y)` and `nextafter(x, y, steps=1)` are
the same float. -/
def NextafterDefaultStep : Prop :=
  ∀ x y : F64,
    sameFloat (math_nextafter (.float x) (.float y) none) (math_nextafter (.float x) (.float y) (some (.int 1)))

theorem nextafterDefaultStep_refuted : ¬ NextafterDefaultStep := by
  intro h
  have := h (F64.ofBits (2 ^ 63 + 1)) (F64.zero false)
  have h1 : math_nextafter (.float (F64.ofBits (2 ^ 63 + 1))) (.float (F64.zero false)) none =
      .ok (F64.zero true) := by decide +kernel
  have h2 : math_nextafter (.float (F64.ofBits (2 ^ 63 + 1))) (.float (F64.zero false))
      (some (.int 1)) = .ok (F64.zero false) := by decide +kernel
  rw [h1, h2] at this
  have h3 : F64.zero true ≠ F64.zero false := by decide +kernel
  have h4 : (F64.zero true).isNaN = false := by decide +kernel
  simp only [sameFloat, h4] at this
  rcases this with h | h
  · exact h3 h
  · cases h.1

/-! ## `ulp` -/

/-- `ulp(x)` for every argument object (Doc/library/math.rst, "ulp"): a conversion error is
raised; a NaN is returned as is; an infinity gives `inf`; for finite `x` the result is the
value of the least significant bit of `x`, `2 ** lsbExp(x)` (`5e-324` for zeros and
subnormals), and `abs(x) + ulp(x)` is the next float above `abs(x)`, except for the largest
float, where `abs(x) - ulp(x)` is the next float below. -/
def UlpDoc : Prop :=
  (∀ o e, convDouble o = .error e → math_ulp o = .error e) ∧
  ∀ o x, convDouble o = .ok x →
    (x.isNaN = true → math_ulp o = .ok x) ∧
    (x.isInf = true → math_ulp o = .ok (F64.inf false)) ∧
    (x.isFinite = true → ∃ u, math_ulp o = .ok u ∧ u.isFinite = true ∧ u.toRat = pw x.lsbExp ∧
      (F64.abs x ≠ F64.maxFinite → F64.add (F64.abs x) u = F64.nextafter (F64.abs x) (F64.inf false)) ∧
      (F64.abs x = F64.maxFinite → F64.sub (F64.abs x) u = F64.nextafter (F64.abs x) (F64.inf true)))

theorem abs_fields (x : F64) : (F64.abs x).sign = false ∧ (F64.abs x).bexp = x.bexp ∧
    (F64.abs x).frac = x.frac := by
  unfold F64.abs
  cases hs : x.sign
  · simp [hs]
  · simp only [↓reduceIte]
    obtain ⟨h1, h2, h3⟩ := neg_fields x
    rw [hs] at h1
    exact ⟨by simpa using h1, h2, h3⟩

theorem abs_lsb (x : F64) : (F64.abs x).lsbExp = x.lsbExp := by
  unfold lsbExp; rw [(abs_fields x).2.1]

theorem abs_isFinite (x : F64) : (F64.abs x).isFinite = x.isFinite := by
  unfold isFinite; rw [(abs_fields x).2.1]

theorem abs_isNaN (x : F64) : (F64.abs x).isNaN = x.isNaN := by
  unfold isNaN; rw [(abs_fields x).2.1, (abs_fields x).2.2]

theorem abs_isZero (x : F64) : (F64.abs x).isZero = x.isZero := by
  unfold isZero; rw [(abs_fields x).2.1, (abs_fields x).2.2]

/-- The next bit pattern of a nonnegative finite float that is not the largest is a finite
float exactly one unit in the last place above it. -/
theorem succ_value {x : F64} (hs : x.sign = false) (hf : x.isFinite = true)
    (hm : x.bits ≠ 0x7fefffffffffffff) :
    (ofBits (x.bits + 1)).isFinite = true ∧
      (ofBits (x.bits + 1)).toRat = x.toRat + pw x.lsbExp ∧ (ofBits (x.bits + 1)).sign = false := by
  have hd := bits_decomp x
  rw [hs] at hd
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hd
  have hb := bexp_lt x
  have hfr := frac_lt x
  have hne : x.bexp ≠ 2047 := (isFinite_eq x).1 hf
  have hlt : x.bits + 1 < 2 ^ 63 := by
    have : x.bexp ≤ 2046 := by omega
    by_cases h2046 : x.bexp = 2046
    · have : x.frac ≠ 2 ^ 52 - 1 := by
        intro h; apply hm; rw [hd, h2046, h]
      omega
    · omega
  have hyb : (ofBits (x.bits + 1)).bits = x.bits + 1 := bits_ofBits_of_lt (by omega)
  generalize ofBits (x.bits + 1) = y at hyb ⊢
  have ys : y.sign = false := by unfold sign; rw [hyb]; simp; omega
  have hyd := bits_decomp y
  rw [ys, hyb] at hyd
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add] at hyd
  have hyb2 := bexp_lt y
  have hyf2 := frac_lt y
  have hyf : y.isFinite = true := by
    rw [isFinite_eq]
    by_cases h2046 : x.bexp = 2046
    · have : x.frac ≠ 2 ^ 52 - 1 := by
        intro h; apply hm; rw [hd, h2046, h]
      omega
    · omega
  refine ⟨hyf, ?_, ys⟩
  rw [toRat_of_finite hyf, toRat_of_finite hf, ys, hs]
  simp only [Bool.false_eq_true, ↓reduceIte]
  by_cases hc : x.frac < 2 ^ 52 - 1
  · have e1 : y.bexp = x.bexp := by omega
    have e2 : y.frac = x.frac + 1 := by omega
    have hm' : y.mant = x.mant + 1 := by unfold mant; rw [e1, e2]; split <;> omega
    have hl : y.lsbExp = x.lsbExp := by unfold lsbExp; rw [e1]
    rw [hm', hl]; push_cast; grind
  · have hc' : x.frac = 2 ^ 52 - 1 := by omega
    have e1 : y.bexp = x.bexp + 1 := by omega
    have e2 : y.frac = 0 := by omega
    have hmy : y.mant = 2 ^ 52 := by unfold mant; rw [e1, e2]; simp
    have hly : y.lsbExp = ((x.bexp + 1 : Nat) : Int) - 1075 := by
      unfold lsbExp; rw [e1]; congr 1; simp
    rw [hmy, hly]
    by_cases hb0 : x.bexp = 0
    · have hmx : x.mant = 2 ^ 52 - 1 := by unfold mant; rw [hb0, hc']; simp
      have hlx : x.lsbExp = -1074 := by unfold lsbExp; rw [hb0]; rfl
      rw [hmx, hlx, hb0]
      push_cast
      grind
    · have hmx : x.mant = 2 ^ 53 - 1 := by unfold mant; rw [hc']; simp [hb0]
      have hlx : x.lsbExp = (x.bexp : Int) - 1075 := by
        unfold lsbExp; congr 1; rw [Nat.max_def]; split <;> omega
      rw [hmx, hlx]
      have e : ((x.bexp + 1 : Nat) : Int) - 1075 = ((x.bexp : Int) - 1075) + 1 := by push_cast; omega
      rw [e, pw_succ]
      push_cast
      grind

theorem nextafter_up {a : F64} (hs : a.sign = false) (hf : a.isFinite = true) :
    F64.nextafter a (F64.inf false) = ofBits (a.bits + 1) := by
  have hn := isNaN_false_of_finite hf
  obtain ⟨_, _, _, _, _, _, _, _⟩ := inf_facts
  unfold F64.nextafter
  have heq : F64.eq a (F64.inf false) = false := by
    rw [eq_inf_iff, isInf_false_of_finite hf]; rfl
  simp only [hn, inf_facts.2.1, Bool.or_false, Bool.false_eq_true, ↓reduceIte, heq]
  by_cases hz : a.isZero = true
  · have hb : a.bits = 0 := by
      have := bits_decomp a
      rw [hs, (isZero_eq a).1 hz |>.1, (isZero_eq a).1 hz |>.2] at this
      simpa using this
    simp only [hz, ↓reduceIte, (inf_bits false).2, Bool.false_eq_true, hb]
  · have hz' : a.isZero = false := by simpa using hz
    have hlt : F64.lt a (F64.inf false) = true := by
      unfold F64.lt; simp [hn, inf_facts.2.1, isInf_false_of_finite hf, (inf_bits false).1,
        (inf_bits false).2]
    simp [hz', hlt, hs]

theorem maxFinite_facts : F64.maxFinite.isFinite = true ∧ F64.maxFinite.sign = false ∧
    F64.maxFinite.bits = 0x7fefffffffffffff ∧ F64.maxFinite.lsbExp = 971 ∧
    F64.maxFinite.isNaN = false ∧ F64.maxFinite.isInf = false := by decide +kernel

theorem ulp_max : ulp_impl F64.maxFinite = F64.ofBits 0x7ca0000000000000 ∧
    (F64.ofBits 0x7ca0000000000000).toRat = pw 971 ∧ (F64.ofBits 0x7ca0000000000000).isFinite = true ∧
    F64.sub F64.maxFinite (F64.ofBits 0x7ca0000000000000) =
      F64.nextafter F64.maxFinite (F64.inf true) := by
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  rw [show pw 971 = ((2 ^ 971 : Nat) : Rat) from pw_natCast 971]
  decide +kernel

theorem abs_eq_self {a : F64} (hs : a.sign = false) : F64.abs a = a := by
  unfold F64.abs; simp [hs]

theorem ulpDoc_proven : UlpDoc := by
  refine ⟨fun o e he => by simp [math_ulp, he, bind, Except.bind], fun o x hx => ?_⟩
  have hu : math_ulp o = .ok (ulp_impl x) := by simp [math_ulp, hx, bind, Except.bind, pure, Except.pure]
  rw [hu]
  refine ⟨fun hn => by simp [ulp_impl, hn], fun hi => ?_, fun hf => ?_⟩
  · have hn := not_nan_of_inf hi
    have hai : (F64.abs x).isInf = true := by
      unfold isInf; rw [(abs_fields x).2.1, (abs_fields x).2.2]; exact hi
    simp only [ulp_impl, hn, Bool.false_eq_true, ↓reduceIte, hai]
    rw [eq_inf_of_isInf hai, (abs_fields x).1]
  · obtain ⟨as, _, _⟩ := abs_fields x
    have af : (F64.abs x).isFinite = true := by rw [abs_isFinite]; exact hf
    have hn := isNaN_false_of_finite hf
    have hai : (F64.abs x).isInf = false := isInf_false_of_finite af
    by_cases hmax : (F64.abs x).bits = 0x7fefffffffffffff
    · have hA : F64.abs x = F64.maxFinite := by
        ext; rw [hmax]; decide +kernel
      have hl : x.lsbExp = 971 := by rw [← abs_lsb, hA]; decide +kernel
      have hU : ulp_impl x = F64.ofBits 0x7ca0000000000000 := by
        have : ulp_impl x = ulp_impl (F64.abs x) := by
          simp [ulp_impl, hn, abs_isNaN, abs_eq_self as]
        rw [this, hA]; exact ulp_max.1
      refine ⟨_, hU ▸ rfl, ulp_max.2.2.1, by rw [hl]; exact ulp_max.2.1, fun h => absurd hA h,
        fun _ => ?_⟩
      rw [hA]; exact ulp_max.2.2.2
    · obtain ⟨yf, yv, _⟩ := succ_value as af hmax
      have hup := nextafter_up as af
      have hU : ulp_impl x = F64.sub (ofBits ((F64.abs x).bits + 1)) (F64.abs x) := by
        have hup' : F64.nextafter (F64.abs x) cInf = ofBits ((F64.abs x).bits + 1) := hup
        simp only [ulp_impl, hn, Bool.false_eq_true, ↓reduceIte, hai]
        rw [hup', isInf_false_of_finite yf]; rfl
      have hlsb := abs_lsb x
      have hq : (ofBits ((F64.abs x).bits + 1)).toRat + (F64.abs x).neg.toRat = pw x.lsbExp := by
        rw [toRat_neg, yv, hlsb]; grind
      have hne : pw x.lsbExp ≠ 0 := pw_ne _
      have hrep : Rep binary64 (pw x.lsbExp) := by
        refine ⟨1, x.lsbExp, by decide, by have := lsbExp_ge x; simp [Fmt.etiny, binary64]; omega, ?_⟩
        left; simp
      have hsmall : Rat.abs (pw x.lsbExp) < overflowLimit := by
        rw [abs_of_nonneg (Rat.le_of_lt (pw_pos _))]
        have : pw x.lsbExp ≤ pw 971 := pw_le (lsbExp_le x hf)
        have h2 : pw 971 < overflowLimit := by decide +kernel
        grind
      have hsub : F64.sub (ofBits ((F64.abs x).bits + 1)) (F64.abs x) = ofRat (pw x.lsbExp) := by
        unfold F64.sub
        rw [add_of_finite yf (by rw [neg_isFinite]; exact af), hq]
        simp [hne]
      refine ⟨ofRat (pw x.lsbExp), by rw [hU, hsub], (ofRat_isFinite _).2 hsmall,
        ofRat_exact hrep hsmall, fun _ => ?_, fun h => ?_⟩
      · rw [hup, add_of_finite af ((ofRat_isFinite _).2 hsmall), ofRat_exact hrep hsmall]
        have hv : (F64.abs x).toRat + pw x.lsbExp = (ofBits ((F64.abs x).bits + 1)).toRat := by
          rw [yv, hlsb]
        have hz : (ofBits ((F64.abs x).bits + 1)).isZero = false := by
          cases hc : (ofBits ((F64.abs x).bits + 1)).isZero
          · rfl
          · exfalso
            have h0 := toRat_of_isZero hc
            rw [yv] at h0
            have ha0 : 0 ≤ (F64.abs x).toRat := by
              rw [toRat_of_finite af, as]; simp only [Bool.false_eq_true, ↓reduceIte]
              exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
            have := pw_pos (F64.abs x).lsbExp
            grind
        have h0 : ¬ ((ofBits ((F64.abs x).bits + 1)).toRat = 0) := by
          intro h0; rw [(isZero_iff_toRat yf).2 h0] at hz; cases hz
        rw [hv]
        simp only [h0, ↓reduceIte, ofRat_toRat yf hz]
      · exfalso; apply hmax; rw [h]; decide +kernel

end PyLean.MathInt
