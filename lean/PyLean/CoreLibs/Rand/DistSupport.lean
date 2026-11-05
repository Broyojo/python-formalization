import PyLean.CoreLibs.Rand.DistFormula

/-!
Where `lognormvariate`, `paretovariate` and `weibullvariate` put their values, over
binary64: `lognormvariate >= 0`, `paretovariate >= 1` for `alpha > 0`, and
`weibullvariate >= 0` for `alpha > 0` and `beta > 0`. Each needs one fact about the C
library, stated as a hypothesis (`ExpNonneg`, `PowGeOne`, `PowNonneg`, with `LogNonpos`
from `DistFormula`); glibc meets all four (checked on the pod over 400k random arguments
and the edge cases).

A value is "at least `+0`" (`Pos0`) when it is not NaN and either has a clear sign bit or
is a zero: `-0.0` counts, because `-0.0 >= 0.0` in Python.
-/

namespace PyLean.CoreLibs.Rand

open PyLean PyLean.Binary64 PyLean.Binary64.F64 PyLean.MathInt RM Flt

/-! ### Signs of binary64 values -/

/-- Not NaN, and `+x` or a zero. -/
def Pos0 (x : F64) : Prop := x.isNaN = false ∧ (x.sign = false ∨ x.isZero = true)

theorem toRat_nonneg_of {x : F64} (hf : x.isFinite = true) (h : x.sign = false ∨ x.isZero = true) :
    0 ≤ x.toRat := by
  rcases h with h | h
  · rw [toRat_of_finite hf, h]
    exact Rat.mul_nonneg Rat.natCast_nonneg (Rat.le_of_lt (pw_pos _))
  · rw [toRat_of_isZero h]; exact Rat.le_refl

theorem isZero_false_of_inf {x : F64} (h : x.isInf = true) : x.isZero = false := by
  cases hz : x.isZero
  · rfl
  · have := isFinite_of_isZero hz
    rw [isInf_false_of_finite this] at h; cases h

theorem le_zero_of {x : F64} (h : Pos0 x) : F64.le (zero false) x = true := by
  obtain ⟨hn, hs⟩ := h
  have zf := zero_isFinite false
  rcases classify x with hf | hi | hn'
  · rw [le_of_finite zf hf, zero_toRat]
    exact decide_eq_true (toRat_nonneg_of hf hs)
  · have hs' : x.sign = false := by
      rcases hs with hs | hs
      · exact hs
      · rw [isZero_false_of_inf hi] at hs; cases hs
    have z1 := isNaN_false_of_finite zf
    have z2 := isInf_false_of_finite zf
    simp only [F64.le, F64.lt, z1, hn, z2, hi, hs', Bool.or_self, Bool.false_eq_true, if_false,
      if_true, Bool.not_false, Bool.true_or]
  · rw [hn] at hn'; cases hn'

theorem sign_false_of_pos {x : F64} (hf : x.isFinite = true) (h : 0 < x.toRat) :
    x.sign = false ∧ x.isZero = false := by
  have hz : x.isZero = false := by
    cases hz : x.isZero
    · rfl
    · rw [toRat_of_isZero hz] at h; exact absurd h (by decide)
  refine ⟨?_, hz⟩
  have := toRat_neg_iff_sign hf hz
  cases hs : x.sign
  · rfl
  · rw [hs] at this
    have : x.toRat < 0 := by simpa using this
    grind

theorem mul_pos0 {a b : F64} (ha : a.isFinite = true) (ha0 : 0 < a.toRat) (hb : Pos0 b) :
    Pos0 (F64.mul a b) := by
  obtain ⟨hsa, hza⟩ := sign_false_of_pos ha ha0
  obtain ⟨hnb, hsb⟩ := hb
  rcases classify b with hf | hi | hn'
  · rw [F64Order.mul_eq ha hf]
    have hq : 0 ≤ a.toRat * b.toRat := Rat.mul_nonneg (Rat.le_of_lt ha0) (toRat_nonneg_of hf hsb)
    unfold F64Order.rnd
    by_cases h0 : a.toRat * b.toRat = 0
    · rw [if_pos h0]
      exact ⟨isNaN_false_of_finite (zero_isFinite _), Or.inr (zero_isZero _)⟩
    · rw [if_neg h0]
      refine ⟨ofRat_isNaN _, Or.inl ?_⟩
      rw [ofRat_sign h0]; simp; exact Rat.not_lt.2 hq
  · have hs' : b.sign = false := by
      rcases hsb with hs | hs
      · exact hs
      · rw [isZero_false_of_inf hi] at hs; cases hs
    have hm : F64.mul a b = F64.inf false := by
      simp [F64.mul, isNaN_false_of_finite ha, hnb, isInf_false_of_finite ha, hi, hza, hsa, hs']
    rw [hm]
    exact ⟨inf_isNaN false, Or.inl (inf_bits false).2⟩
  · rw [hnb] at hn'; cases hn'

/-- `ofRat q` for `q ≠ 0`: a zero, an infinity with the sign of `q`, or a nonzero finite
value with the sign of `q`. -/
theorem ofRat_classify {q : Rat} (hq : q ≠ 0) :
    (ofRat q).isNaN = false ∧
    ((ofRat q).isZero = true ∨ ((ofRat q).isInf = true ∧ (ofRat q).sign = decide (q < 0)) ∨
      ((ofRat q).isFinite = true ∧ (ofRat q).isZero = false ∧
        (q < 0 → (ofRat q).toRat < 0) ∧ (0 < q → 0 < (ofRat q).toRat))) := by
  refine ⟨ofRat_isNaN q, ?_⟩
  rcases classify (ofRat q) with hf | hi | hn
  · cases hz : (ofRat q).isZero
    · right; right
      have hnz : (ofRat q).toRat ≠ 0 := fun h => by
        have := (isZero_iff_toRat hf).2 h; rw [hz] at this; cases this
      have h0f : (ofRat 0).isFinite = true := by rw [ofRat_zero]; exact zero_isFinite false
      have h0r : (ofRat 0).toRat = 0 := by rw [ofRat_zero]; exact zero_toRat false
      refine ⟨hf, rfl, fun hlt => ?_, fun hgt => ?_⟩
      · have := ofRat_mono (Rat.le_of_lt hlt) hf h0f
        rw [h0r] at this
        exact Rat.lt_of_le_of_ne this hnz
      · have := ofRat_mono (Rat.le_of_lt hgt) h0f hf
        rw [h0r] at this
        exact Rat.lt_of_le_of_ne this (Ne.symm hnz)
    · left; rfl
  · right; left; exact ⟨hi, ofRat_sign hq⟩
  · rw [ofRat_isNaN] at hn; cases hn

/-- `x / y` for a finite nonzero `x` and `y > 0` (an infinite `y` included). -/
theorem div_classify {x y : F64} (hx : x.isFinite = true) (hxz : x.isZero = false)
    (hy : F64.lt (zero false) y = true) :
    (F64.div x y).isNaN = false ∧
    ((F64.div x y).isZero = true ∨
      ((F64.div x y).isInf = true ∧ (F64.div x y).sign = decide (x.toRat < 0)) ∨
      ((F64.div x y).isFinite = true ∧ (F64.div x y).isZero = false ∧
        (x.toRat < 0 → (F64.div x y).toRat < 0) ∧ (0 < x.toRat → 0 < (F64.div x y).toRat))) := by
  have zf := zero_isFinite false
  have hyn : y.isNaN = false := by
    cases h : y.isNaN
    · rfl
    · simp [F64.lt, h] at hy
  rcases classify y with hyf | hyi | hyn'
  · rw [lt_of_finite zf hyf, zero_toRat] at hy
    have hy0 : 0 < y.toRat := of_decide_eq_true hy
    have hyz := (sign_false_of_pos hyf hy0).2
    have hx0 : x.toRat ≠ 0 := fun h => by
      have := (isZero_iff_toRat hx).2 h; rw [hxz] at this; cases this
    have hq : x.toRat / y.toRat ≠ 0 := by
      rw [Rat.div_def]
      intro h
      have hinv : y.toRat⁻¹ ≠ 0 := Ne.symm (Rat.ne_of_lt (Rat.inv_pos.2 hy0))
      rcases Rat.mul_eq_zero.1 h with h | h
      · exact hx0 h
      · exact hinv h
    have hd : F64.div x y = ofRat (x.toRat / y.toRat) := by
      simp [F64.div, isNaN_false_of_finite hx, hyn, isInf_false_of_finite hx,
        isInf_false_of_finite hyf, hyz, hq]
    have hinv : 0 < y.toRat⁻¹ := Rat.inv_pos.2 hy0
    have hneg : x.toRat / y.toRat < 0 ↔ x.toRat < 0 := by
      rw [Rat.div_def]
      constructor
      · intro h
        apply Classical.byContradiction
        intro hc
        have := Rat.mul_nonneg (Rat.not_lt.1 hc) (Rat.le_of_lt hinv)
        grind
      · intro h
        have h1 : 0 < -x.toRat * y.toRat⁻¹ := Rat.mul_pos (by grind) hinv
        rw [Rat.neg_mul] at h1
        grind
    have hpos : 0 < x.toRat → 0 < x.toRat / y.toRat := fun h => by
      rw [Rat.div_def]; exact Rat.mul_pos h hinv
    obtain ⟨c1, c2⟩ := ofRat_classify hq
    rw [hd]
    refine ⟨c1, ?_⟩
    rcases c2 with c | ⟨ci, cs⟩ | ⟨cf, cz, cn, cp⟩
    · exact Or.inl c
    · right; left; refine ⟨ci, ?_⟩; rw [cs]; exact decide_eq_decide.2 hneg
    · right; right; exact ⟨cf, cz, fun h => cn (hneg.2 h), fun h => cp (hpos h)⟩
  · have hd : F64.div x y = zero (x.sign != y.sign) := by
      simp [F64.div, isNaN_false_of_finite hx, hyn, isInf_false_of_finite hx, hyi]
    rw [hd]
    exact ⟨isNaN_false_of_finite (zero_isFinite _), Or.inl (zero_isZero _)⟩
  · rw [hyn] at hyn'; cases hyn'

theorem pyDiv_pos [RandLibm] (x y : F64) (hy : Flt.lt 0.0 y = true) : pyDiv x y = .ok (F64.div x y) := by
  have hy' : F64.lt (zero false) y = true := by rw [← zero_f64]; exact hy
  have zf := zero_isFinite false
  have hne : Flt.beq y 0.0 = false := by
    show F64.eq y (0.0 : F64) = false
    rw [zero_f64]
    rcases classify y with hf | hi | hn
    · rw [lt_of_finite zf hf, zero_toRat] at hy'
      rw [eq_of_finite hf zf, zero_toRat]
      have := of_decide_eq_true hy'
      exact decide_eq_false (fun e => by rw [e] at this; exact absurd this (by decide))
    · simp [F64.eq, isNaN_false_of_finite zf, isInf_false_of_finite zf, hi]
    · simp [F64.lt, hn] at hy'
  simp only [pyDiv, hne, Bool.false_eq_true, if_false]
  rfl

/-- `math.log(1.0 - u)` for `u` in `[0, 1)`, given `LogNonpos`: no exception, and a finite
value `<= 0`. -/
theorem mathLog_one_sub [RandLibm] (hlog : LogNonpos) {u : F64} (hu : u.isFinite = true)
    (h0 : 0 ≤ u.toRat) (h1 : u.toRat < 1) :
    mathLog ((1.0 : F64) - u) = .ok (RandLibm.log (F64.sub F64.one u)) ∧
    (RandLibm.log (F64.sub F64.one u)).isFinite = true ∧ (RandLibm.log (F64.sub F64.one u)).toRat ≤ 0 := by
  obtain ⟨wf, wpos, wle⟩ := F64Order.one_sub_unit hu h0 h1
  have hw : (1.0 : F64) - u = F64.sub F64.one u := by rw [one_f64]; rfl
  obtain ⟨lf, lle⟩ := hlog _ wf wpos wle
  refine ⟨?_, lf, lle⟩
  have zf := zero_isFinite false
  rw [hw]
  have a1 : Flt.isNan (F64.sub F64.one u) = false := isNaN_false_of_finite wf
  have a2 : Flt.le (F64.sub F64.one u) 0.0 = false := by
    show F64.le _ (0.0 : F64) = false
    rw [zero_f64, le_of_finite wf zf, zero_toRat]
    exact decide_eq_false (Rat.not_le.2 wpos)
  have a3 : Flt.isInf (F64.sub F64.one u) = false := isInf_false_of_finite wf
  have a4 : Flt.isNan (Flt.log (F64.sub F64.one u)) = false := isNaN_false_of_finite lf
  have a5 : Flt.isInf (Flt.log (F64.sub F64.one u)) = false := isInf_false_of_finite lf
  simp only [mathLog, math1Dom, a1, a2, a3, a4, a5, Bool.false_and, Bool.false_eq_true, if_false]
  rfl

/-! ### `lognormvariate`, Lib/random.py:595-603 -/

/-- C99 Annex F and glibc: `exp` of a non-NaN is not NaN and is `+0`, a positive number
or `+inf`. -/
def ExpNonneg [RandLibm] : Prop :=
  ∀ x : F64, x.isNaN = false → (RandLibm.exp x).isNaN = false ∧ (RandLibm.exp x).sign = false

/-- `lognormvariate(mu, sigma)` is never negative: whenever `normalvariate(mu, sigma)` on the
same draws gives a non-NaN `x` (as it does for finite `mu` and `sigma`, its `z` being
finite), `lognormvariate` returns `exp(x) >= 0`, or raises `OverflowError('math range
error')` when `exp` overflows on a finite `x`, after the same draws. -/
def LognormNonneg : Prop :=
  ∀ [RandLibm], ExpNonneg → ∀ (σ : Type) (g : Gen σ F64) (fuel : Nat) (mu sigma x : F64) (s t : σ),
    normalvariate g fuel mu sigma s = (.ok x, t) → x.isNaN = false →
    lognormvariate g fuel mu sigma s = (.error (.overflowError "math range error"), t) ∨
    ∃ r, lognormvariate g fuel mu sigma s = (.ok r, t) ∧ r = RandLibm.exp x ∧ Flt.le 0.0 r = true

theorem lognormNonneg_proven : LognormNonneg := by
  intro _ hexp σ g fuel mu sigma x s t h hx
  rw [(normalvariateF64_proven σ g).2.2 fuel mu sigma s, h]
  obtain ⟨en, es⟩ := hexp x hx
  have a1 : Flt.isNan (Flt.exp x) = false := en
  by_cases hi : (Flt.isInf (Flt.exp x) && Flt.isFinite x) = true
  · left
    simp only [mathExp, math1Over, a1, Bool.false_and, Bool.false_eq_true, if_false, hi, if_true]
  · right
    refine ⟨RandLibm.exp x, ?_, rfl, ?_⟩
    · simp only [mathExp, math1Over, a1, Bool.false_and, Bool.false_eq_true, if_false, hi]
      rfl
    · show F64.le (0.0 : F64) _ = true
      rw [zero_f64]
      exact le_zero_of ⟨en, Or.inl es⟩

/-! ### `paretovariate`, Lib/random.py:768-773 -/

/-- A fact about the C library's `pow`: for `0 < x < 1` and `y < 0` (both finite) it is not
NaN, and is `+inf` or at least `1` (`x ** y > 1` exactly, and `1` is a double, so a monotone
correctly rounded `pow` cannot go below it). -/
def PowGeOne [RandLibm] : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true → 0 < x.toRat → x.toRat < 1 → y.toRat < 0 →
    (RandLibm.pow x y).isNaN = false ∧ ((RandLibm.pow x y).isInf = true ∨ 1 ≤ (RandLibm.pow x y).toRat)

theorem one_le_one : F64.le F64.one F64.one = true := by decide +kernel
theorem one_le_inf : F64.le F64.one (F64.inf false) = true := by decide +kernel

/-- `paretovariate(alpha)` is at least `1.0` for every `alpha > 0` (an infinite one
included) and a `random()` value in `[0, 1)`, or raises the `OverflowError` of `**` when the
power overflows (a tiny `alpha`); nothing else, and after one draw. -/
def ParetoGeOne : Prop :=
  ∀ [RandLibm], PowGeOne → ∀ (σ : Type) (g : Gen σ F64) (alpha u : F64) (s s1 : σ),
    g.random s = (u, s1) → u.isFinite = true → 0 ≤ u.toRat → u.toRat < 1 → Flt.lt 0.0 alpha = true →
    paretovariate g alpha s = (.error (.overflowError "(34, 'Numerical result out of range')"), s1) ∨
    ∃ r, paretovariate g alpha s = (.ok r, s1) ∧ Flt.le 1.0 r = true

theorem paretoGeOne_proven : ParetoGeOne := by
  intro _ hpow σ g alpha u s s1 h hu h0 h1 ha
  rw [(betaParetoWeibullF64_proven σ g).2.1 alpha u s s1 h, pyDiv_pos _ _ ha]
  simp only [ex_ok_bind]
  obtain ⟨wf, wpos, wle⟩ := F64Order.one_sub_unit hu h0 h1
  have hw : (1.0 : F64) - u = F64.sub F64.one u := by rw [one_f64]; rfl
  have hm1 : (-1.0 : F64) = F64.neg F64.one := by rw [one_f64]; rfl
  rw [hw, hm1]
  generalize hW : F64.sub F64.one u = w at wf wpos wle
  have ha' : F64.lt (zero false) alpha = true := by rw [← zero_f64]; exact ha
  have onef : F64.one.isFinite = true := by decide +kernel
  have nf : (F64.neg F64.one).isFinite = true := by rw [neg_isFinite]; exact onef
  have nz : (F64.neg F64.one).isZero = false := by decide +kernel
  have nr : (F64.neg F64.one).toRat = -1 := by decide +kernel
  obtain ⟨dn, dc⟩ := div_classify nf nz ha'
  generalize hD : F64.div (F64.neg F64.one) alpha = d at dn dc
  rw [nr] at dc
  obtain ⟨wsf, wz⟩ := sign_false_of_pos wf wpos
  have wn : w.isNaN = false := isNaN_false_of_finite wf
  have zf := zero_isFinite false
  -- the facts `pyPow` tests, in `Flt` form
  have one1 : (1.0 : F64) = F64.one := one_f64
  have zero0 : (0.0 : F64) = F64.zero false := zero_f64
  have okOne : Flt.le (1.0 : F64) 1.0 = true := by rw [one1]; exact one_le_one
  have wabs : Flt.fabs w = w := by show F64.abs w = w; simp [F64.abs, wsf]
  have wlt1 : Flt.lt (1.0 : F64) w = false := by
    show F64.lt _ w = false
    rw [one1, lt_of_finite onef wf, show F64.one.toRat = 1 by decide +kernel]
    exact decide_eq_false (Rat.not_lt.2 wle)
  have wneg : Flt.lt w (0.0 : F64) = false := by
    show F64.lt w _ = false
    rw [zero0, lt_of_finite wf zf, zero_toRat]
    exact decide_eq_false (Rat.not_lt.2 (Rat.le_of_lt wpos))
  have wbz : Flt.beq w (0.0 : F64) = false := by
    show F64.eq w _ = false
    rw [zero0, eq_of_finite wf zf, zero_toRat]
    exact decide_eq_false (fun e => by rw [e] at wpos; exact absurd wpos (by decide))
  have wi : Flt.isInf w = false := isInf_false_of_finite wf
  have wn' : Flt.isNan w = false := wn
  have dn' : Flt.isNan d = false := dn
  by_cases hd0 : Flt.beq d 0.0 = true
  · right; refine ⟨1.0, ?_, okOne⟩
    simp only [pyPow, hd0, if_true]
  · simp only [Bool.not_eq_true] at hd0
    by_cases hb1 : Flt.beq w 1.0 = true
    · -- `w == 1.0`: every reachable branch returns `1.0`
      right; refine ⟨1.0, ?_, okOne⟩
      rcases dc with dz | ⟨di, _⟩ | ⟨df, _, _, _⟩
      · exfalso
        have : Flt.beq d (0.0 : F64) = true := by
          show F64.eq d _ = true
          rw [zero0, eq_of_finite (isFinite_of_isZero dz) zf, zero_toRat, toRat_of_isZero dz]; rfl
        rw [this] at hd0; cases hd0
      · have di' : Flt.isInf d = true := di
        simp only [pyPow, hd0, wn', dn', di', wabs, hb1, Bool.false_eq_true, if_false, if_true]
      · have di' : Flt.isInf d = false := isInf_false_of_finite df
        simp only [pyPow, hd0, wn', dn', di', wi, wbz, wneg, hb1, Bool.false_and, Bool.false_eq_true,
          if_false, if_true]
    · simp only [Bool.not_eq_true] at hb1
      rcases dc with dz | ⟨di, ds⟩ | ⟨df, dz, dneg, _⟩
      · exfalso
        have : Flt.beq d (0.0 : F64) = true := by
          show F64.eq d _ = true
          rw [zero0, eq_of_finite (isFinite_of_isZero dz) zf, zero_toRat, toRat_of_isZero dz]; rfl
        rw [this] at hd0; cases hd0
      · -- `d = -inf`: `fabs(d)`
        have di' : Flt.isInf d = true := di
        have ds' : d.sign = true := by rw [ds]; decide
        have dlt : Flt.lt (0.0 : F64) d = false := by
          show F64.lt _ d = false
          rw [zero0]
          simp [F64.lt, isNaN_false_of_finite zf, dn, isInf_false_of_finite zf, di, ds']
        right
        refine ⟨Flt.fabs d, ?_, ?_⟩
        · simp only [pyPow, hd0, wn', dn', di', wabs, hb1, dlt, wlt1, Bool.false_eq_true, if_false,
            beq_self_eq_true, if_true]
        · have : Flt.fabs d = F64.inf false := by
            show F64.abs d = _
            have hdi : d = F64.inf true := by
              apply eq_of_fields
              · rw [ds', (inf_bits true).2]
              · have := (isInf_eq d).1 di; have h2 := (isInf_eq (F64.inf true)).1 (inf_bits true).1
                rw [this.1, h2.1]
              · have := (isInf_eq d).1 di; have h2 := (isInf_eq (F64.inf true)).1 (inf_bits true).1
                rw [this.2, h2.2]
            rw [hdi]; decide +kernel
          rw [this, one1]; exact one_le_inf
      · -- finite `d < 0`: libm `pow(w, d)`
        have di' : Flt.isInf d = false := isInf_false_of_finite df
        have hdr : d.toRat < 0 := dneg (by decide)
        have wne1 : w.toRat < 1 := by
          have : Flt.beq w (1.0 : F64) = false := hb1
          have e2 : F64.eq w F64.one = false := by rw [← one1]; exact this
          rw [eq_of_finite wf onef, show F64.one.toRat = 1 by decide +kernel] at e2
          have hne : w.toRat ≠ 1 := fun c => by rw [c] at e2; simp at e2
          exact Rat.lt_of_le_of_ne wle hne
        obtain ⟨pn, pc⟩ := hpow w d wf df wpos wne1 hdr
        have base : pyPow w d = (if Flt.isInf (Flt.pow w d) then
            .error (.overflowError "(34, 'Numerical result out of range')") else .ok (Flt.pow w d)) := by
          simp only [pyPow, hd0, wn', dn', di', wi, wbz, wneg, hb1, Bool.false_and, Bool.false_eq_true,
            if_false]
        rw [base]
        by_cases hpi : Flt.isInf (Flt.pow w d) = true
        · left; simp only [hpi, if_true]
        · right
          simp only [Bool.not_eq_true] at hpi
          refine ⟨Flt.pow w d, by simp only [hpi, Bool.false_eq_true, if_false], ?_⟩
          rcases pc with pc | pc
          · exact absurd pc (by rw [← Bool.not_eq_true] at hpi; exact hpi)
          · have pf : (RandLibm.pow w d).isFinite = true := by
              rcases classify (RandLibm.pow w d) with h | h | h
              · exact h
              · exact absurd h (by rw [← Bool.not_eq_true] at hpi; exact hpi)
              · rw [pn] at h; cases h
            show F64.le (1.0 : F64) (RandLibm.pow w d) = true
            rw [one1, le_of_finite onef pf, show F64.one.toRat = 1 by decide +kernel]
            exact decide_eq_true pc

/-! ### `weibullvariate`, Lib/random.py:775-784 -/

/-- A fact about the C library's `pow`: for finite `x > 0` and `y > 0` it is not NaN and
has a clear sign bit (`+0`, positive, or `+inf`). -/
def PowNonneg [RandLibm] : Prop :=
  ∀ x y : F64, x.isFinite = true → y.isFinite = true → 0 < x.toRat → 0 < y.toRat →
    (RandLibm.pow x y).isNaN = false ∧ (RandLibm.pow x y).sign = false

/-- `weibullvariate(alpha, beta)` is at least `0.0` for every finite `alpha > 0`, every
`beta > 0` (an infinite one included) and a `random()` value in `[0, 1)`, or raises the
`OverflowError` of `**`; after one draw. (`-0.0`, which `random() == 0.0` and `beta == 1.0`
give, counts: it is `>= 0.0`.) -/
def WeibullNonneg : Prop :=
  ∀ [RandLibm], LogNonpos → PowNonneg → ∀ (σ : Type) (g : Gen σ F64) (alpha beta u : F64) (s s1 : σ),
    g.random s = (u, s1) → u.isFinite = true → 0 ≤ u.toRat → u.toRat < 1 →
    alpha.isFinite = true → 0 < alpha.toRat → Flt.lt 0.0 beta = true →
    weibullvariate g alpha beta s = (.error (.overflowError "(34, 'Numerical result out of range')"), s1) ∨
    ∃ r, weibullvariate g alpha beta s = (.ok r, s1) ∧ Flt.le 0.0 r = true

theorem weibullNonneg_proven : WeibullNonneg := by
  intro _ hlog hpow σ g alpha beta u s s1 h hu h0 h1 haf ha0 hb
  rw [(betaParetoWeibullF64_proven σ g).2.2 alpha beta u s s1 h]
  obtain ⟨hl, lf, lle⟩ := mathLog_one_sub hlog hu h0 h1
  rw [hl, pyDiv_pos _ _ hb]
  simp only [ex_ok_bind]
  generalize hL : RandLibm.log (F64.sub F64.one u) = l at lf lle
  have one1 : (1.0 : F64) = F64.one := one_f64
  have zero0 : (0.0 : F64) = F64.zero false := zero_f64
  have onef : F64.one.isFinite = true := by decide +kernel
  have hb' : F64.lt (zero false) beta = true := by rw [← zero_f64]; exact hb
  obtain ⟨en, ec⟩ := div_classify onef (by decide +kernel) hb'
  rw [show F64.one.toRat = 1 by decide +kernel] at ec
  have hdiv1 : F64.div (1.0 : F64) beta = F64.div F64.one beta := by rw [one1]
  rw [hdiv1]
  generalize hE : F64.div F64.one beta = e at en ec
  -- `x = -log(1.0 - u)`: finite, `+x` or a zero
  have xf : (-l).isFinite = true := by show l.neg.isFinite = true; rw [neg_isFinite]; exact lf
  have xr : (-l).toRat = -l.toRat := toRat_neg l
  have x0 : 0 ≤ (-l).toRat := by rw [xr]; grind
  have zf := zero_isFinite false
  have xn : Flt.isNan (-l) = false := isNaN_false_of_finite xf
  have xi : Flt.isInf (-l) = false := isInf_false_of_finite xf
  have en' : Flt.isNan e = false := en
  have xneg : Flt.lt (-l) (0.0 : F64) = false := by
    show F64.lt (-l) _ = false
    rw [zero0, lt_of_finite xf zf, zero_toRat]
    exact decide_eq_false (Rat.not_lt.2 x0)
  -- the power is `Pos0` or the `OverflowError`
  have hp : pyPow (-l) e = .error (.overflowError "(34, 'Numerical result out of range')") ∨
      ∃ p, pyPow (-l) e = .ok p ∧ Pos0 p := by
    have p1 : Pos0 (1.0 : F64) := by rw [one1]; exact ⟨by decide +kernel, Or.inl (by decide +kernel)⟩
    have p0 : Pos0 (0.0 : F64) := by rw [zero0]; exact ⟨by decide +kernel, Or.inr (by decide +kernel)⟩
    by_cases he0 : Flt.beq e 0.0 = true
    · right; exact ⟨1.0, by simp only [pyPow, he0, if_true], p1⟩
    · simp only [Bool.not_eq_true] at he0
      rcases ec with ez | ⟨ei, es⟩ | ⟨ef, ez, _, epos⟩
      · exfalso
        have : Flt.beq e (0.0 : F64) = true := by
          show F64.eq e _ = true
          rw [zero0, eq_of_finite (isFinite_of_isZero ez) zf, zero_toRat, toRat_of_isZero ez]; rfl
        rw [this] at he0; cases he0
      · -- `e = +inf`
        have ei' : Flt.isInf e = true := ei
        have es' : e.sign = false := by rw [es]; decide
        right
        by_cases ha1 : Flt.beq (Flt.fabs (-l)) 1.0 = true
        · exact ⟨1.0, by simp only [pyPow, he0, xn, en', ei', ha1, Bool.false_eq_true, if_false, if_true], p1⟩
        · simp only [Bool.not_eq_true] at ha1
          by_cases hc : (Flt.lt 0.0 e == Flt.lt 1.0 (Flt.fabs (-l))) = true
          · refine ⟨Flt.fabs e, by simp only [pyPow, he0, xn, en', ei', ha1, hc, Bool.false_eq_true,
              if_false, if_true], ?_⟩
            show Pos0 (F64.abs e)
            simp only [F64.abs, es', Bool.false_eq_true, if_false]
            exact ⟨en, Or.inl es'⟩
          · simp only [Bool.not_eq_true] at hc
            exact ⟨0.0, by simp only [pyPow, he0, xn, en', ei', ha1, hc, Bool.false_eq_true, if_false, if_true], p0⟩
      · -- finite `e > 0`
        have ei' : Flt.isInf e = false := isInf_false_of_finite ef
        have er : 0 < e.toRat := epos (by decide)
        have elt : Flt.lt e (0.0 : F64) = false := by
          show F64.lt e _ = false
          rw [zero0, lt_of_finite ef zf, zero_toRat]
          exact decide_eq_false (Rat.not_lt.2 (Rat.le_of_lt er))
        by_cases hx0 : Flt.beq (-l) 0.0 = true
        · -- `x` is a zero: `x` or `0.0`, both zeros
          right
          have xz : (-l).isZero = true := by
            have : F64.eq (-l) (F64.zero false) = true := by rw [← zero0]; exact hx0
            rw [eq_of_finite xf zf, zero_toRat] at this
            exact (isZero_iff_toRat xf).2 (of_decide_eq_true this)
          by_cases hodd : Flt.isOddInteger e = true
          · exact ⟨-l, by simp only [pyPow, he0, xn, en', ei', xi, hx0, elt, hodd, Bool.false_eq_true,
              if_false, if_true], ⟨isNaN_false_of_finite xf, Or.inr xz⟩⟩
          · simp only [Bool.not_eq_true] at hodd
            exact ⟨0.0, by simp only [pyPow, he0, xn, en', ei', xi, hx0, elt, hodd, Bool.false_eq_true,
              if_false, if_true], p0⟩
        · simp only [Bool.not_eq_true] at hx0
          have xpos : 0 < (-l).toRat := by
            have : F64.eq (-l) (F64.zero false) = false := by rw [← zero0]; exact hx0
            rw [eq_of_finite xf zf, zero_toRat] at this
            have hne : (-l).toRat ≠ 0 := fun c => by rw [c] at this; simp at this
            exact Rat.lt_of_le_of_ne x0 (Ne.symm hne)
          by_cases ha1 : Flt.beq (-l) 1.0 = true
          · right
            exact ⟨1.0, by simp only [pyPow, he0, xn, en', ei', xi, hx0, xneg, ha1, Bool.false_and,
              Bool.false_eq_true, if_false, if_true], p1⟩
          · simp only [Bool.not_eq_true] at ha1
            obtain ⟨pn, ps⟩ := hpow (-l) e xf ef xpos er
            have base : pyPow (-l) e = (if Flt.isInf (Flt.pow (-l) e) then
                .error (.overflowError "(34, 'Numerical result out of range')") else .ok (Flt.pow (-l) e)) := by
              simp only [pyPow, he0, xn, en', ei', xi, hx0, xneg, ha1, Bool.false_and, Bool.false_eq_true,
                if_false]
            rw [base]
            by_cases hpi : Flt.isInf (Flt.pow (-l) e) = true
            · left; simp only [hpi, if_true]
            · right
              simp only [Bool.not_eq_true] at hpi
              exact ⟨Flt.pow (-l) e, by simp only [hpi, Bool.false_eq_true, if_false], ⟨pn, Or.inl ps⟩⟩
  rcases hp with hp | ⟨p, hp, pp⟩
  · left; rw [hp]; rfl
  · right
    refine ⟨alpha * p, ?_, ?_⟩
    · rw [hp]; rfl
    · show F64.le (0.0 : F64) (F64.mul alpha p) = true
      rw [zero0]
      exact le_zero_of (mul_pos0 haf ha0 pp)

end PyLean.CoreLibs.Rand
