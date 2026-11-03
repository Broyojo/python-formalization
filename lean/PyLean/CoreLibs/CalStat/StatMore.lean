import PyLean.CoreLibs.CalStat.StatGeo

/-!
`NormalDist.pdf` (Lib/statistics.py:1259-1265): the shape of the density, and
`linear_regression` (Lib/statistics.py:745-805) with an intercept against the regression through the
origin of the centred data.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-! ## Signs through the float operations -/

theorem neg_ne {q : Rat} (h : q ≠ 0) : -q ≠ 0 := by intro h'; apply h; grind

theorem decide_neg_lt (q : Rat) (h : q ≠ 0) : decide (-q < 0) = !decide (q < 0) := by
  by_cases hq : q < 0
  · have : ¬ (-q < 0) := by grind
    simp [hq, this]
  · have : -q < 0 := by grind
    simp [hq, this]

/-- `x * (-y) == -(x * y)` for a non-zero finite `y`. -/
theorem mul_neg_fin (x : Flt) (b : Rat) (hb : b ≠ 0) (hx : x.Proper) :
    Flt.mul x (Flt.neg (.fin b)) = Flt.neg (Flt.mul x (.fin b)) := by
  cases x with
  | nan => rfl
  | inf s => simp [Flt.mul, Flt.neg, decide_neg_lt b hb]
  | zero s => simp [Flt.mul, Flt.neg, decide_neg_lt b hb]
  | fin a =>
    have ha : a ≠ 0 := hx a rfl
    have hab : a * b ≠ 0 := by intro h; rcases Rat.mul_eq_zero.mp h with h | h <;> contradiction
    simp only [Flt.neg, Flt.mul]
    rw [show a * -b = -(a * b) by grind, ofRat_neg _ hab]
    cases hr : Flt.ofRat (a * b) <;> simp [Flt.neg, decide_neg_lt _ hab]

/-- `(-x) * y == -(x * y)` for a non-zero finite `x`. -/
theorem neg_fin_mul (a : Rat) (y : Flt) (ha : a ≠ 0) (hy : y.Proper) :
    Flt.mul (Flt.neg (.fin a)) y = Flt.neg (Flt.mul (.fin a) y) := by
  cases y with
  | nan => rfl
  | inf s => simp [Flt.mul, Flt.neg, decide_neg_lt a ha]
  | zero s => simp [Flt.mul, Flt.neg, decide_neg_lt a ha]
  | fin b =>
    have hb : b ≠ 0 := hy b rfl
    have hab : a * b ≠ 0 := by intro h; rcases Rat.mul_eq_zero.mp h with h | h <;> contradiction
    simp only [Flt.neg, Flt.mul]
    rw [show -a * b = -(a * b) by grind, ofRat_neg _ hab]
    cases hr : Flt.ofRat (a * b) <;> simp [Flt.neg, decide_neg_lt _ hab]

theorem ofRat_proper (q : Rat) : (Flt.ofRat q).Proper := by
  intro v hv
  unfold Flt.ofRat at hv
  split at hv
  · cases hv
  · simp only at hv
    generalize hRM : Flt.roundMag q.num.natAbs q.den = RM at hv
    obtain ⟨m, e⟩ := RM
    simp only at hv
    split at hv
    · cases hv
    · split at hv
      · cases hv
      · rename_i hm _
        cases hv
        have hp := pow2_pos e
        have hm' : (0 : Rat) < (m : Rat) := Rat.natCast_pos.mpr (by omega)
        have : (0 : Rat) < (m : Rat) * Flt.pow2 e := Rat.mul_pos hm' hp
        split <;> grind

theorem neg_proper {x : Flt} (h : x.Proper) : (Flt.neg x).Proper := by
  intro q hq
  cases x with
  | fin a => simp [Flt.neg] at hq; subst hq; exact neg_ne (h a rfl)
  | _ => simp [Flt.neg] at hq

theorem mul_proper (x y : Flt) : (Flt.mul x y).Proper := by
  intro q hq
  cases x <;> cases y <;> simp [Flt.mul] at hq
  rename_i a b
  generalize hr : Flt.ofRat (a * b) = r at hq
  have := ofRat_proper (a * b)
  rw [hr] at this
  cases r <;> simp at hq
  subst hq; exact this _ rfl

theorem div_proper (x y : Flt) : (Flt.div x y).Proper := by
  intro q hq
  cases x <;> cases y <;> simp [Flt.div] at hq
  rename_i a b
  generalize hr : Flt.ofRat (a / b) = r at hq
  have := ofRat_proper (a / b)
  rw [hr] at this
  cases r <;> simp at hq
  subst hq; exact this _ rfl

/-- `-x / y == -(x / y)` for `y` a positive finite float. -/
theorem neg_div_pos (x : Flt) (b : Rat) (hb : 0 < b) (hx : x.Proper) :
    Flt.div (Flt.neg x) (.fin b) = Flt.neg (Flt.div x (.fin b)) := by
  have hb0 : b ≠ 0 := by grind
  have hbn : ¬ b < 0 := by grind
  cases x with
  | nan => rfl
  | inf s => simp [Flt.div, Flt.neg, Flt.signBit, hbn]
  | zero s => simp [Flt.div, Flt.neg, hbn]
  | fin a =>
    have ha : a ≠ 0 := hx a rfl
    have hab : a / b ≠ 0 := by
      intro h
      have := Rat.div_mul_cancel (a := a) hb0
      rw [h, Rat.zero_mul] at this
      exact ha this.symm
    simp only [Flt.neg, Flt.div]
    rw [show -a / b = -(a / b) by simp only [Rat.div_def]; grind, ofRat_neg _ hab]
    cases hr : Flt.ofRat (a / b) <;> simp [Flt.neg, decide_neg_lt _ hab]

/-- The exponent `-0.5 * z * z` of the density is even in `z`. -/
theorem top_even (z : Flt) (hz : z.Proper) :
    Flt.mul (Flt.mul (Flt.neg Flt.half) (Flt.neg z)) (Flt.neg z) =
      Flt.mul (Flt.mul (Flt.neg Flt.half) z) z := by
  cases z with
  | nan => rfl
  | zero s => cases s <;> decide
  | inf s => cases s <;> decide
  | fin b =>
    have hb : b ≠ 0 := hz b rfl
    have hc := mul_proper (Flt.neg Flt.half) (.fin b)
    rw [mul_neg_fin _ b hb (neg_proper (by intro q hq; cases hq; decide))]
    generalize hu : Flt.mul (Flt.neg Flt.half) (.fin b) = u at hc
    cases u with
    | fin c =>
      have hc0 : c ≠ 0 := hc c rfl
      rw [mul_neg_fin _ b hb (neg_proper hc), neg_fin_mul c (.fin b) hc0 (by intro q hq; cases hq; exact hb),
        neg_neg]
    | nan => rfl
    | inf s => simp [Flt.neg, Flt.mul, decide_neg_lt b hb]
    | zero s => simp [Flt.neg, Flt.mul, decide_neg_lt b hb]

theorem add_proper {x y : Flt} (hx : x.Proper) (hy : y.Proper) : (Flt.add x y).Proper := by
  intro q hq
  cases x <;> cases y <;> simp only [Flt.add] at hq
  all_goals first
    | (cases hq; done)
    | (split at hq <;> cases hq)
    | (cases hq; first | exact hx _ rfl | exact hy _ rfl)
    | exact ofRat_proper _ q hq

theorem ofRat_not_nan (q : Rat) : Flt.ofRat q ≠ .nan := by
  intro h
  unfold Flt.ofRat at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
    · split at h <;> cases h

theorem sub_proper {x y : Flt} (hx : x.Proper) (hy : y.Proper) : (Flt.sub x y).Proper :=
  add_proper hx (neg_proper hy)

def sqrt2piQ : Rat := mkRat 5644425081792261 2251799813685248

theorem sqrt2pi_eq : sqrt2pi = .fin sqrt2piQ := by decide +kernel

/-! ## `NormalDist.pdf` -/

/-- `NormalDist.pdf`, Lib/statistics.py:1259-1265, has the shape of the normal density, for every
`mu` and every positive `sigma`:

* it is symmetric about `mu`: two floats on either side of `mu` at the same computed distance
  (`x' - mu == -(x - mu)` exactly) have the same density, bit for bit, whatever `exp` returns;
* at `mu` it is the peak `1 / (sqrt(tau) * sigma)`, given `exp(-0.0) == 1.0` (C99 Annex F);
* it vanishes at both infinities: `pdf(inf) == pdf(-inf) == 0.0`, given `exp(-inf) == 0.0`
  (Annex F). `sigma` is at least the smallest subnormal, as every positive float is.

A constant function fails the last two together. -/
def PdfShape : Prop :=
  ∀ (L : Libm) (X : ND) (b : Rat), 0 < b → Flt.pow2 (-1074) ≤ b → X.sigma = .fin b → X.mu.Proper →
    (∀ x x', x.Proper → Flt.sub x' X.mu = Flt.neg (Flt.sub x X.mu) →
      ND.pdf L X (.flt x') = ND.pdf L X (.flt x)) ∧
    (X.mu.isFinite = true → L.exp (.zero true) = Flt.one →
      ND.pdf L X (.flt X.mu) = Val.flt <$> fltDiv Flt.one (Flt.mul sqrt2pi X.sigma)) ∧
    (X.mu.isFinite = true → L.exp (.inf true) = .zero false →
      ND.pdf L X (.flt (.inf false)) = .ok (.flt (.zero false)) ∧
      ND.pdf L X (.flt (.inf true)) = .ok (.flt (.zero false)))

theorem pdf_unfold (L : Libm) (X : ND) (b : Rat) (hX : X.sigma = .fin b) (x : Flt) :
    ND.pdf L X (.flt x) =
      match mathExp L (Flt.mul (Flt.mul (Flt.neg Flt.half) (Flt.div (Flt.sub x X.mu) X.sigma))
          (Flt.div (Flt.sub x X.mu) X.sigma)) with
      | .error e => .error e
      | .ok r => (fltDiv r (Flt.mul sqrt2pi X.sigma)).map .flt :=
  pdfExact_proven L X x (by rw [hX]; rfl) ⟨b, hX⟩

theorem pdfShape_proven : PdfShape := by
  intro L X b hb hmin hX hmu
  have hbn : ¬ b < 0 := by grind
  refine ⟨?_, ?_, ?_⟩
  · intro x x' hx hd
    rw [pdf_unfold L X b hX x, pdf_unfold L X b hX x', hd, hX,
      neg_div_pos _ b hb (sub_proper hx hmu), top_even _ (div_proper _ _)]
  · intro hf hE
    rw [pdf_unfold L X b hX X.mu, hX]
    have hz : Flt.sub X.mu X.mu = .zero false := by
      cases h : X.mu with
      | zero s => cases s <;> rfl
      | fin a =>
        simp only [Flt.sub, Flt.neg, Flt.add]
        rw [show a + -a = 0 by grind, ofRat_zero']
      | _ => rw [h] at hf; simp [Flt.isFinite] at hf
    have hd : Flt.div (.zero false) (.fin b) = .zero false := by simp [Flt.div, hbn]
    rw [hz, hd, sq_zero]
    have he1 : mathExp L (.zero true) = .ok Flt.one := by
      simp [mathExp, math1, hE, Flt.one, Flt.isNan, Flt.isInf]
    rw [he1]
    rfl
  · intro hf hE
    -- the scale `sqrt(tau) * sigma` is a positive float or `+inf`
    have hsb : Flt.pow2 (-1074) ≤ sqrt2piQ * b := by
      have h2 : (1 : Rat) ≤ sqrt2piQ := by decide +kernel
      have := Rat.mul_le_mul_of_nonneg_right h2 (Rat.le_of_lt hb)
      generalize Flt.pow2 (-1074) = P at *
      grind
    have hden : (fltDiv (.zero false) (Flt.mul sqrt2pi (.fin b))) = .ok (.zero false) := by
      rw [sqrt2pi_eq]
      simp only [Flt.mul]
      have hne := ofRat_pos_ne_zero hsb
      have hs0 : (0 : Rat) < sqrt2piQ := by decide +kernel
      have hnn := ofRat_not_neg (sqrt2piQ * b) (Rat.not_lt.mpr (Rat.le_of_lt (Rat.mul_pos hs0 hb)))
      cases hr : Flt.ofRat (sqrt2piQ * b) with
      | zero s => exact absurd hr (hne s)
      | nan => exact absurd hr (ofRat_not_nan _)
      | inf s =>
        rw [hr] at hnn
        simp only [Flt.lt, Flt.pz] at hnn
        subst hnn; rfl
      | fin c =>
        rw [hr] at hnn
        simp only [Flt.lt, Flt.pz, Flt.toRat] at hnn
        have hc : ¬ c < 0 := fun h => by simp [h] at hnn
        simp [fltDiv, Flt.div, hc]
    have hinf : ∀ s : Bool, Flt.sub (.inf s) X.mu = .inf s := by
      intro s
      cases h : X.mu with
      | zero t => rfl
      | fin a => rfl
      | _ => rw [h] at hf; simp [Flt.isFinite] at hf
    have hT : ∀ s : Bool, Flt.mul (Flt.mul (Flt.neg Flt.half) (Flt.div (.inf s) (.fin b)))
        (Flt.div (.inf s) (.fin b)) = .inf true := by
      intro s; cases s <;> simp [Flt.div, Flt.signBit, hbn, Flt.mul, Flt.neg, Flt.half] <;> decide
    have hexp : mathExp L (.inf true) = .ok (.zero false) := by
      simp [mathExp, math1, hE, Flt.isNan, Flt.isInf]
    refine ⟨?_, ?_⟩
    · rw [pdf_unfold L X b hX, hinf, hX, hT, hexp]
      simp only [hden]; rfl
    · rw [pdf_unfold L X b hX, hinf, hX, hT, hexp]
      simp only [hden]; rfl

/-! ## `linear_regression` with an intercept -/

theorem lrCore_split (a b : List PyN) (xb yb : Flt) :
    lrCore a b false xb yb = (do
      let r ← lrCore a b true Flt.pz Flt.pz
      let i ← vsub (.flt yb) (← vmul r.1 (.flt xb))
      return (r.1, i)) := by
  unfold lrCore
  cases sumprod a b with
  | error e => rfl
  | ok sxy =>
    simp only [ok_bind']
    cases vadd sxy (.flt Flt.pz) with
    | error e => rfl
    | ok s1 =>
      simp only [ok_bind']
      cases sumprod a a with
      | error e => rfl
      | ok sxx =>
        simp only [ok_bind']
        cases vdiv s1 sxx with
        | error e =>
          cases e <;> simp [bind, Except.bind, pure, Except.pure]
        | ok sl =>
          simp only [ok_bind', Bool.false_eq_true, ite_false, ite_true, pure, Except.pure]

theorem centered_length (x : List PyN) (c : Flt) (r : List PyN) (h : centered x c = .ok r) :
    r.length = x.length := by
  unfold centered at h
  exact mapM_length _ _ _ h

theorem fmean_fbar (x : List PyN) (hn : x ≠ []) (hl : x.length < 2 ^ 53) :
    fmean x none = Val.flt <$> fbar x := by
  have hl0 : x.length ≠ 0 := by simpa using hn
  have hI : intToFlt (x.length : Int) = .ok (Flt.ofInt (x.length : Int)) := by
    rw [intToFlt_small _ (by omega), if_neg (by omega)]
    unfold Flt.ofInt
    rw [ofRat_int _ (by omega) (by omega)]
  simp only [fmean, fbar]
  cases fsumV (x.map (·.v)) with
  | error e => rfl
  | ok t =>
    simp only [ok_bind', hl0, ite_false, vdiv, arith, divOp, hI]
    have : Flt.ofInt (x.length : Int) = Flt.ofInt ((x.length : Nat) : Int) := rfl
    cases fltDiv t (Flt.ofInt (x.length : Int)) <;> rfl

/-- `linear_regression(x, y)` with the default `proportional=False`, Lib/statistics.py:790-805: the
means are `fsum(x) / n` and `fsum(y) / n`, which are `fmean(x)` and `fmean(y)`; the slope is that of
the regression through the origin of the centred data `[xi - xbar]`, `[yi - ybar]`
(`linear_regression(..., proportional=True)` of them, including its "x is constant" error), and the
intercept is `ybar - slope * xbar`. This is the textbook reduction of least squares with an
intercept to least squares through the origin. The length checks come first. -/
def LinRegCentred : Prop :=
  ∀ x y : List PyN, x.length = y.length → 2 ≤ x.length → x.length < 2 ^ 53 →
    linearRegression x y false = (do
      let xbar ← fbar x
      let ybar ← fbar y
      let r ← linearRegression (← centered x xbar) (← centered y ybar) true
      let i ← vsub (.flt ybar) (← vmul r.1 (.flt xbar))
      return (r.1, i)) ∧
    fmean x none = Val.flt <$> fbar x ∧ fmean y none = Val.flt <$> fbar y

theorem linRegCentred_proven : LinRegCentred := by
  intro x y hl h2 hlt
  have hx : x ≠ [] := by intro h; rw [h] at h2; simp at h2
  have hy : y ≠ [] := by intro h; subst h; simp only [List.length_nil] at hl; omega
  refine ⟨?_, fmean_fbar x hx hlt, fmean_fbar y hy (by omega)⟩
  have hc1 : (y.length != x.length) = false := by simp [hl]
  have hc2 : ¬ x.length < 2 := by omega
  simp only [linearRegression, hc1, Bool.false_eq_true, ite_false, hc2, Bool.not_false, ite_true]
  cases fbar x with
  | error e => rfl
  | ok xb =>
    simp only [ok_bind']
    cases fbar y with
    | error e => rfl
    | ok yb =>
      simp only [ok_bind']
      cases hcx : centered x xb with
      | error e => rfl
      | ok x' =>
        simp only [ok_bind']
        cases hcy : centered y yb with
        | error e => rfl
        | ok y' =>
          have l1 := centered_length _ _ _ hcx
          have l2 := centered_length _ _ _ hcy
          have hc1' : (y'.length != x'.length) = false := by simp [l1, l2, hl]
          have hc2' : ¬ x'.length < 2 := by omega
          simp only [ok_bind', pure, Except.pure, hc1', Bool.false_eq_true, ite_false, hc2', Bool.not_true]
          rw [lrCore_split]
          rfl

end PyLean.CoreLibs.CalStat
