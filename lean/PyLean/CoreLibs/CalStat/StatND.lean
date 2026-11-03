import PyLean.CoreLibs.CalStat.StatFmean

/-!
`NormalDist.__eq__` and `NormalDist.__hash__` (Lib/statistics.py:1432-1440): what equality means.
Equal objects are interchangeable: `pdf`, `cdf`, `zscore` and `inv_cdf` give results that compare
equal, and the hashes agree. The only distinct floats that compare equal are `0.0` and `-0.0`, so
this is about the sign of a zero `mu` or `sigma` flowing through the methods.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- The other operand of `X == other`: a `NormalDist`, or any other object. -/
inductive NDOther where
  | nd (Y : ND)
  | other (v : Val)

/-- `NormalDist.__eq__`, statistics.py:1432-1436; `none` is `NotImplemented`. -/
def ND.eqM (X : ND) : NDOther → Option Bool
  | .nd Y => some (Flt.eq X.mu Y.mu && Flt.eq X.sigma Y.sigma)
  | .other _ => none

/-- A float of the model is a binary64 value: `.fin` holds a non-zero number (zeros are `.zero`). -/
def Flt.Proper (x : Flt) : Prop := ∀ q, x = .fin q → q ≠ 0

def ND.Proper (X : ND) : Prop := X.mu.Proper ∧ X.sigma.Proper

/-- Results that compare equal, or are both NaN (which compares unequal to itself). -/
def Flt.Same (a b : Flt) : Prop := Flt.eq a b = true ∨ (a.isNan = true ∧ b.isNan = true)

theorem eq_cases {a b : Flt} (ha : a.Proper) (hb : b.Proper) (h : Flt.eq a b = true) :
    a = b ∨ ∃ s t, a = .zero s ∧ b = .zero t := by
  cases a with
  | zero s =>
    cases b with
    | zero t => exact Or.inr ⟨s, t, rfl, rfl⟩
    | fin q => simp [Flt.eq] at h; exact absurd h.symm (hb q rfl)
    | _ => simp [Flt.eq] at h
  | fin p =>
    cases b with
    | fin q => simp [Flt.eq] at h; left; rw [h]
    | zero t => simp [Flt.eq] at h; exact absurd h (ha p rfl)
    | _ => simp [Flt.eq] at h
  | inf s =>
    cases b with
    | inf t => simp [Flt.eq] at h; left; rw [h]
    | _ => simp [Flt.eq] at h
  | nan => simp [Flt.eq] at h

theorem eq_self (a : Flt) : Flt.eq a a = !a.isNan := by
  cases a <;> simp [Flt.eq, Flt.isNan]

theorem eq_trans' {a b c : Flt} (hb : b.Proper) (h1 : Flt.eq a b = true) (h2 : Flt.eq b c = true) :
    Flt.eq a c = true := by
  cases a <;> cases b <;> cases c <;> simp_all [Flt.eq]

theorem sq_zero (b : Bool) :
    Flt.mul (Flt.mul (Flt.neg Flt.half) (.zero b)) (.zero b) = .zero true := by
  cases b <;> decide

theorem div_zero_same (d : Flt) (s t : Bool) :
    Flt.div (.zero s) d = Flt.div (.zero t) d ∨
      ∃ u v, Flt.div (.zero s) d = .zero u ∧ Flt.div (.zero t) d = .zero v := by
  cases d <;> simp [Flt.div]

theorem sub_zero_same (x : Flt) (s t : Bool) :
    Flt.sub x (.zero s) = Flt.sub x (.zero t) ∨
      ∃ u v, Flt.sub x (.zero s) = .zero u ∧ Flt.sub x (.zero t) = .zero v := by
  cases x <;> simp [Flt.sub, Flt.add, Flt.neg]

/-- `-0.5 * z * z` with `z = (x - mu) / sigma` does not see the sign of a zero `mu`. -/
theorem pdf_top_zero (x σ : Flt) (s t : Bool) :
    (let z := Flt.div (Flt.sub x (.zero s)) σ
     Flt.mul (Flt.mul (Flt.neg Flt.half) z) z) =
    (let z := Flt.div (Flt.sub x (.zero t)) σ
     Flt.mul (Flt.mul (Flt.neg Flt.half) z) z) := by
  simp only
  rcases sub_zero_same x s t with h | ⟨u, v, h1, h2⟩
  · rw [h]
  · rw [h1, h2]
    rcases div_zero_same σ u v with h | ⟨u', v', h3, h4⟩
    · rw [h]
    · rw [h3, h4, sq_zero, sq_zero]

theorem zero_sub_same (x : Flt) (s t : Bool) :
    Flt.sub (.zero s) x = Flt.sub (.zero t) x ∨
      ∃ u v, Flt.sub (.zero s) x = .zero u ∧ Flt.sub (.zero t) x = .zero v := by
  cases x <;> simp [Flt.sub, Flt.add, Flt.neg]

theorem add_zero_same (y : Flt) (s t : Bool) : Flt.Same (Flt.add (.zero s) y) (Flt.add (.zero t) y) := by
  cases y <;> simp [Flt.Same, Flt.add, Flt.eq, Flt.isNan]

/-- `NormalDist.__eq__` and `__hash__`, statistics.py:1432-1440: "Two NormalDist objects are equal
if their mu and sigma are both equal", "NormalDist objects hash equal if their mu and sigma are
both equal". `==` against anything else is `NotImplemented`. The relation is symmetric and
transitive, and reflexive exactly when neither field is NaN. Equal objects hash equal, also for
`0.0` and `-0.0` (equal objects have no NaN field, so the identity hash of a NaN never enters). Equal objects are
interchangeable: `pdf(x)` is the same float, `cdf(x)` too when `erfc(0.0) == erfc(-0.0)` (C99 Annex
F: both are `1`), and `zscore(x)` results compare equal (or are both NaN), for every float
`x`. -/
def NormalDistEq : Prop :=
  ∀ (X Y Z : ND), X.Proper → Y.Proper → Z.Proper →
    (∀ v, X.eqM (.other v) = none) ∧
    (X.eqM (.nd Y) = some true ↔ Flt.eq X.mu Y.mu = true ∧ Flt.eq X.sigma Y.sigma = true) ∧
    X.eqM (.nd Y) = Y.eqM (.nd X) ∧
    (X.eqM (.nd X) = some true ↔ X.mu.isNan = false ∧ X.sigma.isNan = false) ∧
    (X.eqM (.nd Y) = some true → Y.eqM (.nd Z) = some true → X.eqM (.nd Z) = some true) ∧
    (X.eqM (.nd Y) = some true →
      (∀ i j i' j', ND.hash X i j = ND.hash Y i' j') ∧
      ∀ (L : Libm) (x : Flt),
        ND.pdf L X (.flt x) = ND.pdf L Y (.flt x) ∧
        ((∀ b, L.erfc (.zero b) = L.erfc (.zero false)) → ND.cdf L X (.flt x) = ND.cdf L Y (.flt x)) ∧
        (ND.zscore X (.flt x) = .error (.named "StatisticsError" "zscore() not defined when sigma is zero") ∧
          ND.zscore Y (.flt x) = .error (.named "StatisticsError" "zscore() not defined when sigma is zero") ∨
         ∃ r r', ND.zscore X (.flt x) = .ok (.flt r) ∧ ND.zscore Y (.flt x) = .ok (.flt r') ∧ Flt.Same r r'))

@[simp] theorem err_bind' {α β : Type} (e : PyExc) (f : α → Py β) : ((Except.error e : Py α) >>= f) = .error e := rfl

theorem same_refl_eq {r : Flt} : Flt.Same r r := by
  unfold Flt.Same; rw [eq_self]; cases r <;> simp [Flt.isNan]

theorem pdf_sigma_zero (L : Libm) (mu x : Flt) (b : Bool) :
    ND.pdf L ⟨mu, .zero b⟩ (.flt x) = .error (.named "StatisticsError" "pdf() not defined when sigma is zero") := by
  simp [ND.pdf, Flt.truthy, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, statErr]

theorem cdf_sigma_zero (L : Libm) (mu x : Flt) (b : Bool) :
    ND.cdf L ⟨mu, .zero b⟩ (.flt x) = .error (.named "StatisticsError" "cdf() not defined when sigma is zero") := by
  simp [ND.cdf, Flt.truthy, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, statErr]

theorem zscore_sigma_zero (mu x : Flt) (b : Bool) :
    ND.zscore ⟨mu, .zero b⟩ (.flt x) = .error (.named "StatisticsError" "zscore() not defined when sigma is zero") := by
  simp [ND.zscore, Flt.truthy, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, statErr]

theorem zscore_ok (mu σ x : Flt) (h : ∀ b, σ ≠ .zero b) :
    ND.zscore ⟨mu, σ⟩ (.flt x) = .ok (.flt (Flt.div (Flt.sub x mu) σ)) := by
  cases σ with
  | zero b => exact absurd rfl (h b)
  | _ => simp [ND.zscore, Flt.truthy, vsub, vdiv, arith, subOp, divOp, fltDiv, bind, Except.bind, pure,
      Except.pure, Functor.map, Except.map]

theorem pdf_mu_zero (L : Libm) (σ x : Flt) (s t : Bool) :
    ND.pdf L ⟨.zero s, σ⟩ (.flt x) = ND.pdf L ⟨.zero t, σ⟩ (.flt x) := by
  have key := pdf_top_zero x σ s t
  simp only at key
  cases σ with
  | zero b => rw [pdf_sigma_zero, pdf_sigma_zero]
  | _ =>
    simp only [ND.pdf, Flt.truthy, vsub, vdiv, arith, subOp, divOp, fltDiv, vmul, mulOp, asDouble, toFloat,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Bool.not_true, Bool.false_eq_true, ite_false]
    rw [key]

theorem cdf_mu_zero (L : Libm) (hE : ∀ b, L.erfc (.zero b) = L.erfc (.zero false)) (σ x : Flt) (s t : Bool) :
    ND.cdf L ⟨.zero s, σ⟩ (.flt x) = ND.cdf L ⟨.zero t, σ⟩ (.flt x) := by
  cases σ with
  | zero b => rw [cdf_sigma_zero, cdf_sigma_zero]
  | _ =>
    simp only [ND.cdf, Flt.truthy, vsub, vdiv, arith, subOp, divOp, fltDiv, asDouble, toFloat,
      bind, Except.bind, pure, Except.pure, Functor.map, Except.map, Bool.not_true, Bool.false_eq_true, ite_false]
    rcases zero_sub_same x s t with h | ⟨u, v, h1, h2⟩
    · rw [h]
    · rw [h1, h2]
      generalize Flt.mul _ sqrt2 = d
      cases d with
      | zero c => rfl
      | _ =>
        simp only
        rcases div_zero_same _ u v with h | ⟨u', v', h3, h4⟩
        · rw [h]
        · rw [h3, h4]; simp only [mathErfc, hE]

theorem zscore_mu_zero (σ x : Flt) (s t : Bool) (h : ∀ b, σ ≠ .zero b) :
    ∃ r r', ND.zscore ⟨.zero s, σ⟩ (.flt x) = .ok (.flt r) ∧ ND.zscore ⟨.zero t, σ⟩ (.flt x) = .ok (.flt r') ∧
      Flt.Same r r' := by
  refine ⟨_, _, zscore_ok _ _ _ h, zscore_ok _ _ _ h, ?_⟩
  rcases sub_zero_same x s t with h1 | ⟨u, v, h1, h2⟩
  · rw [h1]; exact same_refl_eq
  · rw [h1, h2]
    rcases div_zero_same σ u v with h3 | ⟨u', v', h3, h4⟩
    · rw [h3]; exact same_refl_eq
    · rw [h3, h4]; left; rfl

theorem normalDistEq_proven : NormalDistEq := by
  intro X Y Z hX hY hZ
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ND.eqM]
  · simp only [ND.eqM, eq_symm X.mu Y.mu, eq_symm X.sigma Y.sigma]
  · simp [ND.eqM, eq_self]
  · intro h1 h2
    simp only [ND.eqM, Option.some.injEq, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨eq_trans' hY.1 h1.1 h2.1, eq_trans' hY.2 h1.2 h2.2⟩
  · intro h
    simp only [ND.eqM, Option.some.injEq, Bool.and_eq_true] at h
    obtain ⟨hm, hs⟩ := h
    refine ⟨?_, ?_⟩
    · intro i j i' j'
      simp only [ND.hash, hashObj_eq _ _ i i' hm, hashObj_eq _ _ j j' hs]
    intro L x
    obtain ⟨mu, sigma⟩ := X
    obtain ⟨mu', sigma'⟩ := Y
    simp only at hm hs
    have zs : ∀ (m σ : Flt), (∃ b, σ = .zero b) ∨ (∀ b, σ ≠ .zero b) := by
      intro m σ; cases σ <;> simp
    rcases eq_cases hX.2 hY.2 hs with rfl | ⟨a, b, rfl, rfl⟩
    · rcases zs mu sigma with ⟨c, rfl⟩ | hnz
      · -- `sigma` is a zero: every method refuses, whatever `mu`
        refine ⟨by rw [pdf_sigma_zero, pdf_sigma_zero], fun _ => by rw [cdf_sigma_zero, cdf_sigma_zero],
          Or.inl ⟨zscore_sigma_zero _ _ _, zscore_sigma_zero _ _ _⟩⟩
      · rcases eq_cases hX.1 hY.1 hm with rfl | ⟨s, t, rfl, rfl⟩
        · exact ⟨rfl, fun _ => rfl, Or.inr ⟨_, _, zscore_ok _ _ _ hnz, zscore_ok _ _ _ hnz, same_refl_eq⟩⟩
        · exact ⟨pdf_mu_zero L _ _ s t, fun hE => cdf_mu_zero L hE _ _ s t, Or.inr (zscore_mu_zero _ _ s t hnz)⟩
    · refine ⟨by rw [pdf_sigma_zero, pdf_sigma_zero], fun _ => by rw [cdf_sigma_zero, cdf_sigma_zero],
        Or.inl ⟨zscore_sigma_zero _ _ _, zscore_sigma_zero _ _ _⟩⟩

/-! ## `NormalDist.from_samples` -/

def ovf : PyExc := .overflowError "integer division result too large for a float"

theorem intTrueDiv_err (a b : Int) (hb : b ≠ 0) (e : PyExc) (h : intTrueDiv a b = .error e) : e = ovf := by
  unfold intTrueDiv at h
  rw [if_neg hb] at h
  simp only at h
  split at h
  · cases h
  · split at h <;> cases h; rfl

theorem ofRat_not_neg (q : Rat) (hq : ¬ q < 0) : Flt.lt (Flt.ofRat q) Flt.pz = false := by
  unfold Flt.ofRat
  split
  · rfl
  · simp only [hq, decide_false]
    split
    · rfl
    · split
      · rfl
      · simp only [Flt.lt, Flt.pz, Flt.toRat, Bool.false_eq_true, ite_false, decide_eq_false_iff_not]
        have h0 : (0 : Rat) ≤ Flt.pow2 (Flt.roundMag q.num.natAbs q.den).2 := Rat.le_of_lt (pow2_pos _)
        have := Rat.mul_nonneg (Rat.natCast_nonneg (a := (Flt.roundMag q.num.natAbs q.den).1)) h0
        grind

/-- A float `intTrueDiv` returns for a non-negative numerator and positive denominator is not
negative. -/
theorem intTrueDiv_nonneg (a b : Int) (ha : 0 ≤ a) (hb : 0 < b) (r : Flt) (h : intTrueDiv a b = .ok r) :
    Flt.lt r Flt.pz = false := by
  unfold intTrueDiv at h
  rw [if_neg (by omega)] at h
  simp only at h
  have hn : ((a < 0) != (b < 0)) = false := by simp; omega
  have hq : ¬ ((a : Rat) / (b : Rat) < 0) := by
    have h1 : (0 : Rat) ≤ (a : Rat) := Rat.intCast_nonneg.mpr ha
    have h2 : (0 : Rat) < (b : Rat) := Rat.intCast_pos.mpr hb
    intro hc
    rw [Rat.div_lt_iff h2] at hc
    grind
  have key := ofRat_not_neg _ hq
  split at h
  · cases h; simp [hn, Flt.lt, Flt.pz, Flt.toRat]
  · generalize hX : Flt.ofRat ((a : Rat) / (b : Rat)) = X at h key
    cases X <;> simp at h <;> subst h <;> exact key

theorem isqrtInt_ok (x : Int) (hx : 0 ≤ x) : ∃ r, isqrtInt x = .ok r ∧ 0 ≤ r := by
  obtain ⟨r, h1, -, -⟩ := MathInt.isqrtFloorSqrt_proven x.toNat
  have : ((x.toNat : Nat) : Int) = x := by omega
  rw [this] at h1
  exact ⟨r, by simp [isqrtInt, h1, Functor.map, Except.map], by omega⟩

theorem rto_ok (n m : Int) (hn : 0 ≤ n) (hm : 0 < m) : ∃ r, integerSqrtOfFracRto n m = .ok r ∧ 0 ≤ r := by
  obtain ⟨a, ha, ha0⟩ := isqrtInt_ok (n / m) (Int.ediv_nonneg hn (by omega))
  refine ⟨if a * a * m ≠ n then ((a.toNat ||| 1 : Nat) : Int) else a,
    by simp only [integerSqrtOfFracRto, ha, bind, Except.bind, pure, Except.pure], ?_⟩
  split <;> omega

/-- `_float_sqrt_of_frac(n, m)` for `n >= 0`, `m > 0` fails only by overflow and never gives a
negative float. -/
theorem floatSqrt_facts (n m : Int) (hn : 0 ≤ n) (hm : 0 < m) :
    (∀ e, floatSqrtOfFrac n m = .error e → e = ovf) ∧
    (∀ r, floatSqrtOfFrac n m = .ok r → Flt.lt r Flt.pz = false) := by
  unfold floatSqrtOfFrac
  simp only
  split
  · rename_i hq
    have hm' : 0 < m * 2 ^ (2 * ((bitLen n - bitLen m - sqrtBitWidth) / 2)).toNat :=
      Int.mul_pos hm (Int.pow_pos (by decide))
    obtain ⟨r, hr, hr0⟩ := rto_ok n _ hn hm'
    rw [bind_ok hr]
    have h0 : 0 ≤ r * 2 ^ ((bitLen n - bitLen m - sqrtBitWidth) / 2).toNat :=
      Int.mul_nonneg hr0 (Int.le_of_lt (Int.pow_pos (by decide)))
    exact ⟨fun e h => intTrueDiv_err _ 1 (by decide) e h, fun r' h => intTrueDiv_nonneg _ 1 h0 (by decide) r' h⟩
  · have hn' : 0 ≤ n * 2 ^ (-2 * ((bitLen n - bitLen m - sqrtBitWidth) / 2)).toNat :=
      Int.mul_nonneg hn (Int.le_of_lt (Int.pow_pos (by decide)))
    obtain ⟨r, hr, hr0⟩ := rto_ok _ m hn' hm
    rw [bind_ok hr]
    have hp : (0 : Int) < 2 ^ (-((bitLen n - bitLen m - sqrtBitWidth) / 2)).toNat := Int.pow_pos (by decide)
    exact ⟨fun e h => intTrueDiv_err _ _ (by omega) e h, fun r' h => intTrueDiv_nonneg _ _ hr0 hp r' h⟩

theorem rat_sq_nonneg (a : Rat) : 0 ≤ a * a := by
  by_cases h : 0 ≤ a
  · exact Rat.mul_nonneg h h
  · have h' : 0 ≤ -a := by grind
    have := Rat.mul_nonneg h' h'
    grind

theorem sumDev_nonneg (qs : List Rat) (c : Rat) : 0 ≤ sumDev qs c := by
  unfold sumDev
  induction qs with
  | nil => exact Rat.le_refl
  | cons a l ih =>
    simp only [List.map_cons, sumQ_cons]
    have := rat_sq_nonneg (a - c)
    grind

theorem ratToFlt_err (q : Rat) (e : PyExc) (h : ratToFlt q = .error e) : e = ovf :=
  intTrueDiv_err _ _ (by have := q.den_pos; omega) e h

/-- `NormalDist.from_samples(data)`, Lib/statistics.py:1246-1249, for `Fraction` data: it is the same
as `NormalDist(mean(data), stdev(data))`, outcome for outcome: `mu` is the exact mean correctly
rounded and `sigma` the correctly rounding square root `_float_sqrt_of_frac` of the exact sample
variance, and an `OverflowError` of either conversion is the same. (Doc/library/statistics.rst:918-919
says the parameters are estimated "using fmean() and stdev()"; the code uses the exact mean, which is
`mean()`, not `fmean()`, and the two differ by rounding.) Fewer than two points raise. -/
def FromSamplesTwin : Prop :=
  ∀ qs : List Rat,
    (2 ≤ qs.length → ND.fromSamples (fracs qs) =
      (do let μ ← mean (fracs qs); let σ ← stdev (fracs qs) none; ND.mk' μ.v σ)) ∧
    (qs.length < 2 → ND.fromSamples (fracs qs) =
      .error (.named "StatisticsError" "stdev requires at least two data points"))

theorem fromSamplesTwin_proven : FromSamplesTwin := by
  intro qs
  refine ⟨?_, ?_⟩
  · intro h2
    obtain ⟨v, hvar, hstd, hms⟩ := (stdevOfVariance_proven qs).1 h2
    have hne : qs ≠ [] := by intro h; rw [h] at h2; simp at h2
    have hmean := meanFractions_proven.1 qs hne
    have hv0 : 0 ≤ v := by
      have hvf := (varianceFractions_proven qs).1 h2
      rw [hvar] at hvf
      have hv : v = sumDev qs (meanQ qs) / ((qs.length - 1 : Nat) : Rat) := by
        have := congrArg PyN.v (Except.ok.inj hvf)
        simpa [Val.toN] using this
      rw [hv]
      have hd : (0 : Rat) < ((qs.length - 1 : Nat) : Rat) := Rat.natCast_pos.mpr (by omega)
      exact le_div_of_mul_le hd (by rw [Rat.zero_mul]; exact sumDev_nonneg _ _)
    have hnum : 0 ≤ v.num := Rat.num_nonneg.mpr hv0
    have hden : (0 : Int) < (v.den : Int) := by have := v.den_pos; omega
    obtain ⟨hse, hsn⟩ := floatSqrt_facts v.num v.den hnum hden
    simp only [ND.fromSamples, hms, hmean, hstd, ok_bind']
    have hmk : ∀ (q : Rat) (sv : Flt), Flt.lt sv Flt.pz = false →
        ND.mk' (Val.frac q).toN.v (Val.flt sv) = (ratToFlt q).map (fun m => (⟨m, sv⟩ : ND)) := by
      intro q sv h0
      simp only [ND.mk', vltPy_flt, h0, Val.toN, toFloat, bind, Except.bind, pure, Except.pure]
      cases ratToFlt q <;> rfl
    have hmk2 : ∀ (m sv : Flt), Flt.lt sv Flt.pz = false → ND.mk' (Val.flt m) (Val.flt sv) = .ok ⟨m, sv⟩ := by
      intro m sv h0
      simp only [ND.mk', vltPy_flt, h0, toFloat, bind, Except.bind, pure, Except.pure]
      rfl
    unfold meanQ at *
    cases hs : floatSqrtOfFrac v.num v.den with
    | error e2 =>
      have he2 := hse e2 hs
      cases hr : ratToFlt (sumQ qs / (qs.length : Rat)) with
      | error e1 =>
        have he1 := ratToFlt_err _ e1 hr
        simp [bind, Except.bind, Functor.map, Except.map, he1, he2]
      | ok m => simp [bind, Except.bind, Functor.map, Except.map]
    | ok sv =>
      have hs0 := hsn sv hs
      simp only [Functor.map, Except.map, ok_bind']
      rw [hmk _ _ hs0]
      cases hr : ratToFlt (sumQ qs / (qs.length : Rat)) with
      | error e1 => simp [bind, Except.bind, Except.map]
      | ok m =>
        simp only [ok_bind', Except.map]
        exact hmk2 m sv hs0
  · intro h
    match qs, h with
    | [], _ => exact fromSamplesShort_proven.1
    | [q], _ => exact fromSamplesShort_proven.2 q

/-! ## `quantiles` over a fallible iterable -/

/-- `quantiles(data, n=n, method=method)` with `data` any iterable, statistics.py:1193-1196: the
check of `n` comes first; then `sorted(data)` builds the list (`list(iterable)`, so the iterator's
exception propagates before any comparison) and sorts it. -/
def quantilesIt (data : PyIter) (n : Int) (method : String) : Py (List PyN) :=
  if n < 1 then .error (statErr "n must be at least 1")
  else match data.iterErr, data.fin with
    | some e, _ => .error e
    | none, some e => .error e
    | none, none => quantiles data.items n method

/-- The iteration of `quantiles`: with `n < 1` the iterable is not touched (whatever its iterator
would raise); otherwise an exception of the iterator comes out before the data is compared; an
iterable that ends normally gives what the list of its items gives. -/
def QuantilesIter : Prop :=
  ∀ (data : PyIter) (n : Int) (me : String),
    (n < 1 → quantilesIt data n me = .error (.named "StatisticsError" "n must be at least 1")) ∧
    (1 ≤ n → ∀ e, (data.iterErr = some e ∨ (data.iterErr = none ∧ data.fin = some e)) →
      quantilesIt data n me = .error e) ∧
    (data.iterErr = none → data.fin = none → quantilesIt data n me = quantiles data.items n me)

theorem quantilesIter_proven : QuantilesIter := by
  intro data n me
  refine ⟨fun h => by simp [quantilesIt, h, statErr], fun h e he => ?_, fun he hf => ?_⟩
  · have : ¬ n < 1 := by omega
    rcases he with he | ⟨he, hf⟩
    · simp [quantilesIt, this, he]
    · simp [quantilesIt, this, he, hf]
  · by_cases h : n < 1
    · simp [quantilesIt, h, quantiles, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, statErr]
    · simp [quantilesIt, h, he, hf]

/-! ## The value of `NormalDist.__hash__` -/

/-- The numeric hash of a rational `q` (Doc/library/stdtypes.rst, "Hashing of numeric types", and
`Lib/fractions.py` `_hash_algorithm`): `|num| * inverse(den)` modulo `P = 2**61 - 1`, with the sign of
`q`, and `-1` replaced by `-2`. The inverse is given by its defining property, not by a formula. -/
def NumHash (q : Rat) (h : Int) : Prop :=
  ∃ r : Nat, r < hashModulus ∧ (r * q.den) % hashModulus = q.num.natAbs % hashModulus ∧
    h = (let v : Int := if q < 0 then -(r : Int) else r; if v = -1 then -2 else v)

theorem pow61_mod (t : Nat) : (2 ^ (61 * t)) % hashModulus = 1 := by
  rw [Nat.pow_mul, Nat.pow_mod]
  have : 2 ^ 61 % hashModulus = 1 := by decide
  rw [this, Nat.one_pow]; decide

/-- `_Py_HashDouble` of a finite non-zero float, whose denominator is a power of two, is its numeric
hash: the same value as `hash(Fraction(x))`. -/
theorem hashFlt_numHash (q : Rat) (k : Nat) (hk : q.den = 2 ^ k) : NumHash q (hashFlt (.fin q)) := by
  have hlog : Nat.log2 q.den = k := by rw [hk, Nat.log2_two_pow]
  refine ⟨(q.num.natAbs * 2 ^ ((61 - k % 61) % 61)) % hashModulus, Nat.mod_lt _ (by decide), ?_, ?_⟩
  · rw [hk]
    have he : (61 - k % 61) % 61 + k = 61 * ((k + 60) / 61) := by omega
    rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, he, Nat.mul_mod, pow61_mod, Nat.mul_one, Nat.mod_mod]
  · simp only [hashFlt, hlog]

/-- `NormalDist.__hash__`, statistics.py:1438-1440, where it is defined by value (no NaN field): it is
the tuple hash of the two field hashes, and each finite non-zero field hashes as its exact value does,
`hash(Fraction(mu))` and `hash(Fraction(sigma))` (`0.0` and `-0.0` hash `0`, the infinities
`+-314159`, `sys.hash_info.inf`). A NaN field hashes by the identity of the float object, an input
of the model, so `hash(NormalDist(nan, 1.0))` is not a function of the values. -/
def NormalDistHashValue : Prop :=
  ∀ (X : ND) (i j : Int), X.mu.isNan = false → X.sigma.isNan = false →
    ND.hash X i j = hashTuple [hashFlt X.mu, hashFlt X.sigma] ∧
    (∀ q k, (X.mu = .fin q ∨ X.sigma = .fin q) → q.den = 2 ^ k → NumHash q (hashFlt (.fin q))) ∧
    (∀ b, hashFlt (.zero b) = 0) ∧ hashFlt (.inf false) = 314159 ∧ hashFlt (.inf true) = -314159

theorem normalDistHashValue_proven : NormalDistHashValue := by
  intro X i j hm hs
  refine ⟨?_, fun q k _ hk => hashFlt_numHash q k hk, fun _ => rfl, rfl, rfl⟩
  obtain ⟨mu, sigma⟩ := X
  cases mu <;> cases sigma <;> simp_all [ND.hash, hashFltObj, Flt.isNan]

/-! ## `from_samples` against the documentation and against `mean`/`stdev` on floats -/

/-- Doc/library/statistics.rst:918-919: from_samples "Makes a normal distribution instance with mu and
sigma parameters estimated from the data using fmean() and stdev()". For float data, the outcome is
that of `NormalDist(fmean(data), stdev(data))`. -/
def FromSamplesFmeanStdev : Prop :=
  ∀ xs : List Flt, 2 ≤ xs.length →
    ND.fromSamples (floats xs) =
      (do let μ ← fmean (floats xs) none; let σ ← stdev (floats xs) none; ND.mk' μ σ)

/-- `[0.1, 0.1, 0.1]`: `_mean_stdev` takes the exact mean, `0.1`; `fmean` gives
`0.10000000000000002` (`fsum` rounds `0.3000000000000000166...` up, then the division rounds). -/
theorem fromSamplesFmeanStdev_refuted : ¬FromSamplesFmeanStdev := by
  intro h
  have := h [f01, f01, f01] (by decide)
  have e1 : ND.fromSamples (floats [f01, f01, f01]) = .ok ⟨f01, .zero false⟩ := by decide +kernel
  rw [e1] at this
  revert this
  decide +kernel

/-- The twin of `FromSamplesTwin` beyond Fractions: for float data, `from_samples(data)` has the
outcome of `NormalDist(mean(data), stdev(data))`. -/
def FromSamplesTwinFloats : Prop :=
  ∀ xs : List Flt, 2 ≤ xs.length →
    ND.fromSamples (floats xs) =
      (do let μ ← mean (floats xs); let σ ← stdev (floats xs) none; ND.mk' μ.v σ)

/-- `[nan, 1.0]`: `_mean_stdev` "handles Nans and Infs gracefully" (statistics.py:1767-1769) and gives
`NormalDist(nan, nan)`, while `stdev` raises `ValueError('inf or nan encountered in data')`. -/
theorem fromSamplesTwinFloats_refuted : ¬FromSamplesTwinFloats := by
  intro h
  have := h [.nan, Flt.one] (by decide)
  have e1 : ND.fromSamples (floats [.nan, Flt.one]) = .ok ⟨.nan, .nan⟩ := by decide +kernel
  rw [e1] at this
  revert this
  decide +kernel

end PyLean.CoreLibs.CalStat
