import PyLean.CoreLibs.CalStat.StatMore

/-!
Branches of Lib/statistics.py that the earlier theorems left out: the empty-data and too-few-points
refusals, the one-point `quantiles`, the Decimal paths of `mean`, `variance`, `pvariance`, `stdev`,
`pstdev` and `_convert`, the `numerator`/`denominator` fallback of `_exact_ratio`, `NormalDist.__pos__`
re-validating `sigma`, and the density at one standard deviation.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- "If data is empty, StatisticsError is raised", statistics.py:343-344, :369-370, :391-392. -/
def MedianEmpty : Prop :=
  median [] = .error (.named "StatisticsError" "no median for empty data") ∧
  medianLow [] = .error (.named "StatisticsError" "no median for empty data") ∧
  medianHigh [] = .error (.named "StatisticsError" "no median for empty data")

theorem medianEmpty_proven : MedianEmpty := ⟨rfl, rfl, rfl⟩

/-- `quantiles` of one data point, statistics.py:1199-1201: the point repeated `n - 1` times,
whatever the method. -/
def QuantilesOne : Prop :=
  ∀ (x : PyN) (n : Int) (me : String), 1 ≤ n → quantiles [x] n me = .ok (List.replicate (n - 1).toNat x)

theorem quantilesOne_proven : QuantilesOne := by
  intro x n me h
  have : ¬ n < 1 := by omega
  simp [quantiles, this, pySorted, bind, Except.bind, pick, pure, Except.pure]

/-! ## Decimal data -/

def decs (ds : List Rat) : List PyN := ds.map (fun q => (Val.dec (.fin q)).toN)

theorem decs_props (ds : List Rat) :
    (∀ x ∈ decs ds, IsExact x.v) ∧ (∀ x ∈ decs ds, x.cls = clsDecimal) ∧
      (decs ds).map (fun x => exactQ x.v) = ds := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [decs, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    trivial
  · intro x hx
    simp only [decs, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    rfl
  · simp [decs, List.map_map, Function.comp_def, Val.toN, exactQ]

theorem coerceD : reduceCoerce [clsDecimal] = .ok clsDecimal := by decide

theorem sum_decs (ds : List Rat) (hne : ds ≠ []) :
    sumOf (decs ds) id = .ok (clsDecimal, .frac (sumQ ds), ds.length) := by
  obtain ⟨h1, h2, h3⟩ := decs_props ds
  have hf : decs ds ≠ [] := by simpa [decs] using hne
  rw [sumOf_exact _ h1 hf, h3, typesOf_const _ _ h2 hf]
  simp only [id, coerceD]
  simp [decs]
  rfl

theorem ss_decs (ds : List Rat) (hne : ds ≠ []) :
    ssOf (decs ds) none id =
      .ok (clsDecimal, .frac (sumDev ds (meanQ ds)), .frac (meanQ ds), ds.length) := by
  obtain ⟨h1, h2, h3⟩ := decs_props ds
  have hf : decs ds ≠ [] := by simpa [decs] using hne
  obtain ⟨P, Q, e1, e2, e3⟩ := ss_fold (decs ds) h1 {} rfl (by simp) (by simp)
  have hmapsq : (decs ds).map (fun x => exactQ x.v * exactQ x.v) = ds.map (fun x => x * x) := by
    simp [decs, List.map_map, Function.comp_def, Val.toN, exactQ]
  rw [hmapsq] at e3
  rw [h3] at e2
  have hP : sumPartials P = sumQ ds := by
    rw [e2]; simp only [sumPartials, List.foldr_nil]; grind
  have hQ : sumPartialsSq Q = sumQ (ds.map (fun x => x * x)) := by
    rw [e3]; simp only [sumPartialsSq, List.foldr_nil]; grind
  have hn := length_ne ds hne
  have hlen : (decs ds).length = ds.length := by simp [decs]
  have hty : typesOf [] (decs ds) = [clsDecimal] := typesOf_const _ _ h2 hf
  have hf0 : ¬(0 + (decs ds).length = 0) := by omega
  simp only [ssOf, bind, Except.bind, e1, hP, hQ, hty, hf0, if_false, Nat.zero_add]
  have hform := ss_formula ds hne
  have h0 : ¬ ds.length = 0 := by omega
  simp only [hlen, id, coerceD, pure, Except.pure, h0, if_false]
  unfold sumDev meanQ
  rw [← hform]

/-- `_convert(value, T)`, statistics.py:1624-1641: a value already of type `T` (a NaN or infinity
included) is returned as it is; to `Decimal` a `Fraction` goes through the `TypeError` fallback
`T(value.numerator) / T(value.denominator)` (:1637-1640), the 28-digit half-even rounding. -/
def ConvertBranches : Prop :=
  (∀ x : Flt, convert (.flt x) clsFloat = .ok (Val.flt x).toN) ∧
  (∀ d : Dec, convert (.dec d) clsDecimal = .ok (Val.dec d).toN) ∧
  (∀ q : Rat, convert (.frac q) clsDecimal = .ok (Val.dec (.fin (decRound q))).toN)

theorem convertBranches_proven : ConvertBranches := by
  refine ⟨fun _ => rfl, fun _ => rfl, ?_⟩
  intro q
  have hd' : q.den ≠ 0 := q.den_nz
  have hq' : (q.num : Rat) / (q.den : Rat) = q := by rw [← Rat.mkRat_eq_div, Rat.mkRat_self]
  simp only [convert, Val.cls, Cls.same, construct, isSubclass, clsDecimal, clsInt, clsFloat, clsFraction]
  simp [Dec.div, hd', hq', bind, Except.bind, pure, Except.pure, Val.toN, Val.cls]

/-- The Decimal examples of `mean`, `variance` and `stdev`: on finite Decimal data, `mean` is the exact
mean rounded to 28 digits (the docstring's `Decimal('0.5625')`), `variance`/`pvariance` the exact
variance rounded so, and `stdev`/`pstdev` take `_decimal_sqrt_of_frac` of the exact variance
(statistics.py:628-629, :651-652), not the float root. Too few points raise first. -/
def DecimalPaths : Prop :=
  ∀ ds : List Rat,
    (ds ≠ [] → mean (decs ds) = .ok (Val.dec (.fin (decRound (meanQ ds)))).toN) ∧
    (2 ≤ ds.length →
      variance (decs ds) none =
        .ok (Val.dec (.fin (decRound (sumDev ds (meanQ ds) / ((ds.length - 1 : Nat) : Rat))))).toN ∧
      stdev (decs ds) none = (fun r => Val.dec (.fin r)) <$>
        decimalSqrtOfFrac (sumDev ds (meanQ ds) / ((ds.length - 1 : Nat) : Rat)).num
          (sumDev ds (meanQ ds) / ((ds.length - 1 : Nat) : Rat)).den) ∧
    (1 ≤ ds.length →
      pvariance (decs ds) none =
        .ok (Val.dec (.fin (decRound (sumDev ds (meanQ ds) / (ds.length : Rat))))).toN ∧
      pstdev (decs ds) none = (fun r => Val.dec (.fin r)) <$>
        decimalSqrtOfFrac (sumDev ds (meanQ ds) / (ds.length : Rat)).num
          (sumDev ds (meanQ ds) / (ds.length : Rat)).den)

theorem isSub_dec : isSubclass clsDecimal clsDecimal = true := by decide

theorem decimalPaths_proven : DecimalPaths := by
  intro ds
  have hc := convertBranches_proven.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    have hn := length_ne ds hne
    simp only [mean, bind, Except.bind, sum_decs ds hne]
    rw [if_neg (by omega), vdiv_frac_int _ _ (by omega)]
    exact hc _
  · intro h2
    have hne : ds ≠ [] := by intro h; simp [h] at h2
    have hss := ss_decs ds hne
    refine ⟨?_, ?_⟩
    · simp only [variance, bind, Except.bind]
      rw [hss]
      simp only
      rw [if_neg (by omega), vdiv_frac_int' _ _ h2]
      exact hc _
    · simp only [stdev, bind, Except.bind]
      rw [hss]
      simp only
      rw [if_neg (by omega), vdiv_frac_int' _ _ h2]
      simp only [sqrtTail, isSub_dec, ite_true]
  · intro h1
    have hne : ds ≠ [] := by intro h; simp [h] at h1
    have hss := ss_decs ds hne
    refine ⟨?_, ?_⟩
    · simp only [pvariance, bind, Except.bind]
      rw [hss]
      simp only
      rw [if_neg (by omega), vdiv_frac_int _ _ (by omega)]
      exact hc _
    · simp only [pstdev, bind, Except.bind]
      rw [hss]
      simp only
      rw [if_neg (by omega), vdiv_frac_int _ _ (by omega)]
      simp only [sqrtTail, isSub_dec, ite_true]

/-- The too-few-points refusals of `variance`, `pvariance`, `stdev`, `pstdev` (statistics.py:562-563,
:605-606, :620-621, :643-644), for any numeric data (`Fraction`s here) of too few points. -/
def TooFewPoints : Prop :=
  ∀ qs : List Rat,
    (qs.length < 2 →
      variance (fracs qs) none = .error (.named "StatisticsError" "variance requires at least two data points") ∧
      stdev (fracs qs) none = .error (.named "StatisticsError" "stdev requires at least two data points")) ∧
    pvariance [] none = .error (.named "StatisticsError" "pvariance requires at least one data point") ∧
    pstdev [] none = .error (.named "StatisticsError" "pstdev requires at least one data point")

theorem tooFewPoints_proven : TooFewPoints := by
  intro qs
  refine ⟨?_, by decide, by decide⟩
  intro h
  match qs, h with
  | [], _ => exact ⟨by decide, by decide⟩
  | [q], _ =>
    have hss := ss_fracs [q] (by simp)
    refine ⟨?_, ?_⟩
    · simp only [variance, bind, Except.bind, hss]; rfl
    · simp only [stdev, bind, Except.bind, hss]; rfl

/-- `_exact_ratio`'s fallback, statistics.py:1614-1618: an object that is neither float nor Decimal
but has `numerator` and `denominator` (an Integral or Rational ABC instance) gives that pair. -/
def ExactRatioFallback : Prop := ∀ (n : Int) (d : Nat), exactRatio (.abc n d) = .ok (.ratio n d)

theorem exactRatioFallback_proven : ExactRatioFallback := fun _ _ => rfl

/-- `NormalDist.__pos__`, statistics.py:1416-1418, builds a new instance through `__init__`, which
validates `sigma` again: an instance whose negative `sigma` came from `__setstate__` makes `+X`
raise, which a body returning `x1` itself would not. Otherwise `+X` has the same fields. -/
def PosRevalidates : Prop :=
  ∀ X : ND, ND.pos X =
    if Flt.lt X.sigma Flt.pz then .error (.named "StatisticsError" "sigma must be non-negative")
    else .ok X

theorem posRevalidates_proven : PosRevalidates := by
  intro X
  simp only [ND.pos, ND.mk', vltPy_flt, toFloat, bind, Except.bind]
  split <;> rfl

/-- The density one standard deviation from the mean, statistics.py:1264-1265: when `x - mu` is
exactly `sigma`, `z` is `1.0` and the exponent is `-0.5`, so `pdf(x) = exp(-0.5) / (sqrt(tau) *
sigma)`. A body that forgot to divide by `sigma`, or used `exp(-z*z)`, passes `-0.5 * sigma**2` or
`-1.0` to `exp` instead. -/
def PdfOneSigma : Prop :=
  ∀ (L : Libm) (X : ND) (b : Rat) (x : Flt), 0 < b → X.sigma = .fin b → Flt.sub x X.mu = .fin b →
    ND.pdf L X (.flt x) =
      match mathExp L (.fin (mkRat (-1) 2)) with
      | .error e => .error e
      | .ok r => (fltDiv r (Flt.mul sqrt2pi X.sigma)).map .flt

theorem pdfOneSigma_proven : PdfOneSigma := by
  intro L X b x hb hX hd
  rw [pdf_unfold L X b hX x, hd, hX]
  have hb0 : b ≠ 0 := by grind
  have hz : Flt.div (.fin b) (.fin b) = .fin 1 := by
    simp only [Flt.div]
    rw [show b / b = 1 by simp only [Rat.div_def]; exact Rat.mul_inv_cancel b hb0]
    have : Flt.ofRat 1 = .fin 1 := by decide +kernel
    rw [this]
  have ht : Flt.mul (Flt.mul (Flt.neg Flt.half) (.fin 1)) (.fin 1) = .fin (mkRat (-1) 2) := by decide +kernel
  rw [hz, ht]
  cases mathExp L (.fin (mkRat (-1) 2)) <;> rfl

/-! ## NaN and infinite data: the `partials[None]` branch -/

/-- `partials[None] = partials.get(None, 0) + n` over the non-finite items in order (statistics.py:
1499-1503 and :1541-1545): the first one as it is (`0 + x`), the next ones added. -/
def addSpecial (spec : Option Flt) (x : Flt) : Flt :=
  match spec with
  | some f => Flt.add f x
  | none => x

def accumSpecial (acc : Option Flt) (xs : List Flt) : Option Flt :=
  xs.foldl (fun acc x => if x.isFinite then acc else some (addSpecial acc x)) acc

theorem vadd_zero_special (x : Flt) (h : x.isFinite = false) : vadd (.int 0) (.flt x) = .ok (.flt x) := by
  cases x <;> simp_all [Flt.isFinite, vadd, arith, addOp, intToFlt, Flt.ofInt, Flt.ofRat, Flt.add, bind,
    Except.bind, pure, Except.pure]

theorem accum_cons (spec : Option Flt) (x : Flt) (xs : List Flt) :
    accumSpecial spec (x :: xs) = accumSpecial (if x.isFinite then spec else some (addSpecial spec x)) xs := rfl

/-- The new special after one non-finite item, as `vadd` computes it. -/
theorem vadd_special (spec : Option Flt) (x : Flt) (h : x.isFinite = false) :
    vadd ((spec.map Val.flt).getD (.int 0)) (.flt x) = .ok (.flt (addSpecial spec x)) := by
  cases spec with
  | none => exact vadd_zero_special x h
  | some f => rfl

theorem sum_fold_special (xs : List Flt) : ∀ (spec : Option Flt) (st : SumSt), st.special = spec.map Val.flt →
    ∃ P, (floats xs).foldlM sumStep st = .ok (SumSt.mk (st.count + xs.length)
      (typesOf st.types (floats xs)) P ((accumSpecial spec xs).map Val.flt)) := by
  induction xs with
  | nil =>
    intro spec st h
    refine ⟨st.partials, ?_⟩
    cases st
    simp only at h
    simp [floats, typesOf, accumSpecial, h]
    rfl
  | cons x xs ih =>
    intro spec st h
    simp only [floats, List.map_cons, List.foldlM_cons]
    rw [accum_cons]
    cases hx : x.isFinite with
    | true =>
      have hs : ∃ n d, exactRatio (Val.flt x) = .ok (.ratio n d) := by
        cases x <;> simp [Flt.isFinite] at hx <;> exact ⟨_, _, rfl⟩
      obtain ⟨n, d, hr⟩ := hs
      have e : sumStep st (Val.flt x).toN = .ok (SumSt.mk (st.count + 1) (addType st.types clsFloat)
          (addPartial st.partials d n) st.special) := by
        simp only [sumStep, Val.toN, Val.cls, hr, ok_bind']; rfl
      rw [bind_ok e]
      obtain ⟨P, hP⟩ := ih spec (SumSt.mk (st.count + 1) (addType st.types clsFloat)
          (addPartial st.partials d n) st.special) h
      refine ⟨P, ?_⟩
      simp only [floats] at hP
      rw [hP]
      simp only [ite_true, typesOf, List.foldl_cons, List.length_cons, Val.toN, Val.cls]
      congr 2; omega
    | false =>
      have hr : exactRatio (Val.flt x) = .ok (.special (.flt x)) := by
        cases x <;> simp [Flt.isFinite] at hx <;> rfl
      have e : sumStep st (Val.flt x).toN = .ok (SumSt.mk (st.count + 1) (addType st.types clsFloat)
          st.partials (some (.flt (addSpecial spec x)))) := by
        simp only [sumStep, Val.toN, Val.cls, hr, ok_bind', h, vadd_special spec x hx]; rfl
      rw [bind_ok e]
      obtain ⟨P, hP⟩ := ih (some (addSpecial spec x)) (SumSt.mk (st.count + 1) (addType st.types clsFloat)
          st.partials (some (.flt (addSpecial spec x)))) rfl
      refine ⟨P, ?_⟩
      simp only [floats] at hP
      rw [hP]
      simp only [Bool.false_eq_true, ite_false, typesOf, List.foldl_cons, List.length_cons, Val.toN, Val.cls]
      congr 2; omega

theorem ss_fold_special (xs : List Flt) : ∀ (spec : Option Flt) (st : SsSt), st.specialX = spec.map Val.flt →
    ∃ P Q, (floats xs).foldlM ssStep st = .ok (SsSt.mk (st.count + xs.length)
      (typesOf st.types (floats xs)) P Q ((accumSpecial spec xs).map Val.flt)) := by
  induction xs with
  | nil =>
    intro spec st h
    refine ⟨st.sx, st.sxx, ?_⟩
    cases st
    simp only at h
    simp [floats, typesOf, accumSpecial, h]
    rfl
  | cons x xs ih =>
    intro spec st h
    simp only [floats, List.map_cons, List.foldlM_cons]
    rw [accum_cons]
    cases hx : x.isFinite with
    | true =>
      have hs : ∃ n d, exactRatio (Val.flt x) = .ok (.ratio n d) := by
        cases x <;> simp [Flt.isFinite] at hx <;> exact ⟨_, _, rfl⟩
      obtain ⟨n, d, hr⟩ := hs
      have e : ssStep st (Val.flt x).toN = .ok (SsSt.mk (st.count + 1) (addType st.types clsFloat)
          (addPartial st.sx d n) (addPartial st.sxx d (n * n)) st.specialX) := by
        simp only [ssStep, Val.toN, Val.cls, hr, ok_bind']; rfl
      rw [bind_ok e]
      obtain ⟨P, Q, hP⟩ := ih spec (SsSt.mk (st.count + 1) (addType st.types clsFloat)
          (addPartial st.sx d n) (addPartial st.sxx d (n * n)) st.specialX) h
      refine ⟨P, Q, ?_⟩
      simp only [floats] at hP
      rw [hP]
      simp only [ite_true, typesOf, List.foldl_cons, List.length_cons, Val.toN, Val.cls]
      congr 2; omega
    | false =>
      have hr : exactRatio (Val.flt x) = .ok (.special (.flt x)) := by
        cases x <;> simp [Flt.isFinite] at hx <;> rfl
      have e : ssStep st (Val.flt x).toN = .ok (SsSt.mk (st.count + 1) (addType st.types clsFloat)
          st.sx st.sxx (some (.flt (addSpecial spec x)))) := by
        simp only [ssStep, Val.toN, Val.cls, hr, ok_bind', h, vadd_special spec x hx]; rfl
      rw [bind_ok e]
      obtain ⟨P, Q, hP⟩ := ih (some (addSpecial spec x)) (SsSt.mk (st.count + 1) (addType st.types clsFloat)
          st.sx st.sxx (some (.flt (addSpecial spec x)))) rfl
      refine ⟨P, Q, ?_⟩
      simp only [floats] at hP
      rw [hP]
      simp only [Bool.false_eq_true, ite_false, typesOf, List.foldl_cons, List.length_cons, Val.toN, Val.cls]
      congr 2; omega

theorem floats_cls (xs : List Flt) : ∀ x ∈ floats xs, x.cls = clsFloat := by
  intro x hx; simp only [floats, List.mem_map] at hx; obtain ⟨q, _, rfl⟩ := hx; rfl

/-- NaN or infinite float data, the `partials[None]` branch of `_sum` and `_ss` (statistics.py:1499-1503,
:1541-1545) and what the averages make of it. `s` is the sum, in order, of the non-finite items
(`accumSpecial`, defined only when there is one): `_sum` returns `s` as the total (so `[inf, -inf, 1.0]`
sums to `nan`, `[inf, 2.0, inf]` to `inf`), `_ss` returns `s` both as the sum of squares and as the mean,
`mean`, `variance` and `pvariance` return `s / n`, `s / (n - 1)` and `s / n` as floats, and `stdev` and `pstdev` raise
`ValueError('inf or nan encountered in data')` (:626-627, :649-650). `n` is below `2**53`, as for any
list that fits in memory. -/
def SpecialData : Prop :=
  ∀ (xs : List Flt) (s : Flt), xs.length < 2 ^ 53 → accumSpecial none xs = some s →
    sumOf (floats xs) id = .ok (clsFloat, .flt s, xs.length) ∧
    ssOf (floats xs) none id = .ok (clsFloat, .flt s, .flt s, xs.length) ∧
    (2 ≤ xs.length →
      stdev (floats xs) none = .error (.valueError "inf or nan encountered in data") ∧
      variance (floats xs) none = .ok (Val.flt (Flt.div s (Flt.ofInt ((xs.length : Int) - 1)))).toN) ∧
    (1 ≤ xs.length →
      pstdev (floats xs) none = .error (.valueError "inf or nan encountered in data") ∧
      pvariance (floats xs) none = .ok (Val.flt (Flt.div s (Flt.ofInt (xs.length : Int)))).toN ∧
      mean (floats xs) = .ok (Val.flt (Flt.div s (Flt.ofInt (xs.length : Int)))).toN)

theorem accum_none_ne (xs : List Flt) (s : Flt) (h : accumSpecial none xs = some s) : xs ≠ [] := by
  intro h'; subst h'; simp [accumSpecial] at h

theorem intToFlt_len (n : Nat) (h1 : 1 ≤ n) (h : n < 2 ^ 53) :
    intToFlt (n : Int) = .ok (Flt.ofInt (n : Int)) ∧ ∃ q, Flt.ofInt (n : Int) = .fin q := by
  have e := ofRat_int (n : Int) (by omega) (by omega)
  refine ⟨?_, _, e⟩
  rw [intToFlt_small _ (by omega), if_neg (by omega)]
  simp only [Flt.ofInt]; rw [e]

theorem specialData_proven : SpecialData := by
  intro xs s hlen hs
  have hne := accum_none_ne xs s hs
  have hty : typesOf [] (floats xs) = [clsFloat] := typesOf_const _ _ (floats_cls xs) (by simpa [floats] using hne)
  obtain ⟨P, hP⟩ := sum_fold_special xs none {} rfl
  obtain ⟨P2, Q2, hQ⟩ := ss_fold_special xs none {} rfl
  have hl0 : xs.length ≠ 0 := by simpa using hne
  have hsum : sumOf (floats xs) id = .ok (clsFloat, .flt s, xs.length) := by
    simp only [sumOf, hP, ok_bind', sumFinish, hs, Option.map_some, hty, id, coerce3, Nat.zero_add]; rfl
  have hss : ssOf (floats xs) none id = .ok (clsFloat, .flt s, .flt s, xs.length) := by
    simp only [ssOf, hQ, ok_bind', hs, Option.map_some, hty, id, coerce3, Nat.zero_add, hl0, ite_false]; rfl
  refine ⟨hsum, hss, ?_, ?_⟩
  · intro h2
    obtain ⟨hI, q, hq⟩ := intToFlt_len (xs.length - 1) (by omega) (by omega)
    have e1 : ((xs.length : Int) - 1) = ((xs.length - 1 : Nat) : Int) := by omega
    have hv : vdiv (.flt s) (.int ((xs.length : Int) - 1)) = .ok (.flt (Flt.div s (Flt.ofInt ((xs.length : Int) - 1)))) := by
      rw [e1]; simp only [vdiv, arith, divOp, hI, ok_bind', fltDiv, hq, pure, Except.pure]
    have h2' : ¬ xs.length < 2 := by omega
    refine ⟨?_, ?_⟩
    · simp only [stdev, hss, ok_bind', h2', ite_false, hv, sqrtTail]
    · simp only [variance, hss, ok_bind', h2', ite_false, hv]; rfl
  · intro h1
    obtain ⟨hI, q, hq⟩ := intToFlt_len xs.length h1 hlen
    have hv : vdiv (.flt s) (.int (xs.length : Int)) = .ok (.flt (Flt.div s (Flt.ofInt (xs.length : Int)))) := by
      simp only [vdiv, arith, divOp, hI, ok_bind', fltDiv, hq, pure, Except.pure]
    have h1' : ¬ xs.length < 1 := by omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [pstdev, hss, ok_bind', h1', ite_false, hv, sqrtTail]
    · simp only [pvariance, hss, ok_bind', h1', ite_false, hv]; rfl
    · simp only [mean, hsum, ok_bind', h1', ite_false, hv]; rfl

/-! ## `harmonic_mean` with weights -/

/-- The term `w / x if w else 0` for a Fraction weight and a positive Fraction value. -/
def hmTerm (a q : Rat) : PyN := if a = 0 then (Val.int 0).toN else (Val.frac (a / q)).toN

theorem hmBody_w (msg : String) (st : SumSt) (a q : Rat) (h : 0 < q) :
    hmBody msg st (.frac a, .frac q) = sumStep st (hmTerm a q) := by
  have hq : q ≠ 0 := by grind
  have hn : ¬ q < 0 := by grind
  simp only [hmBody, bind, Except.bind, vltPy_frac, hn, decide_false, Bool.false_eq_true, if_false, hmTerm]
  by_cases ha : a = 0
  · subst ha; simp [Val.truthy, pure, Except.pure]
  · have : (Val.frac a).truthy = true := by simp [Val.truthy, ha]
    simp only [this, ite_true, ha, ite_false, vdiv, arith, divOp, if_neg hq]

theorem hm_fold_w (msg : String) (ws qs : List Rat) (st : SumSt) (h : ∀ q ∈ qs, 0 < q) :
    ((ws.map .frac).zip (qs.map .frac)).foldlM (hmBody msg) st =
      ((ws.zip qs).map (fun p => hmTerm p.1 p.2)).foldlM sumStep st := by
  induction ws generalizing qs st with
  | nil => rfl
  | cons a as ih =>
    cases qs with
    | nil => rfl
    | cons q qs =>
      simp only [List.map_cons, List.zip_cons_cons, List.foldlM_cons]
      rw [hmBody_w msg st a q (h q (by simp))]
      cases sumStep st (hmTerm a q) with
      | error e => rfl
      | ok st' => exact ih qs st' (fun r hr => h r (List.mem_cons_of_mem _ hr))

theorem hmTerm_exact (a q : Rat) : IsExact (hmTerm a q).v ∧ exactQ (hmTerm a q).v = a / q ∧
    ((hmTerm a q).cls = clsInt ∨ (hmTerm a q).cls = clsFraction) ∧ (a ≠ 0 → (hmTerm a q).cls = clsFraction) := by
  unfold hmTerm
  by_cases ha : a = 0
  · subst ha; simp [IsExact, exactQ, Val.toN, Val.cls, Rat.div_def]
  · simp [ha, IsExact, exactQ, Val.toN, Val.cls]

/-- The sets of types the weighted terms can produce, closed under `types.add`. -/
def hmTypes : List (List Cls) := [[], [clsInt], [clsFraction], [clsInt, clsFraction], [clsFraction, clsInt]]

theorem typesOf_hm (l : List PyN) (h : ∀ x ∈ l, x.cls = clsInt ∨ x.cls = clsFraction) :
    ∀ ts ∈ hmTypes, typesOf ts l ∈ hmTypes ∧
      (clsFraction ∈ ts ∨ (∃ x ∈ l, x.cls = clsFraction) → clsFraction ∈ typesOf ts l) := by
  induction l with
  | nil => intro ts hts; simp [typesOf, hts]
  | cons x xs ih =>
    intro ts hts
    have hx := h x (by simp)
    have hr : ∀ y ∈ xs, y.cls = clsInt ∨ y.cls = clsFraction := fun y hy => h y (by simp [hy])
    have hstep : addType ts x.cls ∈ hmTypes ∧ (clsFraction ∈ ts ∨ x.cls = clsFraction → clsFraction ∈ addType ts x.cls) := by
      simp only [hmTypes, List.mem_cons, List.not_mem_nil, or_false] at hts
      rcases hx with hx | hx <;> rw [hx] <;> rcases hts with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨h1, h2⟩ := ih hr _ hstep.1
    refine ⟨by simpa [typesOf] using h1, fun hc => ?_⟩
    simp only [typesOf, List.foldl_cons]
    apply h2
    rcases hc with hc | ⟨y, hy, hyc⟩
    · exact Or.inl (hstep.2 (Or.inl hc))
    · rcases List.mem_cons.mp hy with rfl | hy'
      · exact Or.inl (hstep.2 (Or.inr hyc))
      · exact Or.inr ⟨y, hy', hyc⟩

theorem reduce_hm (ts : List Cls) (h : ts ∈ hmTypes) (hf : clsFraction ∈ ts) :
    reduceCoerce ts = .ok clsFraction := by
  simp only [hmTypes, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl <;> revert hf <;> decide

/-- `harmonic_mean(data, weights)`, statistics.py:306-325, the weighted harmonic mean the docstring
defines ("the reciprocal of the arithmetic mean of the reciprocals ... weighted"), for positive
Fraction data and non-negative Fraction weights: `sum(w) / sum(w / x)` exactly (the docstring's
`harmonic_mean([40, 60], weights=[5, 30]) == 56`), the length check first, a negative weight refused,
and all weights zero refused with 'Weighted sum must be positive'. -/
def HarmonicWeighted : Prop :=
  ∀ (qs ws : List Rat), qs ≠ [] → (∀ q ∈ qs, 0 < q) →
    (ws.length ≠ qs.length → harmonicMean (fracs qs) (some (fracs ws)) =
      .error (.named "StatisticsError" "Number of weights does not match data size")) ∧
    (ws.length = qs.length → (∀ a ∈ ws, 0 ≤ a) → (∃ a ∈ ws, a ≠ 0) →
      harmonicMean (fracs qs) (some (fracs ws)) =
        .ok (Val.frac (sumQ ws / sumQ ((ws.zip qs).map (fun p => p.1 / p.2)))).toN) ∧
    (ws.length = qs.length → (∀ a ∈ ws, a = 0) →
      harmonicMean (fracs qs) (some (fracs ws)) =
        .error (.named "StatisticsError" "Weighted sum must be positive"))

theorem harmonicMean_some (data : List PyN) (w : List PyN) (h : data ≠ []) :
    harmonicMean data (some w) = hmGeneral data (some w) := by
  cases data with
  | nil => exact absurd rfl h
  | cons a rest =>
    have : ¬ ((a :: rest).length < 1) := by simp
    unfold harmonicMean
    rw [if_neg this]
    cases rest <;> rfl

theorem weights_fold (ws : List Rat) (h : ∀ a ∈ ws, 0 ≤ a) (st : SumSt) :
    (fracs ws).foldlM (fun st x => do
        if ← vltPy x.v (.int 0) then throw (statErr hmErrmsg)
        sumStep st x) st = (fracs ws).foldlM sumStep st := by
  induction ws generalizing st with
  | nil => rfl
  | cons a as ih =>
    have ha : ¬ a < 0 := by have := h a (by simp); grind
    have hr : ∀ b ∈ as, 0 ≤ b := fun b hb => h b (by simp [hb])
    have e : (do
        if ← vltPy (Val.frac a).toN.v (.int 0) then throw (statErr hmErrmsg)
        sumStep st (Val.frac a).toN : Py SumSt) = sumStep st (Val.frac a).toN := by
      simp [Val.toN, vltPy_frac, ha]
    rw [fracs, List.map_cons, List.foldlM_cons, List.foldlM_cons]
    rw [e]
    cases sumStep st (Val.frac a).toN with
    | error e => rfl
    | ok st' => exact ih hr st'

theorem sumQ_nonneg' (l : List Rat) (h : ∀ q ∈ l, 0 ≤ q) : 0 ≤ sumQ l := by
  induction l with
  | nil => exact Rat.le_refl
  | cons a as ih =>
    rw [sumQ_cons]
    have := h a (by simp)
    have := ih (fun q hq => h q (by simp [hq]))
    grind

theorem sumQ_pos' (l : List Rat) (h : ∀ q ∈ l, 0 ≤ q) (hp : ∃ q ∈ l, 0 < q) : 0 < sumQ l := by
  induction l with
  | nil => obtain ⟨q, hq, -⟩ := hp; simp at hq
  | cons a as ih =>
    rw [sumQ_cons]
    have ha := h a (by simp)
    have hr : ∀ q ∈ as, 0 ≤ q := fun q hq => h q (by simp [hq])
    obtain ⟨q, hq, hq0⟩ := hp
    rcases List.mem_cons.mp hq with rfl | hq'
    · have := sumQ_nonneg' as hr; grind
    · have := ih hr ⟨q, hq', hq0⟩; grind

theorem sumQ_zero (l : List Rat) (h : ∀ q ∈ l, q = 0) : sumQ l = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih => rw [sumQ_cons, h a (by simp), ih (fun q hq => h q (by simp [hq]))]; exact Rat.add_zero 0

/-- `sum(...)` of exact terms through `sumFinish`: the exact sum, typed by the coercion of the types. -/
theorem sumFinish_exact (l : List PyN) (hd : ∀ x ∈ l, IsExact x.v) (hne : l ≠ []) :
    (l.foldlM sumStep {} >>= sumFinish id) =
      (fun T => (T, Val.frac (sumQ (l.map (fun x => exactQ x.v))), l.length)) <$> reduceCoerce (typesOf [] l) := by
  have := sumOf_exact l hd hne id
  simpa [sumOf] using this

theorem hw_core (qs ws : List Rat) (hne : qs ≠ []) (hpos : ∀ q ∈ qs, 0 < q) (hl : ws.length = qs.length)
    (hnn : ∀ a ∈ ws, 0 ≤ a) :
    ((∃ a ∈ ws, a ≠ 0) → hmGeneral (fracs qs) (some (fracs ws)) =
        .ok (Val.frac (sumQ ws / sumQ ((ws.zip qs).map (fun p => p.1 / p.2)))).toN) ∧
    ((∀ a ∈ ws, a = 0) → hmGeneral (fracs qs) (some (fracs ws)) =
        .error (.named "StatisticsError" "Weighted sum must be positive")) := by
  have hwne : ws ≠ [] := by intro h; subst h; simp at hl; exact hne (List.length_eq_zero_iff.mp hl.symm)
  have hlen : ((fracs ws).length != (fracs qs).length) = false := by simp [fracs, hl]
  -- the weights: their exact sum, typed Fraction
  have hW := sumFinish_exact (fracs ws) (fracs_props ws).1 (by simpa [fracs] using hwne)
  rw [(fracs_props ws).2.2, typesOf_const _ _ (fracs_props ws).2.1 (by simpa [fracs] using hwne), coerce1] at hW
  obtain ⟨PW, hPW, -⟩ := sum_fold (fracs ws) (fracs_props ws).1 {} rfl (by simp)
  rw [hPW, ok_bind'] at hW
  -- the terms
  let terms := (ws.zip qs).map (fun p => hmTerm p.1 p.2)
  have htex : ∀ x ∈ terms, IsExact x.v := by
    intro x hx; simp only [terms, List.mem_map] at hx; obtain ⟨p, -, rfl⟩ := hx; exact (hmTerm_exact _ _).1
  have htne : terms ≠ [] := by
    cases ws with
    | nil => exact absurd rfl hwne
    | cons a as => cases qs with
      | nil => exact absurd rfl hne
      | cons q qs => simp [terms]
  have hsumq : sumQ (terms.map (fun x => exactQ x.v)) = sumQ ((ws.zip qs).map (fun p => p.1 / p.2)) := by
    simp only [terms, List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _; exact (hmTerm_exact _ _).2.1
  have hT := sumFinish_exact terms htex htne
  rw [hsumq] at hT
  obtain ⟨PT, hPT, -⟩ := sum_fold terms htex {} rfl (by simp)
  rw [hPT, ok_bind'] at hT
  have hcls : ∀ x ∈ terms, x.cls = clsInt ∨ x.cls = clsFraction := by
    intro x hx; simp only [terms, List.mem_map] at hx; obtain ⟨p, -, rfl⟩ := hx; exact (hmTerm_exact _ _).2.2.1
  have hS := hm_fold_w hmErrmsg ws qs {} hpos
  have hsumEq : hmSum ((fracs ws).map (·.v)) ((fracs qs).map (·.v)) hmErrmsg =
      (terms.foldlM sumStep {} >>= sumFinish id) := by
    rw [hmSum_eq, fracs_vals, fracs_vals, hS]
  have hpos2 : ∀ p ∈ ws.zip qs, 0 ≤ p.1 / p.2 := by
    intro p hp
    have h1 := hnn p.1 (List.of_mem_zip hp).1
    have h2 := hpos p.2 (List.of_mem_zip hp).2
    exact le_div_of_mul_le h2 (by rw [Rat.zero_mul]; exact h1)
  refine ⟨fun hnz => ?_, fun hz => ?_⟩
  · -- some weight is non-zero: the total is positive and typed Fraction
    obtain ⟨a, ha, ha0⟩ := hnz
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hiq : i < qs.length := by omega
    have hmem : (ws[i], qs[i]) ∈ ws.zip qs := by
      have : (ws.zip qs)[i]'(by simp; omega) = (ws[i], qs[i]) := by simp
      rw [← this]; exact List.getElem_mem _
    have hfr : clsFraction ∈ typesOf [] terms := by
      apply ((typesOf_hm terms hcls [] (by simp [hmTypes])).2)
      right
      exact ⟨hmTerm ws[i] qs[i], List.mem_map.mpr ⟨_, hmem, rfl⟩, (hmTerm_exact _ _).2.2.2 ha0⟩
    have hred := reduce_hm _ (typesOf_hm terms hcls [] (by simp [hmTypes])).1 hfr
    rw [hred] at hT
    have htot : 0 < sumQ ((ws.zip qs).map (fun p => p.1 / p.2)) := by
      apply sumQ_pos'
      · intro q hq; simp only [List.mem_map] at hq; obtain ⟨p, hp, rfl⟩ := hq; exact hpos2 p hp
      · refine ⟨ws[i] / qs[i], List.mem_map.mpr ⟨_, hmem, rfl⟩, ?_⟩
        have h1 : 0 < ws[i] := by have := hnn _ ha; grind
        rw [Rat.div_def]
        exact Rat.mul_pos h1 (Rat.inv_pos.mpr (hpos _ (List.getElem_mem _)))
    generalize sumQ ((ws.zip qs).map (fun p => p.1 / p.2)) = t at hT htot
    have hd : vdiv (.frac (sumQ ws)) (.frac t) = .ok (.frac (sumQ ws / t)) := by
      simp only [vdiv, arith, divOp]; rw [if_neg (by grind)]
    simp only [hmGeneral, hlen, Bool.false_eq_true, ite_false, weights_fold ws hnn, hPW, ok_bind', hW,
      Functor.map, Except.map, pure, Except.pure]
    rw [hsumEq, hPT, ok_bind', hT]
    simp only [Functor.map, Except.map, ok_bind', vlePy_frac_pos t htot, Bool.false_eq_true, ite_false, hd,
      pure, Except.pure]
    rfl
  · -- every weight is zero: the total is 0
    have hz2 : sumQ ((ws.zip qs).map (fun p => p.1 / p.2)) = 0 := by
      apply sumQ_zero
      intro q hq; simp only [List.mem_map] at hq; obtain ⟨p, hp, rfl⟩ := hq
      rw [hz p.1 (List.of_mem_zip hp).1]; simp [Rat.div_def]
    rw [hz2] at hT
    have hv0 : vlePy (.frac 0) (.int 0) = .ok true := by decide
    simp only [hmGeneral, hlen, Bool.false_eq_true, ite_false, weights_fold ws hnn, hPW, ok_bind', hW,
      Functor.map, Except.map, pure, Except.pure]
    rw [hsumEq, hPT, ok_bind', hT]
    have hok : ∃ T, reduceCoerce (typesOf [] terms) = .ok T := by
      have hm := (typesOf_hm terms hcls [] (by simp [hmTypes])).1
      simp only [hmTypes, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h <;> rw [h] <;> exact ⟨_, rfl⟩
    obtain ⟨T, hTc⟩ := hok
    rw [hTc]
    simp [Functor.map, Except.map, hv0, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, statErr]

theorem harmonicWeighted_proven : HarmonicWeighted := by
  intro qs ws hne hpos
  rw [harmonicMean_some _ _ (by simpa [fracs] using hne)]
  have hlen : (fracs ws).length = ws.length := by simp [fracs]
  have hlq : (fracs qs).length = qs.length := by simp [fracs]
  refine ⟨?_, ?_, ?_⟩
  · intro hl
    have : ((fracs ws).length != (fracs qs).length) = true := by simp [hlen, hlq, hl]
    simp only [hmGeneral, this, ite_true]; rfl
  · intro hl hnn hnz
    exact (hw_core qs ws hne hpos hl hnn).1 hnz
  · intro hl hz
    have hnn : ∀ a ∈ ws, 0 ≤ a := fun a ha => by rw [hz a ha]; exact Rat.le_refl
    exact (hw_core qs ws hne hpos hl hnn).2 hz

/-! ## `_fail_neg` as the generator it is -/

/-- `_fail_neg(values, errmsg)`, statistics.py:1644-1649, as a generator: the values it yields, in
order, and how it ends: `none` when the values run out, `some e` when `x < 0` is true for the next value
(`e` is `StatisticsError(errmsg)`) or when the comparison itself raises `e`. Each value is yielded only
after it has been checked, and nothing after the first refused one is looked at. -/
def failNegGen (errmsg : String) : List Val → List Val × Option PyExc
  | [] => ([], none)
  | x :: xs =>
    match vltPy x (.int 0) with
    | .error e => ([], some e)
    | .ok true => ([], some (statErr errmsg))
    | .ok false => let r := failNegGen errmsg xs; (x :: r.1, r.2)

/-- The generator yields every value before the first negative one and then raises, or yields them
all; a comparison that raises ends it with that exception; consuming it to the end (`failNeg`,
`list(_fail_neg(...))`) gives the values or the first exception. -/
def FailNegGen : Prop :=
  ∀ (errmsg : String) (pre rest : List Val) (x : Val),
    (∀ y ∈ pre, vltPy y (.int 0) = .ok false) →
    (failNegGen errmsg pre = (pre, none)) ∧
    (vltPy x (.int 0) = .ok true → failNegGen errmsg (pre ++ x :: rest) = (pre, some (statErr errmsg))) ∧
    (∀ e, vltPy x (.int 0) = .error e → failNegGen errmsg (pre ++ x :: rest) = (pre, some e)) ∧
    (∀ vs, failNeg vs errmsg = match failNegGen errmsg vs with
      | (ys, none) => .ok ys
      | (_, some e) => .error e)

theorem failNeg_consume (errmsg : String) (vs : List Val) :
    failNeg vs errmsg = match failNegGen errmsg vs with
      | (ys, none) => .ok ys
      | (_, some e) => .error e := by
  induction vs with
  | nil => rfl
  | cons x xs ih =>
    simp only [failNeg, List.mapM_cons, failNegGen] at ih ⊢
    cases h : vltPy x (.int 0) with
    | error e => simp [bind, Except.bind]
    | ok b =>
      cases b with
      | true => simp [bind, Except.bind]
      | false =>
        simp only [ok_bind', Bool.false_eq_true, ite_false]
        rw [ih]
        cases failNegGen errmsg xs with
        | mk ys f => cases f <;> rfl

theorem failNegGen_proven : FailNegGen := by
  intro errmsg pre rest x hpre
  have key : ∀ (tail : List Val), failNegGen errmsg (pre ++ tail) =
      (pre ++ (failNegGen errmsg tail).1, (failNegGen errmsg tail).2) := by
    intro tail
    induction pre with
    | nil => rfl
    | cons y ys ih =>
      have hy := hpre y (by simp)
      simp only [List.cons_append, failNegGen, hy]
      rw [ih (fun z hz => hpre z (by simp [hz]))]
  refine ⟨?_, fun h => ?_, fun e h => ?_, failNeg_consume errmsg⟩
  · have := key []; simpa [failNegGen] using this
  · rw [key]; simp [failNegGen, h]
  · rw [key]; simp [failNegGen, h]

/-! ## `multimode`: first-occurrence order, no repeats -/

section MM

variable {α : Type} (eq : α → α → Bool)

/-- The items of `D` at their first occurrence, in order (a later item equal to an earlier one is
left out). -/
def firstOcc (D : List α) : List α :=
  D.foldl (fun acc x => if acc.any (fun k => eq k x) then acc else acc ++ [x]) []

theorem keys_fold (D : List α) : ∀ (c : List (α × Nat)) (acc : List α), c.map Prod.fst = acc →
    (D.foldl (counterAdd eq) c).map Prod.fst =
      D.foldl (fun acc x => if acc.any (fun k => eq k x) then acc else acc ++ [x]) acc := by
  induction D with
  | nil => intro c acc h; exact h
  | cons x xs ih =>
    intro c acc h
    simp only [List.foldl_cons]
    apply ih
    rw [keys_add, ← h, List.any_map]
    rfl

/-- `multimode`, statistics.py:498-516 ("in the order they were first encountered in the data"):
its result is a sublist of the first occurrences of the data, in that order, with no two items
equal. Together with `ModeSpec` (exactly the classes of maximal count, each listed), this is the
docstring's list. -/
def MultimodeOrder : Prop :=
  ∀ (α : Type) (eq : α → α → Bool), (∀ a, eq a a = true) → (∀ a b, eq a b = eq b a) →
    (∀ a b c, eq a b = true → eq b c = true → eq a c = true) →
    ∀ data : List α, (multimode eq data).Sublist (firstOcc eq data) ∧
      (multimode eq data).Pairwise (fun a b => eq a b = false)

end MM

theorem multimodeOrder_proven : MultimodeOrder := by
  intro α eq hrefl hsymm htrans data
  have hk : (counterOf eq data).map Prod.fst = firstOcc eq data := keys_fold eq data [] [] rfl
  have hinv := counter_inv eq hrefl hsymm htrans data
  have hsub : ∀ (P : α × Nat → Bool),
      List.Sublist (((counterOf eq data).filter P).map Prod.fst) ((counterOf eq data).map Prod.fst) :=
    fun P => (List.filter_sublist).map _
  unfold multimode
  cases hc : counterOf eq data with
  | nil => simp
  | cons p ps =>
    simp only
    rw [hc] at hk hsub hinv
    refine ⟨hk ▸ hsub _, ?_⟩
    exact hinv.distinct.sublist (hsub _)

/-! ## `harmonic_mean` refusals -/

theorem weights_neg (ws : List Rat) (h : ∃ a ∈ ws, a < 0) (st : SumSt) :
    (fracs ws).foldlM (fun st x => do
        if ← vltPy x.v (.int 0) then throw (statErr hmErrmsg)
        sumStep st x) st = .error (statErr hmErrmsg) := by
  induction ws generalizing st with
  | nil => obtain ⟨a, ha, -⟩ := h; simp at ha
  | cons a as ih =>
    rw [fracs, List.map_cons, List.foldlM_cons]
    by_cases ha : a < 0
    · simp [Val.toN, vltPy_frac, ha, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw, bind, Except.bind]
    · obtain ⟨b, hb, hb0⟩ := h
      have hb' : b ∈ as := by
        rcases List.mem_cons.mp hb with rfl | h
        · exact absurd hb0 ha
        · exact h
      have e : (do
          if ← vltPy (Val.frac a).toN.v (.int 0) then throw (statErr hmErrmsg)
          sumStep st (Val.frac a).toN : Py SumSt) = sumStep st (Val.frac a).toN := by
        simp [Val.toN, vltPy_frac, ha]
      rw [e]
      obtain ⟨st', hs⟩ := sumStep_exact_ok st (Val.frac a).toN trivial
      rw [bind_ok hs]
      exact ih ⟨b, hb', hb0⟩ st'

/-- `harmonic_mean`'s refusals, statistics.py:297-314: a single value that is not a number
(`isinstance(x, (numbers.Real, Decimal))` fails: a str, `None`, or another object) raises
`TypeError('unsupported type')`, and a single negative number (int, Fraction, float or Decimal)
raises `StatisticsError(errmsg)` (:300-301); with weights of the right length, a negative weight is refused by
`_fail_neg(weights, errmsg)` with `StatisticsError('harmonic mean does not support negative values')`,
before the data is read. -/
def HarmonicRefusals : Prop :=
  (∀ (c : Cls) (v : Val), (v = .none ∨ (∃ s, v = .str s) ∨ (∃ t, v = .other t)) →
    harmonicMean [⟨c, v⟩] none = .error (.typeError "unsupported type")) ∧
  (∀ (data : List PyN) (ws : List Rat), data ≠ [] → ws.length = data.length → (∃ a ∈ ws, a < 0) →
    harmonicMean data (some (fracs ws)) =
      .error (.named "StatisticsError" "harmonic mean does not support negative values")) ∧
  (∀ (c : Cls) (q : Rat), q < 0 →
    (∀ v ∈ [Val.frac q, Val.flt (.fin q), Val.dec (.fin q)],
      harmonicMean [⟨c, v⟩] none =
        .error (.named "StatisticsError" "harmonic mean does not support negative values")) ∧
    (∀ i : Int, i < 0 → harmonicMean [⟨c, .int i⟩] none =
        .error (.named "StatisticsError" "harmonic mean does not support negative values")))

theorem harmonicRefusals_proven : HarmonicRefusals := by
  refine ⟨?_, ?_, ?_⟩
  · intro c v hv
    rcases hv with rfl | ⟨s, rfl⟩ | ⟨t, rfl⟩ <;> rfl
  · intro data ws hne hl hneg
    rw [harmonicMean_some _ _ hne]
    have hlen : ((fracs ws).length != data.length) = false := by simp [fracs, hl]
    simp only [hmGeneral, hlen, Bool.false_eq_true, ite_false, weights_neg ws hneg {}]
    rfl
  · intro c q hq
    have h0 : ((0 : Int) : Rat) = 0 := rfl
    refine ⟨?_, ?_⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl <;>
        simp [harmonicMean, vltPy, vlt, Val.ext, Ext.lt, Val.ordered, h0, hq, throw, throwThe,
          MonadExcept.throw, MonadExceptOf.throw, statErr, hmErrmsg, bind, Except.bind]
    · intro i hi
      have hi' : (i : Rat) < 0 := by
        have := Rat.intCast_lt_intCast.mpr hi
        simpa using this
      simp [harmonicMean, vltPy, vlt, Val.ext, Ext.lt, Val.ordered, hi', throw, throwThe,
        MonadExcept.throw, MonadExceptOf.throw, statErr, hmErrmsg, bind, Except.bind]

/-! ## The pickling state -/

/-- `__getstate__` and `__setstate__`, statistics.py:1445-1449, the pair `pickle` and `copy` use: the
state is the tuple of the two slots, and setting it back restores the slots exactly (so `copy.copy(X)`
and a pickle round trip give an equal instance), for any slot contents, including the floats
`__init__` stores; a state of two items is stored unconverted (`(1, -2)` keeps an int and a negative
`sigma`); a state of any other length raises the unpacking `ValueError` and stores nothing. -/
def StateRoundTrip : Prop :=
  (∀ X : NDSlots, NDSlots.setstate X.getstate = .ok X) ∧
  (∀ X : ND, NDSlots.setstate X.slots.getstate = .ok X.slots) ∧
  (∀ a b : Val, NDSlots.setstate [a, b] = .ok ⟨a, b⟩) ∧
  (∀ l : List Val, l.length < 2 → NDSlots.setstate l =
    .error (.valueError s!"not enough values to unpack (expected 2, got {l.length})")) ∧
  (∀ l : List Val, 2 < l.length → NDSlots.setstate l =
    .error (.valueError s!"too many values to unpack (expected 2, got {l.length})"))

theorem stateRoundTrip_proven : StateRoundTrip := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro l h
    match l, h with
    | [], _ => rfl
    | [a], _ => rfl
  · intro l h
    match l, h with
    | a :: b :: c :: rest, _ =>
      have : ¬ ((a :: b :: c :: rest).length < 2) := by simp
      simp only [NDSlots.setstate, this, ite_false]

end PyLean.CoreLibs.CalStat
