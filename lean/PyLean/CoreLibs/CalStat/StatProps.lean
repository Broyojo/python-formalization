import PyLean.CoreLibs.CalStat.StatLemmas
import PyLean.MathInt.Isqrt

/-! Properties of the `statistics` mirror: exact results on `int`, `Fraction` and finite `float`
data, for `_sum`, `_ss`, `_exact_ratio`, `_coerce`, `_convert`, `mean`, `variance`, `pvariance`,
`stdev`, `pstdev`, `_mean_stdev`, `_integer_sqrt_of_frac_rto`. -/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- A list of `Fraction`s. -/
def fracs (qs : List Rat) : List PyN := qs.map (fun q => (Val.frac q).toN)
/-- A list of `int`s. -/
def ints (xs : List Int) : List PyN := xs.map (fun i => (Val.int i).toN)
/-- A list of `float`s. -/
def floats (xs : List Flt) : List PyN := xs.map (fun x => (Val.flt x).toN)

theorem typesOf_const (c : Cls) (data : List PyN) (h : ∀ x ∈ data, x.cls = c) (hne : data ≠ []) :
    typesOf [] data = [c] := by
  have key : ∀ (l : List PyN), (∀ x ∈ l, x.cls = c) → typesOf [c] l = [c] := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a as ih =>
      intro hl
      have ha := hl a (by simp)
      have : addType [c] a.cls = [c] := by
        rw [ha]
        simp [addType, Cls.same]
      simp only [typesOf, List.foldl_cons, this]
      exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
  cases data with
  | nil => exact absurd rfl hne
  | cons a as =>
    have ha := h a (by simp)
    have : addType [] a.cls = [c] := by rw [ha]; rfl
    simp only [typesOf, List.foldl_cons, this]
    exact key as (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem fracs_props (qs : List Rat) :
    (∀ x ∈ fracs qs, IsExact x.v) ∧ (∀ x ∈ fracs qs, x.cls = clsFraction) ∧
      (fracs qs).map (fun x => exactQ x.v) = qs := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [fracs, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    trivial
  · intro x hx
    simp only [fracs, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    rfl
  · simp [fracs, List.map_map, Function.comp_def, Val.toN, exactQ]

theorem ints_props (xs : List Int) :
    (∀ x ∈ ints xs, IsExact x.v) ∧ (∀ x ∈ ints xs, x.cls = clsInt) ∧
      (ints xs).map (fun x => exactQ x.v) = xs.map (fun (i : Int) => (i : Rat)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [ints, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    trivial
  · intro x hx
    simp only [ints, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    rfl
  · simp [ints, List.map_map, Function.comp_def, Val.toN, exactQ]

theorem floats_props (xs : List Flt) (hf : ∀ x ∈ xs, x.isFinite = true) :
    (∀ x ∈ floats xs, IsExact x.v) ∧ (∀ x ∈ floats xs, x.cls = clsFloat) ∧
      (floats xs).map (fun x => exactQ x.v) = xs.map Flt.toRat := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    simp only [floats, List.mem_map] at hx
    obtain ⟨q, hq, rfl⟩ := hx
    have := hf q hq
    cases q <;> first | trivial | (simp [Flt.isFinite] at this)
  · intro x hx
    simp only [floats, List.mem_map] at hx
    obtain ⟨q, _, rfl⟩ := hx
    rfl
  · simp only [floats, List.map_map]
    apply List.map_congr_left
    intro x hx
    have := hf x hx
    cases x <;> first | rfl | (simp [Flt.isFinite] at this)

theorem length_ne {α : Type} (l : List α) (h : l ≠ []) : 0 < l.length :=
  List.length_pos_iff.mpr h

theorem coerce1 : reduceCoerce [clsFraction] = .ok clsFraction := by decide
theorem coerce2 : reduceCoerce [clsInt] = .ok clsInt := by decide
theorem coerce3 : reduceCoerce [clsFloat] = .ok clsFloat := by decide

theorem sum_fracs (qs : List Rat) (hne : qs ≠ []) :
    sumOf (fracs qs) id = .ok (clsFraction, .frac (sumQ qs), qs.length) := by
  obtain ⟨h1, h2, h3⟩ := fracs_props qs
  have hf : fracs qs ≠ [] := by simpa [fracs] using hne
  rw [sumOf_exact _ h1 hf, h3, typesOf_const _ _ h2 hf]
  simp only [id, coerce1]
  simp [fracs]
  rfl

theorem sum_ints (xs : List Int) (hne : xs ≠ []) :
    sumOf (ints xs) id = .ok (clsInt, .frac (sumQ (xs.map (fun (i : Int) => (i : Rat)))), xs.length) := by
  obtain ⟨h1, h2, h3⟩ := ints_props xs
  have hf : ints xs ≠ [] := by simpa [ints] using hne
  rw [sumOf_exact _ h1 hf, h3, typesOf_const _ _ h2 hf]
  simp only [id, coerce2]
  simp [ints]
  rfl

theorem sum_floats (xs : List Flt) (hne : xs ≠ []) (hf : ∀ x ∈ xs, x.isFinite = true) :
    sumOf (floats xs) id = .ok (clsFloat, .frac (sumQ (xs.map Flt.toRat)), xs.length) := by
  obtain ⟨h1, h2, h3⟩ := floats_props xs hf
  have hf' : floats xs ≠ [] := by simpa [floats] using hne
  rw [sumOf_exact _ h1 hf', h3, typesOf_const _ _ h2 hf']
  simp only [id, coerce3]
  simp [floats]
  rfl

theorem vdiv_frac_int (S : Rat) (n : Nat) (hn : n ≠ 0) :
    vdiv (.frac S) (.int n) = .ok (.frac (S / (n : Rat))) := by
  have : (((n : Nat) : Int) : Rat) ≠ 0 := by
    intro h
    apply hn
    have : (n : Rat) = 0 := h
    simpa using this
  simp only [vdiv, arith, divOp]
  rw [if_neg this]
  rfl

/-- `_sum` is exact for any mix of finite values of any denominators, in every type: the total
is the rational sum and the count the length ("high-precision sum ... as a fraction", the docstring;
`Some sources of round-off error will be avoided`). -/
def SumExact : Prop :=
  ∀ (data : List PyN) (order : List Cls → List Cls), (∀ x ∈ data, IsExact x.v) → data ≠ [] →
    ∀ T, reduceCoerce (order (typesOf [] data)) = .ok T →
      sumOf data order = .ok (T, .frac (sumQ (data.map (fun x => exactQ x.v))), data.length)

theorem sumExact_proven : SumExact := by
  intro data order h1 h2 T hT
  rw [sumOf_exact data h1 h2, hT]
  rfl

/-- `mean` of `Fraction`s is the exact mean, as `Fraction`; `mean([])` raises. -/
def MeanFractions : Prop :=
  (∀ qs : List Rat, qs ≠ [] →
    mean (fracs qs) = .ok (Val.frac (sumQ qs / (qs.length : Rat))).toN) ∧
  mean [] = .error (.named "StatisticsError" "mean requires at least one data point")

theorem meanFractions_proven : MeanFractions := by
  refine ⟨?_, by decide⟩
  intro qs hne
  have hn := length_ne qs hne
  simp only [mean, bind, Except.bind, sum_fracs qs hne]
  rw [if_neg (by omega)]
  simp only [vdiv_frac_int _ _ (by omega : qs.length ≠ 0)]
  rfl

theorem not_same_frac_int (q : Rat) : (Val.frac q).cls.same clsInt = false := by
  show clsFraction.same clsInt = false
  decide

theorem convert_int_den1 (q : Rat) (h : q.den = 1) :
    convert (.frac q) clsInt = .ok (Val.int q.num).toN := by
  unfold convert
  rw [not_same_frac_int]
  simp only [Bool.false_eq_true, if_false]
  have e : (isSubclass clsInt clsInt && q.den != 1) = false := by simp [h]
  rw [e]
  rfl

theorem convert_int_frac (q : Rat) (h : q.den ≠ 1) :
    convert (.frac q) clsInt = (fun r => (Val.flt r).toN) <$> ratToFlt q := by
  unfold convert
  rw [not_same_frac_int]
  simp only [Bool.false_eq_true, if_false]
  have e : (isSubclass clsInt clsInt && q.den != 1) = true := by
    simp only [Bool.and_eq_true, bne_iff_ne]
    exact ⟨by decide, h⟩
  rw [e]
  show construct clsFloat (.frac q) = _
  have e1 : isSubclass clsFloat clsInt = false := by decide
  have e2 : isSubclass clsFloat clsFloat = true := by decide
  simp only [construct, e1, e2, Bool.false_eq_true, if_false, if_true, bind, Except.bind, toFloat,
    pure, Except.pure]
  cases ratToFlt q <;> rfl

/-- `mean` of `int`s: an `int` when the exact mean is whole, otherwise the correctly rounded
`float` (or `OverflowError`, the source's FIXME at statistics.py:1635). -/
def MeanInts : Prop :=
  ∀ xs : List Int, xs ≠ [] →
    let m : Rat := sumQ (xs.map (fun (i : Int) => (i : Rat))) / (xs.length : Rat)
    mean (ints xs) =
      if m.den = 1 then .ok (Val.int m.num).toN else (fun r => (Val.flt r).toN) <$> ratToFlt m

theorem meanInts_proven : MeanInts := by
  intro xs hne m
  have hn := length_ne xs hne
  simp only [mean, bind, Except.bind, sum_ints xs hne]
  rw [if_neg (by omega)]
  simp only [vdiv_frac_int _ _ (by omega : xs.length ≠ 0)]
  by_cases hd : m.den = 1
  · rw [if_pos hd]
    exact convert_int_den1 m hd
  · rw [if_neg hd]
    exact convert_int_frac m hd

/-- `mean` of finite floats is the exact mean correctly rounded: no accumulation error at all. -/
def MeanFloats : Prop :=
  ∀ xs : List Flt, xs ≠ [] → (∀ x ∈ xs, x.isFinite = true) →
    mean (floats xs) = (fun r => (Val.flt r).toN) <$>
      ratToFlt (sumQ (xs.map Flt.toRat) / (xs.length : Rat))

theorem meanFloats_proven : MeanFloats := by
  intro xs hne hf
  have hn := length_ne xs hne
  simp only [mean, bind, Except.bind, sum_floats xs hne hf]
  rw [if_neg (by omega)]
  simp only [vdiv_frac_int _ _ (by omega : xs.length ≠ 0)]
  have e0 : ∀ q : Rat, (Val.frac q).cls.same clsFloat = false := fun _ => by
    show clsFraction.same clsFloat = false
    decide
  have e1 : isSubclass clsFloat clsInt = false := by decide
  have e2 : isSubclass clsFloat clsFloat = true := by decide
  simp only [convert, e0, e1, Bool.false_eq_true, if_false, Bool.false_and, construct, e2, if_true,
    bind, Except.bind, toFloat, pure, Except.pure]
  cases ratToFlt (sumQ (xs.map Flt.toRat) / (xs.length : Rat)) <;> rfl

/-! ## `_ss`, `variance`, `pvariance` -/

/-- `Σ (x - c)**2`. -/
def sumDev (qs : List Rat) (c : Rat) : Rat := sumQ (qs.map (fun x => (x - c) * (x - c)))

/-- The mean of a list of rationals. -/
def meanQ (qs : List Rat) : Rat := sumQ qs / (qs.length : Rat)

theorem ss_fracs (qs : List Rat) (hne : qs ≠ []) :
    ssOf (fracs qs) none id =
      .ok (clsFraction, .frac (sumDev qs (meanQ qs)), .frac (meanQ qs), qs.length) := by
  obtain ⟨h1, h2, h3⟩ := fracs_props qs
  have hf : fracs qs ≠ [] := by simpa [fracs] using hne
  obtain ⟨P, Q, e1, e2, e3⟩ := ss_fold (fracs qs) h1 {} rfl (by simp) (by simp)
  have hmapsq : (fracs qs).map (fun x => exactQ x.v * exactQ x.v) = qs.map (fun x => x * x) := by
    simp [fracs, List.map_map, Function.comp_def, Val.toN, exactQ]
  rw [hmapsq] at e3
  rw [h3] at e2
  have hP : sumPartials P = sumQ qs := by
    rw [e2]; simp only [sumPartials, List.foldr_nil]; grind
  have hQ : sumPartialsSq Q = sumQ (qs.map (fun x => x * x)) := by
    rw [e3]; simp only [sumPartialsSq, List.foldr_nil]; grind
  have hn := length_ne qs hne
  have hlen : (fracs qs).length = qs.length := by simp [fracs]
  have hty : typesOf [] (fracs qs) = [clsFraction] := typesOf_const _ _ h2 hf
  have hf0 : ¬(0 + (fracs qs).length = 0) := by omega
  simp only [ssOf, bind, Except.bind, e1, hP, hQ, hty, hf0, if_false, Nat.zero_add]
  have hform := ss_formula qs hne
  have h0 : ¬ qs.length = 0 := by omega
  simp only [hlen, id, coerce1, pure, Except.pure, h0, if_false]
  unfold sumDev meanQ
  rw [← hform]

theorem ssFoldC (qs : List Rat) (c : Rat) (st : SumSt) :
    (fracs qs).foldlM (fun st x => do
      let d ← vsub x.v (Val.frac c).toN.v
      let e ← vmul d d
      sumStep st e.toN) st =
    (fracs (qs.map (fun x => (x - c) * (x - c)))).foldlM sumStep st := by
  induction qs generalizing st with
  | nil => rfl
  | cons a as ih =>
    simp only [fracs, List.map_cons, List.foldlM_cons]
    have e1 : vsub (Val.frac a).toN.v (Val.frac c).toN.v = .ok (.frac (a - c)) := rfl
    have e2 : vmul (.frac (a - c)) (.frac (a - c)) = .ok (.frac ((a - c) * (a - c))) := rfl
    simp only [bind, Except.bind, e1, e2]
    cases sumStep st (Val.frac ((a - c) * (a - c))).toN with
    | error e => rfl
    | ok st' => exact ih st'

theorem ss_fracs_c (qs : List Rat) (c : Rat) (hne : qs ≠ []) :
    ssOf (fracs qs) (some (Val.frac c).toN) id =
      .ok (clsFraction, .frac (sumDev qs c), .frac c, qs.length) := by
  have hs := sum_fracs (qs.map (fun x => (x - c) * (x - c))) (by simpa using hne)
  have hf := ssFoldC qs c {}
  simp only [ssOf, bind, Except.bind] at hf ⊢
  rw [hf]
  simp only [sumOf, bind, Except.bind] at hs
  cases hfold : (fracs (qs.map (fun x => (x - c) * (x - c)))).foldlM sumStep ({} : SumSt) with
  | error e => rw [hfold] at hs; cases hs
  | ok st =>
    rw [hfold] at hs
    simp only at hs ⊢
    rw [hs]
    simp [sumDev, pure, Except.pure, Val.toN]

/-- `variance` and `pvariance` of `Fraction`s are the exact definitions: the sum of squared
deviations from the mean over `n - 1` and over `n`, as `Fraction`, and they raise for fewer than two
and one points. -/
def VarianceFractions : Prop :=
  ∀ qs : List Rat,
    (2 ≤ qs.length →
      variance (fracs qs) none =
        .ok (Val.frac (sumDev qs (meanQ qs) / ((qs.length - 1 : Nat) : Rat))).toN) ∧
    (1 ≤ qs.length →
      pvariance (fracs qs) none = .ok (Val.frac (sumDev qs (meanQ qs) / (qs.length : Rat))).toN)

theorem vdiv_frac_int' (S : Rat) (n : Nat) (hn : 2 ≤ n) :
    vdiv (.frac S) (.int ((n : Int) - 1)) = .ok (.frac (S / ((n - 1 : Nat) : Rat))) := by
  have e : ((n : Int) - 1) = ((n - 1 : Nat) : Int) := by omega
  rw [e]
  exact vdiv_frac_int S (n - 1) (by omega)

theorem convert_frac (q : Rat) : convert (.frac q) clsFraction = .ok (Val.frac q).toN := rfl

theorem varianceFractions_proven : VarianceFractions := by
  intro qs
  constructor
  · intro h2
    have hne : qs ≠ [] := by
      intro h; simp [h] at h2
    have hss := ss_fracs qs hne
    unfold variance
    simp only [bind, Except.bind]
    rw [hss]
    simp only
    rw [if_neg (by omega), vdiv_frac_int' _ _ h2]
    rfl
  · intro h1
    have hne : qs ≠ [] := by
      intro h; simp [h] at h1
    have hss := ss_fracs qs hne
    unfold pvariance
    simp only [bind, Except.bind]
    rw [hss]
    simp only
    rw [if_neg (by omega), vdiv_frac_int _ _ (by omega)]
    rfl

/-- "If you have already calculated the mean of your data, you can pass it as the optional second
argument": for `Fraction`s, passing the mean gives the same variance. Passing any other
`c` gives the sum of squares about `c`, as the docstring warns. -/
def VarianceWithMean : Prop :=
  ∀ qs : List Rat, 2 ≤ qs.length →
    variance (fracs qs) (some (Val.frac (meanQ qs)).toN) = variance (fracs qs) none ∧
    pvariance (fracs qs) (some (Val.frac (meanQ qs)).toN) = pvariance (fracs qs) none

theorem varianceWithMean_proven : VarianceWithMean := by
  intro qs h2
  have hne : qs ≠ [] := by
    intro h; simp [h] at h2
  have hc := ss_fracs_c qs (meanQ qs) hne
  have hs := ss_fracs qs hne
  constructor
  · unfold variance
    simp only [bind, Except.bind]
    rw [hc, hs]
  · unfold pvariance
    simp only [bind, Except.bind]
    rw [hc, hs]

/-- `stdev` and `pstdev` are "the square root of the sample variance" and of the population variance:
on `Fraction`s they apply `_float_sqrt_of_frac` to the exact variance. `_mean_stdev` agrees with
`mean` and `stdev`: it is the fused single pass. -/
def StdevOfVariance : Prop :=
  ∀ qs : List Rat,
    (2 ≤ qs.length → ∃ v,
      variance (fracs qs) none = .ok (Val.frac v).toN ∧
      stdev (fracs qs) none = .flt <$> floatSqrtOfFrac v.num v.den ∧
      meanStdev (fracs qs) = (do
        let m ← ratToFlt (meanQ qs)
        let s ← floatSqrtOfFrac v.num v.den
        return (m, s))) ∧
    (1 ≤ qs.length → ∃ v,
      pvariance (fracs qs) none = .ok (Val.frac v).toN ∧
      pstdev (fracs qs) none = .flt <$> floatSqrtOfFrac v.num v.den)

theorem isSub_frac_dec : isSubclass clsFraction clsDecimal = false := by decide

theorem stdevOfVariance_proven : StdevOfVariance := by
  intro qs
  constructor
  · intro h2
    have hv := (varianceFractions_proven qs).1 h2
    refine ⟨_, hv, ?_, ?_⟩
    all_goals
      have hne : qs ≠ [] := by
        intro h; simp [h] at h2
      have hss := ss_fracs qs hne
    · unfold stdev
      simp only [bind, Except.bind]
      rw [hss]
      simp only
      rw [if_neg (by omega), vdiv_frac_int' _ _ h2]
      simp only [sqrtTail, isSub_frac_dec, Bool.false_eq_true, if_false]
    · unfold meanStdev
      simp only [bind, Except.bind]
      rw [hss]
      simp only
      rw [if_neg (by omega), vdiv_frac_int' _ _ h2]
      simp only [toFloat, pure, Except.pure]
  · intro h1
    have hv := (varianceFractions_proven qs).2 h1
    refine ⟨_, hv, ?_⟩
    have hne : qs ≠ [] := by
      intro h; simp [h] at h1
    have hss := ss_fracs qs hne
    unfold pstdev
    simp only [bind, Except.bind]
    rw [hss]
    simp only
    rw [if_neg (by omega), vdiv_frac_int _ _ (by omega)]
    simp only [sqrtTail, isSub_frac_dec, Bool.false_eq_true, if_false]

end PyLean.CoreLibs.CalStat
