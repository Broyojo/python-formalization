import PyLean.CoreLibs.CalStat.StatProps3

/-! Properties of `NormalDist`, the kernels, `kde`, `geometric_mean`, `fmean` and the two-input
functions. What libm computes stays abstract: a property that needs a value of a libm function
takes it from `LibmFacts`, the exact values of C99 Annex F. -/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-! ## Comparisons of floats -/

theorem vlt_flt (a b : Flt) : vlt (.flt a) (.flt b) = Flt.lt a b := by
  cases a <;> cases b <;> first
    | rfl
    | (simp [vlt, Val.ext, Ext.lt, Flt.lt, Flt.toRat]; done)
    | (simp [vlt, Val.ext, Ext.lt, Flt.lt, Flt.toRat]; rfl)

theorem vltPy_flt (a b : Flt) : vltPy (.flt a) (.flt b) = .ok (Flt.lt a b) := by
  simp [vltPy, Val.ordered, vlt_flt]

theorem veq_flt (a b : Flt) : veq (.flt a) (.flt b) = Flt.eq a b := by
  cases a <;> cases b <;> first
    | rfl
    | (simp [veq, Val.ext, Flt.eq]; done)
    | (rename_i x y; cases x <;> cases y <;> rfl)

theorem vlePy_flt (a b : Flt) : vlePy (.flt a) (.flt b) = .ok (Flt.le a b) := by
  simp [vlePy, vltPy_flt, veq_flt, Flt.le, bind, Except.bind, pure, Except.pure]

theorem nd_mk (a b : Flt) :
    ND.mk' (.flt a) (.flt b) = if Flt.lt b Flt.pz then .error (statErr "sigma must be non-negative")
      else .ok ⟨a, b⟩ := by
  simp only [ND.mk', bind, Except.bind, vltPy_flt]
  by_cases h : Flt.lt b Flt.pz = true
  · simp only [h, if_true]
    rfl
  · simp only [h, if_false, toFloat, pure, Except.pure]
    rfl

theorem nd_mk_ok {a b : Flt} {Z : ND} (h : ND.mk' (.flt a) (.flt b) = .ok Z) : Z = ⟨a, b⟩ := by
  rw [nd_mk] at h
  split at h
  · cases h
  · cases h; rfl

theorem neg_neg (x : Flt) : Flt.neg (Flt.neg x) = x := by
  cases x <;> simp [Flt.neg]

/-- A `NormalDist` built by the constructor: `sigma` is not negative. -/
def ND.Valid (X : ND) : Prop := Flt.lt X.sigma Flt.pz = false

/-- `NormalDist(mu, sigma)` refuses a negative `sigma`, keeps both otherwise; a constructed
object reports them back through `mean`, `median`, `mode` and `stdev`, and `variance` is
`stdev * stdev`. Pickling state round-trips. -/
def NormalDistInit : Prop :=
  ∀ mu s : Flt,
    (Flt.lt s Flt.pz = true → ND.mk' (.flt mu) (.flt s) =
      .error (.named "StatisticsError" "sigma must be non-negative")) ∧
    (Flt.lt s Flt.pz = false → ∃ X, ND.mk' (.flt mu) (.flt s) = .ok X ∧
      X.meanP = mu ∧ X.medianP = mu ∧ X.modeP = mu ∧ X.stdevP = s ∧ X.variance = Flt.mul s s ∧
      X.setstate X.getstate = X)

theorem normalDistInit_proven : NormalDistInit := by
  intro mu s
  constructor
  · intro h
    rw [nd_mk, h]
    rfl
  · intro h
    refine ⟨⟨mu, s⟩, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [nd_mk, h]
    rfl

/-- The operators with a constant, for a valid `X`: `+` and `-` translate `mu` and keep `sigma`;
`+x` is a copy; `-x` negates `mu` and `-(-x)` is `x`; `c - x` is `-(x - c)`; `*` and `/` scale `mu` by
`c` and `sigma` by `|c|`; dividing by zero raises. -/
def NormalDistArith : Prop :=
  ∀ (X : ND) (c : Flt), X.Valid →
    ND.addConst X (.flt c) = .ok ⟨Flt.add X.mu c, X.sigma⟩ ∧
    ND.subConst X (.flt c) = .ok ⟨Flt.sub X.mu c, X.sigma⟩ ∧
    ND.pos X = .ok X ∧
    ND.neg X = .ok ⟨Flt.neg X.mu, X.sigma⟩ ∧
    (do ND.neg (← ND.neg X)) = .ok X ∧
    ND.rsubConst X (.flt c) = .ok ⟨Flt.neg (Flt.sub X.mu c), X.sigma⟩ ∧
    (∀ Z, ND.mulConst X (.flt c) = .ok Z →
      Z = ⟨Flt.mul X.mu c, Flt.mul X.sigma (Flt.abs c)⟩) ∧
    (∀ Z, ND.divConst X (.flt c) = .ok Z →
      Z = ⟨Flt.div X.mu c, Flt.div X.sigma (Flt.abs c)⟩) ∧
    (∀ b, ND.divConst X (.flt (.zero b)) = .error (.zeroDivisionError "division by zero"))

theorem normalDistArith_proven : NormalDistArith := by
  intro X c hv
  have hs : Flt.lt X.sigma Flt.pz = false := hv
  have add : ∀ a b, vadd (.flt a) (.flt b) = .ok (.flt (Flt.add a b)) := fun _ _ => rfl
  have sub : ∀ a b, vsub (.flt a) (.flt b) = .ok (.flt (Flt.sub a b)) := fun _ _ => rfl
  have hcase : ND.neg X = .ok ⟨Flt.neg X.mu, X.sigma⟩ := by
    simp only [ND.neg, nd_mk, hs, Bool.false_eq_true, if_false]
  refine ⟨?_, ?_, ?_, hcase, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ND.addConst, bind, Except.bind, add, nd_mk, hs, Bool.false_eq_true, if_false]
  · simp only [ND.subConst, bind, Except.bind, sub, nd_mk, hs, Bool.false_eq_true, if_false]
  · simp only [ND.pos, nd_mk, hs, Bool.false_eq_true, if_false]
  · simp only [bind, Except.bind, hcase]
    simp only [ND.neg, nd_mk, hs, Bool.false_eq_true, if_false, neg_neg]
  · simp only [ND.rsubConst, ND.subConst, ND.neg, bind, Except.bind, sub, nd_mk, hs,
      Bool.false_eq_true, if_false]
  · intro Z h
    have m : vmul (.flt X.mu) (.flt c) = .ok (.flt (Flt.mul X.mu c)) := rfl
    simp only [ND.mulConst, bind, Except.bind, m, mathFabs, asDouble, toFloat, pure, Except.pure] at h
    exact nd_mk_ok h
  · intro Z h
    cases hc : c with
    | zero b =>
      subst hc
      have : vdiv (.flt X.mu) (.flt (.zero b)) = .error (.zeroDivisionError "division by zero") := rfl
      simp only [ND.divConst, bind, Except.bind, this] at h
      cases h
    | nan =>
      subst hc
      have m : vdiv (.flt X.mu) (.flt .nan) = .ok (.flt (Flt.div X.mu .nan)) := rfl
      simp only [ND.divConst, bind, Except.bind, m, mathFabs, asDouble, toFloat, pure, Except.pure,
        fltDiv] at h
      exact nd_mk_ok h
    | inf n =>
      subst hc
      have m : vdiv (.flt X.mu) (.flt (.inf n)) = .ok (.flt (Flt.div X.mu (.inf n))) := rfl
      simp only [ND.divConst, bind, Except.bind, m, mathFabs, asDouble, toFloat, pure, Except.pure,
        fltDiv, Flt.abs] at h
      exact nd_mk_ok h
    | fin q =>
      subst hc
      have m : vdiv (.flt X.mu) (.flt (.fin q)) = .ok (.flt (Flt.div X.mu (.fin q))) := rfl
      simp only [ND.divConst, bind, Except.bind, m, mathFabs, asDouble, toFloat, pure, Except.pure,
        fltDiv, Flt.abs] at h
      exact nd_mk_ok h
  · intro b
    rfl

/-- `X + Y` and `X - Y`: means add and subtract, and `sigma` is `hypot` of the two in
both cases (the docstrings: "add both the means and the variances"). The means of `X + Y` and `Y + X`
agree exactly. -/
def NormalDistSum : Prop :=
  ∀ X Y Z : ND,
    (ND.add X Y = .ok Z → Z = ⟨Flt.add X.mu Y.mu, hypot X.sigma Y.sigma⟩) ∧
    (ND.sub X Y = .ok Z → Z = ⟨Flt.sub X.mu Y.mu, hypot X.sigma Y.sigma⟩) ∧
    Flt.add X.mu Y.mu = Flt.add Y.mu X.mu

theorem add_comm_flt (a b : Flt) : Flt.add a b = Flt.add b a := by
  cases a <;> cases b <;> first
    | rfl
    | (simp [Flt.add, Bool.and_comm, Rat.add_comm]; done)
    | (rename_i x y; cases x <;> cases y <;> rfl)

theorem normalDistSum_proven : NormalDistSum := by
  intro X Y Z
  exact ⟨fun h => nd_mk_ok h, fun h => nd_mk_ok h, add_comm_flt _ _⟩

theorem hash_eq (a b : Flt) (h : Flt.eq a b = true) : hashFlt a = hashFlt b := by
  cases a <;> cases b <;> first
    | rfl
    | (simp_all [Flt.eq, hashFlt]; done)
    | (simp only [Flt.eq, decide_eq_true_eq] at h
       subst h
       first | rfl | decide)

theorem eq_symm (a b : Flt) : Flt.eq a b = Flt.eq b a := by
  cases a <;> cases b <;> first
    | rfl
    | (simp [Flt.eq, eq_comm]; done)
    | (rename_i x y; cases x <;> cases y <;> rfl)

/-- `__eq__` compares `mu` and `sigma` numerically and is symmetric; equal objects hash equal
(the docstring of `__hash__`), also for `0.0` against `-0.0`. `__repr__` shows both fields. -/
def NormalDistEqHash : Prop :=
  ∀ (X Y : ND) (i j i' j' : Int),
    ND.beq X Y = ND.beq Y X ∧
    (ND.beq X Y = true → ND.hash X i j = ND.hash Y i' j') ∧
    ND.repr "NormalDist" X = "NormalDist(mu=" ++ fltRepr X.mu ++ ", sigma=" ++ fltRepr X.sigma ++ ")" ∧
    ND.repr "NormalDist" ⟨.zero false, .fin 1⟩ = "NormalDist(mu=0.0, sigma=1.0)" ∧
    ND.repr "NormalDist" ⟨.fin (mkRat 3602879701896397 36028797018963968), .fin (mkRat 5 2)⟩ =
      "NormalDist(mu=0.1, sigma=2.5)"

theorem hashObj_eq (a b : Flt) (i j : Int) (h : Flt.eq a b = true) : hashFltObj i a = hashFltObj j b := by
  have := hash_eq a b h
  cases a <;> cases b <;> simp_all [hashFltObj, Flt.eq]

theorem normalDistEqHash_proven : NormalDistEqHash := by
  intro X Y i j i' j'
  refine ⟨?_, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · simp only [ND.beq, eq_symm X.mu Y.mu, eq_symm X.sigma Y.sigma]
  · intro h
    simp only [ND.beq, Bool.and_eq_true] at h
    simp only [ND.hash, hashObj_eq _ _ i i' h.1, hashObj_eq _ _ j j' h.2]
  · rfl

/-! ## Zero `sigma` and the range of `p` -/

/-- With `sigma == 0` the functions the docs call undefined raise `StatisticsError` with their own
message: `pdf`, `cdf`, `zscore` and `overlap`. `p` outside `0 < p < 1` raises in `inv_cdf`. -/
def NormalDistUndefined : Prop :=
  ∀ (L : Libm) (X Y : ND) (b : Bool) (x : Val) (p : Flt),
    X.sigma = .zero b →
    (ND.pdf L X x = .error (.named "StatisticsError" "pdf() not defined when sigma is zero")) ∧
    (ND.cdf L X x = .error (.named "StatisticsError" "cdf() not defined when sigma is zero")) ∧
    (ND.zscore X x = .error (.named "StatisticsError" "zscore() not defined when sigma is zero")) ∧
    (ND.overlap L X Y = .error (.named "StatisticsError" "overlap() not defined when sigma is zero")) ∧
    ((Flt.le p Flt.pz = true ∨ Flt.le Flt.one p = true) →
      ND.invCdf L Y (.flt p) = .error (.named "StatisticsError" "p must be in the range 0.0 < p < 1.0"))

theorem variance_zero (X : ND) (b : Bool) (h : X.sigma = .zero b) : X.variance.truthy = false := by
  simp only [ND.variance, h]
  cases b <;> rfl

theorem normalDistUndefined_proven : NormalDistUndefined := by
  intro L X Y b x p hz
  have hv := variance_zero X b hz
  have hsig : X.sigma.truthy = false := by rw [hz]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [ND.pdf, bind, Except.bind, hsig, Bool.not_false, if_true]
    rfl
  · simp only [ND.cdf, bind, Except.bind, hsig, Bool.not_false, if_true]
    rfl
  · simp only [ND.zscore, bind, Except.bind, hsig, Bool.not_false, if_true]
    rfl
  · simp only [ND.overlap, bind, Except.bind]
    generalize (Flt.lt Y.sigma X.sigma || Flt.eq Y.sigma X.sigma && Flt.lt Y.mu X.mu) = sw
    cases sw
    · simp only [Bool.false_eq_true, if_false, hv, Bool.not_false, Bool.true_or, if_true]
      rfl
    · simp only [if_true, hv, Bool.not_false, Bool.or_true]
      rfl
  · intro hp
    simp only [ND.invCdf, bind, Except.bind, vlePy_flt]
    rcases hp with h | h
    · simp only [h, Bool.true_or, if_true]
      rfl
    · simp only [h, Bool.or_true, if_true]
      rfl

/-- `inv_cdf(0.5)` is `mu`: the median of the distribution, computed through the central branch of
Wichura's algorithm, for all finite `mu` and `sigma`. So `quantiles(2) == [mu]`; `quantiles(n)` gives
`n - 1` values whenever it succeeds, and `samples` gives one value per random draw. -/
def InvCdfCentre : Prop :=
  ∀ (L : Libm) (X : ND) (us : List Flt) (r : List Flt) (n : Int), X.mu.isFinite = true →
      X.sigma.isFinite = true →
    (∃ m, ND.invCdf L X (.flt Flt.half) = .ok m ∧ Flt.eq m X.mu = true) ∧
    (ND.quantiles L X n = .ok r → r.length = (n - 1).toNat) ∧
    (ND.samples L X us = .ok r → r.length = us.length)

theorem invCdfCentre_proven : InvCdfCentre := by
  intro L X us r n hm hs
  have e1 : Flt.le Flt.half Flt.pz = false := by decide +kernel
  have e2 : Flt.le Flt.one Flt.half = false := by decide +kernel
  have e3 : Flt.le (Flt.abs (Flt.sub Flt.half Flt.half)) (Flt.ofRat (dec10 425 3)) = true := by
    decide +kernel
  let q := Flt.sub Flt.half Flt.half
  let r0 := Flt.sub (Flt.ofRat (dec10 180625 6)) (Flt.mul q q)
  have e4 : Flt.eq (horner r0 invDen1) Flt.pz = false := by decide +kernel
  have e5 : Flt.div (Flt.mul (horner r0 invNum1) q) (horner r0 invDen1) = .zero false := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · have hcore : normalDistInvCdf L Flt.half X.mu X.sigma =
        .ok (Flt.add X.mu (Flt.mul (.zero false) X.sigma)) := by
      unfold normalDistInvCdf
      simp only [e1, e2, Bool.false_or, Bool.false_eq_true, if_false, e3, if_true]
      show (if Flt.eq (horner r0 invDen1) Flt.pz = true then _ else _) = _
      rw [e4]
      simp only [Bool.false_eq_true, if_false]
      show Except.ok (Flt.add X.mu (Flt.mul (Flt.div (Flt.mul (horner r0 invNum1) q)
        (horner r0 invDen1)) X.sigma)) = _
      rw [e5]
    refine ⟨Flt.add X.mu (Flt.mul (.zero false) X.sigma), ?_, ?_⟩
    · simp only [ND.invCdf, bind, Except.bind, vlePy_flt, e1, e2, Bool.false_or, Bool.false_eq_true,
        if_false, toFloat]
      exact hcore
    · cases hmu : X.mu <;> cases hsg : X.sigma <;> simp_all [Flt.isFinite, Flt.mul, Flt.add, Flt.eq]
  · intro h
    rw [← rangeI_length 1 n]
    exact mapM_length _ _ _ h
  · intro h
    exact mapM_length _ _ _ h

/-! ## Kernels -/

/-- The exact libm values the kernels meet at `0` and at the ends of the support: C99 Annex F for
`exp`, `cosh`, `sin`, `erfc`, `pow`, and the correctly rounded `atan(1)`. -/
structure LibmFacts (L : Libm) : Prop where
  exp0 : L.exp Flt.pz = Flt.one
  sin0 : L.sin Flt.pz = Flt.pz
  erfc0 : ∀ b, L.erfc (.zero b) = Flt.one
  atan1 : L.atan Flt.one = Flt.div piF (Flt.ofInt 4)
  pow0 : ∀ y, Flt.lt Flt.pz y = true → L.pow Flt.pz y = Flt.pz
  pow1 : ∀ y, L.pow Flt.one y = Flt.one
  powm1 : ∀ k : Int, (k = 3 ∨ k = 5 ∨ k = 7) → L.pow (Flt.neg Flt.one) (Flt.ofInt k) = Flt.neg Flt.one

theorem math1_ok (f : Flt → Flt) (c : Bool) (m : String) (x r : Flt) (h : f x = r)
    (h1 : r.isNan = false) (h2 : r.isInf = false) : math1 f c m x = .ok r := by
  simp [math1, h, h1, h2]

theorem floatPow_zero (L : Libm) (F : LibmFacts L) (y : Flt) (h1 : Flt.eq y Flt.pz = false)
    (h2 : y.isNan = false) (h3 : y.isInf = false) (h4 : Flt.lt y Flt.pz = false)
    (h5 : Flt.lt Flt.pz y = true) : floatPow L Flt.pz y = .ok Flt.pz := by
  have e1 : Flt.pz.isNan = false := rfl
  have e2 : Flt.pz.isInf = false := rfl
  have e3 : Flt.eq Flt.pz Flt.pz = true := rfl
  simp only [floatPow, h1, h2, h3, h4, e1, e2, e3, Bool.false_eq_true, if_false, Bool.false_or,
    if_true, F.pow0 y h5]

theorem floatPow_unit (L : Libm) (x y r : Flt) (h1 : Flt.eq y Flt.pz = false)
    (h2 : y.isNan = false) (h3 : y.isInf = false) (e1 : x.isNan = false) (e2 : x.isInf = false)
    (e3 : Flt.eq x Flt.pz = false) (e4 : Flt.eq (Flt.abs x) Flt.one = true) (hp : L.pow x y = r) :
    floatPow L x y = .ok r := by
  simp only [floatPow, h1, h2, h3, e1, e2, e3, e4, Bool.false_eq_true, if_false, Bool.false_or,
    if_true, hp]

section Pow
variable (L : Libm) (F : LibmFacts L)
include F

theorem z3 : floatPow L Flt.pz (Flt.ofInt 3) = .ok Flt.pz :=
  floatPow_zero L F _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem z5 : floatPow L Flt.pz (Flt.ofInt 5) = .ok Flt.pz :=
  floatPow_zero L F _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
theorem z7 : floatPow L Flt.pz (Flt.ofInt 7) = .ok Flt.pz :=
  floatPow_zero L F _ (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem o1 (y : Flt) (h1 : Flt.eq y Flt.pz = false) (h2 : y.isNan = false) (h3 : y.isInf = false) :
    floatPow L Flt.one y = .ok Flt.one :=
  floatPow_unit L _ _ _ h1 h2 h3 rfl rfl (by decide +kernel) (by decide +kernel) (F.pow1 y)

theorem m1 (k : Int) (hk : k = 3 ∨ k = 5 ∨ k = 7) :
    floatPow L (Flt.neg Flt.one) (Flt.ofInt k) = .ok (Flt.neg Flt.one) := by
  rcases hk with rfl | rfl | rfl
  all_goals
    exact floatPow_unit L _ _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel) rfl rfl
      (by decide +kernel) (by decide +kernel) (F.powm1 _ (by simp))

end Pow

/-- Every kernel is centred: `cdf(0) == 0.5` for all the names `register` installs (`_kernel_specs`
covers each spelling), and each bounded kernel with a polynomial `cdf` has `cdf(-1) == 0`, `cdf(1) == 1`
and `support == 1.0`. -/
def KernelsCentred : Prop :=
  ∀ L : Libm, LibmFacts L →
    (∀ name ∈ ["normal", "gauss", "logistic", "sigmoid", "rectangular", "uniform", "triangular",
        "parabolic", "epanechnikov", "quartic", "biweight", "triweight", "cosine"],
      ∃ k, kernelSpec L name = some k ∧ k.cdf Flt.pz = .ok Flt.half) ∧
    (∀ name ∈ ["rectangular", "uniform", "triangular", "parabolic", "epanechnikov", "quartic",
        "biweight", "triweight"],
      ∃ k, kernelSpec L name = some k ∧ k.support = some Flt.one ∧
        k.cdf (Flt.neg Flt.one) = .ok Flt.pz ∧ k.cdf Flt.one = .ok Flt.one)

theorem normal_c (L : Libm) (F : LibmFacts L) : (normalKernel L).cdf Flt.pz = .ok Flt.half := by
  have h : fltDiv Flt.pz (Flt.neg (Flt.sqrt Flt.two)) = .ok (.zero true) := by decide +kernel
  have e : Flt.mul Flt.half Flt.one = Flt.half := by decide +kernel
  simp only [normalKernel, bind, Except.bind, h, pure, Except.pure, mathErfc, F.erfc0, e]

theorem logistic_c (L : Libm) (F : LibmFacts L) : (logisticKernel L).cdf Flt.pz = .ok Flt.half := by
  have h : mathExp L Flt.pz = .ok Flt.one := math1_ok _ _ _ _ _ F.exp0 rfl rfl
  have e : (do return Flt.sub Flt.one (← fltDiv Flt.one (Flt.add Flt.one Flt.one)) : Py Flt) =
      .ok Flt.half := by decide +kernel
  simp only [logisticKernel, bind, Except.bind, h]
  exact e

theorem sigmoid_c (L : Libm) (F : LibmFacts L) : (sigmoidKernel L).cdf Flt.pz = .ok Flt.half := by
  have h : mathExp L Flt.pz = .ok Flt.one := math1_ok _ _ _ _ _ F.exp0 rfl rfl
  have h2 : mathAtan L Flt.one = .ok (Flt.div piF (Flt.ofInt 4)) :=
    math1_ok _ _ _ _ _ F.atan1 (by decide +kernel) (by decide +kernel)
  have e : Flt.mul (Flt.div Flt.two piF) (Flt.div piF (Flt.ofInt 4)) = Flt.half := by decide +kernel
  simp only [sigmoidKernel, bind, Except.bind, h, h2, pure, Except.pure, e]

theorem cosine_c (L : Libm) (F : LibmFacts L) : (cosineKernel L).cdf Flt.pz = .ok Flt.half := by
  have e0 : Flt.mul (Flt.div piF Flt.two) Flt.pz = Flt.pz := by decide +kernel
  have h : mathSin L Flt.pz = .ok Flt.pz := math1_ok _ _ _ _ _ F.sin0 rfl rfl
  have e : Flt.add (Flt.mul Flt.half Flt.pz) Flt.half = Flt.half := by decide +kernel
  simp only [cosineKernel, bind, Except.bind, e0, h, pure, Except.pure, e]

theorem parabolic_c (L : Libm) (F : LibmFacts L) :
    (parabolicKernel L).cdf Flt.pz = .ok Flt.half ∧
    (parabolicKernel L).cdf (Flt.neg Flt.one) = .ok Flt.pz ∧
    (parabolicKernel L).cdf Flt.one = .ok Flt.one := by
  have a : sumprodF [fq (-1) 4, fq 3 4, Flt.half] [Flt.pz, Flt.pz, Flt.one] = .ok Flt.half := by
    decide +kernel
  have b : sumprodF [fq (-1) 4, fq 3 4, Flt.half]
      [Flt.neg Flt.one, Flt.neg Flt.one, Flt.one] = .ok Flt.pz := by decide +kernel
  have c : sumprodF [fq (-1) 4, fq 3 4, Flt.half] [Flt.one, Flt.one, Flt.one] = .ok Flt.one := by
    decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · simp only [parabolicKernel, bind, Except.bind, z3 L F, a]
  · simp only [parabolicKernel, bind, Except.bind, m1 L F 3 (by simp), b]
  · simp only [parabolicKernel, bind, Except.bind,
      o1 L F (Flt.ofInt 3) (by decide +kernel) (by decide +kernel) (by decide +kernel), c]

theorem quartic_c (L : Libm) (F : LibmFacts L) :
    (quarticKernel L).cdf Flt.pz = .ok Flt.half ∧
    (quarticKernel L).cdf (Flt.neg Flt.one) = .ok Flt.pz ∧
    (quarticKernel L).cdf Flt.one = .ok Flt.one := by
  have a : sumprodF [fq 3 16, fq (-5) 8, fq 15 16, Flt.half]
      [Flt.pz, Flt.pz, Flt.pz, Flt.one] = .ok Flt.half := by decide +kernel
  have b : sumprodF [fq 3 16, fq (-5) 8, fq 15 16, Flt.half]
      [Flt.neg Flt.one, Flt.neg Flt.one, Flt.neg Flt.one, Flt.one] = .ok Flt.pz := by decide +kernel
  have c : sumprodF [fq 3 16, fq (-5) 8, fq 15 16, Flt.half]
      [Flt.one, Flt.one, Flt.one, Flt.one] = .ok Flt.one := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · simp only [quarticKernel, quarticCdf, bind, Except.bind, z3 L F, z5 L F, a]
  · simp only [quarticKernel, quarticCdf, bind, Except.bind, m1 L F 3 (by simp), m1 L F 5 (by simp), b]
  · simp only [quarticKernel, quarticCdf, bind, Except.bind,
      o1 L F (Flt.ofInt 3) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      o1 L F (Flt.ofInt 5) (by decide +kernel) (by decide +kernel) (by decide +kernel), c]

theorem triweight_c (L : Libm) (F : LibmFacts L) :
    (triweightKernel L).cdf Flt.pz = .ok Flt.half ∧
    (triweightKernel L).cdf (Flt.neg Flt.one) = .ok Flt.pz ∧
    (triweightKernel L).cdf Flt.one = .ok Flt.one := by
  have a : sumprodF [fq (-5) 32, fq 21 32, fq (-35) 32, fq 35 32, Flt.half]
      [Flt.pz, Flt.pz, Flt.pz, Flt.pz, Flt.one] = .ok Flt.half := by decide +kernel
  have b : sumprodF [fq (-5) 32, fq 21 32, fq (-35) 32, fq 35 32, Flt.half]
      [Flt.neg Flt.one, Flt.neg Flt.one, Flt.neg Flt.one, Flt.neg Flt.one, Flt.one] = .ok Flt.pz := by
    decide +kernel
  have c : sumprodF [fq (-5) 32, fq 21 32, fq (-35) 32, fq 35 32, Flt.half]
      [Flt.one, Flt.one, Flt.one, Flt.one, Flt.one] = .ok Flt.one := by decide +kernel
  refine ⟨?_, ?_, ?_⟩
  · simp only [triweightKernel, triweightCdf, bind, Except.bind, z3 L F, z5 L F, z7 L F, a]
  · simp only [triweightKernel, triweightCdf, bind, Except.bind, m1 L F 3 (by simp), m1 L F 5 (by simp),
      m1 L F 7 (by simp), b]
  · simp only [triweightKernel, triweightCdf, bind, Except.bind,
      o1 L F (Flt.ofInt 3) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      o1 L F (Flt.ofInt 5) (by decide +kernel) (by decide +kernel) (by decide +kernel),
      o1 L F (Flt.ofInt 7) (by decide +kernel) (by decide +kernel) (by decide +kernel), c]

theorem rect_c : rectangularKernel.cdf Flt.pz = .ok Flt.half ∧
    rectangularKernel.cdf (Flt.neg Flt.one) = .ok Flt.pz ∧
    rectangularKernel.cdf Flt.one = .ok Flt.one := by decide +kernel

theorem tri_c : triangularKernel.cdf Flt.pz = .ok Flt.half ∧
    triangularKernel.cdf (Flt.neg Flt.one) = .ok Flt.pz ∧
    triangularKernel.cdf Flt.one = .ok Flt.one := by decide +kernel

theorem kernelsCentred_proven : KernelsCentred := by
  intro L F
  constructor
  · intro name h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, normal_c L F⟩
    · exact ⟨_, rfl, normal_c L F⟩
    · exact ⟨_, rfl, logistic_c L F⟩
    · exact ⟨_, rfl, sigmoid_c L F⟩
    · exact ⟨_, rfl, rect_c.1⟩
    · exact ⟨_, rfl, rect_c.1⟩
    · exact ⟨_, rfl, tri_c.1⟩
    · exact ⟨_, rfl, (parabolic_c L F).1⟩
    · exact ⟨_, rfl, (parabolic_c L F).1⟩
    · exact ⟨_, rfl, (quartic_c L F).1⟩
    · exact ⟨_, rfl, (quartic_c L F).1⟩
    · exact ⟨_, rfl, (triweight_c L F).1⟩
    · exact ⟨_, rfl, cosine_c L F⟩
  · intro name h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, rfl, rfl, rect_c.2.1, rect_c.2.2⟩
    · exact ⟨_, rfl, rfl, rect_c.2.1, rect_c.2.2⟩
    · exact ⟨_, rfl, rfl, tri_c.2.1, tri_c.2.2⟩
    · exact ⟨_, rfl, rfl, (parabolic_c L F).2.1, (parabolic_c L F).2.2⟩
    · exact ⟨_, rfl, rfl, (parabolic_c L F).2.1, (parabolic_c L F).2.2⟩
    · exact ⟨_, rfl, rfl, (quartic_c L F).2.1, (quartic_c L F).2.2⟩
    · exact ⟨_, rfl, rfl, (quartic_c L F).2.1, (quartic_c L F).2.2⟩
    · exact ⟨_, rfl, rfl, (triweight_c L F).2.1, (triweight_c L F).2.2⟩

/-- `_newton_raphson`: when the loop ends, `f(x)` is within the tolerance of `y`, as the docstring
of `f_inv` promises (`Return x such that f(x) ≈ y within the specified tolerance`). The
two estimates are exact at the centre: `0` at `p = 0.5`. -/
def NewtonPost : Prop :=
  (∀ (f fp : Flt → Py Flt) (y x r : Flt) (fuel : Nat), newtonLoop f fp y fuel x = .ok r →
    ∃ v, f r = .ok v ∧ Flt.lt (Flt.ofRat (dec10 1 12)) (Flt.abs (Flt.sub v y)) = false) ∧
  (∀ L : Libm, LibmFacts L → ∃ b c, quarticEstimate L Flt.half = .ok (.zero b) ∧
    triweightEstimate L Flt.half = .ok (.zero c))

theorem newtonPost_proven : NewtonPost := by
  constructor
  · intro f fp y x r fuel h
    induction fuel generalizing x with
    | zero => cases h
    | succ n ih =>
      simp only [newtonLoop, bind, Except.bind] at h
      cases hfx : f x with
      | error e => rw [hfx] at h; cases h
      | ok v =>
        rw [hfx] at h
        simp only at h
        split at h
        · cases h1 : fp x with
          | error e => rw [h1] at h; cases h
          | ok w =>
            rw [h1] at h
            simp only at h
            cases h2 : fltDiv (Flt.sub v y) w with
            | error e => rw [h2] at h; cases h
            | ok st =>
              rw [h2] at h
              exact ih _ h
        · rename_i hn
          simp only [pure, Except.pure] at h
          cases h
          exact ⟨v, hfx, by simpa using hn⟩
  · intro L F
    have hs : signSplit Flt.half = (Flt.one, Flt.half) := by decide +kernel
    have e2 : Flt.mul Flt.two Flt.half = Flt.one := by decide +kernel
    have e4 : Flt.sub Flt.one Flt.one = .zero false := by decide +kernel
    have e5 : Flt.lt Flt.half (Flt.ofRat (dec10 499 3)) = false := by decide +kernel
    have e6 : Flt.mul (.zero false) Flt.one = .zero false := by decide +kernel
    refine ⟨false, false, ?_, ?_⟩
    · have e1 : Flt.lt Flt.half (Flt.ofRat (dec10 106 4)) = false := by decide +kernel
      have e3 := o1 L F (Flt.ofRat (dec10 4258865685331 13)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      simp only [quarticEstimate, hs, e1, e2, e3, e4, e5, e6, bind, Except.bind, Bool.false_eq_true,
        if_false, pure, Except.pure]
    · have e3 := o1 L F (Flt.ofRat (dec10 3400218741872791 16)) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
      simp only [triweightEstimate, hs, e2, e3, e4, e5, e6, bind, Except.bind, Bool.and_false,
        Bool.false_eq_true, if_false, pure, Except.pure]

/-! ## `kde`, `kde_random` -/

/-- The checks of `kde` and `kde_random`, in source order: empty data, a first element that is not
an int or float, `h <= 0.0`, an unknown kernel. `kde_random` makes one value per draw. -/
def KdeChecks : Prop :=
  ∀ (L : Libm) (d d2 : List PyN) (h : Val) (k : String) (c : Bool) (x : Val) (ds : List (Nat × Flt)),
    (∀ e, kdeSpec L d h k = .error e → kdeAt L d d2 h k c x = .error e ∧
      kdeRandomAt L d h k ds = .error e) ∧
    kdeSpec L [] h k = .error (.named "StatisticsError" "Empty data sequence") ∧
    (∀ s t, kdeSpec L ((Val.str s).toN :: t) h k =
      .error (.typeError "Data sequence must contain ints or floats")) ∧
    (∀ (a : Flt) (t : List PyN) (hh : Flt), Flt.le hh Flt.pz = true →
      kdeSpec L ((Val.flt a).toN :: t) (.flt hh) k =
        .error (.named "StatisticsError" "~Bandwidth h must be positive")) ∧
    (∀ (r : List Val), kdeRandomAt L d h k ds = .ok r → r.length = ds.length)

theorem kdeChecks_proven : KdeChecks := by
  intro L d d2 h k c x ds
  refine ⟨?_, rfl, fun _ _ => rfl, ?_, ?_⟩
  · intro e he
    constructor
    · simp only [kdeAt, bind, Except.bind, he]
    · simp only [kdeRandomAt, bind, Except.bind, he]
  · intro a t hh hle
    have e1 : ((Val.flt a).toN :: t).isEmpty = false := rfl
    have e2 : (pick ((Val.flt a).toN :: t) 0).v = .flt a := rfl
    simp only [kdeSpec, e1, Bool.false_eq_true, if_false, bind, Except.bind, e2, vlePy_flt, hle,
      if_true]
    rfl
  · intro r hr
    simp only [kdeRandomAt, bind, Except.bind] at hr
    cases hk : kdeSpec L d h k with
    | error e => rw [hk] at hr; cases hr
    | ok kk =>
      rw [hk] at hr
      exact mapM_length _ _ _ hr

theorem bl_all {α : Type} (lt : α → α → Bool) (a : List α) (x : α)
    (h : ∀ (k : Nat) (hk : k < a.length), lt a[k] x = true) :
    ∀ f lo, lo ≤ a.length → a.length - lo < f → bisectLeftGo lt a x f lo a.length = a.length := by
  intro f
  induction f with
  | zero => intro lo _ h2; omega
  | succ f ih =>
    intro lo h1 h2
    simp only [bisectLeftGo]
    split
    · rename_i hlt
      have hm : (lo + a.length) / 2 < a.length := by omega
      rw [List.getElem?_eq_getElem hm]
      simp only [h _ hm, if_true]
      exact ih _ (by omega) (by omega)
    · omega

theorem bl_none {α : Type} (lt : α → α → Bool) (a : List α) (x : α)
    (h : ∀ (k : Nat) (hk : k < a.length), lt a[k] x = false) :
    ∀ f hi, hi ≤ a.length → bisectLeftGo lt a x f 0 hi = 0 := by
  intro f
  induction f with
  | zero => intro hi _; rfl
  | succ f ih =>
    intro hi h1
    simp only [bisectLeftGo]
    split
    · rename_i hlt
      have hm : (0 + hi) / 2 < a.length := by omega
      rw [List.getElem?_eq_getElem hm]
      simp only [h _ hm, Bool.false_eq_true, if_false]
      exact ih _ (by omega)
    · rfl

theorem br_all {α : Type} (lt : α → α → Bool) (a : List α) (x : α)
    (h : ∀ (k : Nat) (hk : k < a.length), lt x a[k] = true) :
    ∀ f hi, hi ≤ a.length → bisectRightGo lt a x f 0 hi = 0 := by
  intro f
  induction f with
  | zero => intro hi _; rfl
  | succ f ih =>
    intro hi h1
    simp only [bisectRightGo]
    split
    · rename_i hlt
      have hm : (0 + hi) / 2 < a.length := by omega
      rw [List.getElem?_eq_getElem hm]
      simp only [h _ hm, if_true]
      exact ih _ (by omega)
    · rfl

/-- `cdf` of a kernel with bounded support outside the data: `0.0` when every sample point is
above `x + bandwidth`, `1.0` when every one is below `x - bandwidth`, whatever the kernel. So the
estimated distribution function really starts at 0 and ends at 1. -/
def KdeCdfOutside : Prop :=
  ∀ (k : Kernel) (s h x : Flt) (S : List PyN), k.support = some s → S ≠ [] →
    let bw := Flt.mul h s
    let st : KdeState := ⟨S.length, S⟩
    ((∀ p ∈ S, vlt (.flt (Flt.add x bw)) p.v = true ∧ vlt p.v (.flt (Flt.sub x bw)) = false) →
      kdeCdf k (.flt h) st S (.flt x) = .ok (.flt (.zero false))) ∧
    ((∀ p ∈ S, vlt p.v (.flt (Flt.sub x bw)) = true) →
      kdeCdf k (.flt h) st S (.flt x) = .ok (.flt Flt.one))

theorem kdeCdfOutside_proven : KdeCdfOutside := by
  intro k s h x S hs hne bw st
  have hn := length_ne S hne
  have hr : kdeRefresh st S = .ok st := by simp [kdeRefresh, st]
  have hmul : vmul (.flt h) (.flt s) = .ok (.flt bw) := rfl
  have hsub : vsub (.flt x) (.flt bw) = .ok (.flt (Flt.sub x bw)) := rfl
  have hadd : vadd (.flt x) (.flt bw) = .ok (.flt (Flt.add x bw)) := rfl
  have hunf : ∀ (i : Nat) (sup : List PyN), supported S (.flt x) (.flt bw) = .ok (i, sup) → sup = [] →
      kdeCdf k (.flt h) st S (.flt x) = vdiv (.int i) (.int S.length) := by
    intro i sup h1 h2
    subst h2
    have h1' : supported st.sample (.flt x) (.flt bw) = .ok (i, []) := h1
    simp only [kdeCdf, hs, bind, Except.bind, hr, hmul, h1']
    rfl
  constructor
  · intro hall
    have hj : bisectRight (fun a b : PyN => vlt a.v b.v) S (Val.flt (Flt.add x bw)).toN = 0 :=
      br_all _ S _ (fun k hk => (hall S[k] (List.getElem_mem hk)).1) _ _ (Nat.le_refl _)
    have hi : bisectLeft (fun a b : PyN => vlt a.v b.v) S (Val.flt (Flt.sub x bw)).toN = 0 :=
      bl_none _ S _ (fun k hk => (hall S[k] (List.getElem_mem hk)).2) _ _ (Nat.le_refl _)
    have hsup : supported S (.flt x) (.flt bw) = .ok (0, []) := by
      simp only [supported, bind, Except.bind, hsub, hadd, hi, hj, pure, Except.pure]
      simp
    rw [hunf 0 [] hsup rfl]
    have : S.length ≠ 0 := by omega
    show (Val.flt <$> intTrueDiv 0 (S.length : Int)) = _
    simp only [intTrueDiv]
    rw [if_neg (by omega)]
    simp
    rfl
  · intro hall
    have hi : bisectLeft (fun a b : PyN => vlt a.v b.v) S (Val.flt (Flt.sub x bw)).toN = S.length :=
      bl_all _ S _ (fun k hk => hall S[k] (List.getElem_mem hk)) _ 0 (by omega) (by omega)
    let j := bisectRight (fun a b : PyN => vlt a.v b.v) S (Val.flt (Flt.add x bw)).toN
    have h1 : supported S (.flt x) (.flt bw) = .ok (S.length, (S.take j).drop S.length) := by
      simp only [supported, bind, Except.bind, hsub, hadd, hi, pure, Except.pure]
      rfl
    have h2 : (S.take j).drop S.length = [] := by
      apply List.drop_eq_nil_of_le
      simp only [List.length_take]
      omega
    rw [hunf _ _ h1 h2]
    have hne0 : ((S.length : Int) : Rat) ≠ 0 := by
      have : (S.length : Rat) ≠ 0 := by
        have : S.length ≠ 0 := by omega
        simpa using this
      exact this
    show (Val.flt <$> intTrueDiv (S.length : Int) (S.length : Int)) = _
    simp only [intTrueDiv]
    rw [if_neg (by omega), if_neg (by omega)]
    have e : ((S.length : Int) : Rat) / ((S.length : Int) : Rat) = 1 := by
      rw [Rat.div_def]
      exact Rat.mul_inv_cancel _ hne0
    have e1 : Flt.ofRat 1 = Flt.one := by decide +kernel
    rw [e, e1]
    rfl

/-! ## `geometric_mean`, `fmean` -/

theorem gm_zero (L : Libm) (st : GmSt) :
    gmStep L st (.frac 0) = .ok { st with n := st.n + 1, foundZero := true } := by
  have e1 : vltPy (.flt Flt.pz) (.frac 0) = .ok false := by decide +kernel
  have e2 : asDouble (.frac 0) = .ok Flt.pz := by decide +kernel
  have e3 : veq (.frac 0) (.flt Flt.pz) = true := by decide +kernel
  simp only [gmStep, bind, Except.bind, e1, e2, e3, Bool.false_eq_true, if_false, if_true, pure,
    Except.pure, Bool.false_or]
  rfl

theorem gm_zeros (L : Libm) (k : Nat) (st : GmSt) (rest : List Val) :
    ((List.replicate k (Val.frac 0)) ++ rest).foldlM (gmStep L) st =
      rest.foldlM (gmStep L) (if k = 0 then st else { st with n := st.n + k, foundZero := true }) := by
  induction k generalizing st with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, List.foldlM_cons, bind, Except.bind, gm_zero]
    rw [ih, if_neg (Nat.succ_ne_zero k)]
    by_cases hk : k = 0
    · subst hk; rfl
    · rw [if_neg hk]
      have e : st.n + 1 + k = st.n + (k + 1) := by omega
      simp only [e]

theorem ratToFlt_not_nan {a : Rat} {r : Flt} (h : ratToFlt a = .ok r) : r.isNan = false := by
  have hof : ∀ q : Rat, (Flt.ofRat q).isNan = false := by
    intro q
    unfold Flt.ofRat
    split
    · rfl
    · simp only
      split
      · rfl
      · split <;> rfl
  unfold ratToFlt intTrueDiv at h
  by_cases b0 : ((a.den : Int)) = 0
  · rw [if_pos b0] at h; cases h
  rw [if_neg b0] at h
  simp only at h
  by_cases a0 : a.num = 0
  · rw [if_pos a0] at h
    cases h
    rfl
  rw [if_neg a0] at h
  generalize hq : Flt.ofRat ((a.num : Rat) / (((a.den : Int)) : Rat)) = v at h
  have := hof ((a.num : Rat) / (((a.den : Int)) : Rat))
  rw [hq] at this
  cases v with
  | inf n => cases h
  | nan => cases h; exact this
  | zero n => cases h; rfl
  | fin q => cases h; rfl

/-- `geometric_mean`: empty data raises; zeros give `0.0`; and, unlike `harmonic_mean`, a zero does
not stop the scan: a negative value after it still raises (the docstring's "if it contains a
negative value"). -/
def GeometricChecks : Prop :=
  ∀ L : Libm,
    geometricMean L [] = .error (.named "StatisticsError" "Must have a non-empty dataset") ∧
    (∀ k : Nat, 0 < k → geometricMean L (fracs (List.replicate k 0)) = .ok Flt.pz) ∧
    (∀ (k : Nat) (a : Rat) (r : Flt) (rest : List PyN), a < 0 → ratToFlt a = .ok r →
      geometricMean L (fracs (List.replicate k 0) ++ (Val.frac a).toN :: rest) =
        .error (.named "StatisticsError" "~No negative inputs allowed: x"))

theorem fracs_replicate (k : Nat) :
    (fracs (List.replicate k 0)).map (·.v) = List.replicate k (Val.frac 0) := by
  rw [fracs_vals]
  simp [List.map_replicate]

theorem geometricChecks_proven : GeometricChecks := by
  intro L
  refine ⟨rfl, ?_, ?_⟩
  · intro k hk
    have h := gm_zeros L k {} []
    simp only [List.append_nil, List.foldlM_nil] at h
    have hk0 : ¬ k = 0 := by omega
    simp only [hk0, if_false] at h
    simp only [geometricMean, bind, Except.bind, fracs_replicate, h, pure, Except.pure]
    have e1 : fsumEnd ({} : FsumState) = .ok Flt.pz := by decide +kernel
    have e2 : Flt.eq Flt.pz (.inf false) = false := rfl
    show (match fsumEnd ({} : FsumState) with
      | .error e => Except.error e
      | .ok total => _) = _
    rw [e1]
    simp [hk0, Flt.isNan, e2]
    rfl
  · intro k a r rest ha hr
    have hmap : ((fracs (List.replicate k 0) ++ (Val.frac a).toN :: rest).map (·.v)) =
        List.replicate k (Val.frac 0) ++ (.frac a :: rest.map (·.v)) := by
      simp only [List.map_append, fracs_replicate, List.map_cons]
      rfl
    have hn : ¬ (0 : Rat) = a := by grind
    have e1 : vltPy (.flt Flt.pz) (.frac a) = .ok false := by
      have : ¬ (0 : Rat) < a := by grind
      simp [vltPy, Val.ordered, vlt, Val.ext, Ext.lt, this, Flt.pz]
    have e2 : asDouble (.frac a) = .ok r := hr
    have e3 : r.isNan = false := ratToFlt_not_nan hr
    have e4 : veq (.frac a) (.flt Flt.pz) = false := by
      have : ¬ a = 0 := by grind
      simp [veq, Val.ext, this, Flt.pz]
    have e2' : ((fun d : Flt => d.isNan) <$> asDouble (.frac a)) = .ok false := by
      rw [e2]
      simp [Functor.map, Except.map, e3]
    have hstep : ∀ st : GmSt, gmStep L st (.frac a) =
        .error (.named "StatisticsError" "~No negative inputs allowed: x") := by
      intro st
      simp only [gmStep, bind, Except.bind, e1, e2', e4, Bool.false_eq_true, if_false, pure,
        Except.pure, Bool.false_or]
      rfl
    simp only [geometricMean, bind, Except.bind, hmap, gm_zeros, List.foldlM_cons, hstep]

/-- `fmean`: empty data raises unless weights are given; with weights, a length mismatch and a
zero total weight raise. -/
def FmeanChecks : Prop :=
  fmean [] none = .error (.named "StatisticsError" "fmean requires at least one data point") ∧
  (∀ (x : PyN) (xs : List PyN),
    fmean [] (some (x :: xs)) = .error (.named "StatisticsError" "data and weights must be the same length") ∧
    fmean (x :: xs) (some []) = .error (.named "StatisticsError" "data and weights must be the same length")) ∧
  fmean [] (some []) = .error (.named "StatisticsError" "sum of weights must be non-zero")

theorem fmeanChecks_proven : FmeanChecks := by
  refine ⟨by decide +kernel, ?_, by decide +kernel⟩
  intro x xs
  constructor <;> rfl

/-! ## Two inputs -/

/-- Shape checks of `covariance`, `correlation` and `linear_regression`, in source order: lengths must
match, at least two points are needed; `correlation` then rejects an unknown `method`. With
`proportional=True` the intercept is exactly `0.0`. -/
def TwoInputChecks : Prop :=
  ∀ (x y : List PyN) (m : String),
    (x.length ≠ y.length →
      covariance x y = .error (.named "StatisticsError" "covariance requires that both inputs have same number of data points") ∧
      correlation x y m = .error (.named "StatisticsError" "correlation requires that both inputs have same number of data points") ∧
      ∀ p, linearRegression x y p = .error (.named "StatisticsError" "linear regression requires that both inputs have same number of data points")) ∧
    (x.length = y.length → x.length < 2 →
      covariance x y = .error (.named "StatisticsError" "covariance requires at least two data points") ∧
      correlation x y m = .error (.named "StatisticsError" "correlation requires at least two data points") ∧
      ∀ p, linearRegression x y p = .error (.named "StatisticsError" "linear regression requires at least two data points")) ∧
    (x.length = y.length → 2 ≤ x.length → m ≠ "linear" → m ≠ "ranked" →
      (correlation x y m).raises "ValueError") ∧
    (∀ a b, linearRegression x y true = .ok (a, b) → b = .flt Flt.pz)

theorem twoInputChecks_proven : TwoInputChecks := by
  intro x y m
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h
    have h' : (y.length != x.length) = true := by
      simp only [bne_iff_ne]; omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [covariance, h', if_true, bind, Except.bind]; rfl
    · simp only [correlation, h', if_true, bind, Except.bind]; rfl
    · intro p
      simp only [linearRegression, h', if_true, bind, Except.bind]; rfl
  · intro h1 h2
    have h' : (y.length != x.length) = false := by
      simp only [bne_eq_false_iff_eq]; omega
    refine ⟨?_, ?_, ?_⟩
    · simp only [covariance, h', Bool.false_eq_true, if_false, h2, if_true, bind, Except.bind]; rfl
    · simp only [correlation, h', Bool.false_eq_true, if_false, h2, if_true, bind, Except.bind]; rfl
    · intro p
      simp only [linearRegression, h', Bool.false_eq_true, if_false, h2, if_true, bind, Except.bind]
      rfl
  · intro h1 h2 h3 h4
    have h' : (y.length != x.length) = false := by
      simp only [bne_eq_false_iff_eq]; omega
    have h5 : ¬ x.length < 2 := by omega
    have h6 : (m != "linear" && m != "ranked") = true := by
      simp only [Bool.and_eq_true, bne_iff_ne]
      exact ⟨h3, h4⟩
    refine ⟨.valueError s!"~Unknown method: '{m}'", ?_, rfl⟩
    simp only [correlation, h', Bool.false_eq_true, if_false, h5, h6, if_true, bind, Except.bind]
    rfl
  · intro a b h
    unfold linearRegression at h
    simp only [bind, Except.bind] at h
    by_cases c1 : (y.length != x.length) = true
    · simp only [c1, if_true] at h
      cases h
    · simp only [c1, if_false] at h
      by_cases c2 : x.length < 2
      · simp only [c2, if_true] at h
        cases h
      · simp only [c2, if_false, Bool.not_true, Bool.false_eq_true, pure, Except.pure] at h
        simp only [lrCore, bind, Except.bind, if_true, pure, Except.pure] at h
        repeat' (first | (cases h; done) | split at h)
        all_goals (cases h; rfl)

/-- `0.1` as a float. -/
def f01 : Flt := .fin (mkRat 3602879701896397 36028797018963968)

/-- `correlation` promises `StatisticsError` for constant input (Doc/library/statistics.rst:757:
inputs "need not to be constant, otherwise StatisticsError is raised"). -/
def ConstantInputDetected : Prop :=
  ∀ (c : Flt) (y : List Int), c.isFinite = true → 2 ≤ y.length →
    (correlation (floats (List.replicate y.length c)) (ints y) "linear").raises "StatisticsError"

/-- `[0.1, 0.1, 0.1]`: `fsum(x) / 3` is not `0.1`, so the deviations are not zero. -/
theorem constantInputDetected_refuted : ¬ConstantInputDetected := by
  intro h
  obtain ⟨e, he, -⟩ := h f01 [1, 2, 3] rfl (by decide)
  have hv : correlation (floats (List.replicate 3 f01)) (ints [1, 2, 3]) "linear" =
      .ok (.flt Flt.pz) := by decide +kernel
  rw [show ([1, 2, 3] : List Int).length = 3 from rfl, hv] at he
  cases he

/-- Pearson's `r` "takes values between -1 and +1" (statistics.py:691-692). -/
def CorrelationBounded : Prop :=
  ∀ (x y : List PyN) (r : Flt), correlation x y "linear" = .ok (.flt r) →
    Flt.le (Flt.neg Flt.one) r = true ∧ Flt.le r Flt.one = true

theorem correlationBounded_refuted : ¬CorrelationBounded := by
  intro h
  have hv : correlation
      (floats [.fin (mkRat 3582582507727775 4503599627370496), .fin (mkRat (-474833679268573) 4503599627370496)])
      (floats [.fin (mkRat (-2686936880795831) 1125899906842624), .fin (mkRat (-474833679268573) 4503599627370496)])
      "linear" = .ok (.flt (.fin (mkRat (-4503599627370497) 4503599627370496))) := by decide +kernel
  have := (h _ _ _ hv).1
  revert this
  decide +kernel

/-! ## `_rank`, the square roots, `_sqrtprod` -/

/-- `_rank`: only `ties='average'` exists; there is one rank per item, and the docstring examples
hold, including idempotence and `reverse`. Ties get the average of their positions. -/
def RankSpec : Prop :=
  (∀ (d : List Val) (rev : Bool) (t : String) (st : Val), t ≠ "average" →
    (rankOf d rev t st).raises "ValueError") ∧
  (∀ (d : List Val) (rev : Bool) (st : Val) (r : List Val), rankOf d rev "average" st = .ok r →
    r.length = d.length) ∧
  rankOf ([31, 56, 31, 25, 75, 18].map .int) false "average" (.int 1) =
    .ok ([mkRat 7 2, 5, mkRat 7 2, 2, 6, 1].map (fun q => Val.flt (.fin q))) ∧
  rankOf ([mkRat 7 2, 5, mkRat 7 2, 2, 6, 1].map (fun q => Val.flt (.fin q))) false "average" (.int 1) =
    .ok ([mkRat 7 2, 5, mkRat 7 2, 2, 6, 1].map (fun q => Val.flt (.fin q))) ∧
  rankOf ([45, 48, 44].map .int) true "average" (.int 1) =
    .ok ([2, 1, 3].map (fun q => Val.flt (.fin q)))

theorem rankSpec_proven : RankSpec := by
  refine ⟨?_, ?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  · intro d rev t st h
    have h' : (t != "average") = true := by simpa using h
    refine ⟨.valueError s!"~Unknown tie resolution method: '{t}'", ?_, rfl⟩
    simp only [rankOf, h', if_true, bind, Except.bind]
    rfl
  · intro d rev st r h
    simp only [rankOf, bind, Except.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [pure, Except.pure] at h
          split at h
          · cases h
          · cases h
            simp

/-- `_decimal_sqrt_of_frac`: `0 / m` is `0` and the sign normalization at statistics.py:1736-1739
makes `(-n) / (-m)` the same as `n / m`. -/
def DecimalSqrtSign : Prop :=
  ∀ n m : Int, 0 < n →
    decimalSqrtOfFrac 0 m = .ok 0 ∧ decimalSqrtOfFrac (-n) (-m) = decimalSqrtOfFrac n m

theorem decimalSqrtSign_proven : DecimalSqrtSign := by
  intro n m hn
  refine ⟨rfl, ?_⟩
  have h1 : ¬ (-n = 0) := by omega
  have h2 : ¬ (n = 0) := by omega
  have h3 : -n ≤ 0 := by omega
  have h4 : ¬ (n ≤ 0) := by omega
  simp only [decimalSqrtOfFrac, h1, h2, h3, h4, if_false, if_true, Int.neg_neg]

/-- `_sqrtprod`: a zero factor gives `0.0` with no division; products that overflow or are perfect
squares come out exact: `sqrtprod(4, 9) == 6`, `sqrtprod(1e308, 1e308) == 1e308`. -/
def SqrtprodSpec : Prop :=
  (∀ q : Rat, 0 < q → sqrtprod (.fin q) Flt.pz = .ok Flt.pz) ∧
  sqrtprod (.fin 4) (.fin 9) = .ok (.fin 6) ∧
  sqrtprod (.fin 100000000000000001097906362944045541740492309677311846336810682903157585404911491537163328978494688899061249669721172515611590283743140088328307009198146046031271664502933027185697489699588559043338384466165001178426897626212945177628091195786707458122783970171784415105291802893207873272974885715430223118336)
    (.fin 100000000000000001097906362944045541740492309677311846336810682903157585404911491537163328978494688899061249669721172515611590283743140088328307009198146046031271664502933027185697489699588559043338384466165001178426897626212945177628091195786707458122783970171784415105291802893207873272974885715430223118336)
    = .ok (.fin 100000000000000001097906362944045541740492309677311846336810682903157585404911491537163328978494688899061249669721172515611590283743140088328307009198146046031271664502933027185697489699588559043338384466165001178426897626212945177628091195786707458122783970171784415105291802893207873272974885715430223118336)

theorem sqrtprodSpec_proven : SqrtprodSpec := by
  refine ⟨?_, by decide +kernel, by decide +kernel⟩
  intro q hq
  have hn : ¬ q < 0 := by grind
  have e : Flt.mul (.fin q) Flt.pz = Flt.pz := by
    simp [Flt.mul, Flt.pz, hn]
  have e2 : mathSqrt Flt.pz = .ok Flt.pz := by decide +kernel
  simp only [sqrtprod, sqrtprodGo, bind, Except.bind, e, e2]
  rfl

/-- `NormalDist.from_samples` needs two points, the message of `_mean_stdev`. -/
def FromSamplesShort : Prop :=
  ND.fromSamples [] = .error (.named "StatisticsError" "stdev requires at least two data points") ∧
  ∀ q : Rat, ND.fromSamples (fracs [q]) =
    .error (.named "StatisticsError" "stdev requires at least two data points")

theorem fromSamplesShort_proven : FromSamplesShort := by
  refine ⟨by decide +kernel, ?_⟩
  intro q
  have hss := ss_fracs [q] (by simp)
  simp only [ND.fromSamples, meanStdev, bind, Except.bind, hss]
  rfl

end PyLean.CoreLibs.CalStat
