import PyLean.CoreLibs.CalStat.StatProps
import PyLean.ListSort.Props

/-! Properties of the `statistics` mirror, continued: `_exact_ratio`, `_isfinite`, `_coerce`,
`_convert`, `_fail_neg`, `harmonic_mean`, the integer square root, the medians. -/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-! ## `_exact_ratio`, `_isfinite` -/

/-- `_exact_ratio` returns the value as a ratio with positive denominator for every finite number
of every type; a NaN or infinity comes back as `(x, None)`, exactly when `_isfinite` says it is not
finite (the `assert` at statistics.py:1613); a non-number is `TypeError`. -/
def ExactRatioSpec : Prop :=
  (∀ v, IsExact v → ∃ n d, exactRatio v = .ok (.ratio n d) ∧ d ≠ 0 ∧ mkRat n d = exactQ v) ∧
  (∀ x : Flt, exactRatio (.flt x) = .ok (.special (.flt x)) ↔ isFiniteV (.flt x) = .ok false) ∧
  (∀ d : Dec, exactRatio (.dec d) = .ok (.special (.dec d)) ↔ isFiniteV (.dec d) = .ok false) ∧
  (∀ s, exactRatio (.str s) = .error (.typeError "can't convert type 'str' to numerator/denominator"))

theorem exactRatioSpec_proven : ExactRatioSpec := by
  refine ⟨?_, ?_, ?_, fun _ => rfl⟩
  · intro v hv
    exact ⟨_, _, exactRatio_exact v hv, (exactQ v).den_nz, Rat.mkRat_self _⟩
  · intro x
    cases x <;> simp [exactRatio, isFiniteV, asDouble, toFloat, Flt.isFinite, bind, Except.bind,
      pure, Except.pure]
  · intro d
    cases d <;> simp [exactRatio, isFiniteV, Dec.isFinite]

/-! ## `_coerce` -/

/-- Two outcomes agree when they are the same class or both raise (the `TypeError` message spells
the two classes in the order met, so it is not compared). -/
def sameOutcome : Py Cls → Py Cls → Prop
  | .ok a, .ok b => a = b
  | .error _, .error _ => True
  | _, _ => False

instance (a b : Py Cls) : Decidable (sameOutcome a b) := by
  unfold sameOutcome
  split <;> infer_instance

/-- `_sum` and `_ss` run `reduce(_coerce, types, int)` over a `set`, whose iteration order follows
the addresses of the type objects. So the result should not depend on the order. -/
def CoerceOrderIndependent : Prop :=
  ∀ l l' : List Cls, l.Perm l' → sameOutcome (reduceCoerce l) (reduceCoerce l')

def clsF1 : Cls := ⟨"F1", ["F1", "Fraction"], none⟩
def clsF2 : Cls := ⟨"F2", ["F2", "Fraction"], none⟩

/-- Two sibling `Fraction` subclasses and `float`: `_coerce` is not associative, the outcome is a
`TypeError` in one order and `float` in another. -/
theorem coerceOrderIndependent_refuted : ¬CoerceOrderIndependent := by
  intro h
  have := h [clsF1, clsF2, clsFloat] [clsF1, clsFloat, clsF2]
    (List.Perm.cons _ (List.Perm.swap _ _ _))
  revert this
  decide

def builtinCls : List Cls := [clsInt, clsBool, clsFloat, clsFraction, clsDecimal]

def coerceStep (x : Py Cls) (c : Cls) : Py Cls :=
  match x with
  | .ok t => coerce t c
  | .error e => .error e

theorem coerce_swap : ∀ t ∈ builtinCls, ∀ a ∈ builtinCls, ∀ b ∈ builtinCls,
    sameOutcome (coerceStep (coerce t a) b) (coerceStep (coerce t b) a) := by
  decide

theorem coerce_closed : ∀ t ∈ builtinCls, ∀ a ∈ builtinCls, ∀ r, coerce t a = .ok r → r ∈ builtinCls := by
  intro t ht a ha r hr
  have key : ∀ t ∈ builtinCls, ∀ a ∈ builtinCls,
      (match coerce t a with
       | .ok r => builtinCls.contains r
       | .error _ => true) = true := by decide
  have := key t ht a ha
  rw [hr] at this
  simpa using this

def GoodOutcome (x : Py Cls) : Prop :=
  match x with
  | .ok c => c ∈ builtinCls
  | .error _ => True

theorem good_step (x : Py Cls) (hx : GoodOutcome x) (c : Cls) (hc : c ∈ builtinCls) :
    GoodOutcome (coerceStep x c) := by
  cases x with
  | error e => trivial
  | ok t =>
    show GoodOutcome (coerce t c)
    cases hr : coerce t c with
    | error e => trivial
    | ok r => exact coerce_closed t hx c hc r hr

theorem same_refl (x : Py Cls) : sameOutcome x x := by
  cases x
  · trivial
  · exact rfl

theorem same_trans {x y z : Py Cls} (h1 : sameOutcome x y) (h2 : sameOutcome y z) :
    sameOutcome x z := by
  cases x <;> cases y <;> cases z <;> simp_all [sameOutcome]

theorem same_step {x y : Py Cls} (h : sameOutcome x y) (c : Cls) :
    sameOutcome (coerceStep x c) (coerceStep y c) := by
  cases x with
  | error e =>
    cases y with
    | error e' => exact trivial
    | ok b => cases h
  | ok a =>
    cases y with
    | error e' => cases h
    | ok b =>
      have : a = b := h
      subst this
      exact same_refl _

theorem good_fold (l : List Cls) (x : Py Cls) (hx : GoodOutcome x) (hl : ∀ c ∈ l, c ∈ builtinCls) :
    GoodOutcome (l.foldl coerceStep x) := by
  induction l generalizing x with
  | nil => exact hx
  | cons a as ih =>
    exact ih _ (good_step x hx a (hl a (by simp))) (fun c hc => hl c (List.mem_cons_of_mem _ hc))

theorem fold_perm {l l' : List Cls} (hp : l.Perm l') :
    ∀ x y, GoodOutcome x → GoodOutcome y → sameOutcome x y → (∀ c ∈ l, c ∈ builtinCls) →
      sameOutcome (l.foldl coerceStep x) (l'.foldl coerceStep y) := by
  induction hp with
  | nil => intro x y _ _ h _; exact h
  | cons a _ ih =>
    intro x y gx gy h hl
    exact ih _ _ (good_step x gx a (hl a (by simp))) (good_step y gy a (hl a (by simp)))
      (same_step h a) (fun c hc => hl c (List.mem_cons_of_mem _ hc))
  | @swap a b rest =>
    intro x y gx gy h hl
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have hrest : ∀ c ∈ rest, c ∈ builtinCls := fun c hc => hl c (by simp [hc])
    have key : sameOutcome (coerceStep (coerceStep x b) a) (coerceStep (coerceStep y a) b) := by
      cases x with
      | error e =>
        cases y with
        | error e' => trivial
        | ok _ => cases h
      | ok t =>
        cases y with
        | error e' => cases h
        | ok t' =>
          have : t = t' := h
          subst this
          exact coerce_swap t gx b hb a ha
    have rel : ∀ (l : List Cls) (u v : Py Cls), sameOutcome u v →
        sameOutcome (l.foldl coerceStep u) (l.foldl coerceStep v) := by
      intro l
      induction l with
      | nil => intro _ _ h; exact h
      | cons c cs ih => intro u v h; exact ih _ _ (same_step h c)
    exact rel rest _ _ key
  | trans h1 _ ih1 ih2 =>
    intro x y gx gy h hl
    have h3 := ih1 x y gx gy h hl
    have hl2 : ∀ c ∈ _, c ∈ builtinCls := fun c hc => hl c (h1.mem_iff.mpr hc)
    have h4 := ih2 y y gy gy (same_refl y) hl2
    exact same_trans h3 h4

theorem reduce_eq_fold (l : List Cls) (x : Py Cls) :
    (match x with
     | .ok t => l.foldlM coerce t
     | .error e => .error e) = l.foldl coerceStep x := by
  induction l generalizing x with
  | nil => cases x <;> rfl
  | cons a as ih =>
    rw [List.foldl_cons, ← ih]
    cases x with
    | error e => rfl
    | ok t =>
      simp only [List.foldlM_cons, coerceStep, bind, Except.bind]
      cases coerce t a <;> rfl

/-- On the built-in numeric types the order of the set does not matter: the broad statement above
fails only through user subclasses. -/
def CoerceBuiltinOrder : Prop :=
  ∀ l l' : List Cls, l.Perm l' → (∀ c ∈ l, c ∈ builtinCls) →
    sameOutcome (reduceCoerce l) (reduceCoerce l')

theorem coerceBuiltinOrder_proven : CoerceBuiltinOrder := by
  intro l l' hp hl
  have e : ∀ m : List Cls, reduceCoerce m = m.foldl coerceStep (.ok clsInt) :=
    fun m => reduce_eq_fold m (.ok clsInt)
  rw [e, e]
  exact fold_perm hp _ _ (by simp [GoodOutcome, builtinCls]) (by simp [GoodOutcome, builtinCls])
    (same_refl _) hl

/-! ## `_convert` -/

/-- `_convert` keeps a `Fraction`, gives a whole value to an unrestricted `int` type, and turns a
non-whole value into the rounded `float`, for every `int` subclass. -/
def ConvertSpec : Prop :=
  ∀ q : Rat,
    convert (.frac q) clsFraction = .ok (Val.frac q).toN ∧
    ∀ T : Cls, isSubclass T clsInt = true → T.same clsFraction = false →
      (q.den = 1 → T.members = none → convert (.frac q) T = .ok ⟨T, .int q.num⟩) ∧
      (q.den ≠ 1 → convert (.frac q) T = (fun r => (Val.flt r).toN) <$> ratToFlt q)

theorem convertSpec_proven : ConvertSpec := by
  intro q
  refine ⟨rfl, ?_⟩
  intro T hT hs
  have h0 : (Val.frac q).cls.same T = false := by
    have e : (Val.frac q).cls = clsFraction := rfl
    rw [e]
    simp only [Cls.same, beq_eq_false_iff_ne, ne_eq] at hs ⊢
    exact fun h => hs h.symm
  constructor
  · intro hd hm
    unfold convert
    rw [h0]
    simp only [Bool.false_eq_true, if_false]
    have e : (isSubclass T clsInt && q.den != 1) = false := by simp [hd]
    rw [e]
    simp [construct, hT, hm]
  · intro hd
    exact (by
      unfold convert
      rw [h0]
      simp only [Bool.false_eq_true, if_false]
      have e : (isSubclass T clsInt && q.den != 1) = true := by
        simp only [Bool.and_eq_true, bne_iff_ne]
        exact ⟨hT, hd⟩
      rw [e]
      show construct clsFloat (.frac q) = _
      have e1 : isSubclass clsFloat clsInt = false := by decide
      have e2 : isSubclass clsFloat clsFloat = true := by decide
      simp only [construct, e1, e2, Bool.false_eq_true, if_false, if_true, bind, Except.bind,
        toFloat, pure, Except.pure]
      cases ratToFlt q <;> rfl)

/-- `mean` should accept any `int` subclass: the value of the mean of valid members is a number,
and nothing in the documentation says the class has to contain it. -/
def MeanIntSubclass : Prop :=
  ∀ (T : Cls) (xs : List Int), isSubclass T clsInt = true → xs ≠ [] →
    (∀ ms, T.members = some ms → ∀ x ∈ xs, x ∈ ms) →
    ¬ (mean (xs.map (fun i => (⟨T, .int i⟩ : PyN)))).raises "ValueError"

/-- `class Level(IntEnum): LOW = 1; HIGH = 3`. -/
def clsLevel : Cls := ⟨"Level", ["Level", "IntEnum", "int"], some [1, 3]⟩

/-- `mean([Level.LOW, Level.HIGH])` is 2, and `_convert` calls `Level(Fraction(2, 1))`. -/
theorem meanIntSubclass_refuted : ¬MeanIntSubclass := by
  intro h
  refine h clsLevel [1, 3] (by decide) (by simp) ?_ ⟨.valueError "~Fraction(2, 1) is not a valid Level", ?_, rfl⟩
  · intro ms hms x hx
    simp only [clsLevel, Option.some.injEq] at hms
    subst hms
    exact hx
  · decide +kernel

/-! ## `_fail_neg` -/

theorem vltPy_frac (q : Rat) : vltPy (.frac q) (.int 0) = .ok (decide (q < 0)) := by
  have : (((0 : Int) : Rat)) = 0 := rfl
  simp [vltPy, vlt, Val.ordered, Val.ext, Ext.lt, this]

/-- `_fail_neg` passes the values through when none is negative and otherwise raises
`StatisticsError(errmsg)`, whatever comes before or after the negative value. -/
def FailNegSpec : Prop :=
  ∀ (qs : List Rat) (msg : String),
    ((∀ q ∈ qs, 0 ≤ q) → failNeg (qs.map .frac) msg = .ok (qs.map .frac)) ∧
    ((∃ q ∈ qs, q < 0) → failNeg (qs.map .frac) msg = .error (statErr msg))

theorem failNegSpec_proven : FailNegSpec := by
  intro qs msg
  constructor
  · intro h
    unfold failNeg
    have := mapM_ok (fun (x : Val) => (do
      if ← vltPy x (.int 0) then Except.error (statErr msg) else Except.ok x : Py Val)) id
      (qs.map Val.frac) (by
        intro x hx
        simp only [List.mem_map] at hx
        obtain ⟨q, hq, rfl⟩ := hx
        have : ¬ q < 0 := by have := h q hq; grind
        simp [vltPy_frac, this, bind, Except.bind])
    simpa using this
  · rintro ⟨q0, hq0, hneg⟩
    unfold failNeg
    induction qs with
    | nil => simp at hq0
    | cons a as ih =>
      simp only [List.map_cons, List.mapM_cons]
      by_cases ha : a < 0
      · simp [vltPy_frac, ha, bind, Except.bind]
      · rcases List.mem_cons.mp hq0 with rfl | hm
        · exact absurd hneg ha
        · have := ih hm
          simp only [vltPy_frac, ha, decide_false, bind, Except.bind, Bool.false_eq_true, if_false]
          simp only [bind, Except.bind] at this
          rw [this]

/-! ## `harmonic_mean` -/

def hmBody (errmsg : String) (st : SumSt) (p : Val × Val) : Py SumSt := do
  let (w, x) := p
  if ← vltPy x (.int 0) then throw (statErr errmsg)
  let term ← if w.truthy then vdiv w x else pure (.int 0)
  sumStep st term.toN

theorem vdiv_one (q : Rat) (h : q ≠ 0) : vdiv (.int 1) (.frac q) = .ok (.frac (1 / q)) := by
  simp only [vdiv, arith, divOp]
  rw [if_neg h]
  rfl

theorem hmBody_pos (msg : String) (st : SumSt) (q : Rat) (h : 0 < q) :
    hmBody msg st (.int 1, .frac q) = sumStep st (Val.frac (1 / q)).toN := by
  have hq : q ≠ 0 := by grind
  have hn : ¬ q < 0 := by grind
  simp only [hmBody, bind, Except.bind, vltPy_frac, hn, decide_false, Bool.false_eq_true, if_false]
  rw [if_pos (show (Val.int 1).truthy = true by decide)]
  simp [vdiv_one q hq]

theorem hm_fold (msg : String) (qs : List Rat) (st : SumSt) (h : ∀ q ∈ qs, 0 < q) :
    ((List.replicate qs.length (Val.int 1)).zip (qs.map .frac)).foldlM (hmBody msg) st =
      (fracs (qs.map (fun q => 1 / q))).foldlM sumStep st := by
  induction qs generalizing st with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.replicate_succ, List.map_cons, List.zip_cons_cons,
      List.foldlM_cons, fracs]
    rw [hmBody_pos msg st a (h a (by simp))]
    simp only [bind, Except.bind]
    cases sumStep st (Val.frac (1 / a)).toN with
    | error e => rfl
    | ok st' =>
      simpa [fracs] using ih st' (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem hmSum_eq (ws data : List Val) (msg : String) :
    hmSum ws data msg = (do sumFinish id (← (ws.zip data).foldlM (hmBody msg) ({} : SumSt))) := rfl

theorem sumQ_pos (l : List Rat) (hne : l ≠ []) (h : ∀ q ∈ l, 0 < q) : 0 < sumQ l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a as ih =>
    have ha := h a (by simp)
    cases as with
    | nil => simp only [sumQ, List.foldr_cons, List.foldr_nil]; grind
    | cons b bs =>
      have := ih (by simp) (fun q hq => h q (List.mem_cons_of_mem _ hq))
      rw [sumQ_cons]
      grind

theorem one_div_pos (q : Rat) (h : 0 < q) : 0 < 1 / q := by
  rw [Rat.div_def]
  have : 0 < q⁻¹ := Rat.inv_pos.mpr h
  grind

theorem vlePy_frac_pos (t : Rat) (h : 0 < t) : vlePy (.frac t) (.int 0) = .ok false := by
  have e0 : (((0 : Int) : Rat)) = 0 := rfl
  have h1 : ¬ t < 0 := by grind
  have h2 : ¬ t = 0 := by grind
  simp [vlePy, vltPy_frac, h1, bind, Except.bind, veq, Val.ext, e0, h2, pure, Except.pure]

theorem harmonicMean_general (data : List PyN) (h : 2 ≤ data.length) :
    harmonicMean data none = hmGeneral data none := by
  match data, h with
  | a :: b :: rest, _ =>
    simp only [harmonicMean, List.length_cons, bind, Except.bind]
    rw [if_neg (by omega)]

theorem fracs_vals (qs : List Rat) : (fracs qs).map (·.v) = qs.map .frac := by
  simp [fracs, List.map_map, Function.comp_def, Val.toN]

/-- For two or more positive `Fraction`s, `harmonic_mean` is the exact reciprocal of the mean of the
reciprocals, `n / Σ(1/x)` (the docstring's definition); a single non-negative value is returned as
it is. Empty data raises. -/
def HarmonicMeanExact : Prop :=
  (∀ qs : List Rat, 2 ≤ qs.length → (∀ q ∈ qs, 0 < q) →
    harmonicMean (fracs qs) none =
      .ok (Val.frac ((qs.length : Rat) / sumQ (qs.map (fun q => 1 / q)))).toN) ∧
  (∀ q : Rat, 0 ≤ q → harmonicMean (fracs [q]) none = .ok (Val.frac q).toN) ∧
  harmonicMean [] none = .error (.named "StatisticsError" "harmonic_mean requires at least one data point")

theorem harmonicMeanExact_proven : HarmonicMeanExact := by
  refine ⟨?_, ?_, by decide⟩
  · intro qs h2 hpos
    have hne : qs ≠ [] := by
      intro h; simp [h] at h2
    have hne2 : qs.map (fun q => 1 / q) ≠ [] := by simpa using hne
    have hs := sum_fracs (qs.map (fun q => 1 / q)) hne2
    have hsum : hmSum (List.replicate qs.length (Val.int 1)) (qs.map .frac) hmErrmsg =
        .ok (clsFraction, .frac (sumQ (qs.map (fun q => 1 / q))), qs.length) := by
      rw [hmSum_eq, hm_fold _ _ _ hpos]
      simpa [sumOf] using hs
    have ht : 0 < sumQ (qs.map (fun q => 1 / q)) := by
      apply sumQ_pos _ hne2
      intro r hr
      simp only [List.mem_map] at hr
      obtain ⟨q, hq, rfl⟩ := hr
      exact one_div_pos q (hpos q hq)
    generalize sumQ (qs.map (fun q => 1 / q)) = t at hsum ht
    have hd : vdiv (.int qs.length) (.frac t) = .ok (.frac ((qs.length : Rat) / t)) := by
      simp only [vdiv, arith, divOp]
      rw [if_neg (by grind)]
      rfl
    have hlen : (fracs qs).length = qs.length := by simp [fracs]
    rw [harmonicMean_general _ (by omega)]
    simp only [hmGeneral, bind, Except.bind, pure, Except.pure, fracs_vals, hlen, hsum]
    simp only [vlePy_frac_pos t ht, Bool.false_eq_true, if_false, hd]
    rfl
  · intro q h
    have hn : ¬ q < 0 := by grind
    simp [harmonicMean, fracs, Val.toN, Val.cls, vltPy_frac, hn, bind, Except.bind, pure, Except.pure]

theorem sumStep_exact_ok (st : SumSt) (x : PyN) (h : IsExact x.v) : ∃ st', sumStep st x = .ok st' := by
  simp only [sumStep, bind, Except.bind, exactRatio_exact x.v h, pure, Except.pure]
  exact ⟨_, rfl⟩

/-- Zero short-circuits, by design (bpo-38382, gh-82563, where the behaviour was discussed and
kept): a zero met before any negative value gives 0 whatever follows it, even a negative value or
a value of no numeric type; a negative value met before any zero raises. -/
def HarmonicEarlyOut : Prop :=
  ∀ (pre : List Rat) (rest : List PyN), (∀ q ∈ pre, 0 < q) →
    (rest ≠ [] ∨ pre ≠ []) →
    harmonicMean (fracs pre ++ (Val.frac 0).toN :: rest) none = .ok (Val.int 0).toN ∧
    ∀ a : Rat, a < 0 →
      harmonicMean (fracs pre ++ (Val.frac a).toN :: rest) none =
        .error (.named "StatisticsError" "harmonic mean does not support negative values")

theorem hm_fold_stop (qs : List Rat) (x : Val) (rest ws : List Val) (st : SumSt) (e : PyExc)
    (h : ∀ q ∈ qs, 0 < q)
    (hstop : ∀ st', hmBody hmErrmsg st' (.int 1, x) = .error e) :
    ((List.replicate qs.length (Val.int 1) ++ (.int 1) :: ws).zip (qs.map .frac ++ x :: rest)).foldlM
      (hmBody hmErrmsg) st = .error e := by
  induction qs generalizing st with
  | nil => simp [List.foldlM_cons, hstop, bind, Except.bind]
  | cons a as ih =>
    simp only [List.length_cons, List.replicate_succ, List.cons_append, List.map_cons,
      List.zip_cons_cons, List.foldlM_cons]
    rw [hmBody_pos _ st a (h a (by simp))]
    obtain ⟨st', hst⟩ := sumStep_exact_ok st (Val.frac (1 / a)).toN trivial
    simp only [bind, Except.bind, hst]
    exact ih st' (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem harmonicEarlyOut_proven : HarmonicEarlyOut := by
  intro pre rest hpos hlen
  have hL : 2 ≤ (fracs pre ++ (Val.frac 0).toN :: rest).length := by
    simp only [fracs, List.length_append, List.length_map, List.length_cons]
    rcases hlen with h | h
    · have := List.length_pos_iff.mpr h; omega
    · have := List.length_pos_iff.mpr h; omega
  have hvals : ∀ a : Rat, (fracs pre ++ (Val.frac a).toN :: rest).map (·.v) =
      pre.map .frac ++ .frac a :: rest.map (·.v) := by
    intro a
    simp only [List.map_append, fracs_vals, List.map_cons]
    rfl
  have hrep : ∀ a : Rat, List.replicate (fracs pre ++ (Val.frac a).toN :: rest).length (Val.int 1) =
      List.replicate pre.length (Val.int 1) ++ (Val.int 1) :: List.replicate rest.length (Val.int 1) := by
    intro a
    simp only [fracs, List.length_append, List.length_map, List.length_cons]
    rw [← List.replicate_succ, List.replicate_append_replicate]
  have htruth : (Val.int 1).truthy = true := by decide
  constructor
  · have hstop : ∀ st', hmBody hmErrmsg st' (.int 1, .frac 0) = .error (.zeroDivisionError "~Fraction(n, 0)") := by
      intro st'
      have hn : ¬ ((0 : Rat) < 0) := by decide
      have hv : vdiv (.int 1) (.frac 0) = .error (.zeroDivisionError "~Fraction(n, 0)") := rfl
      simp only [hmBody, bind, Except.bind, vltPy_frac, hn, decide_false, Bool.false_eq_true,
        if_false, htruth, if_true, hv]
    have hsum := hm_fold_stop pre (.frac 0) (rest.map (·.v)) (List.replicate rest.length (Val.int 1)) {}
      _ hpos hstop
    rw [harmonicMean_general _ hL]
    simp only [hmGeneral, bind, Except.bind, pure, Except.pure, hvals, hrep, hmSum_eq, hsum]
    rfl
  · intro a ha
    have hL' : 2 ≤ (fracs pre ++ (Val.frac a).toN :: rest).length := by
      simpa [fracs] using hL
    have hstop : ∀ st', hmBody hmErrmsg st' (.int 1, .frac a) = .error (statErr hmErrmsg) := by
      intro st'
      simp only [hmBody, bind, Except.bind, vltPy_frac, ha, decide_true, if_true]
      rfl
    have hsum := hm_fold_stop pre (.frac a) (rest.map (·.v)) (List.replicate rest.length (Val.int 1)) {}
      _ hpos hstop
    rw [harmonicMean_general _ hL']
    simp only [hmGeneral, bind, Except.bind, pure, Except.pure, hvals, hrep, hmSum_eq, hsum]
    rfl

/-! ## `_integer_sqrt_of_frac_rto` -/

/-- `_integer_sqrt_of_frac_rto(n, m)` for `n >= 0`, `m > 0` is the floor `a` of the exact square
root of `n/m`, with the low bit forced to 1 when the root is inexact: the round-to-odd of the
reference cited at statistics.py:1708, which is what makes the later rounding to `float` correct. -/
def IntegerSqrtRto : Prop :=
  ∀ n m : Int, 0 ≤ n → 0 < m →
    ∃ a : Int, 0 ≤ a ∧ a * a * m ≤ n ∧ n < (a + 1) * (a + 1) * m ∧
      integerSqrtOfFracRto n m =
        .ok (if a * a * m ≠ n then ((a.toNat ||| 1 : Nat) : Int) else a)

theorem integerSqrtRto_proven : IntegerSqrtRto := by
  intro n m hn hm
  have hq : 0 ≤ n / m := Int.ediv_nonneg hn (by omega)
  obtain ⟨k, hk⟩ : ∃ k : Nat, n / m = k := ⟨(n / m).toNat, by omega⟩
  obtain ⟨r, h1, h2, h3⟩ := MathInt.isqrtFloorSqrt_proven k
  refine ⟨r, by omega, ?_, ?_, ?_⟩
  · have h4 : ((r * r : Nat) : Int) ≤ n / m := by rw [hk]; exact_mod_cast h2
    have := (Int.le_ediv_iff_mul_le hm).mp h4
    simpa using this
  · have h4 : n / m < (((r + 1) * (r + 1) : Nat) : Int) := by rw [hk]; exact_mod_cast h3
    have := (Int.ediv_lt_iff_lt_mul hm).mp h4
    simpa using this
  · simp only [integerSqrtOfFracRto, isqrtInt, bind, Except.bind, hk, h1, pure, Except.pure]
    show (Except.ok _ : Py Int) = _
    simp

end PyLean.CoreLibs.CalStat
