import PyLean.CoreLibs.CalStat.Dist
import PyLean.CoreLibs.CalStat.CalMiscProps

/-! Supporting lemmas for the `statistics` properties: on data whose values are finite, `_sum` and
`_ss` compute exact rational sums, whatever the types and denominators. -/

namespace PyLean.CoreLibs.CalStat

open PyLean

/-- A finite numeric value, the inputs on which `_exact_ratio` returns a true ratio. -/
def IsExact : Val → Prop
  | .int _ | .frac _ | .flt (.zero _) | .flt (.fin _) | .dec (.fin _) => True
  | _ => False

/-- The exact value of a finite number. -/
def exactQ : Val → Rat
  | .int i => (i : Rat)
  | .frac q => q
  | .flt (.fin q) => q
  | .dec (.fin q) => q
  | _ => 0

theorem exactRatio_exact (v : Val) (h : IsExact v) :
    exactRatio v = .ok (.ratio (exactQ v).num (exactQ v).den) := by
  match v, h with
  | .int i, _ => rfl
  | .frac q, _ => rfl
  | .flt (.zero _), _ => rfl
  | .flt (.fin q), _ => rfl
  | .dec (.fin q), _ => rfl

/-- `sum(xs)` on rationals. -/
def sumQ (l : List Rat) : Rat := l.foldr (· + ·) 0

theorem sumQ_cons (a : Rat) (l : List Rat) : sumQ (a :: l) = a + sumQ l := rfl

theorem sumQ_append (a b : List Rat) : sumQ (a ++ b) = sumQ a + sumQ b := by
  induction a with
  | nil =>
    simp only [List.nil_append, sumQ, List.foldr_nil]
    grind
  | cons x xs ih =>
    simp only [List.cons_append, sumQ_cons, ih]
    grind

theorem mkRat_add_same (a b : Int) (d : Nat) (hd : d ≠ 0) :
    mkRat (a + b) d = mkRat a d + mkRat b d := by
  rw [Rat.mkRat_add_mkRat _ _ hd hd]
  have hd2 : d * d ≠ 0 := Nat.mul_ne_zero hd hd
  have : mkRat (a * d + b * d) (d * d) = mkRat ((a + b) * d) (d * d) := by
    rw [Int.add_mul]
  rw [this, Rat.mkRat_mul_right hd]

theorem sumPartials_add (ps : List (Nat × Int)) (d : Nat) (n : Int) (hd : d ≠ 0)
    (hps : ∀ p ∈ ps, p.1 ≠ 0) :
    sumPartials (addPartial ps d n) = sumPartials ps + mkRat n d := by
  induction ps with
  | nil =>
    simp only [addPartial, sumPartials, List.foldr_cons, List.foldr_nil]
    grind
  | cons p ps ih =>
    obtain ⟨e, v⟩ := p
    simp only [addPartial]
    split
    · rename_i he
      subst he
      simp only [sumPartials, List.foldr_cons]
      rw [mkRat_add_same _ _ _ hd]
      grind
    · have ih' := ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
      simp only [sumPartials, List.foldr_cons] at ih' ⊢
      rw [ih']
      grind

theorem addPartial_ne (ps : List (Nat × Int)) (d : Nat) (n : Int) (hd : d ≠ 0)
    (hps : ∀ p ∈ ps, p.1 ≠ 0) : ∀ p ∈ addPartial ps d n, p.1 ≠ 0 := by
  induction ps with
  | nil =>
    intro p hp
    simp only [addPartial, List.mem_singleton] at hp
    subst hp
    exact hd
  | cons q ps ih =>
    obtain ⟨e, v⟩ := q
    intro p hp
    simp only [addPartial] at hp
    split at hp
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hps (e, v) (by simp)
      · exact hps p (List.mem_cons_of_mem _ hp)
    · rcases List.mem_cons.mp hp with rfl | hp
      · exact hps (e, v) (by simp)
      · exact ih (fun p hp => hps p (List.mem_cons_of_mem _ hp)) p hp

theorem addPartial_nonempty (ps : List (Nat × Int)) (d : Nat) (n : Int) :
    (addPartial ps d n).isEmpty = false := by
  cases ps with
  | nil => rfl
  | cons q ps =>
    obtain ⟨e, v⟩ := q
    simp only [addPartial]
    split <;> rfl

/-- The types `_sum` and `_ss` collect, in first-seen order. -/
def typesOf (st : List Cls) (data : List PyN) : List Cls :=
  data.foldl (fun ts x => addType ts x.cls) st

theorem sum_fold (data : List PyN) (hd : ∀ x ∈ data, IsExact x.v) (st : SumSt)
    (hs : st.special = none) (hp : ∀ p ∈ st.partials, p.1 ≠ 0) :
    ∃ P, data.foldlM sumStep st =
        .ok { count := st.count + data.length, types := typesOf st.types data,
              partials := P, special := none } ∧
      sumPartials P = sumPartials st.partials + sumQ (data.map (fun x => exactQ x.v)) ∧
      (data ≠ [] → P.isEmpty = false) ∧ (data = [] → P = st.partials) ∧ ∀ p ∈ P, p.1 ≠ 0 := by
  induction data generalizing st with
  | nil =>
    refine ⟨st.partials, ?_, ?_, by simp, by simp, hp⟩
    · simp only [List.foldlM_nil, List.length_nil, Nat.add_zero, typesOf, List.foldl_nil]
      cases st
      simp_all
      rfl
    · simp [sumQ]
      grind
  | cons x xs ih =>
    have hx := hd x (by simp)
    have hxs : ∀ y ∈ xs, IsExact y.v := fun y hy => hd y (List.mem_cons_of_mem _ hy)
    have hstep : sumStep st x = .ok
        { count := st.count + 1, types := addType st.types x.cls,
          partials := addPartial st.partials (exactQ x.v).den (exactQ x.v).num, special := none } := by
      simp only [sumStep, bind, Except.bind, exactRatio_exact x.v hx, pure, Except.pure]
      cases st
      simp_all
    have hne : (exactQ x.v).den ≠ 0 := (exactQ x.v).den_nz
    obtain ⟨P, h1, h2, h3, h4, h5⟩ := ih hxs
      { count := st.count + 1, types := addType st.types x.cls,
        partials := addPartial st.partials (exactQ x.v).den (exactQ x.v).num, special := none }
      rfl (addPartial_ne _ _ _ hne hp)
    refine ⟨P, ?_, ?_, ?_, by simp, h5⟩
    · simp only [List.foldlM_cons, bind, Except.bind, hstep]
      rw [h1]
      simp only [List.length_cons, typesOf, List.foldl_cons]
      congr 2
      omega
    · rw [h2]
      simp only at *
      rw [sumPartials_add _ _ _ hne hp, Rat.mkRat_self]
      simp only [List.map_cons, sumQ_cons]
      grind
    · intro _
      cases xs with
      | nil =>
        rw [h4 rfl]
        exact addPartial_nonempty _ _ _
      | cons y ys => exact h3 (by simp)

/-- `_sum` on finite data: the exact sum, the count, and the coerced type. -/
theorem sumOf_exact (data : List PyN) (hd : ∀ x ∈ data, IsExact x.v) (hne : data ≠ [])
    (order : List Cls → List Cls) :
    sumOf data order = (fun T => (T, Val.frac (sumQ (data.map (fun x => exactQ x.v))), data.length)) <$>
      reduceCoerce (order (typesOf [] data)) := by
  obtain ⟨P, h1, h2, h3, -, -⟩ := sum_fold data hd {} rfl (by simp)
  have e1 : sumPartials P = sumQ (data.map (fun x => exactQ x.v)) := by
    rw [h2]
    simp only [sumPartials, List.foldr_nil]
    grind
  have e2 : P.isEmpty = false := h3 hne
  simp only [sumOf, bind, Except.bind, h1, sumFinish, e2, e1, Bool.false_eq_true, if_false, pure,
    Except.pure, Nat.zero_add]
  cases reduceCoerce (order (typesOf [] data)) <;> rfl

/-! ### `_ss` -/

theorem sumPartialsSq_add (ps : List (Nat × Int)) (d : Nat) (n : Int) (hd : d ≠ 0)
    (hps : ∀ p ∈ ps, p.1 ≠ 0) :
    sumPartialsSq (addPartial ps d n) = sumPartialsSq ps + mkRat n (d * d) := by
  have hdd : d * d ≠ 0 := Nat.mul_ne_zero hd hd
  induction ps with
  | nil =>
    simp only [addPartial, sumPartialsSq, List.foldr_cons, List.foldr_nil]
    grind
  | cons p ps ih =>
    obtain ⟨e, v⟩ := p
    simp only [addPartial]
    split
    · rename_i he
      subst he
      simp only [sumPartialsSq, List.foldr_cons]
      rw [mkRat_add_same _ _ _ hdd]
      grind
    · have ih' := ih (fun p hp => hps p (List.mem_cons_of_mem _ hp))
      simp only [sumPartialsSq, List.foldr_cons] at ih' ⊢
      rw [ih']
      grind

theorem mkRat_sq (q : Rat) : mkRat (q.num * q.num) (q.den * q.den) = q * q := by
  rw [← Rat.mkRat_mul_mkRat, Rat.mkRat_self]

theorem ss_fold (data : List PyN) (hd : ∀ x ∈ data, IsExact x.v) (st : SsSt)
    (hs : st.specialX = none) (hp : ∀ p ∈ st.sx, p.1 ≠ 0) (hp2 : ∀ p ∈ st.sxx, p.1 ≠ 0) :
    ∃ P Q, data.foldlM ssStep st =
        .ok { count := st.count + data.length, types := typesOf st.types data,
              sx := P, sxx := Q, specialX := none } ∧
      sumPartials P = sumPartials st.sx + sumQ (data.map (fun x => exactQ x.v)) ∧
      sumPartialsSq Q = sumPartialsSq st.sxx + sumQ (data.map (fun x => exactQ x.v * exactQ x.v)) := by
  induction data generalizing st with
  | nil =>
    refine ⟨st.sx, st.sxx, ?_, ?_, ?_⟩
    · simp only [List.foldlM_nil, List.length_nil, Nat.add_zero, typesOf, List.foldl_nil]
      cases st
      simp_all
      rfl
    · simp [sumQ]
      grind
    · simp [sumQ]
      grind
  | cons x xs ih =>
    have hx := hd x (by simp)
    have hxs : ∀ y ∈ xs, IsExact y.v := fun y hy => hd y (List.mem_cons_of_mem _ hy)
    have hstep : ssStep st x = .ok
        { count := st.count + 1, types := addType st.types x.cls,
          sx := addPartial st.sx (exactQ x.v).den (exactQ x.v).num,
          sxx := addPartial st.sxx (exactQ x.v).den ((exactQ x.v).num * (exactQ x.v).num),
          specialX := none } := by
      simp only [ssStep, bind, Except.bind, exactRatio_exact x.v hx, pure, Except.pure]
      cases st
      simp_all
    have hne : (exactQ x.v).den ≠ 0 := (exactQ x.v).den_nz
    obtain ⟨P, Q, h1, h2, h3⟩ := ih hxs
      { count := st.count + 1, types := addType st.types x.cls,
        sx := addPartial st.sx (exactQ x.v).den (exactQ x.v).num,
        sxx := addPartial st.sxx (exactQ x.v).den ((exactQ x.v).num * (exactQ x.v).num),
        specialX := none } rfl (addPartial_ne _ _ _ hne hp) (addPartial_ne _ _ _ hne hp2)
    refine ⟨P, Q, ?_, ?_, ?_⟩
    · simp only [List.foldlM_cons, bind, Except.bind, hstep]
      rw [h1]
      simp only [List.length_cons, typesOf, List.foldl_cons]
      congr 2
      omega
    · rw [h2]
      simp only at *
      rw [sumPartials_add _ _ _ hne hp, Rat.mkRat_self]
      simp only [List.map_cons, sumQ_cons]
      grind
    · rw [h3]
      simp only at *
      rw [sumPartialsSq_add _ _ _ hne hp2, mkRat_sq]
      simp only [List.map_cons, sumQ_cons]
      grind

/-- `Σ (x - c)**2 = Σ x**2 - 2*c*Σ x + n*c**2`. -/
theorem sum_sq_dev (l : List Rat) (c : Rat) :
    sumQ (l.map (fun x => (x - c) * (x - c))) =
      sumQ (l.map (fun x => x * x)) - 2 * c * sumQ l + (l.length : Rat) * (c * c) := by
  induction l with
  | nil => simp [sumQ]; grind
  | cons a as ih =>
    simp only [List.map_cons, sumQ_cons, ih, List.length_cons]
    push_cast
    grind

/-- The closed form of `_ss`: `(n*Σx² - (Σx)²)/n` is the sum of squared deviations from the mean. -/
theorem ss_formula (l : List Rat) (hn : l ≠ []) :
    ((l.length : Rat) * sumQ (l.map (fun x => x * x)) - sumQ l * sumQ l) / (l.length : Rat) =
      sumQ (l.map (fun x => (x - sumQ l / (l.length : Rat)) * (x - sumQ l / (l.length : Rat)))) := by
  rw [sum_sq_dev]
  have h0 : (l.length : Rat) ≠ 0 := by
    have : l.length ≠ 0 := by simpa using hn
    simpa using this
  generalize (l.length : Rat) = n at h0 ⊢
  generalize sumQ l = S
  generalize sumQ (l.map (fun x => x * x)) = Q
  grind

end PyLean.CoreLibs.CalStat
