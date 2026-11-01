import PyLean.CoreLibs.Functools.Model

/-!
Properties of `functools` and `_functools`, part one: `reduce`, `total_ordering`, `cmp_to_key`,
`partial` argument handling.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-! ### `reduce` -/

theorem reduceCLoop_some {α : Type} (f : α → α → Py α) : ∀ (v : α) (xs : List α)
    (e : Option PyExc), reduceCLoop f (some v) xs e = reduceLoop f v xs e
  | v, [], none => rfl
  | v, [], some _ => rfl
  | v, x :: xs, e => by
    simp only [reduceCLoop, reduceLoop, bind, Except.bind]
    cases f v x with
    | error _ => rfl
    | ok r => exact reduceCLoop_some f r xs e

/-- `Except`-monadic left fold. -/
def foldlPy {α : Type} (f : α → α → Py α) : α → List α → Py α
  | v, [] => .ok v
  | v, x :: xs => do foldlPy f (← f v x) xs

theorem reduceLoop_fold {α : Type} (f : α → α → Py α) : ∀ (v : α) (xs : List α),
    reduceLoop f v xs none = foldlPy f v xs
  | _, [] => rfl
  | v, x :: xs => by
    simp only [reduceLoop, foldlPy, bind, Except.bind]
    cases f v x with
    | error _ => rfl
    | ok r => exact reduceLoop_fold f r xs

/-- `reduce` in C and in Python agree on every iterable, with or without `initial`, for any
function and any iterator that may raise; both compute the left fold; an empty iterable without
`initial` raises `TypeError`. A non-iterable raises `TypeError` in both, with different messages.
Docstring of `reduce`. -/
def ReduceTwins : Prop :=
  ∀ (α : Type) (f : α → α → Py α) (xs : List α) (e : Option PyExc) (i : Option α),
    reduceC f (.iter xs e) i = reducePy f (.iter xs e) i ∧
    (∀ v, reduceC f (.iter xs none) (some v) = foldlPy f v xs) ∧
    (∀ x rest, xs = x :: rest → reduceC f (.iter xs none) none = foldlPy f x rest) ∧
    reduceC f (.iter [] none) none = .error emptyReduce ∧
    (reduceC f .notIterable i).raises "TypeError" ∧ (reducePy f .notIterable i).raises "TypeError"

theorem reduceTwins_proven : ReduceTwins := by
  intro α f xs e i
  refine ⟨?_, ?_, ?_, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  · cases i with
    | some v => exact reduceCLoop_some f v xs e
    | none =>
      cases xs with
      | nil => cases e <;> rfl
      | cons x rest => exact reduceCLoop_some f x rest e
  · intro v
    simp only [reduceC, reduceCLoop_some, reduceLoop_fold]
  · intro x rest h
    subst h
    simp only [reduceC, reduceCLoop, reduceCLoop_some, reduceLoop_fold]

/-! ### `total_ordering` -/

/-- The truth of a comparison under a strict order `lt`. -/
def truthOf {α : Type} [DecidableEq α] (lt : α → α → Bool) (o : OrdOp) (a b : α) : Bool :=
  match o with
  | .lt => lt a b
  | .le => lt a b || decide (a = b)
  | .gt => lt b a
  | .ge => lt b a || decide (a = b)

/-- The class's operators, with the root taken from a total order. -/
def primsOf {α : Type} [DecidableEq α] (lt : α → α → Bool) (root : OrdOp) : OrdPrims α :=
  ⟨fun a b => .ok (.val (truthOf lt root a b)), fun a b => .ok (decide (a = b)),
    fun a b => .ok (!decide (a = b))⟩

/-- `lt` is a strict total order: the documented precondition of `total_ordering` ("The class must
define ... one of `__lt__`, `__le__`, `__gt__`, or `__ge__`", with the total-order reading in the
docs' note). -/
structure StrictTotal {α : Type} (lt : α → α → Bool) : Prop where
  irrefl : ∀ a, lt a a = false
  asymm : ∀ a b, lt a b = true → lt b a = false
  total : ∀ a b, a ≠ b → lt a b = true ∨ lt b a = true

/-- Each of the twelve generated methods gives the right answer for a totally ordered class,
from each root, and each passes `NotImplemented` from the root straight through. -/
def TotalOrderingCorrect : Prop :=
  ∀ (α : Type) [DecidableEq α] (lt : α → α → Bool), StrictTotal lt →
    ∀ (root o : OrdOp) (s : Shape) (a b : α), (o, s) ∈ convert root →
      derived (primsOf lt root) s a b = .ok (.val (truthOf lt o a b)) ∧
      derived { primsOf lt root with root := fun _ _ => .ok .notImplemented } s a b =
        .ok .notImplemented

theorem totalOrderingCorrect_proven : TotalOrderingCorrect := by
  intro α _ lt hlt root o s a b hmem
  refine ⟨?_, by cases s <;> rfl⟩
  have c1 : lt a b = true → lt b a = false := hlt.asymm a b
  have c2 : decide (a = b) = true → lt a b = false ∧ lt b a = false := by
    intro h
    have : a = b := by simpa using h
    subst this
    exact ⟨hlt.irrefl a, hlt.irrefl a⟩
  have c3 : decide (a = b) = false → lt a b = true ∨ lt b a = true := by
    intro h
    exact hlt.total a b (by simpa using h)
  cases root <;> simp only [convert, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem <;>
    rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [derived, primsOf, truthOf, bind, Except.bind, pure, Except.pure, Functor.map,
      Except.map] <;>
    cases hx : lt a b <;> cases hy : lt b a <;> cases he : decide (a = b) <;> simp_all

/-- `total_ordering` raises `ValueError` with no root, picks `__lt__` before `__le__` before
`__gt__` before `__ge__`, and adds exactly the comparisons that are missing, so a class ends up
with all four. Docstring: "fills in missing ordering methods". -/
def TotalOrderingFills : Prop :=
  (totalOrdering [] = .error (.valueError
    "must define at least one ordering operation: < > <= >=")) ∧
  ∀ roots : List OrdOp, roots ≠ [] → ∃ root added,
    totalOrdering roots = .ok (root, added) ∧ root ∈ roots ∧
    ∀ o : OrdOp, (o ∈ roots ∨ o ∈ added.map Prod.fst)

theorem totalOrderingFills_proven : TotalOrderingFills := by
  refine ⟨rfl, ?_⟩
  intro roots hne
  have hex : ∃ o, o ∈ roots := by
    cases roots with
    | nil => exact absurd rfl hne
    | cons a _ => exact ⟨a, by simp⟩
  have all : ∀ r : OrdOp, ∀ o : OrdOp, o = r ∨ o ∈ (convert r).map Prod.fst := by
    intro r o
    cases r <;> cases o <;> simp [convert]
  by_cases h1 : OrdOp.lt ∈ roots
  · refine ⟨.lt, _, by simp [totalOrdering, maxRoot, h1]; rfl, h1, ?_⟩
    intro o
    by_cases ho : o ∈ roots
    · exact Or.inl ho
    · right
      rcases all .lt o with rfl | h
      · exact absurd h1 ho
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨p, by simp [hp, ho], rfl⟩
  by_cases h2 : OrdOp.le ∈ roots
  · refine ⟨.le, _, by simp [totalOrdering, maxRoot, h1, h2]; rfl, h2, ?_⟩
    intro o
    by_cases ho : o ∈ roots
    · exact Or.inl ho
    · right
      rcases all .le o with rfl | h
      · exact absurd h2 ho
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨p, by simp [hp, ho], rfl⟩
  by_cases h3 : OrdOp.gt ∈ roots
  · refine ⟨.gt, _, by simp [totalOrdering, maxRoot, h1, h2, h3]; rfl, h3, ?_⟩
    intro o
    by_cases ho : o ∈ roots
    · exact Or.inl ho
    · right
      rcases all .gt o with rfl | h
      · exact absurd h3 ho
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
        exact List.mem_map.mpr ⟨p, by simp [hp, ho], rfl⟩
  have h4 : OrdOp.ge ∈ roots := by
    obtain ⟨o, ho⟩ := hex
    cases o
    · exact absurd ho h1
    · exact absurd ho h2
    · exact absurd ho h3
    · exact ho
  refine ⟨.ge, _, by simp [totalOrdering, maxRoot, h1, h2, h3, h4]; rfl, h4, ?_⟩
  intro o
  by_cases ho : o ∈ roots
  · exact Or.inl ho
  · right
    rcases all .ge o with rfl | h
    · exact absurd h4 ho
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨p, by simp [hp, ho], rfl⟩

/-! ### `cmp_to_key` -/

/-- `cmp_to_key` in C and in Python compare two key objects identically, for all six operators,
including `!=`, and any `mycmp`, which may raise. Comparing with something that is not a key object
raises in both, `TypeError` in C and `AttributeError` in Python. Twin property. -/
def CmpToKeyTwins : Prop :=
  ∀ (α : Type) (mycmp : α → α → Py Int) (op : CmpOp) (x y : α),
    keyCompareC mycmp op x (some y) = keyComparePy mycmp op x (some y) ∧
    (keyCompareC mycmp op x none).raises "TypeError" ∧
    (keyComparePy mycmp op x none).raises "AttributeError"

theorem cmpToKeyTwins_proven : CmpToKeyTwins := by
  intro α mycmp op x y
  refine ⟨?_, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
  cases op <;> simp only [keyCompareC, keyComparePy]
  cases h : mycmp x y with
  | error e => rfl
  | ok r =>
    simp only [bind, Except.bind, pure, Except.pure, CmpOp.test]
    simp

/-- `K(a) < K(b)` follows the sign of `mycmp(a, b)`, for all six operators. `cmp_to_key` docs. -/
def CmpToKeySign : Prop :=
  ∀ (α : Type) (mycmp : α → α → Py Int) (x y : α) (r : Int), mycmp x y = .ok r →
    keyCompareC mycmp .lt x (some y) = .ok (decide (r < 0)) ∧
    keyCompareC mycmp .le x (some y) = .ok (decide (r ≤ 0)) ∧
    keyCompareC mycmp .eq x (some y) = .ok (decide (r = 0)) ∧
    keyCompareC mycmp .ne x (some y) = .ok (decide (r ≠ 0)) ∧
    keyCompareC mycmp .gt x (some y) = .ok (decide (r > 0)) ∧
    keyCompareC mycmp .ge x (some y) = .ok (decide (r ≥ 0))

theorem cmpToKeySign_proven : CmpToKeySign := by
  intro α mycmp x y r h
  simp [keyCompareC, h, bind, Except.bind, pure, Except.pure, CmpOp.test]

/-! ### `partial` -/

/-- A `partial` object is well formed: `phcount` counts the stored placeholders, and the last
stored argument is not a placeholder. Type invariant: `partial_new` and `__setstate__` enforce both. -/
def PWf {α : Type} (args : List (PArg α)) (ph : Nat) : Prop :=
  ph = phCount args ∧ trailingPh args = false

theorem phCount_fill {α : Type} : ∀ (p n : List (PArg α)),
    phCount (fill p n) = phCount p - min (phCount p) n.length + phCount n
  | [], n => by simp [fill, phCount]
  | .ph :: rest, [] => by
    have ih := phCount_fill rest ([] : List (PArg α))
    simp only [phCount, fill, List.filter_cons, isPh, ite_true, List.length_cons, List.length_nil,
      List.filter_nil] at ih ⊢
    omega
  | .ph :: rest, m :: n => by
    have ih := phCount_fill rest n
    cases m <;> simp only [phCount, fill, List.filter_cons, isPh, Bool.false_eq_true, ite_true,
      ite_false, List.length_cons] at ih ⊢ <;> omega
  | .val a :: rest, n => by
    have ih := phCount_fill rest n
    cases n <;> simpa only [phCount, fill, List.filter_cons, isPh, Bool.false_eq_true, ite_false]
      using ih

theorem fill_no_ph {α : Type} : ∀ (p n : List (PArg α)), phCount p = 0 → fill p n = p ++ n
  | [], _, _ => rfl
  | .ph :: _, _, h => by simp [phCount, List.filter_cons, isPh] at h
  | .val a :: rest, n, h => by
    have h' : phCount rest = 0 := by simpa [phCount, List.filter_cons, isPh] using h
    cases n <;> simp [fill, fill_no_ph rest _ h']

/-- `partial(func, *args, **kw)` builds the same object in C and in Python whenever `func` is not a
`partial` with a `__dict__`: same function, same arguments, same keywords, same placeholder count,
for nested partials, for placeholders on both sides, and the same exception for each rejected
call. Well-formedness of the wrapped `partial` is a type invariant. -/
def PartialNewTwins : Prop :=
  ∀ (α : Type) (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α)),
    (∀ o g pargs pkw ph, func = .pobj o true g pargs pkw ph → False) →
    (∀ o d g pargs pkw ph, func = .pobj o d g pargs pkw ph → PWf pargs ph) →
    partialNewC outer func args kw = partialNewPy outer func args kw

theorem phCount_append {α : Type} (a b : List (PArg α)) :
    phCount (a ++ b) = phCount a + phCount b := by
  simp [phCount]

theorem flattenTwins {α : Type} (outer : Option Nat) (o : Option Nat) (g : Fn α)
    (pargs args : List (PArg α)) (pkw kw : List (String × α)) (ph : Nat) (h : ph = phCount pargs) :
    flattenC outer (.pobj o false g pargs pkw ph) args kw =
      flattenPy outer (.pobj o false g pargs pkw ph) args kw := by
  subst h
  cases hn : args with
  | nil =>
    simp [flattenC, flattenPy, phCount]
  | cons a rest =>
    by_cases h0 : phCount pargs = 0
    · simp [flattenC, flattenPy, h0, phCount_append]
    · have hp : phCount pargs > 0 := by omega
      simp only [flattenC, flattenPy, hp, h0, List.isEmpty_cons, Bool.false_eq_true, ite_false,
        Bool.not_false, and_self, ite_true, phCount_fill]

theorem partialNewTwins_proven : PartialNewTwins := by
  intro α outer func args kw hd hwf
  simp only [partialNewC, partialNewPy, bind, Except.bind, pure, Except.pure]
  cases validateNew func args kw with
  | error e => rfl
  | ok kw' =>
    simp only
    cases func with
    | base id => rfl
    | notCallable => rfl
    | pobj o d g pargs pkw ph =>
      cases d with
      | true => exact (hd _ _ _ _ _ rfl).elim
      | false =>
        rw [flattenTwins outer o g pargs args pkw kw' ph (hwf _ _ _ _ _ _ rfl).1]

/-- `partial(p, *args)` is the same object in both twins for every wrapped object. False: when the
wrapped `partial` has an instance `__dict__`, C keeps it as `func` and Python flattens it. -/
def PartialNewTwinsAlways : Prop :=
  ∀ (func : Fn Nat) (args : List (PArg Nat)),
    partialNewC none func args [] = partialNewPy none func args []

theorem partialNewTwinsAlways_refuted : ¬PartialNewTwinsAlways := by
  intro h
  have := h (.pobj none true (.base 0) [] [] 0) []
  simp [partialNewC, partialNewPy, validateNew, trailingPh, kwVals, Fn.isCallable, flattenC, flattenPy,
    bind, Except.bind, pure, Except.pure] at this

end PyLean.CoreLibs.Functools
