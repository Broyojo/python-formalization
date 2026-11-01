import PyLean.CoreLibs.Functools.Props

/-!
Properties of `functools`, part two: `partial` calls and state, `lru_cache`, `singledispatch`, and the
small helpers.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-! ### `partial` calls -/

def valsOf {α : Type} (l : List (PArg α)) : List α :=
  l.filterMap (fun a => match a with
    | .val v => some v
    | .ph => none)

theorem fillCall_no_ph {α : Type} : ∀ (p : List (PArg α)) (n : List α), phCount p = 0 →
    fillCall p n = valsOf p ++ n
  | [], _, _ => rfl
  | .ph :: _, _, h => by simp [phCount, List.filter_cons, isPh] at h
  | .val a :: rest, n, h => by
    have h' : phCount rest = 0 := by simpa [phCount, List.filter_cons, isPh] using h
    simp [fillCall, valsOf, fillCall_no_ph rest n h']

/-- A keyword dictionary has distinct keys: type invariant. -/
def KwOk {α : Type} (kw : List (String × α)) : Prop := (kw.map Prod.fst).Nodup

theorem mergeKw_nil_aux {α : Type} : ∀ (acc rest : List (String × α)),
    ((acc ++ rest).map Prod.fst).Nodup → mergeKw acc rest = acc ++ rest
  | acc, [], _ => by simp [mergeKw]
  | acc, p :: rest, h => by
    have hn : p.1 ∉ acc.map Prod.fst := by
      intro hm
      rw [List.map_append, List.map_cons, List.nodup_append] at h
      exact (h.2.2 _ hm _ (by simp)) rfl
    have hany : acc.any (fun q => q.1 == p.1) = false := by
      rw [List.any_eq_false]
      intro q hq e
      exact hn (List.mem_map.mpr ⟨q, hq, by simpa using e⟩)
    have ih := mergeKw_nil_aux (acc ++ [p]) rest (by simpa using h)
    simp only [mergeKw, List.foldl_cons, hany, Bool.false_eq_true, ite_false] at ih ⊢
    simpa using ih

theorem mergeKw_nil {α : Type} (kw : List (String × α)) (h : KwOk kw) : mergeKw [] kw = kw := by
  simpa using mergeKw_nil_aux [] kw (by simpa [KwOk] using h)

/-- The three ways of calling a `partial`, Python's `__call__`, C's `partial_call` and C's
`partial_vectorcall`, give the same call of the wrapped function, or the same `TypeError` with the
same message, for every wrapped function and every placeholder pattern. Type invariants: well-formed
`partial`, and distinct keywords in the call. -/
def PartialCallTwins : Prop :=
  ∀ (α : Type) (func : Fn α) (pargs : List (PArg α)) (pkw kw : List (String × α)) (ph : Nat)
    (args : List α), PWf pargs ph → KwOk kw →
    partialCallPy func pargs pkw ph args kw = partialCallC func pargs pkw ph args kw ∧
    partialVectorcall func pargs pkw ph args kw = partialCallC func pargs pkw ph args kw

theorem partialCallTwins_proven : PartialCallTwins := by
  intro α func pargs pkw kw ph args ⟨hph, _⟩ hk
  have hfill : ∀ (_ : ph = 0), fillCall pargs args = valsOf pargs ++ args :=
    fun h0 => fillCall_no_ph pargs args (by omega)
  have hmerge : (if pkw.isEmpty then kw else mergeKw pkw kw) = mergeKw pkw kw := by
    cases pkw with
    | nil => simp [mergeKw_nil kw hk]
    | cons _ _ => simp
  constructor
  · simp only [partialCallPy, partialCallC, hmerge]
    by_cases h0 : ph = 0
    · subst h0
      have hn : ¬ (args.length < 0) := by omega
      simp only [ne_eq, not_true_eq_false, false_and, ite_false, hn, hfill rfl]
      rfl
    · by_cases hl : args.length < ph
      · simp [h0, hl]
      · simp [h0, hl]
  · simp only [partialVectorcall, partialCallC]
    cases pkw with
    | cons p ps => simp
    | nil =>
      simp only [List.isEmpty_nil, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
      by_cases hl : args.length < ph
      · simp [hl]
      · by_cases h0 : ph = 0
        · subst h0
          simp only [hl, ite_false, ne_eq, not_true_eq_false, hfill rfl]
          rfl
        · simp [hl, h0]

/-- The result of `partial(func, *args)()` where `func` overrides `__call__`: the override runs. -/
def PartialCallsWrappedObject : Prop :=
  ∀ (func : Fn Nat) (args : List Nat) (more : List Nat),
    func.isCallable = true →
    callFn (flattenC none func (args.map PArg.val) []) more [] =
      callFn func (args ++ more) []

/-- False: both twins flatten a `partial` subclass, so its `__call__` override is never called. -/
theorem partialCallsWrappedObject_refuted : ¬PartialCallsWrappedObject := by
  intro h
  have := h (.pobj (some 77) false (.base 0) [] [] 0) [] [] rfl
  simp [flattenC, callFn, fillCall, mergeKw, phCount] at this

theorem fill_nil {α : Type} : ∀ p : List (PArg α), fill p [] = p
  | [] => rfl
  | .ph :: rest => by simp [fill, fill_nil rest]
  | .val a :: rest => by simp [fill, fill_nil rest]

theorem fillCall_fill {α : Type} : ∀ (p n : List (PArg α)) (more : List α),
    phCount n ≤ more.length → fillCall (fill p n) more = fillCall p (fillCall n more)
  | p, [], more, _ => by simp [fill_nil, fillCall]
  | [], m :: n, more, _ => by simp [fill, fillCall]
  | .val a :: rest, m :: n, more, h => by
    simp only [fill, fillCall]
    rw [fillCall_fill rest (m :: n) more h]
  | .ph :: rest, .val a :: n, more, h => by
    have h' : phCount n ≤ more.length := by
      simpa [phCount, List.filter_cons, isPh] using h
    simp only [fill, fillCall]
    rw [fillCall_fill rest n more h']
  | .ph :: rest, .ph :: n, [], h => by
    simp [phCount, List.filter_cons, isPh] at h
  | .ph :: rest, .ph :: n, x :: ms, h => by
    have h' : phCount n ≤ ms.length := by
      simpa [phCount, List.filter_cons, isPh] using h
    simp only [fill, fillCall]
    rw [fillCall_fill rest n ms h']

theorem length_fillCall {α : Type} : ∀ (a : List (PArg α)) (m : List α), phCount a ≤ m.length →
    (fillCall a m).length + phCount a = a.length + m.length
  | [], m, _ => by simp [fillCall, phCount]
  | .val v :: rest, m, h => by
    have ih := length_fillCall rest m (by simpa [phCount, List.filter_cons, isPh] using h)
    simp only [fillCall, List.length_cons, phCount, List.filter_cons, isPh, Bool.false_eq_true,
      ite_false] at ih ⊢
    omega
  | .ph :: rest, [], h => by
    simp [phCount, List.filter_cons, isPh] at h
  | .ph :: rest, x :: ms, h => by
    have ih := length_fillCall rest ms (by simpa [phCount, List.filter_cons, isPh] using h)
    simp only [fillCall, List.length_cons, phCount, List.filter_cons, isPh, ite_true] at ih ⊢
    omega

theorem phCount_le {α : Type} (a : List (PArg α)) : phCount a ≤ a.length :=
  List.length_filter_le _ _

/-- Both sides give the same call, or both raise `TypeError`. -/
def sameOrTypeError {α : Type} (a b : Py α) : Prop :=
  a = b ∨ (a.raises "TypeError" ∧ b.raises "TypeError")

/-- A `partial` of a plain `partial` behaves like the inner one called with the outer arguments in
the slots they fill: `partial(p, *args)(*more)` is `p(*filled)`, for every placeholder pattern on
both levels, where `more` covers the outer placeholders. The positional core of the docs' "roughly
equivalent" code, with no keywords at either level; a `partial` subclass overriding `__call__` is
excluded here and refuted separately. `PWf` is a type invariant. -/
def PartialNestedPositional : Prop :=
  ∀ (α : Type) (g : Fn α) (d : Bool) (pargs args : List (PArg α)) (ph : Nat) (more : List α),
    PWf pargs ph → phCount args ≤ more.length →
    sameOrTypeError (callFn (flattenPy none (.pobj none d g pargs [] ph) args []) more [])
      (callFn (.pobj none d g pargs [] ph) (fillCall args more) [])

theorem partialNestedPositional_proven : PartialNestedPositional := by
  intro α g d pargs args ph more ⟨hph, _⟩ hm
  have hlen := length_fillCall args more hm
  have hle := phCount_le args
  have hmk : mergeKw ([] : List (String × α)) [] = [] := rfl
  by_cases he : args.isEmpty = true
  · have hn : args = [] := by simpa using he
    subst hn
    left
    simp [flattenPy, fillCall, hmk, callFn]
  · have hne : args.isEmpty = false := by simpa using he
    by_cases h0 : ph = 0
    · left
      have hp : phCount pargs = 0 := by omega
      have htot : fillCall (pargs ++ args) more = fillCall pargs (fillCall args more) := by
        rw [← fillCall_fill pargs args more hm, fill_no_ph pargs args hp]
      simp only [flattenPy, hne, Bool.false_eq_true, ite_false, h0, ite_true, callFn, hmk]
      rw [phCount_append, hp, Nat.zero_add]
      have h1 : ¬ more.length < phCount args := by omega
      have h2 : ¬ (fillCall args more).length < 0 := by omega
      simp only [h1, h2, ite_false, htot, hmk]
    · have hfc := phCount_fill pargs args
      have htot := fillCall_fill pargs args more hm
      simp only [flattenPy, hne, Bool.false_eq_true, ite_false, h0, callFn, hmk]
      rw [hfc, ← hph, htot]
      by_cases hl : more.length < ph - min ph args.length + phCount args
      · have h2 : (fillCall args more).length < ph := by omega
        right
        simp only [hl, ite_true, h2]
        exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩
      · have h2 : ¬ (fillCall args more).length < ph := by omega
        left
        simp only [hl, ite_false, h2]

/-- `__setstate__` in C and Python accept the same states with the same placeholder count, and every
rejected state raises `TypeError` in both. They differ only in two messages: Python says "must be a
tuple" and "expected 4 items", C says "invalid partial state". The state from `__reduce__` is always
accepted, in both twins, so a `partial` round-trips through pickle. Type invariant: `PWf`. -/
def PartialStateTwins : Prop :=
  ∀ (α : Type) (st : PState α),
    ((∃ n, setstateC st = .ok n) ↔ (∃ n, setstatePy st = .ok n)) ∧
    (∀ n, setstateC st = .ok n → setstatePy st = .ok n) ∧
    (∀ e, setstateC st = .error e → e.className = "TypeError") ∧
    (∀ e, setstatePy st = .error e → e.className = "TypeError")

theorem setstateC_err {α : Type} (st : PState α) (e : PyExc) (h : setstateC st = .error e) :
    e.className = "TypeError" := by
  simp only [setstateC] at h
  repeat' split at h
  all_goals (cases h <;> rfl)

theorem setstatePy_err {α : Type} (st : PState α) (e : PyExc) (h : setstatePy st = .error e) :
    e.className = "TypeError" := by
  simp only [setstatePy] at h
  repeat' split at h
  all_goals (cases h <;> rfl)

theorem partialStateTwins_proven : PartialStateTwins := by
  intro α st
  have key : ∀ n, setstateC st = .ok n ↔ setstatePy st = .ok n := by
    intro n
    unfold setstateC setstatePy
    generalize (!st.callable || !st.argsTuple || (!st.kwNone && !st.kwDict) ||
      (!st.nsNone && !st.nsDict)) = b
    cases b <;> by_cases h1 : st.isTuple = true <;> by_cases h2 : st.size = 4 <;>
      by_cases h4 : trailingPh st.args = true <;> simp [h1, h2, h4]
  exact ⟨⟨fun ⟨n, h⟩ => ⟨n, (key n).mp h⟩, fun ⟨n, h⟩ => ⟨n, (key n).mpr h⟩⟩,
    fun n h => (key n).mp h, setstateC_err st, setstatePy_err st⟩

/-- A `partial` built by the constructor round-trips: the state from `__reduce__` passes
`__setstate__` in the same twin and gives back the placeholder count. -/
def PartialReduceRoundTrip : Prop :=
  ∀ (α : Type) (args : List (PArg α)) (kw : List (String × α)) (ph : Nat), PWf args ph →
    setstatePy (reduceStatePy args kw) = .ok ph ∧ setstateC (reduceStateC args) = .ok ph

theorem partialReduceRoundTrip_proven : PartialReduceRoundTrip := by
  intro α args kw ph ⟨h1, h2⟩
  subst h1
  cases hk : kw.isEmpty <;>
    simp [setstatePy, setstateC, reduceStatePy, reduceStateC, h2, hk]

/-- `Placeholder` is a singleton: a second construction returns the object of the first. Its repr
and its `__reduce__` are the name `Placeholder`, which is how it pickles by reference. -/
def PlaceholderSingleton : Prop :=
  (placeholderNew (placeholderNew none).2).1 = (placeholderNew none).1 ∧
  (placeholderNew none).1.repr = "Placeholder" ∧ (placeholderNew none).1.reduce = "Placeholder"

theorem placeholderSingleton_proven : PlaceholderSingleton := ⟨rfl, rfl, rfl⟩

/-- `_unwrap_partial` removes every `partial` layer, whatever the nesting. -/
def UnwrapRemovesPartials : Prop :=
  ∀ (α : Type) (f : Fn α), ∀ o d g a k p, unwrapPartial f ≠ .pobj o d g a k p

theorem unwrapRemovesPartials_proven : UnwrapRemovesPartials := by
  intro α f
  induction f with
  | base id => intro _ _ _ _ _ _; simp [unwrapPartial]
  | notCallable => intro _ _ _ _ _ _; simp [unwrapPartial]
  | pobj o d g a k p ih => simpa [unwrapPartial] using ih

/-- `obj.method(*args)` through `partialmethod` puts `obj` first and then the stored and call
arguments in their slots, whichever branch of `__get__` runs; both branches agree except for the
function name in the `TypeError`. `__isabstractmethod__` defaults to `False`. Docs of
`partialmethod`. -/
def PartialmethodBranches : Prop :=
  ∀ (α : Type) (id ph : Nat) (pargs : List (PArg α)) (pkw kw : List (String × α)) (obj : α)
    (args : List α),
    (ph ≤ args.length →
      partialmethodCall .bound id pargs pkw ph obj args kw =
        .ok ⟨id, obj :: fillCall pargs args, mergeKw pkw kw⟩ ∧
      partialmethodCall .unbound id pargs pkw ph obj args kw =
        .ok ⟨id, obj :: fillCall pargs args, mergeKw pkw kw⟩) ∧
    (args.length < ph →
      (partialmethodCall .bound id pargs pkw ph obj args kw).raises "TypeError" ∧
      (partialmethodCall .unbound id pargs pkw ph obj args kw).raises "TypeError") ∧
    isAbstractOf none = false

theorem partialmethodBranches_proven : PartialmethodBranches := by
  intro α id ph pargs pkw kw obj args
  refine ⟨?_, ?_, rfl⟩
  · intro h
    have h1 : ¬ args.length < ph := by omega
    simp [partialmethodCall, h1]
  · intro h
    have h0 : ph ≠ 0 := by omega
    constructor
    · exact ⟨_, by simp [partialmethodCall, h]; rfl, rfl⟩
    · exact ⟨_, by simp [partialmethodCall, h, h0]; rfl, rfl⟩

/-! ### `lru_cache` keys -/

/-- `_make_key` and `lru_cache_make_key` build the same key, for every positional and keyword
arguments, `typed` or not, including the single fast argument. The key is what decides hits, so
this is the twin's agreement on cache identity. -/
def MakeKeyTwins : Prop :=
  ∀ (α : Type) (O : KeyOps α) (args : List α) (kwds : List (String × α)) (typed : Bool),
    makeKeyPy O args kwds typed = makeKeyC O args kwds typed

theorem makeKeyTwins_proven : MakeKeyTwins := by
  intro α O args kwds typed
  cases typed with
  | true =>
    cases kwds <;> simp [makeKeyPy, makeKeyC]
  | false =>
    cases kwds with
    | cons p ps =>
      simp [makeKeyPy, makeKeyC]
      split
      · next a heq =>
        have := congrArg List.length heq
        simp at this
        omega
      · rfl
    | nil =>
      match args with
      | [] => simp [makeKeyPy, makeKeyC]
      | [a] => simp [makeKeyPy, makeKeyC]
      | a :: b :: rest => simp [makeKeyPy, makeKeyC]

end PyLean.CoreLibs.Functools
