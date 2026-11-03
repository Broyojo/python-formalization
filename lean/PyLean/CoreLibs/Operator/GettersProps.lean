import PyLean.CoreLibs.Operator.Getters

/-!
Properties of `itemgetter`, `attrgetter`, `methodcaller`.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

theorem mapPy_ok {β γ : Type} (f : β → Py γ) (r : β → γ) (h : ∀ x, f x = .ok (r x)) :
    ∀ l : List β, mapPy f l = .ok (l.map r)
  | [] => rfl
  | x :: xs => by simp [mapPy, h, mapPy_ok f r h xs]

/-- `itemgetter` gives the same outcome in both twins, for every item list and any object. On a tuple, what the
shortcut of `itemgetter_call_impl` reads is what `obj[i]` gives: exact tuples have that `__getitem__`, which is the
hypothesis. So the shortcut is invisible. A failing `obj[i]` stops the tuple in both, at the same item. -/
def ItemgetterTwins : Prop :=
  ∀ (α κ : Type) (items : List (ItemKey κ)) (o : ItemObj α κ),
    (∀ k xs i v, o.exactTuple = some xs → fastIndex k = some i → xs[i]? = some v → o.get k.key = .ok v) →
    itemCallC items o = itemCallPy items o

theorem itemgetterTwins_proven : ItemgetterTwins := by
  intro α κ items o h
  cases items with
  | nil => rfl
  | cons k rest =>
    cases rest with
    | cons k2 rest2 => rfl
    | nil =>
      simp only [itemCallC, itemCallPy]
      cases hf : fastIndex k with
      | none => rfl
      | some i =>
        cases ht : o.exactTuple with
        | none => rfl
        | some xs =>
          simp only
          cases hv : xs[i]? with
          | none => rfl
          | some v => simp [h k xs i v ht hf hv]

/-- `ig->index` is set exactly for an exact `int` that is not negative and fits, so `itemgetter(-1)` and
`itemgetter(2**64)` take the slow path. -/
def ItemgetterIndex : Prop :=
  ∀ (κ : Type) (key : κ) (n : Int),
    (0 ≤ n → n ≤ ssizeMax → fastIndex ⟨key, some n⟩ = some n.toNat) ∧
    (n < 0 → fastIndex ⟨key, some n⟩ = none) ∧ (n > ssizeMax → fastIndex ⟨key, some n⟩ = none) ∧
    fastIndex ⟨key, none⟩ = none

theorem itemgetterIndex_proven : ItemgetterIndex := by
  intro κ key n
  refine ⟨?_, ?_, ?_, rfl⟩
  · intro h1 h2; simp [fastIndex, h1, h2]
  · intro h
    have : ¬ (0 ≤ n ∧ n ≤ ssizeMax) := by omega
    simp [fastIndex, this]
  · intro h
    have : ¬ (0 ≤ n ∧ n ≤ ssizeMax) := by omega
    simp [fastIndex, this]

/-- The constructors and calls reject the same argument lists: a `TypeError` in both, for a wrong count and for
keywords, in each of the three classes, whatever the wording. -/
def GetterArity : Prop :=
  ∀ (name : String) (nargs nkw : Nat),
    ((oneArgC name nargs nkw).isSome = (oneArgPy nargs nkw).isSome) ∧
    ((oneArgVectorC name nargs nkw).isSome = (oneArgPy nargs nkw).isSome) ∧
    ((newArgC name nargs nkw).isSome = (newArgPy nargs nkw).isSome)

theorem getterArity_proven : GetterArity := by
  intro name nargs nkw
  refine ⟨?_, ?_, ?_⟩
  · simp only [oneArgC, oneArgPy]
    by_cases h1 : nkw = 0 <;> by_cases h2 : nargs = 1 <;> simp [h1, h2]
  · simp only [oneArgVectorC, oneArgPy]
    by_cases h1 : nkw = 0 <;> by_cases h2 : nargs = 1 <;> simp [h1, h2]
  · simp only [newArgC, newArgPy]
    by_cases h1 : nkw = 0 <;> by_cases h2 : nargs = 0 <;> simp [h1, h2]

theorem fold_append (l : List String) : ∀ s t : String,
    l.foldl (fun a x => a ++ ", " ++ x) (s ++ t) = s ++ l.foldl (fun a x => a ++ ", " ++ x) t := by
  induction l with
  | nil => intro s t; rfl
  | cons x xs ih =>
    intro s t
    simp only [List.foldl_cons]
    rw [← ih, String.append_assoc, String.append_assoc, String.append_assoc]

/-- The `repr` of `itemgetter` and `attrgetter` is one string in both twins when no item's `repr` raises, for one
item or for many, on the object outside any recursion. An item's `repr` that raises propagates from both, the
first one in order. -/
def GetterReprTwins : Prop :=
  ∀ (κ : Type) (rep : κ → Py String) (cls : String) (items : List κ),
    reprC rep false cls items = reprPy rep cls items

theorem getterReprTwins_proven : GetterReprTwins := by
  intro κ rep cls items
  cases items with
  | nil => simp [reprC, reprPy, tupleRepr, mapPy, joinArgs, String.append_assoc]
  | cons k rest =>
    cases rest with
    | nil =>
      simp only [reprC, Bool.false_eq_true, ite_false, reprPy, mapPy]
      cases rep k with
      | error e => rfl
      | ok r => simp [mapPy, joinArgs, String.append_assoc]
    | cons k2 r2 =>
      simp only [reprC, Bool.false_eq_true, ite_false, reprPy, tupleRepr]
      cases mapPy rep (k :: k2 :: r2) with
      | error e => rfl
      | ok rs => simp [String.append_assoc]

/-- The repr of a getter that holds itself. The twins differ: the C classes guard with `Py_ReprEnter` and print
`cls(...)` at the inner level, and the Python classes have no guard, so the recursion is stopped by what
holds the object, a list printing `[...]`. Stated as equality, so refuted. -/
def GetterReprRecursive : Prop :=
  ∀ (cls : String) (items : List String),
    reprC (fun s => Except.ok s) true cls items = reprPy (fun s => Except.ok s) cls items

theorem getterReprRecursive_refuted : ¬GetterReprRecursive := by
  intro h
  have := h "c" ["x"]
  revert this
  decide

theorem split_join : ∀ s : List Char, joinChars (splitChars s) = s ∧ splitChars s ≠ []
  | [] => by simp [splitChars, joinChars]
  | c :: cs => by
    obtain ⟨h1, h2⟩ := split_join cs
    cases hs : splitChars cs with
    | nil => exact absurd hs h2
    | cons r rs =>
      rw [hs] at h1
      by_cases hc : c = '.'
      · subst hc
        simp only [splitChars, hs, ite_true]
        refine ⟨?_, by simp⟩
        cases rs with
        | nil => simp only [joinChars] at h1 ⊢; simp [h1]
        | cons r2 r3 => simp only [joinChars] at h1 ⊢; simp [h1]
      · simp only [splitChars, hs, hc, ite_false]
        refine ⟨?_, by simp⟩
        cases rs with
        | nil => simp only [joinChars] at h1 ⊢; simp [h1]
        | cons r2 r3 => simp only [joinChars] at h1 ⊢; simp [h1]

theorem dotted_append {α : Type} (ga : GetAttr α) : ∀ (obj : α) (a b : Chain),
    dotted ga obj (a ++ b) =
      match dotted ga obj a with
      | .error e => .error e
      | .ok v => dotted ga v b
  | _, [], _ => rfl
  | obj, n :: ns, b => by
    simp only [List.cons_append, dotted]
    cases ga obj n with
    | error _ => rfl
    | ok v => exact dotted_append ga v ns b

def plainArgs (l : List (List Char)) : List AttrArg := l.map AttrArg.str

/-- `attrgetter` on plain `str` names is one function in both twins: the same names and the same call, for one
name or many, where a `getattr` that raises stops the call. Dotted lookups compose: `attrgetter('a.b')` is
`getattr(getattr(o, 'a'), 'b')`. `split` and `join` are inverse, so `__reduce__`, which C rebuilds by joining
and Python keeps as given, returns the arguments, in both twins, for every string, with empty parts. A name
that is not a `str` is a `TypeError`, wherever it stands. Docs of `attrgetter`. -/
def AttrgetterTwins : Prop :=
  ∀ (α : Type) (ga : GetAttr α) (obj : α) (args : List (List Char)) (a b : Chain) (pre post : List AttrArg),
    (∃ g c, attrgetterNewPy (plainArgs args) = .ok g ∧ attrgetterNewC (plainArgs args) = .ok c ∧
      g.names = c ∧ attrCall ga g.names obj = attrCall ga c obj ∧
      attrArgsC c = args ∧ attrArgsPy g = args) ∧
    dotted ga obj (a ++ b) =
      (match dotted ga obj a with
       | .error e => .error e
       | .ok v => dotted ga v b)

theorem attrArgs_plain (args : List (List Char)) :
    attrArgsPy ⟨plainArgs args, args.map splitChars⟩ = args := by
  induction args with
  | nil => rfl
  | cons a as ih =>
    simp only [attrArgsPy, plainArgs, List.map_cons, List.filterMap_cons]
    simp only [attrArgsPy, plainArgs] at ih
    simp [ih]

theorem attrgetterTwins_proven : AttrgetterTwins := by
  intro α ga obj args a b pre post
  refine ⟨⟨⟨plainArgs args, args.map splitChars⟩, args.map splitChars, ?_, ?_, rfl, rfl, ?_, attrArgs_plain args⟩,
    dotted_append ga obj a b⟩
  · have hm : ∀ l : List (List Char), mapPy namePy (plainArgs l) = .ok (l.map splitChars) := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [plainArgs] at ih
        simp [plainArgs, mapPy, namePy, ih]
    simp [attrgetterNewPy, hm]
  · have hm : ∀ l : List (List Char), mapPy nameC (plainArgs l) = .ok (l.map splitChars) := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih =>
        simp only [plainArgs] at ih
        simp [plainArgs, mapPy, nameC, ih]
    exact hm args
  · simp only [attrArgsC, List.map_map]
    have : ∀ l : List (List Char), l.map (joinChars ∘ splitChars) = l := by
      intro l
      induction l with
      | nil => rfl
      | cons x xs ih => simp [ih, (split_join x).1]
    exact this args

/-- `attrgetter` agrees in the twins on a `str` subclass. False when it overrides `split`: Python calls
`attr.split('.')`, and C reads the characters. -/
def AttrgetterStrSubclass : Prop :=
  ∀ (args : List AttrArg) (g : AttrPy) (c : List Chain),
    attrgetterNewPy args = .ok g → attrgetterNewC args = .ok c → g.names = c

theorem attrgetterStrSubclass_refuted : ¬AttrgetterStrSubclass := by
  intro h
  have := h [.strSub ['x'] [['r']]] ⟨[.strSub ['x'] [['r']]], [[['r']]]⟩ [[['x']]] (by decide) (by decide)
  revert this
  decide

/-- A name that is not a `str` is rejected by both constructors with the same message, wherever it stands. -/
def AttrgetterRejects : Prop :=
  ∀ (pre post : List (List Char)),
    attrgetterNewPy (plainArgs pre ++ .other :: plainArgs post) = .error (.typeError attrNameMsg) ∧
    attrgetterNewC (plainArgs pre ++ .other :: plainArgs post) = .error (.typeError attrNameMsg)

theorem mapPy_stops {β γ : Type} (f : β → Py γ) (bad : β) (rest : List β) (e : PyExc)
    (hb : f bad = .error e) : ∀ l : List β, (∀ x ∈ l, ∃ y, f x = .ok y) →
    mapPy f (l ++ bad :: rest) = .error e
  | [], _ => by simp [mapPy, hb]
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    have := mapPy_stops f bad rest e hb xs (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp [mapPy, hy, this]

theorem attrgetterRejects_proven : AttrgetterRejects := by
  intro pre post
  have hok : ∀ x ∈ plainArgs pre, ∃ s, x = AttrArg.str s := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨s, rfl⟩
  constructor
  · have := mapPy_stops namePy AttrArg.other (plainArgs post) (.typeError attrNameMsg) rfl (plainArgs pre)
      (fun x hx => by obtain ⟨s, rfl⟩ := hok x hx; exact ⟨_, rfl⟩)
    simp [attrgetterNewPy, this]
  · exact mapPy_stops nameC AttrArg.other (plainArgs post) (.typeError attrNameMsg) rfl (plainArgs pre)
      (fun x hx => by obtain ⟨s, rfl⟩ := hok x hx; exact ⟨_, rfl⟩)

theorem zip_map_fst_snd {α : Type} : ∀ kw : List (String × α),
    (kw.map Prod.fst).zip (kw.map Prod.snd) = kw
  | [] => rfl
  | (a, b) :: rest => by simp [zip_map_fst_snd rest]

/-- `methodcaller` runs one call in every path, for any method, any arguments and any keywords, and a failing
`getattr` or a failing call propagates: Python's `getattr(obj, name)(*args, **kwargs)`, C's `methodcaller_call` and
the vectorcall path, which flattens the keyword values after the positional arguments and takes them
apart again. The stack of `_METHODCALLER_MAX_ARGS` entries is never overrun. -/
def MethodcallerTwins : Prop :=
  ∀ (α β : Type) (m : Meth α β) (c : Mc α) (obj : α),
    mcVectorcall m c obj = mcCall m c obj ∧ mcCallC m c obj = mcCall m c obj ∧
    (usesVectorcall c.args.length c.kw.length = true → 1 + c.args.length + c.kw.length ≤ 8)

theorem methodcallerTwins_proven : MethodcallerTwins := by
  intro α β m c obj
  have hv : mcVectorcall m c obj = mcCall m c obj := by
    simp only [mcVectorcall, mcCall, vectorcallArgs]
    cases m obj c.name with
    | error e => rfl
    | ok f =>
      simp only
      have h1 : (c.args ++ c.kw.map Prod.snd).take c.args.length = c.args := by simp
      have h2 : (c.args ++ c.kw.map Prod.snd).drop c.args.length = c.kw.map Prod.snd := by simp
      rw [h1, h2, zip_map_fst_snd]
  refine ⟨hv, ?_, ?_⟩
  · unfold mcCallC
    split
    · exact hv
    · rfl
  · intro h
    simp [usesVectorcall] at h
    omega

/-- The constructors of `methodcaller` agree: on a name, and on a non-`str` with one message. With no name at all
each raises `TypeError` in its own words. The object is `__reduce__`-able in both: what `__reduce__` gives
rebuilds the same object through the constructor, with keywords through `partial`, in both twins. -/
def MethodcallerNew : Prop :=
  ∀ (α : Type) (s : List Char) (args : List α) (kw : List (String × α)) (c : Mc α),
    mcNewC (some (.str s)) args kw = mcNewPy (some (.str s)) args kw ∧
    mcNewC (some .other) args kw = mcNewPy (some .other) args kw ∧
    (mcNewC none args kw).raises "TypeError" ∧ (mcNewPy none args kw).raises "TypeError" ∧
    mcRebuild mcNewC (mcReduce c) = .ok c ∧ mcRebuild mcNewPy (mcReduce c) = .ok c

theorem methodcallerNew_proven : MethodcallerNew := by
  intro α s args kw c
  refine ⟨rfl, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, ?_, ?_⟩
  all_goals
    obtain ⟨n, a, k⟩ := c
    cases k with
    | nil => rfl
    | cons p ps => rfl

/-- The `repr` of `methodcaller` is one string in both twins, with no arguments or with any, when neither the name's
nor any argument's `repr` raises. -/
def MethodcallerRepr : Prop :=
  ∀ (α : Type) (r : α → String) (cls nameRepr : String) (c : Mc α),
    let rep : α → Py String := fun a => .ok (r a)
    mcReprC rep false cls (.ok nameRepr) c = mcReprPy rep cls (.ok nameRepr) c

theorem join_cons (n x : String) (xs : List String) :
    joinArgs (n :: x :: xs) = n ++ ", " ++ joinArgs (x :: xs) := by
  simp only [joinArgs, List.foldl_cons]
  exact fold_append xs (n ++ ", ") x

theorem methodcallerRepr_proven : MethodcallerRepr := by
  intro α r cls n c rep
  have h1 : mapPy rep c.args = .ok (c.args.map r) := mapPy_ok rep r (fun _ => rfl) _
  let rk : String × α → String := fun p => p.1 ++ "=" ++ r p.2
  have h2 : mapPy (fun p : String × α => (rep p.2).map (fun x => p.1 ++ "=" ++ x)) c.kw =
      .ok (c.kw.map rk) := mapPy_ok _ rk (fun _ => rfl) _
  simp only [mcReprC, Bool.false_eq_true, ite_false, mcReprPy, h1, h2, List.cons_append]
  by_cases he : (c.args.isEmpty && c.kw.isEmpty) = true
  · have e1 : c.args = [] := by simpa using (Bool.and_eq_true_iff.mp he).1
    have e2 : c.kw = [] := by simpa using (Bool.and_eq_true_iff.mp he).2
    simp [e1, e2, joinArgs, Except.map]
  · simp only [he, Bool.false_eq_true, ite_false]
    cases hl : c.args.map r ++ c.kw.map rk with
    | nil =>
      have h3 := List.append_eq_nil_iff.mp hl
      have e1 : c.args = [] := by simpa using h3.1
      have e2 : c.kw = [] := by simpa using h3.2
      simp [e1, e2] at he
    | cons x xs =>
      rw [join_cons]
      simp [String.append_assoc]

end PyLean.CoreLibs.Operator
