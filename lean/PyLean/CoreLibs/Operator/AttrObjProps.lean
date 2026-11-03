import PyLean.CoreLibs.Operator.Strength

/-!
`attrgetter` with name objects: what C keeps of a `str` subclass, what it looks up and what it prints, against
the Python twin, which only ever passes the exact parts of `attr.split('.')` and prints the original arguments.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

theorem split_nodot : ∀ s : List Char, '.' ∉ s → splitChars s = [s]
  | [], _ => rfl
  | c :: cs, h => by
    have hc : ¬ c = '.' := fun e => h (by simp [e])
    have hcs : '.' ∉ cs := fun e => h (List.mem_cons_of_mem _ e)
    simp [splitChars, split_nodot cs hcs, hc]

theorem mapPy_map {β γ δ : Type} (f : γ → Py δ) (g : β → γ) :
    ∀ l : List β, mapPy f (l.map g) = mapPy (fun x => f (g x)) l
  | [] => rfl
  | x :: xs => by simp only [List.map_cons, mapPy, mapPy_map f g xs]

/-- What C keeps for an exact `str` name. -/
def keepExact (s : List Char) : CAttr := if '.' ∈ s then .chain (splitChars s) else .single (.str s)

theorem newCObj_plain : ∀ l : List (List Char), attrgetterNewCObj (plainArgs l) = .ok (l.map keepExact)
  | [] => rfl
  | s :: l => by
    have ih := newCObj_plain l
    have hs : nameCObj (.str s) = .ok (keepExact s) := by
      by_cases hd : '.' ∈ s <;> simp [nameCObj, keepExact, hd]
    simp only [attrgetterNewCObj, plainArgs, List.map_cons, mapPy, hs] at ih ⊢
    rw [ih]

theorem newPy_plain : ∀ l : List (List Char), attrgetterNewPy (plainArgs l) = .ok ⟨plainArgs l, l.map splitChars⟩ := by
  intro l
  have hm : ∀ l : List (List Char), mapPy namePy (plainArgs l) = .ok (l.map splitChars) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih =>
      simp only [plainArgs] at ih
      simp [plainArgs, mapPy, namePy, ih]
  simp [attrgetterNewPy, hm]

theorem dotted_keepExact {α : Type} (ga : GetAttrObj α) (obj : α) (s : List Char) :
    dottedObj ga obj (keepExact s) = dotted (fun o n => ga o (.str n)) obj (splitChars s) := by
  by_cases hd : '.' ∈ s
  · simp [keepExact, hd, dottedObj]
  · simp only [keepExact, hd, ite_false, dottedObj, split_nodot s hd, dotted]
    cases ga obj (.str s) <;> rfl

/-- `attrgetter` looks names up as the twins agree for exact `str` names, a dotted `str` subclass with `str`'s own
`split` walks the same exact parts, and an undotted `str` subclass is looked up as the object itself in C, where
Python passes the exact `str` its `split` returns. -/
def AttrLookupExact : Prop :=
  ∀ (α : Type) (ga : GetAttrObj α) (obj : α) (s : List Char) (c : Chain) (l : List (List Char)),
    (∀ stored g, attrgetterNewCObj (plainArgs l) = .ok stored → attrgetterNewPy (plainArgs l) = .ok g →
      attrCallCObj ga stored obj = attrCallPyObj ga g obj) ∧
    ('.' ∈ s → ∀ x, nameCObj (.strSub s c) = .ok x →
      dottedObj ga obj x = dotted (fun o n => ga o (.str n)) obj (splitChars s)) ∧
    ('.' ∉ s → ∀ x, nameCObj (.strSub s c) = .ok x → dottedObj ga obj x = ga obj (.strSub s c)) ∧
    ('.' ∉ s → namePy (.strSub s (splitChars s)) = .ok [s])

theorem attrLookupExact_proven : AttrLookupExact := by
  intro α ga obj s c l
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro stored g h1 h2
    rw [newCObj_plain] at h1
    rw [newPy_plain] at h2
    cases h1
    cases h2
    simp only [attrCallPyObj]
    have hf : (fun x => dottedObj ga obj (keepExact x)) =
        (fun x => dotted (fun o n => ga o (.str n)) obj (splitChars x)) := funext (dotted_keepExact ga obj)
    match l with
    | [] => rfl
    | [x] => simp only [List.map_cons, List.map_nil, attrCallCObj, attrCall, dotted_keepExact]
    | x :: y :: rest =>
      have e1 : mapPy (dottedObj ga obj) ((x :: y :: rest).map keepExact) =
          mapPy (dotted (fun o n => ga o (.str n)) obj) ((x :: y :: rest).map splitChars) := by
        rw [mapPy_map, mapPy_map, hf]
      simp only [List.map_cons] at e1
      simp only [attrCallCObj, attrCall, List.map_cons, e1]
  · intro hd x hx
    simp only [nameCObj, hd, ite_true, Except.ok.injEq] at hx
    subst hx
    rfl
  · intro hd x hx
    simp only [nameCObj, hd, ite_false, Except.ok.injEq] at hx
    subst hx
    rfl
  · intro hd
    simp [namePy, split_nodot s hd]

/-- `attrgetter` does one lookup in both twins, for any name the constructors accept. False for an undotted `str`
subclass: C keeps the object (`_PyUnicode_InternMortal` skips subclasses, Objects/unicodeobject.c:14306-14310) and
`PyObject_GetAttr` passes it on, Python passes the exact `str` of `attr.split('.')`, so a `__getattribute__` that
looks at its argument tells them apart (bugs/corelibs-operator-twin-str-subclass.yaml). -/
def AttrLookupTwins : Prop :=
  ∀ (α : Type) (ga : GetAttrObj α) (obj : α) (args : List AttrArg) (stored : List CAttr) (g : AttrPy),
    attrgetterNewCObj args = .ok stored → attrgetterNewPy args = .ok g →
    attrCallCObj ga stored obj = attrCallPyObj ga g obj

theorem attrLookupTwins_refuted : ¬AttrLookupTwins := by
  intro h
  have := h Nat (fun _ a => match a with | .strSub _ _ => .ok 1 | _ => .ok 0) 0 [.strSub ['x'] [['x']]]
    [.single (.strSub ['x'] [['x']])] ⟨[.strSub ['x'] [['x']]], [[['x']]]⟩ (by decide) (by decide)
  revert this
  decide

theorem rep_dotjoin (rep : AttrArg → Py String) (hrep : ∀ s c, rep (.strSub s c) = rep (.str s)) :
    ∀ (a : AttrArg) (x : CAttr), nameCObj a = .ok x → rep (dotjoinObj x) = rep a := by
  intro a x hx
  cases a with
  | other => simp [nameCObj] at hx
  | str s =>
    by_cases hd : '.' ∈ s
    · simp only [nameCObj, hd, ite_true, Except.ok.injEq] at hx
      subst hx
      simp [dotjoinObj, (split_join s).1]
    · simp only [nameCObj, hd, ite_false, Except.ok.injEq] at hx
      subst hx
      rfl
  | strSub s c =>
    by_cases hd : '.' ∈ s
    · simp only [nameCObj, hd, ite_true, Except.ok.injEq] at hx
      subst hx
      simp [dotjoinObj, (split_join s).1, hrep]
    · simp only [nameCObj, hd, ite_false, Except.ok.injEq] at hx
      subst hx
      rfl

theorem mapPy_dotjoin (rep : AttrArg → Py String) (hrep : ∀ s c, rep (.strSub s c) = rep (.str s)) :
    ∀ (args : List AttrArg) (stored : List CAttr), mapPy nameCObj args = .ok stored →
      mapPy rep (stored.map dotjoinObj) = mapPy rep args
  | [], stored, h => by simp [mapPy] at h; subst h; rfl
  | a :: as, stored, h => by
    simp only [mapPy] at h
    cases ha : nameCObj a with
    | error e => simp [ha] at h
    | ok x =>
      cases hs : mapPy nameCObj as with
      | error e => simp [ha, hs] at h
      | ok xs =>
        simp only [ha, hs, Except.ok.injEq] at h
        subst h
        simp only [List.map_cons, mapPy, rep_dotjoin rep hrep a x ha, mapPy_dotjoin rep hrep as xs hs]

/-- The `repr` of `attrgetter`: when no argument is a `str` subclass with a `__repr__` of its own, the twins give one
outcome, text or exception. With such an argument C prints the name it keeps: the subclass object for an undotted
name, so its own `__repr__`, and the new exact `str` that `dotjoinattr` joins for a dotted one, so `str.__repr__`. -/
def AttrReprExact : Prop :=
  ∀ (rep : AttrArg → Py String) (cls : String) (args : List AttrArg) (stored : List CAttr) (g : AttrPy)
    (s : List Char) (c : Chain),
    attrgetterNewCObj args = .ok stored → attrgetterNewPy args = .ok g →
    ((∀ s c, rep (.strSub s c) = rep (.str s)) → attrReprC rep false cls stored = reprPy rep cls g.attrs) ∧
    ('.' ∈ s → ∀ x, nameCObj (.strSub s c) = .ok x → rep (dotjoinObj x) = rep (.str s)) ∧
    ('.' ∉ s → ∀ x, nameCObj (.strSub s c) = .ok x → rep (dotjoinObj x) = rep (.strSub s c)) ∧
    attrReprC rep true cls stored = .ok (cls ++ "(...)")

theorem attrReprExact_proven : AttrReprExact := by
  intro rep cls args stored g s c h1 h2
  have hg : g.attrs = args := by
    simp only [attrgetterNewPy] at h2
    cases hm : mapPy namePy args with
    | error e => simp [hm] at h2
    | ok n => simp only [hm, Except.ok.injEq] at h2; rw [← h2]
  refine ⟨?_, ?_, ?_, by simp [attrReprC, reprC]⟩
  · intro hrep
    rw [attrReprC, getterReprTwins_proven, hg]
    simp only [reprPy, mapPy_dotjoin rep hrep args stored h1]
  · intro hd x hx
    simp only [nameCObj, hd, ite_true, Except.ok.injEq] at hx
    subst hx
    simp [dotjoinObj, (split_join s).1]
  · intro hd x hx
    simp only [nameCObj, hd, ite_false, Except.ok.injEq] at hx
    subst hx
    rfl

/-- The `repr` of `attrgetter` is one outcome in both twins, for any name the constructors accept. False: for a
dotted `str` subclass name C prints `repr` of the exact `str` it rebuilds (Modules/_operator.c:1538-1540) and Python
`repr` of the original object (Lib/operator.py:274), so a subclass with its own `__repr__` prints differently. -/
def AttrReprTwins : Prop :=
  ∀ (rep : AttrArg → Py String) (cls : String) (args : List AttrArg) (stored : List CAttr) (g : AttrPy),
    attrgetterNewCObj args = .ok stored → attrgetterNewPy args = .ok g →
    attrReprC rep false cls stored = reprPy rep cls g.attrs

theorem attrReprTwins_refuted : ¬AttrReprTwins := by
  intro h
  have := h (fun a => match a with | .strSub _ _ => .ok "S" | _ => .ok "E") "c"
    [.strSub ['a', '.', 'b'] [['a'], ['b']]] [.chain [['a'], ['b']]]
    ⟨[.strSub ['a', '.', 'b'] [['a'], ['b']]], [[['a'], ['b']]]⟩ (by decide) (by decide)
  revert this
  decide

end PyLean.CoreLibs.Operator
