import PyLean.TypeObj.PropsSlotExact
import PyLean.TypeObj.PropsReduce

/-!
`type_call`, `object_new`, `object_init`, `object_richcompare`, `object.__format__`,
`_PyObject_GetNewArguments` and `_PyType_GetSlotNames` (`Objects/typeobject.c`, CPython 3.15.2),
stated on every branch, failures of the user code they call included.
-/

namespace PyLean.TypeObj

/-! ## `type_call` -/

/-- **`type_call`, every branch.** `Objects/typeobject.c:2470-2534`:
* `type(x)` (one positional argument, no keywords) returns the type of `x` and calls nothing;
* any other call of `type` itself with other than 3 positional arguments raises
  "type() takes 1 or 3 arguments";
* a class with NULL `tp_new` raises "cannot create '%s' instances";
* an exception from `tp_new` propagates;
* a result that is not an instance of the class is returned without `__init__`;
* otherwise `tp_init` of the result's type runs with the same arguments: its exception
  propagates and the object is dropped (`:2525-2528`), and on success the object is returned. -/
def TypeCallExact : Prop :=
  ∀ (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) (w : World),
    (t = B.type → ∀ x, args = [x] → kw = [] → typeCall rt t args kw w = .ok (.obj (typeOf w x)) w) ∧
    (t = B.type → ¬ (args.length = 1 ∧ kw = []) → args.length ≠ 3 →
      typeCall rt t args kw w = (typeErr "type() takes 1 or 3 arguments" : M Val) w) ∧
    ((t ≠ B.type ∨ args.length = 3) →
      (slotOf w t .tp_new = none →
        typeCall rt t args kw w = (typeErr s!"cannot create '{tpName w t}' instances" : M Val) w) ∧
      (∀ f, slotOf w t .tp_new = some f →
        (∀ e w1, callTpNew rt f t args kw w = .err e w1 → typeCall rt t args kw w = .err e w1) ∧
        (∀ obj w1, callTpNew rt f t args kw w = .ok obj w1 →
          (isSubtype w1 (typeOf w1 obj) t = false → typeCall rt t args kw w = .ok obj w1) ∧
          (isSubtype w1 (typeOf w1 obj) t = true →
            (slotOf w1 (typeOf w1 obj) .tp_init = none → typeCall rt t args kw w = .ok obj w1) ∧
            (∀ g, slotOf w1 (typeOf w1 obj) .tp_init = some g →
              (∀ w2, callTpInit rt g obj args kw w1 = .ok () w2 → typeCall rt t args kw w = .ok obj w2) ∧
              (∀ e w2, callTpInit rt g obj args kw w1 = .err e w2 →
                typeCall rt t args kw w = .err e w2))))))

/-- The part of `type_call` after the `type` special case (`:2505-2534`), for the proof. -/
def typeCallTail (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  match slotOf w t .tp_new with
  | none => typeErr s!"cannot create '{tpName w t}' instances"
  | some f =>
    let obj ← callTpNew rt f t args kw
    let w ← getW
    unless isSubtype w (typeOf w obj) t do return obj
    match slotOf w (typeOf w obj) .tp_init with
    | some g =>
      callTpInit rt g obj args kw
      pure obj
    | none => pure obj

theorem typeCall_tail (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) (w : World)
    (h : t ≠ B.type ∨ args.length = 3) : typeCall rt t args kw w = typeCallTail rt t args kw w := by
  by_cases ht : t = B.type
  · subst ht
    have h3 : args.length = 3 := by simpa using h
    match args, h3 with
    | [_, _, _], _ => rfl
  · have : (t == B.type) = false := by simpa using ht
    simp only [typeCall, typeCallTail, M.bind_app, getW_app, this, Bool.false_eq_true, ite_false]
    rfl

theorem typeCallExact_proven : TypeCallExact := by
  intro rt t args kw w
  refine ⟨?_, ?_, ?_⟩
  · intro ht x hx hk
    subst ht hx hk
    simp [typeCall]
  · intro ht hn h3
    subst ht
    unfold typeCall
    match args, hn, h3 with
    | [x], hn, _ =>
      have hk : kw.isEmpty = false := by
        cases kw with
        | nil => simp at hn
        | cons _ _ => rfl
      simp [hk, typeErr, raiseC]
    | [], _, _ => simp [typeErr, raiseC]
    | [_, _], _, _ => simp [typeErr, raiseC]
    | _ :: _ :: _ :: _ :: _, _, _ => simp [typeErr, raiseC]
    | [_, _, _], _, h3 => simp at h3
  · intro h
    rw [typeCall_tail rt t args kw w h]
    refine ⟨fun hn => by simp [typeCallTail, hn], fun f hf => ⟨fun e w1 he => by simp [typeCallTail, hf, he],
      fun obj w1 ho => ⟨fun hs => by simp [typeCallTail, hf, ho, hs],
        fun hs => ⟨fun hi => by simp [typeCallTail, hf, ho, hs, hi],
        fun g hg => ⟨fun w2 hi => by simp [typeCallTail, hf, ho, hs, hg, hi],
          fun e w2 hi => by simp [typeCallTail, hf, ho, hs, hg, hi]⟩⟩⟩⟩⟩

/-! ## `object_init`, `object_new`, `excess_args` -/

/-- **`object_init`, every cell of the table.** `Objects/typeobject.c:7442-7459`, with
`excess_args` (`:7435-7439`: some positional argument, or a non-empty keyword dict):
* no arguments: success;
* arguments and an overridden `__init__` (whatever `__new__` is): "object.__init__() takes
  exactly one argument (the instance to initialize)";
* arguments, `__init__` not overridden, `__new__` not overridden: "%.200s.__init__() takes
  exactly one argument (the instance to initialize)";
* arguments, `__init__` not overridden, `__new__` overridden: success (the arguments went to
  `__new__`). -/
def ObjectInitExact : Prop :=
  ∀ (self : Val) (args : List Val) (kw : Kw) (w : World),
    (args = [] → kw = [] → objectInit self args kw w = .ok () w) ∧
    ((args ≠ [] ∨ kw ≠ []) →
      (slotOf w (typeOf w self) .tp_init ≠ some (.c .object) →
        objectInit self args kw w =
          (typeErr "object.__init__() takes exactly one argument (the instance to initialize)" : M Unit) w) ∧
      (slotOf w (typeOf w self) .tp_init = some (.c .object) →
        slotOf w (typeOf w self) .tp_new = some (.c .object) →
        objectInit self args kw w =
          (typeErr s!"{trunc 200 (tpName w (typeOf w self))}.__init__() takes exactly one argument (the instance to initialize)" : M Unit) w) ∧
      (slotOf w (typeOf w self) .tp_init = some (.c .object) →
        slotOf w (typeOf w self) .tp_new ≠ some (.c .object) → objectInit self args kw w = .ok () w))

theorem excess_of (args : List Val) (kw : Kw) (h : args ≠ [] ∨ kw ≠ []) :
    excessArgs args kw = true := by
  rcases h with h | h
  · cases args with
    | nil => exact absurd rfl h
    | cons _ _ => simp [excessArgs]
  · cases kw with
    | nil => exact absurd rfl h
    | cons _ _ => simp [excessArgs]

theorem objectInitExact_proven : ObjectInitExact := by
  intro self args kw w
  refine ⟨?_, ?_⟩
  · intro ha hk; subst ha hk; simp [objectInit, excessArgs]
  · intro hx
    have he := excess_of args kw hx
    refine ⟨?_, ?_, ?_⟩
    · intro hi; simp [objectInit, he, hi, typeErr, raiseC]
    · intro hi hn; simp [objectInit, he, hi, hn, typeErr, raiseC]
    · intro hi hn; simp [objectInit, he, hi, hn]

/-- **`object_new`, every cell, and the instance it makes.** `Objects/typeobject.c:7462-7520`:
* arguments and an overridden `__new__`: "object.__new__() takes exactly one argument (the type
  to instantiate)" (whatever `__init__` is);
* arguments and neither overridden: "%.200s() takes no arguments";
* otherwise (no arguments, or only `__init__` overridden), a class that is not abstract gets a new
  object of exactly that class, at a fresh address, with the world otherwise unchanged;
* an abstract class raises "Can't instantiate abstract class %s without an implementation for
  abstract method%s '%U'" with the names from `abstractNames` (`AbstractNamesExact`), "s" when
  there is more than one; an exception computing the names propagates. -/
def ObjectNewExact : Prop :=
  ∀ (rt : Rt) (t : Addr) (args : List Val) (kw : Kw) (w : World),
    ((args ≠ [] ∨ kw ≠ []) → slotOf w t .tp_new ≠ some (.c .object) →
      objectNew rt t args kw w =
        (typeErr "object.__new__() takes exactly one argument (the type to instantiate)" : M Val) w) ∧
    ((args ≠ [] ∨ kw ≠ []) → slotOf w t .tp_new = some (.c .object) →
      slotOf w t .tp_init = some (.c .object) →
      objectNew rt t args kw w = (typeErr s!"{trunc 200 (tpName w t)}() takes no arguments" : M Val) w) ∧
    (((args = [] ∧ kw = []) ∨
        (slotOf w t .tp_new = some (.c .object) ∧ slotOf w t .tp_init ≠ some (.c .object))) →
      ((tdata w t).isAbstract = false →
        objectNew rt t args kw w =
          .ok (.obj w.heap.size) { w with heap := w.heap.push (.val { cls := t, body := freshBody w t }) }) ∧
      ((tdata w t).isAbstract = true →
        (∀ e w1, abstractNames rt t w = .err e w1 → objectNew rt t args kw w = .err e w1) ∧
        (∀ names w1, abstractNames rt t w = .ok names w1 →
          objectNew rt t args kw w =
            (typeErr s!"Can't instantiate abstract class {tpName w1 t} without an implementation for abstract method{if names.length > 1 then "s" else ""} '{"', '".intercalate names}'" : M Val) w1)))

theorem objectNewExact_proven : ObjectNewExact := by
  intro rt t args kw w
  refine ⟨?_, ?_, ?_⟩
  · intro hx hn
    simp [objectNew, excess_of args kw hx, hn, typeErr, raiseC]
  · intro hx hn hi
    simp [objectNew, excess_of args kw hx, hn, hi, typeErr, raiseC]
  · intro hc
    refine ⟨fun ha => ?_, fun ha => ⟨fun e w1 he => ?_, fun names w1 he => ?_⟩⟩ <;>
    rcases hc with ⟨rfl, rfl⟩ | ⟨hn, hi⟩
    · simp [objectNew, excessArgs, ha, alloc, allocCell]
    · by_cases hx : excessArgs args kw = true
      · simp [objectNew, hx, hn, hi, ha, alloc, allocCell]
      · simp at hx; simp [objectNew, hx, ha, alloc, allocCell]
    · simp [objectNew, excessArgs, ha, he]
    · by_cases hx : excessArgs args kw = true
      · simp [objectNew, hx, hn, hi, ha, he]
      · simp at hx; simp [objectNew, hx, ha, he]
    · simp [objectNew, excessArgs, ha, he, typeErr, raiseC]
    · by_cases hx : excessArgs args kw = true
      · simp [objectNew, hx, hn, hi, ha, he, typeErr, raiseC]
      · simp at hx; simp [objectNew, hx, ha, he, typeErr, raiseC]

/-- **The abstract-method names: sorted, then joined.** `Objects/typeobject.c:7484-7502`
(`type_abstractmethods`, `PySequence_List`, `PyList_Sort`, `PyUnicode_Join`):
* no `__abstractmethods__` in the class dict raises `AttributeError('__abstractmethods__')`;
* an exception listing the items propagates;
* `str` items come back sorted by code point;
* one non-`str` item raises "sequence item 0: expected str instance, %.80s found";
* two `int`s are sorted (no Python code) and the join fails on item 0;
* two items of different types are compared once, `items[1] < items[0]`, *before* any join: an
  exception from that comparison propagates, so `['a', 1]` raises
  "'<' not supported between instances of 'int' and 'str'" (CPython 3.15.2), not the join's
  error. -/
def AbstractNamesExact : Prop :=
  ∀ (rt : Rt) (t : Addr) (w : World),
    (NameDict.get? (tdata w t).dict "__abstractmethods__" = none →
      abstractNames rt t w = (raiseC B.AttributeError "__abstractmethods__" : M (List String)) w) ∧
    (∀ am, NameDict.get? (tdata w t).dict "__abstractmethods__" = some am →
      (∀ e w1, pySequenceList rt am w = .err e w1 → abstractNames rt t w = .err e w1) ∧
      (∀ strs w1, pySequenceList rt am w = .ok (strs.map Val.str) w1 →
        abstractNames rt t w = .ok (sortStrs strs) w1) ∧
      (∀ x w1, pySequenceList rt am w = .ok [x] w1 → strOf w1 x = none →
        abstractNames rt t w =
          (typeErr s!"sequence item {(0 : Nat)}: expected str instance, {trunc 80 (typeName w1 x)} found" : M (List String)) w1) ∧
      (∀ a b w1, pySequenceList rt am w = .ok [.int a, .int b] w1 →
        abstractNames rt t w =
          (typeErr s!"sequence item {(0 : Nat)}: expected str instance, {trunc 80 (tpName w1 B.int)} found" : M (List String)) w1) ∧
      (∀ a b w1, pySequenceList rt am w = .ok [a, b] w1 → typeOf w1 a ≠ typeOf w1 b →
        ∀ e w2, rt.richCompare b a .lt w1 = .err e w2 → abstractNames rt t w = .err e w2))

theorem filterMap_str_map (strs : List String) :
    (strs.map Val.str).filterMap (fun x => match x with | .str s => some s | _ => none) = strs := by
  induction strs with
  | nil => rfl
  | cons s ss ih => simp [ih]

theorem joinAbstract_strs (w : World) (strs : List String) :
    joinAbstract w (strs.map Val.str) = pure strs := by
  have h1 : (strs.map Val.str).findIdx? (fun x => (strOf w x).isNone) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨s, _, rfl⟩ := hx
    simp [strOf]
  have h2 : (strs.map Val.str).filterMap (strOf w) = strs := by
    induction strs with
    | nil => rfl
    | cons s ss ih => simp [strOf] at ih ⊢; exact ih
  simp [joinAbstract, h1, h2]

theorem abstractNamesExact_proven : AbstractNamesExact := by
  intro rt t w
  refine ⟨fun h => by simp [abstractNames, h], fun am h => ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · intro e w1 he; simp [abstractNames, h, he]
  · intro strs w1 he
    have hlen : (strs.map Val.str).filterMap (fun x => match x with | .str s => some s | _ => none) = strs :=
      filterMap_str_map strs
    have hsort : sortAbstractItems rt (strs.map Val.str) w1 = .ok ((sortStrs strs).map Val.str) w1 := by
      have key : ∀ (f : Val → Option String), (∀ s, f (.str s) = some s) →
          List.filterMap f (List.map Val.str strs) = strs := by
        intro f hf
        clear hlen he
        induction strs with
        | nil => rfl
        | cons x xs ih => simp [hf, ih]
      unfold sortAbstractItems
      simp only [M.bind_app, getW_app]
      rw [key]
      · simp
      · intro s; rfl
    simp only [abstractNames, M.bind_app, getW_app, h, he, hsort]
    rw [joinAbstract_strs]
    rfl
  · intro x w1 he hx
    have hs : sortAbstractItems rt [x] w1 = .ok [x] w1 := by
      cases x <;> simp_all [sortAbstractItems, strOf]
    simp [abstractNames, h, he, hs, joinAbstract, hx, typeErr, raiseC]
  · intro a b w1 he
    have hs : sortAbstractItems rt [.int a, .int b] w1 =
        .ok (if b < a then [.int b, .int a] else [.int a, .int b]) w1 := by
      simp [sortAbstractItems]
    by_cases hab : b < a <;>
      simp [abstractNames, h, he, hs, hab, joinAbstract, strOf, payloadOf, typeName, typeOf,
        typeErr, raiseC, List.findIdx?_cons]
  · intro a b w1 he hty e w2 hc
    have hs : sortAbstractItems rt [a, b] w1 = .err e w2 := by
      cases a <;> cases b <;> simp_all [sortAbstractItems, typeOf]
    simp [abstractNames, h, he, hs]

end PyLean.TypeObj
