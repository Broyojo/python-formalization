import PyLean.CoreLibs.Misc.Contextlib.HeapLemmas

/-!
Properties of `suppress.__exit__`, Lib/contextlib.py:512-531. The test of :524 is `issubclass`, which
the comment at :513-521 chooses on purpose over the interpreter's concrete matching, so an item of
`self._exceptions` is a class or an object with `__subclasscheck__` (`SupItem`). A group goes
through the builtin `split`, whose matching is concrete, with the group class's `derive`.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

/-- `suppress.__exit__` tests `exctype` (:522), then `issubclass(exctype, self._exceptions)` (:524),
then `issubclass(exctype, BaseExceptionGroup)` (:526). With `exctype` `None` it returns `None` and
does nothing, whatever `excinst` is. Otherwise a true `issubclass` gives `True` and an exception from
it (a `__subclasscheck__` that raises, a non-class argument) comes through, both before anything
looks at `excinst`; a false one gives `False` for a class that is no group class, and the
`TypeError` of `issubclass` for an `exctype` that is no class. -/
def SuppressIssubclass : Prop :=
  ∀ (σ : Type) (items : List (SupItem σ)) (derive : Derive σ) (s s' : St σ) (handled : Option ExcId)
    (d : Derived) (dc : Cls) (excinst : Option ExcId) (e : ExcId),
    suppressExit items derive s handled none excinst = .ok (s, .ok none) ∧
    (issubTuple d handled items s = (s', .ok true) →
      suppressExit items derive s handled (some d) excinst = .ok (s', .ok (some true))) ∧
    (issubTuple d handled items s = (s', .error e) →
      suppressExit items derive s handled (some d) excinst = .ok (s', .error e)) ∧
    (issubTuple (.cls dc) handled items s = (s', .ok false) → subOf dc clsBEG = false →
      suppressExit items derive s handled (some (.cls dc)) excinst = .ok (s', .ok (some false))) ∧
    (issubTuple .other handled items s = (s', .ok false) →
      ∃ t, suppressExit items derive s handled (some .other) excinst =
        .ok ((s'.raiseNew clsType "issubclass() arg 1 must be a class" handled).1, .error t) ∧
        ((s'.raiseNew clsType "issubclass() arg 1 must be a class" handled).1.h.get t).cls = clsType)

theorem suppressIssubclass_proven : SuppressIssubclass := by
  intro σ items derive s s' handled d dc excinst e
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · intro h; simp [suppressExit, h]
  · intro h; simp [suppressExit, h]
  · intro h1 h2; simp [suppressExit, h1, issubItem, h2]
  · intro h
    refine ⟨(s'.raiseNew clsType "issubclass() arg 1 must be a class" handled).2, ?_,
      (raiseNew_obj s' clsType _ handled).2.2.2.2⟩
    simp [suppressExit, h, issubItem]

/-- `issubclass(exctype, self._exceptions)` over the items in order. With plain classes only it is
the concrete test: some item is in `exctype`'s MRO. An item with `__subclasscheck__` decides by
calling it: after plain classes that do not match, a hook that answers `True` (an ABC that
registered the class) or raises is the answer, and the later items are not looked at; one that
answers `False` passes on to the rest. An `exctype` that is no class is a `TypeError` at the first
plain class, and an item that is neither a class nor has `__subclasscheck__` is a `TypeError` when
it is reached. -/
def IssubTupleCases : Prop :=
  ∀ (σ : Type) (handled : Option ExcId) (s s' : St σ) (dc : Cls) (cs pre : List Cls) (d : Derived)
    (check : Derived → St σ → St σ × Res Bool) (x : Option Cls) (r : Res Bool)
    (rest : List (SupItem σ)) (c : Cls),
    issubTuple (.cls dc) handled (cs.map .cls) s = (s, .ok (cs.any (subOf dc))) ∧
    ((∀ c ∈ pre, subOf dc c = false) → check (.cls dc) s = (s', r) → r ≠ .ok false →
      issubTuple (.cls dc) handled (pre.map .cls ++ .hook check x :: rest) s = (s', r)) ∧
    (check d s = (s', .ok false) →
      issubTuple d handled (.hook check x :: rest) s = issubTuple d handled rest s') ∧
    issubTuple .other handled (.cls c :: rest) s =
      (let (s, e) := s.raiseNew clsType "issubclass() arg 1 must be a class" handled; (s, .error e)) ∧
    ((∀ c ∈ pre, subOf dc c = false) →
      issubTuple (.cls dc) handled (pre.map .cls ++ .other :: rest) s =
        (let (s, e) := s.raiseNew clsType
          "issubclass() arg 2 must be a class, a tuple of classes, or a union" handled
         (s, .error e)))

theorem issubTuple_plain {σ : Type} (handled : Option ExcId) (s : St σ) (dc : Cls) :
    ∀ cs : List Cls, issubTuple (.cls dc) handled (cs.map .cls) s = (s, .ok (cs.any (subOf dc))) := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.map_cons, issubTuple, issubItem, List.any_cons]
    cases h : subOf dc c with
    | true => simp
    | false => simpa using ih

theorem issubTuple_skip {σ : Type} (handled : Option ExcId) (s : St σ) (dc : Cls)
    (tail : List (SupItem σ)) :
    ∀ pre : List Cls, (∀ c ∈ pre, subOf dc c = false) →
      issubTuple (.cls dc) handled (pre.map .cls ++ tail) s = issubTuple (.cls dc) handled tail s := by
  intro pre
  induction pre with
  | nil => intro _; rfl
  | cons c rest ih =>
    intro h
    have hc : subOf dc c = false := h c (by simp)
    simp only [List.map_cons, List.cons_append, issubTuple, issubItem, hc]
    exact ih (fun c' hc' => h c' (by simp [hc']))

theorem issubTupleCases_proven : IssubTupleCases := by
  intro σ handled s s' dc cs pre d check x r rest c
  refine ⟨issubTuple_plain handled s dc cs, ?_, ?_, rfl, ?_⟩
  · intro hpre hc hr
    rw [issubTuple_skip handled s dc _ pre hpre]
    simp only [issubTuple, issubItem, hc]
    cases r with
    | error e => rfl
    | ok b =>
      cases b with
      | true => rfl
      | false => exact absurd rfl hr
  · intro hc
    simp [issubTuple, issubItem, hc]
  · intro hpre
    rw [issubTuple_skip handled s dc _ pre hpre]
    rfl

/-- What `splitRec` does on members that are leaves and do not match: they all go to the rest, in
order, and nothing else happens. -/
theorem foldl_leaves {σ : Type} (ms : List Cls) (derive : Derive σ) (handled : Option ExcId)
    (fuel : Nat) (s : St σ) :
    ∀ (cs ml rl : List ExcId), (∀ c ∈ cs, (s.h.get c).children = none ∧ matchBy s.h ms c = false) →
      cs.foldl (splitStep (splitRec ms derive handled (fuel + 1))) (some (s, .ok (ml, rl))) =
        some (s, .ok (ml, rl ++ cs)) := by
  intro cs
  induction cs with
  | nil => intro ml rl _; simp
  | cons c rest ih =>
    intro ml rl h
    have ⟨hc, hm⟩ := h c (by simp)
    simp only [List.foldl_cons]
    have : splitStep (splitRec ms derive handled (fuel + 1)) (some (s, .ok (ml, rl))) c =
        some (s, .ok (ml, rl ++ [c])) := by
      simp [splitStep, splitRec, hm, hc]
    rw [this, ih ml (rl ++ [c]) (fun c' hc' => h c' (by simp [hc']))]
    simp

/-- A group of leaves none of which matches: the rest is the group `derive` makes from all of
them, so whatever the group class's `derive` does decides the outcome, as the docs say ("re-raised
in a new group which is created using the original group's `derive()` method"). An exception from
`derive` comes through; a result that is no `BaseExceptionGroup` is the `TypeError` of
`exceptiongroup_subset`; a group is raised with the original's `__cause__` and `__traceback__`, and
the exception being handled as `__context__`. -/
def SuppressGroupDeriveCore : Prop :=
  ∀ (σ : Type) (items : List (SupItem σ)) (ms : List Cls) (derive : Derive σ) (s s1 s2 : St σ)
    (handled : Option ExcId) (e g x : ExcId) (cs : List ExcId),
    let dc := (s.h.get e).cls
    issubTuple (.cls dc) handled items s = (s1, .ok false) → s1.h.isInst e "BaseExceptionGroup" = true →
    (s1.h.get e).cls = dc → matcherClasses items = some ms → matchBy s1.h ms e = false →
    (s1.h.get e).children = some cs → cs ≠ [] →
    (∀ c ∈ cs, (s1.h.get c).children = none ∧ matchBy s1.h ms c = false) →
    (derive e cs s1 = (s2, .error x) →
      suppressExit items derive s handled (some (.cls dc)) (some e) = .ok (s2, .error x)) ∧
    (derive e cs s1 = (s2, .ok g) → s2.h.isInst g "BaseExceptionGroup" = false →
      ∃ t, suppressExit items derive s handled (some (.cls dc)) (some e) =
        .ok (((s2.raiseNew clsType "derive must return an instance of BaseExceptionGroup" handled).1,
          .error t)) ∧
        ((s2.raiseNew clsType "derive must return an instance of BaseExceptionGroup" handled).1.h.get t).msg =
          "derive must return an instance of BaseExceptionGroup") ∧
    (derive e cs s1 = (s2, .ok g) → s2.h.isInst g "BaseExceptionGroup" = true →
      ∃ s3, suppressExit items derive s handled (some (.cls dc)) (some e) = .ok (s3, .error g) ∧
        (s3.h.get g).cause = (s2.h.get e).cause ∧
        ((s2.h.get e).tb.isSome → (s3.h.get g).tb = (s2.h.get e).tb) ∧
        (handled ≠ some g → handled.isSome → (s3.h.get g).context = handled))

theorem suppressGroupDeriveCore_proven : SuppressGroupDeriveCore := by
  intro σ items ms derive s s1 s2 handled e g x cs dc hsub hbeg hcls hms hm hch hne hleaf
  have hl : e < s1.h.length := isInst_lt hbeg
  have hbegc : subOf dc clsBEG = true := by
    simp only [Heap.isInst] at hbeg
    simpa [subOf, clsBEG, hcls] using hbeg
  obtain ⟨f, hf⟩ : ∃ f, s1.h.length = f + 1 :=
    ⟨s1.h.length - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le e) hl)).symm⟩
  have hfold := foldl_leaves ms derive handled f s1 cs [] [] hleaf
  have hsplit : ∀ (k : St σ × Res (Option ExcId)),
      subsetM derive handled s1 e cs = k →
      egSplit items derive handled s1 (some e) =
        (match k with
         | (s, .error x) => some (s, .error x)
         | (s, .ok r) => some (s, .ok (none, r))) := by
    intro k hk
    simp only [egSplit, hbeg, Bool.not_true, Bool.false_eq_true, if_false, hms]
    rw [hf, splitRec]
    simp only [hm, Bool.false_eq_true, if_false, hch]
    rw [hfold]
    simp only [List.nil_append]
    have hsub0 : subsetM derive handled s1 e [] = (s1, .ok none) := by simp [subsetM]
    rw [hsub0]
    simp only
    rw [hk]
    rcases k with ⟨s', r⟩
    cases r <;> rfl
  have hcs : cs.isEmpty = false := by
    cases cs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  have hpre : suppressExit items derive s handled (some (.cls dc)) (some e) =
      (match egSplit items derive handled s1 (some e) with
       | none => .error .modelFuel
       | some (s, .error e) => .ok (s, .error e)
       | some (s, .ok (_, none)) => .ok (s, .ok (some true))
       | some (s, .ok (_, some r)) => .ok ({ s with h := s.h.raiseCtx r handled }, .error r)) := by
    simp [suppressExit, hsub, issubItem, hbegc]
    try rfl
  refine ⟨?_, ?_, ?_⟩
  · intro hd
    rw [hpre, hsplit (s2, .error x) (by simp [subsetM, hcs, hd])]
    try rfl
  · intro hd hg
    let k := s2.raiseNew clsType "derive must return an instance of BaseExceptionGroup" handled
    refine ⟨k.2, ?_, (raiseNew_obj s2 clsType _ handled).2.1⟩
    rw [hpre, hsplit (k.1, .error k.2) (by simp [subsetM, hcs, hd, hg, k]; try rfl)]
    try rfl
  · intro hd hg
    let o := s2.h.get e
    let h1 := match o.tb with
      | some t => s2.h.setTb g (some t)
      | none => s2.h
    let h2 := (h1.setContext g o.context).modify g (fun y => { y with cause := o.cause })
    have hk : subsetM derive handled s1 e cs = ({ s2 with h := h2 }, .ok (some g)) := by
      simp [subsetM, hcs, hd, hg, h2, h1, o]
      try rfl
    rw [hpre, hsplit _ hk]
    have hgl : g < s2.h.length := isInst_lt hg
    have hl1 : g < h1.length := by
      simp only [h1]
      split <;> simp [Heap.setTb, length_modify, hgl]
    have hl2 : g < h2.length := by
      simp only [h2, length_modify, length_setContext]
      exact hl1
    have hs := raiseCtx_same h2 g handled g
    have h2g : h2.get g = { (h1.setContext g o.context).get g with cause := o.cause } := by
      simp only [h2]
      rw [get_modify_self _ _ _ (by rw [length_setContext]; exact hl1)]
    have hs1 := setContext_same h1 g o.context g
    refine ⟨{ s2 with h := h2.raiseCtx g handled }, rfl, ?_, ?_, ?_⟩
    · show ((h2.raiseCtx g handled).get g).cause = o.cause
      rw [hs.2.2.1, h2g]
    · intro hsome
      show ((h2.raiseCtx g handled).get g).tb = o.tb
      rw [hs.2.2.2.1, h2g]
      show ((h1.setContext g o.context).get g).tb = o.tb
      rw [hs1.2.2.2.1]
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hsome
      have : h1 = s2.h.setTb g (some t) := by simp only [h1, o]; rw [ht]
      rw [this]
      simp only [Heap.setTb]
      rw [get_modify_self _ _ _ hgl]
      exact ht.symm
    · intro hne hsome
      obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.1 hsome
      exact raiseCtx_context h2 g y hl2 (fun h => hne (by rw [h]))

/-- An item `get_matcher_type` accepts in the tuple: an exception class (`PyExceptionClass_Check`,
Objects/exceptions.c:1260-1266). A class whose metaclass has `__subclasscheck__` is one when it
derives from `BaseException`; an ABC that is no exception class, a nested tuple and a union are
not. -/
def ExcClassItem {σ : Type} : SupItem σ → Prop
  | .cls c => c.contains "BaseException" = true
  | .hook _ c => c.isSome = true
  | .other => False

/-- The classes of the items that are exception classes, in order. -/
def itemClasses {σ : Type} : List (SupItem σ) → List Cls
  | [] => []
  | .cls c :: is => c :: itemClasses is
  | .hook _ (some c) :: is => c :: itemClasses is
  | _ :: is => itemClasses is

theorem matcherClasses_some {σ : Type} : ∀ items : List (SupItem σ),
    (∀ i ∈ items, ExcClassItem i) → matcherClasses items = some (itemClasses items)
  | [], _ => rfl
  | i :: is, h => by
    have hi := h i (by simp)
    have hr := matcherClasses_some is (fun j hj => h j (by simp [hj]))
    cases i with
    | cls c =>
      simp only [ExcClassItem] at hi
      simp only [matcherClasses, itemClasses]
      rw [if_pos hi, hr]
      rfl
    | hook ch c =>
      cases c with
      | none => simp [ExcClassItem] at hi
      | some c => simp [matcherClasses, itemClasses, hr]
    | other => simp [ExcClassItem] at hi

theorem matcherClasses_none {σ : Type} : ∀ items : List (SupItem σ),
    (∃ i ∈ items, ¬ExcClassItem i) → matcherClasses items = none
  | [], ⟨_, hi, _⟩ => by simp at hi
  | i :: is, ⟨j, hj, hn⟩ => by
    rcases List.mem_cons.1 hj with rfl | hj'
    · cases j with
      | cls c =>
        simp only [ExcClassItem] at hn
        simp only [matcherClasses]
        rw [if_neg hn]
      | hook ch c =>
        cases c with
        | none => simp [matcherClasses]
        | some c => simp [ExcClassItem] at hn
      | other => simp [matcherClasses]
    · have ih := matcherClasses_none is ⟨j, hj', hn⟩
      cases i with
      | cls c =>
        simp only [matcherClasses]
        by_cases hc : c.contains "BaseException" = true
        · rw [if_pos hc, ih]; rfl
        · rw [if_neg hc]
      | hook ch c =>
        cases c with
        | none => simp [matcherClasses]
        | some c => simp [matcherClasses, ih]
      | other => simp [matcherClasses]

/-- What `suppressExit` gives when it raises a new `c(msg)` in state `s`. -/
def raisedNew {σ : Type} (s : St σ) (c : Cls) (msg : String) (handled : Option ExcId) :
    PyLean.Py (St σ × Res (Option Bool)) :=
  .ok ((s.raiseNew c msg handled).1, .error (s.raiseNew c msg handled).2)

/-- The `TypeError` of `get_matcher_type`, Objects/exceptions.c:1271-1275. -/
def matcherMsg : String :=
  "expected an exception type, a tuple of exception types, or a callable (other than a class)"

/-- When `exctype` is a group class that `issubclass` did not match, `excinst.split(self._exceptions)`
(Lib/contextlib.py:527) runs, and fails: with `AttributeError` for an `excinst` of `None` or of an
exception that is no group, and with the `TypeError` of `get_matcher_type` for a group when an item
of the tuple is no exception class, though `issubclass` accepted it at :524: an ABC that is no
exception class, a nested tuple, a union such as `KeyError | ValueError`, or a class that is no
exception class (`suppress(int)`). Each is raised in `__exit__`, so the exception being handled, the
group itself inside a `with`, is its `__context__`, and `derive` is not called. -/
def SuppressSplitRefusals : Prop :=
  ∀ (σ : Type) (items : List (SupItem σ)) (derive : Derive σ) (s s1 : St σ) (handled : Option ExcId)
    (dc : Cls) (e : ExcId),
    issubTuple (.cls dc) handled items s = (s1, .ok false) → subOf dc clsBEG = true →
    suppressExit items derive s handled (some (.cls dc)) none =
      raisedNew s1 clsAttr "'NoneType' object has no attribute 'split'" handled ∧
    (s1.h.isInst e "BaseExceptionGroup" = false →
      suppressExit items derive s handled (some (.cls dc)) (some e) =
        raisedNew s1 clsAttr s!"'{(s1.h.get e).cls.headD ""}' object has no attribute 'split'" handled) ∧
    (s1.h.isInst e "BaseExceptionGroup" = true → (∃ i ∈ items, ¬ExcClassItem i) →
      suppressExit items derive s handled (some (.cls dc)) (some e) = raisedNew s1 clsType matcherMsg handled)

theorem suppressSplitRefusals_proven : SuppressSplitRefusals := by
  intro σ items derive s s1 handled dc e hsub hbeg
  refine ⟨?_, ?_, ?_⟩
  · simp [suppressExit, hsub, issubItem, hbeg, egSplit, raisedNew]
  · intro hg
    simp [suppressExit, hsub, issubItem, hbeg, egSplit, raisedNew, hg]
  · intro hg hn
    simp [suppressExit, hsub, issubItem, hbeg, egSplit, raisedNew, hg, matcherClasses_none items hn,
      matcherMsg]

/-- The `TypeError` of `exceptiongroup_subset`, Objects/exceptions.c:1179-1183. -/
def deriveMsg : String := "derive must return an instance of BaseExceptionGroup"

theorem get_modify_of_ne (h : Heap) (a i : ExcId) (f : ExcObj → ExcObj) (hne : i ≠ a) :
    (h.modify a f).get i = h.get i := by
  simp only [Heap.modify, Heap.get]
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hne), ← List.getD_eq_getElem?_getD]

/-- What `exceptiongroup_subset` does to the group `derive` returned (:1187-1196). -/
def subsetFix (h : Heap) (orig eg : ExcId) : Heap :=
  let o := h.get orig
  let h1 := match o.tb with
    | some t => h.setTb eg (some t)
    | none => h
  (h1.setContext eg o.context).modify eg (fun x => { x with cause := o.cause })

theorem subsetFix_props (h : Heap) (orig g : ExcId) (hg : g < h.length) :
    (subsetFix h orig g).length = h.length ∧ (∀ i, i ≠ g → (subsetFix h orig g).get i = h.get i) ∧
    ((subsetFix h orig g).get g).cause = (h.get orig).cause ∧
    ((subsetFix h orig g).get g).context = (h.get orig).context ∧
    ((h.get orig).tb.isSome → ((subsetFix h orig g).get g).tb = (h.get orig).tb) := by
  have hl1 : ∀ t, (h.setTb g t).length = h.length := fun t => by simp [Heap.setTb, length_modify]
  generalize ho : h.get orig = o
  have hfix : subsetFix h orig g = ((match o.tb with
      | some t => h.setTb g (some t)
      | none => h).setContext g o.context).modify g (fun x => { x with cause := o.cause }) := by
    simp only [subsetFix, ho]
  rw [hfix]
  generalize hh1 : (match o.tb with
      | some t => h.setTb g (some t)
      | none => h) = h1
  have hlen1 : h1.length = h.length := by
    rw [← hh1]; split
    · exact hl1 _
    · rfl
  have hg1 : g < (h1.setContext g o.context).length := by rw [length_setContext, hlen1]; exact hg
  refine ⟨by rw [length_modify, length_setContext, hlen1], fun i hi => ?_, ?_, ?_, fun hs => ?_⟩
  · rw [get_modify_of_ne _ _ _ _ hi, Heap.setContext, get_modify_of_ne _ _ _ _ hi, ← hh1]
    split
    · rw [Heap.setTb, get_modify_of_ne _ _ _ _ hi]
    · rfl
  · rw [get_modify_self _ _ _ hg1]
  · rw [get_modify_self _ _ _ hg1, Heap.setContext, get_modify_self _ _ _ (by rw [hlen1]; exact hg)]
  · rw [get_modify_self _ _ _ hg1, Heap.setContext, get_modify_self _ _ _ (by rw [hlen1]; exact hg)]
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 hs
    simp only [ht] at hh1
    rw [← hh1, ht, Heap.setTb, get_modify_self _ _ _ hg]

theorem subsetM_cons {σ : Type} (derive : Derive σ) (handled : Option ExcId) (s : St σ) (orig : ExcId)
    (excs : List ExcId) (hne : excs ≠ []) :
    subsetM derive handled s orig excs =
      match derive orig excs s with
      | (s, .error e) => (s, .error e)
      | (s, .ok eg) =>
        if s.h.isInst eg "BaseExceptionGroup" then ({ s with h := subsetFix s.h orig eg }, .ok (some eg))
        else ((s.raiseNew clsType deriveMsg handled).1, .error (s.raiseNew clsType deriveMsg handled).2) := by
  have he : excs.isEmpty = false := by
    cases excs with
    | nil => exact absurd rfl hne
    | cons _ _ => rfl
  simp only [subsetM, he, Bool.false_eq_true, if_false, subsetFix, deriveMsg]
  rcases derive orig excs s with ⟨s', r⟩
  cases r with
  | error x => rfl
  | ok g =>
    simp only
    split <;> rfl

/-- `splitRec` on members that are all leaves: each goes to the match or to the rest by the concrete
test, in order, and nothing else happens. -/
theorem foldl_flat {σ : Type} (ms : List Cls) (derive : Derive σ) (handled : Option ExcId)
    (fuel : Nat) (s : St σ) :
    ∀ (cs ml rl : List ExcId), (∀ c ∈ cs, (s.h.get c).children = none) →
      cs.foldl (splitStep (splitRec ms derive handled (fuel + 1))) (some (s, .ok (ml, rl))) =
        some (s, .ok (ml ++ cs.filter (matchBy s.h ms), rl ++ cs.filter (fun c => !matchBy s.h ms c))) := by
  intro cs
  induction cs with
  | nil => intro ml rl _; simp
  | cons c rest ih =>
    intro ml rl h
    have hc := h c (by simp)
    have hr : ∀ c' ∈ rest, (s.h.get c').children = none := fun c' hc' => h c' (by simp [hc'])
    simp only [List.foldl_cons]
    cases hm : matchBy s.h ms c with
    | true =>
      have : splitStep (splitRec ms derive handled (fuel + 1)) (some (s, .ok (ml, rl))) c =
          some (s, .ok (ml ++ [c], rl)) := by
        simp [splitStep, splitRec, hm]
      rw [this, ih _ _ hr]
      simp [List.filter_cons, hm]
    | false =>
      have : splitStep (splitRec ms derive handled (fuel + 1)) (some (s, .ok (ml, rl))) c =
          some (s, .ok (ml, rl ++ [c])) := by
        simp [splitStep, splitRec, hm, hc]
      rw [this, ih _ _ hr]
      simp [List.filter_cons, hm]

/-- A flat group some of whose leaves match and some not, for every `derive` of the group class:
`split` (Objects/exceptions.c:1374-1420) calls `derive` first on the matched leaves, in order, and
then on the rest. A `derive` that raises on the matched part, or returns something that is no
`BaseExceptionGroup`, makes `excinst.split(...)` (Lib/contextlib.py:527) raise that (the
`TypeError` of :1179-1183), though the match is discarded and the rest is never built. Otherwise the
match gets the original's `__traceback__`, `__context__` and `__cause__` and nothing else changes,
and the rest is `derive` on the unmatched leaves in that world: its exception comes through, a
non-group is the `TypeError`, and a group is raised with the original's cause and traceback and the
exception being handled as `__context__`. -/
def SuppressGroupDerivePartial : Prop :=
  ∀ (σ : Type) (items : List (SupItem σ)) (ms : List Cls) (derive : Derive σ) (s s1 s2 s3 : St σ)
    (handled : Option ExcId) (e g g' x : ExcId) (cs : List ExcId),
    let dc := (s.h.get e).cls
    let ml := cs.filter (matchBy s1.h ms)
    let rl := cs.filter (fun c => !matchBy s1.h ms c)
    let r := suppressExit items derive s handled (some (.cls dc)) (some e)
    issubTuple (.cls dc) handled items s = (s1, .ok false) → s1.h.isInst e "BaseExceptionGroup" = true →
    (s1.h.get e).cls = dc → matcherClasses items = some ms → matchBy s1.h ms e = false →
    (s1.h.get e).children = some cs → (∀ c ∈ cs, (s1.h.get c).children = none) → ml ≠ [] → rl ≠ [] →
    (derive e ml s1 = (s2, .error x) → r = .ok (s2, .error x)) ∧
    (derive e ml s1 = (s2, .ok g) → s2.h.isInst g "BaseExceptionGroup" = false →
      r = raisedNew s2 clsType deriveMsg handled) ∧
    (derive e ml s1 = (s2, .ok g) → s2.h.isInst g "BaseExceptionGroup" = true →
      ∃ s2' : St σ, s2'.g = s2.g ∧ s2'.h.length = s2.h.length ∧ (∀ i, i ≠ g → s2'.h.get i = s2.h.get i) ∧
        (s2'.h.get g).cause = (s2.h.get e).cause ∧ (s2'.h.get g).context = (s2.h.get e).context ∧
        ((s2.h.get e).tb.isSome → (s2'.h.get g).tb = (s2.h.get e).tb) ∧
        (derive e rl s2' = (s3, .error x) → r = .ok (s3, .error x)) ∧
        (derive e rl s2' = (s3, .ok g') → s3.h.isInst g' "BaseExceptionGroup" = false →
          r = raisedNew s3 clsType deriveMsg handled) ∧
        (derive e rl s2' = (s3, .ok g') → s3.h.isInst g' "BaseExceptionGroup" = true →
          ∃ s4, r = .ok (s4, .error g') ∧ (s4.h.get g').cause = (s3.h.get e).cause ∧
            ((s3.h.get e).tb.isSome → (s4.h.get g').tb = (s3.h.get e).tb) ∧
            (handled ≠ some g' → handled.isSome → (s4.h.get g').context = handled)))

theorem suppressGroupDerivePartial_proven : SuppressGroupDerivePartial := by
  intro σ items ms derive s s1 s2 s3 handled e g g' x cs dc ml rl r hsub hbeg hcls hms hm hch hleaf hml hrl
  have hl : e < s1.h.length := isInst_lt hbeg
  have hbegc : subOf dc clsBEG = true := by
    simp only [Heap.isInst] at hbeg
    simpa [subOf, clsBEG, hcls] using hbeg
  obtain ⟨f, hf⟩ : ∃ f, s1.h.length = f + 1 :=
    ⟨s1.h.length - 1, (Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le e) hl)).symm⟩
  have hfold := foldl_flat ms derive handled f s1 cs [] [] hleaf
  simp only [List.nil_append] at hfold
  have hsplit : egSplit items derive handled s1 (some e) =
      (match subsetM derive handled s1 e ml with
       | (s, .error x) => some (s, .error x)
       | (s, .ok m) =>
         match subsetM derive handled s e rl with
         | (s, .error x) => some (s, .error x)
         | (s, .ok r) => some (s, .ok (m, r))) := by
    simp only [egSplit, hbeg, Bool.not_true, Bool.false_eq_true, if_false, hms]
    rw [hf, splitRec]
    simp only [hm, Bool.false_eq_true, if_false, hch]
    rw [hfold]
    rfl
  have hpre : r =
      (match egSplit items derive handled s1 (some e) with
       | none => .error .modelFuel
       | some (s, .error e) => .ok (s, .error e)
       | some (s, .ok (_, none)) => .ok (s, .ok (some true))
       | some (s, .ok (_, some r)) => .ok ({ s with h := s.h.raiseCtx r handled }, .error r)) := by
    simp [r, suppressExit, hsub, issubItem, hbegc]
    try rfl
  have hs1 := subsetM_cons derive handled s1 e ml hml
  refine ⟨fun hd => ?_, fun hd hg => ?_, fun hd hg => ?_⟩
  · rw [hpre, hsplit, hs1, hd]
  · rw [hpre, hsplit, hs1, hd]
    simp only [hg, Bool.false_eq_true, if_false]
    rfl
  · have hgl : g < s2.h.length := isInst_lt hg
    obtain ⟨hlen, hoth, hcause, hctx, htb⟩ := subsetFix_props s2.h e g hgl
    refine ⟨{ s2 with h := subsetFix s2.h e g }, rfl, hlen, hoth, hcause, hctx, htb, ?_⟩
    have hs2 := subsetM_cons derive handled { s2 with h := subsetFix s2.h e g } e rl hrl
    have hfirst : subsetM derive handled s1 e ml = ({ s2 with h := subsetFix s2.h e g }, .ok (some g)) := by
      rw [hs1, hd]; simp only [hg, if_true]
    refine ⟨fun hd2 => ?_, fun hd2 hg2 => ?_, fun hd2 hg2 => ?_⟩
    · rw [hpre, hsplit, hfirst]
      simp only
      rw [hs2, hd2]
    · rw [hpre, hsplit, hfirst]
      simp only
      rw [hs2, hd2]
      simp only [hg2, Bool.false_eq_true, if_false]
      rfl
    · have hgl2 : g' < s3.h.length := isInst_lt hg2
      obtain ⟨_, _, hcause2, _, htb2⟩ := subsetFix_props s3.h e g' hgl2
      have hl2 : g' < (subsetFix s3.h e g').length := by
        rw [(subsetFix_props s3.h e g' hgl2).1]; exact hgl2
      have hsame := raiseCtx_same (subsetFix s3.h e g') g' handled g'
      refine ⟨{ s3 with h := (subsetFix s3.h e g').raiseCtx g' handled }, ?_, ?_, ?_, ?_⟩
      · rw [hpre, hsplit, hfirst]
        simp only
        rw [hs2, hd2]
        simp only [hg2, if_true]
      · show (((subsetFix s3.h e g').raiseCtx g' handled).get g').cause = _
        rw [hsame.2.2.1, hcause2]
      · intro hs
        show (((subsetFix s3.h e g').raiseCtx g' handled).get g').tb = _
        rw [hsame.2.2.2.1, htb2 hs]
      · intro hne hsome
        obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.1 hsome
        exact raiseCtx_context _ g' y hl2 (fun h => hne (by rw [h]))

/-- A group of leaves none of which matches: the rest is the group `derive` makes from all of
them, so whatever the group class's `derive` does decides the outcome, as the docs say ("re-raised
in a new group which is created using the original group's `derive()` method"). An exception from
`derive` comes through; a result that is no `BaseExceptionGroup` is the `TypeError` of
`exceptiongroup_subset`; a group is raised with the original's `__cause__` and `__traceback__`, and
the exception being handled as `__context__`. When an item is no exception class, `split` refuses
the tuple before it looks at the members, with the `TypeError` of `get_matcher_type`. And a flat
group some of whose leaves match and some not, for every `derive`: `SuppressGroupDerivePartial`
(`derive` on the matched leaves first, its failure or non-group result raised, then on the rest). -/
def SuppressGroupDerive : Prop :=
  (∀ (σ : Type) (items : List (SupItem σ)) (derive : Derive σ) (s s1 s2 : St σ)
    (handled : Option ExcId) (e g x : ExcId) (cs : List ExcId),
    let dc := (s.h.get e).cls
    issubTuple (.cls dc) handled items s = (s1, .ok false) → s1.h.isInst e "BaseExceptionGroup" = true →
    (s1.h.get e).cls = dc →
    ((∃ i ∈ items, ¬ExcClassItem i) →
      suppressExit items derive s handled (some (.cls dc)) (some e) = raisedNew s1 clsType matcherMsg handled) ∧
    ((∀ i ∈ items, ExcClassItem i) → matchBy s1.h (itemClasses items) e = false →
      (s1.h.get e).children = some cs → cs ≠ [] →
      (∀ c ∈ cs, (s1.h.get c).children = none ∧ matchBy s1.h (itemClasses items) c = false) →
      (derive e cs s1 = (s2, .error x) →
        suppressExit items derive s handled (some (.cls dc)) (some e) = .ok (s2, .error x)) ∧
      (derive e cs s1 = (s2, .ok g) → s2.h.isInst g "BaseExceptionGroup" = false →
        ∃ t, suppressExit items derive s handled (some (.cls dc)) (some e) =
          .ok (((s2.raiseNew clsType "derive must return an instance of BaseExceptionGroup" handled).1,
            .error t)) ∧
          ((s2.raiseNew clsType "derive must return an instance of BaseExceptionGroup" handled).1.h.get t).msg =
            "derive must return an instance of BaseExceptionGroup") ∧
      (derive e cs s1 = (s2, .ok g) → s2.h.isInst g "BaseExceptionGroup" = true →
        ∃ s3, suppressExit items derive s handled (some (.cls dc)) (some e) = .ok (s3, .error g) ∧
          (s3.h.get g).cause = (s2.h.get e).cause ∧
          ((s2.h.get e).tb.isSome → (s3.h.get g).tb = (s2.h.get e).tb) ∧
          (handled ≠ some g → handled.isSome → (s3.h.get g).context = handled)))) ∧
  SuppressGroupDerivePartial

theorem suppressGroupDerive_proven : SuppressGroupDerive := by
  refine ⟨?_, suppressGroupDerivePartial_proven⟩
  intro σ items derive s s1 s2 handled e g x cs dc hsub hbeg hcls
  have hbegc : subOf dc clsBEG = true := by
    simp only [Heap.isInst] at hbeg
    simpa [subOf, clsBEG, hcls] using hbeg
  refine ⟨fun hn => (suppressSplitRefusals_proven σ items derive s s1 handled dc e hsub hbegc).2.2 hbeg hn,
    fun hall hm hch hne hleaf => ?_⟩
  exact suppressGroupDeriveCore_proven σ items (itemClasses items) derive s s1 s2 handled e g x cs hsub hbeg
    hcls (matcherClasses_some items hall) hm hch hne hleaf

/-- "If the code within the with block raises a `BaseExceptionGroup`, suppressed exceptions are
removed from the group" (Doc/library/contextlib.rst): a group of leaves, each of which `suppress`
suppresses when it is raised alone, is suppressed. Refuted: `issubclass` (:524) honours
`__subclasscheck__`, the group's `split` (:527) matches by the concrete class. With `E`, an
exception class with metaclass `ABCMeta` that registered `KeyError`, `suppress(E)` suppresses a
bare `KeyError` and re-raises `ExceptionGroup([KeyError()])` as a new group. -/
def SuppressGroupConsistent : Prop :=
  ∀ (σ : Type) (items : List (SupItem σ)) (s : St σ) (e : ExcId) (cs : List ExcId),
    (s.h.get e).children = some cs → s.h.isInst e "BaseExceptionGroup" = true →
    (∀ c ∈ cs, (s.h.get c).children = none ∧
      (suppressExit items builtinDerive s (some c) (some (.cls (s.h.get c).cls)) (some c)).map (·.2) =
        .ok (.ok (some true))) →
    (suppressExit items builtinDerive s (some e) (some (.cls (s.h.get e).cls)) (some e)).map (·.2) =
      .ok (.ok (some true))

/-- `E`: an exception class whose metaclass is `ABCMeta`, with `KeyError` registered. -/
def abcItem : SupItem Unit :=
  .hook (fun d s => (s, .ok (match d with
    | .cls c => c.contains "KeyError"
    | .other => false))) (some ["E", "Exception", "BaseException"])

/-- A `KeyError`, and an `ExceptionGroup` of it. -/
def abcHeap : Heap :=
  [{ cls := ["KeyError", "LookupError", "Exception", "BaseException"] },
   { cls := clsEG, msg := "x", children := some [0] }]

theorem suppressGroupConsistent_refuted : ¬SuppressGroupConsistent := by
  intro h
  have hmember : (suppressExit [abcItem] builtinDerive { h := abcHeap, g := () } (some 0)
      (some (Derived.cls (({ h := abcHeap, g := () } : St Unit).h.get 0).cls)) (some 0)).map (·.2) =
      .ok (.ok (some true)) := by rfl
  have hgroup : (suppressExit [abcItem] builtinDerive { h := abcHeap, g := () } (some 1)
      (some (Derived.cls (({ h := abcHeap, g := () } : St Unit).h.get 1).cls)) (some 1)).map (·.2) =
      .ok (.error 2) := by rfl
  have := h Unit [abcItem] { h := abcHeap, g := () } 1 [0] rfl (by decide)
    (by
      intro c hc
      simp at hc
      subst hc
      exact ⟨rfl, hmember⟩)
  rw [hgroup] at this
  simp at this

end PyLean.CoreLibs.Misc.Contextlib
