import PyLean.TypeObj.PropsMro
import PyLean.TypeObj.Wrappers

/-!
Properties of the `slot_*` dispatchers, the `lookup_method` family, `__getattr__` hooks,
slot wrappers and the C API entry points.
-/

namespace PyLean.TypeObj

/-! ## Special method lookup ignores the instance -/

/-- **Special methods are looked up on the type.** If no class in the MRO has `attr`,
`_PyObject_LookupSpecial` finds nothing, even with `attr` in the instance dict: the
"Special method lookup" section of the data model. -/
def SpecialLookupIgnoresInstance : Prop :=
  ∀ (rt : Rt) (self : Val) (attr : Name) (w : World),
    findInMro w (typeOf w self) attr = none →
    lookupSpecial rt self attr w = .ok none w ∧
    (match lookupMethodEx rt self attr false w with
     | .ok .missing w' => w' = w
     | _ => False)

theorem specialLookupIgnoresInstance_proven : SpecialLookupIgnoresInstance := by
  intro rt self attr w h
  simp [lookupSpecial, lookupMethodEx, h]

/-- A function found on the type is not bound: `lookup_method_ex` returns it unbound and
`vectorcall_unbound` keeps `self` first, the same call a bound method would make. -/
def LookupMethodDescriptorUnbound : Prop :=
  ∀ (rt : Rt) (self f : Val) (attr : Name) (args : List Val) (raiseAE : Bool) (w : World),
    findInMro w (typeOf w self) attr = some f →
    (tdata w (typeOf w f)).methodDescriptor = true →
    lookupMethodEx rt self attr raiseAE w = .ok (.unbound f) w ∧
    callUnbound rt (.unbound f) (self :: args) w = rt.call f (self :: args) [] w

theorem lookupMethodDescriptorUnbound_proven : LookupMethodDescriptorUnbound := by
  intro rt self f attr args raiseAE w h1 h2
  simp [lookupMethodEx, callUnbound, h1, h2]

/-- `lookup_method` raises `AttributeError(name)` for a missing special method;
`vectorcall_maybe` answers `NotImplemented`. -/
def MissingMethodOutcomes : Prop :=
  ∀ (rt : Rt) (self : Val) (attr : Name) (args : List Val) (w : World),
    findInMro w (typeOf w self) attr = none →
    vectorcallMethod rt attr (self :: args) w = (attrErr attr : M Val) w ∧
    vectorcallMaybe rt attr (self :: args) w = .ok .notImpl w

theorem missingMethodOutcomes_proven : MissingMethodOutcomes := by
  intro rt self attr args w h
  simp [vectorcallMethod, vectorcallMaybe, lookupMethodEx, h, attrErr, raiseC]

/-- A class attribute of `None` for a special method counts as "defined as None" only for
the callers that ask (`__hash__`, `__iter__`, `__contains__`, `__bool__`). -/
def MaybeCallNone : Prop :=
  ∀ (rt : Rt) (self : Val) (attr : Name) (args : List Val) (w : World),
    findInMro w (typeOf w self) attr = some .none →
    (tdata w (typeOf w Val.none)).methodDescriptor = false →
    slotOf w (typeOf w Val.none) .tp_descr_get = none →
    maybeCallSpecial rt self attr args true w = .ok .isNone w

theorem maybeCallNone_proven : MaybeCallNone := by
  intro rt self attr args w h1 h2 h3
  simp [maybeCallSpecial, lookupMethodEx, h1, h2, h3, Val.is]

/-! ## `__getattr__` -/

/-- **`__getattr__` runs only when normal lookup fails.** With the default
`__getattribute__`, a name found by generic lookup is returned and the hook never runs. -/
def GetattrHookNotCalledWhenFound : Prop :=
  ∀ (rt : Rt) (self v getattr : Val) (n : Name) (w w1 : World),
    findInMro w (typeOf w self) "__getattr__" = some getattr →
    (findInMro w (typeOf w self) "__getattribute__" = none) →
    genericGetAttrSup rt self n true w = .ok (some v) w1 →
    slotTpGetattrHook rt self n w = .ok v w1

theorem getattrHookNotCalledWhenFound_proven : GetattrHookNotCalledWhenFound := by
  intro rt self v getattr n w w1 h1 h2 h3
  simp [slotTpGetattrHook, h1, h2, h3]

/-- ... and it does run, with the name, when the lookup misses. -/
def GetattrHookCalledWhenMissing : Prop :=
  ∀ (rt : Rt) (self getattr : Val) (n : Name) (w w1 : World),
    findInMro w (typeOf w self) "__getattr__" = some getattr →
    (findInMro w (typeOf w self) "__getattribute__" = none) →
    genericGetAttrSup rt self n true w = .ok none w1 →
    slotTpGetattrHook rt self n w = callAttribute rt self getattr n w1

theorem getattrHookCalledWhenMissing_proven : GetattrHookCalledWhenMissing := by
  intro rt self getattr n w w1 h1 h2 h3
  simp [slotTpGetattrHook, h1, h2, h3]

/-- **A user `__getattribute__` that raises `AttributeError` falls back to `__getattr__`**;
any other exception propagates, `Objects/typeobject.c:10430`. -/
def GetattributeAttributeErrorFallback : Prop :=
  ∀ (rt : Rt) (self getattr ga : Val) (n : Name) (e : PyErr) (w w1 : World),
    findInMro w (typeOf w self) "__getattr__" = some getattr →
    findInMro w (typeOf w self) "__getattribute__" = some ga →
    (typeOf w ga = B.wrapperDescr → False) →
    callAttribute rt self ga n w = .err e w1 →
    slotTpGetattrHook rt self n w =
      (if excMatches w1 e B.AttributeError then callAttribute rt self getattr n w1
       else .err e w1)

theorem getattributeAttributeErrorFallback_proven : GetattributeAttributeErrorFallback := by
  intro rt self getattr ga n e w w1 h1 h2 h3 h4
  have hne : (typeOf w ga == B.wrapperDescr) = false := by
    simpa using h3
  simp only [slotTpGetattrHook, M.bind_app, getW_app, h1, h2, hne, Bool.false_and,
    Bool.false_eq_true, ite_false, catchMatch, tryM_app, h4]
  split <;> simp

/-- A class with `__getattribute__` but no `__getattr__` uses the simple dispatcher. -/
def NoHookSimpleDispatch : Prop :=
  ∀ (rt : Rt) (self : Val) (n : Name) (w : World),
    findInMro w (typeOf w self) "__getattr__" = none →
    slotTpGetattrHook rt self n w = slotTpGetattro rt self n w

theorem noHookSimpleDispatch_proven : NoHookSimpleDispatch := by
  intro rt self n w h
  simp [slotTpGetattrHook, h]

/-- **`PyObject_GetOptionalAttr` agrees with `PyObject_GetAttr` on a found attribute**, for
the generic path: the suppressing variant differs only on failure. -/
def OptionalAttrAgrees : Prop :=
  ∀ (rt : Rt) (obj v : Val) (n : Name) (w w1 : World),
    genericGetAttrSup rt obj n false w = .ok (some v) w1 →
    genericGetAttrSup rt obj n true w = .ok (some v) w1

theorem runDescrGet_found (rt : Rt) (fn : SlotFn) (d obj tv v : Val) (w w1 : World)
    (h : runDescrGet rt fn d obj tv false w = .ok (some v) w1) :
    runDescrGet rt fn d obj tv true w = .ok (some v) w1 := by
  simp only [runDescrGet, Bool.false_eq_true, ite_false, map_app] at h
  simp only [runDescrGet, ite_true, catchMatch, tryM_app, map_app]
  cases hc : callDescrGet rt fn d (some obj) (some tv) w with
  | ok a w2 =>
    rw [hc] at h
    simpa using h
  | err e w2 =>
    rw [hc] at h
    simp at h

/-- A computation that never returns normally. -/
def NotOk {α : Type} (m : M α) : Prop := ∀ a w w', m w ≠ .ok a w'

theorem notOk_raise {α : Type} (e : PyErr) : NotOk (raise e : M α) := by
  intro a w w' h
  simp at h

theorem notOk_bind {α β : Type} (x : M α) (f : α → M β) (h : ∀ a, NotOk (f a)) :
    NotOk (x >>= f) := by
  intro a w w' he
  simp only [M.bind_app] at he
  cases hx : x w with
  | ok b w1 =>
    rw [hx] at he
    exact h b a w1 w' he
  | err e w1 =>
    rw [hx] at he
    simp at he

/-- `_PyObject_SetAttributeErrorContext` always leaves an exception set. -/
theorem setAttributeErrorContext_not_ok {α : Type} (v : Val) (n : Name) (e : PyErr) :
    NotOk (setAttributeErrorContext v n e : M α) := by
  intro a w w' h
  simp only [setAttributeErrorContext, M.bind_app, getW_app] at h
  by_cases hm : excMatches w e B.AttributeError = true
  · simp only [hm, ite_true] at h
    exact notOk_bind _ _ (fun x => notOk_bind _ _ (fun _ => notOk_raise _)) a w w' h
  · simp [hm] at h

theorem genericTail_found (rt : Rt) (obj : Val) (n : Name) (descr : Option Val)
    (f : Option SlotFn) (v : Val) (w w1 : World)
    (h : genericGetAttrTail rt obj n descr f false w = .ok (some v) w1) :
    genericGetAttrTail rt obj n descr f true w = .ok (some v) w1 := by
  simp only [genericGetAttrTail, M.bind_app, getW_app] at h ⊢
  cases hi : instDictGet w obj n with
  | some x => rw [hi] at h; simpa using h
  | none =>
    rw [hi] at h
    simp only at h ⊢
    have hmiss : ∀ (hd : descr = none), False := by
      intro hd
      subst hd
      have hn := setAttributeErrorContext_not_ok (α := Option Val) obj n
        (.exc B.AttributeError
          s!"'{trunc 100 (tpName w (typeOf w obj))}' object has no attribute '{n}'" none)
        (some v) w w1
      cases f with
      | some fn =>
        simp only [Bool.false_eq_true, ite_false, tryM_app, raiseC, raise_app] at h
        exact hn h
      | none =>
        simp only [Bool.false_eq_true, ite_false, tryM_app, raiseC, raise_app] at h
        exact hn h
    cases hd : descr with
    | none => exact (hmiss hd).elim
    | some d =>
      subst hd
      cases hf : f with
      | some fn =>
        subst hf
        exact runDescrGet_found rt fn d obj _ v w w1 h
      | none =>
        subst hf
        simpa using h

theorem optionalAttrAgrees_proven : OptionalAttrAgrees := by
  intro rt obj v n w w1 h
  simp only [genericGetAttrSup, M.bind_app, getW_app] at h ⊢
  cases hd : findInMro w (typeOf w obj) n with
  | none =>
    rw [hd] at h
    exact genericTail_found rt obj n none none v w w1 h
  | some d =>
    rw [hd] at h
    simp only at h ⊢
    cases hf : slotOf w (typeOf w d) .tp_descr_get with
    | none =>
      rw [hf] at h
      exact genericTail_found rt obj n (some d) none v w w1 h
    | some fn =>
      rw [hf] at h
      simp only at h ⊢
      by_cases hi : isDataDescr w d = true
      · simp only [hi, ite_true] at h ⊢
        exact runDescrGet_found rt fn d obj _ v w w1 h
      · simp only [hi, ite_false, Bool.false_eq_true] at h ⊢
        exact genericTail_found rt obj n (some d) (some fn) v w w1 h

/-! ## `__setattr__`, items -/

/-- `slot_tp_setattro` sends assignment to `__setattr__` and deletion to `__delattr__`. -/
def SlotSetattrDispatch : Prop :=
  ∀ (rt : Rt) (self v : Val) (n : Name) (w : World),
    slotTpSetattro rt self n (some v) w =
      ((do let _ ← vectorcallMethod rt "__setattr__" [self, .str n, v]; pure ()) : M Unit) w ∧
    slotTpSetattro rt self n none w =
      ((do let _ ← vectorcallMethod rt "__delattr__" [self, .str n]; pure ()) : M Unit) w

theorem slotSetattrDispatch_proven : SlotSetattrDispatch := by
  intro rt self v n w
  simp [slotTpSetattro]

/-- `slot_tp_descr_set` likewise: `__set__` for assignment, `__delete__` for deletion. -/
def SlotDescrSetDispatch : Prop :=
  ∀ (rt : Rt) (self t v : Val) (w : World),
    slotTpDescrSet rt self t (some v) w =
      ((do let _ ← vectorcallMethod rt "__set__" [self, t, v]; pure ()) : M Unit) w ∧
    slotTpDescrSet rt self t none w =
      ((do let _ ← vectorcallMethod rt "__delete__" [self, t]; pure ()) : M Unit) w

theorem slotDescrSetDispatch_proven : SlotDescrSetDispatch := by
  intro rt self t v w
  simp [slotTpDescrSet]

/-- `slot_tp_descr_get` passes `None` for a missing instance or type, and returns the
descriptor unchanged if `__get__` went away, `Objects/typeobject.c:10529-10544`. -/
def SlotDescrGetArgs : Prop :=
  ∀ (rt : Rt) (self get : Val) (ty : Val) (w : World),
    (findInMro w (typeOf w self) "__get__" = some get →
      slotTpDescrGet rt self none (some ty) w = rt.call get [self, .none, ty] [] w) ∧
    (findInMro w (typeOf w self) "__get__" = none →
      slotTpDescrGet rt self none (some ty) w = .ok self w)

theorem slotDescrGetArgs_proven : SlotDescrGetArgs := by
  intro rt self get ty w
  constructor
  · intro h; simp [slotTpDescrGet, h]
  · intro h; simp [slotTpDescrGet, h]

/-- `slot_tp_richcompare` answers `NotImplemented` when the method is missing. -/
def SlotRichcompareMissing : Prop :=
  ∀ (rt : Rt) (self other : Val) (op : CmpOp) (w : World),
    findInMro w (typeOf w self) op.dunder = none →
    slotTpRichcompare rt self other op w = .ok .notImpl w

theorem slotRichcompareMissing_proven : SlotRichcompareMissing := by
  intro rt self other op w h
  simp [slotTpRichcompare, maybeCallSpecial, lookupMethodEx, h]

/-- `slot_tp_new`: `__new__` found by `getattr` on the class is called with the class
first. -/
def SlotNewPrependsType : Prop :=
  ∀ (rt : Rt) (t : Addr) (func : Val) (args : List Val) (kw : Kw) (w w1 : World),
    rt.getAttr (.obj t) "__new__" w = .ok func w1 →
    slotTpNew rt t args kw w = rt.call func (.obj t :: args) kw w1

theorem slotNewPrependsType_proven : SlotNewPrependsType := by
  intro rt t func args kw w w1 h
  simp [slotTpNew, h]

/-- **`SLOT1BINFULL`, same type**: for operands of one type a `NotImplemented` from
`__add__` is the result, and `__radd__` never runs. -/
def Slot1BinSameType : Prop :=
  ∀ (rt : Rt) (s : Slot) (d rd : Name) (a b : Val) (w w1 : World),
    typeOf w a = typeOf w b →
    slotIn w a s = some .generic →
    vectorcallMaybe rt d [a, b] w = .ok .notImpl w1 →
    typeOf w1 a = typeOf w1 b →
    slot1Bin rt s d rd a b [] w = .ok .notImpl w1

theorem slot1BinSameType_proven : Slot1BinSameType := by
  intro rt s d rd a b w w1 h1 h2 h3 h4
  simp [slot1Bin, h1, h2, h3, ← h4]

/-- `method_is_overloaded`: a right operand type without the name is not overloaded; one
having it while the left type lacks it is. -/
def MethodIsOverloadedTable : Prop :=
  ∀ (rt : Rt) (l r b : Val) (n : Name) (w w1 w2 : World),
    (rt.getOptionalAttr (.obj (typeOf w r)) n w = .ok none w1 →
      methodIsOverloaded rt l r n w = .ok false w1) ∧
    (rt.getOptionalAttr (.obj (typeOf w r)) n w = .ok (some b) w1 →
      rt.getOptionalAttr (.obj (typeOf w1 l)) n w1 = .ok none w2 →
      methodIsOverloaded rt l r n w = .ok true w2)

theorem methodIsOverloadedTable_proven : MethodIsOverloadedTable := by
  intro rt l r b n w w1 w2
  constructor
  · intro h; simp [methodIsOverloaded, h]
  · intro h1 h2; simp [methodIsOverloaded, h1, h2]

/-! ## Slot wrappers -/

/-- **`x.__add__(y)` calls the slot function with `(x, y)`, and `x.__radd__(y)` with
`(y, x)`**: `wrap_binaryfunc_l` and `wrap_binaryfunc_r`, `Objects/typeobject.c:9304-9326`. -/
def WrapBinarySwaps : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self other : Val) (w : World),
    (p.wrapper = some .binaryR →
      wrapperApply rt p f self [other] [] w = callNbBinary rt p.slot f other self w) ∧
    (p.wrapper = some .binaryL → p.slot.group = .number →
      wrapperApply rt p f self [other] [] w = callNbBinary rt p.slot f self other w)

/-- `wrapper_call` applies the wrapper to the bound `self`. -/
def WrapperArityChecked : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (w : World),
    p.wrapper = some .unary → args ≠ [] →
    wrapperApply rt p f self args [] w = (typeErr (argCountMsg 0 args.length) : M Val) w

/-- Wrappers other than `__call__` and `__init__` reject keywords,
`Objects/descrobject.c:526-531`. -/
def WrapperRejectsKeywords : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (args : List Val) (kw : Kw) (wr : WrapKind)
    (w : World),
    p.wrapper = some wr → wr ≠ .call → wr ≠ .init → kw ≠ [] →
    wrapperApply rt p f self args kw w =
      (typeErr s!"wrapper {p.name}() takes no keyword arguments" : M Val) w

theorem wrapBinarySwaps_proven : WrapBinarySwaps := by
  intro rt p f self other w
  obtain ⟨n, s, g, wr⟩ := p
  constructor
  · intro h
    simp only at h
    subst h
    simp [wrapperApply, checkNumArgs]
  · intro h hg
    simp only at h hg
    subst h
    cases s <;> simp_all [wrapperApply, checkNumArgs, Slot.group]

theorem wrapperArityChecked_proven : WrapperArityChecked := by
  intro rt p f self args w h1 h2
  have hl : args.length ≠ 0 := by simpa using h2
  simp [wrapperApply, h1, checkNumArgs, hl, typeErr, raiseC]

theorem wrapperRejectsKeywords_proven : WrapperRejectsKeywords := by
  intro rt p f self args kw wr w h1 h2 h3 h4
  have hk : kw.isEmpty = false := by
    cases kw with
    | nil => exact (h4 rfl).elim
    | cons _ _ => rfl
  cases wr <;> simp_all [wrapperApply, typeErr, raiseC]

/-! ## C API wrappers -/

/-- `PyObject_DelAttr` is `PyObject_SetAttr` with NULL, and the `*String` forms equal the
object-name forms. -/
def AttrStringForms : Prop :=
  ∀ (rt : Rt) (v : Val) (n : Name) (w : World),
    pyGetAttrString rt v n w = rt.getAttr v n w ∧
    pyDelAttr rt v n w = rt.setAttr v n none w ∧
    pyGetOptionalAttrString rt v n w = rt.getOptionalAttr v n w

theorem attrStringForms_proven : AttrStringForms := by
  intro rt v n w
  simp [pyGetAttrString, pyDelAttr, pyGetOptionalAttrString]

/-- `hasattr` is true exactly when `PyObject_GetOptionalAttr` found something. -/
def HasAttrIffOptional : Prop :=
  ∀ (rt : Rt) (v : Val) (n : Name) (r : Option Val) (w w1 : World),
    rt.getOptionalAttr v n w = .ok r w1 → pyHasAttrWithError rt v n w = .ok r.isSome w1

theorem hasAttrIffOptional_proven : HasAttrIffOptional := by
  intro rt v n r w w1 h
  simp [pyHasAttrWithError, h]

/-- `PyObject_Not` negates `PyObject_IsTrue`. -/
def NotNegates : Prop :=
  ∀ (rt : Rt) (v : Val) (b : Bool) (w w1 : World),
    rt.isTrue v w = .ok b w1 → pyNot rt v w = .ok (!b) w1

theorem notNegates_proven : NotNegates := by
  intro rt v b w w1 h
  simp [pyNot, h]

/-- `callable(x)` is true exactly when `type(x)` has `tp_call`; calling something without
it raises the exact `TypeError`. -/
def CallableCheck : Prop :=
  ∀ (rt : Rt) (x : Val) (args : List Val) (kw : Kw) (w : World),
    pyCallableCheck w x = false →
    pyCall rt x args kw w =
      (typeErr s!"'{trunc 200 (typeName w x)}' object is not callable" : M Val) w

theorem callableCheck_proven : CallableCheck := by
  intro rt x args kw w h
  have h' : slotOf w (typeOf w x) .tp_call = none := by
    simpa [pyCallableCheck] using h
  simp [pyCall, h', typeName]

/-- `Py_Is` is reflexive and `Py_IsNone` recognises `None`. -/
def IsReflexive : Prop := ∀ x : Val, pyIs x x = true

theorem isReflexive_proven : IsReflexive := Val.is_refl

/-- `PySequence_Concat` falls back to `nb_add` only for two sequences. -/
def SequenceConcatFallback : Prop :=
  ∀ (rt : Rt) (s o : Val) (w : World),
    slotIn w s .sq_concat = none → pySequenceCheck w s = false →
    pySequenceConcat rt s o w =
      (typeErr s!"'{trunc 200 (typeName w s)}' object can't be concatenated" : M Val) w

theorem sequenceConcatFallback_proven : SequenceConcatFallback := by
  intro rt s o w h1 h2
  simp [pySequenceConcat, h1, h2]

/-- `PySequence_Repeat` passes the count to `nb_multiply` as an int only for sequences. -/
def SequenceRepeatFallback : Prop :=
  ∀ (rt : Rt) (o : Val) (c : Int) (w : World),
    slotIn w o .sq_repeat = none → pySequenceCheck w o = false →
    pySequenceRepeat rt o c w =
      (typeErr s!"'{trunc 200 (typeName w o)}' object can't be repeated" : M Val) w

theorem sequenceRepeatFallback_proven : SequenceRepeatFallback := by
  intro rt o c w h1 h2
  simp [pySequenceRepeat, h1, h2]

/-- In-place concatenation prefers `sq_inplace_concat`, then `sq_concat`. -/
def SequenceInPlaceConcatOrder : Prop :=
  ∀ (rt : Rt) (s o : Val) (f : SlotFn) (w : World),
    slotIn w s .sq_inplace_concat = some f →
    pySequenceInPlaceConcat rt s o w = callSqConcat rt f s o w

theorem sequenceInPlaceConcatOrder_proven : SequenceInPlaceConcatOrder := by
  intro rt s o f w h
  simp [pySequenceInPlaceConcat, h]

/-- `PyMapping_GetOptionalItem` turns `KeyError` into "absent". -/
def MappingOptionalItem : Prop :=
  ∀ (rt : Rt) (o k : Val) (e : PyErr) (w w1 : World),
    typeOf w o ≠ B.dict → pyGetItem rt o k w = .err e w1 → excMatches w1 e B.KeyError = true →
    pyMappingGetOptionalItem rt o k w = .ok none w1

theorem mappingOptionalItem_proven : MappingOptionalItem := by
  intro rt o k e w w1 h1 h2 h3
  simp [pyMappingGetOptionalItem, h1, catchMatch, h2, h3]

/-- `PyObject_CallObject` with `NULL`-like `None` args calls with no arguments, and a
tuple is unpacked. -/
def CallObjectArgs : Prop :=
  ∀ (rt : Rt) (f : Val) (xs : List Val) (w : World),
    pyCallObject rt f .none w = rt.call f [] [] w ∧
    pyCallObject rt f (.tuple xs) w = rt.call f xs [] w

theorem callObjectArgs_proven : CallObjectArgs := by
  intro rt f xs w
  simp [pyCallObject, tupleOf]

/-- The call family all reduce to `PyObject_Call`. -/
def CallFamily : Prop :=
  ∀ (rt : Rt) (f a : Val) (args : List Val) (kw : Kw) (w : World),
    pyCallNoArgs rt f w = rt.call f [] [] w ∧ pyCallOneArg rt f a w = rt.call f [a] [] w ∧
    pyCallPrepend rt f a args kw w = rt.call f (a :: args) kw w

theorem callFamily_proven : CallFamily := by
  intro rt f a args kw w
  simp [pyCallNoArgs, pyCallOneArg, pyCallPrepend]

/-- `PyVectorcall_NARGS` drops `PY_VECTORCALL_ARGUMENTS_OFFSET` and keeps smaller counts. -/
def VectorcallNargs : Prop :=
  ∀ n, n < 2 ^ 63 → vectorcallNargs n = n ∧ vectorcallNargs (n + 2 ^ 63) = n

theorem vectorcallNargs_proven : VectorcallNargs := by
  intro n h
  simp only [vectorcallNargs]
  constructor
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt h

end PyLean.TypeObj
