import PyLean.TypeObj.PropsTypeNew

/-!
Remaining properties of `Objects/object.c`, `Objects/abstract.c` and the wrappers of
`Objects/typeobject.c`.
-/

namespace PyLean.TypeObj

/-! ## repr, str, hash -/

/-- `repr()` and `str()` enforce a string result, for every `__repr__`/`__str__`,
`Objects/object.c:791`, `:833`. -/
def ReprMustReturnStr : Prop :=
  ∀ (rt : Rt) (v r : Val) (f : SlotFn) (w w1 : World),
    slotOf w (typeOf w v) .tp_repr = some f →
    callRepr rt f v w = .ok r w1 → strOf w1 r = none →
    pyRepr rt v w =
      (typeErr s!"__repr__ returned non-string (type {trunc 200 (typeName w1 r)})" : M String) w1

theorem reprMustReturnStr_proven : ReprMustReturnStr := by
  intro rt v r f w w1 h1 h2 h3
  simp [pyRepr, h1, h2, h3]

def StrMustReturnStr : Prop :=
  ∀ (rt : Rt) (v r : Val) (f : SlotFn) (w w1 : World),
    (∀ s, v ≠ .str s) → slotOf w (typeOf w v) .tp_str = some f →
    callStr rt f v w = .ok r w1 → strOf w1 r = none →
    pyStr rt v w =
      (typeErr s!"__str__ returned non-string (type {trunc 200 (typeName w1 r)})" : M String) w1

theorem strMustReturnStr_proven : StrMustReturnStr := by
  intro rt v r f w w1 h0 h1 h2 h3
  cases v with
  | str s => exact (h0 s rfl).elim
  | _ => simp [pyStr, h1, h2, h3]

/-- `str(s)` of an exact `str` is `s`, `Objects/object.c:808`. -/
def StrExactShortcut : Prop := ∀ (rt : Rt) (s : String) (w : World), pyStr rt (.str s) w = .ok s w

theorem strExactShortcut_proven : StrExactShortcut := by
  intro rt s w
  simp [pyStr]

/-- A type with no `tp_hash` is unhashable, `Objects/object.c:1176`. -/
def HashNoSlot : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World),
    slotOf w (typeOf w v) .tp_hash = none →
    pyHash rt v w = (typeErr s!"unhashable type: '{trunc 200 (typeName w v)}'" : M Int) w

theorem hashNoSlot_proven : HashNoSlot := by
  intro rt v w h
  simp [pyHash, h, hashNotImplemented]

/-- `hash(x)` for an int is `x` modulo `2**61 - 1` with sign, `-1` replaced by `-2`, so it
is `-1` for no int. -/
def LongHashNotMinusOne : Prop := ∀ i : Int, longHash i ≠ -1

theorem longHashNotMinusOne_proven : LongHashNotMinusOne := by
  intro i
  have key : ∀ h : Int, (if (h == -1) = true then (-2 : Int) else h) ≠ -1 := by
    intro h
    by_cases hh : h = -1 <;> simp [hh]
  exact key _

/-! ## Attribute errors -/

/-- `_PyObject_SetAttributeErrorContext` leaves other exceptions alone. -/
def AttrContextOnlyAttributeError : Prop :=
  ∀ (v : Val) (n : Name) (e : PyErr) (w : World),
    excMatches w e B.AttributeError = false →
    (setAttributeErrorContext v n e : M Val) w = .err e w

theorem attrContextOnlyAttributeError_proven : AttrContextOnlyAttributeError := by
  intro v n e w h
  simp [setAttributeErrorContext, h]

/-- A type without `tp_setattro` cannot be assigned to: the messages of
`Objects/object.c:1550-1563`. -/
def SetAttrNoSlot : Prop :=
  ∀ (rt : Rt) (v x : Val) (n : Name) (w : World),
    slotOf w (typeOf w v) .tp_setattro = none →
    (slotOf w (typeOf w v) .tp_getattro).isSome = true →
    pySetAttr rt v n (some x) w =
      (typeErr (roAttrMsg (typeName w v) "assign to" n) : M Unit) w

theorem setAttrNoSlot_proven : SetAttrNoSlot := by
  intro rt v x n w h1 h2
  have h3 : slotOf w (typeOf w v) .tp_getattro ≠ none := by
    cases hg : slotOf w (typeOf w v) .tp_getattro <;> simp_all
  simp [pySetAttr, h1, h3, typeName]

/-- **`_PyObject_GetMethod` on a method descriptor**: not shadowed by the instance dict it
stays unbound; a name in the instance dict wins, as in generic getattr. -/
def GetMethodDescriptor : Prop :=
  ∀ (rt : Rt) (obj d v : Val) (n : Name) (w : World),
    slotOf w (typeOf w obj) .tp_getattro = some (.c .object) →
    findInMro w (typeOf w obj) n = some d →
    (tdata w (typeOf w d)).methodDescriptor = true →
    (instDictGet w obj n = none → pyGetMethod rt obj n w = .ok (d, true) w) ∧
    (instDictGet w obj n = some v → pyGetMethod rt obj n w = .ok (v, false) w)

theorem getMethodDescriptor_proven : GetMethodDescriptor := by
  intro rt obj d v n w h1 h2 h3
  constructor
  · intro h; simp [pyGetMethod, h1, h2, h3, h]
  · intro h; simp [pyGetMethod, h1, h2, h3, h]

/-- `__dict__` must be set to a dict, `Objects/typeobject.c:4062`. -/
def SetDictRequiresDict : Prop :=
  ∀ (obj v : Val) (w : World),
    dictOf w v = none →
    objectSetDict obj (some v) w =
      (typeErr s!"__dict__ must be set to a dictionary, not a '{trunc 200 (typeName w v)}'" : M Unit) w

theorem setDictRequiresDict_proven : SetDictRequiresDict := by
  intro obj v w h
  simp [objectSetDict, h]

/-- `__dict__` access on an object with no dict raises, `Objects/dictobject.c:8067`. -/
def GetDictRequiresDictPtr : Prop :=
  ∀ (obj : Val) (w : World),
    hasDictPtr w obj = false →
    genericGetDict obj w = (attrErr "This object has no __dict__" : M Val) w

theorem getDictRequiresDictPtr_proven : GetDictRequiresDictPtr := by
  intro obj w h
  simp [genericGetDict, h]

/-! ## Sizes and items -/

/-- `len()`: `sq_length` first, then `mp_length`; neither is the exact `TypeError`. -/
def ObjectSizeOrder : Prop :=
  ∀ (rt : Rt) (o : Val) (f : SlotFn) (w : World),
    (slotIn w o .sq_length = some f → pyObjectSize rt o w = callLen rt f o w) ∧
    (slotIn w o .sq_length = none → slotIn w o .mp_length = some f →
      pyObjectSize rt o w = callLen rt f o w) ∧
    (slotIn w o .sq_length = none → slotIn w o .mp_length = none →
      pyObjectSize rt o w =
        (typeErr s!"object of type '{trunc 200 (typeName w o)}' has no len()" : M Int) w)

theorem objectSizeOrder_proven : ObjectSizeOrder := by
  intro rt o f w
  refine ⟨?_, ?_, ?_⟩
  · intro h; simp [pyObjectSize, h]
  · intro h1 h2; simp [pyObjectSize, pyMappingSize, h1, h2]
  · intro h1 h2; simp [pyObjectSize, pyMappingSize, h1, h2]

/-- `PySequence_Size` refuses a mapping; `PyMapping_Size` refuses a sequence. -/
def SizeProtocolsDistinct : Prop :=
  ∀ (rt : Rt) (o : Val) (f : SlotFn) (w : World),
    (slotIn w o .sq_length = none → slotIn w o .mp_length = some f →
      pySequenceSize rt o w = (typeErr s!"{trunc 200 (typeName w o)} is not a sequence" : M Int) w) ∧
    (slotIn w o .mp_length = none → slotIn w o .sq_length = some f →
      pyMappingSize rt o w = (typeErr s!"{trunc 200 (typeName w o)} is not a mapping" : M Int) w)

theorem sizeProtocolsDistinct_proven : SizeProtocolsDistinct := by
  intro rt o f w
  constructor
  · intro h1 h2; simp [pySequenceSize, h1, h2]
  · intro h1 h2; simp [pyMappingSize, h1, h2]

/-- `PyObject_LengthHint`: a `TypeError` from `__len__` falls through to
`__length_hint__`, and with neither the default is returned. -/
def LengthHintDefault : Prop :=
  ∀ (rt : Rt) (o : Val) (dflt : Int) (w : World),
    hasLen w o = false → findInMro w (typeOf w o) "__length_hint__" = none →
    pyLengthHint rt o dflt w = .ok dflt w

theorem lengthHintDefault_proven : LengthHintDefault := by
  intro rt o dflt w h1 h2
  simp [pyLengthHint, h1, lookupSpecial, h2]

/-- `__length_hint__` results: `NotImplemented` means the default. -/
def LengthHintNotImplemented : Prop :=
  ∀ (rt : Rt) (o hint : Val) (dflt : Int) (w w1 w2 : World),
    hasLen w o = false → lookupSpecial rt o "__length_hint__" w = .ok (some hint) w1 →
    rt.call hint [] [] w1 = .ok .notImpl w2 →
    pyLengthHint rt o dflt w = .ok dflt w2

theorem lengthHintNotImplemented_proven : LengthHintNotImplemented := by
  intro rt o hint dflt w w1 w2 h1 h2 h3
  simp [pyLengthHint, h1, h2, catchMatch, h3]

/-- `o[k] = v` prefers `mp_ass_subscript`, `Objects/abstract.c:243-248`. -/
def SetItemMappingFirst : Prop :=
  ∀ (rt : Rt) (o k : Val) (value : Option Val) (f : SlotFn) (w : World),
    slotIn w o .mp_ass_subscript = some f →
    pySetItem rt o k value w = callAssSubscript rt f o k value w

theorem setItemMappingFirst_proven : SetItemMappingFirst := by
  intro rt o k value f w h
  simp [pySetItem, h]

/-- `PySequence_SetItem` adds the length to a negative index before `sq_ass_item`. -/
def SequenceSetItemNegative : Prop :=
  ∀ (rt : Rt) (s : Val) (i n : Int) (value : Option Val) (f lf : SlotFn) (w w1 : World),
    i < 0 → slotIn w s .sq_ass_item = some f → slotIn w s .sq_length = some lf →
    callLen rt lf s w = .ok n w1 →
    pySequenceSetItem rt s i value w = callAssSubscript rt f s (.int (i + n)) value w1

theorem sequenceSetItemNegative_proven : SequenceSetItemNegative := by
  intro rt s i n value f lf w w1 hi h1 h2 h3
  simp [pySequenceSetItem, h1, h2, h3, hi]

/-! ## Numbers -/

/-- **`ternary_op`**: same-type operands use one slot; the third operand's slot is tried
last, and a type error names two or three types according to `z is None`,
`Objects/abstract.c:1085-1120`. -/
def TernaryNoSlots : Prop :=
  ∀ (rt : Rt) (v u : Val) (name : String) (w : World),
    slotIn w v .nb_power = none → slotIn w u .nb_power = none →
    slotIn w Val.none .nb_power = none →
    ternaryOp rt v u .none name w =
      (typeErr s!"unsupported operand type(s) for {trunc 100 name}: '{trunc 100 (typeName w v)}' and '{trunc 100 (typeName w u)}'" : M Val) w

theorem ternaryNoSlots_proven : TernaryNoSlots := by
  intro rt v u name w h1 h2 h3
  simp [ternaryOp, h1, h2, h3, Val.is]

/-- `x += y` tries `__iadd__` first; a non-`NotImplemented` result is final and `+` never
runs, `Objects/abstract.c:1234-1245`. -/
def InPlaceFirst : Prop :=
  ∀ (rt : Rt) (v u r : Val) (w w1 : World) (islot s : Slot),
    slotIn w v islot = some .generic →
    vectorcallMethod rt (binaryIop1.nbOpOfISlot islot).idunder [v, u] w = .ok r w1 →
    r.is .notImpl = false →
    binaryIop1 rt v u islot s w = .ok r w1

theorem inPlaceFirst_proven : InPlaceFirst := by
  intro rt v u r w w1 islot s h1 h3 h4
  have hr : r ≠ .notImpl := by
    intro h
    subst h
    simp [Val.is] at h4
  simp [binaryIop1, h1, binaryIop1.callInplace, h3, hr]

/-- `PyNumber_Long`: an exact int is returned, a non-int `__int__` result is the exact
`TypeError`. -/
def NumberLongChecks : Prop :=
  ∀ (rt : Rt) (o r : Val) (f : SlotFn) (i : Int) (w w1 : World),
    pyNumberLong rt (.int i) w = .ok (.int i) w ∧
    ((∀ j, o ≠ .int j) → slotIn w o .nb_int = some f →
      callUnaryNb rt .nb_int "__int__" f o w = .ok r w1 → intOf w1 r = none →
      (∀ j, r ≠ .int j) →
      pyNumberLong rt o w =
        (typeErr s!"__int__ returned non-int (type {trunc 200 (typeName w1 r)})" : M Val) w1)

theorem numberLongChecks_proven : NumberLongChecks := by
  intro rt o r f i w w1
  constructor
  · simp [pyNumberLong]
  · intro h0 h1 h2 h3 h4
    cases o with
    | int j => exact (h0 j rfl).elim
    | _ =>
      cases r with
      | int j => exact (h4 j rfl).elim
      | _ => simp [pyNumberLong, h1, h2, h3]

/-- `PyNumber_Check` is true exactly with `nb_index`, `nb_int` or `nb_float`. -/
def NumberCheckSlots : Prop :=
  ∀ (o : Val) (w : World),
    pyNumberCheck w o = ((slotIn w o .nb_index).isSome || (slotIn w o .nb_int).isSome ||
      (slotIn w o .nb_float).isSome)

theorem numberCheckSlots_proven : NumberCheckSlots := fun _ _ => rfl

/-! ## Iteration -/

/-- **`PyIter_Next` treats `StopIteration` as exhaustion** and propagates anything else. -/
def IterNextStop : Prop :=
  ∀ (rt : Rt) (it : Val) (f : SlotFn) (e : PyErr) (w w1 : World),
    slotOf w (typeOf w it) .tp_iternext = some f →
    callIterNext rt f it w = .err e w1 →
    pyIterNext rt it w =
      (if excMatches w1 e B.StopIteration then .ok none w1 else .err e w1)

theorem iterNextStop_proven : IterNextStop := by
  intro rt it f e w w1 h1 h2
  simp only [pyIterNext, M.bind_app, getW_app, h1, catchMatch, tryM_app, h2]
  split <;> simp

/-- `PyIter_Check` rejects `_PyObject_NextNotImplemented`. -/
def IterCheckNotImplemented : Prop :=
  ∀ (o : Val) (w : World),
    slotOf w (typeOf w o) .tp_iternext = some .nextNotImpl → pyIterCheck w o = false

theorem iterCheckNotImplemented_proven : IterCheckNotImplemented := by
  intro o w h
  simp [pyIterCheck, h]

/-- `PySequence_Tuple` returns an exact tuple's items without iterating. -/
def TupleOfTuple : Prop :=
  ∀ (rt : Rt) (xs : List Val) (w : World), pySequenceTuple rt (.tuple xs) w = .ok xs w

theorem tupleOfTuple_proven : TupleOfTuple := by
  intro rt xs w
  simp [pySequenceTuple]

/-- **`issubclass` machinery**: `abstract_issubclass(x, x)` is true with no attribute
access, and a class without `__bases__` is no subclass. -/
def AbstractIssubclass : Prop :=
  ∀ (rt : Rt) (d c : Val) (fuel : Nat) (w w1 : World),
    abstractIssubclass rt (fuel + 1) d d w = .ok true w ∧
    (d.is c = false → rt.getOptionalAttr d "__bases__" w = .ok none w1 →
      abstractIssubclass rt (fuel + 1) d c w = .ok false w1)

theorem abstractIssubclass_proven : AbstractIssubclass := by
  intro rt d c fuel w w1
  constructor
  · simp [abstractIssubclass, Val.is_refl]
  · intro h1 h2
    simp [abstractIssubclass, h1, abstractGetBases, h2]

/-- `isinstance(x, (A, B))`: `object_recursive_isinstance` over a tuple is "any", stopping
at the first true: the empty tuple gives `False`. -/
def IsinstanceEmptyTuple : Prop :=
  ∀ (rt : Rt) (x : Val) (fuel : Nat) (w : World),
    (asType w (.tuple [])).isNone = true →
    typeOf w (.tuple []) ≠ B.type →
    objectRecursiveIsinstance rt (fuel + 1) x (.tuple []) w = .ok false w

theorem isinstanceEmptyTuple_proven : IsinstanceEmptyTuple := by
  intro rt x fuel w h1 h2
  have h3 : asType w (.tuple []) = none := by simpa using h1
  simp [objectRecursiveIsinstance, h3, h2, tupleOf,
    objectRecursiveIsinstance.anyTuple]

/-! ## Wrappers -/

/-- `wrap_next` raises `StopIteration` when the slot returns NULL with no exception,
`Objects/typeobject.c:10388`. -/
def WrapNextStops : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (w w1 : World),
    p.wrapper = some .next → callIterNext rt f self w = .ok none w1 →
    wrapperApply rt p f self [] [] w = .err (.exc B.StopIteration "" none) w1

theorem wrapNextStops_proven : WrapNextStops := by
  intro rt p f self w w1 h1 h2
  simp [wrapperApply, h1, checkNumArgs, h2]

/-- `__get__(None, None)` is refused, `Objects/typeobject.c:10406`. -/
def WrapDescrGetNoneNone : Prop :=
  ∀ (rt : Rt) (p : SlotDef) (f : SlotFn) (self : Val) (w : World),
    p.wrapper = some .descrGet →
    wrapperApply rt p f self [.none, .none] [] w =
      (typeErr "__get__(None, None) is invalid" : M Val) w

theorem wrapDescrGetNoneNone_proven : WrapDescrGetNoneNone := by
  intro rt p f self w h
  simp [wrapperApply, h, unpackTuple, Val.is, typeErr, raiseC]

/-- `hackcheck` applies to type objects only: instances pass unchecked. -/
def HackcheckInstances : Prop :=
  ∀ (self : Val) (f : SlotFn) (what : String) (w : World),
    typeCheck w self = false → hackcheck self f what w = .ok () w

theorem hackcheckInstances_proven : HackcheckInstances := by
  intro self f what w h
  simp [hackcheck, h]

/-- `getindex`: non-negative indices pass through, `Objects/typeobject.c:10096`. -/
def GetIndexNonNegative : Prop :=
  ∀ (rt : Rt) (self arg : Val) (i : Int) (w w1 : World),
    numberAsSsize rt arg (some B.OverflowError) w = .ok i w1 → 0 ≤ i →
    getIndex rt self arg w = .ok i w1

theorem getIndexNonNegative_proven : GetIndexNonNegative := by
  intro rt self arg i w w1 h1 h2
  have : ¬ i < 0 := by omega
  simp [getIndex, h1, this]

/-- `slot_tp_call` is `__call__` on the type, with arguments passed on. -/
def SlotCallDispatch : Prop :=
  ∀ (rt : Rt) (self : Val) (args : List Val) (kw : Kw) (w : World),
    slotTpCall rt self args kw w = callMethod rt self "__call__" args kw w

theorem slotCallDispatch_proven : SlotCallDispatch := fun _ _ _ _ _ => rfl

/-- `slot_tp_repr`: with no `__repr__` on the type, the default text. -/
def SlotReprDefault : Prop :=
  ∀ (rt : Rt) (self : Val) (w : World),
    findInMro w (typeOf w self) "__repr__" = none →
    slotTpRepr rt self w = .ok (.str s!"<{typeName w self} object at 0x0>") w

theorem slotReprDefault_proven : SlotReprDefault := by
  intro rt self w h
  simp [slotTpRepr, maybeCallSpecial, lookupMethodEx, h]

/-- `__ipow__` is called with two arguments: `slot_nb_inplace_power` drops the third
operand, `Objects/typeobject.c:10971-10975`. -/
def InplacePowerTwoArgs : Prop :=
  ∀ (rt : Rt) (v u z r : Val) (w w1 : World),
    slotIn w v .nb_inplace_power = some .generic →
    vectorcallMethod rt "__ipow__" [v, u] w = .ok r w1 → r.is .notImpl = false →
    ternaryIop rt v u z w = .ok r w1

theorem inplacePowerTwoArgs_proven : InplacePowerTwoArgs := by
  intro rt v u z r w w1 h1 h2 h3
  have hr : r ≠ .notImpl := by
    intro h
    subst h
    simp [Val.is] at h3
  simp [ternaryIop, h1, h2, hr]

/-! ## `super` -/

/-- `supercheck`: a class that is a subclass of `type` gives itself; an instance gives its
type, `Objects/typeobject.c:12826-12833`. -/
def SupercheckCases : Prop :=
  ∀ (rt : Rt) (ty oa : Addr) (obj : Val) (w : World),
    (asType w obj = some oa → isSubtype w oa ty = true → supercheck rt ty obj w = .ok oa w) ∧
    (asType w obj = none → isSubtype w (typeOf w obj) ty = true →
      supercheck rt ty obj w = .ok (typeOf w obj) w)

theorem supercheckCases_proven : SupercheckCases := by
  intro rt ty oa obj w
  constructor
  · intro h1 h2; simp [supercheck, h1, h2]
  · intro h1 h2; simp [supercheck, h1, h2]

/-- An already bound `super` object ignores `__get__`; an unbound one binds,
`Objects/typeobject.c:12891`. -/
def SuperGetBound : Prop :=
  ∀ (rt : Rt) (self o v : Val) (ty ot : Option Addr) (w : World),
    payloadOf w self = some (.super ty (some o) ot) →
    superDescrGet rt self (some v) w = .ok self w

theorem superGetBound_proven : SuperGetBound := by
  intro rt self o v ty ot w h
  cases v <;> simp [superDescrGet, h]

/-! ## Layout -/

/-- `__class__` assignment to the same class passes the layout test, for every class. -/
def CompatibleReflexive : Prop :=
  ∀ (t : Addr) (attr : String) (w : World),
    compatibleForAssignment t t attr w = .ok () w

theorem compatibleReflexive_proven : CompatibleReflexive := by
  intro t attr w
  simp [compatibleForAssignment]

/-- `check_set_special_type_attr`: the special attributes of an immutable type cannot be
set, `Objects/typeobject.c@3.14.7:1421`. -/
def TypeDocSet : Prop :=
  ∀ (t : Addr) (v : Option Val) (name : String) (w : World),
    (tdata w t).immutable = true →
    checkSetSpecial t v name w =
      (typeErr s!"cannot set '{name}' attribute of immutable type '{tpName w t}'" : M Unit) w

theorem typeDocSet_proven : TypeDocSet := by
  intro t v name w h
  simp [checkSetSpecial, h, typeErr, raiseC]

/-- `is_dunder_name` needs more than four characters and the double underscores. -/
def IsDunderExamples : Prop :=
  isDunderName "__add__" = true ∧ isDunderName "____" = false ∧ isDunderName "_a_" = false

theorem isDunderExamples_proven : IsDunderExamples := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

end PyLean.TypeObj
