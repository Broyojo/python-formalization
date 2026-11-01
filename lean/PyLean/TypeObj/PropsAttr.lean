import PyLean.TypeObj.Call

/-!
Properties of attribute lookup, quantified over every world and over every behaviour of
user code (`rt : Rt`). The hypotheses of each statement describe the class structure a
case is about: which class in the MRO provides the name and what kind of descriptor it is.
-/

namespace PyLean.TypeObj

@[simp] theorem map_app {α β : Type} (f : α → β) (x : M α) (w : World) :
    (f <$> x) w = match x w with
      | .ok a w' => .ok (f a) w'
      | .err e w' => .err e w' := rfl

mutual
  theorem Val.is_refl : ∀ v : Val, v.is v = true
    | .none | .notImpl | .ellipsis => by simp [Val.is]
    | .bool b => by simp [Val.is]
    | .int i => by simp [Val.is]
    | .float b => by simp [Val.is]
    | .str s => by simp [Val.is]
    | .tuple xs => by simpa [Val.is] using Val.isList_refl xs
    | .obj a => by simp [Val.is]
  theorem Val.isList_refl : ∀ xs : List Val, Val.isList xs xs = true
    | [] => by simp [Val.isList]
    | x :: xs => by simp [Val.isList, Val.is_refl x, Val.isList_refl xs]
end

/-- `_PyType_Lookup` returns the value from the first class in the MRO that has the
name: a class earlier in the MRO overrides every later one. -/
def TypeLookupFirstInMro : Prop :=
  ∀ (w : World) (pre : List Addr) (c : Addr) (post : List Addr) (n : Name) (v : Val),
    (∀ t ∈ pre, NameDict.contains (tdata w t).dict n = false) →
    NameDict.get? (tdata w c).dict n = some v →
    findInMroList w (pre ++ c :: post) n = some v

theorem get?_of_contains_false (d : NameDict) (n : Name) (h : NameDict.contains d n = false) :
    NameDict.get? d n = none := by
  simp only [NameDict.contains, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  exact h

theorem typeLookupFirstInMro_proven : TypeLookupFirstInMro := by
  intro w pre c post n v hpre hc
  induction pre with
  | nil => simp [findInMroList, hc]
  | cons t ts ih =>
    have h1 : NameDict.get? (tdata w t).dict n = none :=
      get?_of_contains_false _ _ (hpre t (List.mem_cons_self))
    simp only [List.cons_append, findInMroList, h1]
    exact ih (fun x hx => hpre x (List.mem_cons_of_mem _ hx))

/-- **Data descriptors win.** If the type's MRO provides a data descriptor for `n`, then
`object.__getattribute__` calls its `__get__` and never reads the instance dict. Holds for
every instance dict and every `__get__`. -/
def GenericGetattrDataDescriptorFirst : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (d : Val) (f : SlotFn) (w : World),
    findInMro w (typeOf w obj) n = some d →
    slotOf w (typeOf w d) .tp_descr_get = some f →
    isDataDescr w d = true →
    genericGetAttrSup rt obj n false w =
      (some <$> callDescrGet rt f d (some obj) (some (.obj (typeOf w obj)))) w

theorem genericGetattrDataDescriptorFirst_proven : GenericGetattrDataDescriptorFirst := by
  intro rt obj n d f w hl hf hdata
  simp [genericGetAttrSup, hl, hf, hdata, runDescrGet]

/-- **The instance dict beats non-data descriptors and class attributes.** Without a data
descriptor, a name in the instance `__dict__` is returned as is. -/
def GenericGetattrInstanceDictNext : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (v : Val) (w : World),
    (∀ d, findInMro w (typeOf w obj) n = some d →
      slotOf w (typeOf w d) .tp_descr_get = none ∨ isDataDescr w d = false) →
    instDictGet w obj n = some v →
    genericGetAttrSup rt obj n false w = .ok (some v) w

theorem genericGetattrInstanceDictNext_proven : GenericGetattrInstanceDictNext := by
  intro rt obj n v w hd hv
  cases hl : findInMro w (typeOf w obj) n with
  | none => simp [genericGetAttrSup, hl, genericGetAttrTail, hv]
  | some d =>
    rcases hd d hl with h | h
    · simp [genericGetAttrSup, hl, h, genericGetAttrTail, hv]
    · cases hf : slotOf w (typeOf w d) .tp_descr_get with
      | none => simp [genericGetAttrSup, hl, hf, genericGetAttrTail, hv]
      | some f => simp [genericGetAttrSup, hl, hf, h, genericGetAttrTail, hv]

/-- **Non-data descriptors come third.** With no data descriptor and nothing in the
instance dict, a descriptor from the type is bound with `__get__`. -/
def GenericGetattrNonDataDescriptor : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (d : Val) (f : SlotFn) (w : World),
    findInMro w (typeOf w obj) n = some d →
    slotOf w (typeOf w d) .tp_descr_get = some f →
    isDataDescr w d = false →
    instDictGet w obj n = none →
    genericGetAttrSup rt obj n false w =
      (some <$> callDescrGet rt f d (some obj) (some (.obj (typeOf w obj)))) w

theorem genericGetattrNonDataDescriptor_proven : GenericGetattrNonDataDescriptor := by
  intro rt obj n d f w hl hf hdata hi
  simp [genericGetAttrSup, hl, hf, hdata, genericGetAttrTail, hi, runDescrGet]

/-- **Class attributes come last.** A plain class attribute (no `__get__`) is returned
unchanged when the instance dict has no such name. -/
def GenericGetattrPlainClassAttr : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (d : Val) (w : World),
    findInMro w (typeOf w obj) n = some d →
    slotOf w (typeOf w d) .tp_descr_get = none →
    instDictGet w obj n = none →
    genericGetAttrSup rt obj n false w = .ok (some d) w

theorem genericGetattrPlainClassAttr_proven : GenericGetattrPlainClassAttr := by
  intro rt obj n d w hl hf hi
  simp [genericGetAttrSup, hl, hf, genericGetAttrTail, hi]

/-- With `suppress` (the path of `hasattr`, `PyObject_GetOptionalAttr`, `__getattr__`
hooks), a missing name gives `none` and raises nothing. -/
def GenericGetattrMissingSuppressed : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (w : World),
    findInMro w (typeOf w obj) n = none →
    instDictGet w obj n = none →
    genericGetAttrSup rt obj n true w = .ok none w

theorem genericGetattrMissingSuppressed_proven : GenericGetattrMissingSuppressed := by
  intro rt obj n w hl hi
  simp [genericGetAttrSup, hl, genericGetAttrTail, hi]

/-- A missing attribute raises `AttributeError` with the exact message of
`Objects/object.c:1919`, for every object. -/
def GenericGetattrMissingRaises : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (w : World),
    findInMro w (typeOf w obj) n = none →
    instDictGet w obj n = none →
    ∃ v w', genericGetAttrSup rt obj n false w =
      .err (.exc B.AttributeError
        s!"'{trunc 100 (tpName w (typeOf w obj))}' object has no attribute '{n}'" (some v)) w'

theorem isSubtype_self_of_mem (w : World) (a : Addr) (m : List Addr)
    (h : (tdata w a).mro = some m) (hm : a ∈ m) : isSubtype w a a = true := by
  simp [isSubtype, h, hm]

/-- Metaclass data descriptors win over the class's own attributes in
`type.__getattribute__`: the analogue for classes. -/
def TypeGetattroMetaDataDescriptorFirst : Prop :=
  ∀ (rt : Rt) (ty : Val) (n : Name) (m : Val) (g : SlotFn) (w : World),
    findInMro w (typeOf w ty) n = some m →
    slotOf w (typeOf w m) .tp_descr_get = some g →
    isDataDescr w m = true →
    typeGetattroImpl rt ty n false w =
      (some <$> callDescrGet rt g m (some ty) (some (.obj (typeOf w ty)))) w

theorem typeGetattroMetaDataDescriptorFirst_proven : TypeGetattroMetaDataDescriptorFirst := by
  intro rt ty n m g w hl hg hd
  simp only [typeGetattroImpl, M.bind_app, getW_app, hl, hg, hd, ite_true]
  cases h : callDescrGet rt g m (some ty) (some (.obj (typeOf w ty))) w <;> simp [h]

/-- The class's own lookup beats non-data attributes of the metaclass, and is bound with
`obj = NULL`, `Objects/typeobject.c:6156`. -/
def TypeGetattroClassAttrNext : Prop :=
  ∀ (rt : Rt) (ty : Val) (t : Addr) (n : Name) (a : Val) (lg : SlotFn) (w : World),
    ty = .obj t →
    (∀ m, findInMro w (typeOf w ty) n = some m →
      slotOf w (typeOf w m) .tp_descr_get = none ∨ isDataDescr w m = false) →
    findInMro w t n = some a →
    slotOf w (typeOf w a) .tp_descr_get = some lg →
    typeGetattroImpl rt ty n false w = (some <$> callDescrGet rt lg a none (some ty)) w

theorem typeGetattroClassAttrNext_proven : TypeGetattroClassAttrNext := by
  intro rt ty t n a lg w hty hm ha hlg
  subst hty
  have key : ∀ (mm : Option Val) (gg : Option SlotFn), (mm.isSome = true →
      gg = none ∨ ∃ m, mm = some m ∧ isDataDescr w m = false) → True := fun _ _ _ => trivial
  cases hl : findInMro w (typeOf w (.obj t)) n with
  | none =>
    simp only [typeGetattroImpl, M.bind_app, getW_app, hl, ha, hlg]
    cases h : callDescrGet rt lg a none (some (.obj t)) w <;> simp [h]
  | some m =>
    cases hg : slotOf w (typeOf w m) .tp_descr_get with
    | none =>
      simp only [typeGetattroImpl, M.bind_app, getW_app, hl, hg, ha, hlg]
      cases h : callDescrGet rt lg a none (some (.obj t)) w <;> simp [h]
    | some g =>
      rcases hm m hl with h1 | h1
      · rw [h1] at hg; simp at hg
      · simp only [typeGetattroImpl, M.bind_app, getW_app, hl, hg, h1, ha, hlg]
        cases h : callDescrGet rt lg a none (some (.obj t)) w <;> simp [h]

/-- `PyObject_GenericSetAttr` calls the descriptor's `__set__`/`__delete__` when the type
has one, for every instance dict state: writes never reach the dict. -/
def GenericSetattrDescriptorFirst : Prop :=
  ∀ (rt : Rt) (obj : Val) (n : Name) (value : Option Val) (d : Val) (f : SlotFn) (w : World),
    findInMro w (typeOf w obj) n = some d →
    slotOf w (typeOf w d) .tp_descr_set = some f →
    genericSetAttr rt obj n value w = callDescrSet rt f d obj value w

theorem genericSetattrDescriptorFirst_proven : GenericSetattrDescriptorFirst := by
  intro rt obj n value d f w hl hf
  simp [genericSetAttr, hl, hf]

end PyLean.TypeObj
