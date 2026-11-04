import PyLean.TypeObj.PropsSetClass

/-!
Attribute lookup on every branch (`Objects/typeobject.c`, CPython 3.15.2): `find_name_in_mro`,
`call_attribute`, `_Py_slot_tp_getattr_hook`, `_Py_type_getattro_stackref`, `do_super_lookup`,
`super_getattro`, `supercheck`.
-/

namespace PyLean.TypeObj

/-! ## `find_name_in_mro` -/

/-- **`find_name_in_mro` over the MRO, exactly.** `Objects/typeobject.c:6193-6243`: the value of
the first class of the MRO whose dict has the name, and nothing when no class has it; a type
without an MRO yet (one being readied, `:6202-6214`) finds nothing. Scope: the model's class
dicts have string keys and names are `str`, so the `DKIX_ERROR` and hash-failure paths
(`:6195-6198`, `:6227-6231`), which CPython also reports as "not found", do not arise. -/
def FindNameInMroExact : Prop :=
  ∀ (w : World) (t : Addr) (n : Name),
    ((tdata w t).mro = none → findInMro w t n = none) ∧
    (∀ mro, (tdata w t).mro = some mro →
      (∀ pre c post v, mro = pre ++ c :: post → (∀ x ∈ pre, NameDict.get? (tdata w x).dict n = none) →
        NameDict.get? (tdata w c).dict n = some v → findInMro w t n = some v) ∧
      ((∀ x ∈ mro, NameDict.get? (tdata w x).dict n = none) → findInMro w t n = none))

theorem findInMroList_none (w : World) (n : Name) :
    ∀ mro : List Addr, (∀ x ∈ mro, NameDict.get? (tdata w x).dict n = none) → findInMroList w mro n = none := by
  intro mro
  induction mro with
  | nil => intro _; rfl
  | cons x xs ih =>
    intro h
    simp only [findInMroList, h x List.mem_cons_self]
    exact ih (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem findNameInMroExact_proven : FindNameInMroExact := by
  intro w t n
  refine ⟨fun h => by simp [findInMro, h, findInMroList], fun mro h => ⟨fun pre c post v hm hpre hc => ?_,
    fun hn => by simp only [findInMro, h, Option.getD_some]; exact findInMroList_none w n mro hn⟩⟩
  simp only [findInMro, h, Option.getD_some, hm]
  exact typeLookupFirstInMro_proven w pre c post n v
    (fun x hx => by simp [NameDict.contains, hpre x hx]) hc

/-! ## `call_attribute` -/

/-- **`call_attribute`, every branch.** `Objects/typeobject.c:11065-11088`: a method descriptor
(`Py_TPFLAGS_METHOD_DESCRIPTOR`) is called with `(self, name)`; another descriptor is bound with
`tp_descr_get(attr, self, type(self))` and the result called with `(name,)`, an exception from
binding propagating; anything else is called with `(name,)`. -/
def CallAttributeExact : Prop :=
  ∀ (rt : Rt) (self attr : Val) (n : Name) (w : World),
    ((tdata w (typeOf w attr)).methodDescriptor = true →
      callAttribute rt self attr n w = rt.call attr [self, .str n] [] w) ∧
    ((tdata w (typeOf w attr)).methodDescriptor = false →
      (slotOf w (typeOf w attr) .tp_descr_get = none → callAttribute rt self attr n w = rt.call attr [.str n] [] w) ∧
      (∀ f, slotOf w (typeOf w attr) .tp_descr_get = some f →
        (∀ b w1, callDescrGet rt f attr (some self) (some (.obj (typeOf w self))) w = .ok b w1 →
          callAttribute rt self attr n w = rt.call b [.str n] [] w1) ∧
        (∀ e w1, callDescrGet rt f attr (some self) (some (.obj (typeOf w self))) w = .err e w1 →
          callAttribute rt self attr n w = .err e w1)))

theorem callAttributeExact_proven : CallAttributeExact := by
  intro rt self attr n w
  refine ⟨fun h => by simp [callAttribute, h], fun h => ⟨fun hg => by simp [callAttribute, h, hg],
    fun f hg => ⟨fun b w1 hd => by simp [callAttribute, h, hg, hd], fun e w1 hd => by simp [callAttribute, h, hg, hd]⟩⟩⟩

/-! ## `_Py_slot_tp_getattr_hook` -/

/-- **`_Py_slot_tp_getattr_hook`, every branch.** `Objects/typeobject.c:11090-11139`:
* without `__getattr__` in the MRO, `__getattribute__` is called through `vectorcall_method`
  (`_Py_slot_tp_getattro`, `:11104-11110`);
* with `__getattr__` and the default `__getattribute__` (object's wrapper, the case of every
  class that does not override it): the generic lookup runs with `suppress`; its result is
  returned, its exception propagates, and a missing attribute calls `__getattr__` through
  `call_attribute` (`:11116-11126`);
* with an overriding `__getattribute__`: it is called through `call_attribute`; an
  `AttributeError` from it calls `__getattr__`, any other result or exception is final
  (`:11127-11134`). -/
def GetattrHookExact : Prop :=
  ∀ (rt : Rt) (self : Val) (n : Name) (w : World),
    (findInMro w (typeOf w self) "__getattr__" = none →
      slotTpGetattrHook rt self n w = vectorcallMethod rt "__getattribute__" [self, .str n] w) ∧
    (∀ ga, findInMro w (typeOf w self) "__getattr__" = some ga →
      (isGenericGetattribute w (findInMro w (typeOf w self) "__getattribute__") = true →
        (∀ r w1, genericGetAttrSup rt self n true w = .ok (some r) w1 → slotTpGetattrHook rt self n w = .ok r w1) ∧
        (∀ w1, genericGetAttrSup rt self n true w = .ok none w1 →
          slotTpGetattrHook rt self n w = callAttribute rt self ga n w1) ∧
        (∀ e w1, genericGetAttrSup rt self n true w = .err e w1 → slotTpGetattrHook rt self n w = .err e w1)) ∧
      (∀ gb, findInMro w (typeOf w self) "__getattribute__" = some gb →
        isGenericGetattribute w (some gb) = false →
        (∀ r w1, callAttribute rt self gb n w = .ok r w1 → slotTpGetattrHook rt self n w = .ok r w1) ∧
        (∀ e w1, callAttribute rt self gb n w = .err e w1 →
          (excMatches w1 e B.AttributeError = true → slotTpGetattrHook rt self n w = callAttribute rt self ga n w1) ∧
          (excMatches w1 e B.AttributeError = false → slotTpGetattrHook rt self n w = .err e w1))))

theorem getattrHookExact_proven : GetattrHookExact := by
  intro rt self n w
  refine ⟨fun h => by simp [slotTpGetattrHook, h, slotTpGetattro], fun ga h => ⟨fun hg => ?_, fun gb hb hg => ?_⟩⟩
  · refine ⟨fun r w1 hr => ?_, fun w1 hr => ?_, fun e w1 hr => ?_⟩ <;>
      simp only [slotTpGetattrHook, M.bind_app, getW_app, h, hg, ite_true, hr, M.pure_app]
  · refine ⟨fun r w1 hr => ?_, fun e w1 hr => ⟨fun hm => ?_, fun hm => ?_⟩⟩
    · simp only [slotTpGetattrHook, M.bind_app, getW_app, h, hb, hg, Bool.false_eq_true, ite_false,
        catchMatch, tryM_app, hr]
    · simp only [slotTpGetattrHook, M.bind_app, getW_app, h, hb, hg, Bool.false_eq_true, ite_false,
        catchMatch, tryM_app, hr, hm, ite_true]
    · simp only [slotTpGetattrHook, M.bind_app, getW_app, h, hb, hg, Bool.false_eq_true, ite_false,
        catchMatch, tryM_app, hr, hm, raise_app]

/-! ## `do_super_lookup`, `super_getattro` -/

/-- **`do_super_lookup` without the method shortcut, every branch.** `Objects/typeobject.c:12741-12790`
with `method == NULL`: with no object type (an unbound `super`) or nothing found after
`su->type` in the MRO of the object's type, the generic attribute lookup on the `super` object
runs (`skip`, `:12773-12789`); a found value without `__get__` is returned; one with `__get__` is
bound with `obj = NULL` when the `super` is class-bound (`su_obj == su_obj_type`, `:12761-12763`)
and `obj = su_obj` otherwise, `type = su_obj_type`, and that result (or exception) is final. -/
def DoSuperLookupExact : Prop :=
  ∀ (rt : Rt) (self : Val) (suType : Addr) (suObj : Option Val) (suObjType : Option Addr) (n : Name)
    (w : World),
    (suObjType = none → doSuperLookup rt self suType suObj suObjType n w = genericGetAttr rt self n w) ∧
    (∀ ot, suObjType = some ot →
      (superLookupDescr w suType ot n = none →
        doSuperLookup rt self suType suObj suObjType n w = genericGetAttr rt self n w) ∧
      (∀ res, superLookupDescr w suType ot n = some res → slotOf w (typeOf w res) .tp_descr_get = none →
        doSuperLookup rt self suType suObj suObjType n w = .ok res w) ∧
      (∀ res f, superLookupDescr w suType ot n = some res → slotOf w (typeOf w res) .tp_descr_get = some f →
        doSuperLookup rt self suType suObj suObjType n w =
          callDescrGet rt f res (superBindObj suObj ot) (some (.obj ot)) w))

theorem doSuperLookupExact_proven : DoSuperLookupExact := by
  intro rt self suType suObj suObjType n w
  refine ⟨fun h => by simp [doSuperLookup, h], fun ot h => ⟨fun hl => by simp [doSuperLookup, h, hl],
    fun res hl hg => by simp [doSuperLookup, h, hl, hg], fun res f hl hg => ?_⟩⟩
  simp only [doSuperLookup, M.bind_app, getW_app, h, hl, hg]

/-- **`super_getattro`, every branch.** `Objects/typeobject.c:12792-12805`: the name `__class__`
goes to the generic lookup on the `super` object itself (so `super().__class__` is `super`);
any other name goes to `do_super_lookup` with the object's three fields, which for an
uninitialised `super` (NULL type) is the generic lookup too. -/
def SuperGetattroExact : Prop :=
  ∀ (rt : Rt) (self : Val) (n : Name) (w : World),
    (n = "__class__" → superGetattro rt self n w = genericGetAttr rt self n w) ∧
    (n ≠ "__class__" →
      (∀ ty o ot, payloadOf w self = some (.super (some ty) o ot) →
        superGetattro rt self n w = doSuperLookup rt self ty o ot n w) ∧
      (∀ o ot, payloadOf w self = some (.super none o ot) → superGetattro rt self n w = genericGetAttr rt self n w))

theorem superGetattroExact_proven : SuperGetattroExact := by
  intro rt self n w
  refine ⟨fun h => by subst h; simp [superGetattro], fun h => ⟨fun ty o ot hp => ?_, fun o ot hp => ?_⟩⟩
  · have : (n == "__class__") = false := by simpa using h
    simp [superGetattro, this, hp]
  · have : (n == "__class__") = false := by simpa using h
    simp [superGetattro, this, hp]

/-- **`supercheck`, every branch.** `Objects/typeobject.c:12807-12871`:
* a class `obj` that is a subclass of `type` is the answer (class-method `super`);
* an instance whose type is a subclass of `type` gives its type;
* otherwise `obj.__class__` is looked up (its exception propagates), and a class other than
  `type(obj)` that is a subclass of `type` is the answer (a proxy);
* otherwise "super(type, obj): obj (%s %.200s) is not an instance or subtype of type (%.200s).",
  with "type" and the class name for a class and "instance of" and the type name otherwise. -/
def SupercheckExact : Prop :=
  ∀ (rt : Rt) (ty : Addr) (obj : Val) (w : World),
    (∀ oa, asType w obj = some oa → isSubtype w oa ty = true → supercheck rt ty obj w = .ok oa w) ∧
    ((∀ oa, asType w obj = some oa → isSubtype w oa ty = false) →
      (isSubtype w (typeOf w obj) ty = true → supercheck rt ty obj w = .ok (typeOf w obj) w) ∧
      (isSubtype w (typeOf w obj) ty = false →
        (∀ e w1, rt.getOptionalAttr obj "__class__" w = .err e w1 → supercheck rt ty obj w = .err e w1) ∧
        (∀ c ca w1, rt.getOptionalAttr obj "__class__" w = .ok (some c) w1 → asType w1 c = some ca →
          ca ≠ typeOf w1 obj → isSubtype w1 ca ty = true → supercheck rt ty obj w = .ok ca w1) ∧
        (∀ r w1, rt.getOptionalAttr obj "__class__" w = .ok r w1 →
          (r = none ∨ ∃ c, r = some c ∧ (asType w1 c = none ∨
            ∃ ca, asType w1 c = some ca ∧ (ca = typeOf w1 obj ∨ isSubtype w1 ca ty = false))) →
          supercheck rt ty obj w =
            (typeErr s!"super(type, obj): obj ({(match asType w1 obj with
                | some oa => ("type", tpName w1 oa)
                | none => ("instance of", typeName w1 obj)).1} {trunc 200 (match asType w1 obj with
                | some oa => ("type", tpName w1 oa)
                | none => ("instance of", typeName w1 obj)).2}) is not an instance or subtype of type ({trunc 200 (tpName w1 ty)})." : M Addr) w1)))

/-- The slow part of `supercheck` (`:12838-12868`), for the proof. -/
def supercheckSlow (rt : Rt) (ty : Addr) (obj : Val) : M Addr := do
  let cattr ← rt.getOptionalAttr obj "__class__"
  let w ← getW
  match cattr with
  | some c =>
    match asType w c with
    | some ca =>
      if ca != typeOf w obj && isSubtype w ca ty then return ca
    | none => pure ()
  | none => pure ()
  let (kind, nm) := match asType w obj with
    | some oa => ("type", tpName w oa)
    | none => ("instance of", typeName w obj)
  typeErr s!"super(type, obj): obj ({kind} {trunc 200 nm}) is not an instance or subtype of type ({trunc 200 (tpName w ty)})."

theorem supercheck_slow (rt : Rt) (ty : Addr) (obj : Val) (w : World)
    (hno : ∀ oa, asType w obj = some oa → isSubtype w oa ty = false)
    (hs : isSubtype w (typeOf w obj) ty = false) :
    supercheck rt ty obj w = supercheckSlow rt ty obj w := by
  cases ha : asType w obj with
  | none => simp only [supercheck, M.bind_app, getW_app, ha, hs, Bool.false_eq_true, ite_false]; rfl
  | some oa =>
    simp only [supercheck, M.bind_app, getW_app, ha, hno oa ha, hs, Bool.false_eq_true, ite_false]; rfl

theorem supercheckExact_proven : SupercheckExact := by
  intro rt ty obj w
  refine ⟨fun oa ha hs => by simp [supercheck, ha, hs], fun hno => ⟨fun hs => ?_, fun hs => ⟨fun e w1 he => ?_,
    fun c ca w1 he hc hne hsub => ?_, fun r w1 he hr => ?_⟩⟩⟩
  · cases ha : asType w obj with
    | none => simp [supercheck, ha, hs]
    | some oa => simp [supercheck, ha, hno oa ha, hs]
  · rw [supercheck_slow rt ty obj w hno hs]; simp [supercheckSlow, he]
  · rw [supercheck_slow rt ty obj w hno hs]
    have hne' : (ca != typeOf w1 obj) = true := by simpa using hne
    simp [supercheckSlow, he, hc, hne', hsub, hne]
  · rw [supercheck_slow rt ty obj w hno hs]
    rcases hr with rfl | ⟨c, rfl, hc⟩
    · simp [supercheckSlow, he, typeErr, raiseC]
    · rcases hc with hc | ⟨ca, hc, hc2⟩
      · simp [supercheckSlow, he, hc, typeErr, raiseC]
      · rcases hc2 with hc2 | hc2
        · simp [supercheckSlow, he, hc, hc2, typeErr, raiseC]
        · simp [supercheckSlow, he, hc, hc2, typeErr, raiseC]

/-! ## `_Py_type_getattro_stackref` -/

/-- **`type.__getattribute__`, every branch.** `Objects/typeobject.c:6620-6738`, for a class `C`
with metaclass `M` and a name `n`:
* a data descriptor for `n` on `M` wins: its `__get__(C, M)` is the result (`:6660-6670`);
* otherwise `n` in the MRO of `C`: bound by its `__get__(None, C)` if it has one, returned as it
  is otherwise (`:6672-6701`), so `C.x` with `x = 1` in the class body is `1`;
* otherwise a non-data descriptor on `M` is bound by `__get__(C, M)`, and a plain attribute of `M`
  is returned (`:6704-6721`);
* otherwise nothing with `suppress`, else `AttributeError("type object '%.100s' has no attribute
  '%U'")` (`:6724-6731`).
Exceptions from a `__get__` propagate. -/
def TypeGetattroExact : Prop :=
  ∀ (rt : Rt) (c : Addr) (n : Name) (suppress : Bool) (w : World),
    let mt := typeOf w (.obj c)
    (∀ m g, findInMro w mt n = some m → slotOf w (typeOf w m) .tp_descr_get = some g → isDataDescr w m = true →
      typeGetattroImpl rt (.obj c) n suppress w = (some <$> callDescrGet rt g m (some (.obj c)) (some (.obj mt))) w) ∧
    ((∀ m g, findInMro w mt n = some m → slotOf w (typeOf w m) .tp_descr_get = some g → isDataDescr w m = false) →
      (∀ a lg, findInMro w c n = some a → slotOf w (typeOf w a) .tp_descr_get = some lg →
        typeGetattroImpl rt (.obj c) n suppress w = (some <$> callDescrGet rt lg a none (some (.obj c))) w) ∧
      (∀ a, findInMro w c n = some a → slotOf w (typeOf w a) .tp_descr_get = none →
        typeGetattroImpl rt (.obj c) n suppress w = .ok (some a) w) ∧
      (findInMro w c n = none →
        (∀ m g, findInMro w mt n = some m → slotOf w (typeOf w m) .tp_descr_get = some g →
          typeGetattroImpl rt (.obj c) n suppress w = (some <$> callDescrGet rt g m (some (.obj c)) (some (.obj mt))) w) ∧
        (∀ m, findInMro w mt n = some m → slotOf w (typeOf w m) .tp_descr_get = none →
          typeGetattroImpl rt (.obj c) n suppress w = .ok (some m) w) ∧
        (findInMro w mt n = none →
          (suppress = true → typeGetattroImpl rt (.obj c) n suppress w = .ok none w) ∧
          (suppress = false → typeGetattroImpl rt (.obj c) n suppress w =
            (attrErr s!"type object '{trunc 100 (tpName w c)}' has no attribute '{n}'" : M (Option Val)) w))))

theorem typeGetattroExact_proven : TypeGetattroExact := by
  intro rt c n suppress w mt
  refine ⟨fun m g hm hg hd => ?_, fun hnd => ⟨fun a lg ha hl => ?_, fun a ha hl => ?_, fun ha => ⟨fun m g hm hg => ?_,
    fun m hm hg => ?_, fun hm => ⟨fun hs => ?_, fun hs => ?_⟩⟩⟩⟩
  · simp [typeGetattroImpl, mt, hm, hg, hd, Functor.map, M.bind, M.pure]
  · cases hm : findInMro w mt n with
    | none => simp [typeGetattroImpl, mt, hm, ha, hl, Functor.map, M.bind, M.pure] at hm ⊢
    | some m =>
      cases hg : slotOf w (typeOf w m) .tp_descr_get with
      | none => simp [typeGetattroImpl, mt, hm, hg, ha, hl, Functor.map, M.bind, M.pure] at hm ⊢
      | some g =>
        have := hnd m g hm hg
        simp [typeGetattroImpl, mt, hm, hg, this, ha, hl, Functor.map, M.bind, M.pure] at hm ⊢
  · cases hm : findInMro w mt n with
    | none => simp [typeGetattroImpl, mt, hm, ha, hl] at hm ⊢
    | some m =>
      cases hg : slotOf w (typeOf w m) .tp_descr_get with
      | none => simp [typeGetattroImpl, mt, hm, hg, ha, hl] at hm ⊢
      | some g =>
        have := hnd m g hm hg
        simp [typeGetattroImpl, mt, hm, hg, this, ha, hl] at hm ⊢
  · have := hnd m g hm hg
    simp [typeGetattroImpl, mt, hm, hg, this, ha, Functor.map, M.bind, M.pure] at hm ⊢
  · simp [typeGetattroImpl, mt, hm, hg, ha] at hm ⊢
  · simp [typeGetattroImpl, mt, hm, ha, hs] at hm ⊢
  · simp [typeGetattroImpl, mt, hm, ha, hs, attrErr, raiseC] at hm ⊢

end PyLean.TypeObj
