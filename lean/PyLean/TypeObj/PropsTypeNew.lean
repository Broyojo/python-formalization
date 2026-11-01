import PyLean.TypeObj.PropsSlots

/-!
Properties of class creation and of slot maintenance, for all class bodies.
-/

namespace PyLean.TypeObj

/-- **`best_base` picks a real base whose solid base is the most derived.** Under the
subtype order, the result is one of the bases and its solid base is a subclass of the solid
base of every other base. -/
def BestBaseMostDerived : Prop :=
  ∀ (w : World) (bases : List Val) (r : Addr), SubtypeOrder w →
    bestBaseLoop w bases none none = .ok r →
    Val.obj r ∈ bases ∧
      ∀ b a, b ∈ bases → asType w b = some a → isSubtype w (solidBase w r) (solidBase w a) = true

theorem asType_obj (w : World) (v : Val) (a : Addr) (h : asType w v = some a) : v = .obj a := by
  cases v <;> simp [asType] at h
  rename_i x
  obtain ⟨_, rfl⟩ := h
  rfl

theorem bestBaseLoop_inv (w : World) (ho : SubtypeOrder w) (bases : List Val) :
    ∀ (win base : Addr) (r : Addr), solidBase w base = win →
      bestBaseLoop w bases (some win) (some base) = .ok r →
      (r = base ∨ Val.obj r ∈ bases) ∧ isSubtype w (solidBase w r) win = true ∧
      ∀ b a, b ∈ bases → asType w b = some a →
        isSubtype w (solidBase w r) (solidBase w a) = true := by
  induction bases with
  | nil =>
    intro win base r hw h
    simp only [bestBaseLoop, Except.ok.injEq] at h
    subst h
    exact ⟨Or.inl rfl, by rw [hw]; exact ho.1 _, by simp⟩
  | cons bp rest ih =>
    intro win base r hw h
    simp only [bestBaseLoop] at h
    cases ha : asType w bp with
    | none => rw [ha] at h; simp at h
    | some bi =>
      rw [ha] at h
      simp only at h
      by_cases hb : (tdata w bi).baseType = true
      · simp only [hb, Bool.not_true, Bool.false_eq_true, ite_false] at h
        by_cases h1 : isSubtype w win (solidBase w bi) = true
        · simp only [h1, ite_true] at h
          obtain ⟨hr, h2, h3⟩ := ih win base r hw h
          refine ⟨hr.imp id (List.mem_cons_of_mem _), h2, ?_⟩
          intro b a hbm hab
          rcases List.mem_cons.mp hbm with rfl | hbm
          · rw [ha] at hab
            simp only [Option.some.injEq] at hab
            subst hab
            exact ho.2 _ _ _ h2 h1
          · exact h3 b a hbm hab
        · have h1' : isSubtype w win (solidBase w bi) = false := by simpa using h1
          simp only [h1', Bool.false_eq_true, ite_false] at h
          by_cases h2 : isSubtype w (solidBase w bi) win = true
          · simp only [h2, ite_true] at h
            obtain ⟨hr, h3, h4⟩ := ih (solidBase w bi) bi r rfl h
            refine ⟨?_, ho.2 _ _ _ h3 h2, ?_⟩
            · rcases hr with rfl | hr
              · rw [asType_obj w bp _ ha]
                exact Or.inr (List.mem_cons_self)
              · exact Or.inr (List.mem_cons_of_mem _ hr)
            · intro b a hbm hab
              rcases List.mem_cons.mp hbm with rfl | hbm
              · rw [ha] at hab
                simp only [Option.some.injEq] at hab
                subst hab
                exact h3
              · exact h4 b a hbm hab
          · simp [h2] at h
      · have hb' : (tdata w bi).baseType = false := by simpa using hb
        simp [hb'] at h

theorem bestBaseMostDerived_proven : BestBaseMostDerived := by
  intro w bases r ho h
  cases bases with
  | nil => simp [bestBaseLoop] at h
  | cons bp rest =>
    simp only [bestBaseLoop] at h
    cases ha : asType w bp with
    | none => rw [ha] at h; simp at h
    | some bi =>
      rw [ha] at h
      simp only at h
      by_cases hb : (tdata w bi).baseType = true
      · simp only [hb, Bool.not_true, Bool.false_eq_true, ite_false] at h
        obtain ⟨hr, h2, h3⟩ := bestBaseLoop_inv w ho rest _ bi r rfl h
        refine ⟨?_, ?_⟩
        · rcases hr with rfl | hr
          · rw [asType_obj w bp _ ha]
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ hr
        · intro b a hbm hab
          rcases List.mem_cons.mp hbm with rfl | hbm
          · rw [ha] at hab
            simp only [Option.some.injEq] at hab
            subst hab
            exact h2
          · exact h3 b a hbm hab
      · have hb' : (tdata w bi).baseType = false := by simpa using hb
        simp [hb'] at h

/-- A base without `Py_TPFLAGS_BASETYPE` is refused: `class X(bool)` raises the exact
`TypeError`, whichever position it has among the bases seen so far. -/
def BestBaseRefusesFinal : Prop :=
  ∀ (w : World) (bp : Val) (bi : Addr) (rest : List Val) (win base : Option Addr),
    asType w bp = some bi → (tdata w bi).baseType = false →
    bestBaseLoop w (bp :: rest) win base =
      .error s!"type '{trunc 100 (tpName w bi)}' is not an acceptable base type"

theorem bestBaseRefusesFinal_proven : BestBaseRefusesFinal := by
  intro w bp bi rest win base h1 h2
  simp [bestBaseLoop, h1, h2]

/-- **No `__slots__`, then a dict and a weakref slot**: without `__slots__` a class gets a
`__dict__` and `__weakref__` unless its base has them, `Objects/typeobject.c:4164-4171`. -/
def NoSlotsAddsDictWeak : Prop :=
  ∀ (ctx : TypeNewCtx) (dict : NameDict) (r : TypeNewCtx × Option (List Name)) (w w1 : World),
    ctx.slots = none → typeNewSlots ctx dict w = .ok r w1 →
    r.1.addDict = ((tdata w ctx.base).dictoffset == 0) ∧
    r.1.addWeak = ((tdata w ctx.base).weaklistoffset == 0 && (tdata w ctx.base).itemsize == 0)

theorem noSlotsAddsDictWeak_proven : NoSlotsAddsDictWeak := by
  intro ctx dict r w w1 hs h
  simp only [typeNewSlots, M.bind_app, getW_app, hs, M.pure_app, R.ok.injEq] at h
  obtain ⟨rfl, _⟩ := h
  simp

/-- A string `__slots__` is one name, not an iterable of characters,
`Objects/typeobject.c:4593`. -/
def SlotsStringIsOneName : Prop :=
  ∀ (rt : Rt) (ctx : TypeNewCtx) (dict : NameDict) (slots : Val) (st : String) (w : World),
    NameDict.get? dict "__slots__" = some slots → strOf w slots = some st →
    typeNewGetSlots rt ctx dict w = .ok { ctx with slots := some [slots], nslot := 1 } w

theorem slotsStringIsOneName_proven : SlotsStringIsOneName := by
  intro rt ctx dict slots st w h1 h2
  simp [typeNewGetSlots, h1, h2]

/-- `__slots__` names `__dict__` at most once when the base has no dict, and never when it
has one. -/
def SlotDictTwiceRejected : Prop :=
  ∀ (ctx : TypeNewCtx) (rest : List Val) (w : World),
    ctx.addDict = true →
    typeNewVisitSlots ctx (.str "__dict__" :: rest) w =
      (typeErr "__dict__ slot disallowed: we already got one" : M TypeNewCtx) w

theorem slotDictTwiceRejected_proven : SlotDictTwiceRejected := by
  intro ctx rest w h
  simp [typeNewVisitSlots, validIdentifier, strOf, isIdentifier, h, typeErr, raiseC]

/-- **Plain functions named `__new__` become staticmethods, and
`__init_subclass__`/`__class_getitem__` become classmethods**,
`Objects/typeobject.c:4547-4560`. Anything else, or an absent name, leaves the dict as it
was. -/
def WrapInDictOnlyFunctions : Prop :=
  ∀ (dict : NameDict) (attr : Name) (cls : Addr) (mk : Val → Payload) (v : Val) (w : World),
    (NameDict.get? dict attr = none → wrapInDict dict attr cls mk w = .ok dict w) ∧
    (NameDict.get? dict attr = some v → (∀ f, payloadOf w v ≠ some (.func f)) →
      wrapInDict dict attr cls mk w = .ok dict w)

theorem wrapInDictOnlyFunctions_proven : WrapInDictOnlyFunctions := by
  intro dict attr cls mk v w
  constructor
  · intro h; simp [wrapInDict, h]
  · intro h1 h2
    simp only [wrapInDict, M.bind_app, getW_app, h1]
    cases hp : payloadOf w v with
    | none => rfl
    | some p =>
      cases p with
      | func f => exact (h2 f hp).elim
      | _ => rfl

/-- `tp_new` is inherited from `tp_base` for a heap type, `Objects/typeobject.c:8857-8862`. -/
def TypeReadyNewInherited : Prop :=
  ∀ (t b : Addr) (w w1 : World),
    (tdata w t).base = some b → (slotOf w t .tp_new).isSome = true →
    typeReadySetNew t w = .ok () w

theorem typeReadyNewInherited_proven : TypeReadyNewInherited := by
  intro t b w w1 h1 h2
  have h : slotOf w t .tp_new ≠ none := by
    cases hs : slotOf w t .tp_new <;> simp_all
  simp [typeReadySetNew, h1, h]

/-- **`update_one_slot`: no method, no slot.** When no class in the MRO defines a special
method of the slot, the slot becomes NULL, whatever it held. `tp_iternext` is the exception
(`_PyObject_NextNotImplemented`). -/
def UpdateSlotCleared : Prop :=
  ∀ (w : World) (t : Addr) (s : Slot),
    s ≠ .tp_iternext →
    (∀ p ∈ slotdefs, p.slot = s → findInMro w t p.name = none) →
    updateOneSlotValue w t s = none

theorem updateOneSlotStep_none (w : World) (t : Addr) (s : Slot) (p : SlotDef) (st : UpdState)
    (hs : s ≠ .tp_iternext) (h : findInMro w t p.name = none) :
    updateOneSlotStep w t s st p = st := by
  simp [updateOneSlotStep, h, hs]

theorem updateSlotCleared_proven : UpdateSlotCleared := by
  intro w t s hs h
  have key : ∀ (l : List SlotDef) (st : UpdState), (∀ p ∈ l, findInMro w t p.name = none) →
      l.foldl (updateOneSlotStep w t s) st = st := by
    intro l
    induction l with
    | nil => intro st _; rfl
    | cons p ps ih =>
      intro st hp
      simp only [List.foldl_cons]
      rw [updateOneSlotStep_none w t s p st hs (hp p (by simp))]
      exact ih st (fun q hq => hp q (by simp [hq]))
  have hall : ∀ p ∈ slotdefs.filter (·.slot == s), findInMro w t p.name = none := by
    intro p hp
    have := List.mem_filter.mp hp
    exact h p this.1 (by simpa using this.2)
  simp only [updateOneSlotValue, key _ _ hall]
  rfl

/-- `__hash__ = None` in a class, however deep, makes the slot
`PyObject_HashNotImplemented`, `Objects/typeobject.c:11392`. -/
def UpdateHashNone : Prop :=
  ∀ (w : World) (t : Addr),
    findInMro w t "__hash__" = some .none →
    updateOneSlotValue w t .tp_hash = some .hashNotImpl

theorem hashSlotdefs :
    slotdefs.filter (·.slot == Slot.tp_hash) =
      [{ name := "__hash__", slot := .tp_hash, generic := some .generic, wrapper := some .hash }] := by
  rfl

theorem updateHashNone_proven : UpdateHashNone := by
  intro w t h
  simp [updateOneSlotValue, hashSlotdefs, updateOneSlotStep, h, payloadOf]

/-- `is_subtype_with_mro` is membership in the MRO for a finished class,
`Objects/typeobject.c:2807`. -/
def SubtypeIsMroMember : Prop :=
  ∀ (w : World) (a b : Addr) (m : List Addr),
    (tdata w a).mro = some m → isSubtype w a b = m.contains b

theorem subtypeIsMroMember_proven : SubtypeIsMroMember := by
  intro w a b m h
  simp [isSubtype, h]

/-- Assigning `__class__` needs a class: the first two checks of `object_set_class`,
`Objects/typeobject.c:7228-7238`. -/
def SetClassChecks : Prop :=
  ∀ (self v : Val) (w : World),
    objectSetClass self none w = (typeErr "can't delete __class__ attribute" : M Unit) w ∧
    (asType w v = none →
      objectSetClass self (some v) w =
        (typeErr s!"__class__ must be set to a class, not '{typeName w v}' object" : M Unit) w)

theorem setClassChecks_proven : SetClassChecks := by
  intro self v w
  constructor
  · simp [objectSetClass]
  · intro h
    simp [objectSetClass, h]

/-- `__class__` assignment to or from an immutable type is refused: `(1).__class__ = C` and
`C().__class__ = int`, `Objects/typeobject.c:7178-7186`. -/
def SetClassImmutable : Prop :=
  ∀ (self v : Val) (t : Addr) (w : World),
    asType w v = some t →
    ((tdata w t).immutable || (tdata w (typeOf w self)).immutable) = true →
    objectSetClass self (some v) w =
      (typeErr "__class__ assignment only supported for mutable types or ModuleType subclasses" : M Unit) w

theorem setClassImmutable_proven : SetClassImmutable := by
  intro self v t w h1 h2
  have h3 : (tdata w t).immutable = true ∨ (tdata w (typeOf w self)).immutable = true := by
    simpa using h2
  simp [objectSetClass, h1, h3, typeErr, raiseC]

/-- `object.__format__` refuses a non-empty spec and is `str()` otherwise,
`Objects/typeobject.c:7880-7886`. -/
def ObjectFormatSpec : Prop :=
  ∀ (rt : Rt) (self : Val) (spec : String) (w : World),
    (spec.length > 0 → objectFormat rt self spec w =
      (typeErr s!"unsupported format string passed to {trunc 200 (typeName w self)}.__format__" : M Val) w) ∧
    (spec = "" → ∀ s w1, rt.str self w = .ok s w1 → objectFormat rt self spec w = .ok (.str s) w1)

theorem objectFormatSpec_proven : ObjectFormatSpec := by
  intro rt self spec w
  constructor
  · intro h; simp [objectFormat, h, typeErr, raiseC]
  · intro h s w1 hs
    subst h
    simp [objectFormat, hs]

/-- `type.__init__` accepts one or three arguments, `Objects/typeobject.c:3895`. -/
def TypeInitArity : Prop :=
  ∀ (args : List Val) (w : World), args.length ≠ 1 → args.length ≠ 3 →
    typeInit args [] w = (typeErr "type.__init__() takes 1 or 3 arguments" : M Unit) w

theorem typeInitArity_proven : TypeInitArity := by
  intro args w h1 h2
  simp [typeInit, h1, h2, typeErr, raiseC]

/-- `type()` with two arguments is refused before anything is created. -/
def TypeCallTwoArgs : Prop :=
  ∀ (rt : Rt) (a b : Val) (kw : Kw) (w : World),
    typeCall rt B.type [a, b] kw w = (typeErr "type() takes 1 or 3 arguments" : M Val) w

theorem typeCallTwoArgs_proven : TypeCallTwoArgs := by
  intro rt a b kw w
  simp [typeCall, typeErr, raiseC]

/-- `tp_new_wrapper` refuses a first argument that is not a type or not a subtype,
`Objects/typeobject.c:9840-9857`. -/
def NewWrapperChecks : Prop :=
  ∀ (rt : Rt) (ty : Addr) (x : Val) (rest : List Val) (kw : Kw) (w : World),
    (asType w x = none → tpNewWrapper rt ty (x :: rest) kw w =
      (typeErr s!"{tpName w ty}.__new__(X): X is not a type object ({typeName w x})" : M Val) w) ∧
    (tpNewWrapper rt ty [] kw w =
      (typeErr s!"{tpName w ty}.__new__(): not enough arguments" : M Val) w)

theorem newWrapperChecks_proven : NewWrapperChecks := by
  intro rt ty x rest kw w
  constructor
  · intro h; simp [tpNewWrapper, h]
  · simp [tpNewWrapper]

/-- `descr_check`: a descriptor from `C` refuses an object that is not a `C`,
`Objects/descrobject.c:80`. -/
def DescrCheckRefuses : Prop :=
  ∀ (owner : Addr) (n : Name) (o : Val) (w : World),
    isSubtype w (typeOf w o) owner = false →
    descrCheck owner n o w =
      (typeErr s!"descriptor '{n}' for '{trunc 100 (tpName w owner)}' objects doesn't apply to a '{trunc 100 (typeName w o)}' object" : M Unit) w

theorem descrCheckRefuses_proven : DescrCheckRefuses := by
  intro owner n o w h
  simp [descrCheck, h, typeErr, raiseC]

/-- `method_get`, `member_get`, `getset_get`, `wrapperdescr_get`: from the class (no
instance) a descriptor returns itself. -/
def DescriptorFromClass : Prop :=
  ∀ (rt : Rt) (d : Val) (o : Addr) (n : Name) (b : Builtin) (p : Name) (w : World),
    methodGet d o n b none w = .ok d w ∧ wrapperdescrGet d o n none w = .ok d w ∧
    memberGet rt d o p none w = .ok d w ∧ getsetDescrGet rt d o p none w = .ok d w

theorem descriptorFromClass_proven : DescriptorFromClass := by
  intro rt d o n b p w
  simp [methodGet, wrapperdescrGet, memberGet, getsetDescrGet]

/-- An unset `__slots__` member raises `AttributeError`; deleting it twice as well,
`Python/structmember.c:16`, `:324`. -/
def SlotMemberUnset : Prop :=
  ∀ (rt : Rt) (d o : Val) (owner : Addr) (name : Name) (w : World),
    isSubtype w (typeOf w o) owner = true → (tdata w owner).heap = true →
    slotValue w o name = none →
    memberGet rt d owner name (some o) w =
      (attrErr s!"'{typeFQN w (typeOf w o)}' object has no attribute '{name}'" : M Val) w

theorem slotMemberUnset_proven : SlotMemberUnset := by
  intro rt d o owner name w h1 h2 h3
  simp [memberGet, descrCheck, h1, h2, h3]

end PyLean.TypeObj
