import PyLean.TypeObj.PropsObjExact2

/-!
Class creation helpers and `__class__` assignment, on every branch (`Objects/typeobject.c`,
CPython 3.15.2): `type_new_staticmethod`, `type_new_classmethod`, `type_new_set_classcell`,
`type_new_set_classdictcell`, `type_new`, `object_set_class`, `object_set_class_world_stopped`,
`compatible_for_assignment`, `same_slots_added`.
-/

namespace PyLean.TypeObj

/-! ## `type_new_staticmethod`, `type_new_classmethod` -/

/-- **`type_new_staticmethod` and `type_new_classmethod`.** `Objects/typeobject.c:4628-4679`, with
`PyStaticMethod_New`/`PyClassMethod_New` (`Objects/funcobject.c:1993`, `:1727`, which copy the
function's attributes with `functools_wraps`): a missing key or a value that is not a function
leaves the dict as it is; a plain function is replaced by a new `staticmethod` (or
`classmethod`) object wrapping it, the new object gets the function's `__module__`,
`__name__`, `__qualname__` and `__doc__` (an exception doing so propagates), and nothing else in
the dict changes. -/
def WrapInDictExact : Prop :=
  ∀ (rt : Rt) (dict : NameDict) (attr : Name) (w : World),
    ∀ (cls : Addr) (mk : Val → Payload), (cls = B.staticmethod ∧ mk = .staticmethod) ∨
        (cls = B.classmethod ∧ mk = .classmethod) →
    (NameDict.get? dict attr = none → wrapInDict rt dict attr cls mk w = .ok dict w) ∧
    (∀ f, NameDict.get? dict attr = some f → (∀ fd, payloadOf w f ≠ some (.func fd)) →
      wrapInDict rt dict attr cls mk w = .ok dict w) ∧
    (∀ f fd, NameDict.get? dict attr = some f → payloadOf w f = some (.func fd) →
      let s : Val := .obj w.heap.size
      let w1 : World := { w with heap := w.heap.push (.val { cls := cls, body := mk f }) }
      (∀ w2, functoolsWraps rt s f w1 = .ok () w2 →
        wrapInDict rt dict attr cls mk w = .ok (NameDict.set dict attr s) w2) ∧
      (∀ e w2, functoolsWraps rt s f w1 = .err e w2 → wrapInDict rt dict attr cls mk w = .err e w2))

theorem wrapInDictExact_proven : WrapInDictExact := by
  intro rt dict attr w cls mk _
  refine ⟨fun h => by simp [wrapInDict, h], fun f h hf => ?_, fun f fd h hf => ⟨fun w2 hw => ?_, fun e w2 hw => ?_⟩⟩
  · cases hp : payloadOf w f with
    | none => simp [wrapInDict, h, hp]
    | some p =>
      cases p <;> simp_all [wrapInDict]
  · simp [wrapInDict, h, hf, alloc, allocCell, hw]
  · simp [wrapInDict, h, hf, alloc, allocCell, hw]

/-! ## `type_new_set_classcell`, `type_new_set_classdictcell` -/

/-- **`type_new_set_classcell` / `type_new_set_classdictcell`.** `Objects/typeobject.c:4808-4858`:
no `__classcell__` (`__classdictcell__`) key leaves the namespace as it is; a cell gets the value
stored (`PyCell_Set`) and the key is deleted from the namespace; anything else raises
"%s must be a nonlocal cell, not %.200R" with the repr of its type. `value` is the class for
`__classcell__`. For `__classdictcell__` CPython stores the class's dict object
(`:4907`, `type(C.f())` is `dict` on 3.15.2); the model's caller passes the class, since its
`tp_dict` is not an object. -/
def TypeNewSetCellExact : Prop :=
  ∀ (key : Name) (value : Val) (dict : NameDict) (w : World),
    (NameDict.get? dict key = none → typeNewSetCell key value dict w = .ok dict w) ∧
    (∀ c o x, NameDict.get? dict key = some (.obj c) → w.get c = .val o → o.body = .cell x →
      typeNewSetCell key value dict w =
        .ok (NameDict.erase dict key) (w.setCell c (.val { o with body := .cell (some value) }))) ∧
    (∀ v, NameDict.get? dict key = some v → (∀ x, payloadOf w v ≠ some (.cell x)) →
      typeNewSetCell key value dict w =
        (typeErr s!"{key} must be a nonlocal cell, not {truncChars 200 (typeRepr w (typeOf w v))}" : M NameDict) w)

theorem typeNewSetCellExact_proven : TypeNewSetCellExact := by
  intro key value dict w
  refine ⟨fun h => by simp [typeNewSetCell, h], fun c o x h hc hb => ?_, fun v h hv => ?_⟩
  · simp [typeNewSetCell, h, payloadOf, hc, hb, modObj]
  · cases v with
    | obj c =>
      cases hp : payloadOf w (.obj c) with
      | none => simp [typeNewSetCell, h, hp]
      | some p =>
        cases p <;> simp_all [typeNewSetCell]
    | _ => simp [typeNewSetCell, h, payloadOf]

/-! ## `type_new` -/

/-- **`type_new`, every branch.** `Objects/typeobject.c:5115-5167`: after the argument checks
(`TypeNewArgs`), `type_new_get_bases` decides; its exception propagates; when it created the class
through a more derived metaclass's `tp_new` (`res == 1`, `:5159-5162`) that object is returned
as it is, and otherwise `type_new_impl` builds the class from the namespace. Precondition: the
namespace keys are exact strings (the model's namespaces; CPython warns for others). -/
def TypeNewExact : Prop :=
  ∀ (rt : Rt) (metatype : Addr) (nameV basesV dictV : Val) (kwds : Kw) (w : World)
    (name : String) (bases : List Val) (es : List (Val × Val)),
    strOf w nameV = some name → tupleOf w basesV = some bases → anyDictOf w dictV = some es →
    (∀ p ∈ es, ∃ k, p.1 = .str k) →
    let ctx : TypeNewCtx := { metatype, args := [nameV, basesV, dictV], kwds, name, bases }
    let orig : NameDict := es.filterMap strKeyEntry
    (∀ e w1, typeNewGetBases rt ctx w = .err e w1 → typeNew rt metatype [nameV, basesV, dictV] kwds w = .err e w1) ∧
    (∀ r w1, typeNewGetBases rt ctx w = .ok (.inl r) w1 →
      typeNew rt metatype [nameV, basesV, dictV] kwds w = .ok r w1) ∧
    (∀ c w1, typeNewGetBases rt ctx w = .ok (.inr c) w1 →
      typeNew rt metatype [nameV, basesV, dictV] kwds w = typeNewImpl rt c orig w1)

theorem filterMap_str_keys (es : List (Val × Val)) (h : ∀ p ∈ es, ∃ k, p.1 = .str k) :
    (es.filterMap strKeyEntry).length = es.length := by
  induction es with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, hk⟩ := h p List.mem_cons_self
    have := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp [strKeyEntry, hk, this]

theorem typeNewExact_proven : TypeNewExact := by
  intro rt metatype nameV basesV dictV kwds w name bases es hn hb hd hk ctx orig
  have hl : orig.length = es.length := filterMap_str_keys es hk
  have hl' : ((es.filterMap strKeyEntry).length != es.length) = false := by
    simp only [orig] at hl; simp [hl]
  refine ⟨fun e w1 h => ?_, fun r w1 h => ?_, fun c w1 h => ?_⟩ <;>
    simp only [typeNew, M.bind_app, getW_app, hn, hb, hd, hl', Bool.false_eq_true, ite_false,
      M.pure_app] <;> simp only [ctx] at h <;> simp [h, orig]

/-! ## `same_slots_added`, `compatible_for_assignment` -/

/-- **`same_slots_added` compares the slot objects with `==`.** `Objects/typeobject.c:7643-7670`:
for two heap types with the same `__dict__`/`__weakref__` layout and slot tuples, the answer is
`PyObject_RichCompareBool(slots_a, slots_b, Py_EQ)` (so a `str` subclass slot name's `__eq__`
runs), with an exception from it counted as "differ", and then the size check. -/
def SameSlotsAddedExact : Prop :=
  ∀ (rt : Rt) (a b base : Addr) (sa sb : List Name) (va vb : List Val) (w : World),
    (tdata w a).base = some base → (tdata w a).heap = true → (tdata w b).heap = true →
    (tdata w a).htSlots = some sa → (tdata w b).htSlots = some sb →
    (tdata w a).htSlotVals = some va → (tdata w b).htSlotVals = some vb →
    let size0 := (tdata w base).basicsize
    let size1 := if (tdata w a).dictoffset == size0 && (tdata w b).dictoffset == size0 then size0 + 8 else size0
    let size2 := if (tdata w a).weaklistoffset == size1 && (tdata w b).weaklistoffset == size1 then size1 + 8 else size1
    let size3 := size2 + 8 * sa.length
    (∀ w1, richCompareBool rt (.tuple va) (.tuple vb) .eq w = .ok false w1 → sameSlotsAdded rt a b w = .ok false w1) ∧
    (∀ w1, richCompareBool rt (.tuple va) (.tuple vb) .eq w = .ok true w1 →
      sameSlotsAdded rt a b w = .ok (size3 == (tdata w a).basicsize && size3 == (tdata w b).basicsize) w1) ∧
    (∀ c m v w1, richCompareBool rt (.tuple va) (.tuple vb) .eq w = .err (.exc c m v) w1 →
      sameSlotsAdded rt a b w = .ok false w1)

theorem sameSlotsAddedExact_proven : SameSlotsAddedExact := by
  intro rt a b base sa sb va vb w h1 h2 h3 h4 h5 h6 h7 size0 size1 size2 size3
  refine ⟨fun w1 h => ?_, fun w1 h => ?_, fun c m v w1 h => ?_⟩ <;>
    simp [sameSlotsAdded, h1, h2, h3, h4, h5, h6, h7, h, size3, size2, size1, size0]

/-- **`compatible_for_assignment` for `__class__`, every branch.** `Objects/typeobject.c:7683-7750`
with `setclass = 1`: a different deallocator (`tp_free`) raises "'%s' deallocator differs from
'%s'"; differing layout flags, `tp_dictoffset` or `tp_weaklistoffset` raise "'%s' object layout
differs from '%s'"; then the highest compatible bases are compared: equal bases pass, bases with
different `tp_base` fail, and otherwise `same_slots_added` decides. -/
def CompatibleForAssignmentExact : Prop :=
  ∀ (rt : Rt) (oldto newto : Addr) (w : World),
    let o := tdata w oldto
    let n := tdata w newto
    let newbase := compatBase w w.heap.size newto
    let oldbase := compatBase w w.heap.size oldto
    let layoutErr : M Unit := typeErr s!"{("__class__" : String)} assignment: '{tpName w newto}' object layout differs from '{tpName w oldto}'"
    (hasGC w newto != hasGC w oldto →
      compatibleForAssignment rt oldto newto "__class__" true w =
        (typeErr s!"{("__class__" : String)} assignment: '{tpName w newto}' deallocator differs from '{tpName w oldto}'" : M Unit) w) ∧
    (hasGC w newto = hasGC w oldto →
      ((!compatibleFlags true w oldto newto || o.dictoffset != n.dictoffset ||
          o.weaklistoffset != n.weaklistoffset) = true →
        compatibleForAssignment rt oldto newto "__class__" true w = layoutErr w) ∧
      ((!compatibleFlags true w oldto newto || o.dictoffset != n.dictoffset ||
          o.weaklistoffset != n.weaklistoffset) = false →
        (newbase = oldbase → compatibleForAssignment rt oldto newto "__class__" true w = .ok () w) ∧
        (newbase ≠ oldbase → (tdata w newbase).base ≠ (tdata w oldbase).base →
          compatibleForAssignment rt oldto newto "__class__" true w = layoutErr w) ∧
        (newbase ≠ oldbase → (tdata w newbase).base = (tdata w oldbase).base →
          (∀ w1, sameSlotsAdded rt newbase oldbase w = .ok true w1 →
            compatibleForAssignment rt oldto newto "__class__" true w = .ok () w1) ∧
          (∀ w1, sameSlotsAdded rt newbase oldbase w = .ok false w1 →
            compatibleForAssignment rt oldto newto "__class__" true w =
              (typeErr s!"{("__class__" : String)} assignment: '{tpName w1 newto}' object layout differs from '{tpName w1 oldto}'" : M Unit) w1))))

theorem compatibleForAssignmentExact_proven : CompatibleForAssignmentExact := by
  intro rt oldto newto w o n newbase oldbase layoutErr
  refine ⟨fun h => ?_, fun hg => ⟨fun hd => ?_, fun hd => ⟨fun he => ?_, fun hne hb => ?_,
    fun hne hb => ⟨fun w1 hs => ?_, fun w1 hs => ?_⟩⟩⟩⟩
  · have : (hasGC w newto != hasGC w oldto) = true := by simpa using h
    simp only [compatibleForAssignment, M.bind_app, getW_app, Bool.true_and, this, ite_true]
    simp [typeErr, raiseC]
  all_goals
    have hg' : (hasGC w newto != hasGC w oldto) = false := by simp [hg]
    simp only [compatibleForAssignment, M.bind_app, getW_app, Bool.true_and, hg',
      Bool.false_eq_true, ite_false, M.pure_app, ite_true, Bool.true_or]
    simp only [o, n] at hd
    simp only [hd, ite_true, Bool.false_eq_true, ite_false]
  · simp [layoutErr, typeErr, raiseC]
  · simp only [newbase, oldbase] at he
    simp [he]
  · simp only [newbase, oldbase] at hne hb
    have h1 : (compatBase w w.heap.size newto != compatBase w w.heap.size oldto) = true := by simpa using hne
    have h2 : ((tdata w (compatBase w w.heap.size newto)).base != (tdata w (compatBase w w.heap.size oldto)).base) = true := by
      simpa using hb
    simp only [h1, h2, ite_true]
    simp [layoutErr, typeErr, raiseC]
  · simp only [newbase, oldbase] at hne hb hs
    have h1 : (compatBase w w.heap.size newto != compatBase w w.heap.size oldto) = true := by simpa using hne
    have h2 : ((tdata w (compatBase w w.heap.size newto)).base != (tdata w (compatBase w w.heap.size oldto)).base) = false := by
      simpa using hb
    simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]
    simp only [M.bind_app, hs, Bool.not_true, Bool.false_eq_true, ite_false, M.pure_app]
  · simp only [newbase, oldbase] at hne hb hs
    have h1 : (compatBase w w.heap.size newto != compatBase w w.heap.size oldto) = true := by simpa using hne
    have h2 : ((tdata w (compatBase w w.heap.size newto)).base != (tdata w (compatBase w w.heap.size oldto)).base) = false := by
      simpa using hb
    simp only [h1, h2, ite_true, Bool.false_eq_true, ite_false]
    simp only [M.bind_app, hs, Bool.not_false, ite_true, getW_app]

/-! ## `object_set_class`, `object_set_class_world_stopped` -/

/-- **`object_set_class_world_stopped`, every branch.** `Objects/typeobject.c:7755-7853`:
* unless both the old and the new type are `ModuleType` subclasses, an immutable old or new type
  raises "__class__ assignment only supported for mutable types or ModuleType subclasses";
* otherwise, in particular for two `ModuleType` subclasses, immutable or not (`m.__class__ = Mod`
  for `Mod(types.ModuleType)` succeeds on 3.15.2), the check passes;
* then `compatible_for_assignment` decides (`CompatibleForAssignmentExact`), its exception
  propagating, and on success the object's type is the new type and nothing else changes. -/
def ObjectSetClassWorldStoppedExact : Prop :=
  ∀ (rt : Rt) (a : Addr) (newto : Addr) (w : World),
    ((isModuleSubtype w newto && isModuleSubtype w (typeOf w (.obj a))) = false →
      ((tdata w newto).immutable || (tdata w (typeOf w (.obj a))).immutable) = true →
      objectSetClassWorldStopped rt (.obj a) newto w =
        (typeErr "__class__ assignment only supported for mutable types or ModuleType subclasses" : M Unit) w) ∧
    ((!(isModuleSubtype w newto && isModuleSubtype w (typeOf w (.obj a))) &&
        ((tdata w newto).immutable || (tdata w (typeOf w (.obj a))).immutable)) = false →
      (∀ e w1, compatibleForAssignment rt (typeOf w (.obj a)) newto "__class__" true w = .err e w1 →
        objectSetClassWorldStopped rt (.obj a) newto w = .err e w1) ∧
      (∀ w1 o, compatibleForAssignment rt (typeOf w (.obj a)) newto "__class__" true w = .ok () w1 →
        w1.get a = .val o →
        objectSetClassWorldStopped rt (.obj a) newto w = .ok () (w1.setCell a (.val { o with cls := newto }))))

theorem objectSetClassWorldStoppedExact_proven : ObjectSetClassWorldStoppedExact := by
  intro rt a newto w
  refine ⟨fun hm hi => ?_, fun hc => ⟨fun e w1 he => ?_, fun w1 o he ho => ?_⟩⟩
  · simp only [objectSetClassWorldStopped, M.bind_app, getW_app, hm, hi, Bool.not_false,
      Bool.true_and, ite_true]
    simp [typeErr, raiseC]
  · simp only [objectSetClassWorldStopped, M.bind_app, getW_app, hc, Bool.false_eq_true,
      ite_false, M.pure_app, he]
  · simp only [objectSetClassWorldStopped, M.bind_app, getW_app, hc, Bool.false_eq_true,
      ite_false, M.pure_app, he]
    simp [ho, modW]

/-- **`object_set_class`, every branch.** `Objects/typeobject.c:7856-7894`: deleting raises
"can't delete __class__ attribute"; a non-class raises "__class__ must be set to a class, not
'%s' object"; then the `object.__setattr__` audit event runs every installed hook with
`(self, "__class__", value)`, and an exception from a hook aborts the assignment before anything
is checked or changed (`:7872-7875`); then `object_set_class_world_stopped` decides. Scope: the
reference to the old type that `:7881` captures and `:7888` drops is not modelled; when the
comparison in `same_slots_added` re-enters and reassigns `__class__` it is stale, which
`bugs/typeobj-set-class-reentrant-slot-eq.yaml` reproduces as a crash. -/
def ObjectSetClassExact : Prop :=
  ∀ (rt : Rt) (self v : Val) (newto : Addr) (w : World),
    asType w v = some newto →
    (w.auditHooks = [] →
      objectSetClass rt self (some v) w = objectSetClassWorldStopped rt self newto w) ∧
    (∀ h hs e w1, w.auditHooks = h :: hs →
      rt.call h [.str "object.__setattr__", .tuple [self, .str "__class__", v]] [] w = .err e w1 →
      objectSetClass rt self (some v) w = .err e w1) ∧
    (∀ h r w1, w.auditHooks = [h] →
      rt.call h [.str "object.__setattr__", .tuple [self, .str "__class__", v]] [] w = .ok r w1 →
      objectSetClass rt self (some v) w = objectSetClassWorldStopped rt self newto w1)

theorem objectSetClassExact_proven : ObjectSetClassExact := by
  intro rt self v newto w hv
  refine ⟨fun ha => ?_, fun h hs e w1 ha hc => ?_, fun h r w1 ha hc => ?_⟩
  · simp [objectSetClass, hv, pySysAudit, pySysAuditLoop, ha]
  · simp [objectSetClass, hv, pySysAudit, pySysAuditLoop, ha, hc]
  · simp [objectSetClass, hv, pySysAudit, pySysAuditLoop, ha, hc]

end PyLean.TypeObj
