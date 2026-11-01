import PyLean.TypeObj.Mro

/-!
Class creation: `mro_invoke`, `best_base`, `_PyType_CalculateMetaclass`, `type_new` and its
helpers, `PyType_Ready` for heap types, `inherit_special`, `inherit_slots`,
`type_new_set_names`, `type_new_init_subclass`, `__bases__` assignment and `__class__`
assignment (`Objects/typeobject.c`).

Namespaces passed to `type()` must have string keys here; the `RuntimeWarning` for other
keys (`:4666`) has no model.
-/

namespace PyLean.TypeObj

/-! ## MRO, on the world -/

/-- `class_name`, `Objects/typeobject.c:3159`. Returns `none` when `__name__` is not a
string. -/
def classNameOf (rt : Rt) (cls : Val) : M (Option String) := do
  match ← rt.getOptionalAttr cls "__name__" with
  | some n =>
    let w ← getW
    pure (strOf w n)
  | none => some <$> rt.repr cls

/-- Distinct items in first-seen order, as a dict keyed by class keeps them. -/
def dedupKeep : List Addr → List Addr → List Addr
  | [], seen => seen.reverse
  | x :: xs, seen => if seen.contains x then dedupKeep xs seen else dedupKeep xs (x :: seen)

/-- `set_mro_error`, `Objects/typeobject.c:3209`. -/
def setMroError {α : Type} (rt : Rt) (rests : List (List Addr)) : M α := do
  let heads := rests.filterMap List.head?
  let cands := dedupKeep heads []
  let mut names : List String := []
  for c in cands do
    let n ← classNameOf rt (.obj c)
    names := names ++ [n.getD "?"]
  let body := ",".intercalate (names.map (" " ++ ·))
  typeErr (trunc 999 ("Cannot create a consistent method resolution order (MRO) for bases" ++ body))

/-- `mro_implementation_unlocked` on type `t`, `Objects/typeobject.c:3330`. -/
def mroImplementation (rt : Rt) (t : Addr) : M (List Addr) := do
  let w ← getW
  match mroImpl t (fun b => (tdata w b).mro) (tdata w t).bases with
  | .ok m => pure m
  | .incomplete b => typeErr s!"Cannot extend an incomplete type '{trunc 100 (tpName w b)}'"
  | .duplicate d =>
    match ← classNameOf rt (.obj d) with
    | some n => typeErr s!"duplicate base class {n}"
    | none => typeErr "duplicate base class"
  | .conflict rests => setMroError rt rests
  | .fuel => raise .fuel

/-- `shape_differs`, `Objects/typeobject.c:3669`. -/
def shapeDiffers (w : World) (a b : Addr) : Bool :=
  (tdata w a).basicsize != (tdata w b).basicsize || (tdata w a).itemsize != (tdata w b).itemsize

/-- `solid_base`, `Objects/typeobject.c:3678`, by fuel over the `tp_base` chain. -/
def solidBaseF (w : World) : Nat → Addr → Addr
  | 0, t => t
  | fuel + 1, t =>
    let base := match (tdata w t).base with
      | some b => solidBaseF w fuel b
      | none => B.object
    if shapeDiffers w t base then t else base

def solidBase (w : World) (t : Addr) : Addr := solidBaseF w w.heap.size t

/-- `mro_check`, `Objects/typeobject.c:3446`. -/
def mroCheck (t : Addr) (mro : List Val) : M Unit := do
  let w ← getW
  let solid := solidBase w t
  for obj in mro do
    match asType w obj with
    | none => typeErr s!"mro() returned a non-class ('{trunc 500 (typeName w obj)}')"
    | some base =>
      unless isSubtype w solid (solidBase w base) do
        typeErr s!"mro() returned base with unsuitable layout ('{trunc 500 (tpName w base)}')"

/-- `mro_invoke`, `Objects/typeobject.c:3492`. -/
def mroInvoke (rt : Rt) (t : Addr) : M (List Addr) := do
  let w ← getW
  let custom := typeOf w (.obj t) != B.type
  let result : List Val ←
    if custom then do
      let r ← callMethod rt (.obj t) "mro" [] []
      pySequenceTuple rt r
    else do
      let m ← mroImplementation rt t
      pure (m.map Val.obj)
  if result.isEmpty then typeErr "type MRO must not be empty"
  if custom then mroCheck t result
  let w ← getW
  pure (result.filterMap (asType w))

/-- `mro_internal_unlocked`, `Objects/typeobject.c:3552`. Returns whether the new MRO was
stored. The reentrancy test compares by value: the C test is on pointers, which differ
in the same cases unless a custom `mro()` installs an equal MRO. -/
def mroInternal (rt : Rt) (t : Addr) : M Bool := do
  let w ← getW
  let old := (tdata w t).mro
  let newMro ← mroInvoke rt t
  let w ← getW
  if (tdata w t).mro != old then pure false
  else
    modType t fun d => { d with mro := some newMro }
    pure true

/-- The loop of `best_base`, `Objects/typeobject.c:3624-3662`. `winner` is the most derived
solid base so far, `base` the base that provided it. -/
def bestBaseLoop (w : World) : List Val → Option Addr → Option Addr → Except String Addr
  | [], _, some b => .ok b
  | [], _, none => .error "bases must be types"
  | bp :: rest, winner, base =>
    match asType w bp with
    | none => .error "bases must be types"
    | some bi =>
      if !(tdata w bi).baseType then
        .error s!"type '{trunc 100 (tpName w bi)}' is not an acceptable base type"
      else
        let candidate := solidBase w bi
        match winner with
        | none => bestBaseLoop w rest (some candidate) (some bi)
        | some win =>
          if isSubtype w win candidate then bestBaseLoop w rest winner base
          else if isSubtype w candidate win then bestBaseLoop w rest (some candidate) (some bi)
          else .error "multiple bases have instance lay-out conflict"

/-- `best_base`, `Objects/typeobject.c:3614`. -/
def bestBase (bases : List Val) : M Addr := do
  let w ← getW
  match bestBaseLoop w bases none none with
  | .ok b => pure b
  | .error m => typeErr m

/-- `_PyType_CalculateMetaclass`, `Objects/typeobject.c:3921`, as a pure loop. -/
def calculateMetaclassLoop (w : World) (winner : Addr) : List Val → Option Addr
  | [] => some winner
  | b :: rest =>
    let t := typeOf w b
    if isSubtype w winner t then calculateMetaclassLoop w winner rest
    else if isSubtype w t winner then calculateMetaclassLoop w t rest
    else none

/-- `_PyType_CalculateMetaclass`, raising the conflict error. -/
def calculateMetaclass (metatype : Addr) (bases : List Val) : M Addr := do
  let w ← getW
  match calculateMetaclassLoop w metatype bases with
  | some m => pure m
  | none =>
    typeErr "metaclass conflict: the metaclass of a derived class must be a (non-strict) subclass of the metaclasses of all its bases"

/-! ## `type_new` -/

/-- `type_new_ctx`, `Objects/typeobject.c:3960`. -/
structure TypeNewCtx where
  metatype : Addr
  args : List Val
  kwds : Kw
  name : String
  bases : List Val
  base : Addr := 0
  slots : Option (List Val) := none
  nslot : Nat := 0
  addDict : Bool := false
  addWeak : Bool := false
  mayAddDict : Bool := false
  mayAddWeak : Bool := false

/-- `PyUnicode_IsIdentifier` for ASCII; other characters are accepted as `XID_Continue`
without the Unicode tables. -/
def isIdentifier (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs =>
    let start (c : Char) := c.isAlpha || c == '_' || c.toNat > 127
    let cont (c : Char) := c.isAlphanum || c == '_' || c.toNat > 127
    start c && cs.all cont

/-- `_Py_Mangle(classname, name)`, `Python/compile.c` family: the rule for `__x` names. -/
def pyMangle (cls name : String) : String :=
  let n := name.toList
  if n.length < 2 || n.take 2 != ['_', '_'] then name
  else if n.drop (n.length - 2) == ['_', '_'] then name
  else if n.contains '.' then name
  else
    let c := cls.toList.dropWhile (· == '_')
    if c.isEmpty then name else String.ofList ('_' :: c) ++ name

/-- `valid_identifier`, `Objects/typeobject.c:3866`. -/
def validIdentifier (s : Val) : M String := do
  let w ← getW
  match strOf w s with
  | none => typeErr s!"__slots__ items must be strings, not '{trunc 200 (typeName w s)}'"
  | some n =>
    if isIdentifier n then pure n else typeErr "__slots__ must be identifiers"

/-- `type_new_visit_slots`, `Objects/typeobject.c:3979`. -/
def typeNewVisitSlots (ctx : TypeNewCtx) : List Val → M TypeNewCtx
  | [] => pure ctx
  | s :: rest => do
    let n ← validIdentifier s
    if n == "__dict__" && (!ctx.mayAddDict || ctx.addDict) then
      typeErr "__dict__ slot disallowed: we already got one"
    let c := if n == "__dict__" then { ctx with addDict := true } else ctx
    if n == "__weakref__" && (!c.mayAddWeak || c.addWeak) then
      typeErr "__weakref__ slot disallowed: we already got one"
    let c := if n == "__weakref__" then { c with addWeak := true } else c
    typeNewVisitSlots c rest

/-- `type_new_copy_slots`, `Objects/typeobject.c:4017`. Sorted with `PyList_Sort` on
strings: code point order. -/
def typeNewCopySlots (ctx : TypeNewCtx) (slots : List Val) (dict : NameDict) :
    M (List Name) := do
  let w ← getW
  let mut out : List Name := []
  for s in slots do
    let n := (strOf w s).getD ""
    if (ctx.addDict && n == "__dict__") || (ctx.addWeak && n == "__weakref__") then continue
    let m := pyMangle ctx.name n
    out := out ++ [m]
    if NameDict.contains dict m then
      if m != "__qualname__" && m != "__classcell__" && m != "__classdictcell__" then
        valueErr s!"{reprStr m} in __slots__ conflicts with class variable"
  pure (out.mergeSort (fun a b => decide (strCompare a.toList b.toList ≤ 0)))

/-- `type_new_slots_bases`, `Objects/typeobject.c:4086`. -/
def typeNewSlotsBases (ctx : TypeNewCtx) : M TypeNewCtx := do
  let w ← getW
  if ctx.bases.length > 1 &&
      ((ctx.mayAddDict && !ctx.addDict) || (ctx.mayAddWeak && !ctx.addWeak)) then
    let mut c := ctx
    for obj in ctx.bases do
      if obj.is (.obj ctx.base) then continue
      let b := match obj with
        | .obj a => a
        | _ => 0
      if c.mayAddDict && !c.addDict && (tdata w b).dictoffset != 0 then
        c := { c with addDict := true }
      if c.mayAddWeak && !c.addWeak && (tdata w b).weaklistoffset != 0 then
        c := { c with addWeak := true }
      if c.mayAddDict && !c.addDict then continue
      if c.mayAddWeak && !c.addWeak then continue
      break
    pure c
  else pure ctx

/-- `type_new_slots_impl`, `Objects/typeobject.c:4125`. -/
def typeNewSlotsImpl (ctx : TypeNewCtx) (slots : List Val) (dict : NameDict) :
    M (TypeNewCtx × List Name) := do
  let w ← getW
  if ctx.nslot > 0 && (tdata w ctx.base).itemsize != 0 then
    typeErr s!"nonempty __slots__ not supported for subtype of '{tpName w ctx.base}'"
  let c ← typeNewVisitSlots ctx slots
  let names ← typeNewCopySlots c slots dict
  let c := { c with nslot := names.length }
  let c ← typeNewSlotsBases c
  pure (c, names)

/-- `type_new_slots`, `Objects/typeobject.c:4155`. -/
def typeNewSlots (ctx : TypeNewCtx) (dict : NameDict) : M (TypeNewCtx × Option (List Name)) := do
  let w ← getW
  let d := tdata w ctx.base
  let c := { ctx with
    addDict := false, addWeak := false,
    mayAddDict := d.dictoffset == 0,
    mayAddWeak := d.weaklistoffset == 0 && d.itemsize == 0 }
  match ctx.slots with
  | none =>
    pure ({ c with addDict := c.mayAddDict, addWeak := c.mayAddWeak }, none)
  | some slots =>
    let (c, names) ← typeNewSlotsImpl c slots dict
    pure (c, some names)

/-- `type_new_get_slots`, `Objects/typeobject.c:4579`. -/
def typeNewGetSlots (rt : Rt) (ctx : TypeNewCtx) (dict : NameDict) : M TypeNewCtx := do
  match NameDict.get? dict "__slots__" with
  | none => pure { ctx with slots := none, nslot := 0 }
  | some slots =>
    let w ← getW
    let items ← match strOf w slots with
      | some _ => pure [slots]
      | none => pySequenceTuple rt slots
    pure { ctx with slots := some items, nslot := items.length }

/-- `PyStaticMethod_New`/`PyClassMethod_New`, `Objects/funcobject.c:1972`, `:1724`. -/
def wrapInDict (dict : NameDict) (attr : Name) (cls : Addr) (mk : Val → Payload) :
    M NameDict := do
  let w ← getW
  match NameDict.get? dict attr with
  | some f =>
    match payloadOf w f with
    | some (.func _) =>
      let s ← alloc cls (mk f)
      pure (NameDict.set dict attr s)
    | _ => pure dict
  | none => pure dict

/-- `type_new_set_attrs`, `Objects/typeobject.c:4526`, on the dict, before descriptors. -/
def typeNewSetAttrs (ctx : TypeNewCtx) (t : Addr) (dict0 : NameDict) : M NameDict := do
  if ctx.name.contains (Char.ofNat 0) then
    valueErr "type name must not contain null characters"
  let w ← getW
  -- type_new_set_module, :4251
  let dict := if NameDict.contains dict0 "__module__" then dict0
    else match w.curModule with
      | some m => NameDict.set dict0 "__module__" m
      | none => dict0
  -- type_new_set_ht_name, :4279
  let (dict, qual) ← match NameDict.get? dict "__qualname__" with
    | some q =>
      match strOf w q with
      | none => typeErr s!"type __qualname__ must be a str, not {typeName w q}"
      | some qs => pure (NameDict.erase dict "__qualname__", qs)
    | none => pure (dict, ctx.name)
  modType t fun d => { d with qualname := qual }
  let dict ← wrapInDict dict "__new__" B.staticmethod .staticmethod
  let dict ← wrapInDict dict "__init_subclass__" B.classmethod .classmethod
  let dict ← wrapInDict dict "__class_getitem__" B.classmethod .classmethod
  pure dict

/-- `type_new_descriptors`, `Objects/typeobject.c:4401`, and `type_new_set_slots`,
`:4444`: sizes and offsets; returns the getset names of `subtype_getsets_*`. -/
def typeNewDescriptors (ctx : TypeNewCtx) (t : Addr) (nslot : Nat) : M (List Name) := do
  let w ← getW
  let bd := tdata w ctx.base
  let basic := bd.basicsize + 8 * nslot
  modType t fun d => { d with
    weaklistoffset := if ctx.addWeak then -32 else d.weaklistoffset
    dictoffset := if ctx.addDict then -1 else d.dictoffset
    basicsize := basic
    itemsize := bd.itemsize }
  pure ((if ctx.addDict then ["__dict__"] else []) ++ (if ctx.addWeak then ["__weakref__"] else []))

/-- `type_new_set_classcell`/`type_new_set_classdictcell`, `Objects/typeobject.c:4474`,
`:4500`. The dict cell receives the tp_dict proxy. -/
def typeNewSetCell (key : Name) (value : Val) (dict : NameDict) : M NameDict := do
  let w ← getW
  match NameDict.get? dict key with
  | none => pure dict
  | some cell =>
    match cell, payloadOf w cell with
    | .obj c, some (.cell _) =>
      modObj c fun o => { o with body := .cell (some value) }
      pure (NameDict.erase dict key)
    | _, _ =>
      typeErr s!"{key} must be a nonlocal cell, not {trunc 200 (typeRepr w (typeOf w cell))}"

/-! ## `PyType_Ready` for heap types -/

/-- `SLOTDEFINED`, `Objects/typeobject.c:8255`. -/
def slotDefined (w : World) (b : Addr) (basebase : Option Addr) (s : Slot) : Bool :=
  match slotOf w b s with
  | none => false
  | some f =>
    match basebase with
    | none => true
    | some bb => slotOf w bb s != some f

/-- `basebase` for a slot group: NULL if that struct is NULL there. -/
def basebaseFor (w : World) (b : Addr) (g : SlotGroup) : Option Addr :=
  match (tdata w b).base with
  | none => none
  | some bb => if hasGroup w bb g then some bb else none

/-- `COPYSLOT`, `Objects/typeobject.c:8259`. -/
def copySlot (t b : Addr) (w : World) (s : Slot) : World :=
  if (slotOf w t s).isNone && slotDefined w b (basebaseFor w b s.group) s then
    match w.get t with
    | .ty c d => w.setCell t (.ty c { d with slots := setSlot d.slots s (slotOf w b s) })
    | .val _ => w
  else w

/-- `overrides_hash`, `Objects/typeobject.c:8231`. -/
def overridesHash (w : World) (t : Addr) : Bool :=
  NameDict.contains (tdata w t).dict "__eq__" || NameDict.contains (tdata w t).dict "__hash__"

/-- The slots `inherit_slots` copies with `COPYNUM`, `COPYSEQ`, `COPYMAP`, `COPYASYNC`,
`COPYBUF`, in order. -/
def inheritedGroupSlots : List Slot :=
  [ .nb_add, .nb_subtract, .nb_multiply, .nb_remainder, .nb_divmod, .nb_power, .nb_negative,
    .nb_positive, .nb_absolute, .nb_bool, .nb_invert, .nb_lshift, .nb_rshift, .nb_and,
    .nb_xor, .nb_or, .nb_int, .nb_float, .nb_inplace_add, .nb_inplace_subtract,
    .nb_inplace_multiply, .nb_inplace_remainder, .nb_inplace_power, .nb_inplace_lshift,
    .nb_inplace_rshift, .nb_inplace_and, .nb_inplace_xor, .nb_inplace_or, .nb_true_divide,
    .nb_floor_divide, .nb_inplace_true_divide, .nb_inplace_floor_divide, .nb_index,
    .nb_matrix_multiply, .nb_inplace_matrix_multiply,
    .am_await, .am_aiter, .am_anext,
    .sq_length, .sq_concat, .sq_repeat, .sq_item, .sq_ass_item, .sq_contains,
    .sq_inplace_concat, .sq_inplace_repeat,
    .mp_length, .mp_subscript, .mp_ass_subscript, .bf_getbuffer, .bf_releasebuffer ]

/-- Set a slot of `t` to the value it has in `b`. -/
def takeSlot (t b : Addr) (w : World) (s : Slot) : World :=
  match w.get t with
  | .ty c d => w.setCell t (.ty c { d with slots := setSlot d.slots s (slotOf w b s) })
  | .val _ => w

/-- `inherit_slots`, `Objects/typeobject.c:8244`. -/
def inheritSlots (w : World) (t b : Addr) : World :=
  let w := inheritedGroupSlots.foldl (fun w s =>
    if hasGroup w t s.group && hasGroup w b s.group then copySlot t b w s else w) w
  let w := if (slotOf w t .tp_getattro).isNone then takeSlot t b w .tp_getattro else w
  let w := if (slotOf w t .tp_setattro).isNone then takeSlot t b w .tp_setattro else w
  let w := copySlot t b w .tp_repr
  let w := copySlot t b w .tp_call
  let w := copySlot t b w .tp_str
  let w := if (slotOf w t .tp_richcompare).isNone && (slotOf w t .tp_hash).isNone then
      if !overridesHash w t then
        takeSlot t b (takeSlot t b w .tp_richcompare) .tp_hash
      else w
    else w
  let w := copySlot t b w .tp_iter
  let w := copySlot t b w .tp_iternext
  let w := copySlot t b w .tp_descr_get
  let w := copySlot t b w .tp_descr_set
  let w := copySlot t b w .tp_init
  copySlot t b w .tp_finalize

/-- `inherit_special`, `Objects/typeobject.c:8164`: the value slots. -/
def inheritSpecial (t b : Addr) : M Unit := do
  let w ← getW
  let bd := tdata w b
  modType t fun d => { d with
    basicsize := if d.basicsize == 0 then bd.basicsize else d.basicsize
    itemsize := if d.itemsize == 0 then bd.itemsize else d.itemsize
    weaklistoffset := if d.weaklistoffset == 0 then bd.weaklistoffset else d.weaklistoffset
    dictoffset := if d.dictoffset == 0 then bd.dictoffset else d.dictoffset }

/-- `type_ready_set_new`, `Objects/typeobject.c:8823`, for a heap type on first
readying: `tp_new` is inherited. -/
def typeReadySetNew (t : Addr) : M Unit := do
  let w ← getW
  match (tdata w t).base with
  | some b =>
    if (slotOf w t .tp_new).isNone then
      modW fun w => takeSlot t b w .tp_new
  | none => pure ()

/-- `PyDict_SetDefaultRef` on `tp_dict`. -/
def dictSetDefault (t : Addr) (n : Name) (v : Val) : M Unit :=
  modType t fun d =>
    if NameDict.contains d.dict n then d else { d with dict := NameDict.set d.dict n v }

/-- `type_ready_fill_dict`, `Objects/typeobject.c:8604`, for a heap type: members from
`__slots__`, the getsets of `subtype_getsets_*`, and `__doc__`. -/
def typeReadyFillDict (t : Addr) (members getsets : List Name) : M Unit := do
  addOperators t
  for m in members do
    let d ← alloc B.memberDescr (.memberDescr t m false)
    dictSetDefault t m d
  for g in getsets do
    let d ← alloc B.getsetDescr (.getsetDescr t g (g == "__dict__"))
    dictSetDefault t g d
  dictSetDefault t "__doc__" .none

/-- `type_ready_inherit`, `Objects/typeobject.c:8729`. -/
def typeReadyInherit (t : Addr) : M Unit := do
  let w ← getW
  match (tdata w t).base with
  | some b => inheritSpecial t b
  | none => pure ()
  modW fun w =>
    ((tdata w t).mro.getD []).drop 1 |>.foldl (fun w b => inheritSlots w t b) w

/-- `type_ready_set_hash`, `Objects/typeobject.c:8781`. -/
def typeReadySetHash (t : Addr) : M Unit := do
  let w ← getW
  if (slotOf w t .tp_hash).isNone && !NameDict.contains (tdata w t).dict "__hash__" then
    modType t fun d => { d with
      dict := NameDict.set d.dict "__hash__" .none
      slots := setSlot d.slots .tp_hash (some .hashNotImpl) }

/-- `add_subclass`, `Objects/typeobject.c:9101`, via `type_ready_add_subclasses`. -/
def addSubclass (b t : Addr) : M Unit :=
  modType b fun d => { d with subclasses := d.subclasses ++ [t] }

/-- `remove_subclass`, `Objects/typeobject.c:9181`. -/
def removeSubclass (b t : Addr) : M Unit :=
  modType b fun d => { d with subclasses := d.subclasses.filter (· != t) }

/-- `type_ready`, `Objects/typeobject.c:8936`, for a heap type. -/
def typeReady (rt : Rt) (t : Addr) (members getsets : List Name) : M Unit := do
  let _ ← mroInternal rt t
  typeReadySetNew t
  typeReadyFillDict t members getsets
  typeReadyInherit t
  typeReadySetHash t
  let w ← getW
  for b in (tdata w t).bases do
    addSubclass b t

/-- `_PyErr_FormatNote` / `_PyException_AddNote`, `Objects/exceptions.c:4574`: append a
note to the exception and re-raise. -/
def raiseWithNote {α : Type} (e : PyErr) (note : String) : M α := do
  let x ← excObject e
  let w ← getW
  match x, payloadOf w x with
  | .obj a, some (.exc d) =>
    let noteList ← match d.notes with
      | some nl => pure nl
      | none => alloc B.list (.list [])
    let w ← getW
    match noteList with
    | .obj l =>
      modObj l fun o => { o with body := .list (((listOf w noteList).getD []) ++ [.str note]) }
    | _ => pure ()
    modObj a fun o =>
      match o.body with
      | .exc d => { o with body := .exc { d with notes := some noteList } }
      | _ => o
    raise (match e with
      | .exc c m _ => .exc c m (some x)
      | .fuel => .fuel)
  | _, _ => raise e

/-- The `while` of `type_new_set_names`, `Objects/typeobject.c:11541`. -/
def typeNewSetNamesLoop (rt : Rt) (t : Addr) : NameDict → M Unit
  | [] => pure ()
  | (key, value) :: rest => do
    match ← lookupSpecial rt value "__set_name__" with
    | none => typeNewSetNamesLoop rt t rest
    | some setName =>
      let _ ← tryM (rt.call setName [.obj t, .str key] []) fun e => do
        let w ← getW
        raiseWithNote e s!"Error calling __set_name__ on '{trunc 100 (typeName w value)}' instance {reprStr key} in '{trunc 100 (tpName w t)}'"
      typeNewSetNamesLoop rt t rest

/-- `type_new_set_names`, `Objects/typeobject.c:11531`. -/
def typeNewSetNames (rt : Rt) (t : Addr) : M Unit := do
  let w ← getW
  typeNewSetNamesLoop rt t (tdata w t).dict

/-- `type_new_init_subclass`, `Objects/typeobject.c:11577`. -/
def typeNewInitSubclass (rt : Rt) (t : Addr) (kwds : Kw) : M Unit := do
  let sup ← rt.call (.obj B.super) [.obj t, .obj t] []
  let func ← rt.getAttr sup "__init_subclass__"
  let _ ← rt.call func [] kwds
  pure ()

/-- `type_new_impl` after `type_new_init`, `Objects/typeobject.c:4647`, with
`type_new_alloc` (`:4183`). -/
def typeNewImpl (rt : Rt) (ctx0 : TypeNewCtx) (orig : NameDict) : M Val := do
  -- type_new_init, :4610
  let ctx ← typeNewGetSlots rt ctx0 orig
  let (ctx, names) ← typeNewSlots ctx orig
  let w ← getW
  let baseAddrs := ctx.bases.filterMap (asType w)
  let t ← allocCell (.ty ctx.metatype {
    name := ctx.name, qualname := ctx.name, base := some ctx.base, bases := baseAddrs,
    dict := orig, asNumber := true, asSequence := true, asMapping := true, asAsync := true,
    asBuffer := true, heap := true, baseType := true, htSlots := names })
  let dict ← typeNewSetAttrs ctx t orig
  let members := names.getD []
  let getsets ← typeNewDescriptors ctx t ctx.nslot
  let dict ← typeNewSetCell "__classcell__" (.obj t) dict
  let dict ← typeNewSetCell "__classdictcell__" (.obj t) dict
  modType t fun d => { d with dict := dict }
  typeReady rt t members getsets
  modW fun w => fixupSlotDispatchers w t
  typeNewSetNames rt t
  typeNewInitSubclass rt t ctx.kwds
  pure (.obj t)

/-- The loop at `Objects/typeobject.c:4710-4725`: a non-class base with `__mro_entries__`. -/
def checkMroEntries (rt : Rt) : List Val → M Unit
  | [] => pure ()
  | base :: rest => do
    let w ← getW
    if typeCheck w base then checkMroEntries rt rest
    else
      match ← rt.getOptionalAttr base "__mro_entries__" with
      | some _ => typeErr "type() doesn't support MRO entry resolution; use types.new_class()"
      | none => checkMroEntries rt rest

/-- `type_new_get_bases`, `Objects/typeobject.c:4696`. The left result is a finished
object from a more derived metaclass. -/
def typeNewGetBases (rt : Rt) (ctx : TypeNewCtx) : M (Sum Val TypeNewCtx) := do
  if ctx.bases.isEmpty then
    return .inr { ctx with base := B.object, bases := [.obj B.object] }
  checkMroEntries rt ctx.bases
  let winner ← calculateMetaclass ctx.metatype ctx.bases
  let w ← getW
  let mut c := ctx
  if winner != ctx.metatype then
    match slotOf w winner .tp_new with
    | some (.c .type) => c := { c with metatype := winner }
    | none => typeErr s!"cannot create '{trunc 400 (tpName w winner)}' instances"
    | some f =>
      let r ← rt.tpNew f winner ctx.args ctx.kwds
      return .inl r
  let base ← bestBase c.bases
  pure (.inr { c with base := base })

/-- `type_new`, `Objects/typeobject.c:4767`. -/
def typeNew (rt : Rt) (metatype : Addr) (args : List Val) (kwds : Kw) : M Val := do
  let w ← getW
  match args with
  | [nameV, basesV, dictV] =>
    let some name := strOf w nameV
      | typeErr s!"type.__new__() argument 1 must be str, not {typeName w nameV}"
    let some bases := tupleOf w basesV
      | typeErr s!"type.__new__() argument 2 must be tuple, not {typeName w basesV}"
    let some es := dictOf w dictV
      | typeErr s!"type.__new__() argument 3 must be dict, not {typeName w dictV}"
    let orig : NameDict := es.filterMap fun p =>
      match p.1 with
      | .str k => some (k, p.2)
      | _ => none
    if orig.length != es.length then unmodelled
    let ctx : TypeNewCtx := { metatype, args, kwds, name, bases }
    match ← typeNewGetBases rt ctx with
    | .inl r => pure r
    | .inr c => typeNewImpl rt c orig
  | _ => typeErr s!"type.__new__() takes exactly 3 arguments ({args.length} given)"

/-! ## `__bases__` and `__class__` assignment -/

/-- `check_set_special_type_attr`, `Objects/typeobject.c:1419`. -/
def checkSetSpecial (t : Addr) (value : Option Val) (name : String) : M Unit := do
  let w ← getW
  if (tdata w t).immutable then
    typeErr s!"cannot set '{name}' attribute of immutable type '{tpName w t}'"
  if value.isNone then
    typeErr s!"cannot delete '{name}' attribute of immutable type '{tpName w t}'"

/-- `compatible_with_tp_base`, `Objects/typeobject.c:7023`. Every heap type has
`subtype_dealloc` and a GC flag equal to its heap parent's; a heap child of a non-GC
static type adds GC and so is not compatible, which `gcFlag` encodes. -/
def compatibleWithTpBase (gcFlag : Addr → Bool) (w : World) (child : Addr) : Bool :=
  match (tdata w child).base with
  | none => false
  | some parent =>
    let c := tdata w child
    let p := tdata w parent
    c.basicsize == p.basicsize && c.itemsize == p.itemsize &&
      c.dictoffset == p.dictoffset && c.weaklistoffset == p.weaklistoffset &&
      gcFlag child == gcFlag parent

/-- `Py_TPFLAGS_HAVE_GC`: heap types always; among builtins, what the table records. A
type's instances participate in GC when it is a heap type or one of these. -/
def hasGC (w : World) (t : Addr) : Bool :=
  (tdata w t).heap || isSubtype w t B.type || isSubtype w t B.BaseException ||
    t == B.list || t == B.dict || t == B.tuple || t == B.super || t == B.property ||
    t == B.classmethod || t == B.staticmethod || t == B.function || t == B.method

/-- The walk up the `tp_base` chain in `compatible_for_assignment`, `:7092`. -/
def compatBase (w : World) : Nat → Addr → Addr
  | 0, t => t
  | fuel + 1, t =>
    if compatibleWithTpBase (hasGC w) w t then
      match (tdata w t).base with
      | some p => compatBase w fuel p
      | none => t
    else t

/-- `same_slots_added`, `Objects/typeobject.c:7038`. -/
def sameSlotsAdded (w : World) (a b : Addr) : Bool :=
  let da := tdata w a
  let db := tdata w b
  match da.base with
  | none => false
  | some base =>
    let size0 := (tdata w base).basicsize
    let size1 := if da.dictoffset == size0 && db.dictoffset == size0 then size0 + 8 else size0
    let size2 := if da.weaklistoffset == size1 && db.weaklistoffset == size1 then size1 + 8 else size1
    if !da.heap || !db.heap then false else
    match da.htSlots, db.htSlots with
    | some sa, some sb =>
      if sa != sb then false
      else
        let size3 := size2 + 8 * sa.length
        size3 == da.basicsize && size3 == db.basicsize
    | _, _ => size2 == da.basicsize && size2 == db.basicsize

/-- The instance-layout flags compared at `Objects/typeobject.c:7101-7111`. -/
def inlineValuesFlag (w : World) (t : Addr) : Bool :=
  let d := tdata w t
  d.heap && d.dictoffset == -1 && d.itemsize == 0

/-- `tp_flags & Py_TPFLAGS_PREHEADER`: managed dict, managed weakref. -/
def preheaderFlag (w : World) (t : Addr) : Bool × Bool :=
  let d := tdata w t
  (d.dictoffset == -1, d.weaklistoffset == -32)

/-- `compatible_for_assignment`, `Objects/typeobject.c:7067`. `tp_free` is
`PyObject_GC_Del` exactly for GC types among those modelled. -/
def compatibleForAssignment (oldto newto : Addr) (attr : String) : M Unit := do
  let w ← getW
  if hasGC w newto != hasGC w oldto then
    typeErr s!"{attr} assignment: '{tpName w newto}' deallocator differs from '{tpName w oldto}'"
  let newbase := compatBase w w.heap.size newto
  let oldbase := compatBase w w.heap.size oldto
  let differs : Bool :=
    (newbase != oldbase &&
      ((tdata w newbase).base != (tdata w oldbase).base || !sameSlotsAdded w newbase oldbase)) ||
    inlineValuesFlag w oldto != inlineValuesFlag w newto ||
    preheaderFlag w oldto != preheaderFlag w newto
  if differs then
    typeErr s!"{attr} assignment: '{tpName w newto}' object layout differs from '{tpName w oldto}'"

/-- `object_set_class`, `Objects/typeobject.c:7225`, with
`object_set_class_world_stopped` (`:7125`). The module allowlist is not modelled: no
module objects here. -/
def objectSetClass (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "can't delete __class__ attribute"
  | some v =>
    match asType w v with
    | none => typeErr s!"__class__ must be set to a class, not '{typeName w v}' object"
    | some newto =>
      let oldto := typeOf w self
      if (tdata w newto).immutable || (tdata w oldto).immutable then
        typeErr "__class__ assignment only supported for mutable types or ModuleType subclasses"
      compatibleForAssignment oldto newto "__class__"
      match self with
      | .obj a =>
        modW fun w =>
          match w.get a with
          | .val o => w.setCell a (.val { o with cls := newto })
          | .ty _ d => w.setCell a (.ty newto d)
      | _ => unmodelled

/-- `mro_hierarchy_for_complete_type`, `Objects/typeobject.c:1724`: recompute the MRO of
`t` and its subclasses, recording old MROs for undo. -/
def mroHierarchy (rt : Rt) : Nat → Addr → M (List (Addr × Option (List Addr)))
  | 0, _ => raise .fuel
  | fuel + 1, t => do
    let w ← getW
    let old := (tdata w t).mro
    let stored ← mroInternal rt t
    if !stored then return []
    let w ← getW
    let subs := (tdata w t).subclasses
    let mut acc : List (Addr × Option (List Addr)) := [(t, old)]
    for s in subs do
      let more ← mroHierarchy rt fuel s
      acc := acc ++ more
    pure acc

/-- `type_set_bases_unlocked`, `Objects/typeobject.c:1792`. A failure while recomputing
restores `tp_bases`, `tp_base` and every MRO already changed (`undo`, `bail`). -/
def typeSetBases (rt : Rt) (t : Addr) (value : Option Val) : M Unit := do
  checkSetSpecial t value "__bases__"
  let w ← getW
  let newV := value.getD .none
  let tn := tpName w t
  let some items := tupleOf w newV
    | typeErr s!"can only assign tuple to {tn}.__bases__, not {typeName w newV}"
  if items.isEmpty then
    typeErr s!"can only assign non-empty tuple to {tn}.__bases__, not ()"
  for ob in items do
    match asType w ob with
    | none => typeErr s!"{tn}.__bases__ must be tuple of classes, not '{typeName w ob}'"
    | some base =>
      if isSubtype w base t || ((tdata w base).mro.isSome && baseChain w w.heap.size base t) then
        typeErr "a __bases__ item causes an inheritance cycle"
  let newBase ← bestBase items
  let w ← getW
  let oldBaseO := (tdata w t).base
  let oldBases := (tdata w t).bases
  compatibleForAssignment (oldBaseO.getD B.object) newBase "__bases__"
  let newAddrs := items.filterMap (asType w)
  modType t fun d => { d with bases := newAddrs, base := some newBase }
  let undoBases : M Unit :=
    modType t fun d => { d with bases := oldBases, base := oldBaseO }
  let saved : Addr → Option (List Addr) := fun x => (tdata w x).mro
  tryM (do
      let _ ← mroHierarchy rt w.heap.size t
      for b in oldBases do removeSubclass b t
      for b in newAddrs do addSubclass b t
      modW fun w => updateAllSlots w t)
    fun e => do
      let wNow ← getW
      for x in (tdata wNow t).subclasses ++ [t] do
        modType x fun d => { d with mro := saved x }
      undoBases
      raise e

end PyLean.TypeObj
