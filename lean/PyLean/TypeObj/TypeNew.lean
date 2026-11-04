import PyLean.TypeObj.Mro

/-!
Class creation: `mro_invoke`, `find_best_base`, `_PyType_CalculateMetaclass`, `type_new` and its
helpers, `PyType_Ready` for heap types, `inherit_special`, `inherit_slots`,
`type_new_set_names`, `type_new_init_subclass`, `__bases__` assignment and `__class__`
assignment (`Objects/typeobject.c`).

Namespaces passed to `type()` must have string keys here; the `RuntimeWarning` for other
keys (`:5017`) has no model.
-/

namespace PyLean.TypeObj

/-! ## MRO, on the world -/

/-- `class_name`, `Objects/typeobject.c:3299`. Returns `none` when `__name__` is not a
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

/-- Bytes of the UTF-8 encoding. -/
def utf8Bytes (cs : List Char) : Nat := (cs.map Char.utf8Size).sum

/-- The `PyDict_Next` loop of `set_mro_error`, `Objects/typeobject.c:3371-3394`. `off` is the
C `off`: the bytes `PyOS_snprintf` would have written so far, so the loop stops calling
`class_name` once the text reaches the 1000-byte buffer (`:3371`), and a `,` is added only
while it fits (`:3391`). The result is the untruncated text; the caller keeps its first 999
bytes, as the buffer does. -/
def setMroErrorLoop (rt : Rt) : List Addr → Nat → List Char → M (List Char)
  | [], _, text => pure text
  | c :: cs, off, text =>
    if off < 1000 then do
      let n ← classNameOf rt (.obj c)
      let s := (" " ++ n.getD "?").toList
      let off := off + utf8Bytes s
      let text := text ++ s
      if cs ≠ [] ∧ off + 1 < 1000 then setMroErrorLoop rt cs (off + 1) (text ++ [','])
      else setMroErrorLoop rt cs off text
    else pure text

/-- `set_mro_error`, `Objects/typeobject.c:3350-3398`. The message is built with `PyOS_snprintf`
in `char buf[1000]` (`:3353`, `:3370-3394`), so it is the first 999 bytes of the UTF-8 of the
whole text (a `,` is added only while it fits, `:3391`, and a cut name ends the loop, `:3373`),
and `PyErr_SetString` decodes it strictly (`:3396`). When byte 999 falls inside a character of a
non-ASCII class name, that decoding fails and CPython raises `UnicodeDecodeError` instead of the
`TypeError` (bug record `getargs-snprintf-cut-utf8-decode`); the model leaves that case out
(`gap%`), since it has no `UnicodeDecodeError` object to raise. -/
def setMroError {α : Type} (rt : Rt) (rests : List (List Addr)) : M α := do
  let heads := rests.filterMap List.head?
  let cands := dedupKeep heads []
  let pre := "Cannot create a consistent method resolution order (MRO) for bases".toList
  let full ← setMroErrorLoop rt cands (utf8Bytes pre) pre
  let cut := cutUtf8 999 full
  if (full.map Char.utf8Size).sum ≤ 999 ∨ (cut.map Char.utf8Size).sum = 999 then
    typeErr (String.ofList cut)
  else gap%

/-- `mro_implementation_unlocked` on type `t`, `Objects/typeobject.c:3471`. -/
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

/-- `shape_differs`, `Objects/typeobject.c:3802`. -/
def shapeDiffers (w : World) (a b : Addr) : Bool :=
  (tdata w a).basicsize != (tdata w b).basicsize || (tdata w a).itemsize != (tdata w b).itemsize

/-- `solid_base`, `Objects/typeobject.c:3811`, by fuel over the `tp_base` chain. -/
def solidBaseF (w : World) : Nat → Addr → Addr
  | 0, t => t
  | fuel + 1, t =>
    let base := match (tdata w t).base with
      | some b => solidBaseF w fuel b
      | none => B.object
    if shapeDiffers w t base then t else base

def solidBase (w : World) (t : Addr) : Addr := solidBaseF w w.heap.size t

/-- `mro_check`, `Objects/typeobject.c:3587`. -/
def mroCheck (t : Addr) (mro : List Val) : M Unit := do
  let w ← getW
  let solid := solidBase w t
  for obj in mro do
    match asType w obj with
    | none => typeErr s!"{typeFQN w t}.mro() returned a non-class ('{objFQN w obj}')"
    | some base =>
      unless isSubtype w solid (solidBase w base) do
        typeErr s!"{typeFQN w t}.mro() returned base with unsuitable layout ('{typeFQN w base}')"

/-- `mro_invoke`, `Objects/typeobject.c:3631`. -/
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

/-- `mro_internal`, `Objects/typeobject.c:3695`. Returns whether the new MRO was
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

/-- The loop of `find_best_base`, `Objects/typeobject.c:3757-3795`. `winner` is the most derived
solid base so far, `base` the base that provided it. -/
def bestBaseLoop (w : World) : List Val → Option Addr → Option Addr → Except String Addr
  | [], _, some b => .ok b
  | [], _, none => .error "bases must be types"
  | bp :: rest, winner, base =>
    match asType w bp with
    | none => .error s!"bases must be types; got '{objFQN w bp}'"
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

/-- `find_best_base`, `Objects/typeobject.c:3747`. -/
def bestBase (bases : List Val) : M Addr := do
  let w ← getW
  match bestBaseLoop w bases none none with
  | .ok b => pure b
  | .error m => typeErr m

/-- `_PyType_CalculateMetaclass`, `Objects/typeobject.c:4213`, as a pure loop. -/
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

/-- `type_new_ctx`, `Objects/typeobject.c:4253`. -/
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

/-- `valid_identifier`, `Objects/typeobject.c:4158`. -/
def validIdentifier (s : Val) : M String := do
  let w ← getW
  match strOf w s with
  | none => typeErr s!"__slots__ items must be strings, not '{trunc 200 (typeName w s)}'"
  | some n =>
    if isIdentifier n then pure n else typeErr "__slots__ must be identifiers"

/-- `type_new_visit_slots`, `Objects/typeobject.c:4272`. -/
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

/-- `type_new_copy_slots`, `Objects/typeobject.c:4310`. Sorted with `PyList_Sort` on
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

/-- `type_new_slots_bases`, `Objects/typeobject.c:4379`. -/
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

/-- `type_new_slots_impl`, `Objects/typeobject.c:4418`. -/
def typeNewSlotsImpl (ctx : TypeNewCtx) (slots : List Val) (dict : NameDict) :
    M (TypeNewCtx × List Name) := do
  let w ← getW
  let c ← typeNewVisitSlots ctx slots
  let names ← typeNewCopySlots c slots dict
  let c := { c with nslot := names.length }
  let c ← typeNewSlotsBases c
  pure (c, names)

/-- `type_new_slots`, `Objects/typeobject.c:4440`. -/
def typeNewSlots (ctx : TypeNewCtx) (dict : NameDict) : M (TypeNewCtx × Option (List Name)) := do
  let w ← getW
  let d := tdata w ctx.base
  let c := { ctx with
    addDict := false, addWeak := false,
    mayAddDict := d.dictoffset == 0,
    mayAddWeak := d.weaklistoffset == 0 }
  match ctx.slots with
  | none =>
    pure ({ c with addDict := c.mayAddDict, addWeak := c.mayAddWeak && d.itemsize == 0 }, none)
  | some slots =>
    let (c, names) ← typeNewSlotsImpl c slots dict
    pure (c, some names)

/-- `type_new_get_slots`, `Objects/typeobject.c:4927`. -/
def typeNewGetSlots (rt : Rt) (ctx : TypeNewCtx) (dict : NameDict) : M TypeNewCtx := do
  match NameDict.get? dict "__slots__" with
  | none => pure { ctx with slots := none, nslot := 0 }
  | some slots =>
    let w ← getW
    let items ← match strOf w slots with
      | some _ => pure [slots]
      | none => pySequenceTuple rt slots
    pure { ctx with slots := some items, nslot := items.length }

/-- `functools_wraps`, `Objects/funcobject.c:1391`, with `functools_copy_attr`. -/
def functoolsWraps (rt : Rt) (wrapper wrapped : Val) : M Unit := do
  for n in ["__module__", "__name__", "__qualname__", "__doc__"] do
    match ← rt.getOptionalAttr wrapped n with
    | some v => rt.setAttr wrapper n (some v)
    | none => pure ()

/-- `PyStaticMethod_New`/`PyClassMethod_New`, `Objects/funcobject.c:1993`, `:1727`. They go through
`sm_set_callable` and `cm_set_callable`, so the wrapper has the attributes of the function. -/
def wrapInDict (rt : Rt) (dict : NameDict) (attr : Name) (cls : Addr) (mk : Val → Payload) :
    M NameDict := do
  let w ← getW
  match NameDict.get? dict attr with
  | some f =>
    match payloadOf w f with
    | some (.func _) =>
      let s ← alloc cls (mk f)
      functoolsWraps rt s f
      pure (NameDict.set dict attr s)
    | _ => pure dict
  | none => pure dict

/-- `type_new_set_attrs`, `Objects/typeobject.c:4862`, on the dict, before descriptors. -/
def typeNewSetAttrs (rt : Rt) (ctx : TypeNewCtx) (t : Addr) (dict0 : NameDict) : M NameDict := do
  if ctx.name.contains (Char.ofNat 0) then
    valueErr "type name must not contain null characters"
  let w ← getW
  -- type_new_set_module, :4535
  let dict := if NameDict.contains dict0 "__module__" then dict0
    else match w.curModule with
      | some m => NameDict.set dict0 "__module__" m
      | none => dict0
  -- type_new_set_ht_name, :4563
  let (dict, qual) ← match NameDict.get? dict "__qualname__" with
    | some q =>
      match strOf w q with
      | none => typeErr s!"type __qualname__ must be a str, not {typeName w q}"
      | some qs => pure (NameDict.erase dict "__qualname__", qs)
    | none => pure (dict, ctx.name)
  modType t fun d => { d with qualname := qual }
  let dict ← wrapInDict rt dict "__new__" B.staticmethod .staticmethod
  let dict ← wrapInDict rt dict "__init_subclass__" B.classmethod .classmethod
  let dict ← wrapInDict rt dict "__class_getitem__" B.classmethod .classmethod
  pure dict

/-- `type_add_common_descriptor`, `Objects/typeobject.c:4684`: the cached getset of `object`, and
`PyDict_SetDefaultRef`, so a `__dict__` of the class body stays. -/
def typeAddCommonDescriptor (isDict : Bool) (dict : NameDict) : M NameDict := do
  let w ← getW
  let n : Name := if isDict then "__dict__" else "__weakref__"
  let descr ← match (if isDict then w.dictDescr else w.weakrefDescr) with
    | some d => pure d
    | none =>
      let d ← alloc B.getsetDescr (.getsetDescr B.object n isDict)
      modW fun w => if isDict then { w with dictDescr := some d } else { w with weakrefDescr := some d }
      pure d
  pure (if NameDict.contains dict n then dict else NameDict.set dict n descr)

/-- `type_new_descriptors`, `Objects/typeobject.c:4711`, and `type_new_set_slots`, `:4791`: sizes,
offsets, and the two common descriptors. -/
def typeNewDescriptors (ctx : TypeNewCtx) (t : Addr) (nslot : Nat) (dict : NameDict) :
    M NameDict := do
  let w ← getW
  let bd := tdata w ctx.base
  if nslot > 0 && bd.itemsize != 0 && !isSubtype w ctx.base B.tuple then
    typeErr s!"arbitrary __slots__ not supported for subtype of '{tpName w ctx.base}'"
  let basic := bd.basicsize + 8 * nslot
  modType t fun d => { d with
    weaklistoffset := if ctx.addWeak then -32 else d.weaklistoffset
    dictoffset := if ctx.addDict then -1 else d.dictoffset
    basicsize := basic
    itemsize := bd.itemsize }
  let dict ← if ctx.addDict then typeAddCommonDescriptor true dict else pure dict
  if ctx.addWeak then typeAddCommonDescriptor false dict else pure dict

/-- `type_new_set_classcell`/`type_new_set_classdictcell`, `Objects/typeobject.c:4810`,
`:4836`. The dict cell receives the tp_dict proxy. -/
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
      typeErr s!"{key} must be a nonlocal cell, not {truncChars 200 (typeRepr w (typeOf w cell))}"

/-! ## `PyType_Ready` for heap types -/

/-- `SLOTDEFINED`, `Objects/typeobject.c:8889`. -/
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

/-- `COPYSLOT`, `Objects/typeobject.c:8893`. -/
def copySlot (t b : Addr) (w : World) (s : Slot) : World :=
  if (slotOf w t s).isNone && slotDefined w b (basebaseFor w b s.group) s then
    match w.get t with
    | .ty c d => w.setCell t (.ty c { d with slots := setSlot d.slots s (slotOf w b s) })
    | .val _ => w
  else w

/-- `overrides_hash`, `Objects/typeobject.c:8865`. -/
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

/-- `inherit_slots`, `Objects/typeobject.c:8878`. -/
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

/-- `inherit_special`, `Objects/typeobject.c:8798`: the value slots. -/
def inheritSpecial (t b : Addr) : M Unit := do
  let w ← getW
  let bd := tdata w b
  modType t fun d => { d with
    basicsize := if d.basicsize == 0 then bd.basicsize else d.basicsize
    itemsize := if d.itemsize == 0 then bd.itemsize else d.itemsize
    weaklistoffset := if d.weaklistoffset == 0 then bd.weaklistoffset else d.weaklistoffset
    dictoffset := if d.dictoffset == 0 then bd.dictoffset else d.dictoffset }

/-- `type_ready_set_new`, `Objects/typeobject.c:9471`, for a heap type on first
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

/-- `type_ready_fill_dict`, `Objects/typeobject.c:9238`, for a heap type: members from
`__slots__`, the getsets of `subtype_getsets_*`, and `__doc__`. -/
def typeReadyFillDict (t : Addr) (members : List Name) : M Unit := do
  addOperators t
  for m in members do
    let d ← alloc B.memberDescr (.memberDescr t m false)
    dictSetDefault t m d
  dictSetDefault t "__doc__" .none

/-- `type_ready_inherit`, `Objects/typeobject.c:9377`. -/
def typeReadyInherit (t : Addr) : M Unit := do
  let w ← getW
  match (tdata w t).base with
  | some b => inheritSpecial t b
  | none => pure ()
  modW fun w =>
    ((tdata w t).mro.getD []).drop 1 |>.foldl (fun w b => inheritSlots w t b) w

/-- `type_ready_set_hash`, `Objects/typeobject.c:9429`. -/
def typeReadySetHash (t : Addr) : M Unit := do
  let w ← getW
  if (slotOf w t .tp_hash).isNone && !NameDict.contains (tdata w t).dict "__hash__" then
    modType t fun d => { d with
      dict := NameDict.set d.dict "__hash__" .none
      slots := setSlot d.slots .tp_hash (some .hashNotImpl) }

/-- `add_subclass`, `Objects/typeobject.c:9793`, via `type_ready_add_subclasses`. -/
def addSubclass (b t : Addr) : M Unit :=
  modType b fun d => { d with subclasses := d.subclasses ++ [t] }

/-- `remove_subclass`, `Objects/typeobject.c:9873`. -/
def removeSubclass (b t : Addr) : M Unit :=
  modType b fun d => { d with subclasses := d.subclasses.filter (· != t) }

/-- `type_ready`, `Objects/typeobject.c:9584`, for a heap type. -/
def typeReady (rt : Rt) (t : Addr) (members : List Name) : M Unit := do
  let _ ← mroInternal rt t
  typeReadySetNew t
  typeReadyFillDict t members
  typeReadyInherit t
  typeReadySetHash t
  let w ← getW
  for b in (tdata w t).bases do
    addSubclass b t

/-- The `while` of `type_new_set_names`, `Objects/typeobject.c:12391`. -/
def typeNewSetNamesLoop (rt : Rt) (t : Addr) : NameDict → M Unit
  | [] => pure ()
  | (key, value) :: rest => do
    match ← lookupSpecial rt value "__set_name__" with
    | none => typeNewSetNamesLoop rt t rest
    | some setName =>
      let _ ← tryM (rt.call setName [.obj t, .str key] []) fun e => do
        let w ← getW
        raiseWithNote rt e s!"Error calling __set_name__ on '{trunc 100 (typeName w value)}' instance {reprStr key} in '{trunc 100 (tpName w t)}'"
      typeNewSetNamesLoop rt t rest

/-- `type_new_set_names`, `Objects/typeobject.c:12381`. -/
def typeNewSetNames (rt : Rt) (t : Addr) : M Unit := do
  let w ← getW
  typeNewSetNamesLoop rt t (tdata w t).dict

/-- `type_new_init_subclass`, `Objects/typeobject.c:12427`. -/
def typeNewInitSubclass (rt : Rt) (t : Addr) (kwds : Kw) : M Unit := do
  let sup ← rt.call (.obj B.super) [.obj t, .obj t] []
  let func ← rt.getAttr sup "__init_subclass__"
  let _ ← rt.call func [] kwds
  pure ()

/-- The object `ht_slots` holds for the (mangled) slot name `n`: the `__slots__` item itself when
`_Py_Mangle` left it unchanged, so a `str` subclass instance stays one, else a new `str`. -/
def slotNameObj (w : World) (slots : List Val) (n : Name) : Val :=
  match slots.find? (fun v => strOf w v == some n) with
  | some v => v
  | none => .str n

/-- `type_new_impl` after `type_new_init`, `Objects/typeobject.c:5001`, with
`type_new_alloc` (`:4467`). -/
def typeNewImpl (rt : Rt) (ctx0 : TypeNewCtx) (orig : NameDict) : M Val := do
  -- type_new_init, :4958
  let ctx ← typeNewGetSlots rt ctx0 orig
  let (ctx, names) ← typeNewSlots ctx orig
  let w ← getW
  let baseAddrs := ctx.bases.filterMap (asType w)
  let t ← allocCell (.ty ctx.metatype {
    name := ctx.name, qualname := ctx.name, base := some ctx.base, bases := baseAddrs,
    dict := orig, asNumber := true, asSequence := true, asMapping := true, asAsync := true,
    asBuffer := true, heap := true, baseType := true,
    htSlots := names.bind fun n => if n.isEmpty then none else some n
    htSlotVals := (names.bind fun n => if n.isEmpty then none else some n).map fun ns =>
      ns.map fun n => slotNameObj w ((ctx.slots).getD []) n })
  let dict ← typeNewSetAttrs rt ctx t orig
  let members := names.getD []
  let dict ← typeNewDescriptors ctx t ctx.nslot dict
  let dict ← typeNewSetCell "__classcell__" (.obj t) dict
  let dict ← typeNewSetCell "__classdictcell__" (.obj t) dict
  modType t fun d => { d with dict := dict }
  typeReady rt t members
  modW fun w => fixupSlotDispatchers w t
  typeNewSetNames rt t
  typeNewInitSubclass rt t ctx.kwds
  pure (.obj t)

/-- The loop at `Objects/typeobject.c:5061-5076`: a non-class base with `__mro_entries__`. -/
def checkMroEntries (rt : Rt) : List Val → M Unit
  | [] => pure ()
  | base :: rest => do
    let w ← getW
    if typeCheck w base then checkMroEntries rt rest
    else
      match ← rt.getOptionalAttr base "__mro_entries__" with
      | some _ => typeErr "type() doesn't support MRO entry resolution; use types.new_class()"
      | none => checkMroEntries rt rest

/-- `type_new_get_bases`, `Objects/typeobject.c:5047`. The left result is a finished
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

/-- A namespace entry with an exact `str` key. -/
def strKeyEntry (p : Val × Val) : Option (Name × Val) :=
  match p.1 with
  | .str k => some (k, p.2)
  | _ => none

/-- `type_new`, `Objects/typeobject.c:5118`. -/
def typeNew (rt : Rt) (metatype : Addr) (args : List Val) (kwds : Kw) : M Val := do
  let w ← getW
  match args with
  | [nameV, basesV, dictV] =>
    let some name := strOf w nameV
      | typeErr s!"type.__new__() argument 1 must be str, not {typeName w nameV}"
    let some bases := tupleOf w basesV
      | typeErr s!"type.__new__() argument 2 must be tuple, not {typeName w basesV}"
    let some es := anyDictOf w dictV
      | typeErr s!"type.__new__() argument 3 must be dict or frozendict, not {objFQN w dictV}"
    let orig : NameDict := es.filterMap strKeyEntry
    if orig.length != es.length then gap%
    let ctx : TypeNewCtx := { metatype, args, kwds, name, bases }
    match ← typeNewGetBases rt ctx with
    | .inl r => pure r
    | .inr c => typeNewImpl rt c orig
  | _ => typeErr s!"type.__new__() takes exactly 3 arguments ({args.length} given)"

/-! ## `__bases__` and `__class__` assignment -/

/-- `check_set_special_type_attr`, `Objects/typeobject.c:1519`. -/
def checkSetSpecial (t : Addr) (value : Option Val) (name : String) : M Unit := do
  let w ← getW
  if value.isNone then
    typeErr s!"cannot delete '{name}' attribute of type '{tpName w t}'"
  if (tdata w t).immutable then
    typeErr s!"cannot set '{name}' attribute of immutable type '{tpName w t}'"

/-- `compatible_with_tp_base`, `Objects/typeobject.c:7633`. Every heap type has `subtype_dealloc`;
the static classes that can be a base and have the size of their parent inherit its `tp_dealloc`. -/
def compatibleWithTpBase (w : World) (child : Addr) : Bool :=
  match (tdata w child).base with
  | none => false
  | some parent =>
    let c := tdata w child
    let p := tdata w parent
    c.basicsize == p.basicsize && c.itemsize == p.itemsize

/-- `Py_TPFLAGS_HAVE_GC`: heap types always; among builtins, what the table records. A
type's instances participate in GC when it is a heap type or one of these. -/
def hasGC (w : World) (t : Addr) : Bool :=
  (tdata w t).heap || isSubtype w t B.type || isSubtype w t B.BaseException ||
    t == B.list || t == B.dict || t == B.tuple || t == B.super || t == B.property ||
    t == B.classmethod || t == B.staticmethod || t == B.function || t == B.method

/-- The walk up the `tp_base` chain in `compatible_for_assignment`, `:7733`. -/
def compatBase (w : World) : Nat → Addr → Addr
  | 0, t => t
  | fuel + 1, t =>
    if compatibleWithTpBase w t then
      match (tdata w t).base with
      | some p => compatBase w fuel p
      | none => t
    else t

/-- `same_slots_added`, `Objects/typeobject.c:7643-7670`. The two `ht_slots` tuples are compared
with `PyObject_RichCompareBool(slots_a, slots_b, Py_EQ)` (`:7665`), which runs the `__eq__` of
`str` subclass slot names; an exception from it counts as "differ" (`!= 1`), and
`compatible_for_assignment` then replaces it with its own `TypeError`. Types the model built
without the slot objects compare their names. -/
def sameSlotsAdded (rt : Rt) (a b : Addr) : M Bool := do
  let w ← getW
  let da := tdata w a
  let db := tdata w b
  match da.base with
  | none => pure false
  | some base =>
    let size0 := (tdata w base).basicsize
    let size1 := if da.dictoffset == size0 && db.dictoffset == size0 then size0 + 8 else size0
    let size2 := if da.weaklistoffset == size1 && db.weaklistoffset == size1 then size1 + 8 else size1
    if !da.heap || !db.heap then pure false else
    match da.htSlots, db.htSlots with
    | some sa, some sb =>
      let eq ← match da.htSlotVals, db.htSlotVals with
        | some va, some vb =>
          tryM (richCompareBool rt (.tuple va) (.tuple vb) .eq) fun e =>
            match e with
            | .exc _ _ _ => pure false
            | e => raise e
        | _, _ => pure (sa == sb)
      if !eq then pure false
      else
        let size3 := size2 + 8 * sa.length
        pure (size3 == da.basicsize && size3 == db.basicsize)
    | _, _ => pure (size2 == da.basicsize && size2 == db.basicsize)

/-- `tp_flags & (Py_TPFLAGS_HAVE_GC | Py_TPFLAGS_INLINE_VALUES | Py_TPFLAGS_PREHEADER)`. -/
def layoutFlags (w : World) (t : Addr) : List Bool :=
  let d := tdata w t
  [hasGC w t, d.heap && d.dictoffset == -1 && d.itemsize == 0, d.dictoffset == -1,
    d.weaklistoffset == -32]

/-- `compatible_flags`, `Objects/typeobject.c:7673`: for `__class__` the flags are equal, for
`__bases__` the new base may only have flags the class has. -/
def compatibleFlags (setclass : Bool) (w : World) (origto newto : Addr) : Bool :=
  if setclass then layoutFlags w origto == layoutFlags w newto
  else ((layoutFlags w origto).zip (layoutFlags w newto)).all fun (o, n) => o || !n

/-- `compatible_for_assignment`, `Objects/typeobject.c:7683-7750`. `tp_free` is `PyObject_GC_Del`
exactly for GC types among those modelled. The checks run in the C order: deallocator, flags,
`tp_dictoffset`, `tp_weaklistoffset`, then the compatible bases, where `same_slots_added` runs
only when the two bases differ and share `tp_base`. -/
def compatibleForAssignment (rt : Rt) (origto newto : Addr) (attr : String) (setclass : Bool) :
    M Unit := do
  let w ← getW
  let oldto := if setclass then origto else (tdata w origto).base.getD B.object
  if setclass && hasGC w newto != hasGC w oldto then
    typeErr s!"{attr} assignment: '{tpName w newto}' deallocator differs from '{tpName w oldto}'"
  let o := tdata w origto
  let n := tdata w newto
  let newbase := compatBase w w.heap.size newto
  let oldbase := compatBase w w.heap.size oldto
  let differsErr : M Unit := do
    let w ← getW
    typeErr s!"{attr} assignment: '{tpName w newto}' object layout differs from '{tpName w oldto}'"
  if !compatibleFlags setclass w origto newto ||
      ((setclass || n.dictoffset != 0) && o.dictoffset != n.dictoffset) ||
      ((setclass || n.weaklistoffset != 0) && o.weaklistoffset != n.weaklistoffset) then
    differsErr
  else if newbase != oldbase then
    if (tdata w newbase).base != (tdata w oldbase).base then differsErr
    else if !(← sameSlotsAdded rt newbase oldbase) then differsErr

/-- `PySys_Audit(event, args)`, `Python/sysmodule.c`: each installed hook is called with the event
name and the argument tuple; the first exception aborts. -/
def pySysAuditLoop (rt : Rt) (event : String) (args : List Val) : List Val → M Unit
  | [] => pure ()
  | h :: hs => do
    let _ ← rt.call h [.str event, .tuple args] []
    pySysAuditLoop rt event args hs

def pySysAudit (rt : Rt) (event : String) (args : List Val) : M Unit := do
  let w ← getW
  pySysAuditLoop rt event args w.auditHooks

/-- `PyType_IsSubtype(t, &PyModule_Type)`; no type is when the world has no `ModuleType`. -/
def isModuleSubtype (w : World) (t : Addr) : Bool :=
  match w.moduleType with
  | some m => isSubtype w t m
  | none => false

/-- `object_set_class_world_stopped`, `Objects/typeobject.c:7755-7853`: the mutable-type check,
with its `ModuleType` allowlist (`:7809-7810`), then `compatible_for_assignment`, then the new
type. Materialising a managed dict (`:7822-7840`) moves the inline values into a dict object,
which this model always has, so it is not a step here. -/
def objectSetClassWorldStopped (rt : Rt) (self : Val) (newto : Addr) : M Unit := do
  let w ← getW
  let oldto := typeOf w self
  if !(isModuleSubtype w newto && isModuleSubtype w oldto) &&
      ((tdata w newto).immutable || (tdata w oldto).immutable) then
    typeErr "__class__ assignment only supported for mutable types or ModuleType subclasses"
  compatibleForAssignment rt oldto newto "__class__" true
  match self with
  | .obj a =>
    modW fun w =>
      match w.get a with
      | .val o => w.setCell a (.val { o with cls := newto })
      | .ty _ d => w.setCell a (.ty newto d)
  | _ => gap%

/-- `object_set_class`, `Objects/typeobject.c:7856-7894`: the delete and non-class errors, the
`object.__setattr__` audit event (`:7872-7875`), then `object_set_class_world_stopped`. -/
def objectSetClass (rt : Rt) (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "can't delete __class__ attribute"
  | some v =>
    match asType w v with
    | none => typeErr s!"__class__ must be set to a class, not '{typeName w v}' object"
    | some newto =>
      pySysAudit rt "object.__setattr__" [self, .str "__class__", v]
      objectSetClassWorldStopped rt self newto

/-- `mro_hierarchy_for_complete_type`, `Objects/typeobject.c:1837`: recompute the MRO of
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

/-- A class and everything below it: what `mro_hierarchy_for_complete_type` puts in `temp`. -/
def hierarchy (w : World) : Nat → Addr → List Addr
  | 0, _ => []
  | fuel + 1, t => t :: (tdata w t).subclasses.flatMap (hierarchy w fuel)

/-- `type_check_new_bases` and `type_set_bases_unlocked`, `Objects/typeobject.c:1905`, `:1968`. A failure while recomputing
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
  compatibleForAssignment rt t newBase "__bases__" false
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
      for x in hierarchy wNow wNow.heap.size t do
        if x < w.heap.size then modType x fun d => { d with mro := saved x }
      undoBases
      raise e

end PyLean.TypeObj
