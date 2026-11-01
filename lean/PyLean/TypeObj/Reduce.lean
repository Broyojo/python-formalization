import PyLean.TypeObj.TypeNew

/-!
`object.__getstate__`, `object.__reduce__` and `object.__reduce_ex__`,
`Objects/typeobject.c:7286-7835`, with the parts of `Lib/copyreg.py` they call.

`copyreg` is Python code, so the mirror of it goes through `Rt` wherever the source does attribute
access, a call or a truth test: a metaclass `__getattribute__` or a raising `__getstate__` acts
here as it does there. The functions `copyreg` contributes to a reduce tuple are only named in the
result; calling one is not modelled.
-/

namespace PyLean.TypeObj

/-- A function of `Lib/copyreg.py`, as it appears in a reduce tuple. -/
def copyregFunc (n : Name) : M Val :=
  alloc B.function (.func { name := n, qualname := n, module := .str "copyreg", code := 1000000 })

/-- The `__dict__` of an object, `PyObject_GenericGetDict`, `Objects/dictobject.c:7607`. -/
def genericGetDict (obj : Val) : M Val := do
  let w ← getW
  if hasDictPtr w obj then
    let d ← ensureDict obj
    pure (.obj d)
  else attrErr "This object has no __dict__"

/-- `_PyObject_IsInstanceDictEmpty`, `Objects/dictobject.c:7216`. -/
def instanceDictEmpty (w : World) (obj : Val) : Bool :=
  if (tdata w (typeOf w obj)).dictoffset == 0 then true
  else
    match instDictAddr w obj with
    | none => true
    | some d => (dictEntries w d).isEmpty

/-- `except:` in Python: every exception, and no model gap. -/
def exceptAll (x : M Unit) : M Unit :=
  tryM x fun e =>
    match e with
    | .exc _ _ _ => pure ()
    | e => raise e

/-- The name `_slotnames` records for a slot, `Lib/copyreg.py:135-145`. -/
def slotnameOf (cname name : String) : String :=
  let cs := name.toList
  if cs.take 2 == ['_', '_'] && cs.drop (cs.length - 2) != ['_', '_'] then
    let stripped := cname.toList.dropWhile (· == '_')
    if stripped.isEmpty then name else "_" ++ String.ofList stripped ++ name
  else name

/-- `for name in slots:` of `_slotnames`, appending to `acc` in reverse. -/
def slotnamesLoop (rt : Rt) (cname : String) (it : Val) : Nat → List Val → M (List Val)
  | 0, _ => raise .fuel
  | fuel + 1, acc => do
    match ← rt.iterNext it with
    | none => pure acc
    | some name =>
      let w ← getW
      match strOf w name with
      | none => gap%
      | some n =>
        if n == "__dict__" || n == "__weakref__" then slotnamesLoop rt cname it fuel acc
        else slotnamesLoop rt cname it fuel (.str (slotnameOf cname n) :: acc)

/-- `for c in cls.__mro__:` of `_slotnames`, `Lib/copyreg.py:130-145`. -/
def slotnamesMro (rt : Rt) : List Val → List Val → M (List Val)
  | [], acc => pure acc
  | c :: cs, acc => do
    let d ← rt.getAttr c "__dict__"
    if ← rt.contains d (.str "__slots__") then
      let slots ← rt.getItem d (.str "__slots__")
      let w ← getW
      -- `isinstance(slots, str)`: one slot given as a string.
      let slots : Val := if (strOf w slots).isSome then .tuple [slots] else slots
      let nameV ← rt.getAttr c "__name__"
      let w ← getW
      let it ← rt.getIter slots
      let acc ← slotnamesLoop rt ((strOf w nameV).getD "") it iterFuel acc
      slotnamesMro rt cs acc
    else slotnamesMro rt cs acc

/-- `copyreg._slotnames`, `Lib/copyreg.py:112`, reached when the class has no cached value. The
result is cached on the class if that works, and an error from trying is dropped (`:157`). -/
def copyregSlotnames (rt : Rt) (cls : Addr) : M Val := do
  let names ← match ← rt.getOptionalAttr (.obj cls) "__slots__" with
    | none => pure []
    | some _ =>
      let mro ← rt.getAttr (.obj cls) "__mro__"
      let w ← getW
      slotnamesMro rt ((tupleOf w mro).getD []) []
  let l ← alloc B.list (.list names.reverse)
  exceptAll (rt.setAttr (.obj cls) "__slotnames__" (some l))
  pure l

/-- `_PyType_GetSlotNames`, `Objects/typeobject.c:7304`. -/
def typeGetSlotNames (rt : Rt) (cls : Addr) : M Val := do
  let w ← getW
  match NameDict.get? (tdata w cls).dict "__slotnames__" with
  | some s =>
    if s.is .none || (listOf w s).isSome then pure s
    else typeErr s!"{trunc 200 (tpName w cls)}.__slotnames__ should be a list or None, not {trunc 200 (typeName w s)}"
  | none =>
    let s ← copyregSlotnames rt cls
    let w ← getW
    if s.is .none || (listOf w s).isSome then pure s
    else typeErr "copyreg._slotnames didn't return a list or None"

/-- One round of the loop of `object_getstate_default`, `Objects/typeobject.c:7420-7436`. -/
def getstateSlotStep (rt : Rt) (obj names : Val) (slots : Addr) (i : Nat) : M Unit := do
  let w ← getW
  let name := ((listOf w names).getD [])[i]?.getD .none
  let value ← match strOf w name with
    | some n => rt.getOptionalAttr obj n
    | none => typeErr s!"attribute name must be string, not '{typeName w name}'"
  match value with
  | none => pure ()
  | some v => dictSetAt rt slots name v

/-- The loop of `object_getstate_default`, `Objects/typeobject.c:7417-7454`. The list lives on the
class, so a getter can change it, which `:7440` catches. -/
def getstateSlotsLoop (rt : Rt) (obj names : Val) (size : Nat) (slots : Addr) :
    Nat → Nat → M Unit
  | 0, _ => raise .fuel
  | fuel + 1, i => do
    if i ≥ size then pure () else
    getstateSlotStep rt obj names slots i
    let w ← getW
    if ((listOf w names).getD []).length != size then
      runtimeErr "__slotnames__ changed size during iteration"
    getstateSlotsLoop rt obj names size slots fuel (i + 1)

/-- `object_getstate_default`, `Objects/typeobject.c:7353`. `required` is the pickling check on
objects that hold more than their `__dict__` and slots. -/
def objectGetstateDefault (rt : Rt) (obj : Val) (required : Bool) : M Val := do
  let w ← getW
  let d := tdata w (typeOf w obj)
  let d' (t : Addr) : NameDict := (tdata w t).dict
  if required && d.itemsize != 0 then
    typeErr s!"cannot pickle {trunc 200 (typeName w obj)} objects"
  -- The `__dict__` of a class is `tp_dict`, here a `NameDict`, read out as a dict. A static type
  -- keeps its dict per interpreter, so its `tp_dict` field is NULL and it counts as empty.
  let state ← match asType w obj with
    | some t =>
      if (tdata w t).heap then alloc B.dict (.dict ((d' t).map fun (k, v) => (Val.str k, v)))
      else pure .none
    | none => if instanceDictEmpty w obj then pure .none else genericGetDict obj
  let names ← typeGetSlotNames rt (typeOf w obj)
  let w ← getW
  let count := ((listOf w names).getD []).length
  if required then
    -- `:7383-7395`: a dict held in the object and a weakref list count as expected, and each slot
    -- as a pointer. `tp_dictoffset` is -1 for a managed dict, which takes no room.
    let base : Int := (tdata w B.object).basicsize
    let base := if d.dictoffset != 0 && d.dictoffset != -1 then base + 8 else base
    let base := if d.weaklistoffset > 0 then base + 8 else base
    let base := if !names.is .none then base + 8 * count else base
    if d.basicsize > base then
      typeErr s!"cannot pickle '{trunc 200 (typeName w obj)}' object"
  if !names.is .none && count > 0 then
    let slots ← allocCell (.val { cls := B.dict, body := .dict [] })
    getstateSlotsLoop rt obj names count slots iterFuel 0
    let w ← getW
    if (dictEntries w slots).isEmpty then pure state
    else pure (.tuple [state, .obj slots])
  else pure state

/-- `object_getstate`, `Objects/typeobject.c:7478`: `__getstate__` is looked up on the object, and
only `object`'s own, bound to this object, gets the `required` argument. -/
def objectGetstate (rt : Rt) (obj : Val) (required : Bool) : M Val := do
  let g ← rt.getAttr obj "__getstate__"
  let w ← getW
  match payloadOf w g with
  | some (.builtin .objectGetstate (some s)) =>
    if s.is obj then objectGetstateDefault rt obj required else rt.call g [] []
  | _ => rt.call g [] []

/-- The two outcomes of `__getnewargs_ex__`, checked as `Objects/typeobject.c:7538-7574` does. -/
def checkNewargsEx (newargs : Val) : M (Val × Val) := do
  let w ← getW
  match tupleOf w newargs with
  | none =>
    typeErr s!"__getnewargs_ex__ should return a tuple, not '{trunc 200 (typeName w newargs)}'"
  | some [a, k] =>
    if (tupleOf w a).isNone then
      typeErr s!"first item of the tuple returned by __getnewargs_ex__ must be a tuple, not '{trunc 200 (typeName w a)}'"
    if (dictOf w k).isNone then
      typeErr s!"second item of the tuple returned by __getnewargs_ex__ must be a dict, not '{trunc 200 (typeName w k)}'"
    pure (a, k)
  | some xs =>
    valueErr s!"__getnewargs_ex__ should return a tuple of length 2, not {xs.length}"

/-- `_PyObject_GetNewArguments`, `Objects/typeobject.c:7520`. -/
def getNewArguments (rt : Rt) (obj : Val) : M (Option Val × Option Val) := do
  match ← lookupSpecial rt obj "__getnewargs_ex__" with
  | some m =>
    let newargs ← rt.call m [] []
    let (a, k) ← checkNewargsEx newargs
    pure (some a, some k)
  | none =>
    match ← lookupSpecial rt obj "__getnewargs__" with
    | some m =>
      let a ← rt.call m [] []
      let w ← getW
      if (tupleOf w a).isNone then
        typeErr s!"__getnewargs__ should return a tuple, not '{trunc 200 (typeName w a)}'"
      pure (some a, none)
    | none => pure (none, none)

/-- `_PyObject_GetItemsIter`, `Objects/typeobject.c:7612`. -/
def getItemsIter (rt : Rt) (obj : Val) : M (Val × Val) := do
  let w ← getW
  let l ← if (listOf w obj).isSome then rt.getIter obj else pure .none
  let w ← getW
  let d ← if (dictOf w obj).isSome then do
      let f ← rt.getAttr obj "items"
      let items ← rt.call f [] []
      rt.getIter items
    else pure .none
  pure (l, d)

/-- `reduce_newobj`, `Objects/typeobject.c:7652`. -/
def reduceNewobj (rt : Rt) (obj : Val) : M Val := do
  let w ← getW
  let cls := Val.obj (typeOf w obj)
  if (slotOf w (typeOf w obj) .tp_new).isNone then
    typeErr s!"cannot pickle '{trunc 200 (typeName w obj)}' object"
  let (args, kwargs) ← getNewArguments rt obj
  let w ← getW
  let hasargs := args.isSome
  let empty := match kwargs with
    | none => true
    | some k => ((dictOf w k).getD []).isEmpty
  let (newobj, newargs) ← if empty then do
      let f ← copyregFunc "__newobj__"
      let xs := match args with
        | some a => (tupleOf w a).getD []
        | none => []
      pure (f, Val.tuple (cls :: xs))
    else
      match args, kwargs with
      | some a, some k => do
        let f ← copyregFunc "__newobj_ex__"
        pure (f, Val.tuple [cls, a, k])
      | _, _ => gap%
  let w ← getW
  let state ← objectGetstate rt obj (!(hasargs || (listOf w obj).isSome || (dictOf w obj).isSome))
  let (l, d) ← getItemsIter rt obj
  pure (.tuple [newobj, newargs, state, l, d])

/-- `for base in cls.__mro__:` of `_reduce_ex`, `Lib/copyreg.py:62-69`. -/
def reduceExBase (rt : Rt) : List Val → M Val
  | [] => pure (.obj B.object)
  | base :: rest => do
    let w ← getW
    match asType w base with
    | none => gap%
    | some b =>
      if !(tdata w b).heap then pure base
      else
        let new ← rt.getAttr base "__new__"
        let w ← getW
        match payloadOf w new with
        | some (.builtin (.tpNewWrapper _) (some s)) =>
          if s.is base then pure base else reduceExBase rt rest
        | _ => reduceExBase rt rest

/-- `copyreg._reduce_ex`, `Lib/copyreg.py:60`, for protocols 0 and 1. -/
def copyregReduceEx (rt : Rt) (self : Val) (proto : Int) : M Val := do
  let cls ← rt.getAttr self "__class__"
  let mro ← rt.getAttr cls "__mro__"
  let w ← getW
  let base ← reduceExBase rt ((tupleOf w mro).getD [])
  let state ← if base.is (.obj B.object) then pure .none
    else if base.is cls then
      let n ← rt.getAttr cls "__name__"
      typeErr s!"cannot pickle {← rt.repr n} object"
    else rt.call base [self] []
  let args := Val.tuple [cls, base, state]
  let slotsSet : M Bool := do
    match ← rt.getOptionalAttr self "__slots__" with
    | some v => rt.isTrue v
    | none => pure false
  let g? ← tryM (some <$> rt.getAttr self "__getstate__") fun e => do
    let w ← getW
    if excMatches w e B.AttributeError then pure none else raise e
  let dict ← match g? with
    | none =>
      if ← slotsSet then
        let n ← rt.getAttr cls "__name__"
        typeErr s!"cannot pickle {← rt.repr n} object: a class that defines __slots__ without defining __getstate__ cannot be pickled with protocol {proto}"
      tryM (rt.getAttr self "__dict__") fun e => do
        let w ← getW
        if excMatches w e B.AttributeError then pure .none else raise e
    | some g =>
      let w ← getW
      let own ← rt.getAttr (.obj (typeOf w self)) "__getstate__"
      let base' ← rt.getAttr (.obj B.object) "__getstate__"
      if own.is base' then
        if ← slotsSet then
          typeErr "a class that defines __slots__ without defining __getstate__ cannot be pickled"
      rt.call g [] []
  let f ← copyregFunc "_reconstructor"
  if ← rt.isTrue dict then pure (.tuple [f, args, dict])
  else pure (.tuple [f, args])

/-- `_common_reduce`, `Objects/typeobject.c:7764`. -/
def commonReduce (rt : Rt) (self : Val) (proto : Int) : M Val :=
  if proto ≥ 2 then reduceNewobj rt self else copyregReduceEx rt self proto

/-- `object___reduce_ex___impl`, `Objects/typeobject.c:7804`: `__reduce__` is called only if the
type overrides it, which is told from `object`'s by identity. -/
def objectReduceEx (rt : Rt) (self : Val) (proto : Int) : M Val := do
  match ← rt.getOptionalAttr self "__reduce__" with
  | none => commonReduce rt self proto
  | some reduce =>
    let w ← getW
    let clsreduce ← rt.getAttr (.obj (typeOf w self)) "__reduce__"
    let w ← getW
    match NameDict.get? (tdata w B.object).dict "__reduce__" with
    | some objreduce =>
      if clsreduce.is objreduce then commonReduce rt self proto else rt.call reduce [] []
    | none => gap%

/-- `merge_class_dict`, `Objects/typeobject.c:6524`: the class's `__dict__`, then each base in the
order of `__bases__`, recursively. A failed `PySequence_Size` is dropped (`:6555`). -/
def mergeClassDict (rt : Rt) (d : Addr) : Nat → Val → M Unit
  | 0, _ => raise .fuel
  | fuel + 1, aclass => do
    match ← rt.getOptionalAttr aclass "__dict__" with
    | some cd => dictMerge rt d cd
    | none => pure ()
    match ← rt.getOptionalAttr aclass "__bases__" with
    | none => pure ()
    | some bases =>
      let n ← tryM (rt.size bases) fun e =>
        match e with
        | .exc _ _ _ => pure (-1)
        | e => raise e
      for i in List.range n.toNat do
        let base ← rt.getItem bases (.int i)
        mergeClassDict rt d fuel base

/-- `PyDict_Keys` of the dict at `d`, as a list. -/
def dictKeysList (d : Addr) : M Val := do
  let w ← getW
  alloc B.list (.list ((dictEntries w d).map (·.1)))

/-- `type___dir___impl`, `Objects/typeobject.c:6587`. -/
def typeDirImpl (rt : Rt) (self : Val) : M Val := do
  let d ← allocCell (.val { cls := B.dict, body := .dict [] })
  mergeClassDict rt d iterFuel self
  dictKeysList d

/-- `object___dir___impl`, `Objects/typeobject.c`: a copy of `__dict__` if that is a dict, then the
class, whose attributes are merged in. -/
def objectDirImpl (rt : Rt) (self : Val) : M Val := do
  let d ← match ← rt.getOptionalAttr self "__dict__" with
    | some x =>
      let w ← getW
      if (dictOf w x).isSome then dictCopy rt x
      else allocCell (.val { cls := B.dict, body := .dict [] })
    | none => allocCell (.val { cls := B.dict, body := .dict [] })
  match ← rt.getOptionalAttr self "__class__" with
  | some c => mergeClassDict rt d iterFuel c
  | none => pure ()
  dictKeysList d

/-- `PyLong_AsInt`, the argument of `__reduce_ex__`. -/
def longAsInt (rt : Rt) (v : Val) : M Int := do
  let i ← pyNumberIndex rt v
  if i < -2147483648 || i > 2147483647 then
    overflowErr "Python int too large to convert to C int"
  else pure i

end PyLean.TypeObj
