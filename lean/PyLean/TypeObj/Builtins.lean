import PyLean.TypeObj.Interp
import PyLean.TypeObj.BuiltinTable

/-!
The builtin types as heap cells, built from `BuiltinTable.lean`: what `_PyTypes_InitTypes`
and `type_ready` produce for static types. Each `tp_dict` key of the table becomes a
descriptor object; slots come from the wrapper keys, then `inherit_slots` runs over each
MRO.

Each exception row names its C family in `familyOf`; `Exceptions.lean` dispatches on it.
-/

namespace PyLean.TypeObj

/-- The C implementation family of a builtin type. -/
def familyOf (a : Addr) : CFn :=
  match a with
  | 0 => .object | 1 => .type | 2 => .int | 3 => .bool | 4 => .float | 5 => .str | 6 => .tuple
  | 7 => .list | 8 => .dict | 9 => .none | 10 => .notImpl | 11 => .ellipsis | 12 => .function
  | 13 => .method | 14 => .builtinFn | 15 => .wrapperDescr | 16 => .methodWrapper
  | 17 => .methodDescr | 18 => .classmethodDescr | 19 => .memberDescr | 20 => .getsetDescr
  | 21 => .property | 22 => .classmethod | 23 => .staticmethod | 24 => .super
  | 25 => .mappingproxy | 26 => .seqIter | 27 => .listIter | 28 => .tupleIter | 29 => .strIter
  | 30 => .cell
  | 34 => .attributeError
  | 37 => .keyError
  | 39 => .stopIteration
  | 43 => .nameError
  | 49 => .exceptionGroup
  | 53 => .memoryError
  | 57 => .osError
  | 69 => .importError
  | 80 => .syntaxError
  | 82 => .systemExit
  | 86 => .unicodeDecodeError
  | 87 => .unicodeEncodeError
  | 88 => .unicodeTranslateError
  | 100 | 101 | 102 | 103 | 104 => .unmodelled
  | 105 => .listIter
  | 106 => .dictKeys
  | 107 => .strIter
  | 109 => .frozendict
  | _ => .exception

/-- Sequence types answer `__add__` and friends with `sq_*` slots. -/
def isSeqType (a : Addr) : Bool := a == B.str || a == B.tuple || a == B.list

/-- The slots a key of `tp_dict` fills on static type `a`. -/
def slotsForKey (a : Addr) (n : Name) : List Slot :=
  if isSeqType a && n == "__add__" then [.sq_concat]
  else if isSeqType a && (n == "__mul__" || n == "__rmul__") then [.sq_repeat]
  else if isSeqType a && n == "__iadd__" then [.sq_inplace_concat]
  else if isSeqType a && n == "__imul__" then [.sq_inplace_repeat]
  else if isSeqType a && n == "__len__" then [.mp_length, .sq_length]
  else if isSeqType a && n == "__getitem__" then [.mp_subscript, .sq_item]
  else if a == B.list && (n == "__setitem__" || n == "__delitem__") then
    [.mp_ass_subscript, .sq_ass_item]
  else
    let hits := (slotdefs.filter (·.name == n)).map (·.slot)
    (hits.filter fun s => s.group != .sequence || s == .sq_contains).eraseDups

/-- `PyMethodDef` entries with a model. Everything else is `Builtin.stub`. -/
def methodOf (tn n : String) : Builtin :=
  match tn, n with
  | "object", "__init_subclass__" => .objectInitSubclass
  | "object", "__subclasshook__" => .objectSubclasshook
  | "object", "__format__" => .objectFormat
  | "object", "__dir__" => .objectDir
  | "object", "__sizeof__" => .objectSizeof
  | "object", "__getstate__" => .objectGetstate
  | "object", "__reduce__" => .objectReduce
  | "object", "__reduce_ex__" => .objectReduceEx
  | "type", "mro" => .typeMro
  | "type", "__subclasses__" => .typeSubclasses
  | "type", "__prepare__" => .typePrepare
  | "type", "__instancecheck__" => .typeInstancecheck
  | "type", "__subclasscheck__" => .typeSubclasscheck
  | "type", "__dir__" => .typeDir
  | "type", "__sizeof__" => .typeSizeof
  | "property", "getter" => .propertyGetter
  | "property", "setter" => .propertySetter
  | "property", "deleter" => .propertyDeleter
  | "property", "__set_name__" => .propertySetName
  | "list", "append" => .listAppend
  | "list", "__getitem__" | "dict", "__getitem__" => .dunderGetitem
  | "dict", "__contains__" => .dunderContains
  | "dict", "keys" => .dictKeysMethod
  | "float", "is_integer" | "float", "__trunc__" | "float", "__floor__" | "float", "__ceil__"
  | "float", "conjugate" | "float", "__getnewargs__" | "float", "hex"
  | "float", "as_integer_ratio" | "float", "__round__" | "float", "fromhex" => .floatMethod n
  | "mappingproxy", "keys" | "mappingproxy", "values" | "mappingproxy", "items"
  | "mappingproxy", "copy" | "mappingproxy", "get" | "mappingproxy", "__reversed__" =>
    .proxyCall n
  | "int", "__getnewargs__" | "str", "__getnewargs__" | "tuple", "__getnewargs__" => .getnewargs
  -- `ellipsis_reduce` and `notimplemented_reduce`, `Objects/sliceobject.c`, `Objects/object.c`.
  | "ellipsis", "__reduce__" => .reduceName "Ellipsis"
  | "NotImplementedType", "__reduce__" => .reduceName "NotImplemented"
  | "method", "__reduce__" => .reduceBound
  | "builtin_function_or_method", "__reduce__" => .reduceCFunction
  | "method-wrapper", "__reduce__" => .reduceWrapper
  | "wrapper_descriptor", "__reduce__" | "method_descriptor", "__reduce__"
  | "classmethod_descriptor", "__reduce__" | "member_descriptor", "__reduce__"
  | "getset_descriptor", "__reduce__" => .reduceDescr
  | "iterator", "__length_hint__" | "list_iterator", "__length_hint__"
  | "tuple_iterator", "__length_hint__" | "str_ascii_iterator", "__length_hint__"
  | "str_iterator", "__length_hint__"
  | "dict_keyiterator", "__length_hint__" => .iterLengthHint
  | "str", "__format__" => .strDunderFormat
  | "int", "__format__" | "float", "__format__" => .numDunderFormat
  | _, "__class_getitem__" => .classGetitem
  | "BaseException", _ | "BaseExceptionGroup", _ | "ImportError", _ | "OSError", _
  | "AttributeError", _ => .excMethod (tn ++ "." ++ n)
  | _, _ => .stub (tn ++ "." ++ n)

/-- The `__bases__` of a builtin. `ExceptionGroup` is the one multiple-inheritance
builtin here (`create_exception_group_class`, `Objects/exceptions.c:1768`). -/
def rowBases (r : BuiltinRow) : List Addr :=
  if r.addr == B.ExceptionGroup then [B.BaseExceptionGroup, B.Exception]
  else match r.base with
    | some b => [b]
    | none => []

/-- The MRO of a builtin row: the base chain, except `ExceptionGroup`. -/
def rowMro (fuel : Nat) (a : Addr) : List Addr :=
  if a == B.ExceptionGroup then
    [B.ExceptionGroup, B.BaseExceptionGroup, B.Exception, B.BaseException, B.object]
  else
    match fuel, (builtinTable.find? (·.addr == a)) with
    | fuel + 1, some r =>
      match r.base with
      | some b => a :: rowMro fuel b
      | none => [a]
    | _, _ => [a]

/-- The flags and own slots of a row. -/
def rowData (r : BuiltinRow) : TypeData :=
  let keyed := r.entries.filter fun e =>
    match e.2 with
    | .w => true
    | .m => e.1 == "__getitem__" || e.1 == "__contains__"
    | _ => false
  let own : List (Slot × SlotFn) :=
    (keyed.flatMap fun e => slotsForKey r.addr e.1).eraseDups.map (·, SlotFn.c (familyOf r.addr))
  let newSlot : List (Slot × SlotFn) :=
    if r.entries.any (·.1 == "__new__") then [(.tp_new, .c (familyOf r.addr))] else []
  { name := r.name, qualname := r.name, base := r.base, bases := rowBases r
    mro := some (rowMro 100 r.addr), slots := own ++ newSlot
    heap := r.addr == B.ExceptionGroup, baseType := r.baseType
    immutable := r.addr != B.ExceptionGroup
    methodDescriptor :=
      r.addr == B.function || r.addr == B.methodDescr || r.addr == B.wrapperDescr
    basicsize := r.basicsize, itemsize := r.itemsize
    dictoffset := r.dictoffset, weaklistoffset := r.weaklistoffset }

/-- The first slotdef named `n` whose slot is filled: the entry `add_operators` wraps. -/
def wrapperDefFor (w : World) (t : Addr) (n : Name) : Option SlotDef :=
  (slotdefs.filter (·.name == n)).find? fun p => (slotOf w t p.slot).isSome

/-- `tp_new` through the static hierarchy, `type_ready_set_new`,
`Objects/typeobject.c:9471`: a static type with base `object` and no `tp_new` cannot be
instantiated. -/
def resolveNew (w : World) (r : BuiltinRow) : Option SlotFn :=
  match slotOf w r.addr .tp_new with
  | some f => some f
  | none =>
    match r.base with
    | none => none
    | some b => if b == B.object then none else slotOf w b .tp_new

/-- Fill the `tp_dict` of one row. -/
def fillRow (r : BuiltinRow) : M Unit := do
  for (n, k) in r.entries do
    let t := r.addr
    let w ← getW
    let v : Val ← match k with
      | .w =>
        match wrapperDefFor w t n, slotOf w t (((wrapperDefFor w t n).map (·.slot)).getD .tp_repr) with
        | some p, some f => alloc B.wrapperDescr (.wrapperDescr t p f)
        | _, _ => pure .none
      | .m => alloc B.methodDescr (.methodDescr t n (methodOf r.name n))
      | .c => alloc B.classmethodDescr (.classmethodDescr t n (methodOf r.name n))
      | .new => alloc B.builtinFn (.builtin (.tpNewWrapper t) (some (.obj t)))
      | .noneV => pure .none
      | .stat =>
        let f ← alloc B.builtinFn (.builtin (methodOf r.name n) (some (.obj t)))
        alloc B.staticmethod (.staticmethod f)
      | .docStr s => pure (.str s)
      | .other => pure (.str "")
      | .g c => alloc B.getsetDescr (.getsetDescr t n c)
      | .mem ro => alloc B.memberDescr (.memberDescr t n ro)
    modType t fun d => { d with dict := NameDict.set d.dict n v }

/-- `tp_as_*` of a static type: it has one if it fills a slot of that group, or inherits
the pointer (`type_ready_inherit_as_structs`, `Objects/typeobject.c:9350`). -/
def groupFlags (w : World) (t : Addr) : TypeData → TypeData := fun d =>
  let any (g : SlotGroup) := d.slots.any (fun p => p.1.group == g)
  let up (g : SlotGroup) := ((tdata w t).mro.getD []).any fun b =>
    (tdata w b).slots.any (fun p => p.1.group == g)
  { d with
    asNumber := any .number || up .number
    asSequence := any .sequence || up .sequence
    asMapping := any .mapping || up .mapping
    asAsync := any .async || up .async
    asBuffer := any .buffer || up .buffer }

/-- All builtin types, ready. -/
def bootstrap : M Unit := do
  for r in builtinTable do
    modW fun w => { w with heap := w.heap.push (.ty B.type (rowData r)) }
  for r in builtinTable do
    let t := r.addr
    modW fun w => match w.get t with
      | .ty c d => w.setCell t (.ty c (groupFlags w t d))
      | .val _ => w
  for r in builtinTable do
    let t := r.addr
    fillRow r
    -- `__hash__ = None` on a static type goes with `tp_hash = PyObject_HashNotImplemented`, which
    -- subclasses inherit, so `type_ready_set_hash` leaves their dicts alone.
    if r.entries.any (fun e => e.1 == "__hash__" && e.2 == .noneV) then
      modType t fun d => { d with slots := setSlot d.slots .tp_hash (some .hashNotImpl) }
    modW fun w => ((tdata w t).mro.getD []).drop 1 |>.foldl (fun w b => inheritSlots w t b) w
    let w ← getW
    modType t fun d => { d with slots := setSlot d.slots .tp_new (resolveNew w r) }

/-- The names of `builtins` this model provides. -/
def builtinFunctions : List (Name × Builtin) :=
  [("isinstance", .isinstance), ("issubclass", .issubclass), ("getattr", .getattr),
   ("setattr", .setattr), ("delattr", .delattr), ("hasattr", .hasattr), ("len", .len),
   ("iter", .iter), ("next", .next), ("repr", .repr), ("hash", .hash),
   ("callable", .callable), ("dir", .dir), ("abs", .abs), ("divmod", .divmod), ("pow", .pow),
   ("format", .format), ("_hash", .hashProbe)]

/-- The initial world and the `builtins` namespace. -/
def initialState : World × NameDict :=
  let setup : M NameDict := do
    bootstrap
    let mut env : NameDict := builtinTable.filterMap fun r =>
      if r.name == "NoneType" || r.name == "ellipsis" then none else some (r.name, Val.obj r.addr)
    -- `INIT_ALIAS`, `Objects/exceptions.c@3.14.7:4545`.
    env := NameDict.set (NameDict.set env "EnvironmentError" (.obj B.OSError)) "IOError" (.obj B.OSError)
    env := NameDict.set (NameDict.set env "NotImplemented" .notImpl) "Ellipsis" .ellipsis
    for (n, b) in builtinFunctions do
      let f ← alloc B.builtinFn (.builtin b none)
      env := NameDict.set env n f
    pure env
  match setup {} with
  | .ok e w => (w, e)
  | .err _ w => (w, [])

end PyLean.TypeObj
