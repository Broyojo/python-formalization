import PyLean.TypeObj.Slots

/-!
Descriptors and attribute access: `Objects/object.c:1310-2132`, `Objects/typeobject.c`
(`_Py_type_getattro_impl`, `type_setattro`, the `lookup_method` family, the getattr
hooks, `super`), `Objects/descrobject.c` (the `tp_descr_get/set` of each descriptor),
`Objects/funcobject.c` and `Objects/classobject.c` (`func_descr_get`, `method_getattro`).

Inline instance values (`Py_TPFLAGS_INLINE_VALUES`) are a representation of the managed
dict, so the model has one path, the dict. `_PyObject_GetMethod` mirrors its own branches
because it is an implementation twin of `_PyObject_GenericGetAttrWithDict`.
-/

namespace PyLean.TypeObj

/-- `%.Ns` of `PyUnicode_FromFormat`, `unicode_fromformat_write_utf8`,
`Objects/unicodeobject.c:2623-2661`: at most `n` bytes, and an incomplete UTF-8 sequence at the
cut is dropped (`pconsumed`), so the longest prefix of whole characters whose encoding fits in
`n` bytes. The same definition as `truncUtf8` in `ExcCore`. -/
def cutUtf8 : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs => if c.utf8Size ≤ n then c :: cutUtf8 (n - c.utf8Size) cs else []

/-- `%.Ns` in `PyErr_Format` of a C string: a `tp_name`, which is valid UTF-8 without NUL
(`type()` refuses both), or a short ASCII literal. -/
def trunc (n : Nat) (s : String) : String := String.ofList (cutUtf8 n s.toList)

/-- `%.NR`, `%.NS`, `%.NU` and `%.NV` in `PyErr_Format`: the precision counts code points
(`unicode_fromformat_write_str`, `Objects/unicodeobject.c:2588-2589`). -/
def truncChars (n : Nat) (s : String) : String := String.ofList (s.toList.take n)

/-- One character of `unicode_repr` for a `str` body, `Objects/unicodeobject.c`: the
escapes that matter for attribute names and messages. -/
def reprChar (quote c : Char) : String :=
  if c == quote || c == '\\' then s!"\\{c}"
  else if c == '\n' then "\\n"
  else if c == '\r' then "\\r"
  else if c == '\t' then "\\t"
  else if c.toNat < 32 || c.toNat == 127 then
    let h := Nat.toDigits 16 c.toNat
    let h := if h.length < 2 then '0' :: h else h
    "\\x" ++ String.ofList h
  else c.toString

/-- `repr(s)` of a `str`: single quotes unless the text has `'` and no `"`. -/
def reprStr (s : String) : String :=
  let quote := if s.contains '\'' && !s.contains '"' then '"' else '\''
  quote.toString ++ String.join (s.toList.map (reprChar quote)) ++ quote.toString

/-- `PyUnicode_Check`: the string of an exact `str` or a `str` subclass instance. -/
def strOf (w : World) : Val → Option String
  | .str s => some s
  | v =>
    match payloadOf w v with
    | some (.boxed (.str s)) => some s
    | _ => none

/-- `PyLong_Check`: the value of an `int`, a `bool`, or an `int` subclass instance. -/
def intOf (w : World) : Val → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | v =>
    match payloadOf w v with
    | some (.boxed (.int i)) => some i
    | _ => none

/-- `PyTuple_Check`: the items of a tuple or a tuple subclass instance. -/
def tupleOf (w : World) : Val → Option (List Val)
  | .tuple xs => some xs
  | v =>
    match payloadOf w v with
    | some (.boxed (.tuple xs)) => some xs
    | _ => none

/-- `PyDict_Check`: the entries of a dict or dict subclass instance. -/
def dictOf (w : World) : Val → Option (List (Val × Val))
  | v =>
    match payloadOf w v with
    | some (.dict es) => some es
    | _ => none

/-- `PyAnyDict_Check`: the entries of a `dict` or `frozendict`, or of a subclass. -/
def anyDictOf (w : World) (v : Val) : Option (List (Val × Val)) :=
  match payloadOf w v with
  | some (.dict es) | some (.frozen es) => some es
  | _ => none

/-- `PyList_Check`: the items of a list or list subclass instance. -/
def listOf (w : World) : Val → Option (List Val)
  | v =>
    match payloadOf w v with
    | some (.list xs) => some xs
    | _ => none

/-- `PyDict_GetItem` for keys compared by identity (see `Payload.dict`). -/
def dictLookup (es : List (Val × Val)) (k : Val) : Option Val :=
  match es with
  | [] => none
  | (a, v) :: rest => if a.is k then some v else dictLookup rest k

def dictSetEntry (es : List (Val × Val)) (k v : Val) : List (Val × Val) :=
  match es with
  | [] => [(k, v)]
  | (a, x) :: rest => if a.is k then (a, v) :: rest else (a, x) :: dictSetEntry rest k v

def dictDelEntry (es : List (Val × Val)) (k : Val) : List (Val × Val) :=
  match es with
  | [] => []
  | (a, x) :: rest => if a.is k then rest else (a, x) :: dictDelEntry rest k

/-- Is the instance `v` allowed a `__dict__`: `_PyObject_GetDictPtr(v) != NULL`? -/
def hasDictPtr (w : World) (v : Val) : Bool := (tdata w (typeOf w v)).dictoffset != 0

/-- The address of the dict of `v` once it exists. -/
def instDictAddr (w : World) : Val → Option Addr
  | .obj a =>
    match w.get a with
    | .val o => o.dict
    | .ty _ _ => none
  | _ => none

/-- `ensure_managed_dict`/`ensure_nonmanaged_dict`: create the instance dict on demand. -/
def ensureDict (v : Val) : M Addr := do
  let w ← getW
  match instDictAddr w v with
  | some d => pure d
  | none =>
    let dv ← alloc B.dict (.dict [])
    match dv, v with
    | .obj d, .obj a =>
      modObj a (fun o => { o with dict := some d })
      pure d
    | _, _ => gap%

/-- Materialise a pending exception as an object (what `PyErr_GetRaisedException` does). -/
def excObject (e : PyErr) : M Val :=
  match e with
  | .exc _ _ (some v) => pure v
  | .exc cls msg none => alloc cls (.exc { args := [.str msg] })
  | e => raise e

/-- The members of an exception object. -/
def excMembers (w : World) (v : Val) : NameDict :=
  match payloadOf w v with
  | some (.exc e) => e.members
  | _ => []

/-- The augmentation in `_PyObject_SetAttributeErrorContext`, `Objects/object.c:1296-1304`:
set `.name` and `.obj` unless already set. -/
def attachContext (x v : Val) (n : Name) : M Unit := do
  let w ← getW
  let ms := excMembers w x
  if NameDict.contains ms "name" || NameDict.contains ms "obj" then pure ()
  else
    match x with
    | .obj a =>
      modObj a fun o =>
        match o.body with
        | .exc d =>
          let ms := NameDict.set (NameDict.set d.members "name" (.str n)) "obj" v
          { o with body := .exc { d with members := ms } }
        | _ => o
    | _ => pure ()

/-- `_PyObject_SetAttributeErrorContext`, `Objects/object.c:1283`, then re-raise. -/
def setAttributeErrorContext {α : Type} (v : Val) (n : Name) (e : PyErr) : M α := do
  let w ← getW
  if excMatches w e B.AttributeError then
    let x ← excObject e
    attachContext x v n
    raise (match e with
      | .exc c m _ => .exc c m (some x)
      | e => e)
  else raise e

/-! ## `tp_descr_get` -/

/-- `PyMethod_New`, `Objects/classobject.c:65`. -/
def pyMethodNew (func self : Val) : M Val := alloc B.method (.bound func self)

/-- `func_descr_get`, `Objects/funcobject.c:1267`. -/
def funcDescrGet (f : Val) (obj : Option Val) : M Val :=
  match obj with
  | none | some .none => pure f
  | some o => pyMethodNew f o

/-- `cm_descr_get`, `Objects/funcobject.c:1535`. `cm_new` sets `cm_callable` to `None`, so the
payload is always there. -/
def cmDescrGet (cm : Val) (obj : Option Val) (ty : Option Val) : M Val := do
  let w ← getW
  match payloadOf w cm with
  | some (.classmethod f) =>
    let t := match ty, obj with
      | some t, _ => t
      | none, some o => .obj (typeOf w o)
      | none, none => .none
    pyMethodNew f t
  | _ => gap%

/-- `sm_descr_get`, `Objects/funcobject.c:1799`. -/
def smDescrGet (sm : Val) : M Val := do
  let w ← getW
  match payloadOf w sm with
  | some (.staticmethod f) => pure f
  | _ => gap%

/-- `PyType_GetQualName(type)`: `type_qualname`, `Objects/typeobject.c:1570`. -/
def typeQualname (w : World) (t : Addr) : String :=
  let d := tdata w t
  if d.heap then d.qualname
  else ((d.name.splitOn ".").getLast?).getD d.name

/-- `_PyType_GetFullyQualifiedName(type, '.')`, `Objects/typeobject.c:1694`: `%T`. -/
def typeFQN (w : World) (t : Addr) : String :=
  let d := tdata w t
  if !d.heap then d.name else
  match NameDict.get? d.dict "__module__" with
  | some (.str m) => if m == "builtins" || m == "__main__" then d.qualname else m ++ "." ++ d.qualname
  | _ => d.qualname

/-- `%T` of `PyUnicode_FromFormat`: the fully qualified name of the type of `v`. -/
def objFQN (w : World) (v : Val) : String := typeFQN w (typeOf w v)

/-- `descr_check`, `Objects/descrobject.c:80`, also `descr_setcheck` at `:217`. -/
def descrCheck (owner : Addr) (name : Name) (obj : Val) : M Unit := do
  let w ← getW
  unless isSubtype w (typeOf w obj) owner do
    typeErr s!"descriptor '{name}' for '{trunc 100 (tpName w owner)}' objects doesn't apply to a '{trunc 100 (typeName w obj)}' object"

/-- `method_get`, `Objects/descrobject.c:138`. -/
def methodGet (d : Val) (owner : Addr) (name : Name) (b : Builtin) (obj : Option Val) :
    M Val :=
  match obj with
  | none => pure d
  | some o => do
    descrCheck owner name o
    alloc B.builtinFn (.builtin b (some o))

/-- `classmethod_get`, `Objects/descrobject.c:95`. -/
def classmethodGet (owner : Addr) (name : Name) (b : Builtin) (obj ty : Option Val) :
    M Val := do
  let w ← getW
  let t ← match ty with
    | some t => pure t
    | none =>
      match obj with
      | some o => pure (Val.obj (typeOf w o))
      | none =>
        typeErr s!"descriptor '{name}' for type '{trunc 100 (tpName w owner)}' needs either an object or a type"
  match asType w t with
  | none =>
    typeErr s!"descriptor '{name}' for type '{trunc 100 (tpName w owner)}' needs a type, not a '{trunc 100 (typeName w t)}' as arg 2"
  | some ta =>
    unless isSubtype w ta owner do
      typeErr s!"descriptor '{name}' requires a subtype of '{trunc 100 (tpName w owner)}' but received '{trunc 100 (tpName w ta)}'"
    alloc B.builtinFn (.builtin b (some t))

/-- `wrapperdescr_get`, `Objects/descrobject.c:204`; `PyWrapper_New` at `:1512`. -/
def wrapperdescrGet (d : Val) (owner : Addr) (name : Name) (obj : Option Val) : M Val :=
  match obj with
  | none => pure d
  | some o => do
    descrCheck owner name o
    alloc B.methodWrapper (.methodWrapper d o)

/-- The value of a `__slots__` member. -/
def slotValue (w : World) (obj : Val) (n : Name) : Option Val :=
  match obj with
  | .obj a =>
    match w.get a with
    | .val o => NameDict.get? o.slotVals n
    | .ty _ _ => none
  | _ => none

/-- `member_get`, `Objects/descrobject.c:163`, with `PyMember_GetOne` for
`Py_T_OBJECT_EX` (`Python/structmember.c:117`). Members of static types go through the
`getsetGet` hook. -/
def memberGet (rt : Rt) (d : Val) (owner : Addr) (name : Name) (obj : Option Val) : M Val :=
  match obj with
  | none => pure d
  | some o => do
    descrCheck owner name o
    let w ← getW
    if (tdata w owner).heap then
      match slotValue w o name with
      | some v => pure v
      | none => attrErr s!"'{typeFQN w (typeOf w o)}' object has no attribute '{name}'"
    else rt.getsetGet owner name o

/-- `getset_get`, `Objects/descrobject.c:184`. -/
def getsetDescrGet (rt : Rt) (d : Val) (owner : Addr) (name : Name) (obj : Option Val) :
    M Val :=
  match obj with
  | none => pure d
  | some o => do
    descrCheck owner name o
    rt.getsetGet owner name o

/-- `property_name`, `Objects/descrobject.c:1671`. -/
def propertyName (rt : Rt) (fget : Val) (name : Option Val) : M (Option Val) :=
  match name with
  | some n => pure (some n)
  | none =>
    match fget with
    | .none => pure none
    | _ => rt.getOptionalAttr fget "__name__"

/-- The fields of a property object: `(fget, fset, fdel, doc, prop_name, getter_doc)`.
`None` stands for a NULL function pointer, as `property_init_impl` stores NULL for
`None`. -/
def propertyFields (w : World) (p : Val) : Option (Val × Val × Val × Val × Option Val × Bool) :=
  match payloadOf w p with
  | some (.property g s d doc n gd) => some (g, s, d, doc, n, gd)
  | _ => none

/-- `property_descr_get`, `Objects/descrobject.c:1685`. -/
def propertyDescrGet (rt : Rt) (self : Val) (obj : Option Val) : M Val := do
  match obj with
  | none | some .none => pure self
  | some o =>
    let w ← getW
    match propertyFields w self with
    | none => gap%
    | some (fget, _, _, _, pname, _) =>
      match fget with
      | .none =>
        let propname ← propertyName rt fget pname
        let w ← getW
        let qual := typeQualname w (typeOf w o)
        match propname with
        | some pn =>
          let r ← rt.repr pn
          attrErr s!"property {r} of {reprStr qual} object has no getter"
        | none => attrErr s!"property of {reprStr qual} object has no getter"
      | f => rt.call f [o] []

/-- `property_descr_set`, `Objects/descrobject.c:1721`. -/
def propertyDescrSet (rt : Rt) (self obj : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match propertyFields w self with
  | none => gap%
  | some (fget, fset, fdel, _, pname, _) =>
    let func := match value with
      | none => fdel
      | some _ => fset
    match func with
    | .none =>
      let propname ← propertyName rt fget pname
      let w ← getW
      let qual := typeQualname w (typeOf w obj)
      let what := match value with
        | none => "deleter"
        | some _ => "setter"
      match propname with
      | some pn =>
        let r ← rt.repr pn
        attrErr s!"property {r} of {reprStr qual} object has no {what}"
      | none => attrErr s!"property of {reprStr qual} object has no {what}"
    | f =>
      match value with
      | none => do let _ ← rt.call f [obj] []
      | some v => do let _ ← rt.call f [obj, v] []

/-- `supercheck`, `Objects/typeobject.c:12808`. -/
def supercheck (rt : Rt) (ty : Addr) (obj : Val) : M Addr := do
  let w ← getW
  match asType w obj with
  | some oa =>
    if isSubtype w oa ty then return oa
  | none => pure ()
  if isSubtype w (typeOf w obj) ty then
    return typeOf w obj
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

/-- Does `super_descr_get` reach `supercheck(su->type, obj)`, `Objects/typeobject.c:12902`, with
`su->type == NULL`? Nothing tests for it. `tp_new` leaves the field NULL (`super_init` fills it),
`PyType_IsSubtype` then just answers no, and the error at :12868 reads `type->tp_name`. -/
def superBindsNullType (w : World) (self o : Val) : Bool :=
  match payloadOf w self, o with
  | _, .none => false
  | some (.super none none _), _ => typeOf w self == B.super
  | _, _ => false

/-- `super_descr_get`, `Objects/typeobject.c:12886`. The `none` branch is `superBindsNullType`:
CPython goes on into a NULL dereference, which is no Python outcome, so the model stops. -/
def superDescrGet (rt : Rt) (self : Val) (obj : Option Val) : M Val := do
  let w ← getW
  match payloadOf w self with
  | some (.super ty suObj _) =>
    match obj, suObj with
    | none, _ | some .none, _ | _, some _ => pure self
    | some o, none =>
      if typeOf w self != B.super then
        -- `PyObject_CallFunctionObjArgs(Py_TYPE(su), su->type, obj, NULL)`: a NULL `su->type`
        -- ends the argument list there.
        rt.call (.obj (typeOf w self)) (match ty with
          | some t => [.obj t, o]
          | none => []) []
      else
        match ty with
        | none => gap%
        | some t =>
          let objType ← supercheck rt t o
          alloc B.super (.super (some t) (some o) (some objType))
  | _ => gap%

/-- `slot_tp_descr_get`, `Objects/typeobject.c:11231`. -/
def slotTpDescrGet (rt : Rt) (self : Val) (obj ty : Option Val) : M Val := do
  let w ← getW
  match findInMro w (typeOf w self) "__get__" with
  | none => pure self
  | some get => rt.call get [self, obj.getD .none, ty.getD .none] []

/-- Call the `tp_descr_get` function `f` on descriptor `d`. -/
def callDescrGet (rt : Rt) (f : SlotFn) (d : Val) (obj ty : Option Val) : M Val := do
  match f with
  | .generic => slotTpDescrGet rt d obj ty
  | .c .function => funcDescrGet d obj
  | .c .classmethod => cmDescrGet d obj ty
  | .c .staticmethod => smDescrGet d
  | .c .property => propertyDescrGet rt d obj
  | .c .super => superDescrGet rt d obj
  | .c .method => pure d
  | .c c =>
    let w ← getW
    match c, payloadOf w d with
    | .methodDescr, some (.methodDescr o n b) => methodGet d o n b obj
    | .classmethodDescr, some (.classmethodDescr o n b) => classmethodGet o n b obj ty
    | .wrapperDescr, some (.wrapperDescr o base _) => wrapperdescrGet d o base.name obj
    | .memberDescr, some (.memberDescr o n _) => memberGet rt d o n obj
    | .getsetDescr, some (.getsetDescr o n _) => getsetDescrGet rt d o n obj
    | _, _ => gap%
  | _ => gap%

/-- `f(res, self, Py_TYPE(self))` when `res` has `tp_descr_get`, else `res`. -/
def bindDescr (rt : Rt) (res self : Val) : M Val := do
  let w ← getW
  match slotOf w (typeOf w res) .tp_descr_get with
  | some f => callDescrGet rt f res (some self) (some (.obj (typeOf w self)))
  | none => pure res

/-- `_PyObject_LookupSpecial`, `Objects/typeobject.c:2990`. -/
def lookupSpecial (rt : Rt) (self : Val) (attr : Name) : M (Option Val) := do
  let w ← getW
  match findInMro w (typeOf w self) attr with
  | none => pure none
  | some res => some <$> bindDescr rt res self

/-- The three results of `lookup_method_ex`: `-1` (missing), `1` (unbound method
descriptor), `0` (already bound). -/
inductive Looked where
  | missing
  | unbound (f : Val)
  | bound (f : Val)
  deriving Repr, Inhabited

/-- `lookup_method_ex`, `Objects/typeobject.c:3038`. -/
def lookupMethodEx (rt : Rt) (self : Val) (attr : Name) (raiseAE : Bool) : M Looked := do
  let w ← getW
  match findInMro w (typeOf w self) attr with
  | none => if raiseAE then attrErr attr else pure .missing
  | some value =>
    if (tdata w (typeOf w value)).methodDescriptor then
      pure (.unbound value)
    else
      match slotOf w (typeOf w value) .tp_descr_get with
      | some f =>
        let get : M Looked := do
          let v ← callDescrGet rt f value (some self) (some (.obj (typeOf w self)))
          pure (.bound v)
        if raiseAE then get else catchMatch B.AttributeError get (pure .missing)
      | none => pure (.bound value)

/-- `vectorcall_unbound`, `Objects/typeobject.c:3086`: `args` starts with `self`. -/
def callUnbound (rt : Rt) (l : Looked) (args : List Val) : M Val :=
  match l with
  | .unbound f => rt.call f args []
  | .bound f => rt.call f (args.drop 1) []
  | .missing => gap%

/-- `vectorcall_method`, `Objects/typeobject.c:3156`. -/
def vectorcallMethod (rt : Rt) (name : Name) (args : List Val) : M Val := do
  let l ← lookupMethodEx rt (args.headD .none) name true
  callUnbound rt l args

/-- `vectorcall_maybe`, `Objects/typeobject.c:3177`: `NotImplemented` if missing. -/
def vectorcallMaybe (rt : Rt) (name : Name) (args : List Val) : M Val := do
  let l ← lookupMethodEx rt (args.headD .none) name false
  match l with
  | .missing => pure .notImpl
  | l => callUnbound rt l args

/-- `call_method`, `Objects/typeobject.c:3130`. -/
def callMethod (rt : Rt) (self : Val) (attr : Name) (args : List Val) (kw : Kw) : M Val := do
  let l ← lookupMethodEx rt self attr true
  match l with
  | .unbound f => rt.call f (self :: args) kw
  | .bound f => rt.call f args kw
  | .missing => gap%

/-- The result of `maybe_call_special_*`: the attribute was `None` when
`attr_is_none != NULL`, or the call result, or missing. -/
inductive Maybe where
  | isNone
  | missing
  | res (v : Val)
  deriving Repr, Inhabited

/-- `maybe_call_special_no_args`/`_one_arg`, `Objects/typeobject.c:3204-3243`.
`checkNone` is `attr_is_none != NULL`. -/
def maybeCallSpecial (rt : Rt) (self : Val) (attr : Name) (args : List Val)
    (checkNone : Bool) : M Maybe := do
  let l ← lookupMethodEx rt self attr false
  let isNone : Bool := match l with
    | .unbound f | .bound f => f.is .none
    | .missing => false
  match l with
  | .missing => pure .missing
  | l =>
    if isNone && checkNone then pure .isNone
    else .res <$> callUnbound rt l (self :: args)

/-! ## `_PyType_LookupRef`-based attribute access -/

/-- `f(descr, obj, type)` with the `suppress` handling of `Objects/object.c:1927-1931`. -/
def runDescrGet (rt : Rt) (fn : SlotFn) (d obj : Val) (tv : Val) (suppress : Bool) :
    M (Option Val) :=
  if suppress then
    catchMatch B.AttributeError (some <$> callDescrGet rt fn d (some obj) (some tv)) (pure none)
  else some <$> callDescrGet rt fn d (some obj) (some tv)

/-- The lookup of `n` in the instance dict of `obj`. -/
def instDictGet (w : World) (obj : Val) (n : Name) : Option Val :=
  if hasDictPtr w obj then
    match instDictAddr w obj with
    | some da =>
      match dictOf w (.obj da) with
      | some es => dictLookup es (.str n)
      | none => none
    | none => none
  else none

/-- `Objects/object.c:1935-2003`: instance dict, then non-data descriptor, then class
attribute, then `AttributeError`. -/
def genericGetAttrTail (rt : Rt) (obj : Val) (n : Name) (descr : Option Val)
    (f : Option SlotFn) (suppress : Bool) : M (Option Val) := do
  let w ← getW
  let tp := typeOf w obj
  match instDictGet w obj n with
  | some v => pure (some v)
  | none =>
    match f, descr with
    | some fn, some d => runDescrGet rt fn d obj (.obj tp) suppress
    | _, some d => pure (some d)
    | _, none =>
      if suppress then pure none
      else
        tryM (raiseC B.AttributeError s!"'{trunc 100 (tpName w tp)}' object has no attribute '{n}'")
          (setAttributeErrorContext obj n)

/-- `_PyObject_GenericGetAttrWithDict`, `Objects/object.c:1888`, with `dict == NULL`.
`suppress` returns `none` for a missing attribute instead of raising. -/
def genericGetAttrSup (rt : Rt) (obj : Val) (n : Name) (suppress : Bool) : M (Option Val) := do
  let w ← getW
  let tp := typeOf w obj
  let descr := findInMro w tp n
  let f := match descr with
    | some d => slotOf w (typeOf w d) .tp_descr_get
    | none => none
  match descr, f with
  | some d, some fn =>
    if isDataDescr w d then runDescrGet rt fn d obj (.obj tp) suppress
    else genericGetAttrTail rt obj n descr f suppress
  | _, _ => genericGetAttrTail rt obj n descr f suppress

/-- `PyObject_GenericGetAttr`, `Objects/object.c:2011`. -/
def genericGetAttr (rt : Rt) (obj : Val) (n : Name) : M Val := do
  match ← genericGetAttrSup rt obj n false with
  | some v => pure v
  | none => gap%

/-- `_Py_type_getattro_stackref`, `Objects/typeobject.c:6620`. `suppress` is
`suppress_missing_attribute != NULL`. -/
def typeGetattroImpl (rt : Rt) (ty : Val) (n : Name) (suppress : Bool) : M (Option Val) := do
  let w ← getW
  let tyA := match ty with
    | .obj a => a
    | _ => 0
  let metatype := typeOf w ty
  let mv : Val := .obj metatype
  let metaAttribute := findInMro w metatype n
  let metaGet := match metaAttribute with
    | some m => slotOf w (typeOf w m) .tp_descr_get
    | none => none
  match metaAttribute, metaGet with
  | some m, some g =>
    if isDataDescr w m then return some (← callDescrGet rt g m (some ty) (some mv))
  | _, _ => pure ()
  match findInMro w tyA n with
  | some a =>
    match slotOf w (typeOf w a) .tp_descr_get with
    | some lg => return some (← callDescrGet rt lg a none (some ty))
    | none => return some a
  | none => pure ()
  match metaAttribute, metaGet with
  | some m, some g => return some (← callDescrGet rt g m (some ty) (some mv))
  | some m, none => return some m
  | none, _ => pure ()
  if suppress then pure none
  else attrErr s!"type object '{trunc 100 (tpName w tyA)}' has no attribute '{n}'"

/-- `_Py_type_getattro`, `Objects/typeobject.c:6603`. -/
def typeGetattro (rt : Rt) (ty : Val) (n : Name) : M Val := do
  match ← typeGetattroImpl rt ty n false with
  | some v => pure v
  | none => gap%

/-- `_PySuper_LookupDescr`, `Objects/typeobject.c:12693`: search the MRO of `objType`
strictly after `suType`. -/
def superLookupDescr (w : World) (suType objType : Addr) (n : Name) : Option Val :=
  match (tdata w objType).mro with
  | none => none
  | some mro =>
    let start := match mro.dropLast.findIdx? (· == suType) with
      | some i => i + 1
      | none => mro.length
    findInMroList w (mro.drop start) n

/-- The `obj` argument `do_super_lookup` passes to `__get__`: NULL for a class-bound `super`
(`su_obj == su_obj_type`), else `su_obj`, `Objects/typeobject.c:12761-12763`. -/
def superBindObj (suObj : Option Val) (ot : Addr) : Option Val :=
  match suObj with
  | some so => if so.is (.obj ot) then none else some so
  | none => none

/-- `do_super_lookup`, `Objects/typeobject.c:12742`, without the method shortcut. -/
def doSuperLookup (rt : Rt) (self : Val) (suType : Addr) (suObj : Option Val)
    (suObjType : Option Addr) (n : Name) : M Val := do
  let w ← getW
  let skip : M Val := genericGetAttr rt self n
  match suObjType with
  | none => skip
  | some ot =>
    match superLookupDescr w suType ot n with
    | none => skip
    | some res =>
      match slotOf w (typeOf w res) .tp_descr_get with
      | none => pure res
      | some f => callDescrGet rt f res (superBindObj suObj ot) (some (.obj ot))

/-- `super_getattro`, `Objects/typeobject.c:12793`. -/
def superGetattro (rt : Rt) (self : Val) (n : Name) : M Val := do
  if n == "__class__" then
    genericGetAttr rt self n
  else
    let w ← getW
    match payloadOf w self with
    | some (.super (some ty) o ot) => doSuperLookup rt self ty o ot n
    | some (.super none _ _) => genericGetAttr rt self n
    | _ => gap%

/-- `method_getattro`, `Objects/classobject.c:155`. -/
def methodGetattro (rt : Rt) (obj : Val) (n : Name) : M Val := do
  let w ← getW
  match findInMro w (typeOf w obj) n with
  | some descr => bindDescr rt descr obj
  | none =>
    match payloadOf w obj with
    | some (.bound f _) => rt.getAttr f n
    | _ => gap%

/-- `call_attribute`, `Objects/typeobject.c:11066`. -/
def callAttribute (rt : Rt) (self attr : Val) (n : Name) : M Val := do
  let w ← getW
  if (tdata w (typeOf w attr)).methodDescriptor then
    rt.call attr [self, .str n] []
  else
    match slotOf w (typeOf w attr) .tp_descr_get with
    | some f =>
      let b ← callDescrGet rt f attr (some self) (some (.obj (typeOf w self)))
      rt.call b [.str n] []
    | none => rt.call attr [.str n] []

/-- `_Py_slot_tp_getattro`, `Objects/typeobject.c:11059`. -/
def slotTpGetattro (rt : Rt) (self : Val) (n : Name) : M Val :=
  vectorcallMethod rt "__getattribute__" [self, .str n]

/-- `getattribute == NULL`, or the `wrapper_descriptor` of `object.__getattribute__`
(`d_wrapped == PyObject_GenericGetAttr`), `Objects/typeobject.c:11116-11119`. -/
def isGenericGetattribute (w : World) (ga : Option Val) : Bool :=
  match ga with
  | none => true
  | some ga =>
    typeOf w ga == B.wrapperDescr &&
      (match payloadOf w ga with
       | some (.wrapperDescr _ _ (.c .object)) => true
       | _ => false)

/-- `_Py_slot_tp_getattr_hook`, `Objects/typeobject.c:11091`. -/
def slotTpGetattrHook (rt : Rt) (self : Val) (n : Name) : M Val := do
  let w ← getW
  let tp := typeOf w self
  match findInMro w tp "__getattr__" with
  | none => slotTpGetattro rt self n
  | some getattr =>
    let getattribute := findInMro w tp "__getattribute__"
    if isGenericGetattribute w getattribute then
      match ← genericGetAttrSup rt self n true with
      | some r => pure r
      | none => callAttribute rt self getattr n
    else
      match getattribute with
      | some ga =>
        catchMatch B.AttributeError (callAttribute rt self ga n) (callAttribute rt self getattr n)
      | none => gap%

/-- Call the `tp_getattro` function `f`. -/
def callGetattro (rt : Rt) (f : SlotFn) (v : Val) (n : Name) : M Val :=
  match f with
  | .generic => slotTpGetattrHook rt v n
  | .c .object => genericGetAttr rt v n
  | .c .type => typeGetattro rt v n
  | .c .super => superGetattro rt v n
  | .c .method => methodGetattro rt v n
  | _ => gap%

/-- `PyObject_GetAttr`, `Objects/object.c:1311`. Name type checks are made by callers:
`n` is a `str` here. -/
def pyGetAttr (rt : Rt) (v : Val) (n : Name) : M Val := do
  let w ← getW
  let tp := typeOf w v
  let run : M Val :=
    match slotOf w tp .tp_getattro with
    | some f => callGetattro rt f v n
    | none => attrErr s!"'{trunc 100 (tpName w tp)}' object has no attribute '{n}'"
  tryM run (setAttributeErrorContext v n)

/-- `PyObject_GetOptionalAttr`, `Objects/object.c:1393`. -/
def pyGetOptionalAttr (rt : Rt) (v : Val) (n : Name) : M (Option Val) := do
  let w ← getW
  let tp := typeOf w v
  match slotOf w tp .tp_getattro with
  | some (.c .object) => genericGetAttrSup rt v n true
  | some (.c .type) =>
    catchMatch B.AttributeError (typeGetattroImpl rt v n true) (pure none)
  | some f => catchMatch B.AttributeError (some <$> callGetattro rt f v n) (pure none)
  | none => pure none

/-- `_PyObject_GetMethod`, `Objects/object.c:1657`. Returns `(callable, found_method)`:
with `found_method`, the result is an unbound method descriptor and `obj` goes in as
`self`. The difference from `_PyObject_GenericGetAttrWithDict` is that a method
descriptor is not bound. -/
def pyGetMethod (rt : Rt) (obj : Val) (n : Name) : M (Val × Bool) := do
  let w ← getW
  let tp := typeOf w obj
  if slotOf w tp .tp_getattro != some (.c .object) then
    return (← rt.getAttr obj n, false)
  let descr := findInMro w tp n
  let tv : Val := .obj tp
  let methFound := match descr with
    | some d => (tdata w (typeOf w d)).methodDescriptor
    | none => false
  let f : Option SlotFn := match descr with
    | some d => if methFound then none else slotOf w (typeOf w d) .tp_descr_get
    | none => none
  match descr, f with
  | some d, some fn =>
    if isDataDescr w d then
      return (← callDescrGet rt fn d (some obj) (some tv), false)
  | _, _ => pure ()
  match instDictGet w obj n with
  | some v => return (v, false)
  | none => pure ()
  if methFound then
    return ((descr.getD .none), true)
  match f, descr with
  | some fn, some d => return (← callDescrGet rt fn d (some obj) (some tv), false)
  | _, some d => return (d, false)
  | _, none =>
    tryM (raiseC B.AttributeError s!"'{trunc 100 (tpName w tp)}' object has no attribute '{n}'")
      (setAttributeErrorContext obj n)

/-! ## `tp_setattro` -/

/-- `slot_tp_descr_set`, `Objects/typeobject.c:11259`. -/
def slotTpDescrSet (rt : Rt) (self target : Val) (value : Option Val) : M Unit := do
  match value with
  | none => let _ ← vectorcallMethod rt "__delete__" [self, target]
  | some v => let _ ← vectorcallMethod rt "__set__" [self, target, v]

/-- `member_set` and `PyMember_SetOne` for `Py_T_OBJECT_EX`,
`Objects/descrobject.c:233`, `Python/structmember.c:323-336`. -/
def memberSet (rt : Rt) (owner : Addr) (name : Name) (readonly : Bool) (obj : Val)
    (value : Option Val) : M Unit := do
  descrCheck owner name obj
  let w ← getW
  if readonly then
    attrErr "readonly attribute"
  if (tdata w owner).heap then
    match obj with
    | .obj a =>
      match value with
      | some v => modObj a fun o => { o with slotVals := NameDict.set o.slotVals name v }
      | none =>
        match slotValue w obj name with
        | some _ => modObj a fun o => { o with slotVals := NameDict.erase o.slotVals name }
        | none => attrErr name
    | _ => gap%
  else rt.getsetSet owner name obj value

/-- `getset_set`, `Objects/descrobject.c:243`. -/
def getsetDescrSet (rt : Rt) (owner : Addr) (name : Name) (canSet : Bool) (obj : Val)
    (value : Option Val) : M Unit := do
  descrCheck owner name obj
  let w ← getW
  if canSet then rt.getsetSet owner name obj value
  else attrErr s!"attribute '{name}' of '{trunc 100 (tpName w owner)}' objects is not writable"

/-- Call the `tp_descr_set` function `f` on descriptor `d`. -/
def callDescrSet (rt : Rt) (f : SlotFn) (d obj : Val) (value : Option Val) : M Unit := do
  match f with
  | .generic => slotTpDescrSet rt d obj value
  | .c .property => propertyDescrSet rt d obj value
  | .c c =>
    let w ← getW
    match c, payloadOf w d with
    | .memberDescr, some (.memberDescr o n ro) => memberSet rt o n ro obj value
    | .getsetDescr, some (.getsetDescr o n cs) => getsetDescrSet rt o n cs obj value
    | _, _ => gap%
  | _ => gap%

/-- `_PyObject_GenericSetAttrWithDict`, `Objects/object.c:2017`, with `dict == NULL`. -/
def genericSetAttr (rt : Rt) (obj : Val) (n : Name) (value : Option Val) : M Unit := do
  let w ← getW
  let tp := typeOf w obj
  let descr := findInMro w tp n
  let ds := match descr with
    | some d => slotOf w (typeOf w d) .tp_descr_set
    | none => none
  match descr, ds with
  | some d, some f => callDescrSet rt f d obj value
  | _, _ =>
    let noAttr := s!"'{trunc 100 (tpName w tp)}' object has no attribute '{n}'"
    if hasDictPtr w obj then
      match value with
      | some v =>
        let da ← ensureDict obj
        modObj da fun o =>
          match o.body with
          | .dict es => { o with body := .dict (dictSetEntry es (.str n) v) }
          | b => { o with body := b }
      | none =>
        let found : Bool := match instDictAddr w obj with
          | some da =>
            match dictOf w (.obj da) with
            | some es => (dictLookup es (.str n)).isSome
            | none => false
          | none => false
        if found then
          let da ← ensureDict obj
          modObj da fun o =>
            match o.body with
            | .dict es => { o with body := .dict (dictDelEntry es (.str n)) }
            | b => { o with body := b }
        else
          -- `_PyObjectDict_SetItem` creates a `tp_dictoffset > 0` dict before deleting.
          if (tdata w tp).dictoffset > 0 then
            let _ ← ensureDict obj
          tryM (raiseC B.AttributeError noAttr) (setAttributeErrorContext obj n)
    else
      match descr with
      | none =>
        if slotOf w tp .tp_setattro == some (.c .object) then
          tryM (raiseC B.AttributeError
            s!"'{trunc 100 (tpName w tp)}' object has no attribute '{n}' and no __dict__ for setting new attributes")
            (setAttributeErrorContext obj n)
        else
          tryM (raiseC B.AttributeError noAttr) (setAttributeErrorContext obj n)
      | some _ =>
        attrErr s!"'{trunc 100 (tpName w tp)}' object attribute '{n}' is read-only"

/-- `type_update_dict`, `Objects/typeobject.c:6743`. -/
def typeUpdateDict (t : Addr) (n : Name) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | some v =>
    modType t fun d => { d with dict := NameDict.set d.dict n v }
  | none =>
    if NameDict.contains (tdata w t).dict n then
      modType t fun d => { d with dict := NameDict.erase d.dict n }
    else
      tryM (attrErr s!"type object '{trunc 50 (tpName w t)}' has no attribute '{n}'")
        (setAttributeErrorContext (.obj t) n)
  if isDunderName n then
    modW fun w => updateSlot w t n

/-- `type_setattro`, `Objects/typeobject.c:6804`. -/
def typeSetattro (rt : Rt) (ty : Val) (n : Name) (value : Option Val) : M Unit := do
  let w ← getW
  let t := match ty with
    | .obj a => a
    | _ => 0
  if (tdata w t).immutable then
    typeErr s!"cannot set {reprStr n} attribute of immutable type '{tpName w t}'"
  let metatype := typeOf w ty
  match findInMro w metatype n with
  | some descr =>
    match slotOf w (typeOf w descr) .tp_descr_set with
    | some f => callDescrSet rt f descr ty value
    | none => typeUpdateDict t n value
  | none => typeUpdateDict t n value

/-- `slot_tp_setattro`, `Objects/typeobject.c:11142`. -/
def slotTpSetattro (rt : Rt) (self : Val) (n : Name) (value : Option Val) : M Unit := do
  match value with
  | none => let _ ← vectorcallMethod rt "__delattr__" [self, .str n]
  | some v => let _ ← vectorcallMethod rt "__setattr__" [self, .str n, v]

/-- Call the `tp_setattro` function `f`. -/
def callSetattro (rt : Rt) (f : SlotFn) (v : Val) (n : Name) (value : Option Val) : M Unit :=
  match f with
  | .generic => slotTpSetattro rt v n value
  | .c .object => genericSetAttr rt v n value
  | .c .type => typeSetattro rt v n value
  | _ => gap%

/-- The message at `Objects/object.c:1558`. -/
def roAttrMsg (tp what n : String) : String :=
  s!"'{trunc 100 tp}' object has only read-only attributes ({what} .{n})"

/-- `PyObject_SetAttr`, `Objects/object.c:1509`. -/
def pySetAttr (rt : Rt) (v : Val) (n : Name) (value : Option Val) : M Unit := do
  let w ← getW
  let tp := typeOf w v
  match slotOf w tp .tp_setattro with
  | some f => callSetattro rt f v n value
  | none =>
    let what := match value with
      | none => "del"
      | some _ => "assign to"
    if (slotOf w tp .tp_getattro).isNone then
      typeErr s!"'{trunc 100 (tpName w tp)}' object has no attributes ({what} .{n})"
    else
      typeErr (roAttrMsg (tpName w tp) what n)

end PyLean.TypeObj
