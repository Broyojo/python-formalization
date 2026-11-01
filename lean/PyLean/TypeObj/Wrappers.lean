import PyLean.TypeObj.Call

/-!
The thin public entry points of `Objects/object.c`, `Objects/abstract.c` and
`Objects/call.c`: string-keyed attribute and item access, `PySequence_*` and `PyMapping_*`
wrappers, and the `PyObject_Call*` family. C callers may pass NULL, which `null_error`
rejects; Python cannot, so these signatures have no NULL. A C string argument is a
`Name`. `tp_getattr` and `tp_setattr` are NULL in every type here (see `Slots.lean`).
-/

namespace PyLean.TypeObj

/-! ## Attributes by C string, `Objects/object.c:1180-1249` -/

/-- `PyObject_GetAttrString`. -/
def pyGetAttrString (rt : Rt) (v : Val) (n : Name) : M Val := rt.getAttr v n
/-- `PyObject_SetAttrString` and, with `none`, `PyObject_DelAttrString`. -/
def pySetAttrString (rt : Rt) (v : Val) (n : Name) (x : Option Val) : M Unit := rt.setAttr v n x
/-- `PyObject_DelAttr`. -/
def pyDelAttr (rt : Rt) (v : Val) (n : Name) : M Unit := rt.setAttr v n none
/-- `PyObject_GetOptionalAttrString`. -/
def pyGetOptionalAttrString (rt : Rt) (v : Val) (n : Name) : M (Option Val) :=
  rt.getOptionalAttr v n
/-- `PyObject_HasAttrWithError`, `PyObject_HasAttrStringWithError`. -/
def pyHasAttrWithError (rt : Rt) (v : Val) (n : Name) : M Bool := do
  pure (← rt.getOptionalAttr v n).isSome
/-- `PyObject_HasAttr`, `PyObject_HasAttrString`: errors are reported as unraisable and give
`False`. -/
def pyHasAttr (rt : Rt) (v : Val) (n : Name) : M Bool :=
  tryM (pyHasAttrWithError rt v n) (fun _ => pure false)

/-- `PyObject_Not`, `Objects/object.c:2167`. -/
def pyNot (rt : Rt) (v : Val) : M Bool := do
  let b ← rt.isTrue v
  pure (!b)

/-- `PyCallable_Check`, `Objects/object.c:2179`. -/
def pyCallableCheck (w : World) (x : Val) : Bool := (slotOf w (typeOf w x) .tp_call).isSome

/-- `_PyObject_IsAbstract`, `Objects/object.c:1252`, on a non-NULL object. -/
def pyIsAbstract (rt : Rt) (o : Val) : M Bool := do
  match ← rt.getOptionalAttr o "__isabstractmethod__" with
  | some x => rt.isTrue x
  | none => pure false

/-! ## `Py_Is`, `Objects/object.c:3384-3402` -/

/-- `Py_Is`. -/
def pyIs (x y : Val) : Bool := x.is y
def pyIsNone (x : Val) : Bool := x.is .none
def pyIsTrueObj (x : Val) : Bool := x.is (.bool true)
def pyIsFalseObj (x : Val) : Bool := x.is (.bool false)

/-! ## Abstract object layer -/

/-- `PyObject_Type`, `Objects/abstract.c:44`. -/
def pyObjectType (w : World) (o : Val) : Val := .obj (typeOf w o)

/-- `PyMapping_GetOptionalItem`, `Objects/abstract.c:209`. -/
def pyMappingGetOptionalItem (rt : Rt) (obj key : Val) : M (Option Val) := do
  let w ← getW
  if typeOf w obj == B.dict then
    pure (dictLookup ((dictOf w obj).getD []) key)
  else
    catchMatch B.KeyError (some <$> pyGetItem rt obj key) (pure none)

/-- `PyObject_DelItemString`, `Objects/abstract.c:304`. -/
def pyDelItemString (rt : Rt) (o : Val) (k : Name) : M Unit := pySetItem rt o (.str k) none

/-- `PyMapping_GetItemString`, `Objects/abstract.c:2308`. -/
def pyMappingGetItemString (rt : Rt) (o : Val) (k : Name) : M Val := pyGetItem rt o (.str k)

/-- `PyMapping_SetItemString`, `Objects/abstract.c:2343`. -/
def pyMappingSetItemString (rt : Rt) (o : Val) (k : Name) (v : Val) : M Unit :=
  pySetItem rt o (.str k) (some v)

/-- `PyMapping_HasKeyWithError`, `Objects/abstract.c:2371`. -/
def pyMappingHasKeyWithError (rt : Rt) (o k : Val) : M Bool := do
  pure (← pyMappingGetOptionalItem rt o k).isSome

/-- `PyMapping_HasKey`, `Objects/abstract.c:2405`: failures read as absent. -/
def pyMappingHasKey (rt : Rt) (o k : Val) : M Bool :=
  tryM (pyMappingHasKeyWithError rt o k) (fun _ => pure false)

/-- `PySequence_Concat`, `Objects/abstract.c:1721`. -/
def pySequenceConcat (rt : Rt) (s o : Val) : M Val := do
  let w ← getW
  let fail : M Val := typeErr s!"'{trunc 200 (typeName w s)}' object can't be concatenated"
  match slotIn w s .sq_concat with
  | some f => callSqConcat rt f s o
  | none =>
    if pySequenceCheck w s && pySequenceCheck w o then
      match ← binaryOp1 rt s o .nb_add with
      | .notImpl => fail
      | r => pure r
    else fail

/-- `PySequence_Repeat`, `Objects/abstract.c:1747`. -/
def pySequenceRepeat (rt : Rt) (o : Val) (count : Int) : M Val := do
  let w ← getW
  let fail : M Val := typeErr s!"'{trunc 200 (typeName w o)}' object can't be repeated"
  match slotIn w o .sq_repeat with
  | some f => callSqRepeat f o count
  | none =>
    if pySequenceCheck w o then
      match ← binaryOp1 rt o (.int count) .nb_multiply with
      | .notImpl => fail
      | r => pure r
    else fail

/-- `PySequence_InPlaceConcat`, `Objects/abstract.c:1778`. -/
def pySequenceInPlaceConcat (rt : Rt) (s o : Val) : M Val := do
  let w ← getW
  let fail : M Val := typeErr s!"'{trunc 200 (typeName w s)}' object can't be concatenated"
  match slotIn w s .sq_inplace_concat, slotIn w s .sq_concat with
  | some f, _ | none, some f => callSqConcat rt f s o
  | none, none =>
    if pySequenceCheck w s && pySequenceCheck w o then
      match ← binaryIop1 rt s o .nb_inplace_add .nb_add with
      | .notImpl => fail
      | r => pure r
    else fail

/-- `PySequence_InPlaceRepeat`, `Objects/abstract.c:1807`. -/
def pySequenceInPlaceRepeat (rt : Rt) (o : Val) (count : Int) : M Val := do
  let w ← getW
  let fail : M Val := typeErr s!"'{trunc 200 (typeName w o)}' object can't be repeated"
  match slotIn w o .sq_inplace_repeat, slotIn w o .sq_repeat with
  | some f, _ | none, some f => callSqRepeat f o count
  | none, none =>
    if pySequenceCheck w o then
      match ← binaryIop1 rt o (.int count) .nb_inplace_multiply .nb_multiply with
      | .notImpl => fail
      | r => pure r
    else fail

/-- `PySequence_Fast`, `Objects/abstract.c:2104`. -/
def pySequenceFast (rt : Rt) (v : Val) (m : String) : M Val := do
  let w ← getW
  if typeOf w v == B.list || typeOf w v == B.tuple then pure v
  else
    let it ← tryM (rt.getIter v) fun e => do
      let w ← getW
      if excMatches w e B.TypeError then typeErr m else raise e
    let xs ← pySequenceList rt it
    alloc B.list (.list xs)

/-- `PySequence_Count`, `Objects/abstract.c:2231`. -/
def pySequenceCount (rt : Rt) (s o : Val) : M Int := pySequenceIterSearch rt s o .count
/-- `PySequence_Index`, `Objects/abstract.c:2261`. -/
def pySequenceIndex (rt : Rt) (s o : Val) : M Int := pySequenceIterSearch rt s o .index
/-- `PySequence_In`, `Objects/abstract.c:2255`. -/
def pySequenceIn (rt : Rt) (w' v : Val) : M Bool := pySequenceContains rt w' v

/-- `method_output_as_list`, `Objects/abstract.c:2433`. -/
def methodOutputAsList (rt : Rt) (o : Val) (meth : Name) : M Val := do
  let out ← callMethod rt o meth [] []
  let w ← getW
  if typeOf w out == B.list then pure out
  else
    let it ← tryM (rt.getIter out) fun e => do
      let w ← getW
      if excMatches w e B.TypeError then
        typeErr s!"{trunc 200 (typeName w o)}.{meth}() returned a non-iterable (type {trunc 200 (typeName w out)})"
      else raise e
    let xs ← pySequenceList rt it
    alloc B.list (.list xs)

/-- `PyMapping_Keys`, `Objects/abstract.c:2460`. -/
def pyMappingKeys (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  if typeOf w o == B.dict then
    alloc B.list (.list (((dictOf w o).getD []).map (·.1)))
  else methodOutputAsList rt o "keys"

/-- `PyMapping_Values`, `Objects/abstract.c:2484`. -/
def pyMappingValues (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  if typeOf w o == B.dict then
    alloc B.list (.list (((dictOf w o).getD []).map (·.2)))
  else methodOutputAsList rt o "values"

/-- `PyMapping_Items`, `Objects/abstract.c:2472`. -/
def pyMappingItems (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  if typeOf w o == B.dict then
    alloc B.list (.list (((dictOf w o).getD []).map fun (k, v) => Val.tuple [k, v]))
  else methodOutputAsList rt o "items"

/-- `PyAIter_Check`, `Objects/abstract.c:2864`. -/
def pyAIterCheck (w : World) (o : Val) : Bool :=
  match slotIn w o .am_anext with
  | none | some .nextNotImpl => false
  | some _ => true

/-- `PyObject_GetAIter`, `Objects/abstract.c:2837`. -/
def pyGetAIter (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  match slotIn w o .am_aiter with
  | none => typeErr s!"'{trunc 200 (typeName w o)}' object is not an async iterable"
  | some _ =>
    let it ← vectorcallMethod rt "__aiter__" [o]
    let w ← getW
    if pyAIterCheck w it then pure it
    else typeErr s!"aiter() returned not an async iterator of type '{trunc 100 (typeName w it)}'"

/-- `PyIter_NextItem`, `Objects/abstract.c:2900`. -/
def pyIterNextItem (rt : Rt) (it : Val) : M (Option Val) := do
  let w ← getW
  match slotOf w (typeOf w it) .tp_iternext with
  | none => typeErr s!"expected an iterator, got '{typeFQN w (typeOf w it)}'"
  | some _ => rt.iterNext it

/-! ## Calls, `Objects/call.c` -/

/-- `PyObject_CallNoArgs`, `Objects/call.c:102`. -/
def pyCallNoArgs (rt : Rt) (f : Val) : M Val := rt.call f [] []
/-- `PyObject_CallOneArg`, `Objects/call.c:386`. -/
def pyCallOneArg (rt : Rt) (f a : Val) : M Val := rt.call f [a] []
/-- `PyObject_CallObject`, `Objects/call.c:460`: `args` must be a tuple. -/
def pyCallObject (rt : Rt) (f args : Val) : M Val := do
  let w ← getW
  match args with
  | .none => rt.call f [] []
  | _ =>
    match tupleOf w args with
    | some xs => rt.call f xs []
    | none => typeErr "argument list must be a tuple"
/-- `_PyObject_Call_Prepend`, `Objects/call.c:478`. -/
def pyCallPrepend (rt : Rt) (f obj : Val) (args : List Val) (kw : Kw) : M Val :=
  rt.call f (obj :: args) kw
/-- `PyObject_CallMethod` family: the attribute is looked up with `PyObject_GetAttr`. -/
def pyCallMethodNamed (rt : Rt) (o : Val) (n : Name) (args : List Val) : M Val := do
  let f ← rt.getAttr o n
  rt.call f args []
/-- `PyObject_VectorcallMethod`, `Objects/call.c:887`: unbound methods get `self`. -/
def pyVectorcallMethod (rt : Rt) (o : Val) (n : Name) (args : List Val) (kw : Kw) : M Val := do
  let (m, unbound) ← pyGetMethod rt o n
  if unbound then rt.call m (o :: args) kw else rt.call m args kw

/-- `PyVectorcall_NARGS`, `Objects/call.c:1105`: the offset flag is bit 63. -/
def vectorcallNargs (nargsf : Nat) : Nat := nargsf % 2 ^ 63

end PyLean.TypeObj
