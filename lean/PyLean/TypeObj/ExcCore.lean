import PyLean.TypeObj.Attr

/-!
`BaseException` and what every other exception class in `Objects/exceptions.c` builds on.

This file comes before `Protocol`, so the abstract-object helpers the exception code calls
(`PySequence_Tuple`, `PyNumber_AsSsize_t`, ...) are stated here over `Rt`, with the same
branches as their twins in `Protocol.lean`.

## Representation

* `ExcData.members` holds the `PyObject *` members of the subclasses by Python attribute
  name. An absent name is a NULL field, which reads as `None` (`_Py_T_OBJECT`,
  `Python/structmember.c:87`).
* `start` and `end` of the Unicode errors are `Py_ssize_t` members, stored as `.int` under
  the same names; absent means the zero of `tp_alloc`.
* `ExcData.traceback` uses `Val.none` for the NULL field. A traceback object is a heap
  object of class `B.traceback`.
* `ExcData.notes` is the C field `PyBaseExceptionObject.notes`. `add_note` does not touch
  it: `__notes__` is an ordinary instance attribute.
-/

namespace PyLean.TypeObj

namespace B
def OSError : Addr := 57
def BlockingIOError : Addr := 58
def ChildProcessError : Addr := 59
def BrokenPipeError : Addr := 61
def ConnectionAbortedError : Addr := 62
def ConnectionRefusedError : Addr := 63
def ConnectionResetError : Addr := 64
def FileExistsError : Addr := 65
def FileNotFoundError : Addr := 66
def ImportError : Addr := 69
def InterruptedError : Addr := 70
def IsADirectoryError : Addr := 71
def NotADirectoryError : Addr := 74
def PermissionError : Addr := 75
def ProcessLookupError : Addr := 76
def SyntaxError : Addr := 80
def SystemExit : Addr := 82
def TimeoutError : Addr := 84
def UnicodeError : Addr := 85
def UnicodeDecodeError : Addr := 86
def UnicodeEncodeError : Addr := 87
def UnicodeTranslateError : Addr := 88
end B

/-! ## Reading an exception object -/

/-- The fields of an exception object; the empty fields for anything else. -/
def excDataOf (w : World) (v : Val) : ExcData :=
  match payloadOf w v with
  | some (.exc e) => e
  | _ => {}

/-- `self->args`. -/
def excArgs (w : World) (v : Val) : List Val := (excDataOf w v).args

/-- Update the fields of an exception object. -/
def excUpdate (v : Val) (f : ExcData → ExcData) : M Unit :=
  match v with
  | .obj a => modObj a fun o =>
    match o.body with
    | .exc d => { o with body := .exc (f d) }
    | _ => o
  | _ => pure ()

/-- A `PyObject *` member. -/
def memGet (d : ExcData) (n : Name) : Option Val := NameDict.get? d.members n

/-- `Py_XSETREF(self->n, v)`. -/
def memSet (n : Name) (v : Option Val) (d : ExcData) : ExcData :=
  { d with members :=
      match v with
      | some x => NameDict.set d.members n x
      | none => NameDict.erase d.members n }

/-- `PyExceptionInstance_Check`. -/
def excInstanceCheck (w : World) (v : Val) : Bool := isSubtype w (typeOf w v) B.BaseException

/-- `PyExceptionClass_Check`. -/
def excClassCheck (w : World) (v : Val) : Bool :=
  match asType w v with
  | some t => isSubtype w t B.BaseException
  | none => false

/-- `_PyBaseExceptionGroup_Check`. -/
def egCheck (w : World) (v : Val) : Bool := isSubtype w (typeOf w v) B.BaseExceptionGroup

/-- `PyTraceBack_Check`. -/
def tracebackCheck (w : World) (v : Val) : Bool := typeOf w v == B.traceback

/-- `_PyType_Name`, `Objects/typeobject.c:1443`: `tp_name` after the last dot. -/
def pyTypeName (w : World) (t : Addr) : String :=
  let n := tpName w t
  ((n.splitOn ".").getLast?).getD n

/-- `PyObject_Str`, which renders a NULL pointer as `<NULL>`, `Objects/object.c:799`. -/
def strOrNull (rt : Rt) : Option Val → M String
  | some v => rt.str v
  | none => pure "<NULL>"

/-! ## Abstract-object helpers over `Rt` -/

/-- The filled slot `s` of the type of `v`, honouring NULL `tp_as_*` structs. -/
def excSlotIn (w : World) (v : Val) (s : Slot) : Option SlotFn :=
  if hasGroup w (typeOf w v) s.group then slotOf w (typeOf w v) s else none

/-- `PySequence_Check`, `Objects/abstract.c:1672`. -/
def excSeqCheck (w : World) (s : Val) : Bool :=
  (dictOf w s).isNone && (excSlotIn w s .sq_item).isSome

/-- `PyCallable_Check`, `Objects/object.c:2100`. -/
def excCallableCheck (w : World) (v : Val) : Bool := (slotOf w (typeOf w v) .tp_call).isSome

/-- `PyNumber_Check`, `Objects/abstract.c:903`. -/
def excNumberCheck (w : World) (o : Val) : Bool :=
  (excSlotIn w o .nb_index).isSome || (excSlotIn w o .nb_int).isSome ||
    (excSlotIn w o .nb_float).isSome

/-- The iteration loop of `PySequence_Tuple` and `PySequence_List`. `fuel` is a model bound. -/
def excCollect (rt : Rt) (it : Val) : Nat → M (List Val)
  | 0 => raise .fuel
  | fuel + 1 => do
    match ← rt.iterNext it with
    | none => pure []
    | some x =>
      let rest ← excCollect rt it fuel
      pure (x :: rest)

/-- Loop bound for iteration. A model limit, not a Python one. -/
def excIterFuel : Nat := 100000

/-- `PySequence_Tuple`, `Objects/abstract.c:1996`, items only. -/
def excSeqTuple (rt : Rt) (v : Val) : M (List Val) := do
  match v with
  | .tuple xs => pure xs
  | _ =>
    let w ← getW
    match listOf w v, typeOf w v == B.list with
    | some xs, true => pure xs
    | _, _ =>
      let it ← rt.getIter v
      excCollect rt it excIterFuel

/-- `PyObject_Size` by way of the `len` builtin. -/
def excLen (rt : Rt) (o : Val) : M Int := do
  let f ← alloc B.builtinFn (.builtin .len none)
  let r ← rt.call f [o] []
  let w ← getW
  pure ((intOf w r).getD 0)

/-- `PyObject_LengthHint`, `Objects/abstract.c:95`. -/
def excLengthHint (rt : Rt) (o : Val) (dflt : Int) : M Int := do
  let w ← getW
  let hasLen := (excSlotIn w o .sq_length).isSome || (excSlotIn w o .mp_length).isSome
  let first : M (Option Int) :=
    if hasLen then catchMatch B.TypeError (some <$> excLen rt o) (pure none)
    else pure none
  match ← first with
  | some r => pure r
  | none =>
    match ← lookupSpecial rt o "__length_hint__" with
    | none => pure dflt
    | some hint =>
      let r? ← catchMatch B.TypeError (some <$> rt.call hint [] []) (pure none)
      match r? with
      | none => pure dflt
      | some .notImpl => pure dflt
      | some result =>
        let w ← getW
        match intOf w result with
        | none =>
          typeErr s!"__length_hint__ must be an integer, not {trunc 100 (typeName w result)}"
        | some i =>
          if !inSsize i then overflowErr "Python int too large to convert to C ssize_t"
          else if i < 0 then valueErr "__length_hint__() should return >= 0"
          else pure i

/-- `PySequence_List`, `Objects/abstract.c:2072`, items only. -/
def excSeqList (rt : Rt) (v : Val) : M (List Val) := do
  let w ← getW
  match v with
  | .tuple xs => pure xs
  | _ =>
    match listOf w v, typeOf w v == B.list with
    | some xs, true => pure xs
    | _, _ =>
      let it ← rt.getIter v
      let n ← excLengthHint rt v 8
      if n ≥ 2 ^ 48 then raiseC B.MemoryError ""
      excCollect rt it excIterFuel

/-- `_PyNumber_Index`, `Objects/abstract.c:1400`, as the value of the resulting `int`. -/
def excNumberIndex (rt : Rt) (item : Val) : M Int := do
  let w ← getW
  match intOf w item with
  | some i => pure i
  | none =>
    let bad := s!"'{trunc 200 (typeName w item)}' object cannot be interpreted as an integer"
    if !hasGroup w (typeOf w item) .number then typeErr bad
    match slotOf w (typeOf w item) .nb_index with
    | none => typeErr bad
    | some .generic =>
      let r ← vectorcallMethod rt "__index__" [item]
      let w ← getW
      match intOf w r with
      | some i => pure i
      | none => typeErr s!"__index__ returned non-int (type {trunc 200 (typeName w r)})"
    | some _ => unmodelled

/-- `PyNumber_AsSsize_t(item, PyExc_ValueError)`, `Objects/abstract.c:1458`. -/
def excAsSsizeValueError (rt : Rt) (item : Val) : M Int := do
  let i ← excNumberIndex rt item
  if inSsize i then pure i
  else
    let w ← getW
    valueErr s!"cannot fit '{trunc 200 (typeName w item)}' into an index-sized integer"

/-- `PyLong_AsSsize_t` overflow, `Objects/longobject.c:628`. -/
def excAsSsizeLong (i : Int) : M Int :=
  if inSsize i then pure i
  else overflowErr "Python int too large to convert to C ssize_t"

/-- `PyObject_IsInstance(inst, PyExc_Exception)`. `PyExc_Exception` is an exact `type`, so
this is `object_isinstance`, `Objects/abstract.c:2596`, with a concrete class. -/
def excIsInstanceOf (rt : Rt) (inst : Val) (ca : Addr) : M Bool := do
  let w ← getW
  if isSubtype w (typeOf w inst) ca then pure true
  else
    match ← rt.getOptionalAttr inst "__class__" with
    | none => pure false
    | some icls =>
      let w ← getW
      match asType w icls with
      | some ia => if ia != typeOf w inst then pure (isSubtype w ia ca) else pure false
      | none => pure false

/-! ## Argument parsing: the cases of `Python/getargs.c` these constructors use -/

/-- `Py_TYPE(arg)->tp_name` in `converterr`, `Python/getargs.c:632`. -/
def excArgName (w : World) (v : Val) : String :=
  if v.is .none then "None" else trunc 50 (typeName w v)

/-- `_PyArg_NoKeywords(name, kw)`, `Python/getargs.c:2800`. -/
def argNoKeywords (name : String) (kw : Kw) : M Unit :=
  unless kw.isEmpty do typeErr s!"{name}() takes no keyword arguments"

/-- The arity error of `vgetargs1_impl`, `Python/getargs.c:215`. -/
def argCount (fname : Option String) (min max n : Nat) : M Unit := do
  if n < min || max < n then
    let f := match fname with
      | some s => s ++ "()"
      | none => "function"
    let how := if min == max then "exactly" else if n < min then "at least" else "at most"
    let m := if n < min then min else max
    typeErr s!"{f} takes {how} {m} argument{if m == 1 then "" else "s"} ({n} given)"

/-- `seterror` around a `must be X, not Y` conversion failure, `Python/getargs.c:399`. -/
def argPrefix (fname : Option String) (i : Nat) : String :=
  let p := match fname with
    | some s => s ++ "() "
    | none => ""
  s!"{p}argument {i}"

/-- Format `U`: `PyUnicode_Check`. -/
def argU (fname : Option String) (i : Nat) (v : Val) : M Unit := do
  let w ← getW
  if (strOf w v).isNone then
    typeErr s!"{argPrefix fname i} must be str, not {excArgName w v}"

/-- Format `n`: `_PyNumber_Index`, then `PyLong_AsSsize_t`, in `convertsimple`, `Python/getargs.c`. -/
def argN (rt : Rt) (v : Val) : M Int := do
  let i ← excNumberIndex rt v
  excAsSsizeLong i

/-- `error_unexpected_keyword_arg`, `Python/getargs.c:1492`, without the "Did you mean"
suggestion of `_Py_CalculateSuggestions` (`Python/suggestions.c`). -/
def argUnexpectedKeyword (fname : String) (names : List Name) (kw : Kw) : M Unit :=
  match kw.find? (fun p => !names.contains p.1) with
  | some (k, _) => typeErr s!"{fname}() got an unexpected keyword argument '{k}'"
  | none => typeErr s!"invalid keyword argument for {fname}()"

/-- `PyArg_ParseTupleAndKeywords(empty_tuple, kwds, "|$OO...:fname", names, ...)`:
`vgetargskeywords`, `Python/getargs.c:1575`, for keyword-only objects. -/
def argKeywordOnly (fname : String) (names : List Name) (kw : Kw) : M (Name → Option Val) := do
  if kw.length > names.length then
    let l := names.length
    typeErr s!"{fname}() takes at most {l} keyword argument{if l == 1 then "" else "s"} ({kw.length} given)"
  if kw.any (fun p => !names.contains p.1) then
    argUnexpectedKeyword fname names kw
  pure fun n => NameDict.get? kw n

/-! ## `BaseException` -/

/-- `BaseException_new`, `Objects/exceptions.c:60`; `kwds` is ignored. -/
def baseExceptionNew (t : Addr) (args : List Val) : M Val :=
  alloc t (.exc { args := args })

/-- `BaseException_init`, `Objects/exceptions.c:88`. -/
def baseExceptionInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  let w ← getW
  argNoKeywords (typeName w self) kw
  excUpdate self fun d => { d with args := args }

/-- `BaseException_vectorcall`, `Objects/exceptions.c:100`: `tp_vectorcall` of the exact
classes that use `BaseException_new` and `BaseException_init` (`_PyExc_InitTypes`, `:4424`),
which is `type_call` with the two steps merged. -/
def baseExceptionVectorcall (t : Addr) (args : List Val) (kw : Kw) : M Val := do
  let w ← getW
  argNoKeywords (tpName w t) kw
  alloc t (.exc { args := args })

/-- `BaseException_str`, `Objects/exceptions.c:171`. -/
def baseExceptionStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match excArgs w v with
  | [] => pure (.str "")
  | [x] => .str <$> rt.str x
  | xs => .str <$> rt.str (.tuple xs)

/-- `BaseException_repr`, `Objects/exceptions.c:193`. -/
def baseExceptionRepr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  let name := pyTypeName w (typeOf w v)
  match excArgs w v with
  | [x] =>
    let r ← rt.repr x
    pure (.str s!"{name}({r})")
  | xs =>
    let r ← rt.repr (.tuple xs)
    pure (.str (name ++ r))

/-- `BaseException___reduce___impl`, `Objects/exceptions.c:220`. -/
def baseExceptionReduce (v : Val) : M Val := do
  let w ← getW
  let tv : Val := .obj (typeOf w v)
  match instDictAddr w v with
  | some d => pure (.tuple [tv, .tuple (excArgs w v), .obj d])
  | none => pure (.tuple [tv, .tuple (excArgs w v)])

/-- The `PyDict_Next` loop of `BaseException___setstate___impl`. -/
def setstateLoop (rt : Rt) (self : Val) : List (Val × Val) → M Unit
  | [] => pure ()
  | (k, v) :: rest => do
    let w ← getW
    match strOf w k with
    | none =>
      typeErr s!"attribute name must be string, not '{trunc 200 (typeName w k)}'"
    | some n =>
      rt.setAttr self n (some v)
      setstateLoop rt self rest

/-- `BaseException___setstate___impl`, `Objects/exceptions.c:243`. -/
def baseExceptionSetstate (rt : Rt) (self state : Val) : M Val := do
  if state.is .none then pure .none
  else
    let w ← getW
    match dictOf w state with
    | none => typeErr "state is not a dictionary"
    | some es =>
      setstateLoop rt self es
      pure .none

/-- `BaseException___traceback___set_impl`, `Objects/exceptions.c:398`, and
`PyException_SetTraceback`, `:530`. -/
def baseExceptionTracebackSet (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "__traceback__ may not be deleted"
  | some v =>
    if tracebackCheck w v then excUpdate self fun d => { d with traceback := v }
    else if v.is .none then excUpdate self fun d => { d with traceback := .none }
    else typeErr "__traceback__ must be a traceback or None"

/-- `BaseException_with_traceback_impl`, `Objects/exceptions.c:279`. -/
def baseExceptionWithTraceback (self tb : Val) : M Val := do
  baseExceptionTracebackSet self (some tb)
  pure self

/-- `BaseException_add_note_impl`, `Objects/exceptions.c:298`; the argument check is
the clinic wrapper, `Objects/clinic/exceptions.c.h`. -/
def baseExceptionAddNote (rt : Rt) (self note : Val) : M Val := do
  let w ← getW
  if (strOf w note).isNone then
    typeErr s!"add_note() argument must be str, not {excArgName w note}"
  let notes ← rt.getOptionalAttr self "__notes__"
  let l ← match notes with
    | none =>
      let l ← alloc B.list (.list [])
      rt.setAttr self "__notes__" (some l)
      pure l
    | some n =>
      let w ← getW
      if (listOf w n).isNone then typeErr "Cannot add note: __notes__ is not a list"
      pure n
  let w ← getW
  match l with
  | .obj a =>
    modObj a fun o => { o with body := .list (((listOf w l).getD []) ++ [note]) }
    pure .none
  | _ => unmodelled

/-- `_PyException_AddNote`, `Objects/exceptions.c:4574`. -/
def pyExceptionAddNote (rt : Rt) (exc note : Val) : M Unit := do
  let w ← getW
  unless excInstanceCheck w exc do
    typeErr s!"exc must be an exception, not '{typeName w exc}'"
  let _ ← baseExceptionAddNote rt exc note

/-- `BaseException_args_set_impl`, `Objects/exceptions.c:359`. -/
def baseExceptionArgsSet (rt : Rt) (self : Val) (value : Option Val) : M Unit := do
  match value with
  | none => typeErr "args may not be deleted"
  | some v =>
    let seq ← excSeqTuple rt v
    excUpdate self fun d => { d with args := seq }

/-- `PyException_SetContext`, `Objects/exceptions.c:572`. -/
def pyExceptionSetContext (self : Val) (context : Option Val) : M Unit :=
  excUpdate self fun d => { d with context := context }

/-- `PyException_SetCause`, `Objects/exceptions.c:551`: it always sets `suppress_context`. -/
def pyExceptionSetCause (self : Val) (cause : Option Val) : M Unit :=
  excUpdate self fun d => { d with suppressContext := true, cause := cause }

/-- `BaseException___context___set_impl`, `Objects/exceptions.c:443`. -/
def baseExceptionContextSet (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "__context__ may not be deleted"
  | some v =>
    if v.is .none then pyExceptionSetContext self none
    else if !excInstanceCheck w v then
      typeErr "exception context must be None or derive from BaseException"
    else pyExceptionSetContext self (some v)

/-- `BaseException___cause___set_impl`, `Objects/exceptions.c:486`. -/
def baseExceptionCauseSet (self : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value with
  | none => typeErr "__cause__ may not be deleted"
  | some v =>
    if v.is .none then pyExceptionSetCause self none
    else if !excInstanceCheck w v then
      typeErr "exception cause must be None or derive from BaseException"
    else pyExceptionSetCause self (some v)

/-- `Py_T_BOOL`, `Python/structmember.c:170`: the `__suppress_context__` member. -/
def suppressContextSet (self : Val) (value : Option Val) : M Unit := do
  match value with
  | none => typeErr "can't delete numeric/char attribute"
  | some (.bool b) => excUpdate self fun d => { d with suppressContext := b }
  | some _ => typeErr "attribute value type must be bool"

/-- `PyObject_GenericSetDict`, `Objects/object.c:2046`. -/
def excDictSet (obj : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match value, obj with
  | none, _ => typeErr "cannot delete __dict__"
  | some v, .obj a =>
    match dictOf w v, v with
    | some _, .obj d => modObj a fun o => { o with dict := some d }
    | _, _ =>
      typeErr s!"__dict__ must be set to a dictionary, not a '{trunc 200 (typeName w v)}'"
  | _, _ => unmodelled

/-! ### The thin C API of `BaseException`, `Objects/exceptions.c:518-603` -/

/-- `PyException_GetTraceback`, `Objects/exceptions.c:519`. -/
def pyExceptionGetTraceback (w : World) (self : Val) : Option Val :=
  match (excDataOf w self).traceback with
  | .none => none
  | t => some t

/-- `PyException_GetCause`, `Objects/exceptions.c:540`. -/
def pyExceptionGetCause (w : World) (self : Val) : Option Val := (excDataOf w self).cause

/-- `PyException_GetContext`, `Objects/exceptions.c:561`. -/
def pyExceptionGetContext (w : World) (self : Val) : Option Val := (excDataOf w self).context

/-- `PyException_GetArgs`, `Objects/exceptions.c:580`. -/
def pyExceptionGetArgs (w : World) (self : Val) : Val := .tuple (excArgs w self)

/-- `PyException_SetArgs`, `Objects/exceptions.c:590`. -/
def pyExceptionSetArgs (self : Val) (args : List Val) : M Unit :=
  excUpdate self fun d => { d with args := args }

/-- `PyExceptionClass_Name`, `Objects/exceptions.c:599`. -/
def pyExceptionClassName (w : World) (t : Addr) : String := tpName w t

/-! ## `StopIteration`, `SystemExit`, `KeyError` -/

/-- `StopIteration_init`, `Objects/exceptions.c:754`. -/
def stopIterationInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  excUpdate self (memSet "value" (some (args.headD .none)))

/-- `SystemExit_init`, `Objects/exceptions.c:819`. -/
def systemExitInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args kw
  match args with
  | [] => pure ()
  | [x] => excUpdate self (memSet "code" (some x))
  | xs => excUpdate self (memSet "code" (some (.tuple xs)))

/-- `KeyError_str`, `Objects/exceptions.c:2942`. -/
def keyErrorStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match excArgs w v with
  | [x] => .str <$> rt.repr x
  | _ => baseExceptionStr rt v

/-! ## `ImportError`, `NameError`, `AttributeError` -/

/-- `ImportError_init`, `Objects/exceptions.c:1810`. -/
def importErrorInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args []
  let get ← argKeywordOnly "ImportError" ["name", "path", "name_from"] kw
  excUpdate self (memSet "name" (get "name"))
  excUpdate self (memSet "path" (get "path"))
  excUpdate self (memSet "name_from" (get "name_from"))
  let msg := match args with
    | [m] => some m
    | _ => none
  excUpdate self (memSet "msg" msg)

/-- `ImportError_str`, `Objects/exceptions.c:1876`. -/
def importErrorStr (rt : Rt) (v : Val) : M Val := do
  let w ← getW
  match memGet (excDataOf w v) "msg" with
  | some (.str s) => pure (.str s)
  | _ => baseExceptionStr rt v

/-- A fresh copy of the entries of the instance dict, `dict ? PyDict_Copy(dict) : PyDict_New()`. -/
def instDictEntries (w : World) (v : Val) : List (Val × Val) :=
  match instDictAddr w v with
  | some d => (dictOf w (.obj d)).getD []
  | none => []

/-- `ImportError_getstate`, `Objects/exceptions.c:1886`. -/
def importErrorGetstate (v : Val) : M Val := do
  let w ← getW
  let d := excDataOf w v
  let (name, path, nameFrom) := (memGet d "name", memGet d "path", memGet d "name_from")
  if name.isSome || path.isSome || nameFrom.isSome then
    let add (es : List (Val × Val)) (k : Name) (x : Option Val) :=
      match x with
      | some y => dictSetEntry es (.str k) y
      | none => es
    let es := add (add (add (instDictEntries w v) "name" name) "path" path) "name_from" nameFrom
    alloc B.dict (.dict es)
  else
    match instDictAddr w v with
    | some a => pure (.obj a)
    | none => pure .none

/-- `ImportError_reduce`, `Objects/exceptions.c:1918`. -/
def importErrorReduce (v : Val) : M Val := do
  let state ← importErrorGetstate v
  let w ← getW
  let tv : Val := .obj (typeOf w v)
  if state.is .none then pure (.tuple [tv, .tuple (excArgs w v)])
  else pure (.tuple [tv, .tuple (excArgs w v), state])

/-- `NameError_init`, `Objects/exceptions.c:2504`. -/
def nameErrorInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args []
  let get ← argKeywordOnly "NameError" ["name"] kw
  excUpdate self (memSet "name" (get "name"))

/-- `AttributeError_init`, `Objects/exceptions.c:2587`. -/
def attributeErrorInit (self : Val) (args : List Val) (kw : Kw) : M Unit := do
  baseExceptionInit self args []
  let get ← argKeywordOnly "AttributeError" ["name", "obj"] kw
  excUpdate self (memSet "name" (get "name"))
  excUpdate self (memSet "obj" (get "obj"))

/-- `AttributeError_getstate`, `Objects/exceptions.c:2643`: `self->args` is never NULL on
an initialised object, so the dictionary branch always runs. -/
def attributeErrorGetstate (v : Val) : M Val := do
  let w ← getW
  let d := excDataOf w v
  let es := instDictEntries w v
  let es := match memGet d "name" with
    | some n => dictSetEntry es (.str "name") n
    | none => es
  alloc B.dict (.dict (dictSetEntry es (.str "args") (.tuple d.args)))

/-- `AttributeError_reduce`, `Objects/exceptions.c:2672`. -/
def attributeErrorReduce (v : Val) : M Val := do
  let state ← attributeErrorGetstate v
  let w ← getW
  pure (.tuple [.obj (typeOf w v), .tuple (excArgs w v), state])

/-! ## `MemoryError` -/

/-- `MemoryError_new`, `Objects/exceptions.c:4066`, on the path every program with fewer
than 16 live `MemoryError`s takes: `get_memory_error` hands out a freelist entry, whose
`args` is the empty tuple whatever was passed. `ExcFreelist.lean` models the list itself. -/
def memoryErrorNew (t : Addr) (args : List Val) : M Val :=
  if t != B.MemoryError then baseExceptionNew t args
  else baseExceptionNew t []

end PyLean.TypeObj
