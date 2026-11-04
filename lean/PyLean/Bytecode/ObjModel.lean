import PyLean.Bytecode.State

/-!
The abstract interface between the interpreter loop and the object model.

The machine in `Uops*.lean`/`Exec.lean` is written against `ObjModel`, a plain
structure of type-dispatched protocol functions, so another module can plug in a
richer data model without touching a step rule. Object operations live in `RM`,
so by construction they cannot read or write the caller's frame or stack. When
one needs to run Python code it goes through `Ctx.evalFrame`, the model of
`_PyEval_EvalFrame`, which the fuel-bounded loop in `Exec.lean` supplies.

This file also holds exception objects: `_PyErr_SetObject` and the builtin
exception hierarchy of `Objects/exceptions.c`.
-/

namespace PyLean.Bytecode

/-- What object code needs from the interpreter. -/
structure Ctx where
  /-- `_PyEval_EvalFrame(tstate, frame, throwflag)`; `some exc` is `throwflag = 1`
  with `exc` as the current exception. -/
  evalFrame : Frame → Option Val → RM Val

/-- Type-dispatched protocol functions (`Objects/abstract.c`, `Objects/object.c`). -/
structure ObjModel where
  /-- `PyObject_IsTrue`. -/
  isTrue : Ctx → Val → RM Bool
  /-- `PyNumber_Negative`. -/
  negative : Ctx → Val → RM Val
  /-- `PyNumber_Invert`. -/
  invert : Ctx → Val → RM Val
  /-- `_PyEval_BinaryOps[nb](lhs, rhs)`. -/
  binaryOp : Ctx → Nat → Val → Val → RM Val
  /-- `PyObject_RichCompare(l, r, op)`. -/
  richCompare : Ctx → Val → Val → Nat → RM Val
  /-- `PySequence_Contains(container, item)`. -/
  contains : Ctx → Val → Val → RM Bool
  /-- `PyObject_GetItem`. -/
  getItem : Ctx → Val → Val → RM Val
  /-- `PyObject_SetItem(container, key, value)`. -/
  setItem : Ctx → Val → Val → Val → RM Unit
  /-- `PyObject_DelItem`. -/
  delItem : Ctx → Val → Val → RM Unit
  /-- `PyObject_GetAttr`. -/
  getAttr : Ctx → Val → String → RM Val
  /-- `_PyObject_GetMethodStackRef`: `(attr, self_or_null)`. -/
  getMethod : Ctx → Val → String → RM (Val × Val)
  /-- `PyObject_SetAttr`. -/
  setAttr : Ctx → Val → String → Val → RM Unit
  /-- `PyObject_DelAttr`. -/
  delAttr : Ctx → Val → String → RM Unit
  /-- `PyObject_GetIter`. -/
  getIter : Ctx → Val → RM Val
  /-- `Py_TYPE(it)->tp_iternext(it)`: `none` is `NULL` with no exception set. -/
  iterNext : Ctx → Val → RM (Option Val)
  /-- `Py_TYPE(it)->tp_iternext != NULL`. -/
  isIterator : Val → RM Bool
  /-- `Py_TYPE(v)->tp_iter != NULL || PySequence_Check(v)`. -/
  isIterable : Val → RM Bool
  /-- `PyObject_Vectorcall`. `args` ends with the values of `kwnames`. -/
  call : Ctx → Val → List Val → List String → RM Val
  /-- `PyObject_Call(callable, args, kwargs)` (`Objects/call.c:333-373`): `args` a tuple, `kwargs` a
  dict or `NULL`. A callable with vectorcall gets the dict unpacked first (`_PyVectorcall_Call`), one
  with only `tp_call` gets the dict itself. -/
  callDict : Ctx → Val → Val → Val → RM Val
  /-- `PyObject_Str`. -/
  str : Ctx → Val → RM Val
  /-- `PyObject_Repr`. -/
  repr : Ctx → Val → RM Val
  /-- `PyObject_ASCII`. -/
  ascii : Ctx → Val → RM Val
  /-- `PyObject_Format(value, spec)`; `.null` is a NULL spec. -/
  format : Ctx → Val → Val → RM Val
  /-- `PyObject_Length`. -/
  length : Ctx → Val → RM Int
  /-- `PyObject_Hash`. -/
  hash : Ctx → Val → RM Int
  /-- `_PyObject_LookupSpecialMethod`: `(method, self_or_null)`; `none` is "not found". -/
  lookupSpecial : Ctx → Val → String → RM (Option (Val × Val))
  /-- `_PySuper_Lookup(cls, self, name, method?)`: `(attr, method_found)`. -/
  superLookup : Ctx → Val → Val → String → Bool → RM (Val × Bool)
  /-- `type(self).__getattribute__ is object.__getattribute__`
  (`tp_getattro == PyObject_GenericGetAttr`). -/
  genericGetattr : Val → RM Bool
  /-- `_PyType_Lookup(type, name)`, with no descriptor binding. -/
  typeLookup : Val → String → RM (Option Val)
  /-- `PyObject_IsInstance`. -/
  isInstance : Ctx → Val → Val → RM Bool
  /-- `__import__`, `_PyEval_ImportName`. -/
  importName : Ctx → Frame → String → Val → Val → RM Val
  /-- `_PyEval_ImportFrom`. -/
  importFrom : Ctx → Val → String → RM Val
  /-- `_PyEval_LazyImportName(tstate, builtins, globals, locals, name, fromlist, level, lazy)`
  (`Python/ceval.c:3096-3164`, PEP 810): the global lazy-imports mode and `__lazy_modules__` may
  make an import lazy, `lazy` is the `lazy import` keyword; an eager one is `_PyEval_ImportName`. -/
  lazyImportName : Ctx → Frame → String → Val → Val → Bool → RM Val
  /-- `PyLazyImport_CheckExact` (`Include/internal/pycore_lazyimportobject.h:15`). -/
  isLazyImport : Val → RM Bool
  /-- `_PyEval_LazyImportFrom(tstate, frame, from, name)` (`Objects/lazyimportobject.c:133`). -/
  lazyImportFrom : Ctx → Frame → Val → String → RM Val
  /-- Unused since `exceptionGroupMatch` mirrors `PyObject_CallMethod(exc_group, "split", match_type)`
  and the checks on its result with `getAttr` and `call` (kept so the object models still build). -/
  egSplit : Ctx → Val → Val → RM (Val × Val)
  /-- `_PyExc_CreateExceptionGroup("", excs)`. -/
  egWrap : Ctx → Val → RM Val
  /-- `_PyEval_MatchClass`: the attribute tuple, or `none` on no match. -/
  matchClass : Ctx → Val → Val → Nat → Val → RM (Option Val)
  /-- `_PyEval_MatchKeys`: a tuple of values, or `.none`. -/
  matchKeys : Ctx → Val → Val → RM Val
  /-- `tp_flags & Py_TPFLAGS_MAPPING`. -/
  isMapping : Val → RM Bool
  /-- `tp_flags & Py_TPFLAGS_SEQUENCE`. -/
  isSequence : Val → RM Bool
  /-- The `__aiter__`/`__anext__`/`__await__` slots for `GET_AITER` and friends. -/
  getAIter : Ctx → Val → RM Val
  getANext : Ctx → Val → RM Val
  getAwaitable : Ctx → Val → Nat → RM Val
  /-- `Py_TYPE(o)->tp_as_async && Py_TYPE(o)->tp_as_async->am_send` (`Objects/abstract.c:2935`). -/
  hasAmSend : Val → RM Bool
  /-- `Py_TYPE(o)->tp_as_async->am_send(o, arg, &result)`: `(result, PYGEN_RETURN?)`, an exception
  being `PYGEN_ERROR`. -/
  amSend : Ctx → Val → Val → RM (Val × Bool)
  /-- `PyCFunction_CheckExact(o)` (`Include/cpython/methodobject.h`): `some (ml_flags, m_self)`,
  `PyCFunction_GET_FLAGS(o)` and `PyCFunction_GET_SELF(o)`, or `none` when `o` is not exactly a
  `builtin_function_or_method`. A read of the object, so a function of the heap. -/
  cfuncOf : Rt → Val → Option (Nat × Val)
  /-- `Py_IS_TYPE(o, &PyMethodDescr_Type)`: `some (d_method->ml_flags, d_common.d_type)`. -/
  methDescrOf : Rt → Val → Option (Nat × Val)
  /-- `f->ml_meth` of a builtin function or method descriptor `f` called on `self` and the
  arguments its calling convention passes (`_PyCFunction_TrampolineCall`, or the
  `PyCFunctionFast[WithKeywords]` cast): `[]` for `METH_NOARGS` (the `NULL`), `[arg]` for `METH_O`,
  the array for `METH_FASTCALL` and `METH_FASTCALL | METH_KEYWORDS` (with `kwnames = NULL`). An
  arbitrary fallible callable: C code that may run Python code and raise. -/
  mlMeth : Ctx → Val → Val → List Val → RM Val
  /-- `PyType_Check(o) && ((PyTypeObject *)o)->tp_vectorcall != NULL`. -/
  hasTypeVectorcall : Rt → Val → Bool
  /-- `tp->tp_vectorcall((PyObject *)tp, args, nargs, NULL)`. -/
  typeVectorcall : Ctx → Val → List Val → RM Val
  /-- `PyDict_Update(d, update)`, used by `DICT_UPDATE`. -/
  dictUpdate : Ctx → Val → Val → RM Unit
  /-- `_PyDict_MergeUniq(d, update, &dupkey)`, used by `DICT_MERGE`: `some k` is the `-2` return
  with `*dupkey = k`, a key already in `d`; an exception is the `-1` return. -/
  dictMerge : Ctx → Val → Val → RM (Option Val)
  /-- `_PyList_Extend`. -/
  listExtend : Ctx → Val → Val → RM Unit
  /-- `_PySet_Update`. -/
  setUpdate : Ctx → Val → Val → RM Unit
  /-- `__build_class__` etc. are looked up in builtins; this is the intrinsic table
  entry for `CALL_INTRINSIC_1`. -/
  intrinsic1 : Ctx → Frame → Nat → Val → RM Val
  intrinsic2 : Ctx → Frame → Nat → Val → Val → RM Val
  /-- `_PyInterpolation_Build`, `_PyTemplate_Build`. -/
  buildInterpolation : Ctx → Val → Val → Nat → Val → RM Val
  buildTemplate : Ctx → Val → Val → RM Val

/-- `METH_NOARGS`, `METH_O`, `METH_FASTCALL`, `METH_KEYWORDS`, `Include/methodobject.h:96-117`. -/
def methNoArgs : Nat := 0x0004
def methO : Nat := 0x0008
def methFastcall : Nat := 0x0080
def methKeywords : Nat := 0x0002

/-- The whole runtime state, for the heap reads `ObjModel.cfuncOf` and friends. -/
def readRt : RM Rt := fun rt => .ok rt rt

/-! ## Builtin exceptions -/

/-- The direct base of each builtin exception class, `Objects/exceptions.c`
(`ExceptionGroup` also inherits `Exception`; it is handled by `excMro`). -/
def excBase : String → Option String
  | "BaseExceptionGroup" | "Exception" | "GeneratorExit" | "KeyboardInterrupt" | "SystemExit" =>
    some "BaseException"
  | "ArithmeticError" | "AssertionError" | "AttributeError" | "BufferError" | "EOFError"
  | "ImportError" | "LookupError" | "MemoryError" | "NameError" | "OSError" | "ReferenceError"
  | "RuntimeError" | "StopAsyncIteration" | "StopIteration" | "SyntaxError" | "SystemError"
  | "TypeError" | "ValueError" | "Warning" => some "Exception"
  | "ExceptionGroup" => some "BaseExceptionGroup"
  | "FloatingPointError" | "OverflowError" | "ZeroDivisionError" => some "ArithmeticError"
  | "ModuleNotFoundError" => some "ImportError"
  | "IndexError" | "KeyError" => some "LookupError"
  | "UnboundLocalError" => some "NameError"
  | "BlockingIOError" | "ChildProcessError" | "ConnectionError" | "FileExistsError"
  | "FileNotFoundError" | "InterruptedError" | "IsADirectoryError" | "NotADirectoryError"
  | "PermissionError" | "ProcessLookupError" | "TimeoutError" => some "OSError"
  | "BrokenPipeError" | "ConnectionAbortedError" | "ConnectionRefusedError"
  | "ConnectionResetError" => some "ConnectionError"
  | "NotImplementedError" | "PythonFinalizationError" | "RecursionError" => some "RuntimeError"
  | "IndentationError" | "IncompleteInputError" => some "SyntaxError"
  | "TabError" => some "IndentationError"
  | "UnicodeError" => some "ValueError"
  | "UnicodeDecodeError" | "UnicodeEncodeError" | "UnicodeTranslateError" => some "UnicodeError"
  | "BytesWarning" | "DeprecationWarning" | "EncodingWarning" | "FutureWarning" | "ImportWarning"
  | "PendingDeprecationWarning" | "ResourceWarning" | "RuntimeWarning" | "SyntaxWarning"
  | "UnicodeWarning" | "UserWarning" => some "Warning"
  | _ => none

/-- `BaseException` itself, or a subclass of it. -/
def isBuiltinExcName (n : String) : Bool := n == "BaseException" || (excBase n).isSome

/-- `tp_mro` of a builtin exception class, by following `excBase`. The depth of
the hierarchy is at most 6. -/
def excMroNames (n : String) : List String :=
  let rec go : Nat → String → List String
    | 0, _ => ["object"]
    | k + 1, c =>
      match excBase c with
      | some b => c :: go k b
      | none => [c, "object"]
  if n == "ExceptionGroup" then
    ["ExceptionGroup", "BaseExceptionGroup", "Exception", "BaseException", "object"]
  else go 8 n

/-- Direct bases of the non-exception builtin types that have any. -/
def builtinMro : String → List String
  | "bool" => ["bool", "int", "object"]
  | "object" => ["object"]
  | n => if isBuiltinExcName n then excMroNames n else [n, "object"]

/-- `Py_TYPE(v)` for values whose type does not need the heap. -/
def immType : Val → Option Val
  | .none => some (.cls "NoneType")
  | .notImpl => some (.cls "NotImplementedType")
  | .ellipsis => some (.cls "ellipsis")
  | .bool _ => some (.cls "bool")
  | .int _ => some (.cls "int")
  | .float _ => some (.cls "float")
  | .str _ => some (.cls "str")
  | .bytes _ => some (.cls "bytes")
  | .cls _ => some (.cls "type")
  | .builtin _ => some (.cls "builtin_function_or_method")
  | .methDescr _ _ => some (.cls "method_descriptor")
  | .code _ => some (.cls "code")
  | _ => Option.none

/-- `Py_TYPE(v)`. -/
def typeOf : Val → RM Val
  | .ref a => do
    match ← getObj a with
    | .tuple _ => pure (.cls "tuple")
    | .list _ => pure (.cls "list")
    | .dict _ => pure (.cls "dict")
    | .set frozen _ => pure (.cls (if frozen then "frozenset" else "set"))
    | .slice .. => pure (.cls "slice")
    | .range .. => pure (.cls "range")
    | .cell _ => pure (.cls "cell")
    | .func _ => pure (.cls "function")
    | .method .. => pure (.cls "method")
    | .gen g =>
      pure (.cls (match g.kind with | .gen => "generator" | .coro => "coroutine" | .asyncGen => "async_generator"))
    | .listIter .. => pure (.cls "list_iterator")
    | .tupleIter .. => pure (.cls "tuple_iterator")
    | .rangeIter .. => pure (.cls "range_iterator")
    | .strIter _ => pure (.cls "str_ascii_iterator")
    | .seqIter .. => pure (.cls "iterator")
    | .callIter .. => pure (.cls "callable_iterator")
    | .dictIter _ k _ _ =>
      pure (.cls (match k with | 0 => "dict_keyiterator" | 1 => "dict_valueiterator" | _ => "dict_itemiterator"))
    | .dictView _ k =>
      pure (.cls (match k with | 0 => "dict_keys" | 1 => "dict_values" | _ => "dict_items"))
    | .setIter .. => pure (.cls "set_iterator")
    | .enumerate .. => pure (.cls "enumerate")
    | .zip .. => pure (.cls "zip")
    | .map .. => pure (.cls "map")
    | .filter .. => pure (.cls "filter")
    | .reversed .. => pure (.cls "reversed")
    | .cls c => pure c.metaclass
    | .inst i => pure i.cls
    | .module .. => pure (.cls "module")
    | .super .. => pure (.cls "super")
    | .property .. => pure (.cls "property")
    | .staticMethod _ => pure (.cls "staticmethod")
    | .classMethod _ => pure (.cls "classmethod")
    | .boundBuiltin .. => pure (.cls "builtin_function_or_method")
    | .asend .. => pure (.cls "async_generator_asend")
    | .agWrapped _ => pure (.cls "async_generator_wrapped_value")
    | .traceback .. => pure (.cls "traceback")
  | .null => fault "Py_TYPE(NULL)"
  | .tagged _ => fault "Py_TYPE(tagged int)"
  | v =>
    match immType v with
    | some t => pure t
    | Option.none => fault "no type"

/-- `tp_mro` of a type object. -/
def mroOf : Val → RM (List Val)
  | .cls n => pure ((builtinMro n).map .cls)
  | .ref a => do
    match ← getObj a with
    | .cls c => pure c.mro
    | _ => fault "not a type"
  | _ => fault "not a type"

/-- `tp_name` of a type object. -/
def typeNameOf : Val → RM String
  | .cls n => pure n
  | .ref a => do
    match ← getObj a with
    | .cls c => pure c.name
    | _ => fault "not a type"
  | _ => fault "not a type"

/-- `Py_TYPE(v)->tp_name`. -/
def tpName (v : Val) : RM String := do typeNameOf (← typeOf v)

/-- `PyType_Check`. -/
def isType : Val → RM Bool
  | .cls _ => pure true
  | .ref a => do
    match ← getObj a with
    | .cls _ => pure true
    | _ => pure false
  | _ => pure false

/-- `PyType_IsSubtype(a, b)`. -/
def isSubtype (a b : Val) : RM Bool := do
  return (← mroOf a).any (· == b)

/-- `PyExceptionClass_Check`. -/
def isExcClass (v : Val) : RM Bool := do
  if ← isType v then isSubtype v (.cls "BaseException") else pure false

/-- `PyExceptionInstance_Check`. -/
def isExcInstance (v : Val) : RM Bool := do
  match v with
  | .ref a =>
    match ← getObj a with
    | .inst i => pure i.exc.isSome
    | _ => pure false
  | _ => pure false

/-- `BaseException_new`/`__init__` for a class and an argument list. -/
def newExc (cls : Val) (args : List Val) : RM Val := do
  let t ← mkTuple args
  let value := if cls == .cls "StopIteration" then (args.head?.getD .none) else .none
  alloc (.inst { cls := cls, exc := some { args := t, value := value } })

def excData : Val → RM ExcData
  | .ref a => do
    match ← getObj a with
    | .inst { exc := some d, .. } => pure d
    | _ => fault "not an exception"
  | _ => fault "not an exception"

def setExcData (v : Val) (d : ExcData) : RM Unit := do
  match v with
  | .ref a =>
    match ← getObj a with
    | .inst i => setObj a (.inst { i with exc := some d })
    | _ => fault "not an exception"
  | _ => fault "not an exception"

/-- `PyException_GetContext`. -/
def getContext (v : Val) : RM Val := do return (← excData v).context

/-- `PyException_SetContext`. -/
def setContext (v c : Val) : RM Unit := do setExcData v { ← excData v with context := c }

/-- `PyException_SetCause`: also sets `__suppress_context__`. -/
def setCause (v c : Val) : RM Unit := do
  setExcData v { ← excData v with cause := c, suppressContext := true }

/-- `_PyErr_GetTopmostException(tstate)->exc_value`: the innermost `exc_info`
item whose value is neither NULL nor None, or the outermost item. -/
def topmostExc : RM Val := fun rt =>
  let rec go : List Val → Val
    | [] => .null
    | [v] => v
    | v :: rest => if v == .null || v == .none then go rest else v
  .ok (go rt.excInfo) rt

/-- The chain walk of `_PyErr_SetObject` (`Python/errors.c`): cut any link back to
`value`. Bounded by `n`, which replaces Floyd's cycle detection. -/
def cutContextCycle (value : Val) : Nat → Val → RM Unit
  | 0, _ => pure ()
  | n + 1, o => do
    let c ← getContext o
    if c == .null then pure ()
    else if c == value then setContext o .null
    else cutContextCycle value n c

/-- `_PyErr_SetObject` for an already normalized `value`: implicit chaining. -/
def setObject (value : Val) : RM Val := do
  let ev ← topmostExc
  if ev != .null && ev != .none && ev != value then
    cutContextCycle value 64 ev
    setContext value ev
  return value

/-- Raise an exception value: `_PyErr_SetObject` then `goto error`. -/
def raiseVal {α : Type} (v : Val) : RM α := do
  let e ← setObject v
  throw (.exc e)

/-- `PyErr_Format(PyExc_<cls>, msg)`. -/
def raiseS {α : Type} (cls msg : String) : RM α := do
  raiseVal (← newExc (.cls cls) [.str msg])

def typeError {α : Type} (msg : String) : RM α := raiseS "TypeError" msg
def valueError {α : Type} (msg : String) : RM α := raiseS "ValueError" msg
def runtimeError {α : Type} (msg : String) : RM α := raiseS "RuntimeError" msg

/-- One level of `PyErr_GivenExceptionMatches`: `err` against a non-tuple `exc`. -/
def excMatchesOne (err exc : Val) : RM Bool := do
  let cls ← if ← isExcInstance err then typeOf err else pure err
  if (← isExcClass cls) && (← isExcClass exc) then isSubtype cls exc
  else pure (cls == exc)

/-- `PyTuple_Check(v)`: the items of a tuple, or of an instance of a `tuple` subclass (its
payload); `none` for anything else. -/
def tupleCheckItems? : Val → RM (Option (Array Val))
  | .ref a => do
    match ← getObj a with
    | .tuple items => pure (some items)
    | .inst i =>
      match i.base with
      | .ref b => do
        match ← getObj b with
        | .tuple items => pure (some items)
        | _ => pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- `PyErr_GivenExceptionMatches(err, exc)`, `Python/errors.c:331-370`: `exc` may be a nested
tuple, or an instance of a `tuple` subclass (`PyTuple_Check`, `:338`). The fuel stands for the
`_Py_ReachedRecursionLimitWithMargin` cut-off of `:340-349` (which answers 0); the `except`
clauses only ever pass a flat tuple, since `_PyEval_CheckExceptTypeValid` rejects nesting. -/
def givenMatches (err : Val) : Nat → Val → RM Bool
  | 0, _ => pure false
  | n + 1, exc => do
    match ← tupleCheckItems? exc with
    | some items => items.toList.anyM (givenMatches err n)
    | none => excMatchesOne err exc

/-- Catch `Err.exc` only; deopts and labels pass through. -/
def tryExc {α : Type} (m : RM α) (h : Val → RM α) : RM α := fun rt =>
  match m rt with
  | .error (.exc v) rt' => h v rt'
  | r => r

end PyLean.Bytecode
