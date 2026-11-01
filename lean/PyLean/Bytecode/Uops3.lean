import PyLean.Bytecode.Uops2

/-!
Step rules of `Python/bytecodes.c`, part 3: lines 3121-5210 (`FOR_ITER`, `with`,
method loads, the `CALL` families, function objects, `COPY`/`SWAP`/`BINARY_OP`).
Conventions as in `Uops1.lean`.
-/

namespace PyLean.Bytecode.Uop

open PyLean.Bytecode

/-! ### Lines 3134-3494: `FOR_ITER` -/

/-- `tstate->py_recursion_remaining`. -/
def getRecursionRemaining : RM Int := fun rt => .ok rt.pyRecursionRemaining rt
/-- `tstate->py_recursion_remaining--`. -/
def decRecursionRemaining : RM Unit := fun rt =>
  .ok () { rt with pyRecursionRemaining := rt.pyRecursionRemaining - 1 }

/-- `@3.14.7:3134`. -/
def _SPECIALIZE_FOR_ITER : M Unit := pure ()

/-- `func(iter_o)` with the `_PyErr_Occurred`/`StopIteration` handling of
`@3.14.7:3148-3172`: `none` means the iterator ended normally. -/
def iterStep (e : Env) (it : Val) : RM (Option Val) := do
  if !(← e.om.isIterator it) then
    typeError s!"'{String.ofList ((← tpName it).toList.take 100)}' object is not an iterator"
  tryExc (e.om.iterNext e.ctx it) fun exc => do
    if ← givenMatches exc 8 (.cls "StopIteration") then pure none else throw (.exc exc)

/-- `@3.14.7:3146`. -/
def _FOR_ITER (e : Env) : M Unit := do
  let ins ← peekN 1
  let r ← BM.lift ((iterStep e (ins.headD .null) : RM _) : BM _)
  match r with
  | some v => pushAll [v]
  | none =>
    BM.lift (jumpBy (e.oparg + 1))
    throw .dispatch
/-- `@3.14.7:3205`. -/
def FOR_ITER (e : Env) : M Unit := do _SPECIALIZE_FOR_ITER; _FOR_ITER e
/-- `@3.14.7:3208`. -/
def INSTRUMENTED_FOR_ITER (e : Env) : M Unit := _FOR_ITER e

/-- `@3.14.7:3241`. -/
def _ITER_CHECK_LIST : M Unit := guardTop 1 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .listIter .. => pure false
    | _ => pure true
  | _ => pure true

/-- `@3.14.7:3252`. -/
def _ITER_JUMP_LIST (e : Env) : M Unit := do
  let ins ← peekN 1
  match ins with
  | [.ref a] =>
    match ← BM.lift ((getObj a : RM Obj) : BM Obj) with
    | .listIter seq index =>
      let size ← match seq with
        | some sq => BM.lift do
          match ← (getObj sq : RM Obj) with
          | .list items => pure items.size
          | _ => fault "list iterator over a non-list"
        | none => pure 0
      if seq.isNone || index < 0 || size ≤ index.toNat then
        BM.lift do
          (setObj a (.listIter none (-1)) : RM Unit)
          jumpBy (e.oparg + 1)
        throw .dispatch
    | _ => fault "not a list iterator"
  | _ => fault "not a list iterator"

/-- `@3.14.7:3294`. -/
def _ITER_NEXT_LIST : M Unit := stk 1 2 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .listIter (some sq) index =>
      match ← (getObj sq : RM Obj) with
      | .list items =>
        (setObj a (.listIter (some sq) (index + 1)) : RM Unit)
        pure [.ref a, items.getD index.toNat .null]
      | _ => fault "list iterator over a non-list"
    | _ => fault "not a list iterator"
  | _ => fault "not a list iterator"

/-- `:4006`. -/
def FOR_ITER_LIST (e : Env) : M Unit := do _ITER_CHECK_LIST; _ITER_JUMP_LIST e; _ITER_NEXT_LIST

/-- `@3.14.7:3355`. -/
def _ITER_CHECK_TUPLE : M Unit := guardTop 1 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .tupleIter .. => pure false
    | _ => pure true
  | _ => pure true

/-- `@3.14.7:3363`. -/
def _ITER_JUMP_TUPLE (e : Env) : M Unit := do
  let ins ← peekN 1
  match ins with
  | [.ref a] =>
    match ← BM.lift ((getObj a : RM Obj) : BM Obj) with
    | .tupleIter seq index =>
      let size ← match seq with
        | some sq => BM.lift do
          match ← (getObj sq : RM Obj) with
          | .tuple items => pure items.size
          | _ => fault "tuple iterator over a non-tuple"
        | none => pure 0
      if seq.isNone || size ≤ index.toNat then
        BM.lift do
          (setObj a (.tupleIter none index) : RM Unit)
          jumpBy (e.oparg + 1)
        throw .dispatch
    | _ => fault "not a tuple iterator"
  | _ => fault "not a tuple iterator"

/-- `@3.14.7:3399`. -/
def _ITER_NEXT_TUPLE : M Unit := stk 1 2 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .tupleIter (some sq) index =>
      match ← (getObj sq : RM Obj) with
      | .tuple items =>
        (setObj a (.tupleIter (some sq) (index + 1)) : RM Unit)
        pure [.ref a, items.getD index.toNat .null]
      | _ => fault "tuple iterator over a non-tuple"
    | _ => fault "not a tuple iterator"
  | _ => fault "not a tuple iterator"

/-- `:4047`. -/
def FOR_ITER_TUPLE (e : Env) : M Unit := do _ITER_CHECK_TUPLE; _ITER_JUMP_TUPLE e; _ITER_NEXT_TUPLE

/-- `@3.14.7:3418`. -/
def _ITER_CHECK_RANGE : M Unit := guardTop 1 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .rangeIter .. => pure false
    | _ => pure true
  | _ => pure true

/-- `@3.14.7:3426`. -/
def _ITER_JUMP_RANGE (e : Env) : M Unit := do
  let ins ← peekN 1
  match ins with
  | [.ref a] =>
    match ← BM.lift ((getObj a : RM Obj) : BM Obj) with
    | .rangeIter _ _ len =>
      if len ≤ 0 then
        BM.lift (jumpBy (e.oparg + 1))
        throw .dispatch
    | _ => fault "not a range iterator"
  | _ => fault "not a range iterator"

/-- `@3.14.7:3447`. -/
def _ITER_NEXT_RANGE : M Unit := stk 1 2 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .rangeIter start step len =>
      (setObj a (.rangeIter (start + step) step (len - 1)) : RM Unit)
      pure [.ref a, .int start]
    | _ => fault "not a range iterator"
  | _ => fault "not a range iterator"

/-- `:4097`. -/
def FOR_ITER_RANGE (e : Env) : M Unit := do _ITER_CHECK_RANGE; _ITER_JUMP_RANGE e; _ITER_NEXT_RANGE

/-- `@3.14.7:3468`. -/
def _FOR_ITER_GEN_FRAME (e : Env) : M Frame := do
  let ins ← peekN 1
  let r ← BM.lift ((resumableGen false (ins.headD .null) : RM _) : BM _)
  match r with
  | some (a, g) =>
    BM.lift do
      let gf ← (genEnter a g .none : RM Frame)
      setReturnOffset (instrSize e.opcode + e.oparg)
      pure gf
  | none => throw .deopt

/-- `:4118`. -/
def FOR_ITER_GEN (e : Env) : M Unit := do
  _CHECK_PEP_523
  let gf ← _FOR_ITER_GEN_FRAME e
  _PUSH_FRAME gf

/-! ### Lines 3496-3592: `with` and exceptions -/

/-- `_Py_SpecialMethods[oparg].name`, `Python/ceval.c:375`. -/
def specialName : Nat → String
  | 0 => "__enter__"
  | 1 => "__exit__"
  | 2 => "__aenter__"
  | _ => "__aexit__"

/-- `_Py_SpecialMethods[oparg].error`, `.error_suggestion`, `Python/ceval.c:375-422`. -/
def specialError (oparg : Nat) (t : String) (suggest : Bool) : String :=
  match oparg, suggest with
  | 0, false => s!"'{t}' object does not support the context manager protocol (missed __enter__ method)"
  | 0, true => s!"'{t}' object does not support the context manager protocol (missed __enter__ method) but it supports the asynchronous context manager protocol. Did you mean to use 'async with'?"
  | 1, false => s!"'{t}' object does not support the context manager protocol (missed __exit__ method)"
  | 1, true => s!"'{t}' object does not support the context manager protocol (missed __exit__ method) but it supports the asynchronous context manager protocol. Did you mean to use 'async with'?"
  | 2, false => s!"'{t}' object does not support the asynchronous context manager protocol (missed __aenter__ method)"
  | 2, true => s!"'{t}' object does not support the asynchronous context manager protocol (missed __aenter__ method) but it supports the context manager protocol. Did you mean to use 'with'?"
  | _, false => s!"'{t}' object does not support the asynchronous context manager protocol (missed __aexit__ method)"
  | _, true => s!"'{t}' object does not support the asynchronous context manager protocol (missed __aexit__ method) but it supports the context manager protocol. Did you mean to use 'with'?"

/-- `type_has_special_method`, `Python/ceval.c:3742-3749`. The binding test
`tp_descr_get != NULL` holds for the functions the model puts in a class. -/
def typeHasSpecial (e : Env) (tp : Val) (name : String) : RM Bool := do
  return (← e.om.typeLookup tp name).isSome

/-- `_PyEval_SpecialMethodCanSuggest`, `Python/ceval.c:3751-3768`. -/
def specialCanSuggest (e : Env) (self : Val) (oparg : Nat) : RM Bool := do
  let tp ← typeOf self
  if oparg ≤ 1 then
    return (← typeHasSpecial e tp "__aenter__") && (← typeHasSpecial e tp "__aexit__")
  else
    return (← typeHasSpecial e tp "__enter__") && (← typeHasSpecial e tp "__exit__")

/-- `:3489`, `:3495`, `:3512`: `_INSERT_NULL` + `_LOAD_SPECIAL`. -/
def LOAD_SPECIAL (e : Env) : M Unit := stkK 1 2 fun
  | [owner] => do
    match ← e.om.lookupSpecial e.ctx owner (specialName e.oparg) with
    | some (m, s) => pure [m, s]
    | none =>
      let sug ← (specialCanSuggest e owner e.oparg : RM Bool)
      let t ← (tpName owner : RM String)
      (typeError (specialError e.oparg t sug) : RM _)
  | _ => fault "arity"

/-- `:3516`. -/
def WITH_EXCEPT_START (e : Env) : M Unit := do
  let ins ← peekN 5
  match ins with
  | [exitFunc, exitSelf, _, _, val] =>
    let res ← BM.lift do
      let exc ← (typeOf val : RM Val)
      let args := if exitSelf != .null then [exitSelf, exc, val, .none] else [exc, val, .none]
      e.om.call e.ctx exitFunc args []
    pushAll [res]
  | _ => fault "arity"

/-- `:3572`. -/
def PUSH_EXC_INFO : M Unit := stk 1 2 fun
  | [exc] => do
    let cur ← (getExcInfoTop : RM Val)
    (setExcInfoTop exc : RM Unit)
    pure [if cur != .null then cur else .none, exc]
  | _ => fault "arity"

/-! ### Lines 3594-3695: method loads -/

/-- `:3587`. -/
def _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT : M Unit := pure ()

/-- `:3594`. The version check says "no instance can shadow `name`"; the model
states that directly on the instance dict it has. -/
def _GUARD_KEYS_VERSION (e : Env) : M Unit := guardTop 1 fun
  | [o] => do
    match ← (instOf o : RM _) with
    | some (_, i) =>
      if i.dict == .null then pure false
      else
        let name ← getName e (e.oparg >>> 1)
        return (← (dictGetStr i.dict name : RM _)).isSome
    | none => pure false
  | _ => fault "arity"

/-- `@3.14.7:3608`. -/
def _LOAD_ATTR_METHOD_WITH_VALUES (e : Env) : M Unit := stk 1 2 fun
  | [o] => pure [(e.cache[1]?).getD .null, o]
  | _ => fault "arity"
/-- `:3612`. -/
def LOAD_ATTR_METHOD_WITH_VALUES (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT; _GUARD_KEYS_VERSION e
  _LOAD_ATTR_METHOD_WITH_VALUES e
/-- `:3619`. -/
def _LOAD_ATTR_METHOD_NO_DICT (e : Env) : M Unit := stk 1 2 fun
  | [o] => pure [(e.cache[1]?).getD .null, o]
  | _ => fault "arity"
/-- `:3631`. -/
def LOAD_ATTR_METHOD_NO_DICT (e : Env) : M Unit := do _GUARD_TYPE_VERSION e; _LOAD_ATTR_METHOD_NO_DICT e
/-- `:3645`. -/
def _LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES (e : Env) : M Unit := stk 1 1 fun _ => pure [(e.cache[1]?).getD .null]
/-- `:3653`. -/
def LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT; _GUARD_KEYS_VERSION e
  _LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES e
/-- `@3.14.7:3658`. -/
def _LOAD_ATTR_NONDESCRIPTOR_NO_DICT (e : Env) : M Unit := stk 1 1 fun _ => pure [(e.cache[1]?).getD .null]
/-- `:3669`. -/
def LOAD_ATTR_NONDESCRIPTOR_NO_DICT (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _LOAD_ATTR_NONDESCRIPTOR_NO_DICT e
/-- `:3675`: the dict must not have been created yet. -/
def _CHECK_ATTR_METHOD_LAZY_DICT : M Unit := guardTop 1 fun
  | [o] => do
    match ← (instOf o : RM _) with
    | some (_, i) => pure (i.dict != .null)
    | none => pure true
  | _ => fault "arity"
/-- `:3682`. -/
def _LOAD_ATTR_METHOD_LAZY_DICT (e : Env) : M Unit := stk 1 2 fun
  | [o] => pure [(e.cache[1]?).getD .null, o]
  | _ => fault "arity"
/-- `:3694`. -/
def LOAD_ATTR_METHOD_LAZY_DICT (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _CHECK_ATTR_METHOD_LAZY_DICT; _LOAD_ATTR_METHOD_LAZY_DICT e

/-! ### Lines 3722-4050: `CALL` -/

/-- `:3763`. -/
def _SPECIALIZE_CALL : M Unit := pure ()

/-- `Py_TYPE(callable) == &PyMethod_Type`: `(im_func, im_self)`. -/
def methodParts : Val → RM (Option (Val × Val))
  | .ref a => do
    match ← getObj a with
    | .method f s => pure (some (f, s))
    | _ => pure none
  | _ => pure none

/-- `:3775`. -/
def _MAYBE_EXPAND_METHOD (e : Env) : M Unit := stk (e.oparg + 2) (e.oparg + 2) fun
  | callable :: self :: args => do
    match ← (methodParts callable : RM _) with
    | some (f, s) => if self == .null then pure (f :: s :: args) else pure (callable :: self :: args)
    | none => pure (callable :: self :: args)
  | _ => fault "arity"

/-- `self_or_null` + args as one array, `:3792-3797`. -/
def withSelf (self : Val) (args : List Val) : List Val :=
  if self != .null then self :: args else args

/-- `_PyEvalFramePushAndInit` from a call site. -/
def pushInit (e : Env) (callable : Val) (args : List Val) (kw : List String) : BM Frame := do
  let func ← (getFunc callable : RM _)
  let co ← (getCodeR e.P func.code : RM _)
  (framePushAndInit e.P callable (localsFor co func) args kw : RM _)

/-- `:3788`. -/
def _DO_CALL (e : Env) : M Unit := do
  let ins ← peekN (e.oparg + 2)
  match ins with
  | callable :: self :: args =>
    if ← BM.lift ((isFunction callable : RM Bool) : BM Bool) then
      let _ ← popN (e.oparg + 2)
      let nf ← BM.lift (pushInit e callable (withSelf self args) [])
      BM.lift (setReturnOffset (instrSize e.opcode))
      dispatchInlined nf
    else
      stk (e.oparg + 2) 1 fun _ => do
        pure [← e.om.call e.ctx callable (withSelf self args) []]
  | _ => fault "arity"

/-- `:3856`. -/
def _MONITOR_CALL : M Unit := pure ()
/-- `:3877`. -/
def CALL (e : Env) : M Unit := do _SPECIALIZE_CALL; _MAYBE_EXPAND_METHOD e; _DO_CALL e; _CHECK_PERIODIC
/-- `:3878`. -/
def INSTRUMENTED_CALL (e : Env) : M Unit := do
  _MAYBE_EXPAND_METHOD e; _MONITOR_CALL; _DO_CALL e; _CHECK_PERIODIC

/-- `:3880`. -/
def _PY_FRAME_GENERAL (e : Env) : M Frame := do
  let ins ← popN (e.oparg + 2)
  match ins with
  | callable :: self :: args => BM.lift (pushInit e callable (withSelf self args) [])
  | _ => fault "arity"

/-- `func_version` of the function at depth `d` below the top. -/
def funcVersionAt (d : Nat) (e : Env) (bad : Val → BM Bool) : M Unit :=
  guardTop (d + 1) fun
    | c :: _ => do
      if ← bad c then pure true
      else
        let f ← (getFunc c : RM _)
        pure (f.version != cacheNat e 0)
    | _ => fault "arity"

/-- `:3905`. -/
def _CHECK_FUNCTION_VERSION (e : Env) : M Unit :=
  funcVersionAt (e.oparg + 1) e fun c => do return !(← (isFunction c : RM Bool))
/-- `:3912`: tier 2 only; the same check. -/
def _CHECK_FUNCTION_VERSION_INLINE (e : Env) : M Unit := _CHECK_FUNCTION_VERSION e

/-- `:4035`. -/
def _CHECK_RECURSION_REMAINING : M Unit := guardTop 0 fun _ => do
  pure ((← (getRecursionRemaining : RM Int)) ≤ 1)

/-- `:3918`. -/
def CALL_PY_GENERAL (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_FUNCTION_VERSION e
  _CHECK_RECURSION_REMAINING
  let nf ← _PY_FRAME_GENERAL e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:3927`. -/
def _CHECK_METHOD_VERSION (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: n :: _ => do
    match ← (methodParts c : RM _) with
    | some (f, _) =>
      if !(← (isFunction f : RM Bool)) then pure true
      else
        let fo ← (getFunc f : RM _)
        pure (fo.version != cacheNat e 0 || n != .null)
    | none => pure true
  | _ => fault "arity"

/-- `:3937`. -/
def _EXPAND_METHOD (e : Env) : M Unit := stk (e.oparg + 2) (e.oparg + 2) fun
  | c :: _ :: args => do
    match ← (methodParts c : RM _) with
    | some (f, s) => pure (f :: s :: args)
    | none => fault "not a method"
  | _ => fault "arity"

/-- `:3948`. -/
def CALL_BOUND_METHOD_GENERAL (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_METHOD_VERSION e
  _EXPAND_METHOD e
  _CHECK_RECURSION_REMAINING
  let nf ← _PY_FRAME_GENERAL e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:3959`. -/
def _CHECK_IS_NOT_PY_CALLABLE (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: _ => do
    if ← (isFunction c : RM Bool) then pure true
    else return (← (methodParts c : RM _)).isSome
  | _ => fault "arity"

/-- The common shape of every non-Python call: `:3965`, and the `_CALL_BUILTIN_*`
and `_CALL_METHOD_DESCRIPTOR_*` bodies once the guards have passed. -/
def callNonPy (e : Env) : M Unit := stk (e.oparg + 2) 1 fun
  | callable :: self :: args => do
    pure [← e.om.call e.ctx callable (withSelf self args) []]
  | _ => fault "arity"

/-- `:3965`. -/
def _CALL_NON_PY_GENERAL (e : Env) : M Unit := callNonPy e
/-- `:3994`. -/
def CALL_NON_PY_GENERAL (e : Env) : M Unit := do
  _CHECK_IS_NOT_PY_CALLABLE e; _CALL_NON_PY_GENERAL e; _CHECK_PERIODIC

/-- `:4001`. -/
def _CHECK_CALL_BOUND_METHOD_EXACT_ARGS (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: n :: _ => do
    if n != .null then pure true
    else return (← (methodParts c : RM _)).isNone
  | _ => fault "arity"
/-- `:4006`. -/
def _INIT_CALL_BOUND_METHOD_EXACT_ARGS (e : Env) : M Unit := _EXPAND_METHOD e

/-- `:4020`. -/
def _CHECK_FUNCTION_EXACT_ARGS (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: s :: _ => do
    let f ← (getFunc c : RM _)
    let co ← (getCodeR e.P f.code : RM _)
    pure (co.argcount != e.oparg + (if s != .null then 1 else 0))
  | _ => fault "arity"
/-- `:4028`. -/
def _CHECK_STACK_SPACE : M Unit := guardTop 0 fun _ => do return !(← hasStackSpace)

/-- `:4039`. -/
def _INIT_CALL_PY_EXACT_ARGS (e : Env) : M Frame := do
  let ins ← popN (e.oparg + 2)
  match ins with
  | callable :: self :: args => BM.lift do
    let func ← (getFunc callable : RM _)
    let co ← (getCodeR e.P func.code : RM _)
    let nf := frameInitialize co func.code func callable .null
    let fast := (withSelf self args).zipIdx.foldl (fun f p => f.setIfInBounds p.2 p.1) nf.fast
    pure { nf with fast := fast }
  | _ => fault "arity"

/-- `:4068`. -/
def CALL_BOUND_METHOD_EXACT_ARGS (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_CALL_BOUND_METHOD_EXACT_ARGS e
  _INIT_CALL_BOUND_METHOD_EXACT_ARGS e
  _CHECK_FUNCTION_VERSION e
  _CHECK_FUNCTION_EXACT_ARGS e
  _CHECK_STACK_SPACE
  _CHECK_RECURSION_REMAINING
  let nf ← _INIT_CALL_PY_EXACT_ARGS e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:4082`. -/
def CALL_PY_EXACT_ARGS (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_FUNCTION_VERSION e
  _CHECK_FUNCTION_EXACT_ARGS e
  _CHECK_STACK_SPACE
  _CHECK_RECURSION_REMAINING
  let nf ← _INIT_CALL_PY_EXACT_ARGS e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-! ### Lines 4052-4372: calls of known builtins -/

/-- `:4093`. -/
def _GUARD_NOS_NULL : M Unit := guardTop 2 fun
  | [n, _] => pure (n != .null)
  | _ => fault "arity"
/-- Guards on the callable below `self_or_null` and one argument. -/
def guardCallable (w : Val) : M Unit := guardTop 3 fun
  | [c, _, _] => pure (c != w)
  | _ => fault "arity"
/-- `:4097`. -/
def _GUARD_CALLABLE_TYPE_1 : M Unit := guardCallable (.cls "type")
/-- `:4102`. -/
def _CALL_TYPE_1 : M Unit := stk 3 1 fun
  | [_, _, a] => do pure [← (typeOf a : RM Val)]
  | _ => fault "arity"
/-- `:4115`. -/
def CALL_TYPE_1 : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_TYPE_1; _CALL_TYPE_1
/-- `:4122`. -/
def _GUARD_CALLABLE_STR_1 : M Unit := guardCallable (.cls "str")
/-- `:4127`. -/
def _CALL_STR_1 (e : Env) : M Unit := stk 3 1 fun
  | [_, _, a] => do pure [← e.om.str e.ctx a]
  | _ => fault "arity"
/-- `:4142`. -/
def CALL_STR_1 (e : Env) : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_STR_1; _CALL_STR_1 e; _CHECK_PERIODIC
/-- `:4150`. -/
def _GUARD_CALLABLE_TUPLE_1 : M Unit := guardCallable (.cls "tuple")
/-- `:4155`: `PySequence_Tuple` is what `tuple(x)` calls. -/
def _CALL_TUPLE_1 (e : Env) : M Unit := stk 3 1 fun
  | [c, _, a] => do pure [← e.om.call e.ctx c [a] []]
  | _ => fault "arity"
/-- `:4170`. -/
def CALL_TUPLE_1 (e : Env) : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_TUPLE_1; _CALL_TUPLE_1 e; _CHECK_PERIODIC

/-- `:4178`: `(callable, self_or_null, args -- init, self, args)`. `cache[1]` is
`cls->_spec_cache.init`. -/
def _CHECK_AND_ALLOCATE_OBJECT (e : Env) : M Unit := stk (e.oparg + 2) (e.oparg + 2) fun
  | c :: n :: args => do
    if n != .null then throw .deopt
    match ← (classVersion c : RM _) with
    | none => throw .deopt
    | some v =>
      if v != cacheNat e 0 then throw .deopt
      deoptIf !(← hasStackSpace)
      let self ← (alloc (.inst { cls := c }) : RM Val)
      pure ((e.cache[1]?).getD .null :: self :: args)
  | _ => fault "arity"

/-- The `_Py_InitCleanup` shim of `Python/specialize.c`: reserved `Program` index 1. -/
def initCleanupIdx : Nat := 1

/-- `:4038`. -/
def _CREATE_INIT_FRAME (e : Env) : M Frame := do
  let ins ← popN (e.oparg + 2)
  match ins with
  | init :: self :: args => do
    -- `frame->return_offset` belongs to the caller
    BM.lift (setReturnOffset (1 + 3))
    let shim : Frame := { code := initCleanupIdx, stack := [self], owner := .thread }
    enterFrame shim
    let nf ← BM.lift do
      (framePushAndInit e.P init .null (self :: args) [] : RM _)
    BM.lift (decRecursionRemaining : RM Unit)
    pure nf
  | _ => fault "arity"

/-- `:4063`. -/
def CALL_ALLOC_AND_ENTER_INIT (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_AND_ALLOCATE_OBJECT e
  let nf ← _CREATE_INIT_FRAME e
  _PUSH_FRAME nf

/-- `:4070`. -/
def EXIT_INIT_CHECK : M Unit := stkK 1 0 fun
  | [v] => do
    if v != .none then
      let t ← (tpName v : RM String)
      (typeError s!"__init__() should return None, not '{trunc200 t}'" : RM _)
    pure []
  | _ => fault "arity"

/-- `(callable, self_or_null, args)` split, for guards of the builtin calls. -/
def builtinGuard (e : Env) (bad : Val → List Val → BM Bool) : M Unit :=
  guardTop (e.oparg + 2) fun
    | c :: s :: args => bad c (withSelf s args)
    | _ => fault "arity"

/-- `:4080`: `tp->tp_vectorcall == NULL` deopts, `specialCalls` decides. -/
def _CALL_BUILTIN_CLASS (e : Env) : M Unit := do
  builtinGuard e fun c _ => do return !(← (isType c : RM Bool))
  callNonPy e
/-- `:4104`. -/
def CALL_BUILTIN_CLASS (e : Env) : M Unit := do _CALL_BUILTIN_CLASS e; _CHECK_PERIODIC
/-- `:4110`. -/
def _CALL_BUILTIN_O (e : Env) : M Unit := do
  builtinGuard e fun c args => pure (args.length != 1 || !(match c with | .builtin _ => true | _ => false))
  callNonPy e
/-- `:4139`. -/
def CALL_BUILTIN_O (e : Env) : M Unit := do _CALL_BUILTIN_O e; _CHECK_PERIODIC
/-- `:4145`. -/
def _CALL_BUILTIN_FAST (e : Env) : M Unit := do
  builtinGuard e fun c _ => pure !(match c with | .builtin _ => true | _ => false)
  callNonPy e
/-- `:4176`. -/
def CALL_BUILTIN_FAST (e : Env) : M Unit := do _CALL_BUILTIN_FAST e; _CHECK_PERIODIC
/-- `:4182`. -/
def _CALL_BUILTIN_FAST_WITH_KEYWORDS (e : Env) : M Unit := _CALL_BUILTIN_FAST e
/-- `:4212`. -/
def CALL_BUILTIN_FAST_WITH_KEYWORDS (e : Env) : M Unit := do _CALL_BUILTIN_FAST_WITH_KEYWORDS e; _CHECK_PERIODIC
/-- `:4225`. -/
def _GUARD_CALLABLE_LEN : M Unit := guardCallable (.builtin "len")
/-- `:4231`. -/
def _CALL_LEN (e : Env) : M Unit := stkK 3 1 fun
  | [_, _, a] => do pure [.int (← e.om.length e.ctx a)]
  | _ => fault "arity"
/-- `:4218`. -/
def CALL_LEN (e : Env) : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_LEN; _CALL_LEN e
/-- `:4251`. -/
def CALL_ISINSTANCE (e : Env) : M Unit := do
  builtinGuard e fun c args => pure (args.length != 2 || c != .builtin "isinstance")
  stkK (e.oparg + 2) 1 fun
    | _ :: s :: args => do
      match withSelf s args with
      | [i, c] => pure [.bool (← e.om.isInstance e.ctx i c)]
      | _ => fault "arity"
    | _ => fault "arity"
/-- `:4277`. -/
def CALL_LIST_APPEND : M Unit := do
  guardTop 3 fun
    | [c, s, _] => do
      if c != .methDescr "list" "append" || s == .null then pure true
      else return !(← (isExactList s : RM Bool))
    | _ => fault "arity"
  stk 3 0 fun
    | [_, s, a] => do
      (listAppend s a : RM Unit)
      jumpBy 1
      pure []
    | _ => fault "arity"

/-- The receiver guard of `_CALL_METHOD_DESCRIPTOR_*`. -/
def methDescrGuard (e : Env) (min : Nat) : M Unit :=
  builtinGuard e fun c args => do
    match c, args with
    | .methDescr tp _, a :: _ =>
      if args.length < min then pure true
      else return (← (tpName a : RM String)) != tp
    | _, _ => pure true
/-- `:4301`. -/
def _CALL_METHOD_DESCRIPTOR_O (e : Env) : M Unit := do methDescrGuard e 2; callNonPy e
/-- `:4334`. -/
def CALL_METHOD_DESCRIPTOR_O (e : Env) : M Unit := do _CALL_METHOD_DESCRIPTOR_O e; _CHECK_PERIODIC
/-- `:4340`. -/
def _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS (e : Env) : M Unit := do methDescrGuard e 1; callNonPy e
/-- `:4376`. -/
def CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS (e : Env) : M Unit := do
  _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS e; _CHECK_PERIODIC
/-- `:4382`. -/
def _CALL_METHOD_DESCRIPTOR_NOARGS (e : Env) : M Unit := do methDescrGuard e 1; callNonPy e
/-- `:4414`. -/
def CALL_METHOD_DESCRIPTOR_NOARGS (e : Env) : M Unit := do _CALL_METHOD_DESCRIPTOR_NOARGS e; _CHECK_PERIODIC
/-- `:4420`. -/
def _CALL_METHOD_DESCRIPTOR_FAST (e : Env) : M Unit := do methDescrGuard e 1; callNonPy e
/-- `:4455`. -/
def CALL_METHOD_DESCRIPTOR_FAST (e : Env) : M Unit := do _CALL_METHOD_DESCRIPTOR_FAST e; _CHECK_PERIODIC

/-! ### Lines 4591-4840: `CALL_KW` -/

/-- `:4468`. -/
def _MONITOR_CALL_KW : M Unit := pure ()
/-- `:4487`. -/
def _MAYBE_EXPAND_METHOD_KW (e : Env) : M Unit := stk (e.oparg + 3) (e.oparg + 3) fun
  | callable :: self :: rest => do
    match ← (methodParts callable : RM _) with
    | some (f, s) => if self == .null then pure (f :: s :: rest) else pure (callable :: self :: rest)
    | none => pure (callable :: self :: rest)
  | _ => fault "arity"

/-- The names in a `kwnames` tuple. -/
def kwNames (t : Val) : RM (List String) := do
  let items ← tupleItems t
  pure (items.toList.map fun
    | .str s => s
    | _ => "")

/-- `:4499`. -/
def _DO_CALL_KW (e : Env) : M Unit := do
  let ins ← peekN (e.oparg + 3)
  match ins with
  | callable :: self :: rest =>
    let args := rest.dropLast
    let kwv := rest.getLastD .null
    let kw ← BM.lift ((kwNames kwv : RM _) : BM _)
    if ← BM.lift ((isFunction callable : RM Bool) : BM Bool) then
      let _ ← popN (e.oparg + 3)
      let nf ← BM.lift (pushInit e callable (withSelf self args) kw)
      BM.lift (setReturnOffset (instrSize e.opcode))
      dispatchInlined nf
    else
      stk (e.oparg + 3) 1 fun _ => do
        pure [← e.om.call e.ctx callable (withSelf self args) kw]
  | _ => fault "arity"

/-- `:4570`. -/
def _PY_FRAME_KW (e : Env) : M Frame := do
  let ins ← popN (e.oparg + 3)
  match ins with
  | callable :: self :: rest =>
    let args := rest.dropLast
    let kw ← BM.lift ((kwNames (rest.getLastD .null) : RM _) : BM _)
    BM.lift (pushInit e callable (withSelf self args) kw)
  | _ => fault "arity"

/-- `:4600`. -/
def _CHECK_FUNCTION_VERSION_KW (e : Env) : M Unit :=
  funcVersionAt (e.oparg + 2) e fun c => do return !(← (isFunction c : RM Bool))
/-- `:4607`. -/
def CALL_KW_PY (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_FUNCTION_VERSION_KW e
  _CHECK_RECURSION_REMAINING
  let nf ← _PY_FRAME_KW e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf
/-- `:4616`. -/
def _CHECK_METHOD_VERSION_KW (e : Env) : M Unit := guardTop (e.oparg + 3) fun
  | c :: n :: _ => do
    match ← (methodParts c : RM _) with
    | some (f, _) =>
      if !(← (isFunction f : RM Bool)) then pure true
      else
        let fo ← (getFunc f : RM _)
        pure (fo.version != cacheNat e 0 || n != .null)
    | none => pure true
  | _ => fault "arity"
/-- `:4626`. -/
def _EXPAND_METHOD_KW (e : Env) : M Unit := stk (e.oparg + 3) (e.oparg + 3) fun
  | c :: _ :: rest => do
    match ← (methodParts c : RM _) with
    | some (f, s) => pure (f :: s :: rest)
    | none => fault "not a method"
  | _ => fault "arity"
/-- `:4637`. -/
def CALL_KW_BOUND_METHOD (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_METHOD_VERSION_KW e
  _EXPAND_METHOD_KW e
  let nf ← _PY_FRAME_KW e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf
/-- `:4647`. -/
def _SPECIALIZE_CALL_KW : M Unit := pure ()
/-- `:4659`. -/
def CALL_KW (e : Env) : M Unit := do _SPECIALIZE_CALL_KW; _MAYBE_EXPAND_METHOD_KW e; _DO_CALL_KW e
/-- `:4665`. -/
def INSTRUMENTED_CALL_KW (e : Env) : M Unit := do _MAYBE_EXPAND_METHOD_KW e; _MONITOR_CALL_KW; _DO_CALL_KW e
/-- `:4672`. -/
def _CHECK_IS_NOT_PY_CALLABLE_KW (e : Env) : M Unit := guardTop (e.oparg + 3) fun
  | c :: _ => do
    if ← (isFunction c : RM Bool) then pure true
    else return (← (methodParts c : RM _)).isSome
  | _ => fault "arity"
/-- `:4679`. -/
def _CALL_KW_NON_PY (e : Env) : M Unit := stk (e.oparg + 3) 1 fun
  | callable :: self :: rest => do
    let kw ← (kwNames (rest.getLastD .null) : RM _)
    pure [← e.om.call e.ctx callable (withSelf self rest.dropLast) kw]
  | _ => fault "arity"
/-- `:4711`. -/
def CALL_KW_NON_PY (e : Env) : M Unit := do
  _CHECK_IS_NOT_PY_CALLABLE_KW e; _CALL_KW_NON_PY e; _CHECK_PERIODIC

/-! ### Lines 4841-5087: `CALL_FUNCTION_EX`, functions, formatting -/

/-- `_Py_Check_ArgsIterable`, `Python/ceval.c:3402-3412`. -/
def checkArgsIterable (e : Env) (func args : Val) : RM Unit := do
  if !(← e.om.isIterable args) then
    let fs ← functionStr e func
    typeError s!"{fs} argument after * must be an iterable, not {trunc200 (← tpName args)}"

/-- `:4882`. -/
def _MAKE_CALLARGS_A_TUPLE (e : Env) : M Unit := stkK 4 4 fun
  | [f, n, ca, kw] => do
    if ← (isExactTuple ca : RM Bool) then pure [f, n, ca, kw]
    else
      (checkArgsIterable e f ca : RM Unit)
      let t ← e.om.call e.ctx (.cls "tuple") [ca] []
      pure [f, n, t, kw]
  | _ => fault "arity"

/-- `_PyStack_UnpackDict` (`Objects/call.c`): names and values of a kwargs dict. -/
def unpackKwargs : Val → RM (List String × List Val)
  | .null => pure ([], [])
  | dv => do
    let d ← getDict dv
    let names ← d.entries.toList.mapM fun en =>
      match en.key with
      | .str s => pure s
      | _ => typeError "keywords must be strings"
    pure (names, d.entries.toList.map (·.value))

/-- `:4836`. -/
def _DO_CALL_FUNCTION_EX (e : Env) : M Unit := do
  let ins ← peekN 4
  match ins with
  | [func, _, callargs, kwargs] =>
    if ← BM.lift ((isFunction func : RM Bool) : BM Bool) then
      let _ ← popN 4
      let nf ← BM.lift do
        let (kw, kwvals) ← (unpackKwargs kwargs : RM _)
        let pos ← (tupleItems callargs : RM _)
        pushInit e func (pos.toList ++ kwvals) kw
      BM.lift (setReturnOffset 1)
      dispatchInlined nf
    else
      stk 4 1 fun _ => do
        let (kw, kwvals) ← (unpackKwargs kwargs : RM _)
        let pos ← (tupleItems callargs : RM _)
        pure [← e.om.call e.ctx func (pos.toList ++ kwvals) kw]
  | _ => fault "arity"

/-- `:4915`. -/
def CALL_FUNCTION_EX (e : Env) : M Unit := do
  _MAKE_CALLARGS_A_TUPLE e; _DO_CALL_FUNCTION_EX e; _CHECK_PERIODIC
/-- `:4920`. -/
def INSTRUMENTED_CALL_FUNCTION_EX (e : Env) : M Unit := CALL_FUNCTION_EX e

/-- `:4925`. -/
def MAKE_FUNCTION (e : Env) : M Unit := stk 1 1 fun
  | [.code i] => do
    let f ← getFrame
    let co ← (getCodeR e.P i : RM _)
    pure [← (alloc (.func { code := i, globals := f.globals, builtins := f.builtins,
                            name := co.name, qualname := co.qualname,
                            version := co.version }) : RM Val)]
  | _ => fault "MAKE_FUNCTION without a code object"

/-- `:4939`. -/
def SET_FUNCTION_ATTRIBUTE (e : Env) : M Unit := stk 2 1 fun
  | [attr, .ref a] => do
    match ← (getObj a : RM Obj) with
    | .func f =>
      let f' := match e.oparg with
        | 0x01 => { f with defaults := attr }
        | 0x02 => { f with kwdefaults := attr }
        | 0x04 => { f with annotations := attr }
        | 0x08 => { f with closure := attr }
        | _ => { f with annotate := attr }
      (setObj a (.func f') : RM Unit)
      pure [.ref a]
    | _ => fault "not a function"
  | _ => fault "not a function"

/-- `_Py_MakeCoro`'s choice of type, `Objects/genobject.c`. -/
def genKindOfFlags (flags : Nat) : GenKind :=
  if flagSet flags coCoroutine then .coro
  else if flagSet flags coAsyncGenerator then .asyncGen
  else .gen

/-- `:5181`. -/
def RETURN_GENERATOR (e : Env) : M Unit := do
  let s ← (get : M St)
  let f := s.regs.frame
  let (gen) ← BM.lift do
    let func ← (getFunc f.funcobj : RM _)
    let co ← getCode e.P
    let gv ← (alloc (.gen { kind := genKindOfFlags co.flags, name := func.name,
                            qualname := func.qualname }) : RM Val)
    match gv with
    | .ref a =>
      let gf := { f with instrPtr := f.instrPtr + 1, owner := .generator a, stack := s.stack }
      (setObj a (.gen { kind := genKindOfFlags co.flags, frame := gf, frameState := -3,
                        name := func.name, qualname := func.qualname }) : RM Unit)
      pure gv
    | _ => fault "alloc"
  BM.lift (leaveRecursivePy : RM Unit)
  popToPrevious
  BM.lift do loadIp (← getFrame).returnOffset
  pushAll [gen]

/-- `:5204`. -/
def BUILD_SLICE (e : Env) : M Unit := stk e.oparg 1 fun args => do
  let start := args.getD 0 .null
  let stop := args.getD 1 .null
  let step := if e.oparg == 3 then args.getD 2 .null else .none
  pure [← (alloc (.slice start stop step) : RM Val)]
/-- `:5214`. -/
def CONVERT_VALUE (e : Env) : M Unit := stk 1 1 fun
  | [v] => do
    match e.oparg with
    | 1 => pure [← e.om.str e.ctx v]
    | 2 => pure [← e.om.repr e.ctx v]
    | 3 => pure [← e.om.ascii e.ctx v]
    | _ => fault "bad conversion"
  | _ => fault "arity"
/-- `:5224`. -/
def FORMAT_SIMPLE (e : Env) : M Unit := stk 1 1 fun
  | [.str s] => pure [.str s]
  | [v] => do pure [← e.om.format e.ctx v .null]
  | _ => fault "arity"
/-- `:5240`. -/
def FORMAT_WITH_SPEC (e : Env) : M Unit := stk 2 1 fun
  | [v, f] => do pure [← e.om.format e.ctx v f]
  | _ => fault "arity"
/-- `:5247`. -/
def COPY (e : Env) : M Unit := stk e.oparg (e.oparg + 1) fun ins => pure (ins ++ [ins.headD .null])
/-- `:5252`. -/
def _SPECIALIZE_BINARY_OP : M Unit := pure ()
/-- `:5266`. -/
def _BINARY_OP (e : Env) : M Unit := stkK 2 1 fun
  | [l, r] => do pure [← e.om.binaryOp e.ctx e.oparg l r]
  | _ => fault "arity"
/-- `:5279`. -/
def BINARY_OP (e : Env) : M Unit := do _SPECIALIZE_BINARY_OP; _BINARY_OP e
/-- `:5281`. -/
def SWAP (e : Env) : M Unit := stk e.oparg e.oparg fun
  | [] => fault "SWAP 0"
  | b :: rest => pure (rest.getLastD b :: rest.dropLast ++ [b])

/-- Lines 5132-5192: without a registered tool every instrumented jump is the
plain one. -/
def INSTRUMENTED_JUMP_FORWARD (e : Env) : M Unit := JUMP_FORWARD e
/-- `:5336`. -/
def _MONITOR_JUMP_BACKWARD (e : Env) : M Unit := JUMP_BACKWARD_NO_INTERRUPT e
/-- `:5340`. -/
def INSTRUMENTED_NOT_TAKEN : M Unit := NOP
/-- `:5345`. -/
def INSTRUMENTED_JUMP_BACKWARD (e : Env) : M Unit := do _CHECK_PERIODIC; _MONITOR_JUMP_BACKWARD e
/-- `:5350`. -/
def INSTRUMENTED_POP_JUMP_IF_TRUE (e : Env) : M Unit := POP_JUMP_IF_TRUE e
/-- `:5360`. -/
def INSTRUMENTED_POP_JUMP_IF_FALSE (e : Env) : M Unit := POP_JUMP_IF_FALSE e
/-- `:5370`. -/
def INSTRUMENTED_POP_JUMP_IF_NONE (e : Env) : M Unit := POP_JUMP_IF_NONE e
/-- `:5382`. -/
def INSTRUMENTED_POP_JUMP_IF_NOT_NONE (e : Env) : M Unit := POP_JUMP_IF_NOT_NONE e

end PyLean.Bytecode.Uop
