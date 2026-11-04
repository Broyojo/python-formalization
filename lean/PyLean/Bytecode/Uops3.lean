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

/-- `:3798`. -/
def _SPECIALIZE_FOR_ITER : M Unit := pure ()

/-- `:3810`: `(iter, null_or_index -- iter, null_or_index, next)`. On exhaustion both slots
stay and the jump skips `END_FOR`, so the `POP_ITER` at the target takes them. -/
def _FOR_ITER (e : Env) : M Unit := do
  let ins ← peekN 2
  match ins with
  | [iter, index] =>
    match ← BM.lift ((virtualNext e iter index : RM _) : BM _) with
    | some (v, index') =>
      let _ ← popN 1
      pushAll [index', v]
    | none =>
      BM.lift (jumpBy (e.oparg + 1))
      throw .dispatch
  | _ => fault "arity"
/-- `:3823`. -/
def FOR_ITER (e : Env) : M Unit := do _SPECIALIZE_FOR_ITER; _FOR_ITER e
/-- `:3913`. -/
def INSTRUMENTED_FOR_ITER (e : Env) : M Unit := _FOR_ITER e

/-- `:3868`. -/
def _GUARD_TOS_NOT_NULL : M Unit := guardTop 1 fun
  | [n] => pure (n == .null)
  | _ => fault "arity"
/-- `:3872`. The index stays out of `iterItem` until the end of the sequence. -/
def _FOR_ITER_VIRTUAL (e : Env) : M Unit := do
  let ins ← peekN 2
  match ins with
  | [iter, .tagged i] =>
    match ← BM.lift ((iterItem iter i : RM _) : BM _) with
    | some (v, i') =>
      let _ ← popN 1
      pushAll [.tagged i', v]
    | none =>
      BM.lift (jumpBy (e.oparg + 1))
      throw .dispatch
  | _ => fault "FOR_ITER_VIRTUAL without a tagged index"
/-- `:3890`. -/
def FOR_ITER_VIRTUAL (e : Env) : M Unit := do _GUARD_TOS_NOT_NULL; _FOR_ITER_VIRTUAL e

/-- The size of the exact sequence under `FOR_ITER_LIST`/`FOR_ITER_TUPLE`. -/
def seqItems : Val → BM (Array Val)
  | .ref a => do
    match ← (getObj a : RM Obj) with
    | .list items | .tuple items => pure items
    | _ => fault "not a sequence"
  | _ => fault "not a sequence"

/-- The tagged index the guards of these forms assert. -/
def taggedIndex : Val → BM Nat
  | .tagged i => pure i
  | _ => fault "not a tagged index"

/-- `:3927`: `Py_TYPE(iter_o) != &PyList_Type` deopts. -/
def _ITER_CHECK_LIST : M Unit := guardTop 2 fun
  | [it, _] => notList it
  | _ => fault "arity"

/-- `:3936` and `:4018`: at the end the slot becomes `PyStackRef_TagInt(-1)`, which only
`POP_ITER` at the jump target sees, and it discards the slot, so the model leaves it alone. -/
def iterJumpSeq (e : Env) : M Unit := do
  let ins ← peekN 2
  match ins with
  | [iter, index] =>
    let items ← BM.lift (seqItems iter)
    let i ← BM.lift (taggedIndex index)
    if items.size ≤ i then
      BM.lift (jumpBy (e.oparg + 1))
      throw .dispatch
  | _ => fault "arity"

/-- `:3964` and `:4038`: `(iter, null_or_index -- iter, null_or_index, next)`. -/
def iterNextSeq : M Unit := stk 2 3 fun
  | [iter, index] => do
    let items ← seqItems iter
    let i ← taggedIndex index
    pure [iter, .tagged (i + 1), items.getD i .null]
  | _ => fault "arity"

/-- `:3936`. -/
def _ITER_JUMP_LIST (e : Env) : M Unit := iterJumpSeq e
/-- `:3964`. -/
def _ITER_NEXT_LIST : M Unit := iterNextSeq
/-- `:4006`. -/
def FOR_ITER_LIST (e : Env) : M Unit := do _ITER_CHECK_LIST; _ITER_JUMP_LIST e; _ITER_NEXT_LIST

/-- `:4012`. -/
def _ITER_CHECK_TUPLE : M Unit := guardTop 2 fun
  | [it, _] => notTuple it
  | _ => fault "arity"
/-- `:4018`. -/
def _ITER_JUMP_TUPLE (e : Env) : M Unit := iterJumpSeq e
/-- `:4038`. -/
def _ITER_NEXT_TUPLE : M Unit := iterNextSeq
/-- `:4047`. -/
def FOR_ITER_TUPLE (e : Env) : M Unit := do _ITER_CHECK_TUPLE; _ITER_JUMP_TUPLE e; _ITER_NEXT_TUPLE

/-- `:4053`. -/
def _ITER_CHECK_RANGE : M Unit := guardTop 2 fun
  | [.ref a, _] => do
    match ← (getObj a : RM Obj) with
    | .rangeIter .. => pure false
    | _ => pure true
  | [_, _] => pure true
  | _ => fault "arity"

/-- `:4061`. -/
def _ITER_JUMP_RANGE (e : Env) : M Unit := do
  let ins ← peekN 2
  match ins with
  | [.ref a, _] =>
    match ← BM.lift ((getObj a : RM Obj) : BM Obj) with
    | .rangeIter _ _ len =>
      if len ≤ 0 then
        BM.lift (jumpBy (e.oparg + 1))
        throw .dispatch
    | _ => fault "not a range iterator"
  | _ => fault "not a range iterator"

/-- `:4082`. -/
def _ITER_NEXT_RANGE : M Unit := stk 2 3 fun
  | [.ref a, index] => do
    match ← (getObj a : RM Obj) with
    | .rangeIter start step len =>
      (setObj a (.rangeIter (start + step) step (len - 1)) : RM Unit)
      pure [.ref a, index, .int start]
    | _ => fault "not a range iterator"
  | _ => fault "not a range iterator"

/-- `:4097`. -/
def FOR_ITER_RANGE (e : Env) : M Unit := do _ITER_CHECK_RANGE; _ITER_JUMP_RANGE e; _ITER_NEXT_RANGE

/-- `:4103`: `(iter, null -- iter, null, gen_frame)`. -/
def _FOR_ITER_GEN_FRAME (e : Env) : M Frame := do
  let ins ← peekN 2
  let r ← BM.lift ((resumableGen false (ins.headD .null) : RM _) : BM _)
  match r with
  | some (a, g) =>
    BM.lift do
      let gf ← (genEnter a g .none : RM Frame)
      setReturnOffset (instrSize e.opcode + e.oparg)
      pure gf
  | none => throw .deopt

/-- `@3.14.7:3490`. -/
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

/-- `:4148`, `:3495`, `:3512`: `_INSERT_NULL` + `_LOAD_SPECIAL`. -/
def LOAD_SPECIAL (e : Env) : M Unit := stkK 1 2 fun
  | [owner] => do
    match ← e.om.lookupSpecial e.ctx owner (specialName e.oparg) with
    | some (m, s) => pure [m, s]
    | none =>
      let sug ← (specialCanSuggest e owner e.oparg : RM Bool)
      let t ← (tpName owner : RM String)
      (typeError (specialError e.oparg t sug) : RM _)
  | _ => fault "arity"

/-- `:4153`. -/
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

/-- `:4213`. -/
def PUSH_EXC_INFO : M Unit := stk 1 2 fun
  | [exc] => do
    let cur ← (getExcInfoTop : RM Val)
    (setExcInfoTop exc : RM Unit)
    pure [if cur != .null then cur else .none, exc]
  | _ => fault "arity"

/-! ### Lines 3594-3695: method loads -/

/-- `:4228`. -/
def _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT : M Unit := pure ()

/-- `:4235`. The version check says "no instance can shadow `name`"; the model
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

/-- `:4242`. -/
def _LOAD_ATTR_METHOD_WITH_VALUES (e : Env) : M Unit := stk 1 2 fun
  | [o] => pure [(e.cache[1]?).getD .null, o]
  | _ => fault "arity"
/-- `:4253`. -/
def LOAD_ATTR_METHOD_WITH_VALUES (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT; _GUARD_KEYS_VERSION e
  _LOAD_ATTR_METHOD_WITH_VALUES e
/-- `:4261`. -/
def _LOAD_ATTR_METHOD_NO_DICT (e : Env) : M Unit := stk 1 2 fun
  | [o] => pure [(e.cache[1]?).getD .null, o]
  | _ => fault "arity"
/-- `:4272`. -/
def LOAD_ATTR_METHOD_NO_DICT (e : Env) : M Unit := do _GUARD_TYPE_VERSION e; _LOAD_ATTR_METHOD_NO_DICT e
/-- `:4279`. -/
def _LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES (e : Env) : M Unit := stk 1 1 fun _ => pure [(e.cache[1]?).getD .null]
/-- `:4287`. -/
def LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT; _GUARD_KEYS_VERSION e
  _LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES e
/-- `:4295`. -/
def _LOAD_ATTR_NONDESCRIPTOR_NO_DICT (e : Env) : M Unit := stk 1 1 fun _ => pure [(e.cache[1]?).getD .null]
/-- `:4304`. -/
def LOAD_ATTR_NONDESCRIPTOR_NO_DICT (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _LOAD_ATTR_NONDESCRIPTOR_NO_DICT e
/-- `:4311`: the dict must not have been created yet. -/
def _CHECK_ATTR_METHOD_LAZY_DICT : M Unit := guardTop 1 fun
  | [o] => do
    match ← (instOf o : RM _) with
    | some (_, i) => pure (i.dict != .null)
    | none => pure true
  | _ => fault "arity"
/-- `:4318`. -/
def _LOAD_ATTR_METHOD_LAZY_DICT (e : Env) : M Unit := stk 1 2 fun
  | [o] => pure [(e.cache[1]?).getD .null, o]
  | _ => fault "arity"
/-- `:4328`. -/
def LOAD_ATTR_METHOD_LAZY_DICT (e : Env) : M Unit := do
  _GUARD_TYPE_VERSION e; _CHECK_ATTR_METHOD_LAZY_DICT; _LOAD_ATTR_METHOD_LAZY_DICT e

/-! ### Lines 3722-4050: `CALL` -/

/-- `:4361`. -/
def _SPECIALIZE_CALL : M Unit := pure ()

/-- `Py_TYPE(callable) == &PyMethod_Type`: `(im_func, im_self)`. -/
def methodParts : Val → RM (Option (Val × Val))
  | .ref a => do
    match ← getObj a with
    | .method f s => pure (some (f, s))
    | _ => pure none
  | _ => pure none

/-- `:4373`. -/
def _MAYBE_EXPAND_METHOD (e : Env) : M Unit := stk (e.oparg + 2) (e.oparg + 2) fun
  | callable :: self :: args => do
    match ← (methodParts callable : RM _) with
    | some (f, s) => if self == .null then pure (f :: s :: args) else pure (callable :: self :: args)
    | none => pure (callable :: self :: args)
  | _ => fault "arity"

/-- `self_or_null` + args as one array, `:4390-4395`. -/
def withSelf (self : Val) (args : List Val) : List Val :=
  if self != .null then self :: args else args

/-- `_PyEvalFramePushAndInit` from a call site. -/
def pushInit (e : Env) (callable : Val) (args : List Val) (kw : List String) : BM Frame := do
  let func ← (getFunc callable : RM _)
  let co ← (getCodeR e.P func.code : RM _)
  (framePushAndInit e.P callable (localsFor co func) args kw : RM _)

/-- `:4386`. -/
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

/-- `:4436`. -/
def _MONITOR_CALL : M Unit := pure ()
/-- `:4457`. -/
def CALL (e : Env) : M Unit := do _SPECIALIZE_CALL; _MAYBE_EXPAND_METHOD e; _DO_CALL e; _CHECK_PERIODIC_AT_END e
/-- `:4458`. -/
def INSTRUMENTED_CALL (e : Env) : M Unit := do
  _MAYBE_EXPAND_METHOD e; _MONITOR_CALL; _DO_CALL e; _CHECK_PERIODIC_AT_END e

/-- `:4460`. -/
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

/-- `:4485`. -/
def _CHECK_FUNCTION_VERSION (e : Env) : M Unit :=
  funcVersionAt (e.oparg + 1) e fun c => do return !(← (isFunction c : RM Bool))
/-- `:4492`: tier 2 only; the same check. -/
def _CHECK_FUNCTION_VERSION_INLINE (e : Env) : M Unit := _CHECK_FUNCTION_VERSION e

/-- `:4611`. -/
def _CHECK_RECURSION_REMAINING : M Unit := guardTop 0 fun _ => do
  pure ((← (getRecursionRemaining : RM Int)) ≤ 1)

/-- `:4498`. -/
def CALL_PY_GENERAL (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_FUNCTION_VERSION e
  _CHECK_RECURSION_REMAINING
  let nf ← _PY_FRAME_GENERAL e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:4508`. -/
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

/-- `:4518`. -/
def _EXPAND_METHOD (e : Env) : M Unit := stk (e.oparg + 2) (e.oparg + 2) fun
  | c :: _ :: args => do
    match ← (methodParts c : RM _) with
    | some (f, s) => pure (f :: s :: args)
    | none => fault "not a method"
  | _ => fault "arity"

/-- `:4529`. -/
def CALL_BOUND_METHOD_GENERAL (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_METHOD_VERSION e
  _EXPAND_METHOD e
  _CHECK_RECURSION_REMAINING
  let nf ← _PY_FRAME_GENERAL e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf

/-- `:4541`. -/
def _CHECK_IS_NOT_PY_CALLABLE (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: _ => do
    if ← (isFunction c : RM Bool) then pure true
    else return (← (methodParts c : RM _)).isSome
  | _ => fault "arity"

/-- The common shape of every non-Python call: `:4547`, and the `_CALL_BUILTIN_*`
and `_CALL_METHOD_DESCRIPTOR_*` bodies once the guards have passed. -/
def callNonPy (e : Env) : M Unit := stk (e.oparg + 2) 1 fun
  | callable :: self :: args => do
    pure [← e.om.call e.ctx callable (withSelf self args) []]
  | _ => fault "arity"

/-- `:4547`. -/
def _CALL_NON_PY_GENERAL (e : Env) : M Unit := callNonPy e
/-- `:4569`. -/
def CALL_NON_PY_GENERAL (e : Env) : M Unit := do
  _CHECK_IS_NOT_PY_CALLABLE e; _CALL_NON_PY_GENERAL e; _CHECK_PERIODIC_AT_END e

/-- `:4577`. -/
def _CHECK_CALL_BOUND_METHOD_EXACT_ARGS (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: n :: _ => do
    if n != .null then pure true
    else return (← (methodParts c : RM _)).isNone
  | _ => fault "arity"
/-- `:4582`. -/
def _INIT_CALL_BOUND_METHOD_EXACT_ARGS (e : Env) : M Unit := _EXPAND_METHOD e

/-- `:4596`. -/
def _CHECK_FUNCTION_EXACT_ARGS (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: s :: _ => do
    let f ← (getFunc c : RM _)
    let co ← (getCodeR e.P f.code : RM _)
    pure (co.argcount != e.oparg + (if s != .null then 1 else 0))
  | _ => fault "arity"
/-- `:4604`. -/
def _CHECK_STACK_SPACE : M Unit := guardTop 0 fun _ => do return !(← hasStackSpace)

/-- `:4615`. -/
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

/-- `:4644`. -/
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

/-- `:4659`. -/
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

/-- `:4671-4673`. -/
def _GUARD_NOS_NULL : M Unit := guardTop 2 fun
  | [n, _] => pure (n != .null)
  | _ => fault "arity"
/-- Guards on the callable below `self_or_null` and one argument. -/
def guardCallable (w : Val) : M Unit := guardTop 3 fun
  | [c, _, _] => pure (c != w)
  | _ => fault "arity"
/-- `:4679-4682`. -/
def _GUARD_CALLABLE_TYPE_1 : M Unit := guardCallable (.cls "type")
/-- `:4684-4692`: `Py_TYPE(arg)`; the `POP_TOP` of the macro is folded in. -/
def _CALL_TYPE_1 : M Unit := stk 3 1 fun
  | [_, _, a] => do pure [← (typeOf a : RM Val)]
  | _ => fault "arity"
/-- `:4694-4700`. -/
def CALL_TYPE_1 : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_TYPE_1; _CALL_TYPE_1
/-- `:4702-4705`. -/
def _GUARD_CALLABLE_STR_1 : M Unit := guardCallable (.cls "str")
/-- `:4707-4719`: `PyObject_Str(arg)`, `ERROR_NO_POP` on failure; the `POP_TOP` of the macro is
folded in. -/
def _CALL_STR_1 (e : Env) : M Unit := stkK 3 1 fun
  | [_, _, a] => do pure [← e.om.str e.ctx a]
  | _ => fault "arity"
/-- `:4721-4728`. -/
def CALL_STR_1 (e : Env) : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_STR_1; _CALL_STR_1 e; _CHECK_PERIODIC_AT_END e
/-- `:4730-4733`. -/
def _GUARD_CALLABLE_TUPLE_1 : M Unit := guardCallable (.cls "tuple")
/-- `:4735-4747`: `PySequence_Tuple(arg)`, which is what calling `tuple` with one argument runs
(`tuple_vectorcall`), `ERROR_NO_POP` on failure; the `POP_TOP` of the macro is folded in. -/
def _CALL_TUPLE_1 (e : Env) : M Unit := stkK 3 1 fun
  | [c, _, a] => do pure [← e.om.call e.ctx c [a] []]
  | _ => fault "arity"
/-- `:4749-4756`. -/
def CALL_TUPLE_1 (e : Env) : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_TUPLE_1; _CALL_TUPLE_1 e; _CHECK_PERIODIC_AT_END e

/-- `:4758`: split off `_CHECK_AND_ALLOCATE_OBJECT` of 3.14, so that
`_CHECK_RECURSION_REMAINING` can run before anything is allocated. -/
def _CHECK_OBJECT (e : Env) : M Unit := guardTop (e.oparg + 2) fun
  | c :: n :: _ => do
    if n != .null then return true
    match ← (classVersion c : RM _) with
    | none => pure true
    | some v => pure (v != cacheNat e 0)
  | _ => fault "arity"

/-- `:4766-4788`: `(callable, self_or_null, args -- init, self, args)`. `init` is
`cls->_spec_cache.init`, which lives on the type: `_PyType_CacheInitForSpecialization` stores it
under the version `_CHECK_OBJECT` has just matched, and `type_modified` clears it and drops the
version (`Objects/typeobject.c`), so under that version it is the `__init__` that `_PyType_Lookup`
finds. The model reads it that way rather than from the instruction's cache, whose object
reference would belong to the profiling run of the `quick` difftest. Note that nothing here looks
at `Py_TPFLAGS_IS_ABSTRACT`: `bytecode-call-alloc-abstract`. -/
def _ALLOCATE_OBJECT (e : Env) : M Unit := stk (e.oparg + 2) (e.oparg + 2) fun
  | c :: _ :: args => do
    let some init ← (e.om.typeLookup c "__init__" : RM _) | fault "_spec_cache.init is NULL"
    deoptIf !(← hasStackSpace)
    let self ← (alloc (.inst { cls := c }) : RM Val)
    pure (init :: self :: args)
  | _ => fault "arity"

/-- The `_Py_InitCleanup` shim of `Python/specialize.c`: reserved `Program` index 1. -/
def initCleanupIdx : Nat := 1

/-- `:4790-4813`. C pushes the `_Py_InitCleanup` shim on the data stack first, without making it
the current frame, then `_PyEvalFramePushAndInit` builds `__init__`'s frame on top of it; when
that fails (`:4803-4806`) the shim is popped again (`_PyEval_FrameClearAndPop`) and the error is
raised in the caller with the operands consumed (`SYNC_SP` before `ERROR_NO_POP`), before
`return_offset` is set and before the recursion counter is touched. Building the frame is
heap-only here, so the model builds it first and enters the shim only on success, which leaves
the same state on both paths. -/
def _CREATE_INIT_FRAME (e : Env) : M Frame := do
  let ins ← popN (e.oparg + 2)
  match ins with
  | init :: self :: args => do
    let nf ← BM.lift do
      (framePushAndInit e.P init .null (self :: args) [] : RM _)
    -- `frame->return_offset` belongs to the caller
    BM.lift (setReturnOffset (1 + 3))
    let shim : Frame := { code := initCleanupIdx, stack := [self], owner := .thread }
    enterFrame shim
    BM.lift (decRecursionRemaining : RM Unit)
    pure nf
  | _ => fault "arity"

/-- `:4815`. -/
def CALL_ALLOC_AND_ENTER_INIT (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_OBJECT e
  _CHECK_RECURSION_REMAINING
  _ALLOCATE_OBJECT e
  let nf ← _CREATE_INIT_FRAME e
  _PUSH_FRAME nf

/-- `:4825`. -/
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

/-- `:4842`: `tp->tp_vectorcall == NULL` deopts, `specialCalls` decides. -/
def _CALL_BUILTIN_CLASS (e : Env) : M Unit := do
  builtinGuard e fun c _ => do return !(← (isType c : RM Bool))
  callNonPy e
/-- `:4862`. -/
def CALL_BUILTIN_CLASS (e : Env) : M Unit := do _CALL_BUILTIN_CLASS e; _CHECK_PERIODIC_AT_END e
/-- `:4883`. -/
def _CALL_BUILTIN_O (e : Env) : M Unit := do
  builtinGuard e fun c args => pure (args.length != 1 || !(match c with | .builtin _ => true | _ => false))
  callNonPy e
/-- `:4905`. -/
def CALL_BUILTIN_O (e : Env) : M Unit := do _CALL_BUILTIN_O e; _CHECK_PERIODIC_AT_END e
/-- `:4922`. -/
def _CALL_BUILTIN_FAST (e : Env) : M Unit := do
  builtinGuard e fun c _ => pure !(match c with | .builtin _ => true | _ => false)
  callNonPy e
/-- `:4944`. -/
def CALL_BUILTIN_FAST (e : Env) : M Unit := do _CALL_BUILTIN_FAST e; _CHECK_PERIODIC_AT_END e
/-- `:4960`. -/
def _CALL_BUILTIN_FAST_WITH_KEYWORDS (e : Env) : M Unit := _CALL_BUILTIN_FAST e
/-- `:4978`. -/
def CALL_BUILTIN_FAST_WITH_KEYWORDS (e : Env) : M Unit := do _CALL_BUILTIN_FAST_WITH_KEYWORDS e; _CHECK_PERIODIC_AT_END e
/-- `:4997-5001`: `callable_cache.len`, the builtin `len`. -/
def _GUARD_CALLABLE_LEN : M Unit := guardCallable (.builtin "len")
/-- `:5003-5020`: `PyObject_Length(arg)` as an int, `ERROR_NO_POP` on failure; the two `POP_TOP`s of
the macro are folded in. -/
def _CALL_LEN (e : Env) : M Unit := stkK 3 1 fun
  | [_, _, a] => do pure [.int (← e.om.length e.ctx a)]
  | _ => fault "arity"
/-- `:4988-4995`. -/
def CALL_LEN (e : Env) : M Unit := do _GUARD_NOS_NULL; _GUARD_CALLABLE_LEN; _CALL_LEN e
/-- `:4675-4677`: `(null, unused, unused -- ...)`. -/
def _GUARD_THIRD_NULL : M Unit := guardTop 3 fun
  | [n, _, _] => pure (n != .null)
  | _ => fault "arity"
/-- `:5022-5026`. -/
def _GUARD_CALLABLE_ISINSTANCE : M Unit := guardTop 4 fun
  | [c, _, _, _] => pure (c != .builtin "isinstance")
  | _ => fault "arity"
/-- `:5028-5044`: `(callable, null, instance, cls -- res)`, `PyObject_IsInstance`, `ERROR_NO_POP` on
failure. -/
def _CALL_ISINSTANCE (e : Env) : M Unit := stkK 4 1 fun
  | [_, _, i, c] => do pure [.bool (← e.om.isInstance e.ctx i c)]
  | _ => fault "arity"
/-- `:5046-5051`. -/
def CALL_ISINSTANCE (e : Env) : M Unit := do
  _GUARD_THIRD_NULL; _GUARD_CALLABLE_ISINSTANCE; _CALL_ISINSTANCE e
/-- `:5063-5067`. -/
def _GUARD_CALLABLE_LIST_APPEND : M Unit := guardCallable (.methDescr "list" "append")
/-- `:5069-5090`: `(callable, self, arg -- none, c, s)`, and the two `POP_TOP` of the macro. It
leaves `None` for the `POP_TOP` that follows in the bytecode, which 3.14 skipped. -/
def _CALL_LIST_APPEND : M Unit := stk 3 1 fun
  | [_, s, a] => do
    (listAppend s a : RM Unit)
    pure [.none]
  | _ => fault "arity"
/-- `:5053-5061`. -/
def CALL_LIST_APPEND : M Unit := do
  _GUARD_CALLABLE_LIST_APPEND; _GUARD_NOS_NOT_NULL; _GUARD_NOS_LIST; _CALL_LIST_APPEND

/-- The receiver guard of `_CALL_METHOD_DESCRIPTOR_*`. -/
def methDescrGuard (e : Env) (min : Nat) : M Unit :=
  builtinGuard e fun c args => do
    match c, args with
    | .methDescr tp _, a :: _ =>
      if args.length < min then pure true
      else return (← (tpName a : RM String)) != tp
    | _, _ => pure true
/-- `:5105`. -/
def _CALL_METHOD_DESCRIPTOR_O (e : Env) : M Unit := do methDescrGuard e 2; callNonPy e
/-- `:5153`. -/
def CALL_METHOD_DESCRIPTOR_O (e : Env) : M Unit := do _CALL_METHOD_DESCRIPTOR_O e; _CHECK_PERIODIC_AT_END e
/-- `:5839`. -/
def _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS (e : Env) : M Unit := do methDescrGuard e 1; callNonPy e
/-- `:5229`. -/
def CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS (e : Env) : M Unit := do
  _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS e; _CHECK_PERIODIC_AT_END e
/-- `:5254`. -/
def _CALL_METHOD_DESCRIPTOR_NOARGS (e : Env) : M Unit := do methDescrGuard e 1; callNonPy e
/-- `:5296`. -/
def CALL_METHOD_DESCRIPTOR_NOARGS (e : Env) : M Unit := do _CALL_METHOD_DESCRIPTOR_NOARGS e; _CHECK_PERIODIC_AT_END e
/-- `:5323`. -/
def _CALL_METHOD_DESCRIPTOR_FAST (e : Env) : M Unit := do methDescrGuard e 1; callNonPy e
/-- `:5372`. -/
def CALL_METHOD_DESCRIPTOR_FAST (e : Env) : M Unit := do _CALL_METHOD_DESCRIPTOR_FAST e; _CHECK_PERIODIC_AT_END e

/-! ### Lines 4591-4840: `CALL_KW` -/

/-- `:5388`. -/
def _MONITOR_CALL_KW : M Unit := pure ()
/-- `:5407`. -/
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

/-- `:5419`. -/
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

/-- `:5474`. -/
def _PY_FRAME_KW (e : Env) : M Frame := do
  let ins ← popN (e.oparg + 3)
  match ins with
  | callable :: self :: rest =>
    let args := rest.dropLast
    let kw ← BM.lift ((kwNames (rest.getLastD .null) : RM _) : BM _)
    BM.lift (pushInit e callable (withSelf self args) kw)
  | _ => fault "arity"

/-- `:5504`. -/
def _CHECK_FUNCTION_VERSION_KW (e : Env) : M Unit :=
  funcVersionAt (e.oparg + 2) e fun c => do return !(← (isFunction c : RM Bool))
/-- `:5511`. -/
def CALL_KW_PY (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_FUNCTION_VERSION_KW e
  _CHECK_RECURSION_REMAINING
  let nf ← _PY_FRAME_KW e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf
/-- `:5521`. -/
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
/-- `:5531`. -/
def _EXPAND_METHOD_KW (e : Env) : M Unit := stk (e.oparg + 3) (e.oparg + 3) fun
  | c :: _ :: rest => do
    match ← (methodParts c : RM _) with
    | some (f, s) => pure (f :: s :: rest)
    | none => fault "not a method"
  | _ => fault "arity"
/-- `:5542`. -/
def CALL_KW_BOUND_METHOD (e : Env) : M Unit := do
  _CHECK_PEP_523
  _CHECK_METHOD_VERSION_KW e
  _EXPAND_METHOD_KW e
  let nf ← _PY_FRAME_KW e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf
/-- `:5553`. -/
def _SPECIALIZE_CALL_KW : M Unit := pure ()
/-- `:5565`. -/
def CALL_KW (e : Env) : M Unit := do _SPECIALIZE_CALL_KW; _MAYBE_EXPAND_METHOD_KW e; _DO_CALL_KW e
/-- `:5571`. -/
def INSTRUMENTED_CALL_KW (e : Env) : M Unit := do _MAYBE_EXPAND_METHOD_KW e; _MONITOR_CALL_KW; _DO_CALL_KW e
/-- `:5578`. -/
def _CHECK_IS_NOT_PY_CALLABLE_KW (e : Env) : M Unit := guardTop (e.oparg + 3) fun
  | c :: _ => do
    if ← (isFunction c : RM Bool) then pure true
    else return (← (methodParts c : RM _)).isSome
  | _ => fault "arity"
/-- `:5585`. -/
def _CALL_KW_NON_PY (e : Env) : M Unit := stk (e.oparg + 3) 1 fun
  | callable :: self :: rest => do
    let kw ← (kwNames (rest.getLastD .null) : RM _)
    pure [← e.om.call e.ctx callable (withSelf self rest.dropLast) kw]
  | _ => fault "arity"
/-- `:5608`. -/
def CALL_KW_NON_PY (e : Env) : M Unit := do
  _CHECK_IS_NOT_PY_CALLABLE_KW e; _CALL_KW_NON_PY e; _CHECK_PERIODIC_AT_END e

/-! ### Lines 4841-5087: `CALL_FUNCTION_EX`, functions, formatting -/

/-- `_Py_Check_ArgsIterable`, `Python/ceval.c:3402-3412`. `func` is unused since 3.15. -/
def checkArgsIterable (e : Env) (_func args : Val) : RM Unit := do
  if !(← e.om.isIterable args) then
    typeError s!"Value after * must be an iterable, not {trunc200 (← tpName args)}"

/-- `:5620`. -/
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

/-- `:5637`. -/
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
      BM.lift (setReturnOffset (instrSize e.opcode))
      dispatchInlined nf
    else
      -- `PyObject_Call(func, callargs, kwargs)` (`:5706`)
      stk 4 1 fun _ => do pure [← e.om.callDict e.ctx func callargs kwargs]
  | _ => fault "arity"

/-- `:5728`. -/
def CALL_FUNCTION_EX (e : Env) : M Unit := do
  _MAKE_CALLARGS_A_TUPLE e; _DO_CALL_FUNCTION_EX e; _CHECK_PERIODIC_AT_END e
/-- `:5801`. -/
def INSTRUMENTED_CALL_FUNCTION_EX (e : Env) : M Unit := CALL_FUNCTION_EX e
/-- `:5734`. -/
def _CHECK_IS_PY_CALLABLE_EX : M Unit := guardTop 4 fun
  | [f, _, _, _] => do return !(← (isFunction f : RM Bool))
  | _ => fault "arity"
/-- `:5740`: `(func_st, null, callargs_st, kwargs_st -- ex_frame)`. -/
def _PY_FRAME_EX (e : Env) : M Frame := do
  let ins ← popN 4
  match ins with
  | [func, _, callargs, kwargs] => BM.lift do
    let (kw, kwvals) ← (unpackKwargs kwargs : RM _)
    let pos ← (tupleItems callargs : RM _)
    pushInit e func (pos.toList ++ kwvals) kw
  | _ => fault "arity"
/-- `:5763`. No `_CHECK_RECURSION_REMAINING` here either: python/cpython#155151. -/
def CALL_EX_PY (e : Env) : M Unit := do
  _CHECK_PEP_523
  _MAKE_CALLARGS_A_TUPLE e
  _CHECK_IS_PY_CALLABLE_EX
  let nf ← _PY_FRAME_EX e
  BM.lift (_SAVE_RETURN_OFFSET e)
  _PUSH_FRAME nf
/-- `:5773`. -/
def _CHECK_IS_NOT_PY_CALLABLE_EX : M Unit := guardTop 4 fun
  | [f, _, _, _] => (isFunction f : RM Bool)
  | _ => fault "arity"
/-- `:5778`. -/
def _CALL_FUNCTION_EX_NON_PY_GENERAL (e : Env) : M Unit := stk 4 1 fun
  | [func, _, callargs, kwargs] => do pure [← e.om.callDict e.ctx func callargs kwargs]
  | _ => fault "arity"
/-- `:5794`. -/
def CALL_EX_NON_PY_GENERAL (e : Env) : M Unit := do
  _CHECK_IS_NOT_PY_CALLABLE_EX; _MAKE_CALLARGS_A_TUPLE e; _CALL_FUNCTION_EX_NON_PY_GENERAL e
  _CHECK_PERIODIC_AT_END e

/-- `:5824`. -/
def MAKE_FUNCTION (e : Env) : M Unit := stk 1 1 fun
  | [.code i] => do
    let f ← getFrame
    let co ← (getCodeR e.P i : RM _)
    pure [← (alloc (.func { code := i, globals := f.globals, builtins := f.builtins,
                            name := co.name, qualname := co.qualname,
                            version := co.version }) : RM Val)]
  | _ => fault "MAKE_FUNCTION without a code object"

/-- `:5826`. -/
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

/-- `:5839`. -/
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
      (setObj a (.gen { kind := genKindOfFlags co.flags, frame := gf, frameState := 0,
                        name := func.name, qualname := func.qualname }) : RM Unit)
      pure gv
    | _ => fault "alloc"
  BM.lift (leaveRecursivePy : RM Unit)
  popToPrevious
  BM.lift do loadIp (← getFrame).returnOffset
  pushAll [gen]

/-- `:5863`. -/
def BUILD_SLICE (e : Env) : M Unit := stk e.oparg 1 fun args => do
  let start := args.getD 0 .null
  let stop := args.getD 1 .null
  let step := if e.oparg == 3 then args.getD 2 .null else .none
  pure [← (alloc (.slice start stop step) : RM Val)]
/-- `:5873`. -/
def CONVERT_VALUE (e : Env) : M Unit := stk 1 1 fun
  | [v] => do
    match e.oparg with
    | 1 => pure [← e.om.str e.ctx v]
    | 2 => pure [← e.om.repr e.ctx v]
    | 3 => pure [← e.om.ascii e.ctx v]
    | _ => fault "bad conversion"
  | _ => fault "arity"
/-- `:5883`. -/
def FORMAT_SIMPLE (e : Env) : M Unit := stk 1 1 fun
  | [.str s] => pure [.str s]
  | [v] => do pure [← e.om.format e.ctx v .null]
  | _ => fault "arity"
/-- `:5899`. -/
def FORMAT_WITH_SPEC (e : Env) : M Unit := stk 2 1 fun
  | [v, f] => do pure [← e.om.format e.ctx v f]
  | _ => fault "arity"
/-- `:5906`. -/
def COPY (e : Env) : M Unit := stk e.oparg (e.oparg + 1) fun ins => pure (ins ++ [ins.headD .null])
/-- `:5910`. -/
def _SPECIALIZE_BINARY_OP : M Unit := pure ()
/-- `:5924`: `(lhs, rhs -- res, l, r)`, `ERROR_NO_POP` on failure. The `POP_TOP + POP_TOP` of the
macro are folded into the `stkK`, since popping has no effect without a finalizer model. -/
def _BINARY_OP (e : Env) : M Unit := stkK 2 1 fun
  | [l, r] => do pure [← e.om.binaryOp e.ctx e.oparg l r]
  | _ => fault "arity"
/-- `:5940`. -/
def BINARY_OP (e : Env) : M Unit := do _SPECIALIZE_BINARY_OP; _BINARY_OP e
/-- `:5942`. -/
def SWAP (e : Env) : M Unit := stk e.oparg e.oparg fun
  | [] => fault "SWAP 0"
  | b :: rest => pure (rest.getLastD b :: rest.dropLast ++ [b])

/-- Lines 5132-5192: without a registered tool every instrumented jump is the
plain one. -/
def INSTRUMENTED_JUMP_FORWARD (e : Env) : M Unit := JUMP_FORWARD e
/-- `:5996`. -/
def _MONITOR_JUMP_BACKWARD (e : Env) : M Unit := JUMP_BACKWARD_NO_INTERRUPT e
/-- `:6000`. -/
def INSTRUMENTED_NOT_TAKEN : M Unit := NOP
/-- `:6005`. -/
def INSTRUMENTED_JUMP_BACKWARD (e : Env) : M Unit := do _CHECK_PERIODIC; _MONITOR_JUMP_BACKWARD e
/-- `:6010`. -/
def INSTRUMENTED_POP_JUMP_IF_TRUE (e : Env) : M Unit := POP_JUMP_IF_TRUE e
/-- `:6020`. -/
def INSTRUMENTED_POP_JUMP_IF_FALSE (e : Env) : M Unit := POP_JUMP_IF_FALSE e
/-- `:6030`. -/
def INSTRUMENTED_POP_JUMP_IF_NONE (e : Env) : M Unit := POP_JUMP_IF_NONE e
/-- `:6042`. -/
def INSTRUMENTED_POP_JUMP_IF_NOT_NONE (e : Env) : M Unit := POP_JUMP_IF_NOT_NONE e

end PyLean.Bytecode.Uop
