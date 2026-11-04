import PyLean.Bytecode.Uops3

/-!
The interpreter loop: instruction dispatch and the labels `error`,
`exception_unwind`, `exit_unwind` and `start_frame` of `Python/bytecodes.c`
(lines 6447-6590) and the entry protocol of `_PyEval_EvalFrameDefault`
(`Python/ceval.c:1241-1353`).

`Program` indices 0 and 1 are reserved for the two static code objects the
interpreter uses itself: the entry trampoline
`_Py_INTERPRETER_TRAMPOLINE_INSTRUCTIONS` and `_Py_InitCleanup`.
-/

namespace PyLean.Bytecode

open Uop

/-- `DEOPT_IF`/`EXIT_IF`: a guard that fails restarts the instruction in its
generic form, from the pre-instruction state. That is the same as continuing at
`PREDICTED_<family>` with the stack the guard saw only when nothing before the
guard changed anything the generic form would not redo: the method expansions of
`CALL_BOUND_METHOD_EXACT_ARGS`/`_GENERAL` and `CALL_KW_BOUND_METHOD` (which the
generic `CALL`/`CALL_KW` redoes in `_MAYBE_EXPAND_METHOD`) are such changes.
`CALL_EX_PY` is not: its `_MAKE_CALLARGS_A_TUPLE` runs `PySequence_Tuple`, which
can run Python code (`__iter__`, `__next__`), before `_CHECK_IS_PY_CALLABLE_EX`,
and `JUMP_TO_PREDICTED(CALL_FUNCTION_EX)` keeps the tuple it wrote into the stack
(`Python/generated_cases.c.h`, `CALL_EX_PY`); it runs as `execCallExPy`. -/
def withDeopt (m g : M Unit) : M Unit := fun s =>
  match m s with
  | .error .deopt _ => g s
  | r => r

/-- `CALL_EX_PY` (`:5763-5771`) as dispatch runs it. `_MAKE_CALLARGS_A_TUPLE` writes its tuple
into the stack before `_CHECK_IS_PY_CALLABLE_EX` can exit, and `JUMP_TO_PREDICTED(CALL_FUNCTION_EX)`
keeps that stack (`Python/generated_cases.c.h`, `CALL_EX_PY`), so an exit of the guards after it
restarts `CALL_FUNCTION_EX` on the converted stack, whose own `_MAKE_CALLARGS_A_TUPLE` then leaves
the exact tuple alone: `PySequence_Tuple` (and the `__iter__`/`__next__` it runs) happens once. An
exit of `_CHECK_PEP_523`, before anything ran, restarts from the instruction's state. -/
def execCallExPy (e : Env) : M Unit := fun s =>
  match (do _CHECK_PEP_523; _MAKE_CALLARGS_A_TUPLE e : M Unit) s with
  | .ok _ s1 => withDeopt (CALL_EX_PY_TAIL e) (CALL_FUNCTION_EX e) s1
  | .error .deopt _ => CALL_FUNCTION_EX e s
  | r => r

/-- The descriptors of `BINARY_OP_EXTEND`, `Python/specialize.c:2282-2311`. A cache
of `[.tagged k]` selects one. The guards are `compactlongs_guard` and
`float_compactlong_guard`/`compactlong_float_guard`. -/
def extendDescr (k : Nat) : ExtendDescr :=
  let ints (f : Int → Int → Int) : ExtendDescr :=
    { guard := fun l r => match l, r with
        | .int a, .int b => isCompact a && isCompact b
        | _, _ => false
      action := fun l r => match l, r with
        | .int a, .int b => .int (f a b)
        | _, _ => .null }
  match k with
  | 0 => ints intOr
  | 1 => ints intAnd
  | _ => ints intXor

/-- `switch (opcode)`: every real opcode. A specialized form falls back to its
generic form on a guard failure. -/
def execOp (e : Env) : Op → M Unit
  | .CACHE => fault "Executing a cache."
  | .RESERVED => fault "Executing RESERVED instruction."
  | .NOP => NOP
  | .NOT_TAKEN => NOT_TAKEN
  | .RESUME => RESUME
  | .RESUME_CHECK => RESUME_CHECK
  | .RESUME_CHECK_JIT => RESUME_CHECK_JIT
  | .TRACE_RECORD => TRACE_RECORD
  | .INSTRUMENTED_RESUME => INSTRUMENTED_RESUME
  | .LOAD_FAST_CHECK => LOAD_FAST_CHECK e
  | .LOAD_FAST => LOAD_FAST e
  | .LOAD_FAST_BORROW => LOAD_FAST_BORROW e
  | .LOAD_FAST_AND_CLEAR => LOAD_FAST_AND_CLEAR e
  | .LOAD_FAST_LOAD_FAST => LOAD_FAST_LOAD_FAST e
  | .LOAD_FAST_BORROW_LOAD_FAST_BORROW => LOAD_FAST_BORROW_LOAD_FAST_BORROW e
  | .LOAD_CONST => LOAD_CONST e
  | .LOAD_SMALL_INT => LOAD_SMALL_INT e
  | .STORE_FAST => STORE_FAST e
  | .STORE_FAST_LOAD_FAST => STORE_FAST_LOAD_FAST e
  | .STORE_FAST_STORE_FAST => STORE_FAST_STORE_FAST e
  | .POP_TOP => POP_TOP
  | .PUSH_NULL => PUSH_NULL
  | .END_FOR => END_FOR
  | .POP_ITER => POP_ITER
  | .INSTRUMENTED_END_FOR => INSTRUMENTED_END_FOR
  | .INSTRUMENTED_POP_ITER => INSTRUMENTED_POP_ITER
  | .END_SEND => END_SEND
  | .INSTRUMENTED_END_SEND => INSTRUMENTED_END_SEND
  | .UNARY_NEGATIVE => UNARY_NEGATIVE e
  | .UNARY_NOT => UNARY_NOT
  | .UNARY_INVERT => UNARY_INVERT e
  | .TO_BOOL => TO_BOOL e
  | .TO_BOOL_BOOL => withDeopt TO_BOOL_BOOL (TO_BOOL e)
  | .TO_BOOL_INT => withDeopt TO_BOOL_INT (TO_BOOL e)
  | .TO_BOOL_LIST => withDeopt TO_BOOL_LIST (TO_BOOL e)
  | .TO_BOOL_NONE => withDeopt TO_BOOL_NONE (TO_BOOL e)
  | .TO_BOOL_STR => withDeopt TO_BOOL_STR (TO_BOOL e)
  | .TO_BOOL_ALWAYS_TRUE => withDeopt (TO_BOOL_ALWAYS_TRUE e) (TO_BOOL e)
  | .BINARY_OP => BINARY_OP e
  | .BINARY_OP_MULTIPLY_INT => withDeopt BINARY_OP_MULTIPLY_INT (BINARY_OP e)
  | .BINARY_OP_ADD_INT => withDeopt BINARY_OP_ADD_INT (BINARY_OP e)
  | .BINARY_OP_SUBTRACT_INT => withDeopt BINARY_OP_SUBTRACT_INT (BINARY_OP e)
  | .BINARY_OP_MULTIPLY_FLOAT => withDeopt BINARY_OP_MULTIPLY_FLOAT (BINARY_OP e)
  | .BINARY_OP_ADD_FLOAT => withDeopt BINARY_OP_ADD_FLOAT (BINARY_OP e)
  | .BINARY_OP_SUBTRACT_FLOAT => withDeopt BINARY_OP_SUBTRACT_FLOAT (BINARY_OP e)
  | .BINARY_OP_ADD_UNICODE => withDeopt BINARY_OP_ADD_UNICODE (BINARY_OP e)
  | .BINARY_OP_INPLACE_ADD_UNICODE => withDeopt (BINARY_OP_INPLACE_ADD_UNICODE e) (BINARY_OP e)
  | .BINARY_OP_EXTEND =>
    withDeopt (BINARY_OP_EXTEND (extendDescr (cacheNat e 0))) (BINARY_OP e)
  | .BINARY_OP_SUBSCR_LIST_INT => withDeopt BINARY_OP_SUBSCR_LIST_INT (BINARY_OP e)
  | .BINARY_OP_SUBSCR_LIST_SLICE => withDeopt (BINARY_OP_SUBSCR_LIST_SLICE e) (BINARY_OP e)
  | .BINARY_OP_SUBSCR_STR_INT => withDeopt BINARY_OP_SUBSCR_STR_INT (BINARY_OP e)
  | .BINARY_OP_SUBSCR_USTR_INT => withDeopt BINARY_OP_SUBSCR_USTR_INT (BINARY_OP e)
  | .BINARY_OP_SUBSCR_TUPLE_INT => withDeopt BINARY_OP_SUBSCR_TUPLE_INT (BINARY_OP e)
  | .BINARY_OP_SUBSCR_DICT => withDeopt (BINARY_OP_SUBSCR_DICT e) (BINARY_OP e)
  | .BINARY_OP_SUBSCR_GETITEM => withDeopt (BINARY_OP_SUBSCR_GETITEM e) (BINARY_OP e)
  | .BINARY_SLICE => BINARY_SLICE e
  | .STORE_SLICE => STORE_SLICE e
  | .LIST_APPEND => LIST_APPEND e
  | .SET_ADD => SET_ADD e
  | .STORE_SUBSCR => STORE_SUBSCR e
  | .STORE_SUBSCR_LIST_INT => withDeopt STORE_SUBSCR_LIST_INT (STORE_SUBSCR e)
  | .STORE_SUBSCR_DICT => withDeopt (STORE_SUBSCR_DICT e) (STORE_SUBSCR e)
  | .DELETE_SUBSCR => DELETE_SUBSCR e
  | .CALL_INTRINSIC_1 => CALL_INTRINSIC_1 e
  | .CALL_INTRINSIC_2 => CALL_INTRINSIC_2 e
  | .RAISE_VARARGS => RAISE_VARARGS e
  | .INTERPRETER_EXIT => INTERPRETER_EXIT
  | .RETURN_VALUE => RETURN_VALUE
  | .INSTRUMENTED_RETURN_VALUE => INSTRUMENTED_RETURN_VALUE
  | .GET_AITER => GET_AITER e
  | .GET_ANEXT => GET_ANEXT e
  | .GET_AWAITABLE => GET_AWAITABLE e
  | .SEND => SEND e
  | .SEND_GEN => withDeopt (SEND_GEN e) (SEND e)
  | .SEND_VIRTUAL => withDeopt (SEND_VIRTUAL e) (SEND e)
  | .SEND_ASYNC_GEN => withDeopt SEND_ASYNC_GEN (SEND e)
  | .YIELD_VALUE => YIELD_VALUE e
  | .INSTRUMENTED_YIELD_VALUE => INSTRUMENTED_YIELD_VALUE e
  | .POP_EXCEPT => POP_EXCEPT
  | .RERAISE => RERAISE e
  | .END_ASYNC_FOR => END_ASYNC_FOR
  | .INSTRUMENTED_END_ASYNC_FOR => INSTRUMENTED_END_ASYNC_FOR
  | .CLEANUP_THROW => CLEANUP_THROW
  | .LOAD_COMMON_CONSTANT => LOAD_COMMON_CONSTANT e
  | .LOAD_BUILD_CLASS => LOAD_BUILD_CLASS e
  | .STORE_NAME => STORE_NAME e
  | .DELETE_NAME => DELETE_NAME e
  | .UNPACK_SEQUENCE => UNPACK_SEQUENCE e
  | .UNPACK_SEQUENCE_TWO_TUPLE => withDeopt UNPACK_SEQUENCE_TWO_TUPLE (UNPACK_SEQUENCE e)
  | .UNPACK_SEQUENCE_TUPLE => withDeopt (UNPACK_SEQUENCE_TUPLE e) (UNPACK_SEQUENCE e)
  | .UNPACK_SEQUENCE_LIST => withDeopt (UNPACK_SEQUENCE_LIST e) (UNPACK_SEQUENCE e)
  | .UNPACK_EX => UNPACK_EX e
  | .STORE_ATTR => STORE_ATTR e
  | .STORE_ATTR_INSTANCE_VALUE => withDeopt (STORE_ATTR_INSTANCE_VALUE e) (STORE_ATTR e)
  | .STORE_ATTR_SLOT => withDeopt (STORE_ATTR_SLOT e) (STORE_ATTR e)
  | .STORE_ATTR_WITH_HINT => withDeopt (STORE_ATTR_WITH_HINT e) (STORE_ATTR e)
  | .DELETE_ATTR => DELETE_ATTR e
  | .STORE_GLOBAL => STORE_GLOBAL e
  | .DELETE_GLOBAL => DELETE_GLOBAL e
  | .LOAD_LOCALS => LOAD_LOCALS
  | .LOAD_FROM_DICT_OR_GLOBALS => LOAD_FROM_DICT_OR_GLOBALS e
  | .LOAD_NAME => LOAD_NAME e
  | .LOAD_GLOBAL => LOAD_GLOBAL e
  | .LOAD_GLOBAL_MODULE => withDeopt (LOAD_GLOBAL_MODULE e) (LOAD_GLOBAL e)
  | .LOAD_GLOBAL_BUILTIN => withDeopt (LOAD_GLOBAL_BUILTIN e) (LOAD_GLOBAL e)
  | .DELETE_FAST => DELETE_FAST e
  | .MAKE_CELL => MAKE_CELL e
  | .DELETE_DEREF => DELETE_DEREF e
  | .LOAD_FROM_DICT_OR_DEREF => LOAD_FROM_DICT_OR_DEREF e
  | .LOAD_DEREF => LOAD_DEREF e
  | .STORE_DEREF => STORE_DEREF e
  | .COPY_FREE_VARS => COPY_FREE_VARS e
  | .BUILD_STRING => BUILD_STRING e
  | .BUILD_INTERPOLATION => BUILD_INTERPOLATION e
  | .BUILD_TEMPLATE => BUILD_TEMPLATE e
  | .BUILD_TUPLE => BUILD_TUPLE e
  | .BUILD_LIST => BUILD_LIST e
  | .LIST_EXTEND => LIST_EXTEND e
  | .SET_UPDATE => SET_UPDATE e
  | .BUILD_SET => BUILD_SET e
  | .BUILD_MAP => BUILD_MAP e
  | .SETUP_ANNOTATIONS => SETUP_ANNOTATIONS e
  | .DICT_UPDATE => DICT_UPDATE e
  | .DICT_MERGE => DICT_MERGE e
  | .MAP_ADD => MAP_ADD e
  | .INSTRUMENTED_LOAD_SUPER_ATTR => INSTRUMENTED_LOAD_SUPER_ATTR e
  | .LOAD_SUPER_ATTR => LOAD_SUPER_ATTR e
  | .LOAD_SUPER_ATTR_ATTR => withDeopt (LOAD_SUPER_ATTR_ATTR e) (LOAD_SUPER_ATTR e)
  | .LOAD_SUPER_ATTR_METHOD => withDeopt (LOAD_SUPER_ATTR_METHOD e) (LOAD_SUPER_ATTR e)
  | .LOAD_ATTR => LOAD_ATTR e
  | .LOAD_ATTR_INSTANCE_VALUE => withDeopt (LOAD_ATTR_INSTANCE_VALUE e) (LOAD_ATTR e)
  | .LOAD_ATTR_MODULE => withDeopt (LOAD_ATTR_MODULE e) (LOAD_ATTR e)
  | .LOAD_ATTR_WITH_HINT => withDeopt (LOAD_ATTR_WITH_HINT e) (LOAD_ATTR e)
  | .LOAD_ATTR_SLOT => withDeopt (LOAD_ATTR_SLOT e) (LOAD_ATTR e)
  | .LOAD_ATTR_CLASS => withDeopt (LOAD_ATTR_CLASS e) (LOAD_ATTR e)
  | .LOAD_ATTR_CLASS_WITH_METACLASS_CHECK =>
    withDeopt (LOAD_ATTR_CLASS_WITH_METACLASS_CHECK e) (LOAD_ATTR e)
  | .LOAD_ATTR_PROPERTY => withDeopt (LOAD_ATTR_PROPERTY e) (LOAD_ATTR e)
  | .LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN =>
    withDeopt (LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN e) (LOAD_ATTR e)
  | .LOAD_ATTR_METHOD_WITH_VALUES => withDeopt (LOAD_ATTR_METHOD_WITH_VALUES e) (LOAD_ATTR e)
  | .LOAD_ATTR_METHOD_NO_DICT => withDeopt (LOAD_ATTR_METHOD_NO_DICT e) (LOAD_ATTR e)
  | .LOAD_ATTR_METHOD_LAZY_DICT => withDeopt (LOAD_ATTR_METHOD_LAZY_DICT e) (LOAD_ATTR e)
  | .LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES =>
    withDeopt (LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES e) (LOAD_ATTR e)
  | .LOAD_ATTR_NONDESCRIPTOR_NO_DICT =>
    withDeopt (LOAD_ATTR_NONDESCRIPTOR_NO_DICT e) (LOAD_ATTR e)
  | .COMPARE_OP => COMPARE_OP e
  | .COMPARE_OP_FLOAT => withDeopt (COMPARE_OP_FLOAT e) (COMPARE_OP e)
  | .COMPARE_OP_INT => withDeopt (COMPARE_OP_INT e) (COMPARE_OP e)
  | .COMPARE_OP_STR => withDeopt (COMPARE_OP_STR e) (COMPARE_OP e)
  | .IS_OP => IS_OP e
  | .CONTAINS_OP => CONTAINS_OP e
  | .CONTAINS_OP_SET => withDeopt (CONTAINS_OP_SET e) (CONTAINS_OP e)
  | .CONTAINS_OP_DICT => withDeopt (CONTAINS_OP_DICT e) (CONTAINS_OP e)
  | .CHECK_EG_MATCH => CHECK_EG_MATCH e
  | .CHECK_EXC_MATCH => CHECK_EXC_MATCH
  | .IMPORT_NAME => IMPORT_NAME e
  | .IMPORT_FROM => IMPORT_FROM e
  | .JUMP_FORWARD => JUMP_FORWARD e
  | .JUMP_BACKWARD => JUMP_BACKWARD e
  | .JUMP_BACKWARD_NO_JIT => JUMP_BACKWARD_NO_JIT e
  | .JUMP_BACKWARD_JIT => JUMP_BACKWARD_JIT e
  | .JUMP_BACKWARD_NO_INTERRUPT => JUMP_BACKWARD_NO_INTERRUPT e
  | .ENTER_EXECUTOR => ENTER_EXECUTOR
  | .POP_JUMP_IF_TRUE => POP_JUMP_IF_TRUE e
  | .POP_JUMP_IF_FALSE => POP_JUMP_IF_FALSE e
  | .POP_JUMP_IF_NONE => POP_JUMP_IF_NONE e
  | .POP_JUMP_IF_NOT_NONE => POP_JUMP_IF_NOT_NONE e
  | .GET_LEN => GET_LEN e
  | .MATCH_CLASS => MATCH_CLASS e
  | .MATCH_MAPPING => MATCH_MAPPING e
  | .MATCH_SEQUENCE => MATCH_SEQUENCE e
  | .MATCH_KEYS => MATCH_KEYS e
  | .GET_ITER => GET_ITER e
  | .GET_ITER_SELF => withDeopt GET_ITER_SELF (GET_ITER e)
  | .GET_ITER_VIRTUAL => withDeopt GET_ITER_VIRTUAL (GET_ITER e)
  | .FOR_ITER => FOR_ITER e
  | .FOR_ITER_LIST => withDeopt (FOR_ITER_LIST e) (FOR_ITER e)
  | .FOR_ITER_TUPLE => withDeopt (FOR_ITER_TUPLE e) (FOR_ITER e)
  | .FOR_ITER_RANGE => withDeopt (FOR_ITER_RANGE e) (FOR_ITER e)
  | .FOR_ITER_GEN => withDeopt (FOR_ITER_GEN e) (FOR_ITER e)
  | .FOR_ITER_VIRTUAL => withDeopt (FOR_ITER_VIRTUAL e) (FOR_ITER e)
  | .INSTRUMENTED_FOR_ITER => INSTRUMENTED_FOR_ITER e
  | .LOAD_SPECIAL => LOAD_SPECIAL e
  | .WITH_EXCEPT_START => WITH_EXCEPT_START e
  | .PUSH_EXC_INFO => PUSH_EXC_INFO
  | .CALL => CALL e
  | .INSTRUMENTED_CALL => INSTRUMENTED_CALL e
  | .CALL_PY_GENERAL => withDeopt (CALL_PY_GENERAL e) (CALL e)
  | .CALL_BOUND_METHOD_GENERAL => withDeopt (CALL_BOUND_METHOD_GENERAL e) (CALL e)
  | .CALL_NON_PY_GENERAL => withDeopt (CALL_NON_PY_GENERAL e) (CALL e)
  | .CALL_BOUND_METHOD_EXACT_ARGS => withDeopt (CALL_BOUND_METHOD_EXACT_ARGS e) (CALL e)
  | .CALL_PY_EXACT_ARGS => withDeopt (CALL_PY_EXACT_ARGS e) (CALL e)
  | .CALL_TYPE_1 => withDeopt CALL_TYPE_1 (CALL e)
  | .CALL_STR_1 => withDeopt (CALL_STR_1 e) (CALL e)
  | .CALL_TUPLE_1 => withDeopt (CALL_TUPLE_1 e) (CALL e)
  | .CALL_ALLOC_AND_ENTER_INIT => withDeopt (CALL_ALLOC_AND_ENTER_INIT e) (CALL e)
  | .EXIT_INIT_CHECK => EXIT_INIT_CHECK
  | .CALL_BUILTIN_CLASS => withDeopt (CALL_BUILTIN_CLASS e) (CALL e)
  | .CALL_BUILTIN_O => withDeopt (CALL_BUILTIN_O e) (CALL e)
  | .CALL_BUILTIN_FAST => withDeopt (CALL_BUILTIN_FAST e) (CALL e)
  | .CALL_BUILTIN_FAST_WITH_KEYWORDS => withDeopt (CALL_BUILTIN_FAST_WITH_KEYWORDS e) (CALL e)
  | .CALL_LEN => withDeopt (CALL_LEN e) (CALL e)
  | .CALL_ISINSTANCE => withDeopt (CALL_ISINSTANCE e) (CALL e)
  | .CALL_LIST_APPEND => withDeopt CALL_LIST_APPEND (CALL e)
  | .CALL_METHOD_DESCRIPTOR_O => withDeopt (CALL_METHOD_DESCRIPTOR_O e) (CALL e)
  | .CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS =>
    withDeopt (CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS e) (CALL e)
  | .CALL_METHOD_DESCRIPTOR_NOARGS => withDeopt (CALL_METHOD_DESCRIPTOR_NOARGS e) (CALL e)
  | .CALL_METHOD_DESCRIPTOR_FAST => withDeopt (CALL_METHOD_DESCRIPTOR_FAST e) (CALL e)
  | .CALL_KW => CALL_KW e
  | .INSTRUMENTED_CALL_KW => INSTRUMENTED_CALL_KW e
  | .CALL_KW_PY => withDeopt (CALL_KW_PY e) (CALL_KW e)
  | .CALL_KW_BOUND_METHOD => withDeopt (CALL_KW_BOUND_METHOD e) (CALL_KW e)
  | .CALL_KW_NON_PY => withDeopt (CALL_KW_NON_PY e) (CALL_KW e)
  | .CALL_FUNCTION_EX => CALL_FUNCTION_EX e
  | .CALL_EX_PY => execCallExPy e
  | .CALL_EX_NON_PY_GENERAL => withDeopt (CALL_EX_NON_PY_GENERAL e) (CALL_FUNCTION_EX e)
  | .INSTRUMENTED_CALL_FUNCTION_EX => INSTRUMENTED_CALL_FUNCTION_EX e
  | .MAKE_FUNCTION => MAKE_FUNCTION e
  | .SET_FUNCTION_ATTRIBUTE => SET_FUNCTION_ATTRIBUTE e
  | .RETURN_GENERATOR => RETURN_GENERATOR e
  | .BUILD_SLICE => BUILD_SLICE e
  | .CONVERT_VALUE => CONVERT_VALUE e
  | .FORMAT_SIMPLE => FORMAT_SIMPLE e
  | .FORMAT_WITH_SPEC => FORMAT_WITH_SPEC e
  | .COPY => COPY e
  | .SWAP => SWAP e
  | .INSTRUMENTED_JUMP_FORWARD => INSTRUMENTED_JUMP_FORWARD e
  | .INSTRUMENTED_JUMP_BACKWARD => INSTRUMENTED_JUMP_BACKWARD e
  | .INSTRUMENTED_NOT_TAKEN => INSTRUMENTED_NOT_TAKEN
  | .INSTRUMENTED_POP_JUMP_IF_TRUE => INSTRUMENTED_POP_JUMP_IF_TRUE e
  | .INSTRUMENTED_POP_JUMP_IF_FALSE => INSTRUMENTED_POP_JUMP_IF_FALSE e
  | .INSTRUMENTED_POP_JUMP_IF_NONE => INSTRUMENTED_POP_JUMP_IF_NONE e
  | .INSTRUMENTED_POP_JUMP_IF_NOT_NONE => INSTRUMENTED_POP_JUMP_IF_NOT_NONE e
  | .INSTRUMENTED_LINE => fault "INSTRUMENTED_LINE without a tool"
  | .INSTRUMENTED_INSTRUCTION => fault "INSTRUMENTED_INSTRUCTION without a tool"
  | .EXTENDED_ARG => fault "EXTENDED_ARG handled by the fetch"

/-- `frame->instr_ptr = next_instr; next_instr += INSTRUCTION_SIZE`. `END_FOR` is
`no_save_ip`, `Python/bytecodes.c:393`. -/
def beginInstr (o : Op) (s : St) : St :=
  let this := s.regs.next
  let f := s.regs.frame
  { s with regs := { s.regs with
      frame := if o == .END_FOR then f else { f with instrPtr := this }
      next := this + instrSize o } }

/-- One `DISPATCH()`: fetch, `EXTENDED_ARG` accumulation, execute. -/
def stepInstr (P : Program) (om : ObjModel) (ctx : Ctx) (s : St) :
    Nat → Nat → EStateM.Result Err St Unit
  | 0, _ => .error (.fault "too many EXTENDED_ARGs") s
  | n + 1, carry =>
    let this := s.regs.next
    match (P[s.regs.frame.code]?).bind (·.instrs[this]?) with
    | none => .error (.fault "instruction pointer out of the code") s
    | some ins =>
      let arg := (carry <<< 8) ||| ins.arg
      if ins.op == .EXTENDED_ARG then
        stepInstr P om ctx { s with regs := { s.regs with next := this + 1 } } n arg
      else
        execOp { P := P, om := om, ctx := ctx, opcode := ins.op, oparg := arg, this := this,
                 cache := ins.cache } ins.op (beginInstr ins.op s)

/-- Where `_PyEval_EvalFrameDefault` goes after an instruction. -/
inductive Outcome where
  /-- Keep executing in this state. -/
  | cont (s : St)
  /-- `return result`. -/
  | ret (v : Val) (rt : Rt)
  /-- `return NULL` with this exception set. -/
  | raised (v : Val) (rt : Rt)
  /-- Fuel or undefined behaviour: not a Python outcome. -/
  | stop (e : Err) (rt : Rt)

/-- `label(exception_unwind)` and `label(exit_unwind)`, `Python/bytecodes.c:6485-6577`.
`next_instr` is what the handler lookup uses; `frame->instr_ptr` is what is pushed
as `lasti`. Fuel bounds the number of frames unwound. -/
def unwind (P : Program) : Nat → Val → St → Outcome
  | 0, _, s => .stop .fuel s.regs.rt
  | n + 1, v, s =>
    let f := s.regs.frame
    let table := (P[f.code]?.map (·.exceptiontable)).getD #[]
    let handled := if s.regs.next = 0 then none else getExceptionHandler table (s.regs.next - 1)
    match handled with
    | some (handler, level, lasti) =>
      -- lines 6505-6524
      let kept := s.stack.drop (s.stack.length - level)
      let st1 := if lasti then Val.tagged f.instrPtr :: kept else kept
      .cont { regs := { s.regs with next := handler }, stack := v :: st1 }
    | none =>
      -- lines 6493-6504, then `exit_unwind_notrace` at 6549-6577
      match (leaveRecursivePy s.regs.rt) with
      | .error e rt => .stop e rt
      | .ok () rt =>
        match s.regs.prev with
        | [] => .stop (.fault "no entry frame") rt
        | caller :: rest =>
          match frameClearAndPop f rt with
          | .error e rt => .stop e rt
          | .ok () rt =>
            let caller := { caller with returnOffset := 0 }
            if caller.owner == .interpreter then .raised v rt
            else
              unwind P n v
                { regs := { rt := rt, frame := caller, prev := rest, next := caller.instrPtr },
                  stack := caller.stack }

/-- Handle what an instruction left behind. -/
def afterInstr (P : Program) : EStateM.Result Err St Unit → Outcome
  | .ok () s => .cont s
  | .error .dispatch s => .cont s
  | .error (.exc v) s => unwind P (s.regs.prev.length + 2) v s
  | .error (.unwind v) s => unwind P (s.regs.prev.length + 2) v s
  | .error (.exitUnwind v) s =>
    -- `start_frame` failed: the new frame goes away without a handler search
    match leaveRecursivePy s.regs.rt with
    | .error e rt => .stop e rt
    | .ok () rt =>
      match s.regs.prev with
      | [] => .stop (.fault "no entry frame") rt
      | caller :: rest =>
        match frameClearAndPop s.regs.frame rt with
        | .error e rt => .stop e rt
        | .ok () rt =>
          let caller := { caller with returnOffset := 0 }
          if caller.owner == .interpreter then .raised v rt
          else
            unwind P (rest.length + 2) v
              { regs := { rt := rt, frame := caller, prev := rest, next := caller.instrPtr },
                stack := caller.stack }
  | .error (.leave v) s => .ret v s.regs.rt
  | .error e s => .stop e s.regs.rt

/-- The frame `_PyEval_EvalFrameDefault` puts below the frame it runs,
`Python/ceval.c:1289-1302`. -/
def entryFrame : Frame := { code := 0, instrPtr := 1, owner := .interpreter }

/-- `_PyEval_EvalFrameDefault` up to the dispatch: start a frame, or with
`throwflag` go straight to `error`, `Python/ceval.c:1311-1351`. -/
def enterEval (P : Program) (f : Frame) (exc : Option Val) (rt : Rt) : Outcome :=
  let s : St := { regs := { rt := rt, frame := f, prev := [entryFrame], next := f.instrPtr },
                  stack := f.stack }
  match exc with
  | some v =>
    match enterRecursivePy rt with
    | .ok () rt => unwind P 3 v { s with regs := { s.regs with rt := rt } }
    | .error (.exc e) rt => afterInstr P (.error (.exitUnwind e) { s with regs := { s.regs with rt := rt } })
    | .error e rt => .stop e rt
  | none => afterInstr P (startFrame s)

/-- `_PyEval_EvalFrame`, given the rest of the loop. -/
def evalWith (P : Program) (loop : St → EStateM.Result Err Rt Val)
    (f : Frame) (exc : Option Val) : RM Val := fun rt =>
  match enterEval P f exc rt with
  | .cont s => loop s
  | .ret v rt => .ok v rt
  | .raised v rt => .error (.exc v) rt
  | .stop e rt => .error e rt

/-- Fuel-bounded evaluation. One unit of fuel is one instruction on the current
path; `Ctx.evalFrame` of the next step closes the recursion through object code. -/
def runLoop (P : Program) (om : ObjModel) : Nat → St → EStateM.Result Err Rt Val
  | 0, s => .error .fuel s.regs.rt
  | n + 1, s =>
    let ctx : Ctx := { evalFrame := evalWith P (runLoop P om n) }
    match afterInstr P (stepInstr P om ctx s 6 0) with
    | .cont s' => runLoop P om n s'
    | .ret v rt => .ok v rt
    | .raised v rt => .error (.exc v) rt
    | .stop e rt => .error e rt

/-- `_PyEval_EvalFrame(tstate, frame, throwflag)` with a fuel budget. -/
def evalFrame (P : Program) (om : ObjModel) (fuel : Nat) (f : Frame) (exc : Option Val) : RM Val :=
  evalWith P (runLoop P om fuel) f exc

end PyLean.Bytecode
