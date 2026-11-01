import PyLean.Bytecode.Stack

/-!
Step rules of `Python/bytecodes.c`, part 1: lines 146-1712 (constants, locals,
unary and binary operators and their specializations, subscripts, `raise`,
`return`, `yield`, `send`, exception handling, names).

Every `inst`/`op`/`macro` is one definition of the same name, in source order,
with the signature of the DSL. The citation on a definition is its line in
`Python/bytecodes.c`. A `macro` is the sequence of its uops. Reference counting,
`STAT_INC`, `QSBR_QUIESCENT_STATE` and free-threading locks are left out: they do
nothing on the default GIL build that Python can see.
-/

namespace PyLean.Bytecode.Uop

open PyLean.Bytecode

/-- Binary64 helpers (the `double` arithmetic of the float specializations). -/
def fadd (a b : UInt64) : UInt64 := (Float.ofBits a + Float.ofBits b).toBits
def fsub (a b : UInt64) : UInt64 := (Float.ofBits a - Float.ofBits b).toBits
def fmul (a b : UInt64) : UInt64 := (Float.ofBits a * Float.ofBits b).toBits

/-- `COMPARISON_BIT(x, y)`, `Include/internal/pycore_code.h:502`. -/
def comparisonBit (ge le : Bool) : Nat :=
  1 <<< (2 * (if ge then 1 else 0) + (if le then 1 else 0))

/-- `_PyLong_IsNonNegativeCompact`: one digit of 30 bits and not negative. -/
def isNonNegCompact (i : Int) : Bool := 0 ≤ i && i < (2 : Int) ^ 30
/-- `_PyLong_IsCompact`: at most one digit. -/
def isCompact (i : Int) : Bool := -((2 : Int) ^ 30) < i && i < (2 : Int) ^ 30

/-- `Py_ARRAY_LENGTH(_Py_SINGLETON(strings).ascii)`. -/
def asciiLimit : Nat := 128

/-! ### Lines 146-253: no-ops, RESUME -/

/-- `Python/bytecodes.c:146`. -/
def NOP : M Unit := pure ()
/-- `:153`. -/
def NOT_TAKEN : M Unit := NOP
/-- `:155`. Pending calls and signals are outside the model. -/
def _CHECK_PERIODIC : M Unit := pure ()
/-- `:164`. -/
def _CHECK_PERIODIC_IF_NOT_YIELD_FROM : M Unit := pure ()
/-- `:175`. Rewriting `RESUME` to `RESUME_CHECK` is the quickening relation. -/
def _QUICKEN_RESUME : M Unit := pure ()
/-- `:183`. No monitoring tool is active in the model. -/
def _MAYBE_INSTRUMENT : M Unit := pure ()
/-- `:206`. Thread-local bytecode exists only on the free-threaded build. -/
def _LOAD_BYTECODE : M Unit := pure ()
/-- `:224`. -/
def RESUME : M Unit := do
  _LOAD_BYTECODE; _MAYBE_INSTRUMENT; _QUICKEN_RESUME; _CHECK_PERIODIC_IF_NOT_YIELD_FROM
/-- `:230`: deopts when the eval breaker differs from the code's version. -/
def RESUME_CHECK : M Unit := pure ()
/-- `:245`. Tools are the identity without a registered callback. -/
def _MONITOR_RESUME : M Unit := pure ()
/-- `:255`. -/
def INSTRUMENTED_RESUME : M Unit := do
  _LOAD_BYTECODE; _MAYBE_INSTRUMENT; _CHECK_PERIODIC_IF_NOT_YIELD_FROM; _MONITOR_RESUME

/-! ### Lines 265-406: locals and constants -/

/-- `:265`. -/
def LOAD_FAST_CHECK (e : Env) : M Unit := stk 0 1 fun _ => do
  let v ← getLocal e.oparg
  if v == .null then
    let co ← getCode e.P
    let n := co.localsplusnames.getD e.oparg ""
    (formatExcCheckArg "UnboundLocalError" (unboundLocalMsg n) : RM _)
  pure [v]

/-- `:277`. -/
def LOAD_FAST (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getLocal e.oparg]
/-- `:282`. A borrow is a copy once refcounts are gone. -/
def LOAD_FAST_BORROW (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getLocal e.oparg]
/-- `:287`. -/
def LOAD_FAST_AND_CLEAR (e : Env) : M Unit := stk 0 1 fun _ => do
  let v ← getLocal e.oparg
  setLocal e.oparg .null
  pure [v]
/-- `:292`. -/
def LOAD_FAST_LOAD_FAST (e : Env) : M Unit := stk 0 2 fun _ => do
  let v1 ← getLocal (e.oparg >>> 4)
  let v2 ← getLocal (e.oparg &&& 15)
  pure [v1, v2]
/-- `:299`. -/
def LOAD_FAST_BORROW_LOAD_FAST_BORROW (e : Env) : M Unit := stk 0 2 fun _ => do
  let v1 ← getLocal (e.oparg >>> 4)
  let v2 ← getLocal (e.oparg &&& 15)
  pure [v1, v2]

/-- `GETITEM(FRAME_CO_CONSTS, oparg)`. -/
def getConst (e : Env) : BM Val := do
  let co ← getCode e.P
  match co.consts[e.oparg]? with
  | some v => pure v
  | none => fault "const index out of range"

/-- `GETITEM(FRAME_CO_NAMES, i)`. -/
def getName (e : Env) (i : Nat) : BM String := do
  let co ← getCode e.P
  match co.names[i]? with
  | some v => pure v
  | none => fault "name index out of range"

/-- `:311`. -/
def LOAD_CONST (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getConst e]
/-- `:333`. -/
def LOAD_CONST_MORTAL (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getConst e]
/-- `:338`. -/
def LOAD_CONST_IMMORTAL (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getConst e]
/-- `:344`. -/
def LOAD_SMALL_INT (e : Env) : M Unit := stk 0 1 fun _ => pure [.int e.oparg]
/-- `:350`. -/
def STORE_FAST (e : Env) : M Unit := stk 1 0 fun
  | [v] => do setLocal e.oparg v; pure []
  | _ => fault "arity"
/-- `:365`. -/
def STORE_FAST_LOAD_FAST (e : Env) : M Unit := stk 1 1 fun
  | [v] => do
    setLocal (e.oparg >>> 4) v
    pure [← getLocal (e.oparg &&& 15)]
  | _ => fault "arity"
/-- `:379`. -/
def STORE_FAST_STORE_FAST (e : Env) : M Unit := stk 2 0 fun
  | [v2, v1] => do
    setLocal (e.oparg >>> 4) v1
    setLocal (e.oparg &&& 15) v2
    pure []
  | _ => fault "arity"
/-- `:400`. -/
def POP_TOP : M Unit := stk 1 0 fun _ => pure []
/-- `:404`. -/
def PUSH_NULL : M Unit := stk 0 1 fun _ => pure [.null]
/-- `:408`. -/
def END_FOR : M Unit := stk 1 0 fun _ => pure []
/-- `:417`. -/
def POP_ITER : M Unit := POP_TOP
/-- `:419`. The `StopIteration` monitoring event has no effect without a tool. -/
def INSTRUMENTED_END_FOR : M Unit := stk 2 1 fun
  | [r, _] => pure [r]
  | _ => fault "arity"
/-- `:431`. -/
def INSTRUMENTED_POP_ITER : M Unit := stk 1 0 fun _ => pure []
/-- `:436`. -/
def END_SEND : M Unit := stk 2 1 fun
  | [_, v] => pure [v]
  | _ => fault "arity"
/-- `:442`. -/
def INSTRUMENTED_END_SEND : M Unit := END_SEND

/-! ### Lines 455-595: unary operators and `TO_BOOL` -/

/-- `:455`. -/
def UNARY_NEGATIVE (e : Env) : M Unit := stk 1 1 fun
  | [v] => do pure [← e.om.negative e.ctx v]
  | _ => fault "arity"
/-- `:462`. -/
def UNARY_NOT : M Unit := stk 1 1 fun
  | [.bool b] => pure [.bool !b]
  | _ => fault "UNARY_NOT on a non-bool"
/-- `:478`. The counter is not modelled; rewriting is the quickening relation. -/
def _SPECIALIZE_TO_BOOL : M Unit := pure ()
/-- `:490`. -/
def _TO_BOOL (e : Env) : M Unit := stk 1 1 fun
  | [v] => do pure [.bool (← e.om.isTrue e.ctx v)]
  | _ => fault "arity"
/-- `:497`. -/
def TO_BOOL (e : Env) : M Unit := do _SPECIALIZE_TO_BOOL; _TO_BOOL e

/-- `:499`. -/
def TO_BOOL_BOOL : M Unit := guardTop 1 fun
  | [.bool _] => pure false
  | _ => pure true
/-- `:504`. -/
def TO_BOOL_INT : M Unit := stk 1 1 fun
  | [.int i] => pure [.bool (i != 0)]
  | _ => throw .deopt

/-- `PyList_CheckExact` on a value. -/
def notList (v : Val) : BM Bool := do return !(← (isExactList v : RM Bool))
/-- `PyTuple_CheckExact`. -/
def notTuple (v : Val) : BM Bool := do return !(← (isExactTuple v : RM Bool))
/-- `PyDict_CheckExact`. -/
def notDict (v : Val) : BM Bool := do return !(← (isExactDict v : RM Bool))
/-- `PySlice_Check`. -/
def notSlice (v : Val) : BM Bool := do
  match v with
  | .ref a =>
    match ← (getObj a : RM Obj) with
    | .slice .. => pure false
    | _ => pure true
  | _ => pure true
def notInt : Val → Bool
  | .int _ => false
  | _ => true
def notFloat : Val → Bool
  | .float _ => false
  | _ => true
def notStr : Val → Bool
  | .str _ => false
  | _ => true

/-- `:519`. -/
def _GUARD_NOS_LIST : M Unit := guardTop 2 fun
  | [nos, _] => notList nos
  | _ => fault "arity"
/-- `:524`. -/
def _GUARD_TOS_LIST : M Unit := guardTop 1 fun
  | [tos] => notList tos
  | _ => fault "arity"
/-- `:529`. -/
def _GUARD_TOS_SLICE : M Unit := guardTop 1 fun
  | [tos] => notSlice tos
  | _ => fault "arity"
/-- `:536`. -/
def _TO_BOOL_LIST : M Unit := stk 1 1 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .list items => pure [.bool (items.size != 0)]
    | _ => fault "not a list"
  | _ => fault "not a list"
/-- `:534`. -/
def TO_BOOL_LIST : M Unit := do _GUARD_TOS_LIST; _TO_BOOL_LIST
/-- `:544`. -/
def TO_BOOL_NONE : M Unit := stk 1 1 fun
  | [.none] => pure [.bool false]
  | _ => throw .deopt
/-- `:552`. -/
def _GUARD_NOS_UNICODE : M Unit := guardTop 2 fun
  | [nos, _] => pure (notStr nos)
  | _ => fault "arity"
/-- `:557`. -/
def _GUARD_TOS_UNICODE : M Unit := guardTop 1 fun
  | [v] => pure (notStr v)
  | _ => fault "arity"
/-- `:562`. -/
def _TO_BOOL_STR : M Unit := stk 1 1 fun
  | [.str s] => pure [.bool (s != "")]
  | _ => fault "not a str"
/-- `:577`. -/
def TO_BOOL_STR : M Unit := do _GUARD_TOS_UNICODE; _TO_BOOL_STR
/-- `:580`. -/
def _REPLACE_WITH_TRUE : M Unit := stk 1 1 fun _ => pure [.bool true]

/-- `Py_TYPE(v)->tp_version_tag` for types that have one. -/
def typeVersionOf (v : Val) : BM Nat := do
  match ← (typeOf v : RM Val) with
  | .ref a =>
    match ← (getObj a : RM Obj) with
    | .cls c => pure c.version
    | _ => pure 0
  | _ => pure 0

/-- The version stored in the inline cache at position `i`. -/
def cacheNat (e : Env) (i : Nat) : Nat :=
  match e.cache[i]? with
  | some (.tagged n) => n
  | _ => 0

/-- `:2317`. -/
def _GUARD_TYPE_VERSION (e : Env) : M Unit := guardTop 1 fun
  | [o] => do return (← typeVersionOf o) != cacheNat e 0
  | _ => fault "arity"

/-- `:585`. -/
def TO_BOOL_ALWAYS_TRUE (e : Env) : M Unit := do _GUARD_TYPE_VERSION e; _REPLACE_WITH_TRUE
/-- `:590`. -/
def UNARY_INVERT (e : Env) : M Unit := stk 1 1 fun
  | [v] => do pure [← e.om.invert e.ctx v]
  | _ => fault "arity"

/-! ### Lines 615-890: `BINARY_OP` specializations -/

/-- `:615`. -/
def _GUARD_NOS_INT : M Unit := guardTop 2 fun
  | [l, _] => pure (notInt l)
  | _ => fault "arity"
/-- `:620`. -/
def _GUARD_TOS_INT : M Unit := guardTop 1 fun
  | [v] => pure (notInt v)
  | _ => fault "arity"
/-- `:625`. -/
def _BINARY_OP_MULTIPLY_INT : M Unit := stk 2 1 fun
  | [.int l, .int r] => pure [.int (l * r)]
  | _ => fault "not ints"
/-- `:640`. -/
def _BINARY_OP_ADD_INT : M Unit := stk 2 1 fun
  | [.int l, .int r] => pure [.int (l + r)]
  | _ => fault "not ints"
/-- `:655`. -/
def _BINARY_OP_SUBTRACT_INT : M Unit := stk 2 1 fun
  | [.int l, .int r] => pure [.int (l - r)]
  | _ => fault "not ints"
/-- `:670`. -/
def BINARY_OP_MULTIPLY_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _BINARY_OP_MULTIPLY_INT
/-- `:672`. -/
def BINARY_OP_ADD_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _BINARY_OP_ADD_INT
/-- `:674`. -/
def BINARY_OP_SUBTRACT_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _BINARY_OP_SUBTRACT_INT
/-- `:677`. -/
def _GUARD_NOS_FLOAT : M Unit := guardTop 2 fun
  | [l, _] => pure (notFloat l)
  | _ => fault "arity"
/-- `:682`. -/
def _GUARD_TOS_FLOAT : M Unit := guardTop 1 fun
  | [v] => pure (notFloat v)
  | _ => fault "arity"
/-- `:687`. -/
def _BINARY_OP_MULTIPLY_FLOAT : M Unit := stk 2 1 fun
  | [.float l, .float r] => pure [.float (fmul l r)]
  | _ => fault "not floats"
/-- `:702`. -/
def _BINARY_OP_ADD_FLOAT : M Unit := stk 2 1 fun
  | [.float l, .float r] => pure [.float (fadd l r)]
  | _ => fault "not floats"
/-- `:717`. -/
def _BINARY_OP_SUBTRACT_FLOAT : M Unit := stk 2 1 fun
  | [.float l, .float r] => pure [.float (fsub l r)]
  | _ => fault "not floats"
/-- `:732`. -/
def BINARY_OP_MULTIPLY_FLOAT : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _BINARY_OP_MULTIPLY_FLOAT
/-- `:734`. -/
def BINARY_OP_ADD_FLOAT : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _BINARY_OP_ADD_FLOAT
/-- `:736`. -/
def BINARY_OP_SUBTRACT_FLOAT : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _BINARY_OP_SUBTRACT_FLOAT
/-- `:739`. -/
def _BINARY_OP_ADD_UNICODE : M Unit := stk 2 1 fun
  | [.str l, .str r] => pure [.str (l ++ r)]
  | _ => fault "not strs"
/-- `:754`. -/
def BINARY_OP_ADD_UNICODE : M Unit := do _GUARD_TOS_UNICODE; _GUARD_NOS_UNICODE; _BINARY_OP_ADD_UNICODE
/-- `:763`: `left = left + right` with the following `STORE_FAST` folded in. -/
def _BINARY_OP_INPLACE_ADD_UNICODE (e : Env) : M Unit := do
  let nextIdx ← BM.lift getNext
  let nextOparg ← BM.lift do
    let co ← getCode e.P
    pure ((co.instrs[nextIdx]?.map (·.arg)).getD 0)
  let ins ← peekN 2
  match ins with
  | [.str l, .str r] =>
    let cur ← BM.lift (getLocal nextOparg)
    BM.lift (deoptIf (cur != .str l))
    stk 2 0 fun _ => do
      setLocal nextOparg (.str (l ++ r))
      jumpBy 1
      pure []
  | _ => fault "not strs"
/-- `:837`. -/
def BINARY_OP_INPLACE_ADD_UNICODE (e : Env) : M Unit := do
  _GUARD_TOS_UNICODE; _GUARD_NOS_UNICODE; _BINARY_OP_INPLACE_ADD_UNICODE e

/-- A `_PyBinaryOpSpecializationDescr` from `Python/specialize.c:2458-2530`:
`cache[0]` names the action. Guard and action on two values. -/
structure ExtendDescr where
  guard : Val → Val → Bool
  action : Val → Val → Val

/-- `_GUARD_BINARY_OP_EXTEND`/`_BINARY_OP_EXTEND` are parameterized by `d`. The
descriptors themselves are in `Specialize.lean`. -/
def _GUARD_BINARY_OP_EXTEND (d : ExtendDescr) : M Unit := guardTop 2 fun
  | [l, r] => pure !(d.guard l r)
  | _ => fault "arity"
/-- `:820`. -/
def _BINARY_OP_EXTEND (d : ExtendDescr) : M Unit := stk 2 1 fun
  | [l, r] => pure [d.action l r]
  | _ => fault "arity"
/-- `:834`. -/
def BINARY_OP_EXTEND (d : ExtendDescr) : M Unit := do _GUARD_BINARY_OP_EXTEND d; _BINARY_OP_EXTEND d

/-- `_PyBuildSlice_ConsumeRefs(start, stop)`. -/
def buildSlice2 (start stop : Val) : RM Val := alloc (.slice start stop .none)
/-- `:840`: placeholder upstream as well. -/
def _SPECIALIZE_BINARY_SLICE : M Unit := pure ()
/-- `:847`. -/
def _BINARY_SLICE (e : Env) : M Unit := stk 3 1 fun
  | [c, s, t] => do
    let sl ← (buildSlice2 s t : RM Val)
    pure [← e.om.getItem e.ctx c sl]
  | _ => fault "arity"
/-- `:865`. -/
def BINARY_SLICE (e : Env) : M Unit := do _SPECIALIZE_BINARY_SLICE; _BINARY_SLICE e
/-- `:867`. -/
def _SPECIALIZE_STORE_SLICE : M Unit := pure ()
/-- `:874`. -/
def _STORE_SLICE (e : Env) : M Unit := stk 4 0 fun
  | [v, c, s, t] => do
    let sl ← (buildSlice2 s t : RM Val)
    e.om.setItem e.ctx c sl v
    pure []
  | _ => fault "arity"
/-- `:889`. -/
def STORE_SLICE (e : Env) : M Unit := do _SPECIALIZE_STORE_SLICE; _STORE_SLICE e

/-- `:894`. -/
def _BINARY_OP_SUBSCR_LIST_INT : M Unit := stk 2 1 fun
  | [.ref a, .int sub] => do
    if !isNonNegCompact sub then throw .deopt
    match ← (getObj a : RM Obj) with
    | .list items =>
      match items[sub.toNat]? with
      | some v => pure [v]
      | none => throw .deopt
    | _ => fault "not a list"
  | _ => fault "not list[int]"
/-- `:891`. -/
def BINARY_OP_SUBSCR_LIST_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_LIST; _BINARY_OP_SUBSCR_LIST_INT
/-- `:923`: `_PyList_SliceSubscript` is the slice branch of `list_subscript`. -/
def _BINARY_OP_SUBSCR_LIST_SLICE (e : Env) : M Unit := stkK 2 1 fun
  | [l, s] => do pure [← e.om.getItem e.ctx l s]
  | _ => fault "arity"
/-- `:920`. -/
def BINARY_OP_SUBSCR_LIST_SLICE (e : Env) : M Unit := do
  _GUARD_TOS_SLICE; _GUARD_NOS_LIST; _BINARY_OP_SUBSCR_LIST_SLICE e
/-- `:940`. -/
def _BINARY_OP_SUBSCR_STR_INT : M Unit := stk 2 1 fun
  | [.str s, .int sub] => do
    if !isNonNegCompact sub then throw .deopt
    match s.toList[sub.toNat]? with
    | none => throw .deopt
    | some c =>
      if asciiLimit ≤ c.toNat then throw .deopt
      pure [.str (String.singleton c)]
  | _ => fault "not str[int]"
/-- `:937`. -/
def BINARY_OP_SUBSCR_STR_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_UNICODE; _BINARY_OP_SUBSCR_STR_INT
/-- `:960`. -/
def _GUARD_NOS_TUPLE : M Unit := guardTop 2 fun
  | [nos, _] => notTuple nos
  | _ => fault "arity"
/-- `:965`. -/
def _GUARD_TOS_TUPLE : M Unit := guardTop 1 fun
  | [tos] => notTuple tos
  | _ => fault "arity"
/-- `:973`. -/
def _BINARY_OP_SUBSCR_TUPLE_INT : M Unit := stk 2 1 fun
  | [.ref a, .int sub] => do
    if !isNonNegCompact sub then throw .deopt
    match ← (getObj a : RM Obj) with
    | .tuple items =>
      match items[sub.toNat]? with
      | some v => pure [v]
      | none => throw .deopt
    | _ => fault "not a tuple"
  | _ => fault "not tuple[int]"
/-- `:970`. -/
def BINARY_OP_SUBSCR_TUPLE_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_TUPLE; _BINARY_OP_SUBSCR_TUPLE_INT
/-- `:992`. -/
def _GUARD_NOS_DICT : M Unit := guardTop 2 fun
  | [nos, _] => notDict nos
  | _ => fault "arity"
/-- `:997`. -/
def _GUARD_TOS_DICT : M Unit := guardTop 1 fun
  | [tos] => notDict tos
  | _ => fault "arity"
/-- `:1005`. -/
def _BINARY_OP_SUBSCR_DICT (e : Env) : M Unit := stk 2 1 fun
  | [d, sub] => do
    let r ← (dictGet e.om e.ctx d sub : RM _)
    match r with
    | some v => pure [v]
    | none => (do raiseVal (← newExc (.cls "KeyError") [sub]) : RM _)
  | _ => fault "arity"
/-- `:1002`. -/
def BINARY_OP_SUBSCR_DICT (e : Env) : M Unit := do _GUARD_NOS_DICT; _BINARY_OP_SUBSCR_DICT e

/-! ### Frame switching -/

/-- `_Py_EnterRecursivePy`, `Python/ceval_macros.h:338`, with the raising half of
`_Py_CheckRecursiveCallPy`, `Python/ceval.c:1029`. -/
def enterRecursivePy : RM Unit := fun rt =>
  let rem := rt.pyRecursionRemaining
  let rt' := { rt with pyRecursionRemaining := rem - 1 }
  if rem ≤ 0 then
    raiseS "RecursionError" "maximum recursion depth exceeded" rt'
  else .ok () rt'

/-- `_Py_LeaveRecursiveCallPy`, `Python/ceval_macros.h:343`. -/
def leaveRecursivePy : RM Unit := fun rt =>
  .ok () { rt with pyRecursionRemaining := rt.pyRecursionRemaining + 1 }

/-- Make `nf` the current frame; the old one goes on the `previous` chain with
its stack saved. -/
def enterFrame (nf : Frame) : M Unit := fun s =>
  let cur := { s.regs.frame with stack := s.stack }
  .ok () { regs := { s.regs with frame := nf, prev := cur :: s.regs.prev }, stack := nf.stack }

/-- `frame = frame->previous`, `RELOAD_STACK()`. -/
def popToPrevious : M Unit := fun s =>
  match s.regs.prev with
  | f :: rest => .ok () { regs := { s.regs with frame := f, prev := rest }, stack := f.stack }
  | [] => .error (.fault "no previous frame") s

/-- `LOAD_IP(off)`, `Python/ceval_macros.h:352`. -/
def loadIp (off : Nat) : BM Unit := fun r => .ok () { r with next := r.frame.instrPtr + off }

/-- `label(start_frame)`, `:5509`. -/
def startFrame : M Unit := do
  let checked : RM Unit := tryExc enterRecursivePy fun v => throw (.exitUnwind v)
  BM.lift checked
  let ip := (← BM.lift getFrame).instrPtr
  BM.lift (setNext ip)

/-- `DISPATCH_INLINED(new_frame)`, `Python/ceval_macros.h:176`. -/
def dispatchInlined {α : Type} (nf : Frame) : M α := do
  enterFrame nf
  startFrame
  throw .dispatch

/-- `:4010`. Note the absence of any recursion check. -/
def _PUSH_FRAME (nf : Frame) : M Unit := do
  enterFrame nf
  BM.lift (do
    let dec : RM Unit := fun rt =>
      .ok () { rt with pyRecursionRemaining := rt.pyRecursionRemaining - 1 }
    dec
    loadIp 0)

/-- `frame->return_offset = n`. -/
def setReturnOffset (n : Nat) : BM Unit := modifyFrame fun f => { f with returnOffset := n }

/-- `:4259`, `_SAVE_RETURN_OFFSET`. -/
def _SAVE_RETURN_OFFSET (e : Env) : BM Unit := do setReturnOffset ((← getNext) - e.this)

/-- The plain form of an instrumented opcode (`_PyOpcode_Deopt` keeps those as
they are, but they have the same size and stack effect). -/
def uninstr : Op → Op
  | .INSTRUMENTED_END_FOR => .END_FOR
  | .INSTRUMENTED_POP_ITER => .POP_ITER
  | .INSTRUMENTED_END_SEND => .END_SEND
  | .INSTRUMENTED_FOR_ITER => .FOR_ITER
  | .INSTRUMENTED_INSTRUCTION => .NOP
  | .INSTRUMENTED_JUMP_FORWARD => .JUMP_FORWARD
  | .INSTRUMENTED_NOT_TAKEN => .NOT_TAKEN
  | .INSTRUMENTED_POP_JUMP_IF_TRUE => .POP_JUMP_IF_TRUE
  | .INSTRUMENTED_POP_JUMP_IF_FALSE => .POP_JUMP_IF_FALSE
  | .INSTRUMENTED_POP_JUMP_IF_NONE => .POP_JUMP_IF_NONE
  | .INSTRUMENTED_POP_JUMP_IF_NOT_NONE => .POP_JUMP_IF_NOT_NONE
  | .INSTRUMENTED_RESUME => .RESUME
  | .INSTRUMENTED_RETURN_VALUE => .RETURN_VALUE
  | .INSTRUMENTED_YIELD_VALUE => .YIELD_VALUE
  | .INSTRUMENTED_END_ASYNC_FOR => .END_ASYNC_FOR
  | .INSTRUMENTED_LOAD_SUPER_ATTR => .LOAD_SUPER_ATTR
  | .INSTRUMENTED_CALL => .CALL
  | .INSTRUMENTED_CALL_KW => .CALL_KW
  | .INSTRUMENTED_CALL_FUNCTION_EX => .CALL_FUNCTION_EX
  | .INSTRUMENTED_JUMP_BACKWARD => .JUMP_BACKWARD
  | .INSTRUMENTED_LINE => .NOP
  | o => o

/-- `INSTRUCTION_SIZE`: the code units of the current instruction. -/
def instrSize (o : Op) : Nat := 1 + (uninstr o).deopt.caches

/-- `:3975`: no PEP 523 frame evaluator is installed in the model. -/
def _CHECK_PEP_523 : M Unit := pure ()

/-- `_PyThreadState_HasStackSpace`. -/
def hasStackSpace : BM Bool := fun r => .ok r.rt.stackSpace r

/-- `:1021`: `(container, unused -- container, unused, getitem)`. The cached
function of `ht->_spec_cache` is `cache[1]`, its version `cache[0]`. -/
def _BINARY_OP_SUBSCR_CHECK_FUNC (e : Env) : M Val := do
  let ins ← peekN 2
  match ins with
  | [container, _] => BM.lift do
    let tp ← (typeOf container : RM Val)
    let heap ← match tp with
      | .ref _ => pure true
      | _ => pure false
    deoptIf !heap
    let g := (e.cache[1]?).getD .null
    deoptIf (g == .null)
    let fo ← (getFunc g : RM FuncObj)
    deoptIf (fo.version != cacheNat e 0)
    deoptIf !(← hasStackSpace)
    pure g
  | _ => fault "arity"

/-- `:1037`: `(container, sub, getitem -- new_frame)`. -/
def _BINARY_OP_SUBSCR_INIT_CALL (e : Env) (getitem : Val) : M Frame := do
  let ins ← popN 2
  match ins with
  | [container, sub] => BM.lift do
    let func ← (getFunc getitem : RM FuncObj)
    let co ← (getCodeR e.P func.code : RM Code)
    let nf := frameInitialize co func.code func getitem .null
    setReturnOffset (instrSize e.opcode)
    pure { nf with fast := (nf.fast.setIfInBounds 0 container).setIfInBounds 1 sub }
  | _ => fault "arity"

/-- `:1045`. -/
def BINARY_OP_SUBSCR_GETITEM (e : Env) : M Unit := do
  _CHECK_PEP_523
  let g ← _BINARY_OP_SUBSCR_CHECK_FUNC e
  let nf ← _BINARY_OP_SUBSCR_INIT_CALL e g
  _PUSH_FRAME nf

/-- `_PyList_AppendTakeRef`. -/
def listAppend (l v : Val) : RM Unit := do
  match l with
  | .ref a =>
    match ← getObj a with
    | .list items => setObj a (.list (items.push v))
    | _ => fault "not a list"
  | _ => fault "not a list"

/-- `:1052`. -/
def LIST_APPEND (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let v := ins.getLastD .null
  let rest := ins.dropLast
  (listAppend (rest.headD .null) v : RM Unit)
  pure rest
/-- `:1058`. -/
def SET_ADD (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let v := ins.getLastD .null
  let rest := ins.dropLast
  (setAdd e.om e.ctx (rest.headD .null) v : RM Unit)
  pure rest
/-- `:1069`. -/
def _SPECIALIZE_STORE_SUBSCR : M Unit := pure ()
/-- `:1081`. -/
def _STORE_SUBSCR (e : Env) : M Unit := stk 3 0 fun
  | [v, c, sub] => do e.om.setItem e.ctx c sub v; pure []
  | _ => fault "arity"
/-- `:1088`. -/
def STORE_SUBSCR (e : Env) : M Unit := do _SPECIALIZE_STORE_SUBSCR; _STORE_SUBSCR e
/-- `:1093`. -/
def _STORE_SUBSCR_LIST_INT : M Unit := stk 3 0 fun
  | [v, .ref a, .int sub] => do
    if !isNonNegCompact sub then throw .deopt
    match ← (getObj a : RM Obj) with
    | .list items =>
      if items.size ≤ sub.toNat then throw .deopt
      (setObj a (.list (items.setIfInBounds sub.toNat v)) : RM Unit)
      pure []
    | _ => fault "not a list"
  | _ => fault "not list[int]"
/-- `:1090`. -/
def STORE_SUBSCR_LIST_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_LIST; _STORE_SUBSCR_LIST_INT
/-- `:1125`. -/
def _STORE_SUBSCR_DICT (e : Env) : M Unit := stk 3 0 fun
  | [v, d, sub] => do (dictSet e.om e.ctx d sub v : RM Unit); pure []
  | _ => fault "arity"
/-- `:1122`. -/
def STORE_SUBSCR_DICT (e : Env) : M Unit := do _GUARD_NOS_DICT; _STORE_SUBSCR_DICT e
/-- `:1137`. -/
def DELETE_SUBSCR (e : Env) : M Unit := stk 2 0 fun
  | [c, sub] => do e.om.delItem e.ctx c sub; pure []
  | _ => fault "arity"
/-- `:1145`. -/
def CALL_INTRINSIC_1 (e : Env) : M Unit := stk 1 1 fun
  | [v] => do
    let f ← getFrame
    pure [← e.om.intrinsic1 e.ctx f e.oparg v]
  | _ => fault "arity"
/-- `:1153`. -/
def CALL_INTRINSIC_2 (e : Env) : M Unit := stk 2 1 fun
  | [v2, v1] => do
    let f ← getFrame
    pure [← e.om.intrinsic2 e.ctx f e.oparg v2 v1]
  | _ => fault "arity"
/-- `:1164`. -/
def RAISE_VARARGS (e : Env) : M Unit := stk e.oparg 0 fun args => do
  let cause := if e.oparg == 2 then args.getD 1 .null else .null
  let exc := if e.oparg > 0 then args.getD 0 .null else .null
  (doRaise e.om e.ctx exc cause : RM Unit)
  -- `do_raise` always leaves through an exception
  fault "do_raise returned"
/-- `:1177`. -/
def INTERPRETER_EXIT : M Unit := do
  let ins ← popN 1
  throw (.leave (ins.headD .null))

/-! ### Lines 1202-1426: return, yield, send -/

def getGen (g : Addr) : RM GenObj := do
  match ← getObj g with
  | .gen o => pure o
  | _ => fault "not a generator"

/-- `_PyGen_GetGeneratorFromFrame`. -/
def frameGen : BM Addr := do
  match (← getFrame).owner with
  | .generator g => pure g
  | _ => fault "not a generator frame"

/-- `gen->gi_exc_state.previous_item = tstate->exc_info; tstate->exc_info = ...`:
the generator's item goes on top of the chain. -/
def pushExcState (g : GenObj) : RM Unit := fun rt =>
  .ok () { rt with excInfo := g.excValue :: rt.excInfo }

/-- The inverse: the item comes off the chain and back into the generator. -/
def popExcState : RM Val := fun rt =>
  match rt.excInfo with
  | v :: rest => .ok v { rt with excInfo := rest }
  | [] => .error (.fault "exc_info underflow") rt

/-- `clear_gen_frame`, `Python/ceval.c:1943-1956`. -/
def clearGenFrame (g : Addr) : RM Unit := do
  let o ← getGen g
  let _ ← popExcState
  setObj g (.gen { o with frameState := 4, excValue := .null,
                          frame := { o.frame with fast := #[], stack := [] } })

/-- `_PyEval_FrameClearAndPop`, `Python/ceval.c:1958-1967`, on the dying frame. -/
def frameClearAndPop (dying : Frame) : RM Unit :=
  match dying.owner with
  | .generator g => clearGenFrame g
  | _ => pure ()

/-- `:1202`. -/
def RETURN_VALUE : M Unit := do
  let ins ← popN 1
  let retval := ins.headD .null
  let dying ← BM.lift getFrame
  BM.lift (leaveRecursivePy : RM Unit)
  popToPrevious
  BM.lift (frameClearAndPop dying : RM Unit)
  BM.lift do loadIp (← getFrame).returnOffset
  pushAll [retval]

/-- `:1219`. -/
def _RETURN_VALUE_EVENT : M Unit := pure ()
/-- `:1226`. -/
def INSTRUMENTED_RETURN_VALUE : M Unit := do _RETURN_VALUE_EVENT; RETURN_VALUE

/-- `:1230`. -/
def GET_AITER (e : Env) : M Unit := stk 1 1 fun
  | [o] => do pure [← e.om.getAIter e.ctx o]
  | _ => fault "arity"
/-- `:1266`. -/
def GET_ANEXT (e : Env) : M Unit := stkK 1 2 fun
  | [a] => do pure [a, ← e.om.getANext e.ctx a]
  | _ => fault "arity"
/-- `:1274`. -/
def GET_AWAITABLE (e : Env) : M Unit := stk 1 1 fun
  | [o] => do pure [← e.om.getAwaitable e.ctx o e.oparg]
  | _ => fault "arity"
/-- `:1285`. -/
def _SPECIALIZE_SEND : M Unit := pure ()

/-- Exact `generator` or `coroutine` object with `gi_frame_state < FRAME_EXECUTING`:
the guard shared by `_SEND`, `_SEND_GEN_FRAME` and `_FOR_ITER_GEN_FRAME`. -/
def resumableGen (allowCoro : Bool) : Val → RM (Option (Addr × GenObj))
  | .ref a => do
    match ← getObj a with
    | .gen g =>
      if (g.kind == .gen || (allowCoro && g.kind == .coro)) && g.frameState < 0 then
        pure (some (a, g))
      else pure none
    | _ => pure none
  | _ => pure none

/-- Lines 1305-1317 of `_SEND` and the same code in `_SEND_GEN_FRAME`,
`_FOR_ITER_GEN_FRAME`: hand `v` to the generator frame and mark it running. -/
def genEnter (a : Addr) (g : GenObj) (v : Val) : RM Frame := do
  let gf := { g.frame with stack := v :: g.frame.stack }
  setObj a (.gen { g with frameState := 0, frame := gf })
  pushExcState g
  pure gf

/-- `_PyGen_FetchStopIterationValue` after a failed send: `some value`, or
re-raise. `Objects/genobject.c`. -/
def fetchStopIterationValue (exc : Val) : RM Val := do
  if ← givenMatches exc 8 (.cls "StopIteration") then
    return (← excData exc).value
  else throw (.exc exc)

/-- `:1297`. -/
def _SEND (e : Env) : M Unit := do
  let ins ← peekN 2
  match ins with
  | [receiver, v] =>
    match ← BM.lift ((resumableGen true receiver : RM _) : BM _) with
    | some (a, g) =>
      let _ ← popN 1
      let gf ← BM.lift ((genEnter a g v : RM Frame) : BM Frame)
      BM.lift (setReturnOffset (instrSize e.opcode + e.oparg))
      dispatchInlined gf
    | none =>
      stk 2 2 fun
        | [receiver, v] => do
          let isIt ← (e.om.isIterator receiver : RM Bool)
          let attempt : RM (Option Val) :=
            if v == .none && isIt then e.om.iterNext e.ctx receiver
            else do
              let (m, slf) ← e.om.getMethod e.ctx receiver "send"
              let args := if slf == .null then [v] else [slf, v]
              some <$> e.om.call e.ctx m args []
          -- the `retval_o == NULL` branch, lines 1327-1341
          let r : RM (Option Val × Bool) := tryExc
            (do
              match ← attempt with
              | some x => pure (some x, false)
              | none => pure (some .none, true))
            fun exc => do pure (some (← fetchStopIterationValue exc), true)
          let (val, jumped) ← (r : RM _)
          if jumped then jumpBy e.oparg
          pure [receiver, val.getD .none]
        | _ => fault "arity"
  | _ => fault "arity"

/-- `:1346`. -/
def SEND (e : Env) : M Unit := do _SPECIALIZE_SEND; _SEND e

/-- `:1348`. -/
def _SEND_GEN_FRAME (e : Env) : M Frame := do
  let ins ← peekN 2
  match ins with
  | [receiver, v] =>
    let r ← BM.lift ((resumableGen true receiver : RM _) : BM _)
    match r with
    | some (a, g) =>
      let _ ← popN 1
      BM.lift do
        let gf ← (genEnter a g v : RM Frame)
        setReturnOffset (instrSize e.opcode + e.oparg)
        pure gf
    | none => throw .deopt
  | _ => fault "arity"

/-- `:1364`. -/
def SEND_GEN (e : Env) : M Unit := do
  _CHECK_PEP_523
  let gf ← _SEND_GEN_FRAME e
  _PUSH_FRAME gf

/-- `:1370`. -/
def YIELD_VALUE (e : Env) : M Unit := do
  let ins ← popN 1
  let retval := ins.headD .null
  let s ← (get : M St)
  let gaddr ← BM.lift frameGen
  let f := s.regs.frame
  let f := { f with instrPtr := f.instrPtr + 1, stack := s.stack }
  let g ← BM.lift ((getGen gaddr : RM _) : BM _)
  let ev ← BM.lift ((popExcState : RM Val) : BM Val)
  BM.lift ((setObj gaddr (.gen { g with frameState := -2 + (e.oparg : Int), excValue := ev,
                                        frame := f }) : RM Unit) : BM Unit)
  BM.lift (leaveRecursivePy : RM Unit)
  popToPrevious
  BM.lift (loadIp 2)
  pushAll [retval]

/-- `:1404`. -/
def _YIELD_VALUE_EVENT : M Unit := pure ()
/-- `:1417`. -/
def INSTRUMENTED_YIELD_VALUE (e : Env) : M Unit := do _YIELD_VALUE_EVENT; YIELD_VALUE e

/-- `tstate->exc_info->exc_value = v`. -/
def setExcInfoTop (v : Val) : RM Unit := fun rt =>
  match rt.excInfo with
  | _ :: rest => .ok () { rt with excInfo := v :: rest }
  | [] => .ok () { rt with excInfo := [v] }

def getExcInfoTop : RM Val := fun rt => .ok (rt.excInfo.headD .null) rt

/-- `:1421`. -/
def POP_EXCEPT : M Unit := stk 1 0 fun
  | [v] => do
    (setExcInfoTop (if v == .none then .null else v) : RM Unit)
    pure []
  | _ => fault "arity"

/-- `:1428`. -/
def RERAISE (e : Env) : M Unit := do
  let ins ← popN 1
  let exc := ins.headD .null
  if e.oparg != 0 then
    let vals ← peekN e.oparg
    match vals.head? with
    | some (.tagged n) => BM.lift (modifyFrame fun f => { f with instrPtr := n })
    | _ => fault "lasti is not a tagged int"
  throw (.unwind exc)

/-- `:1441`. -/
def _END_ASYNC_FOR : M Unit := do
  let ins ← peekN 2
  match ins with
  | [_, exc] =>
    if ← BM.lift ((givenMatches exc 8 (.cls "StopAsyncIteration") : RM Bool) : BM Bool) then
      let _ ← popN 2
      pure ()
    else
      let _ ← popN 2
      throw (.unwind exc)
  | _ => fault "arity"
/-- `:1459`. -/
def _MONITOR_END_ASYNC_FOR : M Unit := pure ()
/-- `:1464`. -/
def INSTRUMENTED_END_ASYNC_FOR : M Unit := do _MONITOR_END_ASYNC_FOR; _END_ASYNC_FOR
/-- `:1468`. -/
def END_ASYNC_FOR : M Unit := _END_ASYNC_FOR

/-- `:1470`. -/
def CLEANUP_THROW : M Unit := do
  let ins ← peekN 3
  match ins with
  | [_, _, exc] =>
    if ← BM.lift ((givenMatches exc 8 (.cls "StopIteration") : RM Bool) : BM Bool) then
      let d ← BM.lift ((excData exc : RM _) : BM _)
      stk 3 2 fun _ => pure [.none, d.value]
    else
      let _ ← popN 3
      throw (.unwind exc)
  | _ => fault "arity"

/-- `:1490`, `_common_constants` of `Lib/opcode.py`. -/
def LOAD_COMMON_CONSTANT (e : Env) : M Unit := stk 0 1 fun _ =>
  match e.oparg with
  | 0 => pure [.cls "AssertionError"]
  | 1 => pure [.cls "NotImplementedError"]
  | 2 => pure [.cls "tuple"]
  | 3 => pure [.builtin "all"]
  | 4 => pure [.builtin "any"]
  | _ => fault "common constant"

/-- `PyMapping_GetOptionalItem` with a str key. -/
def optItem (e : Env) (o : Val) (n : String) : RM (Option Val) := do
  if ← isExactDict o then dictGetStr o n else getOptionalItem e.om e.ctx o (.str n)

/-- `:1496`. -/
def LOAD_BUILD_CLASS (e : Env) : M Unit := stk 0 1 fun _ => do
  let f ← getFrame
  match ← (optItem e f.builtins "__build_class__" : RM _) with
  | some b => pure [b]
  | none => (raiseS "NameError" "__build_class__ not found" : RM _)

/-- `:1508`. -/
def STORE_NAME (e : Env) : M Unit := stk 1 0 fun
  | [v] => do
    let name ← getName e e.oparg
    let ns := (← getFrame).locals
    if ns == .null then
      (raiseS "SystemError" s!"no locals found when storing '{name}'" : RM _)
    if ← (isExactDict ns : RM Bool) then (dictSetStr ns name v : RM Unit)
    else e.om.setItem e.ctx ns (.str name) v
    pure []
  | _ => fault "arity"

/-- `:1528`. -/
def DELETE_NAME (e : Env) : M Unit := stk 0 0 fun _ => do
  let name ← getName e e.oparg
  let ns := (← getFrame).locals
  if ns == .null then
    (raiseS "SystemError" s!"no locals when deleting '{name}'" : RM _)
  let del : RM Unit := tryExc (e.om.delItem e.ctx ns (.str name))
    fun _ => formatExcCheckArg "NameError" (nameErrorMsg name)
  del
  pure []

/-- `:1553`. -/
def _SPECIALIZE_UNPACK_SEQUENCE : M Unit := pure ()
/-- `:1567`. -/
def _UNPACK_SEQUENCE (e : Env) : M Unit := stk 1 e.oparg fun
  | [seq] => do
    let l ← (unpackIterable e.om e.ctx seq e.oparg none : RM _)
    pure l.reverse
  | _ => fault "arity"
/-- `:1574`. -/
def UNPACK_SEQUENCE (e : Env) : M Unit := do _SPECIALIZE_UNPACK_SEQUENCE; _UNPACK_SEQUENCE e
/-- `:1579`. -/
def _UNPACK_SEQUENCE_TWO_TUPLE : M Unit := stk 1 2 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .tuple #[x, y] => pure [y, x]
    | .tuple _ => throw .deopt
    | _ => fault "not a tuple"
  | _ => fault "not a tuple"
/-- `:1576`. -/
def UNPACK_SEQUENCE_TWO_TUPLE : M Unit := do _GUARD_TOS_TUPLE; _UNPACK_SEQUENCE_TWO_TUPLE
/-- `:1593`. -/
def _UNPACK_SEQUENCE_TUPLE (e : Env) : M Unit := stk 1 e.oparg fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .tuple items =>
      if items.size != e.oparg then throw .deopt
      pure items.toList.reverse
    | _ => fault "not a tuple"
  | _ => fault "not a tuple"
/-- `:1590`. -/
def UNPACK_SEQUENCE_TUPLE (e : Env) : M Unit := do _GUARD_TOS_TUPLE; _UNPACK_SEQUENCE_TUPLE e
/-- `:1608`. -/
def _UNPACK_SEQUENCE_LIST (e : Env) : M Unit := stk 1 e.oparg fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .list items =>
      if items.size != e.oparg then throw .deopt
      pure items.toList.reverse
    | _ => fault "not a list"
  | _ => fault "not a list"
/-- `:1605`. -/
def UNPACK_SEQUENCE_LIST (e : Env) : M Unit := do _GUARD_TOS_LIST; _UNPACK_SEQUENCE_LIST e
/-- `:1625`. -/
def UNPACK_EX (e : Env) : M Unit :=
  stk 1 ((e.oparg &&& 255) + 1 + (e.oparg >>> 8)) fun
    | [seq] => do
      let l ← (unpackIterable e.om e.ctx seq (e.oparg &&& 255) (some (e.oparg >>> 8)) : RM _)
      pure l.reverse
    | _ => fault "arity"

/-- `:1638`. -/
def _SPECIALIZE_STORE_ATTR : M Unit := pure ()
/-- `:1651`. -/
def _STORE_ATTR (e : Env) : M Unit := stk 2 0 fun
  | [v, owner] => do
    let name ← getName e e.oparg
    e.om.setAttr e.ctx owner name v
    pure []
  | _ => fault "arity"
/-- `:1659`. -/
def STORE_ATTR (e : Env) : M Unit := do _SPECIALIZE_STORE_ATTR; _STORE_ATTR e
/-- `:1661`. -/
def DELETE_ATTR (e : Env) : M Unit := stk 1 0 fun
  | [owner] => do
    let name ← getName e e.oparg
    e.om.delAttr e.ctx owner name
    pure []
  | _ => fault "arity"
/-- `:1668`. -/
def STORE_GLOBAL (e : Env) : M Unit := stk 1 0 fun
  | [v] => do
    let name ← getName e e.oparg
    (dictSetStr (← getFrame).globals name v : RM Unit)
    pure []
  | _ => fault "arity"
/-- `:1675`. -/
def DELETE_GLOBAL (e : Env) : M Unit := stk 0 0 fun _ => do
  let name ← getName e e.oparg
  let found ← (dictPopStr (← getFrame).globals name : RM Bool)
  if !found then (formatExcCheckArg "NameError" (nameErrorMsg name) : RM _)
  pure []
/-- `:1689`. -/
def LOAD_LOCALS : M Unit := stk 0 1 fun _ => do
  let l := (← getFrame).locals
  if l == .null then (raiseS "SystemError" "no locals found" : RM _)
  pure [l]

/-- `_PyDict_LoadGlobal`: globals, then builtins, then `NameError`. -/
def loadGlobal (e : Env) (name : String) : BM Val := do
  let f ← getFrame
  match ← (optItem e f.globals name : RM _) with
  | some v => pure v
  | none =>
    match ← (optItem e f.builtins name : RM _) with
    | some v => pure v
    | none => (formatExcCheckArg "NameError" (nameErrorMsg name) : RM _)

/-- `:1699`. -/
def LOAD_FROM_DICT_OR_GLOBALS (e : Env) : M Unit := stk 1 1 fun
  | [m] => do
    let name ← getName e e.oparg
    match ← (optItem e m name : RM _) with
    | some v => pure [v]
    | none => pure [← loadGlobal e name]
  | _ => fault "arity"

/-- `_PyEval_LoadName`, `Python/ceval.c:3667-3698`. -/
def loadName (e : Env) (name : String) : BM Val := do
  let f ← getFrame
  if f.locals == .null then (raiseS "SystemError" "no locals found" : RM _)
  match ← (optItem e f.locals name : RM _) with
  | some v => pure v
  | none =>
    match ← (dictGetStr f.globals name : RM _) with
    | some v => pure v
    | none =>
      match ← (optItem e f.builtins name : RM _) with
      | some v => pure v
      | none => (formatExcCheckArg "NameError" (nameErrorMsg name) : RM _)

/-- `:1743`. -/
def LOAD_NAME (e : Env) : M Unit := stk 0 1 fun _ => do
  let name ← getName e e.oparg
  pure [← loadName e name]
/-- `:1755`. -/
def _SPECIALIZE_LOAD_GLOBAL : M Unit := pure ()
/-- `:1769`. -/
def _LOAD_GLOBAL (e : Env) : M Unit := stk 0 1 fun _ => do
  let name ← getName e (e.oparg >>> 1)
  pure [← loadGlobal e name]
/-- `:1775`. -/
def _PUSH_NULL_CONDITIONAL (e : Env) : M Unit :=
  stk 0 (e.oparg &&& 1) fun _ => pure (List.replicate (e.oparg &&& 1) .null)
/-- `:1781`. -/
def LOAD_GLOBAL (e : Env) : M Unit := do _SPECIALIZE_LOAD_GLOBAL; _LOAD_GLOBAL e; _PUSH_NULL_CONDITIONAL e

/-- `:1789`. -/
def _GUARD_GLOBALS_VERSION (e : Env) : M Unit := guardTop 0 fun _ => do
  let d ← (getDict (← getFrame).globals : RM _)
  return d.version != cacheNat e 0

/-- `entries[index].me_value` under `dk_version == version`. -/
def dictSlot (dv : Val) (version index : Nat) : BM Val := do
  deoptIf !(← (isExactDict dv : RM Bool))
  let d ← (getDict dv : RM _)
  deoptIf (d.version != version)
  match d.entries[index]? with
  | some en => pure en.value
  | none => throw .deopt

/-- `:1797`. -/
def _LOAD_GLOBAL_MODULE (e : Env) : M Unit := stk 0 1 fun _ => do
  pure [← dictSlot (← getFrame).globals (cacheNat e 0) (cacheNat e 1)]
/-- `:1817`. -/
def _LOAD_GLOBAL_BUILTINS (e : Env) : M Unit := stk 0 1 fun _ => do
  pure [← dictSlot (← getFrame).builtins (cacheNat e 1) (cacheNat e 2)]
/-- `:1836`. -/
def LOAD_GLOBAL_MODULE (e : Env) : M Unit := do _LOAD_GLOBAL_MODULE e; _PUSH_NULL_CONDITIONAL e
/-- `:1842`. -/
def LOAD_GLOBAL_BUILTIN (e : Env) : M Unit := do
  _GUARD_GLOBALS_VERSION e; _LOAD_GLOBAL_BUILTINS e; _PUSH_NULL_CONDITIONAL e

end PyLean.Bytecode.Uop
