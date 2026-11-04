import PyLean.Bytecode.Stack
import PyLean.Binary64.Float

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
def toF (b : UInt64) : Binary64.F64 := Binary64.F64.ofBits b.toNat
def ofF (x : Binary64.F64) : UInt64 := x.bits.toUInt64
def fadd (a b : UInt64) : UInt64 := ofF (Binary64.F64.add (toF a) (toF b))
def fsub (a b : UInt64) : UInt64 := ofF (Binary64.F64.sub (toF a) (toF b))
def fmul (a b : UInt64) : UInt64 := ofF (Binary64.F64.mul (toF a) (toF b))

/-- `COMPARISON_BIT(x, y)`, `Include/internal/pycore_code.h:523`. -/
def comparisonBit (ge le : Bool) : Nat :=
  1 <<< (2 * (if ge then 1 else 0) + (if le then 1 else 0))

/-- `_PyLong_IsNonNegativeCompact`: one digit of 30 bits and not negative. -/
def isNonNegCompact (i : Int) : Bool := 0 ≤ i && i < (2 : Int) ^ 30
/-- `_PyLong_IsCompact`: at most one digit. -/
def isCompact (i : Int) : Bool := -((2 : Int) ^ 30) < i && i < (2 : Int) ^ 30

/-- `Py_ARRAY_LENGTH(_Py_SINGLETON(strings).ascii)`. -/
def asciiLimit : Nat := 128

/-! ### Lines 146-253: no-ops, RESUME -/

/-- `Python/bytecodes.c:148`. -/
def NOP : M Unit := pure ()
/-- `:156`. -/
def NOT_TAKEN : M Unit := NOP
/-- `check_periodics`, `Python/ceval_macros.h:541-548`: with an event pending, the result of
`_Py_HandlePending`. Which handler runs is not modelled; whether it fails is `Rt.pendingExc`,
and the event is consumed either way. -/
def checkPeriodics : RM Unit := fun rt =>
  if rt.pendingExc == .null then .ok () rt
  else raiseVal rt.pendingExc { rt with pendingExc := .null }
/-- `:157`: `ERROR_IF(err != 0)` with nothing popped. -/
def _CHECK_PERIODIC : M Unit := BM.lift (checkPeriodics : RM Unit)
/-- `@3.14.7:164`. -/
def _CHECK_PERIODIC_IF_NOT_YIELD_FROM : M Unit := pure ()
/-- `:175`. Rewriting `RESUME` to `RESUME_CHECK` is the quickening relation. -/
def _QUICKEN_RESUME : M Unit := pure ()
/-- `@3.14.7:183`. No monitoring tool is active in the model. -/
def _MAYBE_INSTRUMENT : M Unit := pure ()
/-- `:202`. Thread-local bytecode exists only on the free-threaded build. -/
def _LOAD_BYTECODE : M Unit := pure ()
/-- `@3.14.7:224`. -/
def RESUME : M Unit := do
  _LOAD_BYTECODE; _MAYBE_INSTRUMENT; _QUICKEN_RESUME; _CHECK_PERIODIC_IF_NOT_YIELD_FROM
/-- `:226`: deopts when the eval breaker differs from the code's version. -/
def RESUME_CHECK : M Unit := pure ()
/-- `:245`: `_RESUME_CHECK + _JIT`, and `_JIT` does nothing with tier 2 not built. -/
def RESUME_CHECK_JIT : M Unit := RESUME_CHECK
/-- `@3.14.7:245`. Tools are the identity without a registered callback. -/
def _MONITOR_RESUME : M Unit := pure ()
/-- `@3.14.7:255`. -/
def INSTRUMENTED_RESUME : M Unit := do
  _LOAD_BYTECODE; _MAYBE_INSTRUMENT; _CHECK_PERIODIC_IF_NOT_YIELD_FROM; _MONITOR_RESUME

/-! ### Lines 265-406: locals and constants -/

/-- `:271`. -/
def LOAD_FAST_CHECK (e : Env) : M Unit := stk 0 1 fun _ => do
  let v ← getLocal e.oparg
  if v == .null then
    let co ← getCode e.P
    let n := co.localsplusnames.getD e.oparg ""
    (formatExcCheckArg "UnboundLocalError" (unboundLocalMsg n) n : RM _)
  pure [v]

/-- `:283`. -/
def LOAD_FAST (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getLocal e.oparg]
/-- `:288`. A borrow is a copy once refcounts are gone. -/
def LOAD_FAST_BORROW (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getLocal e.oparg]
/-- `:293`. -/
def LOAD_FAST_AND_CLEAR (e : Env) : M Unit := stk 0 1 fun _ => do
  let v ← getLocal e.oparg
  setLocal e.oparg .null
  pure [v]
/-- `:298`. -/
def LOAD_FAST_LOAD_FAST (e : Env) : M Unit := stk 0 2 fun _ => do
  let v1 ← getLocal (e.oparg >>> 4)
  let v2 ← getLocal (e.oparg &&& 15)
  pure [v1, v2]
/-- `:305`. -/
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

/-- `:312`. -/
def LOAD_CONST (e : Env) : M Unit := stk 0 1 fun _ => do pure [← getConst e]
/-- `:317`. -/
def LOAD_SMALL_INT (e : Env) : M Unit := stk 0 1 fun _ => pure [.int e.oparg]
/-- `:323`. -/
def STORE_FAST (e : Env) : M Unit := stk 1 0 fun
  | [v] => do setLocal e.oparg v; pure []
  | _ => fault "arity"
/-- `:336`. -/
def STORE_FAST_LOAD_FAST (e : Env) : M Unit := stk 1 1 fun
  | [v] => do
    setLocal (e.oparg >>> 4) v
    pure [← getLocal (e.oparg &&& 15)]
  | _ => fault "arity"
/-- `:346`. -/
def STORE_FAST_STORE_FAST (e : Env) : M Unit := stk 2 0 fun
  | [v2, v1] => do
    setLocal (e.oparg >>> 4) v1
    setLocal (e.oparg &&& 15) v2
    pure []
  | _ => fault "arity"
/-- `:359`. -/
def POP_TOP : M Unit := stk 1 0 fun _ => pure []
/-- `:389`. -/
def PUSH_NULL : M Unit := stk 0 1 fun _ => pure [.null]
/-- `:393`. -/
def END_FOR : M Unit := stk 1 0 fun _ => pure []
/-- `:403`: `(iter, index_or_null -- )`. -/
def POP_ITER : M Unit := stk 2 0 fun _ => pure []
/-- `:409`. The `StopIteration` monitoring event has no effect without a tool. -/
def INSTRUMENTED_END_FOR : M Unit := stk 3 2 fun
  | [r, i, _] => pure [r, i]
  | _ => fault "arity"
/-- `:421`. -/
def INSTRUMENTED_POP_ITER : M Unit := stk 2 0 fun _ => pure []
/-- `:428`: `(receiver, index_or_null, value -- val)`. -/
def END_SEND : M Unit := stk 3 1 fun
  | [_, _, v] => pure [v]
  | _ => fault "arity"
/-- `:436`. -/
def INSTRUMENTED_END_SEND : M Unit := END_SEND

/-! ### Lines 455-595: unary operators and `TO_BOOL` -/

/-- `:451`: `_UNARY_NEGATIVE + POP_TOP`. `_UNARY_NEGATIVE` (`:453-461`) is `(value -- res, v)`
and leaves through `ERROR_NO_POP()` when `PyNumber_Negative` fails, so the operand stays on the
stack for the handler; `stkK` keeps it. The `POP_TOP` of `v` is folded in. -/
def UNARY_NEGATIVE (e : Env) : M Unit := stkK 1 1 fun
  | [v] => do pure [← e.om.negative e.ctx v]
  | _ => fault "arity"
/-- `:477`. -/
def UNARY_NOT : M Unit := stk 1 1 fun
  | [.bool b] => pure [.bool !b]
  | _ => fault "UNARY_NOT on a non-bool"
/-- `:493`. The counter is not modelled; rewriting is the quickening relation. -/
def _SPECIALIZE_TO_BOOL : M Unit := pure ()
/-- `:505`. -/
def _TO_BOOL (e : Env) : M Unit := stk 1 1 fun
  | [v] => do pure [.bool (← e.om.isTrue e.ctx v)]
  | _ => fault "arity"
/-- `:512`. -/
def TO_BOOL (e : Env) : M Unit := do _SPECIALIZE_TO_BOOL; _TO_BOOL e

/-- `:514`: `EXIT_IF(!PyStackRef_BoolCheck(value))`. -/
def TO_BOOL_BOOL : M Unit := guardTop 1 fun
  | [.bool _] => pure false
  | _ => pure true

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

/-- `:530`. -/
def _GUARD_NOS_LIST : M Unit := guardTop 2 fun
  | [nos, _] => notList nos
  | _ => fault "arity"
/-- `:535`. -/
def _GUARD_TOS_LIST : M Unit := guardTop 1 fun
  | [tos] => notList tos
  | _ => fault "arity"
/-- `:540`. -/
def _GUARD_TOS_SLICE : M Unit := guardTop 1 fun
  | [tos] => notSlice tos
  | _ => fault "arity"
/-- `:547`. -/
def _TO_BOOL_LIST : M Unit := stk 1 1 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .list items => pure [.bool (items.size != 0)]
    | _ => fault "not a list"
  | _ => fault "not a list"
/-- `:545`. -/
def TO_BOOL_LIST : M Unit := do _GUARD_TOS_LIST; _TO_BOOL_LIST
/-- `:556`: `EXIT_IF(!PyStackRef_IsNone(value))`, then `False`. -/
def TO_BOOL_NONE : M Unit := stk 1 1 fun
  | [.none] => pure [.bool false]
  | _ => throw .deopt
/-- `:570`. -/
def _GUARD_NOS_UNICODE : M Unit := guardTop 2 fun
  | [nos, _] => pure (notStr nos)
  | _ => fault "arity"
/-- `:575`. -/
def _GUARD_TOS_UNICODE : M Unit := guardTop 1 fun
  | [v] => pure (notStr v)
  | _ => fault "arity"
/-- `:580`. -/
def _TO_BOOL_STR : M Unit := stk 1 1 fun
  | [.str s] => pure [.bool (s != "")]
  | _ => fault "not a str"
/-- `:588`. -/
def TO_BOOL_STR : M Unit := do _GUARD_TOS_UNICODE; _TO_BOOL_STR
/-- `:591`. -/
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

/-- `:2862`. -/
def _GUARD_TYPE_VERSION (e : Env) : M Unit := guardTop 1 fun
  | [o] => do return (← typeVersionOf o) != cacheNat e 0
  | _ => fault "arity"

/-- `:597`: `_RECORD_TOS_TYPE` only records for tier 2, and the `POP_TOP` is folded in. -/
def TO_BOOL_ALWAYS_TRUE (e : Env) : M Unit := do _GUARD_TYPE_VERSION e; _REPLACE_WITH_TRUE
/-- `:604`: `_UNARY_INVERT + POP_TOP`. `_UNARY_INVERT` (`:606-614`) leaves through
`ERROR_NO_POP()` when `PyNumber_Invert` fails, keeping the operand, as `UNARY_NEGATIVE`. -/
def UNARY_INVERT (e : Env) : M Unit := stkK 1 1 fun
  | [v] => do pure [← e.om.invert e.ctx v]
  | _ => fault "arity"

/-! ### Lines 615-890: `BINARY_OP` specializations

On 3.15 the arithmetic uops are `(left, right -- res, l, r)`, and each macro ends in two
`_POP_TOP_INT`, `_POP_TOP_FLOAT` or `_POP_TOP_UNICODE`. Those pops only drop an exact `int`,
`float` or `str`, so the model folds them into the uop's `stk 2 1`. The failure these uops can
take with the inputs kept is `PyFloat_FromDouble` or the concatenation running out of memory,
which is not modelled. -/

/-- `_PyLong_CheckExactAndCompact`, `Include/internal/pycore_long.h:344`, negated: an exact
`int` of at most one digit is what both int guards ask for on 3.15. -/
def notCompactInt : Val → Bool
  | .int i => !isCompact i
  | _ => true
/-- `:635`. -/
def _GUARD_NOS_INT : M Unit := guardTop 2 fun
  | [l, _] => pure (notCompactInt l)
  | _ => fault "arity"
/-- `:640`. -/
def _GUARD_TOS_INT : M Unit := guardTop 1 fun
  | [v] => pure (notCompactInt v)
  | _ => fault "arity"
/-- `:369`: `assert(PyLong_CheckExact(value))` and a close, which has no effect the model
can see. -/
def _POP_TOP_INT : M Unit := stk 1 0 fun
  | [.int _] => pure []
  | _ => fault "_POP_TOP_INT on a non-int"
/-- `:379`: as `_POP_TOP_INT`, for an exact `str`. -/
def _POP_TOP_UNICODE : M Unit := stk 1 0 fun
  | [.str _] => pure []
  | _ => fault "_POP_TOP_UNICODE on a non-str"
/-- `:519`: `(value -- res, v)`. `_PyLong_IsZero` tests the sign bits, which are zero only for
`0`. -/
def _TO_BOOL_INT : M Unit := stk 1 2 fun
  | [.int i] => pure [.bool (i != 0), .int i]
  | _ => fault "_TO_BOOL_INT on a non-int"
/-- `:527`: `_GUARD_TOS_INT + unused/1 + unused/2 + _TO_BOOL_INT + _POP_TOP_INT`. Since 3.15 the
guard is `_GUARD_TOS_INT`, so an int of more than one digit exits to `TO_BOOL`. -/
def TO_BOOL_INT : M Unit := do _GUARD_TOS_INT; _TO_BOOL_INT; _POP_TOP_INT
/-- `medium_from_stwodigits`, `Objects/longobject.c:328-336`, as the fast paths see it: a
result outside `is_medium_int` (:53-58) comes back as `PyStackRef_NULL`, and the caller's
`EXIT_IF(PyStackRef_IsNull(res))` sends the instruction to its generic form. The
allocation failure on the same path is not modelled. -/
def compactResult (x : Int) : BM (List Val) := if isCompact x then pure [.int x] else throw .deopt
/-- `:657`, `_PyCompactLong_Multiply`. -/
def _BINARY_OP_MULTIPLY_INT : M Unit := stk 2 1 fun
  | [.int l, .int r] => compactResult (l * r)
  | _ => fault "not ints"
/-- `:672`, `_PyCompactLong_Add`. -/
def _BINARY_OP_ADD_INT : M Unit := stk 2 1 fun
  | [.int l, .int r] => compactResult (l + r)
  | _ => fault "not ints"
/-- `:687`, `_PyCompactLong_Subtract`. -/
def _BINARY_OP_SUBTRACT_INT : M Unit := stk 2 1 fun
  | [.int l, .int r] => compactResult (l - r)
  | _ => fault "not ints"
/-- `:702`. -/
def BINARY_OP_MULTIPLY_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _BINARY_OP_MULTIPLY_INT
/-- `:705`. -/
def BINARY_OP_ADD_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _BINARY_OP_ADD_INT
/-- `:708`. -/
def BINARY_OP_SUBTRACT_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_INT; _BINARY_OP_SUBTRACT_INT
/-- `:768`. -/
def _GUARD_NOS_FLOAT : M Unit := guardTop 2 fun
  | [l, _] => pure (notFloat l)
  | _ => fault "arity"
/-- `:773`. -/
def _GUARD_TOS_FLOAT : M Unit := guardTop 1 fun
  | [v] => pure (notFloat v)
  | _ => fault "arity"
/-- `:778`. -/
def _BINARY_OP_MULTIPLY_FLOAT : M Unit := stk 2 1 fun
  | [.float l, .float r] => pure [.float (fmul l r)]
  | _ => fault "not floats"
/-- `:798`. -/
def _BINARY_OP_ADD_FLOAT : M Unit := stk 2 1 fun
  | [.float l, .float r] => pure [.float (fadd l r)]
  | _ => fault "not floats"
/-- `:818`. -/
def _BINARY_OP_SUBTRACT_FLOAT : M Unit := stk 2 1 fun
  | [.float l, .float r] => pure [.float (fsub l r)]
  | _ => fault "not floats"
/-- `:838`. -/
def BINARY_OP_MULTIPLY_FLOAT : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _BINARY_OP_MULTIPLY_FLOAT
/-- `:840`. -/
def BINARY_OP_ADD_FLOAT : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _BINARY_OP_ADD_FLOAT
/-- `:842`. -/
def BINARY_OP_SUBTRACT_FLOAT : M Unit := do _GUARD_TOS_FLOAT; _GUARD_NOS_FLOAT; _BINARY_OP_SUBTRACT_FLOAT
/-- `:945`. -/
def _BINARY_OP_ADD_UNICODE : M Unit := stk 2 1 fun
  | [.str l, .str r] => pure [.str (l ++ r)]
  | _ => fault "not strs"
/-- `:962`. -/
def BINARY_OP_ADD_UNICODE : M Unit := do _GUARD_TOS_UNICODE; _GUARD_NOS_UNICODE; _BINARY_OP_ADD_UNICODE
/-- `:968`: `left = left + right`. On 3.15 this no longer folds the `STORE_FAST` in: it
writes `NULL` to the target local and leaves the result for the `STORE_FAST` that follows. -/
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
    stk 2 1 fun _ => do
      setLocal nextOparg .null
      pure [.str (l ++ r)]
  | _ => fault "not strs"
/-- `:1069`. -/
def BINARY_OP_INPLACE_ADD_UNICODE (e : Env) : M Unit := do
  _GUARD_TOS_UNICODE; _GUARD_NOS_UNICODE; _BINARY_OP_INPLACE_ADD_UNICODE e

/-- A `_PyBinaryOpSpecializationDescr` from `Python/specialize.c:2282-2311`:
`cache[0]` names the action. Guard and action on two values. -/
structure ExtendDescr where
  guard : Val → Val → Bool
  action : Val → Val → Val

/-- `_GUARD_BINARY_OP_EXTEND`/`_BINARY_OP_EXTEND` are parameterized by `d`. The
descriptors themselves are in `Specialize.lean`. -/
def _GUARD_BINARY_OP_EXTEND (d : ExtendDescr) : M Unit := guardTop 2 fun
  | [l, r] => pure !(d.guard l r)
  | _ => fault "arity"
/-- `:1039`. -/
def _BINARY_OP_EXTEND (d : ExtendDescr) : M Unit := stk 2 1 fun
  | [l, r] => pure [d.action l r]
  | _ => fault "arity"
/-- `:1066`. -/
def BINARY_OP_EXTEND (d : ExtendDescr) : M Unit := do _GUARD_BINARY_OP_EXTEND d; _BINARY_OP_EXTEND d

/-- `_PyBuildSlice_ConsumeRefs(start, stop)`. -/
def buildSlice2 (start stop : Val) : RM Val := alloc (.slice start stop .none)
/-- `:1072`: placeholder upstream as well. -/
def _SPECIALIZE_BINARY_SLICE : M Unit := pure ()
/-- `:1079`. -/
def _BINARY_SLICE (e : Env) : M Unit := stk 3 1 fun
  | [c, s, t] => do
    let sl ← (buildSlice2 s t : RM Val)
    pure [← e.om.getItem e.ctx c sl]
  | _ => fault "arity"
/-- `:1108`. -/
def BINARY_SLICE (e : Env) : M Unit := do _SPECIALIZE_BINARY_SLICE; _BINARY_SLICE e
/-- `:1110`. -/
def _SPECIALIZE_STORE_SLICE : M Unit := pure ()
/-- `:1117`. -/
def _STORE_SLICE (e : Env) : M Unit := stk 4 0 fun
  | [v, c, s, t] => do
    let sl ← (buildSlice2 s t : RM Val)
    e.om.setItem e.ctx c sl v
    pure []
  | _ => fault "arity"
/-- `:1132`. -/
def STORE_SLICE (e : Env) : M Unit := do _SPECIALIZE_STORE_SLICE; _STORE_SLICE e

/-- `:1137`. Since 3.15 this takes a negative index too, after `_GUARD_TOS_INT` has made
it compact: `index += PyList_GET_SIZE(list)`, then the bounds check. -/
def _BINARY_OP_SUBSCR_LIST_INT : M Unit := stk 2 1 fun
  | [.ref a, .int sub] => do
    match ← (getObj a : RM Obj) with
    | .list items =>
      let index : Int := if sub < 0 then sub + items.size else sub
      if index < 0 then throw .deopt
      match items[index.toNat]? with
      | some v => pure [v]
      | none => throw .deopt
    | _ => fault "not a list"
  | _ => fault "not list[int]"
/-- `:1134`. -/
def BINARY_OP_SUBSCR_LIST_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_LIST; _BINARY_OP_SUBSCR_LIST_INT
/-- `:1167`: `_PyList_SliceSubscript` is the slice branch of `list_subscript`. -/
def _BINARY_OP_SUBSCR_LIST_SLICE (e : Env) : M Unit := stkK 2 1 fun
  | [l, s] => do pure [← e.om.getItem e.ctx l s]
  | _ => fault "arity"
/-- `:1164`. -/
def BINARY_OP_SUBSCR_LIST_SLICE (e : Env) : M Unit := do
  _GUARD_TOS_SLICE; _GUARD_NOS_LIST; _BINARY_OP_SUBSCR_LIST_SLICE e
/-- `:564`: `PyUnicode_CheckExact` and `PyUnicode_IS_COMPACT_ASCII`. -/
def _GUARD_NOS_COMPACT_ASCII : M Unit := guardTop 2 fun
  | [.str s, _] => pure (s.toList.any fun c => asciiLimit ≤ c.toNat)
  | [_, _] => pure true
  | _ => fault "arity"
/-- `:1188`: the guard has already made every character ASCII. -/
def _BINARY_OP_SUBSCR_STR_INT : M Unit := stk 2 1 fun
  | [.str s, .int sub] => do
    if !isNonNegCompact sub then throw .deopt
    match s.toList[sub.toNat]? with
    | none => throw .deopt
    | some c => pure [.str (String.singleton c)]
  | _ => fault "not str[int]"
/-- `:1185`. -/
def BINARY_OP_SUBSCR_STR_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_COMPACT_ASCII; _BINARY_OP_SUBSCR_STR_INT
/-- `:1210`: any str, with the ASCII test on the character read. -/
def _BINARY_OP_SUBSCR_USTR_INT : M Unit := stk 2 1 fun
  | [.str s, .int sub] => do
    if !isNonNegCompact sub then throw .deopt
    match s.toList[sub.toNat]? with
    | none => throw .deopt
    | some c =>
      if asciiLimit ≤ c.toNat then throw .deopt
      pure [.str (String.singleton c)]
  | _ => fault "not str[int]"
/-- `:1207`. -/
def BINARY_OP_SUBSCR_USTR_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_UNICODE; _BINARY_OP_SUBSCR_USTR_INT
/-- `:1230`. -/
def _GUARD_NOS_TUPLE : M Unit := guardTop 2 fun
  | [nos, _] => notTuple nos
  | _ => fault "arity"
/-- `:1235`. -/
def _GUARD_TOS_TUPLE : M Unit := guardTop 1 fun
  | [tos] => notTuple tos
  | _ => fault "arity"
/-- `:1250`: `EXIT_IF(!_PyLong_IsNonNegativeCompact(sub))`, then `EXIT_IF(index >=
PyTuple_GET_SIZE(tuple))`. -/
def _GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS : M Unit := guardTop 2 fun
  | [.ref a, .int sub] => do
    if !isNonNegCompact sub then return true
    match ← (getObj a : RM Obj) with
    | .tuple items => pure (items.size ≤ sub.toNat)
    | _ => fault "not a tuple"
  | _ => fault "not tuple[int]"
/-- `:1263`: the bounds were checked by the guard above, so the read has no exit; an index
outside them is the `assert(res_o != NULL)`. -/
def _BINARY_OP_SUBSCR_TUPLE_INT : M Unit := stk 2 1 fun
  | [.ref a, .int sub] => do
    match ← (getObj a : RM Obj) with
    | .tuple items =>
      match items[sub.toNat]? with
      | some v => pure [v]
      | none => fault "tuple index past the guard"
    | _ => fault "not a tuple"
  | _ => fault "not tuple[int]"
/-- `:1240`. -/
def BINARY_OP_SUBSCR_TUPLE_INT : M Unit := do
  _GUARD_TOS_INT; _GUARD_NOS_TUPLE; _GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS; _BINARY_OP_SUBSCR_TUPLE_INT
/-- `:1280`: `mp_subscript == _PyDict_Subscript`. That also admits a subclass with no
`__getitem__` and a `frozendict`. The model has no `frozendict`, and `suggest` only picks this
form for an exact dict, so a subclass here takes the generic path to the same result. -/
def _GUARD_NOS_DICT_SUBSCRIPT : M Unit := guardTop 2 fun
  | [nos, _] => notDict nos
  | _ => fault "arity"
/-- `:1286`: `mp_ass_subscript == _PyDict_StoreSubscript`, as `_GUARD_NOS_DICT_SUBSCRIPT`. The
signature names three values, and `nos` is the second from the top. -/
def _GUARD_NOS_DICT_STORE_SUBSCRIPT : M Unit := guardTop 2 fun
  | [nos, _] => notDict nos
  | _ => fault "arity"
/-- `:1292`: `PyAnyDict_CheckExact`, which is `dict` here, the model having no `frozendict`. -/
def _GUARD_TOS_ANY_DICT : M Unit := guardTop 1 fun
  | [tos] => notDict tos
  | _ => fault "arity"
/-- `:1326`: `ERROR_NO_POP` when `_PyDict_Subscript` raises, so the operands stay. -/
def _BINARY_OP_SUBSCR_DICT (e : Env) : M Unit := stkK 2 1 fun
  | [d, sub] => do
    let r ← (dictGet e.om e.ctx d sub : RM _)
    match r with
    | some v => pure [v]
    | none => (do raiseVal (← newExc (.cls "KeyError") [sub]) : RM _)
  | _ => fault "arity"
/-- `:1307`. -/
def BINARY_OP_SUBSCR_DICT (e : Env) : M Unit := do _GUARD_NOS_DICT_SUBSCRIPT; _BINARY_OP_SUBSCR_DICT e

/-! ### Frame switching -/

/-- `_Py_EnterRecursivePy`, `Python/ceval_macros.h:426`, with the raising half of
`_Py_CheckRecursiveCallPy`, `Python/ceval.c:1026`. -/
def enterRecursivePy : RM Unit := fun rt =>
  let rem := rt.pyRecursionRemaining
  let rt' := { rt with pyRecursionRemaining := rem - 1 }
  if rem ≤ 0 then
    raiseS "RecursionError" "maximum recursion depth exceeded" rt'
  else .ok () rt'

/-- `_Py_LeaveRecursiveCallPy`, `Python/ceval_macros.h:431`. -/
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

/-- `LOAD_IP(off)`, `Python/ceval_macros.h:440`. -/
def loadIp (off : Nat) : BM Unit := fun r => .ok () { r with next := r.frame.instrPtr + off }

/-- `label(start_frame)`, `:6579`. -/
def startFrame : M Unit := do
  let checked : RM Unit := tryExc enterRecursivePy fun v => throw (.exitUnwind v)
  BM.lift checked
  let ip := (← BM.lift getFrame).instrPtr
  BM.lift (setNext ip)

/-- `DISPATCH_INLINED(new_frame)`, `Python/ceval_macros.h:171-177`. -/
def dispatchInlined {α : Type} (nf : Frame) : M α := do
  enterFrame nf
  startFrame
  throw .dispatch

/-- `:4628`. Note the absence of any recursion check: a macro has to carry
`_CHECK_RECURSION_REMAINING` itself. `SEND_GEN`, `FOR_ITER_GEN`, `CALL_EX_PY`,
`CALL_KW_BOUND_METHOD` and `LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN` do not. -/
def _PUSH_FRAME (nf : Frame) : M Unit := do
  enterFrame nf
  BM.lift (do
    let dec : RM Unit := fun rt =>
      .ok () { rt with pyRecursionRemaining := rt.pyRecursionRemaining - 1 }
    dec
    loadIp 0)

/-- `frame->return_offset = n`. -/
def setReturnOffset (n : Nat) : BM Unit := modifyFrame fun f => { f with returnOffset := n }

/-- `:6136`, `_SAVE_RETURN_OFFSET`. -/
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

/-- `:4592`: no PEP 523 frame evaluator is installed in the model. -/
def _CHECK_PEP_523 : M Unit := pure ()

/-- `_PyThreadState_HasStackSpace`. -/
def hasStackSpace : BM Bool := fun r => .ok r.rt.stackSpace r

/-- `:1341`: `(container, unused -- container, unused, getitem)`. `ht->_spec_cache` belongs to the
container's type, and `PyType_Modified` empties it (`Objects/typeobject.c:1274`). The model keeps
it on the instruction: `cache[1]` is the function, `cache[0]` its version, and `cache[2]` the
version of the type it was filled for. Any other type version stands for a cache that is empty,
which exits, or that holds that other type's `__getitem__`, which the generic form then calls. -/
def _BINARY_OP_SUBSCR_CHECK_FUNC (e : Env) : M Val := do
  let ins ← peekN 2
  match ins with
  | [container, _] => BM.lift do
    let tp ← (typeOf container : RM Val)
    let heap ← match tp with
      | .ref _ => pure true
      | _ => pure false
    deoptIf !heap
    deoptIf ((← typeVersionOf container) != cacheNat e 2)
    let g := (e.cache[1]?).getD .null
    deoptIf (g == .null)
    let fo ← (getFunc g : RM FuncObj)
    deoptIf (fo.version != cacheNat e 0)
    deoptIf !(← hasStackSpace)
    pure g
  | _ => fault "arity"

/-- `:1356`: `(container, sub, getitem -- new_frame)`. -/
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

/-- `:1366`. -/
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

/-- `:1374`. -/
def LIST_APPEND (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let v := ins.getLastD .null
  let rest := ins.dropLast
  (listAppend (rest.headD .null) v : RM Unit)
  pure rest
/-- `:1380`. -/
def SET_ADD (e : Env) : M Unit := stk (e.oparg + 1) e.oparg fun ins => do
  let v := ins.getLastD .null
  let rest := ins.dropLast
  (setAdd e.om e.ctx (rest.headD .null) v : RM Unit)
  pure rest
/-- `:1399`. -/
def _SPECIALIZE_STORE_SUBSCR : M Unit := pure ()
/-- `:1411`. -/
def _STORE_SUBSCR (e : Env) : M Unit := stk 3 0 fun
  | [v, c, sub] => do e.om.setItem e.ctx c sub v; pure []
  | _ => fault "arity"
/-- `:1418`. -/
def STORE_SUBSCR (e : Env) : M Unit := do _SPECIALIZE_STORE_SUBSCR; _STORE_SUBSCR e
/-- `:1423`. -/
def _STORE_SUBSCR_LIST_INT : M Unit := stk 3 0 fun
  | [v, .ref a, .int sub] => do
    match ← (getObj a : RM Obj) with
    | .list items =>
      -- 3.15 counts a negative index from the end, as `list_ass_subscript` does.
      let index := if sub < 0 then sub + items.size else sub
      if index < 0 || items.size ≤ index then throw .deopt
      (setObj a (.list (items.setIfInBounds index.toNat v)) : RM Unit)
      pure []
    | _ => fault "not a list"
  | _ => fault "not list[int]"
/-- `:1420`. -/
def STORE_SUBSCR_LIST_INT : M Unit := do _GUARD_TOS_INT; _GUARD_NOS_LIST; _STORE_SUBSCR_LIST_INT
/-- `:1458`. -/
def _STORE_SUBSCR_DICT (e : Env) : M Unit := stk 3 0 fun
  | [v, d, sub] => do (dictSet e.om e.ctx d sub v : RM Unit); pure []
  | _ => fault "arity"
/-- `:1454`. -/
def STORE_SUBSCR_DICT (e : Env) : M Unit := do _GUARD_NOS_DICT_STORE_SUBSCRIPT; _STORE_SUBSCR_DICT e
/-- `:1490`. -/
def DELETE_SUBSCR (e : Env) : M Unit := stk 2 0 fun
  | [c, sub] => do e.om.delItem e.ctx c sub; pure []
  | _ => fault "arity"
/-- `@3.14.7:1496`. -/
def CALL_INTRINSIC_1 (e : Env) : M Unit := stk 1 1 fun
  | [v] => do
    let f ← getFrame
    pure [← e.om.intrinsic1 e.ctx f e.oparg v]
  | _ => fault "arity"
/-- `:1529`. -/
def CALL_INTRINSIC_2 (e : Env) : M Unit := stk 2 1 fun
  | [v2, v1] => do
    let f ← getFrame
    pure [← e.om.intrinsic2 e.ctx f e.oparg v2 v1]
  | _ => fault "arity"
/-- `:1531`. -/
def RAISE_VARARGS (e : Env) : M Unit := stk e.oparg 0 fun args => do
  let cause := if e.oparg == 2 then args.getD 1 .null else .null
  let exc := if e.oparg > 0 then args.getD 0 .null else .null
  (doRaise e.om e.ctx exc cause : RM Unit)
  -- `do_raise` always leaves through an exception
  fault "do_raise returned"
/-- `:1544`. -/
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

/-- `clear_gen_frame`, `Python/ceval.c:2000-2016`. -/
def clearGenFrame (g : Addr) : RM Unit := do
  let o ← getGen g
  let _ ← popExcState
  setObj g (.gen { o with frameState := 5, excValue := .null,
                          frame := { o.frame with fast := #[], stack := [] } })

/-- `_PyEval_FrameClearAndPop`, `Python/ceval.c:2018-2030`, on the dying frame. The call to
`_PyThreadState_UpdateLastProfiledFrame` is for the remote profiler, which the model has
no notion of. -/
def frameClearAndPop (dying : Frame) : RM Unit :=
  match dying.owner with
  | .generator g => clearGenFrame g
  | _ => pure ()

/-- `:1591`: `_MAKE_HEAP_SAFE + _RETURN_VALUE` (`:1573`). `_MAKE_HEAP_SAFE` only changes the
reference count, which the model does not have. -/
def RETURN_VALUE : M Unit := do
  let ins ← popN 1
  let retval := ins.headD .null
  let dying ← BM.lift getFrame
  BM.lift (leaveRecursivePy : RM Unit)
  popToPrevious
  BM.lift (frameClearAndPop dying : RM Unit)
  BM.lift do loadIp (← getFrame).returnOffset
  pushAll [retval]

/-- `:1595`. -/
def _RETURN_VALUE_EVENT : M Unit := pure ()
/-- `:1602`. -/
def INSTRUMENTED_RETURN_VALUE : M Unit := do _RETURN_VALUE_EVENT; RETURN_VALUE

/-- `:1607`. -/
def GET_AITER (e : Env) : M Unit := stk 1 1 fun
  | [o] => do pure [← e.om.getAIter e.ctx o]
  | _ => fault "arity"
/-- `:1643`. -/
def GET_ANEXT (e : Env) : M Unit := stkK 1 2 fun
  | [a] => do pure [a, ← e.om.getANext e.ctx a]
  | _ => fault "arity"
/-- `@3.14.7:1638`. -/
def GET_AWAITABLE (e : Env) : M Unit := stk 1 1 fun
  | [o] => do pure [← e.om.getAwaitable e.ctx o e.oparg]
  | _ => fault "arity"
/-- `@3.14.7:1651`. -/
def _SPECIALIZE_SEND : M Unit := pure ()

/-- Exact `generator` or `coroutine` object with `gi_frame_state < FRAME_EXECUTING`:
the test of `gen_try_set_executing` (`Python/ceval_macros.h:569-593`) shared by `_SEND`,
`_SEND_GEN_FRAME` and `_FOR_ITER_GEN_FRAME`. -/
def resumableGen (allowCoro : Bool) : Val → RM (Option (Addr × GenObj))
  | .ref a => do
    match ← getObj a with
    | .gen g =>
      if (g.kind == .gen || (allowCoro && g.kind == .coro)) && g.frameState < 4 then
        pure (some (a, g))
      else pure none
    | _ => pure none
  | _ => pure none

/-- Lines 1305-1317 of `_SEND` and the same code in `_SEND_GEN_FRAME`,
`_FOR_ITER_GEN_FRAME`: hand `v` to the generator frame and mark it running. -/
def genEnter (a : Addr) (g : GenObj) (v : Val) : RM Frame := do
  let gf := { g.frame with stack := v :: g.frame.stack }
  setObj a (.gen { g with frameState := 4, frame := gf })
  pushExcState g
  pure gf

/-- `_PyGen_FetchStopIterationValue` after a failed send: `some value`, or
re-raise. `Objects/genobject.c`. -/
def fetchStopIterationValue (exc : Val) : RM Val := do
  if ← givenMatches exc 8 (.cls "StopIteration") then
    return (← excData exc).value
  else throw (.exc exc)

/-- `tp_iternext`, with the `_PyErr_Occurred`/`StopIteration` handling of
`_PyForIter_VirtualIteratorNext`, `Python/ceval.c:3725-3738`: `none` means the iterator ended
normally. On 3.15 there is no `tp_iternext == NULL` test any more. A value in this slot came
from `tp_iter` and `GET_ITER`, so the slot is set: a class that drops `__next__` afterwards
inherits `_PyObject_NextNotImplemented`, which is a `TypeError`, not a NULL call. -/
def iterStep (e : Env) (it : Val) : RM (Option Val) :=
  tryExc (e.om.iterNext e.ctx it) fun exc => do
    if ← givenMatches exc 8 (.cls "StopIteration") then pure none else throw (.exc exc)

/-- `tp->_tp_iteritem != NULL`. The slot is set on `PyList_Type`, `PyTuple_Type`,
`PyUnicode_Type` and `PyBytes_Type` and `inherit_slots` does not copy it, so a subclass has
none: subclasses are `.inst` here, and take the iterator path. -/
def hasIterItem : Val → RM Bool
  | .str _ | .bytes _ => pure true
  | .ref a => do
    match ← getObj a with
    | .list _ | .tuple _ => pure true
    | _ => pure false
  | _ => pure false

/-- `Py_TYPE(iter)->_tp_iteritem(iter, i)`, at `Objects/listobject.c:3937`,
`tupleobject.c:890`, `unicodeobject.c:14052` and `bytesobject.c:3218`: the item and the next
index, or `none` at the end. A list is read afresh each time, so it may grow or shrink during
the loop. The negative index of `unicode_char` failing to allocate is not modelled. -/
def iterItem (iter : Val) (i : Nat) : RM (Option (Val × Nat)) :=
  let next (v? : Option Val) : RM (Option (Val × Nat)) := pure (v?.map fun v => (v, i + 1))
  match iter with
  | .str s => next ((s.toList[i]?).map fun c => .str (String.singleton c))
  | .bytes b => next ((b[i]?).map fun x => .int x.toNat)
  | .ref a => do
    match ← getObj a with
    | .list items | .tuple items => next items[i]?
    | _ => fault "no _tp_iteritem"
  | _ => fault "no _tp_iteritem"

/-- `_PyForIter_VirtualIteratorNext`, `Python/ceval.c:3709-3739`: the next item with the new
`index_or_null`, or `none` when the iteration ended normally. -/
def virtualNext (e : Env) (iter index : Val) : RM (Option (Val × Val)) :=
  match index with
  | .tagged i => do
    match ← iterItem iter i with
    | some (v, i') => pure (some (v, .tagged i'))
    | none => pure none
  | _ => do
    match ← iterStep e iter with
    | some v => pure (some (v, index))
    | none => pure none

/-- `PyIter_Send`, `Objects/abstract.c:2925-2953`, as `_PyIter_Send` returns it: the value and
whether it is `PYGEN_RETURN`. The receiver of a virtual iterator is the sequence itself, so a
non-`None` value looks up `send` on the list. -/
def iterSend (e : Env) (receiver v : Val) : RM (Val × Bool) := do
  let isIt ← e.om.isIterator receiver
  let attempt : RM (Option Val) :=
    if v == .none && isIt then e.om.iterNext e.ctx receiver
    else do
      let (m, slf) ← e.om.getMethod e.ctx receiver "send"
      let args := if slf == .null then [v] else [slf, v]
      some <$> e.om.call e.ctx m args []
  tryExc
    (do
      match ← attempt with
      | some x => pure (x, false)
      | none => pure (.none, true))
    fun exc => do pure (← fetchStopIterationValue exc, true)

/-- `:1676`: `(receiver, null_or_index, v -- receiver, null_or_index, retval)`. -/
def _SEND (e : Env) : M Unit := do
  let ins ← peekN 3
  match ins with
  | [receiver, nullOrIndex, v] =>
    match ← BM.lift ((resumableGen true receiver : RM _) : BM _) with
    | some (a, g) =>
      let _ ← popN 1
      let gf ← BM.lift ((genEnter a g v : RM Frame) : BM Frame)
      BM.lift (setReturnOffset (instrSize e.opcode + e.oparg))
      dispatchInlined gf
    | none =>
      if nullOrIndex != .null && v == .none then
        match ← BM.lift ((virtualNext e receiver nullOrIndex : RM _) : BM _) with
        | none =>
          -- `v` stays on the stack, and it is `None`, as the value of the `yield from`
          BM.lift (jumpBy e.oparg)
          throw .dispatch
        | some (item, index') =>
          let _ ← popN 2
          pushAll [index', item]
      else
        stkK 3 3 fun _ => do
          let (val, returned) ← (iterSend e receiver v : RM _)
          if returned then jumpBy e.oparg
          pure [receiver, nullOrIndex, val]
  | _ => fault "arity"

/-- `:1722`. -/
def SEND (e : Env) : M Unit := do _SPECIALIZE_SEND; _SEND e

/-- `:1724`: `(receiver, null, v -- receiver, null, gen_frame)`. -/
def _SEND_GEN_FRAME (e : Env) : M Frame := do
  let ins ← peekN 3
  match ins with
  | [receiver, _, v] =>
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

/-- `:1740`. -/
def SEND_GEN (e : Env) : M Unit := do
  _CHECK_PEP_523
  let gf ← _SEND_GEN_FRAME e
  _PUSH_FRAME gf

/-- `:1747`. -/
def _GUARD_TOS_IS_NONE : M Unit := guardTop 1 fun
  | [v] => pure (v != .none)
  | _ => fault "arity"
/-- `:1753`. -/
def _GUARD_NOS_NOT_NULL : M Unit := guardTop 2 fun
  | [n, _] => pure (n == .null)
  | _ => fault "arity"
/-- `:1757`. An index that went negative is the allocation failure of `unicode_iteritem`,
which `iterItem` does not model. At the end `next = none` and the jump leaves the stack as
`_SEND` leaves it. -/
def _SEND_VIRTUAL (e : Env) : M Unit := do
  let ins ← peekN 3
  match ins with
  | [iter, .tagged i, _] =>
    match ← BM.lift ((iterItem iter i : RM _) : BM _) with
    | none =>
      BM.lift (jumpBy e.oparg)
      throw .dispatch
    | some (item, i') =>
      let _ ← popN 2
      pushAll [.tagged i', item]
  | _ => fault "SEND_VIRTUAL without a tagged index"
/-- `:1795`. -/
def SEND_VIRTUAL (e : Env) : M Unit := do _GUARD_TOS_IS_NONE; _GUARD_NOS_NOT_NULL; _SEND_VIRTUAL e
/-- `:1801`. The machine's async generators have no `asend` object: those awaitables live in
`GenObj/AsyncGen.lean`. So no receiver here passes this guard. -/
def _GUARD_3OS_ASYNC_GEN_ASEND : M Unit := guardTop 3 fun _ => pure true
/-- `:1827`. -/
def SEND_ASYNC_GEN : M Unit := _GUARD_3OS_ASYNC_GEN_ASEND

/-- `:1889`: `_MAKE_HEAP_SAFE + _YIELD_VALUE` (`:1851`). -/
def YIELD_VALUE (e : Env) : M Unit := do
  let ins ← popN 1
  let retval := ins.headD .null
  let s ← (get : M St)
  let gaddr ← BM.lift frameGen
  let f := s.regs.frame
  let f := { f with instrPtr := f.instrPtr + 1, stack := s.stack }
  let g ← BM.lift ((getGen gaddr : RM _) : BM _)
  let ev ← BM.lift ((popExcState : RM Val) : BM Val)
  BM.lift ((setObj gaddr (.gen { g with frameState := 1 + (e.oparg : Int), excValue := ev,
                                        frame := f }) : RM Unit) : BM Unit)
  BM.lift (leaveRecursivePy : RM Unit)
  popToPrevious
  BM.lift (loadIp 2)
  pushAll [retval]

/-- `@3.14.7:1836`. -/
def _YIELD_VALUE_EVENT : M Unit := pure ()
/-- `:1906`. -/
def INSTRUMENTED_YIELD_VALUE (e : Env) : M Unit := do _YIELD_VALUE_EVENT; YIELD_VALUE e

/-- `tstate->exc_info->exc_value = v`. -/
def setExcInfoTop (v : Val) : RM Unit := fun rt =>
  match rt.excInfo with
  | _ :: rest => .ok () { rt with excInfo := v :: rest }
  | [] => .ok () { rt with excInfo := [v] }

def getExcInfoTop : RM Val := fun rt => .ok (rt.excInfo.headD .null) rt

/-- `:1911`. -/
def POP_EXCEPT : M Unit := stk 1 0 fun
  | [v] => do
    (setExcInfoTop (if v == .none then .null else v) : RM Unit)
    pure []
  | _ => fault "arity"

/-- `:1918`. -/
def RERAISE (e : Env) : M Unit := do
  let ins ← popN 1
  let exc := ins.headD .null
  if e.oparg != 0 then
    let vals ← peekN e.oparg
    match vals.head? with
    | some (.tagged n) => BM.lift (modifyFrame fun f => { f with instrPtr := n })
    | _ => fault "lasti is not a tagged int"
  throw (.unwind exc)

/-- `:1931`. -/
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
/-- `:1949`. -/
def _MONITOR_END_ASYNC_FOR : M Unit := pure ()
/-- `:1954`. -/
def INSTRUMENTED_END_ASYNC_FOR : M Unit := do _MONITOR_END_ASYNC_FOR; _END_ASYNC_FOR
/-- `:1958`. -/
def END_ASYNC_FOR : M Unit := _END_ASYNC_FOR

/-- `:1960`: `(sub_iter, null_in, last_sent_val, exc_value_st -- none, null_out, value)`. -/
def CLEANUP_THROW : M Unit := do
  let ins ← peekN 4
  match ins with
  | [_, nullIn, _, exc] =>
    if ← BM.lift ((givenMatches exc 8 (.cls "StopIteration") : RM Bool) : BM Bool) then
      let d ← BM.lift ((excData exc : RM _) : BM _)
      stk 4 3 fun _ => pure [.none, nullIn, d.value]
    else
      let _ ← popN 4
      throw (.unwind exc)
  | _ => fault "arity"

/-- `:1980`, `_common_constants` of `Lib/opcode.py:42-47`, in the order of `CONSTANT_*` in
`Include/internal/pycore_opcode_utils.h:71-82`. -/
def LOAD_COMMON_CONSTANT (e : Env) : M Unit := stk 0 1 fun _ =>
  match e.oparg with
  | 0 => pure [.cls "AssertionError"]
  | 1 => pure [.cls "NotImplementedError"]
  | 2 => pure [.cls "tuple"]
  | 3 => pure [.builtin "all"]
  | 4 => pure [.builtin "any"]
  | 5 => pure [.cls "list"]
  | 6 => pure [.cls "set"]
  | 7 => pure [.none]
  | 8 => pure [.str ""]
  | 9 => pure [.bool true]
  | 10 => pure [.bool false]
  | 11 => pure [.int (-1)]
  | _ => fault "common constant"

/-- `PyMapping_GetOptionalItem` with a str key. -/
def optItem (e : Env) (o : Val) (n : String) : RM (Option Val) := do
  if ← isExactDict o then dictGetStr o n else getOptionalItem e.om e.ctx o (.str n)

/-- `:1986`. -/
def LOAD_BUILD_CLASS (e : Env) : M Unit := stk 0 1 fun _ => do
  let f ← getFrame
  match ← (optItem e f.builtins "__build_class__" : RM _) with
  | some b => pure [b]
  | none => (raiseS "NameError" "__build_class__ not found" : RM _)

/-- `:1998`. -/
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

/-- `:2018`. -/
def DELETE_NAME (e : Env) : M Unit := stk 0 0 fun _ => do
  let name ← getName e e.oparg
  let ns := (← getFrame).locals
  if ns == .null then
    (raiseS "SystemError" s!"no locals when deleting '{name}'" : RM _)
  let del : RM Unit := tryExc (e.om.delItem e.ctx ns (.str name))
    fun _ => formatExcCheckArg "NameError" (nameErrorMsg name) name
  del
  pure []

/-- `:2043`. -/
def _SPECIALIZE_UNPACK_SEQUENCE : M Unit := pure ()
/-- `:2057`. -/
def _UNPACK_SEQUENCE (e : Env) : M Unit := stk 1 e.oparg fun
  | [seq] => do
    let l ← (unpackIterable e.om e.ctx seq e.oparg none : RM _)
    pure l.reverse
  | _ => fault "arity"
/-- `:2064`. -/
def UNPACK_SEQUENCE (e : Env) : M Unit := do _SPECIALIZE_UNPACK_SEQUENCE; _UNPACK_SEQUENCE e
/-- `:2069`. -/
def _UNPACK_SEQUENCE_TWO_TUPLE : M Unit := stk 1 2 fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .tuple #[x, y] => pure [y, x]
    | .tuple _ => throw .deopt
    | _ => fault "not a tuple"
  | _ => fault "not a tuple"
/-- `:2066`. -/
def UNPACK_SEQUENCE_TWO_TUPLE : M Unit := do _GUARD_TOS_TUPLE; _UNPACK_SEQUENCE_TWO_TUPLE
/-- `:2102`. -/
def _UNPACK_SEQUENCE_TUPLE (e : Env) : M Unit := stk 1 e.oparg fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .tuple items =>
      if items.size != e.oparg then throw .deopt
      pure items.toList.reverse
    | _ => fault "not a tuple"
  | _ => fault "not a tuple"
/-- `:2099`. -/
def UNPACK_SEQUENCE_TUPLE (e : Env) : M Unit := do _GUARD_TOS_TUPLE; _UNPACK_SEQUENCE_TUPLE e
/-- `:2131`. -/
def _UNPACK_SEQUENCE_LIST (e : Env) : M Unit := stk 1 e.oparg fun
  | [.ref a] => do
    match ← (getObj a : RM Obj) with
    | .list items =>
      if items.size != e.oparg then throw .deopt
      pure items.toList.reverse
    | _ => fault "not a list"
  | _ => fault "not a list"
/-- `:2128`. -/
def UNPACK_SEQUENCE_LIST (e : Env) : M Unit := do _GUARD_TOS_LIST; _UNPACK_SEQUENCE_LIST e
/-- `:2148`. -/
def UNPACK_EX (e : Env) : M Unit :=
  stk 1 ((e.oparg &&& 255) + 1 + (e.oparg >>> 8)) fun
    | [seq] => do
      let l ← (unpackIterable e.om e.ctx seq (e.oparg &&& 255) (some (e.oparg >>> 8)) : RM _)
      pure l.reverse
    | _ => fault "arity"

/-- `:2161`. -/
def _SPECIALIZE_STORE_ATTR : M Unit := pure ()
/-- `:2174`. -/
def _STORE_ATTR (e : Env) : M Unit := stk 2 0 fun
  | [v, owner] => do
    let name ← getName e e.oparg
    e.om.setAttr e.ctx owner name v
    pure []
  | _ => fault "arity"
/-- `:2182`. -/
def STORE_ATTR (e : Env) : M Unit := do _SPECIALIZE_STORE_ATTR; _STORE_ATTR e
/-- `:2184`. -/
def DELETE_ATTR (e : Env) : M Unit := stk 1 0 fun
  | [owner] => do
    let name ← getName e e.oparg
    e.om.delAttr e.ctx owner name
    pure []
  | _ => fault "arity"
/-- `:2191`. -/
def STORE_GLOBAL (e : Env) : M Unit := stk 1 0 fun
  | [v] => do
    let name ← getName e e.oparg
    (dictSetStr (← getFrame).globals name v : RM Unit)
    pure []
  | _ => fault "arity"
/-- `:2198`. -/
def DELETE_GLOBAL (e : Env) : M Unit := stk 0 0 fun _ => do
  let name ← getName e e.oparg
  let found ← (dictPopStr (← getFrame).globals name : RM Bool)
  if !found then (formatExcCheckArg "NameError" (nameErrorMsg name) name : RM _)
  pure []
/-- `:2212`. -/
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
    | none => (formatExcCheckArg "NameError" (nameErrorMsg name) name : RM _)

/-- `:2222`. -/
def LOAD_FROM_DICT_OR_GLOBALS (e : Env) : M Unit := stk 1 1 fun
  | [m] => do
    let name ← getName e e.oparg
    match ← (optItem e m name : RM _) with
    | some v => pure [v]
    | none => pure [← loadGlobal e name]
  | _ => fault "arity"

/-- `_PyEval_LoadName`, `Python/ceval.c:3669-3707`. -/
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
      | none => (formatExcCheckArg "NameError" (nameErrorMsg name) name : RM _)

/-- `:2244`. -/
def LOAD_NAME (e : Env) : M Unit := stk 0 1 fun _ => do
  let name ← getName e e.oparg
  pure [← loadName e name]
/-- `:2256`. -/
def _SPECIALIZE_LOAD_GLOBAL : M Unit := pure ()
/-- `:2270`. -/
def _LOAD_GLOBAL (e : Env) : M Unit := stk 0 1 fun _ => do
  let name ← getName e (e.oparg >>> 1)
  pure [← loadGlobal e name]
/-- `:2277`. -/
def _PUSH_NULL_CONDITIONAL (e : Env) : M Unit :=
  stk 0 (e.oparg &&& 1) fun _ => pure (List.replicate (e.oparg &&& 1) .null)
/-- `:2283`. -/
def LOAD_GLOBAL (e : Env) : M Unit := do _SPECIALIZE_LOAD_GLOBAL; _LOAD_GLOBAL e; _PUSH_NULL_CONDITIONAL e

/-- `:2291`. -/
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

/-- `:2299`. -/
def _LOAD_GLOBAL_MODULE (e : Env) : M Unit := stk 0 1 fun _ => do
  pure [← dictSlot (← getFrame).globals (cacheNat e 0) (cacheNat e 1)]
/-- `:2319`. -/
def _LOAD_GLOBAL_BUILTINS (e : Env) : M Unit := stk 0 1 fun _ => do
  pure [← dictSlot (← getFrame).builtins (cacheNat e 1) (cacheNat e 2)]
/-- `:2342`. -/
def LOAD_GLOBAL_MODULE (e : Env) : M Unit := do _LOAD_GLOBAL_MODULE e; _PUSH_NULL_CONDITIONAL e
/-- `:2348`. -/
def LOAD_GLOBAL_BUILTIN (e : Env) : M Unit := do
  _GUARD_GLOBALS_VERSION e; _LOAD_GLOBAL_BUILTINS e; _PUSH_NULL_CONDITIONAL e

end PyLean.Bytecode.Uop
