/-!
# `Objects/genobject.c` (CPython 3.15.2): generators and coroutines

A standalone state machine, mirroring the C source branch by branch. Line numbers
are those of `Objects/genobject.c` unless another file is named.

The interpreter is abstracted away: the only way the model runs Python code is
through the fields of `Hooks`, above all the plain function `Hooks.resume`, which
stands for `_PyEval_EvalFrame(tstate, frame, exc)` (:281). A frame evaluator from
the bytecode machine instantiates it. A resume returns one of the three outcomes
in `ResumeOutcome`: yielded (with `YIELD_VALUE`'s oparg), returned, or raised.

* The heap is `World`: tables of generator objects and of `asend`/`athrow`
  awaitables, plus a free extension `ext` for whatever the instantiation needs
  (frames, for instance). Hooks get and return the whole world, so a hook may
  re-enter the model (`next(self)` inside a generator body, a sub-iterator's
  `close()` calling the delegator, and so on).
* C's "pending exception" is passed explicitly: `Ret.err (some e)` is `NULL` with
  `e` set, `Ret.err none` is `NULL` with no exception set (only `gen_iternext`
  produces that).
* `gen_close` and `_gen_throw` recurse along the `yield from` chain. The C code
  has no depth limit there, which is a finding (`GenCloseStackBounded`); the model
  takes fuel for it, and `Exc.fuel` is never a Python outcome.
* `gi_exc_state`, `tstate->exc_info`, tracebacks and `__context__` chaining
  (:271-278) are bookkeeping for the frame evaluator: they change which exception
  context a frame sees but none of the state machine, so they are not modelled.
-/

namespace PyLean.Bytecode.GenObj

abbrev Ref := Nat

/-- `PyFrameState`, `Include/internal/pycore_frame.h:47-54`. `FRAME_COMPLETED` is gone in
3.15, and `FRAME_SUSPENDED_YIELD_FROM_LOCKED` is only ever set on the free-threaded build
(`Objects/genobject.c:40-58`), which is out of scope, so it has no constructor here. -/
inductive FrameState where
  | created | suspended | suspendedYieldFrom | executing | cleared
  deriving DecidableEq, Repr, Inhabited

/-- The C enum values, `pycore_frame.h:47-54`. -/
def FrameState.toInt : FrameState → Int
  | .created => 0
  | .suspended => 1
  | .suspendedYieldFrom => 2
  | .executing => 4
  | .cleared => 5

/-- `FRAME_STATE_SUSPENDED(S)`, `pycore_frame.h:56`. -/
def FrameState.isSuspended : FrameState → Bool
  | .suspended | .suspendedYieldFrom => true
  | _ => false

/-- `FRAME_STATE_FINISHED(S)`, `pycore_frame.h:57`: `(S) == FRAME_CLEARED`. -/
def FrameState.finished (s : FrameState) : Bool := decide (s.toInt = 5)

/-- `gi_frame_state = FRAME_SUSPENDED + oparg` (`_YIELD_VALUE`,
`Python/bytecodes.c:1872`); the oparg is 0 or 1. -/
def FrameState.ofOparg (oparg : Bool) : FrameState :=
  if oparg then .suspendedYieldFrom else .suspended

/-- `PyGen_Type`, `PyCoro_Type`, `PyAsyncGen_Type`. None can be subclassed, so
`PyGen_CheckExact` and friends are exactly a test on this tag. -/
inductive GenKind where
  | gen | coro | asyncGen
  deriving DecidableEq, Repr, Inhabited

/-- Which of the three control-flow exception classes an exception derives from.
They are unrelated, so at most one applies; `plain` is everything else. This is
all `PyErr_ExceptionMatches` is asked about in this file. -/
inductive ExcKind where
  | stopIteration | stopAsyncIteration | generatorExit | plain
  deriving DecidableEq, Repr, Inhabited

/-- Python objects as this file sees them. `V` is every object the file treats as
opaque. -/
inductive Obj (V : Type) where
  /-- `Py_None`. -/
  | none
  /-- A generator, coroutine or async generator object. -/
  | gen (r : Ref)
  /-- `_PyAsyncGenWrappedValue`. -/
  | wrapped (o : Obj V)
  /-- A `str` (for `PyUnicode_Check`). -/
  | str (s : String)
  /-- A traceback object (for `PyTraceBack_Check`). -/
  | traceback
  /-- An exception class (for `PyExceptionClass_Check`). -/
  | excClass (kind : ExcKind) (cls : String)
  /-- An exception instance (for `PyExceptionInstance_Check`). -/
  | excInst (kind : ExcKind) (cls : String) (msg : String) (value : Obj V)
  /-- Any other object. -/
  | other (v : V)
  deriving Inhabited

/-- A raised exception. `value` is `StopIteration.value`. -/
structure Exc (V : Type) where
  kind : ExcKind
  cls : String
  msg : String
  value : Obj V := .none
  deriving Inhabited

namespace Exc
variable {V : Type}

def runtimeError (msg : String) : Exc V := ⟨.plain, "RuntimeError", msg, .none⟩
def valueError (msg : String) : Exc V := ⟨.plain, "ValueError", msg, .none⟩
def typeError (msg : String) : Exc V := ⟨.plain, "TypeError", msg, .none⟩
def stopAsyncIteration : Exc V := ⟨.stopAsyncIteration, "StopAsyncIteration", "", .none⟩
def generatorExit : Exc V := ⟨.generatorExit, "GeneratorExit", "", .none⟩
/-- `PyErr_SetNone(PyExc_StopIteration)`. -/
def stopIterationNone : Exc V := ⟨.stopIteration, "StopIteration", "", .none⟩
/-- Not a Python exception: the model's recursion fuel ran out. -/
def fuel : Exc V := ⟨.plain, "<model fuel exhausted>", "", .none⟩

/-- `PyErr_ExceptionMatches(PyExc_StopIteration)`. -/
def isStopIteration (e : Exc V) : Bool := e.kind == .stopIteration
/-- `PyErr_ExceptionMatches(PyExc_StopAsyncIteration)`. -/
def isStopAsyncIteration (e : Exc V) : Bool := e.kind == .stopAsyncIteration
/-- `PyErr_ExceptionMatches(PyExc_GeneratorExit)`. -/
def isGeneratorExit (e : Exc V) : Bool := e.kind == .generatorExit

def toObj (e : Exc V) : Obj V := .excInst e.kind e.cls e.msg e.value

end Exc

/-- A pending exception, tested with `PyErr_ExceptionMatches`: false when no
exception is set. -/
def matchesStopAsyncOrExit {V : Type} : Option (Exc V) → Bool
  | some e => e.isStopAsyncIteration || e.isGeneratorExit
  | none => false

/-- The `co_flags` bits this file reads, `Include/cpython/code.h`. -/
def CO_GENERATOR : Nat := 0x20
def CO_COROUTINE : Nat := 0x80
def CO_ITERABLE_COROUTINE : Nat := 0x100
def CO_ASYNC_GENERATOR : Nat := 0x200

/-- The parts of a code object that are read here. -/
structure Code where
  name : String := ""
  qualname : String := ""
  flags : Nat := 0
  nlocalsplus : Nat := 0
  stacksize : Nat := 0
  deriving Inhabited, Repr

def Code.hasFlag (c : Code) (flag : Nat) : Bool := c.flags &&& flag != 0

/-- The opcodes `is_resume` (:452-461) accepts, `Include/opcode_ids.h:133`, `:205-206`, `:235`. -/
def RESUME : Nat := 128
def RESUME_CHECK : Nat := 200
def RESUME_CHECK_JIT : Nat := 201
def INSTRUMENTED_RESUME : Nat := 244
/-- `RESUME_OPARG_DEPTH1_MASK`, `Include/internal/pycore_opcode_utils.h:93`. -/
def RESUME_OPARG_DEPTH1_MASK : Nat := 0x8
/-- `RESUME_AFTER_YIELD`, `pycore_opcode_utils.h:87`. -/
def RESUME_AFTER_YIELD : Nat := 1

/-- The code unit `frame->instr_ptr` points at: its opcode and oparg, all that `is_resume`
(:452-461) and the `RESUME_OPARG_DEPTH1_MASK` test (:504-505) read. -/
structure InstrPtr where
  opcode : Nat := 0
  oparg : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- `is_resume`, :452-461: the four `RESUME` opcodes, compared one by one. -/
def InstrPtr.isResume (i : InstrPtr) : Bool :=
  i.opcode == RESUME || i.opcode == RESUME_CHECK || i.opcode == RESUME_CHECK_JIT ||
    i.opcode == INSTRUMENTED_RESUME

/-- `oparg & RESUME_OPARG_DEPTH1_MASK` (:504-505). -/
def InstrPtr.depth1 (i : InstrPtr) : Bool := i.oparg &&& RESUME_OPARG_DEPTH1_MASK != 0

/-- A code unit that is not a `RESUME` (opcode 0 is `CACHE`). -/
def InstrPtr.other : InstrPtr := {}

/-- `RESUME` after a `yield` (`RESUME_AFTER_YIELD`), with the depth-1 bit `d`, as
`Python/flowgraph.c:969-977` emits it. -/
def InstrPtr.resumeAfterYield (d : Bool) : InstrPtr :=
  { opcode := RESUME, oparg := RESUME_AFTER_YIELD ||| (if d then RESUME_OPARG_DEPTH1_MASK else 0) }

/-- `PyGenObject`, with the `PyAsyncGenObject`/`PyCoroObject` tail. -/
structure GenObj (V : Type) where
  kind : GenKind := .gen
  /-- `gi_frame_state` -/
  state : FrameState := .cleared
  /-- `gi_iframe.instr_ptr` -/
  instr : InstrPtr := InstrPtr.other
  /-- `_PyFrame_StackPeek(frame, 2)`, meaningful when suspended in a `yield from`: the
  receiver, which on 3.15 lies under `index_or_null`. -/
  stackTop : Obj V := .none
  /-- `gi_iframe.f_executable` -/
  code : Code := {}
  /-- `gi_name` -/
  name : Obj V := .none
  /-- `gi_qualname` -/
  qualname : Obj V := .none
  /-- `ag_origin_or_finalizer` for an async generator. -/
  finalizer : Option (Obj V) := none
  /-- `cr_origin_or_finalizer` for a coroutine. -/
  origin : Option (List (String × Nat × String)) := none
  agClosed : Bool := false
  agHooksInited : Bool := false
  agRunningAsync : Bool := false
  deriving Inhabited

/-- `AwaitableState`, :1601-1605. -/
inductive AwaitableState where
  | init | iter | closed
  deriving DecidableEq, Repr, Inhabited

/-- `PyAsyncGenASend`, :1608-1617. -/
structure ASend (V : Type) where
  gen : Ref := 0
  /-- `ags_sendval`: `none` is NULL, the `__anext__()` mode. -/
  sendval : Option (Obj V) := none
  state : AwaitableState := .init
  deriving Inhabited

/-- `PyAsyncGenAThrow`, :1623-1634. -/
structure AThrow (V : Type) where
  gen : Ref := 0
  /-- `agt_typ`, `agt_val` and `agt_tb`: `none` is `agt_typ == NULL`, the `aclose()` mode.
  3.15 unpacks the arguments when the awaitable is made, so a bad count cannot get here. -/
  args : Option (Obj V × Option (Obj V) × Option (Obj V)) := none
  state : AwaitableState := .init
  deriving Inhabited

/-- The heap. `X` is free for the instantiation (frames and so on). -/
structure World (V X : Type) where
  gens : Ref → GenObj V
  asends : Ref → ASend V
  athrows : Ref → AThrow V
  /-- `_PyEval_NoToolsForUnwind(tstate, frame)`. -/
  noUnwindTools : Bool := true
  /-- `tstate->coroutine_origin_tracking_depth` -/
  originDepth : Nat := 0
  /-- The Python call stack at `_PyCoro_ComputeOrigin` time, innermost first. -/
  callStack : List (String × Nat × String) := []
  /-- `tstate->async_gen_firstiter` -/
  firstiter : Option (Obj V) := none
  /-- `tstate->async_gen_finalizer` -/
  finalizerHook : Option (Obj V) := none
  ext : X

namespace World
variable {V X : Type}

def get (w : World V X) (r : Ref) : GenObj V := w.gens r

def set (w : World V X) (r : Ref) (g : GenObj V) : World V X :=
  { w with gens := fun q => if q = r then g else w.gens q }

def setState (w : World V X) (r : Ref) (s : FrameState) : World V X :=
  w.set r { w.get r with state := s }

def setRunning (w : World V X) (r : Ref) (b : Bool) : World V X :=
  w.set r { w.get r with agRunningAsync := b }

def setClosed (w : World V X) (r : Ref) : World V X :=
  w.set r { w.get r with agClosed := true }

def setAsendState (w : World V X) (a : Ref) (s : AwaitableState) : World V X :=
  { w with asends := fun q => if q = a then { w.asends a with state := s } else w.asends q }

def setAthrowState (w : World V X) (a : Ref) (s : AwaitableState) : World V X :=
  { w with athrows := fun q => if q = a then { w.athrows a with state := s } else w.athrows q }

@[simp] theorem get_set_same (w : World V X) (r : Ref) (g : GenObj V) :
    (w.set r g).get r = g := by simp [get, set]

@[simp] theorem get_set_ne (w : World V X) {r q : Ref} (g : GenObj V) (h : q ≠ r) :
    (w.set r g).get q = w.get q := by simp [get, set, h]

theorem get_set (w : World V X) (r q : Ref) (g : GenObj V) :
    (w.set r g).get q = if q = r then g else w.get q := by simp [get, set]

@[simp] theorem get_setAsendState (w : World V X) (a r : Ref) (s : AwaitableState) :
    (w.setAsendState a s).get r = w.get r := rfl

@[simp] theorem get_setAthrowState (w : World V X) (a r : Ref) (s : AwaitableState) :
    (w.setAthrowState a s).get r = w.get r := rfl

end World

/-- What `_PyEval_EvalFrame` left behind (:281). For `yielded`, `oparg` is
`YIELD_VALUE`'s oparg (`false` is 0: `FRAME_SUSPENDED`, `true` is 1:
`FRAME_SUSPENDED_YIELD_FROM`), `next` is the code unit `frame->instr_ptr` then points at
(the `RESUME` that follows the yield), and `top` is what `_PyFrame_StackPeek` then sees. -/
inductive ResumeOutcome (V : Type) where
  | yielded (oparg : Bool) (value : Obj V) (next : InstrPtr) (top : Obj V)
  | returned (value : Obj V)
  | raised (e : Exc V)
  deriving Inhabited

/-- `PySendResult` with `*presult`. -/
inductive SendResult (V : Type) where
  | next (v : Obj V)
  | ret (v : Obj V)
  | err (e : Option (Exc V))
  deriving Inhabited

/-- `PyObject *` with the pending exception. -/
inductive Ret (V : Type) where
  | ok (v : Obj V)
  | err (e : Option (Exc V))
  deriving Inhabited

/-- An `int` status: 0, or -1 with the pending exception. -/
inductive CStatus (V : Type) where
  | ok
  | fail (e : Option (Exc V))
  deriving Inhabited

/-- The interpreter, as far as `genobject.c` calls into it. All of these are plain
functions over the world, so an instantiation can run arbitrary Python. -/
structure Hooks (V X : Type) where
  /-- `_PyEval_EvalFrame(tstate, frame, exc)` (:281): runs the frame of `r`, whose
  `gi_frame_state` is `FRAME_EXECUTING`, with the sent value on the stack and the
  thrown exception if any. -/
  resume : World V X → Ref → Obj V → Option (Exc V) → World V X × ResumeOutcome V
  /-- `PyObject_GetOptionalAttr(yf, &_Py_ID(close), &meth)` (:436). -/
  getClose : World V X → Obj V → World V X × Except (Exc V) (Option (Obj V))
  /-- `PyObject_GetOptionalAttr(yf, &_Py_ID(throw), &meth)` (:692). -/
  getThrow : World V X → Obj V → World V X × Except (Exc V) (Option (Obj V))
  /-- `_PyObject_CallNoArgs(meth)` (:441). -/
  callNoArgs : World V X → Obj V → World V X × Ret V
  /-- `PyObject_CallOneArg` (:124, @3.14.7:1521). -/
  callOneArg : World V X → Obj V → Obj V → World V X × Ret V
  /-- `PyObject_CallFunctionObjArgs(meth, typ, val, tb, NULL)` (:705). -/
  callThrow : World V X → Obj V → Obj V → Option (Obj V) → Option (Obj V) → World V X × Ret V
  /-- `PyErr_FormatUnraisable` (:126, @3.14.7:132, @3.14.7:348). -/
  unraisable : World V X → String → Exc V → World V X
  /-- `PyErr_WarnEx(PyExc_DeprecationWarning, msg, 1)` (:741, @3.14.7:1570): an exception
  when warnings are errors. -/
  warn : World V X → String → World V X × Option (Exc V)
  /-- `_PyErr_WarnUnawaitedCoroutine` (:147). -/
  warnUnawaitedCoro : World V X → Ref → World V X
  /-- `_PyErr_WarnUnawaitedAgenMethod` (:2098, @3.14.7:2343). -/
  warnUnawaitedAgen : World V X → Ref → String → World V X
  /-- `PyErr_NormalizeException(&typ, &val, &tb)` (:488) for a class `typ`. -/
  normalize : Obj V → Option (Obj V) → Exc V
  /-- `Py_TYPE(o)->tp_name`: for a class statement the bare `__name__`. -/
  typeName : Obj V → String
  /-- `%T` of `PyErr_Format`: `_PyType_GetFullyQualifiedName(Py_TYPE(o), '.')`, the
  `__qualname__` prefixed by `__module__` unless that is `builtins` or `__main__`
  (`Objects/typeobject.c`). -/
  typeFqName : Obj V → String
  /-- `PySys_Audit("object.__getattr__", "Os", gen, name)` (:956, @3.14.7:799). -/
  audit : World V X → String → Option (Exc V)
  /-- `_PyFrame_GetFrameObject` (:964). -/
  frameObject : World V X → Ref → Obj V
  /-- `PyIter_Check`. -/
  isIter : Obj V → Bool
  /-- `ot->tp_as_async->am_await` (:1257-1261); `none` when there is no getter. -/
  amAwait : World V X → Obj V → Option (World V X × Ret V)

variable {V X : Type}

/-! ## `gen_send_ex2` and its callers -/

/-- `arg && arg != Py_None` (:335). -/
def isNonNull : Option (Obj V) → Bool
  | none | some .none => false
  | some _ => true

/-- :336-344. -/
def cantSendMsg : GenKind → String
  | .gen => "can't send non-None value to a just-started generator"
  | .coro => "can't send non-None value to a just-started coroutine"
  | .asyncGen => "can't send non-None value to a just-started async generator"

/-- `gen_raise_already_executing_error`, :241-252. -/
def alreadyExecutingMsg : GenKind → String
  | .gen => "generator already executing"
  | .coro => "coroutine already executing"
  | .asyncGen => "async generator already executing"

/-- `result == Py_None` -/
def Obj.isNone : Obj V → Bool
  | .none => true
  | _ => false

/-- `clear_gen_frame`, `Python/ceval.c:2001-2016`, what a frame does to its
generator as it returns or raises. -/
def clearGenFrame (w : World V X) (r : Ref) : World V X :=
  w.setState r .cleared

/-- What `_YIELD_VALUE` does to its generator, `Python/bytecodes.c:1856-1872`. -/
def suspendFrame (w : World V X) (r : Ref) (oparg : Bool) (next : InstrPtr) (top : Obj V) : World V X :=
  w.set r { w.get r with
    state := FrameState.ofOparg oparg
    instr := next
    stackTop := top }

/-- The end of `gen_send_ex2`, :289-324, with the state write `_YIELD_VALUE` or
`clear_gen_frame` did before control came back. `generator_return_kind` (:293) is which
of the two ran, and is here the shape of the outcome. -/
def finishResume (w : World V X) (r : Ref) (kind : GenKind) (arg : Option (Obj V)) :
    ResumeOutcome V → World V X × SendResult V
  | .yielded oparg v next top => (suspendFrame w r oparg next top, .next v)
  | .returned v =>
    if v.isNone = true ∧ kind ≠ .asyncGen ∧ arg.isNone = true then
      (clearGenFrame w r, .err none)
    else
      (clearGenFrame w r, .ret v)
  | .raised e => (clearGenFrame w r, .err (some e))

/-- `gen_send_ex2`, :259-325. On 3.15 this has no state checks: the caller has already marked
the generator `FRAME_EXECUTING`, and `exc` is the exception pending when `exc` is set. -/
def genSendEx2 (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (exc : Option (Exc V)) : World V X × SendResult V :=
  let res := h.resume w r (arg.getD .none) exc
  finishResume res.1 r (w.get r).kind arg res.2

/-- `gen_send_ex`, :329-375: the state checks in source order, then `gen_send_ex2` with the
generator marked `FRAME_EXECUTING`. A coroutine that finished always raises here: the
`closing` escape of 3.14 is gone, because `gen_close` no longer comes through this. -/
def genSendEx (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)) :
    World V X × SendResult V :=
  let g := w.get r
  if g.state = .created ∧ isNonNull arg = true then
    (w, .err (some (Exc.typeError (cantSendMsg g.kind))))
  else if g.state = .executing then
    (w, .err (some (Exc.valueError (alreadyExecutingMsg g.kind))))
  else if g.state.finished = true then
    if g.kind = .coro then
      (w, .err (some (Exc.runtimeError "cannot reuse already awaited coroutine")))
    else if arg.isSome = true then
      (w, .ret .none)
    else
      (w, .err none)
  else
    genSendEx2 h (w.setState r .executing) r arg none

/-- `PyGen_am_send`, :377-382. -/
def pyGenAmSend (h : Hooks V X) (w : World V X) (r : Ref) (arg : Obj V) :
    World V X × SendResult V :=
  genSendEx h w r (some arg)

/-- `_PyGen_SetStopIterationValue`, :782-799: a tuple value stays a tuple. -/
def setStopIterationValue (value : Obj V) : Exc V :=
  ⟨.stopIteration, "StopIteration", "", value⟩

/-- `_PyGen_FetchStopIterationValue`, :810-826. `.ok v` is the 0 return with
`*pvalue = v`; `.err` keeps the pending exception, the -1 return. -/
def fetchStopIterationValue (pending : Option (Exc V)) : Ret V :=
  match pending with
  | some e => if e.isStopIteration then .ok e.value else .err (some e)
  | none => .ok .none

/-- `gen_set_stop_iteration`, :384-399, on a `PYGEN_RETURN`. -/
def sendResultToRet (kind : GenKind) : SendResult V → Ret V
  | .ret v =>
    if kind = .asyncGen then .err (some Exc.stopAsyncIteration)
    else if v.isNone = true then .err (some Exc.stopIterationNone)
    else .err (some (setStopIterationValue v))
  | .next v => .ok v
  | .err e => .err e

/-- `gen_send`, :405-414. `arg` is `none` for the `async_gen_asend_send` call with
`ags_sendval == NULL`. -/
def genSend (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)) :
    World V X × Ret V :=
  let s := genSendEx h w r arg
  (s.1, sendResultToRet (w.get r).kind s.2)

/-- `gen_throw_current_exception`, :603-612: throw the pending exception into a frame that
is already `FRAME_EXECUTING`. -/
def genThrowCurrent (h : Hooks V X) (w : World V X) (r : Ref) (e : Option (Exc V)) :
    World V X × Ret V :=
  let s := genSendEx2 h w r (some .none) e
  (s.1, sendResultToRet (w.get r).kind s.2)

/-- `gen_iternext`, :760-774, on the result of `gen_send_ex`. -/
def iterResultToRet : SendResult V → Ret V
  | .ret v =>
    if v.isNone = true then .err none
    else .err (some (setStopIterationValue v))
  | .next v => .ok v
  | .err e => .err e

/-- `gen_iternext`, :760-774. -/
def genIternext (h : Hooks V X) (w : World V X) (r : Ref) : World V X × Ret V :=
  let s := genSendEx h w r none
  (s.1, iterResultToRet s.2)

/-- `NULL` with no exception set means `StopIteration` to the caller of
`tp_iternext` (`wrap_next` in `Objects/typeobject.c`, `builtin_next` in
`Python/bltinmodule.c`). -/
def nullToStop : Ret V → Ret V
  | .err none => .err (some Exc.stopIterationNone)
  | res => res

/-- `next(gen)` / `gen.__next__()`. -/
def nextCall (h : Hooks V X) (w : World V X) (r : Ref) : World V X × Ret V :=
  let s := genIternext h w r
  (s.1, nullToStop s.2)

/-! ## Delegation: `gen_close`, `_gen_throw` -/

/-- `is_resume(frame->instr_ptr)` (:500) followed by the mask test at :505. -/
def InstrPtr.isResumeDepth1 (i : InstrPtr) : Bool := i.isResume && i.depth1

/-- `frame_state == FRAME_SUSPENDED_YIELD_FROM` and `_PyFrame_StackPeek(frame, 2)`, which on
3.15 stand where `_PyGen_yf` stood: :776-781 in `gen_getyieldfrom`. -/
def genYf (g : GenObj V) : Option (Obj V) :=
  if g.state = .suspendedYieldFrom then some g.stackTop else none

/-- `PyGen_CheckExact(yf) || PyCoro_CheckExact(yf)` (:429, :672). -/
def genOrCoro? (w : World V X) : Obj V → Option Ref
  | .gen r => if (w.get r).kind = .asyncGen then none else some r
  | _ => none

/-- `PyObject_GetOptionalAttr` failing is reported and ignored, :436-439. -/
def closeMeth (h : Hooks V X) (w : World V X) :
    Except (Exc V) (Option (Obj V)) → World V X × Option (Obj V)
  | .error e => (h.unraisable w "Exception ignored while closing generator" e, none)
  | .ok mo => (w, mo)

/-- :435-445, the non-generator path of `gen_close_iter`. -/
def genCloseIterForeign (h : Hooks V X) (w : World V X) (yf : Obj V) :
    World V X × CStatus V :=
  let a := h.getClose w yf
  let m := closeMeth h a.1 a.2
  match m.2 with
  | some mt =>
    let c := h.callNoArgs m.1 mt
    match c.2 with
    | .err e => (c.1, .fail e)
    | .ok _ => (c.1, .ok)
  | none => (m.1, .ok)

/-- `gen_close_iter`, :424-449. `close` is `gen_close` at the next recursion depth. -/
def genCloseIter (h : Hooks V X) (close : World V X → Ref → World V X × Ret V)
    (w : World V X) (yf : Obj V) : World V X × CStatus V :=
  match genOrCoro? w yf with
  | some r =>
    let c := close w r
    match c.2 with
    | .err e => (c.1, .fail e)
    | .ok _ => (c.1, .ok)
  | none => genCloseIterForeign h w yf

/-- :524-529. -/
def ignoredExitMsg : GenKind → String
  | .gen => "generator ignored GeneratorExit"
  | .coro => "coroutine ignored GeneratorExit"
  | .asyncGen => "async generator ignored GeneratorExit"

/-- `gen_clear_frame`, :166-174: the state was written by the caller, and the frame's
contents go. What this model holds of them is the stack. -/
def genClearFrame (w : World V X) (r : Ref) : World V X :=
  w.set r { w.get r with stackTop := .none }

/-- :517-540, the end of `gen_close`: throw into the frame and interpret the result. A
value the frame returned is the result, and of the exceptions only `GeneratorExit` is
swallowed. There is no `_PyGen_FetchStopIterationValue` here any more. -/
def genCloseFinish (h : Hooks V X) (w : World V X) (r : Ref) (pending : Option (Exc V)) :
    World V X × Ret V :=
  let s := genSendEx2 h w r (some .none) pending
  match s.2 with
  | .ret v => (s.1, .ok v)
  | .next _ => (s.1, .err (some (Exc.runtimeError (ignoredExitMsg (w.get r).kind))))
  | .err e =>
    match e with
    | some x => if x.isGeneratorExit then (s.1, .ok .none) else (s.1, .err e)
    | none => (s.1, .err none)

/-- :493-497, on a generator already `FRAME_EXECUTING`; `state` is what it was before. -/
def closeDelegate (h : Hooks V X) (close : World V X → Ref → World V X × Ret V)
    (w : World V X) (r : Ref) (state : FrameState) : World V X × CStatus V :=
  if state = .suspendedYieldFrom then genCloseIter h close w (w.get r).stackTop
  else (w, .ok)

/-- `if (err == 0) PyErr_SetNone(PyExc_GeneratorExit)`, :513-515. -/
def closePending : CStatus V → Option (Exc V)
  | .ok => some Exc.generatorExit
  | .fail e => e

/-- :491-540, with `close` the recursive `gen_close`. The test at :499-505 reads only the
instruction. `state` is the value of `frame_state` from before :489. -/
def genCloseBody (h : Hooks V X) (close : World V X → Ref → World V X × Ret V)
    (w : World V X) (r : Ref) (state : FrameState) : World V X × Ret V :=
  let p := closeDelegate h close w r state
  if (p.1.get r).instr.isResumeDepth1 = true ∧ p.1.noUnwindTools = true then
    (genClearFrame (p.1.setState r .cleared) r, .ok .none)
  else
    genCloseFinish h p.1 r (closePending p.2)

/-- `gen_close`, :463-541, with fuel for the C recursion through `gen_close_iter`. The checks
come first and the generator stays `FRAME_EXECUTING` from :489 on, so a running frame is
refused and every reentrant call during the close sees it as running. -/
def genCloseF (h : Hooks V X) : Nat → World V X → Ref → World V X × Ret V
  | 0, w, _ => (w, .err (some Exc.fuel))
  | n + 1, w, r =>
    let state := (w.get r).state
    if state = .created then
      (genClearFrame (w.setState r .cleared) r, .ok .none)
    else if state.finished = true then
      (w, .ok .none)
    else if state = .executing then
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))
    else
      genCloseBody h (genCloseF h n) (w.setState r .executing) r state

/-- `PyErr_GivenExceptionMatches(typ, PyExc_GeneratorExit)` (:656). -/
def givenMatchesGeneratorExit : Obj V → Bool
  | .excClass k _ | .excInst k _ _ _ => k == .generatorExit
  | _ => false

/-- `tb != NULL && !PyTraceBack_Check(tb)` after `None` became NULL, :550-558. -/
def badTraceback : Option (Obj V) → Bool
  | none | some .none | some .traceback => false
  | some _ => true

/-- `gen_set_exception`, :546-601: `.ok` with the exception it restored, or `.error` with
the `TypeError` it set. -/
def genSetException (h : Hooks V X) (typ : Obj V) (val tb : Option (Obj V)) :
    Except (Exc V) (Exc V) :=
  if badTraceback tb then
    .error (Exc.typeError "throw() third argument must be a traceback object")
  else
    match typ with
    | .excClass _ _ => .ok (h.normalize typ val)
    | .excInst k c m v =>
      if isNonNull val then
        .error (Exc.typeError "instance exception may not have a separate value")
      else .ok ⟨k, c, m, v⟩
    | _ =>
      .error (Exc.typeError
        ("exceptions must be classes or instances deriving from BaseException, not "
          ++ h.typeName typ))

/-- `throw_here:`, :719-725, on a generator `FRAME_EXECUTING`: bad arguments write the old
state back. -/
def throwHere (h : Hooks V X) (w : World V X) (r : Ref) (state : FrameState) (typ : Obj V)
    (val tb : Option (Obj V)) : World V X × Ret V :=
  match genSetException h typ val tb with
  | .ok e => genThrowCurrent h w r (some e)
  | .error e => (w.setState r state, .err (some e))

/-- :711-716: a value from the sub-iterator writes the old state back; if delegation
failed, the error goes into the delegating frame. -/
def afterDelegate (h : Hooks V X) (w : World V X) (r : Ref) (state : FrameState) :
    Ret V → World V X × Ret V
  | .ok v => (w.setState r state, .ok v)
  | .err e => genThrowCurrent h w r e

/-- `_gen_throw`, :624-726, with fuel for the C recursion along the delegation chain. The
generator is `FRAME_EXECUTING` from :649 on, around everything it does with the
sub-iterator, the lookup of `throw` included. -/
def genThrowF (h : Hooks V X) : Nat → World V X → Ref → Bool → Obj V →
    Option (Obj V) → Option (Obj V) → World V X × Ret V
  | 0, w, _, _, _, _, _ => (w, .err (some Exc.fuel))
  | n + 1, w, r, closeOnGenExit, typ, val, tb =>
    let state := (w.get r).state
    if state = .executing then
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))
    else if state.finished = true then
      if (w.get r).kind = .coro then
        (w, .err (some (Exc.runtimeError "cannot reuse already awaited coroutine")))
      else
        match genSetException h typ val tb with
        | .ok e | .error e => (w, .err (some e))
    else
      let w1 := w.setState r .executing
      if state = .suspendedYieldFrom then
        let yf := (w1.get r).stackTop
        if givenMatchesGeneratorExit typ = true ∧ closeOnGenExit = true then
          let p := genCloseIter h (genCloseF h n) w1 yf
          match p.2 with
          | .fail e => genThrowCurrent h p.1 r e
          | .ok => throwHere h p.1 r state typ val tb
        else
          match genOrCoro? w1 yf with
          | some sub =>
            let p := genThrowF h n w1 sub closeOnGenExit typ val tb
            afterDelegate h p.1 r state p.2
          | none =>
            let q := h.getThrow w1 yf
            match q.2 with
            | .error e => (q.1.setState r state, .err (some e))
            | .ok none => throwHere h q.1 r state typ val tb
            | .ok (some meth) =>
              let p := h.callThrow q.1 meth typ val tb
              afterDelegate h p.1 r state p.2
      else
        throwHere h w1 r state typ val tb

/-- `_PyArg_CheckPositional`, `Python/getargs.c`. -/
def checkPositional (name : String) (nargs lo hi : Nat) : Option (Exc V) :=
  if nargs < lo then
    some (Exc.typeError s!"{name} expected at least {lo} argument{if lo == 1 then "" else "s"}, got {nargs}")
  else if nargs > hi then
    some (Exc.typeError s!"{name} expected at most {hi} argument{if hi == 1 then "" else "s"}, got {nargs}")
  else none

/-- The `(typ, val, tb)` slots of a checked argument list, :748-755. -/
def unpackThrowArgs : List (Obj V) → Obj V × Option (Obj V) × Option (Obj V)
  | [typ] => (typ, none, none)
  | [typ, val] => (typ, some val, none)
  | typ :: val :: tb :: _ => (typ, some val, some tb)
  | [] => (.none, none, none)

/-- `gen_throw`, :729-757. -/
def genThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (args : List (Obj V)) :
    World V X × Ret V :=
  match checkPositional "throw" args.length 1 3 with
  | some e => (w, .err (some e))
  | none =>
    let warned : World V X × Option (Exc V) :=
      if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
      else (w, none)
    match warned.2 with
    | some e => (warned.1, .err (some e))
    | none =>
      let tv := unpackThrowArgs args
      genThrowF h fuel warned.1 r true tv.1 tv.2.1 tv.2.2

/-! ## `gen_finalize` -/

/-- `gen_finalize`, :107-164, called `_PyGen_Finalize` before 3.15. -/
def genFinalize (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) : World V X :=
  let g := w.get r
  if g.state.finished = true then w
  else
    let viaFinalizer : Option (Obj V) :=
      if g.kind = .asyncGen ∧ g.agClosed = false then g.finalizer else none
    match viaFinalizer with
    | some finalizer =>
      match h.callOneArg w finalizer (.gen r) with
      | (w1, .err (some e)) =>
        h.unraisable w1 "Exception ignored while finalizing generator" e
      | (w1, _) => w1
    | none =>
      if g.code.hasFlag CO_COROUTINE = true ∧ g.state = .created then
        h.warnUnawaitedCoro w r
      else
        match genCloseF h fuel w r with
        | (w1, .err (some e)) =>
          h.unraisable w1 "Exception ignored while closing generator" e
        | (w1, _) => w1

/-! ## Getters and setters -/

/-- `gen_get_name`, :836-842. -/
def genGetName (g : GenObj V) : Obj V := g.name
/-- `gen_get_qualname`, :863-869. -/
def genGetQualname (g : GenObj V) : Obj V := g.qualname

/-- `gen_set_name`, :844-861. `value` is `none` for `del gen.__name__`. `Obj.str` stands for
every object `PyUnicode_Check` accepts, `str` subclasses included, and the setter stores the
value it was given (`Py_NewRef(value)`, :857); a value model has no object identity beyond
that. -/
def genSetName (w : World V X) (r : Ref) (value : Option (Obj V)) : World V X × CStatus V :=
  match value with
  | some v@(.str _) => (w.set r { w.get r with name := v }, .ok)
  | _ => (w, .fail (some (Exc.typeError "__name__ must be set to a string object")))

/-- `gen_set_qualname`, :871-887. -/
def genSetQualname (w : World V X) (r : Ref) (value : Option (Obj V)) : World V X × CStatus V :=
  match value with
  | some v@(.str _) => (w.set r { w.get r with qualname := v }, .ok)
  | _ => (w, .fail (some (Exc.typeError "__qualname__ must be set to a string object")))

/-- `gen_getyieldfrom`, :890-914, which on 3.15 is also `cr_await` and `ag_await`. -/
def genGetYieldFrom (g : GenObj V) : Obj V := (genYf g).getD .none

/-- `gen_getrunning`, :917-923, also `cr_running` on 3.15. -/
def genGetRunning (g : GenObj V) : Bool := decide (g.state = .executing)

/-- `gen_getsuspended`, :925-931, also `cr_suspended` and `ag_suspended` on 3.15. -/
def genGetSuspended (g : GenObj V) : Bool := g.state.isSuspended

/-- `_gen_getframe`, :953-965, for `gi_frame`, `cr_frame`, `ag_frame`. -/
def genGetFrame (h : Hooks V X) (w : World V X) (r : Ref) (name : String) : Ret V :=
  match h.audit w name with
  | some e => .err (some e)
  | none =>
    if (w.get r).state.finished = true then .ok .none
    else .ok (h.frameObject w r)

/-- `_gen_getcode`, :974-981, for `gi_code`, `cr_code`, `ag_code`: `_PyGen_GetCode`
(:68-71) and `PyGen_GetCode` (:73-79) are this read of `f_executable`. -/
def genGetCode (h : Hooks V X) (w : World V X) (r : Ref) (name : String) :
    Except (Exc V) Code :=
  match h.audit w name with
  | some e => .error e
  | none => .ok (w.get r).code

/-- `gen_sizeof`, :1010-1019. `base` is
`offsetof(PyGenObject, gi_iframe) + offsetof(_PyInterpreterFrame, localsplus)` and
`_PyFrame_NumSlotsForCodeObject` is `co_nlocalsplus + co_stacksize`
(`Include/internal/pycore_interpframe.h`). -/
def genSizeof (base : Nat) (g : GenObj V) : Nat :=
  base + (g.code.nlocalsplus + g.code.stacksize) * 8

/-- `gen_repr`, :828-834, `coro_repr`, :1286-1292, `async_gen_repr`, :1659-1665,
without the trailing `%p`. -/
def reprPrefix : GenKind → String
  | .gen => "<generator object "
  | .coro => "<coroutine object "
  | .asyncGen => "<async_generator object "

def genRepr (g : GenObj V) (addr : String) (q : String) : String :=
  reprPrefix g.kind ++ q ++ " at " ++ addr ++ ">"

/-! ## Construction -/

/-- `make_gen`, :1095-1115: the frame state is `FRAME_CLEARED` until the frame is
copied in (`RETURN_GENERATOR` then sets `FRAME_CREATED`). -/
def makeGen (kind : GenKind) (code : Code) (funcName funcQualname : Obj V) : GenObj V :=
  { kind := kind, state := .cleared, code := code, name := funcName, qualname := funcQualname }

/-- The first loop of `_PyCoro_ComputeOrigin`, :1544-1549: count up to `origin_depth`
frames. -/
def crOriginCount (originDepth : Nat) :
    List (String × Nat × String) → Nat → Nat
  | [], frameCount => frameCount
  | _ :: rest, frameCount =>
    if frameCount < originDepth then crOriginCount originDepth rest (frameCount + 1)
    else frameCount

/-- The second loop, :1555-1567: collect `frame_count` frames. The loop bound is the
counter; the frame list cannot run out first because the first loop counted it. -/
def crOriginCollect (frameCount : Nat) :
    List (String × Nat × String) → Nat → List (String × Nat × String)
  | [], _ => []
  | f :: rest, i =>
    if i < frameCount then f :: crOriginCollect frameCount rest (i + 1) else []

/-- `_PyCoro_ComputeOrigin`, :1540-1570, frames innermost first. -/
def computeCrOrigin (originDepth : Nat) (frames : List (String × Nat × String)) :
    List (String × Nat × String) :=
  crOriginCollect (crOriginCount originDepth frames 0) frames 0

/-- `_Py_MakeCoro`, :1117-1162. Which of the three types the code flags select, and
the tail initialised for each. The masked flags are compared with `==`: exactly `CO_GENERATOR`
is a generator, exactly `CO_ASYNC_GENERATOR` an async generator, and anything else a coroutine,
since `assert(coro_flags)` and `assert (coro_flags == CO_COROUTINE)` (:1121, :1139) are compiled
out of a release build (no flags, or two of them, set with `code.replace(co_flags=...)`, make a
coroutine on 3.15.2). The result is never `none`. -/
def pyMakeCoro (w : World V X) (code : Code) (funcName funcQualname : Obj V) : Option (GenObj V) :=
  let coroFlags := code.flags &&& (CO_GENERATOR ||| CO_COROUTINE ||| CO_ASYNC_GENERATOR)
  if coroFlags = CO_GENERATOR then
    some (makeGen .gen code funcName funcQualname)
  else if coroFlags = CO_ASYNC_GENERATOR then
    some { makeGen .asyncGen code funcName funcQualname with
           finalizer := none, agClosed := false, agHooksInited := false, agRunningAsync := false }
  else
    let g := makeGen .coro code funcName funcQualname
    if w.originDepth = 0 then
      some { g with origin := none }
    else
      some { g with origin := some (computeCrOrigin w.originDepth w.callStack) }

/-- `gen_new_with_qualname`, :1164-1199: the frame is copied, the state is
`FRAME_CREATED`, and a NULL name or qualname falls back to the code object's. -/
def genNewWithQualname (kind : GenKind) (code : Code) (name qualname : Option (Obj V)) :
    GenObj V :=
  { kind := kind
    state := .created
    instr := { opcode := RESUME, oparg := 0 }
    code := code
    name := name.getD (.str code.name)
    qualname := qualname.getD (.str code.qualname) }

/-- `PyGen_NewWithQualName`, :1201-1205. -/
def pyGenNewWithQualName (code : Code) (name qualname : Option (Obj V)) : GenObj V :=
  genNewWithQualname .gen code name qualname

/-- `PyGen_New`, :1207-1211. -/
def pyGenNew (code : Code) : GenObj V := genNewWithQualname .gen code none none

/-- `PyCoro_New`, :1572-1595. -/
def pyCoroNew (w : World V X) (code : Code) (name qualname : Option (Obj V)) : GenObj V :=
  let g := genNewWithQualname .coro code name qualname
  if w.originDepth = 0 then { g with origin := none }
  else { g with origin := some (computeCrOrigin w.originDepth w.callStack) }

/-- `PyAsyncGen_New`, :1894-1909. -/
def pyAsyncGenNew (code : Code) (name qualname : Option (Obj V)) : GenObj V :=
  { genNewWithQualname .asyncGen code name qualname with
    finalizer := none, agClosed := false, agHooksInited := false, agRunningAsync := false }

/-! ## Coroutines -/

/-- `gen_is_coroutine`, :1225-1235. -/
def genIsCoroutine (w : World V X) : Obj V → Bool
  | .gen r =>
    (w.get r).kind = .gen ∧ (w.get r).code.hasFlag CO_ITERABLE_COROUTINE = true
  | _ => false

/-- `PyCoro_CheckExact(o)`. -/
def isCoro (w : World V X) : Obj V → Bool
  | .gen r => (w.get r).kind = .coro
  | _ => false

/-- `%.Ns` of `PyUnicode_FromFormat` on a C string (`unicode_fromformat_write_utf8`,
`Objects/unicodeobject.c`): the longest prefix of whole characters whose UTF-8 encoding fits
in `n` bytes. The same definition as `PyLean.TypeObj.cutUtf8`. -/
def cutUtf8 : Nat → List Char → List Char
  | _, [] => []
  | n, c :: cs => if c.utf8Size ≤ n then c :: cutUtf8 (n - c.utf8Size) cs else []

def trunc100 (s : String) : String := String.ofList (cutUtf8 100 s.toList)

/-- `_PyCoro_GetAwaitableIter`, :1245-1284. The two `__await__` messages use `%T` (the
fully qualified name), the last one `'%.100s'` of `tp_name`. -/
def pyCoroGetAwaitableIter (h : Hooks V X) (w : World V X) (o : Obj V) : World V X × Ret V :=
  if isCoro w o = true ∨ genIsCoroutine w o = true then
    (w, .ok o)
  else
    match h.amAwait w o with
    | some (w1, .ok res) =>
      if isCoro w1 res = true ∨ genIsCoroutine w1 res = true then
        (w1, .err (some (Exc.typeError
          (h.typeFqName o ++ ".__await__() must return an iterator, not coroutine"))))
      else if h.isIter res = false then
        (w1, .err (some (Exc.typeError
          (h.typeFqName o ++ ".__await__() must return an iterator, not " ++ h.typeFqName res))))
      else
        (w1, .ok res)
    | some (w1, .err e) => (w1, .err e)
    | none =>
      (w, .err (some (Exc.typeError ("'" ++ trunc100 (h.typeName o) ++ "' object can't be awaited"))))

/-- `coro_wrapper_iternext`, :1454-1459. `coro_await` (:1142-1152) just pairs the
coroutine with a wrapper, so a wrapper is its coroutine's `Ref`. -/
def coroWrapperIternext (h : Hooks V X) (w : World V X) (cw : Ref) : World V X × Ret V :=
  genIternext h w cw

/-- `coro_wrapper_send`, :1461-1466. -/
def coroWrapperSend (h : Hooks V X) (w : World V X) (cw : Ref) (arg : Obj V) : World V X × Ret V :=
  genSend h w cw (some arg)

/-- `coro_wrapper_throw`, :1468-1473. -/
def coroWrapperThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (cw : Ref)
    (args : List (Obj V)) : World V X × Ret V :=
  genThrow h fuel w cw args

/-- `coro_wrapper_close`, :1475-1480. -/
def coroWrapperClose (h : Hooks V X) (fuel : Nat) (w : World V X) (cw : Ref) : World V X × Ret V :=
  genCloseF h fuel w cw

/-! ## PEP 479 (`Python/intrinsics.c`) -/

/-- `stopiteration_error`, `Python/intrinsics.c:141-182`: the handler the compiler
wraps every generator body in. A frame's `raised` outcome has been through this,
which is why `gen_send_ex2` may assert no `StopIteration` comes out (:318-320). -/
def stopIterationError (kind : GenKind) (e : Exc V) : Exc V :=
  if e.isStopIteration then
    match kind with
    | .asyncGen => Exc.runtimeError "async generator raised StopIteration"
    | .coro => Exc.runtimeError "coroutine raised StopIteration"
    | .gen => Exc.runtimeError "generator raised StopIteration"
  else if kind = .asyncGen ∧ e.isStopAsyncIteration = true then
    Exc.runtimeError "async generator raised StopAsyncIteration"
  else e

/-- A resume wrapped in that handler. -/
def pep479 (w : World V X) (r : Ref) : ResumeOutcome V → ResumeOutcome V
  | .raised e => .raised (stopIterationError (w.get r).kind e)
  | out => out

end PyLean.Bytecode.GenObj
