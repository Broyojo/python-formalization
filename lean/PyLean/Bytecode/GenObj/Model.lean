/-!
# `Objects/genobject.c` (CPython 3.14.7): generators and coroutines

A standalone state machine, mirroring the C source branch by branch. Line numbers
are those of `Objects/genobject.c` unless another file is named.

The interpreter is abstracted away: the only way the model runs Python code is
through the fields of `Hooks`, above all the plain function `Hooks.resume`, which
stands for `_PyEval_EvalFrame(tstate, frame, exc)` (:259). A frame evaluator from
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
  has no depth limit there, which is a finding (`genCloseDepth` below); the model
  takes fuel, and `Exc.fuel` is never a Python outcome.
* `gi_exc_state`, `tstate->exc_info`, tracebacks and `__context__` chaining
  (:248-255) are bookkeeping for the frame evaluator: they change which exception
  context a frame sees but none of the state machine, so they are not modelled.
-/

namespace PyLean.Bytecode.GenObj

abbrev Ref := Nat

/-- `PyFrameState`, `Include/internal/pycore_frame.h:46-53`. -/
inductive FrameState where
  | created | suspended | suspendedYieldFrom | executing | completed | cleared
  deriving DecidableEq, Repr, Inhabited

/-- The C enum values, `pycore_frame.h:47-52`. -/
def FrameState.toInt : FrameState → Int
  | .created => -3
  | .suspended => -2
  | .suspendedYieldFrom => -1
  | .executing => 0
  | .completed => 1
  | .cleared => 4

/-- `FRAME_STATE_SUSPENDED(S)`, `pycore_frame.h:55`. -/
def FrameState.isSuspended : FrameState → Bool
  | .suspended | .suspendedYieldFrom => true
  | _ => false

/-- `FRAME_STATE_FINISHED(S)`, `pycore_frame.h:56`: `(S) >= FRAME_COMPLETED`. -/
def FrameState.finished (s : FrameState) : Bool := decide (s.toInt ≥ 1)

/-- `gi_frame_state = FRAME_SUSPENDED + oparg` (`YIELD_VALUE`,
`Python/bytecodes.c:1379`); the oparg is 0 or 1. -/
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

/-- Where `frame->instr_ptr` points, as far as `is_resume` (:362-371) and the
`RESUME_OPARG_DEPTH1_MASK` test (:415-416) can tell. `is_resume` accepts `RESUME`,
`RESUME_CHECK` and `INSTRUMENTED_RESUME`; `depth1` is the mask bit. -/
inductive InstrPtr where
  | resume (depth1 : Bool)
  | other
  deriving DecidableEq, Repr, Inhabited

/-- `PyGenObject`, with the `PyAsyncGenObject`/`PyCoroObject` tail. -/
structure GenObj (V : Type) where
  kind : GenKind := .gen
  /-- `gi_frame_state` -/
  state : FrameState := .cleared
  /-- `gi_iframe.instr_ptr` -/
  instr : InstrPtr := .other
  /-- `_PyFrame_StackPeek(frame)`, meaningful when suspended in a `yield from`. -/
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

/-- `AwaitableState`, :1431-1435. -/
inductive AwaitableState where
  | init | iter | closed
  deriving DecidableEq, Repr, Inhabited

/-- `PyAsyncGenASend`, :1438-1447. -/
structure ASend (V : Type) where
  gen : Ref := 0
  /-- `ags_sendval`: `none` is NULL, the `__anext__()` mode. -/
  sendval : Option (Obj V) := none
  state : AwaitableState := .closed
  deriving Inhabited

/-- `PyAsyncGenAThrow`, :1453-1462. -/
structure AThrow (V : Type) where
  gen : Ref := 0
  /-- `agt_args`: `none` is NULL, the `aclose()` mode; otherwise the args tuple. -/
  args : Option (List (Obj V)) := none
  state : AwaitableState := .closed
  deriving Inhabited

/-- The heap. `X` is free for the instantiation (frames and so on). -/
structure World (V X : Type) where
  gens : Ref → GenObj V
  asends : Ref → ASend V
  athrows : Ref → AThrow V
  /-- `_PyEval_NoToolsForUnwind(tstate)`, `Python/ceval.c:2582-2584`. -/
  noUnwindTools : Bool := true
  /-- `tstate->coroutine_origin_tracking_depth` -/
  originDepth : Nat := 0
  /-- The Python call stack at `compute_cr_origin` time, innermost first. -/
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

/-- What `_PyEval_EvalFrame` left behind (:259). For `yielded`, `oparg` is
`YIELD_VALUE`'s oparg (`false` is 0: `FRAME_SUSPENDED`, `true` is 1:
`FRAME_SUSPENDED_YIELD_FROM`), `depth1` is `RESUME_OPARG_DEPTH1_MASK` of the
`RESUME` that follows it, and `top` is what `_PyFrame_StackPeek` then sees. -/
inductive ResumeOutcome (V : Type) where
  | yielded (oparg : Bool) (value : Obj V) (depth1 : Bool) (top : Obj V)
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
  /-- `_PyEval_EvalFrame(tstate, frame, exc)` (:259): runs the frame of `r`, whose
  `gi_frame_state` is `FRAME_EXECUTING`, with the sent value on the stack and the
  thrown exception if any. -/
  resume : World V X → Ref → Obj V → Option (Exc V) → World V X × ResumeOutcome V
  /-- `PyObject_GetOptionalAttr(yf, &_Py_ID(close), &meth)` (:347). -/
  getClose : World V X → Obj V → World V X × Except (Exc V) (Option (Obj V))
  /-- `PyObject_GetOptionalAttr(yf, &_Py_ID(throw), &meth)` (:514). -/
  getThrow : World V X → Obj V → World V X × Except (Exc V) (Option (Obj V))
  /-- `_PyObject_CallNoArgs(meth)` (:352). -/
  callNoArgs : World V X → Obj V → World V X × Ret V
  /-- `PyObject_CallOneArg` (:103, :1521). -/
  callOneArg : World V X → Obj V → Obj V → World V X × Ret V
  /-- `PyObject_CallFunctionObjArgs(meth, typ, val, tb, NULL)` (:528). -/
  callThrow : World V X → Obj V → Obj V → Option (Obj V) → Option (Obj V) → World V X × Ret V
  /-- `PyErr_FormatUnraisable` (:105, :132, :348). -/
  unraisable : World V X → String → Exc V → World V X
  /-- `PyErr_WarnEx(PyExc_DeprecationWarning, msg, 1)` (:610, :1570): an exception
  when warnings are errors. -/
  warn : World V X → String → World V X × Option (Exc V)
  /-- `_PyErr_WarnUnawaitedCoroutine` (:126). -/
  warnUnawaitedCoro : World V X → Ref → World V X
  /-- `_PyErr_WarnUnawaitedAgenMethod` (:1901, :2343). -/
  warnUnawaitedAgen : World V X → Ref → String → World V X
  /-- `PyErr_NormalizeException(&typ, &val, &tb)` (:558) for a class `typ`. -/
  normalize : Obj V → Option (Obj V) → Exc V
  /-- `Py_TYPE(o)->tp_name`. -/
  typeName : Obj V → String
  /-- `PySys_Audit("object.__getattr__", "Os", gen, name)` (:780, :799). -/
  audit : World V X → String → Option (Exc V)
  /-- `_PyFrame_GetFrameObject` (:786). -/
  frameObject : World V X → Ref → Obj V
  /-- `PyIter_Check`. -/
  isIter : Obj V → Bool
  /-- `ot->tp_as_async->am_await` (:1080-1084); `none` when there is no getter. -/
  amAwait : World V X → Obj V → Option (World V X × Ret V)

variable {V X : Type}

/-! ## `gen_send_ex2` and its callers -/

/-- `arg && arg != Py_None` (:199). -/
def isNonNull : Option (Obj V) → Bool
  | none | some .none => false
  | some _ => true

/-- :200-208. -/
def cantSendMsg : GenKind → String
  | .gen => "can't send non-None value to a just-started generator"
  | .coro => "can't send non-None value to a just-started coroutine"
  | .asyncGen => "can't send non-None value to a just-started async generator"

/-- :213-219. -/
def alreadyExecutingMsg : GenKind → String
  | .gen => "generator already executing"
  | .coro => "coroutine already executing"
  | .asyncGen => "async generator already executing"

/-- `result == Py_None` -/
def Obj.isNone : Obj V → Bool
  | .none => true
  | _ => false

/-- `clear_gen_frame`, `Python/ceval.c:1944-1956`, what a frame does to its
generator as it returns or raises. -/
def clearGenFrame (w : World V X) (r : Ref) : World V X :=
  w.setState r .cleared

/-- What `YIELD_VALUE` does to its generator, `Python/bytecodes.c:1375-1379`. -/
def suspendFrame (w : World V X) (r : Ref) (oparg depth1 : Bool) (top : Obj V) : World V X :=
  w.set r { w.get r with
    state := FrameState.ofOparg oparg
    instr := .resume depth1
    stackTop := top }

/-- `gen_send_ex2`, :191-288. `exc`/`err` are the C `exc` flag and, when set, the
pending exception. Everything from `gen_send_ex2`'s `*presult = NULL` to its
`return` is mirrored in order; the state write after the resume is the one
`YIELD_VALUE` or `clear_gen_frame` does before control comes back. -/
def genSendEx2 (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (exc : Bool) (err : Option (Exc V)) (closing : Bool) : World V X × SendResult V :=
  let g := w.get r
  if g.state = .created ∧ isNonNull arg = true then
    (w, .err (some (Exc.typeError (cantSendMsg g.kind))))
  else if g.state = .executing then
    (w, .err (some (Exc.valueError (alreadyExecutingMsg g.kind))))
  else if g.state.finished = true then
    if g.kind = .coro ∧ closing = false then
      (w, .err (some (Exc.runtimeError "cannot reuse already awaited coroutine")))
    else if arg.isSome = true ∧ exc = false then
      (w, .ret .none)
    else
      (w, .err err)
  else
    let argObj := arg.getD .none
    let w1 := w.setState r .executing
    let (w2, out) := h.resume w1 r argObj (if exc then err else none)
    match out with
    | .yielded oparg v depth1 top => (suspendFrame w2 r oparg depth1 top, .next v)
    | .returned v =>
      let w3 := clearGenFrame w2 r
      if v.isNone = true ∧ g.kind ≠ .asyncGen ∧ arg.isNone = true then
        (w3, .err none)
      else
        (w3, .ret v)
    | .raised e => (clearGenFrame w2 r, .err (some e))

/-- `PyGen_am_send`, :290-295. -/
def pyGenAmSend (h : Hooks V X) (w : World V X) (r : Ref) (arg : Obj V) :
    World V X × SendResult V :=
  genSendEx2 h w r (some arg) false none false

/-- `_PyGen_SetStopIterationValue`, :651-668: a tuple value stays a tuple. -/
def setStopIterationValue (value : Obj V) : Exc V :=
  ⟨.stopIteration, "StopIteration", "", value⟩

/-- `_PyGen_FetchStopIterationValue`, :679-695. `.ok v` is the 0 return with
`*pvalue = v`; `.err` keeps the pending exception, the -1 return. -/
def fetchStopIterationValue (pending : Option (Exc V)) : Ret V :=
  match pending with
  | some e => if e.isStopIteration then .ok e.value else .err (some e)
  | none => .ok .none

/-- `gen_send_ex`, :297-315. -/
def genSendEx (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (exc : Bool) (err : Option (Exc V)) (closing : Bool) : World V X × Ret V :=
  match genSendEx2 h w r arg exc err closing with
  | (w', .ret v) =>
    if (w.get r).kind = .asyncGen then (w', .err (some Exc.stopAsyncIteration))
    else if v.isNone = true then (w', .err (some Exc.stopIterationNone))
    else (w', .err (some (setStopIterationValue v)))
  | (w', .next v) => (w', .ok v)
  | (w', .err e) => (w', .err e)

/-- `gen_send`, :321-325. `arg` is `none` for the `async_gen_asend_send` call with
`ags_sendval == NULL`. -/
def genSend (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)) :
    World V X × Ret V :=
  genSendEx h w r arg false none false

/-- `gen_iternext`, :629-643. -/
def genIternext (h : Hooks V X) (w : World V X) (r : Ref) : World V X × Ret V :=
  match genSendEx2 h w r none false none false with
  | (w', .ret v) =>
    if v.isNone = true then (w', .err none)
    else (w', .err (some (setStopIterationValue v)))
  | (w', .next v) => (w', .ok v)
  | (w', .err e) => (w', .err e)

/-- `next(gen)` / `gen.__next__()`: `NULL` with no exception means `StopIteration`
(`wrap_next` in `Objects/typeobject.c`, `builtin_next` in `Python/bltinmodule.c`). -/
def nextCall (h : Hooks V X) (w : World V X) (r : Ref) : World V X × Ret V :=
  match genIternext h w r with
  | (w', .err none) => (w', .err (some Exc.stopIterationNone))
  | res => res

/-! ## Delegation: `_PyGen_yf`, `gen_close`, `_gen_throw` -/

/-- `is_resume` (:362-371) followed by the mask test at :415-416. -/
def InstrPtr.isResumeDepth1 : InstrPtr → Bool
  | .resume d => d
  | .other => false

/-- `_PyGen_yf`, :373-384. -/
def genYf (g : GenObj V) : Option (Obj V) :=
  if g.state = .suspendedYieldFrom then some g.stackTop else none

/-- `PyGen_CheckExact(yf) || PyCoro_CheckExact(yf)` (:340, :493). -/
def genOrCoro? (w : World V X) : Obj V → Option Ref
  | .gen r => if (w.get r).kind = .asyncGen then none else some r
  | _ => none

/-- :347-356, the non-generator path of `gen_close_iter`. -/
def genCloseIterForeign (h : Hooks V X) (w : World V X) (yf : Obj V) :
    World V X × CStatus V :=
  let (w1, m) := h.getClose w yf
  let (w2, meth) : World V X × Option (Obj V) := match m with
    | .error e => (h.unraisable w1 "Exception ignored while closing generator" e, none)
    | .ok mo => (w1, mo)
  match meth with
  | some mt =>
    match h.callNoArgs w2 mt with
    | (w3, .err e) => (w3, .fail e)
    | (w3, .ok _) => (w3, .ok)
  | none => (w2, .ok)

/-- `gen_close_iter`, :335-360. `close` is `gen_close` at the next recursion depth. -/
def genCloseIter (h : Hooks V X) (close : World V X → Ref → World V X × Ret V)
    (w : World V X) (yf : Obj V) : World V X × CStatus V :=
  match genOrCoro? w yf with
  | some r =>
    match close w r with
    | (w', .err e) => (w', .fail e)
    | (w', .ok _) => (w', .ok)
  | none => genCloseIterForeign h w yf

/-- :430-435. -/
def ignoredExitMsg : GenKind → String
  | .gen => "generator ignored GeneratorExit"
  | .coro => "coroutine ignored GeneratorExit"
  | .asyncGen => "async generator ignored GeneratorExit"

/-- `gen_clear_frame`, :145-156. -/
def genClearFrame (w : World V X) (r : Ref) : World V X :=
  if (w.get r).state = .cleared then w else w.setState r .cleared

/-- :428-452, the end of `gen_close`: throw into the frame and interpret the result. -/
def genCloseFinish (h : Hooks V X) (w : World V X) (r : Ref) (pending : Option (Exc V)) :
    World V X × Ret V :=
  match genSendEx h w r (some .none) true pending true with
  | (w', .ok _) => (w', .err (some (Exc.runtimeError (ignoredExitMsg (w.get r).kind))))
  | (w', .err e) =>
    match e with
    | some x =>
      if x.isGeneratorExit then (w', .ok .none)
      else (w', fetchStopIterationValue e)
    | none => (w', fetchStopIterationValue e)

/-- :400-452 after the two early returns, with `close` the recursive `gen_close`. -/
def genCloseBody (h : Hooks V X) (close : World V X → Ref → World V X × Ret V)
    (w : World V X) (r : Ref) : World V X × Ret V :=
  let (w1, err) : World V X × CStatus V :=
    match genYf (w.get r) with
    | some yf =>
      let state := (w.get r).state
      let (w', st) := genCloseIter h close (w.setState r .executing) yf
      (w'.setState r state, st)
    | none => (w, .ok)
  if (w1.get r).instr.isResumeDepth1 = true ∧ w1.noUnwindTools = true then
    (genClearFrame (w1.setState r .completed) r, .ok .none)
  else
    let pending : Option (Exc V) := match err with
      | .ok => some Exc.generatorExit
      | .fail e => e
    genCloseFinish h w1 r pending

/-- `gen_close`, :386-453, with fuel for the C recursion through `gen_close_iter`. -/
def genCloseF (h : Hooks V X) : Nat → World V X → Ref → World V X × Ret V
  | 0, w, _ => (w, .err (some Exc.fuel))
  | n + 1, w, r =>
    if (w.get r).state = .created then
      (genClearFrame (w.setState r .completed) r, .ok .none)
    else if (w.get r).state.finished = true then
      (w, .ok .none)
    else
      genCloseBody h (genCloseF h n) w r

/-- `PyErr_GivenExceptionMatches(typ, PyExc_GeneratorExit)` (:475). -/
def givenMatchesGeneratorExit : Obj V → Bool
  | .excClass k _ | .excInst k _ _ _ => k == .generatorExit
  | _ => false

/-- `throw_here:`, :541-594. `tb == Py_None` becomes NULL, then the three shapes of
`typ`. -/
def throwHere (h : Hooks V X) (w : World V X) (r : Ref) (typ : Obj V)
    (val tb : Option (Obj V)) : World V X × Ret V :=
  let badTb := match tb with
    | none | some .none | some .traceback => false
    | some _ => true
  if badTb then
    (w, .err (some (Exc.typeError "throw() third argument must be a traceback object")))
  else
    match typ with
    | .excClass _ _ =>
      genSendEx h w r (some .none) true (some (h.normalize typ val)) false
    | .excInst k c m v =>
      if isNonNull val then
        (w, .err (some (Exc.typeError "instance exception may not have a separate value")))
      else
        genSendEx h w r (some .none) true (some ⟨k, c, m, v⟩) false
    | _ =>
      (w, .err (some (Exc.typeError
        ("exceptions must be classes or instances deriving from BaseException, not "
          ++ h.typeName typ))))

/-- :534-538: if delegation failed, the error goes into the delegating frame. -/
def afterDelegate (h : Hooks V X) (w : World V X) (r : Ref) : Ret V → World V X × Ret V
  | .ok v => (w, .ok v)
  | .err e => genSendEx h w r (some .none) true e false

/-- `_gen_throw`, :465-595, with fuel for the C recursion along the delegation
chain. -/
def genThrowF (h : Hooks V X) : Nat → World V X → Ref → Bool → Obj V →
    Option (Obj V) → Option (Obj V) → World V X × Ret V
  | 0, w, _, _, _, _, _ => (w, .err (some Exc.fuel))
  | n + 1, w, r, closeOnGenExit, typ, val, tb =>
    match genYf (w.get r) with
    | none => throwHere h w r typ val tb
    | some yf =>
      if givenMatchesGeneratorExit typ = true ∧ closeOnGenExit = true then
        let state := (w.get r).state
        let (w1, st) := genCloseIter h (genCloseF h n) (w.setState r .executing) yf
        let w2 := w1.setState r state
        match st with
        | .fail e => genSendEx h w2 r (some .none) true e false
        | .ok => throwHere h w2 r typ val tb
      else
        match genOrCoro? w yf with
        | some sub =>
          let state := (w.get r).state
          let (w1, ret) := genThrowF h n (w.setState r .executing) sub closeOnGenExit typ val tb
          afterDelegate h (w1.setState r state) r ret
        | none =>
          match h.getThrow w yf with
          | (w1, .error e) => (w1, .err (some e))
          | (w1, .ok none) => throwHere h w1 r typ val tb
          | (w1, .ok (some meth)) =>
            let state := (w1.get r).state
            let (w2, ret) := h.callThrow (w1.setState r .executing) meth typ val tb
            afterDelegate h (w2.setState r state) r ret

/-- `_PyArg_CheckPositional`, `Python/getargs.c`. -/
def checkPositional (name : String) (nargs lo hi : Nat) : Option (Exc V) :=
  if nargs < lo then
    some (Exc.typeError s!"{name} expected at least {lo} argument{if lo == 1 then "" else "s"}, got {nargs}")
  else if nargs > hi then
    some (Exc.typeError s!"{name} expected at most {hi} argument{if hi == 1 then "" else "s"}, got {nargs}")
  else none

/-- The `(typ, val, tb)` slots of a checked argument list, :617-624. -/
def unpackThrowArgs : List (Obj V) → Obj V × Option (Obj V) × Option (Obj V)
  | [typ] => (typ, none, none)
  | [typ, val] => (typ, some val, none)
  | typ :: val :: tb :: _ => (typ, some val, some tb)
  | [] => (.none, none, none)

/-- `gen_throw`, :598-626. -/
def genThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (args : List (Obj V)) :
    World V X × Ret V :=
  match checkPositional "throw" args.length 1 3 with
  | some e => (w, .err (some e))
  | none =>
    let (w1, warned) : World V X × Option (Exc V) :=
      if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
      else (w, none)
    match warned with
    | some e => (w1, .err (some e))
    | none =>
      let (typ, val, tb) := unpackThrowArgs args
      genThrowF h fuel w1 r true typ val tb

/-- The depth of the C recursion `gen_close` -> `gen_close_iter` -> `gen_close`
that `genCloseF` performs on a world, counting generator frames: one per link of
the `yield from` chain. No `_Py_EnterRecursiveCall` guards it. `seen` is fuel. -/
def genCloseDepth (w : World V X) : Nat → Ref → Nat
  | 0, _ => 0
  | n + 1, r =>
    match genYf (w.get r) with
    | some yf =>
      match genOrCoro? w yf with
      | some sub => genCloseDepth w n sub + 1
      | none => 1
    | none => 1

/-! ## `_PyGen_Finalize` -/

/-- `_PyGen_Finalize`, :86-143. -/
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

/-- `gen_get_name`, :705-710. -/
def genGetName (g : GenObj V) : Obj V := g.name
/-- `gen_get_qualname`, :727-732. -/
def genGetQualname (g : GenObj V) : Obj V := g.qualname

/-- `gen_set_name`, :712-725. `value` is `none` for `del gen.__name__`. -/
def genSetName (w : World V X) (r : Ref) (value : Option (Obj V)) : World V X × CStatus V :=
  match value with
  | some (.str s) => (w.set r { w.get r with name := .str s }, .ok)
  | _ => (w, .fail (some (Exc.typeError "__name__ must be set to a string object")))

/-- `gen_set_qualname`, :734-747. -/
def genSetQualname (w : World V X) (r : Ref) (value : Option (Obj V)) : World V X × CStatus V :=
  match value with
  | some (.str s) => (w.set r { w.get r with qualname := .str s }, .ok)
  | _ => (w, .fail (some (Exc.typeError "__qualname__ must be set to a string object")))

/-- `gen_getyieldfrom`, :749-757; `coro_get_cr_await`, :1129-1136 (also `ag_await`). -/
def genGetYieldFrom (g : GenObj V) : Obj V := (genYf g).getD .none

/-- `gen_getrunning`, :760-768; `cr_getrunning`, :1148-1156. -/
def genGetRunning (g : GenObj V) : Bool := decide (g.state = .executing)

/-- `gen_getsuspended`, :770-775; `cr_getsuspended`, :1138-1146;
`ag_getsuspended`, :1595-1603. -/
def genGetSuspended (g : GenObj V) : Bool := g.state.isSuspended

/-- `_gen_getframe`, :777-787, for `gi_frame`, `cr_frame`, `ag_frame`. -/
def genGetFrame (h : Hooks V X) (w : World V X) (r : Ref) (name : String) : Ret V :=
  match h.audit w name with
  | some e => .err (some e)
  | none =>
    if (w.get r).state.finished = true then .ok .none
    else .ok (h.frameObject w r)

/-- `_gen_getcode`, :796-803, for `gi_code`, `cr_code`, `ag_code`: `_PyGen_GetCode`
(:47-50) and `PyGen_GetCode` (:52-58) are this read of `f_executable`. -/
def genGetCode (h : Hooks V X) (w : World V X) (r : Ref) (name : String) :
    Except (Exc V) Code :=
  match h.audit w name with
  | some e => .error e
  | none => .ok (w.get r).code

/-- `gen_sizeof`, :830-839. `base` is
`offsetof(PyGenObject, gi_iframe) + offsetof(_PyInterpreterFrame, localsplus)` and
`_PyFrame_NumSlotsForCodeObject` is `co_nlocalsplus + co_stacksize`
(`Include/internal/pycore_interpframe.h`). -/
def genSizeof (base : Nat) (g : GenObj V) : Nat :=
  base + (g.code.nlocalsplus + g.code.stacksize) * 8

/-- `gen_repr`, :697-703, `coro_repr`, :1109-1115, `async_gen_repr`, :1487-1493,
without the trailing `%p`. -/
def reprPrefix : GenKind → String
  | .gen => "<generator object "
  | .coro => "<coroutine object "
  | .asyncGen => "<async_generator object "

def genRepr (g : GenObj V) (addr : String) (q : String) : String :=
  reprPrefix g.kind ++ q ++ " at " ++ addr ++ ">"

/-! ## Construction -/

/-- `make_gen`, :915-935: the frame state is `FRAME_CLEARED` until the frame is
copied in (`RETURN_GENERATOR` then sets `FRAME_CREATED`). -/
def makeGen (kind : GenKind) (code : Code) (funcName funcQualname : Obj V) : GenObj V :=
  { kind := kind, state := .cleared, code := code, name := funcName, qualname := funcQualname }

/-- `compute_cr_origin`, :1370-1400: count up to `origin_depth` frames, then collect
them, innermost first. -/
def computeCrOrigin (originDepth : Nat) (frames : List (String × Nat × String)) :
    List (String × Nat × String) :=
  let rec count (frame : List (String × Nat × String)) (frameCount : Nat) : Nat :=
    match frame with
    | [] => frameCount
    | _ :: rest =>
      if frameCount < originDepth then count rest (frameCount + 1) else frameCount
  let frameCount := count frames 0
  let rec collect (frame : List (String × Nat × String)) (i : Nat) :
      List (String × Nat × String) :=
    if i < frameCount then
      match frame with
      | [] => []
      | f :: rest => f :: collect rest (i + 1)
    else []
  termination_by frameCount - i
  collect frames 0

/-- `_Py_MakeCoro`, :940-985. Which of the three types the code flags select, and
the tail initialised for each. -/
def pyMakeCoro (w : World V X) (code : Code) (funcName funcQualname : Obj V) : Option (GenObj V) :=
  let coroFlags := code.flags &&& (CO_GENERATOR ||| CO_COROUTINE ||| CO_ASYNC_GENERATOR)
  if coroFlags = CO_GENERATOR then
    some (makeGen .gen code funcName funcQualname)
  else if coroFlags = CO_ASYNC_GENERATOR then
    some { makeGen .asyncGen code funcName funcQualname with
           finalizer := none, agClosed := false, agHooksInited := false, agRunningAsync := false }
  else if coroFlags = CO_COROUTINE then
    let g := makeGen .coro code funcName funcQualname
    if w.originDepth = 0 then
      some { g with origin := none }
    else
      some { g with origin := some (computeCrOrigin w.originDepth w.callStack) }
  else none

/-- `gen_new_with_qualname`, :987-1022: the frame is copied, the state is
`FRAME_CREATED`, and a NULL name or qualname falls back to the code object's. -/
def genNewWithQualname (kind : GenKind) (code : Code) (name qualname : Option (Obj V)) :
    GenObj V :=
  { kind := kind
    state := .created
    instr := .resume false
    code := code
    name := name.getD (.str code.name)
    qualname := qualname.getD (.str code.qualname) }

/-- `PyGen_NewWithQualName`, :1024-1028. -/
def pyGenNewWithQualName (code : Code) (name qualname : Option (Obj V)) : GenObj V :=
  genNewWithQualname .gen code name qualname

/-- `PyGen_New`, :1030-1034. -/
def pyGenNew (code : Code) : GenObj V := genNewWithQualname .gen code none none

/-- `PyCoro_New`, :1402-1425. -/
def pyCoroNew (w : World V X) (code : Code) (name qualname : Option (Obj V)) : GenObj V :=
  let g := genNewWithQualname .coro code name qualname
  if w.originDepth = 0 then { g with origin := none }
  else { g with origin := some (computeCrOrigin w.originDepth w.callStack) }

/-- `PyAsyncGen_New`, :1710-1725. -/
def pyAsyncGenNew (code : Code) (name qualname : Option (Obj V)) : GenObj V :=
  { genNewWithQualname .asyncGen code name qualname with
    finalizer := none, agClosed := false, agHooksInited := false, agRunningAsync := false }

/-! ## Coroutines -/

/-- `gen_is_coroutine`, :1048-1058. -/
def genIsCoroutine (w : World V X) : Obj V → Bool
  | .gen r =>
    (w.get r).kind = .gen ∧ (w.get r).code.hasFlag CO_ITERABLE_COROUTINE = true
  | _ => false

/-- `PyCoro_CheckExact(o)`. -/
def isCoro (w : World V X) : Obj V → Bool
  | .gen r => (w.get r).kind = .coro
  | _ => false

/-- `_PyCoro_GetAwaitableIter`, :1068-1107. -/
def pyCoroGetAwaitableIter (h : Hooks V X) (w : World V X) (o : Obj V) : World V X × Ret V :=
  if isCoro w o = true ∨ genIsCoroutine w o = true then
    (w, .ok o)
  else
    match h.amAwait w o with
    | some (w1, .ok res) =>
      if isCoro w1 res = true ∨ genIsCoroutine w1 res = true then
        (w1, .err (some (Exc.typeError "__await__() returned a coroutine")))
      else if h.isIter res = false then
        (w1, .err (some (Exc.typeError
          ("__await__() returned non-iterator of type '" ++ h.typeName res ++ "'"))))
      else
        (w1, .ok res)
    | some (w1, .err e) => (w1, .err e)
    | none =>
      (w, .err (some (Exc.typeError ("'" ++ h.typeName o ++ "' object can't be awaited"))))

/-- `coro_wrapper_iternext`, :1284-1289. `coro_await` (:1117-1127) just pairs the
coroutine with a wrapper, so a wrapper is its coroutine's `Ref`. -/
def coroWrapperIternext (h : Hooks V X) (w : World V X) (cw : Ref) : World V X × Ret V :=
  genIternext h w cw

/-- `coro_wrapper_send`, :1291-1296. -/
def coroWrapperSend (h : Hooks V X) (w : World V X) (cw : Ref) (arg : Obj V) : World V X × Ret V :=
  genSend h w cw (some arg)

/-- `coro_wrapper_throw`, :1298-1303. -/
def coroWrapperThrow (h : Hooks V X) (fuel : Nat) (w : World V X) (cw : Ref)
    (args : List (Obj V)) : World V X × Ret V :=
  genThrow h fuel w cw args

/-- `coro_wrapper_close`, :1305-1310. -/
def coroWrapperClose (h : Hooks V X) (fuel : Nat) (w : World V X) (cw : Ref) : World V X × Ret V :=
  genCloseF h fuel w cw

/-! ## PEP 479 (`Python/intrinsics.c`) -/

/-- `stopiteration_error`, `Python/intrinsics.c:143-186`: the handler the compiler
wraps every generator body in. A frame's `raised` outcome has been through this,
which is why `gen_send_ex2` may assert no `StopIteration` comes out (:279-281). -/
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
