import PyLean.Core
import PyLean.Bytecode.Opcode

/-!
State of the abstract machine for `Python/bytecodes.c` (CPython 3.15.2).

Three nested state monads keep the layers honest **by type**:

* `RM` runs object-level code: it sees the heap, `tstate->exc_info` and the
  recursion counters, but no frame at all. Everything `Objects/*.c` does lives
  here, so an object operation cannot touch an evaluation stack.
* `BM` adds the current frame and the instruction registers, but not the
  evaluation stack of the current frame. Instruction bodies live here.
* `M` adds the evaluation stack (`stack_pointer` in `_PyEval_EvalFrameDefault`).
  Only the stack-effect combinators in `Stack.lean` use it.

Control-flow labels of `Python/bytecodes.c` are constructors of `Err`, so a
`DEOPT_IF` or `goto exception_unwind` is an early exit carrying the state at
that point, exactly like the C `goto`.
-/

namespace PyLean.Bytecode

abbrev Addr := Nat

/-- A `_PyStackRef` or `PyObject *`. Objects with identity live in the heap
behind `ref`. Ints, floats and strs are immediates: identity of those is not
promised by the language, and the difftest never observes it. Builtin types and
builtin functions are stateless, so they are immediates named by their
`tp_name`. -/
inductive Val where
  /-- `PyStackRef_NULL` / a C `NULL`. -/
  | null
  | none
  | notImpl
  | ellipsis
  | bool (b : Bool)
  /-- An exact `int`. -/
  | int (i : Int)
  /-- An exact `float`, as its binary64 bit pattern. -/
  | float (bits : UInt64)
  /-- An exact `str`. -/
  | str (s : String)
  /-- An exact `bytes`. -/
  | bytes (b : List UInt8)
  /-- `PyStackRef_TagInt`: not an object. `lasti` slots hold one, and so does the
  `index_or_null` slot of a virtual iterator (`Python/ceval.c:1136`). -/
  | tagged (n : Nat)
  /-- A builtin type object, by `tp_name`. -/
  | cls (name : String)
  /-- A builtin function object (`PyCFunction`), by `__name__`. -/
  | builtin (name : String)
  /-- A method descriptor `tp.name` (`PyMethodDescr_Type`). -/
  | methDescr (tp name : String)
  /-- A code object: index into the `Program`. -/
  | code (i : Nat)
  | ref (a : Addr)
  deriving DecidableEq, Inhabited, Repr

/-- `_Py_CODEUNIT` plus the decoded inline cache of the instruction. -/
structure Instr where
  op : Op
  arg : Nat
  /-- Contents of the inline cache: versions as `.tagged`, cached objects as
  themselves. Filled only for specialized forms. -/
  cache : List Val := []
  deriving Inhabited

structure Code where
  name : String := ""
  qualname : String := ""
  flags : Nat := 0
  argcount : Nat := 0
  posonlyargcount : Nat := 0
  kwonlyargcount : Nat := 0
  nlocalsplus : Nat := 0
  ncellvars : Nat := 0
  nfreevars : Nat := 0
  stacksize : Nat := 0
  consts : Array Val := #[]
  names : Array String := #[]
  localsplusnames : Array String := #[]
  /-- `co_localspluskinds`: CO_FAST_LOCAL 0x20, CELL 0x40, FREE 0x80, HIDDEN 0x10. -/
  localspluskinds : Array Nat := #[]
  instrs : Array Instr := #[]
  exceptiontable : Array Nat := #[]
  version : Nat := 0
  deriving Inhabited

abbrev Program := Array Code

inductive FrameOwner where
  | thread
  /-- `FRAME_OWNED_BY_GENERATOR`, with the generator's address. -/
  | generator (g : Addr)
  | interpreter
  deriving DecidableEq, Inhabited, Repr

/-- `_PyInterpreterFrame`. `stack` is only meaningful while the frame is not the
current one; for the current frame the live stack is `St.stack`, as
`stack_pointer` is for C. Head of the list is the top of the stack. -/
structure Frame where
  /-- `f_executable`, an index into the `Program`. -/
  code : Nat := 0
  funcobj : Val := .none
  globals : Val := .null
  builtins : Val := .null
  /-- `f_locals`; `.null` for optimized code. -/
  locals : Val := .null
  instrPtr : Nat := 0
  returnOffset : Nat := 0
  /-- `localsplus[0 .. co_nlocalsplus)`. -/
  fast : Array Val := #[]
  stack : List Val := []
  owner : FrameOwner := .thread
  deriving Inhabited

structure FuncObj where
  code : Nat := 0
  globals : Val := .null
  builtins : Val := .null
  name : String := ""
  qualname : String := ""
  /-- A tuple or `.null`. -/
  defaults : Val := .null
  /-- A dict or `.null`. -/
  kwdefaults : Val := .null
  /-- A tuple of cells or `.null`. -/
  closure : Val := .null
  annotations : Val := .null
  annotate : Val := .null
  typeparams : Val := .null
  dict : Val := .null
  version : Nat := 0
  deriving Inhabited

/-- The kind of a `PyGenObject`. -/
inductive GenKind where
  | gen | coro | asyncGen
  deriving DecidableEq, Inhabited, Repr

/-- `PyGenObject`. `gi_frame_state` as the enum values of `pycore_frame.h:47-54`:
`FRAME_CREATED` 0, `FRAME_SUSPENDED` 1, `FRAME_SUSPENDED_YIELD_FROM` 2,
`FRAME_SUSPENDED_YIELD_FROM_LOCKED` 3 (free-threaded only), `FRAME_EXECUTING` 4,
`FRAME_CLEARED` 5. -/
structure GenObj where
  kind : GenKind := .gen
  frame : Frame := {}
  frameState : Int := 0
  /-- `gi_exc_state.exc_value`. -/
  excValue : Val := .null
  name : String := ""
  qualname : String := ""
  /-- `ag_hooks_inited` of an async generator (`Include/internal/pycore_genobject.h`). -/
  hooksInited : Bool := false
  /-- `ag_running_async`: an `asend`/`athrow` awaitable is running the generator. -/
  runningAsync : Bool := false
  /-- `ag_closed`. -/
  agClosed : Bool := false
  /-- `cr_origin_or_finalizer` of a coroutine, as `cr_origin` reads it: `none` for NULL, else one
  `(code, lasti)` per frame, innermost first, from which `_PyCoro_ComputeOrigin`
  (`Objects/genobject.c:1540-1570`) builds `(co_filename, PyUnstable_InterpreterFrame_GetLine(frame),
  co_name)`; the machine has no line table, so the line is kept as the `lasti` it is read from, as
  `Obj.traceback` keeps `tb_lasti`. -/
  origin : Option (List (Nat × Nat)) := none
  deriving Inhabited

/-- `PyDictKeyEntry`: the stored hash is what makes equality calls observable
in the same order as `lookdict`. -/
structure DictEntry where
  hash : Int
  key : Val
  value : Val
  deriving Inhabited

structure DictObj where
  entries : Array DictEntry := #[]
  /-- `dk_version`: changes whenever the key set changes. -/
  version : Nat := 0
  deriving Inhabited

/-- Per-exception fields of `PyBaseExceptionObject`. -/
structure ExcData where
  args : Val := .null
  cause : Val := .null
  context : Val := .null
  suppressContext : Bool := false
  /-- `PyStopIterationObject.value`. -/
  value : Val := .none
  /-- `PyNameErrorObject.name`, `NULL` until set. -/
  name : Val := .null
  /-- `PyBaseExceptionObject.traceback`, a traceback object or `.null`. -/
  traceback : Val := .null
  deriving Inhabited

structure ClassObj where
  name : String := ""
  qualname : String := ""
  bases : List Val := []
  mro : List Val := []
  dict : Addr := 0
  metaclass : Val := .cls "type"
  /-- `tp_version_tag`. -/
  version : Nat := 0
  /-- Names in `__slots__`. -/
  slots : List String := []
  /-- Instances have a `__dict__`. -/
  hasDict : Bool := true
  /-- `__abstractmethods__`; non-empty is `Py_TPFLAGS_IS_ABSTRACT`. -/
  abstractMethods : List String := []
  deriving Inhabited

structure InstObj where
  cls : Val := .cls "object"
  /-- The `__dict__`, a dict address, or `.null` while not yet materialized. -/
  dict : Val := .null
  slots : Array Val := #[]
  /-- The builtin payload for a subclass of a builtin value type. -/
  base : Val := .null
  exc : Option ExcData := .none
  deriving Inhabited

/-- Heap objects. -/
inductive Obj where
  | tuple (items : Array Val)
  | list (items : Array Val)
  | dict (d : DictObj)
  /-- `set`, or `frozenset` when `frozen`; each item with its hash. -/
  | set (frozen : Bool) (items : Array (Int × Val))
  | slice (start stop step : Val)
  | range (start stop step len : Int)
  | cell (v : Val)
  | func (f : FuncObj)
  | method (func self : Val)
  | gen (g : GenObj)
  /-- `_PyListIterObject`: `seq = none` once exhausted, `it_index` may be `-1`. -/
  | listIter (seq : Option Addr) (index : Int)
  | tupleIter (seq : Option Addr) (index : Int)
  | rangeIter (start step len : Int)
  /-- `strIter`: remaining characters. -/
  | strIter (rest : List Char)
  /-- The generic `iter(seq)` of `Objects/iterobject.c`. -/
  | seqIter (seq : Val) (index : Int)
  | callIter (callable sentinel : Val)
  /-- kind: 0 keys, 1 values, 2 items. `used` is the size at creation. -/
  | dictIter (d : Addr) (kind : Nat) (index : Nat) (used : Nat)
  | dictView (d : Addr) (kind : Nat)
  | setIter (items : Array (Int × Val)) (index : Nat)
  | enumerate (it : Val) (index : Int)
  | zip (its : List Val) (strict : Bool)
  | map (f : Val) (its : List Val)
  | filter (f it : Val)
  | reversed (seq : Val) (index : Int)
  | cls (c : ClassObj)
  | inst (i : InstObj)
  | module (name : String) (dict : Addr)
  /-- `super(type, obj)`. -/
  | super (tp obj objType : Val)
  | property (fget fset fdel : Val)
  | staticMethod (f : Val)
  | classMethod (f : Val)
  /-- A builtin method bound to `self`. -/
  | boundBuiltin (tp name : String) (self : Val)
  /-- `PyAsyncGenASend` (`Objects/genobject.c:1601-1615`): `ags_gen`, `ags_sendval` (`.null` for
  `__anext__`) and `ags_state`, `AWAITABLE_STATE_INIT` 0, `_ITER` 1, `_CLOSED` 2. -/
  | asend (gen : Addr) (sendval : Val) (state : Nat)
  /-- `_PyAsyncGenWrappedValue`, the `agw_val` an async generator yields. -/
  | agWrapped (v : Val)
  /-- `PyTracebackObject` (`Include/internal/pycore_traceback.h`): `tb_next` (`.null` for none), the
  code of `tb_frame`, and `tb_lasti` as a code unit index (the attribute is twice it). The frame object
  itself is not modelled. -/
  | traceback (next : Val) (code : Nat) (lasti : Nat)
  deriving Inhabited

/-- The label a macro leaves through. -/
inductive Err where
  /-- A Python exception is set: `goto error`. -/
  | exc (v : Val)
  /-- `goto exception_unwind`: the error was already reported (`RERAISE`). -/
  | unwind (v : Val)
  /-- `DEOPT_IF` / `EXIT_IF`. -/
  | deopt
  /-- `DISPATCH()` or `DISPATCH_INLINED()` from inside a macro. -/
  | dispatch
  /-- `goto exit_unwind`. -/
  | exitUnwind (v : Val)
  /-- `return` from `_PyEval_EvalFrameDefault` with this value. -/
  | leave (v : Val)
  /-- The model's fuel ran out; never a Python outcome. -/
  | fuel
  /-- Undefined behaviour of the C code on bytecode no compiler produces. -/
  | fault (msg : String)
  deriving Inhabited

/-- The part of `PyThreadState`/`PyInterpreterState` that object code can see. -/
structure Rt where
  heap : Array Obj := #[]
  /-- What `print` wrote. -/
  out : Array String := #[]
  /-- `tstate->exc_info` chain, innermost first: the `exc_value` of each item. -/
  excInfo : List Val := [.null]
  /-- `tstate->py_recursion_remaining`. -/
  pyRecursionRemaining : Int := 1000
  /-- `Py_GetRecursionLimit()`. -/
  recursionLimit : Int := 1000
  /-- Source of fresh `dk_version` / `tp_version_tag` values. -/
  nextVersion : Nat := 1
  /-- The builtins dict. -/
  builtinsDict : Val := .null
  /-- `_PyThreadState_HasStackSpace`: whether the current data-stack chunk has
  room. It depends on the allocator's chunk boundaries, so it is an oracle. -/
  stackSpace : Bool := true
  /-- What `_Py_HandlePending` raises at the next periodic check, or `.null` when the eval
  breaker has no event or its handlers succeed. A signal handler is Python code the model does
  not run, so the outcome of the pending work is an oracle, as `stackSpace` is. -/
  pendingExc : Val := .null
  /-- `Py_Is` on two equal immediates that are not singletons (ints, floats, strs, bytes with the
  same value): whether they are one object depends on how each was made (the small-int cache,
  interning, constant merging, a variable copied), which the machine does not track, so it is an
  oracle, as `stackSpace` is. -/
  sameImmediate : Val → Val → Bool := fun _ _ => false
  /-- `tstate->async_gen_firstiter`, `.null` when unset (`sys.set_asyncgen_hooks`). -/
  asyncGenFirstiter : Val := .null
  /-- `tstate->coroutine_origin_tracking_depth` (`sys.set_coroutine_origin_tracking_depth`). -/
  coroOriginDepth : Nat := 0
  /-- `_Py_ReachedRecursionLimit(tstate)` (`Python/ceval.c`): whether the machine stack pointer is
  past the soft limit. It depends on C stack use, which the machine does not track, so it is an
  oracle, as `stackSpace` is. -/
  cRecursionReached : Bool := false
  /-- Written only by the profiling loop of the difftest: per code object and
  instruction, the specialized form seen first. -/
  profile : Array (Array (Option Instr)) := #[]
  deriving Inhabited

/-- Everything except the evaluation stack of the current frame. -/
structure Regs where
  rt : Rt := {}
  frame : Frame := {}
  /-- `frame->previous` chain. -/
  prev : List Frame := []
  /-- The `next_instr` register. -/
  next : Nat := 0
  deriving Inhabited

structure St where
  regs : Regs := {}
  /-- `stack_pointer`: the current frame's evaluation stack, head on top. -/
  stack : List Val := []
  deriving Inhabited

abbrev RM := EStateM Err Rt
abbrev BM := EStateM Err Regs
abbrev M := EStateM Err St

def RM.lift {α : Type} (m : RM α) : BM α := fun r =>
  match m r.rt with
  | .ok a rt => .ok a { r with rt := rt }
  | .error e rt => .error e { r with rt := rt }

def BM.lift {α : Type} (m : BM α) : M α := fun s =>
  match m s.regs with
  | .ok a r => .ok a { s with regs := r }
  | .error e r => .error e { s with regs := r }

instance : MonadLift RM BM := ⟨RM.lift⟩
instance : MonadLift BM M := ⟨BM.lift⟩

/-- Two's-complement view of an `Int` in `w` bits. -/
def twos (w : Nat) (i : Int) : Nat := (i % ((2 : Int) ^ w)).toNat
/-- The inverse of `twos`, for `n < 2 ^ w`. -/
def fromTwos (w n : Nat) : Int := if 2 ^ (w - 1) ≤ n then (n : Int) - (2 : Int) ^ w else n
/-- A width that holds `a` and `b` and a sign bit. -/
def bitWidth (a b : Int) : Nat := Nat.log2 (a.natAbs + b.natAbs + 1) + 3
/-- `int.__and__`, `__or__`, `__xor__` on Python's infinite two's complement. -/
def intAnd (a b : Int) : Int := let w := bitWidth a b; fromTwos w (twos w a &&& twos w b)
def intOr (a b : Int) : Int := let w := bitWidth a b; fromTwos w (twos w a ||| twos w b)
def intXor (a b : Int) : Int := let w := bitWidth a b; fromTwos w (twos w a ^^^ twos w b)

/-- `Py_DEBUG`-only `assert` or bytecode no compiler emits. -/
def fault {α : Type} {σ : Type} (msg : String) : EStateM Err σ α := throw (.fault msg)

/-! ## Heap access -/

def getObj (a : Addr) : RM Obj := fun rt =>
  match rt.heap[a]? with
  | some o => .ok o rt
  | none => .error (.fault "dangling reference") rt

def setObj (a : Addr) (o : Obj) : RM Unit := fun rt =>
  .ok () { rt with heap := rt.heap.setIfInBounds a o }

def alloc (o : Obj) : RM Val := fun rt =>
  .ok (.ref rt.heap.size) { rt with heap := rt.heap.push o }

def freshVersion : RM Nat := fun rt =>
  .ok rt.nextVersion { rt with nextVersion := rt.nextVersion + 1 }

def write (s : String) : RM Unit := fun rt => .ok () { rt with out := rt.out.push s }

/-- Allocate a tuple. -/
def mkTuple (items : List Val) : RM Val := alloc (.tuple items.toArray)
def mkList (items : List Val) : RM Val := alloc (.list items.toArray)

/-- The items of a tuple address. -/
def tupleItems : Val → RM (Array Val)
  | .null => pure #[]
  | .ref a => do
    match ← getObj a with
    | .tuple items => pure items
    | _ => fault "expected a tuple"
  | _ => fault "expected a tuple"

/-! ## Frame and register access -/

def getFrame : BM Frame := fun r => .ok r.frame r
def modifyFrame (f : Frame → Frame) : BM Unit := fun r => .ok () { r with frame := f r.frame }
def getNext : BM Nat := fun r => .ok r.next r
def setNext (n : Nat) : BM Unit := fun r => .ok () { r with next := n }
/-- `JUMPBY(x)`. -/
def jumpBy (x : Int) : BM Unit := fun r => .ok () { r with next := (r.next + x).toNat }

/-- `GETLOCAL(i)`. -/
def getLocal (i : Nat) : BM Val := fun r =>
  match r.frame.fast[i]? with
  | some v => .ok v r
  | none => .error (.fault "local index out of range") r

/-- `GETLOCAL(i) = v`. -/
def setLocal (i : Nat) (v : Val) : BM Unit := fun r =>
  .ok () { r with frame := { r.frame with fast := r.frame.fast.setIfInBounds i v } }

def getCode (P : Program) : BM Code := fun r =>
  match P[r.frame.code]? with
  | some c => .ok c r
  | none => .error (.fault "no code object") r

end PyLean.Bytecode
