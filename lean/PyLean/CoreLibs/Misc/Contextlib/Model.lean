import PyLean.CoreLibs.Misc.Contextlib.Exc

/-!
`Lib/contextlib.py`, CPython 3.14.7.

A generator is whatever implements `GenOps`, a state machine over `St σ`: `next`, `throw` and
`close` return the value yielded or the exception object raised. `_GeneratorContextManager` and its
async twin are one definition over `Cfg`, because they differ only in the class of the stop
exception, in one message, and in the tuple tested at Lib/contextlib.py:180 and :253. An `await` that
does not suspend has no observable effect, so the async methods are the sync algorithm with the
async object's operations, and what differs is in `Cfg` or written out (`aexit`).

An exit callback is abstract too: `Cb F O` is what `_exit_callbacks` holds and `Calls.call` what
calling `F` does, which lets a callback mutate the heap, the world and the stack itself.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

variable {σ V : Type}

/-! ### Abstract base classes -/

/-- `AbstractContextManager.__enter__`, Lib/contextlib.py:25-27, and
`AbstractAsyncContextManager.__aenter__`, :49-51. -/
def absEnter {O : Type} (self : O) : O := self

/-- `AbstractContextManager.__exit__`, Lib/contextlib.py:29-32, and
`AbstractAsyncContextManager.__aexit__`, :53-56: `None`, so the exception propagates. -/
def absExit {O : Type} (_self : O) (_excInfo : Option ExcId) : Option Bool := none

/-- A class as `_check_methods` reads it: its `__mro__`, each entry the names in `__dict__` with
`true` for a `None` value. -/
abbrev MroDicts := List (List (String × Bool))

/-- `_collections_abc._check_methods`, Lib/_collections_abc.py:108-118, for one method. -/
def checkMethod (mro : MroDicts) (m : String) : Bool :=
  match mro.findSome? (fun d => d.lookup m) with
  | some isNone => !isNone
  | none => false

/-- The result of `__subclasshook__`: `true` or `NotImplemented` (`none`). `exact` is `cls is
AbstractContextManager`. `AbstractContextManager.__subclasshook__`, Lib/contextlib.py:34-38, with
`__enter__`, `__exit__`; `AbstractAsyncContextManager.__subclasshook__`, :58-63, with `__aenter__`,
`__aexit__`. -/
def subclasshook (exact : Bool) (methods : List String) (mro : MroDicts) : Option Bool :=
  if exact then (if methods.all (checkMethod mro) then some true else none) else none

/-! ### The with statement -/

/-- A context manager, by its effect. `exit` gets `(type, value, tb)` as the exception or `none`,
and returns the truth value of the result. -/
structure CM (σ V : Type) where
  enter : St σ → St σ × Res V
  exit : St σ → Option ExcId → St σ × Res Bool

/-- The `with` statement, the compiler's expansion for `with mgr as x: body`, with `body` returning
`Res R`. On a body exception, `exit` runs with that exception being handled; a true result drops
it (`none`), a false one re-raises it. -/
def withStmt {R : Type} (cm : CM σ V) (body : V → St σ → St σ × Res R) (s : St σ) :
    St σ × Res (Option R) :=
  match cm.enter s with
  | (s, .error e) => (s, .error e)
  | (s, .ok v) =>
    match body v s with
    | (s, .ok r) =>
      match cm.exit s none with
      | (s, .error e) => (s, .error e)
      | (s, .ok _) => (s, .ok (some r))
    | (s, .error e) =>
      match cm.exit s (some e) with
      | (s, .error e2) => (s, .error e2)
      | (s, .ok true) => (s, .ok none)
      | (s, .ok false) => (s, .error e)

/-! ### `ContextDecorator` -/

/-- `ContextDecorator._recreate_cm`, Lib/contextlib.py:69-79, and
`AsyncContextDecorator._recreate_cm`, :92-95. -/
def ContextDecorator.recreateCm {C : Type} (self : C) : C := self

/-- `inner` of `ContextDecorator.__call__`, Lib/contextlib.py:81-86, and of
`AsyncContextDecorator.__call__`, :97-102: `recreate` builds the context manager for this call. -/
def ContextDecorator.call {R C : Type} (recreate : St σ → St σ × Res C) (toCM : C → CM σ V)
    (func : St σ → St σ × Res R) (s : St σ) : St σ × Res (Option R) :=
  match recreate s with
  | (s, .error e) => (s, .error e)
  | (s, .ok c) => withStmt (toCM c) (fun _ s => func s) s

/-! ### `@contextmanager` -/

/-- A generator or async generator, in the shape `contextlib` uses it. `close` gets the exception
being handled at the call, which is what an exception raised inside gets as `__context__`. -/
structure GenOps (σ V : Type) where
  next : St σ → St σ × Res V
  throw : St σ → ExcId → St σ × Res V
  close : St σ → Option ExcId → St σ × Res Unit
  /-- `sys.exception()` at the call of `__exit__` -/
  handled : St σ → Option ExcId

/-- What differs between `_GeneratorContextManager` and `_AsyncGeneratorContextManager`. -/
structure Cfg where
  /-- `StopIteration`, `StopAsyncIteration` -/
  stop : String
  /-- Lib/contextlib.py:198, :271 -/
  afterThrow : String
  /-- The classes tested at Lib/contextlib.py:180, :253 -/
  wrapped : List String

def syncCfg : Cfg :=
  { stop := "StopIteration", afterThrow := "generator didn't stop after throw()",
    wrapped := ["StopIteration"] }

def asyncCfg : Cfg :=
  { stop := "StopAsyncIteration", afterThrow := "generator didn't stop after athrow()",
    wrapped := ["StopIteration", "StopAsyncIteration"] }

/-- `_GeneratorContextManagerBase`, Lib/contextlib.py:105-126. `live` says `func`, `args` and `kwds`
are still there. `gen` is kept in `St.g`. -/
structure GCM where
  live : Bool
  deriving Repr, DecidableEq

/-- `_GeneratorContextManagerBase.__init__`, Lib/contextlib.py:108-115: `func(*args, **kwds)` has
run when `make` returns. `doc` is `getattr(func, "__doc__", None)`; `classDoc` is
`type(self).__doc__`. The result is the object's `__doc__` beside the state. -/
def gcmDoc (doc classDoc : Option String) : Option String :=
  match doc with
  | some d => some d
  | none => classDoc

/-- `_GeneratorContextManagerBase._recreate_cm`, Lib/contextlib.py:122-126:
`self.__class__(self.func, self.args, self.kwds)`, an `AttributeError` once `__enter__` deleted the
attributes. `fresh` is the state of a new generator from `func`. -/
def gcmRecreate (className : String) (self : GCM) (fresh : St σ → St σ × Res Unit) (s : St σ) :
    St σ × Res GCM :=
  if self.live then
    match fresh s with
    | (s, .error e) => (s, .error e)
    | (s, .ok ()) => (s, .ok { live := true })
  else
    let (s, e) := s.raiseNew clsAttr s!"'{className}' object has no attribute 'func'"
    (s, .error e)

/-- `_GeneratorContextManager.__enter__`, Lib/contextlib.py:136-143, and
`_AsyncGeneratorContextManager.__aenter__`, :209-216. -/
def gcmEnter (cfg : Cfg) (ops : GenOps σ V) (className : String) (self : GCM) (s : St σ) :
    GCM × St σ × Res V :=
  if !self.live then
    let (s, e) := s.raiseNew clsAttr s!"'{className}' object has no attribute 'args'"
    (self, s, .error e)
  else
    let self : GCM := { live := false }
    match ops.next s with
    | (s, .ok v) => (self, s, .ok v)
    | (s, .error exc) =>
      if s.h.isInst exc cfg.stop then
        let (s, e) := s.raiseNew clsRuntime "generator didn't yield" (some exc)
        (self, s, .error e)
      else (self, s, .error exc)

/-- `try: raise RuntimeError(msg) finally: self.gen.close()`, Lib/contextlib.py:152-155, :197-200;
async :225-228, :270-273. An exception from `close` replaces the `RuntimeError`, which it has as
`__context__`. -/
def raiseThenClose (ops : GenOps σ V) (s : St σ) (msg : String) : St σ × Res Bool :=
  let (s, rt) := s.raiseNew clsRuntime msg (ops.handled s)
  match ops.close s (some rt) with
  | (s, .ok ()) => (s, .error rt)
  | (s, .error e) => (s, .error e)

/-- `value = typ()`, Lib/contextlib.py:160: `typ` is called, which can raise. -/
abbrev Instantiate (σ : Type) := St σ → Cls → St σ × Res ExcId

/-- `_GeneratorContextManager.__exit__`, Lib/contextlib.py:145-200, and
`_AsyncGeneratorContextManager.__aexit__`, :218-273. `typ = none` is `typ is None`. -/
def gcmExit (cfg : Cfg) (ops : GenOps σ V) (inst : Instantiate σ) (s : St σ)
    (typ : Option Cls) (value : Option ExcId) (tb : Option Nat) : St σ × Res Bool :=
  match typ with
  | none =>
    match ops.next s with
    | (s, .error exc) =>
      if s.h.isInst exc cfg.stop then (s, .ok false) else (s, .error exc)
    | (s, .ok _) => raiseThenClose ops s "generator didn't stop"
  | some t =>
    let made : St σ × Res ExcId := match value with
      | some v => (s, .ok v)
      | none => inst s t
    match made with
    | (s, .error e) => (s, .error e)
    | (s, .ok value) =>
      match ops.throw s value with
      | (s, .ok _) => raiseThenClose ops s cfg.afterThrow
      | (s, .error exc) =>
        if s.h.isInst exc cfg.stop then (s, .ok (decide (exc ≠ value)))
        else if s.h.isInst exc "RuntimeError" then
          if exc = value then ({ s with h := s.h.setTb exc tb }, .ok false)
          else if s.h.isInstAny value cfg.wrapped ∧ (s.h.get exc).cause = some value then
            ({ s with h := s.h.setTb value tb }, .ok false)
          else (s, .error exc)
        else if exc ≠ value then (s, .error exc)
        else ({ s with h := s.h.setTb exc tb }, .ok false)

/-- What leaving an `async def` does to a `StopIteration`: the coroutine's frame turns it into
`RuntimeError("coroutine raised StopIteration")`, `gen_send_ex2`, Objects/genobject.c. -/
def coBoundary {α : Type} (s : St σ) (r : Res α) : St σ × Res α :=
  match r with
  | .ok v => (s, .ok v)
  | .error e =>
    if s.h.isInst e "StopIteration" then
      let (h, r) := s.h.alloc
        { cls := clsRuntime, msg := "coroutine raised StopIteration", context := some e,
          cause := some e }
      ({ s with h := h }, .error r)
    else (s, .error e)

/-- `_AsyncGeneratorContextManager.__aexit__`, Lib/contextlib.py:218-273: `gcmExit` inside an
`async def`. -/
def agcmExit (ops : GenOps σ V) (inst : Instantiate σ) (s : St σ)
    (typ : Option Cls) (value : Option ExcId) (tb : Option Nat) : St σ × Res Bool :=
  let (s, r) := gcmExit asyncCfg ops inst s typ value tb
  coBoundary s r

/-- `_AsyncGeneratorContextManager.__aenter__`, Lib/contextlib.py:209-216: `gcmEnter` inside an
`async def`. -/
def agcmEnter (ops : GenOps σ V) (self : GCM) (s : St σ) : GCM × St σ × Res V :=
  let (g, s, r) := gcmEnter asyncCfg ops "_AsyncGeneratorContextManager" self s
  let (s, r) := coBoundary s r
  (g, s, r)

/-- `contextmanager(func)(*args, **kwds)`, Lib/contextlib.py:276-306, and `asynccontextmanager`,
:309-339: `helper` returns a `_GeneratorContextManager` whose state is ready. As a context manager,
it is `gcmEnter` and `gcmExit` on the shared state. -/
def contextmanager : GCM := { live := true }

/-! ### `closing`, `aclosing`, `nullcontext`, `_RedirectStream`, `chdir` -/

/-- `closing.__enter__`, Lib/contextlib.py:361-362, `aclosing.__aenter__`, :387-388. -/
def closingEnter {T : Type} (thing : T) : T := thing

/-- `closing.__exit__`, Lib/contextlib.py:363-364, `aclosing.__aexit__`, :389-390: the result of
`close()` is dropped, and the method returns `None`, so an exception is never suppressed. -/
def closingExit (close : St σ → St σ × Res Unit) (s : St σ) : St σ × Res Bool :=
  match close s with
  | (s, .error e) => (s, .error e)
  | (s, .ok ()) => (s, .ok false)

/-- `nullcontext.__init__`, Lib/contextlib.py:786-787, `__enter__`, :789-790, `__aenter__`, :795-796:
the object is its `enter_result`. -/
def nullEnter {T : Type} (enterResult : T) : T := enterResult

/-- `nullcontext.__exit__`, Lib/contextlib.py:792-793, `__aexit__`, :798-799. -/
def nullExit (_excInfo : Option ExcId) : Bool := false

/-- `_RedirectStream`, Lib/contextlib.py:393-408, against the module attribute `cur`. -/
structure Redirect (S : Type) where
  newTarget : S
  oldTargets : List S
  deriving Repr, DecidableEq

/-- `_RedirectStream.__init__`, Lib/contextlib.py:397-400. -/
def Redirect.init {S : Type} (t : S) : Redirect S := { newTarget := t, oldTargets := [] }

/-- `_RedirectStream.__enter__`, Lib/contextlib.py:402-405: state, new `sys.stream`, result. -/
def Redirect.enter {S : Type} (r : Redirect S) (cur : S) : Redirect S × S × S :=
  ({ r with oldTargets := r.oldTargets ++ [cur] }, r.newTarget, r.newTarget)

/-- `list.pop` on an empty list. -/
def popEmpty : String := "pop from empty list"

/-- `_RedirectStream.__exit__`, Lib/contextlib.py:407-408. `none` is the `IndexError` of popping an
empty list. -/
def Redirect.exit {S : Type} (r : Redirect S) : Option (Redirect S × S) :=
  match r.oldTargets.getLast? with
  | none => none
  | some o => some ({ r with oldTargets := r.oldTargets.dropLast }, o)

/-- `chdir`, Lib/contextlib.py:802-814, against an abstract file system `F`. -/
structure Chdir (P : Type) where
  path : P
  oldCwd : List P
  deriving Repr, DecidableEq

/-- `chdir.__init__`, Lib/contextlib.py:805-807. -/
def Chdir.init {P : Type} (p : P) : Chdir P := { path := p, oldCwd := [] }

/-- `chdir.__enter__`, Lib/contextlib.py:809-811. `osChdir p cwd` is the new cwd, or the failure. The
old directory is on the stack before `os.chdir` can fail. -/
def Chdir.enter {P E : Type} (osChdir : P → P → Except E P) (c : Chdir P) (cwd : P) :
    Chdir P × P × Except E Unit :=
  let c := { c with oldCwd := c.oldCwd ++ [cwd] }
  match osChdir c.path cwd with
  | .error e => (c, cwd, .error e)
  | .ok cwd => (c, cwd, .ok ())

/-- `chdir.__exit__`, Lib/contextlib.py:813-814. `none` is `IndexError`. -/
def Chdir.exit {P E : Type} (osChdir : P → P → Except E P) (c : Chdir P) (cwd : P) :
    Option (Chdir P × P × Except E Unit) :=
  match c.oldCwd.getLast? with
  | none => none
  | some o =>
    let c := { c with oldCwd := c.oldCwd.dropLast }
    match osChdir o cwd with
    | .error e => some (c, cwd, .error e)
    | .ok cwd => some (c, cwd, .ok ())

/-! ### `suppress` -/

/-- `exc` matches the tuple of classes in `except`-clause terms. -/
def matches' (h : Heap) (e : ExcId) (cs : List String) : Bool := h.isInstAny e cs

/-- The class `BaseExceptionGroup.derive` produces: Objects/exceptions.c:1140-1152 calls
`BaseExceptionGroup(msg, excs)`, and `BaseExceptionGroup_new` turns that into `ExceptionGroup` when
every member is an `Exception`. -/
def deriveCls (h : Heap) (excs : List ExcId) : Cls :=
  if excs.all (fun e => h.isInst e "Exception") then clsEG else clsBEG

/-- `exceptiongroup_subset`, Objects/exceptions.c:1155-1234: a new group of `excs` with the
metadata of `orig`; `none` for an empty `excs`. The class comes from `derive`. -/
def subset (h : Heap) (orig : ExcId) (excs : List ExcId) : Heap × Option ExcId :=
  if excs.isEmpty then (h, none)
  else
    let o := h.get orig
    let (h, e) := h.alloc
      { cls := deriveCls h excs, msg := o.msg, context := o.context, cause := o.cause, tb := o.tb,
        children := some excs }
    (h, some e)

/-- `exceptiongroup_split_recursive`, Objects/exceptions.c:1326-1434. `cs` is the matcher. The fold
is the `for` loop over `eg->excs`, :1378-1411; the result is `(match, rest)`. -/
def splitRec (cs : List String) : Nat → Heap → ExcId → Heap × Option ExcId × Option ExcId
  | 0, h, _ => (h, none, none)
  | fuel + 1, h, exc =>
    if matches' h exc cs then (h, some exc, none)
    else
      match (h.get exc).children with
      | none => (h, none, some exc)
      | some excs =>
        let (h, ms, rs) := excs.foldl
          (fun (st : Heap × List ExcId × List ExcId) e =>
            let x := splitRec cs fuel st.1 e
            (x.1, st.2.1 ++ x.2.1.toList, st.2.2 ++ x.2.2.toList))
          (h, [], [])
        let (h, m) := subset h exc ms
        let (h, r) := subset h exc rs
        (h, m, r)

/-- `BaseExceptionGroup.split`, Objects/exceptions.c:1444-1469, with a tuple of classes. -/
def split (cs : List String) (h : Heap) (e : ExcId) : Heap × Option ExcId × Option ExcId :=
  splitRec cs (2 * h.length + 2) h e

/-- `suppress.__enter__`, Lib/contextlib.py:447-448, returns `None`; `__init__`, :444-445, stores
the classes. -/
def suppressEnter : Unit := ()

/-- `suppress.__exit__`, Lib/contextlib.py:450-469, for `self._exceptions = cs`, classes.
`handled` is the exception being handled at the call, which `raise rest` chains to. `.ok none` is
the bare `return` of `exctype is None`. -/
def suppressExit (cs : List String) (s : St σ) (handled : Option ExcId) (excinst : Option ExcId) :
    St σ × Res (Option Bool) :=
  match excinst with
  | none => (s, .ok none)
  | some e =>
    if s.h.isInstAny e cs then (s, .ok (some true))
    else if s.h.isInst e "BaseExceptionGroup" then
      let (h, _, rest) := split cs s.h e
      let s := { s with h := h }
      match rest with
      | none => (s, .ok (some true))
      | some r => ({ s with h := s.h.raiseCtx r handled }, .error r)
    else (s, .ok (some false))

/-! ### `ExitStack` and `AsyncExitStack` -/

/-- An entry of `_exit_callbacks`: what the wrappers of `_BaseExitStack` build. -/
inductive Cb (F O A : Type) where
  /-- `exit` itself, pushed by `push` -/
  | raw (f : F)
  /-- `_create_exit_wrapper`, Lib/contextlib.py:475-477, and `_create_async_exit_wrapper`, :644-646:
  `MethodType(cm_exit, cm)` -/
  | bound (m : F) (cm : O)
  /-- `_create_cb_wrapper`, Lib/contextlib.py:479-483, and `_create_async_cb_wrapper`, :648-652: the
  callback with its arguments, whose result is dropped -/
  | wrapped (f : F) (args : A)
  deriving Repr, DecidableEq

/-- The `_exit_callbacks` deque: `(is_sync, callback)` pairs, the last pushed first. -/
abbrev Stack (F O A : Type) := List (Bool × Cb F O A)

variable {F O A : Type}

/-- What a stack's state is made of. The stack is part of the state because a callback can push. -/
abbrev Xs (σ F O A : Type) := St σ × Stack F O A

/-- Calling what `_exit_callbacks` holds. Results are reduced to the truth value. -/
structure Calls (σ F O A : Type) where
  /-- `f(exc_type, exc, tb)` -/
  raw : F → Xs σ F O A → Option ExcId → Xs σ F O A × Res Bool
  /-- `m(cm, exc_type, exc, tb)` -/
  bound : F → O → Xs σ F O A → Option ExcId → Xs σ F O A × Res Bool
  /-- `f(*args, **kwds)` -/
  wrapped : F → A → Xs σ F O A → Xs σ F O A × Res Unit

/-- Calling an entry of `_exit_callbacks`; `_exit_wrapper` drops the callback's result. -/
def Cb.call (c : Calls σ F O A) (cb : Cb F O A) (x : Xs σ F O A) (d : Option ExcId) :
    Xs σ F O A × Res Bool :=
  match cb with
  | .raw f => c.raw f x d
  | .bound m cm => c.bound m cm x d
  | .wrapped f args =>
    match c.wrapped f args x with
    | (x, .error e) => (x, .error e)
    | (x, .ok ()) => (x, .ok false)

/-- `_BaseExitStack.__init__`, Lib/contextlib.py:485-486. -/
def Stack.init : Stack F O A := []

/-- `_BaseExitStack.pop_all`, Lib/contextlib.py:488-493: the new stack, then what `self` keeps. -/
def popAll (st : Stack F O A) : Stack F O A × Stack F O A := (st, [])

/-- `_BaseExitStack._push_exit_callback`, Lib/contextlib.py:552-553. -/
def pushExitCallback (st : Stack F O A) (cb : Cb F O A) (isSync : Bool := true) : Stack F O A :=
  (isSync, cb) :: st

/-- `_BaseExitStack._push_cm_exit`, Lib/contextlib.py:547-550. -/
def pushCmExit (st : Stack F O A) (cm : O) (cmExit : F) : Stack F O A :=
  pushExitCallback st (.bound cmExit cm) true

/-- `AsyncExitStack._push_async_cm_exit`, Lib/contextlib.py:707-711. -/
def pushAsyncCmExit (st : Stack F O A) (cm : O) (cmExit : F) : Stack F O A :=
  pushExitCallback st (.bound cmExit cm) false

/-- `type(exit).__exit__` when it exists. -/
abbrev ExitLookup (F O : Type) := O → Option F

/-- `_BaseExitStack.push`, Lib/contextlib.py:495-513: `asF exit` is `exit` as a plain callable. -/
def push (lookup : ExitLookup F O) (asF : O → F) (st : Stack F O A) (exit : O) : Stack F O A :=
  match lookup exit with
  | none => pushExitCallback st (.raw (asF exit))
  | some m => pushCmExit st exit m

/-- `AsyncExitStack.push_async_exit`, Lib/contextlib.py:672-688. -/
def pushAsyncExit (lookup : ExitLookup F O) (asF : O → F) (st : Stack F O A) (exit : O) :
    Stack F O A :=
  match lookup exit with
  | none => pushExitCallback st (.raw (asF exit)) false
  | some m => pushAsyncCmExit st exit m

/-- `_BaseExitStack.callback`, Lib/contextlib.py:534-545. -/
def callback (st : Stack F O A) (f : F) (args : A) : Stack F O A :=
  pushExitCallback st (.wrapped f args) true

/-- `AsyncExitStack.push_async_callback`, Lib/contextlib.py:690-701. -/
def pushAsyncCallback (st : Stack F O A) (f : F) (args : A) : Stack F O A :=
  pushExitCallback st (.wrapped f args) false

/-- `_BaseExitStack.enter_context`, Lib/contextlib.py:515-532, and
`AsyncExitStack.enter_async_context`, :654-670. `cm` has `__enter__` and `__exit__` when `methods` is
`some`. `msg` is the formatted `TypeError` of the source, `attrMsg` the message of the
`AttributeError` it replaces, which stays as `__context__` behind `from None`. -/
def enterContext (methods : O → Option ((Xs σ F O A → Xs σ F O A × Res V) × F))
    (msg attrMsg : String) (isSync : Bool) (x : Xs σ F O A) (cm : O) : Xs σ F O A × Res V :=
  match methods cm with
  | none =>
    let (s, a) := x.1.raiseNew clsAttr attrMsg
    let (s, e) := s.raiseNew clsType msg (some a)
    ((s, x.2), .error e)
  | some (enter, exit) =>
    match enter x with
    | (x, .error e) => (x, .error e)
    | (x, .ok r) =>
      let st := pushExitCallback x.2 (.bound exit cm) isSync
      ((x.1, st), .ok r)

/-- `_fix_exception_context`, Lib/contextlib.py:578-590 and :723-735. `none` means the fuel ran out:
the source loop is `while 1`, and a cycle in `__context__` that meets neither test never ends. -/
def fixExceptionContext (frameExc old : Option ExcId) : Nat → Heap → ExcId → Option Heap
  | 0, _, _ => none
  | fuel + 1, h, newExc =>
    let excContext := (h.get newExc).context
    match excContext with
    | none => some h
    | some c =>
      if some c = old then some h
      else if some c = frameExc then some (h.setContext newExc old)
      else fixExceptionContext frameExc old fuel h c

/-- The loop of `ExitStack.__exit__`, Lib/contextlib.py:596-612: `exc`, `suppressed_exc`,
`pending_raise` are the loop state. -/
def exitLoop (c : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat) :
    Nat → Xs σ F O A → Option ExcId → Bool → Bool → Py (Xs σ F O A × Option ExcId × Bool × Bool)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, x, exc, suppressed, pending =>
    match x.2 with
    | [] => .ok (x, exc, suppressed, pending)
    | (isSync, cb) :: rest =>
      if !isSync then .error (.assertionError "") else
      match cb.call c (x.1, rest) exc with
      | (x, .ok true) => exitLoop c frameExc fixFuel fuel x none true false
      | (x, .ok false) => exitLoop c frameExc fixFuel fuel x exc suppressed pending
      | (x, .error newExc) =>
        match fixExceptionContext frameExc exc fixFuel x.1.h newExc with
        | none => .error .modelFuel
        | some h =>
          exitLoop c frameExc fixFuel fuel ({ x.1 with h := h }, x.2) (some newExc) suppressed true

/-- The end of `__exit__`, Lib/contextlib.py:614-622 and :763-771: `fixed_ctx = exc.__context__;
raise exc`, then `exc.__context__ = fixed_ctx`. The `raise` can still cut a link in the chain of
`frameExc`. -/
def raiseKeepingContext (x : Xs σ F O A) (e : ExcId) (frameExc : Option ExcId) : Xs σ F O A :=
  let fixed := (x.1.h.get e).context
  ({ x.1 with h := (x.1.h.raiseCtx e frameExc).setContext e fixed }, x.2)

/-- `ExitStack.__exit__`, Lib/contextlib.py:571-623. `exc` is `exc_details[1]`, `frameExc` is
`sys.exception()`. -/
def exit (c : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (exc frameExc : Option ExcId) :
    Py (Xs σ F O A × Res Bool) := do
  let receivedExc := exc.isSome
  let (x, exc, suppressedExc, pendingRaise) ← exitLoop c frameExc fixFuel fuel x exc false false
  if pendingRaise then
    match exc with
    | some e => return (raiseKeepingContext x e frameExc, .error e)
    | none => .error .modelFuel
  else return (x, .ok (receivedExc && suppressedExc))

/-- `ExitStack.close`, Lib/contextlib.py:625-627, and `AsyncExitStack.aclose`, :703-705. -/
def close (c : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (frameExc : Option ExcId) :
    Py (Xs σ F O A × Res Unit) := do
  let (x, r) ← exit c fuel fixFuel x none frameExc
  match r with
  | .ok _ => return (x, .ok ())
  | .error e => return (x, .error e)

/-- `ExitStack.__enter__`, Lib/contextlib.py:568-569, and `AsyncExitStack.__aenter__`, :713-714. -/
def stackEnter {T : Type} (self : T) : T := self

/-- The loop of `AsyncExitStack.__aexit__`, Lib/contextlib.py:741-761. The `is_sync` branch of
:748-751 picks `cb(...)` or `await cb(...)`, which have the same effect here because the async
callbacks are given by `ac`. -/
def aexitLoop (c ac : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat) :
    Nat → Xs σ F O A → Option ExcId → Bool → Bool → Py (Xs σ F O A × Option ExcId × Bool × Bool)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, x, exc, suppressed, pending =>
    match x.2 with
    | [] => .ok (x, exc, suppressed, pending)
    | (isSync, cb) :: rest =>
      match cb.call (if isSync then c else ac) (x.1, rest) exc with
      | (x, .ok true) => aexitLoop c ac frameExc fixFuel fuel x none true false
      | (x, .ok false) => aexitLoop c ac frameExc fixFuel fuel x exc suppressed pending
      | (x, .error newExc) =>
        match fixExceptionContext frameExc exc fixFuel x.1.h newExc with
        | none => .error .modelFuel
        | some h =>
          aexitLoop c ac frameExc fixFuel fuel ({ x.1 with h := h }, x.2) (some newExc) suppressed true

/-- `AsyncExitStack.__aexit__`, Lib/contextlib.py:716-772. -/
def aexit (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (exc frameExc : Option ExcId) :
    Py (Xs σ F O A × Res Bool) := do
  let receivedExc := exc.isSome
  let (x, exc, suppressedExc, pendingRaise) ← aexitLoop c ac frameExc fixFuel fuel x exc false false
  if pendingRaise then
    match exc with
    | some e =>
      let x := raiseKeepingContext x e frameExc
      let (s, r) := coBoundary x.1 (.error e : Res Bool)
      return ((s, x.2), r)
    | none => .error .modelFuel
  else return (x, .ok (receivedExc && suppressedExc))

end PyLean.CoreLibs.Misc.Contextlib
