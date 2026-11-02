import PyLean.CoreLibs.Misc.Contextlib.Exc

/-!
`Lib/contextlib.py`, CPython 3.14.7.

A generator is whatever implements `GenOps`, a state machine over `St σ`: `next`, `throw` and
`close` return the value yielded or the exception object raised. `_GeneratorContextManager` and its
async twin are one definition over `Cfg`, because they differ only in the class of the stop
exception, in one message, and in the tuple tested at Lib/contextlib.py:242 and :315. An `await` that
does not suspend has no observable effect, so the async methods are the sync algorithm with the
async object's operations, and what differs is in `Cfg` or written out (`aexit`).

An exit callback is abstract too: `Cb F O` is what `_exit_callbacks` holds and `Calls.call` what
calling `F` does, which lets a callback mutate the heap, the world and the stack itself.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

variable {σ V : Type}

/-! ### Abstract base classes -/

/-- `AbstractContextManager.__enter__`, Lib/contextlib.py:31-33, and
`AbstractAsyncContextManager.__aenter__`, :55-57. -/
def absEnter {O : Type} (self : O) : O := self

/-- `AbstractContextManager.__exit__`, Lib/contextlib.py:35-38, and
`AbstractAsyncContextManager.__aexit__`, :59-62: `None`, so the exception propagates. -/
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
AbstractContextManager`. `AbstractContextManager.__subclasshook__`, Lib/contextlib.py:40-44, with
`__enter__`, `__exit__`; `AbstractAsyncContextManager.__subclasshook__`, :64-69, with `__aenter__`,
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

/-- `ContextDecorator._recreate_cm`, Lib/contextlib.py:75-85, and
`AsyncContextDecorator._recreate_cm`, :124-127. -/
def ContextDecorator.recreateCm {C : Type} (self : C) : C := self

/-- `inner` of `ContextDecorator.__call__`, Lib/contextlib.py:113-116, and of `AsyncContextDecorator.__call__`, :160-163:
the branch for a plain function; `recreate` builds the context manager for this call. The branches for generator,
coroutine and async generator functions, new in 3.15, are not modelled. -/
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
  /-- Lib/contextlib.py:260, :333 -/
  afterThrow : String
  /-- The classes tested at Lib/contextlib.py:242, :315 -/
  wrapped : List String

def syncCfg : Cfg :=
  { stop := "StopIteration", afterThrow := "generator didn't stop after throw()",
    wrapped := ["StopIteration"] }

def asyncCfg : Cfg :=
  { stop := "StopAsyncIteration", afterThrow := "generator didn't stop after athrow()",
    wrapped := ["StopIteration", "StopAsyncIteration"] }

/-- `_GeneratorContextManagerBase`, Lib/contextlib.py:167-188. `live` says `func`, `args` and `kwds`
are still there. `gen` is kept in `St.g`. -/
structure GCM where
  live : Bool
  deriving Repr, DecidableEq

/-- `_GeneratorContextManagerBase.__init__`, Lib/contextlib.py:170-177: `func(*args, **kwds)` has
run when `make` returns. `doc` is `getattr(func, "__doc__", None)`; `classDoc` is
`type(self).__doc__`. The result is the object's `__doc__` beside the state. -/
def gcmDoc (doc classDoc : Option String) : Option String :=
  match doc with
  | some d => some d
  | none => classDoc

/-- `_GeneratorContextManagerBase._recreate_cm`, Lib/contextlib.py:184-188:
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

/-- `_GeneratorContextManager.__enter__`, Lib/contextlib.py:198-205, and
`_AsyncGeneratorContextManager.__aenter__`, :271-278. -/
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

/-- `try: raise RuntimeError(msg) finally: self.gen.close()`, Lib/contextlib.py:214-217, :259-262;
async :287-290, :332-335. An exception from `close` replaces the `RuntimeError`, which it has as
`__context__`. -/
def raiseThenClose (ops : GenOps σ V) (s : St σ) (msg : String) : St σ × Res Bool :=
  let (s, rt) := s.raiseNew clsRuntime msg (ops.handled s)
  match ops.close s (some rt) with
  | (s, .ok ()) => (s, .error rt)
  | (s, .error e) => (s, .error e)

/-- `value = typ()`, Lib/contextlib.py:222: `typ` is called, which can raise. -/
abbrev Instantiate (σ : Type) := St σ → Cls → St σ × Res ExcId

/-- `_GeneratorContextManager.__exit__`, Lib/contextlib.py:207-262, and
`_AsyncGeneratorContextManager.__aexit__`, :280-335. `typ = none` is `typ is None`. -/
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

/-- `_AsyncGeneratorContextManager.__aexit__`, Lib/contextlib.py:280-335: `gcmExit` inside an
`async def`. -/
def agcmExit (ops : GenOps σ V) (inst : Instantiate σ) (s : St σ)
    (typ : Option Cls) (value : Option ExcId) (tb : Option Nat) : St σ × Res Bool :=
  let (s, r) := gcmExit asyncCfg ops inst s typ value tb
  coBoundary s r

/-- `_AsyncGeneratorContextManager.__aenter__`, Lib/contextlib.py:271-278: `gcmEnter` inside an
`async def`. -/
def agcmEnter (ops : GenOps σ V) (self : GCM) (s : St σ) : GCM × St σ × Res V :=
  let (g, s, r) := gcmEnter asyncCfg ops "_AsyncGeneratorContextManager" self s
  let (s, r) := coBoundary s r
  (g, s, r)

/-- `contextmanager(func)(*args, **kwds)`, Lib/contextlib.py:338-368, and `asynccontextmanager`,
:371-401: `helper` returns a `_GeneratorContextManager` whose state is ready. As a context manager,
it is `gcmEnter` and `gcmExit` on the shared state. -/
def contextmanager : GCM := { live := true }

/-! ### `closing`, `aclosing`, `nullcontext`, `_RedirectStream`, `chdir` -/

/-- `closing.__enter__`, Lib/contextlib.py:423-424, `aclosing.__aenter__`, :449-450. -/
def closingEnter {T : Type} (thing : T) : T := thing

/-- `closing.__exit__`, Lib/contextlib.py:425-426, `aclosing.__aexit__`, :451-452: the result of
`close()` is dropped, and the method returns `None`, so an exception is never suppressed. -/
def closingExit (close : St σ → St σ × Res Unit) (s : St σ) : St σ × Res Bool :=
  match close s with
  | (s, .error e) => (s, .error e)
  | (s, .ok ()) => (s, .ok false)

/-- `nullcontext.__init__`, Lib/contextlib.py:831-832, `__enter__`, :834-835, `__aenter__`, :840-841:
the object is its `enter_result`. -/
def nullEnter {T : Type} (enterResult : T) : T := enterResult

/-- `nullcontext.__exit__`, Lib/contextlib.py:837-838, `__aexit__`, :843-844. -/
def nullExit (_excInfo : Option ExcId) : Bool := false

/-- `_RedirectStream`, Lib/contextlib.py:455-470, against the module attribute `cur`. -/
structure Redirect (S : Type) where
  newTarget : S
  oldTargets : List S
  deriving Repr, DecidableEq

/-- `_RedirectStream.__init__`, Lib/contextlib.py:459-462. -/
def Redirect.init {S : Type} (t : S) : Redirect S := { newTarget := t, oldTargets := [] }

/-- `_RedirectStream.__enter__`, Lib/contextlib.py:464-467: state, new `sys.stream`, result. -/
def Redirect.enter {S : Type} (r : Redirect S) (cur : S) : Redirect S × S × S :=
  ({ r with oldTargets := r.oldTargets ++ [cur] }, r.newTarget, r.newTarget)

/-- `list.pop` on an empty list. -/
def popEmpty : String := "pop from empty list"

/-- `_RedirectStream.__exit__`, Lib/contextlib.py:469-470. `none` is the `IndexError` of popping an
empty list. -/
def Redirect.exit {S : Type} (r : Redirect S) : Option (Redirect S × S) :=
  match r.oldTargets.getLast? with
  | none => none
  | some o => some ({ r with oldTargets := r.oldTargets.dropLast }, o)

/-- `chdir`, Lib/contextlib.py:847-859, against an abstract file system `F`. -/
structure Chdir (P : Type) where
  path : P
  oldCwd : List P
  deriving Repr, DecidableEq

/-- `chdir.__init__`, Lib/contextlib.py:850-852. -/
def Chdir.init {P : Type} (p : P) : Chdir P := { path := p, oldCwd := [] }

/-- `chdir.__enter__`, Lib/contextlib.py:854-856. `osChdir p cwd` is the new cwd, or the failure. The
old directory is on the stack before `os.chdir` can fail. -/
def Chdir.enter {P E : Type} (osChdir : P → P → Except E P) (c : Chdir P) (cwd : P) :
    Chdir P × P × Except E Unit :=
  let c := { c with oldCwd := c.oldCwd ++ [cwd] }
  match osChdir c.path cwd with
  | .error e => (c, cwd, .error e)
  | .ok cwd => (c, cwd, .ok ())

/-- `chdir.__exit__`, Lib/contextlib.py:858-859. `none` is `IndexError`. -/
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

/-- The class `BaseExceptionGroup.derive` produces: Objects/exceptions.c:1136-1148 calls
`BaseExceptionGroup(msg, excs)`, and `BaseExceptionGroup_new` turns that into `ExceptionGroup` when
every member is an `Exception`. -/
def deriveCls (h : Heap) (excs : List ExcId) : Cls :=
  if excs.all (fun e => h.isInst e "Exception") then clsEG else clsBEG

/-- `exceptiongroup_subset`, Objects/exceptions.c:1151-1230: a new group of `excs` with the
metadata of `orig`; `none` for an empty `excs`. The class comes from `derive`. -/
def subset (h : Heap) (orig : ExcId) (excs : List ExcId) : Heap × Option ExcId :=
  if excs.isEmpty then (h, none)
  else
    let o := h.get orig
    let (h, e) := h.alloc
      { cls := deriveCls h excs, msg := o.msg, context := o.context, cause := o.cause, tb := o.tb,
        children := some excs }
    (h, some e)

/-- `exceptiongroup_split_recursive`, Objects/exceptions.c:1322-1430. `cs` is the matcher. The fold
is the `for` loop over `eg->excs`, :1374-1407; the result is `(match, rest)`. -/
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

/-- `BaseExceptionGroup.split`, Objects/exceptions.c:1440-1463, with a tuple of classes. -/
def split (cs : List String) (h : Heap) (e : ExcId) : Heap × Option ExcId × Option ExcId :=
  splitRec cs (2 * h.length + 2) h e

/-- `suppress.__enter__`, Lib/contextlib.py:509-510, returns `None`; `__init__`, :506-507, stores
the classes. -/
def suppressEnter : Unit := ()

/-- `suppress.__exit__`, Lib/contextlib.py:512-531, for `self._exceptions = cs`, classes.
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
  /-- What `_lookup_special`, Lib/contextlib.py:534-542, gives for a function on the type: the method bound to `cm`. A
  `staticmethod`, or an object with no `__get__`, comes back as itself, and that is `raw`. -/
  | bound (m : F) (cm : O)
  /-- `_create_cb_wrapper`, Lib/contextlib.py:551-555, and `_create_async_cb_wrapper`, :703-707: the
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

/-- `_BaseExitStack.__init__`, Lib/contextlib.py:557-558. -/
def Stack.init : Stack F O A := []

/-- `_BaseExitStack.pop_all`, Lib/contextlib.py:560-565: the new stack, then what `self` keeps. -/
def popAll (st : Stack F O A) : Stack F O A × Stack F O A := (st, [])

/-- `_BaseExitStack._push_exit_callback`, Lib/contextlib.py:611-612. -/
def pushExitCallback (st : Stack F O A) (cb : Cb F O A) (isSync : Bool := true) : Stack F O A :=
  (isSync, cb) :: st

/-- What `getattr_static(cls, name)` found on the type, sorted by the branches of `_descriptor_get`, Lib/inspect.py:2420-2426.
`get` holds the outcome of calling `__get__`, which can raise. -/
inductive Descr (T : Type) where
  | isClass (v : T)
  | noGet (v : T)
  | get (r : Res T)

/-- `_descriptor_get(descr, obj)`, Lib/inspect.py:2420-2426. -/
def descriptorGet : Descr T → Res T
  | .isClass v => .ok v
  | .noGet v => .ok v
  | .get r => r

/-- `_lookup_special(obj, name, default)`, Lib/contextlib.py:534-542; `none` is the `AttributeError` of `getattr_static`.
An exception from `__get__` is not caught. -/
def lookupSpecial (d : Option (Descr T)) (default : T) : Res T :=
  match d with
  | none => .ok default
  | some d => descriptorGet d

/-- `_lookup_special(cm, name, _sentinel)`, Lib/contextlib.py:584, 589 with the sentinel as `none`. -/
def lookupSentinel (d : Option (Descr T)) : Res (Option T) :=
  match d with
  | none => .ok none
  | some d =>
    match descriptorGet d with
    | .error e => .error e
    | .ok v => .ok (some v)

/-- `getattr_static(type(obj), '__exit__')`, for one object. -/
abbrev ExitLookup (F O A : Type) := O → Option (Descr (Cb F O A))

/-- `_BaseExitStack.push`, Lib/contextlib.py:567-576: `asF exit` is `exit` as a plain callable. -/
def push (lookup : ExitLookup F O A) (asF : O → F) (st : Stack F O A) (exit : O) : Stack F O A × Res Unit :=
  match lookupSpecial (lookup exit) (.raw (asF exit)) with
  | .ok cb => (pushExitCallback st cb, .ok ())
  | .error e => (st, .error e)

/-- `AsyncExitStack.push_async_exit`, Lib/contextlib.py:729-739. -/
def pushAsyncExit (lookup : ExitLookup F O A) (asF : O → F) (st : Stack F O A) (exit : O) :
    Stack F O A × Res Unit :=
  match lookupSpecial (lookup exit) (.raw (asF exit)) with
  | .ok cb => (pushExitCallback st cb false, .ok ())
  | .error e => (st, .error e)

/-- `_BaseExitStack.callback`, Lib/contextlib.py:598-609. -/
def callback (st : Stack F O A) (f : F) (args : A) : Stack F O A :=
  pushExitCallback st (.wrapped f args) true

/-- `AsyncExitStack.push_async_callback`, Lib/contextlib.py:741-752. -/
def pushAsyncCallback (st : Stack F O A) (f : F) (args : A) : Stack F O A :=
  pushExitCallback st (.wrapped f args) false

/-- `_BaseExitStack.enter_context`, Lib/contextlib.py:578-596, and `AsyncExitStack.enter_async_context`, :709-727. Both
lookups run first, `__enter__` before `__exit__`, and a missing one is a `TypeError` with the source's message `msg`. The
enter method runs only after both, and the exit is pushed only if it succeeded. -/
def enterContext (enterOf : O → Option (Descr (Xs σ F O A → Xs σ F O A × Res V))) (exitOf : ExitLookup F O A)
    (msg : String) (isSync : Bool) (x : Xs σ F O A) (cm : O) : Xs σ F O A × Res V :=
  let refuse : Xs σ F O A × Res V :=
    let (s, e) := x.1.raiseNew clsType msg
    ((s, x.2), .error e)
  match lookupSentinel (enterOf cm) with
  | .error e => (x, .error e)
  | .ok none => refuse
  | .ok (some enter) =>
    match lookupSentinel (exitOf cm) with
    | .error e => (x, .error e)
    | .ok none => refuse
    | .ok (some exit) =>
      match enter x with
      | (x, .error e) => (x, .error e)
      | (x, .ok r) =>
        let st := pushExitCallback x.2 exit isSync
        ((x.1, st), .ok r)

/-- `_fix_exception_context`, Lib/contextlib.py:637-649 and :768-780. `none` means the fuel ran out:
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

/-- The loop of `ExitStack.__exit__`, Lib/contextlib.py:655-671: `exc`, `suppressed_exc`,
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

/-- The end of `__exit__`, Lib/contextlib.py:673-681 and :808-816: `fixed_ctx = exc.__context__;
raise exc`, then `exc.__context__ = fixed_ctx`. The `raise` can still cut a link in the chain of
`frameExc`. -/
def raiseKeepingContext (x : Xs σ F O A) (e : ExcId) (frameExc : Option ExcId) : Xs σ F O A :=
  let fixed := (x.1.h.get e).context
  ({ x.1 with h := (x.1.h.raiseCtx e frameExc).setContext e fixed }, x.2)

/-- `ExitStack.__exit__`, Lib/contextlib.py:630-682. `exc` is `exc_details[1]`, `frameExc` is
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

/-- `ExitStack.close`, Lib/contextlib.py:684-686, and `AsyncExitStack.aclose`, :754-756. -/
def close (c : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (frameExc : Option ExcId) :
    Py (Xs σ F O A × Res Unit) := do
  let (x, r) ← exit c fuel fixFuel x none frameExc
  match r with
  | .ok _ => return (x, .ok ())
  | .error e => return (x, .error e)

/-- `ExitStack.__enter__`, Lib/contextlib.py:627-628, and `AsyncExitStack.__aenter__`, :758-759. -/
def stackEnter {T : Type} (self : T) : T := self

/-- The loop of `AsyncExitStack.__aexit__`, Lib/contextlib.py:786-806. The `is_sync` branch of
:793-796 picks `cb(...)` or `await cb(...)`, which have the same effect here because the async
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

/-- `AsyncExitStack.__aexit__`, Lib/contextlib.py:761-817. -/
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
