import PyLean.CoreLibs.Misc.Contextlib.Exc

/-!
`Lib/contextlib.py`, CPython 3.15.2.

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

/-- `getattr(obj, name, None)`: `r` is the lookup, whose `AttributeError` gives the default `None`
(`.ok none`); any other exception propagates. -/
def getattrDefault {α : Type} (s : St σ) (r : Res (Option α)) : Res (Option α) :=
  match r with
  | .error e => if s.h.isInst e "AttributeError" then .ok none else .error e
  | .ok v => .ok v

/-- `_GeneratorContextManagerBase.__init__`, Lib/contextlib.py:170-177. `call` is
`func(*args, **kwds)`, :171, whose generator is kept in `St.g`; `getDoc` is the lookup of
`func.__doc__` at :174, `none` for a `None` value; `classDoc` is `type(self).__doc__`, :176. The
attributes of :172 make the object `live`; the second component is the `__doc__` set at :177. -/
def gcmInit {D : Type} (call : St σ → St σ × Res Unit) (getDoc : St σ → St σ × Res (Option D))
    (classDoc : Option D) (s : St σ) : St σ × Res (GCM × Option D) :=
  match call s with
  | (s, .error e) => (s, .error e)
  | (s, .ok ()) =>
    let (s, d) := getDoc s
    match getattrDefault s d with
    | .error e => (s, .error e)
    | .ok none => (s, .ok ({ live := true }, classDoc))
    | .ok (some d) => (s, .ok ({ live := true }, some d))

/-- `_GeneratorContextManagerBase._recreate_cm`, Lib/contextlib.py:184-188:
`self.__class__(self.func, self.args, self.kwds)`. `init` is the `__init__` of the class with the
stored arguments. Once `__enter__` deleted the attributes, reading `self.func` is an
`AttributeError`, raised while `handled` is being handled. -/
def gcmRecreate {D : Type} (className : String) (self : GCM)
    (init : St σ → St σ × Res (GCM × Option D)) (handled : Option ExcId) (s : St σ) :
    St σ × Res (GCM × Option D) :=
  if self.live then init s
  else
    let (s, e) := s.raiseNew clsAttr s!"'{className}' object has no attribute 'func'" handled
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

/-- What leaving an `async def` does to an exception: the handler that wraps a coroutine's body
calls `INTRINSIC_STOPITERATION_ERROR` (Python/codegen.c:1259), `stopiteration_error`,
Python/intrinsics.c:141-182, which turns a `StopIteration` (a subclass too) into a new
`RuntimeError("coroutine raised StopIteration")` whose `__cause__` and `__context__` are the
`StopIteration` (:176-178); anything else, `StopAsyncIteration` included, passes. -/
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

/-- `helper(*args, **kwds)` of `contextmanager(func)`, Lib/contextlib.py:365-367, and of
`asynccontextmanager(func)`, :398-400: `_GeneratorContextManager(func, args, kwds)`, resp. the async
class, built by `gcmInit` when the decorated function is called. `@wraps(func)` (:365, :398) copies
`func`'s metadata onto `helper`; that is `functools.update_wrapper`, outside this model. -/
def contextmanagerCall {D : Type} (call : St σ → St σ × Res Unit)
    (getDoc : St σ → St σ × Res (Option D)) (classDoc : Option D) (s : St σ) :
    St σ × Res (GCM × Option D) :=
  gcmInit call getDoc classDoc s

/-! ### `closing`, `aclosing`, `nullcontext`, `_RedirectStream`, `chdir` -/

/-- `closing.__enter__`, Lib/contextlib.py:423-424, `aclosing.__aenter__`, :449-450: `self.thing`. -/
def closingEnter {T : Type} (thing : T) : T := thing

/-- `closing.__exit__`, Lib/contextlib.py:425-426: `self.thing.close()`, where `close` is the lookup
and the call, either of which can raise. Its result is dropped and the method returns `None`
(`.ok false`), so an exception is never suppressed. -/
def closingExit (close : St σ → St σ × Res Unit) (s : St σ) : St σ × Res Bool :=
  match close s with
  | (s, .error e) => (s, .error e)
  | (s, .ok ()) => (s, .ok false)

/-- `aclosing.__aexit__`, Lib/contextlib.py:451-452: `await self.thing.aclose()` inside an
`async def`. `aclose` is the lookup, the call and the await. -/
def aclosingExit (aclose : St σ → St σ × Res Unit) (s : St σ) : St σ × Res Bool :=
  let r := closingExit aclose s
  coBoundary r.1 r.2

/-- `nullcontext.__enter__`, Lib/contextlib.py:834-835 (difftest only). -/
def nullEnter {T : Type} (enterResult : T) : T := enterResult

/-- `nullcontext.__exit__`, Lib/contextlib.py:837-838 (difftest only). -/
def nullExit (_excInfo : Option ExcId) : Bool := false

/-- `_RedirectStream`, Lib/contextlib.py:455-470, against the module attribute `cur`. -/
structure Redirect (S : Type) where
  newTarget : S
  oldTargets : List S
  deriving Repr, DecidableEq

/-- `_RedirectStream.__init__`, Lib/contextlib.py:459-462. -/
def Redirect.init {S : Type} (t : S) : Redirect S := { newTarget := t, oldTargets := [] }

/-- `_RedirectStream.__enter__`, Lib/contextlib.py:464-467. `cur` is `getattr(sys, self._stream)`,
which fails when the stream attribute is missing; then nothing is appended and nothing is set. The
result is the state, the new `sys.<stream>`, and the return value. -/
def Redirect.enter {S E : Type} (r : Redirect S) (cur : Except E S) :
    Redirect S × Except E (S × S) :=
  match cur with
  | .error e => (r, .error e)
  | .ok cur => ({ r with oldTargets := r.oldTargets ++ [cur] }, .ok (r.newTarget, r.newTarget))

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

/-- `chdir.__enter__`, Lib/contextlib.py:854-856. `getcwd` is `os.getcwd()`, which fails when the
working directory was removed; then nothing is pushed. `osChdir p cwd` is the new cwd, or the
failure. The old directory is on the stack before `os.chdir` can fail. -/
def Chdir.enter {P E : Type} (osChdir : P → P → Except E P) (c : Chdir P) (getcwd : Except E P)
    (cwd : P) : Chdir P × P × Except E Unit :=
  match getcwd with
  | .error e => (c, cwd, .error e)
  | .ok old =>
    let c := { c with oldCwd := c.oldCwd ++ [old] }
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

/-- The `exctype` argument of `suppress.__exit__`: a class by its concrete MRO, or an object that is
no class, with no tuple `__bases__` (`check_class`, Objects/abstract.c:2587-2600). -/
inductive Derived where
  | cls (c : Cls)
  | other
  deriving Repr, DecidableEq

/-- One element of `self._exceptions` as `object_issubclass`, Objects/abstract.c:2732-2789, treats
it. -/
inductive SupItem (σ : Type) where
  /-- A class whose metaclass is exactly `type`, by its concrete MRO: the quick test of :2737-2742
  and `PyType_IsSubtype` in `recursive_issubclass`, :2715-2717. -/
  | cls (c : Cls)
  /-- An object whose type has `__subclasscheck__`, :2770-2783: an ABC, a class with another
  metaclass. `check` is calling it on `exctype` and taking the truth value, which can run any code
  and raise. A nested tuple, which :2749-2766 loops over, is a `hook` whose `check` is that loop.
  `excCls` is the item's MRO when it is an exception class (`PyExceptionClass_Check`). -/
  | hook (check : Derived → St σ → St σ × Res Bool) (excCls : Option Cls)
  /-- Anything else: neither `__subclasscheck__` nor `__bases__`. -/
  | other

/-- The concrete subclass test, `PyType_IsSubtype`: `d`'s MRO holds `c`. -/
def subOf (d c : Cls) : Bool :=
  match c with
  | [] => false
  | n :: _ => d.contains n

/-- `issubclass(exctype, item)` for one item, Objects/abstract.c:2732-2789: the concrete test for a
plain class, the `__subclasscheck__` call, or the `TypeError` of `check_class` in
`recursive_issubclass`, :2719-2726, for the first argument and then the second. -/
def issubItem (d : Derived) (handled : Option ExcId) (i : SupItem σ) (s : St σ) : St σ × Res Bool :=
  let typeErr (msg : String) : St σ × Res Bool :=
    let (s, e) := s.raiseNew clsType msg handled
    (s, .error e)
  match i, d with
  | .cls c, .cls dc => (s, .ok (subOf dc c))
  | .cls _, .other => typeErr "issubclass() arg 1 must be a class"
  | .hook check _, d => check d s
  | .other, .cls _ => typeErr "issubclass() arg 2 must be a class, a tuple of classes, or a union"
  | .other, .other => typeErr "issubclass() arg 1 must be a class"

/-- `issubclass(exctype, self._exceptions)`, the tuple branch Objects/abstract.c:2749-2766: the items
in order, stopping at the first that is true or raises. -/
def issubTuple (d : Derived) (handled : Option ExcId) : List (SupItem σ) → St σ → St σ × Res Bool
  | [], s => (s, .ok false)
  | i :: is, s =>
    match issubItem d handled i s with
    | (s, .ok false) => issubTuple d handled is s
    | r => r

/-- `get_matcher_type`, Objects/exceptions.c:1245-1276, on the tuple `self._exceptions`: it is a type
matcher when every item is an exception class, and `none`, the `TypeError` of :1271-1274,
otherwise. -/
def matcherClasses : List (SupItem σ) → Option (List Cls)
  | [] => some []
  | .cls c :: is => if c.contains "BaseException" then (c :: ·) <$> matcherClasses is else none
  | .hook _ (some c) :: is => (c :: ·) <$> matcherClasses is
  | _ :: _ => none

/-- `PyErr_GivenExceptionMatches(exc, tuple)`, Python/errors.c:332-367: the concrete subclass test of
the class of `e` against each class; no `__subclasscheck__`. -/
def matchBy (h : Heap) (ms : List Cls) (e : ExcId) : Bool := ms.any (subOf (h.get e).cls)

/-- `orig.derive(excs)`: the method of the group's class, which can raise or return anything. -/
abbrev Derive (σ : Type) := ExcId → List ExcId → St σ → St σ × Res ExcId

/-- The class `BaseExceptionGroup(msg, excs)` gets from `BaseExceptionGroup_new`: `ExceptionGroup`
when every member is an `Exception`. -/
def deriveCls (h : Heap) (excs : List ExcId) : Cls :=
  if excs.all (fun e => h.isInst e "Exception") then clsEG else clsBEG

/-- The builtin `BaseExceptionGroup.derive`, Objects/exceptions.c:1136-1148:
`BaseExceptionGroup(self.message, excs)`. -/
def builtinDerive : Derive σ := fun orig excs s =>
  let (h, e) := s.h.alloc
    { cls := deriveCls s.h excs, msg := (s.h.get orig).msg, children := some excs }
  ({ s with h := h }, .ok e)

/-- `exceptiongroup_subset`, Objects/exceptions.c:1151-1230: `none` for an empty `excs` (:1166-1168);
else `orig.derive(excs)` (:1170-1174), refused unless it is a `BaseExceptionGroup` (:1176-1180),
then `__traceback__` when `orig` has one (:1184-1191), `__context__` and `__cause__` from `orig`
(:1192-1193). The copy of `__notes__`, :1195-1220, is outside the model. -/
def subsetM (derive : Derive σ) (handled : Option ExcId) (s : St σ) (orig : ExcId)
    (excs : List ExcId) : St σ × Res (Option ExcId) :=
  if excs.isEmpty then (s, .ok none)
  else
    match derive orig excs s with
    | (s, .error e) => (s, .error e)
    | (s, .ok eg) =>
      if s.h.isInst eg "BaseExceptionGroup" then
        let o := s.h.get orig
        let h := match o.tb with
          | some t => s.h.setTb eg (some t)
          | none => s.h
        let h := (h.setContext eg o.context).modify eg (fun x => { x with cause := o.cause })
        ({ s with h := h }, .ok (some eg))
      else
        let (s, e) := s.raiseNew clsType "derive must return an instance of BaseExceptionGroup" handled
        (s, .error e)

/-- What `splitRec` gives for one exception: the state and `(match, rest)`, or `none` out of fuel. -/
abbrev SplitRes (σ : Type) := Option (St σ × Res (Option ExcId × Option ExcId))

/-- One turn of the loop over `eg->excs`, Objects/exceptions.c:1374-1407: the recursive call `rec`
on member `e`, its parts appended to `match_list` and `rest_list`; a failure stops the loop. -/
def splitStep (rec : St σ → ExcId → SplitRes σ)
    (acc : Option (St σ × Res (List ExcId × List ExcId))) (e : ExcId) :
    Option (St σ × Res (List ExcId × List ExcId)) :=
  match acc with
  | none => none
  | some (s, .error x) => some (s, .error x)
  | some (s, .ok (ml, rl)) =>
    match rec s e with
    | none => none
    | some (s, .error x) => some (s, .error x)
    | some (s, .ok (m, r)) => some (s, .ok (ml ++ m.toList, rl ++ r.toList))

/-- `exceptiongroup_split_recursive`, Objects/exceptions.c:1322-1430, with the type matcher `ms`: a
full match (:1335-1339), an unmatched leaf (:1340-1346), or the loop over `eg->excs` and the two
subsets, match first (:1410-1419). `none` is out of fuel. -/
def splitRec (ms : List Cls) (derive : Derive σ) (handled : Option ExcId) :
    Nat → St σ → ExcId → SplitRes σ
  | 0, _, _ => none
  | fuel + 1, s, exc =>
    if matchBy s.h ms exc then some (s, .ok (some exc, none))
    else
      match (s.h.get exc).children with
      | none => some (s, .ok (none, some exc))
      | some excs =>
        match excs.foldl (splitStep (splitRec ms derive handled fuel)) (some (s, .ok ([], []))) with
        | none => none
        | some (s, .error x) => some (s, .error x)
        | some (s, .ok (ml, rl)) =>
          match subsetM derive handled s exc ml with
          | (s, .error x) => some (s, .error x)
          | (s, .ok m) =>
            match subsetM derive handled s exc rl with
            | (s, .error x) => some (s, .error x)
            | (s, .ok r) => some (s, .ok (m, r))

/-- `excinst.split(self._exceptions)`, Lib/contextlib.py:527, with the builtin `split`,
Objects/exceptions.c:1440-1463: `None` or a non-group has no `split` (`AttributeError`); a tuple
with an item that is no exception class is the `TypeError` of `get_matcher_type`. -/
def egSplit (items : List (SupItem σ)) (derive : Derive σ) (handled : Option ExcId) (s : St σ)
    (excinst : Option ExcId) : SplitRes σ :=
  let raise (c : Cls) (msg : String) : SplitRes σ :=
    let (s, e) := s.raiseNew c msg handled
    some (s, .error e)
  match excinst with
  | none => raise clsAttr "'NoneType' object has no attribute 'split'"
  | some e =>
    if !s.h.isInst e "BaseExceptionGroup" then
      raise clsAttr s!"'{(s.h.get e).cls.headD ""}' object has no attribute 'split'"
    else
      match matcherClasses items with
      | none => raise clsType
          "expected an exception type, a tuple of exception types, or a callable (other than a class)"
      | some ms => splitRec ms derive handled (s.h.length + 1) s e

/-- `suppress.__exit__`, Lib/contextlib.py:512-531, with `self._exceptions = items`. `exctype` is
the class argument and `excinst` the instance, `none` for `None`; `handled` is `sys.exception()` at
the call, which an exception raised here chains to. `.ok none` is the bare `return` of :523. A group
class that overrides `split` is outside the model; one that overrides `derive` is `derive`. -/
def suppressExit (items : List (SupItem σ)) (derive : Derive σ) (s : St σ) (handled : Option ExcId)
    (exctype : Option Derived) (excinst : Option ExcId) : PyLean.Py (St σ × Res (Option Bool)) :=
  match exctype with
  | none => .ok (s, .ok none)
  | some d =>
    match issubTuple d handled items s with
    | (s, .error e) => .ok (s, .error e)
    | (s, .ok true) => .ok (s, .ok (some true))
    | (s, .ok false) =>
      match issubItem d handled (.cls clsBEG) s with
      | (s, .error e) => .ok (s, .error e)
      | (s, .ok false) => .ok (s, .ok (some false))
      | (s, .ok true) =>
        match egSplit items derive handled s excinst with
        | none => .error .modelFuel
        | some (s, .error e) => .ok (s, .error e)
        | some (s, .ok (_, none)) => .ok (s, .ok (some true))
        | some (s, .ok (_, some r)) => .ok ({ s with h := s.h.raiseCtx r handled }, .error r)

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

/-- The `_exit_wrapper` of `_create_cb_wrapper`, Lib/contextlib.py:552-555, has `__wrapped__`
set to the callback (:607, :750); other entries are what was pushed. -/
def Cb.wrappedAttr : Cb F O A → Option F
  | .wrapped f _ => some f
  | _ => none

/-- `_BaseExitStack.pop_all`, Lib/contextlib.py:560-565. `mk` is `type(self)()`, which runs the
class's `__init__` and can raise; only then is the deque moved (:563-564). The result is the state,
what `self` keeps, and the new stack object with its deque. -/
def popAll {N : Type} (mk : St σ → St σ × Res N) (s : St σ) (st : Stack F O A) :
    St σ × Stack F O A × Res (N × Stack F O A) :=
  match mk s with
  | (s, .error e) => (s, st, .error e)
  | (s, .ok n) => (s, [], .ok (n, st))

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

/-- `_BaseExitStack.push`, Lib/contextlib.py:567-576: `asF exit` is `exit` as a plain callable.
`exit` itself is returned (:576). -/
def push (lookup : ExitLookup F O A) (asF : O → F) (st : Stack F O A) (exit : O) :
    Stack F O A × Res O :=
  match lookupSpecial (lookup exit) (.raw (asF exit)) with
  | .ok cb => (pushExitCallback st cb, .ok exit)
  | .error e => (st, .error e)

/-- `AsyncExitStack.push_async_exit`, Lib/contextlib.py:729-739; `exit` is returned (:739). -/
def pushAsyncExit (lookup : ExitLookup F O A) (asF : O → F) (st : Stack F O A) (exit : O) :
    Stack F O A × Res O :=
  match lookupSpecial (lookup exit) (.raw (asF exit)) with
  | .ok cb => (pushExitCallback st cb false, .ok exit)
  | .error e => (st, .error e)

/-- `_BaseExitStack.callback`, Lib/contextlib.py:598-609: the wrapper of `_create_cb_wrapper`
(:603), whose `__wrapped__` is `callback` (:607), is pushed, and `callback` is returned (:609). -/
def callback (st : Stack F O A) (f : F) (args : A) : Stack F O A × F :=
  (pushExitCallback st (.wrapped f args) true, f)

/-- `AsyncExitStack.push_async_callback`, Lib/contextlib.py:741-752: the same with the wrapper of
`_create_async_cb_wrapper` and `is_sync=False`. -/
def pushAsyncCallback (st : Stack F O A) (f : F) (args : A) : Stack F O A × F :=
  (pushExitCallback st (.wrapped f args) false, f)

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

/-- `ExitStack.close`, Lib/contextlib.py:684-686: the result of `__exit__` is dropped. -/
def close (c : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (frameExc : Option ExcId) :
    Py (Xs σ F O A × Res Unit) := do
  let (x, r) ← exit c fuel fixFuel x none frameExc
  match r with
  | .ok _ => return (x, .ok ())
  | .error e => return (x, .error e)

/-- `await cb(*exc_details)`, Lib/contextlib.py:796, for an entry with `is_sync=False`. The
`_exit_wrapper` of `_create_async_cb_wrapper`, :704-707, is an `async def`: `await
callback(*args, **kwds)` raising `StopIteration` leaves it as `RuntimeError`, and the result is
dropped. Any other entry is what `ac` says awaiting it does. -/
def Cb.acall (ac : Calls σ F O A) (cb : Cb F O A) (x : Xs σ F O A) (d : Option ExcId) :
    Xs σ F O A × Res Bool :=
  match cb with
  | .wrapped f args =>
    let r : Xs σ F O A × Res Bool := match ac.wrapped f args x with
      | (x, .error e) => (x, .error e)
      | (x, .ok ()) => (x, .ok false)
    let (s, res) := coBoundary r.1.1 r.2
    ((s, r.1.2), res)
  | cb => cb.call ac x d

/-- The loop of `AsyncExitStack.__aexit__`, Lib/contextlib.py:786-806: `cb(...)` for a sync entry
(:793-794), `await cb(...)` for an async one (:795-796). -/
def aexitLoop (c ac : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat) :
    Nat → Xs σ F O A → Option ExcId → Bool → Bool → Py (Xs σ F O A × Option ExcId × Bool × Bool)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, x, exc, suppressed, pending =>
    match x.2 with
    | [] => .ok (x, exc, suppressed, pending)
    | (isSync, cb) :: rest =>
      match (if isSync then cb.call c (x.1, rest) exc else cb.acall ac (x.1, rest) exc) with
      | (x, .ok true) => aexitLoop c ac frameExc fixFuel fuel x none true false
      | (x, .ok false) => aexitLoop c ac frameExc fixFuel fuel x exc suppressed pending
      | (x, .error newExc) =>
        match fixExceptionContext frameExc exc fixFuel x.1.h newExc with
        | none => .error .modelFuel
        | some h =>
          aexitLoop c ac frameExc fixFuel fuel ({ x.1 with h := h }, x.2) (some newExc) suppressed true

/-- `AsyncExitStack.__aexit__`, Lib/contextlib.py:761-817, an `async def`: the exception it raises
passes `coBoundary`. -/
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

/-- `AsyncExitStack.aclose`, Lib/contextlib.py:754-756: `await self.__aexit__(None, None, None)`
inside an `async def`, the result dropped. -/
def aclose (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (frameExc : Option ExcId) :
    Py (Xs σ F O A × Res Unit) := do
  let (x, r) ← aexit c ac fuel fixFuel x none frameExc
  let r : Res Unit := match r with
    | .ok _ => .ok ()
    | .error e => .error e
  let (s, r) := coBoundary x.1 r
  return ((s, x.2), r)

/-- `AsyncExitStack.enter_async_context`, Lib/contextlib.py:709-727: the steps of `enterContext` with
`is_sync=False`, inside an `async def`, so a `StopIteration` from a lookup or from `await _enter()`
leaves as `RuntimeError`. -/
def aenterContext (enterOf : O → Option (Descr (Xs σ F O A → Xs σ F O A × Res V)))
    (exitOf : ExitLookup F O A) (msg : String) (x : Xs σ F O A) (cm : O) : Xs σ F O A × Res V :=
  let (x, r) := enterContext enterOf exitOf msg false x cm
  let (s, r) := coBoundary x.1 r
  ((s, x.2), r)

end PyLean.CoreLibs.Misc.Contextlib
