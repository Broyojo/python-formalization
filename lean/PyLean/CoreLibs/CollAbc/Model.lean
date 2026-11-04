import PyLean.Core

/-!
`Lib/_collections_abc.py` (CPython 3.15.2), mirrored.

Each mixin is a generic algorithm over the primitives a concrete subclass
supplies, so the primitives are parameters: the structures `Seq`, `MSeq`, `SetV`,
`MSet`, `MapV`, `MMap` and `Gen` below hold them. A primitive returns `Py`, because
a subclass may raise from any of them, and the order in which they are called is
observable. Mutation is explicit state passing over an abstract `σ`.

Iteration is one finite pass: the elements an iterator yields, as a list, and the
exception its `__next__` raises after them (`tail`), which a loop that stops early
never sees. A failing `iter()` is the `.error` of the list.

Identity and equality of elements are abstract (`EqOps`): the source's
`v is value or v == value` tests identity first and only then calls `__eq__`,
which may raise.

Scope limits, stated once: a primitive is a function of the object's state, so a
loop does not see its operand change under it except through the explicit state;
`self.method(...)` calls reach the mixin method, not an override, except where a
parameter says otherwise; and classes are compared by identity (`cls is X`).

Classes are data for `_check_methods`: an MRO is a list of class dictionaries.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

/-- A dunder's result: a value, or `NotImplemented`. -/
inductive Ret (α : Type) where
  | val (a : α)
  | notImplemented
  deriving Repr, DecidableEq, Inhabited

/-- `except KeyError`. -/
def isKeyError : PyExc → Bool
  | .keyError _ => true
  | _ => false

/-- `except IndexError`. -/
def isIndexError : PyExc → Bool
  | .indexError _ => true
  | _ => false

/-- `except TypeError`. -/
def isTypeError : PyExc → Bool
  | .typeError _ => true
  | _ => false

/-- `raise KeyError` without arguments: `str(e)` is empty. -/
def bareKeyError : PyExc := .keyError ""

/-- Abstract identity and equality of elements. -/
structure EqOps (α : Type) where
  is_ : α → α → Bool
  eq : α → α → Py Bool

/-- `v is value or v == value` (Lib/_collections_abc.py:880, 897, 1028, 1054, 1061). -/
def EqOps.same {α : Type} (E : EqOps α) (v w : α) : Py Bool :=
  if E.is_ v w then pure true else E.eq v w

/-- The end of a loop: `StopIteration`, or the exception of the iterator. -/
def raiseTail {β : Type} (tail : Option PyExc) (v : β) : Py β :=
  match tail with
  | none => .ok v
  | some e => .error e

/-! ### One-trick ponies: `_check_methods` and the `__subclasshook__` family -/

/-- A class dictionary: attribute name, and whether its value is `None`. -/
abbrev ClassDict := List (String × Bool)

/-- The inner loop of `_check_methods` (Lib/_collections_abc.py:111-117): walk the
MRO to the first class defining `method`. `.notImplemented` if that binding is
`None` or no class defines it; `.val ()` for the `break`. -/
def checkOne (method : String) : List ClassDict → Ret Unit
  | [] => .notImplemented
  | B :: rest =>
    match B.lookup method with
    | some true => .notImplemented
    | some false => .val ()
    | none => checkOne method rest

/-- `_check_methods(C, *methods)`, Lib/_collections_abc.py:108-118. -/
def checkMethods (mro : List ClassDict) : List String → Ret Bool
  | [] => .val true
  | m :: ms =>
    match checkOne m mro with
    | .notImplemented => .notImplemented
    | .val () => checkMethods mro ms

/-- The ABCs with a `__subclasshook__`, with the method lists their hooks pass to
`_check_methods`: Lib/_collections_abc.py:131, 146, 189, 207, 228, 275-276, 295, 316,
348, 395-396, 414, 429, 442, 457, 540. -/
def hookMethods : String → List String
  | "Hashable" => ["__hash__"]
  | "Awaitable" => ["__await__"]
  | "Coroutine" => ["__await__", "send", "throw", "close"]
  | "AsyncIterable" => ["__aiter__"]
  | "AsyncIterator" => ["__anext__", "__aiter__"]
  | "AsyncGenerator" => ["__aiter__", "__anext__", "asend", "athrow", "aclose"]
  | "Iterable" => ["__iter__"]
  | "Iterator" => ["__iter__", "__next__"]
  | "Reversible" => ["__reversed__", "__iter__"]
  | "Generator" => ["__iter__", "__next__", "send", "throw", "close"]
  | "Sized" => ["__len__"]
  | "Container" => ["__contains__"]
  | "Collection" => ["__len__", "__iter__", "__contains__"]
  | "Buffer" => ["__buffer__"]
  | "Callable" => ["__call__"]
  | _ => []

/-- `X.__subclasshook__(cls, C)`: `if cls is X: return _check_methods(C, ...)`, else
`return NotImplemented`. All fifteen hooks have this one shape. -/
def subclasshook (x cls : String) (mro : List ClassDict) : Ret Bool :=
  if cls = x then checkMethods mro (hookMethods x) else .notImplemented

/-! ### Abstract method bodies -/

/-- What an abstract body does, reached through `super()` or the class. A generator body gives a generator that yields
`n` `None`s and then stops with `StopIteration`; an `async def` body gives a coroutine, so the call succeeds and
awaiting it raises; any other body raises at the call. (The bodies that return one constant, `Hashable.__hash__`,
`Sized.__len__`, `Container.__contains__` and `Callable.__call__`, are not here.) -/
inductive Stub where
  | gen (n : Nat)
  | raises (e : PyExc)
  | awaitRaises (e : PyExc)
  deriving Repr, DecidableEq

/-- `raise StopAsyncIteration`: `str(e)` is empty. -/
def stopAsyncIteration : PyExc := .named "StopAsyncIteration" ""
/-- `raise NotImplementedError`. -/
def notImplementedError : PyExc := .named "NotImplementedError" ""
/-- `AsyncIterator()` for the abstract class, `object_new`'s refusal (Objects/typeobject.c), whose message names the
class's one abstract method. -/
def abstractAsyncIterator : PyExc :=
  .typeError "Can't instantiate abstract class AsyncIterator without an implementation for abstract method '__anext__'"

/-- The body of each abstract method, by inventory name, Lib/_collections_abc.py at the lines given. -/
def stubBody : String → Option Stub
  | "Awaitable.__await__" => some (.gen 1)                     -- :141 `yield`
  | "Iterable.__iter__" => some (.gen 0)                       -- :289-290 `while False: yield None`
  | "Reversible.__reversed__" => some (.gen 0)                 -- :342-343
  | "Iterator.__next__" => some (.raises .stopIteration)       -- :308
  | "Generator.send" => some (.raises .stopIteration)          -- :367
  | "Coroutine.send" => some (.raises .stopIteration)          -- :161
  | "AsyncIterator.__anext__" => some (.awaitRaises stopAsyncIteration)  -- :218-220 `async def`
  | "AsyncGenerator.asend" => some (.awaitRaises stopAsyncIteration)     -- :243-247 `async def`
  | "AsyncIterable.__aiter__" => some (.raises abstractAsyncIterator)    -- :202 `return AsyncIterator()`
  | "Buffer.__buffer__" => some (.raises notImplementedError)  -- :452
  | "MutableSet.add" => some (.raises notImplementedError)     -- :707
  | "MutableSet.discard" => some (.raises notImplementedError) -- :712
  | "Mapping.__getitem__" => some (.raises (.keyError ""))     -- :790
  | "MutableMapping.__setitem__" => some (.raises (.keyError ""))  -- :922
  | "MutableMapping.__delitem__" => some (.raises (.keyError ""))  -- :926
  | "Sequence.__getitem__" => some (.raises (.indexError ""))      -- :1014
  | "MutableSequence.__setitem__" => some (.raises (.indexError ""))  -- :1116
  | "MutableSequence.__delitem__" => some (.raises (.indexError ""))  -- :1120
  | "MutableSequence.insert" => some (.raises (.indexError ""))       -- :1125
  | _ => none

/-! ### Generator, Coroutine, AsyncGenerator mixins -/

mutual
/-- An object passed to `throw(typ, val, tb)` as `typ` or `val`, as `raise`, a call with no arguments and
`.with_traceback(tb)` see it. -/
inductive TObj where
  /-- An exception class. `make` is what calling it with no arguments does (`__new__`, then `__init__`): the
  object made, or the exception raised, as `TypeError` for `UnicodeDecodeError`, whose constructor needs five
  arguments. -/
  | excClass (name : String) (make : TMade)
  /-- An exception instance of class `name`, with the builtin `with_traceback`; `tb` says whether the traceback
  given to `throw` is attached to it. -/
  | excInst (name : String) (tb : Bool)
  /-- Any other object, of type `tname`: `call` is what calling it with no arguments does (`none`: it is not
  callable), and `withTb` what `obj.with_traceback(tb)` does (`none`: it has no such attribute). -/
  | other (tname : String) (call : Option TMade) (withTb : Option TMade)

/-- The outcome of a call: an object, or an exception. -/
inductive TMade where
  | obj (o : TObj)
  | raises (e : PyExc)
end

def TMade.toPy : TMade → Py TObj
  | .obj o => .ok o
  | .raises e => .error e

/-- The `tb` argument of `throw`: `None`, a traceback object, or anything else. -/
inductive TbArg where
  | absent
  | traceback
  | other
  deriving Repr, DecidableEq

/-- What `throw` raised when it raised the exception it was asked to: the class, and whether the traceback given
is attached. -/
structure Raised where
  name : String
  tracebackSet : Bool
  deriving Repr, DecidableEq

/-- `raise x`, Python/ceval.h:541-566 `do_raise`: a class is called with no arguments and must give an instance, an
instance is raised as it is, anything else is a `TypeError`. -/
def raiseObj : TObj → Except PyExc Raised
  | .excClass _ make =>
    match make with
    | .raises e => .error e
    | .obj (.excInst n t) => .ok ⟨n, t⟩
    | .obj _ => .error (.typeError "~calling the class should have returned an instance of BaseException")
  | .excInst n t => .ok ⟨n, t⟩
  | .other .. => .error (.typeError "exceptions must derive from BaseException")

/-- `typ()`: calling an object with no arguments. -/
def callNoArgs : TObj → Py TObj
  | .excClass _ make => make.toPy
  | .excInst n _ => .error (.typeError s!"'{n}' object is not callable")
  | .other t none _ => .error (.typeError s!"'{t}' object is not callable")
  | .other _ (some r) _ => r.toPy

/-- `val.with_traceback(tb)` for a `tb` that is not `None`: on an instance the builtin method, which stores a traceback
and refuses anything else (Objects/exceptions.c:271-277, 399-411); on a class the unbound method descriptor, which does
not apply to `tb`; on another object whatever its attribute does. -/
def withTraceback (tb : TbArg) : TObj → Py TObj
  | .excInst n _ =>
    match tb with
    | .traceback => .ok (.excInst n true)
    | .absent => .ok (.excInst n false)
    | .other => .error (.typeError "__traceback__ must be a traceback or None")
  | .excClass .. => .error (.typeError "~descriptor 'with_traceback' for 'BaseException' objects doesn't apply")
  | .other t _ none => .error (.named "AttributeError" s!"'{t}' object has no attribute 'with_traceback'")
  | .other _ _ (some r) => r.toPy

/-- The body of `Generator.throw`, `Coroutine.throw` and `AsyncGenerator.athrow`
(Lib/_collections_abc.py:374-380, 168-174, 254-260). `val = none` is `val is None`. The `.ok` side is the exception
that was asked for; `.error` is any other exception, from the misuse or from the code `throw` called. -/
def throwBody (typ : TObj) (val : Option TObj) (tb : TbArg) : Except PyExc Raised :=
  match val with
  | none =>
    match tb with
    | .absent => raiseObj typ
    | _ => do
      let v ← callNoArgs typ
      let v ← withTraceback tb v
      raiseObj v
  | some v =>
    match tb with
    | .absent => raiseObj v
    | _ => do
      let v ← withTraceback tb v
      raiseObj v

/-- The outcome of one resumption of a generator. -/
inductive GenStep (V : Type) where
  | yielded (v : V)
  /-- `raise StopIteration(v)`, or `StopAsyncIteration` in the async family. -/
  | stopped (ret : V)
  | raised (e : PyExc)
  deriving Repr, DecidableEq

/-- The two primitives of a `Generator` subclass. -/
structure Gen (σ V : Type) where
  send : σ → V → GenStep V × σ
  /-- `self.throw(GeneratorExit)`; in the async family, what awaiting `self.athrow(GeneratorExit)` gives. -/
  throwExit : σ → GenStep V × σ

def generatorExit : PyExc := .named "GeneratorExit" ""

/-- `except GeneratorExit`, for the exception as raised. -/
def isGeneratorExit : PyExc → Bool
  | .named "GeneratorExit" _ => true
  | _ => false

/-- `Generator.__next__` and `AsyncGenerator.__anext__`: `self.send(None)`,
Lib/_collections_abc.py:360, 240. -/
def Gen.next {σ V : Type} (G : Gen σ V) (none : V) (s : σ) : GenStep V × σ := G.send s none

/-- `Generator.close`, `Coroutine.close`, `AsyncGenerator.aclose`,
Lib/_collections_abc.py:385-390, 179-184, 265-270, with the message of each. Returns `None`. -/
def Gen.close {σ V : Type} (G : Gen σ V) (msg : String) (s : σ) : Py Unit × σ :=
  match G.throwExit s with
  | (.yielded _, s') => (.error (.named "RuntimeError" msg), s')
  | (.stopped _, s') => (.ok (), s')
  | (.raised e, s') => (if isGeneratorExit e then .ok () else .error e, s')

/-- Lib/_collections_abc.py:390. -/
def genCloseMsg := "generator ignored GeneratorExit"
/-- Lib/_collections_abc.py:184. -/
def coroCloseMsg := "coroutine ignored GeneratorExit"
/-- Lib/_collections_abc.py:270. -/
def asyncCloseMsg := "asynchronous generator ignored GeneratorExit"
/-- `ASYNC_GEN_IGNORED_EXIT_MSG`, Objects/genobject.c:64-65. -/
def builtinAsyncCloseMsg := "async generator ignored GeneratorExit"
/-- `gen_close` for a generator, Objects/genobject.c:524. -/
def builtinGenCloseMsg := "generator ignored GeneratorExit"
/-- `gen_close` for a coroutine, Objects/genobject.c:525-526. -/
def builtinCoroCloseMsg := "coroutine ignored GeneratorExit"

/-- The builtin `generator.close()` and `coroutine.close()` after the frame has started and not finished,
Objects/genobject.c:464-545 `gen_close`, with the message of :524-526: a value returned while closing is the result. -/
def builtinClose {σ V : Type} (G : Gen σ V) (msg : String) (s : σ) : Py (Option V) × σ :=
  match G.throwExit s with
  | (.yielded _, s') => (.error (.named "RuntimeError" msg), s')
  | (.stopped v, s') => (.ok (some v), s')
  | (.raised e, s') => (if isGeneratorExit e then .ok none else .error e, s')

/-- The builtin `async_generator.aclose()` awaited, after the frame has started and not finished, for a generator that
does not await while closing: `async_gen_athrow_send` in aclose mode, Objects/genobject.c:2350-2362, 2398-2421. An
async yield is `RuntimeError(ASYNC_GEN_IGNORED_EXIT_MSG)`; `StopAsyncIteration` or `GeneratorExit` end it. -/
def builtinAclose {σ V : Type} (G : Gen σ V) (s : σ) : Py Unit × σ :=
  match G.throwExit s with
  | (.yielded _, s') => (.error (.named "RuntimeError" builtinAsyncCloseMsg), s')
  | (.stopped _, s') => (.ok (), s')
  | (.raised e, s') => (if isGeneratorExit e then .ok () else .error e, s')

/-! ### Callable -/

/-- An object in `Callable[...]`'s arguments, as `_is_param_expr`, `__new__` and `__getitem__` see it. -/
inductive CArg where
  | ellipsis
  /-- An instance of `list` or a subclass. -/
  | list (items : List CArg)
  /-- An instance of `tuple` or a subclass; scope: its type is not one named `ParamSpec` in a module `typing`. -/
  | tuple (items : List CArg)
  /-- Anything else: the `__module__` and `__name__` of its type. -/
  | obj (tmod tname : String) (repr : String)
  deriving Repr, Inhabited

/-- `_is_param_expr(obj)`, Lib/_collections_abc.py:516-526. -/
def isParamExpr : CArg → Bool
  | .ellipsis => true
  | .list _ => true
  | .tuple _ => false
  | .obj m n _ => m == "typing" && ["ParamSpec", "_ConcatenateGenericAlias"].any (n == ·)

/-- `isinstance(x, (tuple, list))`. -/
def CArg.isSeq : CArg → Bool
  | .list _ | .tuple _ => true
  | _ => false

/-- `args` as `isinstance(args, tuple) and len(args) == 2` and `t_args, t_result = args` see it: `none` is anything
that is not a tuple of two. -/
def asPair : List CArg → Option (CArg × CArg)
  | [a, b] => some (a, b)
  | _ => none

/-- `_CallableGenericAlias.__new__`, Lib/_collections_abc.py:473-483: the `__args__` of the alias. -/
def callableNew (args : Option (CArg × CArg)) : Py (List CArg) :=
  match args with
  | none => .error (.typeError "Callable must be used as Callable[[arg, ...], result].")
  | some (tArgs, tResult) =>
    match tArgs with
    | .list items | .tuple items => .ok (items ++ [tResult])
    | _ =>
      if !isParamExpr tArgs then
        .error (.typeError "~Expected a list of types, an ellipsis, ParamSpec, or Concatenate. Got ")
      else .ok [tArgs, tResult]

/-- `_CallableGenericAlias.__repr__`, Lib/_collections_abc.py:485-491. `gaRepr` is `GenericAlias.__repr__`
(Objects/genericaliasobject.c) and `typeRepr` is `annotationlib.type_repr`, both outside this file. -/
def callableRepr (typeRepr : CArg → String) (gaRepr : List CArg → String) (args : List CArg) : Py String :=
  if args.length = 2 ∧ isParamExpr (args.headD .ellipsis) then .ok (gaRepr args)
  else
    match args.getLast? with
    | none => .error (.indexError "tuple index out of range")
    | some r =>
      .ok s!"collections.abc.Callable[[{", ".intercalate (args.dropLast.map typeRepr)}], {typeRepr r}]"

/-- `_CallableGenericAlias.__reduce__`, Lib/_collections_abc.py:493-497: the `args` of the returned
`(_CallableGenericAlias, (Callable, args))`, as the tuple it is. -/
def callableReduce (args : List CArg) : Py (List CArg) :=
  if args.length = 2 ∧ isParamExpr (args.headD .ellipsis) then .ok args
  else
    match args.getLast? with
    | none => .error (.indexError "tuple index out of range")
    | some r => .ok [.list args.dropLast, r]

/-- `_CallableGenericAlias.__getitem__`, Lib/_collections_abc.py:499-514, from `new_args`, the `__args__` that the
inherited substitution (`GenericAlias.__getitem__`, Objects/genericaliasobject.c) produced: the `__args__` of the
result. -/
def callableGetitem (newArgs : List CArg) : Py (List CArg) :=
  match newArgs with
  | [] => .error (.indexError "tuple index out of range")
  | a :: _ =>
    let newArgs := if !a.isSeq then [.tuple newArgs.dropLast, newArgs.getLastD a] else newArgs
    callableNew (asPair newArgs)

/-! ### Sequence -/

/-- The primitives of a `Sequence` subclass. -/
structure Seq (α : Type) where
  getitem : Int → Py α
  len : Py Nat

/-- `Sequence.__iter__`, Lib/_collections_abc.py:1016-1024, drained. An `IndexError`
from `self[i]` ends the iteration; anything else propagates. -/
def Seq.iterFrom {α : Type} (s : Seq α) : (fuel : Nat) → Int → Py (List α)
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    match s.getitem i with
    | .error e => if isIndexError e then .ok [] else .error e
    | .ok v => do
      let rest ← s.iterFrom fuel (i + 1)
      pure (v :: rest)

/-- `Sequence.__contains__`, Lib/_collections_abc.py:1026-1030, over `__iter__`. -/
def Seq.containsFrom {α : Type} (s : Seq α) (E : EqOps α) (value : α) :
    (fuel : Nat) → Int → Py Bool
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    match s.getitem i with
    | .error e => if isIndexError e then .ok false else .error e
    | .ok v => do
      if ← E.same v value then return true
      s.containsFrom E value fuel (i + 1)

/-- `Sequence.count`, Lib/_collections_abc.py:1059-1061: `sum(1 for v in self if ...)` over `__iter__`. -/
def Seq.countFrom {α : Type} (s : Seq α) (E : EqOps α) (value : α) :
    (fuel : Nat) → Int → Py Nat
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    match s.getitem i with
    | .error e => if isIndexError e then .ok 0 else .error e
    | .ok v => do
      let hit ← E.same v value
      let rest ← s.countFrom E value fuel (i + 1)
      pure ((if hit then 1 else 0) + rest)

/-- The loop `for i in reversed(range(n)): yield self[i]`, from `i = n - 1` down. No exception is caught. -/
def Seq.reversedFrom {α : Type} (s : Seq α) : Nat → Py (List α)
  | 0 => .ok []
  | n + 1 => do
    let v ← s.getitem n
    let rest ← s.reversedFrom n
    pure (v :: rest)

/-- `Sequence.__reversed__`, Lib/_collections_abc.py:1032-1034, drained. -/
def Seq.reversed {α : Type} (s : Seq α) : Py (List α) := do
  let n ← s.len
  s.reversedFrom n

/-- The `while` loop of `Sequence.index`, Lib/_collections_abc.py:1048-1057. -/
def Seq.indexLoop {α : Type} (s : Seq α) (E : EqOps α) (value : α) (stop : Option Int) :
    (fuel : Nat) → Int → Py Int
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    if stop.isNone ∨ i < stop.getD 0 then
      match s.getitem i with
      | .error e => if isIndexError e then .error (.valueError "") else .error e
      | .ok v => do
        if ← E.same v value then return i
        s.indexLoop E value stop fuel (i + 1)
    else .error (.valueError "")

/-- `Sequence.index(value, start, stop)` for an `int` `start`,
Lib/_collections_abc.py:1036-1057. `start=None` and non-`int` arguments fall through to
`__getitem__` and to `<`, which is the subclass's business. Each negative bound calls `len(self)`. -/
def Seq.index {α : Type} (s : Seq α) (E : EqOps α) (value : α) (start : Int)
    (stop : Option Int) (fuel : Nat) : Py Int := do
  let start ← if start < 0 then do pure (max ((← s.len : Nat) + start) 0) else pure start
  let stop ← match stop with
    | some t => if t < 0 then do pure (some (t + (← s.len : Nat))) else pure (some t)
    | none => pure none
  s.indexLoop E value stop fuel start

/-! ### MutableSequence -/

/-- The primitives of a `MutableSequence` subclass. -/
structure MSeq (σ α : Type) where
  getitem : σ → Int → Py α
  setitem : σ → Int → α → Py σ
  delitem : σ → Int → Py σ
  insert : σ → Int → α → Py σ
  len : σ → Py Nat

/-- The `Sequence` mixins of the current state. -/
def MSeq.view {σ α : Type} (M : MSeq σ α) (s : σ) : Seq α := ⟨M.getitem s, M.len s⟩

/-- `MutableSequence.append`, Lib/_collections_abc.py:1127-1129: `self.insert(len(self), value)`. -/
def MSeq.append {σ α : Type} (M : MSeq σ α) (s : σ) (v : α) : Py σ := do
  M.insert s (← M.len s : Nat) v

/-- `MutableSequence.pop`, Lib/_collections_abc.py:1153-1159. -/
def MSeq.pop {σ α : Type} (M : MSeq σ α) (s : σ) (index : Int := -1) : Py (α × σ) := do
  let v ← M.getitem s index
  let s' ← M.delitem s index
  pure (v, s')

/-- `MutableSequence.clear`, Lib/_collections_abc.py:1131-1137. -/
def MSeq.clear {σ α : Type} (M : MSeq σ α) : (fuel : Nat) → σ → Py σ
  | 0, _ => .error .modelFuel
  | fuel + 1, s =>
    match M.pop s with
    | .error e => if isIndexError e then .ok s else .error e
    | .ok (_, s') => M.clear fuel s'

/-- The swap `self[i], self[n-i-1] = self[n-i-1], self[i]`: the right side evaluates
left to right, then the targets assign left to right. -/
def MSeq.swap {σ α : Type} (M : MSeq σ α) (n : Nat) (s : σ) (i : Nat) : Py σ := do
  let a ← M.getitem s (n - (i : Int) - 1)
  let b ← M.getitem s i
  let s1 ← M.setitem s i a
  M.setitem s1 (n - (i : Int) - 1) b

/-- `for i in range(k): swap` counting up from `i`. -/
def MSeq.swapLoop {σ α : Type} (M : MSeq σ α) (n : Nat) : (k i : Nat) → σ → Py σ
  | 0, _, s => .ok s
  | k + 1, i, s => do
    let s' ← M.swap n s i
    M.swapLoop n k (i + 1) s'

/-- `MutableSequence.reverse`, Lib/_collections_abc.py:1139-1143. -/
def MSeq.reverse {σ α : Type} (M : MSeq σ α) (s : σ) : Py σ := do
  let n ← M.len s
  M.swapLoop n (n / 2) 0 s

/-- `for v in values: self.append(v)`, over an iterator that may raise after its items. -/
def MSeq.extendList {σ α : Type} (M : MSeq σ α) (tail : Option PyExc) (s : σ) : List α → Py σ
  | [] => raiseTail tail s
  | v :: vs => do
    let s' ← M.append s v
    M.extendList tail s' vs

/-- The argument of `extend`: `self`, or another iterable (`iter()` and its elements, and the exception after them). -/
inductive ExtendArg (α : Type) where
  | self_
  | iter (xs : Py (List α)) (tail : Option PyExc := none)

/-- `MutableSequence.extend(values)`, Lib/_collections_abc.py:1145-1151. For `values is self`, `list(values)` is
`list_extend_iter_lock_held`, Objects/listobject.c:1300-1340: `iter(self)` (a generator, which runs nothing yet), then
`PyObject_LengthHint(self, 8)` (Objects/abstract.c:95-118), which calls `len(self)` and falls back to 8 only after a
`TypeError` (scope: the class has no `__length_hint__`), then preallocation of the hint, `MemoryError` when `alloc`
refuses it (Objects/listobject.c:219-235, 1324), then `Sequence.__iter__`. -/
def MSeq.extend {σ α : Type} (M : MSeq σ α) (alloc : Nat → Bool) (s : σ) (values : ExtendArg α) (fuel : Nat) :
    Py σ :=
  match values with
  | .iter xs t => do M.extendList t s (← xs)
  | .self_ => do
    let hint ← match M.len s with
      | .ok n => pure n
      | .error e => if isTypeError e then pure 8 else throw e
    if hint ≠ 0 ∧ alloc hint = false then throw (.named "MemoryError" "")
    let vs ← (M.view s).iterFrom fuel 0
    M.extendList none s vs

/-- `MutableSequence.__iadd__`, Lib/_collections_abc.py:1167-1169: `self.extend(values)`, whatever `extend` the class
has, then `self`, which is the state the call left. -/
def MSeq.iadd {σ β : Type} (extend : σ → β → Py σ) (s : σ) (values : β) : Py σ := do
  let s' ← extend s values
  pure s'

/-- `MutableSequence.remove`, Lib/_collections_abc.py:1161-1165. -/
def MSeq.remove {σ α : Type} (M : MSeq σ α) (E : EqOps α) (s : σ) (value : α) (fuel : Nat) :
    Py σ := do
  let i ← (M.view s).index E value 0 none fuel
  M.delitem s i

/-! ### Set -/

/-- The primitives of a `Set` subclass. -/
structure SetV (α : Type) where
  len : Py Nat
  iter : Py (List α)
  contains : α → Py Bool
  tail : Option PyExc := none

/-- `cls(it)`, `_from_iterable` (Lib/_collections_abc.py:598-604, or `set(it)` in `KeysView` and `ItemsView`, :852-853,
870-871), as a consumer of what it is given: `start` runs before the first element is asked for, `push` takes each
element as the generator produces it and may raise (as `set()` does for an unhashable element), `done` after the end.
Scope: the constructor drains its argument. -/
structure FromIter (ρ α β : Type) where
  start : Py ρ
  push : ρ → α → Py ρ
  done : ρ → Py β

/-- The other operand of a set operator. `iterable abc xs tail` is anything that is not a `Set`: `abc` says whether
`isinstance(other, Iterable)` (an `__iter__` along the MRO, Lib/_collections_abc.py:293-296), and `xs` is what
`iter(other)` gives, which also accepts an object with only `__getitem__`, and refuses others with `TypeError`. -/
inductive Operand (α : Type) where
  | set (s : SetV α)
  | iterable (abc : Bool) (xs : Py (List α)) (tail : Option PyExc := none)

/-- An operand that `iter()` refuses, such as `5`. -/
def Operand.other {α : Type} : Operand α := .iterable false (.error (.typeError "~object is not iterable"))

/-- `isinstance(other, Iterable)`. -/
def Operand.isIterable {α : Type} : Operand α → Bool
  | .set _ => true
  | .iterable abc _ _ => abc

/-- `iter(other)` and the elements. -/
def Operand.items {α : Type} : Operand α → Py (List α)
  | .set s => s.iter
  | .iterable _ xs _ => xs

/-- What the operand's iterator raises after its elements. -/
def Operand.tail {α : Type} : Operand α → Option PyExc
  | .set s => s.tail
  | .iterable _ _ t => t

/-- `for elem in xs: if elem not in other: return False`, then `return True`, over an iterator that may raise after
its items: a `False` before that returns first. -/
def allInT {α : Type} (contains : α → Py Bool) (tail : Option PyExc) : List α → Py Bool
  | [] => raiseTail tail true
  | x :: xs => do
    if ← contains x then allInT contains tail xs else return false

/-- `Set.__le__`, Lib/_collections_abc.py:562-570. -/
def SetV.le {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) > (← o.len) then return .val false
    let xs ← self.iter
    return .val (← allInT o.contains self.tail xs)
  | _ => .ok .notImplemented

/-- `Set.__ge__`, Lib/_collections_abc.py:582-590. -/
def SetV.ge {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) < (← o.len) then return .val false
    let xs ← o.iter
    return .val (← allInT self.contains o.tail xs)
  | _ => .ok .notImplemented

/-- `Set.__lt__`, Lib/_collections_abc.py:572-575. -/
def SetV.lt {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) < (← o.len) then self.le (.set o) else return .val false
  | _ => .ok .notImplemented

/-- `Set.__gt__`, Lib/_collections_abc.py:577-580. -/
def SetV.gt {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) > (← o.len) then self.ge (.set o) else return .val false
  | _ => .ok .notImplemented

/-- `Set.__eq__`, Lib/_collections_abc.py:592-595. -/
def SetV.eq {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) = (← o.len) then self.le (.set o) else return .val false
  | _ => .ok .notImplemented

/-- A generator `value for value in xs if keep(value)` consumed by the constructor: each element is tested, and pushed
when it is kept, before the next is asked for; then the iterator's end. -/
def feedIf {ρ α β : Type} (B : FromIter ρ α β) (keep : α → Py Bool) (tail : Option PyExc) : ρ → List α → Py ρ
  | r, [] => raiseTail tail r
  | r, x :: xs => do
    let k ← keep x
    if k then do
      let r' ← B.push r x
      feedIf B keep tail r' xs
    else feedIf B keep tail r xs

/-- Every element of an iterator pushed into the constructor, then the iterator's end. -/
def feedAll {ρ α β : Type} (B : FromIter ρ α β) (tail : Option PyExc) : ρ → List α → Py ρ
  | r, [] => raiseTail tail r
  | r, x :: xs => do
    let r' ← B.push r x
    feedAll B tail r' xs

/-- `cls(other)` on an iterable: the constructor starts, calls `iter(other)` and drains it. -/
def build {ρ α β : Type} (B : FromIter ρ α β) (xs : Py (List α)) (tail : Option PyExc) : Py β := do
  let r ← B.start
  let xs ← xs
  let r ← feedAll B tail r xs
  B.done r

/-- `Set.__and__` and `__rand__`, Lib/_collections_abc.py:606-611. `iter(other)` runs when the generator is made,
before `_from_iterable` is called. -/
def SetV.and {ρ α β : Type} (self : SetV α) (B : FromIter ρ α β) (other : Operand α) : Py (Ret β) :=
  if !other.isIterable then .ok .notImplemented
  else do
    let xs ← other.items
    let r ← B.start
    let r ← feedIf B self.contains other.tail r xs
    pure (.val (← B.done r))

/-- The loop of `Set.isdisjoint`. -/
def disjointLoop {α : Type} (contains : α → Py Bool) (tail : Option PyExc) : List α → Py Bool
  | [] => raiseTail tail true
  | x :: rest => do
    if ← contains x then return false else disjointLoop contains tail rest

/-- `Set.isdisjoint`, Lib/_collections_abc.py:613-618: `for value in other` with no `isinstance` test. -/
def SetV.isdisjoint {α : Type} (self : SetV α) (other : Operand α) : Py Bool := do
  disjointLoop self.contains other.tail (← other.items)

/-- `Set.__or__` and `__ror__`, Lib/_collections_abc.py:620-626: the chain generator calls `iter(self)` at its first
step, inside the constructor, and `iter(other)` once `self` is exhausted. -/
def SetV.or {ρ α β : Type} (self : SetV α) (B : FromIter ρ α β) (other : Operand α) : Py (Ret β) :=
  if !other.isIterable then .ok .notImplemented
  else do
    let r ← B.start
    let ys ← self.iter
    let r ← feedAll B self.tail r ys
    let xs ← other.items
    let r ← feedAll B other.tail r xs
    pure (.val (← B.done r))

/-- `isinstance(other, Set)`, else `isinstance(other, Iterable)` and `other = self._from_iterable(other)`, else
`NotImplemented` (`none`), shared by `__sub__`, `__rsub__` and `__xor__`. -/
def Operand.asSet? {ρ α : Type} (B : FromIter ρ α (SetV α)) : Operand α → Option (Py (SetV α))
  | .set s => some (.ok s)
  | .iterable abc xs t => if abc then some (build B xs t) else none

/-- `value not in s`. -/
def notIn {α : Type} (s : SetV α) (x : α) : Py Bool := do pure (!(← s.contains x))

/-- `Set.__sub__`, Lib/_collections_abc.py:628-634. -/
def SetV.sub {ρ α : Type} (self : SetV α) (B : FromIter ρ α (SetV α)) (other : Operand α) :
    Py (Ret (SetV α)) :=
  match other.asSet? B with
  | none => .ok .notImplemented
  | some o => do
    let o ← o
    let xs ← self.iter
    let r ← B.start
    let r ← feedIf B (notIn o) self.tail r xs
    pure (.val (← B.done r))

/-- `Set.__rsub__`, Lib/_collections_abc.py:636-642. -/
def SetV.rsub {ρ α : Type} (self : SetV α) (B : FromIter ρ α (SetV α)) (other : Operand α) :
    Py (Ret (SetV α)) :=
  match other.asSet? B with
  | none => .ok .notImplemented
  | some o => do
    let o ← o
    let xs ← o.iter
    let r ← B.start
    let r ← feedIf B (notIn self) o.tail r xs
    pure (.val (← B.done r))

/-- `Set.__xor__` and `__rxor__`, Lib/_collections_abc.py:644-651: `(self - other) | (other - self)`, where `minus a b`
is Python's `a - b` and `bor` its `|`, each dispatched on the operands' own classes. -/
def SetV.xor {ρ α δ γ : Type} (self : SetV α) (B : FromIter ρ α (SetV α)) (minus : SetV α → SetV α → Py δ)
    (bor : δ → δ → Py γ) (other : Operand α) : Py (Ret γ) :=
  match other.asSet? B with
  | none => .ok .notImplemented
  | some o => do
    let o ← o
    let a ← minus self o
    let b ← minus o self
    pure (.val (← bor a b))

/-! ### `Set._hash` and `frozenset_hash` -/

/-- Python `a ^ b` on arbitrary `int`, two's complement of infinite width. -/
def pyXor : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)

def hashMask : Nat := 2 ^ 64 - 1
def hashMax : Int := 2 ^ 63 - 1

/-- One round of the loop: `h ^= (hx ^ (hx << 16) ^ 89869747) * 3644798167; h &= MASK`,
Lib/_collections_abc.py:675-676. `& MASK` on a Python `int` is reduction mod `2**64`. -/
def hashRound (h : Nat) (hx : Int) : Nat :=
  (pyXor h ((pyXor (pyXor hx (hx * 2 ^ 16)) 89869747) * 3644798167) % (2 ^ 64 : Int)).toNat

/-- The rest of `Set._hash`, Lib/_collections_abc.py:677-684. -/
def hashFinish (h : Nat) : Int :=
  let h : Nat := h ^^^ ((h >>> 11) ^^^ (h >>> 25))
  let h : Nat := (h * 69069 + 907133923) % 2 ^ 64
  let h : Int := if (h : Int) > hashMax then (h : Int) - 2 ^ 64 else h
  if h = -1 then 590923713 else h

/-- The arithmetic of `Set._hash` for a set of `n` elements with the element hashes `hashes` in iteration order. -/
def setHash (n : Nat) (hashes : List Int) : Int :=
  hashFinish (hashes.foldl hashRound ((1927868237 * (n + 1)) % 2 ^ 64))

/-- `for x in self: hx = hash(x); ...`, Lib/_collections_abc.py:673-676. -/
def hashLoop {α : Type} (hash : α → Py Int) (tail : Option PyExc) : Nat → List α → Py Nat
  | h, [] => raiseTail tail h
  | h, x :: xs => do
    let hx ← hash x
    hashLoop hash tail (hashRound h hx) xs

/-- `Set._hash`, Lib/_collections_abc.py:653-684: `len(self)`, then the loop over `iter(self)` with the builtin
`hash()` of each element, which may raise (`TypeError` for an unhashable one). -/
def SetV.hash {α : Type} (self : SetV α) (hash : α → Py Int) : Py Int := do
  let n ← self.len
  let h := (1927868237 * (n + 1)) % 2 ^ 64
  let xs ← self.iter
  let h ← hashLoop hash self.tail h xs
  pure (hashFinish h)

/-- A slot of a C set table: `entry->hash` is 0 in a null slot, -1 in a dummy. -/
inductive Slot where
  | null
  | dummy
  | active (hash : Int)
  deriving Repr, DecidableEq

def Slot.hash : Slot → BitVec 64
  | .null => 0
  | .dummy => BitVec.ofInt 64 (-1)
  | .active h => BitVec.ofInt 64 h

/-- `_shuffle_bits`, Objects/setobject.c:954-957. -/
def shuffleBits (h : BitVec 64) : BitVec 64 :=
  ((h ^^^ 89869747#64) ^^^ (h <<< 16)) * 3644798167#64

def Slot.isNull : Slot → Bool | .null => true | _ => false
def Slot.isDummy : Slot → Bool | .dummy => true | _ => false
def Slot.isActive : Slot → Bool | .active _ => true | _ => false

/-- `frozenset_hash_impl`, Objects/setobject.c:973-1012, on the table: `fill` is the number of
non-null slots and `used` the number of active ones, so `mask + 1 - fill` is the number of null
slots and `fill - used` the number of dummies. -/
def frozensetHash (table : List Slot) : Int :=
  let nulls := (table.filter Slot.isNull).length
  let dummies := (table.filter Slot.isDummy).length
  let used := (table.filter Slot.isActive).length
  let h : BitVec 64 := table.foldl (fun h e => h ^^^ shuffleBits e.hash) 0
  let h := if nulls % 2 = 1 then h ^^^ shuffleBits 0 else h
  let h := if dummies % 2 = 1 then h ^^^ shuffleBits (BitVec.ofInt 64 (-1)) else h
  let h := h ^^^ (BitVec.ofNat 64 (used + 1) * 1927868237#64)
  let h := h ^^^ ((h >>> 11) ^^^ (h >>> 25))
  let h := h * 69069#64 + 907133923#64
  let h := if h = BitVec.ofInt 64 (-1) then 590923713#64 else h
  h.toInt

/-! ### MutableSet -/

/-- The primitives of a `MutableSet` subclass, with its `_from_iterable`. -/
structure MSet (σ ρ α : Type) where
  view : σ → SetV α
  add : σ → α → Py σ
  discard : σ → α → Py σ
  fromIter : FromIter ρ α (SetV α)

/-- `MutableSet.remove`, Lib/_collections_abc.py:714-718. -/
def MSet.remove {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) (value : α) : Py σ := do
  if !(← (M.view s).contains value) then throw (.keyError "~value")
  M.discard s value

/-- `MutableSet.pop`, Lib/_collections_abc.py:720-728. -/
def MSet.pop {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) : Py (α × σ) := do
  match ← (M.view s).iter with
  | [] =>
    -- `next(it)`, whose `StopIteration` becomes `KeyError`; another exception goes through
    match (M.view s).tail with
    | none => throw bareKeyError
    | some e => throw e
  | v :: _ =>
    let s' ← M.discard s v
    pure (v, s')

/-- `MutableSet.clear`, Lib/_collections_abc.py:730-736. -/
def MSet.clear {σ ρ α : Type} (M : MSet σ ρ α) : (fuel : Nat) → σ → Py σ
  | 0, _ => .error .modelFuel
  | fuel + 1, s =>
    match M.pop s with
    | .error e => if isKeyError e then .ok s else .error e
    | .ok (_, s') => M.clear fuel s'

/-- A loop calling `f` on each element of an iterator that may raise after its items. -/
def forAddT {σ α : Type} (f : σ → α → Py σ) (tail : Option PyExc) (s : σ) : List α → Py σ
  | [] => raiseTail tail s
  | x :: xs => do
    let s' ← f s x
    forAddT f tail s' xs

/-- `MutableSet.__ior__`, Lib/_collections_abc.py:738-741: `for value in it`, with no `isinstance` test. -/
def MSet.ior {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) (it : Operand α) : Py σ := do
  forAddT M.add it.tail s (← it.items)

/-- `x` when it is a value, else `k`. -/
def retOr {γ : Type} (x : Py (Ret γ)) (k : Py γ) : Py γ := do
  match ← x with
  | .val v => pure v
  | .notImplemented => k

/-- Python's binary operator, Objects/abstract.c:940-990 `binary_op1`, when the left operand's method gives `l` and
the right one's reflected method gives `r` (`none`: it has none); `rfirst` is the case where the right operand's class
is a proper subclass of the left one's with its own reflected method, which is then tried first. Both
`NotImplemented` is `err`. -/
def binaryOp {γ : Type} (l : Py (Ret γ)) (r : Option (Py (Ret γ))) (rfirst : Bool) (err : PyExc) : Py γ :=
  match r, rfirst with
  | some r, true => retOr r (retOr l (.error err))
  | some r, false => retOr l (retOr r (.error err))
  | none, _ => retOr l (.error err)

/-- `MutableSet.__iand__`, Lib/_collections_abc.py:743-746: `for value in (self - it): self.discard(value)`. The
subtraction is the operator: `Set.__sub__`, then `it.__rsub__(self)`, which `rsub` gives (`none`: it has none). -/
def MSet.iand {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) (it : Operand α) (rsub : Option (Py (Ret (SetV α))))
    (rfirst : Bool) : Py σ := do
  let d ← binaryOp ((M.view s).sub M.fromIter it) rsub rfirst
    (.typeError "~unsupported operand type(s) for -")
  forAddT M.discard d.tail s (← d.iter)

/-- One step of the `__ixor__` loop. -/
def MSet.toggle {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) (value : α) : Py σ := do
  if ← (M.view s).contains value then M.discard s value else M.add s value

/-- `MutableSet.__ixor__`, Lib/_collections_abc.py:748-759. `none` is `it is self`. A non-`Set` goes through
`self._from_iterable(it)` with no `isinstance(it, Iterable)` test, and the loop is over the set that made. -/
def MSet.ixor {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) (it : Option (Operand α)) (fuel : Nat) : Py σ :=
  match it with
  | none => M.clear fuel s
  | some (.set o) => do forAddT M.toggle o.tail s (← o.iter)
  | some (.iterable _ xs t) => do
    let o ← build M.fromIter xs t
    forAddT M.toggle o.tail s (← o.iter)

/-- `MutableSet.__isub__`, Lib/_collections_abc.py:761-767. `none` is `it is self`. -/
def MSet.isub {σ ρ α : Type} (M : MSet σ ρ α) (s : σ) (it : Option (Operand α)) (fuel : Nat) : Py σ :=
  match it with
  | none => M.clear fuel s
  | some it => do forAddT M.discard it.tail s (← it.items)

/-! ### Mapping and the views -/

/-- The primitives of a `Mapping` subclass. -/
structure MapV (K V : Type) where
  getitem : K → Py V
  iter : Py (List K)
  len : Py Nat
  /-- The exception of a `__next__` that raises after the keys. -/
  tail : Option PyExc := none
  /-- The class's own `__contains__`, when it overrides `Mapping.__contains__`. -/
  containsOverride : Option (K → Py Bool) := none

/-- `Mapping.get`, Lib/_collections_abc.py:792-797. -/
def MapV.get {K V : Type} (m : MapV K V) (key : K) (default : V) : Py V :=
  match m.getitem key with
  | .ok v => .ok v
  | .error e => if isKeyError e then .ok default else .error e

/-- `Mapping.__contains__`, Lib/_collections_abc.py:799-805. -/
def MapV.contains {K V : Type} (m : MapV K V) (key : K) : Py Bool :=
  match m.getitem key with
  | .ok _ => .ok true
  | .error e => if isKeyError e then .ok false else .error e

/-- `KeysView.__contains__`, Lib/_collections_abc.py:855-856: `key in self._mapping`, the mapping's own
`__contains__`, which is `Mapping.__contains__` unless the class overrides it. -/
def MapV.keyIn {K V : Type} (m : MapV K V) (key : K) : Py Bool :=
  match m.containsOverride with
  | some f => f key
  | none => m.contains key

/-- `for key in self._mapping: yield (key, self._mapping[key])`, ItemsView.__iter__,
Lib/_collections_abc.py:882-884, drained. No exception is caught. -/
def MapV.itemsOf {K V : Type} (m : MapV K V) : List K → Py (List (K × V))
  | [] => raiseTail m.tail []
  | k :: ks => do
    let v ← m.getitem k
    let rest ← m.itemsOf ks
    pure ((k, v) :: rest)

/-- `ItemsView.__iter__`. -/
def MapV.items {K V : Type} (m : MapV K V) : Py (List (K × V)) := do m.itemsOf (← m.iter)

/-- `for key in self._mapping: yield self._mapping[key]`, ValuesView.__iter__, Lib/_collections_abc.py:901-903,
drained. -/
def MapV.valuesOf {K V : Type} (m : MapV K V) : List K → Py (List V)
  | [] => raiseTail m.tail []
  | k :: ks => do
    let v ← m.getitem k
    let rest ← m.valuesOf ks
    pure (v :: rest)

/-- `ValuesView.__iter__`. -/
def MapV.values {K V : Type} (m : MapV K V) : Py (List V) := do m.valuesOf (← m.iter)

/-- The loop of `ValuesView.__contains__`, Lib/_collections_abc.py:895-899. -/
def MapV.valuesLoop {K V : Type} (m : MapV K V) (E : EqOps V) (value : V) : List K → Py Bool
  | [] => raiseTail m.tail false
  | k :: ks => do
    let v ← m.getitem k
    if ← E.same v value then return true
    m.valuesLoop E value ks

/-- `ValuesView.__contains__`, Lib/_collections_abc.py:894-899. -/
def MapV.valuesContain {K V : Type} (m : MapV K V) (E : EqOps V) (value : V) : Py Bool := do
  m.valuesLoop E value (← m.iter)

/-- An object as `key, value = item` sees it: Python/ceval.c:2359-2427 `_PyEval_UnpackIterable` with two targets. -/
inductive ItemArg (K V : Type) where
  /-- `iter()` refuses it: a type with neither `__iter__` nor `__getitem__`. -/
  | notIterable (tname : String)
  /-- `iter()` raises `e` otherwise. -/
  | iterFails (e : PyExc)
  /-- The iterator ends (`none`) or raises after no element. -/
  | zero (tail : Option PyExc)
  | one (k : K) (tail : Option PyExc)
  /-- Two elements, then the third `next()` ends (`none`) or raises. -/
  | two (k : K) (v : V) (tail : Option PyExc)
  /-- At least three elements; `size` is the length when the object is exactly a `list`, `tuple` or `dict`. -/
  | many (k : K) (v : V) (size : Option Nat)

/-- `key, value = item`, Python/ceval.c:2368-2427: the count read before the end is in "not enough values", and the
length only for an exact `list`, `tuple` or `dict` (:2413-2420). -/
def unpack2 {K V : Type} : ItemArg K V → Py (K × V)
  | .notIterable t => .error (.typeError s!"cannot unpack non-iterable {t} object")
  | .iterFails e => .error e
  | .zero none => .error (.valueError "not enough values to unpack (expected 2, got 0)")
  | .zero (some e) => .error e
  | .one _ none => .error (.valueError "not enough values to unpack (expected 2, got 1)")
  | .one _ (some e) => .error e
  | .two k v none => .ok (k, v)
  | .two _ _ (some e) => .error e
  | .many _ _ (some n) =>
    if n > 2 then .error (.valueError s!"too many values to unpack (expected 2, got {n})")
    else .error (.valueError "too many values to unpack (expected 2)")
  | .many _ _ none => .error (.valueError "too many values to unpack (expected 2)")

/-- `ItemsView.__contains__`, Lib/_collections_abc.py:873-880. The unpack is outside the `try`. -/
def MapV.itemsContain {K V : Type} (m : MapV K V) (E : EqOps V) (item : ItemArg K V) : Py Bool := do
  let (key, value) ← unpack2 item
  match m.getitem key with
  | .error e => if isKeyError e then .ok false else .error e
  | .ok v => E.same v value

/-- `dictitems_contains`, Objects/dictobject.c:7039-7056: an object that is not a tuple (`isTuple`, subclasses
included) of two is `False`. `getitem` stands for `PyDict_GetItemRef`. -/
def dictItemsContain {K V : Type} (m : MapV K V) (E : EqOps V) (isTuple : Bool) : ItemArg K V → Py Bool
  | .two k value none =>
    if !isTuple then .ok false
    else
      match m.getitem k with
      | .error e => if isKeyError e then .ok false else .error e
      | .ok v => E.same v value
  | _ => .ok false

/-- `MappingView.__repr__`, Lib/_collections_abc.py:841-842: `'{0.__class__.__name__}({0._mapping!r})'.format(self)`.
The fields are formatted left to right: the class name, then `repr(self._mapping)`, which may raise (also the
`TypeError` of a `__repr__` that returns a non-string). -/
def viewRepr (cls : String) (mappingRepr : Py String) : Py String := do
  let r ← mappingRepr
  pure s!"{cls}({r})"

/-- `d[k] = v` on a `dict` kept as its item list: an existing key keeps its position. -/
def dictSet {K V : Type} [DecidableEq K] (d : List (K × V)) (k : K) (v : V) : List (K × V) :=
  if d.any (fun p => p.1 = k) then d.map (fun p => if p.1 = k then (k, v) else p)
  else d ++ [(k, v)]

/-- `dict(m.items())`: `PyDict_MergeFromSeq2` (Objects/dictobject.c:4152-4220) over `ItemsView.__iter__`. Each item is
made (`self._mapping[key]`) and then inserted, which hashes the key (`hashKey`, which may raise) before the next item is
made. Key equality is `DecidableEq`, standing for hash and `__eq__` that agree. -/
def dictOfItems {K V : Type} [DecidableEq K] (hashKey : K → Py Unit) (m : MapV K V) :
    List (K × V) → List K → Py (List (K × V))
  | acc, [] => raiseTail m.tail acc
  | acc, k :: ks => do
    let v ← m.getitem k
    hashKey k
    dictOfItems hashKey m (dictSet acc k v) ks

/-- `Mapping.__eq__`, Lib/_collections_abc.py:819-822: `dict(self.items()) == dict(other.items())`: the left dict is
built in full before `other.items()` is iterated, and `dictEq` is the builtin comparison of the two dicts
(Objects/dictobject.c `dict_richcompare`). `none` is an `other` that is not a `Mapping`. -/
def mappingEq {K V : Type} [DecidableEq K] (hashKey : K → Py Unit)
    (dictEq : List (K × V) → List (K × V) → Py Bool) (self : MapV K V) (other : Option (MapV K V)) : Py (Ret Bool) :=
  match other with
  | none => .ok .notImplemented
  | some o => do
    let a ← dictOfItems hashKey self [] (← self.iter)
    let b ← dictOfItems hashKey o [] (← o.iter)
    pure (.val (← dictEq a b))

/-! ### MutableMapping -/

/-- The primitives of a `MutableMapping` subclass. -/
structure MMap (σ K V : Type) where
  view : σ → MapV K V
  setitem : σ → K → V → Py σ
  delitem : σ → K → Py σ

/-- `MutableMapping.pop(key)`, Lib/_collections_abc.py:930-943. `default = none` is the
`__marker`. -/
def MMap.pop {σ K V : Type} (M : MMap σ K V) (s : σ) (key : K) (default : Option V) :
    Py (V × σ) :=
  match (M.view s).getitem key with
  | .error e =>
    if isKeyError e then
      match default with
      | none => .error e
      | some d => .ok (d, s)
    else .error e
  | .ok value => do
    let s' ← M.delitem s key
    pure (value, s')

/-- `MutableMapping.popitem`, Lib/_collections_abc.py:945-955. -/
def MMap.popitem {σ K V : Type} (M : MMap σ K V) (s : σ) : Py ((K × V) × σ) := do
  match ← (M.view s).iter with
  | [] =>
    match (M.view s).tail with
    | none => throw bareKeyError
    | some e => throw e
  | key :: _ =>
    let value ← (M.view s).getitem key
    let s' ← M.delitem s key
    pure ((key, value), s')

/-- `MutableMapping.clear`, Lib/_collections_abc.py:957-963. -/
def MMap.clear {σ K V : Type} (M : MMap σ K V) : (fuel : Nat) → σ → Py σ
  | 0, _ => .error .modelFuel
  | fuel + 1, s =>
    match M.popitem s with
    | .error e => if isKeyError e then .ok s else .error e
    | .ok (_, s') => M.clear fuel s'

/-- The positional argument of `update`, as its three branches see it. -/
inductive UpdateArg (K V : Type) where
  /-- `isinstance(other, Mapping)`: its keys, `__getitem__` and iterator end. -/
  | mapping (m : MapV K V)
  /-- Not a `Mapping`. `hasKeys` is `hasattr(other, "keys")` (an exception other than `AttributeError` from the
  lookup propagates). With keys: `keys` is `other.keys()` iterated, `ktail` its end, `getitem` is `other[key]`.
  Without: `items` is `iter(other)`'s elements, each unpacked by `key, value = item`, and `tail` its end. -/
  | other (hasKeys : Py Bool) (keys : Py (List K)) (ktail : Option PyExc) (getitem : K → Py V)
      (items : Py (List (ItemArg K V))) (tail : Option PyExc)

/-- `for key in keys: self[key] = other[key]`. -/
def MMap.updateKeys {σ K V : Type} (M : MMap σ K V) (getitem : K → Py V) (tail : Option PyExc) (s : σ) :
    List K → Py σ
  | [] => raiseTail tail s
  | k :: ks => do
    let v ← getitem k
    let s' ← M.setitem s k v
    M.updateKeys getitem tail s' ks

/-- `for key, value in other: self[key] = value`, each item unpacked before its assignment. -/
def MMap.setPairs {σ K V : Type} (M : MMap σ K V) (tail : Option PyExc) (s : σ) : List (ItemArg K V) → Py σ
  | [] => raiseTail tail s
  | x :: xs => do
    let (k, v) ← unpack2 x
    let s' ← M.setitem s k v
    M.setPairs tail s' xs

/-- `for key, value in kwds.items(): self[key] = value`. -/
def MMap.setAll {σ K V : Type} (M : MMap σ K V) (s : σ) : List (K × V) → Py σ
  | [] => .ok s
  | (k, v) :: xs => do
    let s' ← M.setitem s k v
    M.setAll s' xs

/-- `MutableMapping.update(other, **kwds)`, Lib/_collections_abc.py:965-984. -/
def MMap.update {σ K V : Type} (M : MMap σ K V) (s : σ) (other : UpdateArg K V)
    (kwds : List (K × V)) : Py σ := do
  let s' ← match other with
    | .mapping m => do M.updateKeys m.getitem m.tail s (← m.iter)
    | .other hasKeys keys ktail getitem items tail => do
      if ← hasKeys then M.updateKeys getitem ktail s (← keys)
      else M.setPairs tail s (← items)
  M.setAll s' kwds

/-- `MutableMapping.setdefault`, Lib/_collections_abc.py:986-992. -/
def MMap.setdefault {σ K V : Type} (M : MMap σ K V) (s : σ) (key : K) (default : V) :
    Py (V × σ) :=
  match (M.view s).getitem key with
  | .ok v => .ok (v, s)
  | .error e =>
    if isKeyError e then do
      let s' ← M.setitem s key default
      pure (default, s')
    else .error e

/-! ### `ByteString` deprecation -/

/-- `warnings._deprecated("collections.abc.ByteString", remove=(3, 17))` on 3.15, Lib/_py_warnings.py:873, 876-892:
the formatted `_DEPRECATED_MSG`, warned with `DeprecationWarning`. -/
def byteStringDeprecated : String :=
  "'collections.abc.ByteString' is deprecated and slated for removal in Python 3.17"

/-- The action of the warnings filter that matches the warning. Scope: `default`, `once` and `module` differ from
`always` only through the registry of earlier warnings, which is not modelled. -/
inductive WarnAction where
  | ignore
  | always
  | error
  deriving Repr, DecidableEq

/-- A warning shown: its category and message. -/
structure Warned where
  category : String
  message : String
  deriving Repr, DecidableEq

/-- `warnings._deprecated("collections.abc.ByteString", remove=(3, 17))` under the filter's action: the warning shown,
nothing, or the warning raised. -/
def byteStringWarn (act : WarnAction) : List Warned × Py Unit :=
  match act with
  | .ignore => ([], .ok ())
  | .always => ([⟨"DeprecationWarning", byteStringDeprecated⟩], .ok ())
  | .error => ([], .error (.named "DeprecationWarning" byteStringDeprecated))

/-- `_DeprecateByteStringMeta.__new__`, Lib/_collections_abc.py:1070-1078: the deprecation warning for any class name
but `ByteString`, then `ABCMeta.__new__` (`make`), which does not run when the warning is an exception. -/
def byteStringMetaNew {γ : Type} (act : WarnAction) (name : String) (make : Py γ) : List Warned × Py γ :=
  if name != "ByteString" then
    let (ws, w) := byteStringWarn act
    (ws, do w; make)
  else ([], make)

/-- `_DeprecateByteStringMeta.__instancecheck__`, Lib/_collections_abc.py:1080-1087: the warning every time, then
`ABCMeta.__instancecheck__` (`answer`). -/
def byteStringInstanceCheck (act : WarnAction) (answer : Py Bool) : List Warned × Py Bool :=
  let (ws, w) := byteStringWarn act
  (ws, do w; answer)

/-- Reading an attribute of the module, Lib/_collections_abc.py:1175-1183: `loaded` says that `ByteString` is in the
module's globals, where the normal lookup finds it and `__getattr__` is not called. The result is the warnings shown,
whether `ByteString` is in the globals afterwards, and the outcome; the name is put back only after the warning.
`attr` is a name whose `repr` is itself in single quotes (no quote, backslash or unprintable character). -/
def moduleGetattr (act : WarnAction) (loaded : Bool) (attr : String) : List Warned × Bool × Py Unit :=
  if attr == "ByteString" then
    if loaded then ([], true, .ok ())
    else
      match act with
      | .ignore => ([], true, .ok ())
      | .always => ([⟨"DeprecationWarning", byteStringDeprecated⟩], true, .ok ())
      | .error => ([], false, .error (.named "DeprecationWarning" byteStringDeprecated))
  else ([], loaded, .error (.named "AttributeError" s!"module 'collections.abc' has no attribute '{attr}'"))

end PyLean.CoreLibs.CollAbc
