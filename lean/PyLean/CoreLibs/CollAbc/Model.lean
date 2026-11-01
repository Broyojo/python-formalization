import PyLean.Core

/-!
`Lib/_collections_abc.py` (CPython 3.14.7), mirrored.

Each mixin is a generic algorithm over the primitives a concrete subclass
supplies, so the primitives are parameters: the structures `Seq`, `MSeq`, `SetV`,
`MSet`, `MapV`, `MMap` and `Gen` below hold them. A primitive returns `Py`, because
a subclass may raise from any of them, and the order in which they are called is
observable. Mutation is explicit state passing over an abstract `σ`.

Identity and equality of elements are abstract (`EqOps`): the source's
`v is value or v == value` tests identity first and only then calls `__eq__`,
which may raise.

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

/-- `raise KeyError` without arguments: `str(e)` is empty. -/
def bareKeyError : PyExc := .keyError ""

/-- Abstract identity and equality of elements. -/
structure EqOps (α : Type) where
  is_ : α → α → Bool
  eq : α → α → Py Bool

/-- `v is value or v == value` (Lib/_collections_abc.py:896, 1027, 1053, 1060). -/
def EqOps.same {α : Type} (E : EqOps α) (v w : α) : Py Bool :=
  if E.is_ v w then pure true else E.eq v w

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

/-- The ABCs with a `__subclasshook__`, with the method lists of their hooks,
Lib/_collections_abc.py:131, 146, 189, 207, 228, 275, 295, 316, 348, 395, 414, 429,
442, 457, 540, and the `Hashable` hook at :131. -/
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

/-- What calling an abstract stub does. -/
inductive Stub where
  | returnsInt (n : Int)
  | returnsBool (b : Bool)
  /-- A generator that yields these `None`s and stops. -/
  | yieldsNones (n : Nat)
  | raises (cls : String)
  deriving Repr, DecidableEq

/-- The body of each abstract method, by inventory name. -/
def stubBody : String → Option Stub
  | "Hashable.__hash__" => some (.returnsInt 0)                -- :126
  | "Sized.__len__" => some (.returnsInt 0)                    -- :409
  | "Container.__contains__" => some (.returnsBool false)      -- :424
  | "Callable.__call__" => some (.returnsBool false)           -- :535
  | "Awaitable.__await__" => some (.yieldsNones 1)             -- :141
  | "Iterable.__iter__" => some (.yieldsNones 0)               -- :289-290
  | "Reversible.__reversed__" => some (.yieldsNones 0)         -- :342-343
  | "Iterator.__next__" => some (.raises "StopIteration")      -- :308
  | "Generator.send" => some (.raises "StopIteration")         -- :367
  | "Coroutine.send" => some (.raises "StopIteration")         -- :161
  | "AsyncIterator.__anext__" => some (.raises "StopAsyncIteration")  -- :220
  | "AsyncGenerator.asend" => some (.raises "StopAsyncIteration")     -- :247
  | "AsyncIterable.__aiter__" => some (.raises "TypeError")    -- :202, AsyncIterator() is abstract
  | "Buffer.__buffer__" => some (.raises "NotImplementedError")  -- :452
  | "MutableSet.add" => some (.raises "NotImplementedError")     -- :707
  | "MutableSet.discard" => some (.raises "NotImplementedError") -- :712
  | "Mapping.__getitem__" => some (.raises "KeyError")           -- :790
  | "MutableMapping.__setitem__" => some (.raises "KeyError")    -- :921
  | "MutableMapping.__delitem__" => some (.raises "KeyError")    -- :925
  | "Sequence.__getitem__" => some (.raises "IndexError")        -- :1013
  | "MutableSequence.__setitem__" => some (.raises "IndexError") -- :1115
  | "MutableSequence.__delitem__" => some (.raises "IndexError") -- :1119
  | "MutableSequence.insert" => some (.raises "IndexError")      -- :1124
  | _ => none

/-! ### Generator, Coroutine, AsyncGenerator mixins -/

/-- An exception argument of `throw(typ, val, tb)`. -/
inductive ExcArg where
  | cls (name : String)
  | inst (name : String)
  /-- Something that is not an exception. -/
  | other
  deriving Repr, DecidableEq

/-- What `throw` ended up raising: the class, and whether `with_traceback` ran. -/
structure Raised where
  name : String
  tracebackSet : Bool
  deriving Repr, DecidableEq

/-- `raise x`. -/
def raiseArg (x : ExcArg) (tb : Bool) : Except String Raised :=
  match x with
  | .cls n | .inst n => .ok ⟨n, tb⟩
  | .other => .error "TypeError"

/-- The body of `Generator.throw`, `Coroutine.throw` and `AsyncGenerator.athrow`
(Lib/_collections_abc.py:374-380, 168-174, 254-260). The error side is the class
name of an exception that is not the requested one. -/
def throwBody (typ : ExcArg) (val : Option ExcArg) (tb : Bool) : Except String Raised :=
  match val with
  | none =>
    if !tb then raiseArg typ false
    else
      -- `val = typ()`, then `val.with_traceback(tb)`
      match typ with
      | .cls n => .ok ⟨n, true⟩
      | .inst _ | .other => .error "TypeError"
  | some v =>
    if tb then
      match v with
      | .inst n => .ok ⟨n, true⟩
      -- `ValueError.with_traceback(tb)` is an unbound descriptor call
      | .cls _ => .error "TypeError"
      | .other => .error "AttributeError"
    else raiseArg v false

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
  /-- `self.throw(GeneratorExit)`. -/
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
Lib/_collections_abc.py:385-390, 179-184, 265-270. Returns `None`. -/
def Gen.close {σ V : Type} (G : Gen σ V) (msg : String) (s : σ) : Py Unit × σ :=
  match G.throwExit s with
  | (.yielded _, s') => (.error (.named "RuntimeError" msg), s')
  | (.stopped _, s') => (.ok (), s')
  | (.raised e, s') => (if isGeneratorExit e then .ok () else .error e, s')

def genCloseMsg := "generator ignored GeneratorExit"
def coroCloseMsg := "coroutine ignored GeneratorExit"
def asyncCloseMsg := "asynchronous generator ignored GeneratorExit"

/-- The builtin `generator.close()` after the frame has started and not finished,
Objects/genobject.c `gen_close`: a value returned while closing is the result. -/
def builtinClose {σ V : Type} (G : Gen σ V) (s : σ) : Py (Option V) × σ :=
  match G.throwExit s with
  | (.yielded _, s') => (.error (.named "RuntimeError" genCloseMsg), s')
  | (.stopped v, s') => (.ok (some v), s')
  | (.raised e, s') => (if isGeneratorExit e then .ok none else .error e, s')

/-! ### Callable -/

/-- `Callable[...]`'s first argument, as `_is_param_expr` and `__new__` see it. -/
inductive CallArg where
  | tupleOrList (items : List String)
  | ellipsis
  /-- A `typing.ParamSpec` or a `Concatenate` alias. -/
  | paramExpr (repr : String)
  /-- Anything else. -/
  | other (repr : String)
  deriving Repr, DecidableEq

/-- `_is_param_expr(obj)`, Lib/_collections_abc.py:516-526. `list` is a param expression;
a tuple is not. The Boolean says whether `tupleOrList` here is a list. -/
def isParamExpr (isList : Bool) : CallArg → Bool
  | .ellipsis => true
  | .tupleOrList _ => isList
  | .paramExpr _ => true
  | .other _ => false

/-- `_CallableGenericAlias.__new__`, Lib/_collections_abc.py:473-483: the flattened
`__args__`. The first argument is the shape `(t_args, t_result)` when it is a 2-tuple. -/
def callableNew (args : Option (CallArg × String)) : Py (List String) :=
  match args with
  | none => .error (.typeError "Callable must be used as Callable[[arg, ...], result].")
  | some (.tupleOrList items, r) => .ok (items ++ [r])
  | some (a, r) =>
    if isParamExpr false a then
      .ok [match a with | .ellipsis => "..." | .paramExpr p => p | _ => "", r]
    else
      .error (.typeError s!"~Expected a list of types, an ellipsis, ParamSpec, or Concatenate.")

/-- `_CallableGenericAlias.__repr__`, Lib/_collections_abc.py:485-491, on the `__args__`,
each already through `type_repr`. The default `GenericAlias` repr applies to `(..., r)`. -/
def callableRepr (args : List String) (paramExprFirst : Bool) : String :=
  match args, paramExprFirst with
  | [a, r], true => s!"collections.abc.Callable[{a}, {r}]"
  | _, _ =>
    s!"collections.abc.Callable[[{", ".intercalate args.dropLast}], {(args.getLast? |>.getD "")}]"

/-- `_CallableGenericAlias.__reduce__`, Lib/_collections_abc.py:493-497: the argument the
reconstruction gets; the flat form only for the single-param-expression case. -/
def callableReduceArgs (args : List String) (paramExprFirst : Bool) : CallArg × String :=
  match args, paramExprFirst with
  | [a, r], true => (if a = "..." then .ellipsis else .paramExpr a, r)
  | _, _ => (.tupleOrList args.dropLast, (args.getLast? |>.getD ""))

/-- An entry of `new_args` in `_CallableGenericAlias.__getitem__`. -/
inductive SubstArg where
  | typ (repr : String)
  /-- `args[0]` from something like `Z[[int, str, bool]]` (PEP 612). -/
  | seq (items : List String)
  deriving Repr, DecidableEq

def SubstArg.repr : SubstArg → String
  | .typ r => r
  | .seq _ => ""

/-- `_CallableGenericAlias.__getitem__`, Lib/_collections_abc.py:499-514, after the
inherited substitution produced `new_args`: `__args__` of the result. -/
def callableGetitem (newArgs : List SubstArg) : Py (List String) :=
  match newArgs with
  | [.seq items, .typ r] => callableNew (some (.tupleOrList items, r))
  | .seq _ :: _ =>
    .error (.typeError "Callable must be used as Callable[[arg, ...], result].")
  | _ =>
    let names := newArgs.map SubstArg.repr
    callableNew (some (.tupleOrList names.dropLast, names.getLast?.getD ""))

/-! ### Sequence -/

/-- The primitives of a `Sequence` subclass. -/
structure Seq (α : Type) where
  getitem : Int → Py α
  len : Py Nat

/-- `Sequence.__iter__`, Lib/_collections_abc.py:1015-1023, drained. An `IndexError`
from `self[i]` ends the iteration; anything else propagates. -/
def Seq.iterFrom {α : Type} (s : Seq α) : (fuel : Nat) → Int → Py (List α)
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    match s.getitem i with
    | .error e => if isIndexError e then .ok [] else .error e
    | .ok v => do
      let rest ← s.iterFrom fuel (i + 1)
      pure (v :: rest)

/-- `Sequence.__contains__`, Lib/_collections_abc.py:1025-1029, over `__iter__`. -/
def Seq.containsFrom {α : Type} (s : Seq α) (E : EqOps α) (value : α) :
    (fuel : Nat) → Int → Py Bool
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    match s.getitem i with
    | .error e => if isIndexError e then .ok false else .error e
    | .ok v => do
      if ← E.same v value then return true
      s.containsFrom E value fuel (i + 1)

/-- `Sequence.count`, Lib/_collections_abc.py:1058-1060. -/
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

/-- The loop `for i in reversed(range(n)): yield self[i]`, from `i = n - 1` down. -/
def Seq.reversedFrom {α : Type} (s : Seq α) : Nat → Py (List α)
  | 0 => .ok []
  | n + 1 => do
    let v ← s.getitem n
    let rest ← s.reversedFrom n
    pure (v :: rest)

/-- `Sequence.__reversed__`, Lib/_collections_abc.py:1031-1033. -/
def Seq.reversed {α : Type} (s : Seq α) : Py (List α) := do
  let n ← s.len
  s.reversedFrom n

/-- The `while` loop of `Sequence.index`, Lib/_collections_abc.py:1048-1056. -/
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
Lib/_collections_abc.py:1035-1056. `start=None` and non-`int` arguments fall through to
`__getitem__` and to `<`, which is the subclass's business. -/
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

/-- `MutableSequence.append`, Lib/_collections_abc.py:1126-1128. -/
def MSeq.append {σ α : Type} (M : MSeq σ α) (s : σ) (v : α) : Py σ := do
  M.insert s (← M.len s : Nat) v

/-- `MutableSequence.pop`, Lib/_collections_abc.py:1152-1158. -/
def MSeq.pop {σ α : Type} (M : MSeq σ α) (s : σ) (index : Int := -1) : Py (α × σ) := do
  let v ← M.getitem s index
  let s' ← M.delitem s index
  pure (v, s')

/-- `MutableSequence.clear`, Lib/_collections_abc.py:1130-1136. -/
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

/-- `MutableSequence.reverse`, Lib/_collections_abc.py:1138-1142. -/
def MSeq.reverse {σ α : Type} (M : MSeq σ α) (s : σ) : Py σ := do
  let n ← M.len s
  M.swapLoop n (n / 2) 0 s

/-- `for v in values: self.append(v)`. -/
def MSeq.extendList {σ α : Type} (M : MSeq σ α) (s : σ) : List α → Py σ
  | [] => .ok s
  | v :: vs => do
    let s' ← M.append s v
    M.extendList s' vs

/-- `MutableSequence.extend(values)`, Lib/_collections_abc.py:1144-1150, and
`MutableSequence.__iadd__`, :1166-1168. `none` is `values is self`, which first takes
`list(values)` through `Sequence.__iter__`. -/
def MSeq.extend {σ α : Type} (M : MSeq σ α) (s : σ) (values : Option (List α)) (fuel : Nat) :
    Py σ := do
  match values with
  | some vs => M.extendList s vs
  | none =>
    let vs ← (M.view s).iterFrom fuel 0
    M.extendList s vs

/-- `MutableSequence.remove`, Lib/_collections_abc.py:1160-1164. -/
def MSeq.remove {σ α : Type} (M : MSeq σ α) (E : EqOps α) (s : σ) (value : α) (fuel : Nat) :
    Py σ := do
  let i ← (M.view s).index E value 0 none fuel
  M.delitem s i

/-! ### Set -/

/-- The primitives of a `Set` subclass. Iteration is one finite pass; an `iter` that
raises models a failing `__iter__` or `__next__`. -/
structure SetV (α : Type) where
  len : Py Nat
  iter : Py (List α)
  contains : α → Py Bool

/-- The other operand of a set operator, as `isinstance` sees it. -/
inductive Operand (α : Type) where
  | set (s : SetV α)
  | iterable (xs : Py (List α))
  | other

/-- `for elem in xs: if elem not in other: return False`, then `return True`. -/
def allIn {α : Type} (contains : α → Py Bool) : List α → Py Bool
  | [] => .ok true
  | x :: xs => do
    if ← contains x then allIn contains xs else return false

/-- `Set.__le__`, Lib/_collections_abc.py:562-570. -/
def SetV.le {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) > (← o.len) then return .val false
    let xs ← self.iter
    return .val (← allIn o.contains xs)
  | _ => .ok .notImplemented

/-- `Set.__ge__`, Lib/_collections_abc.py:582-590. -/
def SetV.ge {α : Type} (self : SetV α) : Operand α → Py (Ret Bool)
  | .set o => do
    if (← self.len) < (← o.len) then return .val false
    let xs ← o.iter
    return .val (← allIn self.contains xs)
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

/-- `value for value in xs if keep(value)`, consumed by the constructor. -/
def filterPy {α : Type} (keep : α → Py Bool) : List α → Py (List α)
  | [] => .ok []
  | x :: xs => do
    let k ← keep x
    let rest ← filterPy keep xs
    pure (if k then x :: rest else rest)

/-- The elements of an operand when `isinstance(other, Iterable)`. -/
def Operand.items? {α : Type} : Operand α → Option (Py (List α))
  | .set s => some s.iter
  | .iterable xs => some xs
  | .other => none

/-- `Set.__and__` and `__rand__`, Lib/_collections_abc.py:606-611. `fromIter` is
`_from_iterable`. -/
def SetV.and {α β : Type} (self : SetV α) (fromIter : List α → β) (other : Operand α) :
    Py (Ret β) :=
  match other.items? with
  | none => .ok .notImplemented
  | some xs => do
    let xs ← xs
    let kept ← filterPy self.contains xs
    pure (.val (fromIter kept))

/-- `Set.isdisjoint`, Lib/_collections_abc.py:613-618. -/
def SetV.isdisjoint {α : Type} (self : SetV α) (other : Operand α) : Py Bool :=
  match other.items? with
  | none => .error (.typeError "~object is not iterable")
  | some xs => do
    let xs ← xs
    let rec go : List α → Py Bool
      | [] => .ok true
      | x :: rest => do
        if ← self.contains x then return false else go rest
    go xs

/-- `Set.__or__` and `__ror__`, Lib/_collections_abc.py:620-626. -/
def SetV.or {α β : Type} (self : SetV α) (fromIter : List α → β) (other : Operand α) :
    Py (Ret β) :=
  match other.items? with
  | none => .ok .notImplemented
  | some xs => do
    let ys ← self.iter
    let xs ← xs
    pure (.val (fromIter (ys ++ xs)))

/-- `isinstance(other, Set)`, else `other = self._from_iterable(other)`, shared by
`__sub__`, `__rsub__` and `__xor__`. -/
def Operand.asSet? {α : Type} (fromIter : List α → SetV α) : Operand α → Option (Py (SetV α))
  | .set s => some (.ok s)
  | .iterable xs => some (do pure (fromIter (← xs)))
  | .other => none

/-- `value for value in xs if value not in s`. -/
def notIn {α : Type} (s : SetV α) (xs : List α) : Py (List α) :=
  filterPy (fun x => do pure (!(← s.contains x))) xs

/-- `Set.__sub__`, Lib/_collections_abc.py:628-634. -/
def SetV.sub {α : Type} (self : SetV α) (fromIter : List α → SetV α) (other : Operand α) :
    Py (Ret (SetV α)) :=
  match other.asSet? fromIter with
  | none => .ok .notImplemented
  | some o => do
    let o ← o
    let xs ← self.iter
    pure (.val (fromIter (← notIn o xs)))

/-- `Set.__rsub__`, Lib/_collections_abc.py:636-642. -/
def SetV.rsub {α : Type} (self : SetV α) (fromIter : List α → SetV α) (other : Operand α) :
    Py (Ret (SetV α)) :=
  match other.asSet? fromIter with
  | none => .ok .notImplemented
  | some o => do
    let o ← o
    let xs ← o.iter
    pure (.val (fromIter (← notIn self xs)))

/-- `Set.__xor__` and `__rxor__`, Lib/_collections_abc.py:644-651:
`(self - other) | (other - self)`. -/
def SetV.xor {α : Type} (self : SetV α) (fromIter : List α → SetV α) (other : Operand α) :
    Py (Ret (SetV α)) :=
  match other.asSet? fromIter with
  | none => .ok .notImplemented
  | some o => do
    let o ← o
    let xs ← self.iter
    let a ← notIn o xs
    let ys ← o.iter
    let b ← notIn self ys
    let aSet := fromIter a
    let bSet := fromIter b
    let aItems ← aSet.iter
    let bItems ← bSet.iter
    pure (.val (fromIter (aItems ++ bItems)))

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
Lib/_collections_abc.py:674-676. `& MASK` on a Python `int` is reduction mod `2**64`. -/
def hashRound (h : Nat) (hx : Int) : Nat :=
  (pyXor h ((pyXor (pyXor hx (hx * 2 ^ 16)) 89869747) * 3644798167) % (2 ^ 64 : Int)).toNat

/-- The rest of `Set._hash`, Lib/_collections_abc.py:677-684. -/
def hashFinish (h : Nat) : Int :=
  let h : Nat := h ^^^ ((h >>> 11) ^^^ (h >>> 25))
  let h : Nat := (h * 69069 + 907133923) % 2 ^ 64
  let h : Int := if (h : Int) > hashMax then (h : Int) - 2 ^ 64 else h
  if h = -1 then 590923713 else h

/-- `Set._hash`, Lib/_collections_abc.py:653-684, for a set of `n` elements with the
element hashes `hashes` in iteration order. -/
def setHash (n : Nat) (hashes : List Int) : Int :=
  hashFinish (hashes.foldl hashRound ((1927868237 * (n + 1)) % 2 ^ 64))

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

/-- `_shuffle_bits`, Objects/setobject.c:763-766. -/
def shuffleBits (h : BitVec 64) : BitVec 64 :=
  ((h ^^^ 89869747#64) ^^^ (h <<< 16)) * 3644798167#64

def Slot.isNull : Slot → Bool | .null => true | _ => false
def Slot.isDummy : Slot → Bool | .dummy => true | _ => false
def Slot.isActive : Slot → Bool | .active _ => true | _ => false

/-- `frozenset_hash_impl`, Objects/setobject.c:779-818, on the table: `fill` is the number of
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

/-- The primitives of a `MutableSet` subclass. -/
structure MSet (σ α : Type) where
  view : σ → SetV α
  add : σ → α → Py σ
  discard : σ → α → Py σ
  fromIter : List α → SetV α

/-- `MutableSet.remove`, Lib/_collections_abc.py:714-718. -/
def MSet.remove {σ α : Type} (M : MSet σ α) (s : σ) (value : α) : Py σ := do
  if !(← (M.view s).contains value) then throw (.keyError "~value")
  M.discard s value

/-- `MutableSet.pop`, Lib/_collections_abc.py:720-728. -/
def MSet.pop {σ α : Type} (M : MSet σ α) (s : σ) : Py (α × σ) := do
  match ← (M.view s).iter with
  | [] => throw bareKeyError
  | v :: _ =>
    let s' ← M.discard s v
    pure (v, s')

/-- `MutableSet.clear`, Lib/_collections_abc.py:730-736. -/
def MSet.clear {σ α : Type} (M : MSet σ α) : (fuel : Nat) → σ → Py σ
  | 0, _ => .error .modelFuel
  | fuel + 1, s =>
    match M.pop s with
    | .error e => if isKeyError e then .ok s else .error e
    | .ok (_, s') => M.clear fuel s'

def forAdd {σ α : Type} (f : σ → α → Py σ) (s : σ) : List α → Py σ
  | [] => .ok s
  | x :: xs => do
    let s' ← f s x
    forAdd f s' xs

/-- `MutableSet.__ior__`, Lib/_collections_abc.py:738-741. -/
def MSet.ior {σ α : Type} (M : MSet σ α) (s : σ) (it : Operand α) : Py σ :=
  match it.items? with
  | none => .error (.typeError "~object is not iterable")
  | some xs => do forAdd M.add s (← xs)

/-- `MutableSet.__iand__`, Lib/_collections_abc.py:743-746: `for value in (self - it)`. A
non-iterable `it` makes `self - it` raise the operator's `TypeError`. -/
def MSet.iand {σ α : Type} (M : MSet σ α) (s : σ) (it : Operand α) : Py σ := do
  match ← (M.view s).sub M.fromIter it with
  | .notImplemented => throw (.typeError "~unsupported operand type(s) for -")
  | .val d => forAdd M.discard s (← d.iter)

/-- One step of the `__ixor__` loop. -/
def MSet.toggle {σ α : Type} (M : MSet σ α) (s : σ) (value : α) : Py σ := do
  if ← (M.view s).contains value then M.discard s value else M.add s value

/-- `MutableSet.__ixor__`, Lib/_collections_abc.py:748-759. `none` is `it is self`. -/
def MSet.ixor {σ α : Type} (M : MSet σ α) (s : σ) (it : Option (Operand α)) (fuel : Nat) :
    Py σ :=
  match it with
  | none => M.clear fuel s
  | some (.set o) => do forAdd M.toggle s (← o.iter)
  | some (.iterable xs) => do forAdd M.toggle s (← (M.fromIter (← xs)).iter)
  | some .other => .error (.typeError "~object is not iterable")

/-- `MutableSet.__isub__`, Lib/_collections_abc.py:761-767. `none` is `it is self`. -/
def MSet.isub {σ α : Type} (M : MSet σ α) (s : σ) (it : Option (Operand α)) (fuel : Nat) :
    Py σ :=
  match it with
  | none => M.clear fuel s
  | some it =>
    match it.items? with
    | none => .error (.typeError "~object is not iterable")
    | some xs => do forAdd M.discard s (← xs)

/-! ### Mapping and the views -/

/-- The primitives of a `Mapping` subclass. -/
structure MapV (K V : Type) where
  getitem : K → Py V
  iter : Py (List K)
  len : Py Nat

/-- `Mapping.get`, Lib/_collections_abc.py:792-797. -/
def MapV.get {K V : Type} (m : MapV K V) (key : K) (default : V) : Py V :=
  match m.getitem key with
  | .ok v => .ok v
  | .error e => if isKeyError e then .ok default else .error e

/-- `Mapping.__contains__`, Lib/_collections_abc.py:799-805, also
`KeysView.__contains__`, :854-855. -/
def MapV.contains {K V : Type} (m : MapV K V) (key : K) : Py Bool :=
  match m.getitem key with
  | .ok _ => .ok true
  | .error e => if isKeyError e then .ok false else .error e

/-- `for key in self._mapping: yield (key, self._mapping[key])`, ItemsView.__iter__,
Lib/_collections_abc.py:881-883, drained. -/
def MapV.itemsOf {K V : Type} (m : MapV K V) : List K → Py (List (K × V))
  | [] => .ok []
  | k :: ks => do
    let v ← m.getitem k
    let rest ← m.itemsOf ks
    pure ((k, v) :: rest)

/-- `ItemsView.__iter__`. -/
def MapV.items {K V : Type} (m : MapV K V) : Py (List (K × V)) := do m.itemsOf (← m.iter)

/-- `ValuesView.__iter__`, Lib/_collections_abc.py:900-902, drained. -/
def MapV.values {K V : Type} (m : MapV K V) : Py (List V) := do
  let it ← m.items
  pure (it.map Prod.snd)

/-- `ValuesView.__contains__`, Lib/_collections_abc.py:893-898. -/
def MapV.valuesContain {K V : Type} (m : MapV K V) (E : EqOps V) (value : V) : Py Bool := do
  let rec go : List K → Py Bool
    | [] => .ok false
    | k :: ks => do
      let v ← m.getitem k
      if ← E.same v value then return true
      go ks
  go (← m.iter)

/-- The item as `key, value = item` sees it. -/
inductive ItemArg (K V : Type) where
  /-- An iterable of exactly two elements; `tuple` says whether it is a tuple. -/
  | pair (k : K) (v : V) (tuple : Bool)
  /-- An iterable of `n ≠ 2` elements. -/
  | wrongLen (n : Nat) (tuple : Bool)
  /-- Not iterable. -/
  | notIterable
  deriving Repr, DecidableEq

/-- `ItemsView.__contains__`, Lib/_collections_abc.py:872-879. The unpack is outside the
`try`, so a non-pair raises. -/
def MapV.itemsContain {K V : Type} (m : MapV K V) (E : EqOps V) : ItemArg K V → Py Bool
  | .notIterable => .error (.typeError "~cannot unpack non-iterable object")
  | .wrongLen n _ =>
    if n < 2 then .error (.valueError s!"not enough values to unpack (expected 2, got {n})")
    else .error (.valueError s!"too many values to unpack (expected 2, got {n})")
  | .pair k value _ =>
    match m.getitem k with
    | .error e => if isKeyError e then .ok false else .error e
    | .ok v => E.same v value

/-- `dictitems_contains`, Objects/dictobject.c: a non-tuple or a tuple of the wrong
length is `False`. `getitem` stands for `PyDict_GetItemRef`. -/
def dictItemsContain {K V : Type} (m : MapV K V) (E : EqOps V) : ItemArg K V → Py Bool
  | .notIterable | .wrongLen .. | .pair _ _ false => .ok false
  | .pair k value true =>
    match m.getitem k with
    | .error e => if isKeyError e then .ok false else .error e
    | .ok v => E.same v value

/-- `MappingView.__repr__`, Lib/_collections_abc.py:840-841. -/
def viewRepr (cls mappingRepr : String) : String := s!"{cls}({mappingRepr})"

/-- The `Set`-mixin primitives of `KeysView(m)`, Lib/_collections_abc.py:846-858. -/
def MapV.keysView {K V : Type} (m : MapV K V) : SetV K := ⟨m.len, m.iter, m.contains⟩

/-! ### MutableMapping -/

/-- The primitives of a `MutableMapping` subclass. -/
structure MMap (σ K V : Type) where
  view : σ → MapV K V
  setitem : σ → K → V → Py σ
  delitem : σ → K → Py σ

/-- `MutableMapping.pop(key)`, Lib/_collections_abc.py:929-942. `default = none` is the
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

/-- `MutableMapping.popitem`, Lib/_collections_abc.py:944-954. -/
def MMap.popitem {σ K V : Type} (M : MMap σ K V) (s : σ) : Py ((K × V) × σ) := do
  match ← (M.view s).iter with
  | [] => throw bareKeyError
  | key :: _ =>
    let value ← (M.view s).getitem key
    let s' ← M.delitem s key
    pure ((key, value), s')

/-- `MutableMapping.clear`, Lib/_collections_abc.py:956-962. -/
def MMap.clear {σ K V : Type} (M : MMap σ K V) : (fuel : Nat) → σ → Py σ
  | 0, _ => .error .modelFuel
  | fuel + 1, s =>
    match M.popitem s with
    | .error e => if isKeyError e then .ok s else .error e
    | .ok (_, s') => M.clear fuel s'

/-- The argument of `update`, as the three branches see it. -/
inductive UpdateArg (K V : Type) where
  /-- `isinstance(other, Mapping)`, or `hasattr(other, "keys")`: its keys and values. -/
  | mapping (m : MapV K V)
  /-- Pairs from an iterable. -/
  | pairs (xs : List (K × V))

/-- `for key in other: self[key] = other[key]`. -/
def MMap.updateKeys {σ K V : Type} (M : MMap σ K V) (other : MapV K V) (s : σ) :
    List K → Py σ
  | [] => .ok s
  | k :: ks => do
    let v ← other.getitem k
    let s' ← M.setitem s k v
    M.updateKeys other s' ks

/-- `for key, value in other: self[key] = value`. -/
def MMap.setAll {σ K V : Type} (M : MMap σ K V) (s : σ) : List (K × V) → Py σ
  | [] => .ok s
  | (k, v) :: xs => do
    let s' ← M.setitem s k v
    M.setAll s' xs

/-- `MutableMapping.update(other, **kwds)`, Lib/_collections_abc.py:964-983. -/
def MMap.update {σ K V : Type} (M : MMap σ K V) (s : σ) (other : UpdateArg K V)
    (kwds : List (K × V)) : Py σ := do
  let s' ← match other with
    | .mapping m => do M.updateKeys m s (← m.iter)
    | .pairs xs => M.setAll s xs
  M.setAll s' kwds

/-- `MutableMapping.setdefault`, Lib/_collections_abc.py:985-991. -/
def MMap.setdefault {σ K V : Type} (M : MMap σ K V) (s : σ) (key : K) (default : V) :
    Py (V × σ) :=
  match (M.view s).getitem key with
  | .ok v => .ok (v, s)
  | .error e =>
    if isKeyError e then do
      let s' ← M.setitem s key default
      pure (default, s')
    else .error e

/-- `Mapping.__eq__`, Lib/_collections_abc.py:819-822: `dict(self.items()) ==
dict(other.items())`, where `dictEq` is the builtin comparison of the two item lists,
last occurrence of a key winning. `none` is an `other` that is not a `Mapping`. -/
def mappingEq {K V : Type} (dictEq : List (K × V) → List (K × V) → Py Bool) (self : MapV K V)
    (other : Option (MapV K V)) : Py (Ret Bool) :=
  match other with
  | none => .ok .notImplemented
  | some o => do
    let a ← self.items
    let b ← o.items
    pure (.val (← dictEq a b))

/-! ### `ByteString` deprecation metaclass -/

/-- `_DeprecateByteStringMeta.__new__`, Lib/_collections_abc.py:1069-1077: a
`DeprecationWarning` for any class name but `ByteString`. -/
def byteStringMetaWarns (name : String) : Bool := name != "ByteString"

/-- `_DeprecateByteStringMeta.__instancecheck__`, Lib/_collections_abc.py:1079-1086:
always warns, then the `ABCMeta` answer. -/
def byteStringInstanceCheck (abcAnswer : Bool) : Bool × Bool := (true, abcAnswer)

end PyLean.CoreLibs.CollAbc
