import PyLean.Core

/-!
`Lib/functools.py` and `Modules/_functoolsmodule.c` (CPython 3.15.2): `reduce` and the cache keys of
`lru_cache`. The other parts are in Compare.lean, Lru.lean, Partial.lean, Dispatch.lean and Wrap.lean.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- A list comprehension whose body may raise. -/
def mapPy {α β : Type} (f : α → Py β) : List α → Py (List β)
  | [] => .ok []
  | x :: xs => do
    let y ← f x
    let ys ← mapPy f xs
    pure (y :: ys)

/-! ### `reduce` -/

/-- The second argument of `reduce`: not iterable, or one whose `iter()` raises `e`, where `isType` says that `e` is a
`TypeError` or a subclass, or an iterator yielding `items` and then stopping, or raising `err`. -/
inductive Source (α : Type) where
  | notIterable
  | iterRaises (e : PyExc) (isType : Bool)
  | iter (items : List α) (err : Option PyExc)

def emptyReduce : PyExc := .typeError "reduce() of empty iterable with no initial value"

/-- `for element in it: value = function(value, element)`, Lib/functools.py:262-263. -/
def reduceLoop {α : Type} (f : α → α → Py α) : α → List α → Option PyExc → Py α
  | v, [], none => .ok v
  | _, [], some e => .error e
  | v, x :: xs, e => do reduceLoop f (← f v x) xs e

/-- `reduce`, Lib/functools.py:237-265. -/
def reducePy {α : Type} (f : α → α → Py α) (seq : Source α) (initial : Option α) : Py α :=
  match seq with
  | .notIterable => .error (.typeError "~object is not iterable")
  | .iterRaises e _ => .error e
  | .iter items err =>
    match initial with
    | some v => reduceLoop f v items err
    | none =>
      match items, err with
      | [], some e => .error e
      | [], none => .error emptyReduce
      | x :: xs, e => reduceLoop f x xs e

/-- The `for (;;)` loop of `_functools_reduce_impl`, Modules/_functoolsmodule.c:1109-1148, where
`result` starts `NULL` without an initial value. -/
def reduceCLoop {α : Type} (f : α → α → Py α) : Option α → List α → Option PyExc → Py α
  | _, [], some e => .error e
  | none, [], none => .error emptyReduce
  | some v, [], none => .ok v
  | none, x :: xs, e => reduceCLoop f (some x) xs e
  | some v, x :: xs, e => do reduceCLoop f (some (← f v x)) xs e

/-- `_functools_reduce_impl`, Modules/_functoolsmodule.c:1088-1155. `PyObject_GetIter` failing with any `TypeError`,
Modules/_functoolsmodule.c:1096-1101, is replaced by a fixed message, so one from a user's `__iter__` is lost. -/
def reduceC {α : Type} (f : α → α → Py α) (seq : Source α) (initial : Option α) : Py α :=
  match seq with
  | .notIterable => .error (.typeError "reduce() arg 2 must support iteration")
  | .iterRaises e isType => .error (if isType then .typeError "reduce() arg 2 must support iteration" else e)
  | .iter items err => reduceCLoop f initial items err


/-- `keyobject_text_signature`, Modules/_functoolsmodule.c:949-952. -/
def keyTextSignature : String := "(obj)"

/-! ### `lru_cache` keys -/

/-- An element of a key tuple. -/
inductive KeyItem (α : Type) where
  | val (a : α)
  | mark
  | name (s : String)
  | typeOf (t : Nat)
  deriving Repr, DecidableEq

/-- A cache key: the single fast argument, or a tuple. -/
inductive CacheKey (α : Type) where
  | scalar (a : α)
  | tuple (items : List (KeyItem α))
  deriving Repr, DecidableEq

/-- The abstract view of an argument: `type(v) in fasttypes`, and `type(v)`. -/
structure MkKeyOps (α : Type) where
  fast : α → Bool
  typ : α → Nat

/-- `_make_key`, Lib/functools.py:522-553. -/
def makeKeyPy {α : Type} (O : MkKeyOps α) (args : List α) (kwds : List (String × α)) (typed : Bool) :
    CacheKey α :=
  let key := args.map KeyItem.val
  let key := if kwds.isEmpty then key else
    key ++ .mark :: kwds.flatMap (fun p => [.name p.1, .val p.2])
  if typed then
    .tuple (key ++ args.map (fun v => .typeOf (O.typ v)) ++
      (if kwds.isEmpty then [] else kwds.map (fun p => .typeOf (O.typ p.2))))
  else
    match key with
    | [.val a] => if O.fast a then .scalar a else .tuple key
    | _ => .tuple key

/-- `_make_key` with what the pure version leaves out. `if typed:` at Lib/functools.py:547 is a truth test on each call,
which `truth` stands for; and `type(key[0]) in fasttypes` at :551 hashes the type, which runs the metaclass's `__hash__`,
and which `typeHash` stands for. -/
def makeKeyPyFull {α : Type} (O : MkKeyOps α) (typeHash : α → Py Unit) (truth : Py Bool) (args : List α)
    (kwds : List (String × α)) : Py (CacheKey α) :=
  match truth with
  | .error e => .error e
  | .ok typed =>
    match typed, args, kwds with
    | false, [a], [] =>
      match typeHash a with
      | .error e => .error e
      | .ok () => .ok (makeKeyPy O args kwds false)
    | _, _, _ => .ok (makeKeyPy O args kwds typed)

/-- `lru_cache_make_key`, Modules/_functoolsmodule.c:1236-1295. -/
def makeKeyC {α : Type} (O : MkKeyOps α) (args : List α) (kwds : List (String × α)) (typed : Bool) :
    CacheKey α :=
  if !typed && kwds.isEmpty then
    match args with
    | [a] => if O.fast a then .scalar a else .tuple [.val a]
    | _ => .tuple (args.map KeyItem.val)
  else
    .tuple (args.map KeyItem.val ++
      (if kwds.isEmpty then [] else .mark :: kwds.flatMap (fun p => [.name p.1, .val p.2])) ++
      (if typed then args.map (fun v => .typeOf (O.typ v)) ++
          (if kwds.isEmpty then [] else kwds.map (fun p => .typeOf (O.typ p.2)))
       else []))

end PyLean.CoreLibs.Functools
