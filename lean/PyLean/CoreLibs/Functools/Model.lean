import PyLean.Core

/-!
`Lib/functools.py` and `Modules/_functoolsmodule.c` (CPython 3.14.7), mirrored as twins.

Everything generic stays generic: `reduce` over an abstract binary function, `cmp_to_key` over an
abstract comparison, `total_ordering` over abstract comparison dunders, `partial` over abstract
argument values, `lru_cache` over abstract keys and an abstract user function. `singledispatch` works
on a class hierarchy given as data (`World`).
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- A dunder's result: a value, or `NotImplemented`. -/
inductive Ret (α : Type) where
  | val (a : α)
  | notImplemented
  deriving Repr, DecidableEq, Inhabited

/-! ### `reduce` -/

/-- The second argument of `reduce`: not iterable, or an iterator yielding `items` and then
stopping, or raising `err`. -/
inductive Source (α : Type) where
  | notIterable
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
  | .iter items err =>
    match initial with
    | some v => reduceLoop f v items err
    | none =>
      match items, err with
      | [], some e => .error e
      | [], none => .error emptyReduce
      | x :: xs, e => reduceLoop f x xs e

/-- The `for (;;)` loop of `_functools_reduce_impl`, Modules/_functoolsmodule.c:1013-1052, where
`result` starts `NULL` without an initial value. -/
def reduceCLoop {α : Type} (f : α → α → Py α) : Option α → List α → Option PyExc → Py α
  | _, [], some e => .error e
  | none, [], none => .error emptyReduce
  | some v, [], none => .ok v
  | none, x :: xs, e => reduceCLoop f (some x) xs e
  | some v, x :: xs, e => do reduceCLoop f (some (← f v x)) xs e

/-- `_functools_reduce_impl`, Modules/_functoolsmodule.c:992-1059. -/
def reduceC {α : Type} (f : α → α → Py α) (seq : Source α) (initial : Option α) : Py α :=
  match seq with
  | .notIterable => .error (.typeError "reduce() arg 2 must support iteration")
  | .iter items err => reduceCLoop f initial items err

/-! ### `total_ordering` -/

/-- The four root comparisons, spelled as the method names. -/
inductive OrdOp where
  | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

def OrdOp.name : OrdOp → String
  | .lt => "__lt__"
  | .le => "__le__"
  | .gt => "__gt__"
  | .ge => "__ge__"

/-- The body shape of each generated method, Lib/functools.py:89-171. -/
inductive Shape where
  /-- `return not op_result and self != other` -/
  | notAndNe
  /-- `return op_result or self == other` -/
  | orEq
  /-- `return not op_result` -/
  | notOp
  /-- `return not op_result or self == other` -/
  | notOrEq
  /-- `return op_result and self != other` -/
  | andNe
  deriving Repr, DecidableEq

/-- `_convert`, Lib/functools.py:173-186. -/
def convert : OrdOp → List (OrdOp × Shape)
  | .lt => [(.gt, .notAndNe), (.le, .orEq), (.ge, .notOp)]
  | .le => [(.ge, .notOrEq), (.lt, .andNe), (.gt, .notOp)]
  | .gt => [(.lt, .notAndNe), (.ge, .orEq), (.le, .notOp)]
  | .ge => [(.le, .notOrEq), (.gt, .andNe), (.lt, .notOp)]

/-- The primitives a generated method reaches: `type(self).__root__(self, other)` and the
operators `==` and `!=`. -/
structure OrdPrims (α : Type) where
  root : α → α → Py (Ret Bool)
  eq : α → α → Py Bool
  ne : α → α → Py Bool

/-- One generated method, `_gt_from_lt` through `_lt_from_ge`, Lib/functools.py:89-171. -/
def derived {α : Type} (P : OrdPrims α) (s : Shape) (a b : α) : Py (Ret Bool) := do
  match ← P.root a b with
  | .notImplemented => pure .notImplemented
  | .val op =>
    match s with
    | .notAndNe => if op then pure (.val false) else (.val <$> P.ne a b)
    | .orEq => if op then pure (.val true) else (.val <$> P.eq a b)
    | .notOp => pure (.val (!op))
    | .notOrEq => if !op then pure (.val true) else (.val <$> P.eq a b)
    | .andNe => if op then (.val <$> P.ne a b) else pure (.val false)

/-- `max(roots)`: string order puts `__lt__` above `__le__`, `__gt__`, `__ge__`. -/
def maxRoot (roots : List OrdOp) : Option OrdOp :=
  if .lt ∈ roots then some .lt
  else if .le ∈ roots then some .le
  else if .gt ∈ roots then some .gt
  else if .ge ∈ roots then some .ge
  else none

/-- `total_ordering(cls)`, Lib/functools.py:188-199: the methods added, given the user-defined
comparisons. -/
def totalOrdering (roots : List OrdOp) : Py (OrdOp × List (OrdOp × Shape)) :=
  match maxRoot roots with
  | none => .error (.valueError "must define at least one ordering operation: < > <= >=")
  | some root => .ok (root, (convert root).filter (fun p => p.1 ∉ roots))

/-! ### `cmp_to_key` -/

inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq, Inhabited

def CmpOp.test (r : Int) : CmpOp → Bool
  | .lt => r < 0
  | .le => r ≤ 0
  | .eq => r == 0
  | .ne => r != 0
  | .gt => r > 0
  | .ge => r ≥ 0

/-- `K.__lt__` and siblings, Lib/functools.py:212-221: `mycmp(self.obj, other.obj) < 0`. `other` is
`none` when it has no `obj`. `__ne__` is `object.__ne__`, the negation of `__eq__`. -/
def keyComparePy {α : Type} (mycmp : α → α → Py Int) (op : CmpOp) (x : α) (other : Option α) :
    Py Bool :=
  match other with
  | none => .error (.named "AttributeError" "~object has no attribute 'obj'")
  | some y =>
    match op with
    | .ne => do pure (!CmpOp.test (← mycmp x y) .eq)
    | _ => do pure (CmpOp.test (← mycmp x y) op)

/-- `keyobject_richcompare`, Modules/_functoolsmodule.c:912-943. `PyObject_RichCompare(res, zero, op)`
on an `int` result. -/
def keyCompareC {α : Type} (mycmp : α → α → Py Int) (op : CmpOp) (x : α) (other : Option α) :
    Py Bool :=
  match other with
  | none => .error (.typeError "other argument must be K instance")
  | some y => do pure (CmpOp.test (← mycmp x y) op)

/-! ### `partial` -/

/-- A stored positional argument. -/
inductive PArg (α : Type) where
  | ph
  | val (a : α)
  deriving Repr, DecidableEq, Inhabited

/-- What a `partial` wraps. A `partial` object carries whether it is a subclass overriding
`__call__` (with that override's identity), and whether it has an instance `__dict__`. -/
inductive Fn (α : Type) where
  | base (id : Nat)
  | notCallable
  | pobj (override : Option Nat) (hasDict : Bool) (func : Fn α) (args : List (PArg α))
      (kw : List (String × α)) (phcount : Nat)
  deriving Repr, DecidableEq

def Fn.isCallable {α : Type} : Fn α → Bool
  | .notCallable => false
  | _ => true

def isPh {α : Type} : PArg α → Bool
  | .ph => true
  | .val _ => false

def phCount {α : Type} (args : List (PArg α)) : Nat := (args.filter isPh).length

/-- `{**a, **b}`: later keys keep the first position and take the later value. -/
def mergeKw {α : Type} (a b : List (String × α)) : List (String × α) :=
  b.foldl (fun acc p =>
    if acc.any (fun q => q.1 == p.1) then acc.map (fun q => if q.1 == p.1 then p else q)
    else acc ++ [p]) a

/-- Fill the placeholders of `base` from `new`, left to right. A placeholder with nothing left stays;
what is left of `new` after the last slot goes at the end. This is the loop at
Modules/_functoolsmodule.c:262-277, and the effect of `func._merger` at Lib/functools.py:336-341. -/
def fill {α : Type} : List (PArg α) → List (PArg α) → List (PArg α)
  | [], new => new
  | .ph :: rest, n :: new => n :: fill rest new
  | .ph :: rest, [] => .ph :: fill rest []
  | a :: rest, new => a :: fill rest new

def trailingPh {α : Type} (args : List (PArg α)) : Bool :=
  match args.getLast? with
  | some .ph => true
  | _ => false

def trailingMsg := "trailing Placeholders are not allowed"
def kwPhMsg := "Placeholder cannot be passed as a keyword argument"

def kwVals {α : Type} (kw : List (String × PArg α)) : Option (List (String × α)) :=
  kw.mapM (fun p => match p.2 with
    | .val a => some (p.1, a)
    | .ph => none)

/-- `_partial_new`, Lib/functools.py:313-357, for `cls` a `partial` type: flattens every `isinstance`
of `partial`. `outer` is the new object's own `override`. -/
def partialNewPy {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α)) : Py (Fn α) := do
  if !func.isCallable then throw (.typeError "the first argument must be callable")
  if trailingPh args then throw (.typeError trailingMsg)
  let some kw' := kwVals kw | throw (.typeError kwPhMsg)
  match func with
  | .pobj _ _ inner pargs pkw pph =>
    if args.isEmpty then
      pure (.pobj outer false inner pargs (mergeKw pkw kw') pph)
    else
      let tot := if pph = 0 then pargs ++ args else fill pargs args
      pure (.pobj outer false inner tot (mergeKw pkw kw') (phCount tot))
  | _ => pure (.pobj outer false func args kw' (phCount args))

/-- `partial_new`, Modules/_functoolsmodule.c:168-324: flattens a `partial` instance only when its
`__dict__` was never created, :219-230. -/
def partialNewC {α : Type} (outer : Option Nat) (func : Fn α) (args : List (PArg α))
    (kw : List (String × PArg α)) : Py (Fn α) := do
  if !func.isCallable then throw (.typeError "the first argument must be callable")
  if trailingPh args then throw (.typeError trailingMsg)
  let some kw' := kwVals kw | throw (.typeError kwPhMsg)
  match func with
  | .pobj _ false inner pargs pkw pph =>
    let newPh := phCount args
    if pph > 0 ∧ !args.isEmpty then
      let tot := fill pargs args
      let filled := min pph args.length
      pure (.pobj outer false inner tot (mergeKw pkw kw') (pph - filled + newPh))
    else
      pure (.pobj outer false inner (pargs ++ args) (mergeKw pkw kw') (pph + newPh))
  | _ => pure (.pobj outer false func args kw' (phCount args))

/-- A completed call: which function, with which positional and keyword arguments. -/
structure Called (α : Type) where
  id : Nat
  args : List α
  kw : List (String × α)
  deriving Repr, DecidableEq

def missingMsg (phcount got : Nat) : String :=
  s!"missing positional arguments in 'partial' call; expected at least {phcount}, got {got}"

/-- The merged positional arguments of a call with enough arguments. -/
def fillCall {α : Type} : List (PArg α) → List α → List α
  | [], new => new
  | .ph :: rest, n :: new => n :: fillCall rest new
  | .ph :: rest, [] => fillCall rest []
  | .val a :: rest, new => a :: fillCall rest new

/-- Calling a function object. -/
def callFn {α : Type} : Fn α → List α → List (String × α) → Py (Called α)
  | .base id, args, kw => .ok ⟨id, args, kw⟩
  | .notCallable, _, _ => .error (.typeError "~object is not callable")
  | .pobj (some o) _ _ _ _ _, args, kw => .ok ⟨o, args, kw⟩
  | .pobj none _ func pargs pkw ph, args, kw =>
    if args.length < ph then .error (.typeError (missingMsg ph args.length))
    else callFn func (fillCall pargs args) (mergeKw pkw kw)

/-- `partial.__call__`, Lib/functools.py:380-393, on a plain `partial`. -/
def partialCallPy {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (args : List α) (kw : List (String × α)) : Py (Called α) :=
  if ph ≠ 0 ∧ args.length < ph then .error (.typeError (missingMsg ph args.length))
  else callFn func (fillCall pargs args) (mergeKw pkw kw)

/-- `partial_call`, Modules/_functoolsmodule.c:497-580. -/
def partialCallC {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (args : List α) (kw : List (String × α)) : Py (Called α) :=
  if args.length < ph then .error (.typeError (missingMsg ph args.length))
  else
    let totKw := if pkw.isEmpty then kw else mergeKw pkw kw
    if ph ≠ 0 then callFn func (fillCall pargs args) totKw
    else callFn func ((pargs.filterMap (fun a => match a with
      | .val v => some v
      | .ph => none)) ++ args) totKw

/-- `partial_vectorcall`, Modules/_functoolsmodule.c:386-476, reached when the wrapped function
supports vectorcall (`partial_setvectorcall`, :480-492); `partial_vectorcall_fallback`, :374-383,
sends a `partial` with stored keywords to `partial_call`. -/
def partialVectorcall {α : Type} (func : Fn α) (pargs : List (PArg α)) (pkw : List (String × α))
    (ph : Nat) (args : List α) (kw : List (String × α)) : Py (Called α) :=
  if !pkw.isEmpty then partialCallC func pargs pkw ph args kw
  else if args.length < ph then .error (.typeError (missingMsg ph args.length))
  else callFn func (fillCall pargs args) kw

/-- `partial.__repr__`, Lib/functools.py:359-366, and `partial_repr`,
Modules/_functoolsmodule.c:610-687, on the reprs of the parts. -/
def partialRepr (cls func : String) (args : List String) (kw : List (String × String)) : String :=
  let parts := func :: args ++ kw.map (fun p => s!"{p.1}={p.2}")
  s!"{cls}({", ".intercalate parts})"

/-- A state tuple of `__setstate__`, as its checks see it. -/
structure PState (α : Type) where
  isTuple : Bool
  size : Nat
  callable : Bool
  argsTuple : Bool
  args : List (PArg α)
  /-- `kwds` is `None`, a dict, or something else. -/
  kwNone : Bool
  kwDict : Bool
  nsNone : Bool
  nsDict : Bool

def invalidState := "invalid partial state"

/-- `partial.__setstate__`, Lib/functools.py:404-432: the placeholder count on success. -/
def setstatePy {α : Type} (st : PState α) : Py Nat :=
  if !st.isTuple then .error (.typeError "argument to __setstate__ must be a tuple")
  else if st.size ≠ 4 then .error (.typeError s!"expected 4 items in state, got {st.size}")
  else if !st.callable || !st.argsTuple || (!st.kwNone && !st.kwDict) ||
      (!st.nsNone && !st.nsDict) then .error (.typeError invalidState)
  else if trailingPh st.args then .error (.typeError trailingMsg)
  else .ok (phCount st.args)

/-- `partial_setstate`, Modules/_functoolsmodule.c:706-768. -/
def setstateC {α : Type} (st : PState α) : Py Nat :=
  if !st.isTuple then .error (.typeError invalidState)
  else if st.size ≠ 4 || !st.callable || !st.argsTuple || (!st.kwNone && !st.kwDict) ||
      (!st.nsNone && !st.nsDict) then .error (.typeError invalidState)
  else if trailingPh st.args then .error (.typeError trailingMsg)
  else .ok (phCount st.args)

/-- `partial.__reduce__`, Lib/functools.py:400-402: `(type(self), (self.func,), state)`, where the
state's keywords are `None` when empty. `partial_reduce`, Modules/_functoolsmodule.c:697-703, keeps
the empty dict. -/
def reduceStatePy {α : Type} (args : List (PArg α)) (kw : List (String × α)) : PState α :=
  ⟨true, 4, true, true, args, kw.isEmpty, !kw.isEmpty, true, false⟩

def reduceStateC {α : Type} (args : List (PArg α)) : PState α :=
  ⟨true, 4, true, true, args, false, true, true, false⟩

/-- `_PlaceholderType`, Lib/functools.py:273-293, with `placeholder_repr`, `placeholder_reduce`,
`placeholder_new` in C: every construction gives the one instance; a call with arguments is a
`TypeError`, subclassing is a `TypeError`. -/
structure PlaceholderType where
  repr : String := "Placeholder"
  reduce : String := "Placeholder"
  deriving Repr, DecidableEq

def placeholderNew (inst : Option PlaceholderType) : PlaceholderType × Option PlaceholderType :=
  match inst with
  | some i => (i, some i)
  | none => ({}, some {})

/-- `_unwrap_partial`, Lib/functools.py:500-503. -/
def unwrapPartial {α : Type} : Fn α → Fn α
  | .pobj _ _ f _ _ _ => unwrapPartial f
  | f => f

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
structure KeyOps (α : Type) where
  fast : α → Bool
  typ : α → Nat

/-- `_make_key`, Lib/functools.py:522-551. -/
def makeKeyPy {α : Type} (O : KeyOps α) (args : List α) (kwds : List (String × α)) (typed : Bool) :
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

/-- `lru_cache_make_key`, Modules/_functoolsmodule.c:1140-1199. -/
def makeKeyC {α : Type} (O : KeyOps α) (args : List α) (kwds : List (String × α)) (typed : Bool) :
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

/-! ### `lru_cache` wrappers -/

/-- What `lru_cache` decided about `maxsize`, in the wrapper's terms. -/
inductive LruMode where
  | uncached
  | infinite
  | bounded (maxsize : Int)
  deriving Repr, DecidableEq

/-- `maxsize` as `lru_cache` sees it. -/
inductive MaxsizeArg where
  | int (n : Int)
  | none
  /-- A callable, the bare `@lru_cache` form, with `typed` a `bool` or not. -/
  | callable (typedBool : Bool)
  | other
  deriving Repr, DecidableEq

def maxsizeErr := "Expected first argument to be an integer, a callable, or None"

/-- The argument handling of `lru_cache`, Lib/functools.py:579-591: the value handed to
`_lru_cache_wrapper`. -/
def lruCacheArg : MaxsizeArg → Py (Option Int)
  | .int n => .ok (some (if n < 0 then 0 else n))
  | .callable true => .ok (some 128)
  | .none => .ok Option.none
  | .callable false | .other => .error (.typeError maxsizeErr)

/-- The selection at Lib/functools.py:615-639. -/
def wrapperPyMode : Option Int → Py LruMode
  | Option.none => .ok .infinite
  | some 0 => .ok .uncached
  | some m => .ok (.bounded m)

/-- `lru_cache_new`, Modules/_functoolsmodule.c:1552-1571. -/
def wrapperCMode : Option Int → Py LruMode
  | Option.none => .ok .infinite
  | some m =>
    if m > ssizeMax ∨ m < ssizeMin then
      .error (.overflowError "cannot fit 'int' into an index-sized integer")
    else if m ≤ 0 then .ok .uncached
    else .ok (.bounded m)

/-- `cache_info()`, Lib/functools.py:698-701, Modules/_functoolsmodule.c:1674. -/
structure CacheInfo where
  hits : Nat
  misses : Nat
  maxsize : Option Int
  currsize : Nat
  deriving Repr, DecidableEq

/-- The C wrapper's state: the linked list from the oldest entry to the newest, Modules/_functoolsmodule.c
:1252-1278. The `cache` dict's contents are the same entries. -/
structure CLru (K V : Type) where
  links : List (K × V)
  hits : Nat
  misses : Nat
  deriving Repr, DecidableEq

/-- The Python wrapper's state: the circular list from `root`, Lib/functools.py:612-613. `none` is the
root link; `ring` lists it first, then the links oldest to newest. -/
structure PyLru (K V : Type) where
  ring : List (Option (K × V))
  hits : Nat
  misses : Nat
  full : Bool
  deriving Repr, DecidableEq

def extract {K V : Type} [DecidableEq K] (k : K) (l : List (K × V)) : List (K × V) :=
  l.filter (fun p => p.1 ≠ k)

def ringExtract {K V : Type} [DecidableEq K] (k : K) (l : List (Option (K × V))) :
    List (Option (K × V)) :=
  l.filter (fun p => match p with
    | some q => q.1 ≠ k
    | none => true)

/-- The bounded wrapper, Lib/functools.py:641-696, with a user function that does not reenter. -/
def stepPy {K V : Type} [DecidableEq K] (maxsize : Nat) (f : K → Py V) (s : PyLru K V) (key : K) :
    Py V × PyLru K V :=
  match (s.ring.filterMap id).lookup key with
  | some result =>
    -- move the link to the front of the circular queue, the position before `root`
    (.ok result, { s with ring := ringExtract key s.ring ++ [some (key, result)], hits := s.hits + 1 })
  | none =>
    let s := { s with misses := s.misses + 1 }
    match f key with
    | .error e => (.error e, s)
    | .ok result =>
      if s.full then
        -- use the old root for the new key; the oldest link becomes the new root
        match s.ring with
        | _ :: _ :: rest =>
          (.ok result, { s with ring := none :: rest ++ [some (key, result)] })
        | r => (.ok result, { s with ring := r })
      else
        let ring := s.ring ++ [some (key, result)]
        (.ok result, { s with ring, full := decide ((ring.filterMap id).length ≥ maxsize) })

/-- `bounded_lru_cache_wrapper`, Modules/_functoolsmodule.c:1493-1521, with `..._get_lock_held`,
:1312-1344, `..._update_lock_held`, :1347-1490, and the link helpers, :1252-1278. -/
def stepC {K V : Type} [DecidableEq K] (maxsize : Nat) (f : K → Py V) (s : CLru K V) (key : K) :
    Py V × CLru K V :=
  match s.links.lookup key with
  | some result =>
    (.ok result, { s with links := extract key s.links ++ [(key, result)], hits := s.hits + 1 })
  | none =>
    let s := { s with misses := s.misses + 1 }
    match f key with
    | .error e => (.error e, s)
    | .ok result =>
      if s.links.length < maxsize ∨ s.links.isEmpty then
        (.ok result, { s with links := s.links ++ [(key, result)] })
      else
        (.ok result, { s with links := s.links.tail ++ [(key, result)] })

/-- `uncached_lru_cache_wrapper`, :1202-1211, and Lib/functools.py:617-622: a miss each call. -/
def stepUncached {K V : Type} (f : K → Py V) (misses : Nat) (key : K) : Py V × Nat :=
  (f key, misses + 1)

/-- `infinite_lru_cache_wrapper`, :1214-1249, and Lib/functools.py:626-637. -/
def stepInfinite {K V : Type} [DecidableEq K] (f : K → Py V) (s : CLru K V) (key : K) :
    Py V × CLru K V :=
  match s.links.lookup key with
  | some result => (.ok result, { s with hits := s.hits + 1 })
  | none =>
    let s := { s with misses := s.misses + 1 }
    match f key with
    | .error e => (.error e, s)
    | .ok result => (.ok result, { s with links := s.links ++ [(key, result)] })

/-- One operation on a wrapper. -/
inductive LruOp (K : Type) where
  | call (k : K)
  | clear
  deriving Repr, DecidableEq

def emptyC {K V : Type} : CLru K V := ⟨[], 0, 0⟩
def emptyPy {K V : Type} : PyLru K V := ⟨[none], 0, 0, false⟩

/-- Run a sequence of operations, collecting the call results. -/
def runC {K V : Type} [DecidableEq K] (maxsize : Nat) (f : K → Py V) :
    CLru K V → List (LruOp K) → List (Py V) × CLru K V
  | s, [] => ([], s)
  | _, .clear :: ops => runC maxsize f emptyC ops
  | s, .call k :: ops =>
    let (r, s') := stepC maxsize f s k
    let (rs, t) := runC maxsize f s' ops
    (r :: rs, t)

def runPy {K V : Type} [DecidableEq K] (maxsize : Nat) (f : K → Py V) :
    PyLru K V → List (LruOp K) → List (Py V) × PyLru K V
  | s, [] => ([], s)
  | _, .clear :: ops => runPy maxsize f emptyPy ops
  | s, .call k :: ops =>
    let (r, s') := stepPy maxsize f s k
    let (rs, t) := runPy maxsize f s' ops
    (r :: rs, t)

def infoC {K V : Type} (maxsize : Nat) (s : CLru K V) : CacheInfo :=
  ⟨s.hits, s.misses, some maxsize, s.links.length⟩

def infoPy {K V : Type} (maxsize : Nat) (s : PyLru K V) : CacheInfo :=
  ⟨s.hits, s.misses, some maxsize, (s.ring.filterMap id).length⟩

/-! ### `update_wrapper`, `cached_property` -/

/-- An object as its attributes. -/
abbrev Attrs (α : Type) := List (String × α)

def setAttr {α : Type} (o : Attrs α) (k : String) (v : α) : Attrs α :=
  (o.filter (fun p => p.1 ≠ k)) ++ [(k, v)]

/-- `update_wrapper`, Lib/functools.py:35-63, with `wraps`, :65-77, the same call through `partial`:
copy `assigned` that exist, merge `__dict__`, then set `__wrapped__`. `selfRef` is the wrapped object. -/
def updateWrapper {α : Type} (wrapper wrapped : Attrs α) (wrapperDict wrappedDict : Attrs α)
    (assigned : List String) (selfRef : α) : Attrs α × Attrs α :=
  let w := assigned.foldl (fun acc a =>
    match wrapped.lookup a with
    | some v => setAttr acc a v
    | none => acc) wrapper
  (setAttr w "__wrapped__" selfRef,
    wrappedDict.foldl (fun acc p => setAttr acc p.1 p.2) wrapperDict)

/-- `cached_property.__set_name__`, Lib/functools.py:1101-1108. -/
def setName (attrname : Option String) (name : String) : Py (Option String) :=
  match attrname with
  | none => .ok (some name)
  | some a =>
    if name ≠ a then
      .error (.typeError
        "~Cannot assign the same cached_property to two different names")
    else .ok (some a)

/-- `cached_property.__get__`, Lib/functools.py:1110-1135: the instance's `__dict__` is `none` when
there is none, and `frozen` when it refuses item assignment. Returns the value and the new dict. -/
def cachedGet {α : Type} (func : Py α) (attrname : Option String) (dict : Option (Attrs α))
    (frozen : Bool) : Py (α × Attrs α) :=
  match attrname with
  | none =>
    .error (.typeError "Cannot use cached_property instance without calling __set_name__ on it.")
  | some name =>
    match dict with
    | none => .error (.typeError "~No '__dict__' attribute on instance")
    | some d =>
      match d.lookup name with
      | some v => .ok (v, d)
      | none => do
        let v ← func
        if frozen then throw (.typeError "~The '__dict__' attribute does not support item assignment")
        pure (v, setAttr d name v)

/-! ### `singledispatchmethod` -/

/-- `singledispatchmethod.__repr__`, Lib/functools.py:1022-1030. -/
def sdmRepr (qualname name : Option String) : String :=
  s!"<single dispatch method descriptor {(qualname <|> name).getD "?"}>"

/-- `_singledispatchmethod_get.__repr__`, Lib/functools.py:1050-1061. -/
def sdmGetRepr (qualname name : Option String) (objRepr : Option String) : String :=
  let n := (qualname <|> name).getD "?"
  match objRepr with
  | some o => s!"<bound single dispatch method {n} of {o}>"
  | none => s!"<single dispatch method {n}>"

/-! ### `singledispatch` -/

abbrev Cls := Nat

/-- A class hierarchy as data. -/
structure World where
  bases : Cls → List Cls
  mro : Cls → List Cls
  /-- `issubclass`, including virtual subclasses of ABCs. -/
  isSub : Cls → Cls → Bool
  /-- `hasattr(cls, '__abstractmethods__')`. -/
  isAbc : Cls → Bool
  /-- `cls.__subclasses__()`. -/
  subclasses : Cls → List Cls

/-- The first sequence head not in the tail of any sequence, Lib/functools.py:746-753. -/
def candidateOf (seqs : List (List Cls)) : Option Cls :=
  seqs.findSome? (fun s =>
    match s with
    | [] => none
    | c :: _ => if seqs.any (fun t => t.tail.contains c) then none else some c)

/-- `_c3_merge`, Lib/functools.py:735-760. -/
def c3Merge : (fuel : Nat) → List (List Cls) → Py (List Cls)
  | 0, _ => .error .modelFuel
  | fuel + 1, seqs =>
    let seqs := seqs.filter (fun s => !s.isEmpty)
    if seqs.isEmpty then .ok []
    else
      match candidateOf seqs with
      | none => .error (.named "RuntimeError" "Inconsistent hierarchy")
      | some c => do
        let rest ← c3Merge fuel (seqs.map (fun s => if s.head? = some c then s.tail else s))
        pure (c :: rest)

/-- The last index-plus-one of a base with `__abstractmethods__`, Lib/functools.py:779-784. -/
def boundaryOf (W : World) (bases : List Cls) : Nat :=
  match (bases.reverse.zipIdx.find? (fun p => W.isAbc p.1)) with
  | some (_, i) => bases.length - i
  | none => 0

/-- `_c3_mro`, Lib/functools.py:762-805. -/
def c3Mro (W : World) : (fuel : Nat) → Cls → List Cls → Py (List Cls)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, cls, abcs => do
    let bases := W.bases cls
    let boundary := boundaryOf W bases
    let explicitBases := bases.take boundary
    let otherBases := bases.drop boundary
    let abstractBases := abcs.filter (fun b => W.isSub cls b && !bases.any (fun x => W.isSub x b))
    let abcs' := abcs.filter (fun b => b ∉ abstractBases)
    let rec mros : List Cls → Py (List (List Cls))
      | [] => .ok []
      | b :: bs => do
        let m ← c3Mro W fuel b abcs'
        let ms ← mros bs
        pure (m :: ms)
    let e ← mros explicitBases
    let a ← mros abstractBases
    let o ← mros otherBases
    let seqs := [[cls]] ++ e ++ a ++ o ++ [explicitBases] ++ [abstractBases] ++ [otherBases]
    -- each pass removes at least one element
    c3Merge ((seqs.map List.length).sum + 1) seqs

/-- `_compose_mro`, Lib/functools.py:807-847. -/
def composeMro (W : World) (fuel : Nat) (cls : Cls) (types : List Cls) : Py (List Cls) :=
  let bases := W.mro cls
  let types := types.filter (fun t => t ∉ bases && W.isSub cls t)
  let types := types.filter (fun t =>
    !types.any (fun other => t != other && (W.mro other).contains t))
  let mro := types.foldl (fun (acc : List Cls) typ =>
    let found := (W.subclasses typ).filterMap (fun sub =>
      if sub ∉ bases && W.isSub cls sub then
        some ((W.mro sub).filter (fun s => types.contains s))
      else none)
    if found.isEmpty then acc ++ [typ]
    else
      -- `found.sort(key=len, reverse=True)` is stable
      let sorted := (found.mergeSort (fun a b => a.length ≥ b.length))
      sorted.foldl (fun acc sub =>
        sub.foldl (fun acc s => if s ∈ acc then acc else acc ++ [s]) acc) acc) []
  c3Mro W fuel cls mro

/-- The registry, in insertion order. -/
abbrev Registry (ι : Type) := List (Cls × ι)

/-- The loop of `_find_impl`, Lib/functools.py:861-872. -/
def findLoop {ι : Type} (W : World) (cls : Cls) (reg : Registry ι) :
    Option Cls → List Cls → Py (Option Cls)
  | m, [] => .ok m
  | some m, t :: rest =>
    if (reg.lookup t).isSome && !(W.mro cls).contains t && !(W.mro cls).contains m &&
        !W.isSub m t then
      .error (.named "RuntimeError" "~Ambiguous dispatch")
    else
      let _ := rest
      .ok (some m)
  | none, t :: rest =>
    if (reg.lookup t).isSome then findLoop W cls reg (some t) rest
    else findLoop W cls reg none rest

/-- `_find_impl`, Lib/functools.py:849-873. -/
def findImpl {ι : Type} (W : World) (fuel : Nat) (cls : Cls) (reg : Registry ι) : Py (Option ι) := do
  let mro ← composeMro W fuel cls (reg.map Prod.fst)
  let m ← findLoop W cls reg none mro
  pure (m.bind (fun c => reg.lookup c))

/-- The closure state of `singledispatch`, Lib/functools.py:889-891. -/
structure Dispatcher (ι : Type) where
  registry : Registry ι
  cache : List (Cls × Option ι)
  token : Option Nat

def regSet {ι : Type} (reg : Registry ι) (c : Cls) (i : ι) : Registry ι :=
  if reg.any (fun p => p.1 == c) then reg.map (fun p => if p.1 == c then (c, i) else p)
  else reg ++ [(c, i)]

/-- The first argument of `register`: a class, or a union of classes. -/
inductive RegArg where
  | cls (c : Cls)
  | union (cs : List Cls)
  deriving Repr, DecidableEq

/-- `register(cls, func)`, Lib/functools.py:968-976. A `types.UnionType` has no
`__abstractmethods__`, so the test at :973 is false for a union, whatever its members are. -/
def register {ι : Type} (W : World) (abcToken : Nat) (d : Dispatcher ι) (arg : RegArg) (f : ι) :
    Dispatcher ι :=
  let registry := match arg with
    | .union cs => cs.foldl (fun r c => regSet r c f) d.registry
    | .cls c => regSet d.registry c f
  let hasAbstract := match arg with
    | .union _ => false
    | .cls c => W.isAbc c
  let token := if d.token.isNone && hasAbstract then some abcToken else d.token
  { registry, cache := [], token }

/-- `dispatch(cls)`, Lib/functools.py:893-914. `abcToken` is `get_cache_token()`. -/
def dispatch {ι : Type} (W : World) (fuel abcToken : Nat) (d : Dispatcher ι) (cls : Cls) :
    Py (Option ι) × Dispatcher ι :=
  let d := match d.token with
    | some t => if t ≠ abcToken then { d with cache := [], token := some abcToken } else d
    | none => d
  match d.cache.lookup cls with
  | some i => (.ok i, d)
  | none =>
    match d.registry.lookup cls with
    | some i => (.ok (some i), { d with cache := (cls, some i) :: d.cache })
    | none =>
      match findImpl W fuel cls d.registry with
      | .error e => (.error e, d)
      | .ok i => (.ok i, { d with cache := (cls, i) :: d.cache })

/-- `singledispatch(func)`, Lib/functools.py:985: `registry[object] = func`. -/
def newDispatcher {ι : Type} (object : Cls) (func : ι) : Dispatcher ι := ⟨[(object, func)], [], none⟩

end PyLean.CoreLibs.Functools
