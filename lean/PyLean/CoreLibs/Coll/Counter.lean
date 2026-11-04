import PyLean.Accel.HeapqSelectProps
import PyLean.CoreLibs.Coll.Dict

/-!
`collections.Counter` and `_count_elements`, Lib/collections/__init__.py:540-1033 and
Modules/_collectionsmodule.c:2544-2644 (CPython 3.15.2), over abstract keys and counts.

* Keys `κ` compare by `DecidableEq` (hash and `==` consistent, `==` cannot raise: a key type
  breaking that is out of scope). `K.hash k` is the type's `__hash__`, which may raise; every
  dict operation runs it first (`dHash`), and keys already stored in a dict are hashable, which
  the theorems assume as `HashOk`.
* Counts `ν` are arbitrary objects; `DecidableEq ν` is `is`. Every operator a method applies
  to them is a parameter in `Num`: `a + b` (after the binary-operator protocol, so a
  `NotImplemented` from both sides is the `TypeError` the operator raises), `a += b`, the six
  comparisons together with the truth test that `if`, `all()`, `and`, `not` and `list.sort`
  apply to their result (`PyObject_RichCompareBool` / `PyObject_IsTrue`; either step may
  raise), `bool(x)`, `abs(x)` and `operator.index(x)`. `zero` and `one` are the int objects
  `0` and `1` the source writes.
* Iterables are `Py (FIt α)`: `iter()` may fail, and then the loop sees the items `next()`
  yields followed by `StopIteration` or by the exception a later `next()` raised.
* Methods that mutate `self` return `Out`: the storage they leave and the exception that
  stopped them, so an exception halfway through a loop keeps the writes made before it.

Scope limits, stated once: callbacks are pure functions of their arguments, so a callback that
mutates the `Counter` being iterated (the dict iterator's `RuntimeError`) or re-enters it is out
of scope; `Counter` subclasses overriding `__init__`, `update`, `__missing__`, `__getitem__`,
`items` or the comparison dunders are out of scope, except for the `get` / `__setitem__`
overrides `_count_elements` dispatches on; a `Mapping` is taken to have `keys()`.
-/

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Eff SEnv Sorter HO hEnv nSelect pySortedBy pureKey builtinHier Hier isA)

variable {κ ν : Type} [DecidableEq κ]

/-! ### Iterables, keys and counts -/

/-- What a `for` loop sees of an iterator: the items `next()` yields, then `stop`: `none` for
`StopIteration`, or the exception the next `next()` raised. -/
structure FIt (α : Type) where
  xs : List α
  stop : Option PyExc := none
  deriving Repr, DecidableEq

/-- An iterator that yields `l` and stops. -/
def FIt.ofList {α : Type} (l : List α) : FIt α := ⟨l, none⟩

/-- The key type's `__hash__` and `%T` name. -/
structure KOps (κ : Type) where
  hash : κ → Py Unit
  tyName : κ → String

/-- The hash step of a dict lookup, store or delete: `dict_unhashable_type`,
Objects/dictobject.c:2442-2460, turns an exception of exact type `TypeError` into
`cannot use '%T' as a dict key (%S)` and lets every other exception through. -/
def dHash (K : KOps κ) (k : κ) : Py Unit :=
  match K.hash k with
  | .ok () => .ok ()
  | .error (.typeError m) => .error (.typeError s!"~cannot use '{K.tyName k}' as a dict key ({m})")
  | .error e => .error e

/-- Every key of `d` hashes: the dict type invariant (a key is hashed when it is stored, and
`__hash__` is a function of the key). -/
def HashOk (K : KOps κ) (d : D κ ν) : Prop := ∀ k ∈ D.keys d, K.hash k = .ok ()

/-- `d.get(k, dflt)` and `d[k]` with `__missing__` returning `dflt`. -/
def dGet (K : KOps κ) (d : D κ ν) (k : κ) (dflt : ν) : Py ν := do
  dHash K k
  pure ((D.get? d k).getD dflt)

/-- `d[k] = v` on a dict. -/
def dSet (K : KOps κ) (d : D κ ν) (k : κ) (v : ν) : Py (D κ ν) := do
  dHash K k
  pure (D.set d k v)

/-- `k in d`. -/
def dMem (K : KOps κ) (d : D κ ν) (k : κ) : Py Bool := do
  dHash K k
  pure (D.mem d k)

/-- Count objects and the operators the methods apply to them. -/
structure Num (ν : Type) where
  zero : ν
  one : ν
  add : ν → ν → Py ν
  sub : ν → ν → Py ν
  iadd : ν → ν → Py ν
  isub : ν → ν → Py ν
  abs : ν → Py ν
  lt : ν → ν → Py Bool
  gt : ν → ν → Py Bool
  le : ν → ν → Py Bool
  ge : ν → ν → Py Bool
  eq : ν → ν → Py Bool
  truth : ν → Py Bool
  index : ν → Py Int

/-- A method that mutates `self`: the storage it leaves, and the exception that stopped it
(`none`: it returned). -/
abbrev Out (σ : Type) := σ × Option PyExc

/-- A loop whose body may raise: the state before the raising iteration is kept. -/
def loopS {σ α : Type} (f : σ → α → Py σ) : σ → List α → Out σ
  | s, [] => (s, none)
  | s, x :: xs =>
    match f s x with
    | .ok s' => loopS f s' xs
    | .error e => (s, some e)

/-- `for x in it: body`, on an iterator. -/
def forIt {σ α : Type} (f : σ → α → Py σ) (s : σ) (it : FIt α) : Out σ :=
  match loopS f s it.xs with
  | (s', none) => (s', it.stop)
  | r => r

/-- `for x in iterable: body`, `iter(iterable)` included. -/
def forPy {σ α : Type} (f : σ → α → Py σ) (s : σ) : Py (FIt α) → Out σ
  | .error e => (s, some e)
  | .ok it => forIt f s it

/-- One mutating step after another. -/
def Out.andThen {σ : Type} (r : Out σ) (k : σ → Out σ) : Out σ :=
  match r with
  | (s, none) => k s
  | r => r

/-- A constructor or a function returning a new object: the exception, or the result. -/
def Out.toPy {σ : Type} : Out σ → Py σ
  | (s, none) => .ok s
  | (_, some e) => .error e

/-- `all(p(x) for x in xs)`: stops at the first false answer or exception. -/
def allM {α : Type} (p : α → Py Bool) : List α → Py Bool
  | [] => .ok true
  | x :: xs => do
    let b ← p x
    if b then allM p xs else pure false

/-- `[x for x in xs if p(x)]`. -/
def filterPy {α : Type} (p : α → Py Bool) : List α → Py (List α)
  | [] => .ok []
  | x :: xs => do
    let b ← p x
    let r ← filterPy p xs
    pure (if b then x :: r else r)

/-! ### `_count_elements` -/

/-- The mapping `_count_elements` writes into, a `dict` subclass instance (`self` of a
`Counter` or subclass): its type's `get` and `__setitem__` when they are not `dict`'s (`none`:
`dict.get` / `dict.__setitem__`), and a `get` stored in the instance `__dict__`, which
`mapping.get` finds first (a function is not a data descriptor). -/
structure CTarget (κ ν : Type) where
  typeGet : Option (D κ ν → κ → ν → Py ν) := none
  typeSet : Option (D κ ν → κ → ν → Py (D κ ν)) := none
  instGet : Option (D κ ν → κ → ν → Py ν) := none

/-- `mapping.get` bound: the instance attribute, else the type's, else `dict.get`. -/
def boundGet (K : KOps κ) (T : CTarget κ ν) : D κ ν → κ → ν → Py ν :=
  match T.instGet, T.typeGet with
  | some g, _ => g
  | none, some g => g
  | none, none => dGet K

/-- `mapping[key] = value`: `type(mapping).__setitem__`. -/
def setItem (K : KOps κ) (T : CTarget κ ν) : D κ ν → κ → ν → Py (D κ ν) :=
  match T.typeSet with
  | some f => f
  | none => dSet K

/-- The pure-Python `_count_elements`, Lib/collections/__init__.py:540-544. It is shadowed
by the C function when `_collections` imports. -/
def countPy (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (iterable : Py (FIt κ)) :
    Out (D κ ν) :=
  let mapping_get := boundGet K T                               -- :542
  forPy (fun d elem => do                                       -- :543
    let old ← mapping_get d elem N.zero                         -- :544
    let new ← N.add old N.one
    setItem K T d elem new) d iterable

/-- The fast path, Modules/_collectionsmodule.c:2576-2617: the key's own hash, no
`dict_unhashable_type` (:2591-2594), the stored value or `one` itself (:2596-2601), else
`PyNumber_Add(oldval, one)` (:2602-2611). -/
def countCFast (K : KOps κ) (N : Num ν) (d : D κ ν) (it : FIt κ) : Out (D κ ν) :=
  forIt (fun d key => do
    K.hash key
    match D.get? d key with
    | none => pure (D.set d key N.one)
    | some old => do
      let new ← N.add old N.one
      pure (D.set d key new)) d it

/-- The slow path, :2618-2644: `mapping.get` looked up on the instance (:2619), called with
the `zero` object (:2628), `one` itself when the result `is` that `zero` (:2631-2632), else
`PyNumber_Add`, then `PyObject_SetItem`. -/
def countCSlow [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (it : FIt κ) :
    Out (D κ ν) :=
  let bound_get := boundGet K T
  forIt (fun d key => do
    let old ← bound_get d key N.zero
    let new ← if old = N.zero then pure N.one else N.add old N.one
    setItem K T d key new) d it

/-- `_collections__count_elements_impl`, :2544-2655: `PyObject_GetIter` first (:2559-2561),
then the fast path when `type(mapping)` has `dict`'s `get` and `__setitem__` (:2566-2573; a
`Counter` passes `PyDict_Check`). The instance attribute is not consulted by the test. -/
def countC [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (iterable : Py (FIt κ)) :
    Out (D κ ν) :=
  match iterable with
  | .error e => (d, some e)
  | .ok it =>
    if T.typeGet.isNone && T.typeSet.isNone then countCFast K N d it
    else countCSlow K N T d it

/-! ### `update`, `subtract`, the constructor -/

/-- A `Mapping` argument. `store` is `some d` for a `dict` (or a subclass keeping
`dict.__iter__`), whose storage `dict.update` copies (`dict_merge`,
Objects/dictobject.c:4268-4277); otherwise `dict.update` reads `list(m.keys())` and then
`m[k]` (:4279-4333). `items` is `m.items()` with its iteration. -/
structure MSrc (κ ν : Type) where
  store : Option (D κ ν)
  items : Py (FIt (κ × ν))
  keys : Py (List κ)
  getitem : κ → Py ν

/-- A `dict` as a `Mapping` argument. -/
def dictSrc (d : D κ ν) : MSrc κ ν where
  store := some d
  items := .ok (FIt.ofList d)
  keys := .ok (D.keys d)
  getitem k := match D.get? d k with
    | some v => .ok v
    | none => .error (.keyError "~key")

/-- The `iterable` argument: `None`, a `Mapping`, or any other iterable. -/
inductive Src (κ ν : Type) where
  | none
  | mapping (m : MSrc κ ν)
  | iter (it : Py (FIt κ))

/-- `dict.update(self, m)` on a `Mapping` (`dict_update_arg`, Objects/dictobject.c:3992-4005,
then `dict_merge`, :4259-4333): the storage, or the keys list and `m[k]` per key, each stored
with `insertdict`. -/
def dictMerge (K : KOps κ) (d : D κ ν) (m : MSrc κ ν) : Out (D κ ν) :=
  match m.store with
  | some s => (D.update d s, none)
  | none =>
    match m.keys with
    | .error e => (d, some e)
    | .ok ks => loopS (fun d k => do
        let v ← m.getitem k
        dSet K d k v) d ks

/-- The general loop of the `Mapping` branch, :700-702. -/
def updateLoop (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (m : MSrc κ ν) : Out (D κ ν) :=
  let self_get := boundGet K T                                  -- :700
  forPy (fun d (p : κ × ν) => do                                -- :701
    let old ← self_get d p.1 N.zero                             -- :702
    let new ← N.add p.2 old
    setItem K T d p.1 new) d m.items

/-- The `Mapping` branch of `update`, :698-705. -/
def updateMapping (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (m : MSrc κ ν) : Out (D κ ν) :=
  if !d.isEmpty then updateLoop K N T d m                       -- :699-702
  else dictMerge K d m                                          -- :705

/-- The `if iterable is not None` block of `update`, :697-707. -/
def updateSrc [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) : Src κ ν → Out (D κ ν)
  | .none => (d, none)
  | .mapping m => updateMapping K N T d m
  | .iter it => countC K N T d it                               -- :707

/-- `Counter.update(iterable, **kwds)`, :677-709: `self.update(kwds)` is the `Mapping`
branch on the keyword dict. -/
def update [DecidableEq ν] (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (src : Src κ ν)
    (kwds : D κ ν) : Out (D κ ν) :=
  (updateSrc K N T d src).andThen (fun d =>
    if !kwds.isEmpty then updateSrc K N T d (.mapping (dictSrc kwds)) else (d, none))  -- :708-709

/-- The `if iterable is not None` block of `subtract`, :727-734. -/
def subtractSrc (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) : Src κ ν → Out (D κ ν)
  | .none => (d, none)
  | .mapping m =>
    forPy (fun d (p : κ × ν) => do                              -- :730
      let old ← boundGet K T d p.1 N.zero                       -- :731
      let new ← N.sub old p.2
      setItem K T d p.1 new) d m.items
  | .iter it =>
    forPy (fun d elem => do                                     -- :733
      let old ← boundGet K T d elem N.zero                      -- :734
      let new ← N.sub old N.one
      setItem K T d elem new) d it

/-- `Counter.subtract(iterable, **kwds)`, :711-736. -/
def subtract (K : KOps κ) (N : Num ν) (T : CTarget κ ν) (d : D κ ν) (src : Src κ ν) (kwds : D κ ν) :
    Out (D κ ν) :=
  (subtractSrc K N T d src).andThen (fun d =>
    if !kwds.isEmpty then subtractSrc K N T d (.mapping (dictSrc kwds)) else (d, none))  -- :735-736

/-- `Counter(iterable, **kwds)`, :605-617: `dict.__init__` with no arguments, then `update`;
an exception leaves no object. -/
def counterNew [DecidableEq ν] (K : KOps κ) (N : Num ν) (src : Src κ ν) (kwds : D κ ν) : Py (D κ ν) :=
  (update K N {} [] src kwds).toPy

/-! ### Objects, `copy`, `__reduce__` -/

/-- A `Counter` object: an id (`is`), its class (by identity, through its name), its storage. -/
structure CObj (κ ν : Type) where
  id : Nat
  cls : String
  data : D κ ν
  deriving Repr, DecidableEq

/-- A `Counter` as a `Mapping` argument: it keeps `dict.__iter__`, so `dict_merge` copies its
storage. -/
def ctrSrc (d : D κ ν) : MSrc κ ν := dictSrc d

/-- `Counter.copy`, :738-740: `self.__class__(self)`, a new object `fresh` of the same class
built by `__init__` from `self` as a `Mapping`. -/
def counterCopy [DecidableEq ν] (K : KOps κ) (N : Num ν) (fresh : Nat) (c : CObj κ ν) : Py (CObj κ ν) := do
  let data ← counterNew K N (.mapping (ctrSrc c.data)) []
  pure ⟨fresh, c.cls, data⟩

/-- A plain `dict` object. -/
structure DObj (κ ν : Type) where
  id : Nat
  ty : String
  data : D κ ν
  deriving Repr, DecidableEq

/-- `Counter.__reduce__`, :742-743: `(self.__class__, (dict(self),))`, with `dict(self)` a new
`dict` `fresh` (`dict_merge` copies the storage). -/
def counterReduce (fresh : Nat) (c : CObj κ ν) : String × DObj κ ν :=
  (c.cls, ⟨fresh, "dict", D.update [] c.data⟩)

/-- `Counter.total`, :624-626: `sum(self.values())`, with builtin `sum` (Python/bltinmodule.c,
not modelled here) as the parameter `sum`. -/
def total (sum : List ν → Py ν) (d : D κ ν) : Py ν := sum (D.values d)

/-- `Counter.fromkeys`, :665-675: always raises. -/
def counterFromkeys {α : Type} (_iterable : List κ) (_v : Option ν) : Py α :=
  .error (.named "NotImplementedError"
    "Counter.fromkeys() is undefined.  Use Counter(iterable) instead.")

/-- `dict.__delitem__`: `KeyError(key)` on an absent key. -/
def dictDelitem (K : KOps κ) (rk : κ → String) (d : D κ ν) (k : κ) : Py (D κ ν) := do
  dHash K k
  if D.mem d k then pure (D.del d k) else .error (.keyError (rk k))

/-- `Counter.__delitem__`, :745-748: `elem in self` first. -/
def delitem (K : KOps κ) (rk : κ → String) (d : D κ ν) (e : κ) : Py (D κ ν) := do
  let present ← dMem K d e                                       -- :747
  if present then dictDelitem K rk d e else pure d               -- :748

/-! ### `most_common`, `elements`, `__repr__` -/

/-- The objects `sorted` and `nlargest` handle: `(some k, v)` is the item tuple `(k, v)` of
`self.items()`, `(none, v)` the count `v` that `_itemgetter(1)` returns from it. -/
abbrev MObj (κ ν : Type) := Option κ × ν

/-- `_itemgetter(1)`. -/
def getCount (a : MObj κ ν) : MObj κ ν := (none, a.2)

/-- Python code that does not touch the world. -/
def liftPy {β : Type} (p : Py β) : Eff Nat PyExc β := ⟨fun w => (p, w)⟩

/-- The items of a dict as objects. -/
def itemObjs (d : D κ ν) : List (MObj κ ν) := d.map (fun p => (some p.1, p.2))

/-- The callbacks `sorted` and `nlargest` call, over `self.items()` (a sized view that
yields the items): the keys they compare are counts, so `<`, `>` and `==` are the counts'. -/
def mcEnv (N : Num ν) (xs : List (MObj κ ν)) : SEnv Nat (MObj κ ν) HO :=
  { hEnv xs (fun _ _ => false) (.ok xs.length) with
    lt := fun a b => liftPy (N.lt a.2 b.2)
    gt := fun a b => liftPy (N.gt a.2 b.2)
    eq := fun a b => liftPy (N.eq a.2 b.2) }

/-- Back from item objects to pairs. -/
def unObj (l : List (MObj κ ν)) : List (κ × ν) := l.filterMap (fun a => a.1.map (fun k => (k, a.2)))

/-- `Counter.most_common`, :628-640: `sorted(self.items(), key=_itemgetter(1), reverse=True)`
for `n is None` (:637-638), else `heapq.nlargest(n, self.items(), key=_itemgetter(1))` (:640),
the C heap functions under it. `So` is `list.sort`. `n` that is not an int is out of scope. -/
def mostCommon [DecidableEq ν] [Inhabited ν] (N : Num ν) (So : Sorter Nat) (d : D κ ν) (n : Option Int) :
    Py (List (κ × ν)) :=
  let E := mcEnv N (itemObjs d)
  let r := match n with
    | none => pySortedBy E So (some (pureKey getCount)) true .src
    | some n => nSelect E So true true (d.length + 1) n .src (some (pureKey getCount))
  ((r.run 0).1).map unObj

/-- `itertools.repeat(elem, n)`'s `n`: clinic `"O|n"` (Modules/itertoolsmodule.c:3744), so
`__index__` and `Py_ssize_t`, then a negative count is `0` (:3748-3749). -/
def repeatTimes (N : Num ν) (v : ν) : Py Nat := do
  let n ← N.index v
  if n < ssizeMin ∨ n > ssizeMax then .error (.overflowError "Python int too large to convert to C ssize_t")
  else pure n.toNat

/-- `c.elements()`, :642-661: `chain.from_iterable(starmap(repeat, self.items()))`, lazy: the
items of earlier counts come out before a later `repeat()` raises. -/
def elements (N : Num ν) : D κ ν → FIt κ
  | [] => FIt.ofList []
  | (e, v) :: t =>
    match repeatTimes N v with
    | .error ex => ⟨[], some ex⟩
    | .ok m =>
      let r := elements N t
      ⟨List.replicate m e ++ r.xs, r.stop⟩

/-- `dict(pairs)`: `dict_merge_from_seq2`, each pair stored in turn. -/
def dictOfPairs (K : KOps κ) (l : List (κ × ν)) : Py (D κ ν) :=
  (loopS (fun d (p : κ × ν) => dSet K d p.1 p.2) [] l).toPy

/-- `repr(d)` of a non-recursive dict: `dict_repr`, `repr(k): repr(v)` joined by `, `, each
`repr` free to raise. -/
def reprDict (rk : κ → Py String) (rv : ν → Py String) (d : D κ ν) : Py String := do
  let parts ← d.mapM (fun p => do
    let a ← rk p.1
    let b ← rv p.2
    pure (a ++ ": " ++ b))
  pure ("{" ++ ", ".intercalate parts ++ "}")

/-- `Counter.__repr__`, :750-759. `H` is the exception-class relation of `except TypeError`. -/
def counterRepr [DecidableEq ν] [Inhabited ν] (K : KOps κ) (N : Num ν) (So : Sorter Nat) (H : Hier)
    (rk : κ → Py String) (rv : ν → Py String) (cls : String) (d : D κ ν) : Py String :=
  if d.isEmpty then .ok (cls ++ "()")                           -- :751-752
  else do
    let dd ← match mostCommon N So d none >>= dictOfPairs K with  -- :753-755
      | .ok dd => .ok dd
      | .error e => if isA H e "TypeError" then .ok (D.update [] d) else .error e  -- :756-758
    let s ← reprDict rk rv dd
    pure (cls ++ "(" ++ s ++ ")")                               -- :759

/-! ### Rich comparison -/

/-- The right operand of a binary dunder: a `Counter`, or any other object. -/
inductive Opnd (κ ν : Type) where
  | ctr (c : D κ ν)
  | other

/-- `if not isinstance(other, Counter): return NotImplemented`; `none` is `NotImplemented`. -/
def guarded {κ ν β : Type} (f : D κ ν → β) : Opnd κ ν → Option β
  | .ctr b => some (f b)
  | .other => none

/-- `all(r(self[e], other[e]) for c in (self, other) for e in c)`, `self[e]` falling back on
`__missing__`'s `0`. -/
def cmpAll (K : KOps κ) (N : Num ν) (r : ν → ν → Py Bool) (a b : D κ ν) : Py Bool :=
  allM (fun e => do
    let x ← dGet K a e N.zero
    let y ← dGet K b e N.zero
    r x y) (D.keys a ++ D.keys b)

/-- `Counter.__eq__`, :799-803. -/
def eqC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py Bool := cmpAll K N N.eq a b

/-- `Counter.__ne__`, :805-809: `not self == other`. -/
def neC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py Bool := do
  let r ← eqC K N a b
  pure (!r)

/-- `Counter.__le__`, :811-815. -/
def leC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py Bool := cmpAll K N N.le a b

/-- `Counter.__lt__`, :817-821: `self <= other and self != other`. -/
def ltC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py Bool := do
  let l ← leC K N a b
  if l then neC K N a b else pure false

/-- `Counter.__ge__`, :823-827. -/
def geC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py Bool := cmpAll K N N.ge a b

/-- `Counter.__gt__`, :829-833. -/
def gtC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py Bool := do
  let l ← geC K N a b
  if l then neC K N a b else pure false

/-! ### Multiset operators -/

/-- `for elem, count in src.items(): ...; if ...: result[elem] = value`: `f elem count` is the
value to store, if any. -/
def loopInto (K : KOps κ) (f : κ → ν → Py (Option ν)) : D κ ν → D κ ν → Py (D κ ν)
  | r, [] => .ok r
  | r, (e, c) :: t => do
    let o ← f e c
    let r ← match o with
      | some v => dSet K r e v
      | none => pure r
    loopInto K f r t

/-- `elem not in self and count > 0`, the second loop of `+` and `|`. -/
def onlyRightPos (K : KOps κ) (N : Num ν) (a : D κ ν) (e : κ) (count : ν) : Py (Option ν) := do
  let m ← dMem K a e
  if !m then do
    let p ← N.gt count N.zero
    pure (if p then some count else none)
  else pure none

/-- `Counter.__add__`, :842-852. -/
def addC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py (D κ ν) := do
  let r ← loopInto K (fun e count => do
    let o ← dGet K b e N.zero                                   -- :846
    let newcount ← N.add count o
    let p ← N.gt newcount N.zero                                -- :847
    pure (if p then some newcount else none)) [] a
  loopInto K (onlyRightPos K N a) r b                           -- :849-851

/-- `Counter.__sub__`, :861-871. -/
def subC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py (D κ ν) := do
  let r ← loopInto K (fun e count => do
    let o ← dGet K b e N.zero                                   -- :865
    let newcount ← N.sub count o
    let p ← N.gt newcount N.zero                                -- :866
    pure (if p then some newcount else none)) [] a
  loopInto K (fun e count => do                                 -- :868-870
    let m ← dMem K a e
    if !m then do
      let neg ← N.lt count N.zero
      if neg then do
        let v ← N.sub N.zero count
        pure (some v)
      else pure none
    else pure none) r b

/-- `Counter.__or__`, :880-891. -/
def orC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py (D κ ν) := do
  let r ← loopInto K (fun e count => do
    let other_count ← dGet K b e N.zero                         -- :884
    let lt ← N.lt count other_count                             -- :885
    let newcount := if lt then other_count else count
    let p ← N.gt newcount N.zero                                -- :886
    pure (if p then some newcount else none)) [] a
  loopInto K (onlyRightPos K N a) r b                           -- :888-890

/-- `Counter.__and__`, :900-908. -/
def andC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py (D κ ν) :=
  loopInto K (fun e count => do
    let other_count ← dGet K b e N.zero                         -- :904
    let lt ← N.lt count other_count                             -- :905
    let newcount := if lt then count else other_count
    let p ← N.gt newcount N.zero                                -- :906
    pure (if p then some newcount else none)) [] a

/-- `Counter.__xor__`, :910-935. -/
def xorC (K : KOps κ) (N : Num ν) (a b : D κ ν) : Py (D κ ν) := do
  let r ← loopInto K (fun e count => do
    let o ← dGet K b e N.zero                                   -- :929
    let d ← N.sub count o
    let newcount ← N.abs d
    let t ← N.truth newcount                                    -- :930
    pure (if t then some newcount else none)) [] a
  loopInto K (fun e count => do                                 -- :932-934
    let m ← dMem K a e
    if !m then do
      let t ← N.truth count
      if t then do
        let v ← N.abs count
        pure (some v)
      else pure none
    else pure none) r b

/-- `Counter.__pos__`, :937-943. -/
def posC (K : KOps κ) (N : Num ν) (a : D κ ν) : Py (D κ ν) :=
  loopInto K (fun _ count => do
    let p ← N.gt count N.zero                                   -- :941
    pure (if p then some count else none)) [] a

/-- `Counter.__neg__`, :945-954. -/
def negC (K : KOps κ) (N : Num ν) (a : D κ ν) : Py (D κ ν) :=
  loopInto K (fun _ count => do
    let n ← N.lt count N.zero                                   -- :952
    if n then do
      let v ← N.sub N.zero count                                -- :953
      pure (some v)
    else pure none) [] a

/-- `Counter._keep_positive`, :956-961: the list of non-positive keys, then `del self[elem]`
(`Counter.__delitem__`) for each. -/
def keepPositive (K : KOps κ) (rk : κ → String) (N : Num ν) (d : D κ ν) : Out (D κ ν) :=
  match filterPy (fun (p : κ × ν) => do
      let b ← N.gt p.2 N.zero
      pure (!b)) d with                                         -- :958
  | .error e => (d, some e)
  | .ok nonpositive => loopS (fun d (p : κ × ν) => delitem K rk d p.1) d nonpositive  -- :959-960

/-- The right operand of an in-place operator, which has no `isinstance` guard: `items` is
`other.items()` with its iteration (an `AttributeError` for a non-mapping), `getitem` is
`other[elem]` (`0` for a `Counter`, `KeyError` for a plain dict, `TypeError` for an object that
is not subscriptable). -/
structure IOpnd (κ ν : Type) where
  items : Py (FIt (κ × ν))
  getitem : κ → Py ν

/-- A `Counter` as an in-place operand. -/
def ctrOpnd (K : KOps κ) (N : Num ν) (b : D κ ν) : IOpnd κ ν where
  items := .ok (FIt.ofList b)
  getitem e := dGet K b e N.zero

/-- A plain `dict` as an in-place operand: `other[elem]` raises `KeyError(elem)`. -/
def dictOpnd (K : KOps κ) (rk : κ → String) (b : D κ ν) : IOpnd κ ν where
  items := .ok (FIt.ofList b)
  getitem e := do
    dHash K e
    match D.get? b e with
    | some v => pure v
    | none => .error (.keyError (rk e))

/-- `Counter.__iadd__`, :963-974: `self[elem] += count` for each item of `other`, then
`_keep_positive`. -/
def iaddC (K : KOps κ) (rk : κ → String) (N : Num ν) (a : D κ ν) (o : IOpnd κ ν) : Out (D κ ν) :=
  (forPy (fun s (p : κ × ν) => do
    let cur ← dGet K s p.1 N.zero
    let new ← N.iadd cur p.2
    dSet K s p.1 new) a o.items).andThen (keepPositive K rk N)

/-- `Counter.__isub__`, :976-987. -/
def isubC (K : KOps κ) (rk : κ → String) (N : Num ν) (a : D κ ν) (o : IOpnd κ ν) : Out (D κ ν) :=
  (forPy (fun s (p : κ × ν) => do
    let cur ← dGet K s p.1 N.zero
    let new ← N.isub cur p.2
    dSet K s p.1 new) a o.items).andThen (keepPositive K rk N)

/-- `Counter.__ior__`, :989-1002. -/
def iorC (K : KOps κ) (rk : κ → String) (N : Num ν) (a : D κ ν) (o : IOpnd κ ν) : Out (D κ ν) :=
  (forPy (fun s (p : κ × ν) => do
    let count ← dGet K s p.1 N.zero                             -- :999
    let gt ← N.gt p.2 count                                     -- :1000
    if gt then dSet K s p.1 p.2 else pure s) a o.items).andThen (keepPositive K rk N)

/-- `Counter.__iand__`, :1004-1017: over `self.items()`, whose values change as it runs (each
after it was read; no key is added). -/
def iandC (K : KOps κ) (rk : κ → String) (N : Num ν) (a : D κ ν) (o : IOpnd κ ν) : Out (D κ ν) :=
  (loopS (fun s (p : κ × ν) => do
    let other_count ← o.getitem p.1                             -- :1014
    let lt ← N.lt other_count p.2                               -- :1015
    if lt then dSet K s p.1 other_count else pure s) a a).andThen (keepPositive K rk N)

/-- `Counter.__ixor__`, :1019-1033. -/
def ixorC (K : KOps κ) (rk : κ → String) (N : Num ν) (a : D κ ν) (o : IOpnd κ ν) : Out (D κ ν) :=
  ((loopS (fun s (p : κ × ν) => do
    let x ← o.getitem p.1                                       -- :1029
    let d ← N.sub p.2 x
    let v ← N.abs d
    dSet K s p.1 v) a a).andThen (fun s =>
    forPy (fun s (p : κ × ν) => do                              -- :1030-1032
      let m ← dMem K s p.1
      if !m then do
        let v ← N.abs p.2
        dSet K s p.1 v
      else pure s) s o.items)).andThen (keepPositive K rk N)

/-! ### Ints -/

/-- Python ints as counts: exact arithmetic, comparisons that return `bool`. -/
def intNum : Num Int where
  zero := 0
  one := 1
  add a b := .ok (a + b)
  sub a b := .ok (a - b)
  iadd a b := .ok (a + b)
  isub a b := .ok (a - b)
  abs a := .ok (if a < 0 then -a else a)
  lt a b := .ok (decide (a < b))
  gt a b := .ok (decide (a > b))
  le a b := .ok (decide (a ≤ b))
  ge a b := .ok (decide (a ≥ b))
  eq a b := .ok (decide (a = b))
  truth a := .ok (a != 0)
  index a := .ok a

end PyLean.CoreLibs.Coll
