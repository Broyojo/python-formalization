import PyLean.Accel.Select
import PyLean.CoreLibs.Coll.Dict

/-!
`collections.Counter` and `_count_elements`, Lib/collections/__init__.py:540-1017 and
Modules/_collectionsmodule.c:2544-2644 (CPython 3.15.2).

Keys are abstract (see `Dict.lean`). Counts are Python ints; the docs allow any
number, but only ints have exact arithmetic here, and the methods use nothing but
`+`, `-`, `<`, `>` and `==` on them. Non-number counts are a `TypeError` in most
paths and are out of scope, as the multiset operators are documented for ints.

`Counter` subclasses are out of scope for the multiset operators, which build a
plain `Counter()` regardless of `self.__class__`.
-/

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ : Type} [DecidableEq κ]

/-- A `Counter` is a dict from elements to integer counts. -/
abbrev Ctr (κ : Type) := D κ Int

/-- `self[e]`: `dict.__getitem__` falling back on `Counter.__missing__`, :619-622. -/
def cGet (c : Ctr κ) (e : κ) : Int := (D.get? c e).getD 0

/-- `self.get(e, 0)`. -/
def cGet0 (c : Ctr κ) (e : κ) : Int := (D.get? c e).getD 0

/-! ### `_count_elements` -/

/-- The pure-Python `_count_elements`, :540-544. It is shadowed by the C helper. -/
def countElementsPy (m : Ctr κ) (it : List κ) : Ctr κ :=
  it.foldl (fun m e => D.set m e (cGet0 m e + 1)) m

/-- The fast path of `_collections__count_elements_impl`,
Modules/_collectionsmodule.c:2572-2617: `get` and `__setitem__` not overridden. A missing key
stores `1` without adding, a present one stores `oldval + 1`. -/
def countElementsCFast (m : Ctr κ) (it : List κ) : Ctr κ :=
  it.foldl (fun m e =>
    match D.get? m e with
    | none => D.set m e 1
    | some old => D.set m e (old + 1)) m

/-- The slow path, Modules/_collectionsmodule.c:2618-2644: `mapping.get(key, 0)`, then
`one` when the result is the `zero` object, else `oldval + 1`. `oldval == zero`
compares identity with the small-int singleton, and every int `0` is that object. -/
def countElementsCSlow (m : Ctr κ) (it : List κ) : Ctr κ :=
  it.foldl (fun m e =>
    let oldval := cGet0 m e
    D.set m e (if oldval = 0 then 1 else oldval + 1)) m

/-- What `_count_elements` does at run time on a `Counter`: `get` and
`__setitem__` are `dict`'s, so the fast path. -/
def countElements (m : Ctr κ) (it : List κ) : Ctr κ := countElementsCFast m it

/-! ### `update`, `subtract`, the constructor -/

/-- The `iterable` argument: `None`, a `Mapping` (by its `.items()`), or any
other iterable (by its elements). -/
inductive Src (κ : Type) where
  | none
  | mapping (items : List (κ × Int))
  | iter (xs : List κ)
  deriving Repr, DecidableEq

/-- The `Mapping` branch of `update`, :698-705. -/
def updateMapping (c : Ctr κ) (items : List (κ × Int)) : Ctr κ :=
  if c ≠ [] then
    items.foldl (fun c p => D.set c p.1 (p.2 + cGet0 c p.1)) c
  else
    D.update c items

/-- The `if iterable is not None` block of `update`, :697-707. -/
def updateSrc (c : Ctr κ) : Src κ → Ctr κ
  | .none => c
  | .mapping items => updateMapping c items
  | .iter xs => countElements c xs

/-- `Counter.update(iterable, **kwds)`, :677-709. `self.update(kwds)` is the
same function on a dict and no keywords. -/
def update (c : Ctr κ) (src : Src κ) (kwds : List (κ × Int)) : Ctr κ :=
  let c := updateSrc c src
  if kwds ≠ [] then updateMapping c kwds else c

/-- The `if iterable is not None` block of `subtract`, :727-734. -/
def subtractSrc (c : Ctr κ) : Src κ → Ctr κ
  | .none => c
  | .mapping items => items.foldl (fun c p => D.set c p.1 (cGet0 c p.1 - p.2)) c
  | .iter xs => xs.foldl (fun c e => D.set c e (cGet0 c e - 1)) c

/-- `Counter.subtract(iterable, **kwds)`, :711-736. -/
def subtract (c : Ctr κ) (src : Src κ) (kwds : List (κ × Int)) : Ctr κ :=
  let c := subtractSrc c src
  if kwds ≠ [] then subtractSrc c (.mapping kwds) else c

/-- `Counter(iterable, **kwds)`, :605-617. -/
def counterNew (src : Src κ) (kwds : List (κ × Int)) : Ctr κ := update [] src kwds

/-- `Counter.copy`, :738-740, `self.__class__(self)`: a `Counter` is a `Mapping`. -/
def counterCopy (c : Ctr κ) : Ctr κ := counterNew (.mapping c) []

/-- `Counter.__reduce__`, :742-743: the constructor and `dict(self)`, as data. -/
def counterReduce (c : Ctr κ) : D κ Int := D.update [] c

/-- `Counter.total`, :624-626. -/
def total (c : Ctr κ) : Int := (D.values c).foldl (· + ·) 0

/-- `Counter.fromkeys`, :665-675: always raises. -/
def counterFromkeys {α : Type} (_iterable : List κ) (_v : Option Int) : Py α :=
  .error (.named "NotImplementedError"
    "Counter.fromkeys() is undefined.  Use Counter(iterable) instead.")

/-- `Counter.__delitem__`, :745-748. -/
def delitem (c : Ctr κ) (e : κ) : Ctr κ := if D.mem c e then D.del c e else c

/-! ### `most_common`, `elements`, `__repr__` -/

/-- The positions `0 .. len-1` of the items, which stand for the items
themselves in the int-only `sorted` and `heapq.nlargest` models of `Accel`:
those functions only move elements around and look at them through `key`. -/
def indices (c : Ctr κ) : List Int := (List.range c.length).map Int.ofNat

/-- `_itemgetter(1)` on the item at a position. -/
def countAt (c : Ctr κ) (i : Int) : Int := ((c[i.toNat]?).map (·.2)).getD 0

/-- Items at the given positions. -/
def atIndices (c : Ctr κ) (is : List Int) : List (κ × Int) := is.filterMap (fun i => c[i.toNat]?)

/-- `sorted(self.items(), key=_itemgetter(1), reverse=True)`, :638. -/
def sortedItems (c : Ctr κ) : List (κ × Int) :=
  atIndices c (Accel.pySortedRev (some (countAt c)) (indices c))

/-- `Counter.most_common`, @3.14.7:628-645. `self.items()` is sized. -/
def mostCommon (c : Ctr κ) : Option Int → Py (List (κ × Int))
  | none => .ok (sortedItems c)
  | some n => do
    let r ← Accel.nlargest n (indices c) true (some (countAt c))
    return atIndices c r

/-- `itertools.repeat(elem, n)`: the clinic `Py_ssize_t` conversion of `n`
(Modules/itertoolsmodule.c), then nothing for `n <= 0`. -/
def repeatCount (n : Int) : Py Nat :=
  if n < ssizeMin ∨ n > ssizeMax then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok n.toNat

/-- `list(c.elements())`, :642-661: `chain.from_iterable(starmap(repeat, self.items()))`. -/
def elements : Ctr κ → Py (List κ)
  | [] => .ok []
  | (e, n) :: t => do
    let m ← repeatCount n
    let r ← elements t
    return List.replicate m e ++ r

/-- `repr` of a dict with int values, given `repr` on keys. -/
def dictRepr (rk : κ → String) (items : List (κ × Int)) : String :=
  "{" ++ ", ".intercalate (items.map (fun p => rk p.1 ++ ": " ++ toString p.2)) ++ "}"

/-- `Counter.__repr__`, :750-759. `self.most_common()` cannot raise on int
counts, so the `except TypeError` branch is not reachable here. -/
def counterRepr (cls : String) (rk : κ → String) (c : Ctr κ) : String :=
  if c.isEmpty then cls ++ "()"
  else cls ++ "(" ++ dictRepr rk (D.update [] (sortedItems c)) ++ ")"

/-! ### Rich comparison -/

/-- `all(r(self[e], other[e]) for c in (self, other) for e in c)`. -/
def cmpAll (r : Int → Int → Bool) (a b : Ctr κ) : Bool :=
  a.all (fun p => r (cGet a p.1) (cGet b p.1)) && b.all (fun p => r (cGet a p.1) (cGet b p.1))

/-- `Counter.__eq__`, :799-803. -/
def eqC (a b : Ctr κ) : Bool := cmpAll (fun x y => decide (x = y)) a b

/-- `Counter.__ne__`, :805-809. -/
def neC (a b : Ctr κ) : Bool := !eqC a b

/-- `Counter.__le__`, :811-815. -/
def leC (a b : Ctr κ) : Bool := cmpAll (fun x y => decide (x ≤ y)) a b

/-- `Counter.__lt__`, :817-821. -/
def ltC (a b : Ctr κ) : Bool := leC a b && neC a b

/-- `Counter.__ge__`, :823-827. -/
def geC (a b : Ctr κ) : Bool := cmpAll (fun x y => decide (x ≥ y)) a b

/-- `Counter.__gt__`, :829-833. -/
def gtC (a b : Ctr κ) : Bool := geC a b && neC a b

/-! ### Multiset operators -/

/-- One `for elem, count in src.items(): ...; if cond: result[elem] = value`
loop: `f elem count` is the value to store, if any. Every operator is one or
two of these. -/
def loopInto (src : Ctr κ) (f : κ → Int → Option Int) (r : Ctr κ) : Ctr κ :=
  src.foldl (fun r p =>
    match f p.1 p.2 with
    | some n => D.set r p.1 n
    | none => r) r

/-- `Counter.__add__`, :842-852. -/
def addC (a b : Ctr κ) : Ctr κ :=
  let r := loopInto a (fun e count =>
    let newcount := count + cGet b e
    if newcount > 0 then some newcount else none) []
  loopInto b (fun e count => if !D.mem a e && decide (count > 0) then some count else none) r

/-- `Counter.__sub__`, :861-871. -/
def subC (a b : Ctr κ) : Ctr κ :=
  let r := loopInto a (fun e count =>
    let newcount := count - cGet b e
    if newcount > 0 then some newcount else none) []
  loopInto b (fun e count => if !D.mem a e && decide (count < 0) then some (0 - count) else none) r

/-- `Counter.__or__`, :880-891. -/
def orC (a b : Ctr κ) : Ctr κ :=
  let r := loopInto a (fun e count =>
    let other_count := cGet b e
    let newcount := if count < other_count then other_count else count
    if newcount > 0 then some newcount else none) []
  loopInto b (fun e count => if !D.mem a e && decide (count > 0) then some count else none) r

/-- `Counter.__and__`, :900-908. -/
def andC (a b : Ctr κ) : Ctr κ :=
  loopInto a (fun e count =>
    let other_count := cGet b e
    let newcount := if count < other_count then count else other_count
    if newcount > 0 then some newcount else none) []

/-- `abs` of an `int`. -/
def absI (x : Int) : Int := if x < 0 then -x else x

/-- `Counter.__xor__`, Lib/collections/__init__.py:910-935. -/
def xorC (a b : Ctr κ) : Ctr κ :=
  let r := loopInto a (fun e count =>
    let newcount := absI (count - cGet b e)
    if newcount ≠ 0 then some newcount else none) []
  loopInto b (fun e count => if !D.mem a e && decide (count ≠ 0) then some (absI count) else none) r

/-- `Counter.__pos__`, :937-943. -/
def posC (a : Ctr κ) : Ctr κ := loopInto a (fun _ count => if count > 0 then some count else none) []

/-- `Counter.__neg__`, :945-954. -/
def negC (a : Ctr κ) : Ctr κ :=
  loopInto a (fun _ count => if count < 0 then some (0 - count) else none) []

/-- `Counter._keep_positive`, :956-961. -/
def keepPositive (c : Ctr κ) : Ctr κ :=
  let nonpositive := (c.filter (fun p => !decide (p.2 > 0))).map (·.1)
  nonpositive.foldl delitem c

/-- `Counter.__iadd__`, :972-974, on the items of `other`. -/
def iaddC (a : Ctr κ) (items : List (κ × Int)) : Ctr κ :=
  keepPositive (items.foldl (fun s p => D.set s p.1 (cGet s p.1 + p.2)) a)

/-- `Counter.__isub__`, @3.14.7:959-961. -/
def isubC (a : Ctr κ) (items : List (κ × Int)) : Ctr κ :=
  keepPositive (items.foldl (fun s p => D.set s p.1 (cGet s p.1 - p.2)) a)

/-- `Counter.__ior__`, @3.14.7:972-976. -/
def iorC (a : Ctr κ) (items : List (κ × Int)) : Ctr κ :=
  keepPositive (items.foldl (fun s p =>
    let count := cGet s p.1
    if p.2 > count then D.set s p.1 p.2 else s) a)

/-- `Counter.__iand__`, :1013-1017, with `other[elem]` given by `other`: `cGet`
for a `Counter`, or a plain-dict lookup that raises `KeyError`. `self.items()` is
iterated live, but only the values change. -/
def iandWith (a : Ctr κ) (other : κ → Py Int) : Py (Ctr κ) := do
  let s ← a.foldlM (fun s p => do
    let other_count ← other p.1
    pure (if other_count < cGet s p.1 then D.set s p.1 other_count else s)) a
  return keepPositive s

/-- `self &= other` for a `Counter`: `other[elem]` cannot fail. -/
def iandC (a b : Ctr κ) : Ctr κ :=
  match iandWith a (fun e => .ok (cGet b e)) with
  | .ok r => r
  | .error _ => a

/-- `Counter.__ixor__`, Lib/collections/__init__.py:1019-1033. `other` is `other[elem]`, `items` is `other.items()`. The values
of `self.items()` change as the first loop runs, but each one only after it was read. -/
def ixorWith (a : Ctr κ) (other : κ → Py Int) (items : List (κ × Int)) : Py (Ctr κ) := do
  let s ← a.foldlM (fun s p => do
    let o ← other p.1
    pure (D.set s p.1 (absI (p.2 - o)))) a
  let s := items.foldl (fun s p => if D.mem s p.1 then s else D.set s p.1 (absI p.2)) s
  return keepPositive s

/-- `self ^= other` for a `Counter`: `other[elem]` cannot fail. -/
def ixorC (a b : Ctr κ) : Ctr κ :=
  match ixorWith a (fun e => .ok (cGet b e)) b with
  | .ok r => r
  | .error _ => a

/-- The right operand of an in-place operator. These methods have no
`isinstance` guard: a `Counter` and a plain `Mapping` both work, up to the
missing-key behaviour of `other[elem]`, and anything else fails on `.items()`
or on the subscript. `ty` is the operand's type name. -/
inductive IOpnd (κ : Type) where
  | ctr (c : Ctr κ)
  | dict (d : D κ Int)
  | nonmapping (ty : String)
  deriving Repr, DecidableEq

/-- `AttributeError` of `other.items()` on a non-mapping. -/
def noItems (ty : String) : PyExc := .named "AttributeError" s!"'{ty}' object has no attribute 'items'"

def dunderIadd (a : Ctr κ) : IOpnd κ → Py (Ctr κ)
  | .ctr b | .dict b => .ok (iaddC a b)
  | .nonmapping ty => .error (noItems ty)

def dunderIsub (a : Ctr κ) : IOpnd κ → Py (Ctr κ)
  | .ctr b | .dict b => .ok (isubC a b)
  | .nonmapping ty => .error (noItems ty)

def dunderIor (a : Ctr κ) : IOpnd κ → Py (Ctr κ)
  | .ctr b | .dict b => .ok (iorC a b)
  | .nonmapping ty => .error (noItems ty)

/-- `__iand__`, given `repr` of keys for the `KeyError` of a plain dict. -/
def dunderIand (rk : κ → String) (a : Ctr κ) : IOpnd κ → Py (Ctr κ)
  | .ctr b => iandWith a (fun e => .ok (cGet b e))
  | .dict b => iandWith a (fun e =>
      match D.get? b e with
      | some n => .ok n
      | none => .error (.keyError (rk e)))
  | .nonmapping ty => iandWith a (fun _ => .error (.typeError s!"'{ty}' object is not subscriptable"))

/-- `__ixor__`: a non-mapping fails on the subscript, or on `.items()` when the left operand is empty. -/
def dunderIxor (rk : κ → String) (a : Ctr κ) : IOpnd κ → Py (Ctr κ)
  | .ctr b => ixorWith a (fun e => .ok (cGet b e)) b
  | .dict b => ixorWith a (fun e =>
      match D.get? b e with
      | some n => .ok n
      | none => .error (.keyError (rk e))) b
  | .nonmapping ty =>
    if a.isEmpty then .error (noItems ty)
    else ixorWith a (fun _ => .error (.typeError s!"'{ty}' object is not subscriptable")) []

/-! ### Operands that are not `Counter`s -/

/-- The right operand of a dunder: a `Counter`, or anything else. -/
inductive Opnd (κ : Type) where
  | ctr (c : Ctr κ)
  | other
  deriving Repr, DecidableEq

/-- The `if not isinstance(other, Counter): return NotImplemented` guard shared
by `__eq__`, ..., `__and__`; `none` is `NotImplemented`. -/
def guarded {β : Type} (f : Ctr κ → β) : Opnd κ → Option β
  | .ctr b => some (f b)
  | .other => none

end PyLean.CoreLibs.Coll
