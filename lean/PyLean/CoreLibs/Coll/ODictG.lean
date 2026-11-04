import PyLean.CoreLibs.Coll.UserDictG

/-!
The pure-Python `OrderedDict` of Lib/collections/__init__.py:69-342 (CPython 3.15.2): a dict
(`dict.__setitem__` and friends on `self`), `self.__map` from keys to links, and the circular
doubly linked list of `_Link`s through `self.__root`, over abstract keys with a fallible `__hash__`
(`KOps`, as in `Counter.lean`) and abstract values.

Links live on a heap `heap : Nat → OLink κ` by id; id `0` is `self.__root`, and `next` is the next
fresh id. `prev`/`next` are `none` once `__delitem__` or `pop` has cleared them; `popitem` and
`clear` leave the removed links' pointers in place.

Scope:
* The module replaces this class by the C `_collections.OrderedDict` when `_collections` imports
  (:345-348); `Objects/odictobject.c` is modelled in `DictSet/ODict.lean`. Known differences: the C
  iterator raises `RuntimeError` when the dict changes size or keys during iteration, where the
  generator here goes on, or fails with `AttributeError` once its current link is cleared; and
  `__sizeof__`.
* Keys compare by `DecidableEq` (an `__eq__` that raises is out of scope); `__hash__` may raise.
* `weakref.proxy` identities (`root.prev = proxy(link)`, `soft_link`) are not modelled: a proxy is
  its referent here.
* `update` is `MutableMapping.update` on `UserDictG.USrc` sources.
-/

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- A `_Link` (:85-86): `key` is `none` on the root, `prev`/`next` are `none` once cleared. -/
structure OLink (κ : Type) where
  key : Option κ
  prev : Option Nat
  next : Option Nat

/-- An `OrderedDict` instance. -/
structure OD (κ ν : Type) where
  d : D κ ν
  map : D κ Nat
  heap : Nat → OLink κ
  next : Nat

namespace OD

/-- A new instance, `__new__` (:104-111): `root.prev = root.next = root`, `__map = {}`. -/
def new : OD κ ν := ⟨[], [], fun i => if i = 0 then ⟨none, some 0, some 0⟩ else ⟨none, none, none⟩, 1⟩

def link (o : OD κ ν) (i : Nat) : OLink κ := o.heap i

def setLink (o : OD κ ν) (i : Nat) (f : OLink κ → OLink κ) : OD κ ν :=
  { o with heap := fun j => if j = i then f (o.heap j) else o.heap j }

def setNext (o : OD κ ν) (i n : Nat) : OD κ ν := o.setLink i fun l => { l with next := some n }
def setPrev (o : OD κ ν) (i n : Nat) : OD κ ν := o.setLink i fun l => { l with prev := some n }

/-- The keys from link `i` on, following `next` (`fuel` steps at most). -/
def walk (o : OD κ ν) : Nat → Nat → List κ
  | 0, _ => []
  | f + 1, i =>
    if i = 0 then []
    else match o.link i with
      | ⟨some k, _, some n⟩ => k :: o.walk f n
      | _ => []

/-- `list(od)`: the keys in link order. -/
def keysList (o : OD κ ν) : List κ := o.walk o.next ((o.link 0).next.getD 0)

/-- The keys from link `i` back, following `prev`. -/
def walkBack (o : OD κ ν) : Nat → Nat → List κ
  | 0, _ => []
  | f + 1, i =>
    if i = 0 then []
    else match o.link i with
      | ⟨some k, some p, _⟩ => k :: o.walkBack f p
      | _ => []

/-- `list(reversed(od))`. -/
def keysBack (o : OD κ ν) : List κ := o.walkBack o.next ((o.link 0).prev.getD 0)

end OD

/-- `OrderedDict.__setitem__`, :119-131: `key not in self` (which hashes), a new link at the end
(`self.__map[key] = link`, `link.prev, link.next, link.key = last, root, key`, `last.next = link`,
`root.prev = proxy(link)`), then `dict_setitem(self, key, value)`. -/
def odSet (K : KOps κ) (o : OD κ ν) (key : κ) (value : ν) : Py (OD κ ν) := do
  let inSelf ← dMem K o.d key                                       -- :124
  let o ← if !inSelf then do
      let id := o.next
      let map ← dSet K o.map key id                                 -- :125
      let last := ((o.link 0).prev).getD 0                          -- :126-127
      let o : OD κ ν := { o with map, next := id + 1 }
      let o := o.setLink id fun _ => ⟨some key, some last, some 0⟩  -- :128
      let o := o.setNext last id                                    -- :129
      pure (o.setPrev 0 id)                                         -- :130
    else pure o
  let d ← dSet K o.d key value                                      -- :131
  pure { o with d }

/-- Unlink `link` and clear its pointers (:138-144). -/
def odDropLink (o : OD κ ν) (link : Nat) : OD κ ν :=
  let lp := ((o.link link).prev).getD 0
  let ln := ((o.link link).next).getD 0
  let o := o.setNext lp ln
  let o := o.setPrev ln lp
  o.setLink link fun l => { l with prev := none, next := none }

/-- `OrderedDict.__delitem__`, :133-144: `dict_delitem(self, key)` (its `KeyError`), then
`self.__map.pop(key)` and the unlinking. -/
def odDel (K : KOps κ) (rk : κ → String) (o : OD κ ν) (key : κ) : Py (OD κ ν) := do
  let d ← dictDelitem K rk o.d key                                  -- :137
  let link := (D.get? o.map key).getD 0                             -- :138
  let o : OD κ ν := { o with d, map := D.del o.map key }
  pure (odDropLink o link)

/-- `OrderedDict.clear`, :164-169. -/
def odClear (o : OD κ ν) : OD κ ν :=
  let o := (o.setPrev 0 0).setNext 0 0
  { o with map := [], d := [] }

/-- `OrderedDict.popitem`, :171-192: the end link unlinked (its own pointers left as they were),
`del self.__map[key]`, `dict.pop(self, key)`. -/
def odPopitem (rk : κ → String) (o : OD κ ν) (last : Bool) : Py ((κ × ν) × OD κ ν) :=
  if o.d.isEmpty then .error (keyErrorStr "dictionary is empty")    -- :176-177
  else
    let (link, o) :=
      if last then
        let link := ((o.link 0).prev).getD 0                        -- :180
        let lp := ((o.link link).prev).getD 0
        (link, (o.setNext lp 0).setPrev 0 lp)                       -- :181-183
      else
        let link := ((o.link 0).next).getD 0                        -- :185
        let ln := ((o.link link).next).getD 0
        (link, (o.setNext 0 ln).setPrev ln 0)                       -- :186-188
    match (o.link link).key with
    | none => .error (keyErrorStr "dictionary is empty")
    | some key =>
      match D.get? o.d key with                                     -- :190
      | some value => .ok ((key, value), { o with map := D.del o.map key, d := D.del o.d key })
      | none => .error (.keyError (rk key))

/-- `OrderedDict.move_to_end`, :194-217: `link = self.__map[key]` (`KeyError(key)`), unlink it, and
put it last (or first). -/
def odMoveToEnd (K : KOps κ) (rk : κ → String) (o : OD κ ν) (key : κ) (last : Bool) : Py (OD κ ν) := do
  dHash K key
  match D.get? o.map key with
  | none => .error (.keyError (rk key))                             -- :199
  | some link =>
    let lp := ((o.link link).prev).getD 0                           -- :200
    let ln := ((o.link link).next).getD 0                           -- :201
    let o := (o.setNext lp ln).setPrev ln lp                        -- :203-204
    if last then
      let l := ((o.link 0).prev).getD 0                             -- :207
      let o := o.setLink link fun x => { x with prev := some l, next := some 0 }  -- :208-209
      pure ((o.setPrev 0 link).setNext l link)                      -- :210-211
    else
      let first := ((o.link 0).next).getD 0                         -- :213
      let o := o.setLink link fun x => { x with prev := some 0, next := some first }  -- :214-215
      pure ((o.setPrev first link).setNext 0 link)                  -- :216-217

/-- `OrderedDict.pop`, :245-265: `dict.pop(self, key, marker)`; if a value came back, drop the link as
`__delitem__` does; else the default, or `KeyError(key)` when none was given (the `__marker`). -/
def odPop (K : KOps κ) (rk : κ → String) (o : OD κ ν) (key : κ) (dflt : Option ν) : Py (ν × OD κ ν) := do
  -- `pop_lock_held` (Objects/dictobject.c:3295-3300): an empty dict answers "absent" before hashing.
  if !o.d.isEmpty then dHash K key
  match D.get? o.d key with
  | some result =>
    let link := (D.get? o.map key).getD 0
    pure (result, odDropLink { o with d := D.del o.d key, map := D.del o.map key } link)
  | none =>
    match dflt with
    | some v => pure (v, o)
    | none => .error (.keyError (rk key))

/-- `OrderedDict.setdefault`, :267-276. -/
def odSetdefault (K : KOps κ) (o : OD κ ν) (key : κ) (dflt : ν) : Py (ν × OD κ ν) := do
  let inSelf ← dMem K o.d key
  if inSelf then pure ((D.get? o.d key).getD dflt, o)
  else do
    let o ← odSet K o key dflt
    pure (dflt, o)

/-- `MutableMapping.update` (Lib/_collections_abc.py:965-984) with `self[key] = value` as
`__setitem__`: `OrderedDict.update` and `__init__` (:113-117). -/
def odUpdate (K : KOps κ) (o : OD κ ν) : USrc κ ν → Out (OD κ ν)
  | .mapping ks g | .keyed ks g => forPy (fun o k => do
      let v ← g k
      odSet K o k v) o ks
  | .pairs it => forPy (fun o p => do
      let (k, v) ← p
      odSet K o k v) o it

/-- An `OrderedDict` as a `Mapping` source: `for key in other` walks its links, `other[key]` is the
dict's value. -/
def odSrc (o : OD κ ν) : USrc κ ν :=
  .mapping (.ok (FIt.ofList o.keysList)) (fun k => match D.get? o.d k with
    | some v => .ok v
    | none => .error (.keyError "~key"))

/-- `OrderedDict.copy`, :303-306, `self.__class__(self)`: a new instance updated from `self`. -/
def odCopy (K : KOps κ) (o : OD κ ν) : Py (OD κ ν) := (odUpdate K OD.new (odSrc o)).toPy

/-- `OrderedDict.fromkeys`, :308-314. -/
def odFromkeys (K : KOps κ) (it : Py (FIt κ)) (value : ν) : Py (OD κ ν) :=
  (forPy (fun o k => odSet K o k value) OD.new it).toPy

/-- `dict.__eq__` between two dicts: equal length and every key of `a` in `b` with an equal value
(`PyObject_RichCompareBool`, identity first: `veq` is called on non-identical values). -/
def dictEq [DecidableEq ν] (veq : ν → ν → Py Bool) (a b : D κ ν) : Py Bool :=
  if a.length ≠ b.length then .ok false
  else allM (fun p => match D.get? b p.1 with
    | none => .ok false
    | some w => if p.2 = w then .ok true else veq p.2 w) a

/-- The right operand of `==`: an `OrderedDict`, or a plain dict. -/
inductive ODOpnd (κ ν : Type) where
  | od (o : OD κ ν)
  | dict (d : D κ ν)

/-- `OrderedDict.__eq__`, :316-324: `dict.__eq__(self, other) and all(map(_eq, self, other))` for an
`OrderedDict`, `dict.__eq__` otherwise. Keys compare by `DecidableEq`. -/
def odEq [DecidableEq ν] (veq : ν → ν → Py Bool) (o : OD κ ν) : ODOpnd κ ν → Py Bool
  | .od p => do
    let e ← dictEq veq o.d p.d
    if e then pure ((o.keysList.zip p.keysList).all (fun q => decide (q.1 = q.2))) else pure false
  | .dict d => dictEq veq o.d d

/-- `OrderedDict.__reduce__`, :285-301, for an instance without other attributes: `(cls, (), None,
None, iter(self.items()))`, the items in link order. -/
def odReduce (cls : String) (o : OD κ ν) : String × List (κ × ν) :=
  (cls, o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·)))

/-- `OrderedDict.__ior__`, :325-327: `self.update(other)`, then `self`. -/
def odIor (K : KOps κ) (o : OD κ ν) (other : USrc κ ν) : Out (OD κ ν) := odUpdate K o other

/-- `OrderedDict.__or__`, :329-334: `NotImplemented` (`none`) unless `other` is a dict or frozendict;
else `new = self.__class__(self); new.update(other)`. -/
def odOr (K : KOps κ) (o : OD κ ν) (other : Option (USrc κ ν)) : Option (Py (OD κ ν)) :=
  other.map fun s => do
    let n ← odCopy K o
    (odUpdate K n s).toPy

/-- `OrderedDict.__ror__`, :336-342: `new = self.__class__(other); new.update(self)`. -/
def odRor (K : KOps κ) (o : OD κ ν) (other : Option (USrc κ ν)) : Option (Py (OD κ ν)) :=
  other.map fun s => do
    let n ← (odUpdate K OD.new s).toPy
    (odUpdate K n (odSrc o)).toPy

/-- `OrderedDict.__repr__`, :278-283, without recursion: `Cls()` when empty, else
`Cls(%r)` of `dict(self.items())`, the items in link order. -/
def odRepr (rk : κ → Py String) (rv : ν → Py String) (cls : String) (o : OD κ ν) : Py String :=
  if o.d.isEmpty then .ok (cls ++ "()")
  else do
    let s ← reprDict rk rv (o.keysList.filterMap (fun k => (D.get? o.d k).map (k, ·)))
    pure (cls ++ "(" ++ s ++ ")")

/-! ### Iteration -/

/-- The state of the `__iter__` / `__reversed__` generator (:146-162): not started, suspended after
yielding the key of link `i`, or finished. -/
inductive OGen where
  | fresh
  | at_ (i : Nat)
  | done
  deriving DecidableEq

/-- `next(gen)`: `curr = curr.next` (or `.prev`) on resumption, then `curr.key`; a link whose pointers
were cleared gives `curr = None`, and `None.key` raises `AttributeError`, ending the generator. -/
def odGenNext (o : OD κ ν) (rev : Bool) : OGen → Py (Option κ) × OGen
  | .done => (.ok none, .done)
  | g =>
    let from_ := match g with | .at_ i => i | _ => 0
    let dir := if rev then (o.link from_).prev else (o.link from_).next
    match dir with
    | none => (.error (.named "AttributeError" "'NoneType' object has no attribute 'key'"), .done)
    | some n =>
      if n = 0 then (.ok none, .done)
      else match (o.link n).key with
        | some k => (.ok (some k), .at_ n)
        | none => (.ok none, .done)

/-- Running the generator to the end without mutation (`fuel` steps). -/
def odGenRun (o : OD κ ν) (rev : Bool) : Nat → OGen → Py (List κ)
  | 0, _ => .ok []
  | f + 1, g =>
    match odGenNext o rev g with
    | (.ok none, _) => .ok []
    | (.ok (some k), g') => (odGenRun o rev f g').map (k :: ·)
    | (.error e, _) => .error e

end PyLean.CoreLibs.Coll
