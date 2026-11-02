import PyLean.Core

/-!
`Lib/weakref.py`, CPython 3.14.7.

Object death is an explicit event. `World` is the set of dead object ids, and a weak reference holds
the id of its referent, so `wr()` is `none` once the id is in the set. In this version
`WeakValueDictionary` has neither `_pending_removals` nor `_IterationGuard`: the callback removes
the entry at once (`_remove_dead_weakref`, Modules/_weakref.c), which is `WVD.onDeath`. The field
`eager` is false when `self._remove` has been replaced by a no-op, which is how the branches for a
dead reference left in `data` (for example Lib/weakref.py:117, :167, :207) become reachable in a
single thread.

A value is an object or something that cannot be weakly referenced (`PV`). `eqv` is `__eq__` on
live objects, which `WeakKeyDictionary` needs because a `ref` hashes and compares as its referent.
Dictionaries are association lists in insertion order, as Python dicts are.
-/

namespace PyLean.CoreLibs.Misc.Weakref

open PyLean

/-- A value: an object with an id, or an int, which `ref()` refuses. -/
inductive PV where
  | obj (id : Nat)
  | int (n : Int)
  deriving Repr, DecidableEq, Inhabited

/-- The dead objects. -/
abbrev World := List Nat

def alive (w : World) (o : Nat) : Bool := !w.contains o

/-- `ref(v)`: Objects/weakrefobject.c refuses a type without weak-reference support. -/
def refOf (v : PV) : Py Nat :=
  match v with
  | .obj i => .ok i
  | .int _ => .error (.typeError "cannot create weak reference to 'int' object")

/-- `wr()` for a reference to `o`. -/
def deref (w : World) (o : Nat) : Option PV := if alive w o then some (.obj o) else none

/-! ### Dict operations -/

section Dict
variable {K β : Type} [DecidableEq K]

def dGet (d : List (K × β)) (k : K) : Option β := d.lookup k

/-- `d[k] = v`: an existing key keeps its position. -/
def dSet (d : List (K × β)) (k : K) (v : β) : List (K × β) :=
  match d with
  | [] => [(k, v)]
  | (a, b) :: rest => if a = k then (a, v) :: rest else (a, b) :: dSet rest k v

def dDel (d : List (K × β)) (k : K) : List (K × β) :=
  match d with
  | [] => []
  | (a, b) :: rest => if a = k then rest else (a, b) :: dDel rest k

/-- `d.popitem()` removes the last item. -/
def dPopLast (d : List (K × β)) : Option ((K × β) × List (K × β)) :=
  match d.getLast? with
  | none => none
  | some kv => some (kv, d.dropLast)

/-- `dict(pairs)`: a repeated key keeps its first position and its last value. -/
def dictFrom (pairs : List (K × β)) : List (K × β) :=
  pairs.foldl (fun d kv => dSet d kv.1 kv.2) []

end Dict

/-! ### `KeyedRef` and `WeakValueDictionary` -/

/-- `KeyedRef`, Lib/weakref.py:277-295: `__new__` and `__init__` store the referent and `key`. -/
structure KRef (K : Type) where
  ob : Nat
  key : K
  deriving Repr, DecidableEq

/-- `KeyedRef.__new__`, Lib/weakref.py:289-292; `KeyedRef.__init__`, :294-295, adds nothing. -/
def KRef.new {K : Type} (v : PV) (key : K) : Py (KRef K) := do
  return { ob := ← refOf v, key }

/-- The attributes of a `WeakValueDictionary`, Lib/weakref.py:104-113. -/
structure WVD (K : Type) where
  data : List (K × KRef K)
  eager : Bool
  deriving Repr

/-- Rendering of `KeyError(key)`. -/
abbrev ReprK (K : Type) := K → String

/-- `popitem` on an empty dict. -/
def popEmpty : PyExc := .keyError "'popitem(): dictionary is empty'"

namespace WVD

variable {K : Type} [DecidableEq K]

/-- The callback of every `KeyedRef` of `o`: `_remove_dead_weakref(self.data, wr.key)`,
Lib/weakref.py:105-110. -/
def onDeath (d : WVD K) (o : Nat) : WVD K :=
  if d.eager then { d with data := d.data.filter (fun kv => kv.2.ob ≠ o) } else d

/-- `WeakValueDictionary.__getitem__`, Lib/weakref.py:115-120. -/
def getitem (r : ReprK K) (w : World) (d : WVD K) (key : K) : Py PV :=
  match dGet d.data key with
  | none => .error (.keyError (r key))
  | some wr =>
    match deref w wr.ob with
    | none => .error (.keyError (r key))
    | some o => .ok o

/-- `WeakValueDictionary.__delitem__`, Lib/weakref.py:122-123. -/
def delitem (r : ReprK K) (d : WVD K) (key : K) : Py (WVD K) :=
  match dGet d.data key with
  | none => .error (.keyError (r key))
  | some _ => .ok { d with data := dDel d.data key }

/-- `WeakValueDictionary.__len__`, Lib/weakref.py:125-126: dead entries left in `data` count. -/
def len (d : WVD K) : Nat := d.data.length

/-- `WeakValueDictionary.__contains__`, Lib/weakref.py:128-133. -/
def contains (w : World) (d : WVD K) (key : K) : Bool :=
  match dGet d.data key with
  | none => false
  | some wr => (deref w wr.ob).isSome

/-- `WeakValueDictionary.__repr__`, Lib/weakref.py:135-136, with `addr` for `hex(id(self))`. -/
def repr (className addr : String) : String := s!"<{className} at {addr}>"

/-- `WeakValueDictionary.__setitem__`, Lib/weakref.py:138-139. -/
def setitem (d : WVD K) (key : K) (value : PV) : Py (WVD K) := do
  let r ← KRef.new value key
  return { d with data := dSet d.data key r }

/-- A new empty dictionary, with the callback of its class. -/
def empty : WVD K := { data := [], eager := true }

/-- The live items in order, the loop of `items`, Lib/weakref.py:173-177, and of `copy`, :141-147. -/
def liveItems (w : World) (d : WVD K) : List (K × PV) :=
  d.data.filterMap (fun kv => (deref w kv.2.ob).map (fun o => (kv.1, o)))

/-- `WeakValueDictionary.items`, Lib/weakref.py:173-177. -/
def items (w : World) (d : WVD K) : List (K × PV) := liveItems w d

/-- `WeakValueDictionary.copy`, Lib/weakref.py:141-147. -/
def copy (w : World) (d : WVD K) : Py (WVD K) :=
  (liveItems w d).foldlM (fun n kv => setitem n kv.1 kv.2) empty

/-- `WeakValueDictionary.__deepcopy__`, Lib/weakref.py:151-158: keys are deep-copied, values not. -/
def deepcopy (dc : K → K) (w : World) (d : WVD K) : Py (WVD K) :=
  (liveItems w d).foldlM (fun n kv => setitem n (dc kv.1) kv.2) empty

/-- `WeakValueDictionary.get`, Lib/weakref.py:160-171. -/
def get (w : World) (d : WVD K) (key : K) (default : PV) : PV :=
  match dGet d.data key with
  | none => default
  | some wr =>
    match deref w wr.ob with
    | none => default
    | some o => o

/-- `WeakValueDictionary.keys`, Lib/weakref.py:179-182. -/
def keys (w : World) (d : WVD K) : List K :=
  (d.data.filter (fun kv => (deref w kv.2.ob).isSome)).map (·.1)

/-- `WeakValueDictionary.itervaluerefs`, Lib/weakref.py:186-196. -/
def itervaluerefs (d : WVD K) : List (KRef K) := d.data.map (·.2)

/-- `WeakValueDictionary.values`, Lib/weakref.py:198-202. -/
def values (w : World) (d : WVD K) : List PV :=
  d.data.filterMap (fun kv => deref w kv.2.ob)

/-- The `while True:` loop of `WeakValueDictionary.popitem`, Lib/weakref.py:204-209. Each pass
shrinks `data`, so the fuel is its length plus one. -/
def popitemLoop (w : World) : Nat → WVD K → WVD K × Py (K × PV)
  | 0, d => (d, .error .modelFuel)
  | fuel + 1, d =>
    match dPopLast d.data with
    | none => (d, .error popEmpty)
    | some ((key, wr), rest) =>
      let d := { d with data := rest }
      match deref w wr.ob with
      | some o => (d, .ok (key, o))
      | none => popitemLoop w fuel d

/-- `WeakValueDictionary.popitem`, Lib/weakref.py:204-209. -/
def popitem (w : World) (d : WVD K) : WVD K × Py (K × PV) :=
  popitemLoop w (d.data.length + 1) d

/-- `WeakValueDictionary.pop`, Lib/weakref.py:211-222. `args` is `*args`. -/
def pop (r : ReprK K) (w : World) (d : WVD K) (key : K) (args : List PV) : WVD K × Py PV :=
  let found := dGet d.data key
  let d := { d with data := dDel d.data key }
  let o := match found with
    | some wr => deref w wr.ob
    | none => none
  match o with
  | some o => (d, .ok o)
  | none =>
    match args with
    | a :: _ => (d, .ok a)
    | [] => (d, .error (.keyError (r key)))

/-- `WeakValueDictionary.setdefault`, Lib/weakref.py:224-233. -/
def setdefault (w : World) (d : WVD K) (key : K) (default : PV) : WVD K × Py PV :=
  let o := match dGet d.data key with
    | some wr => deref w wr.ob
    | none => none
  match o with
  | some o => (d, .ok o)
  | none =>
    match setitem d key default with
    | .error e => (d, .error e)
    | .ok d => (d, .ok default)

/-- `WeakValueDictionary.update`, Lib/weakref.py:235-243: `other` is its items, or `none`. An item
that fails stops the loop with the earlier ones in place. -/
def update (d : WVD K) (other : Option (List (K × PV))) (kwargs : List (K × PV) := []) :
    WVD K × Py Unit :=
  let step : WVD K × Py Unit → K × PV → WVD K × Py Unit := fun st kv =>
    match st with
    | (d, .error e) => (d, .error e)
    | (d, .ok ()) =>
      match setitem d kv.1 kv.2 with
      | .error e => (d, .error e)
      | .ok d => (d, .ok ())
  (other.getD [] ++ kwargs).foldl step (d, .ok ())

/-- `WeakValueDictionary.update` for an `other` without `items`, Lib/weakref.py:238-239:
`other = dict(other)` first. -/
def updatePairs (d : WVD K) (pairs : List (K × PV)) (kwargs : List (K × PV) := []) :
    WVD K × Py Unit :=
  update d (some (dictFrom pairs)) kwargs

/-- `WeakValueDictionary.__init__`, Lib/weakref.py:104-113. -/
def init (other : List (K × PV)) (kw : List (K × PV) := []) : Py (WVD K) :=
  match updatePairs empty other kw with
  | (_, .error e) => .error e
  | (d, .ok ()) => .ok d

/-- `WeakValueDictionary.valuerefs`, Lib/weakref.py:245-255. -/
def valuerefs (d : WVD K) : List (KRef K) := d.data.map (·.2)

/-- `WeakValueDictionary.__ior__`, Lib/weakref.py:257-259. -/
def ior (d : WVD K) (other : List (K × PV)) : WVD K × Py Unit := update d (some other)

/-- `WeakValueDictionary.__or__`, Lib/weakref.py:261-266. `none` is `NotImplemented`, for an `other`
that is no `Mapping`. -/
def or_ (w : World) (d : WVD K) (other : Option (List (K × PV))) : Option (Py (WVD K)) :=
  match other with
  | none => none
  | some o => some (do
      let c ← copy w d
      match update c (some o) with
      | (_, .error e) => .error e
      | (c, .ok ()) => .ok c)

/-- `WeakValueDictionary.__ror__`, Lib/weakref.py:268-274. -/
def ror (w : World) (d : WVD K) (other : Option (List (K × PV))) : Option (Py (WVD K)) :=
  match other with
  | none => none
  | some o => some (
      match update empty (some o) with
      | (_, .error e) => .error e
      | (c, .ok ()) =>
        match update c (some (liveItems w d)) with
        | (_, .error e) => .error e
        | (c, .ok ()) => .ok c)

end WVD

/-! ### `WeakKeyDictionary` -/

/-- The object's `__eq__`, for live objects. -/
abbrev Eqv := Nat → Nat → Bool

/-- A key of `WeakKeyDictionary.data`: a `ref` with an identity. -/
structure WRef where
  rid : Nat
  ob : Nat
  deriving Repr, DecidableEq

/-- The attributes of a `WeakKeyDictionary`, Lib/weakref.py:309-320. `nextRid` numbers refs. -/
structure WKD (V : Type) where
  data : List (WRef × V)
  eager : Bool
  nextRid : Nat
  deriving Repr

/-- `ref(a) == ref(b)`, `weakref_richcompare`, Objects/weakrefobject.c: the referents' `==` when
both are alive, identity otherwise. A lookup key is a fresh live `ref(key)`, so a dead entry never
matches it. -/
def refEq (q : Eqv) (w : World) (a : WRef) (key : Nat) : Bool :=
  alive w a.ob && alive w key && q a.ob key

namespace WKD

variable {V : Type}

/-- The entry whose `ref` equals `ref(key)`. -/
def find (q : Eqv) (w : World) (d : WKD V) (key : Nat) : Option (WRef × V) :=
  d.data.find? (fun kv => refEq q w kv.1 key)

/-- Delete an entry by its `ref`. -/
def delRef (d : List (WRef × V)) (r : WRef) : List (WRef × V) := d.filter (fun kv => kv.1 ≠ r)

/-- The callback `remove`, Lib/weakref.py:311-317, for every entry whose key died. -/
def onDeath (d : WKD V) (o : Nat) : WKD V :=
  if d.eager then { d with data := d.data.filter (fun kv => kv.1.ob ≠ o) } else d

/-- `KeyError(ref(key))` renders an address, so the message is not compared. -/
def keyErr : PyExc := .keyError "~"

/-- `WeakKeyDictionary.__delitem__`, Lib/weakref.py:322-323. -/
def delitem (q : Eqv) (w : World) (d : WKD V) (key : PV) : Py (WKD V) := do
  let k ← refOf key
  match find q w d k with
  | none => .error keyErr
  | some (r, _) => return { d with data := delRef d.data r }

/-- `WeakKeyDictionary.__getitem__`, Lib/weakref.py:325-326. -/
def getitem (q : Eqv) (w : World) (d : WKD V) (key : PV) : Py V := do
  let k ← refOf key
  match find q w d k with
  | none => .error keyErr
  | some (_, v) => return v

/-- `WeakKeyDictionary.__len__`, Lib/weakref.py:328-329. -/
def len (d : WKD V) : Nat := d.data.length

/-- `WeakKeyDictionary.__repr__`, Lib/weakref.py:331-332, with `addr` for `hex(id(self))`. -/
def repr (className addr : String) : String := s!"<{className} at {addr}>"

/-- `data[ref(key, self._remove)] = value`: an equal key keeps its `ref` and takes the value, a new
key appends. -/
def setRef (q : Eqv) (w : World) (d : WKD V) (k : Nat) (value : V) : WKD V :=
  match find q w d k with
  | some (r, _) =>
    { d with data := d.data.map (fun kv => if kv.1 = r then (r, value) else kv) }
  | none =>
    { d with data := d.data ++ [(⟨d.nextRid, k⟩, value)], nextRid := d.nextRid + 1 }

/-- `WeakKeyDictionary.__setitem__`, Lib/weakref.py:334-335. -/
def setitem (q : Eqv) (w : World) (d : WKD V) (key : PV) (value : V) : Py (WKD V) := do
  return setRef q w d (← refOf key) value

/-- An empty dictionary. -/
def empty : WKD V := { data := [], eager := true, nextRid := 0 }

/-- The live items, the loops of `items`, Lib/weakref.py:366-370, and of `copy`, :337-343. -/
def liveItems (w : World) (d : WKD V) : List (PV × V) :=
  d.data.filterMap (fun kv => (deref w kv.1.ob).map (fun o => (o, kv.2)))

/-- `WeakKeyDictionary.items`, Lib/weakref.py:366-370. -/
def items (w : World) (d : WKD V) : List (PV × V) := liveItems w d

/-- `WeakKeyDictionary.copy`, Lib/weakref.py:337-343. -/
def copy (q : Eqv) (w : World) (d : WKD V) : Py (WKD V) :=
  (liveItems w d).foldlM (fun n kv => setitem q w n kv.1 kv.2) empty

/-- `WeakKeyDictionary.__deepcopy__`, Lib/weakref.py:347-354: values are deep-copied, keys not. -/
def deepcopy (dc : V → V) (q : Eqv) (w : World) (d : WKD V) : Py (WKD V) :=
  (liveItems w d).foldlM (fun n kv => setitem q w n kv.1 (dc kv.2)) empty

/-- `WeakKeyDictionary.get`, Lib/weakref.py:356-357. -/
def get (q : Eqv) (w : World) (d : WKD V) (key : PV) (default : V) : Py V := do
  let k ← refOf key
  match find q w d k with
  | none => return default
  | some (_, v) => return v

/-- `WeakKeyDictionary.__contains__`, Lib/weakref.py:359-364. -/
def contains (q : Eqv) (w : World) (d : WKD V) (key : PV) : Bool :=
  match refOf key with
  | .error _ => false
  | .ok k => (find q w d k).isSome

/-- `WeakKeyDictionary.keys`, Lib/weakref.py:372-376. -/
def keys (w : World) (d : WKD V) : List PV := d.data.filterMap (fun kv => deref w kv.1.ob)

/-- `WeakKeyDictionary.values`, Lib/weakref.py:380-383. -/
def values (w : World) (d : WKD V) : List V :=
  (d.data.filter (fun kv => (deref w kv.1.ob).isSome)).map (·.2)

/-- `WeakKeyDictionary.keyrefs`, Lib/weakref.py:385-395. -/
def keyrefs (d : WKD V) : List WRef := d.data.map (·.1)

/-- The `while True:` loop of `WeakKeyDictionary.popitem`, Lib/weakref.py:397-402. -/
def popitemLoop (w : World) : Nat → WKD V → WKD V × Py (PV × V)
  | 0, d => (d, .error .modelFuel)
  | fuel + 1, d =>
    match dPopLast d.data with
    | none => (d, .error popEmpty)
    | some ((key, value), rest) =>
      let d := { d with data := rest }
      match deref w key.ob with
      | some o => (d, .ok (o, value))
      | none => popitemLoop w fuel d

/-- `WeakKeyDictionary.popitem`, Lib/weakref.py:397-402. -/
def popitem (w : World) (d : WKD V) : WKD V × Py (PV × V) := popitemLoop w (d.data.length + 1) d

/-- `WeakKeyDictionary.pop`, Lib/weakref.py:404-405: `self.data.pop(ref(key), *args)`. -/
def pop (q : Eqv) (w : World) (d : WKD V) (key : PV) (args : List V) : WKD V × Py V :=
  match refOf key with
  | .error e => (d, .error e)
  | .ok k =>
    match find q w d k with
    | some (r, v) => ({ d with data := delRef d.data r }, .ok v)
    | none =>
      match args with
      | a :: _ => (d, .ok a)
      | [] => (d, .error keyErr)

/-- `WeakKeyDictionary.setdefault`, Lib/weakref.py:407-408. -/
def setdefault (q : Eqv) (w : World) (d : WKD V) (key : PV) (default : V) : WKD V × Py V :=
  match refOf key with
  | .error e => (d, .error e)
  | .ok k =>
    match find q w d k with
    | some (_, v) => (d, .ok v)
    | none => (setRef q w d k default, .ok default)

/-- `WeakKeyDictionary.update`, Lib/weakref.py:410-420: any keyword is refused first, so `dict` is not applied. -/
def update (q : Eqv) (w : World) (d : WKD V) (dict : Option (List (PV × V))) (kwargs : Bool := false) :
    WKD V × Py Unit :=
  if kwargs then
    (d, .error (.typeError "Keyword arguments are not supported: cannot create weak reference to 'str' object"))
  else
  let step : WKD V × Py Unit → PV × V → WKD V × Py Unit := fun st kv =>
    match st with
    | (d, .error e) => (d, .error e)
    | (d, .ok ()) =>
      match setitem q w d kv.1 kv.2 with
      | .error e => (d, .error e)
      | .ok d => (d, .ok ())
  (dict.getD []).foldl step (d, .ok ())

/-- `dict(pairs)` when the keys are objects: Lib/weakref.py:417-418. Equal keys collapse, and only
hashable keys get here: an `int` is a key of the dict like any other. -/
def dictOf (q : Eqv) (pairs : List (PV × V)) : List (PV × V) :=
  let same (a b : PV) : Bool := match a, b with
    | .obj x, .obj y => q x y
    | .int x, .int y => x == y
    | _, _ => false
  pairs.foldl (fun d kv =>
    if d.any (fun e => same e.1 kv.1) then
      d.map (fun e => if same e.1 kv.1 then (e.1, kv.2) else e)
    else d ++ [kv]) []

/-- `WeakKeyDictionary.update` for a `dict` without `items`, Lib/weakref.py:417-418. -/
def updatePairs (q : Eqv) (w : World) (d : WKD V) (pairs : List (PV × V)) : WKD V × Py Unit :=
  update q w d (some (dictOf q pairs))

/-- `WeakKeyDictionary.__init__`, Lib/weakref.py:309-320. -/
def init (q : Eqv) (w : World) (dict : Option (List (PV × V))) : Py (WKD V) :=
  match dict with
  | none => .ok empty
  | some _ =>
    match update q w empty dict with
    | (_, .error e) => .error e
    | (d, .ok ()) => .ok d

/-- `WeakKeyDictionary.__ior__`, Lib/weakref.py:422-424. -/
def ior (q : Eqv) (w : World) (d : WKD V) (other : List (PV × V)) : WKD V × Py Unit :=
  update q w d (some other)

/-- `WeakKeyDictionary.__or__`, Lib/weakref.py:426-431. -/
def or_ (q : Eqv) (w : World) (d : WKD V) (other : Option (List (PV × V))) : Option (Py (WKD V)) :=
  match other with
  | none => none
  | some o => some (do
      let c ← copy q w d
      match update q w c (some o) with
      | (_, .error e) => .error e
      | (c, .ok ()) => .ok c)

/-- `WeakKeyDictionary.__ror__`, Lib/weakref.py:433-439. -/
def ror (q : Eqv) (w : World) (d : WKD V) (other : Option (List (PV × V))) : Option (Py (WKD V)) :=
  match other with
  | none => none
  | some o => some (
      match update q w empty (some o) with
      | (_, .error e) => .error e
      | (c, .ok ()) =>
        match update q w c (some (liveItems w d)) with
        | (_, .error e) => .error e
        | (c, .ok ()) => .ok c)

end WKD

/-! ### `WeakMethod` -/

/-- A `WeakMethod`, Lib/weakref.py:38-89. `id` is its identity, `obj` and `func` the referents of
the `ref` itself and of `_func_ref`, `callback` whether one was given. -/
structure WM where
  id : Nat
  obj : Nat
  func : Nat
  alive : Bool
  callback : Bool
  deriving Repr, DecidableEq

/-- What `meth` offers: `meth.__self__` and `meth.__func__` when both exist. -/
inductive Meth where
  | bound (obj func : Nat)
  /-- Not a bound method; `tp` is `str(type(meth))`. -/
  | other (tp : String)
  deriving Repr, DecidableEq

/-- `WeakMethod.__new__`, Lib/weakref.py:46-66. -/
def WM.new (id : Nat) (meth : Meth) (callback : Bool) : Py WM :=
  match meth with
  | .bound obj func => .ok { id, obj, func, alive := true, callback }
  | .other tp => .error (.typeError s!"argument should be a bound method, not {tp}")

/-- `_cb`, Lib/weakref.py:53-60, when the object or the function dies: the result is the state and
whether the user's callback ran. -/
def WM.onDeath (m : WM) (o : Nat) : WM × Bool :=
  if m.alive && (m.obj == o || m.func == o) then ({ m with alive := false }, m.callback)
  else (m, false)

/-- `WeakMethod.__call__`, Lib/weakref.py:68-73: the bound method again, as `(obj, func)`. -/
def WM.call (w : World) (m : WM) : Option (Nat × Nat) :=
  if Weakref.alive w m.obj && Weakref.alive w m.func then some (m.obj, m.func) else none

/-- `ref.__eq__`, `weakref_richcompare`, for referents `a` of `id x`, `b` of `id y`. -/
def refCmp (q : Eqv) (w : World) (x : Nat) (a : Nat) (y : Nat) (b : Nat) : Bool :=
  if Weakref.alive w a && Weakref.alive w b then q a b else x == y

/-- `WeakMethod.__eq__`, Lib/weakref.py:75-80. `other = none` is not a `WeakMethod`, which gives
`NotImplemented` (`none`). `_func_ref` of two weak methods is compared as a `ref`; functions compare
by identity and `_func_ref` objects have an identity of their own. -/
def WM.eq (q : Eqv) (w : World) (m : WM) (other : Option WM) : Option Bool :=
  match other with
  | none => none
  | some o =>
    if !m.alive || !o.alive then some (m.id == o.id)
    else some (refCmp q w m.id m.obj o.id o.obj && refCmp (· == ·) w m.id m.func o.id o.func)

/-- `WeakMethod.__ne__`, Lib/weakref.py:82-87. -/
def WM.ne (q : Eqv) (w : World) (m : WM) (other : Option WM) : Option Bool :=
  match other with
  | none => none
  | some o =>
    if !m.alive || !o.alive then some (m.id != o.id)
    else some (!refCmp q w m.id m.obj o.id o.obj || !refCmp (· == ·) w m.id m.func o.id o.func)

/-! ### `finalize` -/

/-- `finalize._Info`, Lib/weakref.py:467-468, with `func(*args, **kwargs)` abstract as `F`. -/
structure Info (F : Type) where
  obj : Nat
  func : F
  atexit : Bool
  index : Nat
  deriving Repr, DecidableEq

/-- The class attributes of `finalize`, Lib/weakref.py:461-465. A finalizer is an id. -/
structure Fin (F : Type) where
  registry : List (Nat × Info F)
  shutdown : Bool
  indexIter : Nat
  dirty : Bool
  registeredWithAtexit : Bool
  deriving Repr

namespace Fin

variable {F : Type}

/-- The initial class state. -/
def start : Fin F :=
  { registry := [], shutdown := false, indexIter := 0, dirty := false,
    registeredWithAtexit := false }

/-- `finalize.__init__`, Lib/weakref.py:470-485. `ref(obj, self)` fails before anything else in the
registry changes, but after `atexit.register`. -/
def init (st : Fin F) (self : Nat) (obj : PV) (func : F) : Fin F × Py Unit :=
  let st := { st with registeredWithAtexit := true }
  match refOf obj with
  | .error e => (st, .error e)
  | .ok o =>
    let info : Info F := { obj := o, func, atexit := true, index := st.indexIter }
    ({ st with
        indexIter := st.indexIter + 1
        registry := dSet st.registry self info
        dirty := true }, .ok ())

/-- `finalize.__call__`, Lib/weakref.py:487-492: `info` is what `self._registry.pop(self, None)`
found and the call happens when the result is `some`. -/
def call (st : Fin F) (self : Nat) : Fin F × Option F :=
  match dGet st.registry self with
  | none => (st, none)
  | some info =>
    let st := { st with registry := dDel st.registry self }
    if st.shutdown then (st, none) else (st, some info.func)

/-- `finalize.detach`, Lib/weakref.py:494-500. -/
def detach (w : World) (st : Fin F) (self : Nat) : Fin F × Option (PV × F) :=
  match dGet st.registry self with
  | none => (st, none)
  | some info =>
    match deref w info.obj with
    | none => (st, none)
    | some o => ({ st with registry := dDel st.registry self }, some (o, info.func))

/-- `finalize.peek`, Lib/weakref.py:502-508. -/
def peek (w : World) (st : Fin F) (self : Nat) : Option (PV × F) :=
  match dGet st.registry self with
  | none => none
  | some info =>
    match deref w info.obj with
    | none => none
    | some o => some (o, info.func)

/-- `finalize.alive`, Lib/weakref.py:510-513. -/
def isAlive (st : Fin F) (self : Nat) : Bool := (dGet st.registry self).isSome

/-- The `atexit` property getter, Lib/weakref.py:515-519. -/
def atexit (st : Fin F) (self : Nat) : Bool :=
  match dGet st.registry self with
  | none => false
  | some info => info.atexit

/-- The `atexit` property setter, Lib/weakref.py:521-525. -/
def setAtexit (st : Fin F) (self : Nat) (value : Bool) : Fin F :=
  match dGet st.registry self with
  | none => st
  | some info => { st with registry := dSet st.registry self { info with atexit := value } }

/-- `finalize.__repr__`, Lib/weakref.py:527-534, for finalizer address `addr`, object address
`oaddr`, and object type name `tn`. -/
def repr (w : World) (st : Fin F) (self : Nat) (addr oaddr tn : String) : String :=
  let dead := s!"<finalize object at {addr}; dead>"
  match dGet st.registry self with
  | none => dead
  | some info =>
    match deref w info.obj with
    | none => dead
    | some _ => s!"<finalize object at {addr}; for '{tn}' at {oaddr}>"

/-- Insert in ascending `index`, `L.sort(key=lambda item:item[1].index)`. -/
def insertByIndex (kv : Nat × Info F) : List (Nat × Info F) → List (Nat × Info F)
  | [] => [kv]
  | x :: rest =>
    if kv.2.index < x.2.index then kv :: x :: rest else x :: insertByIndex kv rest

/-- `finalize._select_for_exit`, Lib/weakref.py:536-541: oldest first. -/
def selectForExit (st : Fin F) : List Nat :=
  ((st.registry.filter (fun kv => kv.2.atexit)).foldr insertByIndex []).map (·.1)

/-- What running a finalizer's function does to the world `σ` and to the class state: a function
can create new finalizers. `Exc` is the exception, `true` when it is an `Exception`. -/
abbrev RunF (σ F : Type) := F → Fin F → σ → Fin F × σ × Option (PyExc × Bool)

variable {σ : Type}

/-- The `while True:` loop of `_exitfunc`, Lib/weakref.py:556-571. `onHook` is
`sys.excepthook(*sys.exc_info())`; a `BaseException` that is no `Exception` leaves the loop. -/
def exitLoop (run : RunF σ F) (onHook : σ → PyExc → σ) :
    Nat → Fin F → σ → Option (List Nat) → Fin F × σ × Option PyExc
  | 0, st, s, _ => (st, s, some .modelFuel)
  | fuel + 1, st, s, pending =>
    let (st, pending) :=
      if pending.isNone || st.dirty then ({ st with dirty := false }, selectForExit st)
      else (st, pending.getD [])
    match pending.getLast? with
    | none => (st, s, none)
    | some f =>
      let pending := pending.dropLast
      match call st f with
      | (st, none) => exitLoop run onHook fuel st s (some pending)
      | (st, some fn) =>
        match run fn st s with
        | (st, s, none) => exitLoop run onHook fuel st s (some pending)
        | (st, s, some (e, true)) => exitLoop run onHook fuel st (onHook s e) (some pending)
        | (st, s, some (e, false)) => (st, s, some e)

/-- `finalize._exitfunc`, Lib/weakref.py:543-576. -/
def exitfunc (run : RunF σ F) (onHook : σ → PyExc → σ) (fuel : Nat) (st : Fin F) (s : σ) :
    Fin F × σ × Option PyExc :=
  let r : Fin F × σ × Option PyExc :=
    if !st.registry.isEmpty then exitLoop run onHook fuel st s none else (st, s, none)
  ({ r.1 with shutdown := true }, r.2.1, r.2.2)

end Fin

end PyLean.CoreLibs.Misc.Weakref
