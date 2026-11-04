import PyLean.Core

/-!
`Lib/weakref.py`, CPython 3.15.2.

Object death is an explicit event. `World` is the set of dead object ids, and a weak reference holds
the id of its referent, so `wr()` is `none` once the id is in the set. In this version
`WeakValueDictionary` has neither `_pending_removals` nor `_IterationGuard`: the callback removes
the entry at once (`_remove_dead_weakref`, Modules/_weakref.c:55-63), which is `WVD.onDeath`. Every
reference keeps its callback (`cb`): `true` when it is the dictionary's own `remove`, `false` when
`self._remove` had been replaced by a no-op when the reference was made, which is how the branches
for a dead reference left in `data` (for example Lib/weakref.py:117, :167, :207) become reachable in
a single thread.

The `dict` behind `data` is modelled with fallible keys (`KOps`): `__hash__` and `__eq__` may raise,
and a lookup compares a stored key with the same hash after the identity test, as `_Py_dict_lookup`
does. Dictionaries are association lists in insertion order, as Python dicts are.
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

/-- `ref(v)`: `weakref___new__` refuses a type without weak-reference support,
Objects/weakrefobject.c. -/
def refOf (v : PV) : Py Nat :=
  match v with
  | .obj i => .ok i
  | .int _ => .error (.typeError "cannot create weak reference to 'int' object")

/-- `wr()` for a reference to `o`. -/
def deref (w : World) (o : Nat) : Option PV := if alive w o then some (.obj o) else none

/-! ### A `dict` with fallible keys -/

/-- A key's `__hash__` and `__eq__`. `=` on `K` is object identity (`is`). `hash k` is
`PyObject_Hash(k)`; `eq a b` is `PyObject_RichCompareBool(a, b, Py_EQ)` past its identity test: the
rich comparison of the stored key `a` with the looked-up key `b`, then `bool()` of its result. Either
may raise. `tn k` is `%T` of `k`. Scope: these are functions, so a key hashes and compares the same
way each time (an `__eq__` that mutates the dict, after which CPython restarts the lookup, is out of
scope). `.typeError` is an exact `TypeError`, `.keyError` a `KeyError`, and `.named` a class that is
a subclass of neither. -/
structure KOps (K : Type) where
  hash : K → Py Int
  eq : K → K → Py Bool
  tn : K → String

/-- `dict_unhashable_type`, Objects/dictobject.c:2442-2460: an exact `TypeError` from the hash is
replaced by one that names the key's type; anything else passes through. -/
def unhashable (tn : String) : Py Int → Py Int
  | .error (.typeError m) => .error (.typeError s!"cannot use '{tn}' as a dict key ({m})")
  | r => r

/-- `_PyObject_HashFast(key)` and, on failure, `dict_unhashable_type`. -/
def KOps.dhash {K : Type} (ops : KOps K) (k : K) : Py Int := unhashable (ops.tn k) (ops.hash k)

/-- A dict entry: the key, its stored hash (`me_hash`) and the value. -/
abbrev Ent (K β : Type) := K × Int × β

section PDict
variable {K β : Type} [DecidableEq K]

/-- One entry further along. -/
def shift : Py (Option (Nat × β)) → Py (Option (Nat × β))
  | .error e => .error e
  | .ok r => .ok (r.map (fun p => (p.1 + 1, p.2)))

/-- `_Py_dict_lookup` with `compare_generic`, Objects/dictobject.c: an identical key is found without
a call, a key with the same stored hash is compared (stored key on the left), and an exception from
`__eq__` ends the lookup. The result is the index of the entry and its value. Scope: same-hash keys
are compared in insertion order; CPython probes them in the order of its table, which is the same
unless a deleted slot was reused. -/
def pFind (eq : K → K → Py Bool) (k : K) (h : Int) : List (Ent K β) → Py (Option (Nat × β))
  | [] => .ok none
  | (k0, h0, v0) :: rest =>
    if k0 = k then .ok (some (0, v0))
    else if h0 = h then
      match eq k0 k with
      | .error e => .error e
      | .ok true => .ok (some (0, v0))
      | .ok false => shift (pFind eq k h rest)
    else shift (pFind eq k h rest)

/-- Replace the value of entry `i`, keeping its key and hash (`insertdict` on a found key keeps the
old key object, Objects/dictobject.c). -/
def setAt : List (Ent K β) → Nat → β → List (Ent K β)
  | [], _, _ => []
  | (k, h, _) :: rest, 0, v => (k, h, v) :: rest
  | e :: rest, i + 1, v => e :: setAt rest i v

/-- Remove entry `i` (`delitem_common`). -/
def delAt {α : Type} : List α → Nat → List α
  | [], _ => []
  | _ :: rest, 0 => rest
  | e :: rest, i + 1 => e :: delAt rest i

/-- A read `d[k]`: the hash, then the lookup. -/
def pLookup (ops : KOps K) (d : List (Ent K β)) (k : K) : Py (Option (Nat × β)) :=
  match ops.dhash k with
  | .error e => .error e
  | .ok h => pFind ops.eq k h d

/-- `d[k] = v`, `setitem_take2_lock_held` and `insertdict`: an equal key keeps its place and takes
the value, a new key goes at the end. -/
def pSet (ops : KOps K) (d : List (Ent K β)) (k : K) (v : β) : Py (List (Ent K β)) :=
  match ops.dhash k with
  | .error e => .error e
  | .ok h =>
    match pFind ops.eq k h d with
    | .error e => .error e
    | .ok none => .ok (d ++ [(k, h, v)])
    | .ok (some (i, _)) => .ok (setAt d i v)

/-- `del d[k]`, `PyDict_DelItem`, Objects/dictobject.c:2926-2970: `err` is `KeyError(k)`. -/
def pDel (ops : KOps K) (err : PyExc) (d : List (Ent K β)) (k : K) : Py (List (Ent K β)) :=
  match pLookup ops d k with
  | .error e => .error e
  | .ok none => .error err
  | .ok (some (i, _)) => .ok (delAt d i)

/-- `PyDict_Pop`, Objects/dictobject.c:3234-3312: an empty dict is answered before the key is
hashed; `none` when the key is missing. -/
def pPop (ops : KOps K) (d : List (Ent K β)) (k : K) : Py (Option (β × List (Ent K β))) :=
  if d.isEmpty then .ok none else
  match pLookup ops d k with
  | .error e => .error e
  | .ok none => .ok none
  | .ok (some (i, v)) => .ok (some (v, delAt d i))

/-- `d.popitem()` removes the last item; no key is hashed. -/
def dPopLast {α : Type} (d : List α) : Option (α × List α) :=
  match d.getLast? with
  | none => none
  | some kv => some (kv, d.dropLast)

end PDict

/-- A finite iterable as a loop sees it: the elements it yields, then the exception `next()` raises
instead of stopping, if any. -/
structure FIt (α : Type) where
  xs : List α
  stop : Option PyExc

/-- An element of the iterable that `dict(other)` consumes, `merge_from_seq2_lock_held`,
Objects/dictobject.c:4052-4138. -/
inductive SeqEl (K : Type) where
  | pair (k : K) (v : PV)
  /-- `PySequence_Fast` refused it. -/
  | notSeq
  /-- A sequence of another length. -/
  | badLen (n : Nat)

/-- The `other` of `update`. Scope: an `other` with `keys` but no `items` (which `dict()` reads
with `keys()` and `[]`) is out of scope. -/
inductive Other (K : Type) where
  | none
  /-- `hasattr(other, "items")` raised something other than `AttributeError`. -/
  | hasattrErr (e : PyExc)
  /-- `other.items()`: the iterable it returned, each element unpacked into `key, o` (or the
  unpacking error), or the exception of the call. -/
  | mapping (it : Py (FIt (Py (K × PV))))
  /-- No `items`: `dict(other)`; `iter(other)` may fail, as may each element. -/
  | seq (it : Py (FIt (SeqEl K)))

/-- `dict(it)`: `merge_from_seq2_lock_held`, the elements in turn, numbered from `i`. -/
def dictOfSeq {K : Type} [DecidableEq K] (ops : KOps K) (stop : Option PyExc) :
    Nat → List (Ent K PV) → List (SeqEl K) → Py (List (Ent K PV))
  | _, acc, [] =>
    match stop with
    | some e => .error e
    | none => .ok acc
  | i, acc, el :: rest =>
    match el with
    | .notSeq => .error (.typeError "object is not iterable")
    | .badLen n =>
      .error (.valueError s!"dictionary update sequence element #{i} has length {n}; 2 is required")
    | .pair k v =>
      match pSet ops acc k v with
      | .error e => .error e
      | .ok acc => dictOfSeq ops stop (i + 1) acc rest

/-! ### `KeyedRef` and `WeakValueDictionary` -/

/-- `KeyedRef`, Lib/weakref.py:277-295: the referent, the callback (`true` when it is the
dictionary's removing `remove`) and `key`. -/
structure KRef (K : Type) where
  ob : Nat
  cb : Bool
  key : K
  deriving Repr, DecidableEq

/-- `KeyedRef.__new__`, Lib/weakref.py:289-292: `ref.__new__(type, ob, callback)` refuses what
cannot be referenced, then `self.key = key`. -/
def KRef.new {K : Type} (v : PV) (callback : Bool) (key : K) : Py (KRef K) :=
  match refOf v with
  | .error e => .error e
  | .ok o => .ok { ob := o, cb := callback, key }

/-- The attributes of a `WeakValueDictionary`, Lib/weakref.py:104-113. `eager` says whether
`self._remove` is still the removing closure. -/
structure WVD (K : Type) where
  data : List (Ent K (KRef K))
  eager : Bool
  deriving DecidableEq

/-- Rendering of `KeyError(key)`. -/
abbrev ReprK (K : Type) := K → String

/-- `popitem` on an empty dict. -/
def popEmpty : PyExc := .keyError "'popitem(): dictionary is empty'"

/-- `except KeyError:`. -/
def isKeyErr : PyExc → Bool
  | .keyError _ => true
  | _ => false

namespace WVD

variable {K : Type} [DecidableEq K]

/-- A new empty dictionary, with the callback of its class. -/
def empty : WVD K := { data := [], eager := true }

/-- `_remove_dead_weakref(d, key)`, `_PyDict_DelItemIf`, Objects/dictobject.c:2982-3017: look `key`
up and delete the entry if its value is a dead reference. A failure is unraisable and changes
nothing. -/
def removeDead (ops : KOps K) (w : World) (data : List (Ent K (KRef K))) (key : K) :
    List (Ent K (KRef K)) :=
  match pLookup ops data key with
  | .ok (some (i, wr)) => if alive w wr.ob then data else delAt data i
  | _ => data

/-- The death of `o` in world `w`: the callback of every reference to `o` in `data`, newest first,
calls `remove(wr)`, Lib/weakref.py:105-110, which is `_remove_dead_weakref(self.data, wr.key)` while
the dictionary lives. Scope: references in `data` are newest-first in reverse `data` order unless a
value was replaced in place; references no longer in `data` would only delete an entry already dead. -/
def onDeath (ops : KOps K) (w : World) (d : WVD K) (o : Nat) : WVD K :=
  let dying := (d.data.filter (fun e => e.2.2.ob == o && e.2.2.cb)).reverse
  { d with data := dying.foldl (fun data e => removeDead ops (o :: w) data e.1) d.data }

/-- `WeakValueDictionary.__getitem__`, Lib/weakref.py:115-120. -/
def getitem (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K) : Py PV :=
  match pLookup ops d.data key with
  | .error e => .error e
  | .ok none => .error (.keyError (r key))
  | .ok (some (_, wr)) =>
    match deref w wr.ob with
    | none => .error (.keyError (r key))
    | some o => .ok o

/-- `WeakValueDictionary.__delitem__`, Lib/weakref.py:122-123. -/
def delitem (ops : KOps K) (r : ReprK K) (d : WVD K) (key : K) : Py (WVD K) :=
  match pDel ops (.keyError (r key)) d.data key with
  | .error e => .error e
  | .ok data => .ok { d with data }

/-- `WeakValueDictionary.__contains__`, Lib/weakref.py:128-133: only a `KeyError` is caught. -/
def contains (ops : KOps K) (w : World) (d : WVD K) (key : K) : Py Bool :=
  match pLookup ops d.data key with
  | .error e => if isKeyErr e then .ok false else .error e
  | .ok none => .ok false
  | .ok (some (_, wr)) => .ok (deref w wr.ob).isSome

/-- `WeakValueDictionary.__setitem__`, Lib/weakref.py:138-139: the `KeyedRef` first, then the store. -/
def setitem (ops : KOps K) (d : WVD K) (key : K) (value : PV) : Py (WVD K) :=
  match KRef.new value d.eager key with
  | .error e => .error e
  | .ok r =>
    match pSet ops d.data key r with
    | .error e => .error e
    | .ok data => .ok { d with data }

/-- The live items in order, the loop of `items`, Lib/weakref.py:173-177, and of `copy`, :141-147. -/
def liveItems (w : World) (d : WVD K) : List (K × PV) :=
  d.data.filterMap (fun e => (deref w e.2.2.ob).map (fun o => (e.1, o)))

/-- The loop of `copy`/`__deepcopy__` over the live items: `new[key] = o` in turn. -/
def setAll (ops : KOps K) : List (K × PV) → WVD K → Py (WVD K)
  | [], n => .ok n
  | (k, o) :: rest, n =>
    match setitem ops n k o with
    | .error e => .error e
    | .ok n => setAll ops rest n

/-- `WeakValueDictionary.copy`, Lib/weakref.py:141-147. -/
def copy (ops : KOps K) (w : World) (d : WVD K) : Py (WVD K) := setAll ops (liveItems w d) empty

/-- The loop of `WeakValueDictionary.__deepcopy__`, Lib/weakref.py:154-157:
`new[deepcopy(key, memo)] = o`. `dc` deep-copies a key and threads the memo (and whatever else the
copy changes), and may raise. -/
def dcLoop {M : Type} (ops : KOps K) (dc : M → K → Py (M × K)) :
    List (K × PV) → M → WVD K → Py (M × WVD K)
  | [], m, n => .ok (m, n)
  | (k, o) :: rest, m, n =>
    match dc m k with
    | .error e => .error e
    | .ok (m, k') =>
      match setitem ops n k' o with
      | .error e => .error e
      | .ok n => dcLoop ops dc rest m n

/-- `WeakValueDictionary.__deepcopy__`, Lib/weakref.py:151-158. `mk` is `self.__class__()`, which a
subclass can make raise. Nothing puts `new` into `memo`. -/
def deepcopy {M : Type} (ops : KOps K) (dc : M → K → Py (M × K)) (mk : Py (WVD K)) (w : World)
    (d : WVD K) (memo : M) : Py (M × WVD K) :=
  match mk with
  | .error e => .error e
  | .ok new => dcLoop ops dc (liveItems w d) memo new

/-- `WeakValueDictionary.get`, Lib/weakref.py:160-171. -/
def get (ops : KOps K) (w : World) (d : WVD K) (key : K) (default : PV) : Py PV :=
  match pLookup ops d.data key with
  | .error e => if isKeyErr e then .ok default else .error e
  | .ok none => .ok default
  | .ok (some (_, wr)) =>
    match deref w wr.ob with
    | none => .ok default
    | some o => .ok o

/-- The step of a generator over `self.data.copy()`: skip what `f` drops, yield the first it keeps. -/
def snapNext {α γ : Type} (f : α → Option γ) : List α → Option (γ × List α)
  | [] => none
  | a :: rest =>
    match f a with
    | some g => some (g, rest)
    | none => snapNext f rest

/-- `next(gen)` for a generator whose body is `for x in self.data.copy()...`: `g = none` before the
first `next()`, which takes the snapshot of `cur`, the `data` of that moment; `some s` is what is left
of the snapshot. `f` is the body for one entry, in the world of that `next()`. The result is the new
state and the yielded value, `none` for `StopIteration`. -/
def genNext {α γ : Type} (f : World → α → Option γ) (cur : List α) (w : World)
    (g : Option (List α)) : Option (List α) × Option γ :=
  match snapNext (f w) (g.getD cur) with
  | none => (some [], none)
  | some (x, rest) => (some rest, some x)

/-- The body of `items`, Lib/weakref.py:174-177. -/
def itemF (w : World) (e : Ent K (KRef K)) : Option (K × PV) :=
  (deref w e.2.2.ob).map (fun o => (e.1, o))

/-- The body of `keys`, Lib/weakref.py:180-182. -/
def keyF (w : World) (e : Ent K (KRef K)) : Option K :=
  if (deref w e.2.2.ob).isSome then some e.1 else none

/-- The body of `values`, Lib/weakref.py:199-202. -/
def valueF (w : World) (e : Ent K (KRef K)) : Option PV := deref w e.2.2.ob

/-- The body of `itervaluerefs`, Lib/weakref.py:196: every reference, dead or alive. -/
def refF (_ : World) (e : Ent K (KRef K)) : Option (KRef K) := some e.2.2

/-- `next()` on `WeakValueDictionary.items()`, Lib/weakref.py:173-177. -/
def itemsNext (w : World) (d : WVD K) (g : Option (List (Ent K (KRef K)))) :=
  genNext itemF d.data w g

/-- `next()` on `WeakValueDictionary.keys()` (and `__iter__`), Lib/weakref.py:179-184. -/
def keysNext (w : World) (d : WVD K) (g : Option (List (Ent K (KRef K)))) :=
  genNext keyF d.data w g

/-- `next()` on `WeakValueDictionary.itervaluerefs()`, Lib/weakref.py:186-196. -/
def irefsNext (w : World) (d : WVD K) (g : Option (List (Ent K (KRef K)))) :=
  genNext refF d.data w g

/-- `next()` on `WeakValueDictionary.values()`, Lib/weakref.py:198-202. -/
def valuesNext (w : World) (d : WVD K) (g : Option (List (Ent K (KRef K)))) :=
  genNext valueF d.data w g

/-- The `while True:` loop of `WeakValueDictionary.popitem`, Lib/weakref.py:204-209. Each pass
shrinks `data`, so the fuel is its length plus one. -/
def popitemLoop (w : World) : Nat → WVD K → WVD K × Py (K × PV)
  | 0, d => (d, .error .modelFuel)
  | fuel + 1, d =>
    match dPopLast d.data with
    | none => (d, .error popEmpty)
    | some ((key, _, wr), rest) =>
      let d := { d with data := rest }
      match deref w wr.ob with
      | some o => (d, .ok (key, o))
      | none => popitemLoop w fuel d

/-- `WeakValueDictionary.popitem`, Lib/weakref.py:204-209. -/
def popitem (w : World) (d : WVD K) : WVD K × Py (K × PV) :=
  popitemLoop w (d.data.length + 1) d

/-- `WeakValueDictionary.pop`, Lib/weakref.py:211-222. `args` is `*args`, of any length: only
`args[0]` is used. -/
def pop (ops : KOps K) (r : ReprK K) (w : World) (d : WVD K) (key : K) (args : List PV) :
    WVD K × Py PV :=
  let miss : Py PV :=
    match args with
    | a :: _ => .ok a
    | [] => .error (.keyError (r key))
  match pPop ops d.data key with
  | .error e => if isKeyErr e then (d, miss) else (d, .error e)
  | .ok none => (d, miss)
  | .ok (some (wr, rest)) =>
    match deref w wr.ob with
    | some o => ({ d with data := rest }, .ok o)
    | none => ({ d with data := rest }, miss)

/-- `WeakValueDictionary.setdefault`, Lib/weakref.py:224-233: the read catches `KeyError`, the
store after it does not. -/
def setdefault (ops : KOps K) (w : World) (d : WVD K) (key : K) (default : PV) : WVD K × Py PV :=
  let o : Py (Option PV) :=
    match pLookup ops d.data key with
    | .error e => if isKeyErr e then .ok none else .error e
    | .ok none => .ok none
    | .ok (some (_, wr)) => .ok (deref w wr.ob)
  match o with
  | .error e => (d, .error e)
  | .ok (some o) => (d, .ok o)
  | .ok none =>
    match setitem ops d key default with
    | .error e => (d, .error e)
    | .ok d => (d, .ok default)

/-- `for key, o in it: d[key] = KeyedRef(o, self._remove, key)`, Lib/weakref.py:240-243: a failure
stops the loop with the earlier items in place. -/
def storeAll (ops : KOps K) : List (Py (K × PV)) → Option PyExc → WVD K → WVD K × Py Unit
  | [], stop, d =>
    match stop with
    | some e => (d, .error e)
    | none => (d, .ok ())
  | x :: rest, stop, d =>
    match x with
    | .error e => (d, .error e)
    | .ok (k, o) =>
      match setitem ops d k o with
      | .error e => (d, .error e)
      | .ok d => storeAll ops rest stop d

/-- `WeakValueDictionary.update`, Lib/weakref.py:235-243. An `other` without `items` is
`dict(other)` first, which either fails as a whole or gives its items. -/
def update (ops : KOps K) (d : WVD K) (other : Other K) (kwargs : List (K × PV) := []) :
    WVD K × Py Unit :=
  let src : Py (FIt (Py (K × PV))) :=
    match other with
    | .none => .ok ⟨[], none⟩
    | .hasattrErr e => .error e
    | .mapping it => it
    | .seq it =>
      match it with
      | .error e => .error e
      | .ok it =>
        match dictOfSeq ops it.stop 0 [] it.xs with
        | .error e => .error e
        | .ok dd => .ok ⟨dd.map (fun e => .ok (e.1, e.2.2)), none⟩
  match src with
  | .error e => (d, .error e)
  | .ok it =>
    match storeAll ops it.xs it.stop d with
    | (d, .error e) => (d, .error e)
    | (d, .ok ()) => storeAll ops (kwargs.map Except.ok) none d

/-- `WeakValueDictionary.__init__`, Lib/weakref.py:104-113: `other` defaults to `()`, which has no
`items`. -/
def init (ops : KOps K) (other : Other K := .seq (.ok ⟨[], none⟩)) (kw : List (K × PV) := []) :
    Py (WVD K) :=
  match update ops empty other kw with
  | (_, .error e) => .error e
  | (d, .ok ()) => .ok d

/-- `WeakValueDictionary.valuerefs`, Lib/weakref.py:245-255. -/
def valuerefs (d : WVD K) : List (KRef K) := d.data.map (fun e => e.2.2)

/-- `WeakValueDictionary.__ior__`, Lib/weakref.py:257-259: `update`, then `self`. -/
def ior (ops : KOps K) (d : WVD K) (other : Other K) : WVD K × Py Unit := update ops d other

/-- `WeakValueDictionary.__or__`, Lib/weakref.py:261-266. `none` is `NotImplemented`, for an `other`
that is no `Mapping`; a `Mapping` is updated through its `items()`. -/
def or_ (ops : KOps K) (w : World) (d : WVD K) (other : Option (List (K × PV))) :
    Option (Py (WVD K)) :=
  match other with
  | none => none
  | some o => some (
      match copy ops w d with
      | .error e => .error e
      | .ok c =>
        match update ops c (.mapping (.ok ⟨o.map Except.ok, none⟩)) with
        | (_, .error e) => .error e
        | (c, .ok ()) => .ok c)

/-- `WeakValueDictionary.__ror__`, Lib/weakref.py:268-274. -/
def ror (ops : KOps K) (w : World) (d : WVD K) (other : Option (List (K × PV))) :
    Option (Py (WVD K)) :=
  match other with
  | none => none
  | some o => some (
      match update ops empty (.mapping (.ok ⟨o.map Except.ok, none⟩)) with
      | (_, .error e) => .error e
      | (c, .ok ()) =>
        match update ops c (.mapping (.ok ⟨(liveItems w d).map Except.ok, none⟩)) with
        | (_, .error e) => .error e
        | (c, .ok ()) => .ok c)

end WVD

/-! ### `WeakKeyDictionary` -/

/-- The referents' `__hash__` and `__eq__`: `eq a b` is `PyObject_RichCompare(a, b, Py_EQ)` (stored
referent on the left) and then `bool()` of the result, which `weakref_richcompare`,
Objects/weakrefobject.c:249-273, and the dict's `PyObject_RichCompareBool` do. Both may raise. -/
structure ROps where
  hash : Nat → Py Int
  eq : Nat → Nat → Py Bool

/-- A key of `WeakKeyDictionary.data`: a `ref` with an identity `rid`, its referent, its cached hash
(`self->hash`, Objects/weakrefobject.c:190-202, which is also the dict's `me_hash`) and whether its
callback is the dictionary's `remove`. -/
structure WRef where
  rid : Nat
  ob : Nat
  hash : Int
  cb : Bool
  deriving Repr, DecidableEq

/-- The attributes of a `WeakKeyDictionary`, Lib/weakref.py:309-320. `nextRid` numbers refs. -/
structure WKD (V : Type) where
  data : List (WRef × V)
  eager : Bool
  nextRid : Nat
  deriving DecidableEq

/-- `%T` of a `ref`. -/
def refTn : String := "weakref.ReferenceType"

namespace WKD

variable {V : Type}

/-- The lookup of a fresh live `ref(key)` with hash `h`: `_Py_dict_lookup` compares each stored
`ref` with the same hash, `weakref_richcompare`, which compares the referents when both live and
gives `False` (identity of two distinct refs) when the stored one is dead. The fresh ref is never
identical to a stored one, whose callback makes it distinct. -/
def find (q : ROps) (w : World) (key : Nat) (h : Int) : List (WRef × V) → Py (Option (WRef × V))
  | [] => .ok none
  | (r, v) :: rest =>
    if r.hash == h && alive w r.ob then
      match q.eq r.ob key with
      | .error e => .error e
      | .ok true => .ok (some (r, v))
      | .ok false => find q w key h rest
    else find q w key h rest

/-- `self.data[ref(key)]` and friends: `ref(key)` (which refuses an int), `hash()` of it, which is the
referent's hash behind `dict_unhashable_type`, then the lookup. -/
def lookup (q : ROps) (w : World) (d : WKD V) (key : PV) : Py (Nat × Int × Option (WRef × V)) :=
  match refOf key with
  | .error e => .error e
  | .ok k =>
    match unhashable refTn (q.hash k) with
    | .error e => .error e
    | .ok h =>
      match find q w k h d.data with
      | .error e => .error e
      | .ok r => .ok (k, h, r)

/-- Delete an entry by its `ref`. -/
def delRef (d : List (WRef × V)) (r : WRef) : List (WRef × V) := d.filter (fun kv => kv.1 ≠ r)

/-- The callback `remove(k)`, Lib/weakref.py:311-317, for every reference to `o` made with it:
`del self.data[k]` finds the dead `k` by identity (its hash is cached and every comparison with a dead
ref is an identity test), so nothing is called. -/
def onDeath (d : WKD V) (o : Nat) : WKD V :=
  { d with data := d.data.filter (fun kv => !(kv.1.ob == o && kv.1.cb)) }

/-- `KeyError(ref(key))` renders an address, so the message is not compared. -/
def keyErr : PyExc := .keyError "~"

/-- `WeakKeyDictionary.__delitem__`, Lib/weakref.py:322-323. -/
def delitem (q : ROps) (w : World) (d : WKD V) (key : PV) : Py (WKD V) :=
  match lookup q w d key with
  | .error e => .error e
  | .ok (_, _, none) => .error keyErr
  | .ok (_, _, some (r, _)) => .ok { d with data := delRef d.data r }

/-- `WeakKeyDictionary.__getitem__`, Lib/weakref.py:325-326. -/
def getitem (q : ROps) (w : World) (d : WKD V) (key : PV) : Py V :=
  match lookup q w d key with
  | .error e => .error e
  | .ok (_, _, none) => .error keyErr
  | .ok (_, _, some (_, v)) => .ok v

/-- Store under a looked-up key: an equal key keeps its `ref` and takes the value, a new key appends
a fresh `ref(key, self._remove)` with hash `h`. -/
def storeAt (d : WKD V) (k : Nat) (h : Int) (found : Option (WRef × V)) (value : V) : WKD V :=
  match found with
  | some (r, _) =>
    { d with data := d.data.map (fun kv => if kv.1 = r then (r, value) else kv) }
  | none =>
    { d with data := d.data ++ [(⟨d.nextRid, k, h, d.eager⟩, value)], nextRid := d.nextRid + 1 }

/-- `WeakKeyDictionary.__setitem__`, Lib/weakref.py:334-335. -/
def setitem (q : ROps) (w : World) (d : WKD V) (key : PV) (value : V) : Py (WKD V) :=
  match lookup q w d key with
  | .error e => .error e
  | .ok (k, h, found) => .ok (storeAt d k h found value)

/-- An empty dictionary. -/
def empty : WKD V := { data := [], eager := true, nextRid := 0 }

/-- The live items, the loops of `items`, Lib/weakref.py:366-370, and of `copy`, :337-343. -/
def liveItems (w : World) (d : WKD V) : List (PV × V) :=
  d.data.filterMap (fun kv => (deref w kv.1.ob).map (fun o => (o, kv.2)))

/-- The loop of `copy`: `new[o] = value` in turn. -/
def setAll (q : ROps) (w : World) : List (PV × V) → WKD V → Py (WKD V)
  | [], n => .ok n
  | (k, v) :: rest, n =>
    match setitem q w n k v with
    | .error e => .error e
    | .ok n => setAll q w rest n

/-- `WeakKeyDictionary.copy`, Lib/weakref.py:337-343. -/
def copy (q : ROps) (w : World) (d : WKD V) : Py (WKD V) := setAll q w (liveItems w d) empty

/-- The loop of `WeakKeyDictionary.__deepcopy__`, Lib/weakref.py:350-353:
`new[o] = deepcopy(value, memo)`, the value first. -/
def dcLoop {M : Type} (q : ROps) (w : World) (dc : M → V → Py (M × V)) :
    List (PV × V) → M → WKD V → Py (M × WKD V)
  | [], m, n => .ok (m, n)
  | (k, v) :: rest, m, n =>
    match dc m v with
    | .error e => .error e
    | .ok (m, v') =>
      match setitem q w n k v' with
      | .error e => .error e
      | .ok n => dcLoop q w dc rest m n

/-- `WeakKeyDictionary.__deepcopy__`, Lib/weakref.py:347-354; `mk` is `self.__class__()`. -/
def deepcopy {M : Type} (q : ROps) (dc : M → V → Py (M × V)) (mk : Py (WKD V)) (w : World)
    (d : WKD V) (memo : M) : Py (M × WKD V) :=
  match mk with
  | .error e => .error e
  | .ok new => dcLoop q w dc (liveItems w d) memo new

/-- `WeakKeyDictionary.get`, Lib/weakref.py:356-357. -/
def get (q : ROps) (w : World) (d : WKD V) (key : PV) (default : V) : Py V :=
  match lookup q w d key with
  | .error e => .error e
  | .ok (_, _, none) => .ok default
  | .ok (_, _, some (_, v)) => .ok v

/-- `WeakKeyDictionary.__contains__`, Lib/weakref.py:359-364: only `ref()`'s `TypeError` is caught. -/
def contains (q : ROps) (w : World) (d : WKD V) (key : PV) : Py Bool :=
  match refOf key with
  | .error _ => .ok false
  | .ok _ =>
    match lookup q w d key with
    | .error e => .error e
    | .ok (_, _, r) => .ok r.isSome

/-- The body of `items`, Lib/weakref.py:367-370. -/
def itemF (w : World) (kv : WRef × V) : Option (PV × V) := (deref w kv.1.ob).map (fun o => (o, kv.2))

/-- The body of `keys`, Lib/weakref.py:373-376. -/
def keyF (w : World) (kv : WRef × V) : Option PV := deref w kv.1.ob

/-- The body of `values`, Lib/weakref.py:381-383. -/
def valueF (w : World) (kv : WRef × V) : Option V :=
  if (deref w kv.1.ob).isSome then some kv.2 else none

/-- `next()` on `WeakKeyDictionary.items()`. -/
def itemsNext (w : World) (d : WKD V) (g : Option (List (WRef × V))) := WVD.genNext itemF d.data w g

/-- `next()` on `WeakKeyDictionary.keys()` (and `__iter__`). -/
def keysNext (w : World) (d : WKD V) (g : Option (List (WRef × V))) := WVD.genNext keyF d.data w g

/-- `next()` on `WeakKeyDictionary.values()`. -/
def valuesNext (w : World) (d : WKD V) (g : Option (List (WRef × V))) := WVD.genNext valueF d.data w g

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

/-- `dict.pop`'s argument check, `dict_pop` clinic code: at most one default. -/
def popArity (n : Nat) : PyExc := .typeError s!"pop expected at most 2 arguments, got {n + 1}"

/-- `WeakKeyDictionary.pop`, Lib/weakref.py:404-405: `self.data.pop(ref(key), *args)`. `ref(key)`
is evaluated first, then `dict.pop` checks its arguments, answers an empty dict without hashing, and
otherwise looks the key up. -/
def pop (q : ROps) (w : World) (d : WKD V) (key : PV) (args : List V) : WKD V × Py V :=
  match refOf key with
  | .error e => (d, .error e)
  | .ok _ =>
    if 1 < args.length then (d, .error (popArity args.length)) else
    let miss : Py V := match args with
      | a :: _ => .ok a
      | [] => .error keyErr
    if d.data.isEmpty then (d, miss) else
    match lookup q w d key with
    | .error e => (d, .error e)
    | .ok (_, _, some (r, v)) => ({ d with data := delRef d.data r }, .ok v)
    | .ok (_, _, none) => (d, miss)

/-- `WeakKeyDictionary.setdefault`, Lib/weakref.py:407-408: `dict.setdefault(ref(key, ...), default)`. -/
def setdefault (q : ROps) (w : World) (d : WKD V) (key : PV) (default : V) : WKD V × Py V :=
  match lookup q w d key with
  | .error e => (d, .error e)
  | .ok (_, _, some (_, v)) => (d, .ok v)
  | .ok (k, h, none) => (storeAt d k h none default, .ok default)

/-- `d[ref(key, self._remove)] = value` for each element in turn, Lib/weakref.py:419-420. -/
def storeAll (q : ROps) (w : World) : List (Py (PV × V)) → Option PyExc → WKD V → WKD V × Py Unit
  | [], stop, d =>
    match stop with
    | some e => (d, .error e)
    | none => (d, .ok ())
  | x :: rest, stop, d =>
    match x with
    | .error e => (d, .error e)
    | .ok (k, v) =>
      match setitem q w d k v with
      | .error e => (d, .error e)
      | .ok d => storeAll q w rest stop d

/-- The keys of `type({})(dict)` are the objects themselves: an int hashes as itself and compares by
value, an object through `q`; an object and an int never compare equal (`MiscW.__eq__` and
`int.__eq__` of the differential test both refuse). -/
def pvOps (q : ROps) : KOps PV where
  hash := fun
    | .obj o => q.hash o
    | .int n => .ok n
  eq := fun
    | .obj a, .obj b => q.eq a b
    | .int a, .int b => .ok (a == b)
    | _, _ => .ok false
  tn := fun
    | .obj _ => "object"
    | .int _ => "int"

/-- The `other` of `WeakKeyDictionary.update`. -/
inductive KOther (V : Type) where
  | none
  | hasattrErr (e : PyExc)
  /-- `dict.items()`: the elements, each unpacked into `key, value` or failing. -/
  | mapping (it : Py (FIt (Py (PV × V))))
  /-- No `items`: `type({})(dict)`. -/
  | seq (it : Py (FIt (Py (PV × V))))

/-- `dict(it)` over pairs of the test: hashing through `pvOps`; an element error is raised as is. -/
def dictOfPairs (q : ROps) (stop : Option PyExc) :
    List (Ent PV V) → List (Py (PV × V)) → Py (List (Ent PV V))
  | acc, [] =>
    match stop with
    | some e => .error e
    | none => .ok acc
  | acc, x :: rest =>
    match x with
    | .error e => .error e
    | .ok (k, v) =>
      match pSet (pvOps q) acc k v with
      | .error e => .error e
      | .ok acc => dictOfPairs q stop acc rest

/-- `WeakKeyDictionary.update`, Lib/weakref.py:410-420: any keyword is refused first, so `dict` is
not applied. -/
def update (q : ROps) (w : World) (d : WKD V) (dict : KOther V) (kwargs : Bool := false) :
    WKD V × Py Unit :=
  if kwargs then
    (d, .error (.typeError
      "Keyword arguments are not supported: cannot create weak reference to 'str' object"))
  else
  let src : Py (FIt (Py (PV × V))) :=
    match dict with
    | .none => .ok ⟨[], none⟩
    | .hasattrErr e => .error e
    | .mapping it => it
    | .seq it =>
      match it with
      | .error e => .error e
      | .ok it =>
        match dictOfPairs q it.stop [] it.xs with
        | .error e => .error e
        | .ok dd => .ok ⟨dd.map (fun e => .ok (e.1, e.2.2)), none⟩
  match src with
  | .error e => (d, .error e)
  | .ok it => storeAll q w it.xs it.stop d

/-- `WeakKeyDictionary.__init__`, Lib/weakref.py:309-320. -/
def init (q : ROps) (w : World) (dict : KOther V) : Py (WKD V) :=
  match dict with
  | .none => .ok empty
  | _ =>
    match update q w empty dict with
    | (_, .error e) => .error e
    | (d, .ok ()) => .ok d

/-- `WeakKeyDictionary.__ior__`, Lib/weakref.py:422-424. -/
def ior (q : ROps) (w : World) (d : WKD V) (other : KOther V) : WKD V × Py Unit :=
  update q w d other

/-- `WeakKeyDictionary.__or__`, Lib/weakref.py:426-431. -/
def or_ (q : ROps) (w : World) (d : WKD V) (other : Option (List (PV × V))) : Option (Py (WKD V)) :=
  match other with
  | none => none
  | some o => some (
      match copy q w d with
      | .error e => .error e
      | .ok c =>
        match update q w c (.mapping (.ok ⟨o.map Except.ok, none⟩)) with
        | (_, .error e) => .error e
        | (c, .ok ()) => .ok c)

/-- `WeakKeyDictionary.__ror__`, Lib/weakref.py:433-439. -/
def ror (q : ROps) (w : World) (d : WKD V) (other : Option (List (PV × V))) : Option (Py (WKD V)) :=
  match other with
  | none => none
  | some o => some (
      match update q w empty (.mapping (.ok ⟨o.map Except.ok, none⟩)) with
      | (_, .error e) => .error e
      | (c, .ok ()) =>
        match update q w c (.mapping (.ok ⟨(liveItems w d).map Except.ok, none⟩)) with
        | (_, .error e) => .error e
        | (c, .ok ()) => .ok c)

end WKD

/-! ### `WeakMethod` -/

/-- A `WeakMethod`, Lib/weakref.py:38-89. `id` is its identity, `obj` and `func` the referents of
the `ref` itself and of `_func_ref`, `alive` is `_alive`, `callback` whether one was given. -/
structure WM where
  id : Nat
  obj : Nat
  func : Nat
  alive : Bool
  callback : Bool
  deriving Repr, DecidableEq

/-- The argument of `WeakMethod(meth)`: what reading `meth.__self__` and `meth.__func__` gives, and
`str(type(meth))`. `AttributeError` is `.named "AttributeError" _`. -/
structure Meth where
  self : Py PV
  func : Py PV
  tp : String

/-- `except AttributeError:`. Scope: a subclass of `AttributeError` is out of scope. -/
def isAttrErr : PyExc → Bool
  | .named "AttributeError" _ => true
  | _ => false

/-- `WeakMethod.__new__`, Lib/weakref.py:46-66: the two attributes, then `ref.__new__(cls, obj, _cb)`
and `ref(func, _cb)`, each of which refuses what cannot be weakly referenced. -/
def WM.new (id : Nat) (meth : Meth) (callback : Bool) : Py WM :=
  let notBound : PyExc := .typeError s!"argument should be a bound method, not {meth.tp}"
  match meth.self with
  | .error e => .error (if isAttrErr e then notBound else e)
  | .ok obj =>
    match meth.func with
    | .error e => .error (if isAttrErr e then notBound else e)
    | .ok func =>
      match refOf obj with
      | .error e => .error e
      | .ok o =>
        match refOf func with
        | .error e => .error e
        | .ok f => .ok { id, obj := o, func := f, alive := true, callback }

/-- `_cb`, Lib/weakref.py:53-60, when the object or the function dies: the result is the state and
whether the user's callback ran. -/
def WM.onDeath (m : WM) (o : Nat) : WM × Bool :=
  if m.alive && (m.obj == o || m.func == o) then ({ m with alive := false }, m.callback)
  else (m, false)

/-- `WeakMethod.__call__`, Lib/weakref.py:68-73: the bound method again, as `(obj, func)`. -/
def WM.call (w : World) (m : WM) : Option (Nat × Nat) :=
  if Weakref.alive w m.obj && Weakref.alive w m.func then some (m.obj, m.func) else none

/-- Rich comparison of the referents: `eq a b` is `PyObject_RichCompare(a, b, Py_EQ)` and `ne a b`
the same with `Py_NE`, each an arbitrary object `R` or an exception; `ofBool` makes `True`/`False`
and `truth` is `PyObject_IsTrue`, which may raise. -/
structure RCmp (R : Type) where
  eq : Nat → Nat → Py R
  ne : Nat → Nat → Py R
  ofBool : Bool → R
  truth : R → Py Bool

/-- `weakref_richcompare(self, other, op)`, Objects/weakrefobject.c:249-273, for two refs with
identities `x`, `y` and referents `a`, `b`: the referents' comparison when both live, identity of
the refs otherwise. -/
def refCmp {R : Type} (c : RCmp R) (cmp : Nat → Nat → Py R) (ne : Bool) (w : World)
    (x a y b : Nat) : Py R :=
  if Weakref.alive w a && Weakref.alive w b then cmp a b
  else .ok (c.ofBool (if ne then x != y else x == y))

/-- `WeakMethod.__eq__`, Lib/weakref.py:75-80. `other = none` is not a `WeakMethod`, which gives
`NotImplemented` (`none`). `x and y`: the first result when it is false, else the comparison of the
`_func_ref`s, which are distinct objects for distinct weak methods. -/
def WM.eq {R : Type} (c : RCmp R) (w : World) (m : WM) (other : Option WM) : Option (Py R) :=
  match other with
  | none => none
  | some o =>
    if !m.alive || !o.alive then some (.ok (c.ofBool (m.id == o.id)))
    else some (
      match refCmp c c.eq false w m.id m.obj o.id o.obj with
      | .error e => .error e
      | .ok x =>
        match c.truth x with
        | .error e => .error e
        | .ok false => .ok x
        | .ok true => refCmp c c.eq false w m.id m.func o.id o.func)

/-- `WeakMethod.__ne__`, Lib/weakref.py:82-87: `ref.__ne__` is the referents' own `!=`, and `x or y`
returns the first result when it is true. -/
def WM.ne {R : Type} (c : RCmp R) (w : World) (m : WM) (other : Option WM) : Option (Py R) :=
  match other with
  | none => none
  | some o =>
    if !m.alive || !o.alive then some (.ok (c.ofBool (m.id != o.id)))
    else some (
      match refCmp c c.ne true w m.id m.obj o.id o.obj with
      | .error e => .error e
      | .ok x =>
        match c.truth x with
        | .error e => .error e
        | .ok true => .ok x
        | .ok false => refCmp c c.ne true w m.id m.func o.id o.func)

/-! ### `finalize` -/

/-- `repr()` of a `str` of printable ASCII, `unicode_repr`, Objects/unicodeobject.c: single quotes
unless the text holds `'` and no `"`. -/
def strRepr (s : String) : String :=
  let q := if s.contains '\'' && !s.contains '"' then '"' else '\''
  let esc (c : Char) : String :=
    if c == q then "\\" ++ c.toString
    else if c == '\\' then "\\\\"
    else c.toString
  q.toString ++ String.join (s.toList.map esc) ++ q.toString

/-- `finalize._Info`, Lib/weakref.py:467-468, with `func(*args, **kwargs)` abstract as `F`. -/
structure Info (F : Type) where
  obj : Nat
  func : F
  atexit : Bool
  index : Nat
  deriving Repr, DecidableEq

section FDict
variable {K β : Type} [DecidableEq K]

def dGet (d : List (K × β)) (k : K) : Option β := d.lookup k

/-- `d[k] = v` for keys that compare by identity: an existing key keeps its position. -/
def dSet (d : List (K × β)) (k : K) (v : β) : List (K × β) :=
  match d with
  | [] => [(k, v)]
  | (a, b) :: rest => if a = k then (a, v) :: rest else (a, b) :: dSet rest k v

def dDel (d : List (K × β)) (k : K) : List (K × β) :=
  match d with
  | [] => []
  | (a, b) :: rest => if a = k then rest else (a, b) :: dDel rest k

end FDict

/-- The class attributes of `finalize`, Lib/weakref.py:461-465, and `gc.isenabled()`. A finalizer is
an id; finalizers hash and compare by identity, so `_registry` is a dict keyed by identity. -/
structure Fin (F : Type) where
  registry : List (Nat × Info F)
  shutdown : Bool
  indexIter : Nat
  dirty : Bool
  registeredWithAtexit : Bool
  gc : Bool
  deriving Repr

namespace Fin

variable {F : Type}

/-- The initial class state. -/
def start : Fin F :=
  { registry := [], shutdown := false, indexIter := 0, dirty := false,
    registeredWithAtexit := false, gc := true }

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

/-- The `atexit` property getter, Lib/weakref.py:515-519: `bool(info) and info.atexit`. -/
def atexit (st : Fin F) (self : Nat) : Bool :=
  match dGet st.registry self with
  | none => false
  | some info => info.atexit

/-- The `atexit` property setter, Lib/weakref.py:521-525: `bool(value)`, which may raise, is only
evaluated for a live finalizer. -/
def setAtexit (st : Fin F) (self : Nat) (value : Py Bool) : Py (Fin F) :=
  match dGet st.registry self with
  | none => .ok st
  | some info =>
    match value with
    | .error e => .error e
    | .ok b => .ok { st with registry := dSet st.registry self { info with atexit := b } }

/-- `finalize.__repr__`, Lib/weakref.py:527-534, for `type(self).__name__ = cls`, finalizer address
`addr`, object address `oaddr`, and `type(obj).__name__ = tn`, which `%r` quotes. -/
def repr (w : World) (st : Fin F) (self : Nat) (cls addr oaddr tn : String) : String :=
  let dead := s!"<{cls} object at {addr}; dead>"
  match dGet st.registry self with
  | none => dead
  | some info =>
    match deref w info.obj with
    | none => dead
    | some _ => s!"<{cls} object at {addr}; for {strRepr tn} at {oaddr}>"

/-- Insert in ascending `index`, `L.sort(key=lambda item:item[1].index)`. -/
def insertByIndex (kv : Nat × Info F) : List (Nat × Info F) → List (Nat × Info F)
  | [] => [kv]
  | x :: rest =>
    if kv.2.index < x.2.index then kv :: x :: rest else x :: insertByIndex kv rest

/-- `finalize._select_for_exit`, Lib/weakref.py:536-541: oldest first. -/
def selectForExit (st : Fin F) : List Nat :=
  ((st.registry.filter (fun kv => kv.2.atexit)).foldr insertByIndex []).map (·.1)

/-- What running a finalizer's function does to the world `σ` and to the class state: a function
can create new finalizers or toggle `gc`. The exception is `true` when it is an `Exception`. -/
abbrev RunF (σ F : Type) := F → Fin F → σ → Fin F × σ × Option (PyExc × Bool)

variable {σ : Type}

/-- The `while True:` loop of `_exitfunc`, Lib/weakref.py:556-571. `onHook` is
`sys.excepthook(*sys.exc_info())`, which may itself raise; a `BaseException` that is no `Exception`
leaves the loop; `assert f not in cls._registry` follows each call. -/
def exitLoop (run : RunF σ F) (onHook : σ → PyExc → σ × Option PyExc) :
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
      let after (st : Fin F) (s : σ) : Fin F × σ × Option PyExc :=
        if isAlive st f then (st, s, some (.assertionError ""))
        else exitLoop run onHook fuel st s (some pending)
      match call st f with
      | (st, none) => after st s
      | (st, some fn) =>
        match run fn st s with
        | (st, s, none) => after st s
        | (st, s, some (e, true)) =>
          match onHook s e with
          | (s, none) => after st s
          | (s, some e') => (st, s, some e')
        | (st, s, some (e, false)) => (st, s, some e)

/-- `finalize._exitfunc`, Lib/weakref.py:543-576: `gc` is disabled around the loop when the registry
is not empty and `gc` was enabled, and the `finally` sets `_shutdown` and re-enables it. -/
def exitfunc (run : RunF σ F) (onHook : σ → PyExc → σ × Option PyExc) (fuel : Nat) (st : Fin F)
    (s : σ) : Fin F × σ × Option PyExc :=
  let reenable := !st.registry.isEmpty && st.gc
  let st := if reenable then { st with gc := false } else st
  let r : Fin F × σ × Option PyExc :=
    if !st.registry.isEmpty then exitLoop run onHook fuel st s none else (st, s, none)
  let st := { r.1 with shutdown := true }
  (if reenable then { st with gc := true } else st, r.2.1, r.2.2)

end Fin

end PyLean.CoreLibs.Misc.Weakref
