import PyLean.Datetime.ZoneCache

/-!
# The `ZoneInfo` caches with fallible keys, per class (CPython 3.15.2), both twins

`ZoneCache.lean` compares keys with a decidable equality that cannot raise. Here a key is an
object: `K`'s equality is identity (`is`), and its `hash` and `==` are arbitrary functions
that can raise. Each cache operation is mirrored with the lookups it really makes:

* C compares the key with every strong-cache node through `PyObject_RichCompareBool`
  (identity first, then `key == node->key`, Modules/_zoneinfo.c:2436-2453), never hashing;
* the weak cache is a `weakref.WeakValueDictionary` (Lib/weakref.py) in both twins, and the
  Python strong cache a `collections.OrderedDict`: a lookup hashes the key, then compares it
  with the stored keys of equal hash (`stored == key`), an identical stored key matching
  without a comparison (Objects/dictobject.c).

Scope limits, stated: a dict is probed in insertion order (CPython probes by hash slot, so
among several stored keys with the same hash the comparison order can differ); the weak cache
holds only instances of the class it belongs to, so the `PyObject_TypeCheck` at
Modules/_zoneinfo.c:352-358 always passes; `zoneinfo_new_instance`/`_new_instance` succeed or
fail by `loads key` and run no key methods; key finalizers and re-entrant `__eq__` are
`clearStrongC`/`findInStrongC` in `ZoneCache.lean`; an instance is collected only at a `drop`
step, so an instance whose last reference goes inside an operation (a C eject freeing the
only node that held it) keeps its weak entry until the next `drop` (in CPython the
`KeyedRef` callback removes it at once).

An instance is named by the key object it was built for and a serial number (`next`, counting
the instances built), so two instances built for the same key object stay distinct; a cache
entry is the pair (stored key, instance).
-/

namespace PyLean.Datetime.Zone

open PyLean

/-- The behaviour of key objects: `hash k` is `hash(k)`, `eq a b` is the truth of `a == b`
with `a` on the left (both may raise), `loads k` whether building a zone for `k` succeeds. -/
structure KeyOps (K : Type) where
  hash : K → Py Int
  eq : K → K → Py Bool
  loads : K → Bool

variable {K : Type} [DecidableEq K] (o : KeyOps K)

/-- A `ZoneInfo` instance: the key object it was built for, and its serial number. -/
abbrev Inst (K : Type) := K × Nat

/-- `ZoneInfoNotFoundError` from `_new_instance`/`zoneinfo_new_instance` (`loads k = false`). -/
def notFound : PyExc := .named "ZoneInfoNotFoundError" "~No time zone found with key"

/-! ### Lookups -/

/-- `PyObject_RichCompareBool(v, w, Py_EQ)` (Objects/object.c): identical objects are equal
without calling `__eq__`. -/
def richEqBool (v w : K) : Py Bool := if v = w then .ok true else o.eq v w

/-- Whether a stored key has hash `h` (its hash was computed when it was stored). -/
def hashIs (e : K) (h : Int) : Bool :=
  match o.hash e with
  | .ok h' => h' == h
  | .error _ => false

/-- The probe of a dict lookup for `key` of hash `h`: an identical stored key matches; a
stored key of equal hash is compared with `stored == key`, which may raise. -/
def dictProbe {V : Type} (key : K) (h : Int) : List (K × V) → Py (Option (K × V))
  | [] => .ok none
  | e :: rest =>
    if e.1 = key then .ok (some e)
    else if hashIs o e.1 h then
      match o.eq e.1 key with
      | .error x => .error x
      | .ok true => .ok (some e)
      | .ok false => dictProbe key h rest
    else dictProbe key h rest

/-- A dict lookup (`d[key]`, `d.pop(key)`, `d[key] = v`): `hash(key)`, then the probe. -/
def dictFind {V : Type} (es : List (K × V)) (key : K) : Py (Option (K × V)) :=
  match o.hash key with
  | .error x => .error x
  | .ok h => dictProbe o key h es

/-- `d[key] = v` on a dict or an `OrderedDict`: an existing entry keeps its stored key and
position and takes the new value; otherwise the pair goes at the end. -/
def dictSet {V : Type} [DecidableEq V] (es : List (K × V)) (key : K) (v : V) : Py (List (K × V)) :=
  match dictFind o es key with
  | .error x => .error x
  | .ok (some e) => .ok (es.map fun p => if p = e then (e.1, v) else p)
  | .ok none => .ok (es ++ [(key, v)])

/-- `d.pop(key, default)`: the removed entry, if any. -/
def dictPop {V : Type} [DecidableEq V] (es : List (K × V)) (key : K) : Py (Option V × List (K × V)) :=
  match dictFind o es key with
  | .error x => .error x
  | .ok (some e) => .ok (some e.2, es.erase e)
  | .ok none => .ok (none, es)

/-! ### `WeakValueDictionary` (Lib/weakref.py), shared by both twins -/

/-- `get(key, None)`, Lib/weakref.py:160-171: `self.data[key]`, `KeyError` giving the
default (a dead reference is already gone: see `drop`). -/
def wvdGet (weak : List (K × Inst K)) (key : K) : Py (Option (Inst K)) :=
  match dictFind o weak key with
  | .error x => .error x
  | .ok r => .ok (r.map Prod.snd)

/-- `setdefault(key, inst)`, :224-233: `self.data[key]`, and on a miss
`self.data[key] = KeyedRef(inst, ...)` (a second lookup). Returns the instance. -/
def wvdSetdefault (weak : List (K × Inst K)) (key : K) (inst : Inst K) :
    Py (Inst K × List (K × Inst K)) :=
  match dictFind o weak key with
  | .error x => .error x
  | .ok (some e) => .ok (e.2, weak)
  | .ok none =>
    match dictSet o weak key inst with
    | .error x => .error x
    | .ok weak' => .ok (inst, weak')

/-- `pop(key, None)`, :211-222: `self.data.pop(key)`, `KeyError` giving `None`. A plain
dict's `pop` returns at once when the dict is empty, without hashing the key
(Objects/dictobject.c:3295-3300, `pop_lock_held`); `OrderedDict.pop` always hashes
(Objects/odictobject.c:1135). -/
def wvdPop (weak : List (K × Inst K)) (key : K) : Py (List (K × Inst K)) :=
  match weak with
  | [] => .ok []
  | _ :: _ =>
    match dictPop o weak key with
    | .error x => .error x
    | .ok (_, weak') => .ok weak'

/-! ### One class, as one twin sees it -/

/-- `base` is `type is ZoneInfo`. `strong` is the strong cache in the twin's order (C newest
first, Python oldest first; C keeps none for a subclass). `weak` is the class's own
`_weak_cache` attribute (C's base class keeps it in the module state), `none` after
`del Sub._weak_cache`; `baseWeak` is `ZoneInfo._weak_cache`, which Python's attribute lookup
reaches from a subclass without its own. `foreign` lists the objects a user put in a
replaced `_weak_cache` (`setWeak`), which are not `ZoneInfo` instances. -/
structure ZCls (K : Type) where
  base : Bool
  strong : List (K × Inst K)
  weak : Option (List (K × Inst K))
  baseWeak : List (K × Inst K)
  next : Nat
  foreign : List (Inst K)
  deriving DecidableEq

/-- A fresh `ZoneInfo` class state. -/
def freshBase : ZCls K := ⟨true, [], some [], [], 0, []⟩

/-- C `get_weak_cache`, Modules/_zoneinfo.c:292-302: the module state's cache for the base
class, `PyObject_GetAttrString(type, "_weak_cache")` for a subclass (the C base type has no
such attribute, so a subclass without its own raises). -/
def getWeakC (c : ZCls K) : Py (List (K × Inst K)) :=
  if c.base then .ok (c.weak.getD [])
  else match c.weak with
    | some w => .ok w
    | none => .error (.named "AttributeError" "~type object has no attribute '_weak_cache'")

/-- Python `cls._weak_cache`: the class's own, else `ZoneInfo._weak_cache` through the MRO. -/
def getWeakPy (c : ZCls K) : List (K × Inst K) := c.weak.getD c.baseWeak

/-- Writing back to the dictionary `getWeakPy` returned. -/
def setWeakPy (c : ZCls K) (w : List (K × Inst K)) : ZCls K :=
  match c.weak with
  | some _ => { c with weak := some w }
  | none => { c with baseWeak := w }

/-! ### C -/

/-- `find_in_strong_cache`, Modules/_zoneinfo.c:2436-2453: `rv < 0` returns `NULL` with the
error set (:2442-2444). -/
def findStrongC (key : K) : List (K × Inst K) → Py (Option (K × Inst K))
  | [] => .ok none
  | n :: rest =>
    match richEqBool o key n.1 with
    | .error x => .error x
    | .ok true => .ok (some n)
    | .ok false => findStrongC key rest

/-- `zone_from_strong_cache`, :2516-2535: a subclass misses at once (:2520-2522); a hit moves
the node to the front (`move_strong_cache_node_to_front`, :2486-2505). The new list is
returned with the instance. -/
def zoneFromStrongC (c : ZCls K) (key : K) : Py (Option (Inst K) × List (K × Inst K)) :=
  if !c.base then .ok (none, c.strong)
  else match findStrongC o key c.strong with
    | .error x => .error x
    | .ok none => .ok (none, c.strong)
    | .ok (some n) => .ok (some n.2, n :: c.strong.erase n)

/-- `update_strong_cache`, :2543-2574: nothing for a subclass, else a new front node and the
list cut to 8. -/
def updateStrongC (c : ZCls K) (key : K) (inst : Inst K) : List (K × Inst K) :=
  if !c.base then c.strong else ((key, inst) :: c.strong).take 8

/-- `zoneinfo_ZoneInfo_impl`, :315-364. The state is the class after the call, with the
result. -/
def newErrC (c : ZCls K) (key : K) : ZCls K × Py (Inst K) :=
  match zoneFromStrongC o c key with
  | .error x => (c, .error x)                                  -- :320-321 PyErr_Occurred()
  | .ok (some inst, strong) => ({ c with strong := strong }, .ok inst)
  | .ok (none, _) =>
    match getWeakC c with
    | .error x => (c, .error x)                                -- :324-327
    | .ok weak =>
      match wvdGet o weak key with
      | .error x => (c, .error x)                              -- :328-332
      | .ok r =>
        let got : Py (Inst K × List (K × Inst K) × Nat) :=
          match r with
          | some inst => .ok (inst, weak, c.next)
          | none =>
            if !o.loads key then .error notFound                -- :336-340
            else (wvdSetdefault o weak key (key, c.next)).map fun (i, w) => (i, w, c.next + 1)  -- :342-350
        match got with
        | .error x => (c, .error x)
        | .ok (inst, weak', next) =>
          let c := { c with weak := some weak', next := next }
          if inst ∈ c.foreign then                                -- :352-358 PyObject_TypeCheck
            (c, .error (.named "RuntimeError" "~Unexpected instance in weak cache"))
          else ({ c with strong := updateStrongC c key inst }, .ok inst)   -- :361

/-- `eject_from_strong_cache`, :2459-2479: `0` for a subclass (:2463-2465); a found node is
unlinked and freed; `-1` when the comparison raised (:2475-2477). -/
def ejectC (c : ZCls K) (key : K) : Py (List (K × Inst K)) :=
  if !c.base then .ok c.strong
  else match findStrongC o key c.strong with
    | .error x => .error x
    | .ok (some n) => .ok (c.strong.erase n)
    | .ok none => .ok c.strong

/-- The `only_keys` loop of `zoneinfo_ZoneInfo_clear_cache_impl`, :533-557: per key, eject
from the strong cache, then `weak_cache.pop(key, None)`; the first failure stops the loop.
`err` is the exception the iterator raises after yielding `ks` (or `PyObject_GetIter`'s,
with `ks = []`). -/
def clearKeysC (weak : List (K × Inst K)) (err : Option PyExc) :
    ZCls K → List K → ZCls K × Py (Option (Inst K))
  | c, [] => ({ c with weak := some weak }, match err with | some e => .error e | none => .ok none)
  | c, k :: ks =>
    match ejectC o c k with
    | .error x => ({ c with weak := some weak }, .error x)
    | .ok strong =>
      let c := { c with strong := strong }
      match wvdPop o weak k with
      | .error x => ({ c with weak := some weak }, .error x)
      | .ok weak' => clearKeysC weak' err c ks

/-- `zoneinfo_ZoneInfo_clear_cache_impl`, :507-567. `only = none` is `only_keys=None`:
`weak_cache.clear()` (which cannot fail on a `WeakValueDictionary`) and `clear_strong_cache`
(a no-op for a subclass, :2584-2586). -/
def clearErrC (c : ZCls K) (only : Option (List K × Option PyExc)) : ZCls K × Py (Option (Inst K)) :=
  match getWeakC c with
  | .error x => (c, .error x)
  | .ok weak =>
    match only with
    | none => ({ c with weak := some [], strong := if c.base then [] else c.strong }, .ok none)
    | some (ks, err) => clearKeysC o weak err c ks

/-! ### Python -/

/-- `ZoneInfo.__new__`, Lib/zoneinfo/_zoneinfo.py:40-56. -/
def newErrPy (c : ZCls K) (key : K) : ZCls K × Py (Inst K) :=
  let weak := getWeakPy c
  match wvdGet o weak key with
  | .error x => (c, .error x)                                   -- :41
  | .ok r =>
    let got : Py (Inst K × List (K × Inst K) × Nat) :=
      match r with
      | some inst => .ok (inst, weak, c.next)
      | none =>
        if !o.loads key then .error notFound                     -- :43, `_new_instance`
        else (wvdSetdefault o weak key (key, c.next)).map fun (i, w) => (i, w, c.next + 1)  -- :43
    match got with
    | .error x => (c, .error x)
    | .ok (inst, weak', next) =>
      let c := { setWeakPy c weak' with next := next }
      -- :47 `cls._strong_cache[key] = cls._strong_cache.pop(key, instance)`
      match dictPop o c.strong key with
      | .error x => (c, .error x)
      | .ok (v, strong1) =>
        match dictSet o strong1 key (v.getD inst) with
        | .error x => ({ c with strong := strong1 }, .error x)
        | .ok strong2 =>
          -- :49-54 `popitem(last=False)` past `_strong_cache_size`
          ({ c with strong := if strong2.length > 8 then strong2.tail else strong2 }, .ok inst)

/-- The `only_keys` loop of `ZoneInfo.clear_cache`, :96-99: per key the weak cache, then the
strong one. -/
def clearKeysPy (err : Option PyExc) : ZCls K → List K → ZCls K × Py (Option (Inst K))
  | c, [] => (c, match err with | some e => .error e | none => .ok none)
  | c, k :: ks =>
    match wvdPop o (getWeakPy c) k with
    | .error x => (c, .error x)
    | .ok weak' =>
      let c := setWeakPy c weak'
      match dictPop o c.strong k with
      | .error x => (c, .error x)
      | .ok (_, strong') => clearKeysPy err { c with strong := strong' } ks

/-- `ZoneInfo.clear_cache`, :95-103. -/
def clearErrPy (c : ZCls K) (only : Option (List K × Option PyExc)) : ZCls K × Py (Option (Inst K)) :=
  match only with
  | none => ({ setWeakPy c [] with strong := [] }, .ok none)
  | some (ks, err) => clearKeysPy o err c ks

/-! ### Runs -/

/-- `ZoneInfo(k)`, `clear_cache()`, `clear_cache(only_keys=...)` (the keys the iterator
yields, and the exception it then raises), the collection of the instance in the weak entry
for key `k` (`dropIn`), `del cls._weak_cache`, and `cls._weak_cache = d` for a dict `d` whose
values are not `ZoneInfo` instances. -/
inductive ZOp (K : Type) where
  | get (k : K)
  | clear
  | clearKeys (ks : List K) (err : Option PyExc)
  | drop (k : K)
  | delWeak
  | setWeak (d : List (K × Inst K))

/-- Deleting or replacing `cls._weak_cache` is modelled for subclasses only (the base class's
C cache is module state, and the C type is immutable); runs of the base class exclude them. -/
def ZOp.isDel : ZOp K → Bool
  | .delWeak => true
  | .setWeak _ => true
  | _ => false

/-- `cls._weak_cache = d` on a subclass, in both twins (a no-op on the base class, which runs
exclude). -/
def setWeakStep (c : ZCls K) (d : List (K × Inst K)) : ZCls K × Py (Option (Inst K)) :=
  if c.base then (c, .ok none)
  else ({ c with weak := some d, foreign := c.foreign ++ d.map Prod.snd }, .ok none)

/-- The instance in the weak entry for key object `k` is collected (possible only while no
strong entry holds it): its `KeyedRef` callback removes its entry. -/
def dropIn (strong weak : List (K × Inst K)) (k : K) : List (K × Inst K) :=
  match weak.find? (·.1 = k) with
  | none => weak
  | some (_, i) => if strong.any (·.2 = i) then weak else weak.eraseP (·.2 = i)

/-- `del cls._weak_cache` on a subclass: `AttributeError` when the class has no own attribute
(a second `del`), the same message in both twins (`type.__delattr__`). -/
def delWeakStep (c : ZCls K) : ZCls K × Py (Option (Inst K)) :=
  if c.base then (c, .ok none)
  else match c.weak with
    | some _ => ({ c with weak := none }, .ok none)
    | none => (c, .error (.named "AttributeError" "~type object has no attribute '_weak_cache'"))

def stepErrC (c : ZCls K) : ZOp K → ZCls K × Py (Option (Inst K))
  | .get k => let (c', r) := newErrC o c k; (c', r.map some)
  | .clear => clearErrC o c none
  | .clearKeys ks err => clearErrC o c (some (ks, err))
  | .drop k => ({ c with weak := c.weak.map fun w => dropIn c.strong w k }, .ok none)
  | .delWeak => delWeakStep c
  | .setWeak d => setWeakStep c d

def stepErrPy (c : ZCls K) : ZOp K → ZCls K × Py (Option (Inst K))
  | .get k => let (c', r) := newErrPy o c k; (c', r.map some)
  | .clear => clearErrPy o c none
  | .clearKeys ks err => clearErrPy o c (some (ks, err))
  | .drop k => ({ c with weak := c.weak.map fun w => dropIn c.strong w k,
                         baseWeak := dropIn c.strong c.baseWeak k }, .ok none)
  | .delWeak => delWeakStep c
  | .setWeak d => setWeakStep c d

def runErrC : ZCls K → List (ZOp K) → ZCls K × List (Py (Option (Inst K)))
  | c, [] => (c, [])
  | c, op :: ops => let (c', r) := stepErrC o c op; let (c'', rs) := runErrC c' ops; (c'', r :: rs)

def runErrPy : ZCls K → List (ZOp K) → ZCls K × List (Py (Option (Inst K)))
  | c, [] => (c, [])
  | c, op :: ops => let (c', r) := stepErrPy o c op; let (c'', rs) := runErrPy c' ops; (c'', r :: rs)

/-! ### Subclass creation -/

/-- What `weakref.WeakValueDictionary` is on a module: `none` when the attribute is missing,
else the outcome of calling it. -/
abbrev WvdAttr := Option (Py Unit)

/-- C `new_weak_cache`, Modules/_zoneinfo.c:2592-2603: `PyImport_ImportModuleAttrString`
imports `weakref` now (`imported`: the import's outcome, through `sys.modules`), reads
`WeakValueDictionary` from it, and calls it. -/
def newWeakCacheC (imported : Py WvdAttr) : Py Unit :=
  match imported with
  | .error x => .error x
  | .ok none => .error (.named "AttributeError" "~module 'weakref' has no attribute 'WeakValueDictionary'")
  | .ok (some call) => call

/-- `weakref.WeakValueDictionary()` in `_zoneinfo.py`: `weakref` is the module bound when
`_zoneinfo.py` was imported (`bound`). -/
def newWeakCachePy (bound : WvdAttr) : Py Unit :=
  match bound with
  | none => .error (.named "AttributeError" "~module 'weakref' has no attribute 'WeakValueDictionary'")
  | some call => call

/-- C `zoneinfo_init_subclass`, :2622-2637, registered `METH_VARARGS | METH_KEYWORDS |
METH_CLASS` (:2654-2656): class keywords `kw` are accepted and ignored; the new weak cache is
stored as `cls._weak_cache` (`PyObject_SetAttrString` on a heap type, which does not fail
here). There is no strong cache. -/
def initSubclassErrC (kw : List String) (imported : Py WvdAttr) (baseWeak : List (K × Inst K)) :
    Py (ZCls K) :=
  let _ := kw
  match newWeakCacheC imported with
  | .error x => .error x
  | .ok () => .ok ⟨false, [], some [], baseWeak, 0, []⟩

/-- `ZoneInfo.__init_subclass__(cls)`, _zoneinfo.py:36-38: `type.__new__` passes the class
keywords, which this signature does not take; then a new `OrderedDict` and
`weakref.WeakValueDictionary()`. -/
def initSubclassErrPy (kw : List String) (bound : WvdAttr) (baseWeak : List (K × Inst K)) :
    Py (ZCls K) :=
  match kw with
  | _ :: _ => .error (.typeError "~ZoneInfo.__init_subclass__() got an unexpected keyword argument")
  | [] =>
    match newWeakCachePy bound with
    | .error x => .error x
    | .ok () => .ok ⟨false, [], some [], baseWeak, 0, []⟩

end PyLean.Datetime.Zone
