import PyLean.Core

/-!
# The `ZoneInfo` caches (CPython 3.15.2), both twins

The strong LRU cache of the primary constructor: Python keeps a
`collections.OrderedDict` (oldest first) and trims it to `_strong_cache_size = 8`
(Lib/zoneinfo/_zoneinfo.py:31-56, :94-103); C keeps a doubly linked list (newest first)
of at most `ZONEINFO_STRONG_CACHE_MAX_SIZE = 8` nodes (Modules/_zoneinfo.c:2353-2590,
:314-364, :506-567).

Scope of `newPy`/`newC`/`runPy`/`runC` (the cases outside it are modelled further down and
refuted in ZoneProps.lean):
* the base class `ZoneInfo`. For a subclass the C strong cache is a no-op
  (:2520-2522, :2547-2549, :2584-2586: "Strong cache currently only implemented for base
  class"), while Python gives each subclass its own (`__init_subclass__`, :36-38); that is
  `runSubPy`/`runSubC` and `CacheTwinsSubclass`;
* keys are compared by a decidable equality that cannot raise, as for the documented `str`
  keys. C compares with `PyObject_RichCompareBool` (:2441), Python through the dict's hash
  and `__eq__`. A key whose `__eq__` re-enters `clear_cache()` is `findInStrongC`
  (`StrongLookupDefined`); keys whose `__eq__` raises or disagrees with `__hash__` are not
  modelled;
* keys have no finalizer that runs Python code. One that constructs a `ZoneInfo` while
  `clear_cache()` frees the list is `clearStrongC` (`ClearCacheDefined`);
* the weak cache is a set of keys whose instance is still alive: it gains the key of every
  instance built by the constructor (`setdefault`), and loses one when the instance is
  collected, which can only happen while no strong entry holds it (`drop`).
-/

namespace PyLean.Datetime.Zone

/-- Operations on the class: `ZoneInfo(k)`, `clear_cache()`, `clear_cache(only_keys=ks)`, and
the collection of the instance of `k`. -/
inductive CacheOp (K : Type) where
  | get (k : K)
  | clear
  | clearKeys (ks : List K)
  | drop (k : K)

variable {K : Type} [DecidableEq K]

/-- The state of one twin: the strong cache in that twin's order, and the weak cache. -/
structure CacheSt (K : Type) where
  strong : List K
  weak : List K

/-- `ZoneInfo.__new__`, _zoneinfo.py:40-56: the weak cache first, building the instance on a
miss (`loads k` says whether `_new_instance` succeeds; when it raises, nothing changes); then
`cls._strong_cache[key] = cls._strong_cache.pop(key, instance)` moves the key to the end, and
past 8 entries the oldest is popped. -/
def newPy (loads : K → Bool) (st : CacheSt K) (k : K) : Option (CacheSt K) :=
  let weak? : Option (List K) :=
    if k ∈ st.weak then some st.weak
    else if loads k then some (k :: st.weak) else none
  weak?.map fun weak =>
    let strong := st.strong.erase k ++ [k]
    let strong := if strong.length > 8 then strong.tail else strong
    ⟨strong, weak⟩

/-- `zoneinfo_ZoneInfo_impl`, Modules/_zoneinfo.c:314-364, on the base class: a strong hit
(`zone_from_strong_cache`, :2516-2535, with `find_in_strong_cache` :2436-2453) moves the node to
the front (`move_strong_cache_node_to_front`, :2486-2505, through `remove_from_strong_cache`,
:2409-2427) and returns. Otherwise the weak cache, building on a miss, and then
`update_strong_cache` (:2543-2574) puts a new node (`strong_cache_node_new`, :2359-2373) in
front and frees everything after the eighth (`strong_cache_free`, :2391-2402). -/
def newC (loads : K → Bool) (st : CacheSt K) (k : K) : Option (CacheSt K) :=
  if k ∈ st.strong then some ⟨k :: st.strong.erase k, st.weak⟩
  else
    let weak? : Option (List K) :=
      if k ∈ st.weak then some st.weak
      else if loads k then some (k :: st.weak) else none
    weak?.map fun weak => ⟨(k :: st.strong).take 8, weak⟩

/-- `ZoneInfo.clear_cache`, _zoneinfo.py:94-103: per key, the weak cache then the strong one. -/
def clearPy (only : Option (List K)) (st : CacheSt K) : CacheSt K :=
  match only with
  | none => ⟨[], []⟩
  | some ks => ks.foldl (fun st k => ⟨st.strong.erase k, st.weak.erase k⟩) st

/-- `zoneinfo_ZoneInfo_clear_cache_impl`, Modules/_zoneinfo.c:506-567: `weak_cache.clear()`
and `clear_strong_cache` (:2581-2590); or per key `eject_from_strong_cache` (:2459-2479) then
`weak_cache.pop(key, None)`. -/
def clearC (only : Option (List K)) (st : CacheSt K) : CacheSt K :=
  match only with
  | none => ⟨[], []⟩
  | some ks => ks.foldl (fun st k => ⟨st.strong.erase k, st.weak.erase k⟩) st

/-- One operation; `none` when `ZoneInfo(k)` raised (the state is then unchanged). `drop k`
is a collection, so it is only possible while no strong entry holds `k`. -/
def stepPy (loads : K → Bool) (st : CacheSt K) : CacheOp K → Option (CacheSt K)
  | .get k => newPy loads st k
  | .clear => some (clearPy none st)
  | .clearKeys ks => some (clearPy (some ks) st)
  | .drop k => some ⟨st.strong, if k ∈ st.strong then st.weak else st.weak.erase k⟩

def stepC (loads : K → Bool) (st : CacheSt K) : CacheOp K → Option (CacheSt K)
  | .get k => newC loads st k
  | .clear => some (clearC none st)
  | .clearKeys ks => some (clearC (some ks) st)
  | .drop k => some ⟨st.strong, if k ∈ st.strong then st.weak else st.weak.erase k⟩

/-- A run of operations; a raising `ZoneInfo(k)` leaves the state as it was. The list records
which operations raised. -/
def runPy (loads : K → Bool) : CacheSt K → List (CacheOp K) → CacheSt K × List Bool
  | st, [] => (st, [])
  | st, op :: ops =>
    match stepPy loads st op with
    | some st' => let (s, r) := runPy loads st' ops; (s, false :: r)
    | none => let (s, r) := runPy loads st ops; (s, true :: r)

def runC (loads : K → Bool) : CacheSt K → List (CacheOp K) → CacheSt K × List Bool
  | st, [] => (st, [])
  | st, op :: ops =>
    match stepC loads st op with
    | some st' => let (s, r) := runC loads st' ops; (s, false :: r)
    | none => let (s, r) := runC loads st ops; (s, true :: r)

/-! ### Subclasses -/

/-- `ZoneInfo.__init_subclass__`, _zoneinfo.py:36-38: a fresh strong cache, then
`weakref.WeakValueDictionary()` (`wvd`, which raises if the lookup or call does). -/
def initSubclassPy (wvd : Py Unit) : Py (CacheSt K) := wvd.map fun _ => ⟨[], []⟩

/-- C `zoneinfo_init_subclass`, Modules/_zoneinfo.c:2622-2637, with `new_weak_cache`
(:2592-2603): `weakref.WeakValueDictionary()` stored as `cls._weak_cache`; there is no strong
cache for a subclass. -/
def initSubclassC (wvd : Py Unit) : Py (CacheSt K) := wvd.map fun _ => ⟨[], []⟩

/-- `zoneinfo_ZoneInfo_impl` on a subclass: `zone_from_strong_cache` misses at once
(:2520-2522), `get_weak_cache` reads `cls._weak_cache` (:299-301), and `update_strong_cache`
returns without inserting (:2547-2549). The Python `__new__` is `newPy` on the subclass's own
caches. -/
def newCSub (loads : K → Bool) (st : CacheSt K) (k : K) : Option (CacheSt K) :=
  let weak? : Option (List K) :=
    if k ∈ st.weak then some st.weak
    else if loads k then some (k :: st.weak) else none
  weak?.map fun weak => ⟨st.strong, weak⟩

/-- `ZoneInfo(k)` calls on a subclass, after its creation; the weak cache loses every key the
strong cache does not hold after each call (refcounting frees the instance at once). -/
def runSubPy (loads : K → Bool) (st : CacheSt K) : List K → CacheSt K
  | [] => st
  | k :: ks =>
    let st := (newPy loads st k).getD st
    runSubPy loads ⟨st.strong, st.weak.filter (· ∈ st.strong)⟩ ks

def runSubC (loads : K → Bool) (st : CacheSt K) : List K → CacheSt K
  | [] => st
  | k :: ks =>
    let st := (newCSub loads st k).getD st
    runSubC loads ⟨st.strong, st.weak.filter (· ∈ st.strong)⟩ ks

/-! ### Re-entry through key finalizers and comparisons (C) -/

/-- C `clear_strong_cache`, Modules/_zoneinfo.c:2581-2590, on the base class, with keys that
have finalizers. `strong_cache_free` (:2391-2402) walks the list it was given, and
`strong_cache_node_free` (:2376-2383) drops the node's key, then its zone (whose dealloc drops
`zone->key`, the key's last reference, `zoneinfo_clear` :376-382), and only then frees the node;
`state->ZONEINFO_STRONG_CACHE` is reset after the whole walk (:2589). `dels k` lists the keys
the finalizer of `k` passes to `ZoneInfo(...)`. While node 0 is being released the list is
intact, so such a call works on it, unless inserting trims a node the walk frees again (double
free); from node 1 on the head is node 0, already freed, and `find_in_strong_cache` reads it.
`none` is that undefined behaviour. The weak cache was cleared first (:518). -/
def clearStrongC (loads : K → Bool) (dels : K → List K) (st : CacheSt K) : Option (CacheSt K) :=
  let call (i : Nat) (s : CacheSt K) (k' : K) : Option (CacheSt K) :=
    if i ≥ 1 then none
    else if k' ∉ s.strong ∧ (k' ∈ s.weak ∨ loads k' = true) ∧ s.strong.length ≥ 8 then none
    else some ((newC loads s k').getD s)    -- a failing `ZoneInfo(k')` in a finalizer is unraisable
  let rec walk : Nat → List K → CacheSt K → Option (CacheSt K)
    | _, [], s => some s
    | i, k :: rest, s =>
      match (dels k).foldlM (call i) s with
      | none => none
      | some s => walk (i + 1) rest s
  (walk 0 st.strong ⟨st.strong, []⟩).map fun s => ⟨[], s.weak⟩

/-- C `find_in_strong_cache`, :2436-2453, when the comparison `key == node->key` can run
`ZoneInfo.clear_cache()` (`clears key k`): that frees every node, so afterwards reading
`node->next`, or handing the node to `move_strong_cache_node_to_front`, reads freed memory
(`none`). `eq` is the comparison's result. -/
def findInStrongC (eq clears : K → K → Bool) (key : K) : List K → Option (Option K)
  | [] => some none
  | k :: rest =>
    if clears key k then none
    else if eq key k then some (some k)
    else findInStrongC eq clears key rest

end PyLean.Datetime.Zone
