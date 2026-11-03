import PyLean.Core

/-!
# The `ZoneInfo` caches (CPython 3.15.2), both twins

The strong LRU cache of the primary constructor: Python keeps a
`collections.OrderedDict` (oldest first) and trims it to `_strong_cache_size = 8`
(Lib/zoneinfo/_zoneinfo.py:31-56, :94-103); C keeps a doubly linked list (newest first)
of at most `ZONEINFO_STRONG_CACHE_MAX_SIZE = 8` nodes (Modules/_zoneinfo.c:2353-2590,
:314-364, :506-567).

Scope limits, stated:
* the base class `ZoneInfo` only. For a subclass the C strong cache is a no-op
  (:2520-2522, :2547-2549, :2584-2586: "Strong cache currently only implemented for base
  class"), while Python gives each subclass its own (`__init_subclass__`, :36-38);
* keys are compared by a decidable equality that cannot raise, as for the documented `str`
  keys. C compares with `PyObject_RichCompareBool` (:2441), Python through the dict's hash
  and `__eq__`; keys whose `__eq__` raises or disagrees with `__hash__` are not modelled;
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

end PyLean.Datetime.Zone
