import PyLean.CoreLibs.Functools.Compare

/-!
`lru_cache`, Lib/functools.py:553-714 and Modules/_functoolsmodule.c:1063-1734.

The user function is a program (`Prog`): it may call the cached function again, clear the cache, or
raise, so the re-check after the call is a real branch. The four dict operations of the bounded wrapper
may each raise, from `__hash__` or from an `__eq__` on a colliding key (`Faults`). The Python wrapper
writes to the ring before the dict and the C wrapper the other way round, so a failing insertion leaves
the two in different states.

A `__eq__` that re-enters the wrapper is not modelled here, and neither is the state after a failed `del`
beyond its first consequence: `LruPtr.lean` has both, with the links as cells and the dict as a table.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- What the user function does when called. -/
inductive Prog (K V : Type) where
  | ret (v : V)
  | raise (e : PyExc)
  /-- Call the cached wrapper with this key, then go on with its result. -/
  | call (k : K) (cont : Py V → Prog K V)
  /-- `wrapper.cache_clear()`, then go on. -/
  | clear (cont : Prog K V)

/-- Failures of the dict operations of a bounded wrapper, given the key and the keys in the cache. `get`
is the first lookup, `recheck` the lookup after the user function, `evict` the deletion of the oldest key,
and `insert` the store. Each may run `__hash__` or `__eq__`. -/
structure Faults (K : Type) where
  get : K → List K → Option PyExc
  recheck : K → List K → Option PyExc
  evict : K → List K → Option PyExc
  insert : K → List K → Option PyExc

def noFaults (K : Type) : Faults K := ⟨fun _ _ => none, fun _ _ => none, fun _ _ => none, fun _ _ => none⟩

/-- Remove the last element satisfying `p`: the link the dict refers to, which is the newest with
that key if an earlier failure stranded another. -/
def dropLastP {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if xs.any p then x :: dropLastP p xs else if p x then xs else x :: xs

/-- The C wrapper's state, Modules/_functoolsmodule.c:1125-1136: the linked list from oldest to newest,
and the keys of the `cache` dict in its own insertion order, which a hit does not change. They hold the
same keys, because C stores in the dict before linking. -/
structure CLru (K V : Type) where
  links : List (K × V)
  cache : List K
  hits : Nat
  misses : Nat
  deriving Repr, DecidableEq

/-- The Python wrapper's closure state, Lib/functools.py:606-613: the circular list starting at `root`,
which is the `none` link, and the keys of the `cache` dict, kept separately because a failure can leave
them out of step. After a failed `del cache[oldkey]`, Lib/functools.py:683, the dict still has `oldkey`, and its link is the
new root, whose key and result are `None`: `stale` is that key. A hit on it returns `None`, and leaves `root[NEXT]` pointing
at the root itself, which a list cannot show: `broken` marks that, and the model stops there. -/
structure PyLru (K V : Type) where
  ring : List (Option (K × V))
  cache : List K
  hits : Nat
  misses : Nat
  full : Bool
  broken : Bool
  stale : Option K
  deriving Repr, DecidableEq

def emptyC {K V : Type} : CLru K V := ⟨[], [], 0, 0⟩
def emptyPy {K V : Type} : PyLru K V := ⟨[none], [], 0, 0, false, false, none⟩

/-- A bounded cached function: `maxsize`, the user function and the dict faults. The user function gets the
key and the current miss count, which a real function can read with `cache_info()`: so the same key can
take a different path on a re-entrant call, and that re-entrant call can terminate. `none` is the value `None`. -/
structure Cfg (K V : Type) where
  maxsize : Nat
  f : K → Nat → Prog K V
  F : Faults K
  none : V

section
variable {K V : Type} [DecidableEq K]

def ringIs (k : K) : Option (K × V) → Bool
  | some p => decide (p.1 = k)
  | none => false

/-- The last element satisfying `p`, the link `dropLastP` removes. -/
def lastP {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    match lastP p xs with
    | some y => some y
    | none => if p x then some x else none

def ringValue (k : K) (ring : List (Option (K × V))) : Option V :=
  ((lastP (ringIs k) ring).join).map Prod.snd

mutual
  /-- `wrapper(*args)` of the bounded branch, Lib/functools.py:641-696. -/
  def callPy (cfg : Cfg K V) : Nat → K → PyLru K V → Py V × PyLru K V
    | 0, _, s => (.error .modelFuel, s)
    | fuel + 1, key, s =>
      if s.broken then (.error .modelFuel, s) else
      match cfg.F.get key s.cache with
      | some e => (.error e, s)
      | none =>
        if key ∈ s.cache then
          -- :647-657: move the link to the front of the circular queue
          match ringValue key s.ring with
          | some result =>
            (.ok result, { s with
              ring := dropLastP (ringIs key) s.ring ++ [some (key, result)], hits := s.hits + 1 })
          | none =>
            -- :649: the link is the root
            if s.stale = some key then (.ok cfg.none, { s with hits := s.hits + 1, broken := true })
            else (.error .modelFuel, s)
        else
          let s := { s with misses := s.misses + 1 }
          match runPy cfg fuel (cfg.f key s.misses) s with
          | (.error e, s) => (.error e, s)
          | (.ok result, s) =>
            match cfg.F.recheck key s.cache with
            | some e => (.error e, s)
            | none =>
              if key ∈ s.cache then (.ok result, s)   -- :661-666
              else if s.full then
                match s.ring with
                | _ :: some old :: rest =>
                  -- :669-681: the old root takes the key, the oldest link becomes the root
                  let s := { s with ring := none :: rest ++ [some (key, result)] }
                  match cfg.F.evict old.1 s.cache with
                  | some e => (.error e, { s with stale := some old.1 })
                  | none =>
                    if old.1 ∉ s.cache then
                      (.error (.keyError "~key"), s)  -- :683, a link no dict entry refers to
                    else
                      let s := { s with cache := s.cache.erase old.1 }
                      match cfg.F.insert key s.cache with
                      | some e => (.error e, s)
                      | none => (.ok result, { s with cache := s.cache ++ [key] })
                | _ => (.error .modelFuel, s)
              else
                -- :690-695: `last[NEXT] = root[PREV] = cache[key] = link` assigns left to right
                let s := { s with ring := s.ring ++ [some (key, result)] }
                match cfg.F.insert key s.cache with
                | some e => (.error e, s)
                | none =>
                  let cache := s.cache ++ [key]
                  (.ok result, { s with cache, full := decide (cache.length ≥ cfg.maxsize) })

  /-- Running the user function against the Python state. -/
  def runPy (cfg : Cfg K V) : Nat → Prog K V → PyLru K V → Py V × PyLru K V
    | 0, _, s => (.error .modelFuel, s)
    | _ + 1, .ret v, s => (.ok v, s)
    | _ + 1, .raise e, s => (.error e, s)
    | fuel + 1, .call k c, s =>
      match callPy cfg fuel k s with
      | (r, s') => runPy cfg fuel (c r) s'
    | fuel + 1, .clear c, _ => runPy cfg fuel c emptyPy
end

mutual
  /-- `bounded_lru_cache_wrapper`, Modules/_functoolsmodule.c:1493-1521, with
  `bounded_lru_cache_get_lock_held`, :1312-1344, `bounded_lru_cache_update_lock_held`, :1347-1490, and the
  link helpers `lru_cache_extract_link`, `lru_cache_append_link`, `lru_cache_prepend_link`, :1252-1278. -/
  def callC (cfg : Cfg K V) : Nat → K → CLru K V → Py V × CLru K V
    | 0, _, s => (.error .modelFuel, s)
    | fuel + 1, key, s =>
      match cfg.F.get key s.cache with
      | some e => (.error e, s)
      | none =>
        match s.links.lookup key with
        | some result =>
          (.ok result, { s with
            links := dropLastP (fun p => decide (p.1 = key)) s.links ++ [(key, result)],
            hits := s.hits + 1 })
        | none =>
          let s := { s with misses := s.misses + 1 }
          match runC cfg fuel (cfg.f key s.misses) s with
          | (.error e, s) => (.error e, s)
          | (.ok result, s) =>
            match cfg.F.recheck key s.cache with
            | some e => (.error e, s)
            | none =>
              match s.links.lookup key with
              | some _ => (.ok result, s)     -- :1361-1368
              | none =>
                if s.cache.length < cfg.maxsize ∨ s.links.isEmpty then
                  -- :1383-1409: the dict first, then the link
                  match cfg.F.insert key s.cache with
                  | some e => (.error e, s)
                  | none =>
                    (.ok result, { s with
                      links := s.links ++ [(key, result)], cache := s.cache ++ [key] })
                else
                  match s.links with
                  | [] => (.error .modelFuel, s)
                  | old :: rest =>
                    match cfg.F.evict old.1 s.cache with
                    -- :1435-1445: the link goes back to the oldest position
                    | some e => (.error e, s)
                    | none =>
                      if old.1 ∉ s.cache then
                        (.ok result, { s with links := rest })  -- :1446-1454: an orphan link
                      else
                        let cache := s.cache.erase old.1
                        match cfg.F.insert key cache with
                        -- :1473-1482: the cache stays short one link
                        | some e => (.error e, { s with links := rest, cache })
                        | none =>
                          (.ok result, { s with links := rest ++ [(key, result)], cache := cache ++ [key] })

  /-- Running the user function against the C state. -/
  def runC (cfg : Cfg K V) : Nat → Prog K V → CLru K V → Py V × CLru K V
    | 0, _, s => (.error .modelFuel, s)
    | _ + 1, .ret v, s => (.ok v, s)
    | _ + 1, .raise e, s => (.error e, s)
    | fuel + 1, .call k c, s =>
      match callC cfg fuel k s with
      | (r, s') => runC cfg fuel (c r) s'
    | fuel + 1, .clear c, _ => runC cfg fuel c emptyC
end

/-- `d[k] = v`: an existing key keeps its position. -/
def setKey (d : List (K × V)) (k : K) (v : V) : List (K × V) :=
  if d.any (fun p => decide (p.1 = k)) then d.map (fun p => if p.1 = k then (k, v) else p)
  else d ++ [(k, v)]

mutual
  /-- `infinite_lru_cache_wrapper`, Modules/_functoolsmodule.c:1214-1249, and the `maxsize is None`
  branch, Lib/functools.py:626-637: no re-check, so a re-entrant call with the same key is overwritten. -/
  def callInf (f : K → Nat → Prog K V) (F : Faults K) : Nat → K → CLru K V → Py V × CLru K V
    | 0, _, s => (.error .modelFuel, s)
    | fuel + 1, key, s =>
      match F.get key s.cache with
      | some e => (.error e, s)
      | none =>
        match s.links.lookup key with
        | some result => (.ok result, { s with hits := s.hits + 1 })
        | none =>
          let s := { s with misses := s.misses + 1 }
          match runInf f F fuel (f key s.misses) s with
          | (.error e, s) => (.error e, s)
          | (.ok result, s) =>
            match F.insert key s.cache with
            | some e => (.error e, s)
            | none =>
              (.ok result, { s with
                links := setKey s.links key result,
                cache := if key ∈ s.cache then s.cache else s.cache ++ [key] })

  def runInf (f : K → Nat → Prog K V) (F : Faults K) : Nat → Prog K V → CLru K V → Py V × CLru K V
    | 0, _, s => (.error .modelFuel, s)
    | _ + 1, .ret v, s => (.ok v, s)
    | _ + 1, .raise e, s => (.error e, s)
    | fuel + 1, .call k c, s =>
      match callInf f F fuel k s with
      | (r, s') => runInf f F fuel (c r) s'
    | fuel + 1, .clear c, _ => runInf f F fuel c emptyC
end

mutual
  /-- `uncached_lru_cache_wrapper`, Modules/_functoolsmodule.c:1202-1211, and the `maxsize == 0` branch,
  Lib/functools.py:617-622: a miss, then the user function, with no key at all. The state is `misses`. -/
  def callNone (f : K → Nat → Prog K V) : Nat → K → Nat → Py V × Nat
    | 0, _, m => (.error .modelFuel, m)
    | fuel + 1, key, m => runNone f fuel (f key (m + 1)) (m + 1)

  def runNone (f : K → Nat → Prog K V) : Nat → Prog K V → Nat → Py V × Nat
    | 0, _, m => (.error .modelFuel, m)
    | _ + 1, .ret v, m => (.ok v, m)
    | _ + 1, .raise e, m => (.error e, m)
    | fuel + 1, .call k c, m =>
      match callNone f fuel k m with
      | (r, m') => runNone f fuel (c r) m'
    | fuel + 1, .clear c, _ => runNone f fuel c 0
end

end

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
  /-- A callable, the bare `@lru_cache` form. `typedBool` is `isinstance(typed, bool)`. -/
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

/-- The selection at Lib/functools.py:615-639. Any object is accepted as the user function. -/
def wrapperPyMode : Option Int → Py LruMode
  | Option.none => .ok .infinite
  | some 0 => .ok .uncached
  | some m => .ok (.bounded m)

/-- `lru_cache_new`, Modules/_functoolsmodule.c:1541-1571: the user function must be callable, and
`maxsize` must fit in `Py_ssize_t`. -/
def wrapperCMode (callable : Bool) : Option Int → Py LruMode
  | m =>
    if !callable then .error (.typeError "the first argument must be callable") else
    match m with
    | Option.none => .ok .infinite
    | some m =>
      if m > ssizeMax ∨ m < ssizeMin then
        .error (.overflowError "cannot fit 'int' into an index-sized integer")
      else if m ≤ 0 then .ok .uncached
      else .ok (.bounded m)

/-- `cache(user_function)`, Lib/functools.py:726-728: `lru_cache(maxsize=None)(user_function)`. -/
def cacheMode (callable : Bool) : Py LruMode := do
  wrapperCMode callable (← lruCacheArg .none)

/-- `cache_info()`, Lib/functools.py:698-701, Modules/_functoolsmodule.c:1674-1697. -/
structure CacheInfo where
  hits : Nat
  misses : Nat
  maxsize : Option Int
  currsize : Nat
  deriving Repr, DecidableEq

def infoC {K V : Type} (maxsize : Nat) (s : CLru K V) : CacheInfo :=
  ⟨s.hits, s.misses, some maxsize, s.cache.length⟩

/-- The Python wrapper reads `cache_len()`, the dict, not the ring. -/
def infoPy {K V : Type} (maxsize : Nat) (s : PyLru K V) : CacheInfo :=
  ⟨s.hits, s.misses, some maxsize, s.cache.length⟩

/-- `lru_cache_copy` and `lru_cache_deepcopy`, Modules/_functoolsmodule.c:1725-1734: the wrapper is its own
copy. -/
def lruCopy {α : Type} (self : α) : α := self

/-- `lru_cache_reduce`, Modules/_functoolsmodule.c:1719-1722: pickled by qualified name. -/
def lruReduce (qualname : String) : String := qualname

end PyLean.CoreLibs.Functools
