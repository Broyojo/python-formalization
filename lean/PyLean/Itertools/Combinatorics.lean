import PyLean.Itertools.Model

/-!
The combinatoric iterators: `product` (:2060-2326), `combinations`
(:2328-2553), `combinations_with_replacement` (:2555-2801) and `permutations`
(:2803-3081) of Modules/itertoolsmodule.c, and their doc equivalents
(Doc/library/itertools.rst:234-254, :277-294, :550-576, :599-612).

Each C object keeps an index array (`Py_ssize_t *indices`, plus `cycles` for
permutations) and a cached result tuple; the result tuple is always
`pool[indices[k]]` for the current indices, so the model stores only the
indices and produces the tuple from them. Index arrays are `List Nat`
(all entries lie in `[0, n)`). Each iterator is drained with an explicit fuel;
`*Fuel` gives a sufficient amount computed from the closed-form counts.
-/

namespace PyLean.Itertools

open PyLean

/-- `l[i]` for an in-range index (`PyTuple_GET_ITEM`). -/
def at! (l : List Int) (i : Nat) : Int := l.getD i 0

/-- `tuple(pool[i] for i in indices)`. -/
def pick (pool : List Int) (idx : List Nat) : List Int := idx.map (at! pool)

/-- `idx[i]` on an index array. -/
def ix (idx : List Nat) (i : Nat) : Nat := idx.getD i 0

/-! ## Counts (used for fuel and in the properties) -/

/-- Binomial coefficient, by Pascal's rule. -/
def choose : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => choose n k + choose n (k + 1)

/-- Falling factorial `n!/(n-r)!` (`math.perm(n, r)`, zero for `r > n`). -/
def perm : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, r + 1 => (n + 1) * perm n r

/-- `C(n, k)` computed with `min(k, n-k)` multiplications (for fuel only). -/
def chooseFast (n k : Nat) : Nat :=
  if k > n then 0
  else
    let k := min k (n - k)
    (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1

/-! ## product -/

structure ProductState where
  pools : List (List Int)
  indices : List Nat
  started : Bool
  stopped : Bool

/-- `[tuple(pool) for pool in iterables] * repeat`. -/
def prodPools (args : List (List Int)) (rep : Int) : List (List Int) :=
  if args.length = 0 then [] else (List.replicate rep.toNat args).flatten

/-- `product_new` (:2073-2153). `rep? = none` is "no keyword" (repeat 1). -/
def cProductNew (args : List (List Int)) (rep? : Option Int) : Py ProductState :=
  -- :2081-2097
  let parsed : Py Int :=
    match rep? with
    | none => .ok 1
    | some r =>
      match asSsize r with
      | .error e => .error e
      | .ok v =>
        if v < 0 then .error (.valueError "repeat argument cannot be negative") else .ok v
  match parsed with
  | .error e => .error e
  | .ok rep =>
    -- :2099-2109
    let nargs : Int := if rep = 0 then 0 else args.length
    if rep ≠ 0 ∧ nargs > ssizeMax / 8 / rep then
      .error (.overflowError "repeat argument too large")
    else
      let npools := nargs * rep
      -- :2111-2119
      if !memNewOk npools then .error memoryError
      else if !tupleNewOk npools then .error memoryError
      else .ok { pools := prodPools args rep, indices := List.replicate npools.toNat 0,
                 started := false, stopped := false }

/-- The right-to-left odometer loop of `product_next_lock_held` (:2241-2262),
by recursion on `i + 1`: `none` is "`i` went negative". -/
def cProductAdvance (pools : List (List Int)) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | i + 1, idx =>
    let pool := pools.getD i []
    let v := ix idx i + 1
    if v = pool.length then cProductAdvance pools i (idx.set i 0)
    else some (idx.set i v)

/-- `product_next_lock_held` (:2190-2274). -/
def cProductNext (s : ProductState) : Step ProductState (List Int) :=
  if s.stopped then .stop s
  else if !s.started then
    if s.pools.any (·.isEmpty) then .stop { s with stopped := true }
    else .yield (s.pools.map (at! · 0)) { s with started := true }
  else
    match cProductAdvance s.pools s.pools.length s.indices with
    | none => .stop { s with stopped := true }
    | some idx => .yield (List.zipWith (fun p i => at! p i) s.pools idx) { s with indices := idx }

def cProductF (fuel : Nat) (args : List (List Int)) (rep? : Option Int) : Run (List Int) :=
  match cProductNew args rep? with
  | .error e => Run.err e
  | .ok s => drain cProductNext fuel s

/-- With enough fuel: the number of tuples is the product of the pool sizes. -/
def cProduct (args : List (List Int)) (rep? : Option Int) : Run (List Int) :=
  match cProductNew args rep? with
  | .error e => Run.err e
  | .ok s => drain cProductNext ((s.pools.map List.length).foldr (· * ·) 1 + 2) s

/-- `result = [x+[y] for x in result for y in pool]`. -/
def docProductStep (result : List (List Int)) (pool : List Int) : List (List Int) :=
  result.flatMap (fun x => pool.map (fun y => x ++ [y]))

/-- rst:599-612. `[...] * repeat` is `list_repeat`: `OverflowError` for
`repeat > sys.maxsize`, `MemoryError` when the list would not fit. -/
def docProduct (args : List (List Int)) (rep? : Option Int) : Run (List Int) :=
  let rep := rep?.getD 1
  if rep < 0 then Run.err (.valueError "repeat argument cannot be negative")
  else if let .error e := listRepeatCheck args.length rep then Run.err e
  else
    Run.ok ((prodPools args rep).foldl docProductStep [[]])

/-! ## combinations -/

structure CombState where
  pool : List Int
  indices : List Nat
  r : Nat
  started : Bool
  stopped : Bool

/-- Argument Clinic converts `r` before the body runs (`Py_ssize_t`), then
`itertools_combinations_impl` (:2352-2398) builds the pool, checks `r`,
allocates `indices` and sets `stopped = r > n`. -/
def cCombinationsNew (pool : List Int) (r : Int) : Py CombState := do
  let r ← asSsize r
  if r < 0 then throw (.valueError "r must be non-negative")
  if !memNewOk r then throw memoryError
  return { pool := pool, indices := List.range r.toNat, r := r.toNat, started := false,
           stopped := decide (r > pool.length) }

/-- `for (i=r-1 ; i >= 0 && indices[i] == i+n-r ; i--)` (:2483-2484), by
recursion on `i + 1`; `none` is `i < 0`. -/
def cCombScan (n r : Nat) (idx : List Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if ix idx i = i + n - r then cCombScan n r idx i else some i

/-- `for (j=i+1 ; j<r ; j++) indices[j] = indices[j-1] + 1;` (:2496-2497),
with `k = r - j` iterations left. -/
def cCombFill (j : Nat) : Nat → List Nat → List Nat
  | 0, idx => idx
  | k + 1, idx => cCombFill (j + 1) k (idx.set j (ix idx (j - 1) + 1))

/-- `combinations_next_lock_held` (:2433-2516). -/
def cCombinationsNext (s : CombState) : Step CombState (List Int) :=
  if s.stopped then .stop s
  else if !s.started then
    if !tupleNewOk s.r then .raise memoryError { s with stopped := true }
    else .yield (pick s.pool s.indices) { s with started := true }
  else
    let n := s.pool.length
    match cCombScan n s.r s.indices s.r with
    | none => .stop { s with stopped := true }
    | some i =>
      let idx := s.indices.set i (ix s.indices i + 1)
      let idx := cCombFill (i + 1) (s.r - (i + 1)) idx
      .yield (pick s.pool idx) { s with indices := idx }

def combFuel (pool : List Int) (r : Int) : Nat := chooseFast pool.length r.toNat + 2

def cCombinationsF (fuel : Nat) (pool : List Int) (r : Int) : Run (List Int) :=
  match cCombinationsNew pool r with
  | .error e => Run.err e
  | .ok s => drain cCombinationsNext fuel s

def cCombinations (pool : List Int) (r : Int) : Run (List Int) :=
  cCombinationsF (combFuel pool r) pool r

/-- `for i in reversed(range(r)): if indices[i] != i + n - r: break`
(rst:245-249); `none` is the `else: return`. -/
def docCombScan (n : Nat) (r : Int) (idx : List Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if (ix idx i : Int) ≠ i + n - r then some i else docCombScan n r idx i

/-- `for j in range(i+1, r): indices[j] = indices[j-1] + 1` (rst:252-253). -/
def docCombFill (j : Nat) : Nat → List Nat → List Nat
  | 0, idx => idx
  | k + 1, idx => docCombFill (j + 1) k (idx.set j (ix idx (j - 1) + 1))

/-- The `while True` loop of rst:244-254. -/
def docCombLoop (pool : List Int) (r : Int) : Nat → List Nat → Run (List Int)
  | 0, _ => Run.err .modelFuel
  | fuel + 1, idx =>
    match docCombScan pool.length r idx r.toNat with
    | none => Run.ok []
    | some i =>
      let idx := idx.set i (ix idx i + 1)
      let idx := docCombFill (i + 1) (r.toNat - (i + 1)) idx
      Run.cons (pick pool idx) (docCombLoop pool r fuel idx)

/-- rst:234-254. `r` is an int; `range(r)` is empty for `r < 0`. -/
def docCombinationsF (fuel : Nat) (pool : List Int) (r : Int) : Run (List Int) :=
  let n := pool.length
  if r > n then Run.ok []
  else
    let idx := List.range r.toNat
    Run.cons (pick pool idx) (docCombLoop pool r fuel idx)

def docCombinations (pool : List Int) (r : Int) : Run (List Int) :=
  docCombinationsF (combFuel pool r) pool r

/-! ## combinations_with_replacement -/

/-- `itertools_combinations_with_replacement_impl` (:2605-2652). -/
def cCwrNew (pool : List Int) (r : Int) : Py CombState := do
  let r ← asSsize r
  if r < 0 then throw (.valueError "r must be non-negative")
  if !memNewOk r then throw memoryError
  return { pool := pool, indices := List.replicate r.toNat 0, r := r.toNat, started := false,
           stopped := pool.length == 0 && r != 0 }

/-- `for (i=r-1 ; i >= 0 && indices[i] == n-1; i--)` (:2737-2738). -/
def cCwrScan (n : Nat) (idx : List Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if (ix idx i : Int) = (n : Int) - 1 then cCwrScan n idx i else some i

/-- `for ( ; i<r ; i++) indices[i] = index;` (:2750-2756). -/
def cCwrFill (v : Nat) (i : Nat) : Nat → List Nat → List Nat
  | 0, idx => idx
  | k + 1, idx => cCwrFill v (i + 1) k (idx.set i v)

/-- `cwr_next_lock_held` (:2687-2764). -/
def cCwrNext (s : CombState) : Step CombState (List Int) :=
  if s.stopped then .stop s
  else if !s.started then
    if !tupleNewOk s.r then .raise memoryError { s with stopped := true }
    else .yield (pick s.pool s.indices) { s with started := true }
  else
    match cCwrScan s.pool.length s.indices s.r with
    | none => .stop { s with stopped := true }
    | some i =>
      let v := ix s.indices i + 1
      let idx := cCwrFill v i (s.r - i) s.indices
      .yield (pick s.pool idx) { s with indices := idx }

def cwrFuel (pool : List Int) (r : Int) : Nat :=
  if pool.length = 0 then 3 else chooseFast (pool.length + r.toNat - 1) r.toNat + 2

def cCwrF (fuel : Nat) (pool : List Int) (r : Int) : Run (List Int) :=
  match cCwrNew pool r with
  | .error e => Run.err e
  | .ok s => drain cCwrNext fuel s

def cCwr (pool : List Int) (r : Int) : Run (List Int) := cCwrF (cwrFuel pool r) pool r

/-- `for i in reversed(range(r)): if indices[i] != n - 1: break` (rst:287-291). -/
def docCwrScan (n : Nat) (idx : List Nat) : Nat → Option Nat
  | 0 => none
  | i + 1 => if (ix idx i : Int) ≠ (n : Int) - 1 then some i else docCwrScan n idx i

/-- The `while True` loop of rst:286-294; `indices[i:] = [indices[i] + 1] * (r - i)`. -/
def docCwrLoop (pool : List Int) (r : Int) : Nat → List Nat → Run (List Int)
  | 0, _ => Run.err .modelFuel
  | fuel + 1, idx =>
    match docCwrScan pool.length idx r.toNat with
    | none => Run.ok []
    | some i =>
      let idx := idx.take i ++ List.replicate (r.toNat - i) (ix idx i + 1)
      Run.cons (pick pool idx) (docCwrLoop pool r fuel idx)

/-- rst:277-294. -/
def docCwrF (fuel : Nat) (pool : List Int) (r : Int) : Run (List Int) :=
  let n := pool.length
  if n = 0 ∧ r ≠ 0 then Run.ok []
  else if let .error e := listRepeatCheck 1 r then Run.err e
  else
    let idx := List.replicate r.toNat 0
    Run.cons (pick pool idx) (docCwrLoop pool r fuel idx)

def docCwr (pool : List Int) (r : Int) : Run (List Int) := docCwrF (cwrFuel pool r) pool r

/-! ## permutations -/

structure PermState where
  pool : List Int
  indices : List Nat
  cycles : List Int
  r : Nat
  started : Bool
  stopped : Bool

/-- `itertools_permutations_impl` (:2854-2919): the pool is built first, then
`r` (`None` → `n`) goes through `PyLong_AsSsize_t`. -/
def cPermutationsNew (pool : List Int) (robj : Option Int) : Py PermState := do
  let n := pool.length
  let r ← match robj with
    | none => pure (n : Int)
    | some v => asSsize v
  if r < 0 then throw (.valueError "r must be non-negative")
  if !memNewOk n || !memNewOk r then throw memoryError
  return { pool := pool, indices := List.range n, r := r.toNat,
           cycles := (List.range r.toNat).map (fun (i : Nat) => (n : Int) - (i : Int)),
           started := false, stopped := decide (r > n) }

/-- The rotation `indices[i:] = indices[i+1:] + indices[i:i+1]` as the C loop
(:3009-3013): shift `indices[i+1..n)` left by one, put the old `indices[i]` last. -/
def cPermRotate (n i : Nat) (idx : List Nat) : List Nat :=
  let index := ix idx i
  let idx := go i (n - 1 - i) idx
  idx.set (n - 1) index
where
  go : Nat → Nat → List Nat → List Nat
    | _, 0, idx => idx
    | j, k + 1, idx => go (j + 1) k (idx.set j (ix idx (j + 1)))

/-- The `for (i=r-1 ; i>=0 ; i--)` loop of `permutations_next_lock_held`
(:3006-3036), by recursion on `i + 1`; `none` is "`i` went negative". -/
def cPermLoop (n : Nat) : Nat → List Nat → List Int → Option (List Nat × List Int) ⊕ (List Nat × List Int)
  | 0, idx, cyc => .inr (idx, cyc)
  | i + 1, idx, cyc =>
    let c := cyc.getD i 0 - 1
    let cyc := cyc.set i c
    if c = 0 then
      cPermLoop n i (cPermRotate n i idx) (cyc.set i ((n : Int) - i))
    else
      let j := c.toNat
      let index := ix idx i
      let idx := idx.set i (ix idx (n - j))
      let idx := idx.set (n - j) index
      .inl (some (idx, cyc))

/-- `permutations_next_lock_held` (:2956-3044). -/
def cPermutationsNext (s : PermState) : Step PermState (List Int) :=
  if s.stopped then .stop s
  else if !s.started then
    if !tupleNewOk s.r then .raise memoryError { s with stopped := true }
    else .yield (pick s.pool (s.indices.take s.r)) { s with started := true }
  else
    let n := s.pool.length
    if n = 0 then .stop { s with stopped := true }
    else match cPermLoop n s.r s.indices s.cycles with
      | .inl (some (idx, cyc)) =>
        .yield (pick s.pool (idx.take s.r)) { s with indices := idx, cycles := cyc }
      | .inl none | .inr _ => .stop { s with stopped := true }

def permFuel (pool : List Int) (robj : Option Int) : Nat :=
  let n := pool.length
  let r := (robj.getD n).toNat
  if r > n then 2 else (List.range r).foldl (fun acc i => acc * (n - i)) 1 + 2

def cPermutationsF (fuel : Nat) (pool : List Int) (robj : Option Int) : Run (List Int) :=
  match cPermutationsNew pool robj with
  | .error e => Run.err e
  | .ok s => drain cPermutationsNext fuel s

def cPermutations (pool : List Int) (robj : Option Int) : Run (List Int) :=
  cPermutationsF (permFuel pool robj) pool robj

/-- Python `l[a:]`-style negative index normalisation for `indices[-j]`
with `1 ≤ j ≤ n`: position `n - j`. Python `indices[:r]` for an int `r`. -/
def pySliceTo (l : List Nat) (r : Int) : List Nat :=
  if r ≥ 0 then l.take r.toNat else l.take (max 0 (l.length + r)).toNat

/-- The `for i in reversed(range(r))` body of rst:562-576, by recursion on
`i + 1`: `.inl idx,cyc` is "yielded and broke out", `.inr` is "fell off the
end" (the `else: return`). -/
def docPermLoop (n : Nat) : Nat → List Nat → List Int → (List Nat × List Int) ⊕ Unit
  | 0, _, _ => .inr ()
  | i + 1, idx, cyc =>
    let cyc := cyc.set i (cyc.getD i 0 - 1)
    if cyc.getD i 0 = 0 then
      let idx := idx.take i ++ (idx.drop (i + 1) ++ (idx.drop i).take 1)
      docPermLoop n i idx (cyc.set i ((n : Int) - i))
    else
      -- `indices[i], indices[-j] = indices[-j], indices[i]`
      let j := (cyc.getD i 0).toNat
      let a := ix idx i
      let b := ix idx (n - j)
      .inl ((idx.set i b).set (n - j) a, cyc)

/-- The `while n:` loop of rst:561-576. -/
def docPermOuter (pool : List Int) (r : Int) : Nat → List Nat → List Int → Run (List Int)
  | 0, _, _ => Run.err .modelFuel
  | fuel + 1, idx, cyc =>
    let n := pool.length
    if n = 0 then Run.ok []
    else match docPermLoop n r.toNat idx cyc with
      | .inr () => Run.ok []
      | .inl (idx, cyc) => Run.cons (pick pool (pySliceTo idx r)) (docPermOuter pool r fuel idx cyc)

/-- rst:550-576. -/
def docPermutationsF (fuel : Nat) (pool : List Int) (robj : Option Int) : Run (List Int) :=
  let n := pool.length
  let r : Int := robj.getD n
  if r > n then Run.ok []
  else
    let idx := List.range n
    let cyc := (List.range r.toNat).map (fun (i : Nat) => (n : Int) - (i : Int))
    Run.cons (pick pool (pySliceTo idx r)) (docPermOuter pool r fuel idx cyc)

def docPermutations (pool : List Int) (robj : Option Int) : Run (List Int) :=
  docPermutationsF (permFuel pool robj) pool robj

end PyLean.Itertools
