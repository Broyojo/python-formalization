import PyLean.Itertools.Islice

/-!
The non-combinatoric iterators of `Modules/itertoolsmodule.c` (CPython 3.14.7)
and their doc equivalents (`Doc/library/itertools.rst`): `accumulate`,
`batched`, `chain`/`chain.from_iterable`, `compress`, `cycle`, `dropwhile`,
`filterfalse`, `pairwise`, `starmap`, `takewhile`, `zip_longest`.
-/

namespace PyLean.Itertools

open PyLean

/-- Pop the next item of a list iterator. -/
def pop : List Int → Option (Int × List Int)
  | [] => none
  | x :: xs => some (x, xs)

/-! ## accumulate (:3083-3224; rst:102-119) -/

structure AccState where
  it : List Int
  total : Option Int
  initial : Option Int

/-- `accumulate_next_lock_held` (:3163-3193). `binop` is `func` (default
`PyNumber_Add`). -/
def cAccumulateNext (binop : Int → Int → Int) (s : AccState) : Step AccState Int :=
  match s.initial with
  | some t => .yield t { s with total := some t, initial := none }
  | none =>
    match pop s.it with
    | none => .stop s
    | some (val, rest) =>
      match s.total with
      | none => .yield val { s with it := rest, total := some val }
      | some total =>
        let newtotal := binop total val
        .yield newtotal { s with it := rest, total := some newtotal }

def cAccumulate (binop : Int → Int → Int) (initial : Option Int) (l : List Int) : Run Int :=
  drain (cAccumulateNext binop) (l.length + 2) { it := l, total := none, initial := initial }

/-- `for element in iterator: total = function(total, element); yield total`. -/
def docAccumulateLoop (f : Int → Int → Int) : Int → List Int → List Int
  | _, [] => []
  | total, x :: xs => let t := f total x; t :: docAccumulateLoop f t xs

/-- rst:102-119. -/
def docAccumulate (f : Int → Int → Int) (initial : Option Int) (l : List Int) : Run Int :=
  match initial with
  | none =>
    match l with
    | [] => Run.ok []
    | x :: xs => Run.ok (x :: docAccumulateLoop f x xs)
  | some t => Run.ok (t :: docAccumulateLoop f t l)

/-! ## batched (:98-271; rst:175-183) -/

structure BatchedState where
  it : List Int
  batchSize : Int
  strict : Bool

/-- `batched_new_impl` (:137-167); `n` went through the `Py_ssize_t` converter. -/
def cBatchedNew (l : List Int) (n : Int) (strict : Bool) : Py BatchedState := do
  let n ← asSsize n
  if n < 1 then throw (.valueError "n must be at least one")
  return { it := l, batchSize := n, strict := strict }

/-- `batched_next` (:190-249). The `for (i=0; i < n; i++)` loop pulls items
until `n` are read or the input runs out, i.e. takes `min(n, len)` items. -/
def cBatchedNext (s : BatchedState) : Step BatchedState (List Int) :=
  let n := s.batchSize
  if n < 0 then .stop s
  else if !tupleNewOk n then .raise memoryError s
  else
    let batch := s.it.take n.toNat
    let rest := s.it.drop n.toNat
    if (batch.length : Int) = n then .yield batch { s with it := rest }
    else if batch.length = 0 then .stop { s with it := rest, batchSize := -1 }
    else if s.strict then .raise (.valueError "batched(): incomplete batch") { s with it := rest, batchSize := -1 }
    else .yield batch { s with it := rest }

def cBatched (l : List Int) (n : Int) (strict : Bool) : Run (List Int) :=
  match cBatchedNew l n strict with
  | .error e => Run.err e
  | .ok s => drain cBatchedNext (l.length + 2) s

/-- The `while batch := tuple(islice(iterator, n))` loop (rst:180-183), with
the C `islice` (whose `stop` must be at most `sys.maxsize`). -/
def docBatchedLoop (n : Int) (strict : Bool) : Nat → List Int → Run (List Int)
  | 0, _ => Run.err .modelFuel
  | fuel + 1, it =>
    let (r, consumed) := cIslice it [some n]
    match r with
    | (_, some e) => Run.err e
    | (batch, none) =>
      if batch = [] then Run.ok []
      else if strict && (batch.length : Int) != n then Run.err (.valueError "batched(): incomplete batch")
      else Run.cons batch (docBatchedLoop n strict fuel (it.drop consumed.toNat))

/-- rst:175-183. -/
def docBatched (l : List Int) (n : Int) (strict : Bool) : Run (List Int) :=
  if n < 1 then Run.err (.valueError "n must be at least one")
  else docBatchedLoop n strict (l.length + 2) l

/-! ## chain, chain.from_iterable (:1883-2057; rst:198-201, :198) -/

structure ChainState where
  source : Option (List (List Int))
  active : Option (List Int)

/-- The `while (lz->source != NULL)` loop of `chain_next_lock_held`
(:1971-2007), by recursion on the remaining sources. -/
def cChainLoop : List (List Int) → Option (List Int) → Step ChainState Int
  | src, some (x :: xs) => .yield x { source := some src, active := some xs }
  | [], some [] => .stop { source := none, active := none }
  | [], none => .stop { source := none, active := none }
  | it :: src, some [] => cChainLoop src (some it)
  | it :: src, none => cChainLoop src (some it)

def cChainNext (s : ChainState) : Step ChainState Int :=
  match s.source with
  | none => .stop s
  | some src => cChainLoop src s.active

def cChain (ls : List (List Int)) : Run Int :=
  drain cChainNext ((ls.map List.length).sum + 2) { source := some ls, active := none }

/-- `for iterable in iterables: yield from iterable`. -/
def docChain (ls : List (List Int)) : Run Int := Run.ok ls.flatten

/-! ## compress (:3226-3360; rst:299-311) -/

/-- `compress_next` (:3305-3339): pull a datum, then a selector. -/
def cCompressNext (s : List Int × List Int) : Step (List Int × List Int) Int :=
  go s.1 s.2
where
  go : List Int → List Int → Step (List Int × List Int) Int
    | [], sel => .stop ([], sel)
    | _ :: d, [] => .stop (d, [])
    | x :: d, y :: sel => if truthy y then .yield x (d, sel) else go d sel

def cCompress (data sel : List Int) : Run Int :=
  drain cCompressNext (data.length + 2) (data, sel)

/-- `(datum for datum, selector in zip(data, selectors) if selector)`. -/
def docCompress (data sel : List Int) : Run Int :=
  Run.ok ((data.zip sel).filter (fun p => truthy p.2) |>.map Prod.fst)

/-! ## cycle (:1207-1338; rst:342-352) -/

structure CycleState where
  it : Option (List Int)
  saved : List Int
  index : Int

/-- `cycle_next` (:1282-1317). -/
def cCycleNext (s : CycleState) : Step CycleState Int :=
  let fromSaved (s : CycleState) : Step CycleState Int :=
    if s.saved.length = 0 then .stop s
    else
      let item := s.saved.getD s.index.toNat 0
      let index := s.index + 1
      let index := if index ≥ s.saved.length then 0 else index
      .yield item { s with index := index }
  if s.index < 0 then
    match s.it.bind pop with
    | some (item, rest) => .yield item { s with it := some rest, saved := s.saved ++ [item] }
    | none => fromSaved { s with index := 0, it := none }
  else fromSaved s

/-- The first `k` items of `cycle(l)`. -/
def cCycle (l : List Int) (k : Nat) : Run Int :=
  takeN cCycleNext k { it := some l, saved := [], index := -1 }

/-- `while saved: for element in saved: yield element`, first `k` items; the
list argument is what remains of the current `for` pass. -/
def docCycleSaved (saved : List Int) : Nat → List Int → List Int
  | 0, _ => []
  | k + 1, x :: xs => x :: docCycleSaved saved k xs
  | k + 1, [] =>
    match saved with
    | [] => []
    | y :: ys => y :: docCycleSaved saved k ys

/-- rst:342-352: the first pass (`yield element; saved.append(element)`), then
the saved copy forever; the first `k` items. -/
def docCycle (l : List Int) (k : Nat) : Run Int :=
  let first := l.take k
  Run.ok (first ++ docCycleSaved l (k - first.length) [])

/-! ## dropwhile, takewhile, filterfalse (:1340-1578, :3362-3482) -/

/-- `dropwhile_next` (:1410-1441); `start` is the "predicate failed" flag. -/
def cDropwhileNext (pred : Int → Bool) : List Int × Bool → Step (List Int × Bool) Int
  | ([], start) => .stop ([], start)
  | (x :: xs, true) => .yield x (xs, true)
  | (x :: xs, false) => if pred x then cDropwhileNext pred (xs, false) else .yield x (xs, true)

def cDropwhile (pred : Int → Bool) (l : List Int) : Run Int :=
  drain (cDropwhileNext pred) (l.length + 2) (l, false)

/-- rst:364-374. -/
def docDropwhile (pred : Int → Bool) (l : List Int) : Run Int :=
  Run.ok (go l)
where
  go : List Int → List Int
    | [] => []
    | x :: xs => if !pred x then x :: xs else go xs

/-- `takewhile_next` (:1532-1559); the flag is `lz->stop`. -/
def cTakewhileNext (pred : Int → Bool) : List Int × Bool → Step (List Int × Bool) Int
  | (l, true) => .stop (l, true)
  | ([], false) => .stop ([], false)
  | (x :: xs, false) => if pred x then .yield x (xs, false) else .stop (xs, true)

def cTakewhile (pred : Int → Bool) (l : List Int) : Run Int :=
  drain (cTakewhileNext pred) (l.length + 2) (l, false)

/-- rst:665-670. -/
def docTakewhile (pred : Int → Bool) (l : List Int) : Run Int :=
  Run.ok (go l)
where
  go : List Int → List Int
    | [] => []
    | x :: xs => if !pred x then [] else x :: go xs

/-- The truth test of `filterfalse_next`: `PyObject_IsTrue(item)` for `None`
or `bool`, else `PyObject_IsTrue(func(item))`. -/
def ffTest (pred : Option (Int → Bool)) (x : Int) : Bool :=
  match pred with
  | none => truthy x
  | some f => f x

/-- `filterfalse_next` (:3430-3462). `pred = none` is `None` (or `bool`):
`PyObject_IsTrue(item)`. -/
def cFilterfalseNext (pred : Option (Int → Bool)) : List Int → Step (List Int) Int
  | [] => .stop []
  | x :: xs =>
    if !ffTest pred x then .yield x xs else cFilterfalseNext pred xs

def cFilterfalse (pred : Option (Int → Bool)) (l : List Int) : Run Int :=
  drain (cFilterfalseNext pred) (l.length + 2) l

/-- rst:387-395. -/
def docFilterfalse (pred : Option (Int → Bool)) (l : List Int) : Run Int :=
  let p := pred.getD truthy
  Run.ok (l.filter (fun x => !p x))

/-! ## pairwise (:273-424; rst:513-521) -/

structure PairwiseState where
  it : Option (List Int)
  old : Option Int

/-- `pairwise_next` (:346-402). -/
def cPairwiseNext (s : PairwiseState) : Step PairwiseState (Int × Int) :=
  match s.it with
  | none => .stop s
  | some l =>
    let first : Option (Int × List Int) :=
      match s.old with
      | some o => some (o, l)
      | none => pop l
    match first with
    | none => .stop { it := none, old := none }
    | some (old, l) =>
      match pop l with
      | none => .stop { it := none, old := none }
      | some (new, rest) => .yield (old, new) { it := some rest, old := some new }

def cPairwise (l : List Int) : Run (Int × Int) :=
  drain cPairwiseNext (l.length + 2) { it := some l, old := none }

/-- `for b in iterator: yield a, b; a = b`. -/
def docPairwiseLoop : Int → List Int → List (Int × Int)
  | _, [] => []
  | a, b :: rest => (a, b) :: docPairwiseLoop b rest

/-- rst:513-521 (`a = next(iterator, None)`). -/
def docPairwise (l : List Int) : Run (Int × Int) :=
  match l with
  | [] => Run.ok []
  | a :: rest => Run.ok (docPairwiseLoop a rest)

/-! ## starmap (:1774-1881; rst:654-657) -/

/-- `starmap_next` (:1840-1860); the argument tuples are lists of ints and
`func` is a pure function of the argument tuple. -/
def cStarmapNext (func : List Int → Int) : List (List Int) → Step (List (List Int)) Int
  | [] => .stop []
  | args :: rest => .yield (func args) rest

def cStarmap (func : List Int → Int) (l : List (List Int)) : Run Int :=
  drain (cStarmapNext func) (l.length + 2) l

def docStarmap (func : List Int → Int) (l : List (List Int)) : Run Int := Run.ok (l.map func)

/-! ## zip_longest (:3859-4079; rst:768-788) -/

structure ZipLongestState where
  its : List (Option (List Int))
  numactive : Nat
  fill : Option Int

/-- The per-iterator loop of `zip_longest_next_lock_held` (both copies of the
loop, :3965-4034): `none` is the "all exhausted" `return NULL`. -/
def cZipLongestRow (fill : Option Int) : List (Option (List Int)) → Nat →
    Option (List (Option Int) × List (Option (List Int)) × Nat)
  | [], numactive => some ([], [], numactive)
  | none :: its, numactive => do
    let (row, its', na) ← cZipLongestRow fill its numactive
    return (fill :: row, none :: its', na)
  | some l :: its, numactive =>
    match pop l with
    | some (x, rest) => do
      let (row, its', na) ← cZipLongestRow fill its numactive
      return (some x :: row, some rest :: its', na)
    | none =>
      let numactive := numactive - 1
      if numactive = 0 then none
      else do
        let (row, its', na) ← cZipLongestRow fill its numactive
        return (fill :: row, none :: its', na)

def cZipLongestNext (s : ZipLongestState) : Step ZipLongestState (List (Option Int)) :=
  if s.its.length = 0 then .stop s
  else if s.numactive = 0 then .stop s
  else match cZipLongestRow s.fill s.its s.numactive with
    | none => .stop { s with numactive := 0 }
    | some (row, its, na) => .yield row { s with its := its, numactive := na }

def cZipLongest (ls : List (List Int)) (fill : Option Int) : Run (List (Option Int)) :=
  drain cZipLongestNext ((ls.map List.length).foldr max 0 + 2)
    { its := ls.map some, numactive := ls.length, fill := fill }

/-- The `for i, iterator in enumerate(iterators)` loop of rst:768-788;
`none` is the `return`. Exhausted iterators are replaced by
`repeat(fillvalue)` (`none` here). -/
def docZipLongestRow (fill : Option Int) : List (Option (List Int)) → Nat →
    Option (List (Option Int) × List (Option (List Int)) × Nat)
  | [], na => some ([], [], na)
  | none :: its, na => do
    let (row, its', na) ← docZipLongestRow fill its na
    return (fill :: row, none :: its', na)
  | some [] :: its, na =>
    let na := na - 1
    if na = 0 then none
    else do
      let (row, its', na) ← docZipLongestRow fill its na
      return (fill :: row, none :: its', na)
  | some (x :: rest) :: its, na => do
    let (row, its', na) ← docZipLongestRow fill its na
    return (some x :: row, some rest :: its', na)

def docZipLongestLoop (fill : Option Int) : Nat → List (Option (List Int)) → Nat → Run (List (Option Int))
  | 0, _, _ => Run.err .modelFuel
  | fuel + 1, its, na =>
    match docZipLongestRow fill its na with
    | none => Run.ok []
    | some (row, its', na') => Run.cons row (docZipLongestLoop fill fuel its' na')

/-- rst:768-788. -/
def docZipLongest (ls : List (List Int)) (fill : Option Int) : Run (List (Option Int)) :=
  if ls.length = 0 then Run.ok []
  else docZipLongestLoop fill ((ls.map List.length).foldr max 0 + 2) (ls.map some) ls.length

end PyLean.Itertools
