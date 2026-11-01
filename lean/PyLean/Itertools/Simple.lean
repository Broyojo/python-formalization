import PyLean.Itertools.Islice

/-!
The non-combinatoric iterators of `Modules/itertoolsmodule.c` (CPython 3.14.7)
and their doc equivalents (`Doc/library/itertools.rst`): `accumulate`,
`batched`, `chain`/`chain.from_iterable`, `compress`, `cycle`, `dropwhile`,
`filterfalse`, `pairwise`, `starmap`, `takewhile`, `zip_longest`.

Everything is generic in the element type. Inputs are `Obj`s (possibly not
iterable, possibly raising after their items). Callbacks may raise: a predicate
`α → Py Bool` stands for `PyObject_IsTrue(func(item))`, so an error from the
call and one from `__bool__` are the same branch. `chain_next`,
`accumulate_next` and `zip_longest_next` only add a critical section around
their `_lock_held` function, so one model mirrors both. A constructor's
`tp_alloc` failure is not modelled.
-/

namespace PyLean.Itertools

open PyLean

variable {α β : Type}

/-! ## accumulate (:3083-3224; rst:102-119) -/

structure AccState (α : Type) where
  it : Src α
  total : Option α
  initial : Option α

/-- `itertools_accumulate_impl` (:3107-3134): `PyObject_GetIter`; the default
`func` is addition, passed as `add` (`PyNumber_Add`). -/
def cAccumulateNew (iterable : Obj α) (initial : Option α) : Py (AccState α) :=
  match getIter iterable with
  | .error e => .error e
  | .ok it => .ok { it := it, total := none, initial := initial }

/-- `accumulate_next_lock_held` (:3163-3193). `binop` is `func`, or addition
for `func=None`. -/
def cAccumulateNext (binop : α → α → Py α) (s : AccState α) : Step (AccState α) α :=
  match s.initial with
  | some t => .yield t { s with total := some t, initial := none }
  | none =>
    match s.it.next with
    | .done => .stop s
    | .fail e it => .raise e { s with it := it }
    | .item val rest =>
      match s.total with
      | none => .yield val { s with it := rest, total := some val }
      | some total =>
        match binop total val with
        | .error e => .raise e { s with it := rest }
        | .ok newtotal => .yield newtotal { s with it := rest, total := some newtotal }

def cAccumulate (binop : α → α → Py α) (initial : Option α) (iterable : Obj α) : Run α :=
  match cAccumulateNew iterable initial with
  | .error e => Run.err e
  | .ok s => drain (cAccumulateNext binop) (iterable.len + 2) s

/-- `for element in iterator: total = function(total, element); yield total`. -/
def docAccumulateLoop (f : α → α → Py α) (err : Option PyExc) : α → List α → Run α
  | _, [] => ([], err)
  | total, x :: xs =>
    match f total x with
    | .error e => Run.err e
    | .ok t => Run.cons t (docAccumulateLoop f err t xs)

/-- rst:102-119. -/
def docAccumulate (f : α → α → Py α) (initial : Option α) (iterable : Obj α) : Run α :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ =>
    match initial with
    | none =>
      match l with
      | [] => ([], err)
      | x :: xs => Run.cons x (docAccumulateLoop f err x xs)
    | some t => Run.cons t (docAccumulateLoop f err t l)

/-! ## batched (:98-271; rst:175-183) -/

structure BatchedState (α : Type) where
  it : Src α
  batchSize : Int
  strict : Bool

/-- `batched_new_impl` (:137-167); `n` went through the `Py_ssize_t` converter. -/
def cBatchedNew (iterable : Obj α) (n : Int) (strict : Bool) : Py (BatchedState α) :=
  match asSsize n with
  | .error e => .error e
  | .ok n =>
    if n < 1 then .error (.valueError "n must be at least one")
    else match getIter iterable with
      | .error e => .error e
      | .ok it => .ok { it := it, batchSize := n, strict := strict }

/-- `batched_next` (:190-249). The `for (i=0; i < n; i++)` loop pulls items
until `n` are read or the input runs out, i.e. takes `min(n, len)` items. -/
def cBatchedNext (s : BatchedState α) : Step (BatchedState α) (List α) :=
  let n := s.batchSize
  if n < 0 then .stop s
  else if !tupleNewOk n then .raise memoryError s
  else
    let batch := s.it.items.take n.toNat
    let rest := s.it.items.drop n.toNat
    if (batch.length : Int) = n then .yield batch { s with it := ⟨rest, s.it.err⟩ }
    else match s.it.err with
      | some e => .raise e { s with it := ⟨[], none⟩, batchSize := -1 }
      | none =>
        if batch.length = 0 then .stop { s with it := ⟨rest, none⟩, batchSize := -1 }
        else if s.strict then
          .raise (.valueError "batched(): incomplete batch") { s with it := ⟨rest, none⟩, batchSize := -1 }
        else .yield batch { s with it := ⟨rest, none⟩ }

def cBatched (iterable : Obj α) (n : Int) (strict : Bool) : Run (List α) :=
  match cBatchedNew iterable n strict with
  | .error e => Run.err e
  | .ok s => drain cBatchedNext (iterable.len + 2) s

/-- The `while batch := tuple(islice(iterator, n))` loop (rst:179-183), with
the C `islice` (whose `stop` must be at most `sys.maxsize`). -/
def docBatchedLoop (n : Int) (strict : Bool) (err : Option PyExc) : Nat → List α → Run (List α)
  | 0, _ => Run.err .modelFuel
  | fuel + 1, it =>
    let (r, consumed) := cIslice (.iter it err) [some n]
    match r with
    | (_, some e) => Run.err e
    | (batch, none) =>
      if batch = [] then Run.ok []
      else if strict && (batch.length : Int) != n then Run.err (.valueError "batched(): incomplete batch")
      else Run.cons batch (docBatchedLoop n strict err fuel (it.drop consumed.toNat))

/-- rst:175-183. -/
def docBatched (iterable : Obj α) (n : Int) (strict : Bool) : Run (List α) :=
  if n < 1 then Run.err (.valueError "n must be at least one")
  else match getIter iterable with
    | .error e => Run.err e
    | .ok ⟨l, err⟩ => docBatchedLoop n strict err (l.length + 2) l

/-! ## chain, chain.from_iterable (:1883-2057; rst:198-201, :209-212) -/

structure ChainState (α : Type) where
  source : Option (Src (Obj α))
  active : Option (Src α)

/-- `chain_new_internal` (:1894-1907). -/
def chainNewInternal (source : Src (Obj α)) : ChainState α := { source := some source, active := none }

/-- `chain_new` (:1910-1925): no keywords; the source is an iterator over `args`. -/
def cChainNew (args : List (Obj α)) (hasKw : Bool) : Py (ChainState α) :=
  if hasKw then .error (.typeError "chain() takes no keyword arguments")
  else .ok (chainNewInternal ⟨args, none⟩)

/-- `itertools_chain_from_iterable_impl` (:1936-1946). -/
def cChainFromIterable (arg : Obj (Obj α)) : Py (ChainState α) :=
  match getIter arg with
  | .error e => .error e
  | .ok source => .ok (chainNewInternal source)

/-- The `while (lz->source != NULL)` loop of `chain_next_lock_held`
(:1971-2007) from "`active` is `NULL`", by recursion on the remaining sources.
A failed pull or `PyObject_GetIter` clears `source`. -/
def cChainPull (serr : Option PyExc) : List (Obj α) → Step (ChainState α) α
  | [] =>
    match serr with
    | none => .stop { source := none, active := none }
    | some e => .raise e { source := none, active := none }
  | iterable :: src =>
    match getIter iterable with
    | .error e => .raise e { source := none, active := none }
    | .ok a =>
      match a.next with
      | .item x a' => .yield x { source := some ⟨src, serr⟩, active := some a' }
      | .fail e a' => .raise e { source := some ⟨src, serr⟩, active := some a' }
      | .done => cChainPull serr src

/-- `chain_next_lock_held` (:1971-2007) and its wrapper `chain_next` (:2010-2017). -/
def cChainNext (s : ChainState α) : Step (ChainState α) α :=
  match s.source with
  | none => .stop s
  | some ⟨src, serr⟩ =>
    match s.active with
    | none => cChainPull serr src
    | some a =>
      match a.next with
      | .item x a' => .yield x { s with active := some a' }
      | .fail e a' => .raise e { s with active := some a' }
      | .done => cChainPull serr src

/-- Total number of items in the sub-iterables. -/
def chainLen (ls : List (Obj α)) : Nat := (ls.map Obj.len).sum

def cChainRun (r : Py (ChainState α)) (fuel : Nat) : Run α :=
  match r with
  | .error e => Run.err e
  | .ok s => drain cChainNext fuel s

def cChain (args : List (Obj α)) : Run α := cChainRun (cChainNew args false) (chainLen args + 2)

/-- `for iterable in iterables: yield from iterable`, with `iterables` ending
as `serr`. -/
def docChainLoop (serr : Option PyExc) : List (Obj α) → Run α
  | [] => ([], serr)
  | iterable :: rest =>
    match getIter iterable with
    | .error e => Run.err e
    | .ok ⟨l, err⟩ =>
      match err with
      | some e => (l, some e)
      | none => Run.prepend l (docChainLoop serr rest)

/-- rst:198-201. -/
def docChain (args : List (Obj α)) : Run α := docChainLoop none args

/-- `list(chain.from_iterable(arg))` in C. -/
def cChainFrom (arg : Obj (Obj α)) : Run α :=
  cChainRun (cChainFromIterable arg)
    (match arg with
     | .iter ls _ => chainLen ls + 2
     | .notIterable _ => 2)

/-- rst:209-212. -/
def docChainFrom (arg : Obj (Obj α)) : Run α :=
  match getIter arg with
  | .error e => Run.err e
  | .ok ⟨ls, serr⟩ => docChainLoop serr ls

/-! ## compress (:3226-3360; rst:306-308) -/

/-- `itertools_compress_impl` (:3255-3280). -/
def cCompressNew (data : Obj α) (selectors : Obj β) : Py (Src α × Src β) :=
  match getIter data with
  | .error e => .error e
  | .ok d =>
    match getIter selectors with
    | .error e => .error e
    | .ok s => .ok (d, s)

/-- The `while (1)` loop of `compress_next` (:3305-3339): pull a datum, pull a
selector, evaluate the selector (`truth` is `PyObject_IsTrue`). -/
def cCompressLoop (truth : β → Py Bool) (derr : Option PyExc) :
    List α → Src β → Step (Src α × Src β) α
  | [], sel =>
    match derr with
    | none => .stop (⟨[], none⟩, sel)
    | some e => .raise e (⟨[], none⟩, sel)
  | x :: d, sel =>
    match sel.next with
    | .done => .stop (⟨d, derr⟩, sel)
    | .fail e sel' => .raise e (⟨d, derr⟩, sel')
    | .item y sel' =>
      match truth y with
      | .error e => .raise e (⟨d, derr⟩, sel')
      | .ok true => .yield x (⟨d, derr⟩, sel')
      | .ok false => cCompressLoop truth derr d sel'

def cCompressNext (truth : β → Py Bool) (s : Src α × Src β) : Step (Src α × Src β) α :=
  cCompressLoop truth s.1.err s.1.items s.2

def cCompress (truth : β → Py Bool) (data : Obj α) (selectors : Obj β) : Run α :=
  match cCompressNew data selectors with
  | .error e => Run.err e
  | .ok s => drain (cCompressNext truth) (data.len + 2) s

/-- `(datum for datum, selector in zip(data, selectors) if selector)`. -/
def docCompressLoop (truth : β → Py Bool) (derr : Option PyExc) : List α → Src β → Run α
  | [], _ => ([], derr)
  | x :: d, sel =>
    match sel.next with
    | .done => Run.ok []
    | .fail e _ => Run.err e
    | .item y sel' =>
      match truth y with
      | .error e => Run.err e
      | .ok true => Run.cons x (docCompressLoop truth derr d sel')
      | .ok false => docCompressLoop truth derr d sel'

def docCompress (truth : β → Py Bool) (data : Obj α) (selectors : Obj β) : Run α :=
  match getIter data with
  | .error e => Run.err e
  | .ok ⟨d, derr⟩ =>
    match getIter selectors with
    | .error e => Run.err e
    | .ok sel => docCompressLoop truth derr d sel

/-! ## cycle (:1207-1338; rst:342-352) -/

structure CycleState (α : Type) where
  it : Option (Src α)
  saved : List α
  index : Int

/-- `itertools_cycle_impl` (:1227-1257). -/
def cCycleNew (iterable : Obj α) : Py (CycleState α) :=
  match getIter iterable with
  | .error e => .error e
  | .ok it => .ok { it := some it, saved := [], index := -1 }

/-- The part of `cycle_next` after the first pass (:1302-1316). -/
def cCycleSaved [Inhabited α] (s : CycleState α) : Step (CycleState α) α :=
  if s.saved.length = 0 then .stop s
  else
    let item := s.saved.getD s.index.toNat default
    let index := s.index + 1
    let index := if index ≥ s.saved.length then 0 else index
    .yield item { s with index := index }

/-- `cycle_next` (:1282-1317). -/
def cCycleNext [Inhabited α] (s : CycleState α) : Step (CycleState α) α :=
  if s.index < 0 then
    match s.it with
    | none => cCycleSaved { s with index := 0, it := none }
    | some src =>
      match src.next with
      | .item item rest => .yield item { s with it := some rest, saved := s.saved ++ [item] }
      | .fail e rest => .raise e { s with it := some rest }
      | .done => cCycleSaved { s with index := 0, it := none }
  else cCycleSaved s

/-- The first `k` items of `cycle(iterable)`. -/
def cCycle [Inhabited α] (iterable : Obj α) (k : Nat) : Run α :=
  match cCycleNew iterable with
  | .error e => Run.err e
  | .ok s => takeN cCycleNext k s

/-- `while saved: for element in saved: yield element`, first `k` items; the
list argument is what remains of the current `for` pass. -/
def docCycleSaved (saved : List α) : Nat → List α → List α
  | 0, _ => []
  | k + 1, x :: xs => x :: docCycleSaved saved k xs
  | k + 1, [] =>
    match saved with
    | [] => []
    | y :: ys => y :: docCycleSaved saved k ys

/-- rst:342-352: the first pass (`yield element; saved.append(element)`), then
the saved copy forever; the first `k` items. Generators are lazy, so a bad
argument surfaces at the first `next()`; the driver below uses `k >= 1` for it. -/
def docCycle (iterable : Obj α) (k : Nat) : Run α :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ =>
    let first := l.take k
    if k ≤ l.length then Run.ok first
    else match err with
      | some e => (first, some e)
      | none => Run.ok (first ++ docCycleSaved l (k - first.length) [])

/-! ## dropwhile, takewhile, filterfalse (:1340-1578, :3362-3482) -/

/-- The constructors share one shape: `PyObject_GetIter(seq)`, then the flag
(`itertools_dropwhile_impl`, :1363-1385; `itertools_takewhile_impl`,
:1485-1507; `itertools_filterfalse_impl`, :3384-3405; `itertools_starmap_impl`,
:1794-1815). -/
def cIterNew (iterable : Obj α) : Py (Src α) := getIter iterable

/-- `dropwhile_next` (:1410-1441); the flag is `lz->start`. -/
def cDropwhileNext (pred : α → Py Bool) : Src α × Bool → Step (Src α × Bool) α
  | (⟨[], err⟩, start) =>
    match err with
    | none => .stop (⟨[], none⟩, start)
    | some e => .raise e (⟨[], none⟩, start)
  | (⟨x :: xs, err⟩, true) => .yield x (⟨xs, err⟩, true)
  | (⟨x :: xs, err⟩, false) =>
    match pred x with
    | .error e => .raise e (⟨xs, err⟩, false)
    | .ok true => cDropwhileNext pred (⟨xs, err⟩, false)
    | .ok false => .yield x (⟨xs, err⟩, true)

def cDropwhile (pred : α → Py Bool) (iterable : Obj α) : Run α :=
  match cIterNew iterable with
  | .error e => Run.err e
  | .ok s => drain (cDropwhileNext pred) (iterable.len + 2) (s, false)

/-- rst:364-374. -/
def docDropwhile (pred : α → Py Bool) (iterable : Obj α) : Run α :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ => go err l
where
  go (err : Option PyExc) : List α → Run α
    | [] => ([], err)
    | x :: xs =>
      match pred x with
      | .error e => Run.err e
      | .ok false => (x :: xs, err)
      | .ok true => go err xs

/-- `takewhile_next` (:1532-1559); the flag is `lz->stop`. -/
def cTakewhileNext (pred : α → Py Bool) : Src α × Bool → Step (Src α × Bool) α
  | (s, true) => .stop (s, true)
  | (s, false) =>
    match s.next with
    | .done => .stop (s, false)
    | .fail e rest => .raise e (rest, false)
    | .item x rest =>
      match pred x with
      | .error e => .raise e (rest, false)
      | .ok true => .yield x (rest, false)
      | .ok false => .stop (rest, true)

def cTakewhile (pred : α → Py Bool) (iterable : Obj α) : Run α :=
  match cIterNew iterable with
  | .error e => Run.err e
  | .ok s => drain (cTakewhileNext pred) (iterable.len + 2) (s, false)

/-- rst:665-670. -/
def docTakewhile (pred : α → Py Bool) (iterable : Obj α) : Run α :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ => go err l
where
  go (err : Option PyExc) : List α → Run α
    | [] => ([], err)
    | x :: xs =>
      match pred x with
      | .error e => Run.err e
      | .ok false => Run.ok []
      | .ok true => Run.cons x (go err xs)

/-- The truth test of `filterfalse_next`: `PyObject_IsTrue(item)` (`truth`) for
`None` or `bool`, else `PyObject_IsTrue(func(item))`. -/
def ffTest (truth : α → Py Bool) (pred : Option (α → Py Bool)) (x : α) : Py Bool :=
  match pred with
  | none => truth x
  | some f => f x

/-- `filterfalse_next` (:3430-3462). -/
def cFilterfalseNext (truth : α → Py Bool) (pred : Option (α → Py Bool)) : Src α → Step (Src α) α
  | ⟨[], err⟩ =>
    match err with
    | none => .stop ⟨[], none⟩
    | some e => .raise e ⟨[], none⟩
  | ⟨x :: xs, err⟩ =>
    match ffTest truth pred x with
    | .error e => .raise e ⟨xs, err⟩
    | .ok false => .yield x ⟨xs, err⟩
    | .ok true => cFilterfalseNext truth pred ⟨xs, err⟩

def cFilterfalse (truth : α → Py Bool) (pred : Option (α → Py Bool)) (iterable : Obj α) : Run α :=
  match cIterNew iterable with
  | .error e => Run.err e
  | .ok s => drain (cFilterfalseNext truth pred) (iterable.len + 2) s

/-- rst:387-395: `predicate = bool` for `None`. -/
def docFilterfalse (truth : α → Py Bool) (pred : Option (α → Py Bool)) (iterable : Obj α) : Run α :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ => go (pred.getD truth) err l
where
  go (p : α → Py Bool) (err : Option PyExc) : List α → Run α
    | [] => ([], err)
    | x :: xs =>
      match p x with
      | .error e => Run.err e
      | .ok false => Run.cons x (go p err xs)
      | .ok true => go p err xs

/-! ## pairwise (:273-424; rst:513-521) -/

structure PairwiseState (α : Type) where
  it : Option (Src α)
  old : Option α

/-- `pairwise_new_impl` (:296-319). -/
def cPairwiseNew (iterable : Obj α) : Py (PairwiseState α) :=
  match getIter iterable with
  | .error e => .error e
  | .ok it => .ok { it := some it, old := none }

/-- The second half of `pairwise_next`: pull `new`. -/
def cPairwiseNew2 (old : α) (s : Src α) : Step (PairwiseState α) (α × α) :=
  match s.next with
  | .done => .stop { it := none, old := none }
  | .fail e _ => .raise e { it := none, old := none }
  | .item new rest => .yield (old, new) { it := some rest, old := some new }

/-- `pairwise_next` (:346-402); a failed pull clears `it` and `old`. -/
def cPairwiseNext (s : PairwiseState α) : Step (PairwiseState α) (α × α) :=
  match s.it with
  | none => .stop s
  | some src =>
    match s.old with
    | some old => cPairwiseNew2 old src
    | none =>
      match src.next with
      | .done => .stop { it := none, old := none }
      | .fail e _ => .raise e { it := none, old := none }
      | .item old rest => cPairwiseNew2 old rest

def cPairwise (iterable : Obj α) : Run (α × α) :=
  match cPairwiseNew iterable with
  | .error e => Run.err e
  | .ok s => drain cPairwiseNext (iterable.len + 2) s

/-- `for b in iterator: yield a, b; a = b`. -/
def docPairwiseLoop (err : Option PyExc) : α → List α → Run (α × α)
  | _, [] => ([], err)
  | a, b :: rest => Run.cons (a, b) (docPairwiseLoop err b rest)

/-- rst:513-521 (`a = next(iterator, None)`). -/
def docPairwise (iterable : Obj α) : Run (α × α) :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ =>
    match l with
    | [] => ([], err)
    | a :: rest => docPairwiseLoop err a rest

/-! ## starmap (:1774-1881; rst:654-657) -/

/-- `starmap_next` (:1840-1860): each input item is an argument object;
`PySequence_Tuple` unless it is a tuple, then the call. -/
def cStarmapNext (func : List α → Py β) (s : Src (Obj α)) : Step (Src (Obj α)) β :=
  match s.next with
  | .done => .stop s
  | .fail e rest => .raise e rest
  | .item args rest =>
    match tupleOf args with
    | .error e => .raise e rest
    | .ok a =>
      match func a with
      | .error e => .raise e rest
      | .ok r => .yield r rest

def cStarmap (func : List α → Py β) (iterable : Obj (Obj α)) : Run β :=
  match cIterNew iterable with
  | .error e => Run.err e
  | .ok s => drain (cStarmapNext func) (iterable.len + 2) s

/-- `function(*args)` in rst:654-657. The call's own `TypeError` for a
non-iterable `args` names the function, so the message is not compared. -/
def docStarArgs : Obj α → Py (List α)
  | .notIterable _ => .error (.typeError "~argument after * must be an iterable")
  | o => tupleOf o

def docStarmapLoop (func : List α → Py β) (err : Option PyExc) : List (Obj α) → Run β
  | [] => ([], err)
  | args :: rest =>
    match docStarArgs args with
    | .error e => Run.err e
    | .ok a =>
      match func a with
      | .error e => Run.err e
      | .ok r => Run.cons r (docStarmapLoop func err rest)

def docStarmap (func : List α → Py β) (iterable : Obj (Obj α)) : Run β :=
  match getIter iterable with
  | .error e => Run.err e
  | .ok ⟨l, err⟩ => docStarmapLoop func err l

/-! ## zip_longest (:3859-4079; rst:768-788) -/

structure ZipLongestState (α : Type) where
  its : List (Option (Src α))
  numactive : Nat
  fill : Option α

/-- Result of one pass over the iterators. -/
inductive RowRes (α : Type) where
  | row (r : List (Option α)) (its : List (Option (Src α))) (na : Nat)
  | stop
  | raise (e : PyExc)

/-- Prepend to the row a recursive pass produced. -/
def RowRes.cons (v : Option α) (it : Option (Src α)) : RowRes α → RowRes α
  | .row r its na => .row (v :: r) (it :: its) na
  | r => r

/-- `kwds`: `fillvalue` alone, or `TypeError` (:3882-3893). -/
def zipFill (kw : List (String × Option α)) : Py (Option α) :=
  match kw with
  | [] => .ok none
  | [("fillvalue", v)] => .ok v
  | _ => .error (.typeError "zip_longest() got an unexpected keyword argument")

/-- `zip_longest_new` (:3873-3938). -/
def cZipLongestNew (args : List (Obj α)) (kw : List (String × Option α)) : Py (ZipLongestState α) :=
  match zipFill kw with
  | .error e => .error e
  | .ok fill =>
    match args.mapM getIter with
    | .error e => .error e
    | .ok its => .ok { its := its.map some, numactive := args.length, fill := fill }

/-- The per-iterator loop of `zip_longest_next_lock_held` (both copies of the
loop, :3965-4034): `stop` is the "all exhausted" `return NULL`, `raise` the
"`PyErr_Occurred()`" one. -/
def cZipLongestRow (fill : Option α) : List (Option (Src α)) → Nat → RowRes α
  | [], numactive => .row [] [] numactive
  | none :: its, numactive => (cZipLongestRow fill its numactive).cons fill none
  | some s :: its, numactive =>
    match s.next with
    | .item x rest => (cZipLongestRow fill its numactive).cons (some x) (some rest)
    | .fail e _ => .raise e
    | .done =>
      let numactive := numactive - 1
      if numactive = 0 then .stop
      else (cZipLongestRow fill its numactive).cons fill none

/-- `zip_longest_next_lock_held` and its wrapper `zip_longest_next` (:4037-4044). -/
def cZipLongestNext (s : ZipLongestState α) : Step (ZipLongestState α) (List (Option α)) :=
  if s.its.length = 0 then .stop s
  else if s.numactive = 0 then .stop s
  else match cZipLongestRow s.fill s.its s.numactive with
    | .stop => .stop { s with numactive := 0 }
    | .raise e => .raise e { s with numactive := 0 }
    | .row row its na => .yield row { s with its := its, numactive := na }

def zipFuel (args : List (Obj α)) : Nat := (args.map Obj.len).foldr max 0 + 2

def cZipLongest (args : List (Obj α)) (kw : List (String × Option α)) : Run (List (Option α)) :=
  match cZipLongestNew args kw with
  | .error e => Run.err e
  | .ok s => drain cZipLongestNext (zipFuel args) s

/-- The `for i, iterator in enumerate(iterators)` loop of rst:768-788;
exhausted iterators are replaced by `repeat(fillvalue)` (`none` here). -/
def docZipLongestRow (fill : Option α) : List (Option (Src α)) → Nat → RowRes α
  | [], na => .row [] [] na
  | none :: its, na => (docZipLongestRow fill its na).cons fill none
  | some ⟨[], some e⟩ :: _, _ => .raise e
  | some ⟨[], none⟩ :: its, na =>
    let na := na - 1
    if na = 0 then .stop
    else (docZipLongestRow fill its na).cons fill none
  | some ⟨x :: rest, e⟩ :: its, na =>
    (docZipLongestRow fill its na).cons (some x) (some ⟨rest, e⟩)

def docZipLongestLoop (fill : Option α) : Nat → List (Option (Src α)) → Nat → Run (List (Option α))
  | 0, _, _ => Run.err .modelFuel
  | fuel + 1, its, na =>
    match docZipLongestRow fill its na with
    | .stop => Run.ok []
    | .raise e => Run.err e
    | .row row its' na' => Run.cons row (docZipLongestLoop fill fuel its' na')

/-- rst:768-788. -/
def docZipLongest (args : List (Obj α)) (fill : Option α) : Run (List (Option α)) :=
  match args.mapM getIter with
  | .error e => Run.err e
  | .ok its =>
    if args.length = 0 then Run.ok []
    else docZipLongestLoop fill (zipFuel args) (its.map some) args.length

end PyLean.Itertools
