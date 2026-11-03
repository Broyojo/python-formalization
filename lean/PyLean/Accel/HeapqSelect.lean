import PyLean.Accel.HeapqModel

/-!
# `heapq.nsmallest`, `heapq.nlargest` and `heapq.merge` with fallible callbacks

Model of `Lib/heapq.py:330-593` (CPython 3.15.2) in which every piece of user code is Python
code over a world `W` that may raise or change the world:

* elements `α` are objects by identity (`DecidableEq α` is `is`); `E.lt a b` is `a < b` with
  the truth test of its result, `E.gt a b` is `a > b` (only `max()` uses it), `E.eq a b` is
  `a == b` with its truth test, called only when `a is not b` (`PyObject_RichCompareBool`'s
  identity shortcut for `Py_EQ`);
* iterables and iterators are objects `O`: `E.iter x` is `iter(x)` (`__iter__`, fallible, and
  free to return any iterator), `E.next it` is `next(it)` (the type's `__next__`; an exception
  that is a `StopIteration` under the class relation `E.hier` ends the iteration, as
  `PyIter_Next`, `FOR_ITER` and `zip` test it with `PyErr_ExceptionMatches`), `E.len x` is
  `len(x)`;
* `key` is `None` or a callable `α → Eff W PyExc α`;
* `E.toList x` is `list(x)` (`list_extend`, Objects/listobject.c, with its own length-hint and
  iteration protocol) and `So.sort lt reverse l` is `list.sort` (`list_sort_impl`,
  Objects/listobject.c:2965) with comparison `lt`. Both are callees in another file and are
  parameters here; the theorems state what they assume of them (`SortOk`).

The decorated tuples `(elem, order)`, `(key, order, elem)` and the `merge` entries
`[value, order, next]` / `[key, order, value, next]` compare as tuples and lists do
(Objects/tupleobject.c `tuplerichcompare`, Objects/listobject.c `list_richcompare`, and
`unsafe_tuple_compare` in `list.sort`): the first position whose items are not `==` (identity
first) decides, through `<` on those items. The `order` ints are pairwise distinct in every
list the source builds, so positions after `order` are never reached; the model marks that
branch `unreachableTie`.

`heapify`, `heapreplace`, `heappop` (and `_max`) are the module globals, so the C functions when
`_heapq` is present (`impl = true`) and the Python ones otherwise; both are the models of
`HeapqModel.lean` on the local list, which no user code can reach.

`merge` is a generator: `mergeStep` runs one `next()` of it, from one suspension point to the
next. `next.__self__` is the callback `E.selfOf`. Not modelled: re-entering the generator from a
callback while it runs (genobject.c raises `ValueError('generator already executing')`), an
`it.__next__` attribute that is not the iterator's own `__next__` (calling the stored `next` is
taken to be `next(it)`), `n` that is not an int, and `MemoryError`.
-/

namespace PyLean.Accel.Heapq

open PyLean

/-! ### Exceptions classes -/

/-- The exception class relation (`PyType_IsSubtype` on the raised class): a parameter, as
user classes may define any MRO. -/
structure Hier where
  sub : String → String → Bool

/-- The builtin classes the module meets, with their bases. -/
def builtinBase : String → Option String
  | "Exception" => some "BaseException"
  | "StopIteration" => some "Exception"
  | "TypeError" => some "Exception"
  | "AttributeError" => some "Exception"
  | "ValueError" => some "Exception"
  | "RuntimeError" => some "Exception"
  | "LookupError" => some "Exception"
  | "IndexError" => some "LookupError"
  | _ => none

def builtinIsA : Nat → String → String → Bool
  | 0, _, _ => false
  | fuel + 1, c, b => c == b || (match builtinBase c with
    | some p => builtinIsA fuel p b
    | none => false)

def isBuiltin (c : String) : Bool := (builtinBase c).isSome || c == "BaseException"

/-- What CPython fixes of the relation: the builtin classes' own ancestors; anything else (a
user class and its `mro()`) is unconstrained. -/
def HierOk (H : Hier) : Prop := ∀ c b, isBuiltin c = true → H.sub c b = builtinIsA 5 c b

def builtinHier : Hier := ⟨builtinIsA 5⟩

theorem builtinHier_ok : HierOk builtinHier := fun _ _ _ => rfl

def isA (H : Hier) (e : PyExc) (base : String) : Bool := H.sub e.className base

/-! ### Environment -/

/-- The user code the three functions call. -/
structure SEnv (W α O : Type) where
  lt : α → α → Eff W PyExc Bool
  gt : α → α → Eff W PyExc Bool
  eq : α → α → Eff W PyExc Bool
  iter : O → Eff W PyExc O
  next : O → Eff W PyExc α
  len : O → Eff W PyExc Nat
  toList : O → Eff W PyExc (List α)
  /-- `next.__self__` for the `next = it.__next__` that `merge` stored from iterator `it`
  (Lib/heapq.py:383, :408): `it` for a bound method; an `AttributeError` when `__next__` is,
  e.g., a staticmethod (a plain function has no `__self__`). -/
  selfOf : O → Eff W PyExc O
  hier : Hier

/-- `list.sort(reverse=...)` with a given item comparison. -/
structure Sorter (W : Type) where
  sort : {β : Type} → (β → β → Eff W PyExc Bool) → Bool → List β → Eff W PyExc (List β)

variable {W α O : Type} [DecidableEq α] [Inhabited α]

/-- Run `m`, returning its exception as a value. -/
def Eff.attempt {ε β : Type} (m : Eff W ε β) : Eff W ε (Except ε β) :=
  ⟨fun w => ((.ok (m.run w).1), (m.run w).2)⟩

/-- The comparison of two tuple or list positions past `order`, which no list the source
builds reaches (its `order` ints are pairwise distinct). -/
def unreachableTie {β : Type} : Eff W PyExc β :=
  Eff.raise (.named "TypeError" "~unreachable: decorated orders are distinct")

/-- `(a, oa) < (b, ob)`: `tuplerichcompare` (Objects/tupleobject.c) and
`unsafe_tuple_compare` (Objects/listobject.c:2905-2935): `a == b` (identity first) decides
whether `a < b` or the orders do. -/
def lt2 (E : SEnv W α O) (x y : α × Int) : Eff W PyExc Bool :=
  let byOrder : Eff W PyExc Bool := if x.2 = y.2 then pure false else pure (decide (x.2 < y.2))
  if x.1 = y.1 then byOrder
  else do
    let e ← E.eq x.1 y.1
    if e then byOrder else E.lt x.1 y.1

/-- `(k, o, e) < (k', o', e')`, likewise; the third items decide only on equal orders, by `==`
(identity first) and then `<`, and equal tuples are not `<`. -/
def lt3 (E : SEnv W α O) (x y : α × Int × α) : Eff W PyExc Bool :=
  let byElem : Eff W PyExc Bool :=
    if x.2.2 = y.2.2 then pure false
    else do
      let e ← E.eq x.2.2 y.2.2
      if e then pure false else E.lt x.2.2 y.2.2
  let byOrder : Eff W PyExc Bool := if x.2.1 = y.2.1 then byElem else pure (decide (x.2.1 < y.2.1))
  if x.1 = y.1 then byOrder
  else do
    let e ← E.eq x.1 y.1
    if e then byOrder else E.lt x.1 y.1

/-! ### The heap functions on a local list -/

/-- A comparison on the local list's items that runs on the outer world only. -/
def liftCmp {β : Type} (cmp : β → β → Eff W PyExc Bool) : Cmp W β :=
  ofSt fun a b s => (cmp a b).run s

def cToPy {γ : Type} : Except CErr γ → Except PyExc γ
  | .ok g => .ok g
  | .error (.py e) => .error e
  | .error (.crash s) => .error (.named "SystemError" s!"~model crash {s}")

/-- Run a heap function on the local list `l`; the outcome and the list it leaves. -/
def onList {β γ : Type} (l : List β) (m : Eff (HW W β) PyExc γ) : Eff W PyExc (Except PyExc γ × List β) :=
  ⟨fun w => ((.ok ((m.run ⟨w, l⟩).1, (m.run ⟨w, l⟩).2.heap)), (m.run ⟨w, l⟩).2.st)⟩

def onListC {β γ : Type} (l : List β) (m : CM W β γ) : Eff W PyExc (Except PyExc γ × List β) :=
  ⟨fun w => ((.ok (cToPy (m.run ⟨w, l⟩).1, (m.run ⟨w, l⟩).2.heap)), (m.run ⟨w, l⟩).2.st)⟩

/-- Re-raise the heap function's exception, else return its value and list. -/
def reraise {β γ : Type} (r : Except PyExc γ × List β) : Eff W PyExc (γ × List β) :=
  match r.1 with
  | .ok g => pure (g, r.2)
  | .error e => Eff.raise e

/-- `heapify(l)` / `heapify_max(l)`: C (`impl`) or Python. -/
def hHeapify {β : Type} [Inhabited β] (impl mx : Bool) (cmp : β → β → Eff W PyExc Bool)
    (l : List β) : Eff W PyExc (Except PyExc Unit × List β) :=
  if impl then onListC l (cHeapify mx (liftCmp cmp) ⟨true, "list"⟩)
  else onList l (pyHeapify listSeq (liftCmp cmp) mx)

/-- `heapreplace(l, item)` / `heapreplace_max`. -/
def hHeapreplace {β : Type} [Inhabited β] (impl mx : Bool) (cmp : β → β → Eff W PyExc Bool)
    (l : List β) (item : β) : Eff W PyExc (Except PyExc β × List β) :=
  if impl then onListC l (cHeapreplace mx (liftCmp cmp) ⟨true, "list"⟩ item)
  else onList l (pyHeapreplace listSeq (liftCmp cmp) mx item)

/-- `heappop(l)` / `heappop_max`. -/
def hHeappop {β : Type} [Inhabited β] (impl mx : Bool) (cmp : β → β → Eff W PyExc Bool)
    (l : List β) : Eff W PyExc (Except PyExc β × List β) :=
  if impl then onListC l (cHeappop mx (liftCmp cmp) ⟨true, "list"⟩)
  else onList l (pyHeappop listSeq (liftCmp cmp) mx)

/-! ### Builtins the selection functions call -/

/-- `next(it)` as `PyIter_Next` / `FOR_ITER` / `zip` see it: `none` at a `StopIteration`. -/
def nextOpt (E : SEnv W α O) (it : O) : Eff W PyExc (Option α) := do
  let r ← Eff.attempt (E.next it)
  match r with
  | .ok x => pure (some x)
  | .error e => if isA E.hier e "StopIteration" then pure none else Eff.raise e

/-- Apply the key (`key is None`: the item itself). -/
def applyK (key : Option (α → Eff W PyExc α)) (x : α) : Eff W PyExc α :=
  match key with
  | none => pure x
  | some k => k x

/-- `val < maxval` (`min`) or `val > maxval` (`max`), Python/bltinmodule.c:2123. -/
def cmpBest (E : SEnv W α O) (isMax : Bool) (val best : α) : Eff W PyExc Bool :=
  if isMax then E.gt val best else E.lt val best

/-- The loop of `min_max`, Python/bltinmodule.c:2087-2137: `val < maxval` for `min`,
`val > maxval` for `max` (:2123), replacing on a true answer. -/
def minMaxLoop (E : SEnv W α O) (isMax : Bool) (key : Option (α → Eff W PyExc α)) (it : O) :
    Nat → Option (α × α) → Eff W PyExc (Option α)
  | 0, _ => Eff.raise .modelFuel
  | fuel + 1, best => do
    let item ← nextOpt E it                                     -- :2096-2102
    match item with
    | none => pure (best.map (·.1))                             -- :2138-2150
    | some item => do
      let val ← applyK key item                                 -- :2106-2114
      match best with
      | none => minMaxLoop E isMax key it fuel (some (item, val))  -- :2117-2120
      | some (bi, bv) => do
        let cmp ← cmpBest E isMax val bv                        -- :2123
        if cmp then minMaxLoop E isMax key it fuel (some (item, val))
        else minMaxLoop E isMax key it fuel (some (bi, bv))

/-- `min(it, default=sentinel, key=key)` / `max(...)`, Python/bltinmodule.c:2046-2161, called
with one positional argument: `PyObject_GetIter(it)` (:2075), then the loop. -/
def minMax (E : SEnv W α O) (isMax : Bool) (key : Option (α → Eff W PyExc α)) (fuel : Nat)
    (it : O) : Eff W PyExc (Option α) := do
  let it ← E.iter it
  minMaxLoop E isMax key it fuel none

/-- `[f(x) for x in l]`, in order, stopping at the first exception. -/
def effMap {β γ : Type} (f : β → Eff W PyExc γ) : List β → Eff W PyExc (List γ)
  | [] => pure []
  | x :: xs => do
    let y ← f x
    let ys ← effMap f xs
    pure (y :: ys)

/-- `sorted(iterable, key=key, reverse=rev)`: `list(iterable)`, then `list.sort`, which calls
the key once per item in order (Objects/listobject.c:3013-3022) and compares keys with `<`. -/
def pySortedBy (E : SEnv W α O) (So : Sorter W) (key : Option (α → Eff W PyExc α)) (rev : Bool)
    (iterable : O) : Eff W PyExc (List α) := do
  let l ← E.toList iterable
  match key with
  | none => So.sort E.lt rev l
  | some k => do
    let ks ← effMap k l
    let s ← So.sort (fun a b => E.lt a.1 b.1) rev (ks.zip l)
    pure (s.map (·.2))

/-- `zip(range(n), it)` (or `zip(range(0, -n, -1), it)`), driven by a comprehension: `range`
is pulled first, so `it` is not touched once `n` items are taken. -/
def takeN (E : SEnv W α O) (it : O) : Nat → Eff W PyExc (List α)
  | 0 => pure []
  | n + 1 => do
    let x ← nextOpt E it
    match x with
    | none => pure []
    | some x => do
      let rest ← takeN E it n
      pure (x :: rest)

/-- The general branch's comprehension `[(key(elem), i, elem) for i, elem in zip(...)]`: each
item's key is computed right after it is pulled. -/
def takeNKey (E : SEnv W α O) (key : α → Eff W PyExc α) (it : O) : Nat → Eff W PyExc (List (α × α))
  | 0 => pure []
  | n + 1 => do
    let x ← nextOpt E it
    match x with
    | none => pure []
    | some x => do
      let k ← key x
      let rest ← takeNKey E key it n
      pure ((k, x) :: rest)

/-! ### nsmallest, Lib/heapq.py:477-535, and nlargest, :537-593 -/

/-- The loop's test: `elem < top` (`nsmallest`, :512 / :530) or `top < elem` (`nlargest`,
:570 / :588). -/
def cmpTop (E : SEnv W α O) (large : Bool) (top elem : α) : Eff W PyExc Bool :=
  if large then E.lt top elem else E.lt elem top

/-- The `for elem in it` loop of the `key is None` branch: `nsmallest` :511-515
(`elem < top`, `heapreplace_max`, `order += 1`), `nlargest` :569-573 (`top < elem`,
`heapreplace`, `order -= 1`). -/
def selLoop2 (E : SEnv W α O) (impl large : Bool) (it : O) :
    Nat → List (α × Int) → α → Int → Eff W PyExc (List (α × Int))
  | 0, _, _, _ => Eff.raise .modelFuel
  | fuel + 1, result, top, order => do
    let elem ← nextOpt E it
    match elem with
    | none => pure result
    | some elem => do
      let c ← cmpTop E large top elem
      if c then do
        let (_, result) ← reraise (← hHeapreplace impl (!large) (lt2 E) result (elem, order))
        let top := (at! result 0).1
        selLoop2 E impl large it fuel result top (if large then order - 1 else order + 1)
      else selLoop2 E impl large it fuel result top order

/-- The `for elem in it` loop of the general branch: `nsmallest` :528-533, `nlargest`
:586-591. -/
def selLoop3 (E : SEnv W α O) (impl large : Bool) (key : α → Eff W PyExc α) (it : O) :
    Nat → List (α × Int × α) → α → Int → Eff W PyExc (List (α × Int × α))
  | 0, _, _, _ => Eff.raise .modelFuel
  | fuel + 1, result, top, order => do
    let elem ← nextOpt E it
    match elem with
    | none => pure result
    | some elem => do
      let k ← key elem
      let c ← cmpTop E large top k
      if c then do
        let (_, result) ← reraise (← hHeapreplace impl (!large) (lt3 E) result (k, order, elem))
        let top := (at! result 0).1
        selLoop3 E impl large key it fuel result top (if large then order - 1 else order + 1)
      else selLoop3 E impl large key it fuel result top order

/-- The heap path of `nsmallest` (`large = false`, :499-535) and `nlargest` (`large = true`,
:559-593): `it = iter(iterable)`; the comprehension over `zip(range(n), it)` (or
`range(0, -n, -1)`), whose `zip` calls `iter(it)`; `heapify_max` (`heapify`); the loop, whose
`for` calls `iter(it)` again; `result.sort()` (`reverse=True`); undecorate. -/
def selHeap (E : SEnv W α O) (So : Sorter W) (impl large : Bool) (fuel : Nat) (n : Int)
    (iterable : O) (key : Option (α → Eff W PyExc α)) : Eff W PyExc (List α) := do
  let it ← E.iter iterable                                      -- :501 / :520 / :561 / :578
  match key with
  | none => do
    let itz ← E.iter it                                         -- zip(range(n), it)
    let firsts ← takeN E itz n.toNat                            -- :504 / :562
    let result := firsts.zipIdx.map (fun (e, i) => (e, if large then -(i : Int) else (i : Int)))
    if result.isEmpty then pure []                              -- :505-506 / :563-564
    else do
      let ((), result) ← reraise (← hHeapify impl (!large) (lt2 E) result)  -- :507 / :565
      let top := (at! result 0).1                               -- :508 / :566
      let itf ← E.iter it                                       -- `for elem in it`
      let result ← selLoop2 E impl large itf fuel result top (if large then -n else n)
      let result ← So.sort (lt2 E) large result                 -- :516 / :574
      pure (result.map (·.1))                                   -- :517 / :575
  | some f => do
    let itz ← E.iter it
    let firsts ← takeNKey E f itz n.toNat                       -- :521 / :579
    let result := firsts.zipIdx.map
      (fun ((k, e), i) => (k, (if large then -(i : Int) else (i : Int)), e))
    if result.isEmpty then pure []                              -- :522-523 / :580-581
    else do
      let ((), result) ← reraise (← hHeapify impl (!large) (lt3 E) result)  -- :524 / :582
      let top := (at! result 0).1                               -- :525 / :583
      let itf ← E.iter it
      let result ← selLoop3 E impl large f itf fuel result top (if large then -n else n)
      let result ← So.sort (lt3 E) large result                 -- :534 / :592
      pure (result.map (·.2.2))                                 -- :535 / :593

/-- `nsmallest(n, iterable, key)` (`large = false`, Lib/heapq.py:477-535) and
`nlargest` (`large = true`, :537-593). -/
def nSelect (E : SEnv W α O) (So : Sorter W) (impl large : Bool) (fuel : Nat) (n : Int)
    (iterable : O) (key : Option (α → Eff W PyExc α)) : Eff W PyExc (List α) :=
  if n = 1 then do                                              -- :484 / :544
    let it ← E.iter iterable                                    -- :485 / :545
    let r ← minMax E large key fuel it                          -- :486-487 / :546-547
    pure r.toList                                               -- :488 / :548
  else do
    let size ← Eff.attempt (E.len iterable)                     -- :491-492 / :551-552
    match size with
    | .error e =>
      if isA E.hier e "TypeError" || isA E.hier e "AttributeError" then  -- :493-494 / :553-554
        selHeap E So impl large fuel n iterable key
      else Eff.raise e
    | .ok size =>
      if n ≥ size then pySortedBy E So key large iterable       -- :496-497 / :556-557
      else selHeap E So impl large fuel n iterable key

/-! ### merge, Lib/heapq.py:330-408 -/

/-- A heap entry: `[value, order, next]` (:366) or `[key(value), order, value, next]` (:390);
`kv` is the first item (the value itself without a key) and `nxt` the iterator whose bound
`__next__` is stored. -/
structure MEnt (α O : Type) where
  kv : α
  order : Int
  value : α
  nxt : O

instance [Inhabited α] [Inhabited O] : Inhabited (MEnt α O) := ⟨⟨default, 0, default, default⟩⟩

/-- Entry comparison (`list_richcompare`, Objects/listobject.c): the first item (`==`,
identity first, then `<`), then the order. Equal orders mean the same input (the order is the
input's index times `direction`), whose `next` is the same object: then `[value, order, next]`
lists are equal, so not `<`, and keyed `[key, order, value, next]` lists are decided by their
values. (The heap never holds two entries of one input, so this branch is not reached.) -/
def entLt (E : SEnv W α O) (keyed : Bool) (x y : MEnt α O) : Eff W PyExc Bool :=
  let tie : Eff W PyExc Bool :=
    if !keyed || decide (x.value = y.value) then pure false
    else do
      let e ← E.eq x.value y.value
      if e then pure false else E.lt x.value y.value
  let byOrder : Eff W PyExc Bool := if x.order = y.order then tie else pure (decide (x.order < y.order))
  if x.kv = y.kv then byOrder
  else do
    let e ← E.eq x.kv y.kv
    if e then byOrder else E.lt x.kv y.kv

/-- The order on entry references: `h` holds the entry lists by reference (`s = h[0]` and
`s[0] = next()` mutate the list object in place), so the model's heap is a list of indices into
the store `ents`. A slot the pure-Python `_siftup` duplicated after an exception points at the
same object as its twin, and a later in-place update changes both, as in CPython. -/
def entLtI [Inhabited O] (E : SEnv W α O) (keyed : Bool) (ents : List (MEnt α O)) (i j : Nat) : Eff W PyExc Bool :=
  entLt E keyed (ents.getD i default) (ents.getD j default)

/-- Where the generator is suspended. -/
inductive MSt (α O : Type) where
  /-- not started -/
  | start
  /-- at `yield value` in the inner `while True` (:374 / :398), `s = h[0]`; `h` refers into
  `ents` -/
  | top (h : List Nat) (ents : List (MEnt α O))
  /-- at `yield value` of the single-iterator case (:382 / :407) -/
  | last (s : MEnt α O)
  /-- inside `yield from next.__self__` (:383 / :408), delegating to `it` -/
  | yfrom (it : O)
  /-- finished -/
  | done

variable [Inhabited O]

/-- The `for order, it in enumerate(map(iter, iterables))` loop (:363-368 / :386-392):
`map` calls `iter()` lazily, and a `StopIteration` from it ends the loop like exhaustion; the
`try` covers `next()` and, with a key, `key(value)`. Returns the entries in `h_append` order. -/
def mergeInit (E : SEnv W α O) (key : Option (α → Eff W PyExc α)) (direction : Int) :
    List (O × Nat) → List (MEnt α O) → Eff W PyExc (List (MEnt α O))
  | [], h => pure h
  | (x, order) :: rest, h => do
    let it ← Eff.attempt (E.iter x)                             -- map(iter, iterables)
    match it with
    | .error e => if isA E.hier e "StopIteration" then pure h else Eff.raise e
    | .ok it => do
      let r ← Eff.attempt (do                                   -- try:
        let value ← E.next it                                   -- :366 / :389
        let kv ← applyK key value                               -- :390
        pure (MEnt.mk kv (order * direction) value it))
      match r with
      | .ok ent => mergeInit E key direction rest (h ++ [ent])  -- h_append
      | .error e =>
        if isA E.hier e "StopIteration" then mergeInit E key direction rest h   -- except: pass
        else Eff.raise e

/-- `while len(h) > 1: ... yield value` (:370-374 / :394-398), else the single-iterator tail
(:379-382 / :405-407), else `return`. -/
def mergeYieldTop (h : List Nat) (ents : List (MEnt α O)) : Eff W PyExc (Option α × MSt α O) :=
  if h.length > 1 then pure (some (ents.getD (at! h 0) default).value, .top h ents)
  else match h with
    | i :: _ => pure (some (ents.getD i default).value, .last (ents.getD i default))
    | [] => pure (none, .done)

/-- One `next()` inside `yield from it` (:383 / :408): the delegated iterator's `StopIteration`
ends the generator. -/
def mergeYieldFrom (E : SEnv W α O) (it : O) : Eff W PyExc (Option α × MSt α O) := do
  let v ← nextOpt E it
  match v with
  | some v => pure (some v, .yfrom it)
  | none => pure (none, .done)

/-- The generator body from one suspension point to the next. -/
def mergeBody (E : SEnv W α O) (impl : Bool) (key : Option (α → Eff W PyExc α)) (rev : Bool)
    (iterables : List O) : MSt α O → Eff W PyExc (Option α × MSt α O)
  | .start => do
    let direction : Int := if rev then -1 else 1                 -- :351-360
    let ents ← mergeInit E key direction iterables.zipIdx []
    let ((), h) ← reraise (← hHeapify impl rev (entLtI E key.isSome ents) (List.range ents.length))
    mergeYieldTop h ents                                        -- :369 / :393 above
  | .top h ents => do
    let sid := at! h 0
    let s := ents.getD sid default                              -- s = h[0]
    let r ← Eff.attempt (do                                     -- try: (:371 / :395)
      let value ← E.next s.nxt                                  -- :375 / :399
      let kv ← applyK key value                                 -- :400
      pure { s with kv := kv, value := value })                 -- :375 / :400-401, in place
    match r with
    | .ok s' => do
      let ents := ents.set sid s'
      let hr ← hHeapreplace impl rev (entLtI E key.isSome ents) h sid   -- :376 / :402
      match hr.1 with
      | .ok _ => mergeYieldTop hr.2 ents
      | .error e =>
        if isA E.hier e "StopIteration" then do                 -- except StopIteration:
          let ((_), h) ← reraise (← hHeappop impl rev (entLtI E key.isSome ents) hr.2)  -- :378 / :404
          mergeYieldTop h ents
        else Eff.raise e
    | .error e =>
      if isA E.hier e "StopIteration" then do
        let (_, h) ← reraise (← hHeappop impl rev (entLtI E key.isSome ents) h)  -- :378 / :404
        mergeYieldTop h ents
      else Eff.raise e
  | .last s => do
    let obj ← E.selfOf s.nxt                                    -- `next.__self__` (:383 / :408)
    let it ← E.iter obj                                         -- `yield from` (GET_YIELD_FROM_ITER)
    mergeYieldFrom E it
  | .yfrom it => mergeYieldFrom E it
  | .done => pure (none, .done)

/-- `next(gen)` on the `merge` generator: run the body; a `StopIteration` escaping it becomes
`RuntimeError('generator raised StopIteration')` (PEP 479, Objects/genobject.c). After an
exception the generator is finished (`done`). -/
def mergeStep (E : SEnv W α O) (impl : Bool) (key : Option (α → Eff W PyExc α)) (rev : Bool)
    (iterables : List O) (st : MSt α O) : Eff W PyExc (Option α × MSt α O) := do
  let r ← Eff.attempt (mergeBody E impl key rev iterables st)
  match r with
  | .ok p => pure p
  | .error e =>
    if isA E.hier e "StopIteration" then
      Eff.raise (.named "RuntimeError" "generator raised StopIteration")
    else Eff.raise e

/-- `list(merge(...))`: `next()` until the generator finishes. -/
def mergeDrain (E : SEnv W α O) (impl : Bool) (key : Option (α → Eff W PyExc α)) (rev : Bool)
    (iterables : List O) : Nat → MSt α O → Eff W PyExc (List α)
  | 0, _ => Eff.raise .modelFuel
  | fuel + 1, st => do
    let (v, st) ← mergeStep E impl key rev iterables st
    match v with
    | none => pure []
    | some v => do
      let rest ← mergeDrain E impl key rev iterables fuel st
      pure (v :: rest)

end PyLean.Accel.Heapq
