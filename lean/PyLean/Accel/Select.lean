import PyLean.Accel.Bisect
import PyLean.Accel.Heap

/-!
Model of the pure-Python-only parts of `heapq` (CPython 3.15.2): `nsmallest`,
`nlargest` (Lib/heapq.py:477-593) and `merge` (:330-408), over ints with an
optional pure key function. They have no C twin; at run time they call
whatever `heapify`/`heapreplace`/... the module exports (the C ones when
`_heapq` is present). The model uses the Python twins; `HeapTwinsAgree` and
`HeapifyTwinsAgree` show the C ones compute the same lists for every `lt`.

An iterable is the list of ints it yields plus three things about `len(iterable)`,
which is a callback (:491-497, :551-557). `sized` says it does not raise
`TypeError` or `AttributeError`, the two classes the source catches. `size` is what
it returns, by default the true count; `__len__` can report any other number,
nothing checks the two against each other, and since 3.15 a low count is observable.
`lenRaises` is any other exception, which propagates.

Python compares the decorated tuples `(elem, order)`, `(key, order, elem)` and
the merge entries `[value, order, next]` lexicographically. The `order` fields
are pairwise distinct, so later fields (the element in `nsmallest`, the bound
`__next__` in `merge`) are never compared and the comparison is lexicographic
on `(first, order)`.
-/

namespace PyLean.Accel

open PyLean

/-- `(a1, a2) < (b1, b2)` on int pairs. -/
def lt2 (a b : Int × Int) : Bool := decide (a.1 < b.1) || (decide (a.1 = b.1) && decide (a.2 < b.2))

/-- `(k, i, e) < (k', i', e')` on int triples. -/
def lt3 (a b : Int × Int × Int) : Bool :=
  decide (a.1 < b.1) || (decide (a.1 = b.1) && lt2 a.2 b.2)

/-- `sorted(l, key=key)`: Python's sort is stable, so it is the stable merge
sort by `key(a) <= key(b)`. -/
def pySorted (key : Option (Int → Int)) (l : List Int) : List Int :=
  l.mergeSort (fun a b => decide (applyKey key a ≤ applyKey key b))

/-- `sorted(l, key=key, reverse=True)`: still stable (equal keys keep their
order), i.e. the stable merge sort by `key(a) >= key(b)`. -/
def pySortedRev (key : Option (Int → Int)) (l : List Int) : List Int :=
  l.mergeSort (fun a b => decide (applyKey key b ≤ applyKey key a))

/-- `l[:n]` for an int `n`. -/
def sliceTo {β : Type} (l : List β) (n : Int) : List β :=
  if 0 ≤ n then l.take n.toNat else l.take (l.length + n).toNat

/-- `min(it, default=sentinel, key=key)` (`min_max`, Python/bltinmodule.c): the
first item whose key is not beaten by a later one under `<`; `none` when
empty. `max` uses `>`. -/
def pyMinMax (better : Int → Int → Bool) (key : Option (Int → Int)) : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl (fun best y => if better (applyKey key y) (applyKey key best) then y else best) x)

/-! ### nsmallest, Lib/heapq.py:477-535 -/

/-- The `for elem in it` loop of the `key is None` branch, :511-515. -/
def nsmallestLoop (result : List (Int × Int)) (top order : Int) :
    List Int → Py (List (Int × Int))
  | [] => .ok result
  | elem :: rest => do
    if elem < top then
      let (_, result) ← pyHeapreplace (maxLt lt2) result (elem, order)
      let top := (at! result 0).1
      nsmallestLoop result top (order + 1) rest
    else nsmallestLoop result top order rest

/-- The `for elem in it` loop of the general branch, :528-533. -/
def nsmallestKeyLoop (key : Int → Int) (result : List (Int × Int × Int)) (top order : Int) :
    List Int → Py (List (Int × Int × Int))
  | [] => .ok result
  | elem :: rest => do
    let k := key elem
    if k < top then
      let (_, result) ← pyHeapreplace (maxLt lt3) result (k, order, elem)
      let top := (at! result 0).1
      nsmallestKeyLoop key result top (order + 1) rest
    else nsmallestKeyLoop key result top order rest

/-- `heapq.nsmallest(n, iterable, key=key)`, Lib/heapq.py:477-535. Only the `n != 1`
path calls `len(iterable)` (:491-497); 3.15 returns `sorted(iterable, key=key)` there
with no `[:n]`. `zip(range(n), it)` takes the first `max(n, 0)` items without
consuming more. -/
def nsmallest (n : Int) (it : List Int) (sized : Bool) (key : Option (Int → Int))
    (size : Int := it.length) (lenRaises : Option PyExc := none) : Py (List Int) := do
  if n = 1 then
    return match pyMinMax (fun a b => decide (a < b)) key it with
      | none => []
      | some r => [r]
  if let some e := lenRaises then throw e
  if sized ∧ n ≥ size then return pySorted key it
  let firstN := (it.take n.toNat).zipIdx
  let rest := it.drop n.toNat
  match key with
  | none =>
    let result := firstN.map (fun (e, i) => (e, (i : Int)))
    if result = [] then return []
    let result := pyHeapify (maxLt lt2) result
    let top := (at! result 0).1
    let result ← nsmallestLoop result top n rest
    let result := result.mergeSort (fun a b => !lt2 b a)
    return result.map (·.1)
  | some f =>
    let result := firstN.map (fun (e, i) => (f e, (i : Int), e))
    if result = [] then return []
    let result := pyHeapify (maxLt lt3) result
    let top := (at! result 0).1
    let result ← nsmallestKeyLoop f result top n rest
    let result := result.mergeSort (fun a b => !lt3 b a)
    return result.map (·.2.2)

/-! ### nlargest, Lib/heapq.py:537-593 -/

/-- The `for elem in it` loop of the `key is None` branch, :569-573. -/
def nlargestLoop (result : List (Int × Int)) (top order : Int) :
    List Int → Py (List (Int × Int))
  | [] => .ok result
  | elem :: rest => do
    if top < elem then
      let (_, result) ← pyHeapreplace lt2 result (elem, order)
      let top := (at! result 0).1
      nlargestLoop result top (order - 1) rest
    else nlargestLoop result top order rest

/-- The `for elem in it` loop of the general branch, :586-591. -/
def nlargestKeyLoop (key : Int → Int) (result : List (Int × Int × Int)) (top order : Int) :
    List Int → Py (List (Int × Int × Int))
  | [] => .ok result
  | elem :: rest => do
    let k := key elem
    if top < k then
      let (_, result) ← pyHeapreplace lt3 result (k, order, elem)
      let top := (at! result 0).1
      nlargestKeyLoop key result top (order - 1) rest
    else nlargestKeyLoop key result top order rest

/-- `heapq.nlargest(n, iterable, key=key)`, Lib/heapq.py:537-593, with `len(iterable)`
as in `nsmallest` (:551-557). `zip(range(0, -n, -1), it)` pairs the first `max(n, 0)`
items with orders `0, -1, -2, ...`; `result.sort(reverse=True)` is a descending
stable sort. -/
def nlargest (n : Int) (it : List Int) (sized : Bool) (key : Option (Int → Int))
    (size : Int := it.length) (lenRaises : Option PyExc := none) : Py (List Int) := do
  if n = 1 then
    return match pyMinMax (fun a b => decide (a > b)) key it with
      | none => []
      | some r => [r]
  if let some e := lenRaises then throw e
  if sized ∧ n ≥ size then return pySortedRev key it
  let firstN := (it.take n.toNat).zipIdx
  let rest := it.drop n.toNat
  match key with
  | none =>
    let result := firstN.map (fun (e, i) => (e, -(i : Int)))
    if result = [] then return []
    let result := pyHeapify lt2 result
    let top := (at! result 0).1
    let result ← nlargestLoop result top (-n) rest
    let result := result.mergeSort (fun a b => !lt2 a b)
    return result.map (·.1)
  | some f =>
    let result := firstN.map (fun (e, i) => (f e, -(i : Int), e))
    if result = [] then return []
    let result := pyHeapify lt3 result
    let top := (at! result 0).1
    let result ← nlargestKeyLoop f result top (-n) rest
    let result := result.mergeSort (fun a b => !lt3 a b)
    return result.map (·.2.2)

/-! ### merge, Lib/heapq.py:330-408 -/

/-- A merge heap entry: `[key_value, order, value, next]` (:390); the `key is
None` branch's `[value, order, next]` (:366) is the same with
`key_value = value`. The remaining items of the input stand for `next`. -/
structure MEntry where
  kv : Int
  order : Int
  value : Int
  rest : List Int
  deriving Repr, Inhabited

/-- Entry comparison: lexicographic on `(key_value, order)`. -/
def entLt (a b : MEntry) : Bool := lt2 (a.kv, a.order) (b.kv, b.order)

/-- The `while len(h) > 1` loop with its inner `while True`, :370-378 and
@3.14.7:394-404. The inner loop only replaces the top entry, so `len(h)` is
unchanged and checking `len(h) > 1` before every step is the same control
flow. `fuel` is the total number of items plus one. -/
def mergeLoop (lt : MEntry → MEntry → Bool) (key : Int → Int) :
    Nat → List MEntry → Py (List Int)
  | 0, _ => .error .modelFuel
  | fuel + 1, h =>
    if h.length > 1 then
      let s := at! h 0
      match s.rest with
      | [] => do
        let (_, h) ← pyHeappop lt h
        let out ← mergeLoop lt key fuel h
        return s.value :: out
      | v :: rest => do
        let (_, h) ← pyHeapreplace lt h { s with kv := key v, value := v, rest := rest }
        let out ← mergeLoop lt key fuel h
        return s.value :: out
    else
      match h with
      | [] => .ok []
      | s :: _ => .ok (s.value :: s.rest)

/-- `list(heapq.merge(*iterables, key=key, reverse=reverse))`, Lib/heapq.py:330-408.
`reverse` selects `heapify_max`/`heappop_max`/`heapreplace_max` and
`direction = -1` (:351-360). -/
def merge (iterables : List (List Int)) (key : Option (Int → Int)) (reverse : Bool) : Py (List Int) :=
  let direction : Int := if reverse then -1 else 1
  let lt := if reverse then maxLt entLt else entLt
  let f := applyKey key
  let h := iterables.zipIdx.filterMap (fun (it, order) =>
    match it with
    | [] => none
    | v :: rest => some { kv := f v, order := order * direction, value := v, rest := rest })
  let h := pyHeapify lt h
  mergeLoop lt f ((iterables.map List.length).sum + 1) h

end PyLean.Accel
