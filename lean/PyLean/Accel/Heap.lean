import PyLean.Core

/-!
Model of the `heapq` heap primitives: the pure-Python twin `Lib/heapq.py` and the
C accelerator `Modules/_heapqmodule.c` (CPython 3.14.7).

Every function is generic in the element type `α` and the comparison
`lt : α → α → Bool`, which is Python's `a < b`. The min-heap functions use
`lt`; the max-heap functions (`*_max`, public since 3.14) are the same code
with every comparison's operands swapped, which is `lt` replaced by
`flip lt` (`maxLt lt`); each `*_max` definition cites its own source lines.

A heap is a Python `list` (`List α`). Functions return the final list (and the
returned item where there is one). The C code's `RuntimeError("list changed
size during iteration")` checks (`_heapqmodule.c:53-57`, `:103-107`, ...) only
fire when a comparison mutates the list, which is out of scope.

Loops use fuel. Each sift loop moves `pos` strictly towards its bound, so the
fuel passed by the callers (the list length or the start position) is always
sufficient, and the fuel-exhausted branches coincide with the loop's normal exit.
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

/-- `heap[i]` for an in-range index. -/
def at! (l : List α) (i : Nat) : α := l.getD i default

/-- The comparison used by the max-heap variants: `maxLt lt a b = lt b a`. -/
def maxLt (lt : α → α → Bool) (a b : α) : Bool := lt b a

/-- Python's `<` on ints, as a `Bool`. -/
def intLt (a b : Int) : Bool := decide (a < b)

/-- The int comparison of the min-heap functions (`isMax = false`) or of the
`*_max` functions (`isMax = true`). -/
def heapLt (isMax : Bool) : Int → Int → Bool := if isMax then maxLt intLt else intLt

/-! ### Pure-Python twin -/

/-- The `while pos > startpos` loop of `_siftdown`, Lib/heapq.py:225-232. -/
def pySiftdownLoop (lt : α → α → Bool) (newitem : α) (startpos : Nat) :
    Nat → List α → Nat → List α × Nat
  | 0, heap, pos => (heap, pos)
  | fuel + 1, heap, pos =>
    if pos > startpos then
      let parentpos := (pos - 1) >>> 1
      let parent := at! heap parentpos
      if lt newitem parent then
        pySiftdownLoop lt newitem startpos fuel (heap.set pos parent) parentpos
      else (heap, pos)
    else (heap, pos)

/-- `_siftdown(heap, startpos, pos)`, Lib/heapq.py:221-233 (`lt`), and
`_siftdown_max`, :294-307 (`maxLt lt`). -/
def pySiftdown (lt : α → α → Bool) (heap : List α) (startpos pos : Nat) : List α :=
  let newitem := at! heap pos
  let (heap, pos) := pySiftdownLoop lt newitem startpos pos heap pos
  heap.set pos newitem

/-- The `while childpos < endpos` loop of `_siftup`, Lib/heapq.py:280-288. -/
def pySiftupLoop (lt : α → α → Bool) (endpos : Nat) : Nat → List α → Nat → List α × Nat
  | 0, heap, pos => (heap, pos)
  | fuel + 1, heap, pos =>
    let childpos := 2 * pos + 1
    if childpos < endpos then
      let rightpos := childpos + 1
      let childpos :=
        if rightpos < endpos ∧ !lt (at! heap childpos) (at! heap rightpos) then rightpos
        else childpos
      pySiftupLoop lt endpos fuel (heap.set pos (at! heap childpos)) childpos
    else (heap, pos)

/-- `_siftup(heap, pos)`, Lib/heapq.py:274-292 (`lt`), and `_siftup_max`,
:309-328 (`maxLt lt`: `not heap[rightpos] < heap[childpos]`). -/
def pySiftup (lt : α → α → Bool) (heap : List α) (pos : Nat) : List α :=
  let endpos := heap.length
  let startpos := pos
  let newitem := at! heap pos
  let (heap, pos) := pySiftupLoop lt endpos endpos heap pos
  pySiftdown lt (heap.set pos newitem) startpos pos

/-- `heappush(heap, item)`, Lib/heapq.py:133-136; `heappush_max` :199-202. -/
def pyHeappush (lt : α → α → Bool) (heap : List α) (item : α) : List α :=
  let heap := heap ++ [item]
  pySiftdown lt heap 0 (heap.length - 1)

/-- `heappop(heap)`, Lib/heapq.py:138-146; `heappop_max` :182-190.
`heap.pop()` raises `IndexError('pop from empty list')`. -/
def pyHeappop (lt : α → α → Bool) (heap : List α) : Py (α × List α) :=
  match heap.getLast? with
  | none => .error (.indexError "pop from empty list")
  | some lastelt =>
    let heap := heap.dropLast
    if heap ≠ [] then
      let returnitem := at! heap 0
      let heap := heap.set 0 lastelt
      .ok (returnitem, pySiftup lt heap 0)
    else .ok (lastelt, heap)

/-- `heapreplace(heap, item)`, Lib/heapq.py:148-162; `heapreplace_max`
:192-197. `heap[0]` on an empty list raises `IndexError('list index out of
range')`. -/
def pyHeapreplace (lt : α → α → Bool) (heap : List α) (item : α) : Py (α × List α) :=
  if heap = [] then .error (.indexError "list index out of range")
  else
    let returnitem := at! heap 0
    .ok (returnitem, pySiftup lt (heap.set 0 item) 0)

/-- `heappushpop(heap, item)`, Lib/heapq.py:164-169 (`heap[0] < item`);
`heappushpop_max` :204-209 (`item < heap[0]`, i.e. `maxLt lt heap[0] item`). -/
def pyHeappushpop (lt : α → α → Bool) (heap : List α) (item : α) : α × List α :=
  if heap ≠ [] ∧ lt (at! heap 0) item then
    (at! heap 0, pySiftup lt (heap.set 0 item) 0)
  else (item, heap)

/-- `heapify(x)`, Lib/heapq.py:171-180; `heapify_max` :211-215:
`for i in reversed(range(n//2)): _siftup(x, i)`. -/
def pyHeapify (lt : α → α → Bool) (x : List α) : List α :=
  ((List.range (x.length / 2)).reverse).foldl (fun h i => pySiftup lt h i) x

/-! ### C accelerator -/

/-- The `while (pos > startpos)` loop of `siftdown`, Modules/_heapqmodule.c:43-66
(`siftdown_max` :426-448 with `maxLt lt`). `newitem` is read once before the
loop (:42) and compared with the parent (:48); the swap re-reads both slots
(:60-64). -/
def cSiftdownLoop (lt : α → α → Bool) (newitem : α) (startpos : Nat) :
    Nat → List α → Nat → List α
  | 0, arr, _ => arr
  | fuel + 1, arr, pos =>
    if pos > startpos then
      let parentpos := (pos - 1) >>> 1
      let parent := at! arr parentpos
      if lt newitem parent then
        let parent := at! arr parentpos
        let newitem' := at! arr pos
        cSiftdownLoop lt newitem startpos fuel ((arr.set parentpos newitem').set pos parent) parentpos
      else arr
    else arr

/-- `siftdown(heap, startpos, pos)`, Modules/_heapqmodule.c:25-68. -/
def cSiftdown (lt : α → α → Bool) (heap : List α) (startpos pos : Nat) : Py (List α) :=
  if pos ≥ heap.length then .error (.indexError "index out of range")
  else .ok (cSiftdownLoop lt (at! heap pos) startpos pos heap pos)

/-- The `while (pos < limit)` loop of `siftup`, Modules/_heapqmodule.c:88-115
(`siftup_max` :470-497 compares `arr[childpos + 1] < arr[childpos]`, which is
`maxLt lt arr[childpos] arr[childpos + 1]`). -/
def cSiftupLoop (lt : α → α → Bool) (endpos limit : Nat) : Nat → List α → Nat → List α × Nat
  | 0, arr, pos => (arr, pos)
  | fuel + 1, arr, pos =>
    if pos < limit then
      let childpos := 2 * pos + 1
      let childpos :=
        if childpos + 1 < endpos then
          if lt (at! arr childpos) (at! arr (childpos + 1)) then childpos else childpos + 1
        else childpos
      let tmp1 := at! arr childpos
      let tmp2 := at! arr pos
      cSiftupLoop lt endpos limit fuel ((arr.set childpos tmp2).set pos tmp1) childpos
    else (arr, pos)

/-- `siftup(heap, pos)`, Modules/_heapqmodule.c:70-118. -/
def cSiftup (lt : α → α → Bool) (heap : List α) (pos : Nat) : Py (List α) :=
  let endpos := heap.length
  let startpos := pos
  if pos ≥ endpos then .error (.indexError "index out of range")
  else
    let limit := endpos >>> 1
    let (arr, pos) := cSiftupLoop lt endpos limit endpos heap pos
    cSiftdown lt arr startpos pos

/-- `_heapq.heappush`, Modules/_heapqmodule.c:131-150; `heappush_max` :513-533. -/
def cHeappush (lt : α → α → Bool) (heap : List α) (item : α) : Py (List α) :=
  let heap := heap ++ [item]
  cSiftdown lt heap 0 (heap.length - 1)

/-- `heappop_internal`, Modules/_heapqmodule.c:152-183 (`heappop` :195-200,
`heappop_max` :545-550). -/
def cHeappop (lt : α → α → Bool) (heap : List α) : Py (α × List α) := do
  let n := heap.length
  if n = 0 then throw (.indexError "index out of range")
  let lastelt := at! heap (n - 1)
  let heap := heap.take (n - 1)
  let n := n - 1
  if n = 0 then return (lastelt, heap)
  let returnitem := at! heap 0
  let heap ← cSiftup lt (heap.set 0 lastelt) 0
  return (returnitem, heap)

/-- `heapreplace_internal`, Modules/_heapqmodule.c:202-220 (`heapreplace`
:242-247, `heapreplace_max` :563-568). -/
def cHeapreplace (lt : α → α → Bool) (heap : List α) (item : α) : Py (α × List α) := do
  if heap.length = 0 then throw (.indexError "index out of range")
  let returnitem := at! heap 0
  let heap ← cSiftup lt (heap.set 0 item) 0
  return (returnitem, heap)

/-- `_heapq.heappushpop`, Modules/_heapqmodule.c:264-298 (`top < item`), and
`heappushpop_max` :601-636 (`item < top`, i.e. `maxLt lt top item`). -/
def cHeappushpop (lt : α → α → Bool) (heap : List α) (item : α) : Py (α × List α) := do
  if heap.length = 0 then return (item, heap)
  let top := at! heap 0
  if !lt top item then return (item, heap)
  if heap.length = 0 then throw (.indexError "index out of range")
  let returnitem := at! heap 0
  let heap ← cSiftup lt (heap.set 0 item) 0
  return (returnitem, heap)

/-- `for (i = hi; i >= lo; i--) body(i)` with early exit on error. -/
def forDown (body : List α → Nat → Py (List α)) (h : List α) (is : List Nat) : Py (List α) :=
  is.foldlM body h

/-- `keep_top_bit(n)`, Modules/_heapqmodule.c:300-310, for `n ≥ 1`. -/
def keepTopBit (n : Nat) : Nat :=
  go n 0 n
where
  go : Nat → Nat → Nat → Nat
    | 0, i, n => n <<< i
    | fuel + 1, i, n => if n > 1 then go fuel (i + 1) (n >>> 1) else n <<< i

/-- The inner `while (1)` of `cache_friendly_heapify`, Modules/_heapqmodule.c:343-349
and :354-360: sift `j`, stop at an even `j`, else continue with `j >>= 1`. -/
def climb (lt : α → α → Bool) : Nat → List α → Nat → Py (List α)
  | 0, h, _ => .ok h
  | fuel + 1, h, j => do
    let h ← cSiftup lt h j
    if j % 2 = 0 then return h
    climb lt fuel h (j >>> 1)

/-- Indices `hi - 1, hi - 2, ..., lo` (empty when `hi ≤ lo`). -/
def downFrom (lo hi : Nat) : List Nat := (List.range (hi - lo)).map (fun k => hi - 1 - k)

/-- `cache_friendly_heapify`, Modules/_heapqmodule.c:332-363. -/
def cCacheFriendlyHeapify (lt : α → α → Bool) (heap : List α) : Py (List α) := do
  let m := heap.length >>> 1
  let leftmost := keepTopBit (m + 1) - 1
  let mhalf := m >>> 1
  let heap ← forDown (fun h i => climb lt (i + 1) h i) heap (downFrom mhalf leftmost)
  forDown (fun h i => climb lt (i + 1) h i) heap (downFrom leftmost m)

/-- `heapify_internal`, Modules/_heapqmodule.c:365-389 (`heapify` :401-406,
`heapify_max` :580-585): the cache-friendly order above 2500 elements, otherwise
`for (i = (n >> 1) - 1; i >= 0; i--) siftup(heap, i)`. -/
def cHeapify (lt : α → α → Bool) (heap : List α) : Py (List α) :=
  let n := heap.length
  if n > 2500 then cCacheFriendlyHeapify lt heap
  else forDown (fun h i => cSiftup lt h i) heap (downFrom 0 (n >>> 1))

end PyLean.Accel
