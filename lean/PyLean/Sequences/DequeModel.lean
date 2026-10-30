import PyLean.Sequences.ListModel

/-!
Model of `collections.deque` (`Modules/_collectionsmodule.c`, CPython 3.14.7).

## Representation of the block structure

A deque is a doubly-linked chain of blocks of `BLOCKLEN = 64` slots. Its items
occupy `leftblock[leftindex..]`, then whole middle blocks, then
`rightblock[..rightindex]`; the chain never has an empty block at either end
(`deque_pop_impl`/`deque_popleft_impl` free a block as soon as it empties,
`deque_append_lock_held` adds one only to store an item). So the chain is
determined by `leftindex` and the number of items, and we number blocks
`0, 1, ...` from `leftblock`: slot `j` of block `b` holds item number
`b * 64 + j - leftindex` (or is unused). `rightblock` is block
`(leftindex + len - 1) / 64` (`rbNum`), and a walk past it is a NULL
pointer.

The record keeps `leftindex`, `rightindex`, the items and `maxlen` exactly
as the C struct does (`maxlen = -1` when unbounded); `Deque.WF` is the
layout invariant documented at _collectionsmodule.c:44-66, which every
operation preserves. `state` (the mutation counter) and the free-block list
only matter for mutation during comparison and for allocation, both out of
scope.
-/

namespace PyLean.Sequences

open PyLean

def BLOCKLEN : Int := 64
/-- `CENTER = (BLOCKLEN - 1) / 2`. -/
def CENTER : Int := 31

structure Deque where
  left : Int
  right : Int
  items : List Int
  maxlen : Int
  deriving Repr, DecidableEq, Inhabited

namespace Deque

def size (d : Deque) : Int := d.items.length

/-- The layout invariant, _collectionsmodule.c:44-66: both indices in
`[0, BLOCKLEN)`, `(leftindex + len - 1) % BLOCKLEN == rightindex`, an empty
deque has `leftindex == rightindex + 1` (in one block), and `maxlen` is `-1`
or bounds the length. -/
def Layout (d : Deque) : Prop :=
  0 ≤ d.left ∧ d.left < 64 ∧ 0 ≤ d.right ∧ d.right < 64 ∧
  (d.left + d.size - 1) % 64 = d.right ∧ (d.size = 0 → d.left = d.right + 1)

def MaxOk (d : Deque) : Prop := d.maxlen = -1 ∨ (0 ≤ d.maxlen ∧ d.size ≤ d.maxlen)

def WF (d : Deque) : Prop := d.Layout ∧ d.MaxOk

/-- Number of the right block. -/
def rbNum (d : Deque) : Int := (d.left + d.size - 1) / 64

/-- Read slot `j` of block `b` (`b->data[j]`). Block numbers outside
`[0, rbNum]` are a NULL dereference; an unused slot holds garbage. -/
def read (d : Deque) (b j : Int) : Py Int :=
  if b < 0 ∨ b > d.rbNum then .error (cUB "NULL block")
  else
    let k := b * 64 + j - d.left
    if 0 ≤ j ∧ j < 64 ∧ 0 ≤ k ∧ k < d.size then .ok (ix d.items k)
    else .error (cUB "unused slot")

/-- Write slot `j` of block `b`. -/
def write (d : Deque) (b j v : Int) : Py Deque :=
  if b < 0 ∨ b > d.rbNum then .error (cUB "NULL block")
  else
    let k := b * 64 + j - d.left
    if 0 ≤ j ∧ j < 64 ∧ 0 ≤ k ∧ k < d.size then .ok { d with items := d.items.set k.toNat v }
    else .error (cUB "unused slot")

/-- `deque_new` (_collectionsmodule.c:143-174): one block, centred, unbounded. -/
def new : Deque := ⟨CENTER + 1, CENTER, [], -1⟩

/-- `deque_pop_impl` (_collectionsmodule.c:185-219). -/
def pop (d : Deque) : Py (Int × Deque) :=
  if d.size = 0 then .error (.indexError "pop from an empty deque")
  else
    let item := ix d.items (d.size - 1)
    let items := d.items.dropLast
    let right := d.right - 1
    if right < 0 then
      if items.length ≠ 0 then .ok (item, { d with items, right := 64 - 1 })
      else .ok (item, { d with items, left := CENTER + 1, right := CENTER })
    else .ok (item, { d with items, right })

/-- `deque_popleft_impl` (_collectionsmodule.c:230-265). -/
def popleft (d : Deque) : Py (Int × Deque) :=
  if d.size = 0 then .error (.indexError "pop from an empty deque")
  else
    let item := ix d.items 0
    let items := d.items.drop 1
    let left := d.left + 1
    if left = 64 then
      if items.length ≠ 0 then .ok (item, { d with items, left := 0 })
      else .ok (item, { d with items, left := CENTER + 1, right := CENTER })
    else .ok (item, { d with items, left })

/-- `NEEDS_TRIM(deque, maxlen)`: `(size_t)maxlen < (size_t)len`, i.e.
`0 <= maxlen < len` (_collectionsmodule.c:279). -/
def needsTrim (d : Deque) (maxlen : Int) : Bool := decide (0 ≤ maxlen ∧ maxlen < d.size)

/-- Drop the popped item of a trim (the C code `Py_DECREF`s it). The trims
only run on non-empty deques, so the error branch is unreachable. -/
def snd' (r : Py (Int × Deque)) (d : Deque) : Deque :=
  match r with
  | .ok (_, d') => d'
  | .error _ => d

/-- `deque_append_lock_held` (_collectionsmodule.c:281-305): a new right
block when `rightindex == BLOCKLEN - 1`, store, then trim from the left. -/
def appendM (d : Deque) (x maxlen : Int) : Deque :=
  let right := if d.right = 64 - 1 then -1 else d.right
  let d := { d with items := d.items ++ [x], right := right + 1 }
  if d.needsTrim maxlen then snd' d.popleft d else d

/-- `deque_appendleft_lock_held` (_collectionsmodule.c:327-352). -/
def appendleftM (d : Deque) (x maxlen : Int) : Deque :=
  let left := if d.left = 0 then 64 else d.left
  let d := { d with items := x :: d.items, left := left - 1 }
  if d.needsTrim maxlen then snd' d.pop d else d

/-- `d.append(x)` / `d.appendleft(x)` (_collectionsmodule.c:318-325, 365-372). -/
def append (d : Deque) (x : Int) : Deque := d.appendM x d.maxlen
def appendleft (d : Deque) (x : Int) : Deque := d.appendleftM x d.maxlen

/-- `deque_extend_impl` (_collectionsmodule.c:415-457) for an iterable other
than the deque itself, yielding `xs`: nothing at all when `maxlen == 0`
(`consume_iterator`), otherwise the "start filling from the left" heuristic
on an empty deque and one `deque_append_lock_held` per item. -/
def extend (d : Deque) (xs : List Int) : Deque :=
  if d.maxlen = 0 then d
  else
    let d := if d.size = 0 then { d with left := 1, right := 0 } else d
    xs.foldl (fun d x => d.appendM x d.maxlen) d

/-- `deque_extendleft_impl` (_collectionsmodule.c:470-513). -/
def extendleft (d : Deque) (xs : List Int) : Deque :=
  if d.maxlen = 0 then d
  else
    let d := if d.size = 0 then { d with left := 64 - 1, right := 64 - 2 } else d
    xs.foldl (fun d x => d.appendleftM x d.maxlen) d

/-- `d.extend(d)` / `d.extendleft(d)` / `d += d`: `PySequence_List(d)` first
(_collectionsmodule.c:423-432, 478-487). -/
def extendSelf (d : Deque) : Deque := d.extend d.items
def extendleftSelf (d : Deque) : Deque := d.extendleft d.items

/-- `deque_clear` (_collectionsmodule.c:658-741): a fresh centred block. -/
def clear (d : Deque) : Deque :=
  if d.size = 0 then d else { d with items := [], left := CENTER + 1, right := CENTER }

/-- `deque_copy_impl` (_collectionsmodule.c:539-584), exact `deque` type:
a new deque with the same `maxlen`, filled from the left by walking the
blocks of the old one. -/
def copy (d : Deque) : Deque :=
  let nd : Deque := { new with maxlen := d.maxlen }
  if d.size > 0 then
    (d.items.foldl (fun nd x => nd.appendM x nd.maxlen) { nd with left := 1, right := 0 })
  else nd

/-- `d + other` (`deque_concat_lock_held`, _collectionsmodule.c:615-645):
copy, then `deque_extend_impl` with the other deque's items. -/
def concat (d other : Deque) : Deque := d.copy.extend other.items

/-! ### Rotation -/

/-- The `n > 0` loop of `_deque_rotate` (_collectionsmodule.c:916-959): a
new left block when `leftindex == 0`, then move the last
`m = min(n, rightindex + 1, leftindex)` items from the right block to the
left block, freeing the right block once it empties. -/
def rotRight : Nat → Int → Int → List Int → Int → Py (Int × Int × List Int)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, li, ri, items, n =>
    if n > 0 then
      let li := if li = 0 then 64 else li
      let m := min (min n (ri + 1)) li
      let ri := ri - m
      let li := li - m
      let k := items.length - m.toNat
      let items := items.drop k ++ items.take k
      let n := n - m
      let ri := if ri < 0 then 64 - 1 else ri
      rotRight fuel li ri items n
    else .ok (li, ri, items)

/-- The `n < 0` loop of `_deque_rotate` (_collectionsmodule.c:960-1003). -/
def rotLeft : Nat → Int → Int → List Int → Int → Py (Int × Int × List Int)
  | 0, _, _, _, _ => .error .modelFuel
  | fuel + 1, li, ri, items, n =>
    if n < 0 then
      let ri := if ri = 64 - 1 then -1 else ri
      let m := min (min (-n) (64 - li)) (64 - 1 - ri)
      let items := items.drop m.toNat ++ items.take m.toNat
      let li := li + m
      let ri := ri + m
      let n := n + m
      let li := if li = 64 then 0 else li
      rotLeft fuel li ri items n
    else .ok (li, ri, items)

/-- The normalisation at the top of `_deque_rotate` (_collectionsmodule.c:903-911);
C `%` truncates. -/
def rotNorm (len n : Int) : Int :=
  let halflen := len / 2
  if n > halflen ∨ n < -halflen then
    let n := n.tmod len
    if n > halflen then n - len else if n < -halflen then n + len else n
  else n

/-- `_deque_rotate(deque, n)` (_collectionsmodule.c:892-1014). -/
def rotateC (d : Deque) (n : Int) : Py Deque :=
  if d.size ≤ 1 then .ok d
  else
    let n := rotNorm d.size n
    let fuel := n.natAbs + 1
    let r := if n > 0 then rotRight fuel d.left d.right d.items n
      else rotLeft fuel d.left d.right d.items n
    match r with
    | .ok (li, ri, items) => .ok { d with left := li, right := ri, items }
    | .error e => .error e

/-- `d.rotate(n)`: Argument Clinic `Py_ssize_t` (default 1), then
`deque_rotate_impl` (_collectionsmodule.c:1027-1034). -/
def rotate (d : Deque) (n : Int) : Py Deque := do
  let n ← asSsize n
  d.rotateC n

/-! ### Searching -/

/-- Advance a `(block, index)` cursor by one slot (`index++; if (index ==
BLOCKLEN) { b = b->rightlink; index = 0; }`). -/
def step1 (b j : Int) : Int × Int := if j + 1 = 64 then (b + 1, 0) else (b, j + 1)

/-- Walk `n` items from `(b, j)`, comparing with `v` (`deque_count_impl`,
_collectionsmodule.c:1154-1189): the number of matches. -/
def countLoop (d : Deque) (v : Int) : Nat → Int → Int → Py Int
  | 0, _, _ => .ok 0
  | n + 1, b, j => do
    let item ← d.read b j
    let (b', j') := step1 b j
    let rest ← countLoop d v n b' j'
    return (if item = v then 1 else 0) + rest

def count (d : Deque) (v : Int) : Py Int := countLoop d v d.items.length 0 d.left

/-- The scan of `deque_remove_impl` (_collectionsmodule.c:1468-1488):
the position `i` of the first match, or `none` (`i == n`). -/
def findLoop (d : Deque) (v : Int) : Nat → Int → Int → Int → Py (Option Int)
  | 0, _, _, _ => .ok none
  | n + 1, i, b, j => do
    let item ← d.read b j
    if item = v then return some i
    let (b', j') := step1 b j
    findLoop d v n (i + 1) b' j'

/-- `deque_index_impl` (_collectionsmodule.c:1257-1316) after argument
conversion: clip, skip whole blocks, skip single slots, then search. -/
def indexC (d : Deque) (v start stop : Int) : Py Int := do
  let size := d.size
  let start := if start < 0 then (if start + size < 0 then 0 else start + size) else start
  let stop := if stop < 0 then (if stop + size < 0 then 0 else stop + size) else stop
  let stop := if stop > size then size else stop
  let start := if start > stop then stop else start
  -- for (i=0 ; i < start - BLOCKLEN ; i += BLOCKLEN) b = b->rightlink;
  let nb := if start - 64 > 0 then (start - 64 + 63) / 64 else 0
  let b := nb
  let i := nb * 64
  -- for ( ; i < start ; i++) { index++; ... }
  let (b, j) := (List.range (start - i).toNat).foldl (fun (bj : Int × Int) _ => step1 bj.1 bj.2) (b, d.left)
  -- a walk from a NULL block would be undefined
  if b > d.rbNum + 1 ∨ nb - 1 > d.rbNum then throw (cUB "walk past NULL")
  match ← findLoop d v (stop - start).toNat start b j with
  | some k => return k
  | none => throw (.valueError "deque.index(x): x not in deque")

/-- `d.index(v[, start[, stop]])`: `_PyEval_SliceIndexNotNone` arguments. -/
def index (d : Deque) (v : Int) (start stop : Option Int) : Py Int :=
  d.indexC v (sliceIndex (start.getD 0)) (sliceIndex (stop.getD ssizeMax))

/-! ### Item access -/

/-- `deque_item_lock_held` (_collectionsmodule.c:1379-1416) for `i` already
made non-negative by `PySequence_GetItem`. -/
def itemC (d : Deque) (i : Int) : Py Int :=
  if !validIndex i d.size then .error (.indexError "deque index out of range")
  else if i = 0 then d.read 0 d.left
  else if i = d.size - 1 then d.read d.rbNum d.right
  else
    let index := i
    let i := i + d.left
    let n := i / 64
    let i := i % 64
    if index < d.size / 2 then d.read n i
    else
      let n := (d.left + d.size - 1) / 64 - n
      d.read (d.rbNum - n) i

/-- `d[i]`: `PyObject_GetItem` → `PyNumber_AsSsize_t(key, IndexError)` →
`PySequence_GetItem` (adds `len` to a negative index), Objects/abstract.c:153-178, 1832-1853. -/
def getitem (d : Deque) (i : Int) : Py Int := do
  let i ← subIndex i
  d.itemC (if i < 0 then i + d.size else i)

/-- `deque_del_item` (_collectionsmodule.c:1429-1444): rotate, popleft, rotate back. -/
def delItem (d : Deque) (i : Int) : Py Deque := do
  let d ← d.rotateC (-i)
  let (_, d) ← d.popleft
  d.rotateC i

/-- `deque_ass_item_lock_held` (_collectionsmodule.c:1498-1528). -/
def assItemC (d : Deque) (i : Int) (v : Option Int) : Py Deque :=
  let len := d.size
  let halflen := (len + 1) / 2
  if !validIndex i len then .error (.indexError "deque index out of range")
  else match v with
  | none => d.delItem i
  | some v =>
    let index := i
    let i := i + d.left
    let n := i / 64
    let i := i % 64
    if index ≤ halflen then d.write n i v
    else
      let n := (d.left + d.size - 1) / 64 - n
      d.write (d.rbNum - n) i v

/-- `d[i] = v` / `del d[i]` (`PySequence_SetItem`/`PySequence_DelItem`). -/
def setitem (d : Deque) (i : Int) (v : Option Int) : Py Deque := do
  let i ← subIndex i
  d.assItemC (if i < 0 then i + d.size else i) v

/-- `deque_remove_impl` (_collectionsmodule.c:1456-1496). -/
def remove (d : Deque) (v : Int) : Py Deque := do
  match ← findLoop d v d.items.length 0 0 d.left with
  | none => throw (.valueError "deque.remove(x): x not in deque")
  | some i => d.delItem i

/-- `deque_insert_impl` (_collectionsmodule.c:1342-1369) after the clinic
`Py_ssize_t` conversion. -/
def insertC (d : Deque) (index v : Int) : Py Deque := do
  let n := d.size
  if d.maxlen = n then throw (.indexError "deque already at its maximum size")
  if index ≥ n then return d.append v
  if index ≤ -n ∨ index = 0 then return d.appendleft v
  let d ← d.rotateC (-index)
  let d := if index < 0 then d.append v else d.appendleft v
  d.rotateC index

def insert (d : Deque) (index v : Int) : Py Deque := do
  let i ← asSsize index
  d.insertC i v

/-- `deque_reverse_impl` (_collectionsmodule.c:1104-1140): swap the items
under a left cursor and a right cursor `len / 2` times. -/
def reverseLoop (d : Deque) : Nat → Int → Int → Int → Int → Py Deque
  | 0, _, _, _, _ => .ok d
  | n + 1, lb, li, rb, ri => do
    let x ← d.read lb li
    let y ← d.read rb ri
    let d ← d.write lb li y
    let d ← d.write rb ri x
    let (lb, li) := step1 lb li
    let (rb, ri) := if ri - 1 < 0 then (rb - 1, 64 - 1) else (rb, ri - 1)
    reverseLoop d n lb li rb ri

def reverse (d : Deque) : Py Deque :=
  d.reverseLoop (d.items.length / 2) 0 d.left d.rbNum d.right

/-! ### Repetition and initialisation -/

/-- `deque_inplace_repeat_lock_held` (_collectionsmodule.c:760-835) for a
`Py_ssize_t` count. The single-item case fills blocks directly. -/
def irepeatC (d : Deque) (n : Int) : Py Deque := do
  let size := d.size
  if size = 0 ∨ n = 1 then return d
  if n ≤ 0 then return d.clear
  if size = 1 then
    let item := ix d.items 0
    let n := if d.maxlen ≥ 0 ∧ n > d.maxlen then d.maxlen else n
    -- the block-filling loop: n - 1 more copies appended on the right
    let k := (n - 1).toNat
    let right := (d.right + (n - 1)) % 64
    return { d with items := d.items ++ List.replicate k item, right }
  if size > ssizeMax / n then throw memoryError
  let seq := d.items
  let n := if d.maxlen ≥ 0 ∧ n * size > d.maxlen then (d.maxlen + size - 1) / size else n
  return (List.range (n - 1).toNat).foldl (fun d _ => d.extend seq) d

/-- `d *= n` (`sequence_repeat` conversion, `deque_inplace_repeat`). -/
def irepeat (d : Deque) (n : Int) : Py Deque := do
  let n ← repeatCount n
  d.irepeatC n

/-- `d * n` (`deque_repeat`, _collectionsmodule.c:848-865): copy, then
repeat the copy in place. -/
def mul (d : Deque) (n : Int) : Py Deque := do
  let n ← repeatCount n
  d.copy.irepeatC n

/-- `d.__init__(iterable, maxlen)` (`deque_init_impl`,
_collectionsmodule.c:1750-1773). `xs` is what the iterable yields after the
clear (so `d.__init__(d)` sees `[]`). -/
def init (d : Deque) (xs : List Int) (maxlen : Option Int) : Py Deque := do
  let maxlen ← match maxlen with
    | none => pure (-1)
    | some m =>
      let m ← asSsize m
      if m < 0 then throw (.valueError "maxlen must be non-negative")
      pure m
  let d := { d with maxlen }
  let d := if d.size > 0 then d.clear else d
  return d.extend xs

/-- `deque(xs, maxlen)`: `deque_new` then `deque_init`. -/
def make (xs : List Int) (maxlen : Option Int) : Py Deque := new.init xs maxlen

/-- Blocks in use, as `__sizeof__` counts them (_collectionsmodule.c:1785-1796). -/
def blocks (d : Deque) : Int := (d.left + d.size + 64 - 1) / 64

end Deque

end PyLean.Sequences
