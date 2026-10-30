import PyLean.Sequences.Common

/-!
Model of the mutating `list` methods of `Objects/listobject.c` (CPython 3.14.7)
on lists of ints. A list is its `List Int` contents; `len(l) <= sys.maxsize`
is a type invariant that properties assume where needed.
-/

namespace PyLean.Sequences

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices toU)

/-- `ins1`, listobject.c:475-499 (the `list_resize` failure path is out of
scope): clip `where` into `[0, n]` (adding `n` to a negative index) and
insert. -/
def ins1Pos (n where_ : Int) : Int :=
  let where_ := if where_ < 0 then (if where_ + n < 0 then 0 else where_ + n) else where_
  if where_ > n then n else where_

def listIns1 (l : List Int) (where_ : Int) (v : Int) : List Int :=
  insAt l (ins1Pos l.length where_).toNat v

/-- `l.insert(index, object)`: Argument Clinic `Py_ssize_t` conversion of
`index`, then `list_insert_impl` (listobject.c:1127-1135). -/
def listInsert (l : List Int) (index v : Int) : Py (List Int) := do
  let i ← asSsize index
  return listIns1 l i v

/-- `l.append(x)`, `list_append_impl` (listobject.c:1176-1184). -/
def listAppend (l : List Int) (v : Int) : List Int := l ++ [v]

/-- `l.pop([index])`: `index` defaults to `-1` (clinic), `list_pop_impl`
(listobject.c:1530-1572). -/
def listPop (l : List Int) (index : Option Int) : Py (Int × List Int) := do
  let index ← match index with
    | none => pure (-1)
    | some i => asSsize i
  if l.length = 0 then throw (.indexError "pop from empty list")
  let index := if index < 0 then index + l.length else index
  if !validIndex index l.length then throw (.indexError "pop index out of range")
  return (ix l index, l.eraseIdx index.toNat)

/-- The search loop of `list_index_impl` (listobject.c:3301-3313):
`for (i = start; i < stop; i++)`, stopping at the end of the list. `fuel`
bounds the iterations (`len(l) + 1` is enough since `start >= 0`). -/
def listIndexLoop (l : List Int) (x : Int) (stop : Int) : Int → Nat → Option Int
  | _, 0 => none
  | i, fuel + 1 =>
    if i < stop then
      if i < l.length then (if ix l i = x then some i else listIndexLoop l x stop (i + 1) fuel)
      else none
    else none

/-- `l.index(x[, start[, stop]])`: `slice_index(accept={int})` arguments
(saturating), `list_index_impl` (listobject.c:3282-3316). -/
def listIndex (l : List Int) (x : Int) (start stop : Option Int) : Py Int :=
  let n : Int := l.length
  let start := sliceIndex (start.getD 0)
  let stop := sliceIndex (stop.getD ssizeMax)
  let start := if start < 0 then (if start + n < 0 then 0 else start + n) else start
  let stop := if stop < 0 then (if stop + n < 0 then 0 else stop + n) else stop
  match listIndexLoop l x stop start (l.length + 1) with
  | some i => .ok i
  | none => .error (.valueError "list.index(x): x not in list")

/-- `l.count(x)`, `list_count_impl` (listobject.c:3323-3346). -/
def listCount (l : List Int) (x : Int) : Int := (l.filter (· == x)).length

/-- `l.remove(x)`, `list_remove_impl` (listobject.c:3361-3382): the first
match is deleted with `list_ass_slice(self, i, i+1, NULL)`. -/
def listRemove (l : List Int) (x : Int) : Py (List Int) :=
  match firstFrom l x 0 l.length with
  | some i => .ok (l.eraseIdx i)
  | none => .error (.valueError "list.remove(x): x not in list")

/-- `l[i]` for an int `i`: `list_subscript` (listobject.c:3646-3656) and
`list_item` (:668-687). -/
def listGetItem (l : List Int) (i : Int) : Py Int := do
  let i ← subIndex i
  let i := if i < 0 then i + l.length else i
  if !validIndex i l.length then throw (.indexError "list index out of range")
  return ix l i

/-- `l[i] = v` / `del l[i]` for an int `i`: `list_ass_subscript_lock_held`
(listobject.c:3692-3699) and `list_ass_item_lock_held` (:1082-1103). -/
def listAssItem (l : List Int) (i : Int) (v : Option Int) : Py (List Int) := do
  let i ← subIndex i
  let i := if i < 0 then i + l.length else i
  if !validIndex i l.length then throw (.indexError "list assignment index out of range")
  match v with
  | none => return l.eraseIdx i.toNat
  | some v => return l.set i.toNat v

/-- `list_ass_slice_lock_held(a, ilow, ihigh, v)` (listobject.c:891-990):
clip `ilow` into `[0, n]` and `ihigh` into `[ilow, n]`, then replace
`a[ilow:ihigh]` by `v` (`[]` for `v == NULL`). -/
def listAssSlice (a : List Int) (ilow ihigh : Int) (v : List Int) : List Int :=
  let n : Int := a.length
  let ilow := if ilow < 0 then 0 else if ilow > n then n else ilow
  let ihigh := if ihigh < ilow then ilow else if ihigh > n then n else ihigh
  a.take ilow.toNat ++ v ++ a.drop ihigh.toNat

/-- `PySlice_Unpack` then `adjust_slice_indexes` (listobject.c:3670-3685):
`(start, stop, step, slicelength)` with `stop` moved to `start` when the
slice runs backwards. -/
def adjustSlice (n : Int) (s : Slice) : Py (Int × Int × Int × Int) := do
  let (start, stop, step) ← sliceUnpack s
  let (start, stop, len) := adjustIndices n start stop step
  let stop := if (step < 0 ∧ start < stop) ∨ (step > 0 ∧ start > stop) then start else stop
  return (start, stop, step, len)

/-- The compaction loop shared by `list_ass_subscript_lock_held`
(listobject.c:3739-3756) and `array_ass_subscr` (Modules/arraymodule.c:2705-2716):
`for (cur = start, i = 0; cur < stop; cur += step, i++)`, moving the `lim`
items after each deleted one down by `i + 1`. All `size_t`, `step > 0`. -/
def delLoop (size step stop : Int) : Nat → List Int → Int → Int → Py (List Int)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, mem, cur, i =>
    if cur < stop then
      let lim := if cur + step ≥ size then size - cur - 1 else step - 1
      match memmove mem (cur - i) (cur + 1) lim with
      | .ok mem => delLoop size step stop fuel mem (cur + step) (i + 1)
      | .error e => .error e
    else .ok mem

/-- Extended-slice deletion after `adjust_slice_indexes`, for `step != 1`
and `slicelength > 0`: listobject.c:3720-3767 (and arraymodule.c:2699-2722,
which runs the same code). The buffer then shrinks to `size - slicelength`. -/
def delExtended (mem : List Int) (start stop step len : Int) : Py (List Int) := do
  let size : Int := mem.length
  let (start, stop, step) :=
    if step < 0 then
      let stop' := start + 1
      (stop' + step * (len - 1) - 1, stop', -step)
    else (start, stop, step)
  let mem ← delLoop size step stop (len.toNat + 1) mem start 0
  let cur := start + len * step
  let mem ← if cur < size then memmove mem (cur - len) cur (size - cur) else pure mem
  return mem.take (size - len).toNat

/-- The extended-slice store loop (listobject.c:3830-3835): positions
`start + i*step` for `i < slicelength`, as a `size_t` cursor. -/
def storeLoop (mem : List Int) (start step : Int) (seq : List Int) : List Int :=
  (List.range seq.length).foldl
    (fun m (i : Nat) => m.set (toU (toU start + (i : Int) * toU step)).toNat (ix seq i)) mem

/-- `l[s] = seq` (`value = some seq`) or `del l[s]` (`value = none`) for a
slice `s` with int/None parts: `list_ass_subscript_lock_held`,
listobject.c:3700-3850. `seq` is the assigned iterable's items
(`PySequence_Fast`; for `l[s] = l` the list's own copy). -/
def listAssSubscript (l : List Int) (s : Slice) (value : Option (List Int)) : Py (List Int) := do
  let (start, stop, step, len) ← adjustSlice l.length s
  match value with
  | none =>
    if step = 1 then return listAssSlice l start stop []
    if len ≤ 0 then return l
    delExtended l start stop step len
  | some seq =>
    if step = 1 then return listAssSlice l start stop seq
    if (seq.length : Int) ≠ len then
      throw (.valueError s!"attempt to assign sequence of size {seq.length} to extended slice of size {len}")
    if len = 0 then return l
    return storeLoop l start step seq

/-- `l *= n`: `sequence_repeat` conversion, then `list_inplace_repeat_lock_held`
(listobject.c:1032-1064). -/
def listIRepeat (l : List Int) (n : Int) : Py (List Int) := do
  let n ← repeatCount n
  let size : Int := l.length
  if size = 0 ∨ n = 1 then return l
  if n < 1 then return []
  if size > ssizeMax / n then throw memoryError
  return (List.replicate n.toNat l).flatten

/-- `l * n`: `list_repeat_lock_held` (listobject.c:789-829). -/
def listRepeat (l : List Int) (n : Int) : Py (List Int) := do
  let n ← repeatCount n
  let size : Int := l.length
  if size = 0 ∨ n ≤ 0 then return []
  if size > ssizeMax / n then throw memoryError
  return (List.replicate n.toNat l).flatten

/-- `l.__init__(iterable)`: `list___init___impl` (listobject.c:3480-3502)
clears the list, then extends it with the iterable; `items` is what the
iterable yields *after* the clear (so `l.__init__(l)` sees `[]`). -/
def listInit (_l : List Int) (items : List Int) : List Int := [] ++ items

end PyLean.Sequences
