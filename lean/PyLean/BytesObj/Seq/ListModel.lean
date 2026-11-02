import PyLean.RangeSlice.Model
import PyLean.BytesObj.Seq.TupleModel

/-!
Model of `Objects/listobject.c` outside `list.sort`, CPython 3.15.2
(`Py_GIL_DISABLED` off, 64-bit), over an abstract element type.

`LObj` keeps the fields of a `PyListObject` that Python can see: the items,
`allocated` (through `list.__sizeof__`) and whether `ob_item` is `NULL` (which
decides between `list_preallocate_exact` and `list_resize` in `extend`). Every
allocation decision of the C code is therefore visible to the difftest.

User code that runs inside a list operation (`__eq__`, `__repr__`) may change the
list. Such an operation takes an effectful callback, `Cmp α`, which sees the
current list object and returns the changed one; the loops reread the size and
the slot on every iteration, as the C does. `pureCmp` is the callback of an
element comparison that leaves the list alone.

`Sequences.ListModel` models the contents of the mutating methods on int lists
and proves them correct; here the same code is written over `α` with the
allocation bookkeeping added.
-/

namespace PyLean.BytesObj.Seq

open PyLean
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices toU)

variable {α ρ : Type}

/-- A `PyListObject`. `hasItems` is `ob_item != NULL`; `PyMem_Realloc(p, 0)` does
not return `NULL`, so a list can have `hasItems` with `allocated = 0`. -/
structure LObj (α : Type) where
  items : List α
  allocated : Int := 0
  hasItems : Bool := false
  deriving Repr, DecidableEq

/-- `PyList_New(0)` and `PyType_GenericAlloc`: no array. -/
def LObj.empty : LObj α := { items := [], allocated := 0, hasItems := false }

/-- `list_new_prealloc(n)` filled to size: exactly `n` slots, for `n > 0`
(listobject.c:302-327), or `PyList_New(0)` when there are no items, which is how
every caller guards it. -/
def LObj.prealloc (items : List α) : LObj α :=
  if items.length = 0 then LObj.empty
  else { items := items, allocated := items.length, hasItems := true }

/-- `list.__sizeof__`, `list___sizeof___impl`, listobject.c:3599-3615, for exact
lists: `_PyObject_SIZE(type) + (size_t)allocated * sizeof(PyObject *)` in `size_t`. -/
def listSizeof (o : LObj α) : Int := (40 + toU o.allocated * 8) % (2 ^ 64 : Int)

/-- `((size_t)newsize + (newsize >> 3) + 6) & ~(size_t)3`, listobject.c:148. -/
def overalloc (newsize : Int) : Int := ((newsize + newsize / 8 + 6) / 4) * 4

/-- The `new_allocated` computation of `py_list_resize`, listobject.c:148-156. The
cast `(Py_ssize_t)(new_allocated - newsize)` is exact: see `overalloc_ge`. -/
def newAllocated (size newsize : Int) : Int :=
  let na := overalloc newsize
  let na := if newsize - size > na - newsize then ((newsize + 3) / 4) * 4 else na
  if newsize = 0 then 0 else na

/-- `LIST_SMALL_ALLOCATED`, listobject.c:94. -/
def listSmallAllocated : Int := 32

/-- `list_resize(self, newsize)`, listobject.c:110-129, and `py_list_resize`, :133-216, on
`(allocated, hasItems)`, with `size` the `Py_SIZE(self)` at the call. A small list does not shrink
(gh-158592), and a failed allocation for a smaller size keeps the array. -/
def listResize (allocated : Int) (hasItems : Bool) (size newsize : Int) : Py (Int × Bool) :=
  if allocated ≥ newsize ∧ (newsize ≥ allocated / 2 ∨ allocated ≤ listSmallAllocated) then
    .ok (allocated, hasItems)
  else
    let na := newAllocated size newsize
    if na ≤ ssizeMax / 8 then .ok (na, true)
    else if newsize < allocated then .ok (allocated, hasItems)
    else .error memoryError

/-- `list_resize` then setting the contents: the new slots are filled by the caller. -/
def resizeTo (o : LObj α) (items : List α) : Py (LObj α) :=
  match listResize o.allocated o.hasItems o.items.length items.length with
  | .ok (a, h) => .ok { items := items, allocated := a, hasItems := h }
  | .error e => .error e

/-- `list_preallocate_exact(self, size)`, listobject.c:218-249, for `self->ob_item
== NULL`: `size` rounded up to even, then `PyMem_New`, whose overflow test fails
for a rounded size past `PY_SSIZE_T_MAX / sizeof(PyObject *)`. `size + 1` overflows
`Py_ssize_t` at `PY_SSIZE_T_MAX`; the wrapped value is negative, then a huge `size_t`
in `PyMem_New`, so the same test fails. -/
def listPreallocateExact (size : Int) : Py Int :=
  let rounded := ((size + 1) / 2) * 2
  if rounded ≤ ssizeMax / 8 then .ok rounded else .error memoryError

/-- `list_clear_impl(a, is_resize)`, listobject.c:893-921, and its wrappers. -/
def listClear (a : LObj α) : LObj α :=
  if !a.hasItems then a else { items := [], allocated := 0, hasItems := false }

/-- `list_get_item_ref(op, i)` of the default build, listobject.c:401-408. -/
def listGetItemRef (l : List α) (i : Int) : Option α :=
  if validIndex i l.length then slot l i else none

/-- `ins1(self, where, v)`, listobject.c:502-528. `v == NULL` is the `none` case. -/
def ins1Where (n where_ : Int) : Int :=
  let w := if where_ < 0 then (if where_ + n < 0 then 0 else where_ + n) else where_
  if w > n then n else w

def ins1 (self : LObj α) (where_ : Int) (v : Option α) : Py (LObj α) :=
  match v with
  | none => .error systemError
  | some v =>
    let n : Int := self.items.length
    let w := (ins1Where n where_).toNat
    resizeTo self (self.items.take w ++ v :: self.items.drop w)

/-- `l.insert(index, object)`, `list_insert_impl`, listobject.c:1203-1211. -/
def listInsert (self : LObj α) (index : Int) (v : α) : Py (LObj α) := do
  let i ← PyLean.Sequences.asSsize index
  ins1 self i (some v)

/-- `_PyList_AppendTakeRef`, Include/internal/pycore_list.h:36-53, with
`_PyList_AppendTakeRefListResize`, listobject.c:546-557. -/
def listAppend (self : LObj α) (v : α) : Py (LObj α) :=
  if self.allocated > self.items.length then
    .ok { self with items := self.items ++ [v] }
  else resizeTo self (self.items ++ [v])

/-- `list_length(a)`, listobject.c:670-674: `PyList_GET_SIZE`. -/
def listLength (l : List α) : Int := l.length

/-- `list_item(aa, i)`, listobject.c:695-714. -/
def listItem (l : List α) (i : Int) : Py α :=
  if !validIndex i l.length then .error (.indexError "list index out of range")
  else match slot l i with
    | some v => .ok v
    | none => .error (cUB "read outside the items array")

/-- `l[i]`, `list_subscript`, listobject.c:3711-3723. -/
def listGetItem (l : List α) (i : Int) : Py α := do
  let i ← PyLean.Sequences.subIndex i
  let i := if i < 0 then i + l.length else i
  listItem l i

/-- `list_slice_lock_held(a, ilow, ihigh)`, listobject.c:716-738. -/
def listSliceLH (a : List α) (ilow ihigh : Int) : LObj α :=
  let len := ihigh - ilow
  if len ≤ 0 then LObj.empty
  else LObj.prealloc ((a.drop ilow.toNat).take len.toNat)

/-- `list_slice_step_lock_held`, listobject.c:3654-3672, and `list_slice_wrap`,
:3674-3691, after `PySlice_Unpack`. -/
def listSliceWrap (a : List α) (start stop step : Int) : Py (LObj α) :=
  let (start, stop, len) := adjustIndices a.length start stop step
  if len ≤ 0 then .ok LObj.empty
  else if step = 1 then .ok (listSliceLH a start stop)
  else
    match sliceLoop a (toU step) len.toNat (toU start) with
    | .ok r => .ok (LObj.prealloc r)
    | .error e => .error e

/-- `l[s]`, `list_slice_subscript`, listobject.c:3693-3703. -/
def listGetSlice (a : List α) (s : Slice) : Py (LObj α) := do
  let (start, stop, step) ← sliceUnpack s
  listSliceWrap a start stop step

/-- `_PyList_BinarySlice(container, start, stop)`, listobject.c, for an exact list. -/
def listBinarySlice (a : List α) (s : Slice) : LObj α :=
  let (istart, istop) := unpackIndices a.length s
  listSliceLH a istart istop

/-- `list_iteritem(obj, index)`, listobject.c, the `_tp_iteritem` of a `for` loop: the size is read at
each step, and the index advances past the end too. -/
def listIterItem (l : List α) (index : Int) : Option α × Int :=
  (listGetItemRef l index, index + 1)

/-- `a + b`, `list_concat_lock_held`, listobject.c:790-820. -/
def listConcat (a b : List α) : LObj α := LObj.prealloc (a ++ b)

/-- `a + other`, `_PyList_Concat`, listobject.c:822-838. -/
def listConcatAny (a : List α) (bb : Sum (List α) String) : Py (LObj α) :=
  match bb with
  | .inl b => .ok (listConcat a b)
  | .inr name => .error (.typeError s!"can only concatenate list (not \"{name}\") to list")

/-- `a * n`, `list_repeat_lock_held`, listobject.c:840-880, with `list_new_prealloc`
failing like `PyMem_New` for an output past `PY_SSIZE_T_MAX / 8`. -/
def listRepeat (a : List α) (n : Int) : Py (LObj α) :=
  let inputSize : Int := a.length
  if inputSize = 0 ∨ n ≤ 0 then .ok LObj.empty
  else if inputSize > ssizeMax / n then .error memoryError
  else if inputSize * n > ssizeMax / 8 then .error memoryError
  else .ok (LObj.prealloc (List.replicate n.toNat a).flatten)

/-- `sequence_repeat` conversion of the count, then `list_repeat`. -/
def listMul (a : List α) (n : Int) : Py (LObj α) := do
  let n ← PyLean.Sequences.repeatCount n
  listRepeat a n

/-- The slice-store core of `list_ass_slice_lock_held`, listobject.c:970-1059:
clip, then clear, shrink (`list_resize`, `d < 0`), grow (`d > 0`) or store. `v =
none` deletes. -/
def listAssSlice (a : LObj α) (ilow ihigh : Int) (v : Option (List α)) : Py (LObj α) :=
  let vs := v.getD []
  let n : Int := vs.length
  let size : Int := a.items.length
  let ilow := if ilow < 0 then 0 else if ilow > size then size else ilow
  let ihigh := if ihigh < ilow then ilow else if ihigh > size then size else ihigh
  let norig := ihigh - ilow
  let d := n - norig
  if size + d = 0 then .ok (listClear a)
  else
    let items := a.items.take ilow.toNat ++ vs ++ a.items.drop ihigh.toNat
    if d = 0 then .ok { a with items := items } else resizeTo a items

/-- `list_inplace_repeat_lock_held(self, n)`, listobject.c:1101-1140. -/
def listInplaceRepeat (self : LObj α) (n : Int) : Py (LObj α) :=
  let inputSize : Int := self.items.length
  if inputSize = 0 ∨ n = 1 then .ok self
  else if n < 1 then .ok (listClear self)
  else if inputSize > ssizeMax / n then .error memoryError
  else
    match listResize self.allocated self.hasItems inputSize (inputSize * n) with
    | .ok (a, h) =>
      .ok { items := (List.replicate n.toNat self.items).flatten, allocated := a, hasItems := h }
    | .error e => .error e

/-- `a *= n`. -/
def listIMul (self : LObj α) (n : Int) : Py (LObj α) := do
  let n ← PyLean.Sequences.repeatCount n
  listInplaceRepeat self n

/-- `list_ass_item_lock_held(a, i, v)`, listobject.c:1159-1179. A deletion moves the tail down and
calls `list_resize`, like every other shrinking path. -/
def listAssItem (a : LObj α) (i : Int) (v : Option α) : Py (LObj α) :=
  if !validIndex i a.items.length then .error (.indexError "list assignment index out of range")
  else match v with
    | none => resizeTo a (a.items.eraseIdx i.toNat)
    | some v => .ok { a with items := a.items.set i.toNat v }

/-- `l[i] = v` / `del l[i]`, the int branch of `list_ass_subscript_lock_held`,
listobject.c:3758-3764. -/
def listSetItem (a : LObj α) (i : Int) (v : Option α) : Py (LObj α) := do
  let i ← PyLean.Sequences.subIndex i
  let i := if i < 0 then i + a.items.length else i
  listAssItem a i v

/-! ## extend -/

/-- `PySequence_Fast_ITEMS` of the argument to `list_extend_fast`,
listobject.c:1262-1298. -/
def listExtendFast (self : LObj α) (seq : List α) : Py (LObj α) :=
  if seq.length = 0 then .ok self
  else if !self.hasItems then
    match listPreallocateExact seq.length with
    | .ok a => .ok { items := self.items ++ seq, allocated := a, hasItems := true }
    | .error e => .error e
  else resizeTo self (self.items ++ seq)

/-- `list_extend_set` / `list_extend_dict` / `list_extend_dictitems`,
listobject.c:1388-1475: `list_resize(self, m + n)`, always (never exact), then
the `n` new items. -/
def listExtendSized (self : LObj α) (items : List α) : Py (LObj α) :=
  if self.items.length + items.length = 0 then .ok self
  else resizeTo self (self.items ++ items)

/-- What `list_extend_iter_lock_held` sees of a generic iterable. -/
structure IterSrc (α : Type) where
  /-- `PyObject_LengthHint(iterable, 8)`. -/
  hint : Py Int := .ok 8
  /-- What the iterator yields before it stops. -/
  items : List α
  /-- The exception that stops it, if it is not `StopIteration`. -/
  err : Option PyExc := none

/-- The result of an operation that can fail after changing the list. -/
abbrev LRes (α : Type) := LObj α × Option PyExc

/-- The drain loop of `list_extend_iter_lock_held`, listobject.c:1338-1359: while
there is room the item goes straight in, otherwise through
`_PyList_AppendTakeRef`. -/
def extendDrain (self : LObj α) : List α → Py (LObj α)
  | [] => .ok self
  | x :: xs =>
    if (self.items.length : Int) < self.allocated then
      extendDrain { self with items := self.items ++ [x] } xs
    else
      match listAppend self x with
      | .ok o => extendDrain o xs
      | .error e => .error e

/-- The room-making step of `list_extend_iter_lock_held`, listobject.c:1316-1335. -/
def extendRoom (self : LObj α) (n : Int) : Py (LObj α) :=
  let m : Int := self.items.length
  if m > ssizeMax - n then .ok self
  else if !self.hasItems then
    if n ≠ 0 then
      match listPreallocateExact n with
      | .ok a => .ok { self with allocated := a, hasItems := true }
      | .error e => .error e
    else .ok self
  else
    match listResize self.allocated self.hasItems m (m + n) with
    | .ok (a, h) => .ok { self with allocated := a, hasItems := h }
    | .error e => .error e

/-- `list_extend_iter_lock_held(self, iterable)`, listobject.c:1300-1373. An
exception out of the iterator skips the final cut-back and leaves what was
appended. -/
def listExtendIter (self : LObj α) (src : IterSrc α) : LRes α :=
  match src.hint with
  | .error e => (self, some e)
  | .ok n =>
    match extendRoom self n with
    | .error e => (self, some e)
    | .ok o =>
      match extendDrain o src.items with
      | .error e => (o, some e)
      | .ok o =>
        match src.err with
        | some e => (o, some e)
        | none =>
          if (o.items.length : Int) < o.allocated then
            match listResize o.allocated o.hasItems o.items.length o.items.length with
            | .ok (a, h) => ({ o with allocated := a, hasItems := h }, none)
            | .error e => (o, some e)
          else (o, none)

/-- The argument of `list.extend`, as `_list_extend` classifies it. -/
inductive ExtArg (α : Type) where
  /-- `(PyObject *)self == iterable`. -/
  | self
  /-- An exact `list` or `tuple`: `list_extend_lock_held`. -/
  | fast (items : List α)
  /-- An exact set or frozenset, a dict, or a dict view: the items in iteration
  order, as `list_extend_set`, `list_extend_dict` and `list_extend_dictitems`
  would store them. -/
  | sized (items : List α)
  /-- Anything else with an iterator: `list_extend_iter_lock_held`. -/
  | iter (src : IterSrc α)
  /-- `PyObject_GetIter` fails; `name` is the type's `tp_name`. -/
  | notIterable (name : String)

/-- `Py (LObj α)` as a `LRes α`: failure leaves the list alone. -/
def liftRes (self : LObj α) : Py (LObj α) → LRes α
  | .ok o => (o, none)
  | .error e => (self, some e)

/-- `_list_extend(self, iterable)`, listobject.c:1477-1532. -/
def listExtend (self : LObj α) : ExtArg α → LRes α
  | .self => liftRes self (listInplaceRepeat self 2)
  | .fast items => liftRes self (listExtendFast self items)
  | .sized items => liftRes self (listExtendSized self items)
  | .iter src => listExtendIter self src
  | .notIterable name => (self, some (.typeError s!"'{name}' object is not iterable"))

/-- `l += iterable`, `list_inplace_concat`, listobject.c:1584-1592, which is
`_list_extend` and returns `self`. -/
def listIConcat (self : LObj α) (arg : ExtArg α) : LRes α := listExtend self arg

/-- `l.__init__(iterable)`, `list___init___impl`, listobject.c:3543-3565: the old
contents are dropped before the iterable is looked at. -/
def listInit (self : LObj α) (iterable : Option (ExtArg α)) : LRes α :=
  let o := if self.hasItems then listClear self else self
  match iterable with
  | some arg => listExtend o arg
  | none => (o, none)

/-- `list(iterable)`: `list_vectorcall`, listobject.c:3567-3590. -/
def listVectorcall (args : List (ExtArg α)) (nkw : Nat) : Py (LObj α) :=
  if nkw ≠ 0 then .error (.typeError "list() takes no keyword arguments")
  else if args.length > 1 then
    .error (.typeError s!"list expected at most 1 argument, got {args.length}")
  else
    match args with
    | arg :: _ =>
      match listInit (LObj.empty : LObj α) (some arg) with
      | (o, none) => .ok o
      | (_, some e) => .error e
    | [] => .ok LObj.empty

/-- `l.pop(index)` after the clinic conversion, `list_pop_impl`,
listobject.c:1606-1638. -/
def listPopK (self : LObj α) (index : Int) : Py (α × LObj α) :=
  let size : Int := self.items.length
  if size = 0 then .error (.indexError "pop from empty list")
  else
    let index := if index < 0 then index + size else index
    if !validIndex index size then .error (.indexError "pop index out of range")
    else
      match slot self.items index with
      | none => .error (cUB "list_pop_impl")
      | some v =>
        let sizeAfter := size - 1
        if sizeAfter = 0 then .ok (v, listClear self)
        else
          match resizeTo self (self.items.eraseIdx index.toNat) with
          | .ok o => .ok (v, o)
          | .error e => .error e

/-- `l.pop([index])`. -/
def listPop (self : LObj α) (index : Option Int) : Py (α × LObj α) :=
  match index with
  | none => listPopK self (-1)
  | some i =>
    match PyLean.Sequences.asSsize i with
    | .ok i => listPopK self i
    | .error e => .error e

/-- `reverse_slice(lo, hi)`, listobject.c:1640-1654: the two cursors swap and
meet. `front` and `back` are the parts already swapped into place, `mid` the
part between the cursors. -/
def reverseLoop : Nat → List α → List α → List α → List α
  | 0, front, mid, back => front.reverse ++ mid ++ back
  | fuel + 1, front, mid, back =>
    match mid with
    | a :: b :: rest =>
      let inner := (a :: b :: rest).dropLast.drop 1
      let hi := (a :: b :: rest).getLast (by simp)
      reverseLoop fuel (hi :: front) inner (a :: back)
    | _ => front.reverse ++ mid ++ back

/-- `l.reverse()`, `list_reverse_impl`, listobject.c:3254-3261, and `PyList_Reverse`,
:3263-3278. -/
def listReverse (self : LObj α) : LObj α :=
  if self.items.length > 1 then
    { self with items := reverseLoop self.items.length [] self.items [] }
  else self

/-! ## Comparisons that may change the list -/

/-- A comparison called from a list method: `(result, list after the call)`. -/
abbrev Cmp (α : Type) := LObj α → α → α → Py Bool × LObj α

/-- `PyObject_RichCompareBool(item, el, Py_EQ)` with no side effect on the list. -/
def pureCmp (E : ElemOps α ρ) : Cmp α := fun o a b => (richBool E .eq a b, o)

/-- `list_contains(aa, el)`, listobject.c:676-693. -/
def containsLoop (cmp : Cmp α) (el : α) : Nat → Int → LObj α → Py Bool × LObj α
  | 0, _, o => (.error .modelFuel, o)
  | fuel + 1, i, o =>
    match listGetItemRef o.items i with
    | none => (.ok false, o)
    | some item =>
      match cmp o item el with
      | (.ok false, o') => containsLoop cmp el fuel (i + 1) o'
      | r => r

def listContains (cmp : Cmp α) (fuel : Nat) (o : LObj α) (el : α) : Py Bool × LObj α :=
  containsLoop cmp el fuel 0 o

/-- The loop of `list_index_impl`, listobject.c:3360-3372: `none` is falling out
of the loop, which is what raises `ValueError`. -/
def indexLoop (cmp : Cmp α) (value : α) (stop : Int) : Nat → Int → LObj α → Py (Option Int) × LObj α
  | 0, _, o => (.error .modelFuel, o)
  | fuel + 1, i, o =>
    if i < stop then
      match listGetItemRef o.items i with
      | none => (.ok none, o)
      | some item =>
        match cmp o item value with
        | (.ok true, o') => (.ok (some i), o')
        | (.ok false, o') => indexLoop cmp value stop fuel (i + 1) o'
        | (.error e, o') => (.error e, o')
    else (.ok none, o)

/-- `start` and `stop` of `list_index_impl`, listobject.c:3350-3359. -/
def listIndexBounds (n : Int) (start stop : Option Int) : Int × Int :=
  let start := PyLean.Sequences.sliceIndex (start.getD 0)
  let stop := PyLean.Sequences.sliceIndex (stop.getD ssizeMax)
  let start := if start < 0 then (if start + n < 0 then 0 else start + n) else start
  let stop := if stop < 0 then (if stop + n < 0 then 0 else stop + n) else stop
  (start, stop)

/-- `l.index(value, start, stop)`, `list_index_impl`, listobject.c:3345-3375. -/
def listIndex (cmp : Cmp α) (fuel : Nat) (o : LObj α) (value : α) (start stop : Option Int) :
    Py Int × LObj α :=
  let (start, stop) := listIndexBounds o.items.length start stop
  match indexLoop cmp value stop fuel start o with
  | (.ok (some i), o') => (.ok i, o')
  | (.ok none, o') => (.error (.valueError "list.index(x): x not in list"), o')
  | (.error e, o') => (.error e, o')

/-- `list_count_impl`, listobject.c:3386-3410: the `obj == value` shortcut, then
the comparison. -/
def countLoop (same : α → α → Bool) (cmp : Cmp α) (value : α) :
    Nat → Int → Int → LObj α → Py Int × LObj α
  | 0, _, _, o => (.error .modelFuel, o)
  | fuel + 1, i, count, o =>
    match listGetItemRef o.items i with
    | none => (.ok count, o)
    | some obj =>
      if same obj value then countLoop same cmp value fuel (i + 1) (count + 1) o
      else
        match cmp o obj value with
        | (.ok true, o') => countLoop same cmp value fuel (i + 1) (count + 1) o'
        | (.ok false, o') => countLoop same cmp value fuel (i + 1) count o'
        | (.error e, o') => (.error e, o')

def listCount (same : α → α → Bool) (cmp : Cmp α) (fuel : Nat) (o : LObj α) (value : α) :
    Py Int × LObj α :=
  countLoop same cmp value fuel 0 0 o

/-- `list_remove_impl`, listobject.c:3424-3445. After the comparison the slice
deletion uses the old `i` on the current list, and clips. -/
def removeLoop (cmp : Cmp α) (value : α) : Nat → Int → LObj α → Py Unit × LObj α
  | 0, _, o => (.error .modelFuel, o)
  | fuel + 1, i, o =>
    if i < o.items.length then
      match slot o.items i with
      | none => (.error (cUB "list_remove_impl"), o)
      | some item =>
        match cmp o item value with
        | (.ok true, o') =>
          match listAssSlice o' i (i + 1) none with
          | .ok o'' => (.ok (), o'')
          | .error e => (.error e, o')
        | (.ok false, o') => removeLoop cmp value fuel (i + 1) o'
        | (.error e, o') => (.error e, o')
    else (.error (.valueError "list.remove(x): x not in list"), o)

def listRemove (cmp : Cmp α) (fuel : Nat) (o : LObj α) (value : α) : Py Unit × LObj α :=
  removeLoop cmp value fuel 0 o

/-! ## Rich comparison -/

/-- The two lists of a comparison, which a user `__eq__` may also change. -/
abbrev Cmp2 (α : Type) := List α × List α → α → α → Py Bool × (List α × List α)

/-- A comparison that does not change either list. -/
def pureCmp2 (E : ElemOps α ρ) : Cmp2 α := fun st a b => (richBool E .eq a b, st)

/-- The closing `PyObject_RichCompare(vitem, witem, op)`: user code again, so it may
change the lists as well, though nothing reads them afterwards. -/
abbrev Final (α ρ : Type) := CmpOp → List α × List α → α → α → Py ρ × (List α × List α)

/-- A closing comparison that does not change either list. -/
def pureFinal (E : ElemOps α ρ) : Final α ρ := fun op st a b => (E.rich op a b, st)

/-- The search of `list_richcompare_impl`, listobject.c:3479-3495: sizes and slots
are reread on each pass, and an identical pair is skipped without a call. -/
def cmpLoop (same : α → α → Bool) (cmp : Cmp2 α) :
    Nat → Int → List α × List α → Py Int × (List α × List α)
  | 0, _, st => (.error .modelFuel, st)
  | fuel + 1, i, st =>
    if i < st.1.length ∧ i < st.2.length then
      match slot st.1 i, slot st.2 i with
      | some vi, some wi =>
        if same vi wi then cmpLoop same cmp fuel (i + 1) st
        else
          match cmp st vi wi with
          | (.ok true, st') => cmpLoop same cmp fuel (i + 1) st'
          | (.ok false, st') => (.ok i, st')
          | (.error e, st') => (.error e, st')
      | _, _ => (.error (cUB "list_richcompare_impl"), st)
    else (.ok i, st)

/-- `list_richcompare_impl(v, w, op)`, listobject.c:3458-3519, for two lists. -/
def listRichcompare (E : ElemOps α ρ) (cmp : Cmp2 α) (final : Final α ρ) (fuel : Nat)
    (op : CmpOp) (v w : List α) : Py ρ × (List α × List α) :=
  if v.length ≠ w.length ∧ (op = .eq ∨ op = .ne) then
    (.ok (E.ofBool (op = .ne)), (v, w))
  else
    match cmpLoop E.same cmp fuel 0 (v, w) with
    | (.error e, st) => (.error e, st)
    | (.ok i, st) =>
      if i ≥ st.1.length ∨ i ≥ st.2.length then
        (.ok (E.ofBool (cmpSizes op st.1.length st.2.length)), st)
      else if op = .eq then (.ok (E.ofBool false), st)
      else if op = .ne then (.ok (E.ofBool true), st)
      else
        match slot st.1 i, slot st.2 i with
        | some vi, some wi => final op st vi wi
        | _, _ => (.error (cUB "list_richcompare_impl"), st)

/-! ## Slice assignment -/

/-- The value of `l[s] = value`, as `list_ass_subscript_lock_held` receives it. -/
inductive AssVal (α : Type) where
  /-- `del l[s]`: `value == NULL`. -/
  | del
  /-- `(PyListObject*)value == self`: a private copy is taken first. -/
  | selfCopy
  /-- `PySequence_Fast(value, ...)` succeeded with these items. -/
  | seq (items : List α)
  /-- `PySequence_Fast` fails: `value` is not iterable. -/
  | notIterable

/-- `memmove` on the items, as `Sequences.memmove`. -/
def memmoveL (mem : List α) (dst src cnt : Int) : Py (List α) :=
  if 0 ≤ dst ∧ 0 ≤ src ∧ 0 ≤ cnt ∧ dst + cnt ≤ mem.length ∧ src + cnt ≤ mem.length then
    .ok (mem.take dst.toNat ++ (mem.drop src.toNat).take cnt.toNat ++ mem.drop (dst + cnt).toNat)
  else .error (cUB "memmove out of bounds")

/-- The compaction loop of `list_ass_subscript_lock_held`, listobject.c:3808-3821. -/
def delLoopL (size step stop : Int) : Nat → List α → Int → Int → Py (List α)
  | 0, _, _, _ => .error .modelFuel
  | fuel + 1, mem, cur, i =>
    if cur < stop then
      let lim := if cur + step ≥ size then size - cur - 1 else step - 1
      match memmoveL mem (cur - i) (cur + 1) lim with
      | .ok mem => delLoopL size step stop fuel mem (cur + step) (i + 1)
      | .error e => .error e
    else .ok mem

/-- Extended-slice deletion, listobject.c:3789-3829: the normalisation of a
negative step, the compaction, the tail move, `Py_SET_SIZE` then `list_resize`
with the size already set. -/
def delExtendedL (o : LObj α) (start stop step len : Int) : Py (LObj α) := do
  let mem := o.items
  let size : Int := mem.length
  let (start, stop, step) :=
    if step < 0 then
      let stop' := start + 1
      (stop' + step * (len - 1) - 1, stop', -step)
    else (start, stop, step)
  let mem ← delLoopL size step stop (len.toNat + 1) mem start 0
  let cur := start + len * step
  let mem ← if cur < size then memmoveL mem (cur - len) cur (size - cur) else pure mem
  let newsize := size - len
  match listResize o.allocated o.hasItems newsize newsize with
  | .ok (a, h) => .ok { items := mem.take newsize.toNat, allocated := a, hasItems := h }
  | .error e => .error e

/-- The store loop of `list_ass_subscript_lock_held`, listobject.c:3893-3898. -/
def storeLoopL (mem : List α) (step : Int) : List α → Int → List α
  | [], _ => mem
  | x :: xs, cur => storeLoopL (mem.set cur.toNat x) step xs (cur + step)

/-- `adjust_slice_indexes(lst, &start, &stop, step)`, listobject.c:3735-3750. -/
def adjustSliceIndexes (n start stop step : Int) : Int × Int × Int :=
  let (start, stop, len) := adjustIndices n start stop step
  let stop := if (step < 0 ∧ start < stop) ∨ (step > 0 ∧ start > stop) then start else stop
  (start, stop, len)

/-- `l[s] = value` / `del l[s]`, the slice branch of
`list_ass_subscript_lock_held`, listobject.c:3766-3909. -/
def listAssSubscript (self : LObj α) (s : Slice) (value : AssVal α) : Py (LObj α) := do
  let (start, stop, step) ← sliceUnpack s
  let n : Int := self.items.length
  match value with
  | .del =>
    let (start, stop, len) := adjustSliceIndexes n start stop step
    if step = 1 then listAssSlice self start stop none
    else if len ≤ 0 then .ok self
    else delExtendedL self start stop step len
  | .notIterable => .error (.typeError "must assign iterable to extended slice")
  | .selfCopy => assSeq self.items n start stop step
  | .seq items => assSeq items n start stop step
where
  assSeq (seq : List α) (n start stop step : Int) : Py (LObj α) :=
    let (start, stop, len) := adjustSliceIndexes n start stop step
    if step = 1 then listAssSlice self start stop (some seq)
    else if (seq.length : Int) ≠ len then
      .error (.valueError s!"attempt to assign sequence of size {seq.length} to extended slice of size {len}")
    else if len = 0 then .ok self
    else .ok { self with items := storeLoopL self.items step seq start }

/-! ## Iterators -/

/-- `_PyListIterObject` and `listreviterobject`: `alive` is `it_seq != NULL`. The
list itself lives outside the iterator and may change between calls. -/
structure ListIter where
  index : Int
  alive : Bool
  deriving Repr, DecidableEq

/-- `list_iter(seq)`, listobject.c:4051-4069. -/
def listIter : ListIter := ⟨0, true⟩

/-- `listiter_next(self)`, listobject.c:4088-4110. A negative index returns first,
so `it_seq` is only used when `alive`; `cUB` reports the NULL dereference that
`ListIterWF` rules out. -/
def listIterNext (it : ListIter) (l : List α) : Py (Option α × ListIter) :=
  if it.index < 0 then .ok (none, it)
  else if !it.alive then .error (cUB "listiter_next on NULL it_seq")
  else
    match listGetItemRef l it.index with
    | none => .ok (none, ⟨-1, false⟩)
    | some v => .ok (some v, { it with index := it.index + 1 })

/-- `listiter_len(self)`, listobject.c:4112-4124. -/
def listIterLen (it : ListIter) (l : List α) : Int :=
  if it.index ≥ 0 then
    let len := (l.length : Int) - it.index
    if len ≥ 0 then len else 0
  else 0

/-- `listiter_setstate(self, state)`, listobject.c:4132-4147. -/
def listIterSetstate (it : ListIter) (l : List α) (state : Int) : Py ListIter := do
  let index ← PyLean.Sequences.asSsize state
  if it.alive then
    let index := if index < -1 then -1 else if index > l.length then (l.length : Int) else index
    .ok { it with index := index }
  else .ok it

/-- `list___reversed___impl`, listobject.c:4210-4224. -/
def listReversed (l : List α) : ListIter := ⟨(l.length : Int) - 1, true⟩

/-- `listreviter_next(self)`, listobject.c:4242-4265. -/
def listRevIterNext (it : ListIter) (l : List α) : Py (Option α × ListIter) :=
  if it.index < 0 then .ok (none, it)
  else if !it.alive then .error (cUB "listreviter_next on NULL it_seq")
  else
    match listGetItemRef l it.index with
    | some v => .ok (some v, { it with index := it.index - 1 })
    | none => .ok (none, ⟨-1, false⟩)

/-- `listreviter_len(self)`, listobject.c:4267-4276. -/
def listRevIterLen (it : ListIter) (l : List α) : Int :=
  let len := it.index + 1
  if !it.alive ∨ (l.length : Int) < len then 0 else len

/-- `listreviter_setstate(self, state)`, listobject.c:4284-4299. -/
def listRevIterSetstate (it : ListIter) (l : List α) (state : Int) : Py ListIter := do
  let index ← PyLean.Sequences.asSsize state
  if it.alive then
    let top := (l.length : Int) - 1
    let index := if index < -1 then -1 else if index > top then top else index
    .ok { it with index := index }
  else .ok it

/-- `listiter_reduce_general(_it, forward)`, listobject.c:4303-4335, as `(args,
state)`: `iter(seq)` or `reversed(seq)` with the index, or an empty list. -/
def listIterReduce (it : ListIter) (l : List α) : List α × Option Int :=
  if it.index ≥ 0 then (l, some it.index) else ([], none)

/-! ## C API -/

/-- `PyList_New(size)`, listobject.c:261-300: `NULL` slots, exact allocation. -/
def pyListNew (size : Int) : Py (LObj (Option α)) :=
  if size < 0 then .error systemError
  else if size ≤ 0 then .ok LObj.empty
  else if size > ssizeMax / 8 then .error memoryError
  else .ok { items := List.replicate size.toNat none, allocated := size, hasItems := true }

/-- `_PyList_FromStackRefStealOnSuccess(src, n)`, listobject.c:3312-3330: a list
display. -/
def listFromStack (src : List α) : LObj α := LObj.prealloc src

/-- `PyList_Size(op)`, listobject.c:329-339. `none` is a non-list. -/
def pyListSize (op : Option (List α)) : Py Int :=
  match op with
  | some l => .ok l.length
  | none => .error systemError

/-- `PyList_GetItem(op, i)`, listobject.c:411-424. -/
def pyListGetItem (op : Option (List α)) (i : Int) : Py α :=
  match op with
  | none => .error systemError
  | some l =>
    if !validIndex i l.length then .error (.indexError "list index out of range")
    else match slot l i with
      | some v => .ok v
      | none => .error (cUB "read outside the items array")

/-- `PyList_GetItemRef(op, i)`, listobject.c:426-440. -/
def pyListGetItemRef (op : Option (List α)) (i : Int) : Py α :=
  match op with
  | none => .error (.typeError "expected a list")
  | some l =>
    match listGetItemRef l i with
    | some v => .ok v
    | none => .error (.indexError "list index out of range")

/-- `PyList_SetItem(op, i, newitem)`, listobject.c:474-500. -/
def pyListSetItem (op : Option (LObj α)) (i : Int) (v : α) : Py (LObj α) :=
  match op with
  | none => .error systemError
  | some self =>
    if !validIndex i self.items.length then
      .error (.indexError "list assignment index out of range")
    else .ok { self with items := self.items.set i.toNat v }

/-- `PyList_Insert(op, where, newitem)`, listobject.c:530-543. -/
def pyListInsert (op : Option (LObj α)) (where_ : Int) (v : Option α) : Py (LObj α) :=
  match op with
  | none => .error systemError
  | some self => ins1 self where_ v

/-- `PyList_Append(op, newitem)`, listobject.c:559-571. -/
def pyListAppend (op : Option (LObj α)) (v : Option α) : Py (LObj α) :=
  match op, v with
  | some self, some v => listAppend self v
  | _, _ => .error systemError

/-- `PyList_GetSlice(a, ilow, ihigh)`, listobject.c:764-788. -/
def pyListGetSlice (op : Option (List α)) (ilow ihigh : Int) : Py (LObj α) :=
  match op with
  | none => .error systemError
  | some a =>
    let n : Int := a.length
    let ilow := if ilow < 0 then 0 else if ilow > n then n else ilow
    let ihigh := if ihigh < ilow then ilow else if ihigh > n then n else ihigh
    .ok (listSliceLH a ilow ihigh)

/-- `PyList_SetSlice(a, ilow, ihigh, v)`, listobject.c:1091-1099, with `list_ass_slice`,
:1061-1089. `v` is `none` for `NULL`, `some items` for a sequence; `isSelf` says `v`
is `a` itself, for which a private copy is made first. -/
def pyListSetSlice (op : Option (LObj α)) (ilow ihigh : Int) (v : Option (List α)) (isSelf : Bool) :
    Py (LObj α) :=
  match op with
  | none => .error systemError
  | some a => listAssSlice a ilow ihigh (if isSelf then some a.items else v)

/-- `PyList_Clear(self)`, listobject.c:1570-1581. -/
def pyListClear (op : Option (LObj α)) : Py (LObj α) :=
  match op with
  | none => .error systemError
  | some a => .ok (listClear a)

/-- `PyList_Reverse(v)`, listobject.c:3263-3278. -/
def pyListReverse (op : Option (LObj α)) : Py (LObj α) :=
  match op with
  | none => .error systemError
  | some a => .ok (listReverse a)

/-- `PyList_AsTuple(v)`, listobject.c:3280-3293. -/
def pyListAsTuple (mayTrack : α → Bool) (op : Option (List α)) : Py (TRes α) :=
  match op with
  | none => .error systemError
  | some l => tupleFromArray mayTrack l

/-- `PyList_Extend(self, iterable)`, listobject.c:1559-1567. -/
def pyListExtend (op : Option (LObj α)) (arg : ExtArg α) : LRes α × Option Unit :=
  match op with
  | none => ((LObj.empty, some systemError), none)
  | some a => (listExtend a arg, some ())

/-- `_PyList_AsTupleAndClear(self)`, listobject.c:3295-3310, for `PySequence_Tuple`:
the items move into a tuple, always tracked, and the list ends empty, with its array. -/
def listAsTupleAndClear (self : LObj α) : Py (TRes α × LObj α) :=
  if !self.hasItems then .ok (.empty, self)
  else
    match tupleFromArraySteal self.items with
    | .ok r => .ok (r, { self with items := [] })
    | .error e => .error e

/-- The list while `list.sort` runs, listobject.c:2989-2994: size 0, no array,
`allocated == -1`. -/
def listDuringSort : LObj α := { items := [], allocated := -1, hasItems := false }

end PyLean.BytesObj.Seq
