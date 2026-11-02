import PyLean.BytesObj.Bytes.Ctor
import PyLean.Sequences.ListModel

/-!
`bytearray`, Objects/bytearrayobject.c. The object keeps the C struct's state:
`ob_alloc`, the size of the `bytes` object `ob_bytes_object`, `ob_start - ob_bytes` (`offset`),
`ob_exports` and the data.

* `data` is a `List Int` of byte values. `uninit` (-1) marks a byte `malloc` or
  `realloc` handed out and nobody wrote yet, so reads of uninitialised memory are
  visible in the model.
* `ob_alloc` is observable through `__alloc__()` and `__sizeof__()`, so the resize
  strategy of `bytearray_resize_lock_held` is modelled exactly (`baNewAlloc`).
* Critical sections are no-ops without free-threading, so each `foo` and its
  `foo_lock_held` are one function.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice sliceUnpack)

/-- A byte nobody wrote. Never a value of `bytes`. -/
def uninit : Int := -1

structure BA where
  data : List Int := []
  alloc : Int := 0
  offset : Int := 0
  exports : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- The bytes as `StrSearch` sees them. -/
def BA.seq (b : BA) : Seq := b.data.map Int.toNat

/-- `len(b)`. -/
def BA.size (b : BA) : Int := b.data.length

def seqData (s : Seq) : List Int := s.map (fun (c : Nat) => (c : Int))

/-- The buffer layout invariant: `ob_start + Py_SIZE` fits in `ob_alloc`, the bytes object's size;
its own terminator comes after. -/
def BA.WF (b : BA) : Prop :=
  0 ≤ b.offset ∧ b.offset + b.size ≤ b.alloc

instance (b : BA) : Decidable b.WF := by unfold BA.WF; infer_instance

/-- `_canresize`, bytearrayobject.c:127-136. -/
def canResize (b : BA) : Py Unit :=
  if b.exports > 0 then
    .error (bufferError "Existing exports of data: object cannot be re-sized")
  else .ok ()

/-- `PyByteArray_FromStringAndSize(bytes, size)`, bytearrayobject.c:168-206, on
`PyBytes_FromStringAndSize(NULL, size)`. `bytes` is `none` for `NULL`: the result is then
uninitialised. -/
def baFromStringAndSize (bytes : Option Seq) (size : Int) : Py BA :=
  if size < 0 then .error (systemError "Negative size passed to PyByteArray_FromStringAndSize")
  else
    match bytesSizeCheck size with
    | .error e => .error e
    | .ok () =>
      if size = 0 then .ok {}
      else
        let data := match bytes with
          | some s => seqData (s.take size.toNat)
          | none => List.replicate size.toNat uninit
        .ok { data, alloc := size }

/-- `bytearray_dealloc`, bytearrayobject.c:1277-1288: what it prints. `ob_exports` is set before
anything that can fail (:189), so it is the
count of exports, which a view keeps from reaching this. -/
def baDealloc (exports : Int) : List String :=
  if exports > 0 then ["SystemError: deallocated bytearray object has exported buffers"] else []

/-- The contents after a resize: the first `requested` bytes, then new bytes. -/
def resizedData (data : List Int) (requested : Int) : List Int :=
  data.take requested.toNat ++ List.replicate (requested.toNat - data.length) uninit

/-- `bytearray_resize_lock_held`, bytearrayobject.c:294-342, past the `_canresize`: the new
`ob_alloc` and offset. A resize to 0 drops the storage. -/
def baResizeAlloc (b : BA) (size : Int) : Py (Int × Int) :=
  if size = 0 then .ok (0, 0)
  else
    match baNewAlloc b.alloc b.offset size with
    | none => .ok (b.alloc, b.offset)
    | some alloc =>
      match baStorageCheck b.alloc alloc with
      | .error e => .error e
      | .ok () => .ok (alloc, 0)

/-- `bytearray_resize_lock_held`, bytearrayobject.c:263-343, with
`PyByteArray_Resize`, :345-353. New bytes are uninitialised. -/
def baResize (b : BA) (requested : Int) : Py BA := do
  if requested < 0 then
    throw (.valueError s!"Can only resize to positive sizes, got {requested}")
  if requested = b.size then return b
  canResize b
  let (alloc, offset) ← baResizeAlloc b requested
  return { b with data := resizedData b.data requested, alloc, offset }

/-- What a failed `baResize` leaves. `bytearray_resize_storage`, :236-258, has moved the data to the
start of the allocation by the time `_PyBytes_ResizeKeepOnError` fails, so `offset` is 0 for a failure
there; an earlier refusal changes nothing. -/
def baResizeLeft (b : BA) (requested : Int) : BA :=
  if requested < 0 ∨ requested = b.size ∨ b.exports > 0 ∨ requested = 0 then b
  else
    match baNewAlloc b.alloc b.offset requested with
    | none => b
    | some alloc => if alloc > baSizeMax then b else { b with offset := 0 }

/-- `memmove(buf + dst, buf + src, cnt)` on the logical buffer, which ends at the
terminator; `Sequences.memmove` checks the bounds (`cUB` on violation). -/
def baMove (mem : List Int) (dst src cnt : Int) : Py (List Int) := Sequences.memmove mem dst src cnt

/-- The tail move and copy of `bytearray_setslice_linear`, the `growth < 0`, `lo ≠ 0`
branch, bytearrayobject.c:627-636. Reads `mem` as it stands, with the terminator. -/
def setsliceShrinkMove (b : BA) (lo hi blen : Int) : Py BA := do
  let mem ← baMove b.data (lo + blen) hi (b.size - hi)
  return { b with data := mem }

/-- `memcpy(buf + lo, bytes, bytes_len)`, bytearrayobject.c:681-682. -/
def baCopyIn (b : BA) (lo : Int) (bytes : List Int) : BA :=
  { b with data := b.data.take lo.toNat ++ bytes ++ b.data.drop (lo + bytes.length).toNat }

/-- The resize of the `lo == 0` shrink, bytearrayobject.c:637-638. `ob_start` has advanced already,
but the size field still has the old value, so the resize is not the "same size" no-op; `b.data` is
already the new contents. -/
def baResizeNoSize (b : BA) (requested : Int) : Py BA := do
  canResize b
  let (alloc, offset) ← baResizeAlloc b requested
  return { b with alloc, offset }

/-- `growth < 0`, `lo == 0`: shrink the buffer by advancing its logical start,
bytearrayobject.c:617-626 and :637. -/
def baShrinkStart (self : BA) (growth : Int) (bytes : List Int) : Py BA := do
  let s := { self with offset := self.offset - growth, data := self.data.drop (-growth).toNat }
  let r ← baResizeNoSize s s.size
  return baCopyIn r 0 bytes

/-- What the shrink of `baShrinkStart` leaves when `_PyBytes_ResizeKeepOnError` fails in
`bytearray_resize_storage`, which `mallocFails` cannot express for a shrink. `none` for the sizes that
do not reach it. By then `ob_start == ob_bytes` (:246), and the failure path of
`bytearray_setslice_linear` subtracts the shrink again (:649), so `ob_start` is before the buffer and
`Py_SIZE` is the old size. -/
def baShrinkStartFailure (self : BA) (growth : Int) : Option BA :=
  let offset := self.offset - growth
  let size := self.size + growth
  if size = 0 then none
  else
    match baNewAlloc self.alloc offset size with
    | none => none
    | some _ => some { self with offset := 0 + growth }

/-- `growth < 0`, `lo != 0`: `memmove` the tail down, then resize,
bytearrayobject.c:627-638. -/
def baShrinkMove (self : BA) (lo hi growth : Int) (bytes : List Int) : Py BA := do
  let blen : Int := bytes.length
  let s ← setsliceShrinkMove self lo hi blen
  let r ← baResize s (self.size + growth)
  return baCopyIn r lo bytes

/-- `growth > 0`: resize, then make the place for the additional bytes,
bytearrayobject.c:659-679. -/
def baGrow (self : BA) (lo hi growth : Int) (bytes : List Int) : Py BA := do
  let blen : Int := bytes.length
  if self.size > baSizeMax - growth then throw memoryError
  let r ← baResize self (self.size + growth)
  let mem ← baMove r.data (lo + blen) hi (r.size - lo - blen)
  return baCopyIn { r with data := mem } lo bytes

/-- `bytearray_setslice_linear`, bytearrayobject.c:601-684. `mallocFails` is a size limit, so the
`realloc` to a smaller size at :637 does not fail here; `baShrinkStartFails` states what a real
failure there leaves. -/
def baSetsliceLinear (self : BA) (lo hi : Int) (bytes : List Int) : Py BA :=
  let growth := (bytes.length : Int) - (hi - lo)
  if growth < 0 then
    match canResize self with
    | .error e => .error e
    | .ok () =>
      if lo = 0 then baShrinkStart self growth bytes
      else baShrinkMove self lo hi growth bytes
  else if growth > 0 then baGrow self lo hi growth bytes
  else .ok (baCopyIn self lo bytes)

/-- A value of `bytearray_setslice`: `none` is NULL; `mutate` is what the value's
`__buffer__` does to `self` while `PyObject_GetBuffer` runs. -/
structure SetVal where
  bytes : Seq
  mutate : BA → Py BA := .ok
  deriving Inhabited

/-- `bytearray_setslice`, bytearrayobject.c:686-738. `lo` and `hi` were computed by
the caller; the value's `__buffer__` runs between that and the clamps, which cover both bounds
(gh-153578). -/
def baSetslice (self : BA) (lo hi : Int) (values : Option SetVal) : Py BA := do
  let (self, bytes) ← match values with
    | none => pure (self, [])
    | some v => do
      let self ← v.mutate self
      pure (self, seqData v.bytes)
  let lo := if lo < 0 then 0 else if lo > self.size then self.size else lo
  let hi := if hi < lo then lo else hi
  let hi := if hi > self.size then self.size else hi
  baSetsliceLinear self lo hi bytes

/-- `bytearray.extend` with a buffer argument, bytearrayobject.c:2254-2260:
`bytearray_setslice(self, size, size, x)`. If the argument's `__buffer__` shrinks
`self`, the clamp puts `lo` at the new end. -/
def baExtendBuffer (self : BA) (v : SetVal) : Py BA :=
  baSetslice self self.size self.size (some v)

/-- `_getbytevalue`, bytearrayobject.c:25-44. -/
def getByteValue (arg : Obj) : Py Nat :=
  match arg.index? with
  | none => .error (notInteger arg)
  | some (.error e) => .error e
  | some (.ok v) =>
    if v < 0 ∨ v ≥ 256 then .error (.valueError "byte must be in range(0, 256)")
    else .ok v.toNat

/-- `bytearray_getbuffer` and `bytearray_getbuffer_lock_held`,
bytearrayobject.c:69-96. -/
def baGetBuffer (b : BA) : BA := { b with exports := b.exports + 1 }

/-- `bytearray_releasebuffer`, bytearrayobject.c:98-106. -/
def baReleaseBuffer (b : BA) : BA := { b with exports := b.exports - 1 }

/-- `_bytearray_with_buffer`, bytearrayobject.c:112-125: `op` runs with `ob_exports`
raised, so a callback cannot resize `self`. -/
def withBuffer {α : Type} (self : BA) (op : BA → Py α) : Py α × BA :=
  let inner := baGetBuffer self
  (op inner, baReleaseBuffer inner)

/-! ## Read-only methods

Each one runs the shared `bytes` code. Those that can call back into Python raise
`ob_exports` around it (`_bytearray_with_buffer`, or by hand in `split`, `rsplit`,
`join`, `hex`, `%` and `__contains__`). The rest take the critical section only. -/

/-- `bytearray_find_impl`, :1336-1342, and `rfind`, `index`, `rindex`, `count`,
`startswith`, `endswith`, `__contains__`: the operation on the contents, with
`ob_exports` raised meanwhile. -/
def baRead {α : Type} (self : BA) (op : Seq → Py α) : Py α × BA :=
  withBuffer self (fun inner => op inner.seq)

/-! ## Subscript -/

/-- `bytearray_getitem`, bytearrayobject.c:508-528. -/
def baGetItemRaw (b : BA) (i : Int) : Py Int :=
  if i < 0 ∨ i ≥ b.size then .error (.indexError "bytearray index out of range")
  else .ok (b.data.getD i.toNat 0)

/-- `bytearray_subscript` for an index, bytearrayobject.c:535-549. -/
def baGetItem (b : BA) (i : Int) : Py Int := do
  let i ← Sequences.subIndex i
  let i := if i < 0 then i + b.size else i
  baGetItemRaw b i

/-- `bytearray_subscript` for a slice, bytearrayobject.c:550-581: a new bytearray. -/
def baGetSlice (b : BA) (sl : Slice) : Py Seq := do
  let (start, stop, step) ← sliceUnpack sl
  let (start, _, len) := RangeSlice.adjustIndices b.size start stop step
  if len ≤ 0 then return []
  if step = 1 then return (b.seq.drop start.toNat).take len.toNat
  return (slicePositions start step len.toNat).map (fun p => b.seq.getD p.toNat 0)

/-- `bytearray_setitem` (`sq_ass_item`), bytearrayobject.c:740-779. -/
def baSetItemRaw (self : BA) (i : Int) (value : Option Obj) : Py BA := do
  let ival ← match value with
    | some v => some <$> getByteValue v
    | none => pure none
  let i := if i < 0 then i + self.size else i
  if i < 0 ∨ i ≥ self.size then throw (.indexError "bytearray index out of range")
  match ival with
  | none => baSetslice self i (i + 1) none
  | some v => return { self with data := self.data.set i.toNat (v : Int) }

/-- `bytearray_ass_subscript` for an index and a value, and for `del b[i]`,
bytearrayobject.c:791-827, with the deletion continuing as a one-byte slice. -/
def baAssIndex (self : BA) (i : Int) (value : Option Obj) : Py BA := do
  let i ← Sequences.subIndex i
  let ival ← match value with
    | some v => some <$> getByteValue v
    | none => pure none
  let i := if i < 0 then i + self.size else i
  if i < 0 ∨ i ≥ self.size then throw (.indexError "bytearray index out of range")
  match ival with
  | none => baSetsliceLinear self i (i + 1) []
  | some v => return { self with data := self.data.set i.toNat (v : Int) }

/-- The right-hand sides of a slice assignment: bytearrayobject.c:844-868. -/
def assValue (self : BA) (values : Option Obj) : Py (Option Seq) :=
  match values with
  | none => .ok none
  | some (.bytearray s) => .ok (some s)
  | some v =>
    if v.isNumber then
      .error (.typeError "can assign only bytes, buffers, or iterables of ints in range(0, 256)")
    else match v with
      | .str _ =>
        .error (.typeError "can assign only bytes, buffers, or iterables of ints in range(0, 256)")
      | _ =>
        let _ := self
        match baFromObjectItems v with
        | .ok s => .ok (some s)
        | .error e => .error e
where
  /-- `PyByteArray_FromObject(values)` on a right-hand side. -/
  baFromObjectItems (v : Obj) : Py Seq :=
    match v.buffer? with
    | some b => .ok b
    | none => do
      let items ← getIterOr (.typeError s!"cannot convert '{v.typeName}' object to bytearray") v
      let vals ← items.mapM getByteValue
      iterFinish v
      return vals

/-- The extended-slice part of `bytearray_ass_subscript_lock_held`,
bytearrayobject.c:880-939, for `step ≠ 1`. `needed == 0` is the deletion branch, also
for an assignment of an empty value (`bugs/sequences-array-extended-slice-empty-deletes.yaml`),
and `_canresize` comes before the `slicelen == 0` return. The loops are the ones of
`Sequences.delExtended` and `Sequences.storeLoop`. -/
def baAssExtended (self : BA) (start stop step slicelen : Int) (bytes : List Int) : Py BA := do
  let needed : Int := bytes.length
  if needed = 0 then
    canResize self
    if slicelen = 0 then return self
    let mem ← Sequences.delExtended self.data start stop step slicelen
    let target := self.size - slicelen
    let r ← baResize self target
    return { r with data := mem }
  else
    if needed ≠ slicelen then
      throw (.valueError s!"attempt to assign bytes of size {needed} to extended slice of size {slicelen}")
    return { self with data := Sequences.storeLoop self.data start step bytes }

/-- `b[s] = v` and `del b[s]` for a slice `s`: `bytearray_ass_subscript_lock_held`,
bytearrayobject.c:828-940, and `bytearray_ass_subscript`, :942-957. `values == self`
is a copy (`self` is passed by value here). -/
def baAssSlice (self : BA) (sl : Slice) (values : Option Obj) : Py BA := do
  let (start, stop, step) ← sliceUnpack sl
  let (start, stop, slicelen) := RangeSlice.adjustIndices self.size start stop step
  let bytes ← assValue self values
  -- Make sure b[5:2] = ... inserts before 5, not before 2.
  let stop := if (step < 0 ∧ start < stop) ∨ (step > 0 ∧ start > stop) then start else stop
  let bytes := seqData (bytes.getD [])
  if step = 1 then baSetsliceLinear self start stop bytes
  else baAssExtended self start stop step slicelen bytes

/-! ## Concatenation and repetition -/

/-- `PyByteArray_Concat`, bytearrayobject.c:355-390. -/
def baConcat (a b : Obj) : Py BA :=
  match a.buffer?, b.buffer? with
  | some va, some vb =>
    if (va.length : Int) > baSizeMax - vb.length then .error memoryError
    else baFromStringAndSize (some (va ++ vb)) (va.length + vb.length)
  | _, _ => .error (.typeError s!"can't concat {b.typeName} to {a.typeName}")

/-- `bytearray_iconcat`, bytearrayobject.c:400-437. -/
def baIConcat (self : BA) (other : Obj) : Py BA := do
  let vo ← match other.buffer? with
    | some v => pure v
    | none => throw (.typeError s!"can't concat {other.typeName} to bytearray")
  let size := self.size
  if size > baSizeMax - vo.length then throw memoryError
  let r ← baResize self (size + vo.length)
  return { r with data := r.data.take size.toNat ++ seqData vo }

/-- `bytearray_repeat`, bytearrayobject.c:439-469. -/
def baRepeat (self : BA) (count : Int) : Py BA := do
  let count := if count < 0 then 0 else count
  let mysize := self.size
  if count > 0 ∧ mysize > Int.tdiv baSizeMax count then throw memoryError
  let size := mysize * count
  let r ← baFromStringAndSize none size
  if size ≠ 0 then return { r with data := seqData (bytesRepeatFill size.toNat self.seq) }
  return r

/-- `bytearray_irepeat`, bytearrayobject.c:471-506. -/
def baIRepeat (self : BA) (count : Int) : Py BA := do
  let count := if count < 0 then 0 else count
  if count = 1 then return self
  let mysize := self.size
  if count > 0 ∧ mysize > Int.tdiv baSizeMax count then throw memoryError
  let size := mysize * count
  let r ← baResize self size
  return { r with data := seqData (bytesRepeatFill size.toNat self.seq) }

/-! ## Mutating methods -/

/-- `PyNumber_AsSsize_t(n, PyExc_IndexError)` on an index object of value `v`. -/
def takeCount (n : Obj) (v : Int) : Py Int :=
  if ssizeMin ≤ v ∧ v ≤ ssizeMax then .ok v
  else .error (.indexError s!"cannot fit '{n.typeName}' into an index-sized integer")

/-- `bytearray.take_bytes` past the conversion of `n`, bytearrayobject.c:1650-1688: the bytes taken and
the object left. The smaller part is copied: a small `to_take` moves `ob_start`, a large one leaves
the rest in a new bytes object and hands over the old one. -/
def baTakeCore (self : BA) (toTake : Int) : Py (Seq × BA) := do
  let size := self.size
  if toTake < 0 ∨ toTake > size then
    throw (.indexError s!"can't take {toTake} bytes outside size {size}")
  canResize self
  if toTake = 0 ∨ size = 0 then return ([], self)
  let remaining := size - toTake
  let taken := (self.data.take toTake.toNat).map Int.toNat
  let rest := self.data.drop toTake.toNat
  if toTake < remaining then
    bytesSizeCheck toTake
    return (taken, { self with data := rest, offset := self.offset + toTake })
  bytesSizeCheck remaining
  bytesResizeCheck self.alloc toTake
  return (taken, { self with data := rest, alloc := remaining, offset := 0 })

/-- `bytearray.take_bytes(n)`, bytearrayobject.c:1614-1688. -/
def baTakeBytes (self : BA) (n : Obj) : Py (Seq × BA) := do
  let toTake : Int ← match n with
    | .none => pure self.size
    | _ =>
      match n.index? with
      | some (.ok v) =>
        let t ← takeCount n v
        pure (if t < 0 then t + self.size else t)
      | some (.error e) => throw e
      | none => throw (.typeError "n must be an integer or None")
  baTakeCore self toTake

/-- `bytearray.clear()`, bytearrayobject.c:1366-1373. -/
def baClear (self : BA) : Py BA := baResize self 0

/-- `bytearray.copy()`, bytearrayobject.c:1382-1388. -/
def baCopy (self : BA) : Py BA := baFromStringAndSize (some self.seq) self.size

/-- `bytearray.resize(size)`, bytearrayobject.c:1588-1602: new bytes are zero. -/
def baResizeMethod (self : BA) (size : Int) : Py BA := do
  let size ← Sequences.asSsize size
  let start := self.size
  let r ← baResize self size
  if size > start then
    return { r with data := r.data.take start.toNat ++ List.replicate (size - start).toNat 0 }
  return r

/-- `bytearray.reverse()`, bytearrayobject.c:2033-2050: the swap loop. -/
def baReverse (self : BA) : BA := { self with data := self.data.reverse }

/-- `bytearray.insert(index, item)`, bytearrayobject.c:2074-2096. -/
def baInsert (self : BA) (index : Int) (item : Obj) : Py BA := do
  let index ← Sequences.asSsize index
  let item ← getByteValue item
  let n := self.size
  let r ← baResize self (n + 1)
  -- the same clamps as `ins1`, listobject.c:515-522
  return { r with data := Sequences.insAt self.data (Sequences.ins1Pos n index).toNat (item : Int) }

/-- `bytearray.append(item)`, bytearrayobject.c:2189-2201. -/
def baAppend (self : BA) (item : Obj) : Py BA := do
  let item ← getByteValue item
  let n := self.size
  let r ← baResize self (n + 1)
  return { r with data := self.data ++ [(item : Int)] }

/-- `bytearray.pop(index)`, bytearrayobject.c:2359-2388. -/
def baPop (self : BA) (index : Option Int) : Py (Int × BA) := do
  let index ← Sequences.popArg index
  let n := self.size
  if n = 0 then throw (.indexError "pop from empty bytearray")
  let index := if index < 0 then index + n else index
  if index < 0 ∨ index ≥ n then throw (.indexError "pop index out of range")
  canResize self
  let value := self.data.getD index.toNat 0
  let r ← baResize self (n - 1)
  return (value, { r with data := self.data.eraseIdx index.toNat })

/-- `bytearray.remove(value)`, bytearrayobject.c:2401-2421. -/
def baRemove (self : BA) (value : Obj) : Py BA := do
  let value ← getByteValue value
  let n := self.size
  let target : Int := value
  match self.data.findIdx? (· == target) with
  | none => throw (.valueError "value not found in bytearray")
  | some whereI =>
    canResize self
    let r ← baResize self (n - 1)
    return { r with data := self.data.eraseIdx whereI }

/-- What `bytearray.__init__`'s and `extend`'s loop gets from an iterable. -/
def baItems (o : Obj) : Option (List Obj) := iterItems? o

/-- The iterator loop of `bytearray___init___impl`, bytearrayobject.c:1142-1172:
each byte extends the object in place when the allocation has room, else through
`PyByteArray_Resize`. -/
def baInitLoop (self : BA) : List Obj → Py BA
  | [] => .ok self
  | item :: rest =>
    match getByteValue item with
    | .error e => .error e
    | .ok value =>
      let grown : Py BA :=
        if self.size + 1 < self.alloc then .ok self
        else baResize self (self.size + 1)
      match grown with
      | .error e => .error e
      | .ok r => baInitLoop { r with data := self.data ++ [(value : Int)] } rest

/-- The result of `__init__`: the object as it is left, and the exception if any. -/
abbrev InitRes := BA × Option PyExc

/-- `PyByteArray_Resize(self, 0)` on an object nothing exports, whatever its size. -/
def baReset (b : BA) : BA := { b with data := [], alloc := 0, offset := 0 }

/-- The exact-list and exact-tuple fast path, bytearrayobject.c:1101-1128. The object was resized to
`size` first; a bad value resets it to empty (:1121-1122). Returns `.inr` to go to the slow path
(a non-`int` item). -/
def baInitFast (self : BA) (items : List Obj) : InitRes ⊕ Unit :=
  let rec go (i : Nat) (cur : BA) : List Obj → InitRes ⊕ Unit
    | [] => .inl (cur, none)
    | item :: rest =>
      match item with
      | .int v =>
        match getByteValue (.int v) with
        | .error e => .inl (baReset cur, some e)
        | .ok value => go (i + 1) { cur with data := cur.data.set i (value : Int) } rest
      | _ => .inr ()
  go 0 self items

/-- `bytearray___init___impl`, bytearrayobject.c:982-1182. Returns the object as it
is afterwards (the C code mutates `self` before it can fail) and the exception. -/
def baInit (self : BA) (arg : Option Obj) (encoding errors : Option String) : InitRes :=
  match (do canResize self; baResize self 0) with
  | .error e => (self, some e)
  | .ok self =>
    let fail (e : PyExc) : InitRes := (self, some e)
    let ofPy (r : Py BA) : InitRes :=
      match r with
      | .ok b => (b, none)
      | .error e => fail e
    let slow (self : BA) (o : Obj) : InitRes :=
      match getIterOr (.typeError s!"cannot convert '{o.typeName}' object to bytearray") o with
      | .error e => (self, some e)
      | .ok items =>
        let rec run (cur : BA) : List Obj → InitRes
          | [] =>
            match iterFinish o with
            | .ok () => (cur, none)
            | .error e => (cur, some e)
          | item :: rest =>
            match baInitLoop cur [item] with
            | .ok next => run next rest
            | .error e => (cur, some e)
        run self items
    match arg with
    | none =>
      if encoding.isSome then fail (.typeError "encoding without a string argument")
      else if errors.isSome then fail (.typeError "errors without a string argument")
      else (self, none)
    | some (.str cs) =>
      match encoding with
      | none => fail (.typeError "string argument without an encoding")
      | some enc =>
        match encodeStr cs enc with
        | .error e => fail e
        -- taking over a unique `encoded` (:1031-1038) and `bytearray_iconcat` (:1040) leave the
        -- same object here, because `self` is empty
        | .ok encoded => ofPy (baIConcat self (.bytes encoded))
    | some o =>
      if encoding.isSome then fail (.typeError "encoding without a string argument")
      else if errors.isSome then fail (.typeError "errors without a string argument")
      else
        let notCount : Unit → InitRes := fun _ =>
          match o.buffer? with
          | some view =>
            match baResize self view.length with
            | .error e => fail e
            | .ok r => (({ r with data := seqData view } : BA), none)
          | none =>
            match o with
            | .list items | .tuple items =>
              match baResize self items.length with
              | .error e => fail e
              | .ok r =>
                match baInitFast r items with
                | .inl res => res
                | .inr () =>
                  -- Resize to 0 and go through slowpath
                  match (if r.size ≠ 0 then baResize r 0 else .ok r) with
                  | .error e => (r, some e)
                  | .ok r0 => slow r0 o
            | _ => slow self o
        match o.index? with
        | some (.ok v) =>
          match countOf o v with
          | .error e => fail e
          | .ok count =>
            if count < 0 then fail (.valueError "negative count")
            else if count > 0 then
              match baResize self count with
              | .error e => fail e
              | .ok r => (({ r with data := List.replicate count.toNat 0 } : BA), none)
            else (self, none)
        | some (.error e) => if isTypeError e then notCount () else fail e
        | none => notCount ()

/-- `bytearray_new`, bytearrayobject.c:959-971: empty, on the empty bytes object, with no exports. -/
def baNewObject : BA := { data := [], alloc := 0, offset := 0, exports := 0 }

/-- `bytearray(x)` for a fresh object. -/
def baNew (arg : Option Obj) (encoding errors : Option String) : Py BA :=
  match baInit baNewObject arg encoding errors with
  | (b, none) => .ok b
  | (_, some e) => .error e

/-- `bytearray.extend(iterable_of_ints)` for a non-buffer argument,
bytearrayobject.c:2262-2342: the items go to a temporary, which is then appended. -/
def baExtend (self : BA) (o : Obj) : Py BA := do
  match o.buffer? with
  | some b => baExtendBuffer self { bytes := b }
  | none =>
    let items ← getIterOr (.typeError s!"can't extend bytearray with {o.typeName}") o
    let bufSize ← lengthHint o 32
    bytesSizeCheck bufSize
    let isStr : Bool := match o with | .str _ => true | _ => false
    let vals ← (items.mapM getByteValue).mapError fun e =>
      if isStr = true ∧ isTypeError e = true then .typeError "expected iterable of integers; got: 'str'"
      else e
    iterFinish o
    let r := baSetsliceLinear self self.size self.size (seqData vals)
    r

/-! ## Iterator, bytearrayobject.c:3015-3195 -/

/-- `bytesiterobject`: `index = -1` is exhausted. `bytearrayiter_setstate` keeps the
sign of a `-1`, unlike the bytes iterator's clamp to 0. -/
structure BAIter where
  index : Int := 0
  deriving Repr, DecidableEq, Inhabited

/-- `bytearrayiter_next`, bytearrayobject.c:3042-3074, against the current object. -/
def baIterNext (seq : BA) (it : BAIter) : Option Int × BAIter :=
  if it.index < 0 then (none, it)
  else if it.index < seq.size then (some (seq.data.getD it.index.toNat 0), { index := it.index + 1 })
  else (none, { index := -1 })

/-- `bytearrayiter_length_hint`, bytearrayobject.c:3076-3089. -/
def baIterLen (seq : BA) (it : BAIter) : Int :=
  if it.index ≥ 0 then
    let len := seq.size - it.index
    if len < 0 then 0 else len
  else 0

/-- `bytearrayiter_reduce`, bytearrayobject.c:3094-3108. -/
def baIterReduce (it : BAIter) : Option Int :=
  if it.index ≥ 0 then some it.index else none

/-- `bytearrayiter_setstate`, bytearrayobject.c:3110-3132. -/
def baIterSetstate (seq : BA) (it : BAIter) (state : Int) : Py BAIter := do
  let index ← Sequences.asSsize state
  if it.index ≥ 0 then
    let index := if index < -1 then -1 else if index > seq.size then seq.size else index
    return { index }
  return it

/-! ## Comparison, repr, reduce -/

/-- `bytearray_richcompare`, bytearrayobject.c:1222-1275: `none` is `NotImplemented`. -/
def baRichcompare (a b : Obj) (op : CmpOp) : Option Bool :=
  match a.buffer?, b.buffer? with
  | some x, some y =>
    if x.length ≠ y.length ∧ (op = .eq ∨ op = .ne) then some (decide (op = .ne))
    else
      let cmp := memcmp (min x.length y.length) x y
      if cmp ≠ 0 then some (richResult op cmp 0)
      else some (richResult op x.length y.length)
  | _, _ => none

/-- `bytearray.__reduce_ex__(proto)` for an exact bytearray with no state:
`_common_reduce`, bytearrayobject.c:2749-2773. The argument tuple is `()`,
`(latin1_text, "latin-1")`, or `(bytes,)`. -/
inductive ReduceArgs where
  | empty
  | text (cs : Seq)
  | bin (b : Seq)
  deriving Repr, DecidableEq

def baReduce (s : Seq) (proto : Int) : ReduceArgs :=
  if s.isEmpty then .empty
  else if proto < 3 then .text s
  else .bin s

/-- What a buffer request on `bytes` exports: the contents, read-only
(`bytes_buffer_getbuffer`, bytesobject.c:1792-1798). -/
def bytesBufferInfo (s : Seq) : Seq × Bool := (s, true)

/-- What a buffer request on `bytearray` exports, and the object afterwards:
`bytearray_getbuffer`, bytearrayobject.c:69-96, writable. -/
def baBufferInfo (b : BA) : (Seq × Bool) × BA := ((b.seq, false), baGetBuffer b)

/-- `bytearray.__alloc__()`, bytearrayobject.c:2605-2612. -/
def baAllocMethod (self : BA) : Int := if self.alloc > 0 then self.alloc + bytesObjectSize else 0

/-- `sizeof(PyByteArrayObject)` on LP64. -/
def baBasicSize : Int := 64

/-- `bytearray.__sizeof__()`, bytearrayobject.c:2813-2820. -/
def baSizeof (self : BA) : Int :=
  if self.alloc > 0 then baBasicSize + bytesObjectSize + self.alloc else baBasicSize

end PyLean.BytesObj.Bytes
