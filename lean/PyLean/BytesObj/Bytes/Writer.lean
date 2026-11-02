import PyLean.BytesObj.Bytes.Obj

/-!
Object allocation and `PyBytesWriter`, Objects/bytesobject.c:91-183 and :3645-4099. The writer is
its bookkeeping; `size ≤ allocated` is the safety invariant.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- The `(size_t)size > PY_SSIZE_T_MAX - PyBytesObject_SIZE` check and the allocation of
`_PyBytes_FromSize`, bytesobject.c:91-121, with no list built: a bytes of size 0 is the empty
singleton, `bytes_get_empty`, :45-50. -/
def bytesSizeCheck (size : Int) : Py Unit :=
  if size = 0 then .ok ()
  else if size > ssizeMax - bytesObjectSize then
    .error (.overflowError "byte string is too large")
  else if mallocFails (bytesObjectSize + size) then .error memoryError
  else .ok ()

/-- `_PyBytes_FromSize`, bytesobject.c:91-121. -/
def bytesFromSize (size : Int) : Py Seq :=
  match bytesSizeCheck size with
  | .ok () => .ok (List.replicate size.toNat 0)
  | .error e => .error e

/-- `PyBytes_FromStringAndSize(str, size)`, bytesobject.c:123-149: `str` is the
data (`none` for `NULL`, an uninitialised result of `size` bytes, read as zeros
here because no caller exposes them). -/
def bytesFromStringAndSize (str : Option Seq) (size : Int) : Py Seq :=
  if size < 0 then .error (systemError "Negative size passed to PyBytes_FromStringAndSize")
  else match str with
    | some s => if size = 1 then .ok (s.take 1)
      else if size = 0 then .ok []
      else do
        let _ ← bytesFromSize size
        return s.take size.toNat
    | none => if size = 0 then .ok [] else bytesFromSize size

/-- `PyBytes_FromString(str)`, bytesobject.c:151-183: the bytes up to the first
NUL. -/
def bytesFromCString (s : Seq) : Seq := s.takeWhile (· != 0)

/-- `_PyBytes_ResizeKeepOnError`, bytesobject.c:3417-3471, with `bytes_resize_inplace`, :3358-3401,
and `_PyBytes_Resize`, :3474-3484, for a buffer of `oldsize` bytes: what can fail. The result is the
first `newsize` bytes, extended with bytes the caller fills. The copy for a shared or hashed object
and `bytes_resize_inplace` have the same two failures as `_PyBytes_FromSize`. -/
def bytesResizeCheck (oldsize newsize : Int) : Py Unit :=
  if newsize < 0 then .error (badInternalCall "../Objects/bytesobject.c:3424")
  else if oldsize = newsize then .ok ()
  else if oldsize = 0 then bytesSizeCheck newsize
  else if newsize = 0 then .ok ()
  else bytesSizeCheck newsize

/-- `PyByteArray_SIZE_MAX`, bytearrayobject.c:21. -/
def baSizeMax : Int := ssizeMax - bytesObjectSize

/-- The allocation strategy of `bytearray_resize_lock_held`, bytearrayobject.c:302-327, for a
`requested` other than 0 and the current size: `none` is the quick exit, `some a` a new storage of
`a` bytes. The double `alloc * 1.125` is exact below `2^49`, and larger allocations fail. -/
def baNewAlloc (alloc offset size : Int) : Option Int :=
  if size + offset ≤ alloc then
    if size < alloc / 2 then some size -- Major downsize; resize down to exact size
    else none -- Minor downsize; quick exit
  else if 8 * size ≤ 9 * alloc then
    some (size + size / 8 + (if size < 9 then 3 else 6)) -- Moderate upsize
  else some size -- Major upsize; resize up to exact size

/-- The `alloc > PyByteArray_SIZE_MAX` test, bytearrayobject.c:328-331, and the
`_PyBytes_ResizeKeepOnError` of `bytearray_resize_storage`, :249, from `alloc` to `newAlloc`. -/
def baStorageCheck (alloc newAlloc : Int) : Py Unit :=
  if newAlloc > baSizeMax then .error memoryError else bytesResizeCheck alloc newAlloc

/-- `PyBytesWriter`, Include/internal/pycore_bytesobject.h:96-102. `obj` is `writer->obj`: `none` for
`NULL`, the small buffer, else the object's size and its storage size, which differ for a bytearray.
The bytes written are kept by the caller, so only the errors and the capacity logic are here. -/
structure Writer where
  obj : Option (Int × Int) := none
  size : Int := 0
  useBytearray : Bool := false
  overallocate : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `sizeof(writer->small_buffer)`. -/
def smallBufferSize : Int := 256

/-- `OVERALLOCATE_FACTOR`, bytesobject.c:3722-3728, not Windows. -/
def overallocateFactor : Int := 4

/-- `byteswriter_allocated`, bytesobject.c:3680-3692. -/
def writerAllocated (w : Writer) : Int :=
  match w.obj with
  | none => smallBufferSize
  | some (n, _) => n

/-- The allocation of `byteswriter_resize`, bytesobject.c:3747-3787, to a `size` past the allocated
one: `PyByteArray_Resize`, `_PyBytes_ResizeKeepOnError`, or a first object. -/
def writerObjResize (w : Writer) (size : Int) : Py (Int × Int) :=
  match w.obj with
  | some (n, a) =>
    if w.useBytearray then
      match baNewAlloc a 0 size with
      | none => .ok (size, a)
      | some a' =>
        match baStorageCheck a a' with
        | .ok () => .ok (size, a')
        | .error e => .error e
    else
      match bytesResizeCheck n size with
      | .ok () => .ok (size, size)
      | .error e => .error e
  | none =>
    match bytesSizeCheck size with
    | .ok () => .ok (size, size)
    | .error e => .error e

/-- `byteswriter_resize(writer, size, resize)`, bytesobject.c:3730-3798. -/
def writerResizeRaw (w : Writer) (size : Int) (resize : Bool) : Py Writer :=
  if size ≤ writerAllocated w then .ok w
  else
    let size :=
      if resize ∧ w.overallocate ∧ size ≤ ssizeMax - size / overallocateFactor then
        size + size / overallocateFactor
      else size
    match writerObjResize w size with
    | .ok obj => .ok { w with obj := some obj }
    | .error e => .error e

/-- `byteswriter_create(size, use_bytearray)`, bytesobject.c:3801-3835, and its two wrappers
`PyBytesWriter_Create`, :3837-3841, and `_PyBytesWriter_CreateByteArray`, :3843-3847. -/
def writerCreate (size : Int) (useBytearray : Bool) : Py Writer :=
  if size < 0 then .error (.valueError "size must be >= 0")
  else
    let w : Writer := { useBytearray, overallocate := !useBytearray }
    if size ≥ 1 then
      match writerResizeRaw w size false with
      | .ok w => .ok { w with size }
      | .error e => .error e
    else .ok w

/-- `PyBytesWriter_Resize(writer, size)`, bytesobject.c:3958-3978. -/
def writerResize (w : Writer) (size : Int) : Py Writer :=
  if size < 0 then .error (.valueError "size must be >= 0")
  else if w.size < size then
    match writerResizeRaw w size true with
    | .ok w => .ok { w with size }
    | .error e => .error e
  else .ok { w with size }

/-- `PyBytesWriter_Grow(writer, grow)`, bytesobject.c:3993-4023. -/
def writerGrow (w : Writer) (grow : Int) : Py Writer :=
  if grow = 0 then .ok w
  else if grow ≥ 0 ∧ grow > ssizeMax - w.size then .error memoryError
  else if grow < 0 ∧ w.size + grow < 0 then .error (.valueError "invalid size")
  else
    let size := w.size + grow
    match writerResizeRaw w size true with
    | .ok w => .ok { w with size }
    | .error e => .error e

/-- `PyBytesWriter_GrowAndUpdatePointer(writer, size, buf)`, bytesobject.c:4026-4035: `pos` is
`buf - data`, which does not move with the buffer. -/
def writerGrowAt (w : Writer) (grow pos : Int) : Py (Writer × Int) :=
  match writerGrow w grow with
  | .ok w => .ok (w, pos)
  | .error e => .error e

/-- `_PyBytesWriter_ResizeAndUpdatePointer(writer, size, data)`, bytesobject.c:3981-3990. -/
def writerResizeAt (w : Writer) (size pos : Int) : Py (Writer × Int) :=
  match writerResize w size with
  | .ok w => .ok (w, pos)
  | .error e => .error e

/-- `PyBytesWriter_WriteBytes(writer, bytes, size)`, bytesobject.c:4038-4060: a negative `size` is
`strlen(bytes)`. `out` is the data so far. -/
def writerWriteBytes (w : Writer) (out bytes : Seq) (size : Int) : Py (Writer × Seq) :=
  let data : Seq := if size < 0 then bytes.takeWhile (· != 0) else bytes.take size.toNat
  match writerGrow w data.length with
  | .ok w => .ok (w, out ++ data)
  | .error e => .error e

/-- `_PyBytesWriter_ResizeToAllocated`, bytesobject.c:4091-4099. -/
def writerResizeToAllocated (w : Writer) : Writer := { w with size := writerAllocated w }

/-- `PyBytesWriter_FinishWithSize(writer, size)`, bytesobject.c:3864-3923, without the data. The
resizes here go down from what was allocated, so they do not fail for a writer that got this far. -/
def writerFinishSize (w : Writer) (size : Int) : Py Unit :=
  if size < 0 then .error (.valueError "size must be positive")
  else if size > w.size then .error (.valueError "size larger than allocated size")
  else if size = 0 ∧ !w.useBytearray then .ok ()
  else
    match w.obj with
    | some (n, a) =>
      if w.useBytearray then
        if size ≠ n ∧ size ≠ 0 then
          match baNewAlloc a 0 size with
          | none => .ok ()
          | some a' => baStorageCheck a a'
        else .ok ()
      else if size ≠ n then bytesResizeCheck n size
      else .ok ()
    | none => bytesSizeCheck size

/-- `PyBytesWriter_FinishWithPointer(writer, buf)`, bytesobject.c:3932-3937, with `out` the bytes
before `buf`, and `PyBytesWriter_Finish`, :3925-3929, when the size was set exactly. -/
def writerFinish (w : Writer) (out : Seq) : Py Seq :=
  match writerFinishSize w out.length with
  | .ok () => .ok out
  | .error e => .error e

/-- `_PyBytes_Repeat(dest, len_dest, src, len_src)`, bytesobject.c:3645-3666,
for `len_src > 0`: the doubling copy. `dest` holds `copied` bytes so far; `fuel`
bounds the doublings. -/
def repeatLoop (lenDest : Nat) : Nat → Seq → Seq
  | 0, dest => dest
  | fuel + 1, dest =>
    if dest.length < lenDest then
      let n := min dest.length (lenDest - dest.length)
      repeatLoop lenDest fuel (dest ++ dest.take n)
    else dest

def bytesRepeatFill (lenDest : Nat) (src : Seq) : Seq :=
  if lenDest = 0 then []
  else match src with
    | [c] => List.replicate lenDest c
    | _ => repeatLoop lenDest lenDest src

/-! ## Properties -/

/-- The capacity promise of `PyBytesWriter`, which the unchecked `*res++` writes of its callers rely
on. A successful `Create`, `Resize` or `Grow` leaves `size` where it was asked to be and leaves room
for it, starting from any writer with room for its size; `WriteBytes` also appends the data.
Hypothesis: `0 <= size <= allocated`, what `Create` establishes. -/
def WriterInvariant : Prop :=
  (∀ (size : Int) (b : Bool) (w : Writer), writerCreate size b = .ok w →
    w.size = size ∧ size ≤ writerAllocated w) ∧
  (∀ (w w' : Writer) (size : Int), w.size ≤ writerAllocated w → writerResize w size = .ok w' →
    w'.size = size ∧ w'.size ≤ writerAllocated w') ∧
  (∀ (w w' : Writer) (grow : Int), 0 ≤ w.size → w.size ≤ writerAllocated w →
    writerGrow w grow = .ok w' → w'.size = w.size + grow ∧ w'.size ≤ writerAllocated w') ∧
  (∀ (w w' : Writer) (out bytes out' : Seq) (n : Int), 0 ≤ w.size → w.size ≤ writerAllocated w →
    n ≤ bytes.length → writerWriteBytes w out bytes n = .ok (w', out') →
    ∃ data : Seq, data = (if n < 0 then bytes.takeWhile (· != 0) else bytes.take n.toNat) ∧
      out' = out ++ data ∧ w'.size = w.size + data.length ∧ w'.size ≤ writerAllocated w') ∧
  (∀ (w w' : Writer) (grow pos pos' : Int), 0 ≤ w.size → w.size ≤ writerAllocated w →
    writerGrowAt w grow pos = .ok (w', pos') →
    pos' = pos ∧ w'.size = w.size + grow ∧ w'.size ≤ writerAllocated w') ∧
  (∀ (w w' : Writer) (size pos pos' : Int), w.size ≤ writerAllocated w →
    writerResizeAt w size pos = .ok (w', pos') →
    pos' = pos ∧ w'.size = size ∧ w'.size ≤ writerAllocated w') ∧
  (∀ w : Writer, (writerResizeToAllocated w).size = writerAllocated (writerResizeToAllocated w))

theorem writerObjResize_size (w : Writer) (size : Int) (o : Int × Int)
    (h : writerObjResize w size = .ok o) : o.1 = size := by
  unfold writerObjResize at h
  have key : ∀ (c : Py Unit) (p : Int × Int), p.1 = size →
      (match c with | .ok () => Except.ok p | .error e => .error e) = .ok o → o.1 = size := by
    intro c p hp hc
    cases c with
    | ok u => cases u; simp only [Except.ok.injEq] at hc; rw [← hc]; exact hp
    | error e => simp at hc
  split at h
  · split at h
    · split at h
      · have := Except.ok.inj h
        rw [← this]
      · exact key _ _ rfl h
    · exact key _ _ rfl h
  · exact key _ _ rfl h

theorem writerResizeRaw_room (w w' : Writer) (size : Int) (b : Bool) (h0 : 0 ≤ size)
    (h : writerResizeRaw w size b = .ok w') : size ≤ writerAllocated w' ∧ w'.size = w.size := by
  unfold writerResizeRaw at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by assumption, rfl⟩
  · simp only at h
    split at h
    · rename_i obj hobj
      have h1 := writerObjResize_size _ _ _ hobj
      simp only [Except.ok.injEq] at h
      subst h
      refine ⟨?_, rfl⟩
      simp only [writerAllocated]
      rcases obj with ⟨n, a⟩
      simp only at h1 ⊢
      rw [h1]
      split
      · have : 0 ≤ size / overallocateFactor := Int.ediv_nonneg h0 (by decide)
        omega
      · omega
    · simp at h

theorem writerGrow_room (w w' : Writer) (grow : Int) (h0 : 0 ≤ w.size)
    (hw : w.size ≤ writerAllocated w) (h : writerGrow w grow = .ok w') :
    w'.size = w.size + grow ∧ w'.size ≤ writerAllocated w' := by
  unfold writerGrow at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨by omega, hw⟩
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only at h
        split at h
        · rename_i w1 hr
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, (writerResizeRaw_room _ _ _ _ (by omega) hr).1⟩
        · simp at h

theorem writerResize_room (w w' : Writer) (size : Int) (hw : w.size ≤ writerAllocated w)
    (h : writerResize w size = .ok w') : w'.size = size ∧ w'.size ≤ writerAllocated w' := by
  unfold writerResize at h
  split at h
  · simp at h
  · split at h
    · split at h
      · rename_i w1 hr
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨rfl, (writerResizeRaw_room _ _ _ _ (by omega) hr).1⟩
      · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      refine ⟨rfl, ?_⟩
      simp only [writerAllocated] at hw ⊢
      omega

theorem writerInvariant_proven : WriterInvariant := by
  refine ⟨?_, writerResize_room, writerGrow_room, ?_, ?_, ?_, ?_⟩
  · intro size b w h
    unfold writerCreate at h
    split at h
    · simp at h
    · simp only at h
      split at h
      · split at h
        · rename_i w1 hr
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, (writerResizeRaw_room _ _ _ _ (by omega) hr).1⟩
        · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp only [writerAllocated, smallBufferSize]
        omega
  · intro w w' out bytes out' n h0 hw _ h
    unfold writerWriteBytes at h
    dsimp only at h
    generalize hd : (if n < 0 then bytes.takeWhile (· != 0) else bytes.take n.toNat) = data at h
    split at h
    · rename_i w1 hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have := writerGrow_room _ _ _ h0 hw hr
      exact ⟨data, rfl, h2.symm, this.1, this.2⟩
    · simp at h
  · intro w w' grow pos pos' h0 hw h
    unfold writerGrowAt at h
    split at h
    · rename_i w1 hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := writerGrow_room _ _ _ h0 hw hr
      exact ⟨rfl, this.1, this.2⟩
    · simp at h
  · intro w w' size pos pos' hw h
    unfold writerResizeAt at h
    split at h
    · rename_i w1 hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have := writerResize_room _ _ _ hw hr
      exact ⟨rfl, this.1, this.2⟩
    · simp at h
  · intro w
    simp [writerResizeToAllocated, writerAllocated]

end PyLean.BytesObj.Bytes
