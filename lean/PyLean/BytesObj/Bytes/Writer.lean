import PyLean.BytesObj.Bytes.Obj

/-!
Object allocation and `_PyBytesWriter`, Objects/bytesobject.c:105-197 and
:3450-3743. The writer is its bookkeeping (`allocated`, `min_size`, the flags);
the bytes written are kept by the caller, so only the errors and the capacity
logic are modelled here. `pos ≤ min_size ≤ allocated` is the safety invariant.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-- The `(size_t)size > PY_SSIZE_T_MAX - PyBytesObject_SIZE` check and allocation
of `_PyBytes_FromSize`, bytesobject.c:105-135. The size-0 path returns the empty
singleton, `bytes_get_empty`, :48-53. -/
def bytesFromSize (size : Int) : Py Seq :=
  if size = 0 then .ok []
  else if size > ssizeMax - bytesObjectSize then
    .error (.overflowError "byte string is too large")
  else if mallocFails (bytesObjectSize + size) then .error memoryError
  else .ok (List.replicate size.toNat 0)

/-- `PyBytes_FromStringAndSize(str, size)`, bytesobject.c:137-163: `str` is the
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

/-- `PyBytes_FromString(str)`, bytesobject.c:165-197: the bytes up to the first
NUL. -/
def bytesFromCString (s : Seq) : Seq := s.takeWhile (· != 0)

/-- The `_PyBytes_Resize` paths that can fail, bytesobject.c:3218-3279, for a
uniquely referenced buffer of `oldsize` bytes. Its `else` paths copy; the result
is the first `newsize` bytes, extended with bytes the caller fills. -/
def bytesResizeCheck (oldsize newsize : Int) : Py Unit :=
  if newsize < 0 then .error (badInternalCall "../Objects/bytesobject.c:3227")
  else if oldsize = newsize then .ok ()
  else if oldsize = 0 then do
    let _ ← bytesFromSize newsize
    return ()
  else if newsize = 0 then .ok ()
  else if mallocFails (bytesObjectSize + newsize) then .error memoryError
  else .ok ()

/-- `PyByteArray_FromStringAndSize`/`PyByteArray_Resize` failure for a buffer of
`size` bytes: only size checks, bytearrayobject.c:158-176 and :261-270. -/
def baAllocCheck (size : Int) : Py Unit :=
  if size ≥ ssizeMax ∨ mallocFails (size + 1) then .error memoryError else .ok ()

/-- `_PyBytesWriter`, Include/internal/pycore_bytesobject.h:79-90. -/
structure Writer where
  allocated : Int := 0
  minSize : Int := 0
  overallocate : Bool := false
  useBytearray : Bool := false
  useSmall : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- `sizeof(writer->small_buffer)`. -/
def smallBufferSize : Int := 512

/-- `_PyBytesWriter_Init`, bytesobject.c:3450-3459. -/
def writerInit (useBytearray : Bool := false) : Writer := { useBytearray }

/-- `OVERALLOCATE_FACTOR`, bytesobject.c:3442-3448, not Windows. -/
def overallocateFactor : Int := 4

/-- The allocation of `_PyBytesWriter_Resize`, bytesobject.c:3547-3589: the
small buffer moves to a new object, or the object is resized. -/
def writerResizeCheck (w : Writer) (allocated : Int) : Py Unit :=
  if !w.useSmall then
    if w.useBytearray then baAllocCheck allocated
    else bytesResizeCheck w.allocated allocated
  else
    if w.useBytearray then baAllocCheck allocated
    else (bytesFromSize allocated).map (fun _ => ())

/-- `_PyBytesWriter_Resize`, bytesobject.c:3531-3599. -/
def writerResize (w : Writer) (size : Int) : Py Writer := do
  let allocated :=
    if w.overallocate ∧ size ≤ ssizeMax - size / overallocateFactor then
      size + size / overallocateFactor
    else size
  writerResizeCheck w allocated
  return { w with allocated, useSmall := false }

/-- `_PyBytesWriter_Prepare`, bytesobject.c:3601-3626. -/
def writerPrepare (w : Writer) (size : Int) : Py Writer := do
  if size = 0 then return w
  if w.minSize > ssizeMax - size then throw memoryError
  let w' ← if w.minSize + size > w.allocated then writerResize w (w.minSize + size) else pure w
  return { w' with minSize := w.minSize + size }

/-- `_PyBytesWriter_Alloc`, bytesobject.c:3631-3659 (release build). -/
def writerAlloc (w : Writer) (size : Int) : Py Writer :=
  writerPrepare { w with useSmall := true, allocated := smallBufferSize } size

/-- `_PyBytesWriter_WriteBytes`, bytesobject.c:3705-3719. -/
def writerWriteBytes (w : Writer) (out bytes : Seq) : Py (Writer × Seq) := do
  let w ← writerPrepare w bytes.length
  return (w, out ++ bytes)

/-- `_PyBytesWriter_GetSize`, bytesobject.c:3484-3492, and
`_PyBytesWriter_AsString`, :3467-3482: the buffer is whichever of the small
buffer, the bytes or the bytearray is in use; the size is the bytes written. -/
def writerGetSize (out : Seq) : Int := out.length

/-- `_PyBytesWriter_Finish`, bytesobject.c:3661-3703: an exact-size bytes or
bytearray holding what was written. The `_PyBytes_Resize` to the final size only
shrinks, so it cannot fail. -/
def writerFinish (_ : Writer) (out : Seq) : Seq := out

/-- `_PyBytes_Repeat(dest, len_dest, src, len_src)`, bytesobject.c:3722-3743,
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

/-- For every writer respecting `min_size ≤ allocated` and every `size ≥ 0`:
a successful `Prepare` raises `min_size` by exactly `size`, keeps
`min_size ≤ allocated`, and with `overallocate` the capacity is at least the
request. `Alloc` starts from the small buffer and establishes the invariant;
`WriteBytes` advances by the data's length. So everything the writer is asked to
reserve fits. -/
def WriterInvariant : Prop :=
  (∀ (w w' : Writer) (size : Int), 0 ≤ size → 0 ≤ w.minSize → w.minSize ≤ w.allocated →
    writerPrepare w size = .ok w' → w'.minSize = w.minSize + size ∧ w'.minSize ≤ w'.allocated) ∧
  (∀ (w w' : Writer) (size : Int), 0 ≤ size → w.minSize = 0 →
    writerAlloc w size = .ok w' → w'.minSize = size ∧ size ≤ w'.allocated ∧
      smallBufferSize ≤ max w'.allocated smallBufferSize) ∧
  (∀ (w w' : Writer) (out bytes out' : Seq), 0 ≤ w.minSize → w.minSize ≤ w.allocated →
    writerWriteBytes w out bytes = .ok (w', out') →
    out' = out ++ bytes ∧ w'.minSize = w.minSize + bytes.length ∧ w'.minSize ≤ w'.allocated)

theorem writerResize_alloc (w w' : Writer) (size : Int) (h0 : 0 ≤ size)
    (h : writerResize w size = .ok w') : size ≤ w'.allocated ∧ w'.minSize = w.minSize := by
  unfold writerResize at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h
    subst h
    refine ⟨?_, rfl⟩
    simp only
    split
    · have : 0 ≤ size / overallocateFactor := Int.ediv_nonneg h0 (by decide)
      omega
    · omega

theorem writerPrepare_inv (w w' : Writer) (size : Int) (h0 : 0 ≤ size) (hm : 0 ≤ w.minSize)
    (hw : w.minSize ≤ w.allocated) (h : writerPrepare w size = .ok w') :
    w'.minSize = w.minSize + size ∧ w'.minSize ≤ w'.allocated := by
  unfold writerPrepare at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i h1
    simp only [Except.ok.injEq] at h
    subst h
    omega
  · split at h
    · simp at h
    · split at h
      · rename_i hgt
        split at h
        · simp at h
        · rename_i v hr
          have := writerResize_alloc _ _ _ (by omega) hr
          simp only [Except.ok.injEq] at h
          subst h
          refine ⟨rfl, ?_⟩
          simp only
          omega
      · simp only [Except.ok.injEq] at h
        subst h
        refine ⟨rfl, ?_⟩
        simp only
        omega

theorem writerInvariant_proven : WriterInvariant := by
  refine ⟨?_, ?_, ?_⟩
  · intro w w' size h0 hm hw h
    exact writerPrepare_inv w w' size h0 hm hw h
  · intro w w' size h0 hm h
    unfold writerAlloc at h
    have := writerPrepare_inv _ _ _ h0 (by simp [hm]) (by simp [hm, smallBufferSize]) h
    simp only [hm] at this
    refine ⟨by omega, by omega, by omega⟩
  · intro w w' out bytes out' hm hw h
    unfold writerWriteBytes at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · simp at h
    · rename_i hp
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1
      have := writerPrepare_inv _ _ _ (by omega) hm hw hp
      exact ⟨h2.symm, this.1, this.2⟩

end PyLean.BytesObj.Bytes
