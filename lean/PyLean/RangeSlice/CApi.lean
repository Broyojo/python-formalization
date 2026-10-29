import PyLean.RangeSlice.Iter

/-!
The legacy C API `PySlice_GetIndices` against its documented error contract.
-/

namespace PyLean.RangeSlice

open PyLean

/-- Doc/c-api/slice.rst, `PySlice_GetIndices`: "Returns 0 on success and -1
on error with no exception set (unless one of the indices was not None and
failed to be converted to an integer, in which case -1 is returned with an
exception set)." So whenever the call leaves an exception set, it returns -1.
Quantified over every slice with int/None parts and every sequence length
`0 <= length <= PY_SSIZE_T_MAX` (the documented precondition: a length). -/
def GetIndicesContract : Prop :=
  ∀ (s : Slice) (length : Int), 0 ≤ length → length ≤ ssizeMax →
    (sliceGetIndices s length).exc.isSome → (sliceGetIndices s length).ret = -1

/-- `PySlice_GetIndices(slice(None, None, 2**64), 10, ...)`: `PyLong_AsSsize_t`
fails and sets `OverflowError`, the error return `-1` is then used as the
step, the bounds checks pass, and the function returns 0 (success) with the
exception still set and `(start, stop, step) = (9, -1, -1)`. -/
theorem getIndicesContract_refuted : ¬GetIndicesContract := by
  intro h
  have hv : sliceGetIndices ⟨none, none, some (2 ^ 64)⟩ 10 = ⟨0, some ssizeOverflow, 9, -1, -1⟩ := by
    decide
  have := h ⟨none, none, some (2 ^ 64)⟩ 10 (by decide) (by decide) (by rw [hv]; rfl)
  rw [hv] at this
  cases this

/-- The same happens for an overflowing start: `slice(2**64, 5)` with length
10 returns 0 with `OverflowError` set and start `-1 + 10 = 9`. -/
example : sliceGetIndices ⟨some (2 ^ 64), some 5, none⟩ 10 = ⟨0, some ssizeOverflow, 9, 5, 1⟩ := by
  decide

end PyLean.RangeSlice
