import PyLean.PyIO.Spec

/-!
`io.BytesIO` vs `_pyio.BytesIO`, layered as in `Accel`: the broad
agreement statements are refuted, and every hypothesis of the proven core
statement corresponds to one of the refutations.
-/

namespace PyLean.PyIO

open PyLean

/-- The two twins return the same values and raise the same exceptions (class
and message) for every initial value and operation sequence. -/
def BytesIOTwinsAgree : Prop := ∀ init ops, runBC init ops = runBPy init ops

/-- On a closed stream, `read()` raises `ValueError('I/O operation on closed
file.')` in C and `ValueError('read from closed file')` in Python. -/
theorem bytesIOTwinsAgree_refuted : ¬BytesIOTwinsAgree := by
  intro h
  have := h [] [.close, .read none]
  revert this
  decide

/-- The two twins agree on every value and exception class. -/
def BytesIOTwinsSameClass : Prop := ∀ init ops, AllSameClass (runBC init ops) (runBPy init ops)

/-- `seek(2**63)`: C raises `OverflowError` while converting the argument to
`Py_ssize_t`; Python seeks. -/
theorem bytesIOTwinsSameClass_refuted : ¬BytesIOTwinsSameClass := by
  intro h
  have := h [] [.seek (2 ^ 63) 0]
  revert this
  decide

/-- With every int argument inside the range of the C converter, the twins
agree on every value and exception class. -/
def BytesIOTwinsSameClassInRange : Prop :=
  ∀ init ops, (∀ o ∈ ops, BOp.InRange o) → AllSameClass (runBC init ops) (runBPy init ops)

/-- While a `getbuffer()` view is alive, C refuses every write (`BufferError`);
Python only refuses writes that resize the `bytearray`, so overwriting in
place succeeds. -/
theorem bytesIOTwinsSameClassInRange_refuted : ¬BytesIOTwinsSameClassInRange := by
  intro h
  have := h [97] [.getbuffer, .write [120]] (by decide)
  revert this
  decide

/-- In range and without `getbuffer()`, the twins agree on every value and
exception class. -/
def BytesIOTwinsSameClassNoExport : Prop :=
  ∀ init ops, (∀ o ∈ ops, BOp.InRange o ∧ BOp.NoExport o) →
    AllSameClass (runBC init ops) (runBPy init ops)

/-- `seek(sys.maxsize - 1); write(b'x')` on a BytesIO with a private buffer asks
`resize_buffer_lock_held` for `PY_SSIZE_T_MAX` bytes; its `alloc = size + 1` is
negative as a `Py_ssize_t`, so `_PyBytes_ResizeKeepOnError` raises `SystemError`.
Python raises `MemoryError`. Both streams stay open. -/
theorem bytesIOTwinsSameClassNoExport_refuted : ¬BytesIOTwinsSameClassNoExport := by
  intro h
  have := h [97, 98] [.seek (2 ^ 63 - 2) 0, .write [120], .closed] (by decide)
  revert this
  decide

/-- In range, without `getbuffer()`, and without allocation failures (every
position and write extent of the Python run below `memLimit`), the twins
agree on every value and exception class. -/
def BytesIOTwinsSameClassNoAllocFail : Prop :=
  ∀ init ops, (∀ o ∈ ops, BOp.InRange o ∧ BOp.NoExport o) → PyRunAll BOp.Small (bInit init) ops →
    AllSameClass (runBC init ops) (runBPy init ops)

/-- `readline(0)` on a closed stream: C raises `ValueError`; Python's
`IOBase.readline` loop never runs for `size == 0` and returns `b''`. -/
theorem bytesIOTwinsSameClassNoAllocFail_refuted : ¬BytesIOTwinsSameClassNoAllocFail := by
  intro h
  have := h [] [.close, .readline (some 0)] (by decide) (by decide)
  revert this
  decide

end PyLean.PyIO
