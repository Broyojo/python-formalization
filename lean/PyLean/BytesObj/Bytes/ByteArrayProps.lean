import PyLean.BytesObj.Bytes.BasicProps5
import PyLean.Sequences.SliceAssign

/-!
Properties of `bytearray`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch
open PyLean.RangeSlice (Slice)

/-! ## resize -/

theorem resizedData_length (d : List Int) (n : Int) (h0 : 0 ≤ n) :
    ((resizedData d n).length : Int) = n := by
  simp only [resizedData, List.length_append, List.length_take, List.length_replicate]
  omega

/-- The buffer layout survives a resize: for every object with a valid layout and every
request, a successful `bytearray_resize_lock_held` gives the requested size and a valid layout
(data and terminator inside the allocation), keeps the first `min(old, new)` bytes, and
leaves the export count alone. This is what makes every `memcpy` after a resize safe. -/
def ResizeWF : Prop :=
  ∀ (b r : BA) (n : Int), b.WF → baResize b n = .ok r →
    r.WF ∧ r.size = n ∧ r.exports = b.exports ∧
    r.data.take b.data.length = b.data.take n.toNat

theorem baResize_cases (b r : BA) (n : Int) (h : baResize b n = .ok r) :
    0 ≤ n ∧ (r = b ∧ n = b.size ∨ b.exports = 0 ∧ n ≠ b.size ∧ r.data = resizedData b.data n ∧
      r.exports = b.exports ∧
      ((n + b.offset + 1 ≤ b.alloc ∧ r.alloc = b.alloc ∧ r.offset = b.offset) ∨
       (r.offset = 0 ∧ n + 1 ≤ r.alloc))) := by
  unfold baResize at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  rename_i h0
  have h0' : 0 ≤ n := by omega
  refine ⟨h0', ?_⟩
  split at h
  · left
    simp only [Except.ok.injEq] at h
    exact ⟨h.symm, by assumption⟩
  rename_i hne
  right
  unfold canResize at h
  split at h
  · simp at h
  rename_i hexp
  simp only at h
  have hE : b.exports = 0 := by omega
  split at h
  · rename_i hfit
    simp only [Except.ok.injEq] at h
    subst h
    exact ⟨hE, hne, rfl, rfl, Or.inl ⟨hfit.1, rfl, rfl⟩⟩
  · rename_i hfit
    split at h
    · simp at h
    split at h
    · simp at h
    simp only [Except.ok.injEq] at h
    subst h
    refine ⟨hE, hne, rfl, rfl, Or.inr ⟨rfl, ?_⟩⟩
    simp only
    repeat' split
    all_goals omega

theorem resizeWF_proven : ResizeWF := by
  intro b r n hw h
  obtain ⟨h0, hc⟩ := baResize_cases b r n h
  rcases hc with ⟨rfl, hn⟩ | ⟨hE, hne, hd, hx, hc⟩
  · refine ⟨hw, hn.symm, rfl, ?_⟩
    have : n.toNat = r.data.length := by simp [BA.size] at hn; omega
    simp [this]
  · have hsize : r.size = n := by
      simp only [BA.size, hd]
      exact resizedData_length _ _ h0
    refine ⟨?_, hsize, hx, ?_⟩
    · rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
      · refine ⟨by rw [h3]; exact hw.1, Or.inr ?_⟩
        omega
      · exact ⟨by omega, Or.inr (by omega)⟩
    · rw [hd]
      simp only [resizedData]
      by_cases hle : n.toNat ≤ b.data.length
      · have e : n.toNat - b.data.length = 0 := by omega
        simp [e, hle]
      · have e : b.data.take n.toNat = b.data := List.take_of_length_le (by omega)
        rw [e]
        simp

/-- The export rule: a resize to the same size is always fine; any other resize of an object
with exports raises `BufferError("Existing exports of data: object cannot be re-sized")`,
checked after the `ValueError` for a negative size. With no exports, a size that fits
in memory succeeds. -/
def ExportRule : Prop :=
  (∀ b : BA, baResize b b.size = .ok b) ∧
  (∀ (b : BA) (n : Int), 0 ≤ n → n ≠ b.size → b.exports > 0 →
    baResize b n = .error (bufferError "Existing exports of data: object cannot be re-sized")) ∧
  (∀ (b : BA) (n : Int), n < 0 → ∃ m, baResize b n = .error (.valueError m)) ∧
  (∀ (b : BA) (n : Int), 0 ≤ n → b.exports = 0 → n < 2 ^ 46 → b.alloc < 2 ^ 46 →
    ∃ r, baResize b n = .ok r ∧ r.data = (if n = b.size then b.data else resizedData b.data n) ∧
      r.exports = b.exports)

theorem exportRule_proven : ExportRule := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro b
    have : ¬ (b.size < 0) := by simp only [BA.size]; omega
    simp [baResize, this, pure, Except.pure]
  · intro b n h0 hn hx
    have h1 : ¬ (n < 0) := by omega
    simp [baResize, h1, hn, canResize, hx, bind, Except.bind]
  · intro b n h
    exact ⟨_, by simp [baResize, h, bind, Except.bind]; rfl⟩
  · intro b n h0 hE h1 h2
    have hn : ¬ (n < 0) := by omega
    by_cases he : n = b.size
    · refine ⟨b, ?_, by simp [he], rfl⟩
      subst he
      simp [baResize, hn, pure, Except.pure, bind, Except.bind]
    · unfold baResize
      simp only [bind, Except.bind, pure, Except.pure, if_neg hn, if_neg he, canResize, hE]
      have hx : ¬ (0 > 0) := by omega
      simp only [gt_iff_lt, Nat.lt_irrefl, if_false]
      have hmax : ssizeMax = 9223372036854775807 := by decide
      split
      · exact ⟨_, rfl, by simp [he], rfl⟩
      · have hn8 : n / 8 ≤ n := Int.ediv_le_self _ h0
        have hA : (if n + b.offset + 1 ≤ b.alloc then n + 1 else if 8 * n ≤ 9 * b.alloc then n + n / 8 + (if n < 9 then 3 else 6) else n + 1) < 2 ^ 47 := by
          repeat' split
          all_goals omega
        have hB : ¬ ((if n + b.offset + 1 ≤ b.alloc then n + 1 else if 8 * n ≤ 9 * b.alloc then n + n / 8 + (if n < 9 then 3 else 6) else n + 1) > ssizeMax) := by
          rw [hmax]; omega
        have hC : mallocFails (if n + b.offset + 1 ≤ b.alloc then n + 1 else if 8 * n ≤ 9 * b.alloc then n + n / 8 + (if n < 9 then 3 else 6) else n + 1) = false := by
          simp only [mallocFails, decide_eq_false_iff_not]
          omega
        rw [if_neg hB, if_neg (by rw [hC]; simp)]
        exact ⟨_, rfl, by simp [he], rfl⟩

/-! ## Two failure paths that expose uninitialised memory -/

/-- "No byte of a bytearray is ever uninitialised": after any `b.__init__(items)` on a
fresh object, also a failed one, every byte is a value. Refuted: the list fast path resizes
first and fills in order, so a bad item leaves the rest of the buffer as `malloc` gave it. -/
def InitInitialised : Prop :=
  ∀ items : List Obj, ∀ x ∈ (baInit {} (some (.list items)) none none).1.data, x ≠ uninit

theorem initInitialised_refuted : ¬ InitInitialised := by
  intro h
  have := h [.int 1000] uninit (by decide)
  exact this rfl

/-- "`extend` of a buffer appends": whatever the argument's `__buffer__` does to `self`,
the result has no uninitialised byte. Refuted: `bytearray_setslice` takes `lo` before
`PyObject_GetBuffer`, so a `__buffer__` that shrinks `self` leaves a gap. -/
def ExtendInitialised : Prop :=
  ∀ (s v : Seq) (r : BA), baExtendBuffer (baOf s) { bytes := v, mutate := baClear } = .ok r →
    ∀ x ∈ r.data, x ≠ uninit

theorem extendInitialised_refuted : ¬ ExtendInitialised := by
  intro h
  have hr : baExtendBuffer (baOf [97]) { bytes := [120], mutate := baClear } =
      .ok { data := [uninit, 120], alloc := 3, offset := 0, exports := 0 } := by
    decide
  exact h _ _ _ hr uninit (by decide) rfl

/-- "An allocation failure in `PyByteArray_FromStringAndSize` is only a `MemoryError`".
Refuted: `bytearray_dealloc` reads `ob_exports` before it is set, so what `PyObject_New`
left there can print a spurious `SystemError` on `stderr`. -/
def AllocFailureSilent : Prop :=
  ∀ (garbage : Int) (bytes : Option Seq) (size : Int), (baFromSizeTrace garbage bytes size).2 = []

theorem allocFailureSilent_refuted : ¬ AllocFailureSilent := by
  intro h
  have := h 1 none (2 ^ 50)
  revert this
  decide

end PyLean.BytesObj.Bytes
