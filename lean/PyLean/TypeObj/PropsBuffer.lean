import PyLean.TypeObj.Buffer

/-! Properties of the buffer helpers of `Objects/abstract.c`. -/

namespace PyLean.TypeObj

theorem stridesMatch_fillF (sd : Int) (shape : List Int) :
    stridesMatch sd (shape.zip (fillStridesF sd shape)) = true := by
  induction shape generalizing sd with
  | nil => simp [stridesMatch, fillStridesF]
  | cons d ds ih =>
    simp [fillStridesF, stridesMatch, ih]

theorem fillStridesF_length (sd : Int) (shape : List Int) :
    (fillStridesF sd shape).length = shape.length := by
  induction shape generalizing sd with
  | nil => rfl
  | cons d ds ih => simp [fillStridesF, ih]

theorem reverse_zip_eq {α β : Type} (l1 : List α) (l2 : List β) (h : l1.length = l2.length) :
    (l1.zip l2).reverse = l1.reverse.zip l2.reverse := by
  induction l1 generalizing l2 with
  | nil => simp
  | cons x xs ih =>
    cases l2 with
    | nil => simp at h
    | cons y ys =>
      have hl : xs.length = ys.length := by simpa using h
      have hr : xs.reverse.length = ys.reverse.length := by simpa using hl
      simp [ih ys hl, List.zip_append hr]

/-- **`PyBuffer_FillContiguousStrides` gives contiguous strides**: strides computed for
order `'F'` pass `_IsFortranContiguous` and those for `'C'` pass `_IsCContiguous`, for every
shape and item size. The two functions must agree, as consumers use one to decide the
other. -/
def FillStridesContiguous : Prop :=
  ∀ (shape : List Int) (itemsize len : Int) (ndim : Nat),
    isFortranContiguous
        (BufView.mk len itemsize ndim shape (some (fillContiguousStrides shape itemsize 'F')) false) = true ∧
    isCContiguous
        (BufView.mk len itemsize ndim shape (some (fillContiguousStrides shape itemsize 'C')) false) = true

theorem fillStridesContiguous_proven : FillStridesContiguous := by
  intro shape itemsize len ndim
  constructor
  · simp [isFortranContiguous, fillContiguousStrides, stridesMatch_fillF]
  · have hl : shape.length = (fillStridesC itemsize shape).length := by
      simp [fillStridesC, fillStridesF_length]
    have hrev : (shape.zip (fillStridesC itemsize shape)).reverse =
        shape.reverse.zip (fillStridesF itemsize shape.reverse) := by
      rw [reverse_zip_eq _ _ hl]
      simp [fillStridesC]
    simp [isCContiguous, fillContiguousStrides, hrev, stridesMatch_fillF]

/-- `PyBuffer_IsContiguous` is false for a view with suboffsets, and unknown orders are
false, `Objects/abstract.c:521`, `:529`. -/
def IsContiguousGuards : Prop :=
  ∀ (v : BufView) (o : Char),
    (v.hasSuboffsets = true → isContiguous v o = false) ∧
    (o ≠ 'C' → o ≠ 'F' → o ≠ 'A' → isContiguous v o = false)

theorem isContiguousGuards_proven : IsContiguousGuards := by
  intro v o
  constructor
  · intro h; simp [isContiguous, h]
  · intro h1 h2 h3
    simp [isContiguous, h1, h2, h3]

/-- Index digits within the shape stay within it after `_Py_add_one_to_index_F`. -/
def InRange : List Int → List Int → Prop
  | [], [] => True
  | i :: is, s :: ss => 0 ≤ i ∧ i < s ∧ InRange is ss
  | _, _ => False

/-- **The odometer stays in bounds**, the invariant that `PyBuffer_FromContiguous` and
`PyObject_CopyData` need for `PyBuffer_GetPointer`. -/
def AddOneInRange : Prop :=
  ∀ (index shape : List Int), InRange index shape → InRange (addOneF index shape) shape

theorem addOneInRange_proven : AddOneInRange := by
  intro index
  induction index with
  | nil =>
    intro shape h
    cases shape with
    | nil => simpa [addOneF, InRange] using h
    | cons _ _ => simp [InRange] at h
  | cons i is ih =>
    intro shape h
    cases shape with
    | nil => simp [InRange] at h
    | cons s ss =>
      obtain ⟨h1, h2, h3⟩ := h
      simp only [addOneF]
      split
      · exact ⟨by omega, by omega, h3⟩
      · exact ⟨by omega, by omega, ih ss h3⟩

/-- All-maximal indices wrap to zero: this is why the increment-before-copy loop of
`PyObject_CopyData` still copies every element, with `(0, ..., 0)` last. -/
def AddOneWraps : Prop :=
  ∀ (shape : List Int), (∀ s ∈ shape, 0 < s) →
    addOneF (shape.map (· - 1)) shape = shape.map (fun _ => 0)

theorem addOneWraps_proven : AddOneWraps := by
  intro shape h
  induction shape with
  | nil => rfl
  | cons s ss ih =>
    have h1 := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simp [addOneF, h1]

/-- **`PyObject_CopyData` stays inside the destination.** Refuted. The only check on the two
buffers is `dest.len >= src.len`; the elaborate copy then applies the source's indices to
the destination, so a destination of another shape is written outside its bounds. Here both
have 6 bytes: the destination has shape `(3, 2)` in Fortran order and the source `(2, 3)`
and index `(0, 2)` is byte 6 of the destination. -/
def CopyDataInBounds : Prop :=
  ∀ (dest src : BufView) (pairs : List (Int × Int)),
    copyDataPlan dest src = .ok (.elements pairs) →
    ∀ p ∈ pairs, 0 ≤ p.1 ∧ p.1 < dest.len

/-- The two views of the counterexample. -/
def cdDest : BufView :=
  { len := 6, itemsize := 1, ndim := 2, shape := [3, 2], strides := some [1, 3] }
def cdSrc : BufView :=
  { len := 6, itemsize := 1, ndim := 2, shape := [2, 3], strides := some [3, 1] }

/-- The plan of the counterexample writes byte 6 of a 6-byte destination. -/
theorem cd_plan : (match copyDataPlan cdDest cdSrc with
    | .ok (.elements ps) => ps.contains (6, 2)
    | _ => false) = true := by
  decide

theorem copyDataInBounds_refuted : ¬CopyDataInBounds := by
  intro h
  have hplan := cd_plan
  cases hc : copyDataPlan cdDest cdSrc with
  | error e => rw [hc] at hplan; simp at hplan
  | ok plan =>
    rw [hc] at hplan
    cases plan with
    | memcpy n => simp at hplan
    | elements ps =>
      have hmem : (6, 2) ∈ ps := by simpa using hplan
      have := h cdDest cdSrc ps hc (6, 2) hmem
      simp [cdDest] at this

end PyLean.TypeObj
