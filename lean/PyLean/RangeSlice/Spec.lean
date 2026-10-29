import PyLean.RangeSlice.Model

/-!
Mathematical vocabulary for `range` properties: the k-th element
`start + k*step`, and the length characterised without any division: `L` is
the length of `range(start, stop, step)` when exactly the indices `0 <= k < L`
give elements strictly before `stop` in the direction of `step`.
-/

namespace PyLean.RangeSlice

/-- `start + k*step` lies strictly before `stop` in the direction of `step`. -/
def InSeq (start stop step k : Int) : Prop :=
  if 0 < step then start + k * step < stop else stop < start + k * step

/-- `L` is the number of elements of `range(start, stop, step)`. -/
def IsLen (start stop step L : Int) : Prop :=
  0 ≤ L ∧ ∀ k, 0 ≤ k → (k < L ↔ InSeq start stop step k)

/-- The k-th element of the mathematical sequence. -/
def Range.elem (r : Range) (k : Int) : Int := r.start + k * r.step

/-- Type invariant of every `rangeobject`: `make_range_object` (rangeobject.c:51-73)
stores `compute_range_length` in `length`, and the step is non-zero
(`validate_step`, or the product of two non-zero steps in `compute_slice`). -/
def Range.WF (r : Range) : Prop :=
  r.step ≠ 0 ∧ r.length = computeRangeLength r.start r.stop r.step

/-- The mathematical length of `r`. -/
def Range.Len (r : Range) (L : Int) : Prop := IsLen r.start r.stop r.step L

/-- `x` is one of the elements of `r` whose length is `L`. -/
def Range.MemL (r : Range) (L x : Int) : Prop := ∃ k, 0 ≤ k ∧ k < L ∧ x = r.elem k

end PyLean.RangeSlice
