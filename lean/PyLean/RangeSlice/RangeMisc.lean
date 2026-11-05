import PyLean.RangeSlice.Objects

/-!
`range.__bool__`, `range.__reduce__` and its round trip through `range(...)` (keyword check, then
`range_from_array`), Objects/rangeobject.c, CPython 3.15.2.
-/

namespace PyLean.RangeSlice

/-- `range_bool`, rangeobject.c:758-762: `PyObject_IsTrue(self->length)`, the stored PyLong
length, so it never overflows. -/
def rangeBool (r : Range) : Bool := r.length != 0

/-- `bool(r)` is true exactly when the range has a first element, for every range object, even
when `len(r)` raises `OverflowError`. -/
def RangeBoolNonEmpty : Prop :=
  ∀ r : Range, r.WF → (rangeBool r = true ↔ InSeq r.start r.stop r.step 0)

theorem rangeBoolNonEmpty_proven : RangeBoolNonEmpty := by
  intro r hwf
  have h := hwf.len
  unfold Range.Len IsLen at h
  obtain ⟨hnn, hk⟩ := h
  rw [← hk 0 (by omega)]
  unfold rangeBool
  simp only [bne_iff_ne, ne_eq]
  omega

/-- `bool(range(2**64))` is true while `len` raises. -/
theorem rangeBool_big : rangeBool (range1 (2 ^ 64)) = true ∧ rangeLength (range1 (2 ^ 64)) = .error ssizeOverflow := by
  decide

/-- `range_reduce`, rangeobject.c:721-726: `(type(r), (start, stop, step))`. -/
def rangeReduce (r : Range) : List Int := [r.start, r.stop, r.step]

/-- Pickling round-trips: calling the type with the reduced arguments, through either entry
point (`range(*args)` is `range_vectorcall`, `range.__new__(range, *args)` is `range_new`) and
with no keywords, rebuilds a range object equal to `r` field for field, for every range object. -/
def RangeReduceRoundTrip : Prop :=
  ∀ r : Range, r.WF →
    rangeVectorcall ((rangeReduce r).map .int) none = .ok r ∧
    rangeNewTp ((rangeReduce r).map .int) none = .ok r

theorem rangeReduceRoundTrip_proven : RangeReduceRoundTrip := by
  intro r ⟨h0, hl⟩
  obtain ⟨a, b, s, L⟩ := r
  simp only at h0 hl
  subst hl
  simp [rangeVectorcall, rangeNewTp, noKwnames, noKeywords, rangeFromArray, rangeFrom23, rangeReduce,
    numberIndex, validateStepObj, h0, makeRangeObject, bind, Except.bind, pure, Except.pure]

end PyLean.RangeSlice
