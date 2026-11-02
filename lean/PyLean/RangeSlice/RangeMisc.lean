import PyLean.RangeSlice.Length

/-!
`range.__bool__`, `range.__reduce__` and the `range(...)` call itself (keyword check, then
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

/-- `range_new` (rangeobject.c:154-160) and `range_vectorcall` (:164-172): keywords are refused
(`_PyArg_NoKeywords`), then `range_from_array` (:96-150) by argument count. -/
def rangeCall (args : List Int) (hasKw : Bool) : Py Range :=
  if hasKw then .error (.typeError "range() takes no keyword arguments")
  else match args with
    | [] => .error (.typeError "range expected at least 1 argument, got 0")
    | [stop] => .ok (range1 stop)
    | [a, b] => rangeNew a b none
    | [a, b, c] => rangeNew a b (some c)
    | l => .error (.typeError s!"range expected at most 3 arguments, got {l.length}")

/-- Pickling round-trips: calling the type with the reduced arguments rebuilds an equal range
object, for every range object. -/
def RangeReduceRoundTrip : Prop := ∀ r : Range, r.WF → rangeCall (rangeReduce r) false = .ok r

theorem rangeReduceRoundTrip_proven : RangeReduceRoundTrip := by
  intro r ⟨h0, hl⟩
  obtain ⟨a, b, s, L⟩ := r
  simp only at h0 hl
  subst hl
  simp [rangeCall, rangeReduce, rangeNew, validateStep, h0, makeRangeObject, bind, Except.bind, pure, Except.pure]

end PyLean.RangeSlice
