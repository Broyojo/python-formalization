import PyLean.Registry
import PyLean.RangeSlice.Diff
import PyLean.RangeSlice.Model
import PyLean.RangeSlice.Spec
import PyLean.RangeSlice.Length
import PyLean.RangeSlice.Index
import PyLean.RangeSlice.Slice
import PyLean.RangeSlice.Iter
import PyLean.RangeSlice.CApi
import PyLean.RangeSlice.SliceHash
import PyLean.RangeSlice.RangeMisc
import PyLean.RangeSlice.Objects
import PyLean.RangeSlice.Search
import PyLean.RangeSlice.IterChoice

/-!
`range` and `slice`: `Objects/rangeobject.c`, `Objects/sliceobject.c`, CPython 3.15.2
(plus the list slicing path of `Objects/listobject.c`). Every property is
quantified over all Python ints, including values far outside `Py_ssize_t`.
-/

namespace PyLean.RangeSlice

open PyLean.Registry

def entries : List Entry := [
  { id := "rangeslice-len-fast-slow", pyFile := "Objects/rangeobject.c"
    pyFns := ["compute_range_length_long"]
    statement := "Whenever the C long fast path of compute_range_length (unsigned long get_len_of_range) produces a length, it equals the PyLong slow path's length."
    source := "invariant: fast path agrees with slow path", status := .proven
    prop := ``RangeLengthFastSlow, thm := some ``rangeLengthFastSlow_proven },
  { id := "rangeslice-new-length", pyFile := "Objects/rangeobject.c"
    pyFns := ["make_range_object"]
    statement := "range(start, stop[, step]) raises ValueError for step 0 and otherwise succeeds for all ints, storing start, stop, step and the mathematical length."
    source := "Doc/builtins/stdtypes.rst:1802 ('If step is zero, ValueError is raised')", status := .proven
    prop := ``RangeNewLength, thm := some ``rangeNewLength_proven },
  { id := "rangeslice-len-overflow", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_length"]
    statement := "len(r) is the mathematical length L when L <= sys.maxsize and raises OverflowError otherwise."
    source := "Doc/builtins/stdtypes.rst:1817-1819", status := .proven
    prop := ``LenOverflow, thm := some ``lenOverflow_proven },
  { id := "rangeslice-getitem", pyFile := "Objects/rangeobject.c"
    pyFns := ["compute_range_item", "compute_item"]
    statement := "r[i] is start + i*step (i + L for negative i) for -L <= i < L and raises IndexError otherwise, for all ints i."
    source := "invariant: sequence indexing", status := .proven
    prop := ``GetItemSeq, thm := some ``getItemSeq_proven },
  { id := "rangeslice-contains", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_contains_long"]
    statement := "For an int x, x in r holds exactly when x is one of the L elements start + k*step."
    source := "invariant: membership in the sequence", status := .proven
    prop := ``ContainsMem, thm := some ``containsMem_proven },
  { id := "rangeslice-index-count", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_index", "range_count"]
    statement := "For an int x, r.index(x) returns the k with r[k] == x and raises ValueError exactly for non-members; r.count(x) is 1 for members and 0 otherwise."
    source := "index/count docstrings, rangeobject.c:774-779", status := .proven
    prop := ``IndexCount, thm := some ``indexCount_proven },
  { id := "rangeslice-eq-sequence", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_equals"]
    statement := "r0 == r1 exactly when both ranges have the same length and the same elements."
    source := "Doc/builtins/stdtypes.rst:1883-1888 (ranges compare as sequences)", status := .proven
    prop := ``EqSameSeq, thm := some ``eqSameSeq_proven },
  { id := "rangeslice-eq-hash", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_equals"]
    statement := "Equal ranges hash the same tuple, so r0 == r1 implies hash(r0) == hash(r1)."
    source := "invariant: hash consistent with equality", status := .proven
    prop := ``EqHashConsistent, thm := some ``eqHashConsistent_proven },
  { id := "rangeslice-indices-in-bounds", pyFile := "Objects/sliceobject.c"
    pyFns := ["slice_indices", "_PySlice_GetLongIndices"]
    statement := "For n >= 0 and a non-zero step, s.indices(n) keeps the slice's step and every element of range(*s.indices(n)) is in [0, n)."
    source := "Doc/reference/datamodel.rst:1909-1916", status := .proven
    prop := ``IndicesInBounds, thm := some ``indicesInBounds_proven },
  { id := "rangeslice-slice-errors", pyFile := "Objects/sliceobject.c"
    pyFns := ["slice_indices", "PySlice_Unpack", "compute_slice"]
    statement := "s.indices(n) raises ValueError for n < 0; a zero step raises ValueError('slice step cannot be zero') in slice.indices, list slicing and range slicing alike."
    source := "invariant: same errors on all slicing paths", status := .proven
    prop := ``SliceErrors, thm := some ``sliceErrors_proven },
  { id := "rangeslice-list-slice-indices", pyFile := "Objects/sliceobject.c"
    pyFns := ["PySlice_Unpack", "PySlice_AdjustIndices", "list_slice_wrap", "list_slice_step_lock_held"]
    statement := "For 0 <= n <= sys.maxsize, list slicing (saturating Py_ssize_t PySlice_Unpack + PySlice_AdjustIndices + size_t cursor) reads exactly the positions range(*s.indices(n)) (PyLong _PySlice_GetLongIndices)."
    source := "Doc/reference/datamodel.rst:1915-1916 ('handled in a manner consistent with regular slices')", status := .proven
    prop := ``ListSliceIndices, thm := some ``listSliceIndices_proven },
  { id := "rangeslice-range-slice", pyFile := "Objects/rangeobject.c"
    pyFns := ["compute_slice", "_PySlice_GetLongIndices"]
    statement := "r[s] is a valid range whose k-th element is r[a + k*c] and whose length is len(range(a, b, c)), where (a, b, c) = s.indices(L) for the mathematical length L."
    source := "invariant: range slicing agrees with sequence slicing", status := .proven
    prop := ``RangeSliceSeq, thm := some ``rangeSliceSeq_proven },
  { id := "rangeslice-iter", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_iter", "fast_range_iter", "rangeiter_next", "longrangeiter_next",
      "longrangeiter_next_lock_held"]
    statement := "iter(r) yields exactly r[0], r[1], ..., r[L-1] and then stops, whichever iterator type is chosen."
    source := "invariant: iteration yields the sequence", status := .proven
    prop := ``IterForward, thm := some ``iterForward_proven },
  { id := "rangeslice-reversed", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_reverse", "fast_range_iter", "rangeiter_next", "longrangeiter_next",
      "longrangeiter_next_lock_held"]
    statement := "reversed(r) yields exactly r[L-1], ..., r[0] and then stops, whichever iterator type is chosen (including near +-2**63 and +-2**64)."
    source := "invariant: reversed yields the sequence backwards", status := .proven
    prop := ``IterReversed, thm := some ``iterReversed_proven },
  { id := "rangeslice-iter-reduce", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_iterator___reduce___impl", "longrange_iterator___reduce___impl",
      "range_iterator___length_hint___impl", "longrange_iterator___length_hint___impl"]
    statement := "After any number of next() calls on iter(r) or reversed(r), __length_hint__ is the number of remaining values and the range in __reduce__ yields exactly those values."
    source := "invariant: pickling round-trip", status := .proven
    prop := ``IterReduceResumes, thm := some ``iterReduceResumes_proven
    notes := "Holds for range_iterator only because range_iter/range_reverse check that start + len*step fits in a long; range_iterator___reduce___impl's len*step may itself wrap (benign under -fno-strict-overflow)." },
  { id := "rangeslice-setstate-clips", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_iterator___setstate___impl"]
    statement := "it.__setstate__(state) clips any int state into [0, len] for every range iterator, as longrange_iterator does."
    source := "invariant: fast path (range_iterator) agrees with slow path (longrange_iterator)", status := .refuted
    prop := ``SetstateClips, thm := some ``setstateClips_refuted
    bug := some "rangeslice-iter-setstate-fast-slow-mismatch"
    notes := "range_iterator raises OverflowError for |state| > LONG_MAX. Low value: maintainers called setstate type differences implementation details in PR 141317." },
  { id := "rangeslice-setstate-skips", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_iterator___setstate___impl", "longrange_iterator___setstate___impl"]
    statement := "For a state that fits a C long (any int on longrange_iterator), it.__setstate__(state) moves the iterator exactly as max(0, min(state, len)) calls of next() would."
    source := "invariant: __setstate__ restores an iteration position (range_iterator___reduce___impl and __setstate__ pair for pickling)", status := .proven
    prop := ``SetstateSkips, thm := some ``setstateSkips_proven
    notes := "The hypothesis on range_iterator is exactly the refuted rangeslice-setstate-clips." },
  { id := "rangeslice-setstate-state-types", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_iterator___setstate___impl", "longrange_iterator___setstate___impl"]
    statement := "longrange_iterator.__setstate__ raises TypeError for every state that is not an exact int, without calling __index__; range_iterator.__setstate__ takes the value of an int subclass or of __index__ and propagates what __index__ raises."
    source := "rangeobject.c:929-931 vs :1103-1106", status := .proven
    prop := ``SetstateStateTypes, thm := some ``setstateStateTypes_proven
    notes := "The twins differ on bool and __index__ by design: PR 141317's review calls that an implementation detail." },
  { id := "rangeslice-getindices-contract", pyFile := "Objects/sliceobject.c"
    pyFns := ["PySlice_GetIndices"]
    statement := "PySlice_GetIndices returns -1 whenever it leaves an exception set."
    source := "Doc/c-api/slice.rst:32-40", status := .refuted
    prop := ``GetIndicesContract, thm := some ``getIndicesContract_refuted
    bug := some "rangeslice-pyslice-getindices-success-with-exception" },
  { id := "rangeslice-slice-hash-eq", pyFile := "Objects/sliceobject.c", pyFns := ["slice_hash", "slice_richcompare"]
    statement := "If the parts' __hash__ agrees with == (equal parts hash alike), equal slices have equal hashes, and a part whose hash raises makes both raise alike."
    source := "invariant: the __hash__/__eq__ contract (Doc/reference/datamodel.rst, object.__hash__)", status := .proven
    prop := ``SliceHash.SliceHashEq, thm := some ``SliceHash.sliceHashEq_proven
    notes := "sliceHash is checked against hash(slice(a, b, c)) for int parts by the rangeslice difftest; sliceHashEq_needs_precondition shows the assumption is needed." },
  { id := "rangeslice-range-bool", pyFile := "Objects/rangeobject.c", pyFns := ["range_bool"]
    statement := "bool(r) is true exactly when the range has a first element, for every range object, without raising even when len(r) overflows."
    source := "invariant: truth of a sequence is non-emptiness (Doc/library/stdtypes.rst, truth value testing)", status := .proven
    prop := ``RangeBoolNonEmpty, thm := some ``rangeBoolNonEmpty_proven },
  { id := "rangeslice-range-reduce-round-trip", pyFile := "Objects/rangeobject.c", pyFns := ["range_reduce", "range_new", "range_vectorcall"]
    statement := "Calling range(*args) or range.__new__(range, *args) with r.__reduce__()'s arguments rebuilds a range object equal to r, field for field, for every range object."
    source := "invariant: pickling round-trips", status := .proven
    prop := ``RangeReduceRoundTrip, thm := some ``rangeReduceRoundTrip_proven
    notes := "The keyword and argument-object behaviour of both entry points is rangeslice-range-call-objects." },
  { id := "rangeslice-len-exact", pyFile := "Objects/rangeobject.c"
    pyFns := ["compute_range_length", "compute_range_length_long", "get_len_of_range"]
    statement := "get_len_of_range returns the mathematical length for all C long arguments; compute_range_length_long answers exactly when the arguments fit a long and the length is at most LONG_MAX; the PyLong slow path and compute_range_length itself return the mathematical length for all Python ints (non-zero step)."
    source := "invariant: every length path computes len(range(start, stop, step))", status := .proven
    prop := ``RangeLengthExact, thm := some ``rangeLengthExact_proven },
  { id := "rangeslice-range-call-objects", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_from_array", "validate_step", "range_new", "range_vectorcall", "make_range_object"]
    statement := "range(*args, **kw) and range.__new__(range, *args, **kw) agree for all objects; any keyword is a TypeError; 0 and >3 arguments are TypeErrors; otherwise start, stop and step go through PyNumber_Index in that order (first failure wins, a raising or non-int __index__ propagates), a zero step is the ValueError only after both conversions, and the result stores the converted values and the mathematical length."
    source := "Doc/library/stdtypes.rst (range: arguments must be integers or objects with __index__; step zero raises ValueError)", status := .proven
    prop := ``RangeCallObj, thm := some ``rangeCallObj_proven
    notes := "numberIndex mirrors PyNumber_Index (Objects/abstract.c:1410-1463) including the DeprecationWarning for an int-subclass __index__ result; the difftest drives it with int subclasses, bool, __index__ objects that raise, return non-ints or int subclasses, and non-index objects." },
  { id := "rangeslice-subscript-objects", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_subscript", "compute_range_item"]
    statement := "r[item]: an object with __index__ is converted by PyNumber_Index (its error propagates) and indexes the sequence (IndexError outside -L..L-1); a slice gives compute_slice's range; anything else is TypeError('range indices must be integers or slices, not <type>')."
    source := "invariant: sequence indexing; Doc/reference/datamodel.rst (__getitem__ takes integers or slices)", status := .proven
    prop := ``SubscriptObj, thm := some ``subscriptObj_proven },
  { id := "rangeslice-richcompare", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_richcompare", "range_equals"]
    statement := "range.__eq__/__ne__ return NotImplemented for a non-range; the four orderings return NotImplemented; a range equals itself; against another range == is True exactly when lengths and elements agree, and != is its negation."
    source := "Doc/library/stdtypes.rst (ranges compare as sequences with == and !=)", status := .proven
    prop := ``RichcompareObj, thm := some ``richcompareObj_proven },
  { id := "rangeslice-hash-key", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_hash"]
    statement := "hash(r) is the hash of (L, None, None), (L, r[0], None) or (L, r[0], step) for L == 0, 1, or more; two ranges hash the same tuple exactly when they compare equal."
    source := "invariant: hash consistent with equality (Doc/reference/datamodel.rst, object.__hash__)", status := .proven
    prop := ``RangeHashObj, thm := some ``rangeHashObj_proven },
  { id := "rangeslice-search-dispatch", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_contains", "range_count", "range_index"]
    statement := "x in r, r.count(x), r.index(x): an exact int or bool takes the arithmetic path and never calls __eq__; every other object (int subclass instances included) runs _PySequence_IterSearch over r[0], ..., r[L-1] in order, threading a stateful, re-entrant, fallible __eq__ through the calls."
    source := "rangeobject.c:507-511, :634-645, :654-660 (PyLong_CheckExact || PyBool_Check)", status := .proven
    prop := ``SearchDispatch, thm := some ``searchDispatch_proven
    notes := "_PySequence_IterSearch is mirrored locally (Search.lean) rather than imported from TypeObj, whose world model does not connect to Range." },
  { id := "rangeslice-search-exact", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_contains", "range_count", "range_index"]
    statement := "For a stateless comparison, the search gives: in/index -> 0 and ValueError when no element compares true, 1 and the first true position k (OverflowError once k passes PY_SSIZE_T_MAX), the first exception propagated; count -> the number of true comparisons, the first exception propagated, OverflowError at the PY_SSIZE_T_MAX + 1-th."
    source := "count/index/__contains__ docstrings; invariant", status := .proven
    prop := ``SearchPureExact, thm := some ``searchPureExact_proven },
  { id := "rangeslice-search-twin", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_contains", "range_count", "range_index"]
    statement := "For a probe that compares equal to the int v (a float, an int subclass keeping int.__eq__), in and count agree with the int path for v, and index agrees on members (up to the PY_SSIZE_T_MAX overflow) and raises ValueError with the generic sequence message instead of 'range.index(x): x not in range' for non-members."
    source := "invariant: the arithmetic fast path agrees with the generic search", status := .proven
    prop := ``SearchTwin, thm := some ``searchTwin_proven
    notes := "The non-member message differs between the two paths (range(5).index(5.0) vs range(5).index(5)); a cosmetic twin difference, not filed." },
  { id := "rangeslice-iter-choice", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_iter", "fast_range_iter"]
    statement := "iter(r) is range_iterator(start, step, L) exactly when start, stop and step fit a C long, L <= LONG_MAX and (for L > 0) stop + step - 1 <= LONG_MAX (step > 0) or stop + step + 1 >= LONG_MIN (step < 0); otherwise longrange_iterator(start, step, L); with range_iterator, start + L*step fits a C long."
    source := "invariant: rangeobject.c:1236-1267 (the overflow check for lstart + ulen * lstep)", status := .proven
    prop := ``IterChoice, thm := some ``iterChoice_proven
    notes := "The choice is observable: range_iterator.__setstate__ accepts True and __index__ objects, longrange_iterator's raises TypeError (rangeslice-setstate-state-types)." },
  { id := "rangeslice-reverse-choice", pyFile := "Objects/rangeobject.c"
    pyFns := ["range_reverse", "fast_range_iter"]
    statement := "reversed(r) is range_iterator(start + (L-1)*step, -step, L) exactly when start, stop and step fit a C long, step != LONG_MIN, start - step fits a C long and L <= LONG_MAX; otherwise longrange_iterator with the same fields."
    source := "invariant: rangeobject.c:1292-1300 (reversed(range(a, b, s)) is range(a + (n-1)*s, a - s, -s))", status := .proven
    prop := ``ReverseChoice, thm := some ``reverseChoice_proven }
]

end PyLean.RangeSlice
