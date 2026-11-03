import PyLean.Registry
import PyLean.Accel.Bisect
import PyLean.Accel.Heap
import PyLean.Accel.Select
import PyLean.Accel.BisectProps
import PyLean.Accel.HeapTwins
import PyLean.Accel.HeapCorrect
import PyLean.Accel.HeapProps
import PyLean.Accel.HeapifyLocal
import PyLean.Accel.HeapifyLocalCanon
import PyLean.Accel.HeapifyLocalOrder
import PyLean.Accel.HeapifyLocalC
import PyLean.Accel.HeapifyTwins
import PyLean.Accel.StableSort
import PyLean.Accel.Selection
import PyLean.Accel.SelectProps
import PyLean.Accel.MergeProps
import PyLean.Accel.HeapqModel
import PyLean.Accel.HeapqRobust
import PyLean.Accel.HeapqCRobust
import PyLean.Accel.HeapqTwins
import PyLean.Accel.HeapqTwinsPub
import PyLean.Accel.HeapqBridge
import PyLean.Accel.HeapqProps
import PyLean.Accel.Diff

/-!
C accelerators vs. their pure-Python twins: `bisect` (`Modules/_bisectmodule.c`
vs `Lib/bisect.py`) and `heapq` (`Modules/_heapqmodule.c` vs `Lib/heapq.py`),
CPython 3.15.2.

`bisect`, `nsmallest`, `nlargest` and `merge` are modelled over int elements compared with `<`
and pure key functions; mutation of the list during a comparison is out of scope there.

The heap primitives (`heappush` ... `heapify` and the `*_max` variants) are modelled in
`Accel/HeapqModel.lean` over any element type with comparisons that are Python code: they may
raise, return an object whose truth test raises, keep state, and read or mutate the heap list.
The Python twin runs over any sequence object (duck typing); C checks `PyList_Check` and uses
the raw list storage. The pure models of `Accel/Heap.lean` are the honest-comparison special
case (`Accel/HeapqBridge.lean`).
-/

namespace PyLean.Accel

open PyLean.Registry

def entries : List Entry := [
  { id := "accel-bisect-twins-agree", pyFile := "Modules/_bisectmodule.c"
    pyFns := ["bisect_left", "bisect_right", "insort_left", "insort_right"]
    statement := "For every list, x, lo, hi and key, the C and Python bisect/insort functions return the same value (or raise the same exception and message) and leave the same list."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``BisectTwinsAgree, thm := some ``bisectTwinsAgree_refuted
    bug := some "accel-bisect-hi-minus-one"
    notes := "hi=-1 is Argument Clinic's encoding of hi=None in C, so C searches the whole list while Python searches nothing." },
  { id := "accel-bisect-twins-agree-hi-not-minus-one", pyFile := "Modules/_bisectmodule.c"
    pyFns := ["bisect_left", "bisect_right", "insort_left", "insort_right"]
    statement := "Excluding hi=-1, the C and Python bisect/insort functions agree for every int lo and hi."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``BisectTwinsAgreeHiNotMinusOne, thm := some ``bisectTwinsAgreeHiNotMinusOne_refuted
    bug := some "accel-bisect-ssize-bounds"
    notes := "lo or hi outside Py_ssize_t: C raises OverflowError at argument parsing, Python returns lo or raises ValueError/IndexError." },
  { id := "accel-bisect-twins-agree-in-range", pyFile := "Modules/_bisectmodule.c"
    pyFns := ["bisect_left"]
    statement := "For lo and hi in Py_ssize_t range and hi != -1, the C and Python bisect/insort functions agree exactly (value or exception and message, and final list)."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``BisectTwinsAgreeInRange, thm := some ``bisectTwinsAgreeInRange_refuted
    bug := some "accel-bisect-negative-lo-message"
    notes := "Proven on 3.14.7. On 3.15.2 a negative lo gives 'lo cannot be negative' in C and 'lo must be non-negative' in Python." },
  { id := "accel-bisect-twins-agree-nonneg-lo", pyFile := "Modules/_bisectmodule.c"
    pyFns := ["bisect_left", "bisect_right", "insort_left", "insort_right"]
    statement := "For 0 <= lo <= sys.maxsize, hi in Py_ssize_t range and hi != -1, the C and Python bisect/insort functions agree exactly (value or exception and message, and final list)."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``BisectTwinsAgreeNonnegLo, thm := some ``bisectTwinsAgreeNonnegLo_proven
    notes := "The three hypotheses are exactly the refuted cases above." },
  { id := "accel-bisect-negative-lo-raises", pyFile := "Modules/_bisectmodule.c"
    pyFns := ["bisect_left", "bisect_right", "insort_left", "insort_right"]
    statement := "For every negative lo that fits a Py_ssize_t and every hi, including hi that C cannot convert, both twins raise ValueError with their own message."
    source := "bisect docs on lo/hi; clinic/_bisectmodule.c.h:96-100 vs Lib/bisect.py:34-35", status := .proven
    prop := ``BisectNegativeLoRaises, thm := some ``bisectNegativeLoRaises_proven
    notes := "C checks lo while parsing it, so a negative lo wins over an hi outside Py_ssize_t. That is new in 3.15: 3.14.7 raised OverflowError for such an hi." },
  { id := "accel-bisect-left-partition", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_left"]
    statement := "For a sorted by key and 0 <= lo <= hi <= len(a), both twins return the same ip in [lo, hi] with key(e) < x on a[lo:ip] and key(e) >= x on a[ip:hi]."
    source := "bisect_left docstring, Lib/bisect.py:77-79; Doc/library/bisect.rst:48-51", status := .proven
    prop := ``BisectLeftPartition, thm := some ``bisectLeftPartition_proven },
  { id := "accel-bisect-right-partition", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_right"]
    statement := "For a sorted by key and 0 <= lo <= hi <= len(a), both twins return the same ip in [lo, hi] with key(e) <= x on a[lo:ip] and key(e) > x on a[ip:hi]."
    source := "bisect_right docstring, Lib/bisect.py:24-26; Doc/library/bisect.rst:70-72", status := .proven
    prop := ``BisectRightPartition, thm := some ``bisectRightPartition_proven },
  { id := "accel-bisect-doc-partition", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_left", "bisect_right"]
    statement := "For a sorted by key and any lo, hi: whenever a twin returns ip, the slices a[lo:ip] and a[ip:hi] satisfy the documented partition."
    source := "Doc/library/bisect.rst:48-51 and :70-72", status := .refuted
    prop := ``BisectDocPartition, thm := some ``bisectDocPartition_refuted
    bug := some "accel-bisect-hi-minus-one"
    notes := "Negative hi: the search range is empty but a[ip:hi] uses negative-index slicing (python/cpython#125889)." },
  { id := "accel-bisect-doc-partition-nonneg-hi", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_left", "bisect_right"]
    statement := "For a sorted by key, any lo and hi=None or hi >= 0 (including lo > hi and hi > len(a)): whenever either twin returns ip, the documented slice partition holds."
    source := "Doc/library/bisect.rst:48-51 and :70-72", status := .proven
    prop := ``BisectDocPartitionNonnegHi, thm := some ``bisectDocPartitionNonnegHi_proven
    notes := "For hi > len(a) the search either returns a correct ip or raises IndexError; it never returns a wrong one." },
  { id := "accel-insort-keeps-sorted", pyFile := "Lib/bisect.py"
    pyFns := ["insort_left", "insort_right"]
    statement := "For a sorted by key and default lo/hi, both twins of insort_left and insort_right leave a list sorted by key that is a permutation of a plus x."
    source := "insort docstrings, Lib/bisect.py:4-8 and :57-61", status := .proven
    prop := ``InsortKeepsSorted, thm := some ``insortKeepsSorted_proven },
  { id := "accel-heap-twins-agree", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["siftdown", "siftup", "siftdown_max", "siftup_max",
      "_heapq_heappush_impl", "heappop_internal", "_heapq_heappop_impl", "heapreplace_internal",
      "_heapq_heapreplace_impl", "_heapq_heappushpop_impl", "heapify_internal", "_heapq_heapify_impl",
      "_heapq_heappush_max_impl", "_heapq_heappop_max_impl", "_heapq_heapreplace_max_impl",
      "_heapq_heappushpop_max_impl", "_heapq_heapify_max_impl",
      "heappush", "heappop", "heapreplace", "heappushpop", "heapify", "heappush_max", "heappop_max",
      "heapreplace_max", "heappushpop_max", "heapify_max", "_siftdown", "_siftup", "_siftdown_max",
      "_siftup_max"]
    statement := "For every element type and every comparison that neither reads nor writes the heap list (it may raise in __lt__ or in the truth test of its result, and keep state), the C and Python heappush/heappop/heapreplace/heappushpop/heapify (heapify up to 2500 items) and their _max variants make the same comparisons in the same order, return the same item and leave the same list, or raise the same exception (on an empty heap heappop/heapreplace raise IndexError with different messages)."
    source := "invariant: C accelerator vs pure-Python twin (Modules/_heapqmodule.c:1 'Drop in replacement for heapq.py')", status := .proven
    prop := ``Heapq.HeapTwinsAgree, thm := some ``Heapq.heapTwinsAgree_proven
    notes := "Python is modelled over an exact list (listSeq); a list subclass that overrides __getitem__, __setitem__, __len__, append or pop, or a non-list, is seen by Python and not by C (PyList_Check, raw storage). The lists left after a raising comparison differ (accel-heap-twins-same-list-on-raise); re-entrant comparisons and heapify above 2500 items are refuted below." },
  { id := "accel-heap-twins-agree-exact", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["heappop_internal", "_heapq_heappop_impl", "heappop"]
    statement := "For comparisons that do not touch the list, the C and Python heappop and heapreplace raise the same exception including its message."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``Heapq.HeapTwinsAgreeExact, thm := some ``Heapq.heapTwinsAgreeExact_refuted
    bug := some "accel-heapq-empty-error-message"
    notes := "Empty heap: C says 'index out of range', Python 'pop from empty list' / 'list index out of range'." },
  { id := "accel-heap-twins-agree-reentrant", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["_heapq_heappush_impl", "siftdown", "heappush", "_siftdown"]
    statement := "For every comparison, including ones that read or mutate the heap list, the C and Python heap functions agree as in accel-heap-twins-agree."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``Heapq.HeapTwinsAgreeReentrant, thm := some ``Heapq.heapTwinsAgreeReentrant_refuted
    bug := some "accel-heapq-py-twin-fallible-compare"
    notes := "heappush([1, 2, 3], 0) with a comparison that appends to the heap: C raises RuntimeError('list changed size during iteration') (_heapqmodule.c:53-57); Python has no such check and returns None." },
  { id := "accel-heap-twins-same-list-on-raise", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["heappop_internal", "_heapq_heappop_impl", "siftup", "heappop", "_siftup"]
    statement := "For comparisons that do not touch the list, the C and Python heap functions also leave the same list when a comparison raises."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``Heapq.HeapTwinsSameListOnRaise, thm := some ``Heapq.heapTwinsSameListOnRaise_refuted
    bug := some "accel-heapq-py-twin-fallible-compare"
    notes := "heappop([0..6]) with a comparison raising on its second call: C leaves [1, 6, 2, 3, 4, 5] (swaps keep every item), Python [1, 1, 2, 3, 4, 5] (its hole technique has copied 1 up and lost 6)." },
  { id := "accel-heapq-c-robust", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["siftdown", "siftup", "siftdown_max", "siftup_max",
      "_heapq_heappush_impl", "heappop_internal", "_heapq_heappop_impl", "heapreplace_internal",
      "_heapq_heapreplace_impl", "_heapq_heappushpop_impl", "heapify_internal", "_heapq_heapify_impl",
      "_heapq_heappush_max_impl", "_heapq_heappop_max_impl", "_heapq_heapreplace_max_impl",
      "_heapq_heappushpop_max_impl", "_heapq_heapify_max_impl", "cache_friendly_heapify", "keep_top_bit"]
    statement := "For every element type and every comparison (raising, with a raising truth test, stateful, reading or mutating the list), the C heap functions (and _max variants) never access the list out of bounds, raise only the comparison's exception, RuntimeError('list changed size during iteration') when the comparison can change the length, or IndexError('index out of range') on an empty heap (heappushpop: when the comparison emptied it); succeed with the documented length otherwise, and always succeed (pop/replace on a non-empty heap) when the comparison never raises and never changes the length; a non-list argument raises clinic's TypeError before anything runs."
    source := "invariant: no crash, no internal error; Modules/_heapqmodule.c:53-57, :103-107, :285-288, :435-439, :485-489; Modules/clinic/_heapqmodule.c.h", status := .proven
    prop := ``Heapq.CHeapRobust, thm := some ``Heapq.cHeapRobust_proven
    notes := "The C model reads the current list after every comparison, as the source re-reads _PyList_ITEMS (:60, :102, :442, :484); the operands are held by Py_INCREF across the call. The IndexError of siftup/siftdown (:34-37, :80-83, :417-420, :462-465) is unreachable from the public functions." },
  { id := "accel-heapify-twins-agree", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["heapify_internal", "_heapq_heapify_impl", "_heapq_heapify_max_impl",
      "cache_friendly_heapify", "keep_top_bit", "siftup", "siftup_max", "heapify", "heapify_max"]
    statement := "For every element type, every pure comparison and every length, the C heapify (cache-friendly order above 2500 items) and the Python heapify (and _max) both succeed and leave the same list."
    source := "invariant: C accelerator vs pure-Python twin; comment at Modules/_heapqmodule.c:312-330", status := .proven
    prop := ``Heapq.HeapifyTwinsAgree, thm := some ``Heapq.heapifyTwinsAgree_proven
    notes := "Above 2500 items the C order (row R-1 climbs, then row R climbs) is a different children-first order; any such order yields the same heap because siftup at k only reads and writes the subtree of k. With a fallible comparison the order is visible (accel-heapify-twins-agree-fallible)." },
  { id := "accel-heapify-twins-agree-fallible", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["_heapq_heapify_impl", "heapify_internal", "cache_friendly_heapify", "keep_top_bit",
      "siftup", "heapify", "_siftup"]
    statement := "For every comparison that does not touch the list but may raise or keep state, the C and Python heapify agree at every length."
    source := "invariant: C accelerator vs pure-Python twin; Modules/_heapqmodule.c:326-329", status := .refuted
    prop := ``Heapq.HeapifyTwinsAgreeFallible, thm := some ``Heapq.heapifyTwinsAgreeFallible_refuted
    bug := some "accel-heapq-heapify-order-raising"
    notes := "heapify(list(range(2501))) with a raising comparison: C first compares heap[2045] < heap[2046], Python heap[2499] < heap[2500]. Proven up to 2500 items in accel-heap-twins-agree." },
  { id := "accel-heap-ops-invariant", pyFile := "Lib/heapq.py"
    pyFns := ["heappush", "heappop", "heapreplace", "heappushpop", "heappush_max", "heappop_max",
      "heapreplace_max", "heappushpop_max", "_siftdown", "_siftup", "_siftdown_max", "_siftup_max"]
    statement := "For every element type and every comparison that is an honest strict weak order, on a min-heap (max-heap for _max) every operation succeeds, leaves a heap, permutes the items as documented, and pops/returns the smallest (largest) item."
    source := "Lib/heapq.py:3-4 and docstrings; Doc/library/heapq.rst", status := .proven
    prop := ``Heapq.HeapOpsKeepInvariant, thm := some ``Heapq.heapOpsKeepInvariant_proven },
  { id := "accel-heapify-makes-heap", pyFile := "Lib/heapq.py"
    pyFns := ["heapify", "heapify_max", "_siftup", "_siftdown", "_siftup_max", "_siftdown_max"]
    statement := "For every element type and honest strict weak order, heapify and heapify_max turn any list into a min-heap / max-heap with the same items."
    source := "Lib/heapq.py:171-180, :211-215; Doc/library/heapq.rst", status := .proven
    prop := ``Heapq.HeapifyMakesHeap, thm := some ``Heapq.heapifyMakesHeap_proven },
  { id := "accel-nsmallest-sorted-prefix", pyFile := "Lib/heapq.py"
    pyFns := ["nsmallest"]
    statement := "For n >= 0, nsmallest(n, iterable, key) == sorted(iterable, key=key)[:n], ties included, for sized and unsized iterables whose len() is their item count."
    source := "nsmallest docstring, Lib/heapq.py:477-481; Doc/library/heapq.rst:183-188", status := .proven
    prop := ``NsmallestIsSortedPrefix, thm := some ``nsmallestIsSortedPrefix_proven
    notes := "Covers the n == 1 min() shortcut, the n >= len sorted() shortcut and both heap branches. Negative n is excluded: its meaning is undefined (python/cpython#57483); nsmallest returns [] there while sorted(...)[:n] drops items. The hypothesis on len() is refuted below as accel-nsmallest-any-len." },
  { id := "accel-nsmallest-any-len", pyFile := "Lib/heapq.py"
    pyFns := ["nsmallest"]
    statement := "For n >= 0 and any len(iterable), nsmallest(n, iterable, key) == sorted(iterable, key=key)[:n]."
    source := "nsmallest docstring, Lib/heapq.py:477-481; Doc/library/heapq.rst:183-188", status := .refuted
    prop := ``NsmallestAnyLen, thm := some ``nsmallestAnyLen_refuted
    bug := some "accel-heapq-select-trusts-len"
    notes := "True on 3.14.7, which sliced. 3.15 returns sorted(iterable) whole when n >= len(iterable), so a __len__ below the item count gives more than n items." },
  { id := "accel-nlargest-sorted-prefix", pyFile := "Lib/heapq.py"
    pyFns := ["nlargest"]
    statement := "For n >= 0, nlargest(n, iterable, key) == sorted(iterable, key=key, reverse=True)[:n], ties included, for sized and unsized iterables whose len() is their item count."
    source := "nlargest docstring, Lib/heapq.py:537-541; Doc/library/heapq.rst:174-180", status := .proven
    prop := ``NlargestIsSortedPrefix, thm := some ``nlargestIsSortedPrefix_proven
    notes := "As for nsmallest; negative n excluded (python/cpython#57483)." },
  { id := "accel-nlargest-any-len", pyFile := "Lib/heapq.py"
    pyFns := ["nlargest"]
    statement := "For n >= 0 and any len(iterable), nlargest(n, iterable, key) == sorted(iterable, key=key, reverse=True)[:n]."
    source := "nlargest docstring, Lib/heapq.py:537-541; Doc/library/heapq.rst:174-180", status := .refuted
    prop := ``NlargestAnyLen, thm := some ``nlargestAnyLen_refuted
    bug := some "accel-heapq-select-trusts-len"
    notes := "As accel-nsmallest-any-len." },
  { id := "accel-merge-sorted", pyFile := "Lib/heapq.py"
    pyFns := ["merge"]
    statement := "For inputs sorted by key (descending if reverse), list(merge(*its, key, reverse)) == sorted(chain(*its), key=key, reverse=reverse), ties included."
    source := "merge docstring, Lib/heapq.py:330-346; Doc/library/heapq.rst:149-171", status := .proven
    prop := ``MergeIsSorted, thm := some ``mergeIsSorted_proven }
]

end PyLean.Accel
