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
import PyLean.Accel.HeapqSelect
import PyLean.Accel.HeapqSelectBase
import PyLean.Accel.HeapqSelectHonest
import PyLean.Accel.HeapqSelectSim
import PyLean.Accel.HeapqSelectSimK
import PyLean.Accel.HeapqSelectProps
import PyLean.Accel.HeapqMergeProps
import PyLean.Accel.HeapqStable
import PyLean.Accel.HeapqMergeBase
import PyLean.Accel.HeapqMergeSorted
import PyLean.Accel.SelectDiff
import PyLean.Accel.Diff

/-!
C accelerators vs. their pure-Python twins: `bisect` (`Modules/_bisectmodule.c`
vs `Lib/bisect.py`) and `heapq` (`Modules/_heapqmodule.c` vs `Lib/heapq.py`),
CPython 3.15.2.

`bisect` is modelled over int elements compared with `<` and pure key functions; mutation of
the list during a comparison is out of scope there. `nsmallest`, `nlargest` and `merge` are
modelled in `Accel/HeapqSelect.lean` over any element type with fallible, stateful callbacks
(`<`, `==`, `>`, the key, `iter`, `next`, `len`), `merge` as a generator; the pure models of
`Accel/Select.lean` are reused, through int codes, in the proofs.

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
  { id := "accel-heap-twins-agree-any-seq", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["_heapq_heappush_impl", "siftdown", "heappush", "_siftdown"]
    statement := "Without the exact-list scope of accel-heap-twins-agree: for every first argument (a list subclass, seen by Python through its own methods and by C through the raw storage, or a non-list), the C and Python heap functions agree."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``Heapq.HeapTwinsAgreeAnySeq, thm := some ``Heapq.heapTwinsAgreeAnySeq_refuted
    bug := some "accel-heapq-list-subclass-overrides"
    notes := "heappush(LoggedList([1, 2, 3]), 0) for a list subclass overriding append: same list, but only Python calls the override. heapify(()) raises TypeError in C and returns None in Python (reproducer)." },
  { id := "accel-nselect-sorted-prefix", pyFile := "Lib/heapq.py"
    pyFns := ["nsmallest", "nlargest"]
    statement := "For every element type, strict weak order < (== its equivalence), pure key or None, n >= 0, C or Python heap functions, correct list.sort, and iterable yielding xs whose len() is the count or is missing: nsmallest(n, it, key) == sorted(it, key=key)[:n] and nlargest(n, it, key) == sorted(it, key=key, reverse=True)[:n], ties included."
    source := "nsmallest/nlargest docstrings, Lib/heapq.py:477-481, :537-541; Doc/library/heapq.rst", status := .proven
    prop := ``Heapq.NSelectIsSortedPrefix, thm := some ``Heapq.nSelectIsSortedPrefix_proven
    notes := "Covers the n == 1 min()/max() path, the n >= len sorted() path and both heap paths with their (elem, order) and (key, order, elem) tuples, whose comparisons call == and < of the elements. list.sort and list() are callees in Objects/listobject.c, taken as a parameter with the contract SortOk (a stable sort for a strict weak order). Negative n excluded (python/cpython#57483); == and > are taken to follow the language reference's consistency rules for a total ordering (Doc/reference/expressions.rst:2201-2237); breaking them is out of scope (python/cpython#158718)." },
  { id := "accel-nselect-any-len", pyFile := "Lib/heapq.py"
    pyFns := ["nsmallest", "nlargest"]
    statement := "As accel-nselect-sorted-prefix for every len() result."
    source := "nsmallest/nlargest docstrings, Lib/heapq.py:477-481, :537-541", status := .refuted
    prop := ``Heapq.NSelectAnyLen, thm := some ``Heapq.nSelectAnyLen_refuted
    bug := some "accel-heapq-select-trusts-len"
    notes := "nsmallest(2, it) for an it yielding 3, 1, 2 with len(it) == 0 returns all three: 3.15 returns sorted(iterable) whole when n >= len(iterable)." },
  { id := "accel-merge-first-next", pyFile := "Lib/heapq.py"
    pyFns := ["merge"]
    statement := "For every element type, strict weak order (== its equivalence), pure key, reverse, and C or Python heap functions, the first next() on merge(*inputs) pulls exactly one item from each non-empty input and yields a head no other head's key is below (above with reverse=True); with only empty inputs it is exhausted."
    source := "merge docstring, Lib/heapq.py:331-335", status := .proven
    prop := ``Heapq.MergeFirstNext, thm := some ``Heapq.mergeFirstNext_proven },
  { id := "accel-merge-no-silent-drop", pyFile := "Lib/heapq.py"
    pyFns := ["merge"]
    statement := "With honest inputs and comparisons and any fallible key, list(merge(*inputs, key=key)) either raises or returns every input item."
    source := "merge docstring, Lib/heapq.py:331-345", status := .refuted
    prop := ``Heapq.MergeNoSilentDrop, thm := some ``Heapq.mergeNoSilentDrop_refuted
    bug := some "accel-heapq-merge-swallows-stopiteration"
    notes := "list(merge([1, 5], [2], key=key)) with key(5) raising StopIteration returns [1, 2]: the except StopIteration meant for an exhausted input (:391, :403) also catches the key's." },
  { id := "accel-merge-sorted", pyFile := "Lib/heapq.py"
    pyFns := ["merge"]
    statement := "For inputs each sorted by key (descending if reverse), list(merge(*inputs, key, reverse)) == sorted(chain(*inputs), key=key, reverse=reverse), ties included, for every element type with a strict weak order and a pure key, and for iterators whose __next__ is a bound method (next.__self__ is the iterator: SEnv.selfOf the identity); accel-merge-sorted-any-iter refutes it without that restriction."
    source := "merge docstring, Lib/heapq.py:330-346; Doc/library/heapq.rst", status := .proven
    prop := ``Heapq.MergeIsSorted, thm := some ``Heapq.mergeIsSorted_proven
    notes := "Over the generator model for both heap implementations, by an invariant (HeapqMergeSorted.MInv) held at every suspension point: per-input iterator positions, one heap entry (by reference) per non-empty input, heap order. It unfolds the main loop (:370-378 / :394-404, both the next() and the StopIteration branch) and the single-input tail with next.__self__ (:379-383 / :405-408). Scope: honest inputs, whose next.__self__ is the iterator itself; a staticmethod __next__ raises AttributeError there (modelled as SEnv.selfOf, difftested), refuted as accel-merge-sorted-any-iter." },
  { id := "accel-merge-sorted-any-iter", pyFile := "Lib/heapq.py"
    pyFns := ["merge"]
    statement := "accel-merge-sorted with next.__self__ (Lib/heapq.py:383, :408) any callback, so for every iterator the protocol allows, including one whose __next__ is a staticmethod."
    source := "merge docstring, Lib/heapq.py:331-345; iterator protocol, Doc/library/stdtypes.rst", status := .refuted
    prop := ``Heapq.MergeIsSortedAnyIter, thm := some ``Heapq.mergeIsSortedAnyIter_refuted
    bug := some "accel-heapq-merge-staticmethod-next"
    notes := "merge(It()) over [1, 2, 3], It's __next__ a staticmethod: the first next() yields 1, the second reaches yield from next.__self__ with one input left and raises AttributeError: 'function' object has no attribute '__self__' (HeapqMergeSorted.mergeStatic_run, by the kernel, for both heap implementations). Measured on 3.15.2 for both heaps, keyed and unkeyed; merge([0, 1], It()) gives 0, 1, 1 then the same error." }
]

end PyLean.Accel
