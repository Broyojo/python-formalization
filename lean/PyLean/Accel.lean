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
import PyLean.Accel.Diff

/-!
C accelerators vs. their pure-Python twins: `bisect` (`Modules/_bisectmodule.c`
vs `Lib/bisect.py`) and `heapq` (`Modules/_heapqmodule.c` vs `Lib/heapq.py`),
CPython 3.14.7, over int elements compared with `<` and pure key functions.
Mutation of the list during a comparison is out of scope.
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
    pyFns := ["bisect_left", "bisect_right", "insort_left", "insort_right"]
    statement := "For lo and hi in Py_ssize_t range and hi != -1, the C and Python bisect/insort functions agree exactly (value or exception and message, and final list)."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``BisectTwinsAgreeInRange, thm := some ``bisectTwinsAgreeInRange_proven
    notes := "The two hypotheses are exactly the refuted cases above. On main the negative-lo message differs (see accel-bisect-ssize-bounds)." },
  { id := "accel-bisect-left-partition", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_left"]
    statement := "For a sorted by key and 0 <= lo <= hi <= len(a), both twins return the same ip in [lo, hi] with key(e) < x on a[lo:ip] and key(e) >= x on a[ip:hi]."
    source := "bisect_left docstring, Lib/bisect.py:77-79; Doc/library/bisect.rst:48-51", status := .proven
    prop := ``BisectLeftPartition, thm := some ``bisectLeftPartition_proven },
  { id := "accel-bisect-right-partition", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_right"]
    statement := "For a sorted by key and 0 <= lo <= hi <= len(a), both twins return the same ip in [lo, hi] with key(e) <= x on a[lo:ip] and key(e) > x on a[ip:hi]."
    source := "bisect_right docstring, Lib/bisect.py:24-26; Doc/library/bisect.rst:71-74", status := .proven
    prop := ``BisectRightPartition, thm := some ``bisectRightPartition_proven },
  { id := "accel-bisect-doc-partition", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_left", "bisect_right"]
    statement := "For a sorted by key and any lo, hi: whenever a twin returns ip, the slices a[lo:ip] and a[ip:hi] satisfy the documented partition."
    source := "Doc/library/bisect.rst:48-51 and :74-77", status := .refuted
    prop := ``BisectDocPartition, thm := some ``bisectDocPartition_refuted
    bug := some "accel-bisect-hi-minus-one"
    notes := "Negative hi: the search range is empty but a[ip:hi] uses negative-index slicing (python/cpython#125889)." },
  { id := "accel-bisect-doc-partition-nonneg-hi", pyFile := "Lib/bisect.py"
    pyFns := ["bisect_left", "bisect_right"]
    statement := "For a sorted by key, any lo and hi=None or hi >= 0 (including lo > hi and hi > len(a)): whenever either twin returns ip, the documented slice partition holds."
    source := "Doc/library/bisect.rst:48-51 and :74-77", status := .proven
    prop := ``BisectDocPartitionNonnegHi, thm := some ``bisectDocPartitionNonnegHi_proven
    notes := "For hi > len(a) the search either returns a correct ip or raises IndexError; it never returns a wrong one." },
  { id := "accel-insort-keeps-sorted", pyFile := "Lib/bisect.py"
    pyFns := ["insort_left", "insort_right"]
    statement := "For a sorted by key and default lo/hi, both twins of insort_left and insort_right leave a list sorted by key that is a permutation of a plus x."
    source := "insort docstrings, Lib/bisect.py:4-8 and :57-61", status := .proven
    prop := ``InsortKeepsSorted, thm := some ``insortKeepsSorted_proven },
  { id := "accel-heap-twins-agree", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["heappush", "heappop", "heapreplace", "heappushpop", "heappush_max", "heappop_max",
      "heapreplace_max", "heappushpop_max"]
    statement := "For every element type and comparison, the C and Python heappush/heappop/heapreplace/heappushpop (and _max variants) return the same item, leave the same list, and raise exceptions of the same class."
    source := "invariant: C accelerator vs pure-Python twin", status := .proven
    prop := ``HeapTwinsAgree, thm := some ``heapTwinsAgree_proven },
  { id := "accel-heap-twins-agree-exact", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["heappop", "heapreplace", "heappop_max", "heapreplace_max"]
    statement := "The C and Python heappop and heapreplace agree including the exception message."
    source := "invariant: C accelerator vs pure-Python twin", status := .refuted
    prop := ``HeapTwinsAgreeExact, thm := some ``heapTwinsAgreeExact_refuted
    bug := some "accel-heapq-empty-error-message"
    notes := "Empty heap: C says 'index out of range', Python 'pop from empty list' / 'list index out of range'." },
  { id := "accel-heapify-twins-agree", pyFile := "Modules/_heapqmodule.c"
    pyFns := ["heapify", "heapify_max", "cache_friendly_heapify"]
    statement := "For every element type, comparison and length, the C heapify (cache-friendly order above 2500 items) builds the same list as the Python heapify."
    source := "invariant: C accelerator vs pure-Python twin; comment at Modules/_heapqmodule.c:312-330", status := .proven
    prop := ``HeapifyTwinsAgree, thm := some ``heapifyTwinsAgree_proven
    notes := "Above 2500 items the C order (row R-1 climbs, then row R climbs) is a different children-first order; any such order yields the same heap because siftup at k only reads and writes the subtree of k." },
  { id := "accel-heap-ops-invariant", pyFile := "Lib/heapq.py"
    pyFns := ["heappush", "heappop", "heapreplace", "heappushpop", "heappush_max", "heappop_max",
      "heapreplace_max", "heappushpop_max"]
    statement := "On an int min-heap (max-heap for _max), every operation leaves a heap, permutes the items as documented, and pops/returns the smallest (largest) item."
    source := "Lib/heapq.py:3-6 and docstrings; Doc/library/heapq.rst:56-145", status := .proven
    prop := ``HeapOpsKeepInvariant, thm := some ``heapOpsKeepInvariant_proven },
  { id := "accel-heapify-makes-heap", pyFile := "Lib/heapq.py"
    pyFns := ["heapify", "heapify_max"]
    statement := "heapify and heapify_max turn any int list into a min-heap / max-heap with the same items."
    source := "Lib/heapq.py:171-180, :211-215; Doc/library/heapq.rst:56-58, :104-106", status := .proven
    prop := ``HeapifyMakesHeap, thm := some ``heapifyMakesHeap_proven },
  { id := "accel-nsmallest-sorted-prefix", pyFile := "Lib/heapq.py"
    pyFns := ["nsmallest"]
    statement := "For n >= 0, nsmallest(n, iterable, key) == sorted(iterable, key=key)[:n], ties included, for sized and unsized iterables."
    source := "nsmallest docstring, Lib/heapq.py:477-481; Doc/library/heapq.rst:183-188", status := .proven
    prop := ``NsmallestIsSortedPrefix, thm := some ``nsmallestIsSortedPrefix_proven
    notes := "Covers the n == 1 min() shortcut, the n >= len sorted() shortcut and both heap branches. Negative n is excluded: its meaning is undefined (python/cpython#57483); nsmallest returns [] there while sorted(...)[:n] drops items." },
  { id := "accel-nlargest-sorted-prefix", pyFile := "Lib/heapq.py"
    pyFns := ["nlargest"]
    statement := "For n >= 0, nlargest(n, iterable, key) == sorted(iterable, key=key, reverse=True)[:n], ties included."
    source := "nlargest docstring, Lib/heapq.py:537-541; Doc/library/heapq.rst:174-180", status := .proven
    prop := ``NlargestIsSortedPrefix, thm := some ``nlargestIsSortedPrefix_proven
    notes := "As for nsmallest; negative n excluded (python/cpython#57483)." },
  { id := "accel-merge-sorted", pyFile := "Lib/heapq.py"
    pyFns := ["merge"]
    statement := "For inputs sorted by key (descending if reverse), list(merge(*its, key, reverse)) == sorted(chain(*its), key=key, reverse=reverse), ties included."
    source := "merge docstring, Lib/heapq.py:330-346; Doc/library/heapq.rst:149-171", status := .proven
    prop := ``MergeIsSorted, thm := some ``mergeIsSorted_proven }
]

end PyLean.Accel
