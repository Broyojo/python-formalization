import PyLean.Registry
import PyLean.ListSort.Props
import PyLean.ListSort.Diff

/-!
`list.sort` (powersort/timsort in `Objects/listobject.c`, `Objects/listsort.txt`), CPython 3.15.2.

The model (`ListSort/Model.lean`) mirrors `count_run`, `binarysort`,
`gallop_left`/`gallop_right`, `merge_lo`/`merge_hi`/`merge_at`, `powerloop`,
`found_new_run`, `merge_force_collapse`, the minrun generator (`merge_init`,
`minrun_next`) and the main loop of `list_sort_impl`, counting every `<` call; the
difftest checks results, exact `<`-call counts and run lengths against CPython. Items are compared by an
integer-valued key (`kf`), which covers Python ints with `<` (`kf = id`),
`(value, index)` pairs and `key=` functions returning ints; the permutation and
stack properties hold for every comparison function. Exceptions raised
by `__lt__`/`key` and mutation of the list during the sort are out of scope.
-/

namespace PyLean.ListSort

open PyLean.Registry

def entries : List Entry := [
  { id := "listsort-powerloop-first-bit", pyFile := "Objects/listobject.c", pyFns := ["powerloop"]
    statement := "For all s1, n1 >= 1, n2 >= 1, n with s1+n1+n2 <= n, powerloop(s1, n1, n2, n) returns the first bit position L >= 1 at which the binary expansions of (s1 + n1/2)/n and (s1 + n1 + n2/2)/n differ, and 2^L < 2n."
    source := "listsort.txt:446-468 (the definition of a run's power)", status := .proven
    prop := ``PowerloopFirstBit, thm := some ``powerloopFirstBit_proven },
  { id := "listsort-powerloop-no-overflow", pyFile := "Objects/listobject.c", pyFns := ["powerloop"]
    statement := "For every list length n <= 2**62 and all valid runs, no intermediate value of powerloop (2*s1 + n1, a + n1 + n2, and every shifted a, b) reaches 2**63, so the Py_ssize_t arithmetic never overflows."
    source := "invariant: no signed overflow; listsort.txt:483-488 argues it from n <= PY_SSIZE_T_MAX/sizeof(PyObject*)", status := .proven
    prop := ``PowerloopNoOverflow, thm := some ``powerloopNoOverflow_proven
    notes := "Precondition n <= 2**62: real lists have at most PY_SSIZE_T_MAX/8 = 2**60-1 items (list_resize). For 2**62 < n < 2**63 the model's overflow flag can be set (b reaches 2n-1); unreachable from Python." },
  { id := "listsort-powers-strict", pyFile := "Objects/listobject.c", pyFns := ["found_new_run", "powerloop"]
    statement := "For every list length N <= PY_SSIZE_T_MAX and every sequence of positive run lengths summing to at most N, after each found_new_run + push the powers stored on the pending stack are >= 1 and strictly increase towards the top."
    source := "listsort.txt:497-498; assert at listobject.c:2739", status := .proven
    prop := ``PolicyPowersStrict, thm := some ``policyPowersStrict_proven
    notes := "Quantifies over arbitrary run structures, not only those count_run/minrun produce. The proof keeps, per stack entry, a ghost list of the original runs merged into it." },
  { id := "listsort-stack-bound", pyFile := "Objects/listobject.c", pyFns := ["found_new_run", "list_sort_impl"]
    statement := "For every N <= PY_SSIZE_T_MAX and every non-empty sequence of positive run lengths summing to at most N, after each push the pending stack holds s entries with 2^s < 4N (s <= ceil(log2 N) + 1), and assert(ms.n < MAX_MERGE_PENDING) holds before every push."
    source := "invariant: ms->pending has MAX_MERGE_PENDING = 64 slots (listobject.c:1744, :1796); assert at :3100", status := .proven
    prop := ``PolicyStackBound, thm := some ``policyStackBound_proven },
  { id := "listsort-stack-bound-tight", pyFile := "Objects/listobject.c", pyFns := ["found_new_run"]
    statement := "The bound is attained: for N = 3 * 2**61 <= PY_SSIZE_T_MAX the runs [2**61, 2**61, 2**60, ..., 2, 1, 1] fill all 64 pending slots (and the assert still holds)."
    source := "listobject.c:1739-1743 (\"plenty large enough for all cases\")", status := .proven
    prop := ``PolicyStackTight, thm := some ``policyStackTight_proven
    notes := "MAX_MERGE_PENDING is exactly large enough for arbitrary run structures on 64-bit builds. With real runs (>= minrun >= 32 except the last) the stack stays far smaller, and real lists have < 2**60 items." },
  { id := "listsort-stack-comment-log2", pyFile := "Objects/listobject.c", pyFns := ["found_new_run"]
    statement := "For every list length n and every run structure (runs not forced to minrun), the pending stack needs at most floor(log2(n)) + 1 entries."
    source := "comment at listobject.c:1739-1743", status := .refuted
    prop := ``StackCommentLog2, thm := some ``stackCommentLog2_refuted
    bug := some "listsort-stack-comment-log2"
    notes := "n = 3, runs [1, 1, 1] reach 3 > floor(log2 3) + 1 = 2 entries; the true bound is ceil(log2 n) + 1 (listsort-stack-bound), attained (listsort-stack-bound-tight). Comment only: the code is safe." },
  { id := "listsort-sort-push-assert", pyFile := "Objects/listobject.c", pyFns := ["list_sort_impl", "count_run", "binarysort", "found_new_run"]
    statement := "For every item type, every comparison function (including inconsistent ones) and every list of length <= PY_SSIZE_T_MAX, the sort never violates assert(ms.n < MAX_MERGE_PENDING) before pushing a run."
    source := "invariant: the assert at listobject.c:3165 is compiled out of release builds, where a violation would write past ms.pending[]", status := .proven
    prop := ``SortPushAssert, thm := some ``sortPushAssert_proven
    notes := "Run lengths come from the model's count_run/binarysort for an arbitrary lt; only 1 <= n <= nremaining is used." },
  { id := "listsort-minrun", pyFile := "Objects/listobject.c", pyFns := ["minrun_next", "merge_init"]
    statement := "With e the smallest exponent such that N >> e < 64 and P = 2^e, call k (from 0) of minrun_next returns floor((k+1)N/P) - floor(kN/P) and leaves mr_current = kN mod P. So for N < 64 every value is N; for N >= 64, 32 * P <= N < 64 * P and every value lies in [32, MAX_MINRUN]; any m consecutive values add up to floor(mN/P) or one more; the first P values add up to exactly N; every value is 32 for a power of two >= 64; and mr_current + listlen stays in Py_ssize_t for N <= 2**62."
    source := "listobject.c:2282-2288, :2767-2775 and listsort.txt:307-392", status := .proven
    prop := ``MinrunSpec, thm := some ``minrunSpec_proven
    notes := "Replaces the 3.14 merge_compute_minrun. Also discharges binarysort's assert n <= MAX_MINRUN at :1843 (force <= minrun). Only the mr_* fields of merge_init are covered here. N <= 2**62 is the bound listsort-powerloop-no-overflow uses: real lists have at most 2**60 - 1 items. The run lengths are difftested against the interpreter (fn \"runs\"); that a real sort draws these values in this order is the model's sortStep, not a separate theorem." },
  { id := "listsort-gallop", pyFile := "Objects/listobject.c", pyFns := ["gallop_left", "gallop_right"]
    statement := "On every sorted vector a[0:n] and every 0 <= hint < n, gallop_left returns the number of items < key (a[k-1] < key <= a[k]) and gallop_right the number of items <= key (a[k-1] <= key < a[k])."
    source := "docstrings at listobject.c:2066-2086 and :2162-2170", status := .proven
    prop := ``GallopSpec, thm := some ``gallopSpec_proven },
  { id := "listsort-binarysort", pyFile := "Objects/listobject.c", pyFns := ["binarysort"]
    statement := "binarysort(a, n, ok) with a[:max(ok,1)] sorted and max(ok,1) <= n leaves the stable sort of a[:n] followed by a[n:]."
    source := "comment at listobject.c:1822-1831 (\"a stable binary insertion sort\")", status := .proven
    prop := ``BinarysortStable, thm := some ``binarysortStable_proven },
  { id := "listsort-count-run", pyFile := "Objects/listobject.c", pyFns := ["count_run"]
    statement := "count_run on a non-empty slice returns 1 <= n <= len and replaces the first n items by their stable sort (ascending runs, descending runs whose all-equal groups keep their order, plus the ascending extension), leaving the rest untouched."
    source := "comments at listobject.c:1963-1970, :2005-2017, :2026-2029", status := .proven
    prop := ``CountRunSpec, thm := some ``countRunSpec_proven },
  { id := "listsort-merge-at", pyFile := "Objects/listobject.c", pyFns := ["merge_at", "merge_lo", "merge_hi"]
    statement := "merge_at on two sorted non-empty adjacent runs produces the stable sort of their concatenation, through merge_lo or merge_hi, galloping or not, for every min_gallop."
    source := "comments at listobject.c:2341-2346, :2473-2478, :2615-2617", status := .proven
    prop := ``MergeAtStable, thm := some ``mergeAtStable_proven
    notes := "merge_lo/merge_hi are proven under the preconditions merge_at establishes (B[0] < A[0], A[-1] > all of B)." },
  { id := "listsort-perm-any-compare", pyFile := "Objects/listobject.c", pyFns := ["list_sort_impl"]
    statement := "For every item type and every comparison function, however inconsistent, the result of list.sort (with or without reverse) is a permutation of the input."
    source := "listobject.c:2940-2944 (\"nothing is lost or duplicated\")", status := .proven
    prop := ``PermAnyCompare, thm := some ``permAnyCompare_proven
    notes := "Inconsistent comparisons are modelled; comparisons that raise are not." },
  { id := "listsort-stable-sort", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "For every item type and integer-valued key compared with <, list.sort() returns the stable sort: sorted by key, a permutation, and for every key value the items with that key in their original order."
    source := "list.sort docstring, listobject.c:2953-2961; Doc/library/stdtypes.rst (list.sort)", status := .proven
    prop := ``SortIsStableSort, thm := some ``sortIsStableSort_proven },
  { id := "listsort-int-sorted-stable", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "For every list of ints, sorted() is non-decreasing and a permutation; sorting (value, index) pairs by value leaves equal values with increasing indices."
    source := "list.sort docstring, listobject.c:2953-2956", status := .proven
    prop := ``IntSortStable, thm := some ``intSortStable_proven },
  { id := "listsort-reverse-stable", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "list.sort(reverse=True) equals reversing, stably sorting and reversing back, which is the stable sort by descending key (equal keys keep their original order)."
    source := "listobject.c:3132-3138, :3201-3202; Doc/howto/sorting.rst (\"The reverse parameter still maintains sort stability\")", status := .proven
    prop := ``ReverseStable, thm := some ``reverseStable_proven },
  { id := "listsort-key", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "list.sort(key=f, reverse=r) with integer keys computed once per item sorts the items stably by f (by descending f when r), the items moving in lockstep with their keys."
    source := "list.sort docstring, listobject.c:2958-2959; :2948-2959", status := .proven
    prop := ``KeySortStable, thm := some ``keySortStable_proven },
  { id := "listsort-long-compare", pyFile := "Objects/listobject.c", pyFns := ["unsafe_long_compare", "unsafe_object_compare", "long_compare", "long_richcompare"]
    statement := "For all-int keys of every size, the compare chosen by the pre-sort check (unsafe_long_compare when all keys are compact, long_richcompare otherwise) agrees with < on every pair of keys; an int is compact exactly when |x| < 2**30 and _PyLong_CompactValue(x) is then x; long_compare's sign, digit-count and digit-loop logic is correct for all ints."
    source := "assert at listobject.c:2879 (res == PyObject_RichCompareBool(v, w, Py_LT)); the pre-sort check at :2964-3059", status := .proven
    prop := ``LongCompareAgrees, thm := some ``longCompareAgrees_proven
    notes := "Ints are modelled as a sign and little-endian 30-bit digits (Include/cpython/longintrepr.h); the 15-bit-digit build is not covered. The whole sort with this compare is difftested (fn \"plain\"), not proven equal to the sort with Int <." },
  { id := "listsort-object-compare", pyFile := "Objects/listobject.c", pyFns := ["unsafe_object_compare"]
    statement := "For every result type, unsafe_object_compare answers as PyObject_RichCompareBool when v's type no longer has key_richcompare or the slot returns NotImplemented, raises what the slot raises, takes a bool as it is, and decides any other object with PyObject_IsTrue, whose exception propagates."
    source := "listobject.c:2799-2832", status := .proven
    prop := ``ObjectCompareSpec, thm := some ``objectCompareSpec_proven
    notes := "The rich comparison, PyObject_IsTrue and the fallback are parameters with no assumptions. Difftested on two-item lists (fn \"objcmp\"). The sameSlot = false branch is not difftested: slot_tp_richcompare on a type without __lt__ returns NotImplemented, so the branch gives the same answer as the slot would and cannot be told apart from Python. The whole sort does not model a raising comparison, so what the list holds after one is not covered here." }
]

end PyLean.ListSort
