import PyLean.Registry
import PyLean.ListSort.Props
import PyLean.ListSort.Diff

/-!
`list.sort` (powersort/timsort in `Objects/listobject.c`, `Objects/listsort.txt`), CPython 3.14.7.

The model (`ListSort/Model.lean`) mirrors `count_run`, `binarysort`,
`gallop_left`/`gallop_right`, `merge_lo`/`merge_hi`/`merge_at`, `powerloop`,
`found_new_run`, `merge_force_collapse`, `merge_compute_minrun` and the main
loop of `list_sort_impl`, counting every `<` call; the difftest checks results
and exact `<`-call counts against CPython. Items are compared by an
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
    source := "listsort.txt:375-397 (the definition of a run's power)", status := .proven
    prop := ``PowerloopFirstBit, thm := some ``powerloopFirstBit_proven },
  { id := "listsort-powerloop-no-overflow", pyFile := "Objects/listobject.c", pyFns := ["powerloop"]
    statement := "For every list length n <= 2**62 and all valid runs, no intermediate value of powerloop (2*s1 + n1, a + n1 + n2, and every shifted a, b) reaches 2**63, so the Py_ssize_t arithmetic never overflows."
    source := "invariant: no signed overflow; listsort.txt:412-417 argues it from n <= PY_SSIZE_T_MAX/sizeof(PyObject*)", status := .proven
    prop := ``PowerloopNoOverflow, thm := some ``powerloopNoOverflow_proven
    notes := "Precondition n <= 2**62: real lists have at most PY_SSIZE_T_MAX/8 = 2**60-1 items (list_resize). For 2**62 < n < 2**63 the model's overflow flag can be set (b reaches 2n-1); unreachable from Python." },
  { id := "listsort-powers-strict", pyFile := "Objects/listobject.c", pyFns := ["found_new_run", "powerloop"]
    statement := "For every list length N <= PY_SSIZE_T_MAX and every sequence of positive run lengths summing to at most N, after each found_new_run + push the powers stored on the pending stack are >= 1 and strictly increase towards the top."
    source := "listsort.txt:426-427; assert at listobject.c:2663", status := .proven
    prop := ``PolicyPowersStrict, thm := some ``policyPowersStrict_proven
    notes := "Quantifies over arbitrary run structures, not only those count_run/minrun produce. The proof keeps, per stack entry, a ghost list of the original runs merged into it." },
  { id := "listsort-stack-bound", pyFile := "Objects/listobject.c", pyFns := ["found_new_run", "list_sort_impl"]
    statement := "For every N <= PY_SSIZE_T_MAX and every non-empty sequence of positive run lengths summing to at most N, after each push the pending stack holds s entries with 2^s < 4N (s <= ceil(log2 N) + 1), and assert(ms.n < MAX_MERGE_PENDING) holds before every push."
    source := "invariant: ms->pending has MAX_MERGE_PENDING = 64 slots (listobject.c:1678, :1733); assert at :3100", status := .proven
    prop := ``PolicyStackBound, thm := some ``policyStackBound_proven },
  { id := "listsort-stack-bound-tight", pyFile := "Objects/listobject.c", pyFns := ["found_new_run"]
    statement := "The bound is attained: for N = 3 * 2**61 <= PY_SSIZE_T_MAX the runs [2**61, 2**61, 2**60, ..., 2, 1, 1] fill all 64 pending slots (and the assert still holds)."
    source := "listobject.c:1673-1677 (\"plenty large enough for all cases\")", status := .proven
    prop := ``PolicyStackTight, thm := some ``policyStackTight_proven
    notes := "MAX_MERGE_PENDING is exactly large enough for arbitrary run structures on 64-bit builds. With real runs (>= minrun >= 32 except the last) the stack stays far smaller, and real lists have < 2**60 items." },
  { id := "listsort-stack-comment-log2", pyFile := "Objects/listobject.c", pyFns := ["found_new_run"]
    statement := "For every list length n and every run structure (runs not forced to minrun), the pending stack needs at most floor(log2(n)) + 1 entries."
    source := "comment at listobject.c:1673-1677", status := .refuted
    prop := ``StackCommentLog2, thm := some ``stackCommentLog2_refuted
    bug := some "listsort-stack-comment-log2"
    notes := "n = 3, runs [1, 1, 1] reach 3 > floor(log2 3) + 1 = 2 entries; the true bound is ceil(log2 n) + 1 (listsort-stack-bound), attained (listsort-stack-bound-tight). Comment only: the code is safe." },
  { id := "listsort-sort-push-assert", pyFile := "Objects/listobject.c", pyFns := ["list_sort_impl", "count_run", "binarysort", "found_new_run"]
    statement := "For every item type, every comparison function (including inconsistent ones) and every list of length <= PY_SSIZE_T_MAX, the sort never violates assert(ms.n < MAX_MERGE_PENDING) before pushing a run."
    source := "invariant: the assert at listobject.c:3100 is compiled out of release builds, where a violation would write past ms.pending[]", status := .proven
    prop := ``SortPushAssert, thm := some ``sortPushAssert_proven
    notes := "Run lengths come from the model's count_run/binarysort for an arbitrary lt; only 1 <= n <= nremaining is used." },
  { id := "listsort-minrun", pyFile := "Objects/listobject.c", pyFns := ["merge_compute_minrun"]
    statement := "merge_compute_minrun(n) is n for n < 64; for n >= 64 it is ceil(n / 2^e) where 32 * 2^e <= n < 64 * 2^e, so 32 <= minrun <= MAX_MINRUN and n/minrun <= 2^e (equality iff 2^e divides n); it is 32 for every power of two >= 64."
    source := "listobject.c:2690-2699 and listsort.txt:313-318", status := .proven
    prop := ``MinrunSpec, thm := some ``minrunSpec_proven
    notes := "Also discharges binarysort's assert n <= MAX_MINRUN (force <= minrun). The code comment's \"strictly less than\" a power of 2 is loose for n = 96 etc. (n/minrun = 2 exactly); listsort.txt states it correctly." },
  { id := "listsort-gallop", pyFile := "Objects/listobject.c", pyFns := ["gallop_left", "gallop_right"]
    statement := "On every sorted vector a[0:n] and every 0 <= hint < n, gallop_left returns the number of items < key (a[k-1] < key <= a[k]) and gallop_right the number of items <= key (a[k-1] <= key < a[k])."
    source := "docstrings at listobject.c:1998-2018 and :2094-2102", status := .proven
    prop := ``GallopSpec, thm := some ``gallopSpec_proven },
  { id := "listsort-binarysort", pyFile := "Objects/listobject.c", pyFns := ["binarysort"]
    statement := "binarysort(a, n, ok) with a[:max(ok,1)] sorted and max(ok,1) <= n leaves the stable sort of a[:n] followed by a[n:]."
    source := "comment at listobject.c:1754-1763 (\"a stable binary insertion sort\")", status := .proven
    prop := ``BinarysortStable, thm := some ``binarysortStable_proven },
  { id := "listsort-count-run", pyFile := "Objects/listobject.c", pyFns := ["count_run"]
    statement := "count_run on a non-empty slice returns 1 <= n <= len and replaces the first n items by their stable sort (ascending runs, descending runs whose all-equal groups keep their order, plus the ascending extension), leaving the rest untouched."
    source := "comments at listobject.c:1895-1902, :1937-1949, :1958-1961", status := .proven
    prop := ``CountRunSpec, thm := some ``countRunSpec_proven },
  { id := "listsort-merge-at", pyFile := "Objects/listobject.c", pyFns := ["merge_at", "merge_lo", "merge_hi"]
    statement := "merge_at on two sorted non-empty adjacent runs produces the stable sort of their concatenation, through merge_lo or merge_hi, galloping or not, for every min_gallop."
    source := "comments at listobject.c:2265-2270, :2397-2402, :2539-2541", status := .proven
    prop := ``MergeAtStable, thm := some ``mergeAtStable_proven
    notes := "merge_lo/merge_hi are proven under the preconditions merge_at establishes (B[0] < A[0], A[-1] > all of B)." },
  { id := "listsort-perm-any-compare", pyFile := "Objects/listobject.c", pyFns := ["list_sort_impl"]
    statement := "For every item type and every comparison function, however inconsistent, the result of list.sort (with or without reverse) is a permutation of the input."
    source := "listobject.c:2875-2879 (\"nothing is lost or duplicated\")", status := .proven
    prop := ``PermAnyCompare, thm := some ``permAnyCompare_proven
    notes := "Inconsistent comparisons are modelled; comparisons that raise are not." },
  { id := "listsort-stable-sort", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "For every item type and integer-valued key compared with <, list.sort() returns the stable sort: sorted by key, a permutation, and for every key value the items with that key in their original order."
    source := "list.sort docstring, listobject.c:2888-2896; Doc/library/stdtypes.rst (list.sort)", status := .proven
    prop := ``SortIsStableSort, thm := some ``sortIsStableSort_proven },
  { id := "listsort-int-sorted-stable", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "For every list of ints, sorted() is non-decreasing and a permutation; sorting (value, index) pairs by value leaves equal values with increasing indices."
    source := "list.sort docstring, listobject.c:2888-2891", status := .proven
    prop := ``IntSortStable, thm := some ``intSortStable_proven },
  { id := "listsort-reverse-stable", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "list.sort(reverse=True) equals reversing, stably sorting and reversing back, which is the stable sort by descending key (equal keys keep their original order)."
    source := "listobject.c:3067-3073, :3136-3137; Doc/howto/sorting.rst (\"The reverse parameter still maintains sort stability\")", status := .proven
    prop := ``ReverseStable, thm := some ``reverseStable_proven },
  { id := "listsort-key", pyFile := "Objects/listobject.c", pyFns := ["list.sort"]
    statement := "list.sort(key=f, reverse=r) with integer keys computed once per item sorts the items stably by f (by descending f when r), the items moving in lockstep with their keys."
    source := "list.sort docstring, listobject.c:2893-2894; :2948-2959", status := .proven
    prop := ``KeySortStable, thm := some ``keySortStable_proven },
  { id := "listsort-long-compare", pyFile := "Objects/listobject.c", pyFns := ["unsafe_long_compare", "unsafe_object_compare", "long_compare", "long_richcompare"]
    statement := "For all-int keys of every size, the compare chosen by the pre-sort check (unsafe_long_compare when all keys are compact, long_richcompare otherwise) agrees with < on every pair of keys; an int is compact exactly when |x| < 2**30 and _PyLong_CompactValue(x) is then x; long_compare's sign, digit-count and digit-loop logic is correct for all ints."
    source := "assert at listobject.c:2814 (res == PyObject_RichCompareBool(v, w, Py_LT)); the pre-sort check at :2964-3059", status := .proven
    prop := ``LongCompareAgrees, thm := some ``longCompareAgrees_proven
    notes := "Ints are modelled as a sign and little-endian 30-bit digits (Include/cpython/longintrepr.h); the 15-bit-digit build is not covered. The whole sort with this compare is difftested (fn \"plain\"), not proven equal to the sort with Int <." }
]

end PyLean.ListSort
