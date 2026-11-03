import PyLean.Registry
import PyLean.BytesObj.Seq.HashProps
import PyLean.BytesObj.Seq.SearchProps
import PyLean.BytesObj.Seq.CompareProps
import PyLean.BytesObj.Seq.IterProps
import PyLean.BytesObj.Seq.ReprProps
import PyLean.BytesObj.Seq.SliceProps
import PyLean.BytesObj.Seq.AllocProps
import PyLean.BytesObj.Seq.MiscProps
import PyLean.BytesObj.Seq.CApiProps
import PyLean.BytesObj.Seq.CApiContent
import PyLean.BytesObj.Seq.ContentProps
import PyLean.BytesObj.Seq.BugProps
import PyLean.BytesObj.Seq.Release
import PyLean.BytesObj.Seq.ListRows
import PyLean.BytesObj.Seq.ListRows2
import PyLean.BytesObj.Seq.ListRows3
import PyLean.BytesObj.Seq.ListRows4
import PyLean.BytesObj.Seq.ListRows5

/-! Registry entries for tuple (Objects/tupleobject.c) and list (Objects/listobject.c). -/

namespace PyLean.BytesObj.Seq

open PyLean.Registry

def entries : List Entry := [
  { id := "bytesobj-tuple-hash-empty", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_hash", "tuple_get_empty"]
    statement := "hash(()) is 5740354900026072187, the value of _PyTuple_HASH_EMPTY, for every element type."
    source := "Include/internal/pycore_tuple.h:76; tupleobject.c:404 (the length mangling keeps the historical value)", status := .proven
    prop := ``TupleHashEmpty, thm := some ``tupleHashEmpty_proven },
  { id := "bytesobj-tuple-hash-not-minus-one", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_hash"]
    statement := "For every element type and every tuple with no cached hash, a successful hash(t) is not -1, is stored in ob_hash, and leaves the items alone."
    source := "invariant: -1 is the C error marker of tp_hash and the cache's 'not computed' marker", status := .proven
    prop := ``TupleHashNotMinusOne, thm := some ``tupleHashNotMinusOne_proven },
  { id := "bytesobj-tuple-hash-cached", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_hash"]
    statement := "After a successful hash(t), later hash(t) calls return the same value without consulting any element, even if an element's __hash__ has changed or would raise."
    source := "Include/cpython/tupleobject.h:7 ('Cached hash'); invariant", status := .proven
    prop := ``TupleHashCached, thm := some ``tupleHashCached_proven },
  { id := "bytesobj-tuple-hash-one-lane", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_hash"]
    statement := "Each round of tuple_hash is a bijection: tuples of equal length differing in exactly one element's hash never collide in the loop, and the final hash can only collide through the single remap of -1 to 1546275796."
    source := "tupleobject.c:356-369 (xxHash construction); invariant of the construction", status := .proven
    prop := ``TupleHashOneLane, thm := some ``tupleHashOneLane_proven },
  { id := "bytesobj-contains-agree", pyFile := "Objects/listobject.c", pyFns := ["list_contains", "list_get_item_ref", "valid_index", "_PyList_GetItemRef", "tuple_contains"]
    statement := "x in l and x in tuple(l) agree for every element type and every comparison, including raising ones, when the comparison leaves the list alone."
    source := "Doc/reference/expressions.rst:2260; list and tuple implement one operation", status := .proven
    prop := ``ContainsAgree, thm := some ``containsAgree_proven
    notes := "The operands are item == x, deliberately since gh-81829. expressions.rst still writes x == e; that doc wording is not treated as a bug here." },
  { id := "bytesobj-contains-identity", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_contains"]
    statement := "An object is in a tuple that holds that very object at any position, unless an earlier comparison raises: the identity shortcut of PyObject_RichCompareBool decides, so a NaN-like element is found."
    source := "Doc/reference/expressions.rst:2260 ('x is e or x == e')", status := .proven
    prop := ``ContainsIdentity, thm := some ``containsIdentity_proven },
  { id := "bytesobj-list-search-reentrant", pyFile := "Objects/listobject.c"
    pyFns := ["list_contains", "list_index_impl", "list_count_impl", "list_remove_impl", "list_richcompare_impl"]
    statement := "x in l, l.index, l.count, l.remove and the search of l == r read no slot outside the list, whatever a comparison does to it, however often."
    source := "listobject.c:676-693, :3360-3372, :3386-3445, :3479-3495", status := .proven
    prop := ``ListSearchSafe, thm := some ``listSearchSafe_proven },
  { id := "bytesobj-index-agree", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_index_impl", "list_index_impl"]
    statement := "list.index and tuple.index run the same search for every element type, every comparison (including raising ones) and every int start and stop: their different clipping of stop never shows."
    source := "common sequence s.index(x[, i[, j]]), Doc/library/stdtypes.rst", status := .proven
    prop := ``IndexAgree, thm := some ``indexAgree_proven },
  { id := "bytesobj-count-agree", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_count_impl", "list_count_impl"]
    statement := "list.count and tuple.count agree for every element type and comparison, including raising ones; the explicit identity test of list_count_impl changes nothing."
    source := "common sequence s.count(x), Doc/library/stdtypes.rst", status := .proven
    prop := ``CountAgree, thm := some ``countAgree_proven },
  { id := "bytesobj-compare-agree", pyFile := "Objects/listobject.c", pyFns := ["list_richcompare_impl", "list_richcompare", "tuple_richcompare"]
    statement := "A list comparison is the tuple comparison, for every element type, comparison (including raising ones) and operator, except for the early out on == and != when lengths differ, which is the difference the note at tupleobject.c:753-758 states."
    source := "tupleobject.c:753-758; Doc/reference/expressions.rst (sequence comparison)", status := .proven
    prop := ``CompareAgree, thm := some ``compareAgree_proven },
  { id := "bytesobj-compare-reflexive", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_richcompare"]
    statement := "A tuple equals itself when every item is identical to itself, whatever its __eq__ says: identity implies equality in collections."
    source := "Doc/reference/expressions.rst (value comparisons, collections)", status := .proven
    prop := ``CompareReflexive, thm := some ``compareReflexive_proven },
  { id := "bytesobj-tuple-iter-yields", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_iter", "tupleiter_next"]
    statement := "iter(t) yields each item once in order and then stops for good, for every tuple."
    source := "iterator protocol, Doc/library/stdtypes.rst", status := .proven
    prop := ``TupleIterYields, thm := some ``tupleIterYields_proven },
  { id := "bytesobj-tuple-iter-reduce", pyFile := "Objects/tupleobject.c", pyFns := ["tupleiter_len", "tupleiter_reduce", "tupleiter_setstate"]
    statement := "For every iterator state, __length_hint__ counts what is left and rebuilding from __reduce__ gives an iterator with the same items left."
    source := "invariant: __reduce__/__setstate__ round trip", status := .proven
    prop := ``TupleIterReduce, thm := some ``tupleIterReduce_proven },
  { id := "bytesobj-list-iter-safe", pyFile := "Objects/listobject.c", pyFns := ["list_iter", "listiter_next", "listiter_setstate", "list___reversed___impl", "listreviter_next", "listreviter_setstate"]
    statement := "The list iterators never dereference a cleared it_seq, whatever the list has become, and once next has stopped it stays stopped under any change to the list."
    source := "Doc/library/stdtypes.rst (iterator protocol: once exhausted, stays exhausted); invariant", status := .proven
    prop := ``ListIterSafe, thm := some ``listIterSafe_proven },
  { id := "bytesobj-list-iter-yields", pyFile := "Objects/listobject.c", pyFns := ["list_iter", "listiter_next", "list___reversed___impl", "listreviter_next"]
    statement := "On an unchanging list, iter(l) yields the items in order and reversed(l) in reverse, each then stopping."
    source := "Doc/library/functions.rst (iter, reversed)", status := .proven
    prop := ``ListIterYields, thm := some ``listIterYields_proven },
  { id := "bytesobj-list-iter-hint", pyFile := "Objects/listobject.c", pyFns := ["listiter_len", "listreviter_len", "listiter_reduce", "listreviter_reduce", "listiter_reduce_general", "listiter_setstate", "listreviter_setstate"]
    statement := "The list iterators' __length_hint__ is never negative and counts what is left, and __reduce__ with __setstate__ restores the index."
    source := "invariant: length hints and the pickling round trip", status := .proven
    prop := ``ListIterHint, thm := some ``listIterHint_proven },
  { id := "bytesobj-repr-shape", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_repr", "list_repr", "list_repr_impl"]
    statement := "repr gives (a, b), (a,), (), [a, b] and [] for every element type whose reprs succeed and leave the container alone."
    source := "Doc/library/stdtypes.rst (tuple and list displays)", status := .proven
    prop := ``ReprShape, thm := some ``reprShape_proven },
  { id := "bytesobj-repr-terminates", pyFile := "Objects/listobject.c", pyFns := ["list_repr", "list_repr_impl", "tuple_repr"]
    statement := "repr terminates on every heap of lists and tuples, cycles included, with depth at most the number of containers plus one."
    source := "invariant: Py_ReprEnter cuts cycles", status := .proven
    prop := ``ReprTerminates, thm := some ``reprTerminates_proven
    notes := "The model has no Py_EnterRecursiveCall, so it says nothing about RecursionError on deep finite nesting." },
  { id := "bytesobj-slice-reads", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_subscript", "list_slice_lock_held", "list_slice_subscript", "_PyList_SliceSubscript"]
    statement := "For every tuple and list and every slice with a non-zero step, of any sign and size, t[s] and l[s] succeed and read exactly the positions of range(*s.indices(n)), all inside the object."
    source := "Doc/library/stdtypes.rst common sequence operations, note (5)", status := .proven
    prop := ``SliceReads, thm := some ``sliceReads_proven
    notes := "Bounds are derived from RangeSlice.IndicesInBounds, not assumed." },
  { id := "bytesobj-list-resize", pyFile := "Objects/listobject.c", pyFns := ["list_resize", "py_list_resize"]
    statement := "list_resize's fast path changes nothing; the over-allocation is a multiple of 4, at most 9/8 of the size plus 6, and below 2^64 for every size up to PY_SSIZE_T_MAX, as the note at listobject.c:145-146 says."
    source := "listobject.c:115-153", status := .proven
    prop := ``ListResizeSpec, thm := some ``listResizeSpec_proven },
  { id := "bytesobj-list-growth-pattern", pyFile := "Objects/listobject.c", pyFns := ["list_resize", "_PyList_AppendTakeRefListResize", "list_append_impl"]
    statement := "The capacities through the first 65 appends are 0, 4, 8, 16, 24, 32, 40, 52, 64, 76, the sequence in the comment at listobject.c:144."
    source := "listobject.c:144", status := .proven
    prop := ``ListGrowthPattern, thm := some ``listGrowthPattern_proven },
  { id := "bytesobj-list-ops-wf", pyFile := "Objects/listobject.c", pyFns := ["list_resize", "list_preallocate_exact", "list_new_prealloc", "list_clear_impl", "list_clear", "list_clear_slot", "py_list_clear_impl", "list_append_impl", "list_extend_fast", "list_extend_lock_held", "list_extend_set", "list_extend_dict", "list_inplace_repeat", "list_ass_item", "list_ass_slice", "reverse_slice", "list_reverse_impl", "PyList_Clear"]
    statement := "Every mutating list method keeps the invariant: allocated covers the items, an array exists when anything is allocated, and its byte size fits Py_ssize_t."
    source := "invariant of PyListObject, Include/cpython/listobject.h", status := .proven
    prop := ``ListOpsWF, thm := some ``listOpsWF_proven },
  { id := "bytesobj-tuple-concat", pyFile := "Objects/tupleobject.c", pyFns := ["_PyTuple_Concat", "tuple_alloc", "tuple_get_empty"]
    statement := "a + b on tuples is a's items then b's for every pair that fits, returns an argument in the two sharing cases, and raises TypeError with the source's message for a non-tuple."
    source := "common sequence s + t, Doc/library/stdtypes.rst", status := .proven
    prop := ``TupleConcatSpec, thm := some ``tupleConcatSpec_proven },
  { id := "bytesobj-repeat", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_repeat", "list_repeat", "tuple_alloc"]
    statement := "t * n and l * n: the sharing cases, the empty cases, n copies of the items, and MemoryError exactly when the result cannot be allocated, for every Py_ssize_t count."
    source := "common sequence s * n, Doc/library/stdtypes.rst", status := .proven
    prop := ``RepeatSpec, thm := some ``repeatSpec_proven },
  { id := "bytesobj-tuple-construct", pyFile := "Objects/tupleobject.c", pyFns := ["maybe_tracked", "PyTuple_FromArray", "_PyTuple_FromStackRefStealOnSuccess", "_PyTuple_FromArraySteal", "PyTuple_Pack", "_PyTuple_MaybeUntrack", "tuple_new_impl", "tuple_vectorcall", "tuple_subtype_new", "tuple___getnewargs___impl", "tuple_slice"]
    statement := "The tuple construction paths and their GC tracking decisions, as gc.is_tracked shows them; tuple(t) is t for an exact tuple; a subclass instance starts with no cached hash; keyword arguments are rejected first."
    source := "tupleobject.c:445-516; Doc/library/gc.rst (is_tracked)", status := .proven
    prop := ``TupleConstruct, thm := some ``tupleConstruct_proven },
  { id := "bytesobj-capi-agree", pyFile := "Objects/listobject.c", pyFns := ["PyList_Size", "PyList_GetItem", "PyList_GetItemRef", "PyList_SetItem", "PyList_Insert", "PyList_Append", "PyList_SetSlice", "PyList_Reverse", "PyList_AsTuple", "PyList_Extend", "PyList_Clear", "list_copy_impl", "PyTuple_Size", "PyTuple_GetItem", "_PyTuple_Resize", "list_ass_slice", "valid_index"]
    statement := "Each C API entry point refuses an object of another type with its own error; PyList_GetItem and friends take no negative index, unlike l[i], and the others act on the contents as described, for every argument; _PyTuple_Resize keeps the prefix and pads with NULL."
    source := "Doc/c-api/list.rst, Doc/c-api/tuple.rst", status := .proven
    prop := ``CApiAgree, thm := some ``cApiAgree_proven },
  { id := "bytesobj-item-access", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_item", "tuple_length", "list_item", "list_length", "tuple_subscript"]
    statement := "t[i] and l[i] for every int i of any size: a negative index counts from the end, both return the item there, and outside [-len, len) both raise IndexError; inside, the position is in the object."
    source := "Doc/library/stdtypes.rst common sequence operations, notes (3), (4)", status := .proven
    prop := ``ItemAccess, thm := some ``itemAccess_proven },
  { id := "bytesobj-capi-construct", pyFile := "Objects/listobject.c", pyFns := ["PyList_New", "PyTuple_New", "_PyList_FromStackRefStealOnSuccess", "_PyList_AsTupleAndClear", "PyTuple_SetItem", "PyList_GetSlice", "PyTuple_GetSlice", "list_vectorcall"]
    statement := "The C API constructors and slice getters for every argument: PyList_New and PyTuple_New for every size, the stack-reference and tuple-and-clear paths, PyTuple_SetItem on a uniquely referenced tuple, PyList_GetSlice, PyTuple_GetSlice, and list_vectorcall's argument checks."
    source := "Doc/c-api/list.rst, Doc/c-api/tuple.rst", status := .proven
    prop := ``CApiConstruct, thm := some ``cApiConstruct_proven },
  { id := "bytesobj-list-contents", pyFile := "Objects/listobject.c", pyFns := ["list_append_impl", "PyList_Insert", "list_clear_impl", "reverse_slice", "list_reverse_impl", "PyList_Reverse", "list_extend_fast", "list_extend_set", "list_extend_dict", "_list_extend", "list_extend_impl", "_PyList_Extend", "list_inplace_concat", "list_concat_lock_held", "_PyList_Concat", "list_copy_impl", "list___init___impl", "list_inplace_repeat", "list_inplace_repeat_lock_held"]
    statement := "What the list methods do to the contents, for every element type and argument, including that __init__ drops the old contents before it looks at the iterable."
    source := "Doc/library/stdtypes.rst, mutable sequence types", status := .proven
    prop := ``ListContents, thm := some ``listContents_proven },
  { id := "bytesobj-list-extend-iter", pyFile := "Objects/listobject.c", pyFns := ["list_extend_iter_lock_held", "_list_extend"]
    statement := "list.extend from a generic iterable gives the old items then what the iterator yields, for every list and every hint with len + hint + items at most sys.maxsize / 16."
    source := "Doc/library/stdtypes.rst (s.extend(t)); narrowed version of bytesobj-list-hint-inert", status := .proven
    prop := ``ListExtendIterContents, thm := some ``listExtendIterContents_proven },
  { id := "bytesobj-sortslice-parallel", pyFile := "Objects/listobject.c", pyFns := ["sortslice_copy", "sortslice_copy_incr", "sortslice_copy_decr", "sortslice_memcpy", "sortslice_memmove", "sortslice_advance", "sortslice_reverse"]
    statement := "Every sortslice move keeps keys[i] the key of values[i], which is what makes list.sort(key=...) return the values in key order."
    source := "listobject.c:1660-1667", status := .proven
    prop := ``SortsliceParallel, thm := some ``sortsliceParallel_proven },
  { id := "bytesobj-merge-mem", pyFile := "Objects/listobject.c", pyFns := ["merge_init", "merge_getmem"]
    statement := "merge_init sizes the stack area as documented, and merge_getmem provides at least need slots, its overflow check not firing below the limit."
    source := "listobject.c:2258-2269, :2323", status := .proven
    prop := ``MergeMemSpec, thm := some ``mergeMemSpec_proven },
  { id := "bytesobj-sort-compare-agree", pyFile := "Objects/listobject.c", pyFns := ["safe_object_compare", "unsafe_latin_compare", "unsafe_tuple_compare", "PyList_Sort"]
    statement := "The compares list.sort selects agree with the generic path: unsafe_latin_compare is str.__lt__ on all byte strings, unsafe_tuple_compare is tuple.__lt__ for every comparison including raising ones, and PyList_Sort rejects a non-list and is otherwise list.sort."
    source := "listobject.c:2777-2938 (the asserts at :2789, :2814, :2829)", status := .proven
    prop := ``SortCompareAgree, thm := some ``sortCompareAgree_proven },
  { id := "bytesobj-release-order", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_dealloc", "list_dealloc"]
    statement := "Containers release and visit their items last to first, for every element type, as finalizers and gc.get_referents show; a live iterator refers to exactly its sequence."
    source := "listobject.c:582-585 ('Do it backwards'); Doc/library/gc.rst (get_referents)", status := .proven
    prop := ``ReleaseOrder, thm := some ``releaseOrder_proven },
  { id := "bytesobj-list-iter-releases", pyFile := "Objects/listobject.c", pyFns := ["listiter_next"]
    statement := "iter(l) lets go of the list once exhausted, for every list and any number of next calls."
    source := "Include/internal/pycore_list.h ('Set to NULL when iterator is exhausted')", status := .proven
    prop := ``ListIterReleases, thm := some ``listIterReleases_proven },
  { id := "bytesobj-list-reviter-releases", pyFile := "Objects/listobject.c", pyFns := ["listreviter_next"]
    statement := "reversed(l) lets go of the list once exhausted, as iter(l) does. False: the early index < 0 return skips the code that clears it_seq, so the list is kept alive."
    source := "listobject.c:4154 ('Set to NULL when iterator is exhausted')", status := .refuted
    prop := ``ListRevIterReleases, thm := some ``listRevIterReleases_refuted, bug := some "bytesobj-list-reversed-keeps-list" },
  { id := "bytesobj-list-reviter-stops", pyFile := "Objects/listobject.c", pyFns := ["listreviter_next"]
    statement := "A reversed iterator whose index is past the end of a shrunken list stops and clears it_seq: the one path that does release the list."
    source := "listobject.c:4259-4263", status := .proven
    prop := ``ListRevIterStops, thm := some ``listRevIterStops_proven },
  { id := "bytesobj-list-sizeof-exact", pyFile := "Objects/listobject.c", pyFns := ["list___sizeof___impl"]
    statement := "Outside list.sort, list.__sizeof__() is exactly 40 + 8 * allocated, with no wraparound."
    source := "Doc/library/sys.rst (getsizeof); narrowed version of bytesobj-list-sizeof-during-sort", status := .proven
    prop := ``ListSizeofExact, thm := some ``listSizeofExact_proven },
  { id := "bytesobj-list-sizeof-during-sort", pyFile := "Objects/listobject.c", pyFns := ["list___sizeof___impl"]
    statement := "list.__sizeof__() never reports less than an empty list's 40 bytes, in any state, including while list.sort runs. False: it reports 32."
    source := "invariant: a size is not below the object's own header", status := .refuted
    prop := ``ListSizeofBase, thm := some ``listSizeofBase_refuted, bug := some "bytesobj-list-sizeof-during-sort" },
  { id := "bytesobj-list-hint-inert", pyFile := "Objects/listobject.c", pyFns := ["list_extend_iter_lock_held", "list_preallocate_exact"]
    statement := "Any legal __length_hint__ leaves list.extend succeeding on an empty iterable. False: an over-estimate raises MemoryError, though the same hint is ignored for a non-empty list."
    source := "Doc/reference/datamodel.rst (__length_hint__: an estimate that 'may be greater or less than the actual length')", status := .refuted
    prop := ``ListHintInert, thm := some ``listHintInert_refuted, bug := some "bytesobj-list-length-hint-overestimate" },
  { id := "bytesobj-list-hint-ignored", pyFile := "Objects/listobject.c", pyFns := ["list_extend_iter_lock_held"]
    statement := "The same maximal hint is ignored for a one-item list, because m > PY_SSIZE_T_MAX - n skips the allocation."
    source := "listobject.c:1317-1322", status := .proven
    prop := ``ListHintIgnoredWhenOverflowing, thm := some ``listHintIgnoredWhenOverflowing_proven },
  { id := "bytesobj-tuple-from-pair", pyFile := "Objects/tupleobject.c", pyFns := ["_PyTuple_FromPair", "_PyTuple_FromPairSteal"]
    statement := "_PyTuple_FromPair is PyTuple_Pack of two items, GC flag included."
    source := "twin: PyTuple_Pack, which it replaced in list_extend_dictitems", status := .proven
    prop := ``TupleFromPairIsPack, thm := some ``tupleFromPairIsPack_proven },
  { id := "bytesobj-tuple-hash-guard", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_hash"]
    statement := "The stack test of tuple_hash comes after the cache and leaves it alone; past it tuple_hash is the xxHash loop."
    source := "tupleobject.c:372-393", status := .proven
    prop := ``TupleHashGuard, thm := some ``tupleHashGuard_proven },
  { id := "bytesobj-list-binary-slice", pyFile := "Objects/listobject.c", pyFns := []
    statement := "l[a:b] under BINARY_SLICE gives what l[slice(a, b)] gives, for every pair of indices of any size."
    source := "twin: list_subscript", status := .proven
    prop := ``ListBinarySlice, thm := some ``listBinarySlice_proven },
  { id := "bytesobj-tuple-binary-slice", pyFile := "Objects/tupleobject.c", pyFns := []
    statement := "t[a:b] under BINARY_SLICE has the items of t[slice(a, b)], for an exact tuple and every pair of indices of any size."
    source := "twin: tuple_subscript", status := .proven
    prop := ``TupleBinarySlice, thm := some ``tupleBinarySlice_proven },
  { id := "bytesobj-iteritem-agrees", pyFile := "Objects/tupleobject.c", pyFns := ["tuple_iteritem", "list_iteritem"]
    statement := "tuple_iteritem and list_iteritem read what the iterators read and stop at the same place."
    source := "twin: the two iteration paths of a for loop", status := .proven
    prop := ``IterItemAgrees, thm := some ``iterItemAgrees_proven },
  { id := "bytesobj-list-del-like-pop", pyFile := "Objects/listobject.c", pyFns := ["list_ass_item_lock_held", "list_pop_impl"]
    statement := "del l[-1] and l.pop() leave the same list, allocation included, except for a list of one item, which pop clears."
    source := "listobject.c:1172, :1626-1630, :1636 (gh-158592)", status := .proven
    prop := ``ListDelLikePop, thm := some ``listDelLikePop_proven },
  { id := "bytesobj-list-ass-item-allocation", pyFile := "Objects/listobject.c", pyFns := ["list_ass_item_lock_held"]
    statement := "l[i] = x leaves the array alone, and del l[i] is list_resize to one item less."
    source := "listobject.c:1159-1179", status := .proven
    prop := ``ListAssItemAllocation, thm := some ``listAssItemAllocation_proven },
  { id := "bytesobj-list-resize-exact", pyFile := "Objects/listobject.c", pyFns := ["list_resize", "py_list_resize"]
    statement := "list_resize keeps the array when it is large enough and at most half empty or at most 32 slots, reallocates a larger array shrinking below half, allocates newsize + newsize/8 + 6 rounded down to a multiple of 4 (or newsize rounded up when the jump is larger), raises MemoryError growing past PY_SSIZE_T_MAX/8 slots, and never fails when shrinking."
    source := "listobject.c:96-216 (the comments at :103, :118-120, :144-146, :203-204; gh-158592)", status := .proven
    prop := ``ListResizeExact, thm := some ``listResizeExact_proven },
  { id := "bytesobj-list-ops-succeed", pyFile := "Objects/listobject.c"
    pyFns := ["list_resize", "valid_index", "list_append_impl", "_PyList_AppendTakeRefListResize", "ins1",
      "list_ass_item", "list_ass_item_lock_held", "list_clear_impl", "list_clear", "py_list_clear_impl",
      "list_extend_fast", "list_preallocate_exact", "list_extend_set", "list_ass_slice_lock_held", "list_ass_slice"]
    statement := "For every list with its invariant: append and insert succeed exactly when list_resize can grow the list by one (insert refuses NULL first, and clips its index); item store and delete succeed for every valid index and raise IndexError otherwise; clear frees the array; extend from a sequence or set and slice assignment succeed up to PY_SSIZE_T_MAX/16 items and raise MemoryError past PY_SSIZE_T_MAX/8, a list with no array taking an exact even allocation from a sequence and an over-allocation from a set; slice deletion always succeeds; a non-iterable raises TypeError."
    source := "Doc/library/stdtypes.rst mutable sequence types; listobject.c:502-528, :546-557, :893-921, :970-1089, :1159-1190, :1262-1298, :1388-1413", status := .proven
    prop := ``ListOpsSucceed, thm := some ``listOpsSucceed_proven
    notes := "The PyMem_Malloc of the recycle buffer in list_ass_slice_lock_held (:1006-1011) fails only when the allocator itself does, which no model here covers." },
  { id := "bytesobj-list-inplace-repeat", pyFile := "Objects/listobject.c"
    pyFns := ["list_inplace_repeat_lock_held", "list_inplace_repeat", "list_repeat_lock_held", "list_repeat"]
    statement := "For every list with its invariant: l *= 1 and [] *= n change nothing, l *= n for n < 1 frees the array, otherwise l *= n holds n copies up to PY_SSIZE_T_MAX/8 - 3 items and raises MemoryError past PY_SSIZE_T_MAX/8; the contents models of l * n and l *= n (sequences-list-repeat) are these functions."
    source := "Doc/library/stdtypes.rst common sequence operations, note (2); listobject.c:840-880, :1101-1156", status := .proven
    prop := ``ListInplaceRepeatSpec, thm := some ``listInplaceRepeatSpec_proven },
  { id := "bytesobj-capi-list-ops", pyFile := "Objects/listobject.c"
    pyFns := ["PyList_SetItem", "PyList_Insert", "PyList_Append", "PyList_SetSlice", "PyList_Clear", "PyList_Extend",
      "list_ass_slice", "list_extend_lock_held"]
    statement := "PyList_SetItem, PyList_Insert, PyList_Append, PyList_SetSlice, PyList_Clear and PyList_Extend refuse a non-list with SystemError; Insert and Append refuse NULL; on a list each does what the method does, success forced: insert and append exactly when the list can grow, slice deletion always, slice assignment up to PY_SSIZE_T_MAX/16 items, a non-iterable slice value raising TypeError, clear freeing the array, extend from a sequence."
    source := "Doc/c-api/list.rst", status := .proven
    prop := ``CApiListOps, thm := some ``cApiListOps_proven },
  { id := "bytesobj-capi-slice-concat", pyFile := "Objects/listobject.c"
    pyFns := ["PyList_GetSlice", "list_slice_lock_held", "PyList_New", "list_new_prealloc", "_PyList_Concat",
      "list_concat_lock_held"]
    statement := "PyList_GetSlice(a, i, j) is a[max(i,0):max(j,0)] for every pair of indices, exactly allocated; PyList_New(0) has no array and a size past PY_SSIZE_T_MAX/8 raises MemoryError; list_new_prealloc fails past that size; a + b refuses a non-list with the source's TypeError and is otherwise a's items then b's, or MemoryError past PY_SSIZE_T_MAX/8 items."
    source := "Doc/c-api/list.rst; listobject.c:261-327, :764-838; Include/pymem.h:63-65; Objects/obmalloc.c:1264", status := .proven
    prop := ``CApiSliceConcat, thm := some ``cApiSliceConcat_proven },
  { id := "bytesobj-list-clear", pyFile := "Objects/listobject.c"
    pyFns := ["list_clear_impl", "list_clear", "py_list_clear_impl", "PyList_Clear"]
    statement := "l.clear() and PyList_Clear leave every list empty with no array (sys.getsizeof 40) and release the old items last to first."
    source := "Doc/library/stdtypes.rst (s.clear()); listobject.c:900-911 (the list is emptied before the items are released)", status := .proven
    prop := ``ListClearSpec, thm := some ``listClearSpec_proven },
  { id := "bytesobj-contains-reentrant", pyFile := "Objects/listobject.c"
    pyFns := ["list_contains", "list_get_item_ref", "_PyList_GetItemRef"]
    statement := "x in l rereads the list after each comparison, for every comparison: it stops at the current end, goes on in the list the comparison left, and ends on a true or raising comparison; with an __eq__ that pops, only the first ceil(n/2) items are compared and n // 2 remain."
    source := "listobject.c:676-693; Doc/reference/expressions.rst membership tests", status := .proven
    prop := ``ContainsReentrant, thm := some ``containsReentrant_proven },
  { id := "bytesobj-repr-reentrant", pyFile := "Objects/listobject.c", pyFns := ["list_repr_impl", "list_repr"]
    statement := "repr(l) rereads the size and the slot after each item's repr, as the comment at listobject.c:621-622 requires: with a __repr__ that pops, the result is the repr of the first ceil(n/2) items and n // 2 remain; a list or tuple already being printed prints as [...] or (...)."
    source := "listobject.c:601-654 (the comment at :621-622); Objects/object.c Py_ReprEnter", status := .proven
    prop := ``ReprReentrant, thm := some ``reprReentrant_proven },
  { id := "bytesobj-list-ass-slice-clear", pyFile := "Objects/listobject.c"
    pyFns := ["list_ass_slice_lock_held", "list_extend_fast"]
    statement := "A slice assignment or deletion whose result is empty frees the array; extend from a sequence into a list whose array has room and is at most half empty keeps that array."
    source := "listobject.c:1006-1010, :1275-1283, :121-128", status := .proven
    prop := ``ListAssSliceClear, thm := some ``listAssSliceClear_proven },
  { id := "bytesobj-list-extend-dispatch", pyFile := "Objects/listobject.c"
    pyFns := ["_list_extend", "list_extend_impl", "_PyList_Extend", "list_inplace_concat", "list_extend_dict",
      "list_extend_dictitems", "list_extend_set", "list_extend_iter_lock_held"]
    statement := "_list_extend tests exact types, so a subclass of list, tuple, set or dict goes to its own iterator; an exact dict and its keys view store the keys and the values view the values, success forced; the items view stores a tuple per entry and, when one fails, keeps the old items and the pairs built so far; the generic path reads the size after the length hint, and a failed append keeps what was appended."
    source := "Doc/library/stdtypes.rst (s.extend(t)); listobject.c:1300-1373, :1415-1532", status := .proven
    prop := ``ListExtendDispatch, thm := some ``listExtendDispatch_proven },
  { id := "bytesobj-list-extend-iter-reentrant", pyFile := "Objects/listobject.c"
    pyFns := ["list_extend_iter_lock_held"]
    statement := "list.extend from an iterator that appends z to the list before yielding each item leaves old ++ [z, x0, z, x1, ...], for every list and every such iterator: the size and allocation are reread after each __next__."
    source := "listobject.c:1338-1365", status := .proven
    prop := ``ListExtendIterReentrant, thm := some ``listExtendIterReentrant_proven },
  { id := "bytesobj-sortslice-moves", pyFile := "Objects/listobject.c"
    pyFns := ["sortslice_copy", "sortslice_copy_incr", "sortslice_copy_decr", "sortslice_memcpy",
      "sortslice_memmove", "sortslice_advance"]
    statement := "Slot by slot, for every slice: sortslice_copy puts s2[j] at s1[i] in keys and values and changes nothing else; copy_incr and copy_decr copy at the cursors and step them forward or back; memcpy and memmove put s2[j+k] at s1[i+k] for k < n, memmove reading the source as it was; advance moves the cursor n slots; a slice without values stays without."
    source := "listobject.c:1660-1723 (keys and values always moved in sync)", status := .proven
    prop := ``SortsliceMoves, thm := some ``sortsliceMoves_proven }
]

end PyLean.BytesObj.Seq
