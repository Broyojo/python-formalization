import PyLean.Registry
import PyLean.Sequences.Diff
import PyLean.Sequences.DequeProps
import PyLean.Sequences.Subscript
import PyLean.Sequences.Index
import PyLean.Sequences.Insert
import PyLean.Sequences.PopRemove
import PyLean.Sequences.SliceAssign
import PyLean.Sequences.ArraySlice
import PyLean.Sequences.ArrayRange
import PyLean.Sequences.DequeRepeat
import PyLean.Sequences.Reverse

/-!
`collections.deque` (`Modules/_collectionsmodule.c`), `list` (`Objects/listobject.c`) and
`array.array` (`Modules/arraymodule.c`, typecodes `b B h i q`) mutable-sequence methods,
CPython 3.14.7, on int elements. The deque model keeps the C struct's `leftindex`,
`rightindex` and `maxlen` and does the block arithmetic of every walk; its layout invariant
(`Deque.WF`) is a hypothesis of the deque properties and is shown to be preserved.
-/

namespace PyLean.Sequences

open PyLean.Registry

def entries : List Entry := [
  { id := "sequences-deque-ends-evict", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_append_lock_held", "deque_appendleft_lock_held", "deque_extend_impl",
      "deque_extendleft_impl", "deque_pop_impl", "deque_popleft_impl"]
    statement := "For every deque satisfying the block-layout invariant and any items: append/extend/+=/extend(d) keep the last maxlen items of items + xs, appendleft/extendleft keep the first maxlen of reversed(xs) + items, pop/popleft remove the last/first item or raise IndexError when empty; the invariant and maxlen are preserved."
    source := "Doc/library/collections.rst:475-481 (bounded deques discard from the opposite end), :488-565", status := .proven
    prop := ``DequeEndsEvict, thm := some ``dequeEndsEvict_proven },
  { id := "sequences-deque-construct", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_new", "deque_init_impl"]
    statement := "deque(xs, maxlen) holds xs (maxlen None) or the last maxlen items of xs (0 <= maxlen <= sys.maxsize); a negative maxlen raises ValueError and one outside Py_ssize_t OverflowError."
    source := "Doc/library/collections.rst:459-481", status := .proven
    prop := ``DequeConstruct, thm := some ``dequeConstruct_proven },
  { id := "sequences-deque-rotate-loop", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["_deque_rotate", "deque_rotate_impl"]
    statement := "For every non-empty deque and every int n: rotate(n) raises OverflowError exactly outside Py_ssize_t, and otherwise leaves the same items as n repetitions of d.appendleft(d.pop()) (or -n of d.append(d.popleft())), keeping the block layout invariant, for n of any size and sign."
    source := "Doc/library/collections.rst:574-581", status := .proven
    prop := ``RotateLoop, thm := some ``rotateLoop_proven
    notes := "Covers the C normalisation with truncating %, both chunked block loops (m = min(n, rightindex+1, leftindex) etc.), and the block allocation/free bookkeeping." },
  { id := "sequences-subscript-agree", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_item_lock_held", "deque_ass_item_lock_held", "deque_del_item", "list_subscript",
      "list_ass_item_lock_held", "array_subscr", "array_ass_subscr"]
    statement := "For every int i (any size): l[i], l[i] = v, del l[i], a[i], del a[i], d[i], d[i] = v and del d[i] add len to a negative index and act on exactly item i when it is in range, raise IndexError otherwise (messages per type), and the deque's left/right block walks reach item i."
    source := "invariant: sequence indexing; Doc/library/stdtypes.rst:1237-1242", status := .proven
    prop := ``SubscriptAgree, thm := some ``subscriptAgree_proven },
  { id := "sequences-index-agree", pyFile := "Objects/listobject.c"
    pyFns := ["list_index_impl", "array_array_index_impl", "deque_index_impl"]
    statement := "For every list l (len <= sys.maxsize), x and any int start/stop: list.index, array.index and deque.index all return the first position of x in range(*slice(start, stop).indices(len(l))) or raise ValueError."
    source := "list/array/deque index docstrings; Doc/library/stdtypes.rst common sequence s.index(x[, i[, j]])", status := .proven
    prop := ``IndexAgree, thm := some ``indexAgree_proven
    notes := "array.index does not clip a negative stop at 0, which is harmless; the deque's whole-block skip loop is covered." },
  { id := "sequences-insert-agree", pyFile := "Objects/listobject.c"
    pyFns := ["list_insert_impl", "ins1", "array_array_insert_impl", "deque_insert_impl"]
    statement := "For every list l, int i and x: array.insert (x fits the typecode) and deque.insert (deque not full) give list.insert's result for every i; a full bounded deque raises IndexError('deque already at its maximum size')."
    source := "Doc/library/collections.rst:539-544; invariant: same method, three types", status := .proven
    prop := ``InsertAgree, thm := some ``insertAgree_proven },
  { id := "sequences-insert-is-slice-assign", pyFile := "Objects/listobject.c"
    pyFns := ["list_insert_impl", "list_ass_subscript_lock_held"]
    statement := "For every list l and every int i, l.insert(i, x) has the same effect as l[i:i] = [x]."
    source := "Doc/library/stdtypes.rst:1336-1343", status := .refuted
    prop := ``InsertIsSliceAssign, thm := some ``insertIsSliceAssign_refuted
    bug := some "sequences-insert-huge-index-vs-slice"
    notes := "|i| >= 2**63: insert raises OverflowError (Py_ssize_t clinic converter), the slice assignment clips. Very low value." },
  { id := "sequences-insert-is-slice-assign-ssize", pyFile := "Objects/listobject.c"
    pyFns := ["list_insert_impl", "list_ass_subscript_lock_held"]
    statement := "For every list l and every int i inside Py_ssize_t, l.insert(i, x) has the same effect as l[i:i] = [x]."
    source := "Doc/library/stdtypes.rst:1336-1343", status := .proven
    prop := ``InsertIsSliceAssignSsize, thm := some ``insertIsSliceAssignSsize_proven },
  { id := "sequences-pop-remove-count-agree", pyFile := "Objects/listobject.c"
    pyFns := ["list_pop_impl", "array_array_pop_impl", "deque_pop_impl", "deque_popleft_impl",
      "list_remove_impl", "array_array_remove_impl", "deque_remove_impl", "list_count_impl",
      "array_array_count_impl", "deque_count_impl"]
    statement := "For every list l, x and optional int i: list.pop(i) and array.pop(i) behave identically up to the empty-sequence message; deque.pop()/popleft() equal list.pop()/pop(0) up to that message; remove(x) deletes the first equal item in all three (ValueError otherwise); count(x) agrees."
    source := "invariant: same methods, three types; Doc/library/stdtypes.rst:1345-1359", status := .proven
    prop := ``PopRemoveCountAgree, thm := some ``popRemoveCountAgree_proven },
  { id := "sequences-list-slice-assign", pyFile := "Objects/listobject.c"
    pyFns := ["list_ass_subscript_lock_held", "list_ass_slice_lock_held", "adjust_slice_indexes"]
    statement := "For every list (len <= sys.maxsize), every slice with int/None parts (any size, step 0 included) and every t: l[s] = t raises ValueError for step 0; with (a, b, c) = s.indices(len(l)) and L = len(range(a, b, c)), step 1 replaces l[a:max(a, b)] by t, any other step raises ValueError unless len(t) == L and replaces l[a + k*c] by t[k]."
    source := "Doc/reference/simple_stmts.rst (slicing targets); Doc/library/stdtypes.rst:1244-1269 note (1)", status := .proven
    prop := ``ListSliceAssign, thm := some ``listSliceAssign_proven },
  { id := "sequences-array-slice-assign-agree", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_ass_subscr"]
    statement := "For every array (any typecode), slice and same-typecode array t, a[s] = t gives the same items as list slice assignment, or an exception of the same class."
    source := "Doc/library/stdtypes.rst:1252-1269 note (1); Doc/library/array.rst (arrays behave like lists)", status := .refuted
    prop := ``ArraySliceAssignAgree, thm := some ``arraySliceAssignAgree_refuted
    bug := some "sequences-array-extended-slice-empty-deletes"
    notes := "a[::2] = array('b') deletes the slice; list raises ValueError. bytearray behaves like array." },
  { id := "sequences-array-slice-assign-agree-nonempty", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_ass_subscr"]
    statement := "For every array, slice and non-empty same-typecode array t, a[s] = t agrees with list slice assignment (same items, or an exception of the same class)."
    source := "Doc/library/array.rst (arrays behave like lists)", status := .proven
    prop := ``ArraySliceAssignAgreeNonempty, thm := some ``arraySliceAssignAgreeNonempty_proven },
  { id := "sequences-array-range-check", pyFile := "Modules/arraymodule.c"
    pyFns := ["b_setitem", "BB_setitem", "h_setitem", "i_setitem", "q_setitem", "ins1", "array_new"]
    statement := "For typecodes b, B, h, i, q and every int v: append, insert (index in Py_ssize_t), a[j] = v (valid j) and array(tc, xs) store exactly v when it fits the C type's range and raise OverflowError (array unchanged) otherwise."
    source := "Doc/library/array.rst (value ranges of the typecodes); invariant: no silent truncation", status := .proven
    prop := ``ArrayRangeCheck, thm := some ``arrayRangeCheck_proven
    notes := "'b' rejects 128..32767 with 'signed char is greater than maximum' but larger values with the 'signed short integer' message of PyArg_Parse('h'); class is OverflowError throughout." },
  { id := "sequences-deque-irepeat", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_inplace_repeat_lock_held", "deque_repeat"]
    statement := "For every deque and every int n in Py_ssize_t whose repeated result list(d)*n, cut to the last maxlen items, has at most sys.maxsize items (always for bounded deques), d *= n succeeds with exactly those items."
    source := "Doc/library/collections.rst:475-478, 599-600", status := .refuted
    prop := ``DequeIRepeat, thm := some ``dequeIRepeat_refuted
    bug := some "sequences-deque-imul-maxlen-memoryerror"
    notes := "deque([1, 2], maxlen=3) *= 2**62 raises MemoryError: the overflow guard precedes the maxlen reduction (the one-item fast path applies maxlen first)." },
  { id := "sequences-deque-irepeat-checked", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_inplace_repeat_lock_held"]
    statement := "For every deque with at most one item, or with len(d) * n <= sys.maxsize, d *= n (n in Py_ssize_t) holds the last maxlen items of list(d) * n, keeping the invariant and maxlen."
    source := "Doc/library/collections.rst:475-478, 599-600", status := .proven
    prop := ``DequeIRepeatChecked, thm := some ``dequeIRepeatChecked_proven
    notes := "Includes the ceil(maxlen / size) shortcut (periodicity of the repeated list) and the single-item block-filling path." },
  { id := "sequences-list-repeat", pyFile := "Objects/listobject.c"
    pyFns := ["list_inplace_repeat_lock_held", "list_repeat_lock_held"]
    statement := "For every list (len <= sys.maxsize) and int n: l *= n and l * n agree; outside Py_ssize_t both raise OverflowError; n <= 0 gives []; otherwise l repeated n times, with MemoryError exactly when that exceeds sys.maxsize items."
    source := "Doc/library/stdtypes.rst:1263-1275 note (2)", status := .proven
    prop := ``ListRepeat, thm := some ``listRepeat_proven },
  { id := "sequences-deque-copy-concat", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_copy_impl", "deque_concat_lock_held"]
    statement := "For every deque d and deque other: d.copy() has the same items and maxlen; d + other holds the last d.maxlen items of list(d) + list(other) with d's maxlen; results keep the invariant."
    source := "Doc/library/collections.rst:503-507, 599-600", status := .proven
    prop := ``DequeCopyConcat, thm := some ``dequeCopyConcat_proven },
  { id := "sequences-deque-reverse", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_reverse_impl"]
    statement := "For every deque with the layout invariant, reverse() swaps through the left and right block cursors len // 2 times, touching only used slots, and leaves exactly the reversed items with the layout and maxlen unchanged."
    source := "Doc/library/collections.rst:567-571", status := .proven
    prop := ``DequeReverse, thm := some ``dequeReverse_proven }
]

end PyLean.Sequences
