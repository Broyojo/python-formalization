import PyLean.Registry
import PyLean.Sequences.Diff
import PyLean.Sequences.DequeProps
import PyLean.Sequences.Subscript
import PyLean.Sequences.Index
import PyLean.Sequences.Insert
import PyLean.Sequences.PopRemove
import PyLean.Sequences.SliceAssign
import PyLean.Sequences.DequeRepeat
import PyLean.Sequences.Reverse
import PyLean.Sequences.ArrayItems
import PyLean.Sequences.ArraySlice
import PyLean.Sequences.ArrayBytes
import PyLean.Sequences.ArrayOps
import PyLean.Sequences.ArrayText
import PyLean.Sequences.CollectionsProps

/-!
`collections.deque`, `collections.defaultdict`, `_count_elements`, `_tuplegetter`
(`Modules/_collectionsmodule.c`), `list` (`Objects/listobject.c`, the methods shared with
deque and array; the rest of that file belongs to `BytesObj`) and `array.array`
(`Modules/arraymodule.c`, all typecodes), CPython 3.15.2. `deque` and `list` are generic in
the element type, with comparison as an explicit function; the deque model keeps the C
struct's `leftindex`, `rightindex` and `maxlen`, does the block arithmetic of every walk,
and its layout invariant (`Deque.WF`) is a hypothesis of the deque properties and is shown
to be preserved. `array` items are the stored C values.
-/

namespace PyLean.Sequences

open PyLean.Registry

def entries : List Entry := [
  { id := "sequences-deque-ends-evict", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_append_lock_held", "deque_append_impl", "deque_appendleft_lock_held",
      "deque_appendleft_impl", "deque_extend_impl", "deque_extendleft_impl", "deque_pop_impl",
      "deque_popleft_impl", "deque_clear", "deque_clearmethod_impl", "deque_inplace_concat",
      "finalize_iterator", "consume_iterator"]
    statement := "For every deque satisfying the block-layout invariant and any items: append/extend/+=/extend(d) keep the last maxlen items of items + xs, appendleft/extendleft keep the first maxlen of reversed(xs) + items, pop/popleft remove the last/first item or raise IndexError when empty; the invariant and maxlen are preserved."
    source := "Doc/library/collections.rst:479-485 (bounded deques discard from the opposite end), :488-565", status := .proven
    prop := ``DequeEndsEvict, thm := some ``dequeEndsEvict_proven },
  { id := "sequences-deque-construct", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_new", "deque_init_impl", "deque_len", "deque_get_maxlen"]
    statement := "deque(xs, maxlen) holds xs (maxlen None) or the last maxlen items of xs (0 <= maxlen <= sys.maxsize); a negative maxlen raises ValueError and one outside Py_ssize_t OverflowError."
    source := "Doc/library/collections.rst:463-485", status := .proven
    prop := ``DequeConstruct, thm := some ``dequeConstruct_proven },
  { id := "sequences-deque-rotate-loop", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["_deque_rotate", "deque_rotate_impl"]
    statement := "For every non-empty deque and every int n: rotate(n) raises OverflowError exactly outside Py_ssize_t, and otherwise leaves the same items as n repetitions of d.appendleft(d.pop()) (or -n of d.append(d.popleft())), keeping the block layout invariant, for n of any size and sign."
    source := "Doc/library/collections.rst:578-585", status := .proven
    prop := ``RotateLoop, thm := some ``rotateLoop_proven
    notes := "Covers the C normalisation with truncating %, both chunked block loops (m = min(n, rightindex+1, leftindex) etc.), and the block allocation/free bookkeeping." },
  { id := "sequences-subscript-agree", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_item_lock_held", "deque_item", "deque_ass_item_lock_held", "deque_ass_item",
      "deque_del_item", "valid_index", "list_subscript", "list_ass_item_lock_held"]
    statement := "For every element type and every int i (any size): l[i], l[i] = v, del l[i], d[i], d[i] = v and del d[i] add len to a negative index and act on exactly item i when it is in range, raise IndexError otherwise (messages per type), and the deque's left/right block walks reach item i."
    source := "invariant: sequence indexing; Doc/builtins/stdtypes.rst:1513-1520", status := .proven
    prop := ``SubscriptAgree, thm := some ``subscriptAgree_proven },
  { id := "sequences-index-agree", pyFile := "Objects/listobject.c"
    pyFns := ["list_index_impl", "deque_index_impl"]
    statement := "For every element type, every equality function, every list l (len <= sys.maxsize) and any int start/stop: list.index and deque.index return the first matching position in range(*slice(start, stop).indices(len(l))) or raise ValueError."
    source := "list/array/deque index docstrings; Doc/builtins/stdtypes.rst common sequence s.index(x[, i[, j]])", status := .proven
    prop := ``IndexAgree, thm := some ``indexAgree_proven
    notes := "The deque's whole-block skip loop is covered." },
  { id := "sequences-insert-agree", pyFile := "Objects/listobject.c"
    pyFns := ["list_insert_impl", "ins1", "deque_insert_impl"]
    statement := "For every element type, list l, int i and x: deque.insert (deque not full) gives list.insert's result for every i; a full bounded deque raises IndexError('deque already at its maximum size')."
    source := "Doc/library/collections.rst:543-548; invariant: same method, three types", status := .proven
    prop := ``InsertAgree, thm := some ``insertAgree_proven },
  { id := "sequences-insert-is-slice-assign", pyFile := "Objects/listobject.c"
    pyFns := ["list_insert_impl", "list_ass_subscript_lock_held"]
    statement := "For every list l and every int i, l.insert(i, x) has the same effect as l[i:i] = [x]."
    source := "Doc/builtins/stdtypes.rst:1612-1615", status := .refuted
    prop := ``InsertIsSliceAssign, thm := some ``insertIsSliceAssign_refuted
    bug := some "sequences-insert-huge-index-vs-slice"
    notes := "|i| >= 2**63: insert raises OverflowError (Py_ssize_t clinic converter), the slice assignment clips. Very low value." },
  { id := "sequences-insert-is-slice-assign-ssize", pyFile := "Objects/listobject.c"
    pyFns := ["list_insert_impl", "list_ass_subscript_lock_held"]
    statement := "For every list l and every int i inside Py_ssize_t, l.insert(i, x) has the same effect as l[i:i] = [x]."
    source := "Doc/builtins/stdtypes.rst:1612-1615", status := .proven
    prop := ``InsertIsSliceAssignSsize, thm := some ``insertIsSliceAssignSsize_proven },
  { id := "sequences-pop-remove-count-agree", pyFile := "Objects/listobject.c"
    pyFns := ["list_pop_impl", "deque_pop_impl", "deque_popleft_impl",
      "list_remove_impl", "deque_remove_impl", "list_count_impl", "deque_count_impl",
      "deque_contains", "deque_contains_lock_held"]
    statement := "For every element type, equality function, list l and optional int i: deque.pop()/popleft() equal list.pop()/pop(0) up to the empty-sequence message; remove(x) deletes the first equal item in both (ValueError otherwise); count(x) and x in d agree."
    source := "invariant: same methods, three types; Doc/builtins/stdtypes.rst:1622-1635", status := .proven
    prop := ``PopRemoveCountAgree, thm := some ``popRemoveCountAgree_proven },
  { id := "sequences-list-slice-assign", pyFile := "Objects/listobject.c"
    pyFns := ["list_ass_subscript_lock_held", "list_ass_slice_lock_held", "adjust_slice_indexes"]
    statement := "For every list (len <= sys.maxsize), every slice with int/None parts (any size, step 0 included) and every t: l[s] = t raises ValueError for step 0; with (a, b, c) = s.indices(len(l)) and L = len(range(a, b, c)), step 1 replaces l[a:max(a, b)] by t, any other step raises ValueError unless len(t) == L and replaces l[a + k*c] by t[k]."
    source := "Doc/reference/simple_stmts.rst (slicing targets); Doc/builtins/stdtypes.rst:1520-1546 note (1)", status := .proven
    prop := ``ListSliceAssign, thm := some ``listSliceAssign_proven },
  { id := "sequences-array-slice-assign-agree", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_ass_subscr"]
    statement := "For every array without exported buffers (any typecode), slice and same-typecode array t, a[s] = t gives the same items as list slice assignment, or an exception of the same class."
    source := "Doc/builtins/stdtypes.rst:1528-1546 note (1); Doc/library/array.rst (arrays behave like lists)", status := .refuted
    prop := ``ArraySliceAssignAgree, thm := some ``arraySliceAssignAgree_refuted
    bug := some "sequences-array-extended-slice-empty-deletes"
    notes := "a[::2] = array('b') deletes the slice; list raises ValueError. bytearray behaves like array." },
  { id := "sequences-array-slice-assign-agree-nonempty", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_ass_subscr"]
    statement := "For every array, slice and non-empty same-typecode array t, a[s] = t agrees with list slice assignment (same items, or an exception of the same class)."
    source := "Doc/library/array.rst (arrays behave like lists)", status := .proven
    prop := ``ArraySliceAssignAgreeNonempty, thm := some ``arraySliceAssignAgreeNonempty_proven },
  { id := "sequences-array-range-check", pyFile := "Modules/arraymodule.c"
    pyFns := ["b_setitem", "BB_setitem", "h_setitem", "HH_setitem", "i_setitem", "II_setitem",
      "l_setitem", "LL_setitem", "q_setitem", "QQ_setitem", "ins1", "ins", "array_resize",
      "array_array_append_impl", "array_array_insert_impl", "array_new"]
    statement := "For every integer typecode (b B h H i I l L q Q), every array and every object with __index__ value v: append, insert (index in Py_ssize_t), a[j] = v (valid j) and array(tc, xs) store exactly v when it fits the C type's range and raise OverflowError (array unchanged) otherwise."
    source := "Doc/library/array.rst (value ranges of the typecodes); invariant: no silent truncation", status := .proven
    prop := ``ArrayRangeCheck, thm := some ``arrayRangeCheck_proven
    notes := "'b' rejects 128..32767 with 'signed char is greater than maximum' but larger values with the 'signed short integer' message of PyArg_Parse('h'); class is OverflowError throughout." },
  { id := "sequences-array-subscript", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_subscr", "array_ass_subscr", "array_item", "array_ass_item", "getarrayitem",
      "array_del_slice", "array_length"]
    statement := "For every array and int i: a[i], a[i] = v and del a[i] are the list operations on the stored values, with IndexError out of range; the sq_item and sq_ass_item slots do the same."
    source := "invariant: sequence indexing", status := .proven
    prop := ``ArraySubscript, thm := some ``arraySubscript_proven },
  { id := "sequences-array-insert-agree", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_insert_impl", "ins", "ins1"]
    statement := "For every array without exported buffers, int i and storable v: a.insert(i, v) gives list.insert on the stored values, OverflowError outside Py_ssize_t included."
    source := "Doc/library/array.rst insert; invariant: same method as list", status := .proven
    prop := ``ArrayInsertAgree, thm := some ``arrayInsertAgree_proven },
  { id := "sequences-array-search-agree", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_index_impl", "array_array_count_impl", "array_contains",
      "array_array_remove_impl", "array_array_pop_impl", "getarrayitem", "array_del_slice"]
    statement := "For every array whose items decode and every pure equality test: index, count, in, remove and pop agree with the list operations (up to messages)."
    source := "invariant: same methods as list", status := .proven
    prop := ``ArraySearchAgree, thm := some ``arraySearchAgree_proven
    notes := "array.index does not clip a negative stop at 0, which is harmless." },
  { id := "sequences-array-non-index-item", pyFile := "Modules/arraymodule.c"
    pyFns := ["b_setitem", "BB_setitem", "h_setitem", "HH_setitem", "i_setitem", "II_setitem",
      "l_setitem", "LL_setitem", "q_setitem", "QQ_setitem"]
    statement := "For every integer typecode, a value without __index__ raises the exception of the __index__ conversion."
    source := "invariant", status := .proven
    prop := ``ArrayNonIndexItem, thm := some ``arrayNonIndexItem_proven },
  { id := "sequences-array-get-set", pyFile := "Modules/arraymodule.c"
    pyFns := ["b_getitem", "b_setitem", "BB_getitem", "BB_setitem", "h_getitem", "h_setitem",
      "HH_getitem", "HH_setitem", "i_getitem", "i_setitem", "II_getitem", "II_setitem",
      "l_getitem", "l_setitem", "LL_getitem", "LL_setitem", "q_getitem", "q_setitem",
      "QQ_getitem", "QQ_setitem", "getarrayitem"]
    statement := "For every integer typecode and every value in its range, storing and reading give the same value."
    source := "invariant", status := .proven
    prop := ``ArrayGetSet, thm := some ``arrayGetSet_proven },
  { id := "sequences-array-char-items", pyFile := "Modules/arraymodule.c"
    pyFns := ["u_getitem", "u_setitem", "w_getitem", "w_setitem"]
    statement := "u and w store the code point of a one-character str and read the same character back; anything else raises TypeError; a stored value outside [0, 0x10FFFF] raises ValueError on reading."
    source := "Doc/library/array.rst typecode table", status := .proven
    prop := ``ArrayCharDouble, thm := some ``arrayCharDouble_proven
    notes := "The d clause of this property is about bit patterns only; f and d are open in sequences-array-float-items." },
  { id := "sequences-array-float-items", pyFile := "Modules/arraymodule.c"
    pyFns := ["f_getitem", "f_setitem", "d_getitem", "d_setitem"]
    statement := "Every bit pattern stored in an f or d array reads as a float and stores back unchanged."
    source := "invariant", status := .open
    prop := ``ArrayFloatItems
    notes := "Waits for lean/PyLean/Binary64/. The model and the difftest cover these paths." },
  { id := "sequences-array-del-slice-agree", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_ass_subscr"]
    statement := "del a[s] agrees with del l[s] for every slice."
    source := "invariant: same statement as list", status := .open
    prop := ``ArrayDelSliceAgree
    notes := "Needs the invariant of the compaction loop: the first cur_i - i cells hold the kept items, the cells from cur_i on the original ones. Plan: define the kept prefix recursively, show it equals the filter over positions of range(a, b, c)." },
  { id := "sequences-array-bytes-round-trip", pyFile := "Modules/arraymodule.c"
    pyFns := ["frombytes", "array_array_frombytes_impl", "array_array_tobytes_impl"]
    statement := "For every array b and a of the same typecode without exports: a.frombytes(b.tobytes()) gives a + b; len(b.tobytes()) == len(b) * itemsize; a length not a multiple of itemsize raises ValueError."
    source := "Doc/library/array.rst frombytes, tobytes", status := .proven
    prop := ``ArrayBytesRoundTrip, thm := some ``arrayBytesRoundTrip_proven },
  { id := "sequences-array-byteswap", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_byteswap_impl"]
    statement := "For every array of every typecode, byteswap reverses the bytes of each item (of each part, real part first, for Zf and Zd), keeps the value range and is its own inverse."
    source := "Doc/library/array.rst byteswap", status := .proven
    prop := ``ArrayByteswap, thm := some ``arrayByteswap_proven },
  { id := "sequences-array-concat", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_concat", "array_inplace_concat", "array_do_extend", "array_array_extend_impl"]
    statement := "a + b, a += b and a.extend(b) for arrays of the same typecode give the items of a then b; other typecodes and non-arrays raise TypeError."
    source := "Doc/library/array.rst extend; invariant", status := .proven
    prop := ``ArrayConcat, thm := some ``arrayConcat_proven },
  { id := "sequences-array-iter-extend", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_iter_extend", "array_array_extend_impl"]
    statement := "a.extend(iterable) stores items one by one: a refused item or a raising iterator leaves the earlier items appended; a non-iterable raises TypeError."
    source := "Doc/library/array.rst extend", status := .refuted
    prop := ``ArrayIterExtend, thm := some ``arrayIterExtend_refuted
    bug := some "sequences-array-e-ins1-overflow-keeps-slot"
    notes := "array('e').extend([65536.0]) raises OverflowError and leaves one uninitialised item." },
  { id := "sequences-array-iter-extend-exact", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_iter_extend", "array_array_extend_impl"]
    statement := "a.extend(iterable), for every typecode, leaves the items stored one by one, plus the slot of an e item that passed the check of setitem(self, -1, v) and was refused by the store; for every other typecode a refused item or a raising iterator leaves exactly the earlier items; a non-iterable raises TypeError."
    source := "Doc/library/array.rst extend", status := .proven
    prop := ``ArrayIterExtendExact, thm := some ``arrayIterExtendExact_proven },
  { id := "sequences-array-ins1-atomic", pyFile := "Modules/arraymodule.c"
    pyFns := ["ins1", "ins", "array_array_append_impl", "array_array_insert_impl", "e_setitem"]
    statement := "For every array without exported buffers, a.append(v) or a.insert(i, v) that raises leaves the array as it was."
    source := "invariant: a failed call changes nothing", status := .refuted
    prop := ``ArrayIns1Atomic, thm := some ``arrayIns1Atomic_refuted
    bug := some "sequences-array-e-ins1-overflow-keeps-slot"
    notes := "array('e').append(65536.0): setitem(self, -1, v) packs nothing, the store after the resize raises OverflowError." },
  { id := "sequences-array-ins1-failure", pyFile := "Modules/arraymodule.c"
    pyFns := ["ins1", "ins", "array_array_append_impl", "array_array_insert_impl"]
    statement := "For every typecode but e, append and insert of a value the store refuses raise its exception and leave the array as it was; a value that passes the first check and is refused by the store is an e item, and append raises with a new last slot."
    source := "invariant: a failed call changes nothing", status := .proven
    prop := ``ArrayIns1Failure, thm := some ``arrayIns1Failure_proven },
  { id := "sequences-array-repeat", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_repeat", "array_inplace_repeat", "newarrayobject", "newarrayobject_untracked"]
    statement := "For every array and int n: a * n and a *= n give the same items as list repetition, OverflowError outside Py_ssize_t included."
    source := "invariant: same operators as list", status := .proven
    prop := ``ArrayRepeat, thm := some ``arrayRepeat_proven },
  { id := "sequences-array-clear-copy", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_clear_impl", "array_array___copy___impl", "array_array___deepcopy___impl",
      "array_slice"]
    statement := "clear empties an array, or raises BufferError while exported; copies are array.array with the same typecode and items; array_slice clips its bounds."
    source := "Doc/library/array.rst clear", status := .proven
    prop := ``ArrayClearCopy, thm := some ``arrayClearCopy_proven
    notes := "copy.copy of a subclass gives a plain array: python/cpython#152042." },
  { id := "sequences-array-fromlist", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_fromlist_impl", "array_array_tolist_impl", "setarrayitem", "getarrayitem"]
    statement := "a.fromlist(l) is all or nothing; a.tolist() on an integer typecode gives the items."
    source := "Doc/library/array.rst fromlist", status := .proven
    prop := ``ArrayFromList, thm := some ``arrayFromList_proven },
  { id := "sequences-array-reverse", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_reverse_impl"]
    statement := "For every array, a.reverse() reverses the items and changes nothing else."
    source := "Doc/library/array.rst reverse", status := .proven
    prop := ``ArrayReverse, thm := some ``arrayReverse_proven },
  { id := "sequences-array-attrs", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_resize", "newarrayobject", "newarrayobject_untracked", "array_length",
      "array_array___sizeof___impl", "array_array_buffer_info_impl", "array_get_typecode",
      "array_get_itemsize"]
    statement := "array_resize and newarrayobject keep len <= allocated and a NULL buffer only when empty, so __sizeof__ covers the items, buffer_info is consistent, typecode names the descriptor and len(tobytes()) == len * itemsize."
    source := "invariant", status := .proven
    prop := ``ArrayAttrs, thm := some ``arrayAttrs_proven },
  { id := "sequences-array-buffer", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_buffer_getbuf", "array_buffer_relbuf", "array_resize"]
    statement := "memoryview(a) has the array's format, itemsize, length and bytes; releasing restores the array; while exported, size changes raise BufferError."
    source := "Doc/library/array.rst; invariant", status := .proven
    prop := ``ArrayBuffer, thm := some ``arrayBuffer_proven },
  { id := "sequences-array-iterator", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_iter", "arrayiter_next", "array_arrayiterator___reduce___impl",
      "array_arrayiterator___setstate___impl"]
    statement := "iter(a) yields the items in order, stays exhausted once exhausted, and __reduce__ and __setstate__ restore the position, clipped to the array."
    source := "invariant: iterator protocol", status := .proven
    prop := ``ArrayIterator, thm := some ``arrayIterator_proven },
  { id := "sequences-array-reduce", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array___reduce_ex___impl", "array__array_reconstructor_impl", "make_array",
      "typecode_to_mformat_code"]
    statement := "pickle of an array: from protocol 3 on, every typecode rebuilds the same type, typecode and items from the native format; below protocol 3 the integer typecodes do so from the list."
    source := "invariant: pickle round trip", status := .proven
    prop := ``ArrayReduce, thm := some ``arrayReduce_proven
    notes := "The other machine formats are mirrored and difftested; the property only reaches the native one." },
  { id := "sequences-array-reconstruct-utf", pyFile := "Modules/arraymodule.c"
    pyFns := ["array__array_reconstructor_impl"]
    statement := "_array_reconstructor(array, 'w', UTF32_BE, s.encode('utf-32-be')) rebuilds every surrogate-free s."
    source := "invariant: pickles load across byte orders", status := .refuted
    prop := ``ArrayReconstructUTF, thm := some ``arrayReconstructUTF_refuted
    bug := some "sequences-array-mformat-utf-sizes"
    notes := "Duplicate of python/cpython#155850, open. Reproduces on main." },
  { id := "sequences-array-w-tounicode", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_tounicode_impl"]
    statement := "array('w', s).tounicode() == s for every str s."
    source := "Doc/library/array.rst:291; invariant", status := .refuted
    prop := ``ArrayToUnicodeW, thm := some ``arrayToUnicodeW_refuted
    bug := some "sequences-array-w-tounicode-bom"
    notes := "A leading U+FEFF is dropped and surrogates raise, because byteorder 0 means detect. Reproduces on main." },
  { id := "sequences-array-tounicode-checked", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_tounicode_impl"]
    statement := "tounicode round-trips for w without surrogates or a leading U+FEFF, and for u for every str; other typecodes raise ValueError."
    source := "Doc/library/array.rst:291", status := .proven
    prop := ``ArrayToUnicodeChecked, thm := some ``arrayToUnicodeChecked_proven },
  { id := "sequences-array-w-fromunicode", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_fromunicode_impl"]
    statement := "a.fromunicode(s) appends the code points of s for every u or w array and every s."
    source := "Doc/library/array.rst:222; invariant: no internal error", status := .refuted
    prop := ``ArrayFromUnicode, thm := some ``arrayFromUnicode_refuted
    bug := some "sequences-array-w-fromunicode-empty"
    notes := "array('w').fromunicode('') raises SystemError. Reproduces on main." },
  { id := "sequences-array-fromunicode-checked", pyFile := "Modules/arraymodule.c"
    pyFns := ["array_array_fromunicode_impl"]
    statement := "a.fromunicode(s) appends for a u array, or a w array that has a buffer or receives at least one character; other typecodes raise ValueError."
    source := "Doc/library/array.rst:222", status := .proven
    prop := ``ArrayFromUnicodeChecked, thm := some ``arrayFromUnicodeChecked_proven },
  { id := "sequences-defdict-getitem", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["defdict_missing"]
    statement := "dd[key] gives a present value; a missing key raises KeyError(key) without a factory, keeps what a raising factory left, and otherwise stores and returns the factory's value, unless the factory stored the key itself."
    source := "Doc/library/collections.rst defaultdict.__missing__", status := .proven
    prop := ``DefDictGetitem, thm := some ``defDictGetitem_proven },
  { id := "sequences-defdict-copy-reduce", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["defdict_copy", "new_defdict", "defdict_reduce"]
    statement := "dd.copy() has the same items in order, type and factory; __reduce__ gives the items and the factory when callable."
    source := "invariant", status := .proven
    prop := ``DefDictCopyReduce, thm := some ``defDictCopyReduce_proven },
  { id := "sequences-defdict-repr-init-or", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["defdict_repr", "defdict_init", "defdict_or"]
    statement := "repr shows the factory, or None, or ... while printing it; __init__ refuses a non-callable and replaces the factory before dict.__init__ runs; | has the updated items and the defaultdict operand's type and factory, also with a frozendict operand, NotImplemented for anything else."
    source := "Doc/library/collections.rst defaultdict", status := .proven
    prop := ``DefDictReprInitOr, thm := some ``defDictReprInitOr_proven },
  { id := "sequences-count-agree", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["_collections__count_elements_impl"]
    statement := "On a real dict, the fast path, the slow path and the pure-Python twin of _count_elements end in the same state with the same outcome, for every __hash__ and __add__, provided 0 + 1 is 1."
    source := "Lib/collections/__init__.py:540-544 twin", status := .proven
    prop := ``CountAgree, thm := some ``countAgree_proven
    notes := "The theorem passes one hash outcome to all paths: the slow path's TypeError for an unhashable key is worded differently in CPython, which the difftest records." },
  { id := "sequences-count-elements", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["_collections__count_elements_impl"]
    statement := "With int counts, every key's count grows by its number of occurrences; a raising iterable keeps the counts reached; a non-iterable raises TypeError."
    source := "Doc/library/collections.rst Counter.update", status := .proven
    prop := ``CountElements, thm := some ``countElements_proven },
  { id := "sequences-tuplegetter", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["tuplegetter_new_impl", "tuplegetter_descr_get", "tuplegetter_descr_set",
      "tuplegetter_reduce", "tuplegetter_repr"]
    statement := "A tuplegetter reads item index of a tuple when 0 <= index < len, raises IndexError otherwise and TypeError for other objects, refuses assignment, is rebuilt by __reduce__, and refuses an index outside Py_ssize_t."
    source := "invariant", status := .proven
    prop := ``TupleGetterSpec, thm := some ``tupleGetterSpec_proven },
  { id := "sequences-deque-irepeat", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_inplace_repeat_lock_held", "deque_inplace_repeat", "deque_repeat"]
    statement := "For every deque and every int n in Py_ssize_t whose repeated result list(d)*n, cut to the last maxlen items, has at most sys.maxsize items (always for bounded deques), d *= n succeeds with exactly those items."
    source := "Doc/library/collections.rst:479-482, 599-600", status := .refuted
    prop := ``DequeIRepeat, thm := some ``dequeIRepeat_refuted
    bug := some "sequences-deque-imul-maxlen-memoryerror"
    notes := "deque([1, 2], maxlen=3) *= 2**62 raises MemoryError: the overflow guard precedes the maxlen reduction (the one-item fast path applies maxlen first)." },
  { id := "sequences-deque-irepeat-checked", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_inplace_repeat_lock_held", "deque_inplace_repeat", "deque_repeat"]
    statement := "For every deque with at most one item, or with len(d) * n <= sys.maxsize, d *= n (n in Py_ssize_t) holds the last maxlen items of list(d) * n, keeping the invariant and maxlen."
    source := "Doc/library/collections.rst:479-482, 599-600", status := .proven
    prop := ``DequeIRepeatChecked, thm := some ``dequeIRepeatChecked_proven
    notes := "Includes the ceil(maxlen / size) shortcut (periodicity of the repeated list) and the single-item block-filling path." },
  { id := "sequences-list-repeat", pyFile := "Objects/listobject.c"
    pyFns := ["list_inplace_repeat_lock_held", "list_repeat_lock_held"]
    statement := "For every list (len <= sys.maxsize) and int n: l *= n and l * n agree; outside Py_ssize_t both raise OverflowError; n <= 0 gives []; otherwise l repeated n times, with MemoryError exactly when that exceeds sys.maxsize items."
    source := "Doc/builtins/stdtypes.rst:1539-1552 note (2)", status := .proven
    prop := ``ListRepeat, thm := some ``listRepeat_proven },
  { id := "sequences-deque-copy-concat", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_copy_impl", "deque___copy___impl", "deque_concat_lock_held", "deque_concat"]
    statement := "For every deque d, of any subclass and maxlen, and deque other: d.copy() has the same items and maxlen; d + other holds the last d.maxlen items of list(d) + list(other) with d's maxlen."
    source := "Doc/library/collections.rst:507-511, 599-600", status := .proven
    prop := ``DequeCopyConcat, thm := some ``dequeCopyConcat_proven
    notes := "Refuted on 3.14.7, where a subclass's maxlen went through the format \"Oi\"; 3.15 uses \"On\"." },
  { id := "sequences-deque-copy-concat-checked", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_copy_impl", "deque___copy___impl", "deque_concat_lock_held", "deque_concat"]
    statement := "For every deque d and deque other, with d an exact deque or its maxlen inside a C int (or unbounded): d.copy() has the same items and maxlen; d + other holds the last d.maxlen items of list(d) + list(other) with d's maxlen; results keep the invariant."
    source := "Doc/library/collections.rst:507-511, 599-600", status := .proven
    prop := ``DequeCopyConcatChecked, thm := some ``dequeCopyConcatChecked_proven
    notes := "The narrowing the 3.14.7 format needed; sequences-deque-copy-concat now covers it." },
  { id := "sequences-deque-reverse", pyFile := "Modules/_collectionsmodule.c"
    pyFns := ["deque_reverse_impl"]
    statement := "For every deque with the layout invariant, reverse() swaps through the left and right block cursors len // 2 times, touching only used slots, and leaves exactly the reversed items with the layout and maxlen unchanged."
    source := "Doc/library/collections.rst:571-575", status := .proven
    prop := ``DequeReverse, thm := some ``dequeReverse_proven }
]

end PyLean.Sequences
