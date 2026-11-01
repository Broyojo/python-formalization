import PyLean.Registry
import PyLean.DictSet.Diff
import PyLean.DictSet.Props4
import PyLean.DictSet.SetProps
import PyLean.DictSet.Findings

/-!
`Objects/dictobject.c`, `Objects/setobject.c`, `Objects/odictobject.c`, CPython 3.14.7.

The dict table is modelled generically: keys are any type with a `Proto`, and the table theorems
hold for every protocol that keeps the `__hash__`/`__eq__` contract (`Honest`). The difftest
instantiates the same definitions with ints, strs, floats, NaNs, str subclasses, objects with a
chosen hash, and objects whose `__eq__` raises or mutates the container.
-/

namespace PyLean.DictSet

open PyLean.Registry

def entries : List Entry := [
  { id := "dict-lcg-full-period", pyFile := "Objects/dictobject.c", pyFns := ["do_lookup"]
    statement := "For all n, x, y, repeating j -> 5*j + 1 from x reaches y mod 2**n within 2**n steps."
    source := "dictobject.c:323-325, cited there as folklore", status := .proven
    prop := ``LcgFullPeriod, thm := some ``lcgFullPeriod_proven
    notes := "Proved from scratch, without Mathlib: 2**n steps add 2**n times an odd number." },
  { id := "dict-probe-reaches-all", pyFile := "Objects/dictobject.c",
    pyFns := ["lookdict_index", "find_empty_slot", "build_indices_unicode"]
    statement := "For every table of 2**n slots, every 64-bit hash and every slot s, the probe sequence reaches s within 2**n + 13 steps."
    source := "dictobject.c:354-358", status := .proven
    prop := ``ProbeReachesAll, thm := some ``probeReachesAll_proven },
  { id := "dict-usable-fraction", pyFile := "Objects/dictobject.c", pyFns := ["new_keys_object"]
    statement := "0 < USABLE_FRACTION(n) < n for every n >= 2."
    source := "dictobject.c:537-538", status := .proven
    prop := ``UsableFractionBounds, thm := some ``usableFractionBounds_proven },
  { id := "dict-keysize-room", pyFile := "Objects/dictobject.c", pyFns := ["calculate_log2_keysize"]
    statement := "calculate_log2_keysize(m) gives a table of at least max(m, 8) slots."
    source := "dictobject.c:545", status := .proven
    prop := ``Log2KeysizeRoom, thm := some ``log2KeysizeRoom_proven },
  { id := "dict-estimate-room", pyFile := "Objects/dictobject.c", pyFns := ["estimate_log2_keysize"]
    statement := "estimate_log2_keysize(n) gives a table with room for n entries without resizing."
    source := "dictobject.c:568-572", status := .proven
    prop := ``EstimateRoom, thm := some ``estimateRoom_proven },
  { id := "dict-index-width", pyFile := "Objects/dictobject.c",
    pyFns := ["dictkeys_get_index", "dictkeys_set_index"]
    statement := "Every entry index of a table of 2**n slots fits the int8, int16 or int32 slot chosen for n."
    source := "asserts at dictobject.c:513, :517, :526", status := .proven
    prop := ``IndexWidthFits, thm := some ``indexWidthFits_proven },
  { id := "dict-growth-room", pyFile := "Objects/dictobject.c", pyFns := ["insertion_resize"]
    statement := "After a resize to GROWTH_RATE(used), the table has room for at least one more entry."
    source := "dictobject.c:580-590; assert at :1827", status := .proven
    prop := ``GrowthRoom, thm := some ``growthRoom_proven },
  { id := "dict-lookup-found", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "do_lookup", "compare_generic", "compare_unicode_generic",
      "compare_unicode_unicode", "unicodekeys_lookup_generic", "dictkeys_generic_lookup",
      "unicode_get_hash"]
    statement := "For every key type keeping the hash/eq contract and every well-formed combined table, lookup of a key equal to a live entry's key stops, returns that entry and its value, runs no restart and leaves the dict unchanged."
    source := "invariant: dictobject.c:1232-1246", status := .proven
    prop := ``LookupFound, thm := some ``lookupFound_proven },
  { id := "dict-lookup-missing", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "do_lookup", "compare_generic", "compare_unicode_generic",
      "compare_unicode_unicode"]
    statement := "For every such key type and table, lookup of a key equal to no live entry stops at an empty slot and returns DKIX_EMPTY. The table always has an empty slot, so the loop terminates at every load the table can reach."
    source := "dictobject.c:145-150, :357-358", status := .proven
    prop := ``LookupMissing, thm := some ``lookupMissing_proven },
  { id := "dict-lookup-assoc", pyFile := "Objects/dictobject.c", pyFns := ["_Py_dict_lookup"]
    statement := "Lookup on a well-formed dict returns exactly what the association list holds for that key."
    source := "language: dict maps keys to values", status := .proven
    prop := ``LookupAssoc, thm := some ``lookupAssoc_proven },
  { id := "dict-setitem-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["setitem_take2_lock_held", "PyDict_SetItem", "_PyDict_SetItem_Take2", "setitem_lock_held",
      "insertdict", "insert_to_emptydict", "insert_combined_dict", "find_empty_slot",
      "is_unusable_slot", "insertion_resize", "dictresize",
      "build_indices_unicode", "new_keys_object", "set_keys"]
    statement := "d[key] = v on any well-formed combined dict either raises MemoryError and changes nothing, or keeps the table well formed and does to the association list what assocSet does: overwrite in place, or append."
    source := "language: dicts preserve insertion order; invariant", status := .proven
    prop := ``SetItemRefines, thm := some ``setItemRefines_proven
    notes := "MemoryError is in the statement rather than assumed away: it is the only failure. Split tables are not covered here." },
  { id := "dict-insertion-order", pyFile := "Objects/dictobject.c", pyFns := ["insert_combined_dict"]
    statement := "A key not in the list goes at the end, and every earlier pair stays in place."
    source := "Doc/library/stdtypes.rst: dictionaries preserve insertion order", status := .proven
    prop := ``InsertionOrder, thm := some ``insertionOrder_proven },
  { id := "dict-overwrite-order", pyFile := "Objects/dictobject.c", pyFns := ["insertdict"]
    statement := "Updating an existing key does not change the order of keys."
    source := "Doc/library/stdtypes.rst: updating a key does not affect the order", status := .proven
    prop := ``OverwriteKeepsOrder, thm := some ``overwriteKeepsOrder_proven },
  { id := "dict-delitem-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_DelItem", "_PyDict_DelItem_KnownHash_LockHeld", "_PyDict_DelItem_KnownHash",
      "delitem_common", "lookdict_index"]
    statement := "del d[key] on a well-formed dict removes exactly that pair and keeps the table well formed; a missing key raises KeyError and changes nothing."
    source := "language; invariant: Dummy slots at dictobject.c:78-83", status := .proven
    prop := ``DelItemRefines, thm := some ``delItemRefines_proven },
  { id := "dict-popitem-lifo", pyFile := "Objects/dictobject.c", pyFns := ["dict_popitem_impl"]
    statement := "popitem on a well-formed non-empty dict removes and returns the last pair of the association list, keeping the table well formed; on an empty dict it raises KeyError."
    source := "dict.popitem docstring, dictobject.c:4590-4593", status := .proven
    prop := ``PopitemLifo, thm := some ``popitemLifo_proven },
  { id := "dict-iteration-order", pyFile := "Objects/dictobject.c",
    pyFns := ["_PyDict_Next", "PyDict_Next", "keys_lock_held", "PyDict_Keys", "values_lock_held",
      "PyDict_Values", "items_lock_held", "PyDict_Items"]
    statement := "A full walk with _PyDict_Next, which is what keys(), values() and items() lists are, yields the live entries in dk_entries order."
    source := "Doc/library/stdtypes.rst: iteration order is insertion order", status := .proven
    prop := ``IterationOrder, thm := some ``iterationOrder_proven },
  { id := "dict-get", pyFile := "Objects/dictobject.c", pyFns := ["dict_get_impl"]
    statement := "d.get(key, default) on a well-formed dict is the list lookup or default, and changes nothing."
    source := "dict.get docstring", status := .proven
    prop := ``DictGetSpec, thm := some ``dictGetSpec_proven },
  { id := "dict-model-equals-assoc", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_SetItem", "PyDict_DelItem"]
    statement := "Over every program of d[k] = v and del d[k] from any well-formed dict, the dict and the association list end equal, unless MemoryError stopped the run."
    source := "task: the model equals an abstract association list", status := .proven
    prop := ``ModelEqualsAssoc, thm := some ``modelEqualsAssoc_proven },
  { id := "dict-read-family", pyFile := "Objects/dictobject.c",
    pyFns := ["dict_getitem", "PyDict_GetItem", "_PyDict_GetItem_KnownHash",
      "_PyDict_GetItemRef_KnownHash_LockHeld", "_PyDict_GetItemRef_KnownHash", "PyDict_GetItemRef",
      "_PyDict_GetItemRef_Unicode_LockHeld", "PyDict_GetItemWithError", "_PyDict_GetItemWithError"]
    statement := "Each C API read returns what the association list holds for the key and leaves the dict unchanged."
    source := "Doc/c-api/dict.rst", status := .proven
    prop := ``ReadFamily, thm := some ``readFamily_proven },
  { id := "dict-contains", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_Contains", "_PyDict_Contains_KnownHash", "dict___contains___impl"]
    statement := "key in d is true exactly when the association list holds the key; the dict is unchanged."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``ContainsSpec, thm := some ``containsSpec_proven },
  { id := "dict-subscript", pyFile := "Objects/dictobject.c", pyFns := ["dict_subscript"]
    statement := "d[key] on an exact dict returns the list's value, or raises KeyError(key) if absent."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``SubscriptSpec, thm := some ``subscriptSpec_proven },
  { id := "dict-pop", pyFile := "Objects/dictobject.c",
    pyFns := ["pop_lock_held", "PyDict_Pop", "_PyDict_Pop_KnownHash"]
    statement := "PyDict_Pop on a well-formed dict removes and returns the list's value, keeping the table well formed; an absent key changes nothing."
    source := "dict.pop docstring", status := .proven
    prop := ``PopSpec, thm := some ``popSpec_proven },
  { id := "dict-clear", pyFile := "Objects/dictobject.c",
    pyFns := ["clear_lock_held", "PyDict_Clear", "_PyDict_Clear_LockHeld", "dict_clear_impl"]
    statement := "d.clear() leaves a well-formed empty dict."
    source := "dict.clear docstring", status := .proven
    prop := ``ClearSpec, thm := some ``clearSpec_proven },
  { id := "dict-len", pyFile := "Objects/dictobject.c", pyFns := ["dict_length", "PyDict_Size"]
    statement := "ma_used is the length of the association list."
    source := "invariant: _PyDict_CheckConsistency", status := .proven
    prop := ``LenSpec, thm := some ``lenSpec_proven },
  { id := "dict-forward-iter-order", pyFile := "Objects/dictobject.c",
    pyFns := ["dictiter_new", "dictiter_iternextkey_lock_held", "dictiter_iternextkey",
      "dictiter_iternextvalue_lock_held", "dictiter_iternextvalue", "dictiter_iternextitem_lock_held",
      "dictiter_iternextitem", "dict_iter", "dictiter_len"]
    statement := "A forward key, value or item iterator over an unchanged dict yields the list in order, whatever deletions left holes in the table, and stops."
    source := "Doc/library/stdtypes.rst: iteration order", status := .proven
    prop := ``ForwardIterOrder, thm := some ``forwardIterOrder_proven
    notes := "Hypothesis d.used < 2**63 is the type invariant of Py_ssize_t ma_used." },
  { id := "dict-pop-default", pyFile := "Objects/dictobject.c",
    pyFns := ["dict_pop_default", "_PyDict_Pop", "dict_pop_impl"]
    statement := "d.pop(key[, default]) returns and removes the list's value; if absent it returns default, or raises KeyError(key) when there is none, changing nothing."
    source := "dict.pop docstring, dictobject.c:4573-4576", status := .proven
    prop := ``PopDefaultSpec, thm := some ``popDefaultSpec_proven },
  { id := "dict-ass-sub", pyFile := "Objects/dictobject.c", pyFns := ["dict_ass_sub"]
    statement := "mp_ass_subscript deletes when the value is NULL and sets otherwise."
    source := "dictobject.c:3540-3547", status := .proven
    prop := ``AssSubDispatch, thm := some ``assSubDispatch_proven },
  { id := "dict-new-empty", pyFile := "Objects/dictobject.c", pyFns := ["PyDict_New", "dict_new", "new_dict"]
    statement := "A new dict is well formed and holds nothing."
    source := "invariant", status := .proven
    prop := ``NewDictEmpty, thm := some ``newDictEmpty_proven },
  { id := "dict-merge-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["dict_dict_merge", "dict_merge", "PyDict_Update", "PyDict_Merge", "_PyDict_MergeEx",
      "clone_combined_dict_keys", "dict_ior"]
    statement := "d.update(other) on well-formed distinct dicts is the fold of d[k] = v over other's items in order, whichever path runs: the clone into an empty dict, the single resize, or plain insertion. MemoryError is the only failure."
    source := "dict.update docstring", status := .proven
    prop := ``DictMergeRefines, thm := some ``dictMergeRefines_proven
    notes := "override == 1; the override 0 and 2 branches are not covered by this statement." },
  { id := "dict-merge-self", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "d.update(d) does nothing."
    source := "comment at dictobject.c:3898", status := .proven
    prop := ``DictMergeSelf, thm := some ``dictMergeSelf_proven },
  { id := "dict-merge-mapping", pyFile := "Objects/dictobject.c", pyFns := ["dict_merge"]
    statement := "With a mapping argument whose __getitem__ succeeds, update is d[k] = E[k] for k in E.keys(), in order."
    source := "dict.update docstring, dictobject.c:4806", status := .proven
    prop := ``MergeMappingRefines, thm := some ``mergeMappingRefines_proven },
  { id := "dict-merge-seq2", pyFile := "Objects/dictobject.c",
    pyFns := ["merge_from_seq2_lock_held", "PyDict_MergeFromSeq2"]
    statement := "With an iterable of pairs, update is d[k] = v for each pair, in order."
    source := "dict.update docstring, dictobject.c:4807", status := .proven
    prop := ``MergeSeq2Refines, thm := some ``mergeSeq2Refines_proven
    notes := "override == 1 and well-formed pairs. The error messages for bad elements are checked by the difftest, not stated here." },
  { id := "dict-update-arg-routes", pyFile := "Objects/dictobject.c", pyFns := ["dict_update_arg"]
    statement := "dict_update_arg sends an object with keys to dict_merge and one without to the sequence route."
    source := "dict.update docstring, dictobject.c:4805-4808", status := .proven
    prop := ``UpdateArgRoutes, thm := some ``updateArgRoutes_proven },
  { id := "dict-cstring-wrappers", pyFile := "Objects/dictobject.c",
    pyFns := ["_PyDict_GetItemIdWithError", "_PyDict_GetItemStringWithError", "PyDict_GetItemStringRef",
      "PyDict_ContainsString", "_PyDict_ContainsId", "_PyDict_SetItemId", "PyDict_SetItemString",
      "_PyDict_DelItemId", "PyDict_DelItemString"]
    statement := "The C-string entry points build the key, raise if that fails with the dict untouched, and otherwise behave as the key operation."
    source := "Doc/c-api/dict.rst", status := .proven
    prop := ``CKeyWrappers, thm := some ``cKeyWrappers_proven
    notes := "One model, withCKey, stands for all of them: their bodies differ only in which key operation they call. PyDict_SetItemString also interns the key, which has no effect on the dict's contents." },
  { id := "set-table-refines", pyFile := "Objects/setobject.c",
    pyFns := ["set_lookkey", "set_add_entry", "set_discard_entry", "set_contains_entry"]
    statement := "For every key type keeping the hash/eq contract, after any program of add and discard from an empty set, membership agrees with a list without duplicates."
    source := "language: set semantics", status := .open
    prop := ``SetTableRefines
    notes := "Not proved. Needs the Chain invariant restated over set_lookkey's nested linear-probe loops, the freeslot logic of set_add_entry_takeref, and set_table_resize. The behaviour is checked by the difftest, including exact slot order." },
  { id := "odict-twins-agree", pyFile := "Objects/odictobject.c",
    pyFns := ["_odict_get_index", "_odict_resize", "_odict_add_new_node", "_odict_remove_node"]
    statement := "For keys keeping the contract, the C and pure-Python OrderedDict hold the same keys in the same order after any program of __setitem__, __delitem__ and move_to_end."
    source := "odictobject.c:3-4: necessarily explicitly equivalent to the pure Python class", status := .open
    prop := ``OdictTwinsAgree
    notes := "Not proved. Needs an invariant tying od_fast_nodes to dk_entries across the deferred _odict_resize, and one for the link heap." },
  { id := "dict-view-len", pyFile := "Objects/dictobject.c",
    pyFns := ["dictview_len", "_PyDictView_New", "dict_keys_impl", "dict_items_impl", "dict_values_impl"]
    statement := "The length of any view of a well-formed dict is the length of the association list."
    source := "Doc/library/stdtypes.rst: dictionary view objects", status := .proven
    prop := ``ViewLen, thm := some ``viewLen_proven },
  { id := "dict-view-iter-order", pyFile := "Objects/dictobject.c",
    pyFns := ["dictkeys_iter", "dictitems_iter", "dictvalues_iter"]
    statement := "Iterating a view of an unchanged dict yields the association list in order."
    source := "Doc/library/stdtypes.rst: views iterate in insertion order", status := .proven
    prop := ``ViewIterOrder, thm := some ``viewIterOrder_proven },
  { id := "dict-keys-view-contains", pyFile := "Objects/dictobject.c", pyFns := ["dictkeys_contains"]
    statement := "x in d.keys() is x in d."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``KeysViewContains, thm := some ``keysViewContains_proven },
  { id := "odict-list-ends", pyFile := "Objects/odictobject.c", pyFns := ["_odict_add_head", "_odict_add_tail"]
    statement := "Adding a node at either end changes the list as named and increments od_state."
    source := "odictobject.c:500: incremented whenever the LL changes", status := .proven
    prop := ``OdictListEnds, thm := some ``odictListEnds_proven },
  { id := "odict-remove-node", pyFile := "Objects/odictobject.c", pyFns := ["_odict_remove_node"]
    statement := "Removing a node drops exactly that node and increments od_state."
    source := "odictobject.c:500", status := .proven
    prop := ``OdictRemoveNode, thm := some ``odictRemoveNode_proven },
  { id := "odict-clear-nodes", pyFile := "Objects/odictobject.c", pyFns := ["_odict_clear_nodes"]
    statement := "Clearing the nodes empties the list and od_fast_nodes, resets the sentinel and increments od_state."
    source := "odictobject.c:795-814", status := .proven
    prop := ``OdictClearNodes, thm := some ``odictClearNodes_proven },
  { id := "odict-iter-start", pyFile := "Objects/odictobject.c",
    pyFns := ["odictiter_new", "odict_iter", "odict_reversed", "odictkeys_iter", "odictkeys_reversed",
      "odictitems_iter", "odictitems_reversed", "odictvalues_iter", "odictvalues_reversed"]
    statement := "An OrderedDict iterator starts at the first or last node as asked, recording the current size and state."
    source := "odictobject.c:1942-1973", status := .proven
    prop := ``OdictIterStart, thm := some ``odictIterStart_proven
    notes := "Says where iteration starts, not how it proceeds; see odict-iter-bounded." },
  { id := "odict-new-empty", pyFile := "Objects/odictobject.c", pyFns := ["PyODict_New"]
    statement := "A new OrderedDict has no nodes and an empty dict."
    source := "invariant", status := .proven
    prop := ``OdictNewEmpty, thm := some ``odictNewEmpty_proven },
  { id := "dict-setdefault-no-crash", pyFile := "Objects/dictobject.c",
    pyFns := ["dict_setdefault_ref_lock_held", "dict_setdefault_impl", "PyDict_SetDefaultRef"]
    statement := "For every key type keeping the hash/eq contract, dict.setdefault on a fresh instance __dict__ never dereferences NULL."
    source := "invariant: no crash", status := .refuted
    prop := ``SetdefaultNoCrash, thm := some ``setdefaultNoCrash_refuted
    bug := some "dictset-setdefault-split-null"
    notes := "A str-subclass key equal to a shared key this dict has no value for. SIGSEGV from pure Python." },
  { id := "odict-no-stale-node", pyFile := "Objects/odictobject.c",
    pyFns := ["_odict_popkey_hash", "OrderedDict_popitem_impl", "_odict_get_index_raw", "_odict_find_node_hash"]
    statement := "After any program of od[k] = v and dict.popitem(od), od.popitem() does not dereference NULL and iteration yields no more items than the list has nodes."
    source := "invariant: no crash, no hang", status := .refuted
    prop := ``OdictNoStaleNode, thm := some ``odictNoStaleNode_refuted
    bug := some "dictset-odict-stale-fast-nodes" },
  { id := "odict-iter-bounded", pyFile := "Objects/odictobject.c",
    pyFns := ["odictiter_nextkey_lock_held", "odictiter_iternext_lock_held", "_odict_find_node"]
    statement := "After any such program, iteration over an OrderedDict yields no more items than the list has nodes."
    source := "invariant: no hang", status := .refuted
    prop := ``OdictIterBounded, thm := some ``odictIterBounded_refuted
    bug := some "dictset-odict-stale-fast-nodes" },
  { id := "dict-reviter-len", pyFile := "Objects/dictobject.c",
    pyFns := ["dictreviter_iter_lock_held", "dictreviter_iternext", "dictiter_len", "dict___reversed___impl", "dictiter_new"]
    statement := "After any program of sets, deletes and next() on a reverse dict iterator, __length_hint__ fits Py_ssize_t."
    source := "invariant; forward iterator check at dictobject.c:5279", status := .refuted
    prop := ``RevIterLenNonneg, thm := some ``revIterLenNonneg_refuted
    bug := some "dictset-reversed-iter-length-hint"
    notes := "Known upstream as gh-158254, fixed on main; 3.14.7 still has it." },
  { id := "set-frozenset-hash-order-free", pyFile := "Objects/setobject.c",
    pyFns := ["frozenset_hash_impl", "_shuffle_bits"]
    statement := "Two tables whose slots are a permutation of each other, with the same mask, fill and used, have the same frozenset hash."
    source := "setobject.c:785-793: a frozenset hash should be independent of order", status := .proven
    prop := ``FrozensetHashOrderFree, thm := some ``frozensetHashOrderFree_proven },
  { id := "set-frozenset-hash-not-minus-one", pyFile := "Objects/setobject.c",
    pyFns := ["frozenset_hash_impl", "frozenset_hash"]
    statement := "The frozenset hash is never -1, the error value of tp_hash."
    source := "setobject.c:813-815", status := .proven
    prop := ``FrozensetHashNotMinusOne, thm := some ``frozensetHashNotMinusOne_proven },
  { id := "set-new-size-minimal", pyFile := "Objects/setobject.c", pyFns := ["set_table_resize"]
    statement := "For minused < 2**63, set_table_resize asks for the smallest table of at least 8 slots above minused."
    source := "setobject.c:311: Find the smallest table size > minused", status := .proven
    prop := ``SetNewSizeMinimal, thm := some ``setNewSizeMinimal_proven
    notes := "Hypothesis: minused is a Py_ssize_t; line 315 notes the largest size is PY_SSIZE_T_MAX + 1." },
  { id := "set-clear-empties", pyFile := "Objects/setobject.c",
    pyFns := ["set_clear_internal", "set_empty_to_minsize", "set_clear_impl", "_PySet_ClearInternal", "PySet_Clear"]
    statement := "After clearing, the table holds no entries, and used is 0 unless the set was already empty."
    source := "set.clear docstring", status := .proven
    prop := ``SetClearEmpties, thm := some ``setClearEmpties_proven },
  { id := "set-iter-len", pyFile := "Objects/setobject.c",
    pyFns := ["setiter_iternext", "setiter_len", "set_iter"]
    statement := "After any program of add, discard and next() on a set iterator, __length_hint__ is not negative."
    source := "PEP 424; PyObject_LengthHint rejects a negative hint", status := .refuted
    prop := ``SetIterLenNonneg, thm := some ``setIterLenNonneg_refuted
    bug := some "dictset-setiter-negative-length-hint" }
]

end PyLean.DictSet
