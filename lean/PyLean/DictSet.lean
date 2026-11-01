import PyLean.Registry
import PyLean.DictSet.Diff
import PyLean.DictSet.Props2
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
    pyFns := ["lookdict_index", "find_empty_slot", "build_indices_generic", "build_indices_unicode"]
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
      "is_unusable_slot", "insertion_resize", "dictresize", "build_indices_generic",
      "build_indices_unicode", "new_keys_object", "set_keys", "dict_unhashable_type"]
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
    pyFns := ["PyDict_Contains", "_PyDict_Contains_KnownHash"]
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
    pyFns := ["dictreviter_iter_lock_held", "dictiter_len", "dict___reversed___impl", "dictiter_new"]
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
    pyFns := ["set_clear_internal", "set_empty_to_minsize"]
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
