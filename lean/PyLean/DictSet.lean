import PyLean.Registry
import PyLean.DictSet.Diff
import PyLean.DictSet.Props4
import PyLean.DictSet.Failure
import PyLean.DictSet.Readers
import PyLean.DictSet.Mutation
import PyLean.DictSet.Merge
import PyLean.DictSet.Split
import PyLean.DictSet.Reentrant
import PyLean.DictSet.SetProps
import PyLean.DictSet.SetRefine
import PyLean.DictSet.Findings
import PyLean.DictSet.Body
import PyLean.DictSet.Iter

/-!
`Objects/dictobject.c`, `Objects/setobject.c`, `Objects/odictobject.c`, CPython 3.15.2.

The dict table is modelled generically: keys are any type with a `Proto`, and the table theorems
hold for every protocol that keeps the `__hash__`/`__eq__` contract (`Honest`). The difftest
instantiates the same definitions with ints, strs, floats, NaNs, str subclasses, objects with a
chosen hash, and objects whose `__eq__` raises or mutates the container.
-/

namespace PyLean.DictSet

open PyLean.Registry

def entries : List Entry := [
  { id := "dict-lcg-full-period", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "For all n, x, y, repeating j -> 5*j + 1 from x reaches y mod 2**n within 2**n steps."
    source := "dictobject.c:363-365, cited there as folklore", status := .proven
    prop := ``LcgFullPeriod, thm := some ``lcgFullPeriod_proven
    notes := "Proved from scratch, without Mathlib: 2**n steps add 2**n times an odd number." },
  { id := "dict-probe-reaches-all", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "For every table of 2**n slots, every 64-bit hash and every slot s, the probe sequence reaches s within 2**n + 13 steps."
    source := "dictobject.c:394-398", status := .proven
    prop := ``ProbeReachesAll, thm := some ``probeReachesAll_proven },
  { id := "dict-usable-fraction", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "0 < USABLE_FRACTION(n) < n for every n >= 2."
    source := "dictobject.c:575-576", status := .proven
    prop := ``UsableFractionBounds, thm := some ``usableFractionBounds_proven },
  { id := "dict-keysize-room", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "calculate_log2_keysize(m) gives a table of at least max(m, 8) slots."
    source := "dictobject.c:583", status := .proven
    prop := ``Log2KeysizeRoom, thm := some ``log2KeysizeRoom_proven },
  { id := "dict-estimate-room", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "estimate_log2_keysize(n) gives a table with room for n entries without resizing."
    source := "dictobject.c:606-610", status := .proven
    prop := ``EstimateRoom, thm := some ``estimateRoom_proven },
  { id := "dict-index-width", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "Every entry index of a table of 2**n slots fits the int8, int16 or int32 slot chosen for n."
    source := "asserts at dictobject.c:551, :555, :564", status := .proven
    prop := ``IndexWidthFits, thm := some ``indexWidthFits_proven },
  { id := "dict-growth-room", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "After a resize to GROWTH_RATE(used), the table has room for at least one more entry."
    source := "dictobject.c:618-628; assert at :1907", status := .proven
    prop := ``GrowthRoom, thm := some ``growthRoom_proven },
  { id := "dict-lookup-found", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "do_lookup", "compare_generic", "compare_unicode_generic", "compare_unicode_unicode", "unicodekeys_lookup_generic", "dictkeys_generic_lookup"]
    statement := "For every key type keeping the hash/eq contract and every well-formed combined table, lookup of a key equal to a live entry's key stops, returns that entry and its value, runs no restart and leaves the dict unchanged."
    source := "invariant: dictobject.c:1312-1326", status := .proven
    prop := ``LookupFound, thm := some ``lookupFound_proven },
  { id := "dict-lookup-missing", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "do_lookup", "compare_generic", "compare_unicode_generic", "compare_unicode_unicode"]
    statement := "For every such key type and table, lookup of a key equal to no live entry stops at an empty slot and returns DKIX_EMPTY. The table always has an empty slot, so the loop terminates at every load the table can reach."
    source := "dictobject.c:156-161, :397-398", status := .proven
    prop := ``LookupMissing, thm := some ``lookupMissing_proven },
  { id := "dict-lookup-assoc", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "Lookup on a well-formed dict returns exactly what the association list holds for that key."
    source := "language: dict maps keys to values", status := .proven
    prop := ``LookupAssoc, thm := some ``lookupAssoc_proven },
  { id := "dict-setitem-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["setitem_take2_lock_held", "setitem_take2_lock_held_known_hash", "insertdict", "replace_value", "insert_to_emptydict", "insert_combined_dict", "find_empty_slot", "is_unusable_slot", "insertion_resize", "build_indices_unicode", "new_keys_object"]
    statement := "d[key] = v on any well-formed combined dict keeps the table well formed and does to the association list what assocSet does, overwrite in place or append, unless the table would need 2**64 slots, when it raises MemoryError and changes nothing."
    source := "language: dicts preserve insertion order; invariant", status := .proven
    prop := ``SetItemRefines, thm := some ``setItemRefines_proven
    notes := "MemoryError is the only failure, and only at log2 size 64: TooBig is calculate_log2_keysize(GROWTH_RATE(d)) >= 64, as dictresize tests it at :2073. Split tables are in dict-split-refines." },
  { id := "dict-insertion-order", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A key not in the list goes at the end, and every earlier pair stays in place."
    source := "Doc/library/stdtypes.rst: dictionaries preserve insertion order", status := .proven
    prop := ``InsertionOrder, thm := some ``insertionOrder_proven },
  { id := "dict-overwrite-order", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "Updating an existing key does not change the order of keys."
    source := "Doc/library/stdtypes.rst: updating a key does not affect the order", status := .proven
    prop := ``OverwriteKeepsOrder, thm := some ``overwriteKeepsOrder_proven },
  { id := "dict-delitem-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_DelItem", "delitem_common", "_PyDict_DelItem_KnownHash_LockHeld", "lookdict_index"]
    statement := "del d[key] on a well-formed dict removes exactly that pair and keeps the table well formed; a missing key raises KeyError and changes nothing."
    source := "language; invariant: Dummy slots at dictobject.c:78-83", status := .proven
    prop := ``DelItemRefines, thm := some ``delItemRefines_proven },
  { id := "dict-popitem-lifo", pyFile := "Objects/dictobject.c", pyFns := ["dict_popitem_impl"]
    statement := "popitem on a well-formed non-empty dict removes and returns the last pair of the association list, keeping the table well formed; on an empty dict it raises KeyError."
    source := "dict.popitem docstring, dictobject.c:4957-4960", status := .proven
    prop := ``PopitemLifo, thm := some ``popitemLifo_proven },
  { id := "dict-iteration-order", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "A full walk with _PyDict_Next, which is what keys(), values() and items() lists are, yields the live entries in dk_entries order."
    source := "Doc/library/stdtypes.rst: iteration order is insertion order", status := .proven
    prop := ``IterationOrder, thm := some ``iterationOrder_proven },
  { id := "dict-get", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "d.get(key, default) on a well-formed dict is the list lookup or default, and changes nothing."
    source := "dict.get docstring", status := .proven
    prop := ``DictGetSpec, thm := some ``dictGetSpec_proven },
  { id := "dict-model-equals-assoc", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "Over every program of d[k] = v and del d[k] from any well-formed dict, the dict and the association list end equal, unless MemoryError stopped the run."
    source := "task: the model equals an abstract association list", status := .proven
    prop := ``ModelEqualsAssoc, thm := some ``modelEqualsAssoc_proven },
  { id := "dict-read-family", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "Each C API read returns what the association list holds for the key and leaves the dict unchanged."
    source := "Doc/c-api/dict.rst", status := .proven
    prop := ``ReadFamily, thm := some ``readFamily_proven },
  { id := "dict-lookup-no-mutate", pyFile := "Objects/dictobject.c",
    pyFns := ["do_lookup", "compare_generic", "compare_unicode_generic", "dictkeys_generic_lookup",
      "unicodekeys_lookup_generic"]
    statement := "If __eq__ never mutates the dict (a lying comparison that returns arbitrary booleans but leaves the object alone), then _Py_dict_lookup leaves the table byte-identical, whatever it answers, so Chain/WF/DictInv all survive. The only route by which lookup can change the table is a genuinely mutating __eq__."
    source := "dictobject.c:1081-1213; the dk re-read and DKIX_KEY_CHANGED checks at 1142, 1198", status := .proven
    prop := ``InvUnderLyingEq, thm := some ``invUnderLyingEq_proven },
  { id := "dict-readers-faithful", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_GetItemRef", "_PyDict_GetItemRef_KnownHash", "PyDict_GetItemWithError", "PyDict_Contains", "_PyDict_Contains_KnownHash", "_PyDict_Subscript", "_PyDict_SubscriptKnownHash", "dict_contains", "dict_get_impl"]
    statement := "For every key protocol, including a hash or __eq__ that raises or mutates the dict, each reader is faithful to _Py_dict_lookup: a raising hash or lookup propagates with the state the lookup left, a slot with ix >= 0 but no value (a split key this dict lacks) reads as absent and is never dereferenced, and a slot with a value gives that value."
    source := "dictobject.c:2520-2609, 2637, 5234-5292, 3755-3794, 4749-4769; the ix>=0,value==NULL note at 2025-2032", status := .proven
    prop := ``ReadersFaithful, thm := some ``readersFaithful_proven },
  { id := "dict-contains", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "key in d is true exactly when the association list holds the key; the dict is unchanged."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``ContainsSpec, thm := some ``containsSpec_proven },
  { id := "dict-subscript", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "d[key] on an exact dict returns the list's value, or raises KeyError(key) if absent."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``SubscriptSpec, thm := some ``subscriptSpec_proven },
  { id := "dict-pop", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "PyDict_Pop on a well-formed dict removes and returns the list's value, keeping the table well formed; an absent key changes nothing."
    source := "dict.pop docstring", status := .proven
    prop := ``PopSpec, thm := some ``popSpec_proven },
  { id := "dict-clear", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "d.clear() leaves a well-formed empty dict."
    source := "dict.clear docstring", status := .proven
    prop := ``ClearSpec, thm := some ``clearSpec_proven },
  { id := "dict-len", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "ma_used is the length of the association list."
    source := "invariant: _PyDict_CheckConsistency", status := .proven
    prop := ``LenSpec, thm := some ``lenSpec_proven },
  { id := "dict-iter-order", pyFile := "Objects/dictobject.c",
    pyFns := ["dictiter_new", "dict_iter", "dict___reversed___impl",
      "dictiter_iternextkey_lock_held", "dictiter_iternextkey",
      "dictiter_iternextvalue_lock_held", "dictiter_iternextvalue",
      "dictiter_iternextitem_lock_held", "dictiter_iternextitem",
      "dictreviter_iter_lock_held", "dictreviter_iternext"]
    statement := "On a well-formed dict of either table form, a new forward key, value or item iterator lists the association list in order and a reverse one lists it reversed, whatever deletions left holes in the table; each flavour hands back what it says."
    source := "Doc/library/stdtypes.rst: iteration order; dictobject.c:5575-5614", status := .proven
    prop := ``DictIterOrder, thm := some ``dictIterOrder_proven
    notes := "ma_used < 2**63 is derived from the table invariants, not assumed." },
  { id := "dict-iter-failure", pyFile := "Objects/dictobject.c",
    pyFns := ["dictiter_iternextkey_lock_held", "dictiter_iternextvalue_lock_held",
      "dictiter_iternextitem_lock_held", "dictreviter_iter_lock_held"]
    statement := "For any iterator state and any dict: an exhausted iterator stays exhausted; a changed size raises and stays raised; and an iterator of either direction that finds an entry when its count is spent raises and dies, in either table form, and otherwise hands the entry back."
    source := "dictobject.c:5681-5686, :5722-5726, :6225-6230", status := .proven
    prop := ``DictIterFailure, thm := some ``dictIterFailure_proven
    notes := "The reverse test is the one 3.14.7 lacked (gh-158254); dict-reviter-len is what it gives." },
  { id := "dict-pop-default", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "d.pop(key[, default]) returns and removes the list's value; if absent it returns default, or raises KeyError(key) when there is none, changing nothing."
    source := "dict.pop docstring, dictobject.c:4940-4943", status := .proven
    prop := ``PopDefaultSpec, thm := some ``popDefaultSpec_proven },
  { id := "dict-ass-sub", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "mp_ass_subscript deletes when the value is NULL and sets otherwise."
    source := "dictobject.c:3796-3803", status := .proven
    prop := ``AssSubDispatch, thm := some ``assSubDispatch_proven },
  { id := "dict-new-empty", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A new dict is well formed and holds nothing."
    source := "invariant", status := .proven
    prop := ``NewDictEmpty, thm := some ``newDictEmpty_proven },
  { id := "dict-split-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "dictresize", "insertdict", "insert_split_key", "_PyDict_InsertSplitValue", "replace_value",
      "delitem_common", "delete_index_from_values", "dict_popitem_impl", "clear_lock_held",
      "clear_embedded_values"]
    statement := "On a well-formed split dict, for a key of any kind: the lookup agrees with the list, in which a shared key with no value is absent; d[key] = v keeps the table well formed, split or combined, and does what assocSet does, up to the object of a key equal to a shared one, unless the table would need 2**64 slots; del, popitem and clear do what the list does; a full iteration gives the list in insertion order."
    source := "task: the model equals an abstract association list; dictobject.c:1327-1391, 1911-1963, 2000-2049, 2155-2305, 2864-2923, 3065-3124, 4963-5045", status := .proven
    prop := ``SplitRefines, thm := some ``splitRefines_proven
    notes := "The combined half of these rows is in dict-lookup-*, dict-setitem-refines, dict-delitem-refines, dict-popitem-lifo and dict-clear; their failure paths are in dict-lookup-control and dict-insert-failure." },
  { id := "dict-split-fresh", pyFile := "Objects/dictobject.c", pyFns := ["new_dict_with_shared_keys"]
    statement := "new_dict_with_shared_keys on any well-formed shared keys gives a well-formed split dict of no items, with shared_keys_usable_size value slots all NULL; and the keys a class builds from any attribute list are such keys, so dict-split-refines is not vacuous."
    source := "dictobject.c:971-984, :7232-7258", status := .proven
    prop := ``SplitFresh, thm := some ``splitFresh_proven },
  { id := "dict-split-del-keeps-key", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "del d[key] on a split dict leaves the key in the shared keys with no value in this dict: the state dict.setdefault fails on is reached by ordinary operations and satisfies the invariant."
    source := "dictobject.c:2894-2899", status := .proven
    prop := ``SplitDelKeepsKey, thm := some ``splitDelKeepsKey_proven },
  { id := "dict-lookup-control", pyFile := "Objects/dictobject.c", pyFns := ["_Py_dict_lookup"]
    statement := "After the scan of _Py_dict_lookup, in every dispatch branch and for every key protocol: an exception is the result, in the state __eq__ left, and DKIX_KEY_CHANGED restarts on that state."
    source := "dictobject.c:1341-1381", status := .proven
    prop := ``LookupControl, thm := some ``lookupControl_proven },
  { id := "dict-insert-failure", pyFile := "Objects/dictobject.c", pyFns := ["insertdict", "dictresize"]
    statement := "If the lookup in insertdict raises, the exception is the result; dictresize refuses a size of 64 bits or more with MemoryError and changes nothing."
    source := "dictobject.c:2019-2023, 2045-2048, 2155-2305", status := .proven
    prop := ``InsertFailure, thm := some ``insertFailure_proven },
  { id := "dict-lookup-index-valid", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "do_lookup", "compare_generic", "compare_unicode_generic"]
    statement := "For every key protocol, including an __eq__ that lies, raises or changes the dict in any way, an index _Py_dict_lookup reports is one the table has when it returns."
    source := "dictobject.c:1142, 1198: dk == mp->ma_keys && ep->me_key == startkey", status := .proven
    prop := ``LookupIndexValid, thm := some ``lookupIndexValid_proven },
  { id := "dict-struct-survives", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "If every comparison keeps the chains and counts of a combined table, whatever it answers and whether or not it raises, then _Py_dict_lookup, insertdict and _PyDict_DelItem_KnownHash keep them, on all their outcomes. Key uniqueness is not claimed: a lying __eq__ can break it."
    source := "invariant: _PyDict_CheckConsistency", status := .proven
    prop := ``StructSurvives, thm := some ``structSurvives_proven
    notes := "Combined tables only; the split case is not proved." },
  { id := "dict-struct-hyp-met", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "An __eq__ that clears the dict it is probing meets the hypothesis of dict-struct-survives."
    source := "dictobject.c:3080-3124", status := .proven
    prop := ``StructHypMet, thm := some ``structHypMet_proven },
  { id := "dict-merge-guard", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "For every key protocol and every override: an error from the loop body is raised as it stands, even if the source changed; otherwise a changed number of items in the source raises RuntimeError('dict mutated during update'), in the state the callback left; otherwise the loop goes on from the source as it now stands."
    source := "dictobject.c:4223-4254", status := .proven
    prop := ``MergeGuard, thm := some ``mergeGuard_proven },
  { id := "dict-merge-quiet", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "If no callback touches the source, then whatever __eq__ answers or does to the receiver, the merge loop runs over the items the source had at the start and the size test never fires."
    source := "dictobject.c:4218-4254", status := .proven
    prop := ``MergeQuiet, thm := some ``mergeQuiet_proven },
  { id := "dict-merge-guard-reachable", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A key whose __eq__ clears the source makes d.update(source) raise RuntimeError('dict mutated during update')."
    source := "dictobject.c:4249-4253; the test reproduces it on CPython", status := .proven
    prop := ``MergeGuardReachable, thm := some ``mergeGuardReachable_proven },
  { id := "dict-merge-same-size-unseen", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A callback that replaces an item of the source and keeps the count is not seen: the merge succeeds, and a key the source held at the start is missing from the receiver."
    source := "dictobject.c:4249 compares only ma_used; checked on 3.15.2 and main", status := .proven
    prop := ``MergeSameSizeUnseen, thm := some ``mergeSameSizeUnseen_proven
    notes := "Behaviour on record, not a bug report: the forward dict iterator goes on past the same change." },
  { id := "dict-merge-empty-target", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "On an empty receiver every override value behaves as override == 1."
    source := "dictobject.c:4178-4183", status := .proven
    prop := ``MergeEmptyTarget, thm := some ``mergeEmptyTarget_proven },
  { id := "dict-merge-generic", pyFile := "Objects/dictobject.c", pyFns := ["dict_merge", "dict_merge_api"]
    statement := "dict_merge takes the fast route exactly for a dict whose tp_iter is dict_iter. On the slow route, for every key protocol and a keys() and __getitem__ that may raise or change the receiver: a failed entry test or keys() raises at once; override 1 never tests membership; on a present key override 0 skips __getitem__ and override 2 raises KeyError; on an absent key, or with override 1, __getitem__ runs first and the store sees what it left."
    source := "dictobject.c:4258-4354, :4356-4377", status := .proven
    prop := ``MergeGeneric, thm := some ``mergeGeneric_proven },
  { id := "dict-merge-seq2-order", pyFile := "Objects/dictobject.c", pyFns := ["merge_from_seq2_lock_held"]
    statement := "For an iterator that may raise or change the receiver at any step: PyObject_GetIter failing or an empty iterator ends it; a raising step or a bad element stops the loop with what earlier elements did still in place, and a TypeError from PySequence_Fast gets the note naming the element; a pair is stored, always if override is true and only if absent otherwise, and the loop goes on from the state the store left."
    source := "dictobject.c:4064-4126", status := .proven
    prop := ``Seq2Order, thm := some ``seq2Order_proven },
  { id := "dict-merge-refines", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "d.update(other) on well-formed distinct dicts is the fold of d[k] = v over other's items in order, whichever path runs: the clone into an empty dict, the single resize, or plain insertion. MemoryError is the only failure."
    source := "dict.update docstring", status := .proven
    prop := ``DictMergeRefines, thm := some ``dictMergeRefines_proven
    notes := "override == 1; the override 0 and 2 branches are not covered by this statement." },
  { id := "dict-merge-self", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "d.update(d) does nothing."
    source := "comment at dictobject.c:4176", status := .proven
    prop := ``DictMergeSelf, thm := some ``dictMergeSelf_proven },
  { id := "dict-merge-mapping", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "With a mapping argument whose __getitem__ succeeds, update is d[k] = E[k] for k in E.keys(), in order."
    source := "dict.update docstring, dictobject.c:5205", status := .proven
    prop := ``MergeMappingRefines, thm := some ``mergeMappingRefines_proven },
  { id := "dict-merge-seq2", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "With an iterable of pairs, update is d[k] = v for each pair, in order."
    source := "dict.update docstring, dictobject.c:5206", status := .proven
    prop := ``MergeSeq2Refines, thm := some ``mergeSeq2Refines_proven
    notes := "override == 1 and well-formed pairs. The error messages for bad elements are checked by the difftest, not stated here." },
  { id := "dict-update-arg-routes", pyFile := "Objects/dictobject.c", pyFns := ["dict_update_arg"]
    statement := "dict_update_arg sends an exact dict to dict_merge at once, an object with keys to dict_merge, and one without to the sequence route; a failed keys lookup is the result."
    source := "dict.update docstring, dictobject.c:3992-4009", status := .proven
    prop := ``UpdateArgRoutes, thm := some ``updateArgRoutes_proven },
  { id := "dict-cstring-wrappers", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "The C-string entry points build the key, raise if that fails with the dict untouched, and otherwise behave as the key operation."
    source := "Doc/c-api/dict.rst", status := .proven
    prop := ``CKeyWrappers, thm := some ``cKeyWrappers_proven
    notes := "One model, withCKey, stands for all of them: their bodies differ only in which key operation they call. PyDict_SetItemString also interns the key, which has no effect on the dict's contents." },
  { id := "set-table-refines", pyFile := "Objects/setobject.c",
    pyFns := ["set_lookkey", "set_do_lookup", "set_compare_entry_lock_held", "set_compare_frozenset", "set_add_entry_takeref", "set_table_resize", "set_contains_entry",
      "set_discard_entry", "set_add_key", "set_contains_key", "set_discard_key"]
    statement := "From an empty set, a run of add and discard leaves a well-formed table that holds what the abstract list holds, up to order, and `in` answers as the list does; or it stops with MemoryError, and then some set of no more keys than the run has steps needed a table PyMem_NEW refuses."
    source := "language: set semantics", status := .proven
    prop := ``SetTableRefines, thm := some ``setTableRefines_proven
    notes := "The one failure is the refusal of PyMem_NEW at setobject.c:527, about 2**58 slots; an allocator that gives up earlier is not modelled." },
  { id := "set-pop", pyFile := "Objects/setobject.c", pyFns := ["set_pop_impl"]
    statement := "s.pop() raises KeyError on an empty set; otherwise exactly one entry leaves and the table stays well formed, wherever the finger stood."
    source := "set.pop docstring; setobject.c:910-934", status := .proven
    prop := ``SetPopSpec, thm := some ``setPopSpec_proven },
  { id := "set-clear", pyFile := "Objects/setobject.c", pyFns := ["set_clear_internal", "set_empty_to_minsize"]
    statement := "Clearing keeps the table well formed and empties it."
    source := "set.clear docstring; setobject.c:633-694", status := .proven
    prop := ``SetClearSpec, thm := some ``setClearSpec_proven },
  { id := "set-iter-order", pyFile := "Objects/setobject.c", pyFns := ["set_next"]
    statement := "An iterator over a set that does not change yields its keys, in table order, each once."
    source := "setobject.c:709-731, 1095-1136", status := .proven
    prop := ``SetIterOrder, thm := some ``setIterOrder_proven },
  { id := "set-probe-failure", pyFile := "Objects/setobject.c", pyFns := ["set_lookkey", "set_do_lookup", "set_compare_entry_lock_held", "set_add_entry_takeref"]
    statement := "For every key protocol: an __eq__ that raises ends the probe with that exception, in the state it left; and when it changed the table, the lookup restarts on any answer and the add restarts on an answer of no."
    source := "setobject.c:153-160, :288-295", status := .proven
    prop := ``SetProbeFailure, thm := some ``setProbeFailure_proven },
  { id := "set-contains-body", pyFile := "Objects/setobject.c",
    pyFns := ["_PySet_Contains", "set_contains", "set___contains___impl", "frozenset___contains___impl",
      "set_compare_frozenset", "set_do_lookup", "set_contains_entry"]
    statement := "On a well-formed table, for every honest key protocol, set and frozenset __contains__ answer what the list answers, whichever compare function the search takes."
    source := "setobject.c:2544-2564, :2606-2626, :171-193, :220-248", status := .proven
    prop := ``SetContainsBody, thm := some ``setContainsBody_proven },
  { id := "set-frozen-identity-first", pyFile := "Objects/setobject.c",
    pyFns := ["set_compare_frozenset", "set_compare_entry_lock_held"]
    statement := "On a key whose hash changed after it went in, an exact frozenset finds the object at its slot by identity and a set walks past it."
    source := "setobject.c:144, :180-182", status := .proven
    prop := ``FrozenIdentityFirst, thm := some ``frozenIdentityFirst_proven
    notes := "A difference between the twins, new in 3.15. It needs a key that breaks the hash contract, and nothing is wrong with either answer. Run against CPython by hand; the difftest's objects keep their hash." },
  { id := "set-contains-retry", pyFile := "Objects/setobject.c",
    pyFns := ["_PySet_Contains", "set_unhashable_type"]
    statement := "For every key protocol, a failed hash in _PySet_Contains is retried with the frozenset hash only for a TypeError from a set, and otherwise goes through set_unhashable_type."
    source := "setobject.c:2549-2562", status := .proven
    prop := ``SetContainsRetry, thm := some ``setContainsRetry_proven },
  { id := "set-add-trusts-yes", pyFile := "Objects/setobject.c", pyFns := []
    statement := "set_add_entry and set_lookkey differ on an __eq__ that answers yes and changes the table: the lookup restarts, the add stops and treats the key as present."
    source := "setobject.c:159-162 against :290-295", status := .proven
    prop := ``SetAddTrustsYes, thm := some ``setAddTrustsYes_proven
    notes := "A difference between two bodies, on record. It needs an __eq__ that lies about its own effect, and nothing goes wrong in memory." },
  { id := "set-hash-failure", pyFile := "Objects/setobject.c", pyFns := ["set_add_key", "set_contains_key", "set_discard_key"]
    statement := "For every key protocol, a hash that raises is reported through set_unhashable_type and the set is unchanged."
    source := "setobject.c:600-631", status := .proven
    prop := ``SetHashFailure, thm := some ``setHashFailure_proven },
  { id := "odict-twins-agree", pyFile := "Objects/odictobject.c",
    pyFns := ["_odict_get_index", "_odict_resize", "_odict_add_new_node", "_odict_remove_node"]
    statement := "For keys keeping the contract, the C and pure-Python OrderedDict hold the same keys in the same order after any program of __setitem__, __delitem__ and move_to_end."
    source := "odictobject.c:3-4: necessarily explicitly equivalent to the pure Python class", status := .open
    prop := ``OdictTwinsAgree
    notes := "Not proved. Needs an invariant tying od_fast_nodes to dk_entries across the deferred _odict_resize, and one for the link heap." },
  { id := "dict-view-len", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "The length of any view of a well-formed dict is the length of the association list."
    source := "Doc/library/stdtypes.rst: dictionary view objects", status := .proven
    prop := ``ViewLen, thm := some ``viewLen_proven },
  { id := "dict-view-iter-order", pyFile := "Objects/dictobject.c",
    pyFns := ["dictkeys_iter", "dictitems_iter", "dictvalues_iter", "dictkeys_reversed",
      "dictitems_reversed", "dictvalues_reversed"]
    statement := "Iterating a view of a well-formed dict of either table form yields the association list in order, or reversed, and each view gives the iterator of its kind."
    source := "Doc/library/stdtypes.rst: views iterate in insertion order", status := .proven
    prop := ``ViewIterOrder, thm := some ``viewIterOrder_proven },
  { id := "dict-keys-view-contains", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "x in d.keys() is x in d."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``KeysViewContains, thm := some ``keysViewContains_proven },
  { id := "odict-list-ends", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "Adding a node at either end changes the list as named and increments od_state."
    source := "odictobject.c:499: incremented whenever the LL changes", status := .proven
    prop := ``OdictListEnds, thm := some ``odictListEnds_proven },
  { id := "odict-remove-node", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "Removing a node drops exactly that node and increments od_state."
    source := "odictobject.c:499", status := .proven
    prop := ``OdictRemoveNode, thm := some ``odictRemoveNode_proven },
  { id := "odict-clear-nodes", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "Clearing the nodes empties the list and od_fast_nodes, resets the sentinel and increments od_state."
    source := "odictobject.c:794-813", status := .proven
    prop := ``OdictClearNodes, thm := some ``odictClearNodes_proven },
  { id := "odict-iter-start", pyFile := "Objects/odictobject.c",
    pyFns := []
    statement := "An OrderedDict iterator starts at the first or last node as asked, recording the current size and state."
    source := "odictobject.c:1938-1968", status := .proven
    prop := ``OdictIterStart, thm := some ``odictIterStart_proven
    notes := "Says where iteration starts, not how it proceeds; see odict-iter-bounded." },
  { id := "odict-new-empty", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "A new OrderedDict has no nodes and an empty dict."
    source := "invariant", status := .proven
    prop := ``OdictNewEmpty, thm := some ``odictNewEmpty_proven },
  { id := "dict-getitem-suppressed", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "For every key protocol, including a hash or comparison that raises, and every dict, PyDict_GetItem returns without raising."
    source := "dictobject.c:2379-2388: PyDict_GetItem() suppresses all errors", status := .proven
    prop := ``GetItemSuppressed, thm := some ``getItemSuppressed_proven },
  { id := "dict-hash-failure", pyFile := "Objects/dictobject.c",
    pyFns := ["setitem_take2_lock_held", "PyDict_DelItem"]
    statement := "For every key protocol, when hashing the key raises, each of these raises dict_unhashable_type's exception and leaves the dict unchanged."
    source := "dictobject.c:2441-2460", status := .proven
    prop := ``HashFailureFamily, thm := some ``hashFailureFamily_proven },
  { id := "dict-pop-hash-order", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "With a key whose hash raises, PyDict_Pop answers not-found on an empty dict without hashing, and raises on a non-empty one."
    source := "dictobject.c:3295-3309", status := .proven
    prop := ``PopHashOrder, thm := some ``popHashOrder_proven },
  { id := "dict-compare-unicode-failure", pyFile := "Objects/dictobject.c", pyFns := ["compare_unicode_generic"]
    statement := "If __eq__ raises, compare_unicode_generic raises it, keeping whatever __eq__ did to the dict. If __eq__ replaced the table or the entry, it returns DKIX_KEY_CHANGED whatever __eq__ answered."
    source := "dictobject.c:1125-1151", status := .proven
    prop := ``CompareUnicodeFailure, thm := some ``compareUnicodeFailure_proven },
  { id := "dict-do-lookup-body", pyFile := "Objects/dictobject.c", pyFns := ["do_lookup"]
    statement := "One turn of the probe loop, at any position and for any check: a raising check ends the search with its exception; a negative answer is returned as it stands, which is how DKIX_KEY_CHANGED leaves; a positive one returns the index; zero goes on from the next slot, an empty slot ends the search, and a dummy goes on."
    source := "dictobject.c:1081-1123", status := .proven
    prop := ``DoLookupBody, thm := some ``doLookupBody_proven },
  { id := "dict-keysize-smallest", pyFile := "Objects/dictobject.c",
    pyFns := ["calculate_log2_keysize"]
    statement := "calculate_log2_keysize(m) is the smallest table of at least 8 slots with room for m."
    source := "dictobject.c:583", status := .proven
    prop := ``KeysizeSmallest, thm := some ``keysizeSmallest_proven },
  { id := "dict-estimate-smallest", pyFile := "Objects/dictobject.c",
    pyFns := ["estimate_log2_keysize"]
    statement := "estimate_log2_keysize(n) is calculate_log2_keysize((n*3+1)/2), and is the smallest table of at least 8 slots whose USABLE_FRACTION holds n."
    source := "dictobject.c:604-610", status := .proven
    prop := ``EstimateSmallest, thm := some ``estimateSmallest_proven },
  { id := "dict-getitem-body", pyFile := "Objects/dictobject.c", pyFns := ["dict_getitem"]
    statement := "PyDict_GetItem, for every key protocol: not a dict is silent; a failed hash goes to sys.unraisablehook; a failed lookup goes there too, unless it is a KeyError, which is dropped; and a good lookup gives its value."
    source := "dictobject.c:2379-2430", status := .proven
    prop := ``DictGetitemBody, thm := some ``dictGetitemBody_proven },
  { id := "dict-getitem-link", pyFile := "Objects/dictobject.c", pyFns := ["dict_getitem"]
    statement := "The model of PyDict_GetItem with its reports and the one the older theorems use agree on the value and the state."
    source := "model link", status := .proven
    prop := ``GetitemLink, thm := some ``getitemLink_proven },
  { id := "dict-del-known-hash-body", pyFile := "Objects/dictobject.c",
    pyFns := ["_PyDict_DelItem_KnownHash_LockHeld"]
    statement := "After its check, for every key protocol: a failed lookup is the result, in the state it left; no slot or no value is KeyError; and a value goes to delitem_common on that state."
    source := "dictobject.c:2958-2968", status := .proven
    prop := ``DelKnownHashBody, thm := some ``delKnownHashBody_proven },
  { id := "dict-subscript-body", pyFile := "Objects/dictobject.c", pyFns := ["_PyDict_Subscript", "_PyDict_SubscriptKnownHash"]
    statement := "d[key] after a good lookup, for every key protocol and any __missing__: a slot with a value gives it; otherwise an exact dict raises KeyError, while a subclass runs the special lookup, whose failure is the result, and calls what it finds on the state it left, either of which may have changed the dict."
    source := "dictobject.c:3755-3783", status := .proven
    prop := ``SubscriptBody, thm := some ``subscriptBody_proven },
  { id := "dict-checks", pyFile := "Objects/dictobject.c",
    pyFns := ["_PyDict_DelItem_KnownHash_LockHeld", "clear_lock_held", "pop_lock_held", "PyDict_SetItem", "PyDict_Contains",
      "dict_setdefault_ref_lock_held"]
    statement := "The opening tests of the writers: neither a dict nor a frozendict gets a SystemError, a frozendict gets the TypeError of frozendict_does_not_support, and a dict goes on to the body; clear_lock_held does nothing to either of the first two, and PyDict_Contains lets a frozendict through."
    source := "dictobject.c:2789-2806, :2941-2949, :3083-3085, :3280-3290, :4775-4786, :5249-5252", status := .proven
    prop := ``DictChecks, thm := some ``dictChecks_proven },
  { id := "dict-dict-merge-body", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "dict_dict_merge, for every key protocol and override: merging into itself or from an empty dict does nothing; an empty target takes a clone when the source is clean, and otherwise goes on with override forced to 1; anything else goes on as it is."
    source := "dictobject.c:4169-4205", status := .proven
    prop := ``DictDictMergeBody, thm := some ``dictDictMergeBody_proven },
  { id := "dict-merge-rest-body", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "The one big resize of dict_dict_merge runs only when the source does not fit, its failure ends the merge, and the loop starts from what it left, with the source in hand and its count as orig_size."
    source := "dictobject.c:4205-4217", status := .proven
    prop := ``MergeRestBody, thm := some ``mergeRestBody_proven },
  { id := "dict-merge-step-body", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "One step of the loop of dict_dict_merge, for each override: 1 stores; otherwise a failed test is the result, an absent key is stored from the state the test left, and a present key is skipped by 0 and raises KeyError under 2."
    source := "dictobject.c:4227-4243", status := .proven
    prop := ``MergeStepBody, thm := some ``mergeStepBody_proven },
  { id := "dict-resize-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["dictresize", "build_indices_generic", "build_indices_unicode"]
    statement := "dictresize on a well-formed table of either form: a size of 64 bits or more raises MemoryError and changes nothing; otherwise the live entries move over in order to a well-formed combined table of that size, with the usable count left over, unicode exactly when the old one was and the caller allows it."
    source := "dictobject.c:2097-2129, :2155-2305", status := .proven
    prop := ``DictResizeRefines, thm := some ``dictResizeRefines_proven },
  { id := "dict-resize-invalidates-inline", pyFile := "Objects/dictobject.c",
    pyFns := ["invalidate_and_clear_inline_values"]
    statement := "When an instance's dict leaves the split form, its inline values are marked invalid and emptied, and the dict is what now answers."
    source := "dictobject.c:2132-2139, :2229-2233", status := .proven
    prop := ``ResizeInvalidatesInline, thm := some ``resizeInvalidatesInline_proven },
  { id := "dict-dealloc", pyFile := "Objects/dictobject.c", pyFns := ["dict_dealloc"]
    statement := "A watcher that keeps a reference during dict_dealloc gets the dict as it left it, not cleared; without one the dict is gone."
    source := "dictobject.c:3605-3612", status := .proven
    prop := ``DictDeallocBody, thm := some ``dictDeallocBody_proven },
  { id := "dict-compare-generic-failure", pyFile := "Objects/dictobject.c", pyFns := ["compare_generic"]
    statement := "If __eq__ raises, compare_generic raises it, keeping whatever __eq__ did to the dict. If __eq__ replaced the table or the entry, it returns DKIX_KEY_CHANGED whatever __eq__ answered."
    source := "dictobject.c:1193-1204", status := .proven
    prop := ``CompareGenericFailure, thm := some ``compareGenericFailure_proven },
  { id := "dict-lookup-restarts", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "On DKIX_KEY_CHANGED, _Py_dict_lookup starts again on the current state of the dict."
    source := "dictobject.c:1379-1381", status := .proven
    prop := ``LookupRestarts, thm := some ``lookupRestarts_proven
    notes := "_Py_dict_lookup stays todo: its split branch is unproved." },
  { id := "dict-missing-hook", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "On a key absent from a well-formed dict, a subclass's __missing__ decides the result: its value, or its exception, and it may change the dict."
    source := "Doc/library/stdtypes.rst, d[key]", status := .proven
    prop := ``MissingHook, thm := some ``missingHook_proven },
  { id := "dict-setdefault-no-crash", pyFile := "Objects/dictobject.c",
    pyFns := ["dict_setdefault_ref_lock_held", "dict_setdefault_impl"]
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
    pyFns := ["dictreviter_iter_lock_held", "dictiter_len", "dictiter_new"]
    statement := "After any program of sets, deletes and next() on a reverse dict iterator, __length_hint__ fits Py_ssize_t."
    source := "invariant; forward iterator check at dictobject.c:5722", status := .proven
    prop := ``RevIterLenNonneg, thm := some ``revIterLenNonneg_proven
    notes := "False on 3.14.7, where a reverse iterator had no di->len == 0 test and len went negative (gh-158254); 3.15.2 has the test at :6273." },
  { id := "set-frozenset-hash-order-free", pyFile := "Objects/setobject.c",
    pyFns := []
    statement := "Two tables whose slots are a permutation of each other, with the same mask, fill and used, have the same frozenset hash."
    source := "setobject.c:979-987: a frozenset hash should be independent of order", status := .proven
    prop := ``FrozensetHashOrderFree, thm := some ``frozensetHashOrderFree_proven },
  { id := "set-frozenset-hash-not-minus-one", pyFile := "Objects/setobject.c",
    pyFns := []
    statement := "The frozenset hash is never -1, the error value of tp_hash."
    source := "setobject.c:1007-1009", status := .proven
    prop := ``FrozensetHashNotMinusOne, thm := some ``frozensetHashNotMinusOne_proven },
  { id := "set-new-size-minimal", pyFile := "Objects/setobject.c", pyFns := []
    statement := "For minused < 2**63, set_table_resize asks for the smallest table of at least 8 slots above minused."
    source := "setobject.c:495: Find the smallest table size > minused", status := .proven
    prop := ``SetNewSizeMinimal, thm := some ``setNewSizeMinimal_proven
    notes := "Hypothesis: minused is a Py_ssize_t; line 315 notes the largest size is PY_SSIZE_T_MAX + 1." },
  { id := "set-clear-empties", pyFile := "Objects/setobject.c",
    pyFns := []
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
