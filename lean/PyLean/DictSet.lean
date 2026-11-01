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
  { id := "dict-lcg-full-period", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "For all n, x, y, repeating j -> 5*j + 1 from x reaches y mod 2**n within 2**n steps."
    source := "dictobject.c:323-325, cited there as folklore", status := .proven
    prop := ``LcgFullPeriod, thm := some ``lcgFullPeriod_proven
    notes := "Proved from scratch, without Mathlib: 2**n steps add 2**n times an odd number." },
  { id := "dict-probe-reaches-all", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "For every table of 2**n slots, every 64-bit hash and every slot s, the probe sequence reaches s within 2**n + 13 steps."
    source := "dictobject.c:354-358", status := .proven
    prop := ``ProbeReachesAll, thm := some ``probeReachesAll_proven },
  { id := "dict-usable-fraction", pyFile := "Objects/dictobject.c", pyFns := []
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
    pyFns := []
    statement := "Every entry index of a table of 2**n slots fits the int8, int16 or int32 slot chosen for n."
    source := "asserts at dictobject.c:513, :517, :526", status := .proven
    prop := ``IndexWidthFits, thm := some ``indexWidthFits_proven },
  { id := "dict-growth-room", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "After a resize to GROWTH_RATE(used), the table has room for at least one more entry."
    source := "dictobject.c:580-590; assert at :1827", status := .proven
    prop := ``GrowthRoom, thm := some ``growthRoom_proven },
  { id := "dict-lookup-found", pyFile := "Objects/dictobject.c",
    pyFns := ["do_lookup", "compare_generic", "compare_unicode_generic", "compare_unicode_unicode", "unicodekeys_lookup_generic", "dictkeys_generic_lookup"]
    statement := "For every key type keeping the hash/eq contract and every well-formed combined table, lookup of a key equal to a live entry's key stops, returns that entry and its value, runs no restart and leaves the dict unchanged."
    source := "invariant: dictobject.c:1232-1246", status := .proven
    prop := ``LookupFound, thm := some ``lookupFound_proven },
  { id := "dict-lookup-missing", pyFile := "Objects/dictobject.c",
    pyFns := ["do_lookup", "compare_generic", "compare_unicode_generic", "compare_unicode_unicode"]
    statement := "For every such key type and table, lookup of a key equal to no live entry stops at an empty slot and returns DKIX_EMPTY. The table always has an empty slot, so the loop terminates at every load the table can reach."
    source := "dictobject.c:145-150, :357-358", status := .proven
    prop := ``LookupMissing, thm := some ``lookupMissing_proven },
  { id := "dict-lookup-assoc", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "Lookup on a well-formed dict returns exactly what the association list holds for that key."
    source := "language: dict maps keys to values", status := .proven
    prop := ``LookupAssoc, thm := some ``lookupAssoc_proven },
  { id := "dict-setitem-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["setitem_take2_lock_held", "insert_to_emptydict", "insert_combined_dict", "find_empty_slot", "is_unusable_slot", "insertion_resize", "build_indices_unicode", "new_keys_object"]
    statement := "d[key] = v on any well-formed combined dict either raises MemoryError and changes nothing, or keeps the table well formed and does to the association list what assocSet does: overwrite in place, or append."
    source := "language: dicts preserve insertion order; invariant", status := .proven
    prop := ``SetItemRefines, thm := some ``setItemRefines_proven
    notes := "MemoryError is in the statement rather than assumed away: it is the only failure. Split tables are not covered here." },
  { id := "dict-insertion-order", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A key not in the list goes at the end, and every earlier pair stays in place."
    source := "Doc/library/stdtypes.rst: dictionaries preserve insertion order", status := .proven
    prop := ``InsertionOrder, thm := some ``insertionOrder_proven },
  { id := "dict-overwrite-order", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "Updating an existing key does not change the order of keys."
    source := "Doc/library/stdtypes.rst: updating a key does not affect the order", status := .proven
    prop := ``OverwriteKeepsOrder, thm := some ``overwriteKeepsOrder_proven },
  { id := "dict-delitem-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_DelItem", "_PyDict_DelItem_KnownHash_LockHeld", "lookdict_index"]
    statement := "del d[key] on a well-formed dict removes exactly that pair and keeps the table well formed; a missing key raises KeyError and changes nothing."
    source := "language; invariant: Dummy slots at dictobject.c:78-83", status := .proven
    prop := ``DelItemRefines, thm := some ``delItemRefines_proven },
  { id := "dict-popitem-lifo", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "popitem on a well-formed non-empty dict removes and returns the last pair of the association list, keeping the table well formed; on an empty dict it raises KeyError."
    source := "dict.popitem docstring, dictobject.c:4590-4593", status := .proven
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
    pyFns := ["dict_getitem"]
    statement := "Each C API read returns what the association list holds for the key and leaves the dict unchanged."
    source := "Doc/c-api/dict.rst", status := .proven
    prop := ``ReadFamily, thm := some ``readFamily_proven },
  { id := "dict-lookup-no-mutate", pyFile := "Objects/dictobject.c",
    pyFns := ["do_lookup", "compare_generic", "compare_unicode_generic", "dictkeys_generic_lookup",
      "unicodekeys_lookup_generic"]
    statement := "If __eq__ never mutates the dict (a lying comparison that returns arbitrary booleans but leaves the object alone), then _Py_dict_lookup leaves the table byte-identical, whatever it answers, so Chain/WF/DictInv all survive. The only route by which lookup can change the table is a genuinely mutating __eq__."
    source := "dictobject.c:1001-1133; the dk re-read and DKIX_KEY_CHANGED checks at 1062, 1118", status := .proven
    prop := ``InvUnderLyingEq, thm := some ``invUnderLyingEq_proven },
  { id := "dict-readers-faithful", pyFile := "Objects/dictobject.c",
    pyFns := ["PyDict_GetItemRef", "_PyDict_GetItemRef_KnownHash", "PyDict_GetItemWithError", "PyDict_Contains", "_PyDict_Contains_KnownHash", "dict_subscript", "dict_get_impl"]
    statement := "For every key protocol, including a hash or __eq__ that raises or mutates the dict, each reader is faithful to _Py_dict_lookup: a raising hash or lookup propagates with the state the lookup left, and a slot with ix >= 0 but no value (a split key this dict lacks) reads as absent and is never dereferenced."
    source := "dictobject.c:2420-2509, 2537, 4835-4882, 3504-3538, 4386-4406; the ix>=0,value==NULL note at 1915-1922", status := .proven
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
  { id := "dict-forward-iter-order", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "A forward key, value or item iterator over an unchanged dict yields the list in order, whatever deletions left holes in the table, and stops."
    source := "Doc/library/stdtypes.rst: iteration order", status := .proven
    prop := ``ForwardIterOrder, thm := some ``forwardIterOrder_proven
    notes := "Hypothesis d.used < 2**63 is the type invariant of Py_ssize_t ma_used." },
  { id := "dict-pop-default", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "d.pop(key[, default]) returns and removes the list's value; if absent it returns default, or raises KeyError(key) when there is none, changing nothing."
    source := "dict.pop docstring, dictobject.c:4573-4576", status := .proven
    prop := ``PopDefaultSpec, thm := some ``popDefaultSpec_proven },
  { id := "dict-ass-sub", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "mp_ass_subscript deletes when the value is NULL and sets otherwise."
    source := "dictobject.c:3540-3547", status := .proven
    prop := ``AssSubDispatch, thm := some ``assSubDispatch_proven },
  { id := "dict-new-empty", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A new dict is well formed and holds nothing."
    source := "invariant", status := .proven
    prop := ``NewDictEmpty, thm := some ``newDictEmpty_proven },
  { id := "dict-split-refines", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "dictresize", "insertdict", "insert_split_key", "insert_split_value",
      "delitem_common", "delete_index_from_values", "dict_popitem_impl", "clear_lock_held",
      "clear_embedded_values"]
    statement := "On a well-formed split dict, for a key of any kind: the lookup agrees with the list, in which a shared key with no value is absent; d[key] = v keeps the table well formed, split or combined, and does what assocSet does, up to the object of a key equal to a shared one; del, popitem and clear do what the list does; a full iteration gives the list in insertion order."
    source := "task: the model equals an abstract association list; dictobject.c:1247-1311, 1831-1882, 1890-1957, 2064-2214, 2772-2831, 2944-3002, 4596-4679", status := .proven
    prop := ``SplitRefines, thm := some ``splitRefines_proven
    notes := "The combined half of these rows is in dict-lookup-*, dict-setitem-refines, dict-delitem-refines, dict-popitem-lifo and dict-clear; their failure paths are in dict-lookup-control and dict-insert-failure." },
  { id := "dict-split-fresh", pyFile := "Objects/dictobject.c", pyFns := ["new_dict_with_shared_keys"]
    statement := "A new dict with the shared keys of a class is a well-formed split table, so dict-split-refines is not vacuous."
    source := "dictobject.c:896-909", status := .proven
    prop := ``SplitFresh, thm := some ``splitFresh_proven },
  { id := "dict-split-del-keeps-key", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "del d[key] on a split dict leaves the key in the shared keys with no value in this dict: the state dict.setdefault fails on is reached by ordinary operations and satisfies the invariant."
    source := "dictobject.c:2802-2807", status := .proven
    prop := ``SplitDelKeepsKey, thm := some ``splitDelKeepsKey_proven },
  { id := "dict-lookup-control", pyFile := "Objects/dictobject.c", pyFns := ["_Py_dict_lookup"]
    statement := "After the scan of _Py_dict_lookup, in every dispatch branch and for every key protocol: an exception is the result, in the state __eq__ left, and DKIX_KEY_CHANGED restarts on that state."
    source := "dictobject.c:1261-1301", status := .proven
    prop := ``LookupControl, thm := some ``lookupControl_proven },
  { id := "dict-insert-failure", pyFile := "Objects/dictobject.c", pyFns := ["insertdict", "dictresize"]
    statement := "If the lookup in insertdict raises, the exception is the result; dictresize refuses a size of 64 bits or more with MemoryError and changes nothing."
    source := "dictobject.c:1909-1913, 1953-1956, 2064-2214", status := .proven
    prop := ``InsertFailure, thm := some ``insertFailure_proven },
  { id := "dict-lookup-index-valid", pyFile := "Objects/dictobject.c",
    pyFns := ["_Py_dict_lookup", "do_lookup", "compare_generic", "compare_unicode_generic"]
    statement := "For every key protocol, including an __eq__ that lies, raises or changes the dict in any way, an index _Py_dict_lookup reports is one the table has when it returns."
    source := "dictobject.c:1062, 1118: dk == mp->ma_keys && ep->me_key == startkey", status := .proven
    prop := ``LookupIndexValid, thm := some ``lookupIndexValid_proven },
  { id := "dict-struct-survives", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "If every comparison keeps the chains and counts of a combined table, whatever it answers and whether or not it raises, then _Py_dict_lookup, insertdict and _PyDict_DelItem_KnownHash keep them, on all their outcomes. Key uniqueness is not claimed: a lying __eq__ can break it."
    source := "invariant: _PyDict_CheckConsistency", status := .proven
    prop := ``StructSurvives, thm := some ``structSurvives_proven
    notes := "Combined tables only; the split case is not proved." },
  { id := "dict-struct-hyp-met", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "An __eq__ that clears the dict it is probing meets the hypothesis of dict-struct-survives."
    source := "dictobject.c:2959-3002", status := .proven
    prop := ``StructHypMet, thm := some ``structHypMet_proven },
  { id := "dict-merge-guard", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "For every key protocol and every override: an error from the loop body is raised as it stands, even if the source changed; otherwise a changed number of items in the source raises RuntimeError('dict mutated during update'), in the state the callback left; otherwise the loop goes on from the source as it now stands."
    source := "dictobject.c:3952-3986", status := .proven
    prop := ``MergeGuard, thm := some ``mergeGuard_proven },
  { id := "dict-merge-quiet", pyFile := "Objects/dictobject.c", pyFns := ["dict_dict_merge"]
    statement := "If no callback touches the source, then whatever __eq__ answers or does to the receiver, the merge loop runs over the items the source had at the start and the size test never fires."
    source := "dictobject.c:3947-3986", status := .proven
    prop := ``MergeQuiet, thm := some ``mergeQuiet_proven },
  { id := "dict-merge-guard-reachable", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A key whose __eq__ clears the source makes d.update(source) raise RuntimeError('dict mutated during update')."
    source := "dictobject.c:3981-3985; the test reproduces it on CPython", status := .proven
    prop := ``MergeGuardReachable, thm := some ``mergeGuardReachable_proven },
  { id := "dict-merge-same-size-unseen", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "A callback that replaces an item of the source and keeps the count is not seen: the merge succeeds, and a key the source held at the start is missing from the receiver."
    source := "dictobject.c:3981 compares only ma_used; checked on 3.14.7 and main", status := .proven
    prop := ``MergeSameSizeUnseen, thm := some ``mergeSameSizeUnseen_proven
    notes := "Behaviour on record, not a bug report: the forward dict iterator goes on past the same change." },
  { id := "dict-merge-empty-target", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "On an empty receiver every override value behaves as override == 1."
    source := "dictobject.c:3900-3905", status := .proven
    prop := ``MergeEmptyTarget, thm := some ``mergeEmptyTarget_proven },
  { id := "dict-merge-generic", pyFile := "Objects/dictobject.c", pyFns := ["dict_merge"]
    statement := "For every key protocol, and a keys() and __getitem__ that may raise or change the receiver: a failed entry test or keys() raises at once; override 1 never tests membership; on a present key override 0 skips __getitem__ and override 2 raises KeyError; on an absent key, or with override 1, __getitem__ runs first and the store sees what it left."
    source := "dictobject.c:4002-4005, 4017-4075", status := .proven
    prop := ``MergeGeneric, thm := some ``mergeGeneric_proven },
  { id := "dict-merge-seq2-order", pyFile := "Objects/dictobject.c", pyFns := ["merge_from_seq2_lock_held"]
    statement := "For an iterator that may raise or change the receiver at any step: a raising step or a bad element stops the loop with what earlier elements did still in place; exhaustion ends it; a pair is stored and the loop goes on from the state the store left."
    source := "dictobject.c:3810-3866", status := .proven
    prop := ``Seq2Order, thm := some ``seq2Order_proven },
  { id := "dict-merge-refines", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "d.update(other) on well-formed distinct dicts is the fold of d[k] = v over other's items in order, whichever path runs: the clone into an empty dict, the single resize, or plain insertion. MemoryError is the only failure."
    source := "dict.update docstring", status := .proven
    prop := ``DictMergeRefines, thm := some ``dictMergeRefines_proven
    notes := "override == 1; the override 0 and 2 branches are not covered by this statement." },
  { id := "dict-merge-self", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "d.update(d) does nothing."
    source := "comment at dictobject.c:3898", status := .proven
    prop := ``DictMergeSelf, thm := some ``dictMergeSelf_proven },
  { id := "dict-merge-mapping", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "With a mapping argument whose __getitem__ succeeds, update is d[k] = E[k] for k in E.keys(), in order."
    source := "dict.update docstring, dictobject.c:4806", status := .proven
    prop := ``MergeMappingRefines, thm := some ``mergeMappingRefines_proven },
  { id := "dict-merge-seq2", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "With an iterable of pairs, update is d[k] = v for each pair, in order."
    source := "dict.update docstring, dictobject.c:4807", status := .proven
    prop := ``MergeSeq2Refines, thm := some ``mergeSeq2Refines_proven
    notes := "override == 1 and well-formed pairs. The error messages for bad elements are checked by the difftest, not stated here." },
  { id := "dict-update-arg-routes", pyFile := "Objects/dictobject.c", pyFns := ["dict_update_arg"]
    statement := "dict_update_arg sends an object with keys to dict_merge and one without to the sequence route."
    source := "dict.update docstring, dictobject.c:4805-4808", status := .proven
    prop := ``UpdateArgRoutes, thm := some ``updateArgRoutes_proven },
  { id := "dict-cstring-wrappers", pyFile := "Objects/dictobject.c",
    pyFns := []
    statement := "The C-string entry points build the key, raise if that fails with the dict untouched, and otherwise behave as the key operation."
    source := "Doc/c-api/dict.rst", status := .proven
    prop := ``CKeyWrappers, thm := some ``cKeyWrappers_proven
    notes := "One model, withCKey, stands for all of them: their bodies differ only in which key operation they call. PyDict_SetItemString also interns the key, which has no effect on the dict's contents." },
  { id := "set-table-refines", pyFile := "Objects/setobject.c",
    pyFns := ["set_lookkey", "set_add_entry_takeref", "set_table_resize", "set_contains_entry",
      "set_discard_entry", "set_add_key", "set_contains_key", "set_discard_key"]
    statement := "From an empty set, a run of add and discard either stops with MemoryError, when a table is refused, or leaves a well-formed table that holds what the abstract list holds, up to order, and `in` answers as the list does."
    source := "language: set semantics", status := .proven
    prop := ``SetTableRefines, thm := some ``setTableRefines_proven
    notes := "The statement admits MemoryError because the model mirrors the refusal of PyMem_NEW at setobject.c:343: a long enough run can reach it." },
  { id := "set-pop", pyFile := "Objects/setobject.c", pyFns := ["set_pop_impl"]
    statement := "s.pop() raises KeyError on an empty set; otherwise exactly one entry leaves and the table stays well formed, wherever the finger stood."
    source := "set.pop docstring; setobject.c:719-743", status := .proven
    prop := ``SetPopSpec, thm := some ``setPopSpec_proven },
  { id := "set-clear", pyFile := "Objects/setobject.c", pyFns := ["set_clear_internal", "set_empty_to_minsize"]
    statement := "Clearing keeps the table well formed and empties it."
    source := "set.clear docstring; setobject.c:445-504", status := .proven
    prop := ``SetClearSpec, thm := some ``setClearSpec_proven },
  { id := "set-iter-order", pyFile := "Objects/setobject.c", pyFns := ["set_next"]
    statement := "An iterator over a set that does not change yields its keys, in table order, each once."
    source := "setobject.c:519-541, 901-942", status := .proven
    prop := ``SetIterOrder, thm := some ``setIterOrder_proven },
  { id := "set-probe-failure", pyFile := "Objects/setobject.c", pyFns := ["set_lookkey", "set_add_entry_takeref"]
    statement := "For every key protocol: an __eq__ that raises ends the probe with that exception, in the state it left; and when it changed the table, the lookup restarts on any answer and the add restarts on an answer of no."
    source := "setobject.c:112-120, 171-178", status := .proven
    prop := ``SetProbeFailure, thm := some ``setProbeFailure_proven },
  { id := "set-add-trusts-yes", pyFile := "Objects/setobject.c", pyFns := []
    statement := "set_add_entry and set_lookkey differ on an __eq__ that answers yes and changes the table: the lookup restarts, the add stops and treats the key as present."
    source := "setobject.c:118-121 against 173-178", status := .proven
    prop := ``SetAddTrustsYes, thm := some ``setAddTrustsYes_proven
    notes := "A difference between two bodies, on record. It needs an __eq__ that lies about its own effect, and nothing goes wrong in memory." },
  { id := "set-hash-failure", pyFile := "Objects/setobject.c", pyFns := ["set_add_key", "set_contains_key", "set_discard_key"]
    statement := "For every key protocol, a hash that raises is reported through set_unhashable_type and the set is unchanged."
    source := "setobject.c:412-443", status := .proven
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
    pyFns := []
    statement := "Iterating a view of an unchanged dict yields the association list in order."
    source := "Doc/library/stdtypes.rst: views iterate in insertion order", status := .proven
    prop := ``ViewIterOrder, thm := some ``viewIterOrder_proven },
  { id := "dict-keys-view-contains", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "x in d.keys() is x in d."
    source := "Doc/library/stdtypes.rst", status := .proven
    prop := ``KeysViewContains, thm := some ``keysViewContains_proven },
  { id := "odict-list-ends", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "Adding a node at either end changes the list as named and increments od_state."
    source := "odictobject.c:500: incremented whenever the LL changes", status := .proven
    prop := ``OdictListEnds, thm := some ``odictListEnds_proven },
  { id := "odict-remove-node", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "Removing a node drops exactly that node and increments od_state."
    source := "odictobject.c:500", status := .proven
    prop := ``OdictRemoveNode, thm := some ``odictRemoveNode_proven },
  { id := "odict-clear-nodes", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "Clearing the nodes empties the list and od_fast_nodes, resets the sentinel and increments od_state."
    source := "odictobject.c:795-814", status := .proven
    prop := ``OdictClearNodes, thm := some ``odictClearNodes_proven },
  { id := "odict-iter-start", pyFile := "Objects/odictobject.c",
    pyFns := []
    statement := "An OrderedDict iterator starts at the first or last node as asked, recording the current size and state."
    source := "odictobject.c:1942-1973", status := .proven
    prop := ``OdictIterStart, thm := some ``odictIterStart_proven
    notes := "Says where iteration starts, not how it proceeds; see odict-iter-bounded." },
  { id := "odict-new-empty", pyFile := "Objects/odictobject.c", pyFns := []
    statement := "A new OrderedDict has no nodes and an empty dict."
    source := "invariant", status := .proven
    prop := ``OdictNewEmpty, thm := some ``odictNewEmpty_proven },
  { id := "dict-getitem-suppressed", pyFile := "Objects/dictobject.c",
    pyFns := ["dict_getitem"]
    statement := "For every key protocol, including a hash or comparison that raises, and every dict, PyDict_GetItem returns without raising."
    source := "dictobject.c:2290-2299: PyDict_GetItem() suppresses all errors", status := .proven
    prop := ``GetItemSuppressed, thm := some ``getItemSuppressed_proven },
  { id := "dict-hash-failure", pyFile := "Objects/dictobject.c",
    pyFns := ["setitem_take2_lock_held", "PyDict_DelItem"]
    statement := "For every key protocol, when hashing the key raises, each of these raises dict_unhashable_type's exception and leaves the dict unchanged."
    source := "dictobject.c:2352-2366", status := .proven
    prop := ``HashFailureFamily, thm := some ``hashFailureFamily_proven },
  { id := "dict-pop-hash-order", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "With a key whose hash raises, PyDict_Pop answers not-found on an empty dict without hashing, and raises on a non-empty one."
    source := "dictobject.c:3171-3185", status := .proven
    prop := ``PopHashOrder, thm := some ``popHashOrder_proven },
  { id := "dict-compare-unicode-failure", pyFile := "Objects/dictobject.c", pyFns := ["compare_unicode_generic"]
    statement := "If __eq__ raises, compare_unicode_generic raises it, keeping whatever __eq__ did to the dict. If __eq__ replaced the table or the entry, it returns DKIX_KEY_CHANGED whatever __eq__ answered."
    source := "dictobject.c:1045-1071", status := .proven
    prop := ``CompareUnicodeFailure, thm := some ``compareUnicodeFailure_proven },
  { id := "dict-do-lookup-raises", pyFile := "Objects/dictobject.c", pyFns := ["do_lookup"]
    statement := "A check that raises ends the probe loop with that exception, in the state the check left."
    source := "dictobject.c:1001-1043", status := .proven
    prop := ``DoLookupRaises, thm := some ``doLookupRaises_proven },
  { id := "dict-compare-generic-failure", pyFile := "Objects/dictobject.c", pyFns := ["compare_generic"]
    statement := "If __eq__ raises, compare_generic raises it, keeping whatever __eq__ did to the dict. If __eq__ replaced the table or the entry, it returns DKIX_KEY_CHANGED whatever __eq__ answered."
    source := "dictobject.c:1113-1124", status := .proven
    prop := ``CompareGenericFailure, thm := some ``compareGenericFailure_proven },
  { id := "dict-lookup-restarts", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "On DKIX_KEY_CHANGED, _Py_dict_lookup starts again on the current state of the dict."
    source := "dictobject.c:1299-1301", status := .proven
    prop := ``LookupRestarts, thm := some ``lookupRestarts_proven
    notes := "_Py_dict_lookup stays todo: its split branch is unproved." },
  { id := "dict-missing-hook", pyFile := "Objects/dictobject.c", pyFns := []
    statement := "On a key absent from a well-formed dict, a subclass's __missing__ decides the result: its value, or its exception."
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
    source := "invariant; forward iterator check at dictobject.c:5279", status := .refuted
    prop := ``RevIterLenNonneg, thm := some ``revIterLenNonneg_refuted
    bug := some "dictset-reversed-iter-length-hint"
    notes := "Known upstream as gh-158254, fixed on main; 3.14.7 still has it." },
  { id := "set-frozenset-hash-order-free", pyFile := "Objects/setobject.c",
    pyFns := []
    statement := "Two tables whose slots are a permutation of each other, with the same mask, fill and used, have the same frozenset hash."
    source := "setobject.c:785-793: a frozenset hash should be independent of order", status := .proven
    prop := ``FrozensetHashOrderFree, thm := some ``frozensetHashOrderFree_proven },
  { id := "set-frozenset-hash-not-minus-one", pyFile := "Objects/setobject.c",
    pyFns := []
    statement := "The frozenset hash is never -1, the error value of tp_hash."
    source := "setobject.c:813-815", status := .proven
    prop := ``FrozensetHashNotMinusOne, thm := some ``frozensetHashNotMinusOne_proven },
  { id := "set-new-size-minimal", pyFile := "Objects/setobject.c", pyFns := []
    statement := "For minused < 2**63, set_table_resize asks for the smallest table of at least 8 slots above minused."
    source := "setobject.c:311: Find the smallest table size > minused", status := .proven
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
