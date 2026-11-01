import PyLean.Registry
import PyLean.TypeObj.ExcPropsGroup

/-!
The registry of `Objects/exceptions.c`. The properties live in `ExcPropsBase`, `ExcPropsRest`,
`ExcPropsSplit` and `ExcPropsGroup`, with the hypotheses of each explained in its docstring.
The model is `ExcCore`, `ExcGroup`, `ExcOs`, `ExcUnicode`, `ExcFreelist`, and `Exceptions` for
the dispatch.
-/

namespace PyLean.TypeObj

open PyLean.Registry

private def src := "Objects/exceptions.c"

private def p (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (notes : String := "") : Entry :=
  { id := id, pyFile := src, pyFns := fns, statement := statement, source := source,
    status := .proven, prop := prop, thm := some thm, notes := notes }

private def r (id : String) (fns : List String) (statement source : String)
    (prop thm : Lean.Name) (bug : String) (notes : String := "") : Entry :=
  { id := id, pyFile := src, pyFns := fns, statement := statement, source := source,
    status := .refuted, prop := prop, thm := some thm, bug := some bug, notes := notes }

def excEntries : List Entry := [
  -- BaseException
  p "typeobj-exc-str-args" ["BaseException_str"]
    "For every exception and every rt, str(e) is '' with no args, str(args[0]) with one, and str(args) otherwise."
    "exceptions.c:171-190" ``BaseExceptionStrArgs ``baseExceptionStrArgs_proven,
  p "typeobj-exc-repr-args" ["BaseException_repr"]
    "repr(e) is Name(repr(args[0])) with one argument and Name + repr(args) otherwise, where Name is the last dotted part of tp_name."
    "exceptions.c:193-210" ``BaseExceptionReprArgs ``baseExceptionReprArgs_proven,
  p "typeobj-exc-keyerror-str" ["KeyError_str"]
    "str(KeyError(x)) is repr(x) for one argument; any other argument count behaves as BaseException_str."
    "comment at exceptions.c:2944-2952" ``KeyErrorStrOneArg ``keyErrorStrOneArg_proven,
  p "typeobj-exc-vectorcall-twin" ["BaseException_new", "BaseException_init", "BaseException_vectorcall"]
    "With no keywords, BaseException_vectorcall builds an object with the same class and fields as tp_new followed by tp_init."
    "twin paths: _PyExc_InitTypes installs the vectorcall on classes with both default slots (exceptions.c:4424)"
    ``BaseExceptionVectorcallTwin ``baseExceptionVectorcallTwin_proven,
  p "typeobj-exc-reduce" ["BaseException___reduce___impl"]
    "e.__reduce__() is (type(e), e.args) plus the instance dict exactly when a dict exists."
    "exceptions.c:220-227" ``BaseExceptionReduceShape ``baseExceptionReduceShape_proven,
  p "typeobj-exc-setstate" ["BaseException___setstate___impl"]
    "__setstate__(None) does nothing; a non-dict is a TypeError that changes nothing; a non-string key is a TypeError."
    "exceptions.c:243-266" ``BaseExceptionSetstateChecks ``baseExceptionSetstateChecks_proven,
  p "typeobj-exc-traceback-setter" ["BaseException___traceback___set_impl", "BaseException___traceback___get_impl", "BaseException_with_traceback_impl"]
    "__traceback__ accepts only a traceback or None (TypeError otherwise, world unchanged), cannot be deleted, and with_traceback returns self."
    "exceptions.c:279-286, :398-418" ``TracebackSetterChecks ``tracebackSetterChecks_proven,
  p "typeobj-exc-cause-suppress" ["BaseException___cause___set_impl", "BaseException___cause___get_impl", "PyException_SetCause"]
    "Every successful assignment to __cause__, None included, stores the value and sets __suppress_context__."
    "docs (Built-in Exceptions: raising and handling) and exceptions.c:551-558" ``CauseSetsSuppressContext ``causeSetsSuppressContext_proven,
  p "typeobj-exc-context-set" ["BaseException___context___set_impl", "BaseException___context___get_impl", "PyException_SetContext"]
    "Assigning __context__ stores the value (None as NULL) and leaves __cause__ and __suppress_context__ alone."
    "exceptions.c:443-461" ``ContextSetKeepsSuppress ``contextSetKeepsSuppress_proven,
  p "typeobj-exc-suppress-bool" []
    "__suppress_context__ stores True or False, rejects any other value with TypeError, and cannot be deleted."
    "BaseException_members, exceptions.c:605; Py_T_BOOL in Python/structmember.c:170"
    ``SuppressContextOnlyBool ``suppressContextOnlyBool_proven,
  p "typeobj-exc-args-set" ["BaseException_args_set_impl", "BaseException_args_get_impl"]
    "e.args = t stores t's items for a tuple t; args cannot be deleted."
    "exceptions.c:343-372" ``ArgsSetStoresTuple ``argsSetStoresTuple_proven,
  p "typeobj-exc-add-note" ["BaseException_add_note_impl"]
    "add_note(x) raises TypeError for a non-str x before anything else; when __notes__ is a list, however it was found, the list gains x at the end."
    "exceptions.c:298-326" ``AddNoteAppends ``addNoteAppends_proven,
  p "typeobj-exc-capi-roundtrip" ["PyException_GetTraceback", "PyException_SetTraceback", "PyException_GetCause", "PyException_SetCause", "PyException_GetContext", "PyException_SetContext", "PyException_GetArgs", "PyException_SetArgs"]
    "PyException_SetCause, SetContext, SetArgs and SetTraceback are read back unchanged by the matching getters."
    "exceptions.c:518-596" ``PyExceptionApiRoundTrip ``pyExceptionApiRoundTrip_proven,
  p "typeobj-exc-capi-misc" ["_PyException_AddNote", "PyExceptionClass_Name"]
    "_PyException_AddNote rejects a non-exception with TypeError before calling add_note; PyExceptionClass_Name is tp_name."
    "exceptions.c:599-603, :4574-4586" ``PyExceptionMiscApi ``pyExceptionMiscApi_proven,
  -- StopIteration, SystemExit
  p "typeobj-exc-stopiteration-value" ["StopIteration_init"]
    "After StopIteration.__init__, value is args[0], or None with no args, on every call."
    "exceptions.c:754-769" ``StopIterationValue ``stopIterationValue_proven,
  p "typeobj-exc-systemexit-code" ["SystemExit_init"]
    "After SystemExit.__init__, code is unchanged with no args, args[0] with one, and the tuple otherwise."
    "exceptions.c:819-836" ``SystemExitCode ``systemExitCode_proven
    "Unlike StopIteration, code is not reset by a second __init__() with no arguments.",
  -- ImportError, NameError, AttributeError
  p "typeobj-exc-importerror-msg" ["ImportError_init", "ImportError_str"]
    "ImportError(m) sets msg to m; str(e) is msg when msg is an exact str, BaseException_str otherwise."
    "exceptions.c:1810-1843, :1876-1883" ``ImportErrorMsgStr ``importErrorMsgStr_proven,
  p "typeobj-exc-reduce-keeps-name" ["ImportError_getstate", "ImportError_reduce", "AttributeError_getstate", "AttributeError_reduce"]
    "The state dict of ImportError.__reduce__ and AttributeError.__reduce__ holds a set name; AttributeError's also holds args."
    "exceptions.c:1886-1931, :2643-2683" ``ReduceKeepsNameImportAttr ``reduceKeepsNameImportAttr_proven,
  r "typeobj-exc-nameerror-reduce" ["BaseException___reduce___impl"]
    "For NameError, as for ImportError and AttributeError, a set name is carried by __reduce__."
    "implementation disagreeing with itself: the three classes with a name member" ``NameErrorReduceKeepsName ``nameErrorReduceKeepsName_refuted
    "typeobj-exc-nameerror-name-not-pickled",
  p "typeobj-exc-nameerror-init" ["NameError_init"]
    "NameError(*args, name=n) keeps args and stores n."
    "exceptions.c:2504-2528" ``NameErrorInitKeyword ``nameErrorInitKeyword_proven,
  p "typeobj-exc-attributeerror-init" ["AttributeError_init"]
    "AttributeError(*args, name=n, obj=o) keeps args and stores n and o."
    "exceptions.c:2587-2613" ``AttributeErrorInitKeywords ``attributeErrorInitKeywords_proven,
  -- OSError
  p "typeobj-exc-oserror-parsed-once" ["oserror_use_init", "OSError_new", "OSError_init"]
    "When oserror_use_init holds, OSError_new parses nothing, keywords included; when it does not, OSError_init does nothing. Arguments are processed exactly once."
    "comment at exceptions.c:2116-2125" ``OsErrorParsedOnce ``osErrorParsedOnce_proven,
  p "typeobj-exc-oserror-remap" ["OSError_new"]
    "OSError_new changes the class only when called on OSError itself, for every errno object and every __hash__ it has."
    "exceptions.c:2158-2167" ``OsErrorRemapOnlyExact ``osErrorRemapOnlyExact_proven,
  p "typeobj-exc-oserror-errnomap" ["_PyExc_InitState"]
    "errnomap has one entry per code on Linux x86-64 and no entry maps to OSError itself."
    "exceptions.c:4476-4503" ``ErrnoMapWellFormed ``errnoMapWellFormed_proven
    "The numbers come from <errno.h> on the difftest platform.",
  p "typeobj-exc-oserror-positions" ["OSError_init"]
    "With 2 to 5 arguments, errno, strerror, filename and filename2 are positions 0, 1, 2 and 4; otherwise none is parsed."
    "oserror_parse_args, exceptions.c:1997-2051" ``OsErrorParsePositions ``osErrorParsePositions_proven,
  p "typeobj-exc-oserror-reduce" ["OSError_reduce"]
    "When args has two items and filename is set, parsing the reduced arguments recovers errno, strerror, filename and filename2."
    "comment at exceptions.c:2329-2330, :2342-2346" ``OsErrorReduceRoundTrip ``osErrorReduceRoundTrip_proven,
  p "typeobj-exc-oserror-str" ["OSError_str"]
    "With no filename and errno or strerror unset, str(e) is BaseException_str."
    "exceptions.c:2316-2319" ``OsErrorStrFallback ``osErrorStrFallback_proven,
  p "typeobj-exc-oserror-written" ["OSError_written_get", "OSError_written_set"]
    "After e.characters_written = n, reading gives n, except that -1 reads as AttributeError: it is the unset value."
    "exceptions.c:2364-2392" ``OsErrorWrittenRoundTrip ``osErrorWrittenRoundTrip_proven,
  -- SyntaxError
  p "typeobj-exc-syntaxerror-init" ["SyntaxError_init"]
    "SyntaxError(msg, info) raises TypeError when info has fewer than 4 or more than 7 items, and when it has exactly 5 (end_offset missing)."
    "exceptions.c:2726-2758" ``SyntaxErrorInitChecks ``syntaxErrorInitChecks_proven,
  p "typeobj-exc-my-basename" ["my_basename"]
    "my_basename(s) is a suffix of s with no separator in it, for every s."
    "exceptions.c:2806-2827" ``MyBasenameSuffix ``myBasenameSuffix_proven,
  p "typeobj-exc-syntaxerror-lineno" ["SyntaxError_str"]
    "The line number printed is the value when it fits in long and -1 otherwise, so __str__ cannot raise OverflowError."
    "comment at exceptions.c:2837-2839" ``SyntaxErrorLinenoInRange ``syntaxErrorLinenoInRange_proven,
  p "typeobj-exc-syntaxerror-plain" ["SyntaxError_str"]
    "With filename and lineno unset, str(e) is str(msg), or 'None' when msg is unset."
    "exceptions.c:2854-2855" ``SyntaxErrorStrPlain ``syntaxErrorStrPlain_proven,
  -- Unicode errors
  p "typeobj-exc-unicode-adjust" ["unicode_error_adjust_start", "unicode_error_adjust_end", "unicode_error_adjust_len", "assert_adjusted_unicode_error_start", "assert_adjusted_unicode_error_end", "assert_adjusted_unicode_error_len"]
    "For every start, end and length, the three adjustments satisfy the three assert_adjusted functions."
    "exceptions.c:3156-3275" ``UnicodeAdjustInRange ``unicodeAdjustInRange_proven,
  p "typeobj-exc-unicode-params" ["_PyUnicodeError_GetParams"]
    "On success, _PyUnicodeError_GetParams returns start, end and slen inside the bounds of the object, for every stored start and end."
    "comment at exceptions.c:3277-3304" ``UnicodeGetParamsInRange ``unicodeGetParamsInRange_proven,
  p "typeobj-exc-unicode-str-bounds" ["UnicodeEncodeError_str", "UnicodeDecodeError_str", "UnicodeTranslateError_str"]
    "The guard of all three __str__ methods implies 0 <= start < len, so the read of one character or byte is in bounds for every assigned start and end."
    "exceptions.c:3693, :3816, :3915" ``UnicodeStrReadInBounds ``unicodeStrReadInBounds_proven,
  p "typeobj-exc-unicode-str-unset" ["UnicodeEncodeError_str", "UnicodeDecodeError_str", "UnicodeTranslateError_str"]
    "With object NULL, all three __str__ methods return '' without reading reason."
    "exceptions.c:3671-3674" ``UnicodeStrUninitialized ``unicodeStrUninitialized_proven,
  p "typeobj-exc-unicode-attr-check" ["check_unicode_error_attribute", "as_unicode_error_attribute"]
    "The attribute check raises TypeError for NULL and for the wrong type, and passes a str (or bytes with as_bytes)."
    "exceptions.c:2988-3021" ``UnicodeAttributeCheck ``unicodeAttributeCheck_proven,
  p "typeobj-exc-unicode-capi" ["check_unicode_error_type", "unicode_error_set_start_impl", "unicode_error_set_end_impl", "unicode_error_get_start_impl", "unicode_error_get_end_impl", "PyUnicodeEncodeError_GetStart", "PyUnicodeDecodeError_GetStart", "PyUnicodeTranslateError_GetStart", "PyUnicodeEncodeError_SetStart", "PyUnicodeDecodeError_SetStart", "PyUnicodeTranslateError_SetStart", "PyUnicodeEncodeError_GetEnd", "PyUnicodeDecodeError_GetEnd", "PyUnicodeTranslateError_GetEnd", "PyUnicodeEncodeError_SetEnd", "PyUnicodeDecodeError_SetEnd", "PyUnicodeTranslateError_SetEnd"]
    "SetStart and SetEnd store the raw value, GetParams returns it clipped, for every kind of error; a non-UnicodeError is a TypeError."
    "exceptions.c:3131-3152, :3411-3535" ``UnicodeCapiStartEnd ``unicodeCapiStartEnd_proven
    "All kinds share these helpers; UKind carries the name and as_bytes.",
  p "typeobj-exc-unicode-capi-attrs" ["unicode_error_get_encoding_impl", "unicode_error_get_object_impl", "unicode_error_get_reason_impl", "unicode_error_set_reason_impl", "PyUnicodeEncodeError_GetEncoding", "PyUnicodeDecodeError_GetEncoding", "PyUnicodeEncodeError_GetObject", "PyUnicodeDecodeError_GetObject", "PyUnicodeTranslateError_GetObject", "PyUnicodeEncodeError_GetReason", "PyUnicodeDecodeError_GetReason", "PyUnicodeTranslateError_GetReason", "PyUnicodeEncodeError_SetReason", "PyUnicodeDecodeError_SetReason", "PyUnicodeTranslateError_SetReason"]
    "The getters reject a non-UnicodeError with TypeError, and SetReason stores the reason."
    "exceptions.c:3073-3122, :3360-3587" ``UnicodeCapiAttributes ``unicodeCapiAttributes_proven,
  p "typeobj-exc-unicode-init-encode" ["UnicodeEncodeError_init"]
    "UnicodeEncodeError.__init__ stores args before it parses them, so a failed parse leaves the new args in place."
    "exceptions.c:3641-3652" ``UnicodeInitArgsFirst ``unicodeInitArgsFirst_proven,
  p "typeobj-exc-unicode-init-others" ["UnicodeDecodeError_init", "UnicodeTranslateError_init"]
    "The same for UnicodeDecodeError and UnicodeTranslateError."
    "exceptions.c:3748-3759, :3870-3879" ``UnicodeInitArgsFirstOthers ``unicodeInitArgsFirstOthers_proven,
  p "typeobj-exc-unicode-create" ["PyUnicodeDecodeError_Create", "_PyUnicodeTranslateError_Create"]
    "The two creators call the class with the formatted arguments, so the constructor's checks apply."
    "exceptions.c:3854-3860, :3960-3966" ``UnicodeCreateCallsClass ``unicodeCreateCallsClass_proven,
  -- MemoryError
  p "typeobj-exc-memoryerror-freelist-bound" ["MemoryError_dealloc", "preallocate_memerrors", "free_preallocated_memerrors", "_PyErr_NoMemory", "get_memory_error"]
    "MemoryError_dealloc keeps the freelist within MEMERRORS_SAVE and ignores subclasses, preallocate_memerrors fills it, teardown empties it, and an empty list with allocation forbidden gives the last-resort error."
    "exceptions.c:4024, :4077-4150" ``MemoryErrorFreelistBound ``memoryErrorFreelistBound_proven,
  r "typeobj-exc-memoryerror-freelist-fresh" ["MemoryError_dealloc", "get_memory_error", "BaseException_clear", "MemoryError_new"]
    "A MemoryError taken from the freelist has __suppress_context__ False, like any new exception."
    "invariant: an object from a freelist is indistinguishable from a fresh one" ``MemoryErrorFreelistFresh ``memoryErrorFreelistFresh_refuted
    "typeobj-exc-memoryerror-freelist-state",
  r "typeobj-exc-memoryerror-new-args" ["MemoryError_new", "get_memory_error"]
    "MemoryError.__new__(MemoryError, *args) keeps args, as BaseException.__new__ and MemoryError subclasses do."
    "implementation disagreeing with itself: the freelist and allocation paths of get_memory_error (exceptions.c:4047, :4062)" ``MemoryErrorNewKeepsArgs ``memoryErrorNewKeepsArgs_refuted
    "typeobj-exc-memoryerror-freelist-state",
  -- BaseExceptionGroup
  p "typeobj-exc-eg-rejects-non-exception" ["BaseExceptionGroup_new"]
    "The first item that is not an exception instance raises ValueError naming its index."
    "exceptions.c:943-949" ``EgRejectsNonException ``egRejectsNonException_proven,
  p "typeobj-exc-eg-no-base-in-exception" ["BaseExceptionGroup_new"]
    "When an item is not an Exception, the class of the new group never derives from Exception."
    "docs: ExceptionGroup 'can only wrap Exception subclasses'; exceptions.c:959-989" ``EgNoBaseInExceptionGroup ``egNoBaseInExceptionGroup_proven,
  p "typeobj-exc-eg-wraps" ["BaseExceptionGroup_new"]
    "With only Exception items, BaseExceptionGroup makes an ExceptionGroup and every other class is kept."
    "docs and exceptions.c:967-974" ``EgWrapsInExceptionGroup ``egWrapsInExceptionGroup_proven,
  p "typeobj-exc-eg-rejects-empty" ["BaseExceptionGroup_new"]
    "An empty sequence of exceptions is a ValueError."
    "exceptions.c:930-935" ``EgRejectsEmpty ``egRejectsEmpty_proven,
  p "typeobj-exc-eg-str" ["BaseExceptionGroup_str"]
    "str(eg) is the message, then the count, with 's' only above one."
    "exceptions.c:1071-1082" ``EgStrFormat ``egStrFormat_proven,
  p "typeobj-exc-eg-init" ["BaseExceptionGroup_init"]
    "__init__ stores args only and leaves message and exceptions; a keyword is a TypeError."
    "exceptions.c:1031-1040" ``EgInitKeepsMembers ``egInitKeepsMembers_proven,
  r "typeobj-exc-eg-repr-in-bounds" ["BaseExceptionGroup_repr"]
    "repr(eg) reads args[1] in bounds after any assignment to args."
    "invariant: no out-of-bounds read; self->args is writable (exceptions.c:359) and read with PyTuple_GET_ITEM at :1103" ``EgReprInBoundsAfterArgsSet ``egReprInBoundsAfterArgsSet_refuted
    "typeobj-exc-eg-repr-args-oob" "Fixed after 3.14.7 by gh-146141; the model stops at the read, which is undefined behaviour.",
  p "typeobj-exc-eg-repr-after-new" ["BaseExceptionGroup_repr", "BaseExceptionGroup_new"]
    "Every group fresh from BaseExceptionGroup_new has two args, so the read is in bounds until args is replaced."
    "narrowing of typeobj-exc-eg-repr-in-bounds" ``EgReprInBoundsAfterNew ``egReprInBoundsAfterNew_proven,
  p "typeobj-exc-eg-repr-saved" ["BaseExceptionGroup_repr"]
    "A saved exceptions_str is used as is."
    "comment at exceptions.c:1092, :910" ``EgReprSavedString ``egReprSavedString_proven,
  p "typeobj-exc-eg-created-through-class" ["BaseExceptionGroup_derive_impl", "_PyExc_CreateExceptionGroup"]
    "derive and _PyExc_CreateExceptionGroup both call BaseExceptionGroup."
    "exceptions.c:1014-1028, :1140-1152" ``EgCreatedThroughClass ``egCreatedThroughClass_proven,
  p "typeobj-exc-eg-bases" ["create_exception_group_class"]
    "ExceptionGroup has the bases (BaseExceptionGroup, Exception), both in its MRO."
    "exceptions.c:1774-1789" ``ExceptionGroupBases ``exceptionGroupBases_proven,
  p "typeobj-exc-subset-metadata" ["exceptiongroup_subset"]
    "After exceptiongroup_subset's copy, the new group has the original's __context__ and __cause__, and its __traceback__ when it has one, including when derive returned the original."
    "comment at exceptions.c:1158-1159; docs for split and subgroup ('preserves ... metadata')" ``SubsetCopiesMetadata ``subsetCopiesMetadata_proven,
  r "typeobj-exc-subset-suppress-context" ["exceptiongroup_subset", "PyException_SetCause"]
    "exceptiongroup_subset also preserves __suppress_context__."
    "comment at exceptions.c:1158-1159 ('with metadata from _orig'); docs for derive ('__traceback__, __cause__, __context__ and __notes__')" ``SubsetCopiesSuppressContext ``subsetCopiesSuppressContext_refuted
    "typeobj-exc-split-sets-suppress-context",
  p "typeobj-exc-subset-checks" ["exceptiongroup_subset"]
    "An empty part is NULL without calling derive; a derive that does not return a group is a TypeError."
    "exceptions.c:1173-1187" ``SubsetChecks ``subsetChecks_proven,
  p "typeobj-exc-matcher-type" ["get_matcher_type"]
    "A non-class callable matches by predicate, an exception class or a tuple of them by type, and an int is the TypeError."
    "exceptions.c:1249-1280" ``GetMatcherTypeClassifies ``getMatcherTypeClassifies_proven,
  p "typeobj-exc-match-by-type" ["exceptiongroup_split_check_match"]
    "For an exception instance and an exception class, matching by type is the subclass test."
    "exceptions.c:1288-1292; PyErr_GivenExceptionMatches" ``MatchByTypeIsSubclass ``matchByTypeIsSubclass_proven,
  p "typeobj-exc-split-partition" ["exceptiongroup_split_recursive", "BaseExceptionGroup_split_impl", "exceptiongroup_split_check_match", "exceptiongroup_subset"]
    "If the matcher is a function of the exception, derive honours its contract and groups stay intact, the leaves of split's two parts are exactly the leaves of the group, each once."
    "docs for BaseExceptionGroup.split" ``SplitPartitionsLeaves ``splitPartitionsLeaves_proven
    "SplitHyp: the matcher is p, derive returns a group of the given exceptions, and user code changes no group's exceptions. Quantifies over every rt with these properties.",
  p "typeobj-exc-split-structure" ["exceptiongroup_split_recursive", "BaseExceptionGroup_split_impl"]
    "Under the same hypotheses each part has the shape specSplit gives: matching exceptions stay whole, a partly matching group is rebuilt around its matching children, and empty groups are dropped."
    "docs for BaseExceptionGroup.subgroup ('preserves the nesting structure')" ``SplitPreservesStructure ``splitPreservesStructure_proven,
  p "typeobj-exc-subgroup-is-split-match" ["BaseExceptionGroup_subgroup_impl", "exceptiongroup_split_recursive"]
    "Under the same hypotheses, the recursion with construct_rest false builds the shape of the match part of the recursion with construct_rest true, and no rest."
    "docs for BaseExceptionGroup.split" ``SubgroupEqualsSplitMatch ``subgroupEqualsSplitMatch_proven,
  p "typeobj-exc-split-identity" ["exceptiongroup_split_recursive", "BaseExceptionGroup_split_impl", "BaseExceptionGroup_subgroup_impl"]
    "When the matcher accepts the exception, the recursion returns it by identity with no rest, for every matcher and rt; split and subgroup then return self."
    "docs for subgroup ('If the condition matches the whole group...'); exceptions.c:1341-1345" ``SplitFullMatchIdentity ``splitFullMatchIdentity_proven,
  p "typeobj-exc-split-leaf" ["exceptiongroup_split_recursive"]
    "A leaf that does not match goes to the rest, and nowhere when no rest is asked for."
    "exceptions.c:1346-1352" ``SplitLeafNoMatch ``splitLeafNoMatch_proven,
  p "typeobj-exc-leaf-ids" ["collect_exception_group_leaf_ids"]
    "collect_exception_group_leaf_ids ignores None and adds a leaf as itself."
    "exceptions.c:1507-1524" ``CollectLeafIdsBase ``collectLeafIdsBase_proven,
  p "typeobj-exc-instance-ids" ["exceptiongroup_split_check_match", "exception_group_projection"]
    "The instance-ids matcher never accepts a group, and accepts a leaf exactly when it is in the set."
    "exceptions.c:1303-1315" ``InstanceIdsMatchLeaves ``instanceIdsMatchLeaves_proven,
  p "typeobj-exc-prep-reraise-short" ["_PyExc_PrepReraiseStar"]
    "No exceptions give None, and for a naked exception the first entry is returned as is."
    "exceptions.c:1628-1642" ``PrepReraiseStarShortPaths ``prepReraiseStarShortPaths_proven,
  p "typeobj-exc-prep-reraise-validates" ["PyUnstable_Exc_PrepReraiseStar"]
    "The public wrapper rejects a non-exception orig, a non-list excs and an orig without traceback before running."
    "exceptions.c:1713-1740" ``PrepReraiseStarValidates ``prepReraiseStarValidates_proven,
  p "typeobj-exc-same-metadata-refl" ["is_same_exception_metadata"]
    "An exception has the same metadata as itself."
    "exceptions.c:1587-1599" ``SameMetadataReflexive ``sameMetadataReflexive_proven,
  r "typeobj-exc-same-metadata-notes" ["is_same_exception_metadata", "_PyExc_PrepReraiseStar", "exception_group_projection"]
    "Two exceptions that is_same_exception_metadata calls the same have the same __notes__."
    "exceptions.c:1595 compares notes; PEP 678 defines notes as __notes__" ``SameMetadataComparesNotes ``sameMetadataComparesNotes_refuted
    "typeobj-exc-except-star-drops-notes"
]

end PyLean.TypeObj
