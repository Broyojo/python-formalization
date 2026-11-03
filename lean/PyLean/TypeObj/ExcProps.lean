import PyLean.Registry
import PyLean.TypeObj.ExcPropsGroup
import PyLean.TypeObj.ExcPropsGroup2
import PyLean.TypeObj.ExcPropsBase2
import PyLean.TypeObj.ExcPropsRest2
import PyLean.TypeObj.ExcPropsOsStr
import PyLean.TypeObj.ExcPropsSetstateC
import PyLean.TypeObj.ExcPropsUnicode2
import PyLean.TypeObj.ExcPropsUnicode3
import PyLean.TypeObj.ExcPropsSplitTotal

/-!
The registry of `Objects/exceptions.c` (CPython 3.15.2; line numbers are that file's). The
properties live in `ExcPropsBase`, `ExcPropsBase2`, `ExcPropsRest`, `ExcPropsRest2`, `ExcPropsSplit`,
`ExcPropsGroup`, `ExcPropsGroup2` and `ExcPropsOsStr`, with the hypotheses of each explained in its
docstring. The model is `ExcCore`, `ExcGroup`, `ExcOs`, `ExcOsStrC`, `ExcUnicode`, `ExcFreelist`, and
`Exceptions` for the dispatch.
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

private def o (id : String) (fns : List String) (statement source : String)
    (prop : Lean.Name) (notes : String) : Entry :=
  { id := id, pyFile := src, pyFns := fns, statement := statement, source := source,
    status := .open, prop := prop, notes := notes }

def excEntries : List Entry := [
  -- BaseException
  p "typeobj-exc-str-args" []
    "For every exception and every rt, str(e) is '' with no args, str(args[0]) with one, and str(args) otherwise."
    "exceptions.c:162-182" ``BaseExceptionStrArgs ``baseExceptionStrArgs_proven,
  p "typeobj-exc-repr-args" []
    "repr(e) is Name(repr(args[0])) with one argument and Name + repr(args) otherwise, where Name is the last dotted part of tp_name."
    "exceptions.c:184-202" ``BaseExceptionReprArgs ``baseExceptionReprArgs_proven,
  p "typeobj-exc-keyerror-str" []
    "str(KeyError(x)) is repr(x) for one argument; any other argument count behaves as BaseException_str."
    "comment at exceptions.c:3021-3029; KeyError_str :3018-3035" ``KeyErrorStrOneArg ``keyErrorStrOneArg_proven,
  p "typeobj-exc-vectorcall-twin" ["BaseException_new", "BaseException_init", "BaseException_vectorcall"]
    "With no keywords, BaseException_vectorcall builds an object with the same class and fields as tp_new followed by tp_init."
    "twin paths: _PyExc_InitTypes installs the vectorcall on classes with both default slots (exceptions.c:4502-4506)"
    ``BaseExceptionVectorcallTwin ``baseExceptionVectorcallTwin_proven,
  p "typeobj-exc-reduce" ["BaseException___reduce___impl"]
    "e.__reduce__() is (type(e), e.args) plus the instance dict exactly when a dict exists."
    "exceptions.c:211-219" ``BaseExceptionReduceShape ``baseExceptionReduceShape_proven,
  p "typeobj-exc-setstate" ["BaseException___setstate___impl"]
    "__setstate__(None) does nothing, a non-dict is a TypeError, a non-str first key is the TypeError of setattr, and with a __setattr__ that leaves the dict alone the result is setattr of every item in order."
    "exceptions.c:234-258" ``BaseExceptionSetstateLive ``baseExceptionSetstateLive_proven
    "The interpreter's dict has no dummy slots, so a __setattr__ that changes the state dict is stated on the real table instead: typeobj-exc-setstate-table.",
  p "typeobj-exc-setstate-table" ["BaseException___setstate___impl"]
    "Over the dict table of dictobject.c, each turn of __setstate__ calls PyDict_Next on the dict as it now is from the last position, sets the attribute through __setattr__ (whose insertions, resizes and deletions the next turn sees), and stops at the end or at a raise; with a __setattr__ that leaves the dict alone it sets exactly the items of the walk, in order."
    "exceptions.c:246-255; PyDict_Next and insertion_resize, Objects/dictobject.c (PyLean.DictSet)" ``SetstateC.SetstateTableSteps ``SetstateC.setstateTableSteps_proven,
  p "typeobj-exc-setstate-table-examples" []
    "As on 3.15.2: deleting 'a' while setting it still sets a, b and c (the deletion leaves a dummy), and an insertion that resizes a table holding two dummies skips the two keys after the current one."
    "CPython 3.15.2 runs of both programs" ``SetstateC.SetstateTableExamples ``SetstateC.setstateTableExamples_proven
    "Behaviour on record, not a bug: PyDict_Next under mutation has no promised result.",
  p "typeobj-exc-traceback-setter" ["BaseException___traceback___set_impl", "BaseException_with_traceback_impl"]
    "__traceback__ accepts only a traceback or None (TypeError otherwise, world unchanged), cannot be deleted, and with_traceback returns self."
    "exceptions.c:270-278, 391-412" ``TracebackSetterChecks ``tracebackSetterChecks_proven,
  p "typeobj-exc-cause-suppress" ["BaseException___cause___set_impl", "PyException_SetCause"]
    "Every successful assignment to __cause__, None included, stores the value and sets __suppress_context__."
    "docs (Built-in Exceptions: raising and handling) and exceptions.c:481-501, 546-554" ``CauseSetsSuppressContext ``causeSetsSuppressContext_proven,
  p "typeobj-exc-context-set" ["BaseException___context___set_impl", "PyException_SetContext"]
    "Assigning __context__ stores the value (None as NULL) and leaves __cause__ and __suppress_context__ alone."
    "exceptions.c:437-456, 567-573" ``ContextSetKeepsSuppress ``contextSetKeepsSuppress_proven,
  p "typeobj-exc-suppress-bool" []
    "__suppress_context__ stores True or False, rejects any other value with TypeError, and cannot be deleted."
    "BaseException_members, exceptions.c:601-605; Py_T_BOOL in Python/structmember.c:180"
    ``SuppressContextOnlyBool ``suppressContextOnlyBool_proven,
  p "typeobj-exc-args-set" ["BaseException_args_set_impl", "BaseException_args_get_impl"]
    "e.args = t stores t's items for a tuple t; args cannot be deleted."
    "exceptions.c:343-372" ``ArgsSetStoresTuple ``argsSetStoresTuple_proven,
  p "typeobj-exc-add-note" ["BaseException_add_note_impl"]
    "add_note(x) raises TypeError for a non-str x before anything else; when __notes__ is a list, however it was found, the list gains x at the end."
    "exceptions.c:289-318" ``AddNoteAppends ``addNoteAppends_proven,
  p "typeobj-exc-capi-roundtrip" []
    "PyException_SetCause, SetContext, SetArgs and SetTraceback are read back unchanged by the matching getters."
    "exceptions.c:514-592" ``PyExceptionApiRoundTrip ``pyExceptionApiRoundTrip_proven,
  p "typeobj-exc-capi-misc" []
    "_PyException_AddNote rejects a non-exception with TypeError before calling add_note; PyExceptionClass_Name is tp_name."
    "exceptions.c:594-599, 4645-4658" ``PyExceptionMiscApi ``pyExceptionMiscApi_proven,
  -- StopIteration, SystemExit
  p "typeobj-exc-stopiteration-value" ["StopIteration_init"]
    "After StopIteration.__init__, value is args[0], or None with no args, on every call."
    "exceptions.c:749-765" ``StopIterationValue ``stopIterationValue_proven,
  p "typeobj-exc-systemexit-code" ["SystemExit_init"]
    "After SystemExit.__init__, code is unchanged with no args, args[0] with one, and the tuple otherwise."
    "exceptions.c:814-832" ``SystemExitCode ``systemExitCode_proven
    "Unlike StopIteration, code is not reset by a second __init__() with no arguments.",
  -- ImportError, NameError, AttributeError
  p "typeobj-exc-importerror-msg" ["ImportError_init", "ImportError_str"]
    "ImportError(m) sets msg to m; str(e) is msg when msg is an exact str, BaseException_str otherwise."
    "exceptions.c:1803-1837, 1869-1877" ``ImportErrorMsgStr ``importErrorMsgStr_proven,
  p "typeobj-exc-reduce-keeps-name" ["ImportError_getstate", "ImportError_reduce", "AttributeError_getstate", "AttributeError_reduce"]
    "The state dict of ImportError.__reduce__ and AttributeError.__reduce__ holds a set name; AttributeError's also holds args."
    "exceptions.c:1879-1925, 2719-2760" ``ReduceKeepsNameImportAttr ``reduceKeepsNameImportAttr_proven,
  r "typeobj-exc-nameerror-reduce" ["BaseException___reduce___impl"]
    "For NameError, as for ImportError and AttributeError, a set name is carried by __reduce__."
    "implementation disagreeing with itself: the three classes with a name member" ``NameErrorReduceKeepsName ``nameErrorReduceKeepsName_refuted
    "typeobj-exc-nameerror-name-not-pickled",
  p "typeobj-exc-nameerror-init" ["NameError_init"]
    "NameError(*args, name=n) keeps args and stores n."
    "exceptions.c:2580-2605" ``NameErrorInitKeyword ``nameErrorInitKeyword_proven,
  p "typeobj-exc-attributeerror-init" ["AttributeError_init"]
    "AttributeError(*args, name=n, obj=o) keeps args and stores n and o."
    "exceptions.c:2663-2690" ``AttributeErrorInitKeywords ``attributeErrorInitKeywords_proven,
  -- OSError
  p "typeobj-exc-oserror-parsed-once" ["oserror_use_init"]
    "When oserror_use_init holds, OSError_new parses nothing, keywords included; when it does not, OSError_init does nothing. Arguments are processed exactly once."
    "comment at exceptions.c:2186-2195; OSError_new :2215, :2248; OSError_init :2281-2283" ``OsErrorParsedOnce ``osErrorParsedOnce_proven,
  p "typeobj-exc-oserror-remap" []
    "OSError_new changes the class only when called on OSError itself, for every errno object and every __hash__ it has."
    "exceptions.c:2227-2237" ``OsErrorRemapOnlyExact ``osErrorRemapOnlyExact_proven,
  p "typeobj-exc-oserror-errnomap" []
    "errnomap has one entry per code on Linux x86-64 and no entry maps to OSError itself."
    "exceptions.c:4547-4581" ``ErrnoMapWellFormed ``errnoMapWellFormed_proven
    "The numbers come from <errno.h> on the difftest platform.",
  p "typeobj-exc-oserror-positions" []
    "With 2 to 5 arguments, errno, strerror, filename and filename2 are positions 0, 1, 2 and 4; otherwise none is parsed."
    "oserror_parse_args, exceptions.c:2066-2121" ``OsErrorParsePositions ``osErrorParsePositions_proven,
  p "typeobj-exc-oserror-reduce" []
    "When args has two items and filename is set, parsing the reduced arguments recovers errno, strerror, filename and filename2."
    "comment at exceptions.c:2399-2400; OSError_reduce :2401-2421" ``OsErrorReduceRoundTrip ``osErrorReduceRoundTrip_proven,
  p "typeobj-exc-oserror-str" ["OSError_str"]
    "For every rt: with filename set, str(e) is '[Errno e] s: f' plus ' -> f2' when filename2 is set; without it but with errno and strerror it is '[Errno e] s'; otherwise BaseException_str. The conversions run in order on the values read at the start, and the first raise is the result."
    "exceptions.c:2346-2390" ``OsErrorStrFormats ``osErrorStrFormats_proven
    "This is the interpreter's OSError_str, whose heap never frees: it reads the members once, as 3.15.2 and main both do. On 3.15.2 it describes CPython only while no conversion drops the last reference to a member not yet formatted; when one does, 3.15.2 reads freed memory instead (typeobj-exc-oserror-str-no-crash, over the reference-counted model). Main, which takes strong references, matches it in every case.",
  p "typeobj-exc-oserror-str-branches" ["OSError_str"]
    "In a reachable C state where no __str__ or __repr__ assigns a member, OSError_str is '[Errno e] s: f -> f2', '[Errno e] s: f', '[Errno e] s' or BaseException_str by which members are set, and a raising str(errno) is the result."
    "exceptions.c:2346-2390 (3.15.2: borrowed members passed to PyUnicode_FromFormat, :2372-2388)" ``OsStrC.OsErrorStrBranches ``OsStrC.osErrorStrBranches_proven,
  r "typeobj-exc-oserror-str-no-crash" ["OSError_str"]
    "From every reachable state, whatever member assignments the __str__ and __repr__ of the members make, OSError_str never reads a freed object."
    "invariant: no crash from pure-Python code" ``OsStrC.OsErrorStrNoCrash ``OsStrC.osErrorStrNoCrash_refuted
    "typeobj-exc-oserror-str-borrowed-free"
    "Duplicate of gh-160773, fixed by gh-160822 on main and gh-160884 on the 3.15 branch after 3.15.2. Counterexample: an errno whose __str__ sets e.filename = None, with the filename held only by the member.",
  p "typeobj-exc-oserror-str-fixed-on-cex" []
    "With the strong references of gh-160822, the counterexample state of typeobj-exc-oserror-str-no-crash formats as '[Errno 1] s: fn', what main prints for the reproducer."
    "main's OSError_str (strong references, then the same formats)" ``OsStrC.OsErrorStrFixedOnUaf ``OsStrC.osErrorStrFixedOnUaf_proven,
  o "typeobj-exc-oserror-str-fixed-no-crash" []
    "The fixed OSError_str never reads a freed object from a reachable state."
    "main's OSError_str" ``OsStrC.OsErrorStrFixedNoCrash
    "Open: needs a reference-count invariant through runAct (counts cover members, args and pinned references). The 3.15.2 version is refuted.",
  p "typeobj-exc-oserror-written" ["OSError_written_get", "OSError_written_set"]
    "After e.characters_written = n, reading gives n, except that -1 reads as AttributeError: it is the unset value."
    "exceptions.c:2433-2462" ``OsErrorWrittenRoundTrip ``osErrorWrittenRoundTrip_proven,
  -- BaseException: success values and refusals (ExcPropsBase2)
  p "typeobj-exc-new-stores" ["BaseException_new"]
    "BaseException.__new__(t, *args) makes an object of class t with those args, NULL traceback, cause and context, suppress_context false, and no dict, ignoring keywords."
    "exceptions.c:51-77" ``BaseExceptionNewStores ``baseExceptionNewStores_proven,
  p "typeobj-exc-init-kw" ["BaseException_init"]
    "BaseException.__init__ refuses any keyword with '<tp_name cut to 200 bytes>() takes no keyword arguments' before changing anything, and otherwise replaces args only."
    "exceptions.c:79-88; _PyArg_NoKeywords, Python/getargs.c:2942-2959; %.200s, Objects/unicodeobject.c:2623-2660" ``BaseExceptionInitKw ``baseExceptionInitKw_proven,
  p "typeobj-exc-vectorcall-kw" ["BaseException_vectorcall"]
    "BaseException_vectorcall refuses keyword names with the whole tp_name before allocating, and with none builds what BaseException_new builds."
    "exceptions.c:91-121; _PyArg_NoKwnames, Python/getargs.c:2978-2993" ``BaseExceptionVectorcallKw ``baseExceptionVectorcallKw_proven,
  p "typeobj-exc-traceback-set-stores" ["BaseException___traceback___set_impl", "BaseException_with_traceback_impl"]
    "__traceback__ = tb stores tb and = None clears it, with every other field kept and the getter reading it back; with_traceback(tb) does the same and returns self, and refuses anything else with TypeError."
    "exceptions.c:270-278, 391-412" ``TracebackSetStores ``tracebackSetStores_proven,
  p "typeobj-exc-chain-refusals" ["BaseException___context___set_impl", "BaseException___cause___set_impl"]
    "del e.__context__ and del e.__cause__ are TypeErrors, as is assigning a non-exception; the world is unchanged."
    "exceptions.c:437-456, 481-501" ``ChainSetRefusals ``chainSetRefusals_proven,
  p "typeobj-exc-args-set-get" ["BaseException_args_set_impl", "BaseException_args_get_impl"]
    "e.args = x stores tuple(x) and e.args reads it back: an exact tuple as is, an exact list's items, any other iterable through iter/next in order; a raise from iter or next is the result with no write."
    "exceptions.c:334-365; PySequence_Tuple, Objects/abstract.c:2005-2078" ``ArgsSetGet ``argsSetGet_proven,
  p "typeobj-exc-add-note-branches" ["BaseException_add_note_impl"]
    "add_note creates __notes__ as a new list through setattr when it is missing and appends to it; a failed lookup or setattr is the result; a __notes__ that is not a list is 'Cannot add note: __notes__ is not a list'."
    "exceptions.c:289-318" ``AddNoteBranches ``addNoteBranches_proven,
  p "typeobj-exc-clear-fields" ["BaseException_clear", "MemoryError_dealloc", "get_memory_error"]
    "A MemoryError reused from the freelist has no args, notes, traceback, cause or context, and keeps suppress_context and the members of the dead object."
    "exceptions.c:124-135, 4169-4196, 4111-4140" ``BaseExceptionClearFields ``baseExceptionClearFields_proven,
  -- BaseExceptionGroup (ExcPropsGroup2)
  p "typeobj-exc-eg-new-refusals" ["BaseExceptionGroup_new"]
    "BaseExceptionGroup.__new__ refuses, before any user code, a count other than two, a non-str message, and a second argument that is not a sequence, with the getargs messages."
    "exceptions.c:892-904" ``EgNewRefusals ``egNewRefusals_proven,
  p "typeobj-exc-eg-new-stores" ["BaseExceptionGroup_new"]
    "On success BaseExceptionGroup.__new__ stores args as passed, the message, the items of tuple(exceptions) and, for a sequence other than a list or tuple, the repr taken before the conversion; the class is the one the checks chose."
    "exceptions.c:906-1002" ``EgNewStores ``egNewStores_proven,
  p "typeobj-exc-eg-isinstance" ["BaseExceptionGroup_new"]
    "isinstance(x, Exception) in BaseExceptionGroup_new is true without running code for an Exception, and false for another exception whose __class__ is its own type."
    "exceptions.c:946; object_isinstance, Objects/abstract.c:2603" ``EgIsInstanceException ``egIsInstanceException_proven,
  p "typeobj-exc-eg-nested-flag" ["BaseExceptionGroup_new"]
    "The nested flag is true exactly when some item's isinstance(x, Exception) is false."
    "exceptions.c:933-953" ``EgNestedFlag ``egNestedFlag_proven,
  p "typeobj-exc-eg-choose-nested" ["BaseExceptionGroup_new"]
    "With a nested BaseException, ExceptionGroup and its Exception subclasses refuse (%.200s of the name), BaseExceptionGroup and its other subclasses keep their class."
    "exceptions.c:955-985" ``EgChooseNested ``egChooseNested_proven,
  p "typeobj-exc-eg-repr-tuple" ["BaseExceptionGroup_repr"]
    "With no saved string and two args whose second is not a list, repr(eg) shows eg.exceptions as a tuple."
    "exceptions.c:1108-1110, 1119-1122" ``EgReprTupleForm ``egReprTupleForm_proven,
  p "typeobj-exc-check-match-class" ["exceptiongroup_split_check_match"]
    "Matching by one exception class is issubclass(type(exc), cls), with no code run."
    "exceptions.c:1284-1288; PyErr_GivenExceptionMatches, Python/errors.c" ``SplitCheckMatchClass ``splitCheckMatchClass_proven,
  p "typeobj-exc-eg-repr-list" ["BaseExceptionGroup_repr"]
    "With no saved string, two args and a list second arg, repr(eg) shows a new list of eg.exceptions."
    "exceptions.c:1098-1107, 1119-1122" ``EgReprListForm ``egReprListForm_proven,
  p "typeobj-exc-matcher-refuses" ["get_matcher_type"]
    "get_matcher_type refuses a tuple holding any non-class, and any value that is neither a non-class callable, an exception class nor a tuple."
    "exceptions.c:1260-1275" ``GetMatcherTypeRefuses ``getMatcherTypeRefuses_proven,
  p "typeobj-exc-check-match-branches" ["exceptiongroup_split_check_match"]
    "The predicate matcher calls the predicate with the exception and answers bool() of the result, a raise from either being the result; matching by type tests each class of a tuple."
    "exceptions.c:1283-1298" ``SplitCheckMatchBranches ``splitCheckMatchBranches_proven,
  p "typeobj-exc-subset-notes" ["exceptiongroup_subset"]
    "After derive and the metadata copy, a sequence __notes__ of the original is copied into a new list and set on the part with setattr; a failed read or set is the result; a missing or non-sequence __notes__ is skipped."
    "exceptions.c:1198-1226" ``SubsetCopiesNotes ``subsetCopiesNotes_proven,
  p "typeobj-exc-projection-leaf-group" ["exception_group_projection"]
    "On a group of leaves, exception_group_projection is exceptiongroup_subset of the leaves whose ids were collected from keep, in order (None when none are)."
    "exceptions.c:1542-1578" ``ProjectionLeafGroup ``projectionLeafGroup_proven,
  p "typeobj-exc-same-metadata-iff" ["is_same_exception_metadata"]
    "is_same_exception_metadata is true exactly when notes, traceback, cause and context are the same objects or both NULL."
    "exceptions.c:1580-1593" ``SameMetadataIff ``sameMetadataIff_proven,
  p "typeobj-exc-prep-reraise-group" ["_PyExc_PrepReraiseStar"]
    "On a group, _PyExc_PrepReraiseStar projects the re-raised entries onto orig; with nothing raised that is the result, otherwise the projection (if not None) is appended to the raised list and a list of two or more is wrapped by _PyExc_CreateExceptionGroup(\"\", list); a failing projection is the result."
    "exceptions.c:1638-1702" ``PrepReraiseStarGroup ``prepReraiseStarGroup_proven,
  p "typeobj-exc-prep-reraise-handoff" ["PyUnstable_Exc_PrepReraiseStar"]
    "PyUnstable_Exc_PrepReraiseStar names the index of the first item that is neither an exception nor None, and when all pass and orig has a traceback it is _PyExc_PrepReraiseStar(orig, excs)."
    "exceptions.c:1716-1737" ``PrepReraiseStarHandOff ``prepReraiseStarHandOff_proven,
  -- ImportError and OSError (ExcPropsRest2)
  p "typeobj-exc-importerror-init-kw" ["ImportError_init"]
    "ImportError.__init__ sets args, each of name, path and name_from to its keyword or NULL, and msg to the only argument or NULL, on every call; an unexpected keyword is a TypeError, with the 'Did you mean' suggestion of _Py_CalculateSuggestions when there is one, raised after args was replaced."
    "exceptions.c:1803-1837; Python/getargs.c:1939-1999; Python/suggestions.c:16-180" ``ImportErrorInitKw ``importErrorInitKw_proven,
  p "typeobj-exc-kw-suggestions" []
    "The modelled _Py_CalculateSuggestions gives, for the keyword names of ImportError, NameError and AttributeError, the suggestions 3.15.2 prints for nam, Name, nme, named, pat, path_, name_fro, nameFrom, ob, obj_ and none for zzq, x, naem, é, o, zz, obj."
    "CPython 3.15.2 runs" ``KwSuggestionsMatch ``kwSuggestionsMatch_proven,
  p "typeobj-exc-name-attr-unexpected" ["NameError_init", "AttributeError_init"]
    "NameError and AttributeError refuse an unknown keyword with the getargs message and suggestion, after args was replaced."
    "exceptions.c:2580-2605, 2663-2690; Python/getargs.c:1939-1999" ``NameAttrInitUnexpected ``nameAttrInitUnexpected_proven,
  p "typeobj-exc-importerror-getstate-reduce" ["ImportError_getstate", "ImportError_reduce"]
    "With name, path or name_from set, the state is a new copy of the instance dict with the set members over it; otherwise the instance dict itself or None; __reduce__ is (type, args) for a None state and (type, args, state) otherwise."
    "exceptions.c:1879-1925" ``ImportErrorGetstateReduce ``importErrorGetstateReduce_proven,
  p "typeobj-exc-oserror-use-init-slots" ["oserror_use_init"]
    "oserror_use_init is true exactly when tp_init is not OSError_init and tp_new is OSError_new."
    "exceptions.c:2183-2201" ``OsErrorUseInitSlots ``osErrorUseInitSlots_proven,
  p "typeobj-exc-oserror-init-use-init" ["OSError_init"]
    "When oserror_use_init holds, OSError.__init__ refuses keywords with the %.200s message and otherwise is oserror_init on the parsed arguments."
    "exceptions.c:2271-2308" ``OsErrorInitUseInit ``osErrorInitUseInit_proven,
  p "typeobj-exc-oserror-init-effects" ["OSError_init"]
    "oserror_init with 3-5 arguments and a non-None filename stores errno, strerror, filename (and a non-None filename2) and cuts args to two; with fewer than 2 or more than 5 it clears errno and strerror and keeps args; an exact BlockingIOError with an int third argument stores characters_written and keeps args."
    "exceptions.c:2123-2176" ``OsErrorInitEffects ``osErrorInitEffects_proven,
  p "typeobj-exc-oserror-init-two-or-none" ["OSError_init"]
    "oserror_init with exactly two arguments stores errno and strerror and keeps args; with 3-5 arguments and a None filename it stores errno and strerror, skips filename and filename2, and keeps args whole."
    "exceptions.c:2136, 2165-2172" ``OsErrorInitTwoOrNone ``osErrorInitTwoOrNone_proven,
  p "typeobj-exc-oserror-written-set" ["OSError_written_set"]
    "del e.characters_written is AttributeError when unset and resets it otherwise; an int outside Py_ssize_t is a ValueError with nothing stored."
    "exceptions.c:2444-2462" ``OsErrorWrittenSetBranches ``osErrorWrittenSetBranches_proven,
  -- SyntaxError
  p "typeobj-exc-syntaxerror-init" ["SyntaxError_init"]
    "SyntaxError(msg, info) raises TypeError when info has fewer than 4 or more than 7 items, and when it has exactly 5 (end_offset missing)."
    "exceptions.c:2790-2837" ``SyntaxErrorInitChecks ``syntaxErrorInitChecks_proven,
  p "typeobj-exc-my-basename" ["my_basename"]
    "my_basename(s) is a suffix of s with no separator in it, for every s."
    "exceptions.c:2882-2904" ``MyBasenameSuffix ``myBasenameSuffix_proven,
  p "typeobj-exc-syntaxerror-lineno" ["SyntaxError_str"]
    "The line number printed is the value when it fits in long and -1 otherwise, so __str__ cannot raise OverflowError."
    "comment at exceptions.c:2914-2916; :2936-2948" ``SyntaxErrorLinenoInRange ``syntaxErrorLinenoInRange_proven,
  p "typeobj-exc-syntaxerror-plain" ["SyntaxError_str"]
    "When filename is not a str (NULL or any other value) and lineno is not an exact int (NULL, True, a float), str(e) is str(msg), or 'None' when msg is unset."
    "exceptions.c:2931-2932" ``SyntaxErrorStrPlainAll ``syntaxErrorStrPlainAll_proven,
  p "typeobj-exc-syntaxerror-info-tuple" ["SyntaxError_init"]
    "SyntaxError(msg, info) parses an exact list info as the tuple of its items, and a non-iterable info is the TypeError of iter()."
    "exceptions.c:2805; PySequence_Tuple, Objects/abstract.c:2005-2078" ``SyntaxErrorInfoTuple ``syntaxErrorInfoTuple_proven,
  p "typeobj-exc-unicode-capi-refusals" ["PyUnicodeEncodeError_SetStart", "PyUnicodeDecodeError_SetStart", "PyUnicodeTranslateError_SetStart", "PyUnicodeEncodeError_GetEnd", "PyUnicodeDecodeError_GetEnd", "PyUnicodeTranslateError_GetEnd", "PyUnicodeEncodeError_SetEnd", "PyUnicodeDecodeError_SetEnd", "PyUnicodeTranslateError_SetEnd", "PyUnicodeEncodeError_SetReason", "PyUnicodeDecodeError_SetReason", "PyUnicodeTranslateError_SetReason"]
    "SetStart, GetEnd, SetEnd and SetReason of every kind refuse a non-UnicodeError with 'expecting a <Kind> object, got <type>' before anything else."
    "exceptions.c:3127-3137, 3523-3612, 3643-3664" ``UnicodeCapiRefusals ``unicodeCapiRefusals_proven,
  p "typeobj-exc-unicode-getreason-refusals" ["unicode_error_get_reason_impl", "PyUnicodeEncodeError_GetReason", "PyUnicodeDecodeError_GetReason", "PyUnicodeTranslateError_GetReason"]
    "GetReason refuses a NULL reason ('UnicodeError 'reason' attribute is not set') and a non-str one ('... must be a string')."
    "exceptions.c:3175-3180, 3093-3098" ``UnicodeGetReasonRefusals ``unicodeGetReasonRefusals_proven,
  p "typeobj-exc-unicode-encode-parse" ["UnicodeEncodeError_init"]
    "UnicodeEncodeError.__init__ parses UUnnU: a non-str encoding, object or reason is 'argument i must be str, not T'; an int start outside Py_ssize_t is the OverflowError; start and end are stored as the integers n gives (through __index__)."
    "exceptions.c:3724-3736; getargs U and n" ``UnicodeEncodeInitParse ``unicodeEncodeInitParse_proven,
  p "typeobj-exc-unicode-decode-parse" ["UnicodeDecodeError_init"]
    "UnicodeDecodeError.__init__ parses UOnnU: non-str encoding or reason refused with its position, start through n with the OverflowError."
    "exceptions.c:3831-3835; getargs U and n" ``UnicodeDecodeInitParse ``unicodeDecodeInitParse_proven,
  p "typeobj-exc-unicode-translate-parse" ["UnicodeTranslateError_init"]
    "UnicodeTranslateError.__init__ parses UnnU: non-str object or reason refused with its position, start through n with the OverflowError, and start and end stored as n gives them."
    "exceptions.c:3953-3962; getargs U and n" ``UnicodeTranslateInitParse ``unicodeTranslateInitParse_proven,
  -- Unicode errors
  p "typeobj-exc-unicode-adjust" ["unicode_error_adjust_start", "unicode_error_adjust_end", "unicode_error_adjust_len", "assert_adjusted_unicode_error_start", "assert_adjusted_unicode_error_end", "assert_adjusted_unicode_error_len"]
    "For every start, end and length, the three adjustments satisfy the three assert_adjusted functions."
    "exceptions.c:3242-3348" ``UnicodeAdjustInRange ``unicodeAdjustInRange_proven,
  p "typeobj-exc-unicode-params" []
    "On success, _PyUnicodeError_GetParams returns start, end and slen inside the bounds of the object, for every stored start and end."
    "comment above _PyUnicodeError_GetParams, exceptions.c:3354-3381; :3382-3431" ``UnicodeGetParamsInRange ``unicodeGetParamsInRange_proven,
  p "typeobj-exc-unicode-str-bounds" ["UnicodeEncodeError_str", "UnicodeDecodeError_str", "UnicodeTranslateError_str"]
    "The guard of all three __str__ methods implies 0 <= start < len, so the read of one character or byte is in bounds for every assigned start and end."
    "exceptions.c:3770, 3893, 3992" ``UnicodeStrReadInBounds ``unicodeStrReadInBounds_proven,
  p "typeobj-exc-unicode-str-unset" ["UnicodeEncodeError_str", "UnicodeDecodeError_str", "UnicodeTranslateError_str"]
    "With object NULL, all three __str__ methods return '' without reading reason."
    "exceptions.c:3748, 3871, 3974" ``UnicodeStrUninitialized ``unicodeStrUninitialized_proven,
  p "typeobj-exc-unicode-attr-check" ["check_unicode_error_attribute", "as_unicode_error_attribute"]
    "The attribute check raises TypeError for NULL and for the wrong type, and passes a str (or bytes with as_bytes)."
    "exceptions.c:3064-3098" ``UnicodeAttributeCheck ``unicodeAttributeCheck_proven,
  p "typeobj-exc-unicode-capi" ["check_unicode_error_type", "unicode_error_set_start_impl", "unicode_error_set_end_impl", "unicode_error_get_start_impl", "unicode_error_get_end_impl"]
    "SetStart and SetEnd store the raw value, GetParams returns it clipped, for every kind of error; a non-UnicodeError is a TypeError."
    "exceptions.c:3127-3137, 3207-3229, 3487-3612" ``UnicodeCapiStartEnd ``unicodeCapiStartEnd_proven
    "All kinds share these helpers; UKind carries the name and as_bytes.",
  p "typeobj-exc-unicode-capi-attrs" ["unicode_error_get_encoding_impl", "unicode_error_get_object_impl", "unicode_error_get_reason_impl", "unicode_error_set_reason_impl"]
    "The getters reject a non-UnicodeError with TypeError, and SetReason stores the reason."
    "exceptions.c:3149-3199, 3437-3476, 3617-3664" ``UnicodeCapiAttributes ``unicodeCapiAttributes_proven,
  p "typeobj-exc-unicode-init-encode" ["UnicodeEncodeError_init"]
    "UnicodeEncodeError.__init__ stores args before it parses them, so a failed parse leaves the new args in place."
    "exceptions.c:3715-3738" ``UnicodeInitArgsFirst ``unicodeInitArgsFirst_proven,
  p "typeobj-exc-unicode-init-others" ["UnicodeDecodeError_init", "UnicodeTranslateError_init"]
    "The same for UnicodeDecodeError and UnicodeTranslateError."
    "exceptions.c:3822-3861, 3944-3964" ``UnicodeInitArgsFirstOthers ``unicodeInitArgsFirstOthers_proven,
  p "typeobj-exc-unicode-create" ["PyUnicodeDecodeError_Create", "_PyUnicodeTranslateError_Create"]
    "The two creators call the class with the formatted arguments, so the constructor's checks apply."
    "exceptions.c:3930-3937, 4036-4043" ``UnicodeCreateCallsClass ``unicodeCreateCallsClass_proven,
  -- MemoryError
  p "typeobj-exc-memoryerror-freelist-bound" ["MemoryError_dealloc", "preallocate_memerrors", "_PyErr_NoMemory", "get_memory_error"]
    "MemoryError_dealloc keeps the freelist within MEMERRORS_SAVE and ignores subclasses, preallocate_memerrors fills it, teardown empties it, and an empty list with allocation forbidden gives the last-resort error."
    "exceptions.c:4101, 4111-4227" ``MemoryErrorFreelistBound ``memoryErrorFreelistBound_proven,
  r "typeobj-exc-memoryerror-freelist-fresh" ["MemoryError_dealloc", "get_memory_error", "BaseException_clear", "MemoryError_new"]
    "A MemoryError taken from the freelist has __suppress_context__ False, like any new exception."
    "invariant: an object from a freelist is indistinguishable from a fresh one" ``MemoryErrorFreelistFresh ``memoryErrorFreelistFresh_refuted
    "typeobj-exc-memoryerror-freelist-state",
  r "typeobj-exc-memoryerror-new-args" ["MemoryError_new", "get_memory_error"]
    "MemoryError.__new__(MemoryError, *args) keeps args, as BaseException.__new__ and MemoryError subclasses do."
    "implementation disagreeing with itself: the freelist and allocation paths of get_memory_error (exceptions.c:4124, 4139)" ``MemoryErrorNewCKeepsArgs ``memoryErrorNewCKeepsArgs_refuted
    "typeobj-exc-memoryerror-freelist-state"
    "Stated on memoryErrorNewC, the mirror with the freelist explicit: false whenever an entry is free (from startup), true once the freelist is empty.",
  p "typeobj-exc-memoryerror-new-branches" ["MemoryError_new", "get_memory_error"]
    "MemoryError.__new__ on a subclass makes a fresh object with its args; on MemoryError it takes a free entry with args () when there is one, and a fresh object with its args when there is none."
    "exceptions.c:4111-4151" ``MemoryErrorNewBranches ``memoryErrorNewBranches_proven
    "Scope limit of the interpreter: its memoryErrorNew has no freelist in its world and always takes the entry branch, so it gives args () where CPython, with the freelist empty, keeps the args; and every MemoryError it makes has suppress_context False, so the freelist-state leak of typeobj-exc-memoryerror-freelist-state is invisible at the interpreter level and is stated on the explicit freelist model only.",
  p "typeobj-exc-pyerr-nomemory" ["_PyErr_NoMemory", "get_memory_error"]
    "_PyErr_NoMemory takes the most recent free entry with args () and shrinks the list, or gives the last-resort singleton when the list is empty."
    "exceptions.c:4153-4167, 4111-4140" ``PyErrNoMemoryBranches ``pyErrNoMemoryBranches_proven,
  p "typeobj-exc-preallocate-contents" ["preallocate_memerrors"]
    "preallocate_memerrors leaves sixteen entries on the freelist, each a MemoryError made with no arguments and cleared."
    "exceptions.c:4198-4217" ``PreallocateContents ``preallocateContents_proven,
  -- Review part 2 fixes
  p "typeobj-exc-name-attr-stores" ["NameError_init", "AttributeError_init"]
    "NameError.__init__ and AttributeError.__init__ set args and each keyword member to its keyword or NULL, on every call."
    "exceptions.c:2580-2605, 2663-2690" ``NameAttrInitStores ``nameAttrInitStores_proven,
  p "typeobj-exc-attr-getstate-reduce" ["AttributeError_getstate", "AttributeError_reduce"]
    "AttributeError.__getstate__ is a new copy of the instance dict with name (when set) and args over it and obj left out; __reduce__ is (type, args, state)."
    "exceptions.c:2719-2760" ``AttributeErrorGetstateReduce ``attributeErrorGetstateReduce_proven
    "Keys are compared by the model's identity test; the colliding-__eq__ path of PyDict_Copy is bug typeobj-exc-getstate-borrowed-dict.",
  p "typeobj-exc-syntaxerror-init-stores" ["SyntaxError_init"]
    "SyntaxError.__init__ stores msg with at least one argument and, with two, the 4, 6 or 7 items of tuple(info) as the location members (NULL when absent)."
    "exceptions.c:2790-2837" ``SyntaxErrorInitStores ``syntaxErrorInitStores_proven,
  p "typeobj-exc-my-basename-exact" ["my_basename"]
    "my_basename gives what follows the last '/', or the whole name when there is none."
    "exceptions.c:2882-2904" ``MyBasenameExact ``myBasenameExact_proven,
  p "typeobj-exc-syntaxerror-str-formats" ["SyntaxError_str"]
    "str(SyntaxError) is str(msg) followed by ' (file, line N)', ' (file)' or ' (line N)' from a str filename's basename and an exact-int lineno (-1 outside long)."
    "exceptions.c:2907-2949" ``SyntaxErrorStrFormats ``syntaxErrorStrFormats_proven,
  p "typeobj-exc-unicode-attr-full" ["check_unicode_error_attribute", "as_unicode_error_attribute", "check_unicode_error_type"]
    "The attribute check refuses NULL, a non-bytes with as_bytes and a non-str without it, and as_unicode_error_attribute otherwise returns the attribute; the type check passes every UnicodeError."
    "exceptions.c:3064-3098, 3127-3137" ``UnicodeAttributeFull ``unicodeAttributeFull_proven,
  p "typeobj-exc-unicode-getters" ["unicode_error_get_encoding_impl", "unicode_error_get_object_impl", "unicode_error_get_reason_impl", "unicode_error_get_start_impl", "unicode_error_get_end_impl", "PyUnicodeEncodeError_GetEncoding", "PyUnicodeDecodeError_GetEncoding", "PyUnicodeEncodeError_GetObject", "PyUnicodeDecodeError_GetObject", "PyUnicodeTranslateError_GetObject", "PyUnicodeEncodeError_GetStart", "PyUnicodeDecodeError_GetStart", "PyUnicodeTranslateError_GetStart", "PyUnicodeEncodeError_GetEnd", "PyUnicodeDecodeError_GetEnd", "PyUnicodeTranslateError_GetEnd", "PyUnicodeEncodeError_GetReason", "PyUnicodeDecodeError_GetReason", "PyUnicodeTranslateError_GetReason"]
    "On a UnicodeError the getters return the encoding, reason and object attributes (the object as bytes for decode), and GetStart/GetEnd the stored values clipped to the object's length."
    "exceptions.c:3149-3180, 3437-3494, 3555-3562, 3565-3638" ``UnicodeGettersRead ``unicodeGettersRead_proven,
  p "typeobj-exc-unicode-setters" ["unicode_error_set_reason_impl", "unicode_error_set_start_impl", "unicode_error_set_end_impl", "PyUnicodeEncodeError_SetStart", "PyUnicodeDecodeError_SetStart", "PyUnicodeTranslateError_SetStart", "PyUnicodeEncodeError_SetEnd", "PyUnicodeDecodeError_SetEnd", "PyUnicodeTranslateError_SetEnd", "PyUnicodeEncodeError_SetReason", "PyUnicodeDecodeError_SetReason", "PyUnicodeTranslateError_SetReason"]
    "On a UnicodeError SetStart and SetEnd succeed and store the raw value, which e.start and e.end read; SetReason stores the str."
    "exceptions.c:3188-3229, 3523-3612, 3643-3664" ``UnicodeSettersStore ``unicodeSettersStore_proven,
  p "typeobj-exc-unicode-adjust-keeps" ["unicode_error_adjust_start", "unicode_error_adjust_end", "unicode_error_adjust_len"]
    "The clipping keeps a start in [0, objlen), an end in [1, objlen] and a non-negative length, and moves the others to the bound."
    "exceptions.c:3242-3337" ``UnicodeAdjustKeeps ``unicodeAdjustKeeps_proven,
  p "typeobj-exc-unicode-encode-init" ["UnicodeEncodeError_init"]
    "UnicodeEncodeError.__init__ with str encoding, object and reason and Py_ssize_t start and end stores args and the five members, start and end raw."
    "exceptions.c:3715-3738" ``UnicodeEncodeInitStores ``unicodeEncodeInitStores_proven,
  p "typeobj-exc-unicode-decode-init" ["UnicodeDecodeError_init"]
    "UnicodeDecodeError.__init__ keeps a bytes object, copies another buffer into a new bytes, and refuses a non-buffer with the %.100s message of PyObject_GetBuffer after storing args."
    "exceptions.c:3822-3861; Objects/abstract.c:450-452" ``UnicodeDecodeInitStores ``unicodeDecodeInitStores_proven,
  p "typeobj-exc-unicode-translate-init" ["UnicodeTranslateError_init"]
    "UnicodeTranslateError.__init__ with a str object and reason and Py_ssize_t start and end stores args and the four members."
    "exceptions.c:3944-3964" ``UnicodeTranslateInitStores ``unicodeTranslateInitStores_proven,
  p "typeobj-exc-unicode-encode-str" ["UnicodeEncodeError_str"]
    "str(UnicodeEncodeError) is '' with no object; otherwise after str(reason) and str(encoding) (<NULL> when deleted) the object must still be a str, and the message names one bad character with its escape or the range start-(end-1)."
    "exceptions.c:3740-3801" ``UnicodeEncodeStrFormats ``unicodeEncodeStrFormats_proven,
  p "typeobj-exc-unicode-decode-str" ["UnicodeDecodeError_str"]
    "The same for UnicodeDecodeError over bytes, with 'byte 0x%02x' and the bytes re-check."
    "exceptions.c:3863-3924" ``UnicodeDecodeStrFormats ``unicodeDecodeStrFormats_proven,
  p "typeobj-exc-unicode-translate-str" ["UnicodeTranslateError_str"]
    "The same for UnicodeTranslateError, with only str(reason) and no encoding."
    "exceptions.c:3967-4022" ``UnicodeTranslateStrFormats ``unicodeTranslateStrFormats_proven,
  p "typeobj-exc-unicode-escapes" []
    "The escapes of one bad character on the 3.15.2 runs: \\xe9, \\u0100, \\U0001f600, \\x61."
    "exceptions.c:3772-3780" ``BadCharEscapes ``badCharEscapes_proven,
  -- BaseExceptionGroup
  p "typeobj-exc-eg-rejects-non-exception" ["BaseExceptionGroup_new"]
    "The first item that is not an exception instance raises ValueError naming its index."
    "exceptions.c:933-953" ``EgRejectsNonException ``egRejectsNonException_proven,
  p "typeobj-exc-eg-no-base-in-exception" ["BaseExceptionGroup_new"]
    "When an item is not an Exception, the class of the new group never derives from Exception."
    "docs: ExceptionGroup 'can only wrap Exception subclasses'; exceptions.c:955-985" ``EgNoBaseInExceptionGroup ``egNoBaseInExceptionGroup_proven,
  p "typeobj-exc-eg-wraps" ["BaseExceptionGroup_new"]
    "With only Exception items, BaseExceptionGroup makes an ExceptionGroup and every other class is kept."
    "docs and exceptions.c:963-970" ``EgWrapsInExceptionGroup ``egWrapsInExceptionGroup_proven,
  p "typeobj-exc-eg-rejects-empty" ["BaseExceptionGroup_new"]
    "An empty sequence of exceptions is a ValueError."
    "exceptions.c:925-931" ``EgRejectsEmpty ``egRejectsEmpty_proven,
  p "typeobj-exc-eg-str" ["BaseExceptionGroup_str"]
    "str(eg) is the message, then the count, with 's' only above one."
    "exceptions.c:1065-1077" ``EgStrFormat ``egStrFormat_proven,
  p "typeobj-exc-eg-init" ["BaseExceptionGroup_init"]
    "__init__ stores args only and leaves message and exceptions; a keyword is a TypeError."
    "exceptions.c:1025-1035; _PyArg_NoKeywords, Python/getargs.c:2956" ``EgInitKeepsMembers ``egInitKeepsMembers_proven,
  p "typeobj-exc-eg-repr-in-bounds" ["BaseExceptionGroup_repr"]
    "repr(eg) reads args[1] only when args has two items; with any other args it shows eg.exceptions as a tuple."
    "invariant: no out-of-bounds read; self->args is writable, and exceptions.c:1099 sizes it first" ``EgReprAnyArgs ``egReprAnyArgs_proven,
  p "typeobj-exc-eg-repr-after-new" ["BaseExceptionGroup_repr", "BaseExceptionGroup_new"]
    "Every group fresh from BaseExceptionGroup_new has two args, so the read is in bounds until args is replaced."
    "narrowing of typeobj-exc-eg-repr-in-bounds" ``EgReprInBoundsAfterNew ``egReprInBoundsAfterNew_proven,
  p "typeobj-exc-eg-repr-saved" ["BaseExceptionGroup_repr"]
    "A saved exceptions_str is used as is."
    "comment at exceptions.c:1087; :1088-1090 and :906-916" ``EgReprSavedString ``egReprSavedString_proven,
  p "typeobj-exc-eg-created-through-class" []
    "derive and _PyExc_CreateExceptionGroup both call BaseExceptionGroup."
    "exceptions.c:1009-1023, 1135-1148" ``EgCreatedThroughClass ``egCreatedThroughClass_proven
    "No pyFns: this is rfl on two one-line definitions; derive and _PyExc_CreateExceptionGroup stay todo until a property ties them to what BaseExceptionGroup's construction stores.",
  p "typeobj-exc-eg-bases" []
    "ExceptionGroup has the bases (BaseExceptionGroup, Exception), both in its MRO."
    "exceptions.c:1767-1783" ``ExceptionGroupBases ``exceptionGroupBases_proven,
  p "typeobj-exc-subset-metadata" ["exceptiongroup_subset"]
    "After exceptiongroup_subset's copy, the new group has the original's __context__ and __cause__, and its __traceback__ when it has one, including when derive returned the original."
    "comment at exceptions.c:1154-1155; :1187-1196; docs for split and subgroup ('preserves ... metadata')" ``SubsetCopiesMetadata ``subsetCopiesMetadata_proven,
  r "typeobj-exc-subset-suppress-context" ["exceptiongroup_subset", "PyException_SetCause"]
    "exceptiongroup_subset also preserves __suppress_context__."
    "comment at exceptions.c:1154-1155 ('with metadata from _orig'), :1196; docs for derive ('__traceback__, __cause__, __context__ and __notes__')" ``SubsetCopiesSuppressContext ``subsetCopiesSuppressContext_refuted
    "typeobj-exc-split-sets-suppress-context",
  p "typeobj-exc-subset-checks" ["exceptiongroup_subset"]
    "An empty part is NULL without calling derive; a derive that does not return a group is a TypeError."
    "exceptions.c:1164-1183" ``SubsetChecks ``subsetChecks_proven,
  p "typeobj-exc-matcher-type" ["get_matcher_type"]
    "A non-class callable matches by predicate, an exception class or a tuple of them by type, and an int is the TypeError."
    "exceptions.c:1244-1276" ``GetMatcherTypeClassifies ``getMatcherTypeClassifies_proven,
  p "typeobj-exc-match-by-type" ["exceptiongroup_split_check_match"]
    "For an exception instance and an exception class, matching by type is the subclass test."
    "exceptions.c:1284-1288; PyErr_GivenExceptionMatches" ``MatchByTypeIsSubclass ``matchByTypeIsSubclass_proven,
  p "typeobj-exc-split-partition" ["exceptiongroup_split_recursive", "BaseExceptionGroup_split_impl", "exceptiongroup_split_check_match", "exceptiongroup_subset"]
    "If the matcher is a function of the exception, derive honours its contract and groups stay intact, the leaves of split's two parts are exactly the leaves of the group, each once."
    "docs for BaseExceptionGroup.split" ``SplitPartitionsLeaves ``splitPartitionsLeaves_proven
    "SplitHyp: the matcher is p, derive returns a group of the given exceptions, and user code changes no group's exceptions. Quantifies over every rt with these properties.",
  p "typeobj-exc-split-structure" ["exceptiongroup_split_recursive", "BaseExceptionGroup_split_impl"]
    "Under the same hypotheses each part has the shape specSplit gives: matching exceptions stay whole, a partly matching group is rebuilt around its matching children, and empty groups are dropped."
    "docs for BaseExceptionGroup.subgroup ('preserves the nesting structure')" ``SplitPreservesStructure ``splitPreservesStructure_proven,
  p "typeobj-exc-split-computes-spec" ["exceptiongroup_split_recursive", "exceptiongroup_subset", "BaseExceptionGroup_split_impl", "BaseExceptionGroup_subgroup_impl"]
    "Under SplitHyp and SplitTotalHyp (matcher, derive and __notes__ do not raise, derive returns a group, in worlds satisfying an invariant I) split and subgroup succeed and return exactly the parts of specSplit, so a function that only succeeds on a full match fails."
    "docs for BaseExceptionGroup.split; exceptions.c:1321-1496" ``SplitComputesSpec ``splitComputesSpec_proven,
  p "typeobj-exc-split-hyps-inhabited" []
    "SplitHyp and SplitTotalHyp are met together by a concrete rt on a group that matches in part, with the real subsetCopyMeta and exceptiongroupSubset: the totality theorem is not vacuous."
    "non-vacuity of typeobj-exc-split-computes-spec" ``SplitHypsInhabited ``splitHypsInhabited_proven,
  p "typeobj-exc-split-failures" ["exceptiongroup_split_recursive", "exceptiongroup_subset"]
    "A matcher that raises makes the recursion raise the same exception, and derive returning a non-group is the exact TypeError."
    "exceptions.c:1179-1183, 1332-1335" ``SplitPropagatesFailures ``splitPropagatesFailures_proven,
  p "typeobj-exc-subgroup-is-split-match" ["exceptiongroup_split_recursive"]
    "Under the same hypotheses, the recursion with construct_rest false builds the shape of the match part of the recursion with construct_rest true, and no rest."
    "docs for BaseExceptionGroup.split" ``SubgroupEqualsSplitMatch ``subgroupEqualsSplitMatch_proven,
  p "typeobj-exc-split-identity" ["exceptiongroup_split_recursive", "BaseExceptionGroup_split_impl", "BaseExceptionGroup_subgroup_impl"]
    "When the matcher accepts the exception, the recursion returns it by identity with no rest, for every matcher and rt; split and subgroup then return self."
    "docs for subgroup ('If the condition matches the whole group...'); exceptions.c:1337-1342" ``SplitFullMatchIdentity ``splitFullMatchIdentity_proven,
  p "typeobj-exc-split-leaf" ["exceptiongroup_split_recursive"]
    "A leaf that does not match goes to the rest, and nowhere when no rest is asked for."
    "exceptions.c:1344-1358" ``SplitLeafNoMatch ``splitLeafNoMatch_proven,
  p "typeobj-exc-leaf-ids" ["collect_exception_group_leaf_ids"]
    "collect_exception_group_leaf_ids adds nothing for None, a leaf as itself, a group's items' ids in order one level down, propagates the first failure, and is an error (not []) when out of depth."
    "exceptions.c:1498-1534" ``CollectLeafIdsSteps ``collectLeafIdsSteps_proven,
  p "typeobj-exc-instance-ids" ["exceptiongroup_split_check_match", "exception_group_projection"]
    "The instance-ids matcher never accepts a group, and accepts a leaf exactly when it is in the set."
    "exceptions.c:1299-1311" ``InstanceIdsMatchLeaves ``instanceIdsMatchLeaves_proven,
  p "typeobj-exc-prep-reraise-short" ["_PyExc_PrepReraiseStar"]
    "No exceptions give None, and for a naked exception the first entry is returned as is."
    "exceptions.c:1620-1636" ``PrepReraiseStarShortPaths ``prepReraiseStarShortPaths_proven,
  p "typeobj-exc-prep-reraise-validates" ["PyUnstable_Exc_PrepReraiseStar"]
    "The public wrapper rejects a non-exception orig, a non-list excs and an orig without traceback before running."
    "exceptions.c:1704-1738" ``PrepReraiseStarValidates ``prepReraiseStarValidates_proven,
  p "typeobj-exc-same-metadata-refl" []
    "An exception has the same metadata as itself."
    "exceptions.c:1580-1593" ``SameMetadataReflexive ``sameMetadataReflexive_proven,
  r "typeobj-exc-same-metadata-notes" ["is_same_exception_metadata", "_PyExc_PrepReraiseStar", "exception_group_projection"]
    "Two exceptions that is_same_exception_metadata calls the same have the same __notes__."
    "exceptions.c:1589 compares notes; PEP 678 defines notes as __notes__" ``SameMetadataComparesNotes ``sameMetadataComparesNotes_refuted
    "typeobj-exc-except-star-drops-notes"
]

end PyLean.TypeObj
