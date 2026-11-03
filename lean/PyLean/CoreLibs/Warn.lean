import PyLean.Registry
import PyLean.CoreLibs.Warn.Diff
import PyLean.CoreLibs.Warn.Props
import PyLean.CoreLibs.Warn.FiltersProps
import PyLean.CoreLibs.Warn.OptionProps
import PyLean.CoreLibs.Warn.WarnCallProps
import PyLean.CoreLibs.Warn.ContextProps

/-! Registry for the `Warn` area of CoreLibs: Python/_warnings.c and Lib/_py_warnings.py,
`warn_explicit` in both twins, CPython 3.15.2. -/

namespace PyLean.CoreLibs.Warn

open PyLean.Registry

def cFns : List String := ["warn_explicit", "get_filter", "check_matched", "already_warned", "update_registry"]

def entries : List Entry := [
  { id := "warn-twins-narrow", pyFile := "Python/_warnings.c"
    pyFns := cFns
    statement := "For callbacks that do not raise, filters that are 5-tuples of a str action error/ignore/always/all/default, compiled patterns and lines that fit Py_ssize_t, an int line that fits C int, a module omitted or a str, a message that can be built, and a registry that is None or a dict whose version is an exact int within C long, C warn_explicit and _py_warnings.warn_explicit give the same result and leave the same registry and once registry (True == 1)."
    source := "twin: _py_warnings.py:556-625 against _warnings.c:797-922", status := .proven
    prop := ``WarnTwinsNarrow, thm := some ``warnTwinsNarrow_proven
    notes := "Difftest corelibs area warn: plain-str filters, 5-element lists, short items, non-str actions and default actions, non-int lines, non-str modules, raising message constructors, non-dict registries and True versions included; 180k cases over 6 seeds, 100%." },
  { id := "warn-twins-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn_explicit"]
    statement := "The same agreement, from the Python twin's side."
    source := "twin: _py_warnings.py:556-625 against _warnings.c:797-922", status := .proven
    prop := ``WarnTwinsNarrow, thm := some ``warnTwinsNarrow_proven },
  { id := "warn-twins-once", pyFile := "Python/_warnings.c"
    pyFns := cFns
    statement := "With the once action as well, the twins agree."
    source := "docs: once prints the first occurrence regardless of location; twin", status := .refuted
    prop := ``WarnTwinsOnce, thm := some ``warnTwinsOnce_refuted, bug := some "corelibs-warnings-once-per-module" },
  { id := "warn-twins-module", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn_explicit"]
    statement := "With the module action as well, the twins agree."
    source := "twin; docs: module prints the first occurrence for each module regardless of line number", status := .refuted
    prop := ``WarnTwinsModule, thm := some ``warnTwinsModule_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-valid-lines", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit", "get_filter"]
    statement := "With filter lines as filterwarnings accepts them (any int >= 0), the twins agree."
    source := "twin; docs: lineno is an integer line number", status := .refuted
    prop := ``WarnTwinsValidLines, thm := some ``warnTwinsValidLines_refuted, bug := some "corelibs-warnings-filter-lineno-overflow" },
  { id := "warn-twins-any-version", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit", "already_warned"]
    statement := "With any int as the registry's version, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsAnyVersion, thm := some ``warnTwinsAnyVersion_refuted, bug := some "corelibs-warnings-registry-version-systemerror" },
  { id := "warn-no-system-error", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit", "already_warned"]
    statement := "C warn_explicit never leaks an internal error (SystemError), for every registry of ints."
    source := "invariant: no internal error leaking", status := .refuted
    prop := ``NoSystemError, thm := some ``noSystemError_refuted, bug := some "corelibs-warnings-registry-version-systemerror" },
  { id := "warn-twins-raising", pyFile := "Python/_warnings.c"
    pyFns := ["check_matched", "get_filter"]
    statement := "With callbacks that may raise, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsRaising, thm := some ``warnTwinsRaising_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-none-module", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit"]
    statement := "With module=None passed explicitly, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsNoneModule, thm := some ``warnTwinsNoneModule_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-any-line", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit"]
    statement := "With any int line, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsAnyLine, thm := some ``warnTwinsAnyLine_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-unknown-action", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit"]
    statement := "With an unknown action, the twins leave the same registry."
    source := "twin", status := .refuted
    prop := ``WarnTwinsUnknownAction, thm := some ``warnTwinsUnknownAction_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-inexact-version", pyFile := "Python/_warnings.c"
    pyFns := ["already_warned"]
    statement := "With a registry version that is not an exact int (True, an int subclass), the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsInexactVersion, thm := some ``warnTwinsInexactVersion_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-plain-filter", pyFile := "Python/_warnings.c"
    pyFns := ["check_matched", "get_filter"]
    statement := "With filters whose patterns are plain strs (as C's internal default filters are), the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsPlainFilter, thm := some ``warnTwinsPlainFilter_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-item-shape", pyFile := "Python/_warnings.c"
    pyFns := ["get_filter"]
    statement := "With filters-list items that are 5-element lists or carry a non-str action, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsItemShape, thm := some ``warnTwinsItemShape_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-module-obj", pyFile := "Python/_warnings.c"
    pyFns := ["check_matched", "get_filter"]
    statement := "With a module argument that is not a str, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsModuleObj, thm := some ``warnTwinsModuleObj_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-reg-obj", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit"]
    statement := "With a registry that is neither a dict nor None, the twins raise the same exception."
    source := "twin", status := .refuted
    prop := ``WarnTwinsRegObj, thm := some ``warnTwinsRegObj_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-msg-raises", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit"]
    statement := "When the message cannot be built (category(message) or str(message) raising), the twins raise the same exception."
    source := "twin", status := .refuted
    prop := ``WarnTwinsMsgRaises, thm := some ``warnTwinsMsgRaises_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-twins-dflt-type", pyFile := "Python/_warnings.c"
    pyFns := ["warn_explicit", "get_filter"]
    statement := "With a defaultaction that is not a str, the twins raise the same exception."
    source := "twin", status := .refuted
    prop := ``WarnTwinsDfltType, thm := some ``warnTwinsDfltType_refuted, bug := some "corelibs-warnings-py-twin" },
  { id := "warn-py-unknown-action", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn_explicit"]
    statement := "_py_warnings raises RuntimeError for an unknown action whenever C does, for every filters list."
    source := "twin; the RuntimeError the code means to raise", status := .refuted
    prop := ``PyUnknownActionRaises, thm := some ``pyUnknownActionRaises_refuted, bug := some "corelibs-warnings-py-twin" },
  -- filters-list API (Warn/Filters.lean, FiltersProps.lean)
  { id := "warn-filterwarnings-spec", pyFile := "Lib/_py_warnings.py"
    pyFns := ["filterwarnings", "_add_filter"]
    statement := "On a filters list whose elements' == against the new item does not raise, filterwarnings succeeds exactly for the documented arguments (one of the seven actions, str message and module that compile, a Warning subclass, an int lineno >= 0), and then the new item is first and the first element equal to it is removed (append: last, unless an equal element is present), and the version moves on by one."
    source := "docstring :256-265 and the comment at :324-325", status := .proven
    prop := ``FilterwarningsSpec, thm := some ``filterwarningsSpec_proven
    notes := "Difftest warn.filt_c / warn.filt_py: scripts of filterwarnings, simplefilter, resetwarnings, _filters_mutated and the C lock on lists (with elements whose __eq__ raises), tuples and a deleted warnings.filters." },
  { id := "warn-simplefilter-warncat", pyFile := "Lib/_py_warnings.py"
    pyFns := ["simplefilter", "filterwarnings"]
    statement := "For a category that is a Warning subclass, simplefilter(a, c, l, ap) does exactly what filterwarnings(a, '', c, '', l, ap) does, for every action, lineno and filters state."
    source := "docstring :295-302: the parameters mean what they mean for filterwarnings", status := .proven
    prop := ``SimpleIsFilterWarnCat, thm := some ``simpleIsFilterWarnCat_proven },
  { id := "warn-simplefilter-any-cat", pyFile := "Lib/_py_warnings.py"
    pyFns := ["simplefilter"]
    statement := "For every category, simplefilter does what filterwarnings with an empty message and module does."
    source := "docstring :295-302", status := .refuted
    prop := ``SimpleIsFilter, thm := some ``simpleIsFilter_refuted, bug := some "corelibs-warnings-simplefilter-category"
    notes := "Duplicate of python/cpython#125893." },
  { id := "warn-version-bumps", pyFile := "Lib/_py_warnings.py"
    pyFns := ["filterwarnings", "simplefilter", "resetwarnings", "_filters_mutated", "_add_filter"]
    statement := "Every successful filterwarnings, simplefilter, resetwarnings (list, tuple or deleted filters) and _filters_mutated (at any lock depth) moves the filters version on by exactly one, and C _filters_mutated_lock_held does whenever it succeeds."
    source := "invariant: registries are invalidated by the version (_warnings.c:616-632, _py_warnings.py:570-572)", status := .proven
    prop := ``VersionBumps, thm := some ``versionBumps_proven },
  { id := "warn-version-bumps-c", pyFile := "Python/_warnings.c"
    pyFns := ["warnings_filters_mutated_lock_held_impl"]
    statement := "The same, from the C side: _filters_mutated_lock_held moves the version on by one whenever it succeeds."
    source := "invariant", status := .proven
    prop := ``VersionBumps, thm := some ``versionBumps_proven },
  { id := "warn-lock-spec", pyFile := "Python/_warnings.c"
    pyFns := ["warnings_acquire_lock_impl", "warnings_release_lock_impl", "warnings_filters_mutated_lock_held_impl",
              "warnings_lock", "warnings_unlock", "warnings_lock_held"]
    statement := "_release_lock after _acquire_lock gives the depth back, _release_lock raises RuntimeError exactly when the lock is not held, and _filters_mutated_lock_held raises RuntimeError exactly when the lock is not held."
    source := "invariant; the 'cannot release un-acquired lock' and 'warnings lock is not held' errors", status := .proven
    prop := ``LockSpec, thm := some ``lockSpec_proven },
  { id := "warn-mutated-lock-twins", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_filters_mutated_lock_held"]
    statement := "The C and Python _filters_mutated_lock_held agree at every lock depth."
    source := "twin", status := .refuted
    prop := ``MutatedLockHeldTwins, thm := some ``mutatedLockHeldTwins_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  { id := "warn-defaults-twin-narrow", pyFile := "Python/_warnings.c"
    pyFns := ["init_filters", "create_filter"]
    statement := "For every module name that is __main__ or does not start with __main__, C's initial filters and the list _setup_defaults builds pick the same filter action for every warning."
    source := "twin: _setup_defaults (:920-928) against init_filters (:101-132)", status := .proven
    prop := ``DefaultsTwinNarrow, thm := some ``defaultsTwinNarrow_proven
    notes := "Difftest warn.defaults compares both lists with fresh interpreters (with and without _warnings)." },
  { id := "warn-defaults-twin-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_setup_defaults"]
    statement := "The same agreement, from the Python side."
    source := "twin", status := .proven
    prop := ``DefaultsTwinNarrow, thm := some ``defaultsTwinNarrow_proven },
  { id := "warn-defaults-twin", pyFile := "Python/_warnings.c"
    pyFns := ["init_filters", "create_filter"]
    statement := "For every module name, the two default lists pick the same action."
    source := "twin", status := .refuted
    prop := ``DefaultsTwin, thm := some ``defaultsTwin_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  -- -W options (Warn/Option.lean, OptionProps.lean)
  { id := "warn-getaction", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_getaction"]
    statement := "Every action name stands for itself, the empty field for 'default', every answer is an action name the field is a prefix of, and anything else raises _OptionError."
    source := "docs: the -W action may be abbreviated", status := .proven
    prop := ``GetactionSpec, thm := some ``getactionSpec_proven },
  { id := "warn-options-narrow", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_processoptions", "_setoption", "_getcategory", "_getaction"]
    statement := "When imports raise only ImportError, getattr only AttributeError, every attribute named is a class and re.compile raises only PatternError (the same with or without re.I), no list of -W options makes _processoptions raise, on a filters list whose elements' == does not raise."
    source := "invariant: _processoptions reports invalid options as 'Invalid -W option ignored'", status := .proven
    prop := ``ProcessOptionsNoEscapeNarrow, thm := some ``processOptionsNoEscapeNarrow_proven
    notes := "Difftest warn.opt: option lists over abbreviated and invalid actions, raw and escaped regexes, dotted category names, int() forms of the line field, on the real builtins and re." },
  { id := "warn-options-no-escape", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_processoptions", "_setoption", "_getcategory"]
    statement := "No -W option makes _processoptions raise (so `import warnings` cannot fail at startup)."
    source := "invariant; bpo-39056", status := .refuted
    prop := ``ProcessOptionsNoEscape, thm := some ``processOptionsNoEscape_refuted, bug := some "corelibs-warnings-option-escape"
    notes := "Also refuted by processOptionsNoEscape_refuted_module (empty module name) and processOptionsNoEscape_refuted_regex (repetition overflow)." },
  -- warnings.warn (Warn/WarnCall.lean, WarnCallProps.lean)
  { id := "warn-call-twins-narrow", pyFile := "Python/_warnings.c"
    pyFns := ["warnings_warn_impl", "get_category", "do_warn", "setup_context", "next_external_frame",
              "is_internal_frame", "is_filename_to_skip", "is_internal_filename"]
    statement := "For a str or Warning message, a Warning subclass or None category, a stacklevel from 1 to the C int maximum, skip_file_prefixes a tuple of strs, frames with C int lines and globals whose __name__ is a str or missing and whose registry is missing, None or a dict with an exact version in C long, and the hypotheses of warn-twins-narrow: C and Python warnings.warn give the same result and use and leave the same registry and once registry."
    source := "twin: _py_warnings.py:465-520 against _warnings.c:1015-1211", status := .proven
    prop := ``WarnCallTwinsNarrow, thm := some ``warnCallTwinsNarrow_proven
    notes := "Difftest warn.call_c / warn.call_py: generated stacks of frames (exec'd functions with chosen filenames and globals) run in a fresh thread, so they are the whole stack." },
  { id := "warn-call-twins-narrow-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn", "_next_external_frame", "_is_internal_frame", "_is_filename_to_skip", "_is_internal_filename"]
    statement := "The same agreement, from the Python side."
    source := "twin", status := .proven
    prop := ``WarnCallTwinsNarrow, thm := some ``warnCallTwinsNarrow_proven },
  { id := "warn-call-twins", pyFile := "Python/_warnings.c"
    pyFns := ["warnings_warn_impl", "setup_context"]
    statement := "For every stacklevel and skip_file_prefixes, the twins give the same result and use the same registry."
    source := "twin", status := .refuted
    prop := ``WarnCallTwins, thm := some ``warnCallTwins_refuted, bug := some "corelibs-warnings-py-twin-warn"
    notes := "stacklevel=0; also warnCallTwins_refuted_prefix (a tuple prefix) and warnCallTwins_refuted_huge (stacklevel 2**64)." },
  { id := "warn-call-twins-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn"]
    statement := "The same, from the Python side."
    source := "twin", status := .refuted
    prop := ``WarnCallTwins, thm := some ``warnCallTwins_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  -- catch_warnings and the contexts (Warn/Context.lean, ContextProps.lean)
  { id := "warn-filter-list-twins", pyFile := "Python/_warnings.c"
    pyFns := ["get_warnings_context", "get_warnings_context_filters", "get_warnings_filters"]
    statement := "While warnings.filters exists, the list C's get_filter searches (the context's _filters, else warnings.filters) is the one Python's _get_filters() returns, in context mode or while no context is set."
    source := "twin", status := .proven
    prop := ``FilterListTwins, thm := some ``filterListTwins_proven },
  { id := "warn-filter-list-twins-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_get_filters", "_get_context", "_GlobalContext._filters"]
    statement := "The same, from the Python side."
    source := "twin", status := .proven
    prop := ``FilterListTwins, thm := some ``filterListTwins_proven },
  { id := "warn-filter-list-twins-any", pyFile := "Python/_warnings.c"
    pyFns := ["get_warnings_filters"]
    statement := "Also when warnings.filters was deleted, C and Python search the same list."
    source := "twin", status := .refuted
    prop := ``FilterListTwinsAny, thm := some ``filterListTwinsAny_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  { id := "warn-catch-restores", pyFile := "Lib/_py_warnings.py"
    pyFns := ["catch_warnings.__init__", "catch_warnings.__enter__", "catch_warnings.__exit__", "_Context.__init__",
              "_Context.copy", "_new_context", "_set_context", "_get_context", "_get_filters", "_GlobalContext._filters"]
    statement := "In both context modes, a catch_warnings whose action simplefilter accepts enters, a second __enter__ raises RuntimeError and changes nothing, and whatever the block does to the filters it sees, __exit__ makes _get_filters() what it was and restores showwarning (and without contexts warnings.filters and _showwarnmsg_impl), the version moving on by one."
    source := "docs: copies and, upon exit, restores the warnings filter and showwarning()", status := .open
    prop := ``CatchRestores
    notes := "Open: the proof (both modes, any edit of the filters inside the block) is not done; difftest warn.ctx agrees on 150k cases." },
  { id := "warn-catch-enter-atomic", pyFile := "Lib/_py_warnings.py"
    pyFns := ["catch_warnings.__enter__"]
    statement := "An __enter__ that raises leaves _showwarnmsg_impl, warnings.filters and the context as they were."
    source := "invariant: a with statement does not call __exit__ when __enter__ raises", status := .refuted
    prop := ``EnterAtomic, thm := some ``enterAtomic_refuted, bug := some "corelibs-warnings-catch-enter-leak" },
  { id := "warn-record-captures", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_showwarnmsg", "_showwarnmsg_impl", "_Context._record_warning", "catch_warnings.__enter__",
              "_new_context", "_set_context"]
    statement := "Inside catch_warnings(record=True), every warning shown through _showwarnmsg is appended to the returned list and written nowhere (with contexts, when _showwarnmsg_impl is the module's own)."
    source := "docs: record=True appends the warnings to a list", status := .proven
    prop := ``RecordCaptures, thm := some ``recordCaptures_proven
    notes := "Difftest warn.ctx: scripts of catch_warnings objects entered and exited (twice, out of order, with bad actions), shows through _showwarnmsg with replaced hooks and failing writers, in both context modes." }
]

end PyLean.CoreLibs.Warn
