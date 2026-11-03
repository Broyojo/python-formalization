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

def cFns : List String := ["warn_explicit", "get_filter", "check_matched", "already_warned", "update_registry",
  "get_once_registry", "get_default_action", "get_warnings_attr", "call_show_warning", "warnings_warn_explicit_impl"]

def entries : List Entry := [
  { id := "warn-twins-narrow", pyFile := "Python/_warnings.c"
    pyFns := cFns
    statement := "For callbacks that do not raise, warnings._showwarnmsg (callable) and warnings.WarningMessage present, a filters list (in warnings.filters or a context) of 5-tuples with a str action error/ignore/always/all/default, compiled patterns and int lines that fit Py_ssize_t, such a str defaultaction, a dict onceregistry, an int line that fits C int, a module omitted or a str, a message that can be built, no module_globals, and a registry that is None or a dict whose version is an exact int within C long, C warn_explicit and _py_warnings.warn_explicit give the same result and leave the same registry and once registry (True == 1)."
    source := "twin: _py_warnings.py:556-625 against _warnings.c:797-922", status := .proven
    prop := ``WarnTwinsNarrow, thm := some ``warnTwinsNarrow_proven
    notes := "Difftest corelibs area warn: plain-str filters, 5-element lists, short items, non-str and unhashable actions, non-int filter lines, tuple filters, context filters, deleted defaultaction and onceregistry, a non-dict onceregistry, deleted or non-callable _showwarnmsg, deleted WarningMessage, module_globals (an int, a dict, a dict whose loader raises), mapping registries, non-int linenos, non-str modules, raising message constructors and True versions included; 150k cases over 3 seeds, 100%. Every hypothesis is on record as a refutation (the entries below)." },
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
  { id := "warn-twins-line-obj", pyFile := "Python/_warnings.c"
    pyFns := ["get_filter"]
    statement := "With a filter line that is not an int, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsLineObj, thm := some ``warnTwinsLineObj_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  { id := "warn-twins-module-state", pyFile := "Python/_warnings.c"
    pyFns := ["get_filter", "get_once_registry", "get_default_action", "get_warnings_attr", "call_show_warning", "warn_explicit"]
    statement := "For every state of warnings.filters (list or tuple, or a context's), defaultaction (or deleted), onceregistry (a dict, another object, or deleted), _showwarnmsg and WarningMessage, the twins agree."
    source := "twin", status := .refuted
    prop := ``WarnTwinsModuleState, thm := some ``warnTwinsModuleState_refuted_tuple, bug := some "corelibs-warnings-py-twin-warn"
    notes := "Also refuted by warnTwinsModuleState_refuted_ctxTuple, _show (C falls back to show_warning when _showwarnmsg is deleted), _once (TypeError against AttributeError) and _dflt (C uses the cached default)." },
  { id := "warn-twins-module-state-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn_explicit"]
    statement := "The same, from the Python side."
    source := "twin", status := .refuted
    prop := ``WarnTwinsModuleState, thm := some ``warnTwinsModuleState_refuted_show, bug := some "corelibs-warnings-py-twin-warn" },
  { id := "warn-twins-globals", pyFile := "Python/_warnings.c"
    pyFns := ["warnings_warn_explicit_impl"]
    statement := "With module_globals given, the twins agree (here for an ignored warning)."
    source := "twin", status := .refuted
    prop := ``WarnTwinsGlobals, thm := some ``warnTwinsGlobals_refuted, bug := some "corelibs-warnings-py-twin-warn"
    notes := "module_globals=5 and a dict whose loader's get_source raises (warnTwinsGlobals_refuted_loader): C raises before the filters, Python returns None." },
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
    statement := "For every thread and lock state: _acquire_lock succeeds exactly when no other thread holds the lock, releasing right after gives the state back, _release_lock raises RuntimeError exactly when the calling thread does not hold the lock (another thread holding it is not enough), and _filters_mutated_lock_held raises RuntimeError exactly when no thread holds it."
    source := "invariant; the 'cannot release un-acquired lock' and 'warnings lock is not held' errors", status := .proven
    prop := ``LockSpec, thm := some ``lockSpec_proven
    notes := "Difftest warn.filt_c runs the lock from the main thread and a helper thread." },
  { id := "warn-mutated-lock-twins", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_filters_mutated_lock_held"]
    statement := "Under C's precondition (the lock is held, _warnings.c:1368), the C and Python _filters_mutated_lock_held agree: both move the version on by one."
    source := "twin", status := .proven
    prop := ``MutatedLockHeldTwins, thm := some ``mutatedLockHeldTwins_proven
    notes := "Without the lock C raises and Python does not; that breaks C's stated precondition, so it is not recorded as a defect." },
  { id := "warn-reset-spec", pyFile := "Lib/_py_warnings.py"
    pyFns := ["resetwarnings"]
    statement := "resetwarnings leaves an empty list (and moves the version on); a tuple refuses item deletion with TypeError; with warnings.filters deleted nothing changes but the version."
    source := "docstring :338: 'Clear the list of warning filters'", status := .proven
    prop := ``ResetSpec, thm := some ``resetSpec_proven },
  { id := "warn-add-filter-valueerror", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_add_filter"]
    statement := "For every class hierarchy: an exception raised by an element's __eq__ during filters.remove whose class is ValueError or a subclass (UnicodeError, io.UnsupportedOperation, user subclasses) is taken for 'not in the list': the new item is inserted in front and every element, the raising one included, stays; any other exception propagates."
    source := "the except ValueError of :326-329", status := .proven
    prop := ``AddFilterValueError, thm := some ``addFilterValueError_proven
    notes := "Difftest warn.filt_*: elements whose __eq__ raises ValueError, UnicodeError or KeyError." },
  { id := "warn-get-warnings-attr", pyFile := "Python/_warnings.c"
    pyFns := ["get_warnings_attr"]
    statement := "For every class hierarchy, get_warnings_attr: with try_import, an exception from import warnings whose class is ImportError or a subclass (ModuleNotFoundError, ImportCycleError, user subclasses) is cleared and gives NULL, any other import error propagates; without it, warnings missing from sys.modules gives NULL; a present attribute is returned, a missing one is NULL (no error), and a lookup that raises propagates."
    source := "the comments of :219-222 and :232-233 ('Fallback to the C implementation')", status := .proven
    prop := ``GetWarningsAttrSpec, thm := some ``getWarningsAttrSpec_proven
    notes := "Measured on 3.15.2: sys.modules['warnings'] = None, or a finder raising ImportCycleError or a user ImportError subclass for warnings, makes warn_explicit print through show_warning (a ValueError propagates); a warnings module whose __getattr__ raises ValueError makes warn_explicit raise it. call_show_warning and get_default_action are written over getWarningsAttr (Model.lean)." },
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
  { id := "warn-getaction-abbrev", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_getaction"]
    statement := "A non-empty prefix of an action name stands for that name unless it also abbreviates a name earlier in default, always, all, ignore, module, once, error."
    source := "docs: the -W action may be abbreviated", status := .proven
    prop := ``GetactionAbbrev, thm := some ``getactionAbbrev_proven },
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
    statement := "For a str or Warning message, a Warning subclass or None category, a stacklevel from 1 to the C int maximum, skip_file_prefixes a tuple of strs, frames with C int lines and globals whose __name__ is a str or missing and whose registry is missing, None or a dict with an exact version in C long, and the hypotheses of warn-twins-narrow: C and Python warnings.warn give the same result and use and leave the same registry and once registry. The twins' registry lookups are separate mirrors (cRegOf, pyRegOf)."
    source := "twin: _py_warnings.py:465-520 against _warnings.c:1015-1211", status := .proven
    prop := ``WarnCallTwinsNarrow, thm := some ``warnCallTwinsNarrow_proven
    notes := "Difftest warn.call_c / warn.call_py: generated stacks of frames (exec'd functions with chosen filenames and globals) run in a fresh thread, so they are the whole stack." },
  { id := "warn-call-twins-narrow-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn", "_next_external_frame", "_is_internal_frame", "_is_filename_to_skip", "_is_internal_filename"]
    statement := "The same agreement, from the Python side."
    source := "twin", status := .proven
    prop := ``WarnCallTwinsNarrow, thm := some ``warnCallTwinsNarrow_proven },
  { id := "warn-internal-filename", pyFile := "Python/_warnings.c"
    pyFns := ["is_internal_filename"]
    statement := "is_internal_filename (and _is_internal_filename, the same internalFn) holds exactly when the filename contains both 'importlib' and '_bootstrap'."
    source := "docstring of _is_internal_frame :450", status := .proven
    prop := ``InternalFnSpec, thm := some ``internalFnSpec_proven },
  { id := "warn-internal-filename-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_is_internal_filename"]
    statement := "The same, from the Python side."
    source := "docstring of _is_internal_frame :450", status := .proven
    prop := ``InternalFnSpec, thm := some ``internalFnSpec_proven },
  { id := "warn-next-external", pyFile := "Python/_warnings.c"
    pyFns := ["next_external_frame"]
    statement := "next_external_frame (and _next_external_frame, the same nextExt) with a skip test that does not raise returns the first frame after the current one that is neither internal nor skipped, or none."
    source := "docstring of _next_external_frame :455", status := .proven
    prop := ``NextExtSpec, thm := some ``nextExtSpec_proven },
  { id := "warn-next-external-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_next_external_frame"]
    statement := "The same, from the Python side."
    source := "docstring of _next_external_frame :455", status := .proven
    prop := ``NextExtSpec, thm := some ``nextExtSpec_proven },
  { id := "warn-category-errors", pyFile := "Python/_warnings.c"
    pyFns := ["get_category", "warnings_warn_impl"]
    statement := "With a str message and a category that is not a Warning subclass (an instance or another class), both twins raise TypeError, for every stacklevel within Py_ssize_t and every tuple of prefixes."
    source := "docs: category must be a subclass of Warning", status := .proven
    prop := ``WarnCatErr, thm := some ``warnCatErr_proven },
  { id := "warn-category-errors-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn"]
    statement := "The same, from the Python side."
    source := "docs", status := .proven
    prop := ``WarnCatErr, thm := some ``warnCatErr_proven },
  { id := "warn-category-message", pyFile := "Python/_warnings.c"
    pyFns := ["get_category"]
    statement := "The two category TypeErrors have the same message."
    source := "twin", status := .refuted
    prop := ``WarnCatMsg, thm := some ``warnCatMsg_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  { id := "warn-call-twins", pyFile := "Python/_warnings.c"
    pyFns := ["warnings_warn_impl", "setup_context"]
    statement := "For every stacklevel and skip_file_prefixes, the twins give the same result and use the same registry."
    source := "twin", status := .refuted
    prop := ``WarnCallTwins, thm := some ``warnCallTwins_refuted, bug := some "corelibs-warnings-py-twin-warn"
    notes := "stacklevel=0; also warnCallTwins_refuted_prefix (a tuple prefix), _huge (stacklevel 2**64), _order (warn('x', 5, skip_file_prefixes=[]): C's skip_file_prefixes TypeError first), _nameNone (C drops the warning, Python shows it) and _nameObj (C uses '<string>', Python passes the object)." },
  { id := "warn-call-twins-py", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn"]
    statement := "The same, from the Python side."
    source := "twin", status := .refuted
    prop := ``WarnCallTwins, thm := some ``warnCallTwins_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  -- catch_warnings and the contexts (Warn/Context.lean, ContextProps.lean)
  { id := "warn-filter-list-twins", pyFile := "Python/_warnings.c"
    pyFns := ["get_warnings_context", "get_warnings_context_filters", "get_warnings_filters"]
    statement := "While warnings.filters exists and no filters container is a tuple, the list C's get_filter searches (the context's _filters, else warnings.filters) is the one Python's _get_filters() returns, in context mode or while no context is set."
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
  { id := "warn-filter-list-twins-tuple", pyFile := "Python/_warnings.c"
    pyFns := ["get_warnings_filters", "get_warnings_context_filters"]
    statement := "Also with a tuple as warnings.filters, C and Python search the same list."
    source := "twin", status := .refuted
    prop := ``FilterListTwinsTuple, thm := some ``filterListTwinsTuple_refuted, bug := some "corelibs-warnings-py-twin-warn" },
  { id := "warn-show-dispatch", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_showwarnmsg", "_showwarnmsg_impl"]
    statement := "_showwarnmsg calls a replaced showwarning instead of the implementation, and an exception it raises propagates (TypeError when it is not callable); the original or deleted showwarning goes to _showwarnmsg_impl, which outside record mode propagates an exception from a replaced formatwarning, loses the warning when sys.stderr is None or the write raises an exception whose class is OSError or a subclass under the class hierarchy (BrokenPipeError, io.UnsupportedOperation, user subclasses), writes it when the write succeeds, and propagates any other exception from the write. Quantified over every class hierarchy."
    source := "docs: showwarning may be replaced; _showwarnmsg_impl's comments :141-150", status := .proven
    prop := ``ShowDispatch, thm := some ``showDispatch_proven },
  { id := "warn-nested-record", pyFile := "Lib/_py_warnings.py"
    pyFns := ["_Context.copy", "_new_context", "catch_warnings.__enter__", "_showwarnmsg_impl"]
    statement := "A catch_warnings() entered inside a catch_warnings(record=True) still records every warning shown through _showwarnmsg into the outer list, in both modes (with contexts, _Context.copy passes the log on; without, the inner __enter__ leaves _showwarnmsg_impl alone)."
    source := "_Context.copy :59-60; docs: record=True", status := .proven
    prop := ``NestedRecord, thm := some ``nestedRecord_proven
    notes := "Measured on 3.15.2 in both context modes; difftest warn.ctx enters objects in any order." },
  { id := "warn-exit-not-entered", pyFile := "Lib/_py_warnings.py"
    pyFns := ["catch_warnings.__exit__"]
    statement := "__exit__ of a catch_warnings that was never entered raises RuntimeError('Cannot exit <repr> without entering first') (a KeyError from the repr propagates instead) and changes nothing."
    source := ":728-729", status := .proven
    prop := ``ExitNotEntered, thm := some ``exitNotEntered_proven },
  { id := "warn-repr-spec", pyFile := "Lib/_py_warnings.py"
    pyFns := ["catch_warnings.__repr__"]
    statement := "catch_warnings.__repr__ raises KeyError when sys.modules['warnings'] is missing; otherwise it is the class name with record=True when recording and module=<repr> exactly when self._module is not sys.modules['warnings'] at the time of the call."
    source := ":689-696", status := .proven
    prop := ``ReprSpec, thm := some ``reprSpec_proven
    notes := "Measured on 3.15.2 (module=, a swapped and a missing sys.modules['warnings']); difftest warn.ctx repr cases." },
  { id := "warn-catch-restores", pyFile := "Lib/_py_warnings.py"
    pyFns := ["catch_warnings.__init__", "catch_warnings.__enter__", "catch_warnings.__exit__", "_Context.__init__",
              "_Context.copy", "_new_context", "_set_context", "_get_context", "_get_filters", "_GlobalContext._filters"]
    statement := "In both context modes, a catch_warnings(...) whose action simplefilter accepts enters; with no action the block sees a copy of the filters (a new list, same contents); a second __enter__ raises RuntimeError and changes nothing; and whatever the block does to the filters it sees, __exit__ makes _get_filters() what it was and restores showwarning (and without contexts warnings.filters and _showwarnmsg_impl), the version moving on by one."
    source := "docs: copies and, upon exit, restores the warnings filter and showwarning()", status := .proven
    prop := ``CatchRestores, thm := some ``catchRestores_proven
    notes := "Difftest warn.ctx agrees on 150k cases over 3 seeds." },
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
