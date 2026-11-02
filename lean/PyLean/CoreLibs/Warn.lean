import PyLean.Registry
import PyLean.CoreLibs.Warn.Diff
import PyLean.CoreLibs.Warn.Props

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
    prop := ``PyUnknownActionRaises, thm := some ``pyUnknownActionRaises_refuted, bug := some "corelibs-warnings-py-twin" }
]

end PyLean.CoreLibs.Warn
