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
    statement := "For callbacks that do not raise, filters whose actions are error, ignore, always, all or default with lines that fit Py_ssize_t, a line that fits C int, a module that is not an explicit None and a registry version that fits C long, C warn_explicit and _py_warnings.warn_explicit give the same result and leave the same registry and once registry."
    source := "twin: _py_warnings.py:556-625 against _warnings.c:797-922", status := .proven
    prop := ``WarnTwinsNarrow, thm := some ``warnTwinsNarrow_proven
    notes := "Difftest corelibs area warn: C and Python models against both CPython twins, 180k cases over 6 seeds, 100%." },
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
  { id := "warn-py-unknown-action", pyFile := "Lib/_py_warnings.py"
    pyFns := ["warn_explicit"]
    statement := "_py_warnings raises RuntimeError for an unknown action whenever C does, for every filters list."
    source := "twin; the RuntimeError the code means to raise", status := .refuted
    prop := ``PyUnknownActionRaises, thm := some ``pyUnknownActionRaises_refuted, bug := some "corelibs-warnings-py-twin" }
]

end PyLean.CoreLibs.Warn
