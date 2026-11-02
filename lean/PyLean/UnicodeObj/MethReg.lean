import PyLean.Registry
import PyLean.UnicodeObj.MethCase
import PyLean.UnicodeObj.MethStripProps
import PyLean.UnicodeObj.MethPadProps

/-! Registry entries of the `str` method slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def methEntries : List Entry := [
  { id := "unicodeobj-meth-case-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["do_capitalize", "do_swapcase", "do_title", "case_operation", "unicode_title_impl",
      "unicode_capitalize_impl", "unicode_casefold_impl", "unicode_lower_impl", "unicode_upper_impl",
      "unicode_swapcase_impl", "do_upper", "do_lower", "do_upper_or_lower", "do_casefold",
      "lower_ucs4", "handle_capital_sigma", "ascii_upper_or_lower"]
    statement := "For every string, upper, lower, casefold, title, capitalize and swapcase equal the per-position reading of the docs (full Unicode mappings, Final_Sigma by final_sigma, title after a non-cased character), through the ASCII shortcuts, the loops and the kind-narrowing copy of case_operation; the only error is OverflowError above PY_SSIZE_T_MAX // 12 characters."
    source := "str.upper/lower/casefold docs (Unicode 3.13), str.title/capitalize/swapcase docs; invariant: case_operation's copy loses no bits"
    status := .proven, prop := ``CaseDocSpec, thm := some ``caseDocSpec_proven },
  { id := "unicodeobj-meth-findchar-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_FindChar", "findchar"]
    statement := "For every string, Py_UCS4, start, end and direction, PyUnicode_FindChar returns the first (last) position of the character in unicode[start:end], or -1; the casts to the unit type never report a character the string lacks."
    source := "C API docs of PyUnicode_FindChar"
    status := .proven, prop := ``FindCharDoc, thm := some ``findCharDoc_proven },
  { id := "unicodeobj-meth-strip-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_XStrip", "do_strip", "do_argstrip", "unicode_strip_impl",
      "unicode_lstrip_impl", "unicode_rstrip_impl", "PyUnicode_Substring", "PyUnicode_FindChar",
      "findchar"]
    statement := "For every string, strip/lstrip/rstrip with a str remove exactly the leading/trailing characters in it, with None exactly the leading/trailing str.isspace characters (ASCII table and general branch alike), and raise TypeError naming the method for any other argument."
    source := "str.strip/lstrip/rstrip docs"
    status := .proven, prop := ``StripDoc, thm := some ``stripDoc_proven },
  { id := "unicodeobj-meth-new-size", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_New"]
    statement := "For every positive size and code point maxchar, PyUnicode_New's check passes exactly when struct_size + (size + 1) * char_size fits in Py_ssize_t, char_size is the width of the kind chosen, and the only refusal is MemoryError."
    source := "invariant: the allocation size neither overflows nor refuses a representable size"
    status := .proven, prop := ``NewSizeExact, thm := some ``newSizeExact_proven
    notes := "A failure of PyObject_Malloc below the limit is not modelled." },
  { id := "unicodeobj-meth-pad-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["pad", "unicode_center_impl", "unicode_ljust_impl", "unicode_rjust_impl",
      "unicode_zfill_impl", "PyUnicode_New"]
    statement := "For every string, Py_ssize_t width and fill character, ljust/rjust/center/zfill return the string when width <= len, else the documented string of exactly width characters (center's odd character on the left exactly when margin and width are odd; zfill's zeros after a leading sign); the only error is PyUnicode_New's MemoryError, pad's OverflowError being unreachable."
    source := "str.ljust/rjust/center/zfill docs"
    status := .proven, prop := ``PadDoc, thm := some ``padDoc_proven
    notes := "A failure of PyObject_Malloc below PyUnicode_New's limit is not modelled." },
  { id := "unicodeobj-meth-pad-args", pyFile := "Objects/unicodeobject.c"
    pyFns := ["convert_uc", "unicode_center_impl", "unicode_ljust_impl", "unicode_rjust_impl",
      "unicode_zfill_impl"]
    statement := "For every argument objects, center/ljust/rjust/zfill convert the width first (its __index__ errors and OverflowError win), then require the fill character to be a str of exactly one character (TypeError otherwise), then pad."
    source := "str.center/ljust/rjust docs: 'fillchar'; clinic converters"
    status := .proven, prop := ``PadArgs, thm := some ``padArgs_proven }
]

end PyLean.UnicodeObj
