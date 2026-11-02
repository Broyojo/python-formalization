import PyLean.Registry
import PyLean.UnicodeObj.MethCase
import PyLean.UnicodeObj.MethStripProps
import PyLean.UnicodeObj.MethPadProps
import PyLean.UnicodeObj.MethTailProps
import PyLean.UnicodeObj.MethSliceProps
import PyLean.UnicodeObj.MethPartition

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
    status := .proven, prop := ``PadArgs, thm := some ``padArgs_proven },
  { id := "unicodeobj-meth-substring-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_Substring"]
    statement := "For every string and pair of Py_ssize_t, PyUnicode_Substring raises IndexError for a negative index and otherwise returns the Python slice str[start:end], through its shortcuts for the whole string, an empty result and the ASCII and kind copies."
    source := "C API docs of PyUnicode_Substring"
    status := .proven, prop := ``SubstringDoc, thm := some ``substringDoc_proven },
  { id := "unicodeobj-meth-tailmatch-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["tailmatch"]
    statement := "For all strings, start, end and directions, tailmatch answers whether sub is a prefix (suffix) of s[start:end], nothing matching when the adjusted start plus len(sub) passes the clipped end, through the memcmp for one kind and the first/last/middle comparison for two."
    source := "str.startswith/endswith docs; invariant: kind paths agree"
    status := .proven, prop := ``TailmatchDoc, thm := some ``tailmatchDoc_proven },
  { id := "unicodeobj-meth-tailmatch-api", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_Tailmatch", "tailmatch"]
    statement := "For all arguments, PyUnicode_Tailmatch raises TypeError for a str or substr that is not a str (str checked first) and otherwise returns 1 or 0 as the documented tail match."
    source := "C API docs of PyUnicode_Tailmatch"
    status := .proven, prop := ``TailmatchApi, thm := some ``tailmatchApi_proven },
  { id := "unicodeobj-meth-startsends-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_startswith_impl", "unicode_endswith_impl", "tailmatch"]
    statement := "For every string and Py_ssize_t start and end, startswith/endswith answer the tail match for a str, any() over a tuple of str, raise TypeError at the first non-str tuple element only when no earlier element matched, and TypeError for any other argument."
    source := "str.startswith/endswith docs"
    status := .proven, prop := ``StartsEndsDoc, thm := some ``startsEndsDoc_proven },
  { id := "unicodeobj-meth-removeaffix-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_removeprefix_impl", "unicode_removesuffix_impl", "tailmatch",
      "PyUnicode_Substring"]
    statement := "For every string, removeprefix returns string[len(prefix):] when it starts with the prefix and the string otherwise; removesuffix returns string[:-len(suffix)] when it ends with a non-empty suffix and the string otherwise; a non-str argument raises TypeError."
    source := "str.removeprefix/removesuffix docs"
    status := .proven, prop := ``RemoveAffixDoc, thm := some ``removeAffixDoc_proven },
  { id := "unicodeobj-meth-slice-twin", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_BinarySlice", "unicode_subscript", "PyUnicode_Substring"]
    statement := "For every string and every pair of bound objects (any ints, None, objects whose __index__ answers or raises, objects without __index__), the 3.15 fast path _PyUnicode_BinarySlice behind s[a:b] gives what unicode_subscript gives for s[slice(a, b)], result or exception; for int bounds both are Python's slice."
    source := "invariant: fast path vs general path (BINARY_SLICE vs BINARY_SUBSCR); sequence slicing docs"
    status := .proven, prop := ``SliceTwin, thm := some ``sliceTwin_proven },
  { id := "unicodeobj-meth-index-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_subscript", "unicode_getitem"]
    statement := "For every string and object i, s[i] is the character at i (from the end when negative) for an index in [-len, len), IndexError for any other int, the __index__ exception when it raises, and TypeError for an object without __index__."
    source := "sequence indexing docs"
    status := .proven, prop := ``IndexDoc, thm := some ``indexDoc_proven },
  { id := "unicodeobj-meth-partition-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_Partition", "PyUnicode_RPartition", "unicode_partition",
      "unicode_rpartition", "stringlib_partition", "stringlib_rpartition"]
    statement := "For every string and separator object, partition/rpartition split at the first/last occurrence or return the string with two empty strings, raise ValueError for an empty separator and TypeError for a non-str; the shortcut for a separator of a wider kind or greater length (the length test new in 3.15) agrees with the general path."
    source := "str.partition/rpartition docs; invariant: shortcut vs general path"
    status := .proven, prop := ``PartitionDoc, thm := some ``partitionDoc_proven
    notes := "FASTSEARCH is modelled by its result (StrSearch.findL/rfindL), the first/last occurrence." }
]

end PyLean.UnicodeObj
