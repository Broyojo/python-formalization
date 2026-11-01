import PyLean.Registry
import PyLean.UnicodeObj.TextProps2
import PyLean.UnicodeObj.TextTranslateX

/-! Registry entries of the text slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def textEntries : List Entry := [
  { id := "unicodeobj-text-case-ascii-fast-path", pyFile := "Objects/unicodeobject.c"
    pyFns := ["ascii_upper_or_lower", "do_upper", "do_lower", "do_upper_or_lower", "do_casefold"]
    statement := "For every ASCII string, ascii_upper_or_lower gives what the general do_upper, do_lower and do_casefold give."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``CaseAsciiFastPath, thm := some ``caseAsciiFastPath_proven },
  { id := "unicodeobj-text-case-output-bound", pyFile := "Objects/unicodeobject.c"
    pyFns := ["do_upper", "do_lower", "do_casefold", "lower_ucs4"]
    statement := "For every valid string, every do_* writes at most 3*len code points, all valid, and reports their maximum in maxchar, so case_operation's buffer cannot overflow and PyUnicode_New picks the canonical kind."
    source := "invariant: no buffer overflow (Py_UCS4 tmp[3*length], mapped[3]); canonical kind"
    status := .proven, prop := ``CaseOutputBound, thm := some ``caseOutputBound_proven },
  { id := "unicodeobj-text-final-sigma-regex", pyFile := "Objects/unicodeobject.c"
    pyFns := ["handle_capital_sigma"]
    statement := "handle_capital_sigma returns U+03C2 exactly in the context \\p{cased}\\p{case-ignorable}*U+03A3!(\\p{case-ignorable}*\\p{cased}) of its own comment and of Unicode's Final_Sigma."
    source := "comment at unicodeobject.c:10047-10051; The Unicode Standard, Table 3-17"
    status := .refuted, prop := ``FinalSigmaRegex, thm := some ``finalSigmaRegex_refuted
    bug := some "unicodeobj-text-final-sigma-cased-ignorable"
    notes := "Differs only for characters that are both Cased and Case_Ignorable (267 code points, e.g. U+02B0)." },
  { id := "unicodeobj-text-final-sigma-no-overlap", pyFile := "Objects/unicodeobject.c"
    pyFns := ["handle_capital_sigma", "lower_ucs4"]
    statement := "With no character around the sigma that is both cased and case-ignorable, handle_capital_sigma implements the Final_Sigma context exactly."
    source := "narrowing of unicodeobj-text-final-sigma-regex"
    status := .proven, prop := ``FinalSigmaNoOverlap, thm := some ``finalSigmaNoOverlap_proven },
  { id := "unicodeobj-text-is-predicates", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_isdecimal_impl", "unicode_isdigit_impl", "unicode_isnumeric_impl", "_PyUnicode_ToDecimalDigit", "_PyUnicode_IsDecimalDigit", "_PyUnicode_ToDigit", "_PyUnicode_IsDigit", "_PyUnicode_IsNumeric"]
    statement := "isspace, isalpha, isalnum, isdecimal, isdigit and isnumeric hold exactly for non-empty strings of such characters (shortcut and loop agree); isalnum is the documented disjunction; decimal strings are digit strings and digit strings numeric."
    source := "docstrings; invariant: shortcut vs loop; stdtypes.rst"
    status := .proven, prop := ``IsPredicates, thm := some ``isPredicates_proven },
  { id := "unicodeobj-text-is-case-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_islower_impl", "unicode_isupper_impl", "_PyUnicode_IsLowercase", "_PyUnicode_IsUppercase", "_PyUnicode_IsTitlecase"]
    statement := "islower and isupper match their docstrings for every string, which also makes their one-character shortcuts agree with their loops; istitle's shortcut agrees with its loop."
    source := "docstrings of str.islower, str.isupper, str.istitle"
    status := .proven, prop := ``IsCaseDoc, thm := some ``isCaseDoc_proven },
  { id := "unicodeobj-text-isidentifier", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_ScanIdentifier", "PyUnicode_IsIdentifier", "unicode_isidentifier_impl"]
    statement := "s.isidentifier() holds exactly for a string starting with an XID_Start character or '_' and continuing with XID_Continue characters."
    source := "PEP 3131, comment at unicodeobject.c:12442-12449"
    status := .proven, prop := ``IsIdentifierSpec, thm := some ``isIdentifierSpec_proven },
  { id := "unicodeobj-text-repr-two-passes", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_repr"]
    statement := "For every string, the size computed by unicode_repr's first pass is the length its second pass writes, and no written character exceeds maxch."
    source := "invariant: no buffer overflow or truncation (first pass sizes the allocation)"
    status := .proven, prop := ``ReprTwoPasses, thm := some ``reprTwoPasses_proven
    notes := "The OverflowError branch needs about PY_SSIZE_T_MAX/10 characters and is not modelled." },
  { id := "unicodeobj-text-isprintable-repr", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_isprintable_impl"]
    statement := "For a string without ' and \\, s.isprintable() holds exactly when repr copies every character unchanged."
    source := "docstring: 'A character is printable if repr() may use it in its output.'"
    status := .proven, prop := ``IsPrintableRepr, thm := some ``isPrintableRepr_proven },
  { id := "unicodeobj-text-translate-fast-slow", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "For every pure table and every string, str.translate equals the per-character reading, whichever of the ASCII fast path, the handover from it, or the general loop runs."
    source := "invariant: fast path vs general path; str.translate docstring"
    status := .proven, prop := ``TranslateFastSlow, thm := some ``translateFastSlow_proven
    notes := "Pure tables only: the fast path caches one lookup per ASCII character, so a stateful __getitem__ is called fewer times." },
  { id := "unicodeobj-text-translate-pure-fast-slow", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_fast_translate", "unicode_fast_translate_lookup", "_PyUnicode_TranslateCharmap", "unicode_translate"]
    statement := "For a table with no state, the ASCII fast path and the general loop give the same result, success or failure, for every string."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``TranslatePureFastSlow, thm := some ``translatePureFastSlow_proven },
  { id := "unicodeobj-text-translate-stateful-table", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_fast_translate"]
    statement := "For any table, including one with state, the ASCII fast path gives what the general loop gives."
    source := "invariant: fast path vs general path"
    status := .refuted, prop := ``TranslateStatefulFastSlow, thm := some ``translateStatefulFastSlow_refuted
    bug := some "unicodeobj-text-translate-stateful-table" },
  { id := "unicodeobj-text-translate-one-lookup", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_fast_translate", "unicode_fast_translate_lookup"]
    statement := "If the fast path finishes, it asked the table about each distinct character of the string exactly once, for every table."
    source := "invariant: what ascii_table is for"
    status := .proven, prop := ``FastPathOneLookupPerChar, thm := some ``fastPathOneLookupPerChar_proven },
  { id := "unicodeobj-text-translate-doc", pyFile := "Objects/unicodeobject.c"
    pyFns := ["charmaptranslate_lookup", "charmaptranslate_output", "unicode_translate"]
    statement := "With allowed answers, str.translate leaves a character on LookupError, deletes it on None, and replaces it with an ordinal or a string, for every table with no state."
    source := "str.translate docs"
    status := .proven, prop := ``TranslateDocReading, thm := some ``translateDocReading_proven },
  { id := "unicodeobj-text-translate-bad-item", pyFile := "Objects/unicodeobject.c"
    pyFns := ["charmaptranslate_lookup", "charmaptranslate_output"]
    statement := "The first answer that is not allowed decides the result: an ordinal out of range, an object of the wrong type, or an exception from __getitem__ other than LookupError."
    source := "str.translate docs; invariant: exact errors"
    status := .proven, prop := ``TranslateBadItem, thm := some ``translateBadItem_proven },
  { id := "unicodeobj-text-translate-callback-position", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_translate_call_errorhandler", "make_translate_exception"]
    statement := "A translate handler's position lands inside the string, and a negative one counts from the end."
    source := "invariant: no out-of-bounds read"
    status := .proven, prop := ``TranslateCallbackPosition, thm := some ``translateCallbackPosition_proven },
  { id := "unicodeobj-text-translate-strict", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "PyUnicode_Translate(s, table, NULL) agrees with the per-character reading whenever no character maps to None."
    source := "invariant: strict mode vs ignore mode"
    status := .proven, prop := ``TranslateStrict, thm := some ``translateStrict_proven },
  { id := "unicodeobj-text-maketrans-translate", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_maketrans_impl"]
    statement := "str.maketrans(x, y, z) followed by translate deletes characters of z and maps x[i] to y[i], last occurrence winning, for all equal-length x, y and every s."
    source := "str.maketrans docstring"
    status := .proven, prop := ``MaketransTranslate, thm := some ``maketransTranslate_proven },
  { id := "unicodeobj-text-bytes-str-twin", pyFile := "Objects/stringlib/ctype.h"
    pyFns := []
    statement := "On ASCII data, bytes and str agree on lower, upper, swapcase, title, capitalize, islower, isupper, istitle, isalpha, isdigit, isalnum, and on isspace away from \\x1c-\\x1f."
    source := "invariant: str vs bytes"
    status := .proven, prop := ``BytesStrTwin, thm := some ``bytesStrTwin_proven
    notes := "Precondition: at most PY_SSIZE_T_MAX//12 characters, the limit of case_operation." },
  { id := "unicodeobj-text-transform-decimal", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_TransformDecimalAndSpaceToASCII"]
    statement := "The result is ASCII for every string, and a string of ASCII below 0x7F, whitespace and decimal digits keeps its length."
    source := "invariant: callers (int, float, complex) parse the result as ASCII"
    status := .proven, prop := ``TransformDecimal, thm := some ``transformDecimal_proven },
  { id := "unicodeobj-text-bloom-superset", pyFile := "Objects/unicodeobject.c"
    pyFns := ["make_bloom_mask"]
    statement := "Every character of a string passes BLOOM on make_bloom_mask of that string."
    source := "invariant: no false negatives"
    status := .proven, prop := ``BloomSuperset, thm := some ``bloomSuperset_proven },
  { id := "unicodeobj-text-dedent-defined", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_Dedent", "search_longest_common_leading_whitespace"]
    statement := "_PyUnicode_Dedent never reaches memcpy with a negative length."
    source := "assert(new_line_len >= 0), unicodeobject.c:14487"
    status := .refuted, prop := ``DedentDefined, thm := some ``dedentDefined_refuted
    bug := some "unicodeobj-text-dedent-negative-memcpy" },
  { id := "unicodeobj-text-dedent-textwrap", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_Dedent", "search_longest_common_leading_whitespace"]
    statement := "For input ending in a newline, _PyUnicode_Dedent equals textwrap.dedent."
    source := "comment at unicodeobject.c:14425-14428"
    status := .refuted, prop := ``DedentMatchesTextwrap, thm := some ``dedentMatchesTextwrap_refuted
    bug := some "unicodeobj-text-dedent-isspace-blank-lines" },
  { id := "unicodeobj-text-case-tables", pyFile := "Objects/unicodectype.c"
    pyFns := ["gettyperecord", "_PyUnicode_ToTitlecase", "_PyUnicode_ToUppercase", "_PyUnicode_ToLowercase", "_PyUnicode_ToLowerFull", "_PyUnicode_ToTitleFull", "_PyUnicode_ToUpperFull", "_PyUnicode_ToFoldedFull", "_PyUnicode_IsCased", "_PyUnicode_IsXidStart", "_PyUnicode_IsXidContinue"]
    statement := "For all 0x110000 code points, the full mappings have 1 to 3 valid code points, the simple mappings are their first element, and the flags relate as documented."
    source := "invariant: mapped[3] in the callers; kernel evaluation of the two-stage tables"
    status := .proven, prop := ``CaseTables, thm := some ``caseTables_proven }
]

end PyLean.UnicodeObj
