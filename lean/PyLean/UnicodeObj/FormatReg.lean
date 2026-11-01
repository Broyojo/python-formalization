import PyLean.Registry
import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatPercentProps

/-! Registry entries of the formatting slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def formatEntries : List Entry := [
  { id := "unicodeobj-format-nul-presentation-type", pyFile := "Python/formatter_unicode.c"
    pyFns := ["parse_internal_render_format_spec", "_PyFloat_FormatAdvancedWriter",
      "_PyComplex_FormatAdvancedWriter"]
    statement := "A format spec ending in NUL is rejected by float and complex, as it is by int and str."
    source := "the presentation types of Doc/library/string.rst; int and str as twins"
    status := .refuted, prop := ``FormatNulRejected, thm := some ``formatNulRejected_refuted
    bug := some "unicodeobj-format-nul-presentation-type" },
  { id := "unicodeobj-format-nul-int-str", pyFile := "Python/formatter_unicode.c"
    pyFns := ["_PyLong_FormatAdvancedWriter", "_PyUnicode_FormatAdvancedWriter",
      "unknown_presentation_type"]
    statement := "For every spec that parses to a NUL type, int and str raise Unknown format code."
    source := "the presentation types of Doc/library/string.rst"
    status := .proven, prop := ``FormatNulIntStr, thm := some ``formatNulIntStr_proven },
  { id := "unicodeobj-format-parse-asserts", pyFile := "Python/formatter_unicode.c"
    pyFns := ["parse_internal_render_format_spec", "get_integer", "is_alignment_token",
      "is_sign_element", "invalid_thousands_separator_type", "invalid_comma_and_underscore"]
    statement := "Every parsed spec has one of the four alignments and a sign of NUL, space, + or -, whatever the input."
    source := "assert (format->align <= 127) and assert (format->sign <= 127), formatter_unicode.c:369-370, in sharp form"
    status := .proven, prop := ``ParseAsserts, thm := some ``parseAsserts_proven },
  { id := "unicodeobj-format-str-shape", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_string_internal", "calc_padding", "fill_padding", "unicode___format___impl"]
    statement := "format(s, spec) is s cut to the precision and padded to the width, left, right or centred, with the extra fill going to the right."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``StrFormatShape, thm := some ``strFormatShape_proven },
  { id := "unicodeobj-format-int-fast-slow", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_long_internal", "calc_number_widths", "fill_number", "get_locale_info"]
    statement := "When format_long_internal takes its _PyLong_FormatWriter shortcut, the general path would give the same text, for every int, in all four bases, with or without #."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``IntFastSlow, thm := some ``intFastSlow_proven },
  { id := "unicodeobj-format-group-loop", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "GroupGenerator_init", "GroupGenerator_next",
      "InsertThousandsGrouping_fill"]
    statement := "The rounds of the grouping loop are bounded by the number of digits."
    source := "invariant: no hang"
    status := .refuted, prop := ``GroupLoopLinear, thm := some ``groupLoopLinear_refuted
    bug := some "unicodeobj-format-grouping-width-loop" },
  { id := "unicodeobj-format-group-digits", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping"]
    statement := "With no padding, dropping the separator from the grouped text gives the digits back, and the count is the text's length."
    source := "invariant: format spec mini-language"
    status := .open, prop := ``GroupDigits
    notes := "Needs an induction over groupLoop with remaining and min_width; not done." },
  { id := "unicodeobj-format-percent-int-fast-slow", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_FormatLong", "mainformatlong"]
    statement := "With no precision, _PyUnicode_FormatLong gives what the fast path _PyLong_FormatWriter writes, for %d, %o and %x, with or without #, for every int."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``PercentIntFastSlow, thm := some ``percentIntFastSlow_proven },
  { id := "unicodeobj-format-percent-star-width", pyFile := "Objects/unicodeobject.c"
    pyFns := ["unicode_format_arg_parse"]
    statement := "A negative * width is negated to a positive width."
    source := "invariant: no signed overflow in C"
    status := .refuted, prop := ``StarWidthNegated, thm := some ``starWidthNegated_refuted
    bug := some "unicodeobj-format-percent-star-width"
    notes := "Known: python/cpython#151847 (open)." },
  { id := "unicodeobj-format-percent-no-directive", pyFile := "Objects/unicodeobject.c"
    pyFns := ["PyUnicode_Format", "unicode_mod"]
    statement := "A format with no % gives itself for an empty tuple, and raises 'not all arguments converted' for a non-empty one."
    source := "printf-style formatting, Doc/library/stdtypes.rst"
    status := .proven, prop := ``PercentNoDirective, thm := some ``percentNoDirective_proven }
]

end PyLean.UnicodeObj
