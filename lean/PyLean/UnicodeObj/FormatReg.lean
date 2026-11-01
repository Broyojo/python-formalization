import PyLean.Registry
import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatFloat
import PyLean.UnicodeObj.FormatPercentProps

/-! Registry entries of the formatting slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def formatEntries : List Entry := [
  { id := "unicodeobj-format-nul-presentation-type", pyFile := "Python/formatter_unicode.c"
    pyFns := []
    statement := "A format spec ending in NUL is rejected by float and complex, as it is by int and str."
    source := "the presentation types of Doc/library/string.rst; int and str as twins"
    status := .refuted, prop := ``FormatNulRejected, thm := some ``formatNulRejected_refuted
    bug := some "unicodeobj-format-nul-presentation-type" },
  { id := "unicodeobj-format-nul-int-str", pyFile := "Python/formatter_unicode.c"
    pyFns := []
    statement := "For every spec that parses to a NUL type, int and str raise Unknown format code."
    source := "the presentation types of Doc/library/string.rst"
    status := .proven, prop := ``FormatNulIntStr, thm := some ``formatNulIntStr_proven },
  { id := "unicodeobj-format-parse-asserts", pyFile := "Python/formatter_unicode.c"
    pyFns := []
    statement := "Every parsed spec has one of the four alignments and a sign of NUL, space, + or -, whatever the input."
    source := "assert (format->align <= 127) and assert (format->sign <= 127), formatter_unicode.c:369-370, in sharp form"
    status := .proven, prop := ``ParseAsserts, thm := some ``parseAsserts_proven },
  { id := "unicodeobj-format-str-shape", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_string_internal", "calc_padding", "fill_padding"]
    statement := "format(s, spec) is s cut to the precision and padded to the width, left, right or centred, with the extra fill going to the right."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``StrFormatShape, thm := some ``strFormatShape_proven },
  { id := "unicodeobj-format-int-fast-slow", pyFile := "Python/formatter_unicode.c"
    pyFns := []
    statement := "When format_long_internal takes its _PyLong_FormatWriter shortcut, the general path would give the same text, for every int, in all four bases, with or without #."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``IntFastSlow, thm := some ``intFastSlow_proven },
  { id := "unicodeobj-format-group-loop", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "GroupGenerator_init", "GroupGenerator_next", "InsertThousandsGrouping_fill"]
    statement := "The rounds of the grouping loop are bounded by the number of digits."
    source := "invariant: no hang"
    status := .refuted, prop := ``GroupLoopLinear, thm := some ``groupLoopLinear_refuted
    bug := some "unicodeobj-format-grouping-width-loop" },
  { id := "unicodeobj-format-group-digits", pyFile := "Objects/unicodeobject.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping"]
    statement := "With no padding, dropping the separator from the grouped text gives the digits back, and the count is the text's length."
    source := "invariant: format spec mini-language"
    status := .proven, prop := ``GroupDigits, thm := some ``groupDigits_proven },
  { id := "unicodeobj-format-percent-int-fast-slow", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "With no precision, _PyUnicode_FormatLong gives what the fast path _PyLong_FormatWriter writes, for %d, %o and %x, with or without #, for every int."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``PercentIntFastSlow, thm := some ``percentIntFastSlow_proven },
  { id := "unicodeobj-format-percent-star-width", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "A negative * width is negated to a positive width."
    source := "invariant: no signed overflow in C"
    status := .refuted, prop := ``StarWidthNegated, thm := some ``starWidthNegated_refuted
    bug := some "unicodeobj-format-percent-star-width"
    notes := "Known: python/cpython#151847 (open)." },
  { id := "unicodeobj-format-parse-number", pyFile := "Python/formatter_unicode.c"
    pyFns := ["parse_number"]
    statement := "parse_number splits a number into digits, decimal point, fraction and remainder with nothing lost, for every string."
    source := "invariant"
    status := .proven, prop := ``ParseNumberSplit, thm := some ``parseNumberSplit_proven },
  { id := "unicodeobj-format-float-internal", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_float_internal"]
    statement := "For every float and every spec with no separator, format(x, spec) is the buffer of PyOS_double_to_string with the sign the spec asks for and the padding of its width, fill and alignment."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``FloatSpecLayout, thm := some ``floatSpecLayout_proven },
  { id := "unicodeobj-format-float-fast-slow", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_float_internal"]
    statement := "The fast path of format_float_internal gives what the general path gives, for every float and every spec that takes it."
    source := "invariant: fast path vs slow path"
    status := .proven, prop := ``FloatFastSlowAgree, thm := some ``floatFastSlowAgree_proven },
  { id := "unicodeobj-format-float-width", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_float_internal", "calc_number_widths", "fill_number"]
    statement := "format(x, spec) is at least width characters long, for every float and every spec, separators included."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``FloatWidthIsMinimum, thm := some ``floatWidthIsMinimum_proven },
  { id := "unicodeobj-format-int-width", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_long_internal", "calc_number_widths", "fill_number"]
    statement := "format(n, spec) is at least width characters long, for every int and every spec, on the prefix path of '#x' and for the 'c' type."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``IntWidthIsMinimum, thm := some ``intWidthIsMinimum_proven },
  { id := "unicodeobj-format-float-grouping", pyFile := "Python/formatter_unicode.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "InsertThousandsGrouping_fill", "GroupGenerator_next"]
    statement := "Adding ',' or '_' to the integer part, the fraction or both changes a float's text only by the separators, including '.3_f', where the integer loop runs with an empty separator."
    source := "invariant: a separator only separates"
    status := .proven, prop := ``FloatGroupingOnlyInserts, thm := some ``floatGroupingOnlyInserts_proven },
  { id := "unicodeobj-format-complex-internal", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_complex_internal"]
    statement := "With a presentation type, format(z, spec) is format(z.real, spec) + format(z.imag, '+' + spec) + 'j' with the padding of the spec."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``ComplexPartsCompose, thm := some ``complexPartsCompose_proven },
  { id := "unicodeobj-format-complex-repr", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_complex_internal"]
    statement := "A spec with no type, precision or option gives str(z): format_complex_internal and complex_repr drop the real part and add the parentheses under the same rule, for every complex, nan and -0.0 included."
    source := "format() docs; invariant: format vs repr"
    status := .proven, prop := ``ComplexOmittedTypeIsRepr, thm := some ``complexOmittedTypeIsRepr_proven },
  { id := "unicodeobj-format-complex-width", pyFile := "Python/formatter_unicode.c"
    pyFns := ["format_complex_internal"]
    statement := "format(z, spec) is at least width characters long, for every complex and every spec."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``ComplexWidthIsMinimum, thm := some ``complexWidthIsMinimum_proven },
  { id := "unicodeobj-format-percent-float", pyFile := "Objects/unicodeobject.c"
    pyFns := ["formatfloat"]
    statement := "A %e, %f or %g directive gives the text of format() with the matching spec, for every float, flag, width and precision: unicode_format_arg_output and calc_number_widths agree on the layout."
    source := "invariant: % vs format"
    status := .proven, prop := ``PercentFloatMatchesFormat, thm := some ``percentFloatMatchesFormat_proven },
  { id := "unicodeobj-format-percent-no-directive", pyFile := "Objects/unicodeobject.c"
    pyFns := []
    statement := "A format with no % gives itself for an empty tuple, and raises 'not all arguments converted' for a non-empty one."
    source := "printf-style formatting, Doc/library/stdtypes.rst"
    status := .proven, prop := ``PercentNoDirective, thm := some ``percentNoDirective_proven }
]

end PyLean.UnicodeObj
