import PyLean.Registry
import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatFloat
import PyLean.UnicodeObj.FormatPercentProps
import PyLean.UnicodeObj.FormatStrProps

/-! Registry entries of the formatting slice. -/

namespace PyLean.UnicodeObj

open PyLean.Registry

def formatEntries : List Entry := [
  { id := "unicodeobj-format-nul-presentation-type", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "A format spec ending in NUL is rejected by float and complex, as it is by int and str."
    source := "the presentation types of Doc/library/string.rst; int and str as twins"
    status := .refuted, prop := ``FormatNulRejected, thm := some ``formatNulRejected_refuted
    bug := some "unicodeobj-format-nul-presentation-type" },
  { id := "unicodeobj-format-nul-int-str", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "For every spec that parses to a NUL type, int and str raise Unknown format code."
    source := "the presentation types of Doc/library/string.rst"
    status := .proven, prop := ``FormatNulIntStr, thm := some ``formatNulIntStr_proven },
  { id := "unicodeobj-format-parse-asserts", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "Every parsed spec has one of the four alignments and a sign of NUL, space, + or -, whatever the input."
    source := "assert (format->align <= 127) and assert (format->sign <= 127), unicode_formatter.c:604-605, in sharp form"
    status := .proven, prop := ``ParseAsserts, thm := some ``parseAsserts_proven },
  { id := "unicodeobj-format-str-shape", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "format(s, spec) is s cut to the precision and padded to the width, left, right or centred, with the extra fill going to the right."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``StrFormatShape, thm := some ``strFormatShape_proven },
  { id := "unicodeobj-format-int-fast-slow", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "When format_long_internal takes its _PyLong_FormatWriter shortcut, the general path would give the same text, for every int, in all four bases, with or without #."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``IntFastSlow, thm := some ``intFastSlow_proven },
  { id := "unicodeobj-format-group-loop", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "GroupGenerator_init", "GroupGenerator_next", "InsertThousandsGrouping_fill"]
    statement := "The rounds of the grouping loop are bounded by the number of digits."
    source := "invariant: no hang"
    status := .refuted, prop := ``GroupLoopLinear, thm := some ``groupLoopLinear_refuted
    bug := some "unicodeobj-format-grouping-width-loop" },
  { id := "unicodeobj-format-group-digits", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping"]
    statement := "With no padding, dropping the separator from the grouped text gives the digits back, and the count is the text's length."
    source := "invariant: format spec mini-language"
    status := .proven, prop := ``GroupDigits, thm := some ``groupDigits_proven },
  { id := "unicodeobj-format-percent-int-fast-slow", pyFile := "Objects/unicode_format.c"
    pyFns := []
    statement := "With no precision, _PyUnicode_FormatLong gives what the fast path _PyLong_FormatWriter writes, for %d, %o and %x, with or without #, for every int."
    source := "invariant: fast path vs general path"
    status := .proven, prop := ``PercentIntFastSlow, thm := some ``percentIntFastSlow_proven },
  { id := "unicodeobj-format-percent-star-width", pyFile := "Objects/unicode_format.c"
    pyFns := []
    statement := "A * width comes out as its size with the left-justify flag if it was negative, and PY_SSIZE_T_MIN, which has no negation, raises OverflowError like a width too big for Py_ssize_t."
    source := "invariant: no signed overflow in C; unicode_format.c:558-573"
    status := .proven, prop := ``StarWidthSpec, thm := some ``starWidthSpec_proven
    notes := "3.14.7 negated PY_SSIZE_T_MIN: python/cpython#151847, fixed by 3.15.2." },
  { id := "unicodeobj-format-parse-number", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "parse_number splits a number into digits, decimal point, fraction and remainder with nothing lost, for every string."
    source := "invariant"
    status := .proven, prop := ``ParseNumberSplit, thm := some ``parseNumberSplit_proven },
  { id := "unicodeobj-format-float-internal", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "For every float and every spec with no separator, format(x, spec) is the buffer of PyOS_double_to_string with the sign the spec asks for and the padding of its width, fill and alignment."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``FloatSpecLayout, thm := some ``floatSpecLayout_proven },
  { id := "unicodeobj-format-float-fast-slow", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "The fast path of format_float_internal gives what the general path gives, for every float and every spec that takes it."
    source := "invariant: fast path vs slow path"
    status := .proven, prop := ``FloatFastSlowAgree, thm := some ``floatFastSlowAgree_proven },
  { id := "unicodeobj-format-float-width", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["calc_number_widths", "fill_number"]
    statement := "format(x, spec) is at least width characters long, for every float and every spec, separators included."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``FloatWidthIsMinimum, thm := some ``floatWidthIsMinimum_proven },
  { id := "unicodeobj-format-int-width", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["calc_number_widths", "fill_number"]
    statement := "format(n, spec) is at least width characters long, for every int and every spec, on the prefix path of '#x' and for the 'c' type."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``IntWidthIsMinimum, thm := some ``intWidthIsMinimum_proven },
  { id := "unicodeobj-format-float-grouping", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "InsertThousandsGrouping_fill", "GroupGenerator_next"]
    statement := "Adding ',' or '_' to the integer part, the fraction or both changes a float's text only by the separators, including '.3_f', where the integer loop runs with an empty separator."
    source := "invariant: a separator only separates"
    status := .proven, prop := ``FloatGroupingOnlyInserts, thm := some ``floatGroupingOnlyInserts_proven },
  { id := "unicodeobj-format-complex-internal", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "With a presentation type, format(z, spec) is format(z.real, spec) + format(z.imag, '+' + spec) + 'j' with the padding of the spec."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``ComplexPartsCompose, thm := some ``complexPartsCompose_proven },
  { id := "unicodeobj-format-complex-repr", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "A spec with no type, precision or option gives str(z): format_complex_internal and complex_repr drop the real part and add the parentheses under the same rule, for every complex, nan and -0.0 included."
    source := "format() docs; invariant: format vs repr"
    status := .proven, prop := ``ComplexOmittedTypeIsRepr, thm := some ``complexOmittedTypeIsRepr_proven },
  { id := "unicodeobj-format-complex-width", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "format(z, spec) is at least width characters long, for every complex and every spec."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``ComplexWidthIsMinimum, thm := some ``complexWidthIsMinimum_proven },
  { id := "unicodeobj-format-percent-float-errors", pyFile := "Objects/unicode_format.c"
    pyFns := ["formatfloat"]
    statement := "A %e, %f or %g directive of None, a str or a dict raises TypeError naming the conversion, the argument and its type, and an int too large for a double keeps its OverflowError."
    source := "unicode_format.c:136-144; invariant: exact error messages"
    status := .proven, prop := ``PercentFloatErrors, thm := some ``percentFloatErrors_proven },
  { id := "unicodeobj-format-percent-float", pyFile := "Objects/unicode_format.c"
    pyFns := ["formatfloat"]
    statement := "A %e, %f or %g directive gives the text of format() with the matching spec, for every float, flag, width and precision: unicode_format_arg_output and calc_number_widths agree on the layout."
    source := "invariant: % vs format"
    status := .proven, prop := ``PercentFloatMatchesFormat, thm := some ``percentFloatMatchesFormat_proven },
  { id := "unicodeobj-format-str-builtin", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["do_string_format", "build_string", "do_markup", "output_markup", "MarkupIterator_next", "parse_field", "field_name_split", "AutoNumber_Init"]
    statement := "'{0:spec}'.format(x) is format(x, spec), for every object and every spec with no braces."
    source := "Doc/library/string.rst: a replacement field calls format()"
    status := .proven, prop := ``FormatFieldIsBuiltin, thm := some ``formatFieldIsBuiltin_proven },
  { id := "unicodeobj-format-str-render-field", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["render_field"]
    statement := "render_field, which skips the __format__ lookup for the exact types, gives what format(obj, spec) gives, for every object and spec."
    source := "invariant: fast path vs generic path"
    status := .proven, prop := ``RenderFieldIsFormat, thm := some ``renderFieldIsFormat_proven },
  { id := "unicodeobj-format-str-autonumber", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["field_name_split"]
    statement := "The numbering rule holds for every field name and state: an empty name takes the next number and is refused after manual numbering, a numeric name is refused after automatic numbering, and any other name leaves the state alone."
    source := "Doc/library/string.rst: auto-numbering"
    status := .proven, prop := ``AutoNumberingRule, thm := some ``autoNumberingRule_proven },
  { id := "unicodeobj-format-str-get-integer", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["get_integer"]
    statement := "A field index in any script of decimal digits is read without wrapping: its value if it fits Py_ssize_t, otherwise ValueError."
    source := "invariant: no silent wraparound"
    status := .proven, prop := ``GetIntegerNoWrap, thm := some ``getIntegerNoWrap_proven },
  { id := "unicodeobj-format-str-conversion-rejected", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := []
    statement := "Every conversion character but r, s, a and NUL is refused with its exact error, for every object."
    source := "Doc/library/string.rst: conversion"
    status := .proven, prop := ``ConversionRejected, thm := some ``conversionRejected_proven },
  { id := "unicodeobj-format-nul-conversion", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["parse_field", "output_markup"]
    statement := "Every conversion character but r, s and a is refused."
    source := "Doc/library/string.rst: conversion"
    status := .refuted, prop := ``ConversionChecked, thm := some ``conversionChecked_refuted
    bug := some "unicodeobj-format-nul-conversion" },
  { id := "unicodeobj-format-str-escape", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["MarkupIterator_next", "do_markup"]
    statement := "Doubling every brace of any string and formatting gives the string back, whatever the arguments."
    source := "Doc/library/string.rst: {{ and }}"
    status := .proven, prop := ``BraceEscapeRoundTrip, thm := some ``braceEscapeRoundTrip_proven },
  { id := "unicodeobj-format-str-format-map", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := []
    statement := "format_map refuses a positional field, for every field name, mapping and state, before the mapping is touched."
    source := "str.format_map docs; invariant: no positional arguments"
    status := .proven, prop := ``FormatMapNoPositional, thm := some ``formatMapNoPositional_proven },
  { id := "unicodeobj-format-str-parser-accepts", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["MarkupIterator_next"]
    statement := "Whatever str.format accepts, _string.formatter_parser accepts."
    source := "invariant: string.Formatter vs str.format"
    status := .proven, prop := ``FormatterParserAccepts, thm := some ``formatterParserAccepts_proven },
  { id := "unicodeobj-format-str-parser-reads", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["SubString_new_object", "SubString_new_object_or_empty"]
    statement := "formatter_parser reports a field's name and spec, gives None in all three places for plain text, and refuses anything but a str."
    source := "string.Formatter.parse docs"
    status := .proven, prop := ``FormatterParserReads, thm := some ``formatterParserReads_proven },
  { id := "unicodeobj-format-str-field-name", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := []
    statement := "formatter_field_name_split reads back every chain of attributes and non-numeric items."
    source := "invariant: round trip"
    status := .proven, prop := ``FieldNameRoundTrip, thm := some ``fieldNameRoundTrip_proven },
  { id := "unicodeobj-format-str-nested-spec", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["output_markup", "build_string"]
    statement := "A nested field's text is the spec and is not parsed again: '{0:{1}}'.format(x, spec) is format(x, spec), for every object and every string."
    source := "Doc/library/string.rst: nested replacement fields"
    status := .proven, prop := ``NestedSpecExpands, thm := some ``nestedSpecExpands_proven },
  { id := "unicodeobj-format-str-nested-auto", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["output_markup", "field_name_split"]
    statement := "A nested field shares the outer numbering, and the outer field numbers first: '{:{}}'.format(x, spec) is format(x, spec)."
    source := "Doc/library/string.rst: auto-numbering"
    status := .proven, prop := ``NestedAutoNumbering, thm := some ``nestedAutoNumbering_proven },
  { id := "unicodeobj-format-str-recursion-limit", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["build_string", "output_markup"]
    statement := "'{0:{1:{2}}}' raises 'Max string recursion exceeded', for every object, before anything is rendered."
    source := "PEP 3101; do_string_format comment"
    status := .proven, prop := ``RecursionLimit, thm := some ``recursionLimit_proven },
  { id := "unicodeobj-format-str-many-fields", pyFile := "Objects/stringlib/unicode_format.h"
    pyFns := ["do_markup", "MarkupIterator_next", "field_name_split"]
    statement := "'{}{}...' is the concatenation of each object formatted with an empty spec, in order, and the first failure is the exception, for every list of objects."
    source := "Doc/library/string.rst: auto-numbering"
    status := .proven, prop := ``AutoFieldsConcat, thm := some ``autoFieldsConcat_proven },
  { id := "unicodeobj-format-percent-no-directive", pyFile := "Objects/unicode_format.c"
    pyFns := []
    statement := "A format with no % gives itself for an empty tuple, and raises 'not all arguments converted' for a non-empty one."
    source := "printf-style formatting, Doc/library/stdtypes.rst"
    status := .proven, prop := ``PercentNoDirective, thm := some ``percentNoDirective_proven }
]

end PyLean.UnicodeObj
