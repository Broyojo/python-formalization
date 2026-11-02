import PyLean.Registry
import PyLean.UnicodeObj.FormatProps
import PyLean.UnicodeObj.FormatFloat
import PyLean.UnicodeObj.FormatPercentProps
import PyLean.UnicodeObj.FormatStrProps
import PyLean.UnicodeObj.StrFormatDoc
import PyLean.UnicodeObj.IntFormatDoc
import PyLean.UnicodeObj.FormatNumErrors
import PyLean.UnicodeObj.FormatEntryDoc

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
  { id := "unicodeobj-format-str-doc", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyUnicode_FormatAdvancedWriter", "format_obj", "format_string_internal", "calc_padding",
      "fill_padding", "unknown_presentation_type"]
    statement := "For every str or subclass instance, type name and spec the grammar describes: an empty spec gives the string (exact type) or str(obj), its exception included (subclass); otherwise the spec is read as docParse says, a sign, z, # or '=' is refused with its message, the s type cuts to the precision and pads to the width as documented (no width: no padding), and any other type raises 'Unknown format code' with the type name cut to 200 bytes."
    source := "docs: Doc/library/string.rst, Format Specification Mini-Language; the messages as written"
    status := .proven, prop := ``StrFormatSpecDoc, thm := some ``strFormatSpecDoc_proven
    notes := "format_string_internal is StrInternalDoc, for every spec satisfying SpecInv (what the parser returns, parse_inv). The subclass, type-name and __str__ paths are in the fmt_sub difftest." },
  { id := "unicodeobj-format-parse-doc", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["parse_internal_render_format_spec", "get_integer", "is_alignment_token", "is_sign_element",
      "invalid_thousands_separator_type", "invalid_comma_and_underscore"]
    statement := "For every spec written from the grammar's fields (fill, alignment, sign, z, #, 0, width and precision in decimal digits of any script and any size, the separators after each, doubled separators, and a type or a longer tail), the parser returns the documented fields or the documented refusal: digits above sys.maxsize, both separators, a missing precision, an invalid specifier, and a separator the type does not take, with their messages in the order the parser meets them."
    source := "docs: the format_spec grammar of Doc/library/string.rst; round trip of the parser"
    status := .proven, prop := ``ParseDoc, thm := some ``parseDoc_proven },
  { id := "unicodeobj-format-int-as-str", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "For every int within the 4300-digit limit, fill character, alignment <, > or ^ and width, format(n, fill + align + width + 'd') equals format(str(n), fill + align + width + 's'), the documented padding of str(n)."
    source := "the implementation disagreeing with itself (int and str formatting of the same text)"
    status := .proven, prop := ``IntFormatAsStr, thm := some ``intFormatAsStr_proven
    notes := "Goes through the slow path of format_long_internal (a width is given), calc_number_widths and fill_number; smoke-tested on 3.15.2 with 200k ints including 4000-digit ones. The int rows are covered by unicodeobj-format-int-doc." },
  { id := "unicodeobj-format-int-doc", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_long_internal", "calc_number_widths", "fill_number", "get_locale_info"]
    statement := "For every int, exact or not, and every parsed spec with an integer type: no precision and no z; for c no sign and no #, the character, OverflowError outside a C long and outside range(0x110000); for b, o, x, X, d, n the digits of |n| in the base (upper case for X) after the prefix # adds (0X for X), grouped by 3 for , and _ and by 4 for _ with b, o, x, X, zero padded with the fewest zeros that reach the width under 0=, and padded by the alignment; base 10 keeps the 4300-digit limit; fast path included."
    source := "docs: Doc/library/string.rst, integer presentation types, grouping, width"
    status := .proven, prop := ``IntFormatDoc, thm := some ``intFormatDoc_proven },
  { id := "unicodeobj-format-long-entry", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyLong_FormatAdvancedWriter", "format_obj"]
    statement := "For every int or subclass instance, type name, str(obj) and float(obj) outcome (either can raise) and spec the grammar describes: an empty spec gives str(n) (exact int, 4300-digit limit included) or str(obj) (subclass); an integer type is docInt; a float type formats float(obj), its exception included, as docFloat; any other type raises 'Unknown format code' with the type name."
    source := "docs: empty spec is str(); 'float() is used to convert the integer'; the messages as written"
    status := .proven, prop := ``LongEntryDoc, thm := some ``longEntryDoc_proven },
  { id := "unicodeobj-format-str-errors", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "format(s, t) for every str or subclass, type name and one-character type t that is no mini-language field raises 'Unknown format code ...' with the message written out (in hex outside 33..127); ',' with '_' in either order after the width or the precision, and ',' or '_' with the str type, raise their messages."
    source := "docs: the mini-language's presentation types for str; the messages as written"
    status := .proven, prop := ``StrFormatErrors, thm := some ``strFormatErrors_proven },
  { id := "unicodeobj-format-frac-separator-unchecked", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["parse_internal_render_format_spec"]
    statement := "A separator after the precision is refused for the str type, as the separator after the width is."
    source := "docs: ',' and '_' are 'not supported' for presentation types other than d and the float types; twin: the separator after the width"
    status := .refuted, prop := ``FracSeparatorChecked, thm := some ``fracSeparatorChecked_refuted
    bug := some "unicodeobj-format-frac-separator-unchecked" },
  { id := "unicodeobj-format-group-digits", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "GroupGenerator_init", "GroupGenerator_next",
      "InsertThousandsGrouping_fill"]
    statement := "For every grouping size 0 < g < 127, separator, non-empty digits and min_width, the backward call writes the digits with the separator between groups of g counted from the right, padded with exactly the leading zeros that reach min_width (none if it is reached, and never a leading separator), and returns the text's length."
    source := "docs: 'Inserts a comma every 3 digits', zero padding to the width"
    status := .proven, prop := ``GroupingPlacement, thm := some ``groupingPlacement_proven
    notes := "The bug unicodeobj-format-grouping-width-loop (no size or signal check before the counting loop that precedes a doomed allocation) has no Lean statement: the model has no allocator and no interrupts. Its former refutation bounded the rounds by the digits, which CPython never promises, and was withdrawn." },
  { id := "unicodeobj-format-group-fraction", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyUnicode_InsertThousandsGrouping", "GroupGenerator_init", "GroupGenerator_next",
      "InsertThousandsGrouping_fill"]
    statement := "For every grouping size 0 < g < 127, separator and non-empty fraction, the forward call (min_width the fraction's length) writes the fraction with the separator between groups of g counted from the decimal point."
    source := "docs: the grouping option for the fractional part"
    status := .proven, prop := ``GroupingFraction, thm := some ``groupingFraction_proven },
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
  { id := "unicodeobj-format-float-buf", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_float_internal"]
    statement := "For every float and float type, format_float_internal asks PyOS_double_to_string for what the docs give: repr ('r', ADD_DOT_0) for no type and no precision, 'g' with ADD_DOT_0 for no type with a precision, 'g' for n, 'f' of 100x then '%' for %, the type itself otherwise, precision 6 by default, # and z as ALT and NO_NEG_0."
    source := "docs: Doc/library/string.rst, presentation types for float"
    status := .proven, prop := ``FloatBufDoc, thm := some ``floatBufDoc_proven },
  { id := "unicodeobj-format-float-doc", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_float_internal", "calc_number_widths", "fill_number", "parse_number", "get_locale_info",
      "_PyUnicode_InsertThousandsGrouping", "InsertThousandsGrouping_fill", "GroupGenerator_init",
      "GroupGenerator_next"]
    statement := "For every float and every parsed spec with a float type: 'precision too big' above INT_MAX, else the documented PyOS_double_to_string text laid out as documented: the sign option, the integral digits grouped by 3 from the decimal point with , or _ (none for n), the fraction grouped by 3 from the point with the separator after the precision, the rest as is, zero padded under 0= with the fewest grouped zeros that reach the width, else padded by the alignment; fast path included."
    source := "docs: Doc/library/string.rst, grouping, width, alignment"
    status := .proven, prop := ``FloatFormatDoc, thm := some ``floatFormatDoc_proven },
  { id := "unicodeobj-format-float-entry", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyFloat_FormatAdvancedWriter", "format_obj"]
    statement := "For every float or subclass instance, type name, str(obj) outcome (it can raise) and spec the grammar describes: an empty spec gives str(obj); a float type or none is docFloat; any other type raises 'Unknown format code' with the type name."
    source := "docs: empty spec is str(); the float presentation types"
    status := .proven, prop := ``FloatEntryDoc, thm := some ``floatEntryDoc_proven },
  { id := "unicodeobj-format-complex-entry", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyComplex_FormatAdvancedWriter", "format_obj"]
    statement := "For every complex or subclass instance, type name, str(obj) outcome (it can raise) and spec the grammar describes: an empty spec gives str(obj); a complex type or none goes to format_complex_internal; any other type raises 'Unknown format code' with the type name."
    source := "docs: empty spec is str(); the complex presentation types"
    status := .proven, prop := ``ComplexEntryDoc, thm := some ``complexEntryDoc_proven },
  { id := "unicodeobj-format-float-fast-slow", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "The fast path of format_float_internal gives what the general path gives, for every float and every spec that takes it."
    source := "invariant: fast path vs slow path"
    status := .proven, prop := ``FloatFastSlowAgree, thm := some ``floatFastSlowAgree_proven },
  { id := "unicodeobj-format-float-width", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "format(x, spec) is at least width characters long, for every float and every spec, separators included."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``FloatWidthIsMinimum, thm := some ``floatWidthIsMinimum_proven },
  { id := "unicodeobj-format-int-width", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "format(n, spec) is at least width characters long, for every int and every spec, on the prefix path of '#x' and for the 'c' type."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``IntWidthIsMinimum, thm := some ``intWidthIsMinimum_proven },
  { id := "unicodeobj-format-float-grouping", pyFile := "Objects/unicode_formatter.c"
    pyFns := []
    statement := "Adding ',' or '_' to the integer part, the fraction or both changes a float's text only by the separators, including '.3_f', where the integer loop runs with an empty separator."
    source := "invariant: a separator only separates"
    status := .proven, prop := ``FloatGroupingOnlyInserts, thm := some ``floatGroupingOnlyInserts_proven },
  { id := "unicodeobj-format-complex-internal", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_complex_internal"]
    statement := "With a presentation type, format(z, spec) is format(z.real, spec) + format(z.imag, '+' + spec) + 'j' with the padding of the spec."
    source := "format spec mini-language, Doc/library/string.rst"
    status := .proven, prop := ``ComplexPartsCompose, thm := some ``complexPartsCompose_proven },
  { id := "unicodeobj-format-complex-repr", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_complex_internal"]
    statement := "A spec with no type, precision or option gives str(z): format_complex_internal and complex_repr drop the real part and add the parentheses under the same rule, for every complex, nan and -0.0 included."
    source := "format() docs; invariant: format vs repr"
    status := .proven, prop := ``ComplexOmittedTypeIsRepr, thm := some ``complexOmittedTypeIsRepr_proven },
  { id := "unicodeobj-format-complex-width", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_complex_internal"]
    statement := "format(z, spec) is at least width characters long, for every complex and every spec."
    source := "format spec docs: width is the minimum total field width"
    status := .proven, prop := ``ComplexWidthIsMinimum, thm := some ``complexWidthIsMinimum_proven },
  { id := "unicodeobj-format-float-complex-errors", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["format_float_internal", "format_complex_internal", "_PyFloat_FormatAdvancedWriter",
      "_PyComplex_FormatAdvancedWriter"]
    statement := "For every float and complex: a precision above INT_MAX raises 'precision too big'; for complex, then zero padding and then '=' alignment raise their messages; and a one-character spec whose character is no mini-language field, no float (or complex) type and not NUL raises 'Unknown format code ...'."
    source := "unicode_formatter.c:1403-1406, 1576-1595, 1907-1924, 1946-1962; the documented float and complex presentation types"
    status := .proven, prop := ``FloatComplexErrors, thm := some ``floatComplexErrors_proven
    notes := "Checked on 3.15.2 for every code point below 0x3000 on 1.5 and nan, real and complex, and the checks on inf, nan, -0.0 and 1e300." },
  { id := "unicodeobj-format-float-nul-type", pyFile := "Objects/unicode_formatter.c"
    pyFns := ["_PyFloat_FormatAdvancedWriter", "_PyComplex_FormatAdvancedWriter"]
    statement := "float and complex reject a NUL presentation type as int and str do."
    source := "twin: int and str raise for format(x, '\\x00'); the documented presentation types"
    status := .refuted, prop := ``NulTypeRejected, thm := some ``nulTypeRejected_refuted
    bug := some "unicodeobj-format-nul-type" },
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
