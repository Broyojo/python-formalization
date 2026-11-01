import PyLean.Registry
import PyLean.Decimal.Diff
import PyLean.Decimal.Refute
import PyLean.Decimal.TupleProps
import PyLean.Decimal.Props

/-!
`Lib/_pydecimal.py` vs `Modules/_decimal/` (libmpdec), CPython 3.14.7.

Both twins are modelled side by side where their code differs (string and
tuple constructors, `__format__` spec handling, `hash`, integer conversions,
`as_integer_ratio`, `Decimal(int)`); the context arithmetic (`_fix`,
`_rescale`, `quantize`, `to_integral_*`, `round`, `normalize`, `+ - *`,
`compare_total`, `copy_sign`) is modelled from `_pydecimal` and checked
against both twins by `difftest/decimal_diff.py`. Division, sqrt, exp, ln,
log10, pow and floats are out of scope.

The difftest and reproducers run on interpreters built with the bundled
libmpdec 2.5.1, whose source these line numbers cite. A build against system
libmpdec 4.0.1 (Homebrew) differs only in the format-spec parser, which also
takes `z`; Format.lean models both.
-/

namespace PyLean.Decimal

open PyLean.Registry

def entries : List Entry := [
  { id := "decimal-parse-c-accepts-py", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["Decimal.__new__ (str)", "numeric_as_ascii", "mpd_qset_string", "_pydecimal._parser"]
    statement := "For every string s, if _pydecimal.Decimal(s) returns a value within the C module's documented limits, _decimal.Decimal(s) returns the same value."
    source := "twin agreement (both implement the spec's numeric-string syntax, whose letters are ASCII, case-insensitive)"
    status := .refuted, prop := ``ParseCAcceptsPy, thm := some ``parseCAcceptsPy_refuted
    bug := some "decimal-pydecimal-parser-unicode-casefold"
    notes := "Decimal('ınf') (U+0131), 'İnfinity' (U+0130), 'ſNaN' (U+017F): _pydecimal's regex is compiled with re.IGNORECASE and matches these by Unicode case folding; _decimal rejects them. Exhaustively, these three code points are the only non-ASCII characters any letter of the pattern matches." },
  { id := "decimal-parse-py-accepts-c", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__ (str)"]
    statement := "For every string s, if _decimal.Decimal(s) returns a value, _pydecimal.Decimal(s) returns the same value."
    source := "twin agreement; decimal docs: 'user alterable precision ... which can be as large as needed for a given problem' (Doc/library/decimal.rst:63-65)"
    status := .refuted, prop := ``ParsePyAcceptsC, thm := some ``parsePyAcceptsC_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('1'*4301): _pydecimal stores str(int(intpart+fracpart)), and int() refuses more than 4300 digits (leading zeros included), so it raises ValueError. Known and declined upstream: python/cpython#96589, closed as not planned." },
  { id := "decimal-str-roundtrip-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__str__", "Decimal.__new__ (str)"]
    statement := "For every decimal d within the C limits, Decimal(str(d)) == d in _pydecimal, with the same sign, coefficient and exponent."
    source := "invariant (__repr__ comment, _pydecimal.py:981: 'eval(repr(d)) == d')"
    status := .refuted, prop := ``StrRoundTripPy, thm := some ``strRoundTripPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "d = Decimal(10**4300) built from a tuple: str(d) has 4301 digits and cannot be parsed back." },
  { id := "decimal-hash-twins-agree", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__hash__"]
    statement := "Whenever _decimal hashes a decimal, _pydecimal hashes it to the same int."
    source := "twin agreement; Built-in Types, Hashing of numeric types"
    status := .refuted, prop := ``HashTwinsAgree, thm := some ``hashTwinsAgree_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "hash(Decimal(10**4300)): __hash__ evaluates int(self._int)." },
  { id := "decimal-int-conversions-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floor__", "Decimal.__ceil__", "Decimal.__round__"]
    statement := "For every finite decimal, math.floor, math.ceil and round() of a _pydecimal.Decimal return the correctly rounded int (the one _decimal returns)."
    source := "__floor__/__ceil__/__round__ docstrings, _pydecimal.py:1784-1873"
    status := .refuted, prop := ``IntConversionsPy, thm := some ``intConversionsPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "math.floor(Decimal('1E+4300')): _rescale(0, ...) pads the coefficient to 4301 digits and int() of it fails, although int(Decimal('1E+4300')) works." },
  { id := "decimal-mul-no-valueerror-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "Decimal.__add__", "_WorkRep", "_normalize"]
    statement := "Under every context, _pydecimal's * returns a value or raises a trapped decimal signal; it never raises ValueError."
    source := "invariant; twin agreement (_decimal rounds the product to the context precision)"
    status := .refuted, prop := ``MulNoValueErrorPy, thm := some ``mulNoValueErrorPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('1'*2200) * Decimal('1'*2200) at the default precision 28: __mul__ formats the exact 4400-digit product with str() before rounding. + and - fail the same way through _WorkRep and _normalize. Both operands are under the limit here, but the root cause is the one declined in python/cpython#96589." },
  { id := "decimal-tuple-twins-agree", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__ (tuple)", "dectuple_as_str"]
    statement := "For every tuple (sign, digits, exp) with |exp| <= 10**17 and at most 10**17 digits, if _pydecimal.Decimal(t) succeeds then _decimal.Decimal(t) succeeds and str() of both agree."
    source := "twin agreement; Decimal docs: 'three components, a sign ..., a tuple of digits, and an integer exponent' (Doc/library/decimal.rst:395-397)"
    status := .refuted, prop := ``TupleTwinsAgree, thm := some ``tupleTwinsAgree_refuted
    bug := some "decimal-pydecimal-tuple-bool-digits"
    notes := "Decimal((0, (True,), 0)) is Decimal('True') in _pydecimal (the bool passes isinstance(digit, int) and is joined with str()) and Decimal('1') in _decimal. Also Decimal((0, None, 'F')): _pydecimal ignores the coefficient of an infinity, _decimal requires a tuple of digits." },
  { id := "decimal-tuple-twins-agree-int-digits", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__ (tuple)", "dectuple_as_str", "Decimal.__str__"]
    statement := "For every tuple whose coefficient is a tuple of ints in 0..9, with |exp| <= 10**17 and at most 10**17 digits, if _pydecimal.Decimal(t) succeeds then _decimal.Decimal(t) succeeds and str() of both agree (leading zeros, NaN payloads, any sign or exponent value)."
    source := "twin agreement (narrowed version of decimal-tuple-twins-agree)"
    status := .proven, prop := ``TupleTwinsAgreeDigits, thm := some ``tupleTwinsAgreeDigits_proven
    notes := "The excluded cases are bool digits and out-of-range digits under 'F', both recorded by the refuted entry." },
  { id := "decimal-format-c-accepts-only-py", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_format", "mpd_parse_fmt_str"]
    statement := "For every format spec not ending in the C-only deprecated type 'N', if format(_decimal.Decimal(x), spec) accepts the spec, so does _pydecimal."
    source := "twin agreement; format spec mini-language (int, str and Fraction reject these specs; float rejects all but a single trailing NUL)"
    status := .refuted, prop := ``FormatCAcceptsOnlyPy, thm := some ``formatCAcceptsOnlyPy_refuted
    bug := some "decimal-c-format-spec-nul"
    notes := "format(Decimal('1234.5'), '10\\x00xyz') == '    1234.5': dec_format passes the UTF-8 buffer to libmpdec as a C string, which ends at the embedded NUL." },
  { id := "decimal-format-no-encode-error", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_format"]
    statement := "format(_decimal.Decimal(x), spec) never raises UnicodeEncodeError."
    source := "invariant; twin agreement (_pydecimal, float, int and Fraction accept a lone surrogate fill)"
    status := .refuted, prop := ``FormatNoEncodeError, thm := some ``formatNoEncodeError_refuted
    bug := some "decimal-c-format-surrogate-fill"
    notes := "format(Decimal('1.5'), '\\ud800<5'): PyUnicode_AsUTF8AndSize fails on the surrogate before any parsing." },
  { id := "decimal-rounding-modes-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._rescale", "Decimal._round_down", "Decimal._round_up", "Decimal._round_half_up",
              "Decimal._round_half_down", "Decimal._round_half_even", "Decimal._round_ceiling",
              "Decimal._round_floor", "Decimal._round_05up"]
    statement := "For all 8 rounding modes, every finite non-zero value and every larger target exponent, _rescale returns the coefficient the mode prescribes (roundSpec: truncate / away from zero / toward ±inf / nearest with ties up, down, even / 05up), or raises the int-limit ValueError."
    source := "decimal docs, 'Rounding modes'; General Decimal Arithmetic, 'Rounding'"
    status := .proven, prop := ``RoundingModesCorrect, thm := some ``roundingModesCorrect_proven
    notes := "Covers the digits-below-zero substitution (_pydecimal.py:2600-2602). The ValueError branch is decimal-pydecimal-int-max-str-digits." },
  { id := "decimal-to-integral-value-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.to_integral_value"]
    statement := "For every context, rounding argument and finite value, to_integral_value returns the value unchanged if its exponent is >= 0, and otherwise the correctly rounded integer at exponent 0, without setting any flag (or the int-limit ValueError)."
    source := "to_integral_value docstring ('without raising inexact, rounded'), decimal docs"
    status := .proven, prop := ``ToIntegralValueCorrect, thm := some ``toIntegralValueCorrect_proven },
  { id := "decimal-int-conversions-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_as_long", "PyDec_Round", "dec_floor", "dec_ceil", "dec_trunc"]
    statement := "For every finite decimal and rounding mode, _decimal's int()/math.floor/math.ceil/round() return the signed integer whose magnitude the mode prescribes (exact for exponents >= 0)."
    source := "__floor__/__ceil__/__round__/__int__ docs"
    status := .proven, prop := ``IntConversionsC, thm := some ``intConversionsC_proven },
  { id := "decimal-int-conversions-py-or-limit", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floor__", "Decimal.__ceil__", "Decimal.__round__", "Decimal.__int__"]
    statement := "For every finite decimal and rounding mode, _pydecimal's integer conversion returns the same int as _decimal's, or raises the int-limit ValueError."
    source := "twin agreement (narrowed version of decimal-int-conversions-py)"
    status := .proven, prop := ``IntConversionsPyOrLimit, thm := some ``intConversionsPyOrLimit_proven },
  { id := "decimal-hash-consistent-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["_dec_hash", "dec_from_long"]
    statement := "For every finite Decimal d, hash(d) == hash(Fraction(*d.as_integer_ratio())), and for every int n, hash(Decimal(n)) == hash(n), in _decimal."
    source := "Built-in Types, 'Hashing of numeric types': x == y implies hash(x) == hash(y)"
    status := .proven, prop := ``HashConsistentC, thm := some ``hashConsistentC_proven
    notes := "Reuses PyLean.Fractions.hashMatchesDecimal_proven / hashMatchesInt_proven. The C constant inv10_p equals pow(10, P-2, P) (tenInv_eq)." },
  { id := "decimal-compare-total-order", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.compare_total", "Decimal._cmp"]
    statement := "For all decimals a, b (NaNs, infinities, signed zeros, any exponents), compare_total(b, a) == -compare_total(a, b), and compare_total(a, b) == 0 iff a and b are the same representation."
    source := "compare_total docs: 'the result gives a total ordering on Decimal instances' (Doc/library/decimal.rst:529-530)"
    status := .proven, prop := ``CompareTotalOrder, thm := some ``compareTotalOrder_proven }
]

end PyLean.Decimal
