import PyLean.Registry
import PyLean.Decimal.Diff
import PyLean.Decimal.Refute
import PyLean.Decimal.TupleProps
import PyLean.Decimal.Props
import PyLean.Decimal.Quantize
import PyLean.Decimal.RoundTrip
import PyLean.Decimal.MulProps
import PyLean.Decimal.ParseAgree
import PyLean.Decimal.OpenProps

/-!
`Lib/_pydecimal.py` vs `Modules/_decimal/` (libmpdec), CPython 3.14.7.

Both twins are modelled side by side where their code differs (string and
tuple constructors, `__format__` spec handling, `hash`, integer conversions,
`as_integer_ratio`, `Decimal(int)`); the context arithmetic (`_fix`,
`_rescale`, `quantize`, `to_integral_*`, `round`, `normalize`, `+ - *`,
`compare_total`, `copy_sign`) is modelled from `_pydecimal` and checked
against both twins by `difftest/decimal_diff.py`. Division, sqrt, exp, ln,
log10, pow and floats are out of scope. `__format__` is modelled as far as
which specs are accepted; what an accepted spec renders is not modelled.

Properties about `Ctx`-dependent operations are conditional on the operation
returning: a trapped signal, or `_pydecimal`'s int-limit `ValueError`, raises
instead (the C twin sets all of an operation's flags before raising, `_pydecimal`
stops at the first trapped signal; deccheck.py excludes this deliberately).

The difftest and reproducers run on interpreters built with the bundled
libmpdec 2.5.1, whose source these line numbers cite. A build against system
libmpdec 4.0.1 (Homebrew) differs only in the format-spec parser, which also
takes `z`; Format.lean models both.
-/

namespace PyLean.Decimal

open PyLean.Registry

def entries : List Entry := [
  { id := "decimal-parse-c-accepts-py", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["Decimal.__new__", "PyDecType_FromUnicodeExactWS", "PyDecType_FromCStringExact", "numeric_as_ascii"]
    statement := "For every string s, if _pydecimal.Decimal(s) returns a value within the C module's documented limits, _decimal.Decimal(s) returns the same value."
    source := "twin agreement (both implement the spec's numeric-string syntax, whose letters are ASCII, case-insensitive)"
    status := .refuted, prop := ``ParseCAcceptsPy, thm := some ``parseCAcceptsPy_refuted
    bug := some "decimal-pydecimal-parser-unicode-casefold"
    notes := "Decimal('ınf') (U+0131), 'İnfinity' (U+0130), 'ſNaN' (U+017F): _pydecimal's regex is compiled with re.IGNORECASE and matches these by Unicode case folding; _decimal rejects them. Exhaustively, these three code points are the only non-ASCII characters any letter of the pattern matches." },
  { id := "decimal-parse-c-accepts-py-casefree", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["Decimal.__new__", "PyDecType_FromUnicodeExactWS", "PyDecType_FromCStringExact", "numeric_as_ascii"]
    statement := "For every string s not containing U+0130, U+0131 or U+017F, if _pydecimal.Decimal(s) returns a value within the C module's documented limits, _decimal.Decimal(s) returns the same value (sign, coefficient, exponent, NaN kind and payload), for arbitrary Unicode input: Nd digits, whitespace, underscores, every spelling of Inf and NaN."
    source := "twin agreement (narrowed version of decimal-parse-c-accepts-py)"
    status := .proven, prop := ``ParseCAcceptsPyCasefree, thm := some ``parseCAcceptsPyCasefree_proven
    notes := "One direction only: _pydecimal accepts => _decimal agrees. The converse is decimal-parse-converse, open." },
  { id := "decimal-parse-py-accepts-c", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__", "PyDecType_FromUnicodeExactWS", "PyDecType_FromCStringExact", "numeric_as_ascii"]
    statement := "For every string s, if _decimal.Decimal(s) returns a value, _pydecimal.Decimal(s) returns the same value."
    source := "twin agreement; decimal docs: 'user alterable precision ... which can be as large as needed for a given problem' (Doc/library/decimal.rst:63-65)"
    status := .refuted, prop := ``ParsePyAcceptsC, thm := some ``parsePyAcceptsC_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('1'*4301): _pydecimal stores str(int(intpart+fracpart)), and int() refuses more than 4300 digits (leading zeros included), so it raises ValueError. Known and declined upstream: python/cpython#96589, closed as not planned." },
  { id := "decimal-str-roundtrip-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__str__", "Decimal.__new__"]
    statement := "For every decimal d within the C limits, Decimal(str(d)) == d in _pydecimal, with the same sign, coefficient and exponent."
    source := "invariant (__repr__ comment, _pydecimal.py:981: 'eval(repr(d)) == d')"
    status := .refuted, prop := ``StrRoundTripPy, thm := some ``strRoundTripPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "d = Decimal(10**4300) built from a tuple: str(d) has 4301 digits and cannot be parsed back." },
  { id := "decimal-str-roundtrip-py-bounded", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__str__", "Decimal.__new__"]
    statement := "For every decimal d within the C limits whose coefficient has at most 4294 digits (NaN payload at most 4300), Decimal(str(d)) == d in _pydecimal, with the same sign, coefficient, exponent and NaN kind and payload."
    source := "invariant (narrowed version of decimal-str-roundtrip-py)"
    status := .proven, prop := ``StrRoundTripPyBounded, thm := some ``strRoundTripPyBounded_proven
    notes := "4294 rather than 4300 because str() of a value such as 0.00000ddd adds up to six zeros, which int() counts. The excluded cases are the int-limit refutation." },
  { id := "decimal-str-roundtrip-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_str", "PyDecType_FromUnicodeExactWS", "PyDecType_FromCStringExact", "numeric_as_ascii"]
    statement := "For every decimal d within the C limits (NaNs and infinities included) whose coefficient has at most MPD_MAX_PREC - 5 digits, Decimal(str(d)) == d in _decimal, with the same sign, coefficient, exponent and NaN kind and payload."
    source := "invariant (__repr__ comment, _pydecimal.py:981: 'eval(repr(d)) == d'; both twins)"
    status := .proven, prop := ``StrRoundTripC, thm := some ``strRoundTripC_proven
    notes := "The -5 is real in the model: mpd_qset_string rejects more than MPD_MAX_PREC fraction digits (io.c:286), and 0.00000ddd adds zeros to the fraction, so a value with about 10**18 digits would not read back. No such string fits in memory; this is not recorded as a bug." },
  { id := "decimal-hash-twins-agree", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__hash__", "_dec_hash"]
    statement := "Whenever _decimal hashes a decimal, _pydecimal hashes it to the same int."
    source := "twin agreement; Built-in Types, Hashing of numeric types"
    status := .refuted, prop := ``HashTwinsAgree, thm := some ``hashTwinsAgree_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "hash(Decimal(10**4300)): __hash__ evaluates int(self._int)." },
  { id := "decimal-int-conversions-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floor__", "Decimal.__ceil__", "Decimal.__round__", "Decimal._rescale", "Decimal.__int__",
              "dec_as_long", "dec_floor", "dec_ceil", "PyDec_Round"]
    statement := "For every finite decimal, math.floor, math.ceil and round() of a _pydecimal.Decimal return the correctly rounded int (the one _decimal returns)."
    source := "__floor__/__ceil__/__round__ docstrings, _pydecimal.py:1784-1873"
    status := .refuted, prop := ``IntConversionsPy, thm := some ``intConversionsPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "math.floor(Decimal('1E+4300')): _rescale(0, ...) pads the coefficient to 4301 digits and int() of it fails, although int(Decimal('1E+4300')) works." },
  { id := "decimal-mul-no-valueerror-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "_WorkRep.__init__"]
    statement := "Under every context, _pydecimal's * returns a value or raises a trapped decimal signal; it never raises ValueError."
    source := "invariant; twin agreement (_decimal rounds the product to the context precision)"
    status := .refuted, prop := ``MulNoValueErrorPy, thm := some ``mulNoValueErrorPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('1'*2200) * Decimal('1'*2200) at the default precision 28: __mul__ formats the exact 4400-digit product with str() before rounding. Both operands are under the limit here, but the root cause is the one declined in python/cpython#96589." },
  { id := "decimal-add-no-valueerror-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__add__", "_WorkRep.__init__", "_normalize"]
    statement := "Under every context, _pydecimal's + returns a value or raises a trapped decimal signal; it never raises ValueError."
    source := "invariant; twin agreement (_decimal rounds the sum to the context precision)"
    status := .refuted, prop := ``AddNoValueErrorPy, thm := some ``addNoValueErrorPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('9'*4300) + Decimal('9'*4300): both operands pass _WorkRep and _normalize, and Decimal(result) formats the exact 4301-digit sum with str() before rounding. Same root cause as python/cpython#96589." },
  { id := "decimal-sub-no-valueerror-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__sub__", "Decimal.__add__", "Decimal.copy_negate", "_WorkRep.__init__", "_normalize"]
    statement := "Under every context, _pydecimal's - returns a value or raises a trapped decimal signal; it never raises ValueError."
    source := "invariant; twin agreement (_decimal rounds the difference to the context precision)"
    status := .refuted, prop := ``SubNoValueErrorPy, thm := some ``subNoValueErrorPy_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('9'*4300) - Decimal('-' + '9'*4300): __sub__ negates the operand and calls __add__, which fails as in decimal-add-no-valueerror-py." },
  { id := "decimal-add-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__add__", "_normalize", "_WorkRep.__init__", "Decimal._fix"]
    statement := "For every context with prec >= 1 and all finite non-zero operands with a non-zero exact sum, when + returns a value in the normal range, it is the exact sum correctly rounded to prec digits, with Inexact set exactly when non-zero digits were dropped and Rounded exactly when any were."
    source := "General Decimal Arithmetic, 'add' and 'Rounding'; decimal docs, signals Inexact and Rounded"
    status := .open, prop := ``AddCorrect
    notes := "Missing: the sticky-digit argument for _normalize, namely that replacing the smaller operand by 1 at exponent min(-1, len-prec-2) below the larger changes neither the rounded result nor Inexact/Rounded. Without it, even commutativity is not structural, because _normalize is not symmetric at equal exponents. The difftest finds no counterexample." },
  { id := "decimal-sub-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__sub__", "Decimal.__add__", "_normalize", "Decimal._fix"]
    statement := "For every context with prec >= 1 and all finite non-zero operands with a non-zero exact difference, when - returns a value in the normal range, it is the exact difference correctly rounded to prec digits."
    source := "General Decimal Arithmetic, 'subtract'"
    status := .open, prop := ``SubCorrect
    notes := "Follows from decimal-add-correct once that is proven: sub reduces to add with the sign of the second operand flipped." },
  { id := "decimal-mul-overflow-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "Decimal._fix", "Overflow.handle"]
    statement := "For every context with prec >= 1 and Emin <= 0 <= Emax and all finite non-zero operands, if the correctly rounded product has an adjusted exponent above Emax, a returning * gives the rounding mode's overflow value and sets Overflow, Inexact and Rounded."
    source := "decimal docs, signal Overflow; General Decimal Arithmetic, 'Overflow'"
    status := .open, prop := ``MulOverflowCorrect
    notes := "Missing: the two overflow branches of _fix (before rounding, and after a carry) joined to roundPrec." },
  { id := "decimal-mul-subnormal-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "Decimal._fix"]
    statement := "For every context with prec >= 1 and Emin <= 0 <= Emax and all finite non-zero operands whose product is below the normal range and has digits below Etiny, a returning * rounds the product at exponent Etiny and sets Subnormal and Rounded, with Inexact and Underflow set exactly when non-zero digits were dropped."
    source := "decimal docs, signals Subnormal and Underflow; General Decimal Arithmetic, 'Subnormal numbers'"
    status := .open, prop := ``MulSubnormalCorrect
    notes := "Missing: _fix's digits-below-zero substitution joined to quantSpec, as rescale_quantSpec does for _rescale, and the absence of a carry past prec digits." },
  { id := "decimal-parse-converse", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__", "PyDecType_FromUnicodeExactWS", "numeric_as_ascii"]
    statement := "For every string s, if _decimal.Decimal(s) returns a value, _pydecimal.Decimal(s) returns the same value or raises the int-limit ValueError."
    source := "twin agreement (narrowed version of decimal-parse-py-accepts-c)"
    status := .open, prop := ``ParseConverse
    notes := "Missing: inverting mpd_qset_string's scanner into the regex's accepted shape, the mirror image of ParseAgree.lean. The difftest finds no counterexample." },
  { id := "decimal-as-tuple-roundtrip", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.as_tuple", "PyDec_AsTuple", "dectuple_as_str"]
    statement := "For every decimal d within the C limits, Decimal(d.as_tuple()) returns d in _decimal: sign, coefficient, exponent, NaN kind and payload."
    source := "as_tuple docs and the Decimal constructor's tuple form (Doc/library/decimal.rst:395-397)"
    status := .open, prop := ``AsTupleRoundTrip
    notes := "Missing: joining toDigits_digs (TupleProps.lean) to asTuple's three cases." },
  { id := "decimal-normalize-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.normalize", "Decimal._fix"]
    statement := "For every context and non-NaN operand, a returning normalize gives the value of _fix with trailing zeros stripped: no trailing zero remains unless the exponent limit stopped it, and a zero becomes the zero with exponent 0."
    source := "normalize docs: 'Normalize the number by stripping the rightmost trailing zeros' (Doc/library/decimal.rst)"
    status := .open, prop := ``NormalizeCorrect
    notes := "Missing: an induction on the strip loop, whose fuel is numDigits co." },
  { id := "decimal-tuple-twins-agree", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__", "dectuple_as_str", "PyDecType_FromCStringExact", "Decimal.__str__", "dec_str"]
    statement := "For every tuple (sign, digits, exp) with |exp| <= 10**17 and at most 10**17 digits, if _pydecimal.Decimal(t) succeeds then _decimal.Decimal(t) succeeds and str() of both agree."
    source := "twin agreement; Decimal docs: 'three components, a sign ..., a tuple of digits, and an integer exponent' (Doc/library/decimal.rst:395-397)"
    status := .refuted, prop := ``TupleTwinsAgree, thm := some ``tupleTwinsAgree_refuted
    bug := some "decimal-pydecimal-tuple-bool-digits"
    notes := "Decimal((0, (True,), 0)) is Decimal('True') in _pydecimal (the bool passes isinstance(digit, int) and is joined with str()) and Decimal('1') in _decimal. Also Decimal((0, None, 'F')): _pydecimal ignores the coefficient of an infinity, _decimal requires a tuple of digits." },
  { id := "decimal-tuple-twins-agree-int-digits", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__", "dectuple_as_str", "PyDecType_FromCStringExact", "Decimal.__str__", "dec_str"]
    statement := "For every tuple whose coefficient is a tuple of ints in 0..9, with |exp| <= 10**17 and at most 10**17 digits, if _pydecimal.Decimal(t) succeeds then _decimal.Decimal(t) succeeds and str() of both agree (leading zeros, NaN payloads, any sign or exponent value)."
    source := "twin agreement (narrowed version of decimal-tuple-twins-agree)"
    status := .proven, prop := ``TupleTwinsAgreeDigits, thm := some ``tupleTwinsAgreeDigits_proven
    notes := "The excluded cases are bool digits and out-of-range digits under 'F', both recorded by the refuted entry." },
  { id := "decimal-format-c-accepts-only-py", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_format", "_parse_format_specifier"]
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
    pyFns := ["Decimal.to_integral_value", "Decimal._rescale"]
    statement := "For every context, rounding argument and finite value, to_integral_value returns the value unchanged if its exponent is >= 0, and otherwise the correctly rounded integer at exponent 0, without setting any flag (or the int-limit ValueError)."
    source := "to_integral_value docstring ('without raising inexact, rounded'), decimal docs"
    status := .proven, prop := ``ToIntegralValueCorrect, thm := some ``toIntegralValueCorrect_proven },
  { id := "decimal-quantize-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.quantize", "Decimal._rescale", "Decimal._fix", "Decimal.__round__", "Decimal._cmp",
              "Decimal.adjusted", "Context.Etiny", "Context.Etop", "Context._raise_error"]
    statement := "For every context with prec >= 1, rounding mode and finite operands, when quantize returns: if the correctly rounded (or zero-padded) coefficient q' at the target exponent fits (target in [Etiny, Emax], q' has at most prec digits, its adjusted exponent is at most Emax), the result is q' at that exponent (folded down to Etop under clamp, same value) and Inexact is set exactly when non-zero digits were dropped; otherwise the result is NaN with InvalidOperation set."
    source := "decimal docs, quantize: 'Return a value equal to the first operand after rounding and having the exponent of the second operand'; 'if the length of the coefficient after the quantize operation would be greater than precision, then an InvalidOperation is signaled'"
    status := .proven, prop := ``QuantizeCorrect, thm := some ``quantizeCorrect_proven
    notes := "round(d, n) is quantize(Decimal((0, (1,), -n))) by definition (_pydecimal.py:1834-1835, _decimal.c PyDec_Round), so this covers it for |n| < 2**63. Beyond that _decimal raises OverflowError and _pydecimal does not: a discrepancy deccheck.py already lists (SkipHandler.__round__), not recorded as a bug here. Conditional on returning: a trapped signal or the int-limit ValueError raises instead. Under clamp=1 the result's exponent can be below the operand's (the fold-down keeps the value), so the docs' 'the quantized exponent is always equal to that of the right-hand operand' holds only for clamp=0, in both twins." },
  { id := "decimal-mul-correctly-rounded", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "Decimal._fix", "_WorkRep.__init__", "Context.Etiny", "Context.Etop", "Context._raise_error"]
    statement := "For every context with prec >= 1, all 8 rounding modes and all finite non-zero operands, when * returns a value in the normal range (no subnormal result, no overflow after rounding), that value is the exact product correctly rounded to prec digits, including the carry from 99...9 to 100...0 (folded down under clamp when nothing was rounded), Inexact is set exactly when non-zero digits were dropped, and Rounded exactly when any digits were dropped."
    source := "General Decimal Arithmetic, 'multiply' and 'Rounding'; decimal docs, signals Inexact and Rounded"
    status := .proven, prop := ``MulCorrect, thm := some ``mulCorrect_proven
    notes := "The subnormal and overflow ranges of _fix are hypotheses here; they are stated by decimal-mul-subnormal-correct and decimal-mul-overflow-correct, and + and - by decimal-add-correct and decimal-sub-correct, all open. Conditional on returning: a trapped signal or the int-limit ValueError raises instead." },
  { id := "decimal-to-integral-exact-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.to_integral_exact", "Decimal._rescale", "Decimal._cmp", "Context._raise_error"]
    statement := "For every context, rounding argument and finite non-zero value with exponent < 0, when to_integral_exact returns, the result is the correctly rounded integer at exponent 0, Rounded is set, and Inexact is set exactly when non-zero digits were dropped."
    source := "decimal docs: 'signaling Inexact or Rounded as appropriate if rounding occurs' (Doc/library/decimal.rst:929-930)"
    status := .proven, prop := ``ToIntegralExactCorrect, thm := some ``toIntegralExactCorrect_proven },
  { id := "decimal-int-conversions-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_as_long", "PyDec_Round", "dec_floor", "dec_ceil", "dec_trunc"]
    statement := "For every finite decimal and rounding mode, _decimal's int()/math.floor/math.ceil/round() return the signed integer whose magnitude the mode prescribes (exact for exponents >= 0)."
    source := "__floor__/__ceil__/__round__/__int__ docs"
    status := .proven, prop := ``IntConversionsC, thm := some ``intConversionsC_proven },
  { id := "decimal-int-conversions-py-or-limit", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floor__", "Decimal.__ceil__", "Decimal.__round__", "Decimal.__int__", "Decimal._rescale"]
    statement := "For every finite decimal and rounding mode, _pydecimal's integer conversion returns the same int as _decimal's, or raises the int-limit ValueError."
    source := "twin agreement (narrowed version of decimal-int-conversions-py)"
    status := .proven, prop := ``IntConversionsPyOrLimit, thm := some ``intConversionsPyOrLimit_proven },
  { id := "decimal-hash-consistent-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["_dec_hash", "dec_from_long"]
    statement := "For every finite Decimal d, hash(d) == hash(Fraction(*d.as_integer_ratio())), and for every int n, hash(Decimal(n)) == hash(n), in _decimal."
    source := "Built-in Types, 'Hashing of numeric types': x == y implies hash(x) == hash(y)"
    status := .proven, prop := ``HashConsistentC, thm := some ``hashConsistentC_proven
    notes := "Reuses PyLean.Fractions.hashMatchesDecimal_proven / hashMatchesInt_proven. The C constant inv10_p equals pow(10, P-2, P) (tenInv_eq)." },
  { id := "decimal-ratio-correct-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_as_integer_ratio"]
    statement := "For every finite Decimal, as_integer_ratio() returns (n, d) with d > 0, n and d coprime, and n/d exactly the value."
    source := "as_integer_ratio docstring, _pydecimal.py:929-941"
    status := .proven, prop := ``RatioCorrectC, thm := some ``ratioCorrectC_proven },
  { id := "decimal-compare-total-order", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.compare_total", "Decimal._cmp", "Decimal._isnan"]
    statement := "For all decimals a, b (NaNs, infinities, signed zeros, any exponents), compare_total(b, a) == -compare_total(a, b), and compare_total(a, b) == 0 iff a and b are the same representation."
    source := "compare_total docs: 'the result gives a total ordering on Decimal instances' (Doc/library/decimal.rst:529-530)"
    status := .proven, prop := ``CompareTotalOrder, thm := some ``compareTotalOrder_proven }
]

end PyLean.Decimal
