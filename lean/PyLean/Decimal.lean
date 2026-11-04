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
import PyLean.Decimal.DivisionProps
import PyLean.Decimal.ExactProps
import PyLean.Decimal.Pow10Refute
import PyLean.Decimal.FixExact
import PyLean.Decimal.ContextExact
import PyLean.Decimal.DelegateExact
import PyLean.Decimal.Pow10a
import PyLean.Decimal.DelegateExact2
import PyLean.Decimal.Exact3
import PyLean.Decimal.Exact4
import PyLean.Decimal.AddExact

/-!
`Lib/_pydecimal.py` vs `Modules/_decimal/` (libmpdec), CPython 3.15.2.

Both twins are modelled side by side where their code differs (string and
tuple constructors, `__format__` spec handling, `hash`, integer conversions,
`as_integer_ratio`, `Decimal(int)`, `Context` objects and attributes, status words
and `SignalDict`, `//` and `divmod`); the context arithmetic and the remaining methods
are modelled from `_pydecimal` and checked against both twins by
`difftest/decimal_diff.py`. pow, sqrt, exp, ln, log10 and floats are not modelled yet.
`__format__` is modelled as far as which specs are accepted; what an accepted spec
renders is not modelled.

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
    source := "twin agreement; decimal docs: 'user alterable precision ... which can be as large as needed for a given problem' (Doc/library/decimal.rst:55-57)"
    status := .refuted, prop := ``ParsePyAcceptsC, thm := some ``parsePyAcceptsC_refuted
    bug := some "decimal-pydecimal-int-max-str-digits"
    notes := "Decimal('1'*4301): _pydecimal stores str(int(intpart+fracpart)), and int() refuses more than 4300 digits (leading zeros included), so it raises ValueError. Known and declined upstream: python/cpython#96589, closed as not planned." },
  { id := "decimal-str-roundtrip-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__str__", "Decimal.__new__"]
    statement := "For every decimal d within the C limits, Decimal(str(d)) == d in _pydecimal, with the same sign, coefficient and exponent."
    source := "invariant (__repr__ comment, _pydecimal.py:1073: 'eval(repr(d)) == d')"
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
    source := "invariant (__repr__ comment, _pydecimal.py:1073: 'eval(repr(d)) == d'; both twins)"
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
              "dec_as_long", "_decimal_Decimal___floor___impl", "_decimal_Decimal___ceil___impl",
              "_decimal_Decimal___round___impl"]
    statement := "For every finite decimal, math.floor, math.ceil and round() of a _pydecimal.Decimal return the correctly rounded int (the one _decimal returns)."
    source := "__floor__/__ceil__/__round__ docstrings, _pydecimal.py:1883-1973"
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
    status := .proven, prop := ``AddCorrect, thm := some ``addCorrect_proven
    notes := "A consequence of decimal-add-exact (the sum is fixSpec of the exact sum, so a returning + is fix of it) and fix_normal; decimal-add-exact also states the overflow, subnormal and int-limit outcomes this statement assumes away." },
  { id := "decimal-add-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__add__", "_normalize", "_WorkRep.__init__"]
    statement := "For every context with prec >= 1, on every operand pair: for non-zero finite operands, _WorkRep's int/str-limit ValueError when a coefficient has more than 4300 digits (the first operand's first); an exact sum of zero is the zero _fix makes of +0 (of -0 under ROUND_FLOOR) at min(ea, eb); the int/str-limit ValueError of str(result.int) exactly when _normalize's working sum has more than 4300 digits; and otherwise the exact sum rounded into the context by _fix (fixSpec: overflow, subnormals, clamping, the signals in order with the first trapped one raising), whatever _normalize's substitution of the smaller operand did. 0 + b is b padded to exponent max(min(ea, eb), eb - prec - 1) through _fix (and a + 0 alike); 0 + 0 is the zero of sign (sa and sb), or negative under ROUND_FLOOR when the signs differ, at min(ea, eb); a NaN operand goes through _check_nans; an infinity plus t is t's NaN, InvalidOperation for the opposite infinity, else the infinity; a finite value plus an infinity is the infinity."
    source := "General Decimal Arithmetic, 'add' and 'Rounding'; decimal docs, Context.add; Lib/_pydecimal.py:1202-1286, :5723-5749"
    status := .proven, prop := ``AddExact, thm := some ``addExact_proven
    notes := "Unconditional equations for (add c a b).run fl. The sticky-digit lemma (fixSpec_sticky) shows that the substituted working sum, which has at least prec + 1 digits, agrees with the exact sum on the kept prefix, on dropping non-zero digits and on the comparison with half a unit, so _fix gives the same result and signals, subnormal and overflow ranges included. Checked on 3.15.2 (200,000 random contexts and operands, zeros, subnormal and overflow ranges and clamp included): _pydecimal's add equals _decimal's correctly rounded add with the same flags; Context(prec=6000).add(Decimal('1E+5000'), 1) and Context(prec=5000).add(Decimal('1E+10000'), 1) raise the int/str-limit ValueError and Context(prec=4000).add(Decimal('1E+10000'), 1) does not, as the working-sum condition says." },
  { id := "decimal-sub-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__sub__", "Decimal.__add__", "_normalize", "Decimal._fix"]
    statement := "For every context with prec >= 1 and all finite non-zero operands with a non-zero exact difference, when - returns a value in the normal range, it is the exact difference correctly rounded to prec digits."
    source := "General Decimal Arithmetic, 'subtract'"
    status := .proven, prop := ``SubCorrect, thm := some ``subCorrect_proven
    notes := "A consequence of decimal-sub-exact and fix_normal." },
  { id := "decimal-fma-fin-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.fma", "Decimal.__add__", "_normalize"]
    statement := "For every context with prec >= 1 and non-zero finite a, b, t whose coefficients and product have at most 4300 digits, fma(a, b, t) is the exact a*b + t rounded once into the context by _fix (fixSpec), an exact zero giving the zero of sign ROUND_FLOOR, except for __add__'s int/str-limit ValueErrors (t's coefficient past 4300 digits, or the working sum past 4300 digits)."
    source := "Decimal.fma docstring: 'Returns self*other+third with no rounding of the intermediate product self*other'"
    status := .proven, prop := ``FmaFinExact, thm := some ``fmaFinExact_proven
    notes := "decimal-fma-exact's finite conjunct (fma is __add__ of the unrounded product) composed with decimal-add-exact. Checked on 3.15.2 (100,000 random contexts and operands, subnormal and overflow ranges and clamp included): _pydecimal's fma equals _decimal's correctly rounded fma with the same flags." },
  { id := "decimal-sub-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__sub__", "Decimal.__add__", "_normalize", "_WorkRep.__init__"]
    statement := "For every context with prec >= 1, on every operand pair: a NaN operand goes through _check_nans on the operands as given; on finite operands a - b is decimal-add-exact with the sign of b flipped (the exact difference rounded by _fix, the same int/str-limit ValueErrors, x - x the zero of sign ROUND_FLOOR); an infinity minus a non-NaN t is the infinity added to -t; a finite value minus an infinity is the opposite infinity."
    source := "General Decimal Arithmetic, 'subtract'; Lib/_pydecimal.py:1290-1302"
    status := .proven, prop := ``SubExact, thm := some ``subExact_proven
    notes := "Checked on 3.15.2: Context(rounding=ROUND_FLOOR).subtract(Decimal('1.5'), Decimal('1.5')) is -0.0, at the default rounding 0.0." },
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
    pyFns := ["Decimal.as_tuple", "_decimal_Decimal_as_tuple_impl", "dectuple_as_str"]
    statement := "For every decimal d within the C limits, Decimal(d.as_tuple()) returns d in _decimal: sign, coefficient, exponent, NaN kind and payload."
    source := "as_tuple docs and the Decimal constructor's tuple form (Doc/library/decimal.rst:387-389)"
    status := .open, prop := ``AsTupleRoundTrip
    notes := "Missing: joining toDigits_digs (TupleProps.lean) to asTuple's three cases." },
  { id := "decimal-normalize-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.normalize", "Decimal._fix"]
    statement := "For every context and non-NaN operand, a returning normalize gives the value of _fix with trailing zeros stripped: no trailing zero remains unless the exponent limit stopped it, and a zero becomes the zero with exponent 0."
    source := "normalize docs: 'Normalize the number by stripping the rightmost trailing zeros' (Doc/library/decimal.rst)"
    status := .open, prop := ``NormalizeCorrect
    notes := "Missing: an induction on the strip loop, whose fuel is numDigits co." },
  { id := "decimal-copy-ops-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.copy_abs", "Decimal.copy_negate", "Decimal.copy_sign", "Decimal.compare_total_mag"]
    statement := "copy_negate is an involution flipping the sign, copy_abs clears it and is idempotent, copy_sign takes the sign of the second operand and the magnitude of the first, and compare_total_mag is compare_total on magnitudes, reflexive and antisymmetric, for all decimals including NaNs."
    source := "decimal docs, copy_abs, copy_negate, copy_sign, compare_total_mag"
    status := .proven, prop := ``CopyOpsCorrect, thm := some ``copyOpsCorrect_proven },
  { id := "decimal-classification-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.number_class", "Decimal.is_nan", "Decimal.is_qnan", "Decimal.is_snan", "Decimal.is_finite",
              "Decimal.is_infinite", "Decimal.is_normal", "Decimal.is_subnormal", "Decimal.is_zero",
              "Decimal.__bool__", "Decimal._isnan", "Decimal._isinfinity"]
    statement := "For every context and decimal: number_class reports sNaN and NaN exactly for is_snan and is_qnan, is_nan is their union, bool(d) is not is_zero, is_finite, is_infinite and is_nan partition the values, is_normal and is_subnormal partition the finite non-zero values, and is_canonical is true."
    source := "decimal docs, is_* methods and number_class"
    status := .proven, prop := ``ClassificationCorrect, thm := some ``classificationCorrect_proven },
  { id := "decimal-comparisons-consistent", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__eq__", "Decimal.__lt__", "Decimal.__le__", "Decimal.__gt__", "Decimal.__ge__",
              "Decimal.compare", "Decimal.compare_signal", "Decimal._cmp", "Decimal._check_nans",
              "Decimal._compare_check_nans", "Decimal._fix_nan"]
    statement := "For non-NaN Decimal operands, ==, <, <=, >, >= follow _cmp and set no flag, compare and compare_signal return it as a Decimal, and it is antisymmetric. With a quiet NaN on the left and no signaling NaN, == is False with no flag, and < is False with InvalidOperation set."
    source := "decimal docs, comparisons; invariant"
    status := .proven, prop := ``ComparisonsConsistent, thm := some ``comparisonsConsistent_proven
    notes := "Decimal operands only: _convert_for_comparison (int, Rational, float, complex) is not modelled yet." },
  { id := "decimal-minmax-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.max", "Decimal.min", "Decimal.max_mag", "Decimal.min_mag"]
    statement := "For non-NaN operands, max, min, max_mag and min_mag do not depend on operand order, even for numerically equal operands, where compare_total decides; when a > b, max is _fix(a) and min is _fix(b); and a quiet NaN loses to a number."
    source := "decimal docs, max and min; General Decimal Arithmetic, 'max'"
    status := .proven, prop := ``MinMaxCorrect, thm := some ``minMaxCorrect_proven },
  { id := "decimal-raise-error-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context._raise_error"]
    statement := "For every condition: an ignored signal sets no flag and raises nothing; otherwise the flag is set, and the result is the handler's unless the signal is trapped, when its exception is raised. The handlers return NaN, the quieted operand, a signed infinity, the rounding mode's overflow value, or None, per condition."
    source := "decimal docs, Signals; invariant"
    status := .proven, prop := ``RaiseErrorCorrect, thm := some ``raiseErrorCorrect_proven },
  { id := "decimal-context-methods-match-decimal", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_convert_other", "Context.add", "Context.subtract", "Context.multiply", "Context.divide",
              "Context.divide_int", "Context.divmod", "Context.remainder", "Context.compare",
              "Context.compare_signal", "Context.max", "Context.max_mag", "Context.min", "Context.min_mag",
              "Context.logical_and", "Context.logical_or", "Context.logical_xor", "Context.next_toward",
              "Context.quantize", "Context.remainder_near", "Context.rotate", "Context.scaleb", "Context.shift",
              "Context.compare_total", "Context.compare_total_mag", "Context.copy_sign", "Context.same_quantum",
              "Context.abs", "Context.logb", "Context.logical_invert", "Context.minus", "Context.plus",
              "Context.next_minus", "Context.next_plus", "Context.normalize", "Context.to_integral_exact",
              "Context.to_integral_value", "Context.number_class", "Context.is_normal", "Context.is_subnormal",
              "Context.to_eng_string", "Context.to_sci_string", "Context.copy_abs", "Context.copy_negate",
              "Context.copy_decimal", "Context.is_finite", "Context.is_infinite", "Context.is_nan",
              "Context.is_qnan", "Context.is_signed", "Context.is_snan", "Context.is_zero", "Context.canonical",
              "Context.is_canonical", "Context.radix", "Context.fma"]
    statement := "Every Context method on one to three operands behaves as the Decimal method under that context on the operands converted by _convert_other, for Decimal and int operands; any other operand raises the conversion's TypeError, and an int past the 4300-digit limit its ValueError. canonical and is_canonical take only a Decimal."
    source := "Doc/library/decimal.rst:1162-1168: 'C.exp(x) is equivalent to x.exp(context=C). Each Context method accepts a Python integer anywhere that a Decimal instance is accepted.'"
    status := .proven, prop := ``ContextMethodsMatchDecimal, thm := some ``contextMethodsMatchDecimal_proven
    notes := "canonical and is_canonical reject an int, against the literal doc sentence, in both twins and deliberately: Lib/test/test_decimal.py:5447-5448. Not recorded as a bug. Context.exp, ln, log10, sqrt and power wait for those methods." },
  { id := "decimal-reflected-operators", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_convert_other", "Decimal.__rsub__", "Decimal.__rtruediv__", "Decimal.__rdivmod__", "Decimal.__rmod__",
              "Decimal.__rfloordiv__"]
    statement := "a.__rop__(b) for a Decimal or int b is the operator with the operands swapped, under the same context; for anything else it is NotImplemented, with no flag set."
    source := "Python data model, reflected operators"
    status := .proven, prop := ``ReflectedOperators, thm := some ``reflectedOperators_proven },
  { id := "decimal-c-context-clears-flags", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["context_new", "context_init_impl"]
    statement := "For every state of DefaultContext, _decimal's Context() with no flags argument has all flags clear."
    source := "Doc/library/decimal.rst:1110-1111: 'If the flags field is not specified or is None, all flags are cleared.'"
    status := .refuted, prop := ``ContextNewClearsFlagsC, thm := some ``contextNewClearsFlagsC_refuted
    bug := some "decimal-c-context-inherits-flags"
    notes := "After DefaultContext.divide(Decimal(1), Decimal(3)), Context().flags[Inexact] is True: context_new copies the template's status word." },
  { id := "decimal-c-context-copies-capitals", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["context_new", "context_init_impl"]
    statement := "_decimal's Context() with no capitals argument takes capitals from DefaultContext."
    source := "Doc/library/decimal.rst:1109-1110: 'If a field is not specified or is None, the default values are copied from the DefaultContext.'"
    status := .refuted, prop := ``ContextNewCopiesCapitalsC, thm := some ``contextNewCopiesCapitalsC_refuted
    bug := some "decimal-c-context-ignores-default-capitals"
    notes := "context_new sets CtxCaps(self) = 1 after copying the template." },
  { id := "decimal-context-clears-flags-py", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context.__init__", "Context.__setattr__", "Context._set_signal_dict"]
    statement := "For every state of DefaultContext, _pydecimal's Context() with no flags argument has all flags clear."
    source := "Doc/library/decimal.rst:1110-1111"
    status := .proven, prop := ``ContextNewClearsFlagsPy, thm := some ``contextNewClearsFlagsPy_proven },
  { id := "decimal-fix-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._fix", "Context.Etiny", "Context.Etop", "Overflow.handle", "Decimal._fix_nan"]
    statement := "For every context with prec >= 1 and every flag state, _fix of a finite non-zero ±co·10^e is the exact value rounded into the context: an adjusted exponent above Emax overflows (Overflow, Inexact, Rounded, the mode's overflow value); otherwise the exponent becomes max(e + digits - prec, Emin - prec + 1), the dropped digits rounded as the mode says, a carry to 10**prec taking one more exponent, a result exponent above Emax - prec + 1 overflowing, with Underflow (inexact and subnormal), Subnormal, Inexact (non-zero digits dropped), Rounded and Clamped (zero result) in that order; a value already at or above that exponent is kept, folded down to Emax - prec + 1 under clamp=1 with Clamped, and Subnormal when below Emin. The first trapped signal raises. _pydecimal's only other outcome is the int-limit ValueError when the rounded coefficient is the kept prefix plus one with more than 4300 digits. A zero has its exponent clamped into [Etiny, Emax] ([Etiny, Etop] under clamp=1) with Clamped when that changes it; infinities are unchanged and a NaN keeps the last prec - clamp payload digits."
    source := "General Decimal Arithmetic, 'Rounding' and 'Exceptional conditions'; decimal docs, signals Clamped, Inexact, Overflow, Rounded, Subnormal, Underflow"
    status := .proven, prop := ``FixExact, thm := some ``fixExact_proven
    notes := "Unconditional: an equation for (fix c d).run fl, so an always-raising or always-returning _fix fails it. fixSpec writes Etiny and Etop out as Emin - prec + 1 and Emax - prec + 1, so it also pins Context.Etiny and Context.Etop." },
  { id := "decimal-context-setattr-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context.__setattr__", "Context._set_integer_check", "Context._set_signal_dict"]
    statement := "Every assignment to a _pydecimal Context attribute: prec, Emin, Emax, capitals, clamp store an int (or bool) in [1, inf], [-inf, 0], [0, inf], [0, 1], [0, 1] and refuse one outside with ValueError and _set_integer_check's exact message (a bool printed as True/False), except that an int of more than 4300 digits raises the int/str-limit ValueError from the message's %s; any non-int raises TypeError('<name> must be an integer'); rounding stores one of the eight mode names and refuses any other string with TypeError('<s>: invalid rounding mode'); because `value in _rounding_modes` compares with ==, an object whose __eq__ answers true for a mode is stored (the first such mode in order), an exception from __eq__ propagates, and an object equal to none of them is refused with TypeError; any other value (an int, a bool, None, a tuple, a list, a dict, a plain object) is refused with what raise TypeError('%s: invalid rounding mode' % value) raises: the TypeError, the exception of str(value) itself (an int of more than 4300 digits, a list holding one, a __str__ that raises), or for a tuple the argument-tuple errors of %; flags and traps store a dict whose keys are exactly the signals, refuse a dict with another key or a missing signal with what raise KeyError('%s is not a valid signal dict' % d) raises (the KeyError, or the exception repr() of the first key or value that does not print raises), and anything else with what raise TypeError('%s must be a signal dict' % d) raises; _ignored_flags stores its list; any other name raises AttributeError."
    source := "Lib/_pydecimal.py:4005-4053; decimal docs, Context attributes"
    status := .proven, prop := ``SetattrExact, thm := some ``setattrExact_proven
    notes := "Context().prec = -10**5000 raises 'Exceeds the limit (4300 digits) for integer string conversion...' (checked on 3.15.2), so the message conjuncts carry limitOr. For a tuple, '%s must be a signal dict' % d formats the tuple's elements as the arguments, so () and tuples of two or more elements give a format-string TypeError instead of the message (decimal-pydecimal-signal-dict-tuple-message); the rounding message does the same. Checked on 3.15.2: Context().rounding = [10**5000], Context().traps = {10**5000: 1}, Context().traps = {Clamped: 10**5000} and Context().traps = 10**5000 raise the int/str-limit ValueError; an object whose __repr__ raises in a traps dict raises that exception; Context().rounding = (10**5000, 1) raises the limit ValueError (the first element is formatted before the argument count is checked). The model stores only the signals of a list assigned to _ignored_flags; other objects are out of scope (the module only assigns lists). A non-str rounding object is recorded by identity (roundingObj); what arithmetic does under such a context is out of scope, as are int subclasses overriding __str__ and dict keys or list elements whose __eq__ (against a signal or each other) or __bool__ runs Python code." },
  { id := "decimal-signal-dict-type-error-message", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context._set_signal_dict", "Context.__setattr__"]
    statement := "Assigning anything but a dict to a _pydecimal Context's traps (or flags) raises TypeError('<value> must be a signal dict')."
    source := "the message Lib/_pydecimal.py:4021 writes; twin agreement (_decimal: 'argument must be a signal dict')"
    status := .refuted, prop := ``SignalDictTypeErrorMessage, thm := some ``signalDictTypeErrorMessage_refuted
    bug := some "decimal-pydecimal-signal-dict-tuple-message"
    notes := "Context().traps = (): '%s must be a signal dict' % () fails with 'not enough arguments for format string (got 0)'; a tuple of two or more elements gives 'not all arguments converted during string formatting'." },
  { id := "decimal-context-init-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context.__init__", "Context.__setattr__", "Context._set_integer_check", "Context._set_signal_dict"]
    statement := "For every DefaultContext (traps a signal dict; a non-str rounding it holds equal to its stored mode), Context(prec, rounding, Emin, Emax, capitals, clamp, flags, traps, _ignored_flags) with ints, rounding modes, a list of signals for _ignored_flags, and lists or dicts for flags and traps returns, when every value is accepted, exactly the context with the given values, the DefaultContext's for the omitted ones (flags all clear and _ignored_flags empty when omitted), a list becoming the dict of the listed signals and a dict stored as given; otherwise the first refused value in the order prec, rounding, Emin, Emax, capitals, clamp, traps, flags raises: the ValueError of _set_integer_check (the int/str-limit ValueError for an int of more than 4300 digits), TypeError('<s>: invalid rounding mode'), for a list with a non-signal the exception hashing its first unhashable element raises in dict(...) (a TypeError becoming 'cannot use <type> as a dict key'), else KeyError('<d> is not a valid signal dict') or the exception repr() of the first element that does not print raises, and for a dict that is not a signal dict the KeyError or the exception repr() of its first key or value that does not print raises; a prec that is not an int raises TypeError('prec must be an integer')."
    source := "Doc/library/decimal.rst:1104-1120 (Context constructor); Lib/_pydecimal.py:3969-4003"
    status := .proven, prop := ``ContextInitExact, thm := some ``contextInitExact_proven
    notes := "Context(prec=-10**5000) and Context(clamp=10**5000) raise the int/str-limit ValueError (checked on 3.15.2); Context(flags={1: 2}, traps={3: 4}) reports the traps dict, which is assigned first. Checked on 3.15.2: Context(traps=[[]]) raises TypeError: cannot use 'list' as a dict key (unhashable type: 'list'), Context(traps=[10**5000]) and Context(flags={10**5000: 1}) the int/str-limit ValueError, Context(traps=[R(), []]) the unhashable TypeError before R's raising __repr__ is reached." },
  { id := "decimal-convert-other-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_convert_other"]
    statement := "_convert_other returns a Decimal unchanged and an int n as the exact Decimal(n) (sign n < 0, coefficient |n|, exponent 0), raising the int/str-limit ValueError exactly when |n| has more than 4300 digits; any other operand is NotImplemented, or with raiseit what raise TypeError('Unable to convert %s to Decimal' % other) raises: the TypeError when str(other) prints, its own exception when it does not (the int/str-limit ValueError for [10**5000] or Fraction(10**5000))."
    source := "Lib/_pydecimal.py:6096-6113; decimal docs: 'Each Context method accepts a Python integer anywhere that a Decimal instance is accepted'"
    status := .proven, prop := ``ConvertOtherExact, thm := some ``convertOtherExact_proven
    notes := "With decimal-context-methods-match-decimal (each Context method is the Decimal method on the converted operands, the first failing conversion raising), this fixes what every Context method does with an int operand. Checked on 3.15.2: Context().plus([10**5000]), Context().plus(Fraction(10**5000)) and Context().add(1, [10**5000]) (the wrapper's own '% b', :4248) raise the int/str-limit ValueError." },
  { id := "decimal-convert-other-type-error-message", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_convert_other"]
    statement := "_convert_other(x, raiseit=True) raises TypeError('Unable to convert <x> to Decimal') for every operand that is not a Decimal or an int."
    source := "the message Lib/_pydecimal.py:6112 writes; twin agreement (_decimal: 'conversion from <type> to Decimal is not supported')"
    status := .refuted, prop := ``ConvertOtherTypeErrorMessage, thm := some ``convertOtherTypeErrorMessage_refuted
    bug := some "decimal-pydecimal-signal-dict-tuple-message"
    notes := "Context().plus(()): '... %s ...' % () takes the empty tuple as the argument tuple and fails with 'not enough arguments for format string (got 0)'. Context.add and the other arithmetic wrappers format their second operand the same way (:4248)." },
  { id := "decimal-unary-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__pos__", "Decimal.__neg__", "Decimal.__abs__", "Decimal._fix", "Decimal._check_nans"]
    statement := "For every context with prec >= 1: +x, -x and abs(x) of a finite non-zero x are x, -x and |x| rounded into the context by _fix (decimal-fix-exact); of a zero, the zero _fix makes of +0 (of -0 for +(-0) and -(+0) under ROUND_FLOOR), abs giving +0 always; of an infinity, the same, the negated and the positive infinity; of a quiet NaN, the NaN quieted with its own sign (no negation), and a signaling NaN signals InvalidOperation."
    source := "decimal docs, Context.plus/minus/abs ('the result is rounded to the context'); General Decimal Arithmetic, 'plus', 'minus', 'abs'"
    status := .proven, prop := ``UnaryExact, thm := some ``unaryExact_proven },
  { id := "decimal-mul-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "_WorkRep.__init__", "Decimal._fix", "Context.Etiny", "Context.Etop"]
    statement := "For every context with prec >= 1: the product of two finite non-zero decimals is the exact product rounded into the context by _fix (overflow and the subnormal range included, decimal-fix-exact), and the only other outcome is the int/str-limit ValueError, raised exactly when a coefficient or the product has more than 4300 digits and neither coefficient is 1; a zero operand gives the zero _fix makes of ±0·10^(ea+eb); an infinity times a non-zero finite value or an infinity is the infinity of the product's sign, times a zero InvalidOperation."
    source := "General Decimal Arithmetic, 'multiply'; decimal docs, Context.multiply"
    status := .proven, prop := ``MulExact, thm := some ``mulExact_proven
    notes := "Unconditional equation for (mul c a b).run fl; supersedes the conditional decimal-mul-correctly-rounded, and decides the open decimal-mul-overflow-correct and decimal-mul-subnormal-correct through fixSpec (those statements are left as they were)." },
  { id := "decimal-same-quantum-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.same_quantum"]
    statement := "same_quantum of two finite values is True exactly when their exponents are equal; with a special operand it is True exactly when both are NaNs or both are infinities."
    source := "decimal docs, same_quantum: 'Test whether self and other have the same exponent or whether both are NaN'; General Decimal Arithmetic, 'samequantum'"
    status := .proven, prop := ``SameQuantumExact, thm := some ``sameQuantumExact_proven },
  { id := "decimal-logb-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.logb", "Decimal.adjusted"]
    statement := "For every context with prec >= 1, logb of a finite non-zero value is its adjusted exponent A = e + digits - 1 as a Decimal rounded into the context by _fix when |A| has at most 4300 digits, and otherwise the int/str-limit ValueError of Decimal(A)'s str(abs(A)); logb(0) signals DivisionByZero and returns -Infinity; logb(±Infinity) is Infinity; a NaN goes through _check_nans."
    source := "decimal docs, logb: 'the adjusted exponent of the operand ... If the operand is a zero then Decimal('-Infinity') is returned and the DivisionByZero flag is raised. If the operand is an infinity then Decimal('Infinity') is returned'"
    status := .proven, prop := ``LogbExact, thm := some ``logbExact_proven
    notes := "Decimal((0, (1,), 10**4300)).logb() raises 'Exceeds the limit (4300 digits) for integer string conversion...' and Decimal((0, (1,), 10**4299)).logb() returns 1.000000000000000000000000000E+4299 (checked on 3.15.2). The model makes the result with pyFromInt, the mirror of Decimal(int)." },
  { id := "decimal-scaleb-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.scaleb"]
    statement := "For every context with prec >= 1, scaleb(±co·10^e, n) for an integral n (exponent 0, at most 4300 digits) with |n| <= 2·(Emax + prec) is ±co·10^(e+n) rounded into the context by _fix; an n outside that range, a non-integral n (non-zero exponent or infinity) signals InvalidOperation; an infinite first operand is returned unchanged; NaNs go through _check_nans."
    source := "decimal docs, scaleb: 'Return the first operand with exponent adjusted by the second'; General Decimal Arithmetic, 'scaleb'"
    status := .proven, prop := ``ScalebExact, thm := some ``scalebExact_proven },
  { id := "decimal-fma-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.fma", "Context.fma", "_convert_other"]
    statement := "Context.fma converts a, b and t in order, the first failing conversion raising; for finite a and b, fma is __add__ of the exact, unrounded product ±(ca·cb)·10^(ea+eb) and t, except for the int/str-limit ValueError when a coefficient or the product has more than 4300 digits; a signaling NaN a, else b, signals InvalidOperation and is returned quieted; an infinity times zero is InvalidOperation; an infinity times a non-zero finite value adds the signed infinity to t."
    source := "Decimal.fma docstring: 'Returns self*other+third with no rounding of the intermediate product self*other'"
    status := .proven, prop := ``FmaExact, thm := some ``fmaExact_proven
    notes := "The single final rounding is __add__'s, which decimal-add-exact states for every operand pair: for finite a, b, t with a non-zero product the result is the exact a*b + t rounded once by _fix." },
  { id := "decimal-context-predicates-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context.is_signed", "Context.canonical", "Context.is_canonical", "_convert_other"]
    statement := "Context.is_signed(a) is the sign bit of a Decimal (True for -0) and n < 0 for an int within the int/str limit; Context.canonical and is_canonical return the Decimal itself and True for a Decimal and raise TypeError for every other operand, ints included."
    source := "decimal docs, Context.is_signed, canonical, is_canonical"
    status := .proven, prop := ``ContextPredicatesExact, thm := some ``contextPredicatesExact_proven },
  { id := "decimal-pow10a-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_is_less_than_pow10a", "_tento"]
    statement := "For every math.log10 that is accurate to 19 ulps (on ints q >= 10 with fewer than 2**40 digits: a finite double in [1, 2**40) whose 19-ulp interval meets [len(str(q)) - 1, len(str(q)))), _is_less_than_pow10a(q, a) returns len(str(q)) <= a for every a and every such q: both assertions hold, z - 20 ulp is exact, z + 20 ulp rounds within the band, and the exact _tento(inthi) = 10**inthi comparison settles a band that straddles an integer."
    source := "the helper's docstring: 'Check that len(str(q)) <= a without computing str(q)' (Lib/_pydecimal.py:504-517)"
    status := .proven, prop := ``Pow10aExact, thm := some ``pow10aExact_proven
    notes := "math.log10 is a parameter of the model (it is libm's). Unlike _is_less_than_pow10a_use_str (decimal-pydecimal-pow10-float-misfire), the margin here is wide: CPython's log10 of an int is within about one ulp (libm log10 of the correctly rounded double, or fma(log10(2), e, log10(x)) past 2**1024, whose constant's error contributes under 0.1 ulp), and the largest error measured on 3.15.2 over 2824 ints up to 2**1000000 bits is 0.56 ulp, against the 19 the proof allows. No misfire, so no bug record. The digit bound excludes only ints of more than 10**12 digits." },
  { id := "decimal-remainder-near-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.remainder_near", "_is_less_than_pow10a", "_tento", "_WorkRep.__init__"]
    statement := "For every context with prec >= 1 and every accurate math.log10: for finite non-zero operands within the int/str limit whose adjusted exponents differ by -1 to prec, remainder_near(a, b) is InvalidOperation (DivisionImpossible) exactly when the integer n nearest a/b (ties to even) has more than prec digits, and otherwise r = a - n·b at exponent min(ea, eb), with the sign of a flipped when r < 0, rounded into the context by _fix, where |r| <= |b|/2 (and n is even when |r| = |b|/2); the int/str-limit ValueError of str(r) is the only other outcome. A zero b or an infinite a is InvalidOperation, an infinite b gives a through _fix."
    source := "decimal docs, remainder_near: 'Return the remainder from dividing self by other ... the nearest integer to the exact value of self / other, and if two integers are equally near then the even one is chosen'; General Decimal Arithmetic, 'remainder-near'"
    status := .proven, prop := ``RemainderNearExact, thm := some ``remainderNearExact_proven
    notes := "The model's remainderNear (and Context.remainder_near) runs with log10Stand, which log10Stand_accurate proves accurate, so the statement covers it. The quotient is assumed to have fewer than 2**40 digits." },
  { id := "decimal-to-integral-exact-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.to_integral_exact", "Decimal._rescale", "Decimal._cmp", "Context._raise_error"]
    statement := "For every context and rounding argument: to_integral_exact returns a finite value with exponent >= 0 unchanged, turns a zero with a negative exponent into the zero of its sign at exponent 0, and rounds a non-zero value with a negative exponent to the integer the mode prescribes at exponent 0, signalling Inexact (only when non-zero digits were dropped) and then Rounded, the first trapped one raising; the int/str-limit ValueError is raised exactly when the rounded integer is the truncated one plus one with more than 4300 digits; an infinity is returned unchanged and a NaN goes through _check_nans."
    source := "decimal docs: 'Round to the nearest integer, signaling Inexact or Rounded as appropriate if rounding occurs' (Doc/library/decimal.rst:921-922)"
    status := .proven, prop := ``ToIntegralExactExact, thm := some ``toIntegralExactExact_proven
    notes := "Unconditional; supersedes decimal-to-integral-exact-correct (which holds only when it returns). Rounded is raised even when the dropped digits are zeros (:2759), as in libmpdec." },
  { id := "decimal-normalize-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.normalize", "Decimal._fix", "Decimal._check_nans"]
    statement := "For every context and every operand that is not a NaN, normalize first rounds it with _fix (decimal-fix-exact), raising what _fix raises; a zero result becomes the zero of its sign at exponent 0; a non-zero ±co·10^e loses as many trailing zeros as divide co, but none past the exponent Emax (Etop under clamp=1); an infinity is returned. NaNs go through _check_nans."
    source := "decimal docs, normalize: 'Normalize the number by stripping the rightmost trailing zeros and converting any result equal to Decimal('0') to Decimal('0e0')'"
    status := .proven, prop := ``NormalizeExact, thm := some ``normalizeExact_proven
    notes := "The count k of stripped zeros is pinned by its three properties (10**k divides co; the exponent limit is reached or 10**(k+1) does not divide co; k = 0 or e + k <= the limit). Supersedes the open decimal-normalize-correct." },
  { id := "decimal-c-context-clean-template", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["context_new", "context_init_impl"]
    statement := "For a template whose flags are clear and whose capitals is 1, the state DefaultContext starts in, _decimal's Context() equals the template in every field."
    source := "narrowed version of decimal-c-context-clears-flags and decimal-c-context-copies-capitals"
    status := .proven, prop := ``ContextNewCleanTemplate, thm := some ``contextNewCleanTemplate_proven },
  { id := "decimal-context-attr-twins", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Context.__setattr__", "Context._set_integer_check", "context_setattr", "context_setprec",
              "context_setemin", "context_setemax", "context_setcapitals", "context_setclamp"]
    statement := "An integer prec, Emin, Emax, capitals or clamp in its documented range is stored by both twins, and one outside it (within ssize_t) is refused by both with ValueError."
    source := "twin agreement; decimal docs, Context attributes"
    status := .proven, prop := ``ContextAttrTwins, thm := some ``contextAttrTwins_proven
    notes := "prec above MAX_PREC and Emin, Emax beyond their limits are outside the documented ranges; _pydecimal does not enforce those limits." },
  { id := "decimal-c-signaldict-eq-items", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["signaldict_richcompare"]
    statement := "Two SignalDicts with the same items compare equal."
    source := "Mapping contract, Lib/_collections_abc.py:822; SignalDict is a MutableMapping, _decimal.c:7796-7797; twin agreement"
    status := .refuted, prop := ``SignalDictEqualityByItems, thm := some ``signalDictEqualityByItems_refuted
    bug := some "decimal-c-signaldict-eq-raw-bits"
    notes := "After ctx.divide(0, 0) in one context and ctx.create_decimal('xyz') in another, both show InvalidOperation, but the status words differ in which condition bit is set." },
  { id := "decimal-c-signaldict-eq-copy", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["signaldict_richcompare", "dict_as_flags", "flags_as_dict"]
    statement := "ctx.flags == ctx.flags.copy(), for every status word."
    source := "Mapping contract, Lib/_collections_abc.py:822; twin agreement"
    status := .refuted, prop := ``SignalDictEqualsCopy, thm := some ``signalDictEqualsCopy_refuted
    bug := some "decimal-c-signaldict-eq-raw-bits"
    notes := "dict_as_flags turns InvalidOperation: True into all seven bits of MPD_IEEE_Invalid_operation; an operation sets one." },
  { id := "decimal-c-signaldict-eq-canonical", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["signaldict_richcompare"]
    statement := "Status words in which the bits of InvalidOperation are all set or all clear, as assignment and dict conversion leave them, compare equal when their items are equal."
    source := "narrowed version of decimal-c-signaldict-eq-items"
    status := .proven, prop := ``SignalDictEqualityCanonical, thm := some ``signalDictEqualityCanonical_proven },
  { id := "decimal-c-signaldict-set-get", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["signaldict_getitem", "signaldict_setitem"]
    statement := "ctx.flags[s] = v then ctx.flags[s] gives v, whichever bits were set before, and no other signal changes."
    source := "Mapping contract; invariant"
    status := .proven, prop := ``SignalDictSetGet, thm := some ``signalDictSetGet_proven },
  { id := "decimal-divide-verdict", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._divide", "Decimal._rescale", "_WorkRep.__init__", "_is_less_than_pow10a_use_str"]
    statement := "For finite non-zero operands, a returning _divide gives the exact integer quotient and remainder of the operands scaled to their lower exponent, when the operand gap is small or _is_less_than_pow10a_use_str says the quotient fits, and otherwise InvalidOperation."
    source := "Doc/library/decimal.rst:441: 'the usual identity x == (x // y) * y + x % y'; _pydecimal.py:1452-1459"
    status := .proven, prop := ``DivideVerdict, thm := some ``divideVerdict_proven
    notes := "The conclusion names the decision instead of q < 10**prec, because 3.15 replaced that comparison with float tests; decimal-divide-correct keeps the stronger statement, open." },
  { id := "decimal-pow10-band-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_is_less_than_pow10a_use_str"]
    statement := "In the band the two float tests leave open, _is_less_than_pow10a_use_str(q, a) is q < 10**a, for every q and a >= 1."
    source := "Docstring of _is_less_than_pow10a_use_str, _pydecimal.py:471-476"
    status := .proven, prop := ``Pow10BandExact, thm := some ``pow10BandExact_proven },
  { id := "decimal-divide-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._divide", "_WorkRep.__init__", "_is_less_than_pow10a_use_str"]
    statement := "For finite non-zero operands, a returning _divide gives the integer quotient and remainder of the operands scaled to their lower exponent, the quotient at exponent 0 with the sign of the product and the remainder at min(ea, eb) with the sign of the dividend, or NaN for both with InvalidOperation exactly when the quotient has more than prec digits."
    source := "Doc/library/decimal.rst:441: 'the usual identity x == (x // y) * y + x % y'; General Decimal Arithmetic, 'divide-integer' and 'remainder'; DivisionImpossible docstring, _pydecimal.py:190-196"
    status := .refuted, prop := ``DivideCorrect, thm := some ``divideCorrect_refuted
    bug := some "decimal-pydecimal-pow10-float-misfire"
    notes := "Decimal('1E+355861594')._divide(Decimal('1.000000001')) at prec 355861594, traps off: the quotient 10**355861603 // 1000000001 has 355861594 digits (proven with 128-bit interval arithmetic, Pow10Refute.lean), but _is_less_than_pow10a_use_str's float test calls it too large, so the result is NaN with InvalidOperation. Proven on 3.14.7, where the test was q < 10**prec." },
  { id := "decimal-truediv-specials", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__truediv__", "DivisionByZero.handle"]
    statement := "x/0 is a signed infinity with DivisionByZero, 0/0 and inf/inf are NaN with InvalidOperation, inf/x is a signed infinity with no flag, and x/inf is a signed zero at Etiny with Clamped."
    source := "General Decimal Arithmetic, 'divide'"
    status := .proven, prop := ``TruedivSpecials, thm := some ``truedivSpecials_proven },
  { id := "decimal-truediv-core", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__truediv__", "_WorkRep.__init__"]
    statement := "For finite non-zero operands, __truediv__'s integer division gives q, e with: either q*10^e is the exact quotient, at the ideal exponent unless trailing digits prevent it, or q has more than prec digits, its last digit is not 0 or 5, and the exact quotient lies strictly between q0 and q0+1 for q0 equal to q or q-1."
    source := "General Decimal Arithmetic, 'divide'; the comment at _pydecimal.py:1415"
    status := .proven, prop := ``TruedivCoreCorrect, thm := some ``truedivCoreCorrect_proven
    notes := "This is the integer core. That _fix of this q gives the correctly rounded quotient is the sticky-digit argument, not yet stated." },
  { id := "decimal-divmod-consistent", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__divmod__", "Decimal.__mod__", "Decimal.__floordiv__", "Decimal._divide", "Decimal._fix"]
    statement := "For finite operands with a non-zero divisor, //, % and divmod run the same _divide, so divmod(x, y) is (x // y, x % y), with _fix applied to the remainder alone."
    source := "Doc/reference/datamodel.rst:3418: __divmod__ 'should be the equivalent to using __floordiv__() and __mod__()'"
    status := .proven, prop := ``DivmodConsistent, thm := some ``divmodConsistent_proven },
  { id := "decimal-floordiv-twins-agree", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floordiv__", "Decimal._divide"]
    statement := "// gives the same result and flags in both twins, for every context and operands."
    source := "twin agreement; Doc/library/decimal.rst:1738 on Overflow"
    status := .refuted, prop := ``FloordivTwinsAgree, thm := some ``floordivTwinsAgree_refuted
    bug := some "decimal-pydecimal-floordiv-no-finalize"
    notes := "Context(prec=28, Emax=10, Emin=-10, traps=[]).divide_int(Decimal(10)**20, 1): _pydecimal returns the quotient unfixed, _decimal gives Infinity with Overflow." },
  { id := "decimal-floordiv-twins-in-range", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floordiv__", "Decimal._divide"]
    statement := "In a context with Emin <= 0 and Emax >= prec - 1, a returning // gives the same value and flags in both twins, for finite operands with a non-zero divisor."
    source := "narrowed version of decimal-floordiv-twins-agree"
    status := .open, prop := ``FloordivTwinsAgreeInRange
    notes := "Missing: joining DivideCorrect to mpdDivmodFin and cOp. fix_int, the main lemma, is proven." },
  { id := "decimal-tuple-twins-agree", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__new__", "dectuple_as_str", "PyDecType_FromCStringExact", "Decimal.__str__", "dec_str"]
    statement := "For every tuple (sign, digits, exp) with |exp| <= 10**17 and at most 10**17 digits, if _pydecimal.Decimal(t) succeeds then _decimal.Decimal(t) succeeds and str() of both agree."
    source := "twin agreement; Decimal docs: 'three components, a sign ..., a tuple of digits, and an integer exponent' (Doc/library/decimal.rst:387-389)"
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
    pyFns := ["_decimal_Decimal___format___impl"]
    statement := "For every format spec not ending in the C-only deprecated type 'N', if format(_decimal.Decimal(x), spec) accepts the spec, so does _pydecimal."
    source := "twin agreement; format spec mini-language (int, str and Fraction reject these specs; float rejects all but a single trailing NUL)"
    status := .refuted, prop := ``FormatCAcceptsOnlyPy, thm := some ``formatCAcceptsOnlyPy_refuted
    bug := some "decimal-c-format-spec-nul"
    notes := "format(Decimal('1234.5'), '10\\x00xyz') == '    1234.5': _decimal_Decimal___format___impl passes the UTF-8 buffer to libmpdec as a C string, which ends at the embedded NUL." },
  { id := "decimal-format-no-encode-error", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["_decimal_Decimal___format___impl"]
    statement := "format(_decimal.Decimal(x), spec) never raises UnicodeEncodeError."
    source := "invariant; twin agreement (_pydecimal, float, int and Fraction accept a lone surrogate fill)"
    status := .refuted, prop := ``FormatNoEncodeError, thm := some ``formatNoEncodeError_refuted
    bug := some "decimal-c-format-surrogate-fill"
    notes := "format(Decimal('1.5'), '\\ud800<5'): PyUnicode_AsUTF8AndSize fails on the surrogate before any parsing." },
  { id := "decimal-rounding-modes-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._rescale", "Decimal._round_down", "Decimal._round_up", "Decimal._round_half_up",
              "Decimal._round_half_down", "Decimal._round_half_even", "Decimal._round_ceiling",
              "Decimal._round_floor", "Decimal._round_05up"]
    statement := "For all 8 rounding modes, every finite non-zero value and every larger target exponent, _rescale returns the coefficient the mode prescribes (roundSpec: truncate / away from zero / toward ±inf / nearest with ties up, down, even / 05up), and raises the int-limit ValueError exactly when that coefficient is the truncated prefix plus one and has more than 4300 digits (a 5000-digit coefficient that is only truncated rounds without error); to a smaller or equal exponent it pads with zeros, and a zero coefficient just takes the new exponent."
    source := "decimal docs, 'Rounding modes'; General Decimal Arithmetic, 'Rounding'"
    status := .proven, prop := ``RoundingModesCorrect, thm := some ``roundingModesCorrect_proven
    notes := "Covers the digits-below-zero substitution (_pydecimal.py:2700-2702). The ValueError branch is decimal-pydecimal-int-max-str-digits." },
  { id := "decimal-to-integral-value-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.to_integral_value", "Decimal._rescale"]
    statement := "For every context, rounding argument and value, to_integral_value returns a finite value unchanged if its exponent is >= 0, and otherwise the correctly rounded integer at exponent 0 without setting any flag (a zero gives the signed zero); it raises the int-limit ValueError exactly when that integer is the truncated one plus one with more than 4300 digits; an infinity is returned unchanged, a quiet NaN quieted, and a signaling NaN signals InvalidOperation."
    source := "to_integral_value docstring ('without raising inexact, rounded'), decimal docs"
    status := .proven, prop := ``ToIntegralValueCorrect, thm := some ``toIntegralValueCorrect_proven },
  { id := "decimal-quantize-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.quantize", "Decimal._rescale", "Decimal._fix", "Decimal.__round__", "Decimal._cmp",
              "Decimal.adjusted", "Context.Etiny", "Context.Etop", "Context._raise_error"]
    statement := "For every context with prec >= 1, rounding mode and finite operands, when quantize returns: if the correctly rounded (or zero-padded) coefficient q' at the target exponent fits (target in [Etiny, Emax], q' has at most prec digits, its adjusted exponent is at most Emax), the result is q' at that exponent (folded down to Etop under clamp, same value) and Inexact is set exactly when non-zero digits were dropped; otherwise the result is NaN with InvalidOperation set."
    source := "decimal docs, quantize: 'Return a value equal to the first operand after rounding and having the exponent of the second operand'; 'if the length of the coefficient after the quantize operation would be greater than precision, then an InvalidOperation is signaled'"
    status := .proven, prop := ``QuantizeCorrect, thm := some ``quantizeCorrect_proven
    notes := "round(d, n) is quantize(Decimal((0, (1,), -n))) by definition (_pydecimal.py:1934-1935, _decimal.c _decimal_Decimal___round___impl, formerly PyDec_Round), so this covers it for |n| < 2**63. Beyond that _decimal raises OverflowError and _pydecimal does not: a discrepancy deccheck.py already lists (SkipHandler.__round__), not recorded as a bug here. Conditional on returning: a trapped signal or the int-limit ValueError raises instead. Under clamp=1 the result's exponent can be below the operand's (the fold-down keeps the value), so the docs' 'the quantized exponent is always equal to that of the right-hand operand' holds only for clamp=0, in both twins." },
  { id := "decimal-mul-correctly-rounded", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "Decimal._fix", "_WorkRep.__init__", "Context.Etiny", "Context.Etop", "Context._raise_error"]
    statement := "For every context with prec >= 1, all 8 rounding modes and all finite non-zero operands, when * returns a value in the normal range (no subnormal result, no overflow after rounding), that value is the exact product correctly rounded to prec digits, including the carry from 99...9 to 100...0 (folded down under clamp when nothing was rounded), Inexact is set exactly when non-zero digits were dropped, and Rounded exactly when any digits were dropped."
    source := "General Decimal Arithmetic, 'multiply' and 'Rounding'; decimal docs, signals Inexact and Rounded"
    status := .proven, prop := ``MulCorrect, thm := some ``mulCorrect_proven
    notes := "The subnormal and overflow ranges of _fix are hypotheses here; they are stated by decimal-mul-subnormal-correct and decimal-mul-overflow-correct, and + and - by decimal-add-correct and decimal-sub-correct, all open. Conditional on returning: a trapped signal or the int-limit ValueError raises instead." },
  { id := "decimal-to-integral-exact-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.to_integral_exact", "Decimal._rescale", "Decimal._cmp", "Context._raise_error"]
    statement := "For every context, rounding argument and finite non-zero value with exponent < 0, when to_integral_exact returns, the result is the correctly rounded integer at exponent 0, Rounded is set, and Inexact is set exactly when non-zero digits were dropped."
    source := "decimal docs: 'signaling Inexact or Rounded as appropriate if rounding occurs' (Doc/library/decimal.rst:921-922)"
    status := .proven, prop := ``ToIntegralExactCorrect, thm := some ``toIntegralExactCorrect_proven },
  { id := "decimal-int-conversions-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["dec_as_long", "_decimal_Decimal___round___impl", "_decimal_Decimal___floor___impl",
      "_decimal_Decimal___ceil___impl", "_decimal_Decimal___trunc___impl"]
    statement := "For every finite decimal and rounding mode, _decimal's int()/math.floor/math.ceil/round() return the signed integer whose magnitude the mode prescribes (exact for exponents >= 0)."
    source := "__floor__/__ceil__/__round__/__int__ docs"
    status := .proven, prop := ``IntConversionsC, thm := some ``intConversionsC_proven },
  { id := "decimal-int-conversions-py-or-limit", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__floor__", "Decimal.__ceil__", "Decimal.__round__", "Decimal.__int__", "Decimal._rescale"]
    statement := "For every finite decimal and rounding mode, _pydecimal's int(), math.floor, math.ceil and round() return the same int as _decimal's when that int has at most 4300 digits, and raise the int-limit ValueError exactly when it has more (math.floor(Decimal((0, (1,)*5000, -4999))) is 1); a NaN raises ValueError('cannot round a NaN') and an infinity OverflowError('cannot round an infinity'); round(d, n) with a non-int n raises TypeError, and with an int n is quantize(Decimal((0, (1,), -n)))."
    source := "twin agreement (narrowed version of decimal-int-conversions-py)"
    status := .proven, prop := ``IntConversionsPyOrLimit, thm := some ``intConversionsPyOrLimit_proven },
  { id := "decimal-hash-consistent-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["_dec_hash", "dec_from_long"]
    statement := "For every finite Decimal d, hash(d) == hash(Fraction(*d.as_integer_ratio())), and for every int n, hash(Decimal(n)) == hash(n), in _decimal."
    source := "Built-in Types, 'Hashing of numeric types': x == y implies hash(x) == hash(y)"
    status := .proven, prop := ``HashConsistentC, thm := some ``hashConsistentC_proven
    notes := "Reuses PyLean.Fractions.hashMatchesDecimal_proven / hashMatchesInt_proven. The C constant inv10_p equals pow(10, P-2, P) (tenInv_eq)." },
  { id := "decimal-ratio-correct-c", pyFile := "Modules/_decimal/_decimal.c"
    pyFns := ["_decimal_Decimal_as_integer_ratio_impl"]
    statement := "For every finite Decimal, as_integer_ratio() returns (n, d) with d > 0, n and d coprime, and n/d exactly the value."
    source := "as_integer_ratio docstring, _pydecimal.py:1021-1033"
    status := .proven, prop := ``RatioCorrectC, thm := some ``ratioCorrectC_proven },
  { id := "decimal-pow10-correct", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_is_less_than_pow10a_use_str"]
    statement := "For every q and a >= 1, if _is_less_than_pow10a_use_str(q, a) returns, its first item is q < 10**a."
    source := "Docstring of _is_less_than_pow10a_use_str, _pydecimal.py:471-476, and the claims in its comments (:479-492)"
    status := .refuted, prop := ``Pow10Correct, thm := some ``pow10Correct_refuted
    bug := some "decimal-pydecimal-pow10-float-misfire"
    notes := "q = 10**355861603 // 1000000001, a = 355861594: q has bit length 1182146628 and 355861594 digits, and the double 1 + a*_LOG_10_BASE_2_HI is exactly 1182146628.0, so the helper returns (False, None). The smallest such a below 4*10**9; the _LOG_10_BASE_2_LO test never misfires in that range. The band where str(q) decides is decimal-pow10-band-exact." },
  { id := "decimal-cmp-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._cmp", "Decimal._isinfinity", "Decimal.__bool__"]
    statement := "For all decimals that are not NaNs, _cmp is the exact numeric order: finite values compared at the lower exponent as integers, -Infinity below and Infinity above every finite value, +0 equal to -0."
    source := "_cmp docstring, _pydecimal.py:863-866: 'Returns -1 if self < other, 0 if self == other and 1 if self > other'"
    status := .proven, prop := ``CmpExact, thm := some ``cmpExact_proven },
  { id := "decimal-check-nans-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._check_nans", "Decimal._isnan", "Decimal._fix_nan", "InvalidOperation.handle", "Context._raise_error"]
    statement := "_check_nans: a signaling NaN on either side signals InvalidOperation (raising if trapped) and returns that operand quiet with its payload cut to prec - clamp digits, the left one first; otherwise a quiet NaN is returned so, the left one first, with no flag; with no NaN it returns 0. The same for the one-operand form."
    source := "_check_nans docstring, _pydecimal.py:791-798; InvalidOperation docstring (:136-157)"
    status := .proven, prop := ``CheckNansExact, thm := some ``checkNansExact_proven },
  { id := "decimal-compare-check-nans-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._compare_check_nans", "Decimal.is_snan", "Decimal.is_qnan", "Decimal._fix_nan",
              "InvalidOperation.handle", "Context._raise_error"]
    statement := "_compare_check_nans signals InvalidOperation for any NaN operand and returns the signaling one before a quiet one, the left before the right, quieted; with no NaN it returns 0 and sets nothing."
    source := "_compare_check_nans docstring, _pydecimal.py:823-831: 'Signaling NaNs take precedence over quiet NaNs.'"
    status := .proven, prop := ``CompareCheckNansExact, thm := some ``compareCheckNansExact_proven },
  { id := "decimal-comparisons-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__eq__", "Decimal.__lt__", "Decimal.__le__", "Decimal.__gt__", "Decimal.__ge__",
              "Decimal.compare", "Decimal.compare_signal", "Decimal._cmp", "Decimal._check_nans",
              "Decimal._compare_check_nans", "_convert_for_comparison"]
    statement := "For two Decimals: without NaNs, ==, <, <=, >, >= are the exact numeric order with no flag, and compare and compare_signal return Decimal(-1/0/1) of it; with a NaN, == is False and signals InvalidOperation only for a signaling NaN, the orderings and compare_signal signal InvalidOperation for every NaN and the orderings are False, and compare and compare_signal return the NaN chosen sNaN-first, left-first."
    source := "Comment at _pydecimal.py:909-924 on rich comparisons and NaNs; compare docstring (:971-977); decimal docs, compare_signal"
    status := .proven, prop := ``ComparisonsExact, thm := some ``comparisonsExact_proven
    notes := "Operators are called as a == b (context=None), so the context read is getcontext()." },
  { id := "decimal-convert-comparisons", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_convert_for_comparison", "Decimal.__eq__", "Decimal.__lt__", "Decimal.__le__", "Decimal.__gt__",
              "Decimal.__ge__"]
    statement := "Against an int or Fraction n/d, a comparison is that of self*d with Decimal(n) (for a finite self the exact order of the value and n/d), raising ValueError exactly past the 4300-digit limits; against a float, that with Decimal.from_float(f) after FloatOperation, which == only flags and the orderings signal; a complex with zero imaginary part compares under == as its real part; any other complex or object gives NotImplemented with no flag."
    source := "_convert_for_comparison docstring and comments, _pydecimal.py:6116-6140; decimal docs, FloatOperation"
    status := .proven, prop := ``ConvertComparisonsCorrect, thm := some ``convertComparisonsCorrect_proven
    notes := "The float path is stated through fromFloat, whose exactness is decimal-from-float-exact (open)." },
  { id := "decimal-minmax-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.max", "Decimal.min", "Decimal.max_mag", "Decimal.min_mag"]
    statement := "max, min, max_mag and min_mag of two numbers return _fix of the operand the exact order picks (of the magnitudes for the _mag forms), ties broken by compare_total; a quiet NaN against a number gives _fix of the number; a signaling NaN or two quiet NaNs give _check_nans's result."
    source := "max/min docstrings and comments, _pydecimal.py:2880-2954, :3515-3573; General Decimal Arithmetic, 'max', 'min'"
    status := .proven, prop := ``MinMaxExact, thm := some ``minMaxExact_proven },
  { id := "decimal-compare-total-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.compare_total", "Decimal.compare_total_mag"]
    statement := "compare_total is antisymmetric and 0 only for identical representations; for numbers of different value it is the numeric order; equal values put the negative sign first, and then the lower exponent first when positive and last when negative; a positive NaN is above every number and a negative one below, sNaN below qNaN for positive NaNs and above for negative, NaNs of one kind by payload; operands of opposite signs (NaNs included) put the negative one first. compare_total_mag is that order of the magnitudes: different magnitudes by value, equal magnitudes by exponent (Decimal('1.0').compare_total_mag(Decimal('-1')) is -1, 1 against -1 is 0), every NaN above every number, sNaN below qNaN and NaNs of one kind by payload whatever their signs."
    source := "Doc/library/decimal.rst:518-545 (Decimal('12.0').compare_total(Decimal('12')) == Decimal('-1')); General Decimal Arithmetic, 'compare-total'"
    status := .proven, prop := ``CompareTotalExact, thm := some ``compareTotalExact_proven },
  { id := "decimal-classification-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.number_class", "Decimal.is_normal", "Decimal.is_subnormal", "Decimal.is_zero",
              "Decimal.__bool__", "Decimal._isinfinity", "Decimal.is_snan", "Decimal.is_qnan"]
    statement := "number_class returns each of the ten documented classes by sign, kind, zero coefficient and adjusted() < Emin; is_normal and is_subnormal test that threshold for non-zero finite values and are False otherwise; is_zero and bool test the coefficient (specials are nonzero); _isinfinity is +1/-1 by sign and 0 otherwise."
    source := "number_class docstring (_pydecimal.py:3668-3681); is_normal, is_subnormal, is_zero docstrings; __bool__ docstring (:856-859)"
    status := .proven, prop := ``ClassificationExact, thm := some ``classificationExact_proven },
  { id := "decimal-copy-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.copy_abs", "Decimal.copy_negate", "Decimal.copy_sign"]
    statement := "copy_negate flips the sign and keeps coefficient, exponent, NaN kind and payload: an involution reversing the numeric order; copy_abs is copy_negate on a negative operand and the operand otherwise, and copy_sign(copy_abs(a), a) rebuilds a."
    source := "decimal docs, copy_abs ('Return the absolute value of the argument'), copy_negate ('Return the negation of the argument')"
    status := .proven, prop := ``CopyExact, thm := some ``copyExact_proven },
  { id := "decimal-overflow-handle-table", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Overflow.handle"]
    statement := "Overflow.handle gives the signed infinity for ROUND_HALF_UP, HALF_EVEN, HALF_DOWN and UP; prec nines at exponent Emax - prec + 1 (prec digits, adjusted exponent Emax) with the result's sign for ROUND_DOWN and ROUND_05UP; for ROUND_CEILING that for a negative result and +Infinity otherwise; for ROUND_FLOOR that for a positive result and -Infinity otherwise."
    source := "Overflow docstring, _pydecimal.py:263-282"
    status := .proven, prop := ``OverflowHandleTable, thm := some ``overflowHandleTable_proven
    notes := "ROUND_05UP is not in the docstring; the handler gives the ROUND_DOWN value, which is what 05up rounding of nines gives." },
  { id := "decimal-fix-nan-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal._fix_nan", "InvalidOperation.handle"]
    statement := "_fix_nan keeps the sign and kind and the last prec - clamp payload digits (leading zeros dropped); InvalidOperation.handle returns that, quiet, for its NaN argument, and the positive quiet NaN without one."
    source := "_fix_nan comment, _pydecimal.py:1704-1708; InvalidOperation docstring (:136-157)"
    status := .proven, prop := ``FixNanExact, thm := some ``fixNanExact_proven },
  { id := "decimal-int-trunc-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__int__"]
    statement := "int(d) truncates toward zero, as _decimal's int() does, for every finite decimal; it raises the int-limit ValueError exactly when the digit string it converts (the coefficient for exp >= 0, the integer part otherwise) has more than 4300 digits; NaN raises ValueError and an infinity OverflowError."
    source := "__int__ docstring, _pydecimal.py:1673; twin agreement"
    status := .proven, prop := ``IntTruncExact, thm := some ``intTruncExact_proven },
  { id := "decimal-from-float-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.from_float", "Decimal.__new__", "Decimal.from_number"]
    statement := "Decimal.from_float(f) is exact: for finite f, the sign of f and co / 10**k = |f|; infinities map to signed infinities and NaNs to Decimal('NaN')."
    source := "from_float docstring, _pydecimal.py:720-735: 'Converts a float to a decimal number, exactly.'"
    status := .open, prop := ``FromFloatExact
    notes := "Model: fromFloat and pyNew (Convert.lean). Missing: a bound on as_integer_ratio's numerator and denominator (n < 2**53, d <= 2**1074) to show str(n*5**k) stays under the 4300-digit limit; the value part (co/10**k = n/2**k) went through in a draft." },
  { id := "decimal-compare-total-order", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.compare_total", "Decimal._cmp", "Decimal._isnan"]
    statement := "For all decimals a, b (NaNs, infinities, signed zeros, any exponents), compare_total(b, a) == -compare_total(a, b), and compare_total(a, b) == 0 iff a and b are the same representation."
    source := "compare_total docs: 'the result gives a total ordering on Decimal instances' (Doc/library/decimal.rst:521-522)"
    status := .proven, prop := ``CompareTotalOrder, thm := some ``compareTotalOrder_proven },
  { id := "decimal-mul-nan-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__mul__", "Decimal._check_nans", "_convert_other"]
    statement := "For every context: a product with a NaN operand is what _check_nans gives, whatever the other operand (an infinity included): a signaling NaN on the left, else on the right, signals InvalidOperation and is returned quiet with its payload cut to prec - clamp digits, else the left quiet NaN, else the right one, quieted, with no flag. __mul__'s prologue multiplies a Decimal operand as is and an int n as the exact Decimal(n), raising the int/str-limit ValueError when |n| has more than 4300 digits, and returns NotImplemented for any other operand with no flag."
    source := "Lib/_pydecimal.py:1317-1329; _check_nans docstring (:791-798); General Decimal Arithmetic, 'multiply' (NaN operands)"
    status := .proven, prop := ``MulNanExact, thm := some ``mulNanExact_proven
    notes := "With decimal-mul-exact (finite, zero and infinite operands) every pair of operands is stated. Checked on 3.15.2: NaN12 * Inf = NaN12 with no flag; Inf * sNaN7 = NaN7 with InvalidOperation; NaN123456789 * 1 = NaN56789 at prec 5." },
  { id := "decimal-normalize-nan-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.normalize", "Decimal._check_nans", "Decimal._fix_nan"]
    statement := "For every context, normalize of a quiet NaN returns it with its payload cut to prec - clamp digits and no flag, and of a signaling NaN signals InvalidOperation (raising if trapped) and returns it quiet."
    source := "Lib/_pydecimal.py:2581-2584; General Decimal Arithmetic, 'reduce' (NaN operands)"
    status := .proven, prop := ``NormalizeNanExact, thm := some ``normalizeNanExact_proven
    notes := "With decimal-normalize-exact (every non-NaN operand) normalize is stated for every operand." },
  { id := "decimal-scaleb-rest-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.scaleb", "Decimal._check_nans"]
    statement := "For every context: scaleb with a NaN operand is what _check_nans gives (a signaling NaN, left first, signals InvalidOperation and is returned quiet, else the quiet NaN); for an integral second operand whose digit string has more than 4300 digits, int(other) raises the int/str-limit ValueError ('value has N digits') whatever the non-NaN first operand; and an infinite first operand with an integral n outside [-2*(Emax+prec), 2*(Emax+prec)] signals InvalidOperation."
    source := "Lib/_pydecimal.py:3751-3769; General Decimal Arithmetic, 'scaleb'"
    status := .proven, prop := ``ScalebRestExact, thm := some ``scalebRestExact_proven
    notes := "With decimal-scaleb-exact every operand pair is stated. Checked on 3.15.2: Context().scaleb(1, Decimal((0, (1,)+(0,)*5000, 0))) and the same with Infinity raise 'value has 5001 digits'; scaleb(Inf, 10**9) is NaN with InvalidOperation." },
  { id := "decimal-fma-special-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.fma"]
    statement := "For every context, with no signaling NaN among a and b: a quiet NaN a (else b) is the product, which __add__ returns quieted unless t is a signaling NaN (InvalidOperation, t returned quiet); an infinity times an infinity or a non-zero finite value is the infinity of the product's sign added to t: a NaN t goes through _check_nans, the opposite infinity is InvalidOperation, anything else gives the infinity."
    source := "Decimal.fma docstring and Lib/_pydecimal.py:1986-2017, with __add__'s special branch (:1213-1225)"
    status := .proven, prop := ``FmaSpecialExact, thm := some ``fmaSpecialExact_proven
    notes := "Checked on 3.15.2: fma(NaN1, 2, sNaN2) = NaN2 with InvalidOperation; fma(Inf, -Inf, Inf) = NaN with InvalidOperation; fma(-Inf, 2, sNaN3) = NaN3 with InvalidOperation. The finite product's sum is decimal-fma-exact's __add__, stated by decimal-add-exact." },
  { id := "decimal-abs-no-round-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.__abs__", "Decimal.copy_abs"]
    statement := "For every context, abs(x, round=False) is x with its sign cleared, unrounded and with no flag, a signaling NaN included (no _check_nans)."
    source := "__abs__ docstring: 'self.__abs__(round=False) is equivalent to self.copy_abs()' (Lib/_pydecimal.py:1183-1188)"
    status := .proven, prop := ``AbsNoRoundExact, thm := some ``absNoRoundExact_proven
    notes := "Checked on 3.15.2: Decimal('-sNaN5').__abs__(round=False) is sNaN5 with no flag; Decimal('-1.23456789').__abs__(round=False) at prec 5 is 1.23456789." },
  { id := "decimal-compare-total-mag-rest", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.compare_total_mag"]
    statement := "compare_total_mag(b, a) == -compare_total_mag(a, b) for all decimals, and a number (finite or infinite) against a NaN of either sign and kind is -1."
    source := "compare_total_mag docs: 'like compare_total, but ignoring the sign of each operand' (Doc/library/decimal.rst); total-order antisymmetry"
    status := .proven, prop := ``CompareTotalMagRest, thm := some ``compareTotalMagRest_proven
    notes := "With decimal-compare-total-exact's compare_total_mag conjuncts every pair is stated. Checked on 3.15.2: Decimal(5).compare_total_mag(Decimal('-NaN')) and Decimal('-Inf').compare_total_mag(Decimal('sNaN')) are -1." },
  { id := "decimal-convert-other-tuple-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["_convert_other"]
    statement := "_convert_other(t, raiseit=True) for a tuple t raises what raise TypeError('Unable to convert %s to Decimal' % t) raises: 'not enough arguments for format string (got 0)' for (); the exception str() of the first element raises, when it does (the int/str-limit ValueError for (10**5000,) and (10**5000, 1)); otherwise the TypeError with the formatted message for a 1-tuple and 'not all arguments converted during string formatting (required 1, got k)' for k >= 2 elements."
    source := "Lib/_pydecimal.py:6111-6112; PyUnicode_Format's argument-count errors"
    status := .proven, prop := ``ConvertOtherTupleExact, thm := some ``convertOtherTupleExact_proven
    notes := "What CPython 3.15.2 does (checked: Context().plus((10**5000,)) raises the int/str-limit ValueError), which is the wrong message recorded in decimal-pydecimal-signal-dict-tuple-message; with decimal-convert-other-exact every operand and both raiseit values are stated." },
  { id := "decimal-remainder-near-rest", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.remainder_near", "Decimal._check_nans", "_WorkRep.__init__"]
    statement := "For every context and every math.log10: remainder_near with a NaN operand is what _check_nans gives, before the infinity and zero tests; a zero a is the zero of a's sign at min(ea, eb) through _fix for a non-zero finite b, and a through _fix for an infinite b; for non-zero finite operands whose adjusted exponents differ by prec + 1 or more the result is InvalidOperation (DivisionImpossible), and by -2 or less it is a, padded to exponent min(ea, eb), through _fix; in between, a coefficient of more than 4300 digits raises _WorkRep's int/str-limit ValueError, a's first."
    source := "remainder_near docstring and Lib/_pydecimal.py:1559-1598; General Decimal Arithmetic, 'remainder-near'"
    status := .proven, prop := ``RemainderNearRest, thm := some ``remainderNearRest_proven
    notes := "With decimal-remainder-near-exact (the in-between case within the limit, a zero b, an infinite a or b) every operand pair is stated; the only remaining hypothesis there is a quotient of fewer than 2**40 digits (the domain on which math.log10's accuracy is assumed). Checked on 3.15.2 at prec 5: remainder_near(-0E+5, 3E-2) = -0.00; remainder_near(1E+5, 1) is NaN with InvalidOperation; remainder_near(0.0123456789, 7) = 0.012346 with Inexact, Rounded; a 4301-digit coefficient raises 'value has 4301 digits'." },
  { id := "decimal-quantize-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.quantize", "Decimal._check_nans", "Decimal.__round__", "Context.quantize"]
    statement := "For every context and rounding argument, on every operand pair: for finite ±co·10^e and a finite target exponent qe, with v the coefficient at qe (co padded with zeros when qe <= e, otherwise co with its last qe - e digits dropped and rounded as the mode says): qe outside [Etiny, Emax] is InvalidOperation; a zero becomes the zero of its sign at qe through _fix; an adjusted exponent above Emax, or adjusted - qe + 1 above prec, is InvalidOperation; the int/str-limit ValueError is raised exactly when the rounding incremented to a coefficient of more than 4300 digits; otherwise a result with adjusted exponent above Emax or more than prec digits is InvalidOperation, and else Subnormal (non-zero and below Emin), Inexact (non-zero digits dropped) and Rounded (digits dropped) are signalled in that order, the first trapped one raising, and ±v·10^qe goes through _fix. A NaN operand goes through _check_nans, two infinities give the first operand, one infinity is InvalidOperation."
    source := "quantize docs (Doc/library/decimal.rst, Decimal.quantize); Lib/_pydecimal.py:2600-2659; General Decimal Arithmetic, 'quantize'"
    status := .proven, prop := ``QuantizeExact, thm := some ``quantizeExact_proven
    notes := "Unconditional, so it supersedes decimal-quantize-correct (which holds only when quantize returns). Checked on 3.15.2 at prec 5, Emin -5: quantize(1.234E-6, 1E-8) = 1.23E-6 with Subnormal, Inexact, Rounded, and Subnormal is the one raised when both it and Inexact are trapped; quantize(123, 1E-3) is NaN with InvalidOperation; 4301 nines E-1 quantized to 1 with ROUND_UP raises the int/str-limit ValueError, 4300 nines does not." },
  { id := "decimal-adjusted-exact", pyFile := "Lib/_pydecimal.py"
    pyFns := ["Decimal.adjusted"]
    statement := "adjusted() is exp + (number of coefficient digits) - 1 for every finite decimal, zeros included (Decimal('0E+5').adjusted() == 5), and 0 for every infinity and NaN."
    source := "adjusted docstring 'Return the adjusted exponent of self' and Lib/_pydecimal.py:2973-2977 (the except TypeError for special values)"
    status := .proven, prop := ``AdjustedExact, thm := some ``adjustedExact_proven
    notes := "The difftest compares adjusted() with both twins on every operand kind (the 'adjusted' method case)." }
]

end PyLean.Decimal
