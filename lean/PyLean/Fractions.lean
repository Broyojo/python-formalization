import PyLean.Registry
import PyLean.Fractions.Model
import PyLean.Fractions.Parse
import PyLean.Fractions.Format
import PyLean.Fractions.Diff
import PyLean.Fractions.Ctor
import PyLean.Fractions.Arith
import PyLean.Fractions.ArithProps
import PyLean.Fractions.Round
import PyLean.Fractions.Limit
import PyLean.Fractions.Hash
import PyLean.Fractions.StrProps
import PyLean.Fractions.FormatProps
import PyLean.Fractions.FormatF

/-!
`Lib/fractions.py`, CPython 3.14.7. The model covers construction from ints
and strings, the arithmetic and comparison operators with Fraction and int
operands, `**` with an int exponent, the integer conversions and rounding,
`__hash__`, `limit_denominator`, `__str__` and `__format__`. Float operands
and float conversions are out of scope.
-/

namespace PyLean.Fractions

open PyLean.Registry

def entries : List Entry := [
  { id := "fractions-ctor-normalizes", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__new__"]
    statement := "For all ints n and d != 0, Fraction(n, d) has a positive denominator, numerator and denominator coprime, and value n/d."
    source := "Fraction docs (\"value equal to numerator/denominator\", numerator/denominator \"in lowest terms\", denominator \"Guaranteed to be positive\"); fractions.py:302-311"
    status := .proven, prop := ``CtorNormalizes, thm := some ``ctorNormalizes_proven },
  { id := "fractions-ctor-zero-denominator", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__new__"]
    statement := "For every int n, Fraction(n, 0) raises ZeroDivisionError."
    source := "Fraction docs: \"If denominator is zero, it raises a ZeroDivisionError.\""
    status := .refuted, prop := ``CtorZeroDenominatorRaises, thm := some ``ctorZeroDenominatorRaises_refuted
    bug := some "fractions-zero-denominator-huge-numerator-valueerror"
    notes := "Building the message 'Fraction(%s, 0)' % numerator hits int_max_str_digits when the numerator has more than 4300 digits, so ValueError escapes instead." },
  { id := "fractions-arith-exact", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction._add", "Fraction._sub", "Fraction._mul", "Fraction._div", "_operator_fallbacks"]
    statement := "For all Fraction or int operands, +, -, * and / return a Fraction in lowest terms with positive denominator and the exact rational value; / by zero raises ZeroDivisionError."
    source := "invariant (class invariant; Knuth's normalization argument in the comment at fractions.py:726-790)"
    status := .proven, prop := ``ArithExact, thm := some ``arithExact_proven },
  { id := "fractions-pow-exact", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__pow__"]
    statement := "For every Fraction a and int e, a ** e is a normalized Fraction equal to a^e; 0 ** e raises ZeroDivisionError for e < 0."
    source := "__pow__ docstring, fractions.py:886-891 (\"If b is an integer, the result will be rational\")"
    status := .proven, prop := ``PowExact, thm := some ``powExact_proven },
  { id := "fractions-compare-consistent", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__eq__", "Fraction._richcmp"]
    statement := "For Fraction or int operands, == (structural) and <, <=, >, >= (cross-multiplication) all agree with the rational order."
    source := "invariant"
    status := .proven, prop := ``CompareConsistent, thm := some ``compareConsistent_proven },
  { id := "fractions-divmod-consistent", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction._floordiv", "Fraction._mod", "Fraction._divmod"]
    statement := "For b != 0, divmod(a, b) == (a // b, a % b), a == (a//b)*b + a%b exactly, and a % b is normalized with the sign of b and smaller magnitude; b == 0 raises ZeroDivisionError."
    source := "Python Reference, binary arithmetic operations (floor division and modulo identities)"
    status := .proven, prop := ``DivmodConsistent, thm := some ``divmodConsistent_proven },
  { id := "fractions-int-conversions", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__floor__", "Fraction.__ceil__", "Fraction.__trunc__", "Fraction.__int__",
              "Fraction.is_integer", "Fraction.as_integer_ratio"]
    statement := "floor is the greatest int <= x, ceil the least int >= x, trunc and int round toward zero, is_integer holds iff x is an integer, and as_integer_ratio is in lowest terms with positive denominator."
    source := "fractions docs for __floor__, __ceil__, is_integer, as_integer_ratio"
    status := .proven, prop := ``IntConversions, thm := some ``intConversions_proven },
  { id := "fractions-round-half-even", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__round__"]
    statement := "round(x) is the int nearest to x, and an even int when x is exactly halfway."
    source := "__round__ docs: \"returns the nearest int to self, rounding half to even\""
    status := .proven, prop := ``RoundHalfEven, thm := some ``roundHalfEven_proven },
  { id := "fractions-round-ndigits", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__round__"]
    statement := "For every int ndigits, round(x, ndigits) is the multiple of 10**-ndigits nearest to x (ties to even), as a normalized Fraction."
    source := "__round__ docs: \"rounds self to the nearest multiple of Fraction(1, 10**ndigits) ... again rounding half toward even\""
    status := .proven, prop := ``RoundNdigits, thm := some ``roundNdigits_proven },
  { id := "fractions-limit-denominator-closest", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.limit_denominator"]
    statement := "For max_denominator >= 1, limit_denominator returns a normalized Fraction with denominator <= max_denominator, and no fraction r/s with 1 <= s <= max_denominator is strictly closer to self; for max_denominator < 1 it raises ValueError."
    source := "limit_denominator docstring, fractions.py:387 (\"Closest Fraction to self with denominator at most max_denominator\")"
    status := .proven, prop := ``LimitDenominatorClosest, thm := some ``limitDenominatorClosest_proven
    notes := "Includes ties and max_denominator == 1; the proof is the Farey-neighbour argument (see Limit.lean)." },
  { id := "fractions-hash-int", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__hash__", "_hash_algorithm"]
    statement := "For every int n, hash(Fraction(n)) == hash(n)."
    source := "Built-in Types, Hashing of numeric types: hash(x) == hash(y) whenever x == y"
    status := .proven, prop := ``HashMatchesInt, thm := some ``hashMatchesInt_proven },
  { id := "fractions-hash-decimal", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__hash__", "_hash_algorithm"]
    statement := "For every finite Decimal d, hash(Fraction(d)) == hash(d)."
    source := "Built-in Types, Hashing of numeric types: hash(x) == hash(y) whenever x == y"
    status := .proven, prop := ``HashMatchesDecimal, thm := some ``hashMatchesDecimal_proven
    notes := "Decimal.__hash__ modelled from Lib/_pydecimal.py:988-1012; the proof needs only that 10 is invertible mod 2**61-1." },
  { id := "fractions-str-roundtrip", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__str__", "Fraction.__new__"]
    statement := "For every Fraction x whose str() succeeds, Fraction(str(x)) == x (same numerator and denominator)."
    source := "invariant (round trip between __str__ and the string constructor)"
    status := .proven, prop := ``StrRoundTrip, thm := some ``strRoundTrip_proven },
  { id := "fractions-format-empty-is-str", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__format__", "Fraction._format_general", "Fraction.__str__"]
    statement := "For every Fraction x, format(x, '') behaves exactly like str(x), including the exception raised."
    source := "format() convention (an empty spec gives str()); Fraction docs on formatting without a presentation type"
    status := .proven, prop := ``FormatEmptyIsStr, thm := some ``formatEmptyIsStr_proven },
  { id := "fractions-format-f-matches-round", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__format__", "Fraction._format_float_style", "_round_to_exponent",
              "Fraction.__round__", "Fraction.__new__"]
    statement := "For every Fraction x and 0 <= p <= 4300, whenever format(x, '.{p}f') returns s, Fraction(s) == round(x, p)."
    source := "Fraction.__format__ docs ('f' follows the float rules: fixed point, round half to even) and __round__ docs; self-consistency of three code paths"
    status := .proven, prop := ``FormatFRoundTrip, thm := some ``formatFRoundTrip_proven
    notes := "p <= 4300 because Fraction(s) itself applies int()'s 4300-digit limit to the p fractional digits. Covers p == 0 (no decimal point) and negative values that round to -0." },
  { id := "fractions-format-e-total", pyFile := "Lib/fractions.py"
    pyFns := ["Fraction.__format__", "Fraction._format_float_style", "_round_to_figures"]
    statement := "For every Fraction x and precision p, format(x, '.{p}e') returns a string."
    source := "Fraction.__format__ docs: with a presentation type, formatting \"follows the rules outlined for the float type\" (float formatting does not raise for a valid spec)"
    status := .refuted, prop := ``FormatETotal, thm := some ``formatETotal_refuted
    bug := some "fractions-format-e-int-max-str-digits"
    notes := "_round_to_figures computes the decimal magnitude with str(abs(n)) and str(d), which raise past 4300 digits even when the requested output is a few characters. Duplicate of python/cpython#158716 (closed as bulk-filing cleanup)." }
]

end PyLean.Fractions
