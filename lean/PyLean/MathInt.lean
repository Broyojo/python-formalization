import PyLean.Registry
import PyLean.MathInt.Diff
import PyLean.MathInt.Model
import PyLean.MathInt.IntOps
import PyLean.MathInt.Errors
import PyLean.MathInt.Divmod
import PyLean.MathInt.Round
import PyLean.MathInt.Pow
import PyLean.MathInt.Comb
import PyLean.MathInt.Factorial
import PyLean.MathInt.Isqrt
import PyLean.MathInt.Bytes
import PyLean.MathInt.Gcd
import PyLean.MathInt.Lehmer
import PyLean.MathInt.FltClassify
import PyLean.MathInt.FltFrexp
import PyLean.MathInt.FltFloor
import PyLean.MathInt.FltWrap
import PyLean.MathInt.FltLogProps

/-!
Integer functions of `math.integer` (`Modules/mathintegermodule.c`, re-exported by
`math`) and the related `int` operations of `Objects/longobject.c`, CPython 3.15.2.

The float functions of `Modules/mathmodule.c` are in `MathInt/Flt*.lean`: the model in
`FltBase` (argument objects with fallible `__float__`/`__index__`, `errno`, `math_1`,
`math_1a`, `math_2`), `FltFns`, `FltLog`, `FltGamma`, `FltSum`; properties in the other
`Flt*` files. The transcendental C library functions are parameters of every property.
Difftest: `difftest/mathint_float_diff.py`.

Model: `MathInt/Model.lean` (isqrt, comb/perm, factorial, gcd/lcm with
`_PyLong_GCD`) and `MathInt/IntOps.lean` (three-argument pow, to_bytes /
from_bytes at the 30-bit digit level, divmod with its fast path and the
`_pylong` twin, round). Difftest: `difftest/mathint_diff.py`.

No defect was found: every C fast path examined (the uint64 odd-part tables
and loops of `perm_comb_small`, the uint32 `_approximate_isqrt`, the
unsigned-long tight loop of `factorial_partial_product`, the byte/digit
packing of `_PyLong_AsByteArray` / `_PyLong_FromByteArray`) is proven exact
for all inputs, and so is Lehmer's step in `_PyLong_GCD` (`MathInt/Lehmer.lean`).
-/

namespace PyLean.MathInt

open PyLean.Registry

def entries : List Entry := [
  { id := "mathint-classify", pyFile := "Modules/mathmodule.c"
    pyFns := ["math.isfinite", "math.isnan", "math.isinf", "math.isnormal", "math.issubnormal",
      "math.signbit"]
    statement := "For every argument object, isfinite, isnan, isinf, isnormal, issubnormal and signbit raise the conversion error unchanged; otherwise, with x the converted float, isnan(x) is x != x, isinf(x) is x in (inf, -inf), isfinite(x) is neither, issubnormal(x) is finite, nonzero and abs(x) < 2**-1022, isnormal(x) is finite, nonzero and abs(x) >= 2**-1022, the C11 and C23 branches of issubnormal agree, and signbit(x) == (copysign(1.0, x) < 0)."
    source := "Doc/library/math.rst: isfinite, isnormal (\"a finite nonzero number that is not a subnormal\"), issubnormal (\"a finite nonzero number with a magnitude smaller than sys.float_info.min\"), isinf, isnan, signbit", status := .proven
    prop := ``MathClassify, thm := some ``mathClassify_proven },
  { id := "mathint-frexp-ldexp", pyFile := "Modules/mathmodule.c"
    pyFns := ["math.frexp", "math.ldexp"]
    statement := "For every argument object: a conversion error of x is raised by frexp and ldexp before i is examined; ldexp(x, i) for every int (or bool) i, however large, is x * 2**i rounded once (zeros, infinities and NaNs unchanged, OverflowError('math range error') when it rounds to infinity); any other i raises TypeError('Expected an int as second argument to ldexp.'); frexp(x) is (m, e) with 0.5 <= abs(m) < 1 and m * 2**e == x exactly for finite nonzero x, (x, 0) otherwise; and ldexp(*frexp(x)) is x bit for bit."
    source := "Doc/library/math.rst: frexp, ldexp (\"Return x * (2**i). This is essentially the inverse of function frexp()\")", status := .proven
    prop := ``FrexpLdexp, thm := some ``frexpLdexp_proven
    notes := "Includes the replacement of out-of-range exponents by LONG_MIN/LONG_MAX (mathmodule.c:1486-1490) and the INT_MAX/INT_MIN guards (:1502-1509). The C frexp and ldexp are the exact IEEE operations." },
  { id := "mathint-floor-ceil-trunc", pyFile := "Modules/mathmodule.c"
    pyFns := ["math.floor", "math.ceil", "math.trunc"]
    statement := "For an exact float, or a float subclass that does not override the method, floor, ceil and trunc return the exact floor, ceiling and truncation as an int (ValueError for NaN, OverflowError for an infinity), the C fast path agreeing with float.__floor__/__ceil__/__trunc__; an overriding subclass or any object with __floor__/__ceil__/__trunc__ gets that method's result or exception; ints and bools come back exactly; floor and ceil of an object without the method use its __float__/__index__ conversion and raise its errors, and trunc of such an object raises TypeError."
    source := "Doc/library/math.rst: ceil, floor, trunc (\"If x is not a float, delegates to x.__floor__\")", status := .proven
    prop := ``FloorCeilTrunc, thm := some ``floorCeilTrunc_proven },
  { id := "mathint-math1-rules", pyFile := "Modules/mathmodule.c"
    pyFns := ["math_1", "is_error"]
    statement := "For every C function f, can_overflow flag, error message and argument object, math_1 raises conversion errors unchanged and otherwise never returns a NaN for a non-NaN argument nor an infinity for a finite one: a NaN result from a non-NaN argument is ValueError, an infinite result from a finite argument is OverflowError('math range error') when can_overflow and ValueError otherwise, a finite result with errno EDOM is ValueError('math domain error'), with ERANGE is returned when below 1.5 in magnitude (an underflow) and OverflowError otherwise, and anything else is f's result."
    source := "mathmodule.c:757-785 (the comment above math_1) and :725-744 (is_error); Doc/library/math.rst: \"A NaN will not be returned from any of the functions above unless one or more of the input arguments was a NaN\"", status := .proven
    prop := ``Math1Rules, thm := some ``math1Rules_proven },
  { id := "mathint-math1a-rules", pyFile := "Modules/mathmodule.c"
    pyFns := ["math_1a", "is_error"]
    statement := "For every C function f that sets errno, error message and argument object, math_1a raises conversion errors unchanged and otherwise returns f's result when errno is 0, raises ValueError (with the formatted message when there is one) on EDOM, and on ERANGE returns the result when below 1.5 in magnitude and raises OverflowError('math range error') otherwise."
    source := "mathmodule.c:827-829 (\"to be used when the function being wrapped is known to set errno properly\") and :725-744 (is_error)", status := .proven
    prop := ``Math1aRules, thm := some ``math1aRules_proven },
  { id := "mathint-math2-rules", pyFile := "Modules/mathmodule.c"
    pyFns := ["math_2", "is_error"]
    statement := "For every two-argument C function f, math_2 raises TypeError for a wrong number of arguments, then the conversion error of the first argument, then of the second; otherwise a NaN result is ValueError('math domain error') unless an argument is a NaN (then returned), an infinite result is OverflowError('math range error') unless an argument is infinite (then returned), a finite result with EDOM is ValueError, with ERANGE is returned below 1.5 in magnitude and OverflowError otherwise, and f's result otherwise."
    source := "mathmodule.c:854-879 (the comment above math_2) and :725-744 (is_error)", status := .proven
    prop := ``Math2Rules, thm := some ``math2Rules_proven },
  { id := "mathint-log-twins", pyFile := "Modules/mathmodule.c"
    pyFns := ["m_log", "m_log2", "m_log10", "loghelper_int", "loghelper", "math.log", "math.log2",
      "math.log10"]
    statement := "For every C logarithm that returns a finite value without errno on positive finite arguments, math.log (one argument), math.log2 and math.log10: agree on an int and its float conversion; never raise for a positive int however large; treat an object with __index__ (and no __float__) as the int it returns, including beyond the float range, and raise what __index__ raises; raise ValueError('expected a positive input') for ints <= 0 and ValueError for floats <= 0 (zeros and -inf included); return NaN for NaN and inf for inf; and return the C function's value for positive finite floats. math.log(x, base) is log(x) / log(base) as Python divides floats (ZeroDivisionError for base 1)."
    source := "Doc/library/math.rst: log (\"calculated as log(x)/log(base)\"), log2, log10; mathmodule.c:1573-1580 (logs of ints beyond the float range); C99 Annex F special values", status := .proven
    prop := ``LogTwins, thm := some ``logTwins_proven
    notes := "Scope: __index__ is modelled as returning the same int each time it is called (loghelper calls it twice when the float conversion overflows)." },
  { id := "mathint-log2-powers-of-two", pyFile := "Modules/mathmodule.c"
    pyFns := ["m_log2", "loghelper_int", "loghelper", "math.log2"]
    statement := "For a C log2 that is exact on the powers of two a double holds, math.log2(2**k) == k exactly for every k with k + 1 < 2**53, for an int and for an object whose __index__ returns 2**k; past 2**1023 this is the fma(log2(2.0), e, log2(0.5)) path of loghelper_int."
    source := "mathmodule.c:650-658 (log2 \"should produce exact results for powers of 2\")", status := .proven
    prop := ``Log2PowersOfTwo, thm := some ``log2PowersOfTwo_proven
    notes := "The bound k + 1 < 2**53 is where (double)e in loghelper_int stops being exact; an int that large needs a petabyte of memory." },
  { id := "mathint-isqrt-floor-sqrt", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.isqrt", "_approximate_isqrt"]
    statement := "For every n >= 0, isqrt(n) returns r with r*r <= n < (r+1)*(r+1)."
    source := "math.isqrt docs: \"the greatest integer a such that a**2 <= n\"", status := .proven
    prop := ``IsqrtFloorSqrt, thm := some ``isqrtFloorSqrt_proven
    notes := "Covers the n < 2**64 fast path (192-entry table checked by the kernel, no uint32_t wraparound, including the top range where the clamped entry 255 matters) and the slow path. c is modelled as an unbounded Nat (C int64 cannot overflow for any representable n)." },
  { id := "mathint-comb-formula", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.comb", "perm_comb_small", "perm_comb"]
    statement := "For 0 <= k <= n, comb(n, k) == n! // (k! * (n-k)!) exactly, unless min(k, n-k) > LLONG_MAX, where it raises OverflowError."
    source := "comb docstring: \"Evaluates to n! / (k! * (n - k)!) when k <= n\"", status := .proven
    prop := ``CombFormula, thm := some ``combFormula_proven
    notes := "Covers both uint64 fast paths (odd-part tables checked by the kernel, the C(n,k)*k loop bounded by fast_comb_limits2) and both recursions." },
  { id := "mathint-perm-formula", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.perm", "perm_comb_small", "perm_comb"]
    statement := "For 0 <= k <= n, perm(n, k) == n! // (n-k)! exactly, unless k > LLONG_MAX, where it raises OverflowError."
    source := "perm docstring: \"Evaluates to n! / (n - k)! when k <= n\"", status := .proven
    prop := ``PermFormula, thm := some ``permFormula_proven },
  { id := "mathint-factorial-exact", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.factorial", "math.integer.perm", "factorial_odd_part", "factorial_partial_product", "count_set_bits"]
    statement := "For 0 <= n <= LONG_MAX, factorial(n) and perm(n) equal n!."
    source := "math.factorial docs; perm docstring (k=None returns n!)", status := .proven
    prop := ``FactorialExact, thm := some ``factorialExact_proven
    notes := "Includes the unsigned long tight loop of factorial_partial_product (no wraparound under its num_operands * max_bits <= 64 guard)." },
  { id := "mathint-isqrt-negative", pyFile := "Modules/mathintegermodule.c", pyFns := ["math.integer.isqrt"]
    statement := "isqrt(n) raises ValueError for every n < 0."
    source := "math.isqrt docs; mathintegermodule.c:367-372", status := .proven
    prop := ``IsqrtRejectsNegative, thm := some ``isqrtRejectsNegative_proven },
  { id := "mathint-comb-perm-negative", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.comb", "math.integer.perm"]
    statement := "comb(n, k) and perm(n, k) raise ValueError whenever n < 0 or k < 0."
    source := "comb/perm docstrings: \"Raises ValueError if either of the arguments are negative.\""
    status := .proven
    prop := ``CombPermRejectNegative, thm := some ``combPermRejectNegative_proven },
  { id := "mathint-comb-perm-zero-above", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.comb", "math.integer.perm"]
    statement := "For 0 <= n < k (any size), comb(n, k) == 0 and perm(n, k) == 0."
    source := "comb/perm docstrings: \"evaluates to zero when k > n\"", status := .proven
    prop := ``CombPermZeroAbove, thm := some ``combPermZeroAbove_proven },
  { id := "mathint-factorial-arg-errors", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.factorial"]
    statement := "factorial(n) raises ValueError for n < 0 and OverflowError for n > LONG_MAX."
    source := "math.factorial docs; mathintegermodule.c:698-712", status := .proven
    prop := ``FactorialArgErrors, thm := some ``factorialArgErrors_proven },
  { id := "mathint-to-bytes-exact", pyFile := "Objects/longobject.c"
    pyFns := ["int.to_bytes", "_PyLong_AsByteArray"]
    statement := "For 0 <= n <= PY_SSIZE_T_MAX - 33 (the largest bytes object) and a valid byteorder, v.to_bytes(n, byteorder, signed=s) returns n bytes holding v mod 256**n when v fits (0 <= v < 256**n, or -256**n/2 <= v < 256**n/2 if signed) and raises OverflowError otherwise."
    source := "int.to_bytes docs: \"An OverflowError is raised if the integer is not representable with the given number of bytes\"", status := .proven
    prop := ``ToBytesExact, thm := some ``toBytesExact_proven
    notes := "Models the 30-bit digit loop, the two's-complement carry, the bit counting of the top digit, the straggler byte and the sign-bit check of _PyLong_AsByteArray." },
  { id := "mathint-from-bytes-value", pyFile := "Objects/longobject.c"
    pyFns := ["int.from_bytes", "_PyLong_FromByteArray"]
    statement := "int.from_bytes(bs, byteorder, signed=s) is the unsigned value of bs in that byte order, minus 256**len(bs) when s and the top bit is set."
    source := "int.from_bytes docs", status := .proven
    prop := ``FromBytesValue, thm := some ``fromBytesValue_proven
    notes := "Includes the insignificant-leading-byte trimming and its +1 bump for negative values." },
  { id := "mathint-bytes-roundtrip", pyFile := "Objects/longobject.c"
    pyFns := ["int.to_bytes", "int.from_bytes"]
    statement := "If v fits in n bytes, int.from_bytes(v.to_bytes(n, order, signed=s), order, signed=s) == v."
    source := "invariant: round trip", status := .proven
    prop := ``BytesRoundTrip, thm := some ``bytesRoundTrip_proven },
  { id := "mathint-bytes-arg-errors", pyFile := "Objects/longobject.c"
    pyFns := ["int.to_bytes", "int.from_bytes"]
    statement := "A negative length raises ValueError('length cannot be negative') whatever the byteorder; otherwise a byteorder other than 'little'/'big' raises ValueError in to_bytes and from_bytes; a length outside Py_ssize_t raises OverflowError, and so does a length above PY_SSIZE_T_MAX - 33 ('byte string is too large')."
    source := "int.to_bytes / int.from_bytes docs; clinic/longobject.c.h:332-349; longobject.c:6399-6410", status := .proven
    prop := ``BytesArgErrors, thm := some ``bytesArgErrors_proven },
  { id := "mathint-from-bytes-dispatch", pyFile := "Objects/longobject.c"
    pyFns := ["int.from_bytes"]
    statement := "The exact-bytes, buffer and PyObject_Bytes routes of int.from_bytes give the same int for the same bytes, a subclass constructor receives that int, a failing conversion propagates, and a bad byteorder raises before the object is touched."
    source := "int.from_bytes docs: \"a bytes-like object or an iterable producing bytes\"", status := .proven
    prop := ``FromBytesDispatch, thm := some ``fromBytesDispatch_proven
    notes := "The conversions themselves (PyObject_GetBuffer, PyObject_Bytes) are inputs here: the payload is what they yield. Difftest case from_bytes_obj builds real objects for each route." },
  { id := "mathint-gcd-small", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.gcd", "_PyLong_GCD"]
    statement := "If every argument has abs < 2**60, gcd(*args) is the nonnegative greatest common divisor of the arguments (gcd() == 0), including the 2-argument fast path and the res == 1 short cut."
    source := "math.gcd docs", status := .proven
    prop := ``GcdSmall, thm := some ``gcdSmall_proven
    notes := "Scope: the inputs on which _PyLong_GCD takes its simple: path (Euclid on C longs). Subsumed by mathint-gcd-general." },
  { id := "mathint-lcm-small", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.lcm", "long_lcm"]
    statement := "lcm() == 1, lcm(a) == abs(a), and for abs(a), abs(b) < 2**60, lcm(a, b) is the nonnegative least common multiple (0 if either is 0)."
    source := "math.lcm docs", status := .proven
    prop := ``LcmSmall, thm := some ``lcmSmall_proven
    notes := "Scope as for mathint-gcd-small; subsumed by mathint-lcm-general." },
  { id := "mathint-gcd-general", pyFile := "Objects/longobject.c"
    pyFns := ["math.integer.gcd", "_PyLong_GCD"]
    statement := "For all int arguments, gcd(*args) is the nonnegative greatest common divisor (gcd() == 0)."
    source := "math.gcd docs", status := .proven
    prop := ``GcdGeneral, thm := some ``gcdGeneral_proven
    notes := "Includes Lehmer's step of _PyLong_GCD (longobject.c:5782-5907): the cofactors accepted by the test B + q*D <= x - q*y are the true Euclidean cofactors of (a, b), so the digit loop yields two consecutive nonnegative remainders below 2**(30*size_a) (no wraparound), b strictly decreases, and no int64_t intermediate of the inner loop exceeds 2**62 in absolute value." },
  { id := "mathint-lcm-general", pyFile := "Modules/mathintegermodule.c"
    pyFns := ["math.integer.lcm", "long_lcm"]
    statement := "For all int arguments, lcm(*args) is the nonnegative least common multiple (lcm() == 1, 0 if any argument is 0)."
    source := "math.lcm docs", status := .proven
    prop := ``LcmGeneral, thm := some ``lcmGeneral_proven },
  { id := "mathint-divmod-floor", pyFile := "Objects/longobject.c"
    pyFns := ["divmod", "l_divmod", "fast_floor_div", "fast_mod", "_pylong.int_divmod"]
    statement := "For w != 0, divmod(v, w) returns (q, r) with q*w + r == v, r of the sign of w and abs(r) < abs(w), on the single-digit fast path, the _pylong path and the long_divrem path; w == 0 raises ZeroDivisionError."
    source := "language reference, binary arithmetic operations", status := .proven
    prop := ``DivmodFloor, thm := some ``divmod_floor_proven
    notes := "long_divrem and _pylong._divmod_pos are taken as exact truncated / Nat division." },
  { id := "mathint-round-half-even", pyFile := "Objects/longobject.c"
    pyFns := ["int.__round__", "_PyLong_DivmodNear"]
    statement := "round(x, d) for d < 0 is the multiple of 10**-d nearest to x, ties to the even multiple; for d >= 0 or None it is x."
    source := "built-in round() docs", status := .proven
    prop := ``RoundIntHalfEven, thm := some ``roundIntHalfEven_proven },
  { id := "mathint-pow-neg-exp-inverse", pyFile := "Objects/longobject.c"
    pyFns := ["pow", "long_pow", "long_invmod"]
    statement := "For k > 0: pow(a, -k, m) raises ValueError for m == 0; is 0 for abs(m) == 1; for abs(m) > 1 returns r with r*a**k == 1 (mod m) in the range of % m when gcd(a, m) == 1, and raises ValueError otherwise."
    source := "built-in pow() docs", status := .proven
    prop := ``PowNegExpInverse, thm := some ``powNegExpInverse_proven
    notes := "The windowed exponentiation loop of long_pow is taken as a**e % c." }
]

end PyLean.MathInt
