import PyLean.Registry
import PyLean.MathInt.Diff
import PyLean.MathInt.Model
import PyLean.MathInt.IntOps
import PyLean.MathInt.Errors
import PyLean.MathInt.Divmod
import PyLean.MathInt.Round
import PyLean.MathInt.Pow

/-!
Integer functions of `math` (`Modules/mathmodule.c`) and the related `int`
operations of `Objects/longobject.c`, CPython 3.14.7.
-/

namespace PyLean.MathInt

open PyLean.Registry

def entries : List Entry := [
  { id := "mathint-isqrt-negative", pyFile := "Modules/mathmodule.c", pyFns := ["math.isqrt"]
    statement := "isqrt(n) raises ValueError for every n < 0."
    source := "math.isqrt docs; mathmodule.c:1707-1712", status := .proven
    prop := ``IsqrtRejectsNegative, thm := some ``isqrtRejectsNegative_proven },
  { id := "mathint-comb-perm-negative", pyFile := "Modules/mathmodule.c"
    pyFns := ["math.comb", "math.perm"]
    statement := "comb(n, k) and perm(n, k) raise ValueError whenever n < 0 or k < 0."
    source := "comb/perm docstrings: \"Raises ValueError if either of the arguments are negative.\""
    status := .proven
    prop := ``CombPermRejectNegative, thm := some ``combPermRejectNegative_proven },
  { id := "mathint-comb-perm-zero-above", pyFile := "Modules/mathmodule.c"
    pyFns := ["math.comb", "math.perm"]
    statement := "For 0 <= n < k (any size), comb(n, k) == 0 and perm(n, k) == 0."
    source := "comb/perm docstrings: \"evaluates to zero when k > n\"", status := .proven
    prop := ``CombPermZeroAbove, thm := some ``combPermZeroAbove_proven },
  { id := "mathint-factorial-arg-errors", pyFile := "Modules/mathmodule.c"
    pyFns := ["math.factorial"]
    statement := "factorial(n) raises ValueError for n < 0 and OverflowError for n > LONG_MAX."
    source := "math.factorial docs; mathmodule.c:2025-2039", status := .proven
    prop := ``FactorialArgErrors, thm := some ``factorialArgErrors_proven },
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
