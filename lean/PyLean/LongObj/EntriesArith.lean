import PyLean.Registry
import PyLean.LongObj.Props

/-! Registry entries for the arithmetic kernels of `Objects/longobject.c`. -/

namespace PyLean.LongObj

open PyLean.Registry

def entriesArith : List Entry := [
  { id := "longobj-normalize", pyFile := "Objects/longobject.c", pyFns := ["long_normalize"]
    statement := "long_normalize keeps the value, leaves a non-zero top digit and never lengthens the vector."
    source := "invariant: comment at longobject.c:121-123", status := .proven
    prop := ``NormalizeSpec, thm := some ``normalizeSpec_proven },
  { id := "longobj-from-stwodigits", pyFile := "Objects/longobject.c"
    pyFns := ["_PyLong_FromSTwoDigits", "_PyLong_FromMedium", "_PyLong_FromLarge", "is_medium_int"]
    statement := "For every int64_t x, _PyLong_FromSTwoDigits(x) builds the canonical object of x; is_medium_int is |x| <= MASK despite its unsigned wraparound."
    source := "invariant", status := .proven
    prop := ``FromSTwoDigitsCanonical, thm := some ``fromSTwoDigitsCanonical_proven },
  { id := "longobj-x-add", pyFile := "Objects/longobject.c", pyFns := ["x_add"]
    statement := "x_add is exact on all digit vectors, normalized, and its digit carry never wraps."
    source := "comment at longobject.c:3746", status := .proven
    prop := ``XAddExact, thm := some ``xAddExact_proven },
  { id := "longobj-x-sub", pyFile := "Objects/longobject.c", pyFns := ["x_sub"]
    statement := "On normalized magnitudes x_sub returns the canonical object of val(a) - val(b), through the wrapping uint32_t borrow."
    source := "comment at longobject.c:3780", status := .proven
    prop := ``XSubExact, thm := some ``xSubExact_proven },
  { id := "longobj-add-sub", pyFile := "Objects/longobject.c"
    pyFns := ["long_add", "long_sub"]
    statement := "a + b and a - b return the canonical object for all ints with room for one more digit, on the compact path and the digit path."
    source := "invariant: exact integer arithmetic", status := .proven
    prop := ``LongAddSubExact, thm := some ``longAddSubExact_proven
    notes := "The slot wrappers are in longobj-binary-methods." },
  { id := "longobj-compact-ops", pyFile := "Objects/longobject.c"
    pyFns := ["_PyCompactLong_Add", "_PyCompactLong_Subtract", "_PyCompactLong_Multiply", "medium_from_stwodigits"]
    statement := "On compact ints the functions behind BINARY_OP_ADD_INT, BINARY_OP_SUBTRACT_INT and BINARY_OP_MULTIPLY_INT give the canonical object of the exact result when it is medium, and otherwise decline with no exception."
    source := "comment at longobject.c:4359-4360; invariant: exact integer arithmetic", status := .proven
    prop := ``CompactOpsExact, thm := some ``compactOpsExact_proven
    notes := "These replace _PyLong_Add, _PyLong_Subtract and _PyLong_Multiply of 3.14. The difftest reaches them through a specialized BINARY_OP, checked with dis." },
  { id := "longobj-vector-add-sub", pyFile := "Objects/longobject.c", pyFns := ["v_iadd", "v_isub"]
    statement := "v_iadd and v_isub are exact modulo the width of x, returning a carry or borrow of 0 or 1."
    source := "comments at longobject.c:1849-1852, :1875-1878", status := .proven
    prop := ``VectorAddSub, thm := some ``vectorAddSub_proven },
  { id := "longobj-k-mul", pyFile := "Objects/longobject.c"
    pyFns := ["k_mul", "k_lopsided_mul", "kmul_split"]
    statement := "k_mul is exact on all digit vectors, including the non-normalized slices of k_lopsided_mul, and every memcpy and v_iadd stays inside ret."
    source := "comment at longobject.c:4068-4071 and the (*) comment at :4233-4276", status := .proven
    prop := ``KMulExact, thm := some ``kMulExact_proven },
  { id := "longobj-mul", pyFile := "Objects/longobject.c"
    pyFns := ["long_mul"]
    statement := "a * b returns the canonical object on the compact path and through k_mul, for x * y and for x * x on one object."
    source := "invariant: exact integer arithmetic", status := .proven
    prop := ``LongMulExact, thm := some ``longMulExact_proven },
  { id := "longobj-vector-shifts", pyFile := "Objects/longobject.c", pyFns := ["v_lshift", "v_rshift"]
    statement := "v_lshift and v_rshift by d < PyLong_SHIFT are exact and return the bits shifted out."
    source := "comments at longobject.c:1901-1903, :1919-1921", status := .proven
    prop := ``VectorShifts, thm := some ``vectorShifts_proven },
  { id := "longobj-divrem-one-digit", pyFile := "Objects/longobject.c"
    pyFns := ["inplace_divrem1", "divrem1", "inplace_rem1"]
    statement := "Division of a digit vector by a non-zero digit gives the exact quotient and remainder; inplace_rem1 agrees with inplace_divrem1."
    source := "comments at longobject.c:1938-1942, :1995-1996", status := .proven
    prop := ``DivremOneDigit, thm := some ``divremOneDigit_proven },
  { id := "longobj-knuth-digit", pyFile := "Objects/longobject.c", pyFns := []
    statement := "One digit of Algorithm D: with wm1 >= BASE/2 and V < BASE*W the estimate, its corrections and the add-back give the true digit and remainder, with q <= BASE after the loop and no overflow."
    source := "comment at longobject.c:3334-3338 and the asserts at :3314, :3332, :3347, :3359", status := .proven
    prop := ``KnuthDigit, thm := some ``knuthDigit_proven },
  { id := "longobj-divrem", pyFile := "Objects/longobject.c"
    pyFns := ["long_divrem", "long_rem", "rem1"]
    statement := "long_divrem and long_rem give the canonical truncated quotient and remainder, and raise ZeroDivisionError for b == 0."
    source := "comment at longobject.c:4460-4473", status := .proven
    prop := ``LongDivremExact, thm := some ``longDivremExact_proven
    notes := "The |a| < |b| test is only sufficient: equal top digits fall through to the general path, which handles them." },
  { id := "longobj-l-divmod-refines", pyFile := "Objects/longobject.c"
    pyFns := ["l_divmod", "pylong_int_divmod", "fast_mod", "fast_floor_div"]
    statement := "The digit-level l_divmod returns the canonical objects of MathInt.divmod, discharging mathint-divmod-floor's assumption that long_divrem is exact."
    source := "invariant", status := .proven
    prop := ``LDivmodRefines, thm := some ``lDivmodRefines_proven
    notes := "The _pylong branch is pylong_int_divmod (pylongIntDivmodC) with the real _pylong.int_divmod, MathInt.pylongIntDivmod; its failure paths are longobj-pylong-divmod-paths." },
  { id := "longobj-division-floor", pyFile := "Objects/longobject.c"
    pyFns := ["l_mod"]
    statement := "divmod, // and % satisfy q*w + r == v with r taking the sign of w and abs(r) < abs(w), on the digit model."
    source := "language reference, binary arithmetic operations", status := .proven
    prop := ``DivisionFloor, thm := some ``divisionFloor_proven },
  { id := "longobj-rshift", pyFile := "Objects/longobject.c"
    pyFns := ["long_rshift1", "_PyLong_Rshift"]
    statement := "a >> b is the floor of a / 2**b for all b >= 0, including b >= 2**63, and raises ValueError for b < 0."
    source := "stdtypes: bitwise operations on integer types", status := .proven
    prop := ``RshiftExact, thm := some ``rshiftExact_proven },
  { id := "longobj-lshift", pyFile := "Objects/longobject.c"
    pyFns := ["long_lshift1", "long_lshift_int64", "_PyLong_Lshift"]
    statement := "a << b raises ValueError for b < 0, is 0 for a == 0, raises OverflowError for a != 0 when b does not fit int64_t; below 2**63 it is a * 2**b exactly when long_alloc accepts oldsize + b // 30 (+1 if b % 30), and OverflowError('too many digits in integer') otherwise; long_lshift_int64 and _PyLong_Lshift likewise for every count."
    source := "stdtypes: bitwise operations on integer types", status := .proven
    prop := ``LshiftExact, thm := some ``lshiftExact_proven
    notes := "Smoke-tested on 3.15.2: 1 << (2**63 - 1), 1 << (30 * MAX_LONG_DIGITS - 1) and 2**31 << (30 * (MAX_LONG_DIGITS - 1)) raise OverflowError; 1 << (30 * (MAX_LONG_DIGITS - 1)), where long_alloc accepts the size, raises MemoryError, which is outside the model." },
  { id := "longobj-v-complement", pyFile := "Objects/longobject.c", pyFns := ["v_complement"]
    statement := "On a non-zero vector, v_complement computes 2**(30*m) - val(a) with no carry out."
    source := "comment at longobject.c:5553-5555", status := .proven
    prop := ``VComplementExact, thm := some ``vComplementExact_proven },
  { id := "longobj-bitwise", pyFile := "Objects/longobject.c"
    pyFns := ["long_bitwise"]
    statement := "&, | and ^ act bit by bit on the infinite two's complement expansions for all ints, on the compact path and on long_bitwise, and the result is canonical."
    source := "stdtypes: bitwise operations on integer types", status := .proven
    prop := ``BitwiseBits, thm := some ``bitwiseBits_proven },
  { id := "longobj-unary", pyFile := "Objects/longobject.c"
    pyFns := ["long_invert", "long_neg", "long_neg_method", "long_abs", "long_abs_method", "long_bool"]
    statement := "~a == -a - 1, -a, abs(a) and bool(a) return the canonical results for all ints."
    source := "stdtypes: numeric types", status := .proven
    prop := ``UnaryExact, thm := some ``unaryExact_proven },
  { id := "longobj-pow", pyFile := "Objects/longobject.c", pyFns := []
    statement := "a ** e for e >= 0 is the exact power on the small-exponent, binary and sliding-window paths."
    source := "built-in pow() docs", status := .proven
    prop := ``PowExact, thm := some ``powExact_proven
    notes := "MULT is modelled on values because long_mul and l_mod are proven exact. A negative exponent with no modulus leaves for float_pow and is outside this entry." },
  { id := "longobj-pow-mod-refines", pyFile := "Objects/longobject.c", pyFns := []
    statement := "For all v, w, x the mirrored exponentiation loops give the result of MathInt.powMod, discharging mathint-pow-neg-exp-inverse's assumption that they compute a**e % c."
    source := "invariant", status := .proven
    prop := ``PowModRefines, thm := some ``powModRefines_proven },
  { id := "longobj-pow-mod-floor", pyFile := "Objects/longobject.c", pyFns := []
    statement := "pow(v, w, x) for w >= 0 and x != 0 is the Python remainder of v**w by x, with the sign of x."
    source := "built-in pow() docs", status := .proven
    prop := ``PowModFloor, thm := some ``powModFloor_proven }
]

end PyLean.LongObj
