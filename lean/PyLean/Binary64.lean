import PyLean.Registry
import PyLean.Binary64.Model
import PyLean.Binary64.Round
import PyLean.Binary64.Lemmas
import PyLean.Binary64.Bigint
import PyLean.Binary64.BigintProps
import PyLean.Binary64.BigintProps2
import PyLean.Binary64.Float
import PyLean.Binary64.Strtod
import PyLean.Binary64.Dtoa
import PyLean.Binary64.Props
import PyLean.Binary64.Props2
import PyLean.Binary64.Props3
import PyLean.Binary64.Props4
import PyLean.Binary64.Pack2Check
import PyLean.Binary64.CompareProps
import PyLean.Binary64.StrtodProps
import PyLean.Binary64.DtoaProps
import PyLean.Binary64.RatioProps
import PyLean.Binary64.OpenProps
import PyLean.Binary64.Complex
import PyLean.Binary64.ComplexProps
import PyLean.Binary64.Diff

/-!
Shared exact IEEE-754 binary64 model, and `Objects/floatobject.c`, `Python/dtoa.c`,
`Python/pystrtod.c`, CPython 3.14.7.

Other modules import `PyLean.Binary64.Model` for the type `F64` and its operations, and
`PyLean.Binary64.Lemmas` for the theorems about them.
-/

namespace PyLean.Binary64

open PyLean.Registry

def floatFile : String := "Objects/floatobject.c"
def strtodFile : String := "Python/pystrtod.c"
def dtoaFile : String := "Python/dtoa.c"
def complexFile : String := "Objects/complexobject.c"

def entries : List Entry := [
  { id := "binary64-round-nearest-even", pyFile := floatFile
    pyFns := []
    statement := "For every rational q, F64.ofRat q is not a NaN, is as close to q as every finite float, has an even mantissa on a tie, and is an infinity exactly when |q| is at least DBL_MAX + 2^970."
    source := "IEEE 754-2019 section 4.3.1 (roundTiesToEven); sys.float_info.rounds == 1"
    status := .proven, prop := ``RoundToNearestEven, thm := some ``roundToNearestEven_proven
    notes := "Foundation." },
  { id := "binary64-bits-value-roundtrip", pyFile := floatFile
    pyFns := []
    statement := "Every F64 is its bit pattern, and every nonzero finite F64 is the rounding of its exact value."
    source := "invariant"
    status := .proven, prop := ``BitsAndValueRoundTrip, thm := some ``bitsAndValueRoundTrip_proven
    notes := "Foundation." },
  { id := "binary64-fma-correct", pyFile := floatFile, pyFns := []
    statement := "For finite x, y, z, F64.fma x y z is x * y + z with a single rounding."
    source := "IEEE 754-2019 section 5.4.1 (fusedMultiplyAdd); math.fma docs"
    status := .proven, prop := ``FmaCorrect, thm := some ``fmaCorrect_proven
    notes := "Foundation, for math.fma." },
  { id := "float-add-correct", pyFile := floatFile, pyFns := ["float_add"]
    statement := "For finite floats x and y, x + y is the exact sum rounded to nearest even, and an exact zero is -0.0 only when both operands are negative."
    source := "IEEE 754 addition; floatobject.c:551-559 performs C double addition"
    status := .proven, prop := ``FloatAddCorrect, thm := some ``floatAddCorrect_proven },
  { id := "float-sub-correct", pyFile := floatFile, pyFns := ["float_sub"]
    statement := "For finite floats x and y, x - y is the exact difference rounded to nearest even."
    source := "IEEE 754 subtraction; floatobject.c:561-569"
    status := .proven, prop := ``FloatSubCorrect, thm := some ``floatSubCorrect_proven },
  { id := "float-mul-correct", pyFile := floatFile, pyFns := ["float_mul"]
    statement := "For finite floats x and y, x * y is the exact product rounded to nearest even, and a zero product carries the exclusive or of the signs."
    source := "IEEE 754 multiplication; floatobject.c:571-579"
    status := .proven, prop := ``FloatMulCorrect, thm := some ``floatMulCorrect_proven },
  { id := "float-div-correct", pyFile := floatFile, pyFns := ["float_div"]
    statement := "x / y raises ZeroDivisionError for a zero y, whatever x is, and for finite x and nonzero finite y it is the exact quotient rounded to nearest even."
    source := "floatobject.c:587-592; IEEE 754 division"
    status := .proven, prop := ``FloatDivCorrect, thm := some ``floatDivCorrect_proven },
  { id := "float-int-operand-correct", pyFile := floatFile
    pyFns := ["_Py_convert_int_to_double"]
    statement := "An int operand converts to its exact value rounded to nearest even, and OverflowError is raised exactly for the ints at or past DBL_MAX + 2^970."
    source := "PyLong_AsDouble documentation; float(int) docs (OverflowError)"
    status := .proven, prop := ``IntToFloatCorrect, thm := some ``intToFloatCorrect_proven },
  { id := "float-int-conversions", pyFile := floatFile
    pyFns := ["float___trunc___impl", "float___floor___impl", "float___ceil___impl"]
    statement := "math.floor and math.ceil of a finite float are its exact floor and ceiling, int(x) truncates toward zero, a NaN raises ValueError and an infinity raises OverflowError."
    source := "float.__trunc__, __floor__, __ceil__ docstrings (floatobject.c:868, :881, :895)"
    status := .proven, prop := ``FloatIntConversions, thm := some ``floatIntConversions_proven },
  { id := "float-is-integer", pyFile := floatFile, pyFns := ["float_is_integer_impl"]
    statement := "x.is_integer() is true exactly when x is finite with an integer value."
    source := "float.is_integer docstring, floatobject.c:841"
    status := .proven, prop := ``FloatIsInteger, thm := some ``floatIsInteger_proven },
  { id := "float-divmod-twins", pyFile := floatFile
    pyFns := ["float_rem", "_float_div_mod", "float_divmod", "float_floor_div"]
    statement := "For every x and nonzero y, x % y equals divmod(x, y)[1], and x // y equals divmod(x, y)[0], including NaN and infinite operands."
    source := "The two copies of the remainder logic at floatobject.c:603-621 and :628-648 must agree; divmod docs"
    status := .proven, prop := ``DivmodTwins, thm := some ``divmodTwins_proven },
  { id := "float-divmod-zero", pyFile := floatFile
    pyFns := ["float_rem", "float_divmod", "float_floor_div"]
    statement := "%, // and divmod raise ZeroDivisionError for a zero divisor, whatever the dividend."
    source := "floatobject.c:603, :669, :684"
    status := .proven, prop := ``DivmodZero, thm := some ``divmodZero_proven },
  { id := "float-floordiv-exact-floor", pyFile := floatFile
    pyFns := ["_float_div_mod", "float_floor_div"]
    statement := "For finite x and nonzero finite y, if the exact floor of x / y fits in 53 bits, then x // y equals that floor."
    source := "Docs: x // y is the floored quotient. Every such floor is a float, so the result could be exact."
    status := .refuted, prop := ``FloorDivExactFloor, thm := some ``floorDivExactFloor_refuted
    bug := some "binary64-floordiv-not-exact-floor"
    notes := "574432016605032.2 // 0.24012708848409187 is 2392199981398964.0; the floor is 2392199981398965, below 2**52." },
  { id := "float-divmod-quotient-doc", pyFile := floatFile
    pyFns := ["_float_div_mod", "float_divmod"]
    statement := "For finite x and nonzero finite y with finite x / y, divmod(x, y)[0] is math.floor(x / y) or one less."
    source := "Doc/library/functions.rst, divmod: q is usually math.floor(a / b) but may be 1 less than that"
    status := .refuted, prop := ``DivmodQuotientDoc, thm := some ``divmodQuotientDoc_refuted
    bug := some "binary64-floordiv-not-exact-floor"
    notes := "The quotient can be one more than the floor, and for quotients above 2**52 two less." },
  { id := "float-pow-special-values", pyFile := floatFile, pyFns := ["float_pow"]
    statement := "For any C library pow: x ** 0 and 1 ** y are 1.0, even for NaNs; nan ** y is nan for y != 0; 0.0 ** y raises ZeroDivisionError for finite y < 0; a negative base with a finite non-integer exponent goes to complex; two positive finite operands call pow, and an infinite result raises OverflowError."
    source := "Comments at floatobject.c:711-797; C99 Annex F"
    status := .proven, prop := ``PowSpecialValues, thm := some ``powSpecialValues_proven },
  { id := "float-hash-basics", pyFile := floatFile, pyFns := ["float_hash"]
    statement := "hash(x) is never -1, infinities hash to +-314159, a NaN hashes by identity, and floats that compare equal hash equal."
    source := "tp_hash contract; Doc/library/stdtypes.rst, hashing of numeric types"
    status := .proven, prop := ``FloatHashBasics, thm := some ``floatHashBasics_proven
    notes := "The hash of a finite float against the exact rational rule is the separate open entry." },
  { id := "float-unary", pyFile := floatFile, pyFns := ["float_neg", "float_abs", "float_bool"]
    statement := "-x flips only the sign bit, abs(x) clears it, and bool(x) is false exactly for the two zeros."
    source := "IEEE 754 sign-bit operations; float_bool, floatobject.c:835"
    status := .proven, prop := ``FloatUnary, thm := some ``floatUnary_proven },
  { id := "float-identities", pyFile := floatFile
    pyFns := ["float_float", "float_conjugate_impl", "float_getreal", "float_getimag",
      "float___getnewargs___impl", "float_from_number_impl", "float_new_impl",
      "float_subtype_new", "float_vectorcall"]
    statement := "conjugate, real, __float__, __getnewargs__, from_number, float(x) and its subclass path keep a float's value, imag is 0.0, and float() is 0.0."
    source := "docstrings; floatobject.c:1078-1100, :1574-1593, :1740-1750"
    status := .proven, prop := ``FloatIdentities, thm := some ``floatIdentities_proven },
  { id := "float-getformat", pyFile := floatFile, pyFns := ["float___getformat___impl"]
    statement := "float.__getformat__ answers for 'double' and 'float' and raises ValueError for any other string."
    source := "float.__getformat__ docstring, floatobject.c:1693-1703"
    status := .proven, prop := ``GetFormat, thm := some ``getFormat_proven },
  { id := "float-info", pyFile := floatFile
    pyFns := ["PyFloat_GetMax", "PyFloat_GetMin", "PyFloat_GetInfo"]
    statement := "sys.float_info.max bounds every finite float, min is 2**-1022 and the smallest normal, epsilon is the gap above 1.0, and the digit and exponent fields have their IEEE values."
    source := "floatinfo_fields, floatobject.c:52-72"
    status := .proven, prop := ``FloatInfoCorrect, thm := some ``floatInfoCorrect_proven },
  { id := "float-hex-sign", pyFile := floatFile, pyFns := ["float_hex_impl", "char_from_hex"]
    statement := "(-x).hex() is '-' + x.hex() for every positive finite x."
    source := "float.hex docstring, floatobject.c:1155-1160"
    status := .proven, prop := ``FloatHexSign, thm := some ``floatHexSign_proven },
  { id := "float-fromhex-trailing-garbage", pyFile := floatFile
    pyFns := ["float_fromhex_impl", "hex_from_char"]
    statement := "float.fromhex raises ValueError for every string that ends in 'x', since no valid hexadecimal float does."
    source := "float.fromhex docs (ValueError for a malformed string); parse_error label, floatobject.c:1464"
    status := .refuted, prop := ``FromhexRejectsTrailingGarbage
    thm := some ``fromhexRejectsTrailingGarbage_refuted
    bug := some "binary64-fromhex-overflow-before-trailing-garbage"
    notes := "float.fromhex('1p2000x') raises OverflowError: overflow_error leaves before finished: checks the end of the string." },
  { id := "float-pack8-roundtrip", pyFile := floatFile, pyFns := ["PyFloat_Pack8", "PyFloat_Unpack8"]
    statement := "struct.unpack('d', struct.pack('d', x)) restores all 64 bits of every float, NaNs included, in both byte orders."
    source := "struct docs; floatobject.c:2358-2375"
    status := .proven, prop := ``Pack8RoundTrip, thm := some ``pack8RoundTrip_proven },
  { id := "float-pack2-roundtrip", pyFile := floatFile, pyFns := ["PyFloat_Pack2", "PyFloat_Unpack2"]
    statement := "PyFloat_Pack2 inverts PyFloat_Unpack2 on all 65536 half precision patterns, in both byte orders, checked exhaustively."
    source := "struct docs ('e' format); floatobject.c:1981-1990"
    status := .proven, prop := ``Pack2RoundTrip, thm := some ``pack2RoundTrip_proven },
  { id := "dtoa-fixed-keeps-integer-part", pyFile := dtoaFile, pyFns := ["_Py_dg_dtoa"]
    statement := "In mode 3, for |x| >= 1 and any int ndigits >= 0, the returned decimal point lies after the first digit."
    source := "Comment at dtoa.c:2213: through ndigits past the decimal point"
    status := .refuted, prop := ``DtoaFixedKeepsIntegerPart, thm := some ``dtoaFixedKeepsIntegerPart_refuted
    bug := some "binary64-format-precision-near-int-max"
    notes := "format(123.456, '.2147483647f') is all zeros: i = ndigits + k + 1 wraps at dtoa.c:2377. Fixed upstream as gh-158446." },
  { id := "pystrtod-e-format-digit-count", pyFile := strtodFile
    pyFns := ["PyOS_double_to_string", "format_float_short"]
    statement := "For finite x and 0 <= p <= INT_MAX, '%.{p}e' % x has p + 1 mantissa digits."
    source := "Doc/library/string.rst, format code 'e'"
    status := .refuted, prop := ``EFormatDigitCount, thm := some ``eFormatDigitCount_refuted
    bug := some "binary64-format-precision-near-int-max"
    notes := "format(1.5, '.2147483647e') is '2e+00': precision++ wraps at pystrtod.c:1240. Fixed upstream as gh-158446." },
  { id := "float-int-compare-exact", pyFile := floatFile, pyFns := ["float_richcompare"]
    statement := "Comparing a finite float with an int of any size gives the exact answer, for all six operators; a NaN compares false except for !=, and an infinity compares like its sign."
    source := "Comment at floatobject.c:366-379; Doc/library/stdtypes.rst: comparisons between numbers of different types behave as though the exact values were compared"
    status := .proven, prop := ``FloatIntCompareExact, thm := some ``floatIntCompareExact_proven },
  { id := "float-as-double", pyFile := floatFile, pyFns := ["PyFloat_AsDouble"]
    statement := "PyFloat_AsDouble returns a float's value, converts ints and __index__ results exactly as PyLong_AsDouble does, and raises TypeError for an object with neither __float__ nor __index__ and for a __float__ that returns a non-float."
    source := "Doc/c-api/float.rst, PyFloat_AsDouble; floatobject.c:256-313"
    status := .proven, prop := ``FloatAsDouble, thm := some ``floatAsDouble_proven },
  { id := "float-blank-string", pyFile := floatFile
    pyFns := ["float_from_string_inner", "PyFloat_FromString"]
    statement := "float() of an empty string, or of a str or bytes that is only spaces, raises ValueError."
    source := "floatobject.c:159-164"
    status := .proven, prop := ``FloatBlankRaises, thm := some ``floatBlankRaises_proven },
  { id := "float-repr-special", pyFile := floatFile, pyFns := ["float_repr"]
    statement := "repr gives 'nan' for every NaN, 'inf' and '-inf' for the infinities, and '0.0' and '-0.0' for the zeros."
    source := "Doc/library/functions.rst, float; floatobject.c:348-364"
    status := .proven, prop := ``ReprSpecial, thm := some ``reprSpecial_proven },
  { id := "float-round-extremes", pyFile := floatFile
    pyFns := ["float___round___impl", "double_round"]
    statement := "round(x, n) returns a NaN or infinity unchanged, x for n > 323, a zero with the sign of x for n < -308, and a zero unchanged for every n."
    source := "Comment at floatobject.c:1060-1062"
    status := .proven, prop := ``FloatRoundExtremes, thm := some ``floatRoundExtremes_proven },
  { id := "dtoa-multadd", pyFile := dtoaFile, pyFns := ["multadd"]
    statement := "multadd(b, m, a) is b * m + a, on every limb list."
    source := "Comment at dtoa.c:438"
    status := .proven, prop := ``MultaddValue, thm := some ``multaddValue_proven },
  { id := "dtoa-s2b", pyFile := dtoaFile, pyFns := ["s2b", "i2b"]
    statement := "s2b appends the digits past the ninth to y9 as decimal digits, and i2b holds its argument."
    source := "Comment at dtoa.c:477-481"
    status := .proven, prop := ``S2bValue, thm := some ``s2bValue_proven },
  { id := "dtoa-hi0bits", pyFile := dtoaFile, pyFns := ["hi0bits"]
    statement := "hi0bits(0) is 32, and for 0 < x < 2**32, shifting x left by hi0bits(x) puts its top bit at bit 31."
    source := "Comment at dtoa.c:516"
    status := .proven, prop := ``Hi0bitsSpec, thm := some ``hi0bitsSpec_proven },
  { id := "dtoa-lo0bits", pyFile := dtoaFile, pyFns := ["lo0bits"]
    statement := "For 0 < y < 2**32, lo0bits(&y) leaves y odd and counts the bits removed, and it reports 32 for 0."
    source := "Comment at dtoa.c:547-548"
    status := .proven, prop := ``Lo0bitsSpec, thm := some ``lo0bitsSpec_proven },
  { id := "dtoa-mult", pyFile := dtoaFile, pyFns := ["mult"]
    statement := "mult(a, b) is a * b on all Bigints."
    source := "Comment at dtoa.c:608-609"
    status := .proven, prop := ``MultValue, thm := some ``multValue_proven },
  { id := "dtoa-pow5mult", pyFile := dtoaFile, pyFns := ["pow5mult"]
    statement := "pow5mult(b, k) is b * 5**k for every k below the bound of 1024 the source asserts."
    source := "Comment at dtoa.c:671-673"
    status := .proven, prop := ``Pow5multValue, thm := some ``pow5multValue_proven },
  { id := "dtoa-lshift", pyFile := dtoaFile, pyFns := ["lshift"]
    statement := "lshift(b, k) is b * 2**k for a Bigint with 32-bit limbs."
    source := "Comment at dtoa.c:768-770"
    status := .proven, prop := ``LshiftValue, thm := some ``lshiftValue_proven },
  { id := "dtoa-cmp", pyFile := dtoaFile, pyFns := ["cmp"]
    statement := "On normalized Bigints, cmp is negative, zero or positive exactly as a is below, equal to or above b."
    source := "Comment at dtoa.c:816-817"
    status := .proven, prop := ``CmpSpec, thm := some ``cmpSpec_proven },
  { id := "dtoa-diff", pyFile := dtoaFile, pyFns := ["diff"]
    statement := "On normalized Bigints, diff(a, b) is |a - b| and its sign is set exactly when a < b."
    source := "Comment at dtoa.c:848-850"
    status := .proven, prop := ``DiffValue, thm := some ``diffValue_proven },
  { id := "dtoa-dshift", pyFile := dtoaFile, pyFns := ["dshift"]
    statement := "dshift(b, p2) is a shift below 32 that, with p2, leaves four leading zero bits in the top limb, modulo 32."
    source := "Comment at dtoa.c:2597-2603"
    status := .proven, prop := ``DshiftSpec, thm := some ``dshiftSpec_proven },
  { id := "dtoa-ulp", pyFile := dtoaFile, pyFns := ["ulp", "sulp"]
    statement := "For a positive float with biased exponent at least 53, ulp is the gap 2**lsb above it, and sulp without scaling agrees."
    source := "Comments at dtoa.c:906-907 and :1205-1209"
    status := .proven, prop := ``UlpSpec, thm := some ``ulpSpec_proven },
  { id := "dtoa-sd2b", pyFile := dtoaFile, pyFns := ["sd2b"]
    statement := "With scale 0, sd2b reads a positive finite float as its mantissa and exponent, for subnormals too."
    source := "Comment at dtoa.c:958-977"
    status := .proven, prop := ``Sd2bSpec, thm := some ``sd2bSpec_proven },
  { id := "dtoa-bigcomp-choice", pyFile := dtoaFile, pyFns := ["bigcomp"]
    statement := "bigcomp returns rv or rv + ulp(rv), and nothing else."
    source := "Comment at dtoa.c:1233-1238"
    status := .proven, prop := ``BigcompChoice, thm := some ``bigcompChoice_proven },
  { id := "dtoa-strtod-no-number", pyFile := dtoaFile, pyFns := ["_Py_dg_strtod"]
    statement := "With no sign, digit or point at the start, _Py_dg_strtod consumes nothing and returns 0.0."
    source := "dtoa.c:1452-1456"
    status := .proven, prop := ``StrtodNoNumber, thm := some ``strtodNoNumber_proven },
  { id := "dtoa-strtod-sign", pyFile := dtoaFile, pyFns := ["_Py_dg_strtod"]
    statement := "The sign only negates the result, at every magnitude, so a negative parse is the negation of the positive one with the same errno."
    source := "dtoa.c:2076, :2089, :2097"
    status := .proven, prop := ``StrtodSign, thm := some ``strtodSign_proven },
  { id := "dtoa-strtod-fast-path", pyFile := dtoaFile, pyFns := ["_Py_dg_strtod"]
    statement := "For a significand below 10**15 and an exponent up to 22 in size, the fast path gives the correctly rounded value of n * 10**e."
    source := "Comment at dtoa.c:101-107 (Clinger's fast path)"
    status := .proven, prop := ``StrtodFastPathExact, thm := some ``strtodFastPathExact_proven },
  { id := "dtoa-special-values", pyFile := dtoaFile, pyFns := ["_Py_dg_dtoa"]
    statement := "_Py_dg_dtoa returns Infinity, NaN and 0 for infinities, NaNs and zeros, with the input's sign, and decpt 9999 or 1."
    source := "Comment at dtoa.c:2201-2202; dtoa.c:2257-2269"
    status := .proven, prop := ``DtoaSpecial, thm := some ``dtoaSpecial_proven },
  { id := "float-hash-numeric-tower", pyFile := floatFile, pyFns := ["float_hash"]
    statement := "For a finite float with value m / n, hash(x) is m * n^-1 modulo 2**61 - 1, with the sign of x."
    source := "Doc/library/stdtypes.rst, hashing of numeric types"
    status := .open, prop := ``FloatHashNumericTower
    notes := "Needs a loop invariant for hashLoop over the F64 mantissa. Difftested." },
  { id := "float-hex-roundtrip", pyFile := floatFile, pyFns := ["float_hex_impl", "float_fromhex_impl"]
    statement := "float.fromhex(x.hex()) == x for every finite x."
    source := "float.hex docs"
    status := .open, prop := ``HexRoundTrip
    notes := "Needs the digits of hexDigits and the exact no-rounding path of hexValue related to mant. Difftested." },
  { id := "float-repr-roundtrip", pyFile := floatFile, pyFns := ["float_repr"]
    statement := "float(repr(x)) == x for every finite x."
    source := "Doc/tutorial/floatingpoint.rst"
    status := .open, prop := ``ReprRoundTrip
    notes := "Depends on dtoa-shortest-roundtrip and strtod-correctly-rounded. Difftested." },
  { id := "strtod-correctly-rounded", pyFile := dtoaFile, pyFns := ["_Py_dg_strtod"]
    statement := "_Py_dg_strtod returns the correctly rounded value of every digit string it accepts."
    source := "Doc/whatsnew/3.1.rst (correctly rounded string to float conversions)"
    status := .open, prop := ``StrtodCorrectlyRounded
    notes := "Needs termination and an error bound for the correction loop strtodLoop. The fast path is proven separately. Difftested with halfway decimal strings." },
  { id := "dtoa-fixed-correct", pyFile := dtoaFile, pyFns := ["_Py_dg_dtoa"]
    statement := "In mode 3, for the ndigits double_round passes, the digits are within half a unit of 10**-ndigits of x."
    source := "Comment at dtoa.c:2213"
    status := .open, prop := ``DtoaFixedCorrect
    notes := "Needs QuoremSpec and an error analysis of the quick path. Difftested." },
  { id := "dtoa-shortest-roundtrip", pyFile := dtoaFile, pyFns := ["_Py_dg_dtoa"]
    statement := "In mode 0 the digits read back as x."
    source := "Comment at dtoa.c:2205"
    status := .open, prop := ``DtoaShortestRoundTrip
    notes := "Needs QuoremSpec and the Steele-White invariant of shortestDigits. Difftested." },
  { id := "float-round-half-even", pyFile := floatFile, pyFns := ["float___round___impl"]
    statement := "round(x) is the nearest int, with ties to even."
    source := "float.__round__ docstring, floatobject.c:1028"
    status := .open, prop := ``FloatRoundHalfEven
    notes := "Needs exactness of x - round(x) and of x / 2.0 on halfway values. Difftested." },
  { id := "float-as-integer-ratio", pyFile := floatFile, pyFns := ["float_as_integer_ratio_impl"]
    statement := "x.as_integer_ratio() is exact, in lowest terms, with a positive denominator, and raises OverflowError for infinities and ValueError for NaNs."
    source := "float.as_integer_ratio docstring, floatobject.c:1478-1481"
    status := .proven, prop := ``AsIntegerRatioExact, thm := some ``asIntegerRatioExact_proven },
  { id := "float-pack4-roundtrip", pyFile := floatFile, pyFns := ["PyFloat_Pack4", "PyFloat_Unpack4"]
    statement := "PyFloat_Pack4 inverts PyFloat_Unpack4 on every binary32 pattern, in both byte orders."
    source := "struct docs; floatobject.c:2187-2201 and :2509-2522"
    status := .open, prop := ``Pack4RoundTrip
    notes := "Needs roundPos on exact binary32 values. Difftested." },
  { id := "dtoa-quorem", pyFile := dtoaFile, pyFns := ["quorem"]
    statement := "quorem(b, S) is the quotient digit and the remainder, given b < 10 * S and a normalized S."
    source := "Comment at dtoa.c:1135-1137"
    status := .open, prop := ``QuoremSpec
    notes := "Needs a bound on the estimate q and the two subtraction loops. Difftested through dtoa." },
  { id := "dtoa-d2b", pyFile := dtoaFile, pyFns := ["d2b"]
    statement := "d2b writes a positive finite float as an odd integer times a power of two, with its bit count."
    source := "Comment at dtoa.c:1028-1035"
    status := .open, prop := ``D2bSpec
    notes := "Follows from Lo0bitsSpec with the word layout. Difftested through dtoa." },
  { id := "dtoa-b2d", pyFile := dtoaFile, pyFns := ["b2d"]
    statement := "b2d gives the leading bits of a Bigint as a double in [1, 2), with the exponent."
    source := "Comment at dtoa.c:921"
    status := .open, prop := ``B2dSpec
    notes := "Needs the shifts split over two limbs. Difftested through strtod." },
  { id := "dtoa-ratio", pyFile := dtoaFile, pyFns := ["ratio"]
    statement := "ratio(a, b) is within 2.5 ulps of a / b."
    source := "Comment at dtoa.c:1082-1083"
    status := .open, prop := ``RatioBound
    notes := "Follows from B2dSpec and an error analysis. Difftested through strtod." },
  { id := "complex-parts", pyFile := complexFile
    pyFns := ["_Py_c_sum", "_Py_cr_sum", "_Py_rc_sum", "_Py_c_diff", "_Py_cr_diff", "_Py_rc_diff",
      "_Py_c_neg", "complex_neg", "complex_pos", "complex_conjugate_impl",
      "complex___getnewargs___impl", "complex___complex___impl"]
    statement := "Complex addition and subtraction give each part correctly rounded, mixed real and complex forms leave the other part alone, and negation and conjugation only flip signs."
    source := "Comment at complexobject.c:665-678 (C11 Annex G mixed-mode rules)"
    status := .proven, prop := ``ComplexParts, thm := some ``complexParts_proven },
  { id := "complex-prod-shape", pyFile := complexFile
    pyFns := ["_Py_c_prod", "_Py_cr_prod", "_Py_rc_prod"]
    statement := "_Py_c_prod is the textbook product unless both of its parts are NaN, and multiplication by a real scales both parts."
    source := "Comment at complexobject.c:96-97 (C11 Annex G.5.1)"
    status := .proven, prop := ``ComplexProdShape, thm := some ``complexProdShape_proven },
  { id := "complex-div-zero", pyFile := complexFile
    pyFns := ["_Py_c_quot", "_Py_cr_quot", "_Py_rc_quot"]
    statement := "Dividing by a complex or real zero, of any signs, sets EDOM, so complex division raises ZeroDivisionError for every dividend."
    source := "complexobject.c:200-203, :257-258, :272-274, :710-713"
    status := .proven, prop := ``ComplexDivZero, thm := some ``complexDivZero_proven },
  { id := "complex-abs", pyFile := complexFile, pyFns := ["_Py_c_abs", "complex_abs"]
    statement := "abs(z) is infinite when a part is infinite, even with a NaN in the other, and for finite parts is hypot, with OverflowError exactly when hypot is not finite. Holds for any C library."
    source := "Comment at complexobject.c:374-376"
    status := .proven, prop := ``ComplexAbs, thm := some ``complexAbs_proven },
  { id := "complex-bool", pyFile := complexFile, pyFns := ["complex_bool"]
    statement := "bool(z) is false exactly when both parts are zero."
    source := "complexobject.c:796"
    status := .proven, prop := ``ComplexBool, thm := some ``complexBool_proven },
  { id := "complex-compare", pyFile := complexFile, pyFns := ["complex_richcompare"]
    statement := "Order comparisons are NotImplemented, == with a float needs a zero imaginary part, and == with an int of any size is exact."
    source := "complexobject.c:806-842; Doc/library/stdtypes.rst, comparisons"
    status := .proven, prop := ``ComplexCompare, thm := some ``complexCompare_proven },
  { id := "complex-pow-special", pyFile := complexFile
    pyFns := ["_Py_c_pow", "c_powu", "c_powi", "complex_pow"]
    statement := "z ** 0 is 1 for every z, _Py_c_pow answers 1 for a zero exponent, and a zero base with a nonzero imaginary exponent sets EDOM. Holds for any C library."
    source := "complexobject.c:314-323, :738-749"
    status := .proven, prop := ``ComplexPowSpecial, thm := some ``complexPowSpecial_proven },
  { id := "complex-real-operand", pyFile := complexFile, pyFns := ["real_to_double", "real_to_complex"]
    statement := "A float operand keeps its value and gets imaginary part 0.0, and an int goes through the float conversion."
    source := "complexobject.c:644-663"
    status := .proven, prop := ``ComplexRealOperand, thm := some ``complexRealOperand_proven },
  { id := "complex-repr", pyFile := complexFile, pyFns := ["complex_repr"]
    statement := "With a positive zero real part, repr(z) is the repr of the imaginary part followed by j, with no parentheses."
    source := "Comment at complexobject.c:577-578"
    status := .proven, prop := ``ComplexRepr, thm := some ``complexRepr_proven },
  { id := "complex-blank-string", pyFile := complexFile
    pyFns := ["complex_from_string_inner", "complex_subtype_from_string"]
    statement := "complex() of an empty string, or of one that is only spaces, raises ValueError."
    source := "parse_error label, complexobject.c:1047-1050"
    status := .proven, prop := ``ComplexBlankRaises, thm := some ``complexBlankRaises_proven },
  { id := "pystrtod-case-insensitive-match", pyFile := strtodFile, pyFns := ["case_insensitive_match"]
    statement := "case_insensitive_match(s, t) is true exactly when the lowered prefix of s spells t."
    source := "Comment at pystrtod.c:9-10"
    status := .proven, prop := ``CaseInsensitiveMatch, thm := some ``caseInsensitiveMatch_proven },
  { id := "pystrtod-parse-inf-or-nan", pyFile := strtodFile, pyFns := ["_Py_parse_inf_or_nan"]
    statement := "_Py_parse_inf_or_nan returns -1.0 with the end at the start, or an infinity or NaN with the end past the start."
    source := "Comment at pystrtod.c:22-26"
    status := .proven, prop := ``ParseInfOrNan, thm := some ``parseInfOrNan_proven },
  { id := "pystrtod-ascii-strtod-fallback", pyFile := strtodFile, pyFns := ["_PyOS_ascii_strtod"]
    statement := "_PyOS_ascii_strtod keeps a _Py_dg_strtod result that consumed input, and otherwise tries inf and nan."
    source := "Comment at pystrtod.c:107-109"
    status := .proven, prop := ``AsciiStrtodFallback, thm := some ``asciiStrtodFallback_proven },
  { id := "pystrtod-string-to-double", pyFile := strtodFile, pyFns := ["PyOS_string_to_double"]
    statement := "With endptr NULL, PyOS_string_to_double succeeds only when the conversion consumed input and stopped at the NUL."
    source := "Comment at pystrtod.c:279-281"
    status := .proven, prop := ``StringToDoubleContract, thm := some ``stringToDoubleContract_proven },
  { id := "pystrtod-underscores", pyFile := strtodFile, pyFns := ["_Py_string_to_number_with_underscores"]
    statement := "With no underscore the input reaches the inner conversion untouched, a successful scan removes exactly the underscores, and a leading underscore raises ValueError."
    source := "Comment at pystrtod.c:333-343; PEP 515"
    status := .proven, prop := ``UnderscoreRule, thm := some ``underscoreRule_proven }
]

end PyLean.Binary64
