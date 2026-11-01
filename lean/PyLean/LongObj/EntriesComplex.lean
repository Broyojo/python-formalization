import PyLean.Registry
import PyLean.LongObj.ComplexAlgebra
import PyLean.LongObj.ComplexBranches
import PyLean.LongObj.ComplexFindings
import PyLean.LongObj.ComplexObjProps
import PyLean.LongObj.ComplexNewProps
import PyLean.LongObj.ComplexParseProps
import PyLean.LongObj.ComplexParseTwin
import PyLean.LongObj.ComplexParseWrap
import PyLean.LongObj.ComplexStrtodSpec

/-!
Registry entries for `Objects/complexobject.c`, CPython 3.14.7.

The arithmetic has three layers. Ring and field theorems show the branch structure
computes the intended function over exact arithmetic; `CProdBranchOrder` and
`CQuotBranchOrder` record which branch of the NaN and infinity recovery runs; and
`Dbl`, exact binary64, refutes what fails on real doubles. Universally quantified
statements about rounding stay open until `Binary64` is merged.
-/

namespace PyLean.LongObj

open PyLean.Registry Cplx

def complexFile : String := "Objects/complexobject.c"

def entriesComplex : List Entry := [
  { id := "complex-ring-sum-diff", pyFile := complexFile
    pyFns := ["_Py_c_sum", "_Py_cr_sum", "_Py_rc_sum", "_Py_c_diff", "_Py_cr_diff", "_Py_rc_diff",
              "_Py_c_neg"]
    statement := "Over any commutative ring with the C operations being the ring's, _Py_cr_sum, _Py_rc_sum, _Py_cr_diff and _Py_rc_diff equal the complex operation with the real operand given a zero imaginary part; _Py_c_diff(a, b) is _Py_c_sum(a, _Py_c_neg(b)); _Py_c_sum is commutative."
    source := "complexobject.c:665-678 (rules for mixed-mode arithmetic)"
    status := .proven, prop := ``RingSumDiff, thm := some ``ringSumDiff_proven
    notes := "Generic over `Lean.Grind.CommRing`. At binary64 the mixed forms differ from the coerced ones on signed zeros, on purpose: see complex-mixed-mode-direct." },
  { id := "complex-ring-prod", pyFile := complexFile
    pyFns := ["_Py_c_prod", "_Py_cr_prod", "_Py_rc_prod"]
    statement := "Over any commutative ring, _Py_c_prod is (ac-bd)+(ad+bc)j and commutative, and _Py_cr_prod and _Py_rc_prod equal it with the real operand given a zero imaginary part."
    source := "invariant; complexobject.c:665-678"
    status := .proven, prop := ``RingProd, thm := some ``ringProd_proven },
  { id := "complex-prod-branch-order", pyFile := complexFile
    pyFns := ["_Py_c_prod"]
    statement := "For every CDouble instance, _Py_c_prod returns the plain product unless both parts are NaN; it still returns it when no operand part and no partial product is infinite; an infinite z takes the boxing branch and the recomputed result."
    source := "complexobject.c:96-145 (C11 Annex G.5.1 _Cmultd)"
    status := .proven, prop := ``CProdBranchOrder, thm := some ``cProdBranchOrder_proven
    notes := "Records the branch structure only. That the recomputed value is infinite is complex-prod-annex-g, which waits on Binary64." },
  { id := "complex-prod-annex-g", pyFile := complexFile
    pyFns := ["_Py_c_prod"]
    statement := "At binary64, if one operand of _Py_c_prod is an infinity and the other a nonzero finite number or an infinity, the result has an infinite part."
    source := "C11 Annex G.5.1; complexobject.c:96-97"
    status := .open, prop := ``CProdAnnexG
    notes := "Waits on Binary64: needs that the boxed x - y and x + y are not both zero, a statement about rounding and underflow." },
  { id := "complex-ring-powu", pyFile := complexFile
    pyFns := ["c_powu"]
    statement := "Over any commutative ring, c_powu(x, n) is the n-th power of x under _Py_c_prod, for every non-negative n a C long can hold, across the wrap of mask at 2^63."
    source := "invariant: square-and-multiply"
    status := .proven, prop := ``RingPowu, thm := some ``ringPowu_proven },
  { id := "complex-field-quot", pyFile := complexFile
    pyFns := ["_Py_c_quot"]
    statement := "Over any ordered field, _Py_c_quot(a, b) with b nonzero leaves errno alone and its product with b is a; with b zero it sets EDOM and returns zero."
    source := "invariant; complexobject.c:188-193 (Smith's algorithm)"
    status := .proven, prop := ``FieldQuot, thm := some ``fieldQuot_proven
    notes := "Generic over `Lean.Grind.Field` with an order; Rat is a witness (`ratFieldCompat`)." },
  { id := "complex-quot-branch-order", pyFile := complexFile
    pyFns := ["_Py_c_quot"]
    statement := "For every CDouble instance, _Py_c_quot takes the zero-divisor EDOM branch whenever the larger magnitude is zero, independently of a; when neither >= holds and neither recovery applies, the result is nan+nanj."
    source := "complexobject.c:198-222 and 224-243"
    status := .proven, prop := ``CQuotBranchOrder, thm := some ``cQuotBranchOrder_proven },
  { id := "complex-quot-annex-g", pyFile := complexFile
    pyFns := ["_Py_c_quot"]
    statement := "At binary64, an infinite dividend over a finite divisor gives an infinite part, and a finite dividend over an infinite divisor gives zero parts."
    source := "C11 Annex G.5.2; complexobject.c:224-243"
    status := .open, prop := ``CQuotAnnexG
    notes := "Waits on Binary64: needs a rounding argument about x*b.real + y*b.imag." },
  { id := "complex-field-mixed-quot", pyFile := complexFile
    pyFns := ["_Py_cr_quot", "_Py_rc_quot"]
    statement := "Over any ordered field, _Py_cr_quot(a, x) is _Py_c_quot(a, x+0j) and _Py_rc_quot(x, b) is _Py_c_quot(x+0j, b), errno included."
    source := "complexobject.c:263 (\"an equivalent of _Py_c_quot() function, when 1st argument is real\")"
    status := .proven, prop := ``FieldMixedQuot, thm := some ``fieldMixedQuot_proven },
  { id := "complex-rc-quot-twin", pyFile := complexFile
    pyFns := ["_Py_rc_quot", "_Py_c_quot"]
    statement := "At binary64, _Py_rc_quot(a, b) equals _Py_c_quot(complex(a, 0), b), up to the signs of zeros."
    source := "complexobject.c:263 (\"an equivalent of _Py_c_quot() function, when 1st argument is real\"), and C11 Annex G.5.2"
    status := .refuted, prop := ``RcQuotMatchesCQuot, thm := some ``rcQuotMatchesCQuot_refuted
    bug := some "longobj-complex-rc-quot-inf-dividend"
    notes := "float('inf') / (1e308+1e308j): the denominator overflows, both parts are NaN, and _Py_rc_quot has no counterpart of the first recovery branch of _Py_c_quot." },
  { id := "complex-rc-quot-finite", pyFile := complexFile
    pyFns := ["_Py_rc_quot", "_Py_c_quot"]
    statement := "At binary64, for a finite a, _Py_rc_quot(a, b) equals _Py_c_quot(complex(a, 0), b) up to the signs of zeros: the excluded case of complex-rc-quot-twin is exactly an infinite dividend."
    source := "complexobject.c:263"
    status := .open, prop := ``RcQuotMatchesCQuotFinite
    notes := "Waits on Binary64: needs x + 0*r == x and 0 - x*r == (-x)*r up to the sign of zero, which `Dbl` has no proof for." },
  { id := "complex-field-powi", pyFile := complexFile
    pyFns := ["c_powi"]
    statement := "Over any ordered field, c_powi(x, n) is x^n for n > 0, 1 at 0, and the inverse of x^n at -n for nonzero x; only a zero base with a negative exponent sets EDOM."
    source := "invariant"
    status := .proven, prop := ``FieldPowi, thm := some ``fieldPowi_proven },
  { id := "complex-pow-zero-division-needs-zero-base", pyFile := complexFile
    pyFns := ["complex_pow", "c_powi", "c_powu", "_Py_c_quot"]
    statement := "At binary64, complex_pow raises 'zero to a negative or complex power' only for a zero base."
    source := "the message; complexobject.c:746-749"
    status := .refuted, prop := ``PowZeroDivisionNeedsZeroBase
    thm := some ``powZeroDivisionNeedsZeroBase_refuted
    bug := some "longobj-complex-pow-underflow-zero-division"
    notes := "complex(1e-200) ** -2: the power underflows to 0 and c_powi divides by it. Any base and exponent whose power underflows; the slow path raises OverflowError for the same value." },
  { id := "complex-cpow-edom-needs-zero-base", pyFile := complexFile
    pyFns := ["_Py_c_pow"]
    statement := "At binary64 with a glibc-like libm, _Py_c_pow sets EDOM only for a zero base."
    source := "complexobject.c:318-320 and 746-749"
    status := .refuted, prop := ``CPowEdomNeedsZeroBase, thm := some ``cPowEdomNeedsZeroBase_refuted
    bug := some "longobj-complex-pow-infinite-phase-edom"
    notes := "(1+1j) ** float('inf'): cos of an infinite phase sets EDOM. Fixed on main (gh-156886); still in 3.14.7." },
  { id := "complex-cpow-branches", pyFile := complexFile
    pyFns := ["_Py_c_pow"]
    statement := "For every CDouble instance and libm, _Py_c_pow with a zero exponent returns 1 before looking at the base, and a zero base with a nonzero exponent returns 0, with EDOM exactly when the exponent has a nonzero imaginary part or a negative real part."
    source := "complexobject.c:314-323"
    status := .proven, prop := ``CPowBranches, thm := some ``cPowBranches_proven },
  { id := "complex-pow-one-never-raises", pyFile := complexFile
    pyFns := ["complex_pow"]
    statement := "At binary64, x ** 1 does not raise."
    source := "invariant; float('inf') ** 1 returns inf"
    status := .refuted, prop := ``PowOneNeverRaises, thm := some ``powOneNeverRaises_refuted
    bug := some "longobj-complex-pow-infinite-base-overflow"
    notes := "complex('inf') ** 1: _Py_ADJUST_ERANGE2 reads an infinite result as an overflow even when the base was infinite. Fixed on main (gh-156693); still in 3.14.7." },
  { id := "complex-pow-modulo-order", pyFile := complexFile
    pyFns := ["complex_pow", "real_to_complex", "real_to_double"]
    statement := "complex_pow converts both operands first: NotImplemented and the int-overflow error come before 'complex modulo', which is raised for any non-None third argument once they convert."
    source := "complexobject.c:728-734"
    status := .proven, prop := ``PowModuloOrder, thm := some ``powModuloOrder_proven },
  { id := "complex-pow-fast-path-bound", pyFile := complexFile
    pyFns := ["complex_pow", "c_powi", "_Py_c_pow"]
    statement := "An integral exponent with |b.real| <= 100 and zero imaginary part makes no libm call, so the result is the same for every libm; any other exponent is exactly _Py_c_pow with its errno mapped to the two exceptions."
    source := "complexobject.c:736-744"
    status := .proven, prop := ``PowFastPathBound, thm := some ``powFastPathBound_proven },
  { id := "complex-pow-zero-is-one", pyFile := complexFile
    pyFns := ["complex_pow", "c_powi", "c_powu", "_Py_c_quot"]
    statement := "At binary64, z ** 0 is 1+0j for every z, NaN and infinity included, for either sign of zero in either part of the exponent."
    source := "invariant; float pow, IEEE 754 pow(x, 0)"
    status := .proven, prop := ``PowZeroIsOne, thm := some ``powZeroIsOne_proven
    notes := "The hypotheses say the exponent's parts are +0 or -0 as 64-bit patterns." },
  { id := "complex-abs-ignores-stale-errno", pyFile := complexFile
    pyFns := ["complex_abs", "_Py_c_abs"]
    statement := "abs(z) does not depend on the errno left by the previous C call."
    source := "complexobject.c:370 (\"sets errno = ERANGE on overflow;  otherwise errno = 0\")"
    status := .refuted, prop := ``ComplexAbsIgnoresStaleErrno
    thm := some ``complexAbsIgnoresStaleErrno_refuted
    bug := some "longobj-complex-abs-stale-errno"
    notes := "The NaN branch does not set errno and complex_abs does not clear it, so a stale ERANGE raises OverflowError. Fixed on main (gh-155526); still in 3.14.7." },
  { id := "complex-abs-clean-errno", pyFile := complexFile
    pyFns := ["complex_abs", "_Py_c_abs"]
    statement := "With no stale ERANGE on entry, abs of a value with a NaN part and no infinite part is NaN and does not raise."
    source := "complexobject.c:387-389"
    status := .proven, prop := ``ComplexAbsCleanErrno, thm := some ``complexAbsCleanErrno_proven },
  { id := "complex-abs-infinity", pyFile := complexFile
    pyFns := ["_Py_c_abs"]
    statement := "If either part is infinite, _Py_c_abs returns the absolute value of that part, the real part first, and clears errno, even if the other part is a NaN."
    source := "complexobject.c:374-386 (C99 rules)"
    status := .proven, prop := ``CAbsInfinity, thm := some ``cAbsInfinity_proven },
  { id := "complex-constructors-store", pyFile := complexFile
    pyFns := ["complex_subtype_from_c_complex", "PyComplex_FromCComplex",
              "complex_subtype_from_doubles", "PyComplex_FromDoubles"]
    statement := "The four constructors store exactly the doubles they are given, signed zeros and NaNs included, in an object of the requested type."
    source := "invariant"
    status := .proven, prop := ``ConstructorsStore, thm := some ``constructorsStore_proven },
  { id := "complex-neg-conj", pyFile := complexFile
    pyFns := ["complex_neg", "_Py_c_neg", "complex_conjugate_impl"]
    statement := "complex_neg and _Py_c_neg agree, and in every instance where C unary minus is an involution, negating or conjugating twice is the identity; conjugation keeps the real part."
    source := "complex.conjugate docstring, invariant"
    status := .proven, prop := ``NegConjInvolutions, thm := some ``negConjInvolutions_proven },
  { id := "complex-pos-identity", pyFile := complexFile
    pyFns := ["complex_pos", "complex___complex___impl"]
    statement := "+z and z.__complex__() return z itself for an exact complex, and an exact complex with the same value for a subclass instance."
    source := "complex.__complex__ docstring (\"Convert this value to exact type complex.\")"
    status := .proven, prop := ``PosAndComplexIdentity, thm := some ``posAndComplexIdentity_proven },
  { id := "complex-bool", pyFile := complexFile
    pyFns := ["complex_bool"]
    statement := "bool(z) is false exactly when both parts compare equal to zero, so a NaN part is truthy."
    source := "invariant"
    status := .proven, prop := ``BoolIffNonzero, thm := some ``boolIffNonzero_proven },
  { id := "complex-getnewargs-round-trip", pyFile := complexFile
    pyFns := ["complex___getnewargs___impl", "actual_complex_new", "complex_new_impl"]
    statement := "complex(*z.__getnewargs__()) reproduces z exactly, signed zeros and NaNs included, without warning or running Python code."
    source := "invariant: copy and pickle rely on it"
    status := .proven, prop := ``GetnewargsRoundTrip, thm := some ``getnewargsRoundTrip_proven },
  { id := "complex-hash-composition", pyFile := complexFile
    pyFns := ["complex_hash"]
    statement := "For any real hash that is a Py_hash_t and never -1, complex_hash is never -1, and it equals the hash of the real part when the imaginary part hashes to 0."
    source := "complexobject.c:625-630 (\"hash(x + 0*j) must equal hash(x)\")"
    status := .proven, prop := ``HashComposition, thm := some ``hashComposition_proven },
  { id := "complex-repr-structure", pyFile := complexFile
    pyFns := ["complex_repr", "complex___format___impl"]
    statement := "repr leaves out a +0 real part, without parentheses, and otherwise prints the real part and a signed imaginary part in parentheses; format(z, '') is repr(z) and any other spec goes to the format engine."
    source := "complexobject.c:576-606; Python/formatter_unicode.c:1698-1701"
    status := .proven, prop := ``ReprStructure, thm := some ``reprStructure_proven },
  { id := "complex-repr-round-trip", pyFile := complexFile
    pyFns := ["complex_repr", "complex_from_string_inner", "complex_subtype_from_string"]
    statement := "complex(repr(z)) is z up to the sign of a NaN, for every z, for any double printer and strtod that read each other's text."
    source := "invariant; repr docs"
    status := .proven, prop := ``ReprRoundTrip, thm := some ``reprRoundTrip_proven
    notes := "The printer/strtod hypothesis is `ReprSpec`." },
  { id := "complex-real-to-double", pyFile := complexFile
    pyFns := ["real_to_double", "real_to_complex"]
    statement := "real_to_double gives a float's value, an int's PyLong_AsDouble or OverflowError, and NotImplemented otherwise; real_to_complex and TO_COMPLEX add a zero imaginary part except on a complex."
    source := "complexobject.c:638-663"
    status := .proven, prop := ``RealToDouble, thm := some ``realToDouble_proven },
  { id := "complex-mixed-mode-direct", pyFile := complexFile
    pyFns := ["_Py_cr_sum", "_Py_rc_sum", "_Py_cr_diff", "_Py_rc_diff", "_Py_cr_prod", "_Py_rc_prod",
              "real_to_double"]
    statement := "For every CDouble instance, a float operand of +, - or * is combined directly with a complex: the part it does not touch is the complex operand's exactly, so a -0.0 or NaN there survives."
    source := "complexobject.c:665-678"
    status := .proven, prop := ``MixedModeDirect, thm := some ``mixedModeDirect_proven },
  { id := "complex-binop-not-implemented", pyFile := complexFile
    pyFns := ["real_to_double"]
    statement := "A binary slot given anything other than a float, int or complex instance returns NotImplemented."
    source := "complexobject.c:680-716"
    status := .proven, prop := ``BinopNotImplemented, thm := some ``binopNotImplemented_proven },
  { id := "complex-richcompare-shape", pyFile := complexFile
    pyFns := ["complex_richcompare"]
    statement := "Only == and != are implemented; != negates == on every right operand; an int compares through the exact float comparison only when the imaginary part is zero; a float or complex compares componentwise."
    source := "complexobject.c:806-853"
    status := .proven, prop := ``RichCompareShape, thm := some ``richCompareShape_proven },
  { id := "complex-richcompare-huge-int", pyFile := complexFile
    pyFns := ["complex_richcompare"]
    statement := "At binary64, complex(x) == n compares n exactly, without rounding it, however large n is."
    source := "complexobject.c:813-826; Objects/floatobject.c:382-542"
    status := .proven, prop := ``RichCompareHugeInt, thm := some ``richCompareHugeInt_proven },
  { id := "complex-accessors-agree", pyFile := complexFile
    pyFns := ["PyComplex_RealAsDouble", "PyComplex_ImagAsDouble", "PyComplex_AsCComplex"]
    statement := "PyComplex_RealAsDouble and PyComplex_ImagAsDouble agree with the two parts of PyComplex_AsCComplex on every object, in value, exception, calls and warnings."
    source := "Doc/c-api/complex.rst; the three carry separate copies of the logic"
    status := .proven, prop := ``AccessorsAgree, thm := some ``accessorsAgree_proven },
  { id := "complex-try-special-outcomes", pyFile := complexFile
    pyFns := ["try_complex_special_method"]
    statement := "try_complex_special_method does nothing when __complex__ is absent, propagates its exception, returns an exact complex's value, warns on a subclass instance, and raises TypeError on anything else."
    source := "complexobject.c:488-519"
    status := .proven, prop := ``TrySpecialOutcomes, thm := some ``trySpecialOutcomes_proven },
  { id := "complex-new-checks-real-first", pyFile := complexFile
    pyFns := ["complex_new_impl"]
    statement := "With no __complex__ on it, a real argument that is not a number raises its TypeError whatever imag is, before anything converts and with no Python code run."
    source := "complexobject.c:1195-1206"
    status := .proven, prop := ``NewChecksRealFirst, thm := some ``newChecksRealFirst_proven },
  { id := "complex-new-checks-imag-before-converting", pyFile := complexFile
    pyFns := ["complex_new_impl"]
    statement := "A valid real and an invalid imag raise the imag TypeError with no __float__ or __index__ run."
    source := "complexobject.c:1207-1220"
    status := .proven, prop := ``NewChecksImagBeforeConverting
    thm := some ``newChecksImagBeforeConverting_proven },
  { id := "complex-one-arg-matches-two-arg", pyFile := complexFile
    pyFns := ["actual_complex_new", "complex_new_impl"]
    statement := "complex(x) and complex(x, 0) take the same real part from a float instance."
    source := "Doc/library/functions.rst:426-431 (\"complex(x) delegates to x.__complex__() ... falls back to __float__()\"); 3.13 behaviour"
    status := .refuted, prop := ``OneArgMatchesTwoArgOnFloats
    thm := some ``oneArgMatchesTwoArgOnFloats_refuted
    bug := some "longobj-complex-float-subclass-dunder-float"
    notes := "class F(float) overriding __float__: complex(F(1)) reads the value directly through PyFloat_AsDouble, complex(F(1), 0) calls __float__ through PyNumber_Float. 3.13 called it in both." },
  { id := "complex-one-arg-matches-two-arg-narrow", pyFile := complexFile
    pyFns := ["actual_complex_new", "complex_new_impl"]
    statement := "On any real-number object that is not a complex or string, has no __complex__, and is not a float subclass overriding __float__, complex(x) and complex(x, 0.0) are the same computation, including errors, warnings and calls."
    source := "layered twin of complex-one-arg-matches-two-arg"
    status := .proven, prop := ``OneArgMatchesTwoArgNarrow, thm := some ``oneArgMatchesTwoArgNarrow_proven },
  { id := "complex-new-dispatch", pyFile := complexFile
    pyFns := ["actual_complex_new"]
    statement := "complex() is 0j; complex(z) is z itself for an exact complex and the exact type; a string goes to the parser before __complex__ is looked at."
    source := "complexobject.c:1099-1118"
    status := .proven, prop := ``NewDispatch, thm := some ``newDispatch_proven },
  { id := "complex-subtype-from-string", pyFile := complexFile
    pyFns := ["complex_subtype_from_string"]
    statement := "complex_subtype_from_string on a str is the parser's outcome in the requested type, and on anything else the TypeError of lines 1071-1073."
    source := "complexobject.c:1060-1080"
    status := .proven, prop := ``SubtypeFromString, thm := some ``subtypeFromString_proven
    notes := "The TypeError branch is dead code: the only caller has checked PyUnicode_Check." },
  { id := "complex-from-number-matches-constructor", pyFile := complexFile
    pyFns := ["complex_from_number_impl", "actual_complex_new", "PyComplex_AsCComplex"]
    statement := "complex.from_number(x) is x itself on an exact complex, and on an object that is neither a complex nor a string instance and has __complex__, __float__ or __index__, it computes the same value as complex(x)."
    source := "Doc/library/stdtypes.rst:746-752"
    status := .proven, prop := ``FromNumberMatchesConstructor
    thm := some ``fromNumberMatchesConstructor_proven
    notes := "A complex subclass overriding __complex__ is excluded: from_number reads its value, complex(x) calls the method." },
  { id := "complex-parse-rejects-nul", pyFile := complexFile
    pyFns := ["complex_from_string_inner", "complex_subtype_from_string"]
    statement := "Every string holding a NUL raises ValueError, on any strtod that stops at NUL, with or without underscores or non-ASCII characters."
    source := "complexobject.c:1041-1043; Python/pystrtod.c:387-390"
    status := .proven, prop := ``ParseRejectsNul, thm := some ``parseRejectsNul_proven
    notes := "The hypothesis on strtod is `StrtodSpec`." },
  { id := "complex-parser-at-binary64", pyFile := complexFile
    pyFns := ["complex_from_string_inner", "complex_subtype_from_string"]
    statement := "With the concrete binary64 strtod, every string holding a NUL raises ValueError, and every string float() accepts, complex() accepts as the same real number. No hypothesis on strtod remains."
    source := "StrtodSpec discharged for Dbl.asciiStrtod"
    status := .proven, prop := ``ParserAtBinary64, thm := some ``parserAtBinary64_proven },
  { id := "complex-parse-only-value-error", pyFile := complexFile
    pyFns := ["complex_from_string_inner", "complex_subtype_from_string"]
    statement := "complex(str) raises no exception other than ValueError, for every string and every strtod."
    source := "invariant; complex docs"
    status := .proven, prop := ``ParseRaisesOnlyValueError, thm := some ``parseRaisesOnlyValueError_proven
    notes := "MemoryError on allocation failure is not modelled." },
  { id := "complex-parse-transform-ascii", pyFile := complexFile
    pyFns := ["complex_subtype_from_string"]
    statement := "The buffer the parser sees is ASCII, and ASCII input reaches it unchanged."
    source := "complexobject.c:1065 (assert(PyUnicode_IS_ASCII(s_buffer)))"
    status := .proven, prop := ``TransformAscii, thm := some ``transformAscii_proven },
  { id := "complex-parse-leading-whitespace", pyFile := complexFile
    pyFns := ["complex_from_string_inner"]
    statement := "Leading Py_ISSPACE whitespace does not change the parse, for every string and every strtod."
    source := "complex docs (\"can optionally be surrounded by whitespaces\"); complexobject.c:938-941"
    status := .proven, prop := ``LeadingWhitespace, thm := some ``leadingWhitespace_proven },
  { id := "complex-parse-surroundings", pyFile := complexFile
    pyFns := ["complex_from_string_inner"]
    statement := "An accepted string with no parenthesis of its own keeps its value with trailing whitespace, and inside parentheses with whitespace after them, on any strtod satisfying StrtodSpec."
    source := "complex docs (\"can optionally be surrounded by whitespaces and the round parentheses\"); complexobject.c:942-948 and 1028-1039"
    status := .proven, prop := ``ParseSurroundings, thm := some ``parseSurroundings_proven
    notes := "Whitespace inside the parentheses is complex-parse-leading-whitespace and this entry applied first. A second pair of parentheses is rejected." },
  { id := "complex-parse-forms", pyFile := complexFile
    pyFns := ["complex_from_string_inner"]
    statement := "Each form the source comment lists, <float>, <float>j, <float><signed-float>j, <float><sign>j, <sign>j and j, parses to the real and imaginary parts it names."
    source := "complexobject.c:950-969; Doc/library/functions.rst (complexvalue grammar)"
    status := .proven, prop := ``ParseForms, thm := some ``parseForms_proven },
  { id := "complex-float-strings-are-complex-strings", pyFile := complexFile
    pyFns := ["complex_from_string_inner", "complex_subtype_from_string"]
    statement := "Every string float() accepts, complex() accepts as the same real number with a zero imaginary part, on any strtod satisfying StrtodSpec."
    source := "complex docs (\"in the same format as for float\"); twin of float_from_string_inner"
    status := .proven, prop := ``FloatStringsAreComplexStrings
    thm := some ``floatStringsAreComplexStrings_proven }
]

end PyLean.LongObj
