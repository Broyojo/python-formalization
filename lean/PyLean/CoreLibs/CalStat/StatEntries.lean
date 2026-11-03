import PyLean.Registry
import PyLean.CoreLibs.CalStat.StatSqrt
import PyLean.CoreLibs.CalStat.StatExact
import PyLean.CoreLibs.CalStat.StatND

/-! Registry entries for `Lib/statistics.py`. -/

namespace PyLean.CoreLibs.CalStat

open PyLean.Registry

private def st (id : String) (fns : List String) (s src : String) (p t : Lean.Name) : Entry :=
  { id := "calstat-statistics-" ++ id, pyFile := "statistics.py", pyFns := fns, statement := s,
    source := src, status := .proven, prop := p, thm := some t }

private def re (id bug : String) (fns : List String) (s src : String) (p t : Lean.Name) : Entry :=
  { id := "calstat-statistics-" ++ id, pyFile := "statistics.py", pyFns := fns, statement := s,
    source := src, status := .refuted, prop := p, thm := some t, bug := some bug }

private def op (id : String) (fns : List String) (s src note : String) (p : Lean.Name) : Entry :=
  { id := "calstat-statistics-" ++ id, pyFile := "statistics.py", pyFns := fns, statement := s,
    source := src, status := .open, prop := p, notes := note }

def statisticsEntries : List Entry := [
  st "sum-exact" ["_sum"]
    "For any mix of finite values, _sum returns the exact rational sum and the count, with the coerced type."
    "docstring of _sum" ``SumExact ``sumExact_proven,
  st "mean-fractions" ["mean"]
    "mean of Fractions is the exact mean as a Fraction; mean([]) raises StatisticsError."
    "docstring of mean" ``MeanFractions ``meanFractions_proven,
  st "mean-ints" ["mean", "_convert"]
    "mean of ints is an int when the exact mean is whole and otherwise the correctly rounded float."
    "docstring of mean; statistics.py:1631-1636" ``MeanInts ``meanInts_proven,
  st "mean-floats" ["mean", "_convert"]
    "mean of finite floats is the exact mean correctly rounded."
    "docstring of _sum (no round-off)" ``MeanFloats ``meanFloats_proven,
  re "mean-int-subclass" "corelibs-statistics-mean-intenum-valueerror"
    ["mean", "_convert", "variance", "pvariance"]
    "mean of valid members of an int subclass does not raise ValueError."
    "Doc/library/statistics.rst, mean" ``MeanIntSubclass ``meanIntSubclass_refuted,
  st "variance-fractions" ["variance", "pvariance", "_ss"]
    "variance and pvariance of Fractions are the exact sum of squared deviations from the mean over n-1 and n, as Fraction."
    "docstrings of variance, pvariance, _ss" ``VarianceFractions ``varianceFractions_proven,
  st "variance-with-mean" ["variance", "pvariance", "_ss"]
    "For Fractions, passing the mean as xbar or mu gives the same result as not passing it."
    "docstring of variance" ``VarianceWithMean ``varianceWithMean_proven,
  st "stdev-of-variance" ["stdev", "pstdev", "_mean_stdev"]
    "stdev and pstdev apply _float_sqrt_of_frac to the exact variance; _mean_stdev agrees with mean and stdev."
    "docstrings of stdev, pstdev" ``StdevOfVariance ``stdevOfVariance_proven,
  st "exact-ratio-spec" ["_exact_ratio", "_isfinite"]
    "_exact_ratio gives the value with a positive denominator for finite numbers, (x, None) exactly for what _isfinite calls non-finite, TypeError for non-numbers."
    "docstring of _exact_ratio; statistics.py:1613" ``ExactRatioSpec ``exactRatioSpec_proven,
  re "coerce-order" "corelibs-statistics-coerce-set-order" ["_coerce", "_sum", "_ss"]
    "The result of reduce(_coerce, types, int) does not depend on the order of the set of types."
    "invariant: same input, same outcome" ``CoerceOrderIndependent ``coerceOrderIndependent_refuted,
  st "coerce-builtin-order" ["_coerce"]
    "On int, bool, float, Fraction and Decimal the outcome of the reduction does not depend on the order."
    "narrowing of coerce-order" ``CoerceBuiltinOrder ``coerceBuiltinOrder_proven,
  st "convert-spec" ["_convert"]
    "_convert keeps a Fraction, gives a whole value to an unrestricted int type and a non-whole value the rounded float, for every int subclass."
    "statistics.py:1624-1641" ``ConvertSpec ``convertSpec_proven,
  st "fail-neg" ["_fail_neg"]
    "_fail_neg passes values through when none is negative and otherwise raises StatisticsError(errmsg)."
    "docstring" ``FailNegSpec ``failNegSpec_proven,
  st "harmonic-exact" ["harmonic_mean"]
    "For two or more positive Fractions harmonic_mean is n / sum(1/x) exactly; one non-negative value is returned as it is; empty data raises."
    "docstring" ``HarmonicMeanExact ``harmonicMeanExact_proven,
  st "harmonic-early-out" ["harmonic_mean"]
    "A zero met before any negative value gives 0 whatever follows; a negative value met before any zero raises."
    "actual behaviour, kept by decision in gh-82563" ``HarmonicEarlyOut ``harmonicEarlyOut_proven,
  st "integer-sqrt-rto" ["_integer_sqrt_of_frac_rto"]
    "For n >= 0, m > 0 the result is the floor a of sqrt(n/m), with the low bit set when the root is inexact."
    "docstring: round-to-odd" ``IntegerSqrtRto ``integerSqrtRto_proven,
  st "float-sqrt-basic" ["_float_sqrt_of_frac"]
    "_float_sqrt_of_frac(0, m) is 0.0 and _float_sqrt_of_frac(k*k, 1) is float(k) for 0 < k < 2**53."
    "docstring (narrowing of float-sqrt-rounded)" ``FloatSqrtBasic ``floatSqrtBasic_proven,
  op "float-sqrt-rounded" ["_float_sqrt_of_frac"]
    "_float_sqrt_of_frac(n, m) is the correctly rounded square root of n/m."
    "docstring"
    "Stated in rationals. Needs the double-rounding argument for round-to-odd: a 109-bit odd result rounds to 53 bits as the exact root does. Not attempted." ``FloatSqrtCorrectlyRounded,
  st "decimal-sqrt-sign" ["_decimal_sqrt_of_frac"]
    "_decimal_sqrt_of_frac(0, m) is 0, and (-n, -m) gives the same as (n, m)."
    "statistics.py:1736-1739" ``DecimalSqrtSign ``decimalSqrtSign_proven,
  st "sqrtprod" ["_sqrtprod"]
    "_sqrtprod with a zero factor is 0.0; sqrtprod(4, 9) == 6 and sqrtprod(1e308, 1e308) == 1e308 through the rescaling."
    "docstring" ``SqrtprodSpec ``sqrtprodSpec_proven,
  st "rank" ["_rank"]
    "Only ties='average' exists, there is one rank per item, and the docstring examples hold, including idempotence and reverse."
    "docstring" ``RankSpec ``rankSpec_proven,
  st "median-order" ["median", "median_low", "median_high"]
    "For items with an integer key the low and high medians are items of the data, in order, equal for odd sizes, and split the data in half; median is the middle item or the average of the two."
    "docstrings" ``MedianOrder ``medianOrder_proven,
  st "grouped-bounds" ["median_grouped"]
    "In median_grouped on sorted data, i <= n//2 < j <= n, so the run length j - i is positive; empty data raises."
    "statistics.py:446-465" ``GroupedBounds ``groupedBounds_proven,
  st "mode-spec" ["mode", "multimode"]
    "For == an equivalence, multimode lists exactly the items of maximal count, mode is its first item and the first such item in the data; empty data: mode raises, multimode gives []."
    "docstrings" ``ModeSpec ``modeSpec_proven,
  st "quantiles-inclusive" ["quantiles"]
    "With method='inclusive' on sorted Fractions the indices stay in range and each cut point lies between two neighbours, hence between minimum and maximum."
    "docstring" ``QuantilesInclusive ``quantilesInclusive_proven,
  st "quantiles-exclusive" ["quantiles"]
    "With method='exclusive' the clamp keeps both indices valid and an interior cut point lies between two neighbours."
    "statistics.py:1216-1221" ``QuantilesExclusive ``quantilesExclusive_proven,
  st "quantiles-shape" ["quantiles"]
    "n < 1 and empty data raise; two or more Fractions give n - 1 cut points with either method."
    "docstring: Returns a list of (n - 1) cut points" ``QuantilesShape ``quantilesShape_proven,
  re "quantiles-method" "corelibs-statistics-quantiles-method-unchecked" ["quantiles"]
    "An unknown method raises ValueError whenever there is data."
    "statistics.py:1224" ``QuantilesMethodChecked ``quantilesMethodChecked_refuted,
  st "fmean-checks" ["fmean"]
    "fmean raises for empty data without weights, for a length mismatch, and for zero total weight."
    "docstring" ``FmeanChecks ``fmeanChecks_proven,
  st "fmean-exact" ["fmean"]
    "fmean is fsum over the count, and with weights sumprod over the sum of the weights; each step's exception comes out, and sumprod's ValueError becomes the length message."
    "Lib/statistics.py:182-222" ``FmeanExact ``fmeanExact_proven,
  st "geometric-exact" ["geometric_mean"]
    "After its scan geometric_mean is exp of the mean of the logarithms; a NaN total is NaN, a zero gives 0.0 or NaN with an infinity, and a failure comes out."
    "Lib/statistics.py:225-262" ``GeometricExact ``geometricExact_proven,
  st "pdf-exact" ["NormalDist.pdf"]
    "pdf of a float is exp(-0.5 * z * z) / (sqrt(tau) * sigma) for every non-zero sigma, including one whose square underflows."
    "Lib/statistics.py:1259-1265" ``PdfExact ``pdfExact_proven,
  st "geometric-checks" ["geometric_mean"]
    "geometric_mean raises for empty data, gives 0.0 for zeros, and a negative value after a zero still raises."
    "docstring" ``GeometricChecks ``geometricChecks_proven,
  st "two-input-checks" ["covariance", "correlation", "linear_regression"]
    "Length mismatch, fewer than two points and an unknown method raise, in source order; proportional=True gives intercept 0.0."
    "docstrings" ``TwoInputChecks ``twoInputChecks_proven,
  re "correlation-constant" "corelibs-statistics-correlation-constant-undetected"
    ["correlation"]
    "correlation raises StatisticsError for constant x."
    "Doc/library/statistics.rst:757" ``ConstantInputDetected ``constantInputDetected_refuted,
  re "correlation-bounded" "corelibs-statistics-correlation-out-of-range" ["correlation", "_sqrtprod"]
    "correlation returns a value in [-1, 1]."
    "docstring" ``CorrelationBounded ``correlationBounded_refuted,
  st "kernels-centred" ["register", "normal_kernel", "logistic_kernel", "sigmoid_kernel",
      "rectangular_kernel", "triangular_kernel", "parabolic_kernel", "quartic_kernel",
      "triweight_kernel", "cosine_kernel"]
    "Under the exact libm values of C99 Annex F, every kernel has cdf(0) == 0.5 for each registered name, and the polynomial bounded kernels have cdf(-1) == 0, cdf(1) == 1, support 1.0."
    "kernel definitions" ``KernelsCentred ``kernelsCentred_proven,
  st "newton-post" ["_newton_raphson", "_quartic_invcdf_estimate", "_triweight_invcdf_estimate"]
    "When the Newton loop ends, f(x) is within the tolerance of y; both estimates are 0 at p = 0.5."
    "docstring of f_inv" ``NewtonPost ``newtonPost_proven,
  st "kde-checks" ["kde", "kde_random"]
    "kde and kde_random check empty data, the type of the first element, h <= 0.0 and the kernel name, in that order; kde_random makes one value per draw."
    "docstrings" ``KdeChecks ``kdeChecks_proven,
  st "kde-cdf-outside" ["kde"]
    "The cdf of a bounded kernel is exactly 0.0 below the data and 1.0 above it."
    "cdf contract; statistics.py:1076-1084" ``KdeCdfOutside ``kdeCdfOutside_proven,
  st "normaldist-init" ["NormalDist.__init__", "NormalDist.mean", "NormalDist.median",
      "NormalDist.mode", "NormalDist.stdev", "NormalDist.variance", "NormalDist.__getstate__",
      "NormalDist.__setstate__"]
    "NormalDist refuses a negative sigma; a constructed object reports mu and sigma back, variance is stdev*stdev, and the pickling state round-trips."
    "docstrings" ``NormalDistInit ``normalDistInit_proven,
  st "normaldist-arith" ["NormalDist.__add__", "NormalDist.__sub__", "NormalDist.__mul__",
      "NormalDist.__truediv__", "NormalDist.__pos__", "NormalDist.__neg__", "NormalDist.__rsub__"]
    "With a constant, + and - translate mu, * and / scale mu by c and sigma by |c|, -(-x) is x, c - x is -(x - c), and dividing by zero raises."
    "docstrings" ``NormalDistArith ``normalDistArith_proven,
  st "normaldist-sum" ["NormalDist.__add__", "NormalDist.__sub__"]
    "X + Y and X - Y add and subtract the means and take hypot of the sigmas; the means of X + Y and Y + X agree."
    "docstrings" ``NormalDistSum ``normalDistSum_proven,
  op "normaldist-hypot-commutes" ["NormalDist.__add__"]
    "hypot(a, b) == hypot(b, a) for finite a, b, so X + Y == Y + X."
    "invariant"
    "vector_norm accumulates in argument order, so it needs an error analysis of the compensated sum; a scan of 300000 random pairs found no difference." ``HypotCommutes,
  st "normaldist-eq-hash" ["NormalDist.__eq__", "NormalDist.__hash__", "NormalDist.__repr__"]
    "__eq__ is symmetric, equal objects hash equal, also for 0.0 and -0.0, and __repr__ shows mu and sigma with repr(float)."
    "docstrings" ``NormalDistEqHash ``normalDistEqHash_proven,
  st "normaldist-undefined" ["NormalDist.pdf", "NormalDist.cdf", "NormalDist.zscore",
      "NormalDist.overlap", "NormalDist.inv_cdf"]
    "With sigma == 0, pdf, cdf, zscore and overlap raise StatisticsError; p outside 0 < p < 1 raises in inv_cdf."
    "docstrings; Lib/statistics.py:1259-1339" ``NormalDistUndefined ``normalDistUndefined_proven,
  st "inv-cdf-centre" ["NormalDist.inv_cdf", "NormalDist.quantiles", "NormalDist.samples",
      "_normal_dist_inv_cdf"]
    "inv_cdf(0.5) == mu for finite mu and sigma; quantiles(n) gives n - 1 values and samples one value per draw when they succeed."
    "docstrings" ``InvCdfCentre ``invCdfCentre_proven,
  st "from-samples-short" ["NormalDist.from_samples"]
    "from_samples needs two points and raises the StatisticsError of _mean_stdev otherwise."
    "statistics.py:1762-1763" ``FromSamplesShort ``fromSamplesShort_proven,
  re "sqrtprod-accurate" "calstat-statistics-sqrtprod-partial-underflow" ["_sqrtprod"]
    "For positive finite floats x, y, _sqrtprod(x, y) is a finite float v with |v*v - x*y| <= 2**-50 * x*y."
    "Lib/statistics.py:1773 (docstring: improved accuracy, without overflow/underflow)"
    ``SqrtprodAccurate ``sqrtprodAccurate_refuted,
  re "correlation-proportional" "calstat-statistics-sqrtprod-partial-underflow" ["correlation", "_sqrtprod"]
    "For exactly proportional normal-float data y = c*x, c > 0, x not constant, correlation(x, y) is within 2**-50 of 1."
    "Lib/statistics.py:691-692; docstring of _sqrtprod"
    ``CorrelationProportional ``correlationProportional_refuted,
  re "decimal-sqrt-half-even" "calstat-statistics-decimal-sqrt-tie" ["_decimal_sqrt_of_frac"]
    "Whenever sqrt(n/m) is rational, _decimal_sqrt_of_frac(n, m) is its 28-digit half-even rounding."
    "Lib/statistics.py:1732 (docstring: correctly rounded)" ``DecimalSqrtHalfEven ``decimalSqrtHalfEven_refuted,
  op "decimal-sqrt-nearest" ["_decimal_sqrt_of_frac"]
    "_decimal_sqrt_of_frac(n, m) is a nearest 28-digit value to sqrt(n/m), ties either way."
    "narrowing of decimal-sqrt-half-even"
    "Needs: the sticky-digit argument that decSqrtFin is the 28-digit rounding of the root of the rounded quotient, the 0.5-ulp error of that quotient, and a 1.5-ulp bound so that one neighbour step suffices, including at powers of ten. Smoke-tested on 100000 random and tie cases." ``DecimalSqrtNearest,
  re "quantiles-inclusive-in-range" "calstat-statistics-quantiles-inclusive-outside-range" ["quantiles"]
    "With method='inclusive' every cut point of finite float data lies between the minimum and the maximum."
    "Lib/statistics.py:1188-1190" ``QuantilesInclusiveInRange ``quantilesInclusiveInRange_refuted,
  st "quantiles-hf" ["quantiles"]
    "For Fraction data, n < 1 raises before the data is read; with two or more points the cut points are Hyndman-Fan definition 7 ('inclusive') or 6 ('exclusive', extended linearly past the ends) of sorted(data) at i/n, exactly; an unknown method raises ValueError."
    "Lib/statistics.py:1149-1170 (R6/R7), 1176-1224" ``QuantilesHF ``quantilesHF_proven,
  st "linreg-proportional" ["linear_regression"]
    "For int data, linear_regression(x, y, proportional=True) checks the lengths, then computes the exact sums sum(x*y) and sum(x*x) (sumprod is exact on ints), converts them to float (OverflowError past the float range), raises 'x is constant' when sum(x*x) == 0, and otherwise returns float(sum(x*y)) / float(sum(x*x)) with intercept 0.0: the correctly rounded least-squares slope through the origin when both sums are below 2**53."
    "Lib/statistics.py:745-805 (docstring: fit through the origin, intercept always 0.0)" ``LinRegProportional ``linRegProportional_proven,
  st "fmean-ints" ["fmean"]
    "For int data with magnitudes summing below 2**53 and len() truthful or raising a TypeError (an iterator, decided by the class relation H), fmean is the correctly rounded mean, StatisticsError for no data; an exception of the iterator propagates; another exception of len() propagates before iteration."
    "Lib/statistics.py:182-207" ``FmeanInts ``fmeanInts_proven,
  st "fmean-weighted-ints" ["fmean"]
    "For int data and int weights (sum(x*w) and the weights' magnitudes below 2**53), fmean(data, weights) is sum(x*w) / sum(w) correctly rounded (a signed zero for a zero numerator), raises for zero total weight, turns sumprod's ValueError and any ValueError (under H) of the data iterator into the length error, and lets any other iterator exception through."
    "Lib/statistics.py:209-222" ``FmeanWeightedInts ``fmeanWeightedInts_proven,
  st "normaldist-eq" ["NormalDist.__eq__", "NormalDist.__hash__"]
    "__eq__ is NotImplemented for non-NormalDist, true iff mu and sigma compare equal, symmetric, transitive, reflexive iff no NaN; __hash__ is hash((mu, sigma)) and agrees on equal objects; equal objects give the same pdf(x), cdf(x) (erfc(+-0) equal) and zscore(x) up to ==."
    "Lib/statistics.py:1432-1440 (docstrings)" ``NormalDistEq ``normalDistEq_proven
]

end PyLean.CoreLibs.CalStat
