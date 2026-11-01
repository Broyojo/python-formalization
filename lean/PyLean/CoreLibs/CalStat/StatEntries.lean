import PyLean.Registry
import PyLean.CoreLibs.CalStat.StatSqrt

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
  st "geometric-checks" ["geometric_mean"]
    "geometric_mean raises for empty data, gives 0.0 for zeros, and a negative value after a zero still raises."
    "docstring" ``GeometricChecks ``geometricChecks_proven,
  st "two-input-checks" ["covariance", "correlation", "linear_regression"]
    "Length mismatch, fewer than two points and an unknown method raise, in source order; proportional=True gives intercept 0.0."
    "docstrings" ``TwoInputChecks ``twoInputChecks_proven,
  re "correlation-constant" "corelibs-statistics-correlation-constant-undetected"
    ["correlation", "linear_regression"]
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
    "docstrings; statistics.py@3.14.7:1261-1339" ``NormalDistUndefined ``normalDistUndefined_proven,
  st "inv-cdf-centre" ["NormalDist.inv_cdf", "NormalDist.quantiles", "NormalDist.samples",
      "_normal_dist_inv_cdf"]
    "inv_cdf(0.5) == mu for finite mu and sigma; quantiles(n) gives n - 1 values and samples one value per draw when they succeed."
    "docstrings" ``InvCdfCentre ``invCdfCentre_proven,
  st "from-samples-short" ["NormalDist.from_samples"]
    "from_samples needs two points and raises the StatisticsError of _mean_stdev otherwise."
    "statistics.py:1762-1763" ``FromSamplesShort ``fromSamplesShort_proven
]

end PyLean.CoreLibs.CalStat
