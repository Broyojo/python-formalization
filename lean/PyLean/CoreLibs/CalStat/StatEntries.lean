import PyLean.Registry
import PyLean.CoreLibs.CalStat.StatSqrt
import PyLean.CoreLibs.CalStat.StatExact
import PyLean.CoreLibs.CalStat.StatFix

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
    ["mean", "_convert"]
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
  re "coerce-order" "corelibs-statistics-coerce-set-order" ["_coerce"]
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
    "__eq__ is symmetric, equal objects hash equal whatever the identity hash of a NaN field, also for 0.0 and -0.0, and __repr__ shows type(self).__name__, mu and sigma with repr(float)."
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
  st "quantiles-iter" ["quantiles"]
    "With n < 1 quantiles raises before touching the iterable; otherwise the iterator's exception comes out before any comparison; an iterable that ends normally behaves as the list of its items."
    "Lib/statistics.py:1193-1196" ``QuantilesIter ``quantilesIter_proven,
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
    "__eq__ is NotImplemented for non-NormalDist, true iff mu and sigma compare equal, symmetric, transitive, reflexive iff no NaN; equal objects hash equal (whatever the identity hash of a NaN) and give the same pdf(x), cdf(x) (erfc(+-0) equal) and zscore(x) up to ==."
    "Lib/statistics.py:1432-1440 (docstrings)" ``NormalDistEq ``normalDistEq_proven,
  st "from-samples-twin" ["NormalDist.from_samples"]
    "For Fraction data, NormalDist.from_samples(data) has the same outcome as NormalDist(mean(data), stdev(data)): the correctly rounded exact mean and _float_sqrt_of_frac of the exact sample variance, the same OverflowError; fewer than two points raise."
    "Lib/statistics.py:1246-1249, 1759-1769; Doc/library/statistics.rst:918-919" ``FromSamplesTwin ``fromSamplesTwin_proven,
  re "from-samples-fmean" "calstat-statistics-from-samples-not-fmean-stdev" ["NormalDist.from_samples"]
    "For float data, from_samples(data) has the outcome of NormalDist(fmean(data), stdev(data)), as the documentation says."
    "Doc/library/statistics.rst:918-919" ``FromSamplesFmeanStdev ``fromSamplesFmeanStdev_refuted,
  re "from-samples-twin-floats" "calstat-statistics-from-samples-not-fmean-stdev" ["NormalDist.from_samples", "_mean_stdev"]
    "For float data, from_samples(data) has the outcome of NormalDist(mean(data), stdev(data))."
    "the Fraction twin from-samples-twin, extended to floats" ``FromSamplesTwinFloats ``fromSamplesTwinFloats_refuted,
  st "normaldist-hash-value" ["NormalDist.__hash__"]
    "With no NaN field, hash(NormalDist(mu, sigma)) is the tuple hash of the field hashes, and each finite non-zero field hashes as its exact value (the numeric hash: r * den = |num| mod 2**61-1, as hash(Fraction(x))); zeros hash 0, infinities +-314159; a NaN field hashes by identity, an input of the model."
    "Lib/statistics.py:1438-1440; Doc/library/stdtypes.rst, hashing of numeric types" ``NormalDistHashValue ``normalDistHashValue_proven,
  st "fmean-weights-arg" ["fmean"]
    "Weights that are not a list or tuple are copied by list() first, whose exception propagates before the data is read; a list or tuple (subclasses included) is iterated inside sumprod's try, so an exception of its iter() or of its iterator before the data ends becomes the length StatisticsError when it is a ValueError (under H) and comes out otherwise."
    "Lib/statistics.py:209-215" ``FmeanWeightsArg ``fmeanWeightsArg_proven,
  st "fmean-floats" ["fmean"]
    "If math.fsum is correctly rounded (the open mathint-fsum-correctly-rounded, a hypothesis), fmean of finite float data with a non-zero exact sum S is round(round(S) / n), for a sequence or an iterator."
    "Lib/statistics.py:183, 192-207" ``FmeanFloats ``fmeanFloats_proven,
  st "geometric-scan" ["geometric_mean"]
    "geometric_mean of positive data is exp(fsum(map(log, data)) / n) (NaN for a NaN sum); with zeros it is 0.0, or NaN when the sum of the logs of the positive items is NaN or +inf; the first negative item raises after the logs of the items before it; empty data raises."
    "Lib/statistics.py:225-262" ``GeometricScan ``geometricScan_proven,
  st "pdf-shape" ["NormalDist.pdf"]
    "For positive sigma, pdf is symmetric about mu (equal computed distances give equal densities, any exp), pdf(mu) is 1/(sqrt(tau)*sigma) given exp(-0.0) == 1, and pdf(+-inf) is 0.0 given exp(-inf) == 0."
    "Lib/statistics.py:1259-1265; C99 Annex F" ``PdfShape ``pdfShape_proven,
  st "linreg-centred" ["linear_regression"]
    "linear_regression(x, y) with an intercept is the regression through the origin of the centred data [xi - fmean(x)], [yi - fmean(y)], with intercept fmean(y) - slope * fmean(x); fsum(x) / n is fmean(x)."
    "Lib/statistics.py:790-805" ``LinRegCentred ``linRegCentred_proven,
  st "median-empty" ["median", "median_low", "median_high"]
    "median, median_low and median_high of empty data raise StatisticsError('no median for empty data')."
    "Lib/statistics.py:343-344, 369-370, 391-392" ``MedianEmpty ``medianEmpty_proven,
  st "quantiles-one" ["quantiles"]
    "quantiles of one data point, n >= 1, is that point repeated n - 1 times, whatever the method."
    "Lib/statistics.py:1199-1201" ``QuantilesOne ``quantilesOne_proven,
  st "convert-branches" ["_convert"]
    "_convert returns a float or Decimal (NaN and infinities included) of type T as it is, and turns a Fraction into a Decimal through T(numerator) / T(denominator), the 28-digit half-even rounding."
    "Lib/statistics.py:1624-1641" ``ConvertBranches ``convertBranches_proven,
  st "decimal-paths" ["mean", "variance", "pvariance", "stdev", "pstdev", "_convert"]
    "On finite Decimal data, mean and (p)variance are the exact values rounded to 28 digits and (p)stdev is _decimal_sqrt_of_frac of the exact variance."
    "docstring examples; Lib/statistics.py:628-629, 651-652" ``DecimalPaths ``decimalPaths_proven,
  st "too-few-points" ["variance", "pvariance", "stdev", "pstdev"]
    "variance and stdev of fewer than two points, pvariance and pstdev of no data, raise their StatisticsError."
    "Lib/statistics.py:562-563, 605-606, 620-621, 643-644" ``TooFewPoints ``tooFewPoints_proven,
  st "special-data" ["_sum", "_ss", "mean", "variance", "pvariance", "stdev", "pstdev"]
    "For float data with a NaN or infinity, _sum and _ss return the in-order sum s of the non-finite items (partials[None]); mean, variance, pvariance give s / n, s / (n-1), s / n; stdev and pstdev raise ValueError('inf or nan encountered in data')."
    "Lib/statistics.py:1499-1503, 1541-1545, 626-627, 649-650" ``SpecialData ``specialData_proven,
  st "exact-ratio-fallback" ["_exact_ratio"]
    "_exact_ratio of an object with numerator and denominator (not float, not Decimal) is that pair."
    "Lib/statistics.py:1614-1618" ``ExactRatioFallback ``exactRatioFallback_proven,
  st "pos-revalidates" ["NormalDist.__pos__"]
    "+X builds a new instance through __init__: a negative sigma (possible after __setstate__) raises StatisticsError, otherwise the fields are kept."
    "Lib/statistics.py:1416-1418" ``PosRevalidates ``posRevalidates_proven,
  st "pdf-one-sigma" ["NormalDist.pdf"]
    "When x - mu is exactly sigma, pdf(x) = exp(-0.5) / (sqrt(tau) * sigma), for any exp."
    "Lib/statistics.py:1264-1265" ``PdfOneSigma ``pdfOneSigma_proven,
  st "harmonic-weighted" ["harmonic_mean"]
    "For positive Fraction data and non-negative Fraction weights, harmonic_mean(data, weights) is sum(w) / sum(w/x) exactly; mismatched lengths and all-zero weights raise."
    "Lib/statistics.py:306-325; docstring example" ``HarmonicWeighted ``harmonicWeighted_proven,
  st "fail-neg-gen" ["_fail_neg"]
    "_fail_neg is a generator: it yields every value before the first negative one, then raises StatisticsError(errmsg), or ends; a comparison that raises ends it with that exception; consuming it gives the values or the first exception."
    "Lib/statistics.py:1644-1649" ``FailNegGen ``failNegGen_proven,
  st "multimode-order" ["multimode"]
    "multimode's result is a sublist of the data's first occurrences, in order, with no two items equal (== an equivalence)."
    "Lib/statistics.py:498-516 (docstring: in the order they were first encountered)" ``MultimodeOrder ``multimodeOrder_proven,
  st "harmonic-refusals" ["harmonic_mean"]
    "A single non-number raises TypeError('unsupported type'); a single negative int, Fraction, float or Decimal raises StatisticsError; a negative weight raises StatisticsError('harmonic mean does not support negative values') from _fail_neg(weights)."
    "Lib/statistics.py:297-314" ``HarmonicRefusals ``harmonicRefusals_proven,
  st "state-round-trip" ["NormalDist.__getstate__", "NormalDist.__setstate__"]
    "__getstate__ is the tuple of the two slots and __setstate__ of it restores them exactly; a 2-item state is stored unconverted; any other length raises the unpacking ValueError."
    "Lib/statistics.py:1445-1449" ``StateRoundTrip ``stateRoundTrip_proven
]

end PyLean.CoreLibs.CalStat
