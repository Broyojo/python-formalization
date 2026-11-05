<!-- title: calstat: 4 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. statistics._decimal_sqrt_of_frac rounds an exact halfway root down to an odd digit, so stdev/pstdev of Decimals is not half-even

`_decimal_sqrt_of_frac(n, m)` promises "Square root of n/m as a Decimal, correctly rounded". It
computes `(Decimal(n) / Decimal(m)).sqrt()` and then moves one step up or down when n/m lies
strictly beyond the midpoint to a neighbour. When the root lies exactly on that midpoint neither
strict test fires, and the first estimate is kept whatever its last digit. In the default context
(28 digits, ROUND_HALF_EVEN) `pstdev([Decimal(0), Decimal('2.000000000000000000000000003')])` is
exactly 1.0000000000000000000000000015 and should round to ...002; it returns
1.000000000000000000000000001.

<details><summary>Reproducer</summary>

```python
import statistics
from decimal import Decimal as D
from fractions import Fraction as F
r = statistics.pstdev([D(0), D('2.000000000000000000000000003')])
exact = F(2000000000000000000000000003, 2 * 10**27)   # 1.0000000000000000000000000015, a tie
d = statistics._decimal_sqrt_of_frac(exact.numerator ** 2, exact.denominator ** 2)
print(r, d)
```

</details>

#### 2. NormalDist.from_samples is documented as using fmean() and stdev() but uses neither

The documentation says from_samples "Makes a normal distribution instance with mu and sigma
parameters estimated from the data using fmean() and stdev()". The code calls `_mean_stdev`, which
differs from both in two observable ways:
* mu is the exact mean correctly rounded (what `mean()` gives), not `fmean()`:
  `NormalDist.from_samples([0.1, 0.1, 0.1]).mean` is 0.1 while `fmean([0.1, 0.1, 0.1])` is
  0.10000000000000002. The difference is in the last bit, and from_samples is the more accurate.
* with a NaN or infinity in the data, `_mean_stdev` "handles Nans and Infs gracefully" and returns
  NaN parameters, while `stdev()` raises: `NormalDist.from_samples([nan, 1.0])` is
  `NormalDist(mu=nan, sigma=nan)`, `stdev([nan, 1.0])` raises
  `ValueError('inf or nan encountered in data')`.

<details><summary>Reproducer</summary>

```python
import statistics, math
X = statistics.NormalDist.from_samples([0.1, 0.1, 0.1])
f = statistics.fmean([0.1, 0.1, 0.1])
Y = statistics.NormalDist.from_samples([math.nan, 1.0])
try:
    statistics.stdev([math.nan, 1.0])
    raised = False
except ValueError:
    raised = True
print(X.mean, f, Y, raised)
```

</details>

#### 3. statistics.quantiles(method='inclusive') gives cut points above the maximum of constant float data

With `method='inclusive'` the data's minimum and maximum are documented as the 0th and 100th
percentiles, so every cut point should lie between them. The interpolation
`(data[j] * (n - delta) + data[j + 1] * delta) / n` rounds three times, and for constant data it need
not give back the constant: `quantiles([0.1, 0.1], n=3, method='inclusive')` is
`[0.10000000000000002, 0.10000000000000002]`, above the maximum 0.1. The same rounding makes the cut
points of sorted data non-monotone, which is the open issue python/cpython#150318.

<details><summary>Reproducer</summary>

```python
import statistics
q = statistics.quantiles([0.1, 0.1], n=3, method='inclusive')
print(q)
```

</details>

#### 4. statistics._sqrtprod loses accuracy when x*y is subnormal, so correlation() of exactly linear data is far from 1

`_sqrtprod(x, y)` promises sqrt(x * y) "with improved accuracy and without overflow/underflow".
It rescales only when `sqrt(x * y)` overflows to inf or underflows to exactly 0.0. When the
product lands in the subnormal range it keeps as few as one or two significant bits, and the
differential correction cannot recover them, because `sumprod((x, h), (y, -h))` underflows the
same way. `_sqrtprod(10 * 2**-540, 10 * 2**-538)` returns 9.79... * 2**-539 instead of the exact
10 * 2**-539 (2% low); in a scan, the relative error reaches 41%.

<details><summary>Reproducer</summary>

```python
import statistics, math
x = [math.ldexp(i, -270) for i in range(1, 6)]   # 1..5 times 2**-270, all normal floats
y = [2 * v for v in x]                            # exactly proportional
r = statistics.correlation(x, y)
s = statistics._sqrtprod(10 * 2.0**-540, 10 * 2.0**-538)
print(r, s, s == 10 * 2.0**-539)
print(statistics.correlation([1e-100, 2e-100, 3e-100], [1e-62, 2e-62, 3e-62]))
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
