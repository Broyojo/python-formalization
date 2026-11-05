<!-- title: Small inconsistencies in calendar and statistics found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. statistics._sqrtprod loses accuracy when x*y is subnormal, so correlation() of exactly linear data is far from 1

`_sqrtprod(x, y)` promises sqrt(x * y) "with improved accuracy and without overflow/underflow". It rescales only when `sqrt(x * y)` overflows to inf or underflows to exactly 0.0. When the product lands in the subnormal range it keeps as few as one or two significant bits, and the differential correction cannot recover them, because `sumprod((x, h), (y, -h))` underflows the same way. `_sqrtprod(10 * 2**-540, 10 * 2**-538)` returns 9.79... * 2**-539 instead of the exact 10 * 2**-539 (2% low); in a scan, the relative error reaches 41%.

*May be intended:* Possibly regarded as an accepted float limitation; a maintainer has rejected subnormal-input reports before (python/cpython#158786). Here the inputs are normal floats, and the function exists to handle underflow: it already rescales by 2**537 when the product underflows to zero, it just does not do so when the product is merely subnormal. The rescaling came with PR #107855 ("Extend _sqrtprod() to cover the full range of inputs"); in its review Serhiy Storchaka doubted it was worth going so far, since under/overflow can occur outside _sqrtprod in computing its inputs, and Raymond Hettinger answered that the module's ethos is "to aim for perfection almost regardless of cost". The differential correction came with PR #107781 ("Minor accuracy improvement for statistics.correlation()"). The tests added with #107855 (Lib/test/test_statistics.py:2768-2772) check only `sys.float_info.min * sys.float_info.epsilon`, whose product underflows to exactly zero, and `sys.float_info.max`; no subnormal non-zero product is tested.

<details><summary>Reproducer</summary>

```python
import statistics, math
x = [math.ldexp(i, -270) for i in range(1, 6)]   # 1..5 times 2**-270, all normal floats
y = [2 * v for v in x]                            # exactly proportional
r = statistics.correlation(x, y)
s = statistics._sqrtprod(10 * 2.0**-540, 10 * 2.0**-538)
print(r, s, s == 10 * 2.0**-539)
print(statistics.correlation([1e-100, 2e-100, 3e-100], [1e-62, 2e-62, 3e-62]))
if abs(r - 1.0) > 1e-12 and s != 10 * 2.0**-539:
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
