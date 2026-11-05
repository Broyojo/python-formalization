<!-- title: mathint: 4 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. cmath.isclose calls a number with a NaN part close when the other part's difference overflows and a tolerance is infinite

The docstring says "NaN is not close to anything, even itself". cmath.isclose(complex(nan,
1e308), complex(0.0, -1e308), abs_tol=inf) returns True: the imaginary difference 2e308
overflows to inf, _Py_c_abs returns inf for (nan, inf) (C99's hypot(inf, nan) = inf), and
inf <= abs_tol. rel_tol=inf does the same. math.isclose(nan, 0, abs_tol=inf) is False.

<details><summary>Reproducer</summary>

```python
import cmath, math
r = cmath.isclose(complex(math.nan, 1e308), complex(0.0, -1e308), abs_tol=math.inf)
print('isclose:', r)
```

</details>

#### 2. cmath.log(0, base) returns (-inf+nanj) instead of raising ValueError: the second c_log() call clears errno

cmath.log(0) raises ValueError('math domain error'), but cmath.log(0, 2) (or any finite
nonzero base, e.g. cmath.log(0j, 10)) silently returns (-inf+nanj). cmath_log_impl sets
errno = 0, computes x = c_log(x), which sets errno = EDOM for a zero argument
(cmathmodule.c:615-622), then computes y = c_log(base), and c_log ends every non-special path
with errno = 0 (:636). The EDOM of the first call is gone when the check `if (errno != 0)`
runs at :971, so the quotient (-inf+0j)/(log(2)+0j) = (-inf+nanj) is returned. The real
analogue math.log(0, 2) raises ValueError('expected a positive input'), and cmath.log(0)
raises. The same masking hides any EDOM of c_log(x) whenever the base is a finite nonzero
number; a base of 0 still raises because its own c_log sets EDOM last.

<details><summary>Reproducer</summary>

```python
import cmath
try:
    cmath.log(0)
    one = 'no error'
except ValueError as e:
    one = 'ValueError: ' + str(e)
try:
    two = repr(cmath.log(0, 2))
except ValueError as e:
    two = 'ValueError: ' + str(e)
print('log(0):', one, ' log(0, 2):', two)
```

</details>

#### 3. cmath.phase(z) raises OverflowError('math range error') when atan2 underflows, unlike math.atan2

The docs say phase(z) is equivalent to math.atan2(z.imag, z.real). With glibc, atan2(1e-300,
1e300) underflows to 0.0 and sets errno = ERANGE (C23 7.12.4.4 allows a range error there).
math.atan2 goes through math_2/is_error, which ignores ERANGE for results below 1.5 in
magnitude, and returns 0.0. cmath_phase_impl passes any nonzero errno to math_error, so
cmath.phase(complex(1e300, 1e-300)) raises OverflowError('math range error') for a result
that is a tiny angle. cmath.polar of the same z returns (1e300, 0.0), because 3.15 moved
`errno = 0` after polar's atan2.

<details><summary>Reproducer</summary>

```python
import cmath, math
z = complex(1e300, 1e-300)
a = math.atan2(z.imag, z.real)
try:
    p = repr(cmath.phase(z))
except OverflowError as e:
    p = 'OverflowError: ' + str(e)
print('math.atan2:', a, ' cmath.phase:', p)
```

</details>

#### 4. math.nextafter(x, y) and math.nextafter(x, y, steps=1) return zeros of opposite sign when the step lands on y's zero

The docstring says "If steps is not specified or is None, it defaults to 1", and the docs
describe nextafter(x, y, steps) as the value `steps` steps after x towards y. Without
`steps`, math.nextafter calls the C library's nextafter(), which steps from -5e-324 towards
0.0 to -0.0 (the C standard's next representable value in that direction; glibc and IEEE
754 nextUp agree). With steps=1, the bit-twiddling path of math_nextafter_impl sees that
the distance from x to y in units in the last place is ax + ay = 1 + 0 <= steps and returns
y itself, +0.0. So nextafter(-5e-324, 0.0) is -0.0 but nextafter(-5e-324, 0.0, steps=1) is
0.0, and symmetrically nextafter(5e-324, -0.0) is 0.0 but with steps=1 it is -0.0. The same
happens for any steps that lands exactly on a zero y of the other sign (e.g. x=-1e-323,
steps=2): the iterated single steps end on -0.0, the steps path on +0.0. The two results
compare equal, so only code that looks at the sign of zero (copysign, 1/x, repr, atan2) sees
it. Every other case agrees bit for bit, as the Lean model of the steps path shows.

<details><summary>Reproducer</summary>

```python
import math
a = math.nextafter(-5e-324, 0.0)
b = math.nextafter(-5e-324, 0.0, steps=1)
c = math.nextafter(5e-324, -0.0)
d = math.nextafter(5e-324, -0.0, steps=1)
print('no steps:', repr(a), repr(c), ' steps=1:', repr(b), repr(d))
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
