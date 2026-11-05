<!-- title: longobj: 5 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. complex(x) ignores __float__ on a float subclass, while complex(x, 0) and float(x) call it

The 3.14 split of the constructor made complex(x) convert through PyFloat_AsDouble
(line 1141), which reads a float subclass's value directly, while complex(x, 0) and
complex(real=x) still use PyNumber_Float (line 1256), which calls __float__. So for a
float subclass overriding __float__, complex(x) and complex(x, 0) give different real
parts. complex(x) now also disagrees with float(x). In 3.13 every path went through
PyNumber_Float, so this is a behaviour change.

<details><summary>Reproducer</summary>

```python
class F(float):
    def __float__(self):
        return 42.0
x = F(1.0)
one, two, kw, fl = complex(x), complex(x, 0), complex(real=x), float(x)
print('complex(x)      ->', one)
print('complex(x, 0)   ->', two)
print('complex(real=x) ->', kw)
print('float(x)        ->', fl)
```

</details>

#### 2. complex(1e-200) ** -2 raises ZeroDivisionError: zero to a negative or complex power, for a nonzero base

For an integer exponent n with -100 <= n < 0, c_powi computes 1 / x**-n. When x**-n
underflows to 0, the division sets EDOM, which complex_pow reports as a zero base. The
base is not zero, and the true result overflows, so the exception has the wrong type
and the wrong message. The two paths in complex_pow disagree on the same value:
complex(1e-200) ** -2 raises ZeroDivisionError, while complex(1e-200) ** -2.5, on the
slow path, raises OverflowError, as float does: 1e-200 ** -2 is OverflowError.

<details><summary>Reproducer</summary>

```python
def kind(f):
    try:
        return repr(f())
    except Exception as e:
        return type(e).__name__
z = complex(1e-200)
fast, slow, real = kind(lambda: z ** -2), kind(lambda: z ** -2.5), kind(lambda: 1e-200 ** -2)
print('complex(1e-200) ** -2   ->', fast)
print('complex(1e-200) ** -2.5 ->', slow)
print('1e-200 ** -2            ->', real)
```

</details>

#### 3. complex(1e308, 1e308) / complex(inf, inf) is nan+0j, not 0j

gh-119372 added the C11 Annex G.5.2 recoveries to _Py_c_quot so that a finite number over
a complex infinity is a zero: (1+1j)/(inf+infj) is 0j. The zero recovery computes
0.0 * (a.real*x + a.imag*y) with x and y the boxed signs of the divisor's parts. When both
divisor parts are infinite, x and y are both +-1, and a.real*x + a.imag*y can overflow to
an infinity even though a is finite; 0.0 * inf is a NaN. So complex(1e308, 1e308) /
complex(inf, inf) is nan+0j, and complex(1e308, -1e308) / complex(inf, inf) is nanj
(real 0, imaginary NaN).

<details><summary>Reproducer</summary>

```python
import sys
r = complex(1e308, 1e308) / complex(float('inf'), float('inf'))
print(sys.version.split()[0], r)
```

</details>

#### 4. float('inf') / (1e308+1e308j) is nan+nanj, but complex('inf') / (1e308+1e308j) is inf-infj

_Py_rc_quot, new in 3.14, is commented as "an equivalent of _Py_c_quot() function, when
1st argument is real". _Py_c_quot has two recovery branches for a nan+nanj result, and
_Py_rc_quot has only the second. The first handles an infinite dividend over a finite
divisor. It looks unreachable for a real dividend, but it is reachable when Smith's
denominator overflows: inf / inf is NaN in both parts. So a float infinity divided by a
large finite complex gives nan+nanj, while the same value as a complex gives an
infinity, as C11 Annex G.5.2 asks.

<details><summary>Reproducer</summary>

```python
inf = float('inf')
b = 1e308 + 1e308j
r, c = inf / b, complex(inf, 0) / b
print('float  ->', r)
print('complex ->', c)
```

</details>

#### 5. str(int) can return more digits than sys.set_int_max_str_digits allows when the limit is 9000 or more

long_to_decimal_string_internal guards the digit limit twice: a rough pre-check on the
number of 30-bit digits (lines 2125-2135), and an exact check on the computed decimal
length (lines 2207-2217). Since _pylong was added, values of more than 1000 30-bit
digits switch to _pylong.int_to_decimal_string (lines 2138-2145) right after the
pre-check, so the exact check never runs for them. The pre-check only fires when
max_str_digits // 90 <= (size_a - 11) // 10; it is deliberately loose (10/3 against
log2(10)), and it was written when the exact check always followed. For a limit of
9000 or more some values of more than 1000 digits pass it, and str() returns all their
digits. With sys.set_int_max_str_digits(10000), str(10**10050) returns a 10051-digit
string, and int() of that string then raises the limit ValueError, so the output does
not round-trip under the same limit. repr(), f-strings, "%d" and b"%d" go through the
same function and behave the same way. Below 9000 (the default 4300 included) the
pre-check fires on every value that takes the _pylong path, so the limit holds exactly.

<details><summary>Reproducer</summary>

```python
import sys
sys.set_int_max_str_digits(10000)
n = 10 ** 10050
s = str(n)
print('limit', sys.get_int_max_str_digits(), 'len(str(10**10050)) =', len(s))
try:
    int(s)
    back = 'ok'
except ValueError as e:
    back = 'ValueError: ' + str(e)[:60]
print('int(str(n)) ->', back)
sys.set_int_max_str_digits(5000)
try:
    str(10 ** 5010)
    small = 'no error'
except ValueError:
    small = 'ValueError'
print('limit 5000, str(10**5010) ->', small)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
