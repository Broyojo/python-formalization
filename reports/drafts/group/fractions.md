<!-- title: fractions: 2 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. format(Fraction, '.2e') raises ValueError (int string-conversion limit) for values with more than 4300-digit numerator or denominator

For presentation types e, E, g, G, _round_to_figures finds the decimal magnitude of n/d
with str(abs(n)) and str(d). When either has more than 4300 digits this raises
ValueError ("Exceeds the limit (4300 digits) for integer string conversion"), although
the requested output is a handful of characters. Example:
format(Fraction(10**4300 + 1, 10**4300), '.2e') should be '1.00e+00';
format(Fraction(1, 3**10000), '.3e') fails the same way. format(Decimal(10**4400), '.3e')
works, format(Fraction(10**4400), '.3e') does not.

<details><summary>Reproducer</summary>

```python
from fractions import Fraction
x = Fraction(10**4300 + 1, 10**4300)
try:
    got = format(x, '.2e')
except ValueError as e:
    got = 'ValueError: ' + str(e)[:40]
print("format(Fraction(10**4300 + 1, 10**4300), '.2e') ->", got)
```

</details>

#### 2. Fraction(n, 0) raises ValueError instead of ZeroDivisionError when n has more than 4300 digits

The zero-denominator check builds its message with 'Fraction(%s, 0)' % numerator.
For a numerator with more than sys.get_int_max_str_digits() (default 4300) decimal
digits, formatting the message raises ValueError ("Exceeds the limit (4300 digits) for
integer string conversion"), so the documented ZeroDivisionError is never raised and
`except ZeroDivisionError` does not catch the error.

<details><summary>Reproducer</summary>

```python
from fractions import Fraction
def kind(n):
    try:
        Fraction(n, 0)
        return 'no error'
    except Exception as e:
        return type(e).__name__
big, small = kind(10**4300), kind(10**4299)
print('Fraction(10**4300, 0) ->', big)
print('Fraction(10**4299, 0) ->', small)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
