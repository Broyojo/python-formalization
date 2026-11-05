<!-- title: unicodeobj: 2 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. A separator after the precision is silently ignored by str and the integer types, which refuse it after the width

Since 3.14 a ',' or '_' may follow the precision, to group the digits of the fractional part.
parse_internal_render_format_spec validates the separator after the width against the type
(unicode_formatter.c:566-594: "Cannot specify ',' with 's'." and so on), but the separator after
the precision only against 'n' (:596-602). Every other type takes it and ignores it:
format('abc', '.,') == 'abc', format('abc', '.2_s') == 'ab', format(255, '.,x') == 'ff',
format(65, '._c') == 'A', format(1234, '.,') == '1234', while format('abc', ',') and
format(255, ',x') raise ValueError. For the integer types the '.' also slips past "Precision not
allowed in integer format specifier", because a '.' followed only by a separator leaves the
precision at -1 (:501-520). Fraction and _pydecimal refuse '.,s' as an invalid format string.

<details><summary>Reproducer</summary>

```python
def f(x, s):
    try:
        return format(x, s)
    except ValueError:
        return 'ValueError'
got = (f('abc', ','), f('abc', '.,'), f('abc', '.2_s'), f(255, ',x'), f(255, '.,x'),
       f(65, ',c'), f(65, '._c'), f(1.5, '.,n'))
print(ascii(got))
```

</details>

#### 2. format(float/complex, spec) accepts a literal NUL as the presentation type, unlike int, str, Fraction and _pydecimal

parse_internal_render_format_spec stores '\0' in format.type when the type field is absent, and
takes the last character of the spec as the type otherwise. The float and complex writers then
treat case '\0' as "no format code", so a literal NUL type character is read as no type:
format(1.5, '\x00') == '1.5', format(1+2j, '\x00') == '(1+2j)', format(1.5, '>8\x00') pads, and
format(1.5, '.2\x00') == '1.5'. The same spec raises ValueError("Unknown format code '\x0' for
object of type 'int'") for int, and for str; Fraction and _pydecimal raise "Invalid format
specifier". The C _decimal raises for '\x00' alone but accepts '>8\x00' and '.2\x00', and stops
at the NUL ('.2f\x00garbage!' formats as '.2f').

<details><summary>Reproducer</summary>

```python
from fractions import Fraction
def f(x, s):
    try:
        return format(x, s)
    except ValueError:
        return 'ValueError'
got = (f(1.5, '\x00'), f(1+2j, '\x00'), f(1.5, '>8\x00'), f(1, '\x00'), f('a', '\x00'),
       f(Fraction(3, 2), '\x00'))
print(ascii(got))
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
