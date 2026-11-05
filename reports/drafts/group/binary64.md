<!-- title: binary64: 3 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. float // and divmod miss the exact floor for quotients above about 2**51, in both directions

_float_div_mod computes the remainder exactly with fmod, then gets the quotient by
rounding (vx - mod) / wx in floating point. For quotients above about 2**51 the two
roundings can move it past the nearest integer, and the "snap" step keeps the wrong one.
574432016605032.2 // 0.24012708848409187 returns 2392199981398964.0, but the exact floor
is 2392199981398965, which is below 2**52 and exactly representable. The documentation of
divmod says q is usually math.floor(a / b) "but may be 1 less"; q can also be one more,
and for quotients above 2**52 two less. Since x % y is the exact remainder, the pair from
divmod can miss the identity q * y + r == x by a whole y in exact arithmetic.

<details><summary>Reproducer</summary>

```python
import math
from fractions import Fraction as F
x, y = 574432016605032.2, 0.24012708848409187
q, r = divmod(x, y)
exact = math.floor(F(x) / F(y))
print('x // y =', x // y, ' exact floor =', exact)
a = float.fromhex('-0x1.765b303d50491p+51')
b = float.fromhex('0x1.b92103f617877p-2')
print('a // b =', a // b, ' floor(a / b) =', math.floor(a / b))
c = float.fromhex('0x1.4e16a2c34ecadp+53')
d = float.fromhex('0x1.5e87688daf401p+0')
print('c // d =', c // d, ' floor(c / d) =', math.floor(c / d))
if (exact < 2 ** 52 and q != float(exact) and x // y == float(exact) - 1
        and a // b == float(math.floor(a / b)) + 1
        and c // d == float(math.floor(c / d)) - 2):
```

</details>

#### 2. float.fromhex raises OverflowError instead of ValueError for a malformed string with a large exponent

float.fromhex checks the end of the string only at the `finished:` label. A value that
overflows jumps to `overflow_error` first, so '1p2000x' raises OverflowError although the
string is not a hexadecimal float at all, while '1p-2000x', '1p5x' and 'x' all raise
ValueError. Whether a malformed string is reported as malformed depends on the magnitude
of the prefix.

<details><summary>Reproducer</summary>

```python
def outcome(s):
    try:
        return float.fromhex(s)
    except Exception as e:
        return type(e).__name__
print('1p2000x  ->', outcome('1p2000x'))
print('1p1024 z ->', outcome('1p1024 z'))
print('1p-2000x ->', outcome('1p-2000x'))
print('1p5x     ->', outcome('1p5x'))
if (outcome('1p2000x') == 'OverflowError' and outcome('1p1024 z') == 'OverflowError'
        and outcome('1p-2000x') == 'ValueError' and outcome('1p5x') == 'ValueError'):
```

</details>

#### 3. struct.unpack('<f') quiets a signaling NaN on a little-endian host, while struct.unpack('>f') keeps it

On a little-endian host, struct.unpack('<f', b) and struct.unpack('>f', b[::-1]) read the same
binary32 and disagree when it is a signaling NaN. '>f' reaches PyFloat_Unpack4, which restores
the signaling bit after the conversion to double. '<f' and '=f' now reach nu_float, which does a
plain (double)x, and that conversion sets the quiet bit. So 0x7f89b33c unpacks to
0x7ff9366780000000 through '<f' and to 0x7ff1366780000000 through '>f', and
struct.pack('<f', struct.unpack('<f', b)[0]) no longer gives b back. On a big-endian host the
same split would hit '>f' instead.
Before 3.15 the endian tables skipped 'f' and 'd', so '<f' went through PyFloat_Unpack4 on every
host. gh-145633 removed that exception along with the unknown_format code, and only native 'f'
had the plain conversion before.

<details><summary>Reproducer</summary>

```python
import struct, sys
raw = bytes.fromhex('3cb3897f')          # little-endian bytes of the signaling NaN 0x7f89b33c
bits = lambda x: struct.pack('>d', x).hex()
host, other = ('<f', '>f') if sys.byteorder == 'little' else ('>f', '<f')
data = raw if host == '<f' else raw[::-1]
a = struct.unpack(host, data)[0]
b = struct.unpack(other, data[::-1])[0]
print(host, '->', bits(a))
print(other, '->', bits(b))
print('pack of the', host, 'result ->', struct.pack(host, a).hex(), 'from', data.hex())
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
