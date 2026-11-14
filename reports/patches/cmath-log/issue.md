<!-- title: cmath.log(0, base) returns (-inf+nanj) instead of raising ValueError -->
### Bug report

`cmath.log(0)` raises `ValueError`, but `cmath.log(0, base)` returns a value such as `(-inf+nanj)` for most bases. In `cmath_log_impl`, the domain error from `c_log(z)` is stored in `errno`, and the second call `c_log(base)` resets `errno` to 0 before it is checked.

```python
import cmath, math

cmath.log(0)       # ValueError: math domain error
cmath.log(0, 2)    # (-inf+nanj)
cmath.log(0, -1)   # (nan+infj)
math.log(0, 2)     # ValueError: expected a positive input
```

Expected: `cmath.log(0, base)` raises `ValueError: math domain error`, the same as `cmath.log(0)` and `math.log(0, 2)`. A zero or one base already raises (`cmath.log(2, 0)`, `cmath.log(2, 1)`), because there the error comes from the second call or from the division.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [mathint-cmath-log-base-errno](https://github.com/Broyojo/python-formalization/blob/main/bugs/mathint-cmath-log-base-errno.yaml)
