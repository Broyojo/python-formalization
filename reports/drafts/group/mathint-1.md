<!-- title: Small inconsistencies in math found by a formal model -->
# Bug report

### Bug description

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped here so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. cmath.log(0, base) returns (-inf+nanj) instead of raising ValueError: the second c_log() call clears errno

cmath.log(0) raises ValueError('math domain error'), but cmath.log(0, 2) (or any finite nonzero base, e.g. cmath.log(0j, 10)) silently returns (-inf+nanj). cmath_log_impl sets errno = 0, computes x = c_log(x), which sets errno = EDOM for a zero argument (cmathmodule.c:615-622), then computes y = c_log(base), and c_log ends every non-special path with errno = 0 (:636). The EDOM of the first call is gone when the check `if (errno != 0)` runs at :971, so the quotient (-inf+0j)/(log(2)+0j) = (-inf+nanj) is returned. The real analogue math.log(0, 2) raises ValueError('expected a positive input'), and cmath.log(0) raises. The same masking hides any EDOM of c_log(x) whenever the base is a finite nonzero number; a base of 0 still raises because its own c_log sets EDOM last.

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

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Drafted with AI assistance (Claude); each case was reproduced on 3.15.2 and on main and the report reviewed before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
