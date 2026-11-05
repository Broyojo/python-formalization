<!-- title: Small inconsistencies in int found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. str(int) can return more digits than sys.set_int_max_str_digits allows when the limit is 9000 or more

long_to_decimal_string_internal guards the digit limit twice: a rough pre-check on the number of 30-bit digits (lines 2125-2135), and an exact check on the computed decimal length (lines 2207-2217). Since _pylong was added, values of more than 1000 30-bit digits switch to _pylong.int_to_decimal_string (lines 2138-2145) right after the pre-check, so the exact check never runs for them. The pre-check only fires when max_str_digits // 90 <= (size_a - 11) // 10; it is deliberately loose (10/3 against log2(10)), and it was written when the exact check always followed. For a limit of 9000 or more some values of more than 1000 digits pass it, and str() returns all their digits. With sys.set_int_max_str_digits(10000), str(10**10050) returns a 10051-digit string, and int() of that string then raises the limit ValueError, so the output does not round-trip under the same limit. repr(), f-strings, "%d" and b"%d" go through the same function and behave the same way. Below 9000 (the default 4300 included) the pre-check fires on every value that takes the _pylong path, so the limit holds exactly.

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
if len(s) > 10000 and back.startswith('ValueError') and small == 'ValueError':
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
