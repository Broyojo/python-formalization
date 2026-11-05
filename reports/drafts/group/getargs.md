<!-- title: getargs: 1 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. A non-ASCII type name cut by snprintf turns argument and MRO TypeErrors into UnicodeDecodeError

Two error paths build their message with PyOS_snprintf into a char buffer and then call
PyErr_SetString, which decodes the buffer strictly as UTF-8. The C library's "%.50s" (and the
1000-byte buffer of set_mro_error) cut bytes, not characters, so a non-ASCII class name whose
cut falls inside a character leaves an incomplete UTF-8 sequence at the end of the buffer.
PyUnicode_FromString then fails and its UnicodeDecodeError is the exception that propagates.
The TypeError the code meant to raise is lost.
- getargs.c converterr: every PyArg_Parse* format unit that rejects an argument by type prints
  "must be %.50s, not %.50s" with the argument's tp_name. Reached from Python by, for example,
  json.dumps([1], separators=(T(), ':')), which passes the separator to c_make_encoder's "U"
  unit, with type(T()).__name__ == 'a' + 'é' * 30. It raises "UnicodeDecodeError: 'utf-8' codec
  can't decode byte 0xc3 in position 92: unexpected end of data" instead of "TypeError:
  make_encoder() argument 6 must be str, not aéé...". With a 3-byte character cut after two
  bytes ('中' * 30) the message is "can't decode bytes in position 91-92".
- typeobject.c set_mro_error: an MRO conflict whose message passes 999 bytes inside a character
  of a candidate's name raises UnicodeDecodeError at position 998 instead of "TypeError: Cannot
  create a consistent method resolution order (MRO) for bases ...".
PyErr_Format's own "%.50s" (unicode_fromformat_write_utf8) drops an incomplete final sequence,
which is why _PyArg_BadArgument, the Argument Clinic twin of converterr, gets this right:
heapq.heappush(T(), 1) prints 'a' and 24 'é'.

<details><summary>Reproducer</summary>

```python
import json

def kind(f):
    try:
        f()
    except Exception as e:
        return type(e).__name__
    return None

# Site 1, converterr: 'a' + 30 'é' is 61 bytes; byte 50 is the first byte of the 25th 'é'.
T = type('a' + 'é' * 30, (), {})
U = type('a' + 'é' * 23, (), {})  # 47 bytes, no cut: the TypeError
r1 = kind(lambda: json.dumps([1], separators=(T(), ':')))
r1_control = kind(lambda: json.dumps([1], separators=(U(), ':')))

# Site 2, set_mro_error: candidates 'a' + 500 'é' and B; byte 998 starts an 'é'.
def conflict(name):
    A = type(name, (), {})
    B = type('B', (), {})
    X = type('X', (A, B), {})
    Y = type('Y', (B, A), {})
    return kind(lambda: type('Z', (X, Y), {}))
r2 = conflict('a' + 'é' * 500)
r2_control = conflict('é' * 500)  # byte 998 ends an 'é': the TypeError

print(r1, r1_control, r2, r2_control)
if (r1, r1_control, r2, r2_control) == ('UnicodeDecodeError', 'TypeError',
                                        'UnicodeDecodeError', 'TypeError'):
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
