<!-- title: binascii.b2a_qp() and quopri write lines longer than 76 characters when a line ends with whitespace -->
### Bug report

`binascii.b2a_qp()` inserts soft line breaks so that encoded lines are at most 76 characters, as RFC 2045 requires. A space or tab just before a line break is first counted as one character and then rewritten as `=20` or `=09`, so a line that was 75 or 76 characters long before the break comes out as 77 or 78. `quopri.encodestring()` and the `quopri_codec` use `b2a_qp()`, and the pure-Python encoder in `quopri` (used when `binascii` is not available) has the same problem.

```python
import binascii

for data in (b'a' * 75 + b' \n', b'a' * 74 + b'\t\n', b'a' * 74 + b' \r\n'):
    out = binascii.b2a_qp(data)
    print([len(line) for line in out.splitlines()])
```

Actual:

```
[78]
[77]
[77]
```

Expected: no line longer than 76 characters, with a soft line break before the whitespace, for example `b'a' * 75 + b'=\n=20\n'` for the first input. This is what `b2a_qp()` already does when the whitespace is at the very end of the data: `binascii.b2a_qp(b'a' * 75 + b' ')` returns `b'a' * 75 + b'=\n=20'`.

The pure-Python encoder gives the same 78 and 77 for the first two inputs, and also 78 for `b'a' * 75 + b' '`:

```python
import quopri
quopri.b2a_qp = None  # force the pure-Python encoder
print([len(line) for line in quopri.encodestring(b'a' * 75 + b' \n').splitlines()])  # [78]
```

A related case in binary mode: `binascii.b2a_qp(b'a' * 76 + b'\n', istext=False)` returns a 77-character first line (`b'a' * 76 + b'=\n=0A'`). The check that skips the soft line break before a newline does not look at `istext`, but with `istext=False` the newline is encoded, so a soft line break follows anyway.

In all cases the output still decodes to the original data; the problem is only the line length.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [textlibs-binascii-qp-line-length](https://github.com/Broyojo/python-formalization/blob/main/bugs/textlibs-binascii-qp-line-length.yaml)
