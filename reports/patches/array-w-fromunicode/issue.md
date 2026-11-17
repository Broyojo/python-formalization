<!-- title: array: fromunicode('') on an empty 'w' array raises SystemError -->
### Bug report

`array.array('w').fromunicode('')` raises `SystemError` instead of doing nothing. It happens when the array has no item buffer yet (for example `array('w')` or `array('w', [])`), or after its buffer was freed by shrinking it to zero length. Calling `fromunicode('')` on a non-empty `'w'` array works, as does the same call on a `'u'` array in 3.15.

```python
import array

a = array.array('w')
a.fromunicode('')
```

Actual (3.15.2 release build):

```
Traceback (most recent call last):
  File "repro.py", line 4, in <module>
    a.fromunicode('')
    ~~~~~~~~~~~~~^^^^
SystemError: <method 'fromunicode' of 'array.array' objects> returned a result with an exception set
```

A debug build of main aborts instead: `Modules/arraymodule.c:1989: array_array_fromunicode_impl: Assertion 'u != NULL' failed.`

Expected: `None`, with the array still empty, the same as `array.array('w', 'x').fromunicode('')` leaving the array unchanged.

The cause is in `array_array_fromunicode_impl`: for an empty string, `array_resize()` keeps `ob_item` as `NULL`, and `PyUnicode_AsUCS4()` is then called with a `NULL` buffer. It rejects that with `PyErr_BadInternalCall()`, and the result is ignored because the call is marked "must not fail". The `'u'` branch in 3.15 already skips the copy for an empty string.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [sequences-array-w-fromunicode-empty](https://github.com/Broyojo/python-formalization/blob/main/bugs/sequences-array-w-fromunicode-empty.yaml)
