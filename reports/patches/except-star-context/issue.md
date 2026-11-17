<!-- title: except* and ExceptionGroup.split() hide the group's __context__ in tracebacks -->
### Bug report

`BaseExceptionGroup.split()` and `subgroup()` copy `__context__` and `__cause__` from the original group to each part, but they also set `__suppress_context__` on every part, even when the original group has it unset. Because `except*` builds the group it re-raises with `split()`, a group that is only partly handled by `except*` inside an `except` block loses the "During handling of the above exception, another exception occurred" section from its traceback. A plain `except` that does not match the group keeps that section.

```python
def f():
    try:
        raise ValueError("context")
    except ValueError:
        try:
            raise ExceptionGroup("eg", [TypeError(1), KeyError(2)])
        except* TypeError:
            pass

f()
```

Actual output (3.15 and main):

```
  + Exception Group Traceback (most recent call last):
  |   File "repro.py", line 10, in <module>
  |     f()
  |     ~^^
  |   File "repro.py", line 6, in f
  |     raise ExceptionGroup("eg", [TypeError(1), KeyError(2)])
  | ExceptionGroup: eg (1 sub-exception)
  +-+---------------- 1 ----------------
    | KeyError: 2
    +------------------------------------
```

Expected output (what you get if `except* TypeError` is replaced by `except TypeError`, apart from the number of sub-exceptions):

```
Traceback (most recent call last):
  File "repro.py", line 3, in f
    raise ValueError("context")
ValueError: context

During handling of the above exception, another exception occurred:

  + Exception Group Traceback (most recent call last):
  |   File "repro.py", line 10, in <module>
  |     f()
  |     ~^^
  |   File "repro.py", line 6, in f
  |     raise ExceptionGroup("eg", [TypeError(1), KeyError(2)])
  | ExceptionGroup: eg (1 sub-exception)
  +-+---------------- 1 ----------------
    | KeyError: 2
    +------------------------------------
```

The same at the attribute level:

```python
try:
    raise ValueError("context")
except ValueError:
    try:
        raise ExceptionGroup("eg", [TypeError(1), KeyError(2)])
    except ExceptionGroup as e:
        match, rest = e.split(TypeError)
        print(e.__suppress_context__, match.__suppress_context__, rest.__suppress_context__)
        # False True True    (expected: False False False)
        print(match.__context__ is e.__context__)
        # True
```

The cause is in `exceptiongroup_subset()` in `Objects/exceptions.c`, which copies the cause with `PyException_SetCause(eg, PyException_GetCause(orig))`. `PyException_SetCause()` always sets `suppress_context = 1`, even when the cause is `NULL`, so the part keeps `__context__` but hides it.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [typeobj-exc-split-sets-suppress-context](https://github.com/Broyojo/python-formalization/blob/main/bugs/typeobj-exc-split-sets-suppress-context.yaml)
