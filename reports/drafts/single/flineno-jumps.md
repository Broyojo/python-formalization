<!-- title: Setting frame.f_lineno can approve a jump to an incompatible stack and crash (three cases) -->
### Crash report

`frame.f_lineno = n` uses `mark_stacks` (Objects/frameobject.c) to check that the stack at the target line is compatible with the current one. I found three gaps that let an unsafe jump through. Each case below segfaults on 3.15.2 and on main; the correct result would be `ValueError` from the assignment.

**1. The second value pushed by `GET_ITER` (new in 3.15).** `GET_ITER` now pushes `iter, index_or_null`, and `mark_stacks` marks both as `Iterator` (frameobject.c:1396-1400). `compatible_kind` lets `Iterator` flow into `Object`, so a jump from a `for` body into the middle of a two-line expression is accepted, and `BUILD_LIST` then consumes a tagged int or NULL.

```python
import sys

def victim(p=1, q=2):
    x = [p,
         q]
    for i in x:
        y = i
    return 1

first = victim.__code__.co_firstlineno
done = False

def tr(frame, event, arg):
    global done
    if frame.f_code is victim.__code__ and event == "line" and not done and frame.f_lineno == first + 4:
        done = True
        frame.f_lineno = first + 1   # into the middle of the list display
        sys.settrace(None)
    return tr

sys.settrace(tr)
victim()
```

**2. The NULL pushed for a `with` statement.** The `default:` arm of `mark_stacks` (frameobject.c:1483-1496) records the `self_or_null` slot that `LOAD_SPECIAL` pushes as `Object`, not `Null`, so a jump out of a `with` body into a multi-line expression is approved with a NULL on the stack.

<details><summary>Reproducer</summary>

```python
import sys

class CM:
    __enter__ = staticmethod(lambda: None)
    __exit__ = staticmethod(lambda *a: None)

def victim(a, b, c):
    with CM():
        x = 1
        pass
    y = (a, b,
         c)
    return y

first = victim.__code__.co_firstlineno
done = False

def tr(frame, event, arg):
    global done
    if frame.f_code is victim.__code__ and event == "line" and not done and frame.f_lineno == first + 2:
        done = True
        frame.f_lineno = first + 5
    return tr

sys.settrace(tr)
victim(1, 2, 3)
```

</details>

**3. `stack_swap` truncates the stack.** `static Kind stack_swap(int64_t stack, int n)` (frameobject.c:1239) builds an `int64_t` but returns it as `Kind`, which is 32 bits, so a `SWAP` with more than about ten entries on the stack records a wrong stack for every later offset. Nine nested `for` loops are enough. On 3.14 the same jump gives `TypeError: 'NoneType' object is not an iterator`; on 3.15 it segfaults.

<details><summary>Reproducer</summary>

```python
import sys

DEPTH = 9
src = "def victim():\n    n = 0\n"
ind = "    "
for i in range(DEPTH):
    src += ind + f"for i{i} in [1]:\n"
    ind += "    "
src += ind + "w = [j for j in [1]]\n" + ind + "n += 1\n" + ind + "n += 2\n" + "    return n\n"
ns = {}
exec(src, ns)
victim = ns["victim"]
line = victim.__code__.co_firstlineno + 2 + DEPTH
done = False

def tr(frame, event, arg):
    global done
    if frame.f_code is victim.__code__ and event == "line" and frame.f_lineno == line and not done:
        done = True
        frame.f_lineno = line + 1
    return tr

sys.settrace(tr)
victim()
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Record: [bytecode-flineno-iter-index-as-object](https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-flineno-iter-index-as-object.yaml), [bytecode-flineno-null-on-stack](https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-flineno-null-on-stack.yaml), [bytecode-flineno-stack-swap-truncation](https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-flineno-stack-swap-truncation.yaml)
