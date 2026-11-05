<!-- title: Setting f_lineno to jump into a with block leaves NULL on the stack -->
# Bug report

### Bug description

`mark_stacks` (Objects/frameobject.c:1316-1531) assigns a `Kind` to each stack slot; `Null` marks a `NULL` placeholder such as the `self_or_null` that `LOAD_SPECIAL` / `_INSERT_NULL` push for a `with` statement's `__enter__`/`__exit__` lookup (Python/bytecodes.c:4125-4151). `compatible_kind` (lines 1183-1195) allows anything to flow *to* a `Null` slot but, crucially, `mark_stacks` records the slot that a bound method / `__exit__` is loaded into via the `default:` case as `Object` (lines 1483-1496), not `Null`. The jump-target analysis in `frame_lineno_set_impl` then approves a `frame.f_lineno = n` jump that lands just after a `with`'s setup, where the eval stack actually holds a `NULL`. The warning/`None`-assignment pass at lines 1796-1820 only fixes NULL *locals*, not NULL values already on the eval stack, so the interpreter resumes and reads a `NULL` as a live object, segfaulting on 3.14.7, 3.15.2 and main.

```python
import subprocess, sys, textwrap
prog = textwrap.dedent('''
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
    LINE_A = first + 2
    LINE_B = first + 5
    done = [False]
    def tr(frame, event, arg):
        if frame.f_code is victim.__code__ and event == "line" and not done[0] and frame.f_lineno == LINE_A:
            done[0] = True
            try:
                frame.f_lineno = LINE_B
            except ValueError:
                print("rejected"); sys.exit(7)
        return tr
    sys.settrace(tr)
    victim(1, 2, 3)
    sys.settrace(None)
    print("no crash")
''')
r = subprocess.run([sys.executable, "-c", prog], capture_output=True, text=True)
# A clean reject (exit 7) is correct; a crash (negative return code) is the bug.
if r.returncode < 0:
    print("returncode", r.returncode)
```

**Expected:** The jump is either performed safely or rejected with `ValueError`; it must never leave a `NULL` on the evaluation stack to be used as an object.

**Actual:** python3 3.15.2: segmentation fault (returncode -11). Same on 3.14.7. main (vendor/cpython-main/python.exe, 3.16.0a1+dev): segmentation fault (core dumped).

**Cause:** Objects/frameobject.c:1483-1496 (the `default:` arm of `mark_stacks`) records pushed slots as `Object`, so the `NULL` slot of a `with`/`LOAD_SPECIAL` sequence is analysed as `Object` and `compatible_stack` (1533-1552) approves a jump into it; the NULL-fixup at 1796-1820 covers only locals.

**Possible fix:** Mark the `self_or_null`/`PUSH_NULL` slots as `Null` in `mark_stacks` (as `PUSH_NULL` already does at lines 1438-1439), or extend the resume-time fixup to replace NULLs on the eval stack, or reject jumps whose target stack has an `Object` slot where the source has `Null`.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-flineno-null-on-stack.yaml
