<!-- title: Setting f_lineno into deeply nested blocks corrupts the stack -->
# Bug report

### Bug description

`mark_stacks` models the evaluation stack of each offset as an `int64_t`, three bits per entry (Objects/frameobject.c:1169-1531). `stack_swap` (lines 1239-1249) computes the swapped stack in `int64_t` but is declared to return `Kind` (an enum, 32-bit on the usual ABI), so its result is truncated to 32 bits -- it is assigned straight to `next_stack` at line 1467. For a function nested deeply enough that the stack at a `SWAP` needs more than ~10 entries (> 32 bits), the truncation drops the high entries, `mark_stacks` records a wrong stack for every later offset, and `compatible_stack` then approves a `frame.f_lineno = n` jump that is in fact incompatible. The interpreter resumes with a malformed stack. With ~9 nested `for` loops plus a comprehension (which the compiler inlines with `SWAP` since 3.14), jumping one line within the innermost body segfaults on 3.15.2 and main, and raises `TypeError: 'NoneType' object is not an iterator` on 3.14.7.

```python
import subprocess, sys, textwrap
prog = textwrap.dedent('''
    import sys
    DEPTH = 9
    src = "def victim():\\n    n = 0\\n"
    ind = "    "
    for i in range(DEPTH):
        src += ind + f"for i{i} in [1]:\\n"
        ind += "    "
    src += ind + "w = [j for j in [1]]\\n"
    src += ind + "n += 1\\n"
    src += ind + "n += 2\\n"
    src += "    return n\\n"
    ns = {}
    exec(compile(src, "<v>", "exec"), ns)
    victim = ns["victim"]
    first = victim.__code__.co_firstlineno
    LINE_FROM = first + 2 + DEPTH
    LINE_TO = LINE_FROM + 1
    done = [False]
    def tr(frame, event, arg):
        if frame.f_code is victim.__code__ and event == "line" and frame.f_lineno == LINE_FROM and not done[0]:
            done[0] = True
            try:
                frame.f_lineno = LINE_TO
            except ValueError:
                print("rejected"); sys.exit(7)
        return tr
    sys.settrace(tr)
    victim()
    sys.settrace(None)
    print("no error")
''')
r = subprocess.run([sys.executable, "-I", "-c", prog], capture_output=True, text=True)
# A clean reject (exit 7) would be correct; a crash or a TypeError is the bug.
crashed = r.returncode < 0
typeerr = "TypeError" in r.stderr and "not an iterator" in r.stderr
if crashed or typeerr:
    print("returncode", r.returncode, "stderr-tail", r.stderr.strip().splitlines()[-1:] )
```

**Expected:** The jump is either safely performed with a correctly-analysed stack, or rejected with a `ValueError`. It must never resume with a corrupted stack (TypeError from a `None` iterator, or a segfault).

**Actual:** python3 3.15.2: segmentation fault (returncode -11). On 3.14.7: `TypeError: 'NoneType' object is not an iterator` from the jumped-to code. main (vendor/cpython-main/python.exe, 3.16.0a1+dev): segmentation fault (core dumped). (the harness runs it in a child and detects the negative return code).

**Cause:** Objects/frameobject.c:1239-1240 declares `static Kind stack_swap(int64_t stack, int n)`; the body (1241-1248) builds an `int64_t` but the `Kind` return type narrows it to 32 bits. Line 1467 assigns that to `next_stack`. For stacks over ~32 bits the recorded stack is wrong, so `compatible_stack` (1533-1552) is consulted with bad data.

**Possible fix:** Change `stack_swap`'s return type to `int64_t`.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-flineno-stack-swap-truncation.yaml
