<!-- title: Setting f_lineno to jump out of a for loop crashes -->
# Bug report

### Bug description

On 3.15 `GET_ITER` pushes two values, `(iterable -- iter, index_or_null)` (Python/bytecodes.c:3736). The upper one is not an object: `_PyEval_GetIter` stores `PyStackRef_TagInt(0)` for an exact list, tuple, str or bytes (Python/ceval.c:1136) and `PyStackRef_NULL` for everything else (:1139). `mark_stacks` follows the new shape but gives both slots the kind `Iterator` (Objects/frameobject.c:1396-1400), and `compatible_kind` lets `Iterator` flow into `Object` (:1183-1195, `to == Object` only rejects `Null`). In a `for` body the stack is now `[Iterator, Iterator]`, which is exactly as tall as the `[Object, Object]` in the middle of a two-line expression. When `frame.f_lineno = n` names such a line, `frame_lineno_set_impl` looks at every place the line table starts line `n` (:1766-1789). The first start has an empty stack, the second, where the line resumes after the continuation line, has `[Object, Object]`. Both are compatible, and the taller wins at `target_stack > best_stack` (:1771). Nothing is popped (:1825) and the frame resumes at `BUILD_LIST 2` with the iterable and the index as its operands. `_PyList_FromStackRefStealOnSuccess` (Objects/listobject.c:3326) then treats the index slot as an object and the process dies. On 3.14 the same analysis had `[Iterator]`, one entry against two, so `compatible_stack` rejected that target and the jump went to the true start of the line.

```python
import subprocess, sys, textwrap
prog = textwrap.dedent('''
    import sys
    def victim(p=1, q=2):
        x = [p,
             q]
        for i in x:
            y = i
        return 1
    first = victim.__code__.co_firstlineno
    LOOP_BODY = first + 4
    TWO_LINE_LIST = first + 1
    done = [False]
    def tr(frame, event, arg):
        if frame.f_code is victim.__code__ and event == "line" and not done[0] and frame.f_lineno == LOOP_BODY:
            done[0] = True
            try:
                frame.f_lineno = TWO_LINE_LIST
            except ValueError:
                print("rejected"); sys.exit(7)
            sys.settrace(None)
        return tr
    sys.settrace(tr)
    victim()
    sys.settrace(None)
    print("no crash")
''')
r = subprocess.run([sys.executable, "-I", "-W", "ignore", "-c", prog], capture_output=True, text=True)
# Rejecting the jump (exit 7) or running it safely ("no crash") is correct; dying is the bug.
if r.returncode < 0:
    print("returncode", r.returncode)
```

**Expected:** The jump lands at the true start of the line, with the loop's two slots popped, as it does on 3.14.7, or it is rejected with `ValueError`. It must not resume with the index slot as an operand.

**Actual:** python3 3.15.2: frame.f_lasti reads 8 after the jump (offset of BUILD_LIST), then segmentation fault in _PyList_FromStackRefStealOnSuccess. Same for `iter(x)`, a generator expression, range(2), a tuple and dict.fromkeys(x), so both the tagged-int and the NULL form of the slot crash. main (vendor/cpython-main/python.exe, 3.16.0a1+dev, ef1fce0): same. 3.14.7 (not a target, run to date the regression): frame.f_lasti reads 2, the function returns.

**Cause:** Objects/frameobject.c:1396-1400 marks both GET_ITER outputs `Iterator`. :1183-1195 `compatible_kind` accepts `Iterator -> Object`, which is sound for a real iterator and unsound for `index_or_null`. Python/ceval.c:1136 and :1139 are what that slot actually holds. :1771 `target_stack > best_stack` then prefers the taller, wrong target over the safe one. Found by bytecode_frame_diff.py: seed 0 first draws this triple at case 5127, which is why a 3000-case run passed and a 20000-case run segfaulted.

**Possible fix:** Give the second slot a kind that cannot flow to `Object`. `Null` does that with what is already there: `next_stack = push_value(next_stack, Null)` at :1398, since `compatible_kind(Null, Object)` is false, and a jump onto another loop's iterator pair stays allowed because `to == Null` accepts anything. The message for "can't jump into the body of a for loop" needs a look, since `explain_incompatible_stack` would now see `Null` first for such a jump.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/bytecode-flineno-iter-index-as-object.yaml
