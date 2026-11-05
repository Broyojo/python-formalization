<!-- title: partial_vectorcall trusts a keyword count taken before a key's __eq__ … -->
# Bug report

### Bug description

New in 3.15: partial_vectorcall merges stored and call keywords itself instead of falling back to partial_call. It reads
pto_nkwds = PyDict_GET_SIZE(partial_keywords), sizes `stack` and the keyword-name tuple from it, and then calls
PyDict_Contains(partial_keywords, key) for each call keyword. That lookup can run a key's __eq__, for a str subclass whose hash
collides with a stored key, and p.keywords is the same dict and is writable. The later PyDict_Next loop walks the dict as
it is then, and asserts i == pto_nkwds only in a debug build. If the dict grew, the loop writes past the tuple and past
`stack`: in a release build that is a stack smash when `stack` is small_stack. If it shrank, the tuple keeps NULL items and
the callee reads them: a segfault. If one key was added and the sizes still fit, a call keyword is silently lost.
The holding of references added for gh-154189 protects the dict object and not its size.

```python
import subprocess, sys, textwrap
child = textwrap.dedent("""
    import functools
    p = functools.partial(lambda **k: len(k), a=1)
    armed = [True]
    class S(str):
        def __hash__(self):
            return hash('a')
        def __eq__(self, o):
            if armed[0]:
                armed[0] = False
                for i in range(2000):
                    p.keywords['k%d' % i] = i
            return False
    print(p(**{S('b'): 2}))
    print('survived')
""")
r = subprocess.run([sys.executable, '-c', child], capture_output=True, text=True, timeout=30)
print(r.returncode, r.stdout[-200:], r.stderr[-200:])
```

**Expected:** The call keeps working on a consistent view of the keywords, as it does on 3.14.7, where the same program prints a result.

**Actual:** python3 3.15.2: stack smashing detected, signal 6, when the dict grows; segfault, signal 11, when it is cleared; a dropped call keyword when one key is added. REPRODUCED. main (3.16.0a1+dev): segfault on grow and on clear. REPRODUCED. 3.14.7: no crash.

**Cause:** Modules/_functoolsmodule.c, partial_vectorcall: the count is read once, `PyDict_Contains(partial_keywords, key)` in the merge loop can run arbitrary code, and the PyDict_Next loop after it writes `tot_kwnames` and `stack` by index with no bound in a release build.

**Possible fix:** Take a private copy of the keywords before the merge loop, or re-check PyDict_GET_SIZE after it and fall back to a slow path; in the PyDict_Next loop, stop at pto_nkwds and raise RuntimeError on a size change, as dict iteration does.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
