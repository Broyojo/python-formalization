<!-- title: functools.partial: changing p.keywords during the call's keyword merge overflows a stack buffer (new in 3.15) -->
### Crash report

In 3.15, `partial_vectorcall` merges the stored and the call keywords itself. It reads the size of `p.keywords` once, sizes its buffers from it, and then calls `PyDict_Contains(p.keywords, key)` for each call keyword. That lookup can run a key's `__eq__`, and `p.keywords` is the same, writable dict. The loop that follows writes one slot per item of the dict as it is now, with only a debug-build `assert` on the count.

```python
import functools

p = functools.partial(lambda **k: len(k), a=1)
armed = True

class S(str):
    def __hash__(self):
        return hash('a')
    def __eq__(self, o):
        global armed
        if armed:
            armed = False
            for i in range(2000):
                p.keywords['k%d' % i] = i
        return False

p(**{S('b'): 2})
```

Output on 3.15.2: `*** stack smashing detected ***: terminated` (SIGABRT). If `__eq__` clears `p.keywords` instead, it segfaults; if it adds one key, a call keyword is silently dropped. 3.14 does not crash.

Cause: Modules/_functoolsmodule.c, `partial_vectorcall`: the keyword count is read once, `PyDict_Contains(partial_keywords, key)` in the merge loop can run Python code, and the `PyDict_Next` loop after it writes `stack` and the names tuple by index with no bound in a release build.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [corelibs-partial-vectorcall-stale-kw-count](https://github.com/Broyojo/python-formalization/blob/main/bugs/corelibs-partial-vectorcall-stale-kw-count.yaml)
