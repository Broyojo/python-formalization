<!-- title: operator.methodcaller.__reduce__() exposes its private kwargs through partial.keywords, causing stale calls and a repr crash -->
### Crash report

The partial returned by `methodcaller.__reduce__()` shares the methodcaller's internal keyword dict. Updating `partial.keywords` changes the methodcaller's repr, while its cached vectorcall arguments still use the original values. Adding a non-string key makes `repr()` segfault.

```python
import operator
class O:
    def f(self, **kw): return kw
mc = operator.methodcaller('f', a=1)
p, args = mc.__reduce__()
p.keywords['a'] = 2
print("repr:", repr(mc), "| call:", mc(O()))
```

Recorded output on 3.15.2 and main:

```text
repr: operator.methodcaller('f', a=2) | call: {'a': 1}
```

Run this second case separately:

```python
import operator
mc = operator.methodcaller('f', a=1)
p, _ = mc.__reduce__()
p.keywords[1] = 2
print("before", flush=True)
repr(mc)
print("survived", flush=True)
```

Recorded on both interpreters: prints `before`, then SIGSEGV. Mutating the reconstruction recipe should leave the original methodcaller unchanged. Ordinary `pickle` and `copy` usage only reads the recipe and does not trigger these mutations.

Cause: Modules/_operator.c:1903 passes `mc->kwds` to `functools.partial`. Modules/_functoolsmodule.c:299-300 adopts a uniquely referenced dict, but here its one reference belongs to a live methodcaller. The cached arguments at Modules/_operator.c:1649-1686 do not change with the dict; `methodcaller_repr` at :1838 then uses `%U` on an unchecked key. The fallback call path at :1793 can also share the dict when the called method is `functools.partial`. Copying the keywords at these call sites, or limiting partial's adoption to known temporary dicts, would avoid the alias.

The record distinguishes this from gh-155733: that report concerns invalid keys supplied at construction, whereas this key is added after construction through the shared dict. Its recorded review of PR gh-155779 found construction-time checks only; that PR's current state needs rechecking before filing.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [operator-methodcaller-reduce-shares-kwargs](https://github.com/Broyojo/python-formalization/blob/main/bugs/operator-methodcaller-reduce-shares-kwargs.yaml)
