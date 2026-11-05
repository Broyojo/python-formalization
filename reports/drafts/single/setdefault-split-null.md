<!-- title: dict.setdefault() segfaults on an instance dict with an absent shared key passed as a str subclass -->
### Crash report

`setdefault()` crashes when a str-subclass key equals a shared key that has no value in this instance's `__dict__`. No callbacks, threads or C extension are needed. An exact `str` key takes a different, safe path.

```python
class C:
    pass
a = C()
a.x = 1
b = C()
b.y = 2
d = b.__dict__
class S(str):
    pass
print('get', d.get(S('x'), 'default'), flush=True)
print('setdefault', d.setdefault(S('x'), 5), flush=True)
```

Recorded on 3.15.2 and main: prints `get default`, then SIGSEGV in `setdefault()`. Expected: return `5` and insert the missing key. The record also reproduces the crash with a `StrEnum` member in place of the str subclass.

Cause: Objects/dictobject.c:4817-4841 uses the split-table insertion path only for exact str keys. The generic `_Py_dict_lookup` can return a nonnegative index with `value == NULL` when the shared key exists but this instance has no value. The test at :4843 checks only `ix == DKIX_EMPTY`; :4865-4869 then reaches `Py_NewRef(value)` with NULL. The missing-value test needs `|| value == NULL`, as other lookup callers in this file already use.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [dictset-setdefault-split-null](https://github.com/Broyojo/python-formalization/blob/main/bugs/dictset-setdefault-split-null.yaml)
