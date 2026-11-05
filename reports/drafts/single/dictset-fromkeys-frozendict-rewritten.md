<!-- title: frozendict.fromkeys of a subclass hands an untracked frozendict to … -->
# Bug report

### Bug description

Since gh-151722, `_PyDict_FromKeys` uses "not tracked by the GC" to mean "a frozendict still being
built, which I may fill". A tracked frozendict returned by `cls()` is copied into a fresh untracked
frozendict, which is filled and then passed to `cls(d)` at :3593. That call runs Python code
(`cls.__new__`, `cls.__init__`) with the finished but still untracked frozendict, so the object
escapes untracked. A later `fromkeys` whose `cls()` returns that object sees an untracked
frozendict, skips the copy (:3443), and fills it in place through `setitem_take2_lock_held`
(:3538-3555), or through `dict_dict_fromkeys`/`dict_set_fromkeys` for a dict or set argument.

```python
leaked = []
class F(frozendict):
    def __init__(self, *args):
        if args:
            leaked.append(args[0])   # the argument of cls(d) at :3593
F.fromkeys([1, 2])
fd = leaked[0]
before = dict(fd)
h = hash(fd)
table = {fd: 'value'}
class G(frozendict):
    def __new__(cls, *args):
        return fd
r = G.fromkeys(['x'])
equal = frozendict(dict(fd))   # a new frozendict with the same items
print('type', type(fd).__name__, 'same object', r is fd)
print('before', before, 'after', dict(fd))
print('hash unchanged', hash(fd) == h, 'equal copy == fd', equal == fd,
      'hash(copy) == hash(fd)', hash(equal) == hash(fd), 'copy in table', equal in table)
if (equal is not fd and r is fd and dict(fd) != before and hash(fd) == h and equal == fd
        and equal not in table):
```

**Expected:** `fd` never changes: `G.fromkeys(['x'])` either copies `fd` before filling (as it does for a tracked frozendict) or returns a new object; `dict(fd)` stays `{1: None, 2: None}`.

**Actual:** python3 3.15.2: `same object True`, `before {1: None, 2: None} after {1: None, 2: None, 'x': None}`, `hash unchanged True`, `equal copy == fd True`, `hash(copy) == hash(fd) False`, `copy in table False`. REPRODUCED. main (3.16.0a1+dev, ef1fce0): identical. REPRODUCED.

**Cause:** Objects/dictobject.c:3592-3595: `_PyObject_CallOneArg(cls, d)` runs with `d` the untracked copy made at :3443-3455, and nothing tracks `d` first, so `cls.__new__`/`cls.__init__` can keep it. :3443 then treats any untracked frozendict that `cls()` returns as one it may fill: `need_copy` stays 0 and :3486-3508 (dict or set argument) or :3538-3555 (any other iterable) write into it; :3596-3597 then tracks it.

**Possible fix:** Track the copy before handing it out: `_PyObject_GC_TRACK(d)` before `_PyObject_CallOneArg(cls, d)` at :3593. Alternatively, test at :3443 that `cls()` returned a new object, not only an untracked one (for example, copy whenever `d` is a frozendict that `cls()` returned, tracked or not).

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
