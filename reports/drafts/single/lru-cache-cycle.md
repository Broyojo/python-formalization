<!-- title: lru_cache: a cache hit from __eq__ during eviction corrupts the C cache's list, and the next gc.collect() hangs -->
### Bug report

To evict, the C `lru_cache` unlinks the oldest link and then pops its key from the dict. The pop can run a colliding key's `__eq__` while the dict still refers to the unlinked link. If that `__eq__` calls the cached function with the evicted key (a cache hit) and then raises, the error path links the same link back in a second time. The list now has a cycle that skips the root, and `lru_cache_tp_traverse` walks until it reaches the root, so the next `gc.collect()` never returns.

```python
import functools, gc

hook = None

class K:
    def __init__(self, n, h):
        self.n, self.h = n, h
    def __hash__(self):
        return self.h
    def __eq__(self, o):
        global hook
        if hook is not None:
            h, hook = hook, None
            h()
        return self is o

a, b, c = K(1, 0), K(2, 0), K(3, 1)
f = functools.lru_cache(maxsize=2)(lambda k: k.n)
f(a), f(b), f(a)          # b is now the oldest entry

def on_eq():
    f(b)                  # a hit on the entry being evicted
    raise ValueError

hook = on_eq
try:
    f(c)
except ValueError:
    pass
gc.collect()              # never returns
```

The pure-Python `lru_cache` has no such path.

Cause: Modules/_functoolsmodule.c:1523-1530 unlinks the link while the dict still refers to it; :1425-1426 (a hit) assumes a link found in the dict is in the list; the failure branch at :1531-1541 links it again; `lru_cache_tp_traverse` (:1837-1844) stops only at the root.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [corelibs-lru-evicted-hit-gc-hang](https://github.com/Broyojo/python-formalization/blob/main/bugs/corelibs-lru-evicted-hit-gc-hang.yaml)
