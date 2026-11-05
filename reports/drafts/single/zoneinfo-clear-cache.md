<!-- title: ZoneInfo.clear_cache() crashes if a cache key's __del__ creates a ZoneInfo -->
### Crash report

`clear_strong_cache` frees the strong cache's nodes and sets `ZONEINFO_STRONG_CACHE = NULL` only after the walk. Freeing a node drops its key, which can run a `str` subclass's `__del__`. If that `__del__` constructs a `ZoneInfo`, the constructor updates the strong cache through the pointer that still refers to the nodes being freed.

```python
import os, struct, tempfile, gc
import zoneinfo
from zoneinfo import ZoneInfo

def tzif():   # a minimal UTC TZif file, so the example needs no tzdata
    h = b"TZif2" + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 1, 4)
    b = h + struct.pack(">lBB", 0, 0, 0) + b"UTC\x00"
    return b + b + b"\nUTC0\n"

d = tempfile.mkdtemp()
for i in range(10):
    with open(os.path.join(d, "k%d" % i), "wb") as f:
        f.write(tzif())
zoneinfo.reset_tzpath([d])

n = 3
class K(str):
    def __del__(self):
        global n
        ZoneInfo("k%d" % n); n += 1

for i in range(3):
    ZoneInfo(K("k%d" % i))
gc.collect()
ZoneInfo.clear_cache()   # segfault
```

Cause: Modules/_zoneinfo.c:2588-2589 calls `strong_cache_free(state->ZONEINFO_STRONG_CACHE)`, whose `Py_XDECREF(node->key)` (:2377-2383) can run Python code, before setting the pointer to NULL. Detaching the list first (save the head, set the pointer to NULL, then free) would fix it.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

### Output from running 'python -VV' on the command line:

Python 3.15.2 (tags/v3.15.2:5e58eaa, Nov  5 2026, 20:20:36) [GCC 11.4.0]

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [datetime-zoneinfo-clear-cache-reentrant-free](https://github.com/Broyojo/python-formalization/blob/main/bugs/datetime-zoneinfo-clear-cache-reentrant-free.yaml)
