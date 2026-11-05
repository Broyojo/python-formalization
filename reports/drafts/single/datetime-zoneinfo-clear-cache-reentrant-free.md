<!-- title: ZoneInfo.clear_cache() can free cache nodes that are still in use -->
# Bug report

### Bug description

`clear_strong_cache` (Modules/_zoneinfo.c:2581-2590) calls `strong_cache_free(state->ZONEINFO_STRONG_CACHE)` and only afterwards sets `state->ZONEINFO_STRONG_CACHE = NULL`. `strong_cache_free` (:2392-2402) walks the list and, for each node, `strong_cache_node_free` (:2377-2383) runs `Py_XDECREF(node->key)` and `Py_XDECREF(node->zone)` before `PyMem_Free(node)`. Dropping the last reference to a key runs arbitrary Python code (a str subclass's `__del__`). If that code constructs a `ZoneInfo`, the constructor updates the strong cache through `state->ZONEINFO_STRONG_CACHE` (`update_strong_cache` and the move-to-front / eject logic), which still points at the nodes being freed: it links new nodes to freed ones, reads `next`/`prev` from freed nodes, and frees nodes a second time. The process segfaults.

```python
import subprocess, sys
child = r'''
import struct, os, tempfile, gc
import zoneinfo
from zoneinfo import ZoneInfo
def tz():
    h = b"TZif2" + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 1, 4)
    b = h + struct.pack(">lBB", 0, 0, 0) + b"UTC\x00"
    return b + b + b"\nUTC0\n"
T = tempfile.mkdtemp()
for i in range(10):
    with open(os.path.join(T, "k%d" % i), "wb") as f:
        f.write(tz())
zoneinfo.reset_tzpath([T])
N = [3]
class K(str):
    def __del__(self):
        ZoneInfo("k%d" % N[0]); N[0] += 1
for i in range(3):
    ZoneInfo(K("k%d" % i))
gc.collect()
print("clearing", flush=True)
ZoneInfo.clear_cache()
print("survived", flush=True)
'''
p = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True)
print("child returncode:", p.returncode, "stdout:", p.stdout.strip().replace("\n", " | "))
```

**Expected:** `clear_cache()` empties the strong cache; the ZoneInfo objects created by `__del__` are either cached in a fresh list or dropped; the process continues ("survived").

**Actual:** python3 3.15.2: child prints "clearing", then dies with SIGSEGV (rc -11). main (3.16.0a1+dev, ef1fce0): identical.

**Cause:** Modules/_zoneinfo.c:2588-2589: the list is freed (running key/zone destructors) while `state->ZONEINFO_STRONG_CACHE` still points at its head; it is cleared only after the walk.

**Possible fix:** Detach first: `StrongCacheNode *old = state->ZONEINFO_STRONG_CACHE; state->ZONEINFO_STRONG_CACHE = NULL; strong_cache_free(old);`. Nodes the destructors add then go into a fresh list. (The same pattern is worth checking in `eject_from_strong_cache`, which also frees nodes while running `Py_XDECREF` on keys.)

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/datetime-zoneinfo-clear-cache-reentrant-free.yaml
