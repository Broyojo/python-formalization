<!-- title: zoneinfo: a cache key whose __eq__ calls ZoneInfo.clear_cache() makes … -->
# Bug report

### Bug description

`find_in_strong_cache` (Modules/_zoneinfo.c:2436-2453) walks the strong cache list and compares
`PyObject_RichCompareBool(key, node->key, Py_EQ)` for each node (:2441). The comparison runs the
key's `__eq__`, which can call `ZoneInfo.clear_cache()`; that frees every node
(`clear_strong_cache`, :2581-2590). The walk then reads `node->next` of a freed node
(:2449), and on a hit `zone_from_strong_cache` (:2516-2535) hands the freed node to
`move_strong_cache_node_to_front`. DUPLICATE of gh-142782 (open).

```python
import subprocess, sys
child = r'''
import struct, os, tempfile, zoneinfo
from zoneinfo import ZoneInfo
T = tempfile.mkdtemp()
h = b"TZif2" + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 1, 4)
blob = h + struct.pack(">lBB", 0, 0, 0) + b"UTC\x00"
for i in range(4):
    with open(os.path.join(T, "k%d" % i), "wb") as f:
        f.write(blob + blob + b"\nUTC0\n")
zoneinfo.reset_tzpath([T])
held = [ZoneInfo("k0"), ZoneInfo("k1"), ZoneInfo("k2")]
del held
class K(str):
    def __hash__(self):
        return str.__hash__(self)
    def __eq__(self, other):
        ZoneInfo.clear_cache()
        return False
print("lookup", flush=True)
ZoneInfo(K("k3"))
print("survived", flush=True)
'''
p = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True)
print("child returncode:", p.returncode, "stdout:", p.stdout.strip().replace("\n", " | "))
```

**Expected:** The lookup either finds nothing or raises; the process continues ("survived").

**Actual:** python3 3.15.2: child prints "lookup", then dies with SIGSEGV (rc -11), 3 of 3 runs. REPRODUCED.

**Cause:** Modules/_zoneinfo.c:2441-2449: the list is used across a call into Python code that can free it.

**Possible fix:** As proposed on gh-142782: hold a reference to the node's key and re-check the cache head after the comparison (or restart the walk when the cache changed).

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
