<!-- title: A hit on the link being evicted, from a raising __eq__, leaves a cycle … -->
# Bug report

### Bug description

To evict, bounded_lru_cache_update_lock_held unlinks the oldest link and then pops its key from the dict. The pop can run the
__eq__ of a colliding key while the dict still refers to that link. If the __eq__ calls the cached function with the evicted
key, that is a hit: bounded_lru_cache_get_lock_held extracts the link a second time and appends it as the newest. If the
__eq__ then raises, the pop fails, and the error path puts the link back at the oldest position with
lru_cache_prepend_link, although it is in the list already. The list now has a cycle that does not pass through the root.
lru_cache_tp_traverse walks the list until it reaches the root, so the next collection of the generation holding the
wrapper never ends. The interpreter hangs in gc, at whatever allocation triggered it, with the GIL held.

```python
import subprocess, sys, textwrap
child = textwrap.dedent("""
    import functools, gc
    box = {'hook': None}
    class K:
        def __init__(self, n, h):
            self.n, self.h = n, h
        def __hash__(self):
            return self.h
        def __eq__(self, o):
            h = box['hook']
            if h is not None:
                box['hook'] = None
                h()
            return self is o
    a, b, c = K(1, 0), K(2, 0), K(3, 1)
    f = functools.lru_cache(maxsize=2)(lambda k: k.n)
    f(a), f(b), f(a)     # the dict holds a, b in that order, and b is the oldest link
    def hook():
        f(b)             # a hit on the link that is being evicted
        raise ValueError('eq')
    box['hook'] = hook
    try:
        f(c)
    except ValueError:
        pass
    print('collecting', flush=True)
    gc.collect()
    print('survived', flush=True)
""")
try:
    r = subprocess.run([sys.executable, '-c', child], capture_output=True, text=True, timeout=10)
    print(r.returncode, r.stdout)
except subprocess.TimeoutExpired:
```

**Expected:** gc.collect() returns.

**Actual:** python3 3.14.7: gc.collect() does not return within 10 seconds. REPRODUCED. main (3.16.0a1+dev): REPRODUCED. python3 3.15.2: REPRODUCED. main (3.16.0a1+dev): REPRODUCED.

**Cause:** Modules/_functoolsmodule.c:1523-1530 unlinks the link while the dict still refers to it, and :1425-1426 trusts that a link found in the dict is in the list. The failure branch at :1531-1541 then links it again. `lru_cache_tp_traverse`, :1837-1844, ends only at the root. The pure Python twin has no such path: it rotates the root instead of unlinking.

**Possible fix:** Pop the key before unlinking the link, and unlink only the link the pop returned; or mark the link as out of the list and make the hit path treat it as a miss. Either way the hit path must not extract a link that is not in the list.

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.
