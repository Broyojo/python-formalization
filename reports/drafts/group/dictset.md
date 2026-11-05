<!-- title: dictset: 2 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. After dict.popitem(od), od.popitem() and od.pop(k) segfault, and iterating od never ends

od_fast_nodes mirrors dk_entries by index, and _odict_get_index_raw answers a failed lookup
with dk_nentries, "index of new entry". dict.popitem(od) shrinks dk_nentries, so that index
now names the slot of the node for the key just popped. A lookup for a missing key therefore
returns a stale node instead of none, with two results from plain Python:

<details><summary>Reproducer</summary>

```python
import itertools, resource, subprocess, sys
from collections import OrderedDict
crash = r"""
from collections import OrderedDict
od = OrderedDict(a=1, b=2)
dict.popitem(od)
print('before', flush=True)
od.popitem()
print('after', flush=True)
"""
r = subprocess.run([sys.executable, '-I', '-c', crash], capture_output=True, text=True)
print('popitem returncode', r.returncode)
# Never call list(od) here: it would not return. islice bounds the walk.
od = OrderedDict(a=1, b=2, c=3)
dict.popitem(od)
dict.popitem(od)
walked = list(itertools.islice(od, 100))
print('len', len(od), 'walked', len(walked), walked[:4])
```

</details>

#### 2. NOT FOR FILING: a failed hash does not leave a set unchanged when __hash__ changed it first

This records why the withdrawn claim SetHashFailureUnchanged ("a hash that raises leaves the set
unchanged") is false; it is not a defect report. __hash__ is Python code and runs before the set is
touched (_PyObject_HashFast at :602, :613, :624). Whatever it does to the set stands when it then
raises: with s = {1, 2, 3} and a key whose __hash__ does s.add(99) and raises TypeError("no"),
s.add(k), s.discard(k), s.remove(k), s.__contains__(k) and `k in s` all raise
"TypeError: cannot use 'K' as a set element (no)" and leave s == {1, 2, 3, 99}. The model now runs
__hash__ as a world-threaded hook (Proto.hashM), and set-hash-failure states the corrected
property: the error is set_unhashable_type's, in the state __hash__ left.

<details><summary>Reproducer</summary>

```python
s = {1, 2, 3}
class K:
    def __hash__(self):
        s.add(99)
        raise TypeError("no")
results = []
for op in ("add", "discard", "remove", "__contains__"):
    s.clear()
    s.update([1, 2, 3])
    try:
        getattr(s, op)(K())
    except TypeError as e:
        results.append((op, str(e), sorted(s)))
for r in results:
    print(*r)
if len(results) == 4 and all(m == "cannot use 'K' as a set element (no)" and v == [1, 2, 3, 99]
                             for _, m, v in results):
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
