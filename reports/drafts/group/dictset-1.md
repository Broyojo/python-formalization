<!-- title: Small inconsistencies in dict and set found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. After dict.popitem(od), od.popitem() and od.pop(k) segfault, and iterating od never ends

od_fast_nodes mirrors dk_entries by index, and _odict_get_index_raw answers a failed lookup with dk_nentries, "index of new entry". dict.popitem(od) shrinks dk_nentries, so that index now names the slot of the node for the key just popped. A lookup for a missing key therefore returns a stale node instead of none, with two results from plain Python:

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

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
