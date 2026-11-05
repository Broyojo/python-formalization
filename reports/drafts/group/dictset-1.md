<!-- title: Small inconsistencies in dict and set found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. After dict.popitem(od), od.popitem() and od.pop(k) segfault, and iterating od never ends

od_fast_nodes mirrors dk_entries by index, and _odict_get_index_raw answers a failed lookup with dk_nentries, "index of new entry". dict.popitem(od) shrinks dk_nentries, so that index now names the slot of the node for the key just popped. A lookup for a missing key therefore returns a stale node instead of none, with two results from plain Python:

*May be intended:* Partly, and a maintainer may well decline this. Bypassing OrderedDict through dict's methods is known to desynchronise it. On gh-68914 (dict.__setitem__ on an OrderedDict) the closing comment says some holes probably remain and that the answer should likely be to document "don't do that". gh-154835, on inconsistent state from a stateful __eq__, was closed as not planned. Against that, gh-154817 is open with a PR for the same NULL dereference, so the crash has a route to a fix regardless of this trigger. The hang is the part with no such route, and on the precedent above "don't do that" is a fair answer to it.

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
if r.returncode == -11 and 'after' not in r.stdout and len(od) == 1 and len(walked) == 100:
    print("Observed the reported behavior.")
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude and Codex) helped investigate the findings and prepare this report. The examples were rerun on CPython 3.15.2 and main, and the report received technical review. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
