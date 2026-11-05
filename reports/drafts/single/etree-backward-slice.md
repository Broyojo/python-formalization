<!-- title: ElementTree slice assignment with start greater than stop duplicates a child without owning its second reference -->
### Bug report

Assigning to a step-1 slice with `start > stop` should insert at `start`, as a list does. The C Element implementation shifts from `stop` but writes from `start`. This duplicates one child without incrementing its reference count and overwrites another child's slot without releasing its reference.

```python
import sys
import xml.etree.ElementTree as ET
kids = [ET.Element('a%d' % i) for i in range(7)]
e = ET.Element('r')
e[:] = kids
before = sys.getrefcount(kids[2])
e[5:2] = [ET.Element('X')]
tags = [c.tag for c in e]
print(tags, 'refcount change of a2:', sys.getrefcount(kids[2]) - before)
```

Recorded on 3.15.2 and main:

```text
['a0', 'a1', 'a2', 'a2', 'a3', 'X', 'a5', 'a6'] refcount change of a2: 0
```

Expected, also obtained with the pure-Python Element implementation:

```text
['a0', 'a1', 'a2', 'a3', 'a4', 'X', 'a5', 'a6']
```

The duplicate `a2` has no additional owned reference. Releasing the parent therefore decrements it twice, potentially freeing it while `kids` still holds it. The record confirms this lifetime error separately; the reproducer above shows the wrong slots and missing reference without adding an allocator-reuse demonstration.

Cause: Modules/_elementtree.c:1976-1977 uses `PySlice_AdjustIndices` without normalizing a backward empty slice. The insertion loop at :2026-2030 shifts from `stop`, whereas replacement at :2033-2037 starts at `start`. Normalize `stop` to `start` for a positive step with `stop < start`, as list slice assignment does. No reentrancy or threads are required.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [textlibs-etree-slice-backward-dup](https://github.com/Broyojo/python-formalization/blob/main/bugs/textlibs-etree-slice-backward-dup.yaml)
