<!-- title: Small inconsistencies in itertools found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. itertools.islice with stop=None yields an extra item when start + step overflows Py_ssize_t

islice_next computes the index of the next item to return with `lz->next += (size_t)lz->step` and handles overflow with `if (lz->next < oldnext || (stop != -1 && lz->next > stop)) lz->next = stop;`. When stop is None, `stop` is the sentinel -1, so an overflow sets `lz->next = -1`. The next call then skips nothing (`cnt < -1` is false), does not check a stop, and returns the very next input item; `next` then becomes `-1 + step` and the iterator resumes skipping. So islice(range(10), 1, None, sys.maxsize) yields [1, 2] instead of [1], and islice(range(10), 5, None, sys.maxsize - 2) yields [5, 6] instead of [5]. Every argument is inside the documented range 0 <= x <= sys.maxsize, no error is raised, and the result is silently wrong. With an int stop the same overflow is harmless (next is set to stop), and range(10)[1::sys.maxsize] / the documented pure-Python equivalent give [1]. Lean: the C model and the doc equivalent agree on items, consumption and when they raise for every Py_ssize_t start/stop/step with stop given, or with len + step <= sys.maxsize + 1 (itertools-islice-doc-agree-nowrap, proven); itertools-islice-doc-agree-ssize, without that hypothesis, is refuted by this reproducer.

<details><summary>Reproducer</summary>

```python
import sys
from itertools import islice
M = sys.maxsize
r1 = list(islice(range(10), 1, None, M))
r2 = list(islice(range(10), 5, None, M - 2))
r3 = list(islice(range(10), 1, 10, M))
print('islice(range(10), 1, None, sys.maxsize)     ->', r1, '; range(10)[1::sys.maxsize] =', list(range(10))[1::M])
print('islice(range(10), 5, None, sys.maxsize - 2) ->', r2, '; range(10)[5::sys.maxsize-2] =', list(range(10))[5::M - 2])
print('islice(range(10), 1, 10, sys.maxsize)       ->', r3, '(an int stop is fine)')
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
