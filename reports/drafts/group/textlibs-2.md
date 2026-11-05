<!-- title: Small inconsistencies in text and binary codecs found by a formal model (part 2 of 2) -->
# Bug report

### Bug description

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped here so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. Pure-Python Element.__setitem__ consumes an iterator before storing it, so slice assignment from a generator inserts nothing

Element.__setitem__ checks a slice value with `for elt in element: self._assert_is_element(elt)` and then runs `self._children[index] = element`, which iterates the value a second time. A generator or any other one-shot iterator is exhausted by the first loop, so e[1:1] = (x for x in new) inserts nothing, and e[:] = iter(new) empties the element. The C accelerator calls PySequence_Fast once and stores every item. Element.extend differs the other way on a failing iterator: C materialises the iterable with PySequence_Fast before appending, so an iterator that yields two Elements and then raises leaves the element unchanged in C and with both appended in the twin (which, like list.extend, appends as it goes). Neither is documented; recorded as a twin difference. Element.remove checks its argument only after list.remove has searched: e.remove(5) with a child whose __eq__ returns True removes that child in the twin, while C's Argument Clinic refuses 5 with TypeError before searching (3.15 added the twin's TypeError to match C, but after the search). The twin also checks the value before the index, so e[100] = 5 raises TypeError there and IndexError in C; that difference is cosmetic and is recorded only for completeness. e.extend(e) never returns in the twin: Element has no __iter__, so the loop iterates e by index while appending to it and grows without bound (list.extend special-cases its own list); C takes a sequence snapshot and doubles the children. Likewise insert(2**63, 5) raises TypeError in the twin and OverflowError in C, whose Argument Clinic converts the index first. (Found by the second review pass of the etree rows; checked on 3.15.2.)

<details><summary>Reproducer</summary>

```python
import xml.etree.ElementTree as cmod
from test.support import import_helper
pymod = import_helper.import_fresh_module('xml.etree.ElementTree', blocked=['_elementtree'])
def run(mod):
    e = mod.Element('r')
    e.extend([mod.Element('a%d' % i) for i in range(3)])
    new = [mod.Element('X0'), mod.Element('X1')]
    e[1:1] = (x for x in new)
    return [c.tag for c in e]
c, py = run(cmod), run(pymod)
print('C ', c)
print('Py', py)
```

</details>

#### 2. plistlib: a binary plist written from datetime.max cannot be read back (InvalidFileException)

The binary writer stores a datetime as the double (value - datetime(2001, 1, 1)).total_seconds() (Lib/plistlib.py:808-815). Near datetime.max that double is only accurate to about 30 microseconds, and total_seconds() rounds 9999-12-31 23:59:59.999999 up to 252423993600.0, which is 10000-01-01. The reader (:587-595) computes datetime(2001, 1, 1) + timedelta(seconds=f), which overflows, and parse turns the OverflowError into InvalidFileException. So plistlib.dumps(datetime.datetime.max, fmt=FMT_BINARY) succeeds and plistlib.loads of the result raises InvalidFileException("Invalid file"); so does any datetime within about 15 microseconds of datetime.max. The XML writer drops the microseconds and round-trips the same value. Far from 2001 the binary round trip also silently loses microseconds (datetime(1, 1, 1, 0, 0, 0, 1) reads back as datetime(1, 1, 1)), which is inherent in the format's double; the exception is not.

<details><summary>Reproducer</summary>

```python
import datetime, plistlib
out = {}
for name, d in [("max", datetime.datetime.max),
                ("max-5us", datetime.datetime.max - datetime.timedelta(microseconds=5)),
                ("year1+1us", datetime.datetime(1, 1, 1, 0, 0, 0, 1))]:
    data = plistlib.dumps(d, fmt=plistlib.FMT_BINARY)
    try:
        out[name] = repr(plistlib.loads(data))
    except plistlib.InvalidFileException as e:
        out[name] = "InvalidFileException: " + str(e)
    print(name, repr(d), "->", out[name])
print("XML round trip of datetime.max:", repr(plistlib.loads(plistlib.dumps(datetime.datetime.max))))
```

</details>

#### 3. re: x{m,n}+ with m >= 2 is not equivalent to (?>x{m,n}), as the docs say it is

The docs say "x{m,n}+ is equivalent to (?>x{m,n})". They differ when m >= 2 and x can match more than one way: `re.fullmatch(r'(?:a|ab){2}+', 'aba')` is None, and `re.fullmatch(r'(?>(?:a|ab){2})', 'aba')` matches. `re.match(r'(?:a+){2}+', 'aa')` is None, and `re.match(r'(?>(?:a+){2})', 'aa')` matches. An atomic group forbids backtracking into it once it is finished, so inside it the iterations can still trade characters to reach the minimum. The possessive loop makes each iteration atomic alone, so the first iteration cannot give back what the second needs. No difference appears with m <= 1, so x*+, x++ and x?+ keep the sentence the docs state for them. The Lean declarative semantics agrees with CPython on 150000 of 150000 random cases once this is modelled, and the documented form is refuted.

<details><summary>Reproducer</summary>

```python
import re
a = re.fullmatch(r'(?:a|ab){2}+', 'aba')
b = re.fullmatch(r'(?>(?:a|ab){2})', 'aba')
c = re.match(r'(?:a+){2}+', 'aa')
d = re.match(r'(?>(?:a+){2})', 'aa')
print(a, b, c, d)
```

</details>

#### 4. SimpleQueue.get(timeout=inf) raises OverflowError even with an item ready (C), and the twins disagree on NaN and tiny negative timeouts

The C SimpleQueue.get converts a blocking timeout with _PyTime_FromSecondsObject before it looks at the queue. So q.put(1); q.get(timeout=float('inf')) raises OverflowError ("timestamp out of range for C PyTime_t") although the item is there; so do 1e300 and 2**63, and NaN raises ValueError. queue.Queue.get and the pure-Python queue._PySimpleQueue return the item in all four cases. The conversion also rounds up: timeout=-1e-10 becomes 0 ns, so C returns the item where the twin raises ValueError("'timeout' must be a non-negative number").

<details><summary>Reproducer</summary>

```python
import math, queue
res = []
for Q in (queue.SimpleQueue, queue._PySimpleQueue):
    out = []
    for t in (math.inf, -1e-10):
        q = Q(); q.put(1)
        try:
            out.append(q.get(timeout=t))
        except Exception as e:
            out.append(type(e).__name__)
    res.append(out)
print('C', res[0], 'Py', res[1])
```

</details>

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Drafted with AI assistance (Claude); each case was reproduced on 3.15.2 and on main and the report reviewed before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
