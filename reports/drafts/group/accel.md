<!-- title: accel: 10 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. bisect: C treats hi=-1 as len(a) while bisect.py searches an empty range; negative hi breaks the documented partition

`_bisect` receives hi=None from Argument Clinic as the C default -1 and replaces any hi == -1
with len(a). An explicit hi=-1 is therefore "search the whole list" in C, while the pure-Python
twin searches the empty range [lo, -1) and returns lo. With a sorted a = [1, 2, 3, 4, 5],
bisect_left(a, 3, 0, -1) is 2 in C and 0 in Python; insort_left(a, 3, 0, -1) inserts at
index 2 in C (list stays sorted) and at index 0 in Python ([3, 1, 2, 3, 4, 5]). Every other
negative hi returns lo in both twins. Read literally, the docs' partition
"all(elem < x for elem in a[lo:ip]) ... all(elem >= x for elem in a[ip:hi])" then fails for
negative hi, because a[ip:hi] uses negative-index slicing (Python with hi=-1, both twins with
hi <= -2). The Lean proofs show these are the only failures: for hi=None or hi >= 0 any
returned ip is a correct partition point (accel-bisect-doc-partition-nonneg-hi).

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
cb = import_fresh_module('bisect', fresh=['_bisect'])
pb = import_fresh_module('bisect', blocked=['_bisect'])
a = [1, 2, 3, 4, 5]
c, p = cb.bisect_left(a, 3, 0, -1), pb.bisect_left(a, 3, 0, -1)
print('bisect_left(a, 3, 0, -1): C', c, 'Python', p)
la, lb = list(a), list(a)
cb.insort_left(la, 3, 0, -1); pb.insort_left(lb, 3, 0, -1)
print('insort_left(a, 3, 0, -1): C', la, 'Python', lb)
doc_ok = all(e < 3 for e in a[0:p]) and all(e >= 3 for e in a[p:-1])
print('Python partition of a[0:ip], a[ip:-1] holds:', doc_ok)
```

</details>

#### 2. bisect: a negative lo raises ValueError with different messages in C and in bisect.py since 3.15

gh-135763 (PR #138394) moved the negative-lo check of `_bisect` out of internal_bisect_left
and internal_bisect_right and into Argument Clinic, as `lo: Py_ssize_t(allow_negative=False)`.
The generated message is "lo cannot be negative", while Lib/bisect.py still says
"lo must be non-negative". On 3.14.7 the twins agreed exactly for every lo and hi in
Py_ssize_t range except hi=-1; that agreement is now false for every negative lo. For
lo >= 0 it still holds (Lean: accel-bisect-twins-agree-nonneg-lo), and both twins still
raise ValueError for every negative lo that fits Py_ssize_t (Lean:
accel-bisect-negative-lo-raises). The move has one further effect, an improvement: C now
refuses lo while parsing it, before converting hi, so bisect_left(a, x, -1, 2**64) gives
ValueError in both twins where 3.14.7 gave OverflowError in C.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
cb = import_fresh_module('bisect', fresh=['_bisect'])
pb = import_fresh_module('bisect', blocked=['_bisect'])
def run(f, *args):
    try:
        return f([1, 2, 3], 2, *args)
    except Exception as e:
        return type(e).__name__, str(e)
rows = [(args, run(cb.bisect_left, *args), run(pb.bisect_left, *args))
        for args in [(-1,), (-1, 2**64)]]
for args, c, p in rows:
    print('bisect_left(a, 2, *%r): C %r | Python %r' % (args, c, p))
if all(c == ('ValueError', 'lo cannot be negative') and
       p == ('ValueError', 'lo must be non-negative') for _, c, p in rows):
```

</details>

#### 3. bisect: lo/hi outside Py_ssize_t raise OverflowError in C but return lo / raise ValueError or IndexError in bisect.py

`_bisect` converts lo and hi to Py_ssize_t during argument parsing, so any int outside
[-2**63, 2**63 - 1] raises OverflowError before the search. The pure-Python twin works on
Python ints: bisect_left(a, x, 2**63) returns 2**63 (the loop never runs), a lo below -2**63
raises ValueError('lo must be non-negative'), and a hi of 2**63 or more raises IndexError when
a[mid] is probed. For lo/hi inside Py_ssize_t (and hi != -1) the twins agree exactly, message
included (Lean: accel-bisect-twins-agree-nonneg-lo), for lo >= 0; the message of a negative lo
differs since 3.15, which is accel-bisect-negative-lo-message. insort_* agree for a huge lo,
because list.insert() then raises the same OverflowError in Python.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
cb = import_fresh_module('bisect', fresh=['_bisect'])
pb = import_fresh_module('bisect', blocked=['_bisect'])
a = [1, 2, 3, 4, 5]
def run(f, *args):
    try:
        return f(a, 3, *args)
    except Exception as e:
        return f'{type(e).__name__}: {e}'
rows = [(args, run(cb.bisect_left, *args), run(pb.bisect_left, *args))
        for args in [(2**63,), (-2**63 - 1,), (0, 2**63), (-1,)]]
for args, c, p in rows:
    print('bisect_left(a, 3, *%r): C %r | Python %r' % (args, c, p))
```

</details>

#### 4. heapq: heappop/heapreplace (and _max) on an empty heap raise IndexError with different messages in C and Python

On an empty list the C functions raise IndexError('index out of range'); the pure-Python twins
raise IndexError('pop from empty list') (heappop, heappop_max: from list.pop()) and
IndexError('list index out of range') (heapreplace, heapreplace_max: from heap[0]). For
comparisons that do not touch the list (they may raise and keep state), this message is the
only difference in outcome: Lean proves the same comparisons, the same returned item, the
same final list and otherwise the same exception for all ten heap primitives
(accel-heap-twins-agree; heapify up to 2500 items, and at every length with an honest
comparison in accel-heapify-twins-agree). The other twin differences, under raising or
re-entrant comparisons, are accel-heapq-py-twin-fallible-compare and
accel-heapq-heapify-order-raising.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
ch = import_fresh_module('heapq', fresh=['_heapq'])
ph = import_fresh_module('heapq', blocked=['_heapq'])
def msg(f, *args):
    try:
        f([], *args)
    except IndexError as e:
        return str(e)
rows = [(name, msg(getattr(ch, name), *args), msg(getattr(ph, name), *args))
        for name, args in [('heappop', ()), ('heappop_max', ()),
                           ('heapreplace', (1,)), ('heapreplace_max', (1,))]]
for name, c, p in rows:
    print(f'{name}([]): C {c!r} | Python {p!r}')
```

</details>

#### 5. heapq: above 2500 items C heapify compares in a different order, so a raising comparison gives a different exception than Python (and than 2500 items)

For lists longer than 2500 items the C heapify uses cache_friendly_heapify
(Modules/_heapqmodule.c:332-363), which sifts the internal nodes in a different
children-first order from Lib/heapq.py's `for i in reversed(range(n//2))`. With a comparison
that always succeeds the result is the same list (Lean: accel-heapify-twins-agree, for every
element type, comparison and length). The source comment says "both ways do the exact same
number of comparisons and produce exactly the same heap" (:326-329). That is true of the final
heap, but the comparisons run in a different order, so a comparison that raises, or keeps
state, can tell the two apart. On list(range(2501)) with a comparison that raises at once, C
first compares items 2045 and 2046, Python items 2499 and 2500, so the two raise different
exceptions (for a TypeError from incomparable items, a different message). In that example the
comparison raises at once, before anything has moved, so both twins leave the list unchanged;
when the comparison raises later, after some sifting, the partly heapified lists differ too.
Up to 2500 items C and Python make exactly the same comparisons in the same order (Lean:
accel-heap-twins-agree); the refutation is accel-heapify-twins-agree-fallible.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
ch = import_fresh_module('heapq', fresh=['_heapq'])
ph = import_fresh_module('heapq', blocked=['_heapq'])

class Item:
    def __init__(self, v): self.v = v
    def __lt__(self, other):
        raise TypeError(f'cannot compare {self.v} with {other.v}')

def first_failure(mod, n):
    try:
        mod.heapify([Item(i) for i in range(n)])
    except TypeError as e:
        return str(e)

rows = [(n, first_failure(ch, n), first_failure(ph, n)) for n in (2500, 2501)]
for n, c, p in rows:
    print(f'heapify of {n} items: C {c!r} | Python {p!r}')
(_, c0, p0), (_, c1, p1) = rows
```

</details>

#### 6. heapq: _heapq ignores a list subclass's overridden methods and rejects non-lists, while heapq.py honours and accepts them

The C functions take any object passing PyList_Check (a list or any subclass) and then work on
the raw list storage (_PyList_AppendTakeRef, _PyList_ITEMS, PyList_SetSlice), so a subclass's
append, __getitem__, __setitem__, __len__ or pop overrides are never called. Lib/heapq.py is
duck-typed: it calls heap.append, heap[i], heap[i] = v, len(heap), heap.pop() and bool(heap),
which dispatch to the overrides, and it accepts objects that are not lists at all.
heappush(LoggedList([1, 2, 3]), 0) for a subclass logging append and __getitem__ leaves
[0, 1, 3, 2] in both, but C calls none of the overrides and Python calls append once and
__getitem__ three times. heapify(()) raises TypeError('heapify() argument must be list, not
tuple') in C and returns None in Python.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
ch = import_fresh_module('heapq', fresh=['_heapq'])
ph = import_fresh_module('heapq', blocked=['_heapq'])

calls = []

class LoggedList(list):
    def append(self, x):
        calls.append('append')
        super().append(x)
    def __getitem__(self, i):
        calls.append('getitem')
        return super().__getitem__(i)

seen = {}
for name, mod in (('C', ch), ('Python', ph)):
    calls.clear()
    h = LoggedList([1, 2, 3])
    mod.heappush(h, 0)
    seen[name] = (list(h), list(calls))
    print(f'{name:6s} heappush(LoggedList([1, 2, 3]), 0): list {list(h)}, overrides called {calls}')

tup = {}
for name, mod in (('C', ch), ('Python', ph)):
    try:
        tup[name] = repr(mod.heapify(()))
    except Exception as e:
        tup[name] = f'{type(e).__name__}: {e}'
    print(f'{name:6s} heapify(()): {tup[name]}')

if (seen['C'][1] == [] and 'append' in seen['Python'][1] and seen['C'][0] == seen['Python'][0]
        and tup['C'].startswith('TypeError') and tup['Python'] == 'None'):
```

</details>

#### 7. heapq.merge raises AttributeError for a valid iterator whose __next__ is a staticmethod, once it is the last input left

merge stores `next = it.__next__` for each input (Lib/heapq.py:365, :388) and, when only one
input is left, delegates to it with `yield from next.__self__` (:383, :408). That assumes
`it.__next__` is a bound method whose `__self__` is the iterator. The iterator protocol does
not require it: a class may define `__next__` as a staticmethod (or any callable that is not
a descriptor binding to the instance), and `next(it)`, `for` loops and `list(it)` accept such
an iterator. Then `it.__next__` is a plain function, and merge raises
`AttributeError: 'function' object has no attribute '__self__'` after yielding that input's
current head. merge(It()) over [1, 2, 3] yields 1, then raises; merge([0, 1], It()) yields
0, 1, 1, then raises. Same with the C and the pure-Python heap functions, with and without a
key. Nothing is lost silently: the error propagates.
Lean: accel-merge-sorted-any-iter (MergeIsSorted with next.__self__ a free callback) is refuted
on the merge(It()) run, checked by the kernel; accel-merge-sorted is proven for iterators whose
__next__ is bound. The difftest generates such iterators (accel_diff.py, "static").

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
ch = import_fresh_module('heapq', fresh=['_heapq'])
ph = import_fresh_module('heapq', blocked=['_heapq'])

def It(items):
    """A valid iterator whose __next__ is a staticmethod."""
    src = iter(items)
    class It:
        def __iter__(self):
            return self
        __next__ = staticmethod(lambda: next(src))
    return It()

print('list(It([1, 2, 3])) ->', list(It([1, 2, 3])))

def run(mod, inputs, key):
    out = []
    try:
        for v in mod.merge(*inputs, key=key):
            out.append(v)
    except Exception as e:
        return out, f'{type(e).__name__}: {e}'
    return out, None

rows = []
for name, mod in (('stock heapq (C heap functions)', ch), ('pure-Python heapq', ph)):
    for key in (None, lambda x: x):
        k = 'key=None' if key is None else 'key=lambda x: x'
        a = run(mod, [It([1, 2, 3])], key)
        b = run(mod, [[0, 1], It([1, 2, 3])], key)
        print(f'{name}, {k}: merge(It([1, 2, 3])) -> {a}; merge([0, 1], It([1, 2, 3])) -> {b}')
        rows.append((a, b))

err = "AttributeError: 'function' object has no attribute '__self__'"
```

</details>

#### 8. heapq.merge: a StopIteration raised by the key (or by __lt__) is taken for an exhausted input, which is silently dropped

merge wraps `value = next(); s[0] = key(value); ...; _heapreplace(h, s)` (Lib/heapq.py:396-402,
and the key=None twin :372-376) and the start-up `value = next(); h_append([key(value), ...])`
(:388-390) in `try ... except StopIteration`, which is meant to catch an exhausted input. A
StopIteration raised by the key, or by an element's `__lt__` during the `_heapreplace`
comparisons inside the try, is caught the same way: the current input is popped from the heap
(:404) and its remaining items, plus the value just fetched, are lost, while merge returns
normally. list(merge([1, 5], [2], key=key)) with key(5) raising StopIteration returns [1, 2].
With the pure-Python heap functions it is worse when the StopIteration comes from `__lt__`
inside `_heapreplace`: `_siftup` has already copied a child into the hole, the popped and the
copied slot then refer to the same entry list, and the in-place `s[0] = next()` updates both,
so merge can yield an item twice (the difftest found [-89, 22, 25, 35, 68, 80, 80] for inputs
holding one 80; accel_diff.py seed 5).
Lean: accel-merge-no-silent-drop is refuted on exactly this case; the model reproduces the
difftest's scripted StopIteration from key, __lt__ and __eq__ at every position.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
ch = import_fresh_module('heapq', fresh=['_heapq'])
ph = import_fresh_module('heapq', blocked=['_heapq'])

def key(x):
    if x == 5:
        raise StopIteration
    return x

rows = []
for name, mod in (('stock heapq (C heap functions)', ch), ('pure-Python heapq', ph)):
    try:
        out = list(mod.merge([1, 5], [2], key=key))
    except Exception as e:
        out = f'{type(e).__name__}: {e}'
    rows.append(out)
    print(f'{name}: list(merge([1, 5], [2], key=key)) -> {out}')
```

</details>

#### 9. heapq: the pure-Python heap functions lose an item when a comparison raises, and have no list-changed-size guard, unlike _heapq

The C sift loops swap items, so when a comparison raises midway the list still holds every
item (heappop/heapreplace drop only the item being returned). Lib/heapq.py moves items into a
hole and keeps `newitem` in a local that it writes back only at the end (Lib/heapq.py:222-233,
:277-292), so when a comparison raises after the first move the list is left with one item
duplicated and `newitem` gone. For heappop on list(range(7)) with a comparison that raises on
its second call (a TypeError from incomparable tie-breakers, say) C leaves [1, 6, 2, 3, 4, 5],
Python [1, 1, 2, 3, 4, 5]: 6 is lost and 1 appears twice. heappush, heapreplace, heappushpop
and heapify lose items the same way.

<details><summary>Reproducer</summary>

```python
from test.support.import_helper import import_fresh_module
ch = import_fresh_module('heapq', fresh=['_heapq'])
ph = import_fresh_module('heapq', blocked=['_heapq'])

class Item:
    calls = 0
    hook = None
    def __init__(self, v): self.v = v
    def __lt__(self, other):
        Item.calls += 1
        if Item.hook: Item.hook(Item.calls)
        return self.v < other.v
    def __repr__(self): return str(self.v)

def run(mod, fn, heap, *args, hook):
    Item.calls, Item.hook = 0, hook
    try:
        out = repr(getattr(mod, fn)(heap, *args))
    except Exception as e:
        out = f'{type(e).__name__}({str(e)!r})'
    Item.hook = None
    return out, heap

# 1. a comparison that raises: C keeps every item, Python duplicates one and loses one
def raise_second(k):
    if k == 2:
        raise TypeError('incomparable')
res = {}
for name, mod in (('C', ch), ('Python', ph)):
    heap = [Item(v) for v in range(7)]
    res[name] = run(mod, 'heappop', heap, hook=raise_second)
    print(f'{name:6s} heappop(list(range(7))), 2nd comparison raises: {res[name][0]}, list left {res[name][1]}')
c_vals = sorted(x.v for x in res['C'][1])
p_vals = sorted(x.v for x in res['Python'][1])
lost = c_vals == [1, 2, 3, 4, 5, 6] and p_vals == [1, 1, 2, 3, 4, 5]

# 2. a comparison that mutates the heap: C raises RuntimeError, Python carries on
res2 = {}
for name, mod in (('C', ch), ('Python', ph)):
    heap = [Item(1), Item(2), Item(3)]
    hook = (lambda h: (lambda k: h.append(Item(99)) if k == 1 else None))(heap)
    res2[name] = run(mod, 'heappush', heap, Item(0), hook=hook)
    print(f'{name:6s} heappush([1, 2, 3], 0), 1st comparison appends 99: {res2[name][0]}, list left {res2[name][1]}')
guard = res2['C'][0].startswith('RuntimeError') and res2['Python'][0] == 'None'
```

</details>

#### 10. heapq.nsmallest and nlargest return more than n items when len(iterable) is below the item count, since 3.15

PR #139087 ("removing redundant slicing in heapq.py") changed the shortcut for n >= size from
`return sorted(iterable, key=key)[:n]` to `return sorted(iterable, key=key)`, in nsmallest and
in nlargest. The slice is redundant only if `len(iterable)` equals the number of items the
iterable yields, and nothing checks that: `size` comes from calling `__len__`, the items from
iterating afterwards. An iterable whose `__len__` reports fewer items than it yields now gets
all of them back. nsmallest(2, it) returns 4 items for an `it` that yields 3, 1, 2, 5 and has
len(it) == 0, and nsmallest(0, it) returns the same 4. On 3.14.7 both results are what the
docs say, sorted(iterable)[:n]. When `__len__` is right the docs still hold, with ties, for
every n >= 0 (Lean: accel-nselect-sorted-prefix, now for any element type with a strict weak order and fallible callbacks).

<details><summary>Reproducer</summary>

```python
import heapq
class Liar:
    def __init__(self, items, n):
        self.items, self.n = items, n
    def __iter__(self):
        return iter(self.items)
    def __len__(self):
        return self.n
items = [3, 1, 2, 5]
s = heapq.nsmallest(2, Liar(items, 0))
l = heapq.nlargest(2, Liar(items, 0))
z = heapq.nsmallest(0, Liar(items, 0))
print('nsmallest(2):', s, 'nlargest(2):', l, 'nsmallest(0):', z)
print('sorted(...)[:2]:', sorted(items)[:2], sorted(items, reverse=True)[:2])
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
