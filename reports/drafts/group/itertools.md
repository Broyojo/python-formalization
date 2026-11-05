<!-- title: itertools: 10 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. itertools.batched preallocates an n-item tuple per batch: MemoryError for large n even on short or empty input

batched_next calls PyTuple_New(n) before reading any item and shrinks it with
_PyTuple_Resize at the end. For a large n this fails even when the input is short:
list(batched('abc', sys.maxsize)) and list(batched([], sys.maxsize)) raise MemoryError,
whereas the documented equivalent (tuple(islice(iterator, n)), rst:175-183) returns
[('a', 'b', 'c')] and []. For n around 10**8-10**9 each batch allocates (and frees) n
pointers, e.g. batched('abc', 10**8) allocates 800 MB to return one 3-tuple. n is accepted
up to sys.maxsize, so "one batch of everything" (n = sys.maxsize) is a plausible but failing
call.
Lean: C and doc agree on the batches and on when they raise for every n whose result tuple
can be allocated (itertools-batched-doc-agree-alloc, proven); itertools-batched-doc-agree is
refuted by n = sys.maxsize.

<details><summary>Reproducer</summary>

```python
import sys, itertools
def run(data):
    try:
        return list(itertools.batched(data, sys.maxsize))
    except MemoryError:
        return 'MemoryError'
a, b = run('abc'), run([])
doc = tuple(itertools.islice(iter('abc'), sys.maxsize))
print("batched('abc', sys.maxsize) ->", a, "; doc equivalent first batch:", doc)
print("batched([], sys.maxsize)    ->", b)
```

</details>

#### 2. combinations/permutations/combinations_with_replacement allocate r indices even when the result is empty (MemoryError instead of an empty iterator)

The constructors allocate and fill an r-element index array (`PyMem_New(Py_ssize_t, r)`,
plus `cycles` for permutations) before looking at whether r > n, where the documented result
is empty ("zero when r > n", math.comb/math.perm). The C code even computes
`stopped = r > n` right afterwards. So combinations('abc', sys.maxsize),
permutations('abc', sys.maxsize) and combinations_with_replacement('', sys.maxsize) raise
MemoryError, any r above a few times 10**9 fails or exhausts memory depending on the
machine, and e.g. combinations('abc', 10**8) allocates and initialises 800 MB and takes
~0.1 s to return an empty iterator. The doc equivalents return immediately.
Lean: the C index machines run in lockstep with the doc generators for every r whose index
array and result tuple can be allocated (itertools-combinatorics-doc-agree-alloc, proven);
itertools-combinatorics-doc-agree-ssize (0 <= r <= sys.maxsize) is refuted by r = sys.maxsize.

<details><summary>Reproducer</summary>

```python
import sys, itertools, math
M = sys.maxsize
cases = [('combinations', lambda: itertools.combinations('abc', M), math.comb(3, M)),
         ('permutations', lambda: itertools.permutations('abc', M), math.perm(3, M)),
         ('combinations_with_replacement', lambda: itertools.combinations_with_replacement('', M), 0)]
bad = 0
for name, make, expected_len in cases:
    try:
        out = list(make())
    except MemoryError:
        out = 'MemoryError'
    print(f'{name}(..., sys.maxsize) -> {out!r}; documented length {expected_len}')
    bad += out == 'MemoryError'
```

</details>

#### 3. itertools.count computes the next value before returning the current one: a failing add loses a value the documented equivalent yields

count_nextlong adds the step before returning the current value, while the equivalent in the docs
yields n and adds on the following call. When the add can fail the two differ:
next(count(10**400, 1.0)) raises OverflowError, where the doc code yields 10**400 first. The value
is not recoverable from the C object by next(), though its repr shows it. A side-effecting __add__
also runs once more in C than in the doc code, for the same number of values.
Lean: count gives the doc generator's values whenever adds cannot fail and no int subclass is
involved (itertools-count-doc-agree-closed, proven); for floats that is exact repeated IEEE-754
addition (itertools-count-float). C and the spec agree on the failing path too
(itertools-count-consistent). itertools-count-doc-agree is refuted by a start whose add raises.

<details><summary>Reproducer</summary>

```python
import itertools
def doc_count(start=0, step=1):
    n = start
    while True:
        yield n
        n += step
doc = next(doc_count(10**400, 1.0))
try:
    c = next(itertools.count(10**400, 1.0))
except OverflowError as e:
    c = e
print('doc:', str(doc)[:8], 'C:', repr(c))
```

</details>

#### 4. itertools.count's fast path drops int subclasses: count(True) gives 1 where count(True, 2) gives True, and __add__ of a subclass is not called

fast_mode tests PyLong_Check, which accepts subclasses, and keeps only the C integer. So
next(count(True)) is the int 1 and repr(count(True)) is count(1), while the doc code yields True,
and so does the slow path: next(count(True, 2)) is True and repr is count(True, 2). A subclass of
int with its own __add__ is likewise ignored on the fast path, as start or as a step equal to 1.
Lean: itertools-count-doc-agree-total-add is refuted by count(True) with an add that cannot
fail; with no int subclass, count and the doc generator agree (itertools-count-doc-agree-closed).

<details><summary>Reproducer</summary>

```python
import itertools
class I(int):
    def __add__(self, other):
        return I(int(self) + 2)
fast = next(itertools.count(True))
slow = next(itertools.count(True, 2))
sub = list(itertools.islice(itertools.count(I(0)), 3))
print(repr(fast), repr(slow), repr(itertools.count(True)), repr(itertools.count(True, 2)), sub)
```

</details>

#### 5. itertools.groupby: a key function (or input) that advances the groupby from inside a group silently drops the new group's first item

_grouper_next checks that its group is current (:669) and that there is no current value
(:671), then calls groupby_step (:672), which runs the input's __next__ (:510) and the key
function (:517). Neither check is repeated after them. If that Python code calls next() on
the groupby object, groupby_next makes a new group current and leaves that group's first item
as currvalue. groupby_step then stores the item it pulled over it (:524-527, the old value is
released), and the old group compares and returns its item as if nothing had happened.
With groupby([1, 1, 1, 2, 2, 3, 3]) and a key whose second call runs next(gb): the old group
gives 1, 1; the inner next(gb) returns key 2; the new group then yields only [2]. The first 2
was made current for that group and released unseen. An input whose __next__ re-enters the
same way loses items too. No crash, no memory error: the released item is a value the
groupby owned.
The doc's pure Python groupby raises ValueError('generator already executing') on the same
re-entry, so the doc gives no behaviour to match.
Lean: GrouperStepKeepsItems ("the step _grouper_next takes to fill an empty value never
releases one") is refuted by the run above, run through the model's own operations;
GrouperStepKeepsItemsNoReentry proves it for every comparison (re-entrant __eq__ included),
key function and input that do not re-enter, and GrouperReentrantStep states exactly what
the step does after any re-entrant code. The difftest runs random key and input hooks
(3 seeds, 60000 cases each, 100%).

<details><summary>Reproducer</summary>

```python
import itertools
calls = [0]
inner = []
def key(x):
    calls[0] += 1
    if calls[0] == 2:
        inner.append(next(gb))   # re-enter while the first group pulls its second item
    return x
gb = itertools.groupby([1, 1, 1, 2, 2, 3, 3], key)
k1, g1 = next(gb)
a = next(g1)
b = next(g1)                     # the key call for the second 1 runs next(gb)
k2, g2 = inner[0]
c = next(g1, 'STOP')
d = list(g2)
rest = [(k, list(g)) for k, g in gb]
print('first group', a, b, c, '| inner key', k2, 'its group', d, '| rest', rest)
```

</details>

#### 6. islice rejects a step above sys.maxsize with 'Step for islice() must be a positive integer or None.'

For start and stop above sys.maxsize, islice says what the limit is ("must be None or an
integer: 0 <= x <= sys.maxsize."; the stop message was clarified for exactly this reason in
bpo-6305 / gh-50554). For the step, an int above sys.maxsize hits the overflow branch of
PyNumber_AsSsize_t, is replaced by -1, and is then reported as
"Step for islice() must be a positive integer or None." although it is a positive integer.
Lean: itertools-islice-step-message (refuted by step = 2**63).

<details><summary>Reproducer</summary>

```python
from itertools import islice
msgs = {}
for name, args in [('start', (2**63, None)), ('stop', (0, 2**63)), ('step', (0, None, 2**63))]:
    try:
        islice('abc', *args)
    except ValueError as e:
        msgs[name] = str(e)
    print(f'{name} = 2**63:', msgs.get(name))
if 'sys.maxsize' in msgs['start'] and 'sys.maxsize' in msgs['stop'] and 'sys.maxsize' not in msgs['step'] \
        and 'positive integer' in msgs['step']:
```

</details>

#### 7. itertools.islice with stop=None yields an extra item when start + step overflows Py_ssize_t

islice_next computes the index of the next item to return with
`lz->next += (size_t)lz->step` and handles overflow with
`if (lz->next < oldnext || (stop != -1 && lz->next > stop)) lz->next = stop;`.
When stop is None, `stop` is the sentinel -1, so an overflow sets `lz->next = -1`. The next
call then skips nothing (`cnt < -1` is false), does not check a stop, and returns the very
next input item; `next` then becomes `-1 + step` and the iterator resumes skipping. So
islice(range(10), 1, None, sys.maxsize) yields [1, 2] instead of [1], and
islice(range(10), 5, None, sys.maxsize - 2) yields [5, 6] instead of [5]. Every argument is
inside the documented range 0 <= x <= sys.maxsize, no error is raised, and the result is
silently wrong. With an int stop the same overflow is harmless (next is set to stop), and
range(10)[1::sys.maxsize] / the documented pure-Python equivalent give [1].
Lean: the C model and the doc equivalent agree on items, consumption and when they raise for
every Py_ssize_t start/stop/step with stop given, or with len + step <= sys.maxsize + 1
(itertools-islice-doc-agree-nowrap, proven); itertools-islice-doc-agree-ssize, without that
hypothesis, is refuted by this reproducer.

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

#### 8. itertools.product with an empty pool keeps a half-filled result tuple with NULL items, reachable through gc.get_referents (segfault on access)

On the first next(), product_next_lock_held allocates the result tuple and stores it in
lz->result at once (:2203-2206), then fills it pool by pool; at the first empty pool it
jumps to `empty` (:2209-2210) and sets stopped, leaving lz->result with NULL items for that
pool and every later one. The object keeps that tuple for its whole life, and
product_traverse (:2176-2183) visits it, so gc.get_referents(p) (and gc.get_objects())
return it. Reading it from Python then fails: repr shows ('a', <NULL>), t[1], list(t),
hash(t) and t[::-1] segfault, and t == ('a', 'b'), 'b' in t and t.count('a') raise
SystemError "bad argument to internal function".
Unlike the general "objects under construction" caveat of gc.get_objects/get_referrers
(gh-59313, gh-39117), this tuple is not temporary: the iterator is finished and the
half-filled tuple stays reachable until the product is freed. Only product does this;
combinations, permutations and combinations_with_replacement fill their first tuple
completely before any `goto empty`.
No Lean model: GC traversal rows are no-behaviour by policy (no heap model), so this is a
probe record only.

<details><summary>Reproducer</summary>

```python
import subprocess, sys
child = r"""
import itertools, gc
p = itertools.product('ab', '')
assert next(p, None) is None
t = [r for r in gc.get_referents(p) if isinstance(r, tuple) and len(r) == 2 and r[0] == 'a'][0]
print(repr(t), flush=True)
t[1]
print("survived")
"""
r = subprocess.run([sys.executable, "-c", child], capture_output=True, text=True)
print(r.stdout.strip(), "exit status", r.returncode)
```

</details>

#### 9. itertools.product with repeat=0 ignores its positional arguments: non-iterables are accepted and raising iterables are never read

product_new sets nargs = 0 when repeat == 0, so the loop that turns each argument into a
tuple never runs. product(5, repeat=0) succeeds and yields one empty tuple, and
product(raising_generator(), repeat=0) never starts the generator. For every other repeat, and
in the documented equivalent (`pools = [tuple(pool) for pool in iterables] * repeat`), all
arguments are read first, so the same call raises TypeError.
The tuples agree whenever the arguments can be read: both sides give [()] for repeat=0. Only
the error, and the side effect of consuming the arguments, differ.
Lean: C and doc agree when repeat=0 is not combined with unreadable arguments
(itertools-product-doc-agree-iterable, proven); itertools-product-doc-agree is refuted by
args = [5], repeat = 0.

<details><summary>Reproducer</summary>

```python
import itertools
def doc_product(*iterables, repeat=1):
    if repeat < 0:
        raise ValueError('repeat argument cannot be negative')
    pools = [tuple(pool) for pool in iterables] * repeat
    result = [[]]
    for pool in pools:
        result = [x+[y] for x in result for y in pool]
    for prod in result:
        yield tuple(prod)
c = list(itertools.product(5, repeat=0))
try:
    doc = list(doc_product(5, repeat=0))
except TypeError as e:
    doc = 'TypeError'
started = []
def gen():
    started.append(1)
    yield 1
list(itertools.product(gen(), repeat=0))
print('C:', c, 'doc:', doc, 'generator started:', bool(started))
print('product(5, repeat=1) raises:', end=' ')
try:
    itertools.product(5, repeat=1)
    print('nothing')
    bad = True
except TypeError as e:
    print(e)
    bad = False
```

</details>

#### 10. itertools arguments are limited to Py_ssize_t while the documented equivalents accept any int (known, won't fix)

islice start/stop/step, combinations/cwr/permutations r, repeat times, batched n, product
repeat and tee n are converted to Py_ssize_t. Ints above sys.maxsize raise (ValueError for
islice, OverflowError elsewhere), while the "Roughly equivalent to" code accepts them:
islice('abc', 2**63) gives 'abc' in the doc code, combinations('abc', 2**63) and
permutations('abc', 2**63) are empty there, repeat(x, 2**63) is effectively endless.
Recorded only so that the broad Lean properties (itertools-islice-doc-agree,
itertools-combinatorics-doc-agree-nonneg, itertools-repeat-doc-agree) have their excluded
case on record; every narrowed version is proven or refuted separately.

<details><summary>Reproducer</summary>

```python
import itertools
out = []
for name, make in [('islice', lambda: list(itertools.islice('abc', 2**63))),
                   ('combinations', lambda: list(itertools.combinations('abc', 2**63))),
                   ('permutations', lambda: list(itertools.permutations('abc', 2**63))),
                   ('repeat', lambda: next(itertools.repeat('x', 2**63)))]:
    try:
        r = make()
    except (ValueError, OverflowError) as e:
        r = type(e).__name__
    out.append(r)
    print(f'{name}(..., 2**63) ->', r)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
