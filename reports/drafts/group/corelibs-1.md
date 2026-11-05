<!-- title: Small inconsistencies in functools, enum, random and other core library modules found by a formal model (part 1 of 2) -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. dataclasses.asdict and astuple turn a Counter field into a Counter of (key, count) pairs

For a dict subclass without default_factory, _asdict_inner builds obj_type((k, v) for ...). dict accepts pairs, and Counter counts what it is given, so Counter({'a': 2, 'b': 1}) comes back as Counter({('a', 2): 1, ('b', 1): 1}). The data is changed with no error, in asdict and astuple.

<details><summary>Reproducer</summary>

```python
from collections import Counter
from dataclasses import dataclass, asdict, astuple
@dataclass
class C:
    x: object
a = asdict(C(Counter('aab')))['x']
b = astuple(C(Counter('aab')))[0]
print(a, b)
```

</details>

#### 2. enum.unique and verify(UNIQUE) report every member as a duplicate when the class defines its own name

unique and the UNIQUE check of verify look for aliases by comparing each key of __members__ with member.name. member.name is a public attribute that a class may redefine, and a property such as `def name(self): return self._name_.lower()` is accepted: the rest of enum reads _name_ and works. With such a class there is no alias, and yet @unique raises "duplicate values found in <enum 'Color'>: RED -> red, GREEN -> green". verify(CONTINUOUS) has the same shape with e.value. _add_value_alias_ files an unhashable value under self.name at Lib/enum.py:1262, and Enum.__new__ then does cls[name] at :1193, so Color([1]) raises KeyError 'red' from a lookup that should end in the member.

<details><summary>Reproducer</summary>

```python
from enum import Enum, unique, verify, UNIQUE
class Color(Enum):
    RED = 1
    GREEN = 2
    @property
    def name(self):
        return self._name_.lower()
def attempt(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
a = attempt(lambda: unique(Color))
b = attempt(lambda: verify(UNIQUE)(Color))
Color.RED._add_value_alias_([1])
c = attempt(lambda: Color([1]))
print(a, b, c)
```

</details>

#### 3. Enum._add_value_alias_ does not keep its ValueError for an unhashable value

The docs say that _add_value_alias_ raises ValueError if the value is already linked with a different member. That holds for a hashable value. For an unhashable one it fails in two ways. When the value is another member's _value_, the ValueError at Lib/enum.py:1251 is formatted with cls._value2member_map_[value], which hashes the value again, so TypeError "cannot use 'list' as a dict key" comes out instead. When the value was linked by an earlier _add_value_alias_, the long search at :1248-1252 only reads _value_, does not see it, and the second member is linked as well, with no error: D.A._add_value_alias_([9]) and then D.B._add_value_alias_([9]) both succeed, and D([9]) finds the first.

<details><summary>Reproducer</summary>

```python
from enum import Enum
class C(Enum):
    A = [1]
    B = 2
class D(Enum):
    A = 1
    B = 2
def attempt(f):
    try:
        f()
        return 'no error'
    except Exception as e:
        return type(e).__name__
first = attempt(lambda: C.B._add_value_alias_([1]))
D.A._add_value_alias_(9)
hashable = attempt(lambda: D.B._add_value_alias_(9))
D.A._add_value_alias_([9])
second = attempt(lambda: D.B._add_value_alias_([9]))
print(first, hashable, second, D._unhashable_values_map_)
```

</details>

#### 4. ExitStack can create a __context__ cycle that nested with statements cannot, and its own while 1 loop then never ends

`_fix_exception_context` (Lib/contextlib.py:637-649) has two related defects.

<details><summary>Reproducer</summary>

```python
import contextlib, signal
def on_alarm(*_):
    raise TimeoutError
signal.signal(signal.SIGALRM, on_alarm)
saved = {}
def first(*exc):
    try:
        raise KeyError('B')
    except KeyError as b:
        saved['b'] = b
        raise ValueError('A')
def second(*exc):
    raise saved['b']
try:
    with contextlib.ExitStack() as stack:
        stack.push(second)
        stack.push(first)
        raise RuntimeError('F')
except KeyError as e:
    got = e
chain = []
c = got
while c is not None and len(chain) < 5:
    chain.append(type(c).__name__)
    c = c.__context__
print('ExitStack chain:', chain)
saved.clear()
class CM:
    def __init__(self, f):
        self.f = f
    def __enter__(self):
        return self
    def __exit__(self, *exc):
        self.f(*exc)
try:
    with CM(second):
        with CM(first):
            raise RuntimeError('F')
except KeyError as e:
    nested = e
chain2 = []
c = nested
while c is not None and len(chain2) < 5:
    chain2.append(type(c).__name__)
    c = c.__context__
print('nested with chain:', chain2)
def third(*exc):
    raise got
stack = contextlib.ExitStack()
stack.push(third)
signal.alarm(3)
hang = False
try:
    stack.close()
except TimeoutError:
    hang = True
except KeyError:
    pass
signal.alarm(0)
print('second ExitStack hangs:', hang)
def run(co):
    try:
        co.send(None)
    except StopIteration as e:
        return e.value
    raise AssertionError('suspended')
async def afirst(*exc):
    first(*exc)
async def asecond(*exc):
    second(*exc)
async def body():
    async with contextlib.AsyncExitStack() as astack:
        astack.push_async_exit(asecond)
        astack.push_async_exit(afirst)
        raise RuntimeError('F')
saved.clear()
try:
    run(body())
except KeyError as e:
    agot = e
achain = []
c = agot
while c is not None and len(achain) < 5:
    achain.append(type(c).__name__)
    c = c.__context__
print('AsyncExitStack chain:', achain)
async def athird(*exc):
    raise agot
astack = contextlib.AsyncExitStack()
astack.push_async_exit(athird)
signal.alarm(3)
ahang = False
try:
    run(astack.aclose())
except TimeoutError:
    ahang = True
except KeyError:
    pass
signal.alarm(0)
print('second AsyncExitStack hangs:', ahang)
```

</details>

#### 5. A cache around a cached function reports the inner cache's cache_parameters, and in pure Python its cache_info too

lru_cache sets wrapper.cache_parameters and only then calls update_wrapper(wrapper, user_function), which copies user_function.__dict__ over it. When the user function is a cached function, as with stacked decorators or lru_cache(maxsize=5)(some_cached), outer.cache_parameters() reports the inner's maxsize and typed. On the Python wrapper, cache_info and cache_clear are entries of the same __dict__, so they are overwritten too: outer.cache_info() reads the inner cache, and outer.cache_clear() clears the inner one and leaves the outer full.

<details><summary>Reproducer</summary>

```python
from functools import lru_cache
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
def build(m):
    inner = m.lru_cache(maxsize=7)(lambda x: x)
    return m.lru_cache(maxsize=5, typed=True)(inner), inner
outer, inner = build(__import__('functools'))
p = outer.cache_parameters()
pouter, pinner = build(py)
pouter(1)
before = pouter.cache_info()
print(p, before)
```

</details>

#### 6. functools.partial flattens a partial subclass, so the subclass's __call__ never runs

partial(p, x) merges p's stored function and arguments when p is an instance of partial. The test is isinstance, so it also matches a subclass that overrides __call__: partial(Sub(f, 1), 2)() calls f(1, 2) and never reaches Sub.__call__. The twins also disagree on a related case: C does not flatten a partial that has an instance __dict__, Python does, so partial(p, 2).func is p in C and f in the pure-Python module.

<details><summary>Reproducer</summary>

```python
from functools import partial
def target(*args):
    return ('target', args)
class Sub(partial):
    def __call__(self, *args, **kwargs):
        return ('override', self.args + args)
outer = partial(Sub(target, 1), 2)
direct = Sub(target, 1)(2)
wrapped = outer()
print('direct:', direct, 'wrapped:', wrapped, 'outer.func:', outer.func)
```

</details>

#### 7. A random.Random subclass whose __init__ does not call super().__init__() silently returns 0.0 forever

Since Python 3.11 _random.Random seeds in tp_init, and tp_new is PyType_GenericNew, which leaves index = 0 and all 624 words zero. All-zero is the fixed point of the Mersenne Twister recurrence. random.Random.__init__ seeds, so a plain Random() is fine, but a subclass that defines __init__ and does not chain up never seeds. No error is raised: random() returns 0.0 every time, randrange(100) returns 0, and shuffle and sample become one fixed permutation. Before 3.11 the same class worked, because tp_new seeded (bpo-44260 moved it). random.Random.__new__(random.Random) and _random.Random.__new__(_random.Random, 5) behave the same way; the seed argument of the second one is ignored.

<details><summary>Reproducer</summary>

```python
import random, _random
class Sub(random.Random):
    def __init__(self, label):
        self.label = label
s = Sub('x')
floats = {s.random() for _ in range(2000)}
ints = {s.randrange(100) for _ in range(2000)}
print(floats, ints)
raw = _random.Random.__new__(_random.Random, 5)
print(raw.random())
plain = {random.Random().random() for _ in range(5)}
```

</details>

#### 8. @f.register registers the first annotation found, which can be the return type or a later parameter

With a bare @f.register, register takes `next(iter(get_type_hints(func).items()))`: the first entry of the hints, whatever its name. `def g(x) -> int` therefore registers the implementation for int, on the return annotation, and `def g(x, y: str)` registers it for str, on the second parameter. Neither raises, and calling f(1) then silently runs g. The docs say that the decorator infers the type of the first argument.

<details><summary>Reproducer</summary>

```python
import functools
@functools.singledispatch
def f(x):
    return 'default'
@f.register
def g(x) -> int:
    return 'g'
@f.register
def h(x, y: str):
    return 'h'
print(f(1), sorted(k.__name__ for k in f.registry))
```

</details>

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
