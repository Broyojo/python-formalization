<!-- title: corelibs: 74 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. collections.abc.AsyncGenerator.aclose says 'asynchronous generator ignored GeneratorExit', builtin aclose() says 'async generator ignored GeneratorExit'

When an async generator yields instead of finishing after GeneratorExit is thrown in, both the
mixin AsyncGenerator.aclose and the builtin async_generator.aclose() raise RuntimeError, but with
different messages: the mixin says "asynchronous generator ignored GeneratorExit", the builtin
"async generator ignored GeneratorExit". For generators and coroutines the mixin and the builtin
use the same text ("generator ignored GeneratorExit", "coroutine ignored GeneratorExit"), so the
async family is the odd one out. Code that matches the message, or a test that compares a wrapper
with the generator it wraps, sees the difference.

<details><summary>Reproducer</summary>

```python
from collections.abc import AsyncGenerator
def drive(c):
    try:
        c.send(None)
    except StopIteration as e:
        return e.value
    raise AssertionError("suspended")
def msg(f):
    try:
        f()
    except RuntimeError as e:
        return str(e)
class Mixin(AsyncGenerator):
    async def asend(self, value):
        return 1
    async def athrow(self, *args):
        return 1   # yields instead of closing
async def builtin():
    try:
        yield 1
    except GeneratorExit:
        yield 2
b = builtin()
drive(b.asend(None))
builtin_msg = msg(lambda: drive(b.aclose()))
mixin_msg = msg(lambda: drive(Mixin().aclose()))
print('builtin:', builtin_msg)
print('mixin:  ', mixin_msg)
```

</details>

#### 2. collections.abc.Callable[[[int]], str] does not survive copy or pickle: __reduce__ skips the re-listing for a list first argument

_CallableGenericAlias flattens the argument list into __args__, so Callable[[[int]], str] has
__args__ ([int], str). __reduce__ re-lists the arguments unless there are two of them and the
first is a parameter expression, and _is_param_expr counts any list as one. So for this alias
__reduce__ returns the flat ([int], str) and rebuilding it flattens once more: copy.copy, deepcopy
and pickle give an alias with __args__ (int, str), which is not equal to the original, though
both reprs read "collections.abc.Callable[[int], str]".

<details><summary>Reproducer</summary>

```python
import copy, pickle
from collections.abc import Callable
c = Callable[[[int]], str]
copied = copy.copy(c)
pickled = pickle.loads(pickle.dumps(c))
print(c.__args__, copied.__args__, pickled.__args__, repr(c), repr(copied))
```

</details>

#### 3. cmp_to_key twins differ on a right operand with .obj, and on != when mycmp returns an object

The pure-Python K reads `other.obj` from whatever `other` is, so K(1) < Duck() works for any object with an
obj attribute. keyobject_richcompare tests the exact type first and raises TypeError "other argument must be
K instance". Separately, Python's K has no __ne__, so `!=` is object.__ne__, the negation of the truth of
__eq__, while C runs `res != 0` itself. With a mycmp returning an object whose __ne__ differs from the
negation of __eq__, the two give different values.

<details><summary>Reproducer</summary>

```python
import functools
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
def cmp(a, b):
    return a - b
class Duck:
    obj = 5
def lt(m):
    try:
        return m.cmp_to_key(cmp)(1) < Duck()
    except TypeError as e:
        return 'TypeError'
class Res:
    def __eq__(self, o):
        return False
    def __ne__(self, o):
        return 'ne'
def ne(m):
    K = m.cmp_to_key(lambda a, b: Res())
    return K(1) != K(2)
print('C:', lt(functools), ne(functools), 'Python:', lt(py), ne(py))
```

</details>

#### 4. copy.deepcopy of a bound method whose __self__ refers back to it makes two copies of the method

_deepcopy_method (Lib/copy.py:220-221) returns type(x)(x.__func__, deepcopy(x.__self__, memo))
without looking in memo again after copying __self__. When __self__ reaches the method again (an
instance that stores its own bound method, a callback registry, an object graph holding both the
method and its instance), copying __self__ copies the method once through that reference and records
it in memo; _deepcopy_method then builds a second method object and deepcopy (:159-160) overwrites
the memo entry with it. The result is two distinct copies of one source object: for a.m = a.f,
deepcopy(a.m).__self__.m is not the copy, and deepcopy([a.m, a]) gives r[0] is not r[1].m, while the
source has a.m.__self__.m is a.m. The order matters: deepcopy([a, a.m]) keeps the identity, because
the instance is copied first. _deepcopy_tuple (:181-187) has the same shape of problem and solves it by
reading memo[id(x)] after copying its items; _deepcopy_frozendict (:213-216) does the same.

<details><summary>Reproducer</summary>

```python
import copy
class A:
    def f(self):
        pass
a = A()
a.m = a.f
c = copy.deepcopy(a.m)
r = copy.deepcopy([a.m, a])
b = A()
b.t = (b,)
ct = copy.deepcopy(b.t)
outcome = {'orig': a.m.__self__.m is a.m, 'copy': c.__self__.m is c, 'list': r[0] is r[1].m,
           'tuple': ct[0].t is ct}
print(outcome)
```

</details>

#### 5. copy.copy and copy.deepcopy raise TypeError on a __reduce__ result with a state_setter, which pickle accepts

DUPLICATE of the closed python/cpython#90494, which is why this stays a record and is not to be
filed. There serhiy-storchaka made the old `deepcopy` parameter keyword-only and said support for the
sixth item is a new feature that needs its own issue. No such issue turned up. Since 3.8 __reduce__ may return a sixth item, a state_setter callable, and pickle honours it. The
copy module unpacks the same result into _reconstruct(x, None, *rv), whose signature takes five
items, so a class using that form pickles fine and fails in copy.copy and copy.deepcopy with
"_reconstruct() takes from 4 to 7 positional arguments but 8 were given", even when the sixth
item is None.

<details><summary>Reproducer</summary>

```python
import copy, pickle
def build():
    return Thing()
def setter(obj, state):
    obj.state = state
class Thing:
    def __reduce__(self):
        return (build, (), 5, None, None, setter)
outcome = {}
pickled = pickle.loads(pickle.dumps(Thing(), protocol=4))
outcome['pickle'] = pickled.state
for f in (copy.copy, copy.deepcopy):
    try:
        outcome[f.__name__] = f(Thing()).state
    except TypeError as e:
        outcome[f.__name__] = type(e).__name__
print(outcome)
```

</details>

#### 6. _count_elements: the C fast path ignores an instance `get` and reports unhashable elements without the dict message

Counter.update(iterable) calls _count_elements(self, iterable), whose C version replaces the pure-Python
one. The two differ twice.
(1) The Python twin binds `mapping.get` (Lib/collections/__init__.py:542), which finds a `get` stored in
the instance dict. The C function chooses its fast path by looking `get` and `__setitem__` up on the type
(Modules/_collectionsmodule.c:2566-2573) and then reads the dict storage directly, so an instance attribute
is never called: `c = Counter(); c.get = lambda k, d=0: 10; c.update('a')` stores 1 with the C helper and
11 with the Python one.
(2) For an unhashable element the fast path raises the bare hash error, `TypeError: unhashable type: 'list'`
(:2591-2594, `_PyObject_HashFast`), while the Python twin's `dict.get` and the C slow path go through
`dict_unhashable_type` (Objects/dictobject.c:2442-2460) and raise
`TypeError: cannot use 'list' as a dict key (unhashable type: 'list')`, the 3.15 message.

<details><summary>Reproducer</summary>

```python
import collections
from test.support import import_helper
py = import_helper.import_fresh_module('collections', blocked=['_collections'])
def inst(m):
    c = m.Counter()
    c.get = lambda k, d=0: 10
    c.update('a')
    return c['a']
def unhashable(m):
    try:
        m.Counter().update([[1]])
    except TypeError as e:
        return str(e)
a, b = inst(collections), inst(py)
u, v = unhashable(collections), unhashable(py)
print('C:', a, repr(u), 'Python:', b, repr(v))
```

</details>

#### 7. dataclasses.asdict and astuple turn a Counter field into a Counter of (key, count) pairs

For a dict subclass without default_factory, _asdict_inner builds obj_type((k, v) for ...). dict accepts pairs,
and Counter counts what it is given, so Counter({'a': 2, 'b': 1}) comes back as Counter({('a', 2): 1, ('b', 1): 1}).
The data is changed with no error, in asdict and astuple.

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

#### 8. dataclasses.asdict raises TypeError on a dict field keyed by a frozen dataclass, where astuple works

_asdict_inner converts the keys of a dict too, and a dataclass key becomes a dict, which cannot be a key, so
asdict(C({K(1): 2})) raises TypeError. astuple makes the key a tuple, and works.

<details><summary>Reproducer</summary>

```python
from dataclasses import dataclass, asdict, astuple
@dataclass
class C:
    x: object
@dataclass(frozen=True)
class K:
    a: int
t = astuple(C({K(1): 2}))
try:
    asdict(C({K(1): 2}))
    r = 'no error'
except TypeError:
    r = 'TypeError'
print(t, r)
```

</details>

#### 9. An InitVar with init=False makes every instantiation raise NameError in generated code

x: InitVar[int] = field(default=1, init=False) is accepted by @dataclass. If the class has a __post_init__, the
generated __init__ passes every InitVar by name, and x is not a parameter of __init__, so C() raises
NameError: name 'x' is not defined, from code the user did not write. A TypeError when the class is defined
would say what is wrong.

<details><summary>Reproducer</summary>

```python
from dataclasses import dataclass, field, InitVar
@dataclass
class C:
    x: InitVar[int] = field(default=1, init=False)
    def __post_init__(self, x):
        pass
try:
    C()
    r = 'no error'
except NameError as e:
    r = 'NameError'
print(r)
```

</details>

#### 10. Any int is `in` a CONFORM Flag class, whose own value it is not

EnumType.__contains__ answers for a Flag class by calling cls._missing_(value) and looking at the type of the
result. Under CONFORM, _missing_ drops the unknown bits and returns a member, so `8 in F` is True for a class with
A = 1 and B = 2, although F(8) is F(0), and no member or pseudo-member has the value 8. The same goes for any int,
which makes the test vacuous on such a class, while the same value in the same class under STRICT or EJECT is False.

<details><summary>Reproducer</summary>

```python
from enum import Flag, CONFORM
class F(Flag, boundary=CONFORM):
    A = 1
    B = 2
print(8 in F, F(8), F(8).value)
```

</details>

#### 11. Iterating a Flag alias with unnamed bits yields None, or raises AttributeError when the members are not in value order

Flag._iter_member_by_value_ (Lib/enum.py:1456-1461) yields `cls._value2member_map_.get(val)` for each bit of
`value & _flag_mask_`, so a bit no member has gives None: for `class H(Flag): A = 1; X = 6`, list(H.X) is
[None, None]. Once `H(2)` has been called, the pseudo-member it stored at :1566 is found instead, and list(H.X)
becomes [<H: 2>, None], so the result of iterating a member depends on what was looked up before.
For a class whose single-bit members are not defined in value order, _iter_member_ is _iter_member_by_def_
(:663-667), which sorts those same items by `m._sort_order_` (:1466-1473): there the None raises
AttributeError: 'NoneType' object has no attribute '_sort_order_' (`class G(Flag): B = 2; A = 1; X = 12`), and a
stored pseudo-member raises AttributeError: 'G' object has no attribute '_sort_order_'. So the same alias is
iterated as Nones, as pseudo-members, or as an exception, depending on definition order and history.

<details><summary>Reproducer</summary>

```python
from enum import Flag
class H(Flag):
    A = 1
    X = 6
first = list(H.X)
H(2)
second = list(H.X)
class G(Flag):
    B = 2
    A = 1
    X = 12
try:
    list(G.X)
    third = 'no error'
except AttributeError as e:
    third = 'AttributeError: %s' % e
print(first, second, third)
```

</details>

#### 12. len(flag) counts bits outside the class, so it disagrees with iteration under KEEP and for IntFlag

Flag.__len__ returns self._value_.bit_count(), while __iter__ goes through _iter_member_ on
value & _flag_mask_. With the KEEP boundary, the default for IntFlag, a value can hold bits outside the
class: Perm(8) of a three-bit IntFlag has len 1 and no members.

<details><summary>Reproducer</summary>

```python
from enum import IntFlag
class Perm(IntFlag):
    R = 4
    W = 2
    X = 1
p = Perm(8 | 4)
print(repr(p), len(p), list(p))
```

</details>

#### 13. enum.unique and verify(UNIQUE) report every member as a duplicate when the class defines its own name

unique and the UNIQUE check of verify look for aliases by comparing each key of __members__ with member.name.
member.name is a public attribute that a class may redefine, and a property such as `def name(self): return
self._name_.lower()` is accepted: the rest of enum reads _name_ and works. With such a class there is no alias,
and yet @unique raises "duplicate values found in <enum 'Color'>: RED -> red, GREEN -> green". verify(CONTINUOUS)
has the same shape with e.value. _add_value_alias_ files an unhashable value under self.name at
Lib/enum.py:1262, and Enum.__new__ then does cls[name] at :1193, so Color([1]) raises KeyError 'red' from a lookup
that should end in the member.

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

#### 14. A STRICT Flag accepts a value made only of bits that exist inside a multi-bit member, then rejects it in combinations

For class F(Flag): A = 1; X = 6, the default STRICT boundary rejects F(3) with "no members with value
2", yet F(2) is accepted as a nameless pseudo-member. Flag._missing_ tests `not combined_value` before
the strict test, so a value with no member at all skips the check. The accepted F(2) then breaks
closure: F(2) | F.A raises ValueError, though both operands are valid values of the class.

<details><summary>Reproducer</summary>

```python
from enum import Flag
class F(Flag):
    A = 1
    X = 6
def attempt(f):
    try:
        return f()
    except ValueError as e:
        return 'ValueError'
two = attempt(lambda: F(2))
three = attempt(lambda: F(3))
combined = attempt(lambda: F(2) | F.A)
print(repr(two), three, combined)
```

</details>

#### 15. Enum._add_value_alias_ silently accepts a value linked to another member when a repr raises TypeError

The docs say that _add_value_alias_ raises ValueError if the value is already linked with a different member. The
ValueError of Lib/enum.py:1244 is raised inside the try of :1241, and the message runs repr() of the value and of
the bound member. If either repr raises TypeError (a __repr__ of the class that returns a non-str, or a value whose
__repr__ has a TypeError bug), the except TypeError of :1246, which is meant for unhashable values, catches it. The
long search there reads only the members' _value_, so it does not see a link made by an earlier _add_value_alias_.
Control then falls through to the binding at :1253-1262. That binding does setdefault, which keeps the old link, and
appends the value to _hashable_values_ again, a list on 3.15.2. The call returns None. It raises neither the
ValueError nor the TypeError of the repr, and the value stays linked to the first member.

<details><summary>Reproducer</summary>

```python
from enum import Enum
class W(Enum):
    A = 1
    B = 2
    def __repr__(self):
        return 5
W.B._add_value_alias_(3)
try:
    r = W.A._add_value_alias_(3)
    outcome = 'returned %r' % (r,)
except Exception as e:
    outcome = type(e).__name__
print(outcome, W(3) is W.B, list(W._hashable_values_))
```

</details>

#### 16. Enum._add_value_alias_ does not keep its ValueError for an unhashable value

The docs say that _add_value_alias_ raises ValueError if the value is already linked with a different member.
That holds for a hashable value. For an unhashable one it fails in two ways. When the value is another member's
_value_, the ValueError at Lib/enum.py:1251 is formatted with cls._value2member_map_[value], which hashes the
value again, so TypeError "cannot use 'list' as a dict key" comes out instead. When the value was linked by an
earlier _add_value_alias_, the long search at :1248-1252 only reads _value_, does not see it, and the second member
is linked as well, with no error: D.A._add_value_alias_([9]) and then D.B._add_value_alias_([9]) both succeed, and
D([9]) finds the first.

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

#### 17. verify(...)(x) reads x.__name__ before its type check, so a non-class gets AttributeError or issubclass's TypeError, not verify's

verify.__call__ starts with `cls_name = enumeration.__name__` (Lib/enum.py:1970) and only then asks
`issubclass(enumeration, Flag)` / `issubclass(enumeration, Enum)` (:1971-1976), whose else branch raises
TypeError("the 'verify' decorator only works with Enum and Flag"). That message is therefore reached only for a
class that is not an Enum. An object without __name__, such as `verify(UNIQUE)(42)`, raises
AttributeError: 'int' object has no attribute '__name__'; a function, which has a __name__, raises the
TypeError "issubclass() arg 1 must be a class" from issubclass itself.

<details><summary>Reproducer</summary>

```python
from enum import verify, UNIQUE
try:
    verify(UNIQUE)(42)
    r1 = 'no error'
except Exception as e:
    r1 = '%s: %s' % (type(e).__name__, e)
try:
    verify(UNIQUE)(len)
    r2 = 'no error'
except Exception as e:
    r2 = '%s: %s' % (type(e).__name__, e)
try:
    verify(UNIQUE)(int)
    r3 = 'no error'
except Exception as e:
    r3 = '%s: %s' % (type(e).__name__, e)
print(r1); print(r2); print(r3)
```

</details>

#### 18. EnumDict used directly has no _generate_next_value, so auto() fails, and update then stores the wrong keys

EnumDict has been public since 3.13. EnumDict.__init__ does not set _generate_next_value; only the __setitem__ of
'_generate_next_value_' in EnumType.__prepare__ does. So d = EnumDict('C'); d['A'] = auto() raises AttributeError:
'EnumDict' object has no attribute '_generate_next_value'. EnumDict.update makes it worse. Its try wraps the whole
loop over members.keys(), so the AttributeError from __setitem__ is taken to mean that members has no keys method,
and it goes on with `for name, value in members`, which unpacks the keys of the mapping. d.update({'AB': auto()})
therefore raises nothing and leaves {'A': 'B'} in the namespace.

<details><summary>Reproducer</summary>

```python
from enum import EnumDict, auto
d = EnumDict('C')
try:
    d['A'] = auto()
    first = 'no error'
except AttributeError as e:
    first = 'AttributeError'
e2 = EnumDict('C')
e2.update({'AB': auto()})
print(first, dict(e2))
```

</details>

#### 19. ExitStack can create a __context__ cycle that nested with statements cannot, and its own while 1 loop then never ends

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

#### 20. ExitStack.enter_context and push use a metaclass's __enter__/__exit__ on an instance, which the with statement refuses

`_lookup_special(obj, name, default)`, new in 3.15 (Lib/contextlib.py:534-542), says it follows
"the standard lookup behaviour for special methods" (:535) and does
`getattr_static(type(obj), name)`. But `getattr_static` on a class also searches the class's
metaclass when the class's own MRO has no such attribute ("for types we check the metaclass too",
Lib/inspect.py:1796-1803). The interpreter's special lookup, `_PyObject_LookupSpecial` and
`_PyObject_LookupSpecialMethod` (Objects/typeobject.c:2990-3002, :3009), looks at the MRO of
`type(obj)` only.

<details><summary>Reproducer</summary>

```python
import contextlib
class Meta(type):
    def __enter__(self):
        return 'meta'
    def __exit__(self, *exc):
        return True
class C(metaclass=Meta):
    pass
try:
    with C():
        pass
    with_ok = True
except TypeError as e:
    with_ok = False
    print('with C():', e)
got = contextlib.ExitStack().enter_context(C())
print('ExitStack().enter_context(C()):', repr(got))
stack = contextlib.ExitStack()
stack.push(C())
try:
    with stack:
        raise ValueError('lost')
    suppressed = True
except ValueError:
    suppressed = False
print('push(C()) suppressed ValueError:', suppressed)
```

</details>

#### 21. collections.abc.Generator.close discards the value that builtin generator.close() returns

Since 3.13 (gh-104770) generator.close() returns the value of a generator that catches
GeneratorExit and returns. The mixin Generator.close was not updated: it catches StopIteration
and falls off the end, so a Generator subclass delegating send and throw to a real generator
returns None from close(), where the wrapped generator returned a value. Coroutine.close has the
same shape.

<details><summary>Reproducer</summary>

```python
from collections.abc import Generator
def g():
    try:
        yield 1
    except GeneratorExit:
        return 7
class Wrapped(Generator):
    def __init__(self):
        self.g = g()
    def send(self, value):
        return self.g.send(value)
    def throw(self, *args):
        return self.g.throw(*args)
b = g()
next(b)
builtin = b.close()
m = Wrapped()
next(m)
mixin = m.close()
print('builtin close:', builtin, 'mixin close:', mixin)
```

</details>

#### 22. ItemsView.__contains__ raises for non-pairs and accepts lists, unlike dict_items; set operators inherit the crash

DUPLICATE of the open python/cpython#68622; do not file separately. dict_items.__contains__ is False
for anything but a 2-tuple. ItemsView.__contains__ runs `key, value = item` outside its try, so a
non-iterable raises TypeError, a wrong-length iterable raises ValueError, and ['a', 1] is True. What
the old issue does not list is the consequence for the Set mixins, which call __contains__:
M.items() & [1, 2], [1, 2] & M.items(), [1, 2] - M.items(), M.items() ^ [1, 2],
M.items().isdisjoint([1, 2]) and M.items() >= {1} all raise TypeError, where the dict_items
equivalents return. Mappings with a Python ItemsView include os.environ, shelve and UserDict.

<details><summary>Reproducer</summary>

```python
from collections.abc import Mapping
class M(Mapping):
    def __init__(self, d):
        self.d = d
    def __getitem__(self, k):
        return self.d[k]
    def __iter__(self):
        return iter(self.d)
    def __len__(self):
        return len(self.d)
def attempt(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
d = {'a': 1}
cases = [lambda x: 1 in x, lambda x: (1, 2, 3) in x, lambda x: ['a', 1] in x,
         lambda x: x & [1, 2], lambda x: x.isdisjoint([1, 2]), lambda x: x ^ [1, 2]]
builtin = [attempt(lambda c=c: c(d.items())) for c in cases]
mixin = [attempt(lambda c=c: c(M(d).items())) for c in cases]
print('dict_items', builtin)
print('ItemsView ', mixin)
if mixin[:3] == ['TypeError', 'ValueError', True] and builtin[:3] == [False, False, False] \
        and mixin[3:5] == ['TypeError', 'TypeError'] and mixin[5] == 'TypeError':
```

</details>

#### 23. lru_cache(maxsize=2**63) raises OverflowError with the C wrapper and works with the Python wrapper

lru_cache accepts any int. The C wrapper converts maxsize with PyNumber_AsSsize_t and raises
OverflowError above sys.maxsize, at decoration time, where the Python wrapper keeps the int and
behaves as a large bounded cache. Negative values are clamped first by lru_cache, so they agree.

<details><summary>Reproducer</summary>

```python
import sys
import functools
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
def f():
    return 0
def attempt(m):
    try:
        return m.lru_cache(maxsize=sys.maxsize + 1)(f).cache_info().maxsize
    except OverflowError as e:
        return type(e).__name__
c_result, py_result = attempt(functools), attempt(py)
print('C:', c_result, 'Python:', py_result)
```

</details>

#### 24. lru_cache holds maxsize + 1 entries for good after a key's __eq__ re-enters the cache during the store

Both twins decide whether the cache is full before the store and do not look again. The store compares a colliding key,
so a key's __eq__ can run a nested call of the cached function there. That call sees a cache with room and adds its own
entry. The outer store then adds a second one, and the cache holds maxsize + 1 entries. From then on each miss evicts one
entry and adds one, so currsize stays above maxsize for the life of the cache.

<details><summary>Reproducer</summary>

```python
import functools
box = {'n': 0, 'hook': None}
class K:
    def __init__(self, v, h):
        self.v, self.h = v, h
    def __hash__(self):
        return self.h
    def __eq__(self, o):
        box['n'] += 1
        if box['n'] == 3 and box['hook']:
            hook, box['hook'] = box['hook'], None
            hook()
        return self is o
f = functools.lru_cache(maxsize=2)(lambda k: k.v)
a, b, c = K(1, 0), K(2, 0), K(3, 1)
f(a)
box['hook'] = lambda: f(c)
box['n'] = 0
f(b)                       # lookup, lookup after the call, store: the third comparison is the store
sizes = [f.cache_info().currsize]
for i in range(10, 15):
    f(K(i, i))
    sizes.append(f.cache_info().currsize)
print(sizes, f.cache_info())
```

</details>

#### 25. After a failed del in the pure Python lru_cache, a hit on the old key returns None

The bounded wrapper empties the oldest link and makes it the new root before `del cache[oldkey]`. If that raises, from the
__eq__ of a key that collides with it, the dict keeps oldkey, and its link is now the root, whose key and result are
None. The next call with oldkey is a hit that returns None, and rewires the root to point at itself; a later eviction
raises KeyError. The comment at :701-703 is careful about the assignment after the del, and not about the del itself.
The C wrapper puts the link back, and keeps the value.

<details><summary>Reproducer</summary>

```python
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
c = import_helper.import_fresh_module('functools', fresh=['_functools'])
def run(m):
    armed = [False]
    class K:
        def __init__(self, n, h):
            self.n, self.h = n, h
        def __hash__(self):
            return self.h
        def __eq__(self, o):
            if armed[0]:
                raise ValueError('eq')
            return self is o
    a, b, d = K(1, 0), K(2, 0), K(3, 1)
    def user(k):
        if k is d:
            armed[0] = True
        return k.n * 10
    f = m.lru_cache(maxsize=2)(user)
    f(a), f(b), f(a)
    try:
        f(d)
    except ValueError:
        pass
    armed[0] = False
    return f(b)
x, y = run(c), run(py)
print(x, y)
```

</details>

#### 26. pure-Python lru_cache: a failed cache[key] store leaves a ring link, and a later unrelated call raises KeyError

In the not-full branch the pure-Python wrapper runs `last[NEXT] = root[PREV] = cache[key] = link`, and
assignment targets run left to right: the ring is linked before the dict store. If the store raises, from
`__eq__` on a colliding key, the link stays in the ring with no dict entry. The ring is now one longer than
the dict, and once the wrapper is full it picks that link as oldest and `del cache[oldkey]` raises KeyError
from a call that has nothing to do with the failed key. The C wrapper stores first and links afterwards
(Modules/_functoolsmodule.c:1499-1504), so it recovers. The twin's own comment at
bounded_lru_cache_update_lock_held explains why that order was chosen.

<details><summary>Reproducer</summary>

```python
import functools
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
class Key:
    armed = None
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return 0
    def __eq__(self, other):
        if Key.armed is not None:
            Key.armed -= 1
            if Key.armed == 0:
                Key.armed = None
                raise ValueError('eq')
        return self.n == other.n
def run(m):
    w = m.lru_cache(maxsize=2)(lambda k: k.n)
    w(Key(1))
    Key.armed = 3      # the third compare is the store, after the lookup and the re-check
    try:
        w(Key(2))
    except ValueError:
        pass
    out = []
    for n in (3, 4, 5, 6):
        try:
            out.append(w(Key(n)))
        except KeyError:
            out.append('KeyError')
    return out
c, p = run(functools), run(py)
print('C:', c, 'Python:', p)
```

</details>

#### 27. With a re-entrant __eq__, the pure Python lru_cache raises KeyError from its own del, where C keeps going

When the __eq__ of a colliding key calls the cached function again with the same key during the store, the ring gets two
links for one dict entry. The comment at Modules/_functoolsmodule.c:1494-1498 describes this orphan, and the C wrapper has a
branch for it at :1542-1550. Python has none: the second eviction of that key reaches `del cache[oldkey]` at
Lib/functools.py:699 with the key already gone, so the KeyError escapes from a call to the cached function, for a key that
has nothing to do with the collision. The ring stays out of step, and a later call raises KeyError again.

<details><summary>Reproducer</summary>

```python
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
c = import_helper.import_fresh_module('functools', fresh=['_functools'])
box = {'left': None, 'hook': None}
class K:
    def __init__(self, n):
        self.n = n
    def __hash__(self):
        return 1000 if self.n in (0, 2) else self.n
    def __eq__(self, o):
        if box['left'] is not None:
            box['left'] -= 1
            if box['left'] == 0:
                box['left'] = None
                box['hook']()
        return self.n == o.n
def run(m):
    keys = [K(i) for i in range(7)]
    f = m.lru_cache(maxsize=3)(lambda k: k.n * 10)
    box['hook'] = lambda: f(keys[0])
    f(keys[2])
    box['left'] = 3          # the lookup, the check after the call, then the store of key 0
    out = []
    for k in (0, 3, 4, 5, 6):
        try:
            out.append(f(keys[k]))
        except KeyError:
            out.append('KeyError')
    return out
x, y = run(c), run(py)
print(x, y)
```

</details>

#### 28. A cache around a cached function reports the inner cache's cache_parameters, and in pure Python its cache_info too

lru_cache sets wrapper.cache_parameters and only then calls update_wrapper(wrapper, user_function), which copies
user_function.__dict__ over it. When the user function is a cached function, as with stacked decorators or
lru_cache(maxsize=5)(some_cached), outer.cache_parameters() reports the inner's maxsize and typed. On the Python
wrapper, cache_info and cache_clear are entries of the same __dict__, so they are overwritten too: outer.cache_info() reads
the inner cache, and outer.cache_clear() clears the inner one and leaves the outer full.

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

#### 29. The pure Python lru_cache raises TypeError on an instance of a class with an unhashable metaclass, and C does not

_make_key tests `type(key[0]) in fasttypes`, a set, which hashes the type. A class whose metaclass defines __eq__ and
so has __hash__ = None cannot be hashed, so an instance of it, itself hashable, as the only argument of an untyped
cache is a TypeError. The C twin tests the exact type with Py_IS_TYPE and gets on.

<details><summary>Reproducer</summary>

```python
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
c = import_helper.import_fresh_module('functools', fresh=['_functools'])
class M(type):
    def __eq__(self, o):
        return self is o
class K(metaclass=M):
    __hash__ = object.__hash__
def attempt(m):
    f = m.lru_cache(maxsize=None)(lambda x: 1)
    try:
        return f(K())
    except TypeError:
        return 'TypeError'
a, b = attempt(c), attempt(py)
print(a, b)
```

</details>

#### 30. namedtuple validates field names as raw strings but compiles them after NFKC normalisation

DUPLICATE of the closed python/cpython#78061, "namedtuple should use NFKD to find duplicate members",
which rhettinger closed: the checks are "just courtesy checks", and "It wasn't the goal to upstage all
possible syntax errors." Do not file. Kept as the record of the refuted property.
namedtuple checks field names as plain strings (isidentifier, iskeyword, `seen`), then builds
`__new__` by eval'ing source text, where the compiler NFKC-normalises every identifier. So a
name that is not NFKC-stable means one thing to the checks and another to the compiler:
- namedtuple('T', ['ﬁ', 'fi']) (U+FB01 LATIN SMALL LIGATURE FI) passes the duplicate check,
  then raises SyntaxError "duplicate argument 'fi'" from inside eval. rename=True does not help,
  although it exists so that bad names never raise.
- namedtuple('T', ['\U0001d40d\U0001d428\U0001d427\U0001d41e']) (mathematical bold "None") raises
  ValueError "identifier field can't represent 'None' constant", also with rename=True.
- With a single field 'ﬁ' the class is created, but it is inconsistent: `_fields` is ('ﬁ',) while
  `__new__` takes `fi`. T(**p._asdict()), the round trip in the class docstring, raises TypeError,
  and `p.ﬁ` written in source raises AttributeError, because source normalises to `p.fi` and the
  descriptor is stored under the raw name.

<details><summary>Reproducer</summary>

```python
from collections import namedtuple
bad = []
try:
    namedtuple('T', ['ﬁ', 'fi'], rename=True)
except SyntaxError as e:
    bad.append(('rename', type(e).__name__, str(e)))
try:
    namedtuple('T', ['\U0001d40d\U0001d428\U0001d427\U0001d41e'], rename=True)
except ValueError as e:
    bad.append(('none', type(e).__name__, str(e)))
T = namedtuple('T', ['ﬁ'])
p = T(1)
print(T._fields, T.__new__.__code__.co_varnames, p._asdict())
try:
    T(**p._asdict())
except TypeError as e:
    bad.append(('asdict', type(e).__name__, str(e)))
try:
    eval('p.ﬁ')
except AttributeError as e:
    bad.append(('attr', type(e).__name__, str(e)))
for b in bad:
    print(b)
```

</details>

#### 31. operator.concat(a, b) is not a + b when b defines __radd__: the C function never tries it

RELATED to the open python/cpython#73325, where maintainers defended the behaviour; read that first.
The new part here is only the disagreement with the pure-Python twin. The docstring of operator.concat says "Same as a + b, for a and b sequences". The pure-Python
function does that. The C function calls PySequence_Concat, which goes straight to a's sq_concat
when it has one. For a a list or a tuple, that raises TypeError at once, where a + b first tries
nb_add and so reaches b.__radd__. operator.concat([1], UserList([2])) raises TypeError, while
[1] + UserList([2]) and the pure-Python concat give UserList([1, 2]). iconcat has the same shape,
and it also differs on a list: a += b reaches __radd__ first, so the result is what __radd__
returned, while C's iconcat extends the list in place.

<details><summary>Reproducer</summary>

```python
import operator
from collections import UserList
from test.support import import_helper
py = import_helper.import_fresh_module('operator', blocked=['_operator'])
def attempt(f, *args):
    try:
        return f(*args)
    except TypeError as e:
        return 'TypeError'
a, b = [1], UserList([2])
print('a + b:', a + b)
print('C concat:', attempt(operator.concat, a, b))
print('Python concat:', attempt(py.concat, a, b))
```

</details>

#### 32. operator.length_hint twins bind __length_hint__ differently: a staticmethod or a property gives the hint in C and the default in Python

`PyObject_LengthHint` (Objects/abstract.c:113-121) looks the hint up with `_PyObject_LookupSpecial`, which
runs the descriptor's `__get__` with the object, and calls the result with no argument; a failing lookup
returns -1 whatever the exception (:114-116). The pure twin (Lib/operator.py:213-221) reads
`type(obj).__length_hint__`, which runs `__get__` with no instance, and calls `hint(obj)`, swallowing a
TypeError. So:
* `__length_hint__ = staticmethod(lambda: 5)`: C returns 5; Python calls it with `obj`, gets a TypeError
  and returns the default.
* `__length_hint__ = property(getter)` where the getter returns a callable: C calls it; Python calls the
  property object, a TypeError, and returns the default. A getter that raises TypeError makes C raise it
  and Python return the default.

<details><summary>Reproducer</summary>

```python
import operator
from test.support import import_helper
py = import_helper.import_fresh_module('operator', blocked=['_operator'])
class S:
    __length_hint__ = staticmethod(lambda: 5)
class P:
    @property
    def __length_hint__(self):
        return lambda: 7
class Q:
    @property
    def __length_hint__(self):
        raise TypeError('get')
def t(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
r = [(t(lambda: operator.length_hint(X())), t(lambda: py.length_hint(X()))) for X in (S, P, Q)]
print(r)
```

</details>

#### 33. operator twins differ on index, on attrgetter with a str subclass, and on a getter holding itself

Three small differences, each a consequence of the pure twin being written literally. operator.index is
a.__index__() in Python and PyNumber_Index in C: no __index__ is AttributeError against TypeError, a non-int
result comes back from Python and is a TypeError in C, and an __index__ in the instance dict is used by Python
and ignored by C. attrgetter calls attr.split('.') in Python, so a str subclass overriding split changes
the lookup, and C reads the characters. And the C getters guard repr with Py_ReprEnter and the Python ones do
not, so a getter that holds itself prints differently.

<details><summary>Reproducer</summary>

```python
import operator
from test.support import import_helper
py = import_helper.import_fresh_module('operator', blocked=['_operator'])
def t(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
a = t(lambda: operator.index(1.5)), t(lambda: py.index(1.5))
class Bad:
    def __index__(self):
        return 'x'
b = t(lambda: operator.index(Bad())), t(lambda: py.index(Bad()))
class S(str):
    def split(self, sep):
        return ['real']
class O:
    real = 5
    x = 7
c = operator.attrgetter(S('x'))(O), py.attrgetter(S('x'))(O)
l1, l2 = [], []
g1, g2 = operator.itemgetter(l1), py.itemgetter(l2)
l1.append(g1)
l2.append(g2)
d = repr(g1), repr(g2)
print(a, b, c, d)
```

</details>

#### 34. operator twins differ where the pure twin does a Python-level lookup: index on an int subclass, length_hint on a metaclass and with a bool default, methodcaller repr of a str-subclass key, concat when hasattr raises

Five differences between Modules/_operator.c and Lib/operator.py, each because the pure twin does an
ordinary attribute lookup or keeps an object where C reads a type slot or converts. C's result is given first:
* index: `_PyNumber_Index` answers `PyLong_Check` first (Objects/abstract.c:1416-1418); `a.__index__()`
  (Lib/operator.py:97) runs an int subclass's own override. `class I(int): __index__ = lambda s: 7`:
  `index(I(3))` is 3 vs 7.
* length_hint, metaclass: `_PyObject_LookupSpecial` reads only the class's MRO; `type(obj).__length_hint__`
  (Lib/operator.py:213) also finds a metaclass attribute. 0 vs 3.
* length_hint, default object: C converts `default` to `Py_ssize_t`; Python returns it as given.
  `length_hint(object(), True)` is 1 vs True.
* methodcaller repr: `%U` writes a str-subclass key's characters (Modules/_operator.c:1838); `'%s=%r' % (k, v)`
  (Lib/operator.py:332) runs its `__str__`. `methodcaller('f', **{K('k'): 1})` with `K.__str__` returning 'X':
  `k=1` vs `X=1`. (The Python repr's dict iteration is also stricter than C's size check; see
  PyLean.CoreLibs.Operator.McShare.McReprPyMutations against McReprMutations.)
* concat/iconcat: `hasattr(a, '__getitem__')` (Lib/operator.py:156, :359) passes on any exception but
  AttributeError, so a `__getattr__` raising ValueError gives ValueError, where C says "'X' object can't be
  concatenated" (TypeError).

<details><summary>Reproducer</summary>

```python
import operator
from test.support import import_helper
py = import_helper.import_fresh_module('operator', blocked=['_operator'])
def t(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
class I(int):
    __index__ = lambda s: 7
idx = operator.index(I(3)), py.index(I(3))
class M(type):
    def __length_hint__(cls, obj):
        return 3
class O(metaclass=M):
    pass
meta = operator.length_hint(O()), py.length_hint(O())
dflt = operator.length_hint(object(), True), py.length_hint(object(), True)
class K(str):
    def __str__(self):
        return 'X'
key = repr(operator.methodcaller('f', **{K('k'): 1})), repr(py.methodcaller('f', **{K('k'): 1}))
class G:
    def __getattr__(self, name):
        raise ValueError('getattr')
cat = t(lambda: operator.concat(G(), [1])), t(lambda: py.concat(G(), [1]))
icat = t(lambda: operator.iconcat(G(), [1])), t(lambda: py.iconcat(G(), [1]))
print(idx, meta, dflt, key, cat, icat)
if (idx == (3, 7) and meta == (0, 3) and dflt[0] == 1 and dflt[1] is True
        and key == ("operator.methodcaller('f', k=1)", "operator.methodcaller('f', X=1)")
        and cat == ('TypeError', 'ValueError') and icat == ('TypeError', 'ValueError')):
```

</details>

#### 35. operator twins differ on str-subclass names: attrgetter looks up and prints a different object, and methodcaller reprs its name at the other end

Three small differences between Modules/_operator.c and Lib/operator.py, all about names that are
instances of a str subclass:
* attrgetter lookup: for an undotted name, `attrgetter_new` keeps the object itself
  (Modules/_operator.c:1304-1307; `_PyUnicode_InternMortal` leaves subclasses alone,
  Objects/unicodeobject.c:14306-14310) and `dotted_getattr` passes it to `PyObject_GetAttr` (:1420).
  Lib/operator.py:255-259 passes the exact strs that `attr.split('.')` returns. A `__getattribute__`
  (or a dict lookup through the name's `__eq__`/`__hash__`) sees a different object.
* attrgetter repr: for a dotted name C prints `repr` of the exact str that `dotjoinattr` rebuilds
  (:1536-1549), Python prints `repr` of the original argument (Lib/operator.py:271-274), so a subclass with
  its own `__repr__` prints differently. (For an undotted name both print the object.)
* methodcaller repr order: Python evaluates `repr(self._name)` first (Lib/operator.py:330), C formats
  `%R` of `mc->name` last (:1865), after the arguments, so when both the name's and an argument's
  `__repr__` raise, the exceptions differ.

<details><summary>Reproducer</summary>

```python
import operator
from test.support import import_helper
py = import_helper.import_fresh_module('operator', blocked=['_operator'])
class R(str):
    def __repr__(self):
        return 'R!'
class O:
    def __getattribute__(self, n):
        return type(n).__name__
look = operator.attrgetter(R('x'))(O()), py.attrgetter(R('x'))(O())
rep1 = repr(operator.attrgetter(R('a.b'))), repr(py.attrgetter(R('a.b')))
rep2 = repr(operator.attrgetter(R('a.b'), 'c')), repr(py.attrgetter(R('a.b'), 'c'))
rep3 = repr(operator.attrgetter(R('x'))), repr(py.attrgetter(R('x')))
class S(str):
    def __repr__(self):
        raise ValueError('name')
class X:
    def __repr__(self):
        raise KeyError('arg')
def t(f):
    try:
        return f()
    except Exception as e:
        return type(e).__name__
order = t(lambda: repr(operator.methodcaller(S('f'), X()))), t(lambda: repr(py.methodcaller(S('f'), X())))
order0 = t(lambda: repr(operator.methodcaller(S('f')))), t(lambda: repr(py.methodcaller(S('f'))))
print(look, rep1, rep2, rep3, order, order0)
if (look == ('R', 'str') and rep1 == ("operator.attrgetter('a.b')", "operator.attrgetter(R!)")
        and rep2 == ("operator.attrgetter('a.b', 'c')", "operator.attrgetter(R!, 'c')")
        and rep3 == ("operator.attrgetter(R!)", "operator.attrgetter(R!)")
        and order == ('KeyError', 'ValueError') and order0 == ('ValueError', 'ValueError')):
```

</details>

#### 36. partial.__setstate__ can make a partial its own func, and inspect then hangs on it

p.__setstate__((p, (), {}, None)) is accepted, since p is callable, and leaves p.func is p. _unwrap_partial is a
plain `while isinstance(func, partial): func = func.func`, so it never returns on p, in a loop that does not
allocate and is not stopped by the recursion limit. inspect.iscoroutinefunction(p), isgeneratorfunction and
isasyncgenfunction all reach it through _has_code_flag.

<details><summary>Reproducer</summary>

```python
import inspect, signal
from functools import partial
class Stop(Exception):
    pass
def on(*a):
    raise Stop
signal.signal(signal.SIGALRM, on)
p = partial(int)
p.__setstate__((p, (), {}, None))
signal.alarm(2)
try:
    inspect.iscoroutinefunction(p)
    r = 'returned'
except Stop:
    r = 'hung'
signal.alarm(0)
print(p.func is p, r)
```

</details>

#### 37. functools.partial flattens a partial subclass, so the subclass's __call__ never runs

partial(p, x) merges p's stored function and arguments when p is an instance of partial. The test
is isinstance, so it also matches a subclass that overrides __call__: partial(Sub(f, 1), 2)() calls
f(1, 2) and never reaches Sub.__call__. The twins also disagree on a related case: C does not
flatten a partial that has an instance __dict__, Python does, so partial(p, 2).func is p in C and
f in the pure-Python module.

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

#### 38. repr(partial) raises a different exception in the twins when two reprs fail

_partial_repr evaluates repr(self.func) first; partial_repr formats the arguments and keywords and takes the
function's repr last, in the final format call. With both raising, each twin reports its own one.

<details><summary>Reproducer</summary>

```python
import functools
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
class F:
    def __call__(self):
        pass
    def __repr__(self):
        raise ValueError('func')
class A:
    def __repr__(self):
        raise ValueError('arg')
def go(m):
    try:
        repr(m.partial(F(), A()))
    except ValueError as e:
        return str(e)
c, p = go(functools), go(py)
print('C:', c, 'Python:', p)
```

</details>

#### 39. partial twins differ on an object claiming to be a partial, on a repr that grows keywords, and in __setstate__ on subclasses

Four small differences between the Python and C partial. _partial_new uses isinstance, which goes through __class__,
so an object that claims to be a partial is taken apart, where PyObject_TypeCheck leaves it as the function.
_partial_repr runs a generator over self.keywords, so a repr that adds a keyword raises RuntimeError, where the PyDict_Next
loop of C goes on. In __setstate__, dict(kwds) runs an overridden keys of an empty dict subclass, which PyDict_Copy
skips. And for a tuple subclass the Python twin goes through the protocol: a __bool__ that says no lets a trailing
placeholder through, and a stateful __iter__ makes phcount count one iteration when args keeps another. The
matching C defect, with memory unsafety, is corelibs-partial-setstate-phcount.

<details><summary>Reproducer</summary>

```python
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
c = import_helper.import_fresh_module('functools', fresh=['_functools'])
def inner():
    return 0
def duck(m):
    class Fake:
        func = staticmethod(inner)
        args = ()
        keywords = {}
        _phcount = 0
        _merger = None
        __class__ = property(lambda s: m.partial)
        def __call__(self):
            return 1
    return m.partial(Fake()).func is inner
a = duck(py), duck(c)
def grow(m):
    hold = []
    class V:
        def __repr__(self):
            if hold:
                hold.pop().keywords['zz'] = 0
            return 'v'
    p = m.partial(inner, k=V())
    hold.append(p)
    try:
        repr(p)
        return 'ok'
    except RuntimeError:
        return 'RuntimeError'
b = grow(py), grow(c)
def empty(m):
    class D(dict):
        def keys(self):
            raise ValueError('conv')
        def __iter__(self):
            raise ValueError('conv')
    p = m.partial(inner)
    try:
        p.__setstate__((inner, (), D(), None))
        return 'ok'
    except ValueError:
        return 'ValueError'
d = empty(py), empty(c)
print(a, b, d)
```

</details>

#### 40. python -m random 0 prints a float, and python -m random -5 a negative float, where --integer raises

The help says of a positional argument "integer: same as --integer". For an integer below 1 it
is not. main() runs `val = int(val); return randint(1, val)` inside a try whose
`except ValueError` is meant for int(val), but randint's "empty range" ValueError lands there too.
val is now an int, so the handler's float(val) succeeds and uniform(0, val) runs:
`python -m random 0` prints 0.0, and `python -m random -5` prints something like
-3.378311363952542, while `python -m random --integer 0` and `--integer -5` raise ValueError. With
an integer too large for a float the handler itself fails with OverflowError.

<details><summary>Reproducer</summary>

```python
import random
random.seed(1)
out0 = random.main(['0'])
outm = random.main(['-5'])
print(repr(out0), repr(outm))
errs = []
for arg in ('0', '-5'):
    try:
        random.main(['--integer', arg])
    except ValueError as e:
        errs.append(str(e))
print(errs)
```

</details>

#### 41. random.Random.__init_subclass__ never calls super().__init_subclass__(**kwargs): later mixin hooks are skipped and class keywords are swallowed

Random.__init_subclass__(cls, /, **kwargs) (Lib/random.py:225-243) runs its MRO loop to pick
_randbelow and returns. It does not call super().__init_subclass__(**kwargs). Two effects:
(1) In a class such as `class R(random.Random, Mixin)`, where Mixin defines a cooperative
__init_subclass__, Random's hook comes first in the MRO and Mixin's hook never runs; with
`class R(Mixin, random.Random)` it runs, so the result depends on base order. (2) Class keywords
are accepted and dropped: `class R(random.Random, flag=1)` succeeds silently, where any class
whose chain reaches object.__init_subclass__ raises TypeError ("takes no keyword arguments").

<details><summary>Reproducer</summary>

```python
import random
ran = []
class Mixin:
    def __init_subclass__(cls, **kw):
        super().__init_subclass__(**kw)
        ran.append(cls.__name__)
class After(random.Random, Mixin):
    pass
class Before(Mixin, random.Random):
    pass
swallowed = False
try:
    class Kw(random.Random, flag=1):
        pass
    swallowed = True
except TypeError:
    pass
rejected = False
try:
    class Plain(flag=1):
        pass
except TypeError:
    rejected = True
print(ran, swallowed, rejected)
```

</details>

#### 42. NaN parameters hang gammavariate, betavariate and vonmisesvariate, and trip an assert in binomialvariate

The parameter checks are written so that a NaN passes them, and every comparison after that is
false. gammavariate(nan, 1.0) passes `alpha <= 0.0 or beta <= 0.0`, is neither `> 1.0` nor
`== 1.0`, and enters the alpha < 1 loop, where no draw can reach a `break`: it spins forever and
cannot be interrupted by anything but a signal. betavariate inherits that through either
parameter. vonmisesvariate(0.0, nan) passes `kappa <= 1e-6` and spins the same way.
binomialvariate(2, nan) passes `p <= 0.0 or p >= 1.0`, fails both branch tests and raises a bare
AssertionError at :850, with n == 1 it returns 0, and under python -O the assert is gone and
_floor(nan) raises. The other distributions just return nan.

<details><summary>Reproducer</summary>

```python
import random
nan = float('nan')
class Hang(Exception):
    pass
class Limited(random.Random):
    draws = 0
    def random(self):
        self.draws += 1
        if self.draws > 200000:
            raise Hang
        return super().random()
def spins(name, *args):
    try:
        getattr(Limited(1), name)(*args)
    except Hang:
        return True
    return False
hung = [spins('gammavariate', nan, 1.0), spins('betavariate', nan, 1.0), spins('betavariate', 1.0, nan),
        spins('vonmisesvariate', 0.0, nan)]
print(hung)
try:
    random.Random(1).binomialvariate(2, nan)
    err = None
except Exception as e:
    err = type(e).__name__
print(err, random.Random(1).binomialvariate(1, nan))
sane = not spins('gammavariate', 0.5, 1.0) and not spins('vonmisesvariate', 0.0, 1.0)
```

</details>

#### 43. random.sample accepts negative counts when their total is not negative, and then skews the selection

DUPLICATE of the closed python/cpython#134816, 'random.sample() does not properly check counts
parameter for negative entries', where the maintainer answered "It's the caller's bug" and cited
garbage in, garbage out. Do not file. Kept as the record of the refuted property.
sample raises "Counts must be non-negative", but it tests only the total. counts=[3, -1] passes,
the prefix sums [3, 2] are no longer sorted, and bisect's precondition is gone. The result is a
sample that matches no expansion of the population: sample(['a', 'b', 'c'], counts=[1, -1, 2], k=2)
always returns ['c', 'c'], so 'a', with a count of 1, is never selected.

<details><summary>Reproducer</summary>

```python
import random
r = random.Random(1)
a = {tuple(r.sample(['a', 'b'], counts=[3, -1], k=2)) for _ in range(200)}
b = {tuple(r.sample(['a', 'b', 'c'], counts=[1, -1, 2], k=2)) for _ in range(200)}
print(a, b)
try:
    r.sample(['a', 'b'], counts=[-1, -1], k=0)
    raised = False
except ValueError as e:
    raised = 'non-negative' in str(e)
```

</details>

#### 44. A rejected Random.setstate still replaces gauss_next

Random.setstate unpacks `version, internalstate, self.gauss_next = state` before the C setstate
validates internalstate. If the C call raises, the Mersenne Twister state is unchanged (that was
made atomic in bpo-29960), but gauss_next already holds the value from the rejected state, and
the next gauss() returns it. After `r.setstate((3, 'bad', 1.25))` raises TypeError,
r.gauss(0, 1) returns 1.25.

<details><summary>Reproducer</summary>

```python
import random
r = random.Random(1)
r.getstate()
try:
    r.setstate((3, 'bad', 1.25))
    raised = False
except TypeError:
    raised = True
print(raised, r.gauss_next)
```

</details>

#### 45. A random.Random subclass whose __init__ does not call super().__init__() silently returns 0.0 forever

Since Python 3.11 _random.Random seeds in tp_init, and tp_new is PyType_GenericNew, which leaves
index = 0 and all 624 words zero. All-zero is the fixed point of the Mersenne Twister recurrence.
random.Random.__init__ seeds, so a plain Random() is fine, but a subclass that defines __init__
and does not chain up never seeds. No error is raised: random() returns 0.0 every time,
randrange(100) returns 0, and shuffle and sample become one fixed permutation. Before 3.11 the
same class worked, because tp_new seeded (bpo-44260 moved it). random.Random.__new__(random.Random)
and _random.Random.__new__(_random.Random, 5) behave the same way; the seed argument of the
second one is ignored.

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

#### 46. functools.reduce in C replaces a TypeError raised by a user's __iter__ with its own message

When PyObject_GetIter fails with any TypeError, reduce replaces it by "reduce() arg 2 must support iteration". That is
right for an object that is not iterable, and wrong for an __iter__ that ran and raised a TypeError, whose message
and traceback are lost, and for a subclass of TypeError, whose class is lost. The pure Python twin passes on what
__iter__ raised.

<details><summary>Reproducer</summary>

```python
from functools import reduce
from test.support import import_helper
py = import_helper.import_fresh_module('functools', blocked=['_functools'])
class It:
    def __iter__(self):
        raise TypeError('mine')
def attempt(f):
    try:
        f(lambda a, b: a, It(), 0)
    except TypeError as e:
        return str(e)
c, p = attempt(reduce), attempt(py.reduce)
print(c, '|', p)
```

</details>

#### 47. _compose_mro can list an ABC twice, and singledispatch then raises RuntimeError: Inconsistent hierarchy

In the loop of _compose_mro, a type with no useful subclass is appended at :860 without the test `if subcls not in
mro` that :866 has for the other branch. A type can already be there, added through a subclass of an earlier
type. The list then has a repeat, _c3_mro keeps both in abstract_bases, and _c3_merge finds the type in the tail of
that one list, so every head is rejected and dispatch raises RuntimeError on a hierarchy that is consistent.

<details><summary>Reproducer</summary>

```python
import abc
from functools import singledispatch
def hook(answer):
    def h(cls, c):
        return answer if c.__name__ == 'K' else NotImplemented
    return classmethod(h)
class B(abc.ABC):
    __subclasshook__ = hook(True)
class A(abc.ABC):
    __subclasshook__ = hook(True)
class Mid(B):
    __subclasshook__ = hook(False)
class Sub(A, Mid):
    __subclasshook__ = hook(True)
class K:
    pass
@singledispatch
def f(x):
    return 'default'
f.register(A, lambda x: 'A')
f.register(B, lambda x: 'B')
try:
    r = f(K())
except RuntimeError as e:
    r = str(e)
print(r)
```

</details>

#### 48. @f.register registers the first annotation found, which can be the return type or a later parameter

With a bare @f.register, register takes `next(iter(get_type_hints(func).items()))`: the first entry of the
hints, whatever its name. `def g(x) -> int` therefore registers the implementation for int, on the return
annotation, and `def g(x, y: str)` registers it for str, on the second parameter. Neither raises, and calling
f(1) then silently runs g. The docs say that the decorator infers the type of the first argument.

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

#### 49. @f.register on a function whose __annotate__ yields nothing raises a bare StopIteration

register checks that `__annotate__` exists and then runs `next(iter(get_type_hints(func, ...).items()))` with
no default. A callable whose annotations are empty passes the check, and StopIteration escapes, instead of
the "Use either @register(some_class)" TypeError the unannotated case gets. Inside a generator or a
comprehension over decorators that StopIteration is the worst kind of exception to leak.

<details><summary>Reproducer</summary>

```python
import functools
@functools.singledispatch
def f(x):
    return 'default'
def g(x):
    return 'g'
g.__annotate__ = lambda format: {}
try:
    f.register(g)
    r = 'no error'
except StopIteration:
    r = 'StopIteration'
except TypeError as e:
    r = 'TypeError'
print(r)
```

</details>

#### 50. singledispatch keeps a stale dispatch after ABC.register when the ABC was registered through a union

singledispatch caches dispatch results and clears the cache when abc.get_cache_token() changes,
but it only starts watching the token once an ABC is registered. The test at
Lib/functools.py:994 is `hasattr(cls, '__abstractmethods__')`, on the argument of register. For
register(Sized | int, impl), cls is the UnionType, which has no such attribute, so cache_token stays
None. A class dispatched before Sized.register(C) then stays on the old implementation forever,
while the same code with register(Sized, impl) picks up the new implementation.

<details><summary>Reproducer</summary>

```python
from collections.abc import Sized
from functools import singledispatch
@singledispatch
def by_union(x):
    return 'default'
by_union.register(Sized | int, lambda x: 'sized')
@singledispatch
def by_class(x):
    return 'default'
by_class.register(Sized, lambda x: 'sized')
class C:
    pass
c = C()
before = by_union(c), by_class(c)
Sized.register(C)
after = by_union(c), by_class(c)
print('before:', before, 'after:', after)
```

</details>

#### 51. statistics._sum folds _coerce over a set, so the result depends on the addresses of the types

`T = reduce(_coerce, types, int)` iterates a set of type objects, whose order follows their hashes,
that is their addresses. _coerce is neither commutative nor associative once user subclasses are
involved, so the same call on equal data can differ between runs. For two sibling int subclasses the
result type flips. For two sibling Fraction subclasses and float (or a float subclass), mean either
returns a float or raises TypeError.

<details><summary>Reproducer</summary>

```python
import statistics
from fractions import Fraction
types, outcomes = set(), set()
keep = []
for i in range(3000):
    # New classes each time; the padding varies their addresses, hence the order of the set.
    A = type('A', (int,), {})
    keep.append([type('Z', (), {}) for _ in range(i % 5)])
    B = type('B', (int,), {})
    P = type('P', (Fraction,), {})
    keep.append([type('Z', (), {}) for _ in range(i % 7)])
    Q = type('Q', (Fraction,), {})
    R = type('R', (float,), {})
    types.add(type(statistics.mean([A(1), B(3)])).__name__)
    try:
        outcomes.add(type(statistics.mean([P(1), Q(2), R(1.5)])).__name__)
    except TypeError:
        outcomes.add('TypeError')
    if i % 11 == 0:
        keep.clear()
print(sorted(types), sorted(outcomes))
```

</details>

#### 52. statistics.correlation and linear_regression miss constant input when the rounded mean differs from it

Both functions detect constant input through a zero sum of squares after subtracting
`fsum(x) / n`. For `x = [0.1, 0.1, 0.1]` that rounded mean is 0.10000000000000002, so the deviations
are a small non-zero number. `correlation` then returns 0.0 and `linear_regression` returns
slope 0.0, intercept 2.0, instead of the documented StatisticsError. The same call with
`[0.5, 0.5, 0.5]` raises. `method='ranked'` raises for both.

<details><summary>Reproducer</summary>

```python
import statistics
x, y = [0.1, 0.1, 0.1], [1, 2, 3]
r = statistics.correlation(x, y)
s = statistics.linear_regression(x, y).slope
print(r, s)
try:
    statistics.correlation([0.5, 0.5, 0.5], y)
except statistics.StatisticsError as e:
    print('0.5 raises:', e)
```

</details>

#### 53. statistics.correlation returns values outside [-1, 1] on exactly proportional data

For two points, which are always perfectly correlated, the function can return
-1.0000000000000002. In a random scan about 1.4% of proportional float inputs of length 2 to 6
land outside the range. Code that continues with `math.acos(r)` or `sqrt(1 - r*r)` then raises
ValueError.

<details><summary>Reproducer</summary>

```python
import statistics
x = [0.7954931175397417, -0.10543425671828932]
y = [-2.386479352619225, -0.10543425671828932]
r = statistics.correlation(x, y)
print(r)
```

</details>

#### 54. statistics.mean and variance raise ValueError for IntEnum data when the result is not a member

_convert ends with `T(value)`, where T is the common type of the data. For an int subclass whose
constructor rejects some ints, that call fails when the mean happens to be a whole number outside
the class. `mean([Level.LOW, Level.HIGH])` with LOW = 1, HIGH = 3 raises
`ValueError: Fraction(2, 1) is not a valid Level`, while `mean([Level.LOW, Level.LOW, Level.HIGH])`
gives 1.666..., and `fmean`, `median`, `stdev` work on the same data. When the whole number happens
to be a member, the mean silently comes back as that enum member.

<details><summary>Reproducer</summary>

```python
import enum, statistics
class Level(enum.IntEnum):
    LOW = 1
    HIGH = 3
print(statistics.fmean([Level.LOW, Level.HIGH]), statistics.median([Level.LOW, Level.HIGH]))
try:
    print(statistics.mean([Level.LOW, Level.HIGH]))
except ValueError as e:
    print('ValueError:', e)
```

</details>

#### 55. statistics.quantiles accepts an unknown method when the data has one point

The single-point shortcut returns before `method` is looked at, so
`quantiles([1], method='bogus')` returns `[1, 1, 1]`, while the same call with two points raises
`ValueError: Unknown method: 'bogus'`. A typo in `method` passes tests that happen to use one point.

<details><summary>Reproducer</summary>

```python
import statistics
r = statistics.quantiles([1], method='bogus')
print(r)
try:
    statistics.quantiles([1, 2], method='bogus')
except ValueError as e:
    print('ValueError:', e)
```

</details>

#### 56. contextlib.suppress honours __subclasscheck__ and unions for a bare exception but not inside an ExceptionGroup

`suppress.__exit__` (Lib/contextlib.py:512-531) decides with `issubclass(exctype,
self._exceptions)` (:524), and its comment (:513-521) says it chooses "the simpler issubclass based
semantics" on purpose, over the interpreter's concrete matching. For a group it calls
`excinst.split(self._exceptions)` (:527), and `BaseExceptionGroup.split` matches with
`PyErr_GivenExceptionMatches` (Objects/exceptions.c:1284-1287, Python/errors.c:365-366), the
concrete subclass test, after `get_matcher_type` (:1260-1275) refuses any item of the tuple that is
no exception class. So the classes `suppress` was given mean different things for a bare exception
and for the same exception in a group:

<details><summary>Reproducer</summary>

```python
import abc, contextlib
class E(Exception, metaclass=abc.ABCMeta):
    pass
E.register(KeyError)
class A(abc.ABC):
    pass
A.register(ValueError)
def outcome(cls, exc):
    try:
        with contextlib.suppress(cls):
            raise exc
        return 'suppressed'
    except BaseException as e:
        return repr(e)
bare_e = outcome(E, KeyError())
group_e = outcome(E, ExceptionGroup('x', [KeyError()]))
bare_a = outcome(A, ValueError())
group_a = outcome(A, ExceptionGroup('x', [ValueError()]))
bare_u = outcome(KeyError | ValueError, KeyError())
group_u = outcome(KeyError | ValueError, ExceptionGroup('x', [KeyError()]))
print('suppress(E), KeyError():', bare_e)
print('suppress(E), ExceptionGroup([KeyError()]):', group_e)
print('suppress(A), ValueError():', bare_a)
print('suppress(A), ExceptionGroup([ValueError()]):', group_a)
print('suppress(KeyError | ValueError), KeyError():', bare_u)
print('suppress(KeyError | ValueError), ExceptionGroup([KeyError()]):', group_u)
if (bare_e == 'suppressed' and group_e.startswith('ExceptionGroup') and bare_a == 'suppressed'
        and group_a.startswith('TypeError') and bare_u == 'suppressed'
        and group_u.startswith('TypeError')):
```

</details>

#### 57. UserDict subclasses with __missing__: pop(k, default) raises KeyError, setdefault stores nothing, items() contains absent keys

UserDict.__getitem__ calls __missing__, and the inherited MutableMapping methods use `self[key]`
and treat KeyError as "absent". With __missing__ defined there is no KeyError, so for a key that is
not present:
- pop(k, default) gets the __missing__ value, then `del self[key]` raises KeyError: the default is
  ignored. A dict subclass with __missing__ returns the default.
- setdefault(k, v) returns the __missing__ value and stores nothing. A dict subclass stores v and
  returns it.
- (k, m) in d.items() is True for the __missing__ value m, while `k in d` is False and the
  item is not listed by iteration. A dict subclass says False.
UserDict.get and __contains__ were fixed for exactly this reason (gh-83445), and the comment above
them says they exist "to work like dict does when __missing__ is present".

<details><summary>Reproducer</summary>

```python
from collections import UserDict
class U(UserDict):
    def __missing__(self, key):
        return 'missing'
class D(dict):
    def __missing__(self, key):
        return 'missing'
def pop(cls):
    try:
        return cls().pop('x', 'default')
    except KeyError as e:
        return 'KeyError'
def sd(cls):
    d = cls()
    return d.setdefault('x', 'value'), dict(d)
r = [(pop(c), sd(c), ('x', 'missing') in c().items()) for c in (U, D)]
print(r)
```

</details>

#### 58. reversed(UserDict(...)) raises TypeError although dict is reversible

dict gained __reversed__ in 3.8, and OrderedDict has one. UserDict inherits `__reversed__ = None` from
Mapping, so reversed(UserDict(a=1)) is a TypeError although the wrapped dict can do it. The
same applies to `reversed(u.keys())`, `.values()` and `.items()`, which work on dict.

<details><summary>Reproducer</summary>

```python
from collections import UserDict
d = {'a': 1, 'b': 2}
print(list(reversed(d)))
try:
    print(list(reversed(UserDict(d))))
except TypeError as e:
    print(type(e).__name__, e)
```

</details>

#### 59. format(UserString(...), spec) and f-strings with a spec raise TypeError

UserString wraps every str method but has no __format__, so object.__format__ applies:
f"{UserString('a'):>5}" raises TypeError "unsupported format string passed to UserString.__format__"
where the same f-string on str gives '    a'. Only the empty spec works.

<details><summary>Reproducer</summary>

```python
from collections import UserString
print(repr(f"{'a':>5}"))
try:
    print(repr(f"{UserString('a'):>5}"))
except TypeError as e:
    print(type(e).__name__, e)
```

</details>

#### 60. UserString.replace(old, new, count=n) raises TypeError: the parameter is named maxsplit

str.replace accepts `count` as a keyword since 3.13. UserString.replace is declared
`replace(self, old, new, maxsplit=-1)`, a name str.replace never had, so u.replace('a', 'b', count=1)
raises TypeError while u.replace('a', 'b', maxsplit=1), which str rejects, works. Code that
moves to the 3.13 keyword form breaks on UserString only.

<details><summary>Reproducer</summary>

```python
from collections import UserString
print('aaa'.replace('a', 'b', count=1))
try:
    print(UserString('aaa').replace('a', 'b', count=1))
except TypeError as e:
    print(type(e).__name__, e)
    print(UserString('aaa').replace('a', 'b', maxsplit=1))
```

</details>

#### 61. UserString.partition, split, strip and the pad methods reject UserString arguments that count, find and replace accept

count, find, index, rfind, rindex, replace, removeprefix, removesuffix and __contains__ start with
`if isinstance(sub, UserString): sub = sub.data`. partition, rpartition, split, rsplit, strip, lstrip,
rstrip, center, ljust and rjust do not, so an equal UserString argument is a TypeError.
startswith and endswith had the same gap and were fixed on main by gh-159868, whose report gives this
same inconsistency as the reason; the fix touched those two only. It is not in 3.14.

<details><summary>Reproducer</summary>

```python
from collections import UserString as U
u = U('a b')
sep = U(' ')
ok = [u.count(sep), u.find(sep), str(u.replace(sep, U('-'))), str(u.removeprefix(U('a')))]
print(ok)
failed = []
for name, args in [('partition', (sep,)), ('rpartition', (sep,)), ('split', (sep,)), ('rsplit', (sep,)),
                   ('strip', (U('a'),)), ('lstrip', (U('a'),)), ('rstrip', (U('b'),)),
                   ('center', (5, U('x'))), ('ljust', (5, U('x'))), ('rjust', (5, U('x')))]:
    try:
        getattr(u, name)(*args)
    except TypeError as e:
        failed.append(name)
        print(name, e)
```

</details>

#### 62. warnings.catch_warnings(action=...): a bad action leaves the module patched; with record=True every later warning is swallowed

`catch_warnings.__enter__` first saves and replaces the module state (a copy of
`warnings.filters`, or a new context in context-aware mode; with `record=True`,
`_showwarnmsg_impl = log.append` or `context.log = log`, and `showwarning` reset), bumps the
filters version, and only then calls `simplefilter(*self._filter)` for the `action`, `category`,
`lineno`, `append` arguments (:723-724). When that call raises (an invalid action such as
'bogus' or 'Ignore', a negative or non-int lineno), `__enter__` raises after the state was
changed, and a `with` statement does not call `__exit__` when `__enter__` raises. So the module
stays patched: with `record=True`, every later warning in the program is appended to a list
nobody holds and is never shown; without it, `warnings.filters` is left as a copy (filters
installed later are dropped from view when an enclosing catch_warnings exits) and, in
context-aware mode, the thread's context stays switched.

<details><summary>Reproducer</summary>

```python
import io, sys, warnings
try:
    with warnings.catch_warnings(record=True, action='bogus'):
        pass
except ValueError as e:
    print('enter raised:', e)
err = io.StringIO()
old, sys.stderr = sys.stderr, err
try:
    warnings.simplefilter('always')
    warnings.warn('hello')
finally:
    sys.stderr = old
print('shown:', repr(err.getvalue()))
```

</details>

#### 63. _py_warnings.warn and warn_explicit read message.__class__ (isinstance), C uses the exact type: a str subclass can change the category or raise

The pure-Python twin decides whether the message is a Warning with `isinstance(message,
Warning)` and takes the category from `message.__class__` (Lib/_py_warnings.py:469-470 in
`warn`, :560-562 in `warn_explicit`). `isinstance` falls back to reading `__class__` when the
real type is not a Warning subclass (`object_isinstance`, Objects/abstract.c:2603-2622), and
`message.__class__` is an attribute read too, so a class can override it. C uses the exact
type: `get_category` checks `PyObject_TypeCheck(message, Warning)` and takes `Py_TYPE`
(Python/_warnings.c:1121-1123), as does `warn_explicit` (:822-833). Measured on 3.15.2:
1. A str subclass whose `__class__` property returns `UserWarning`:
   `warn(s, DeprecationWarning)` is shown as a DeprecationWarning by C and as a UserWarning by
   Python (so `simplefilter('ignore', DeprecationWarning)` hides it in C only, and the
   registry keys differ); `warn(s, 5)` raises TypeError in C ("category must be a Warning
   subclass, not 'int'") and shows a UserWarning in Python.
2. The same message with the `error` action: C raises `DeprecationWarning(s)`; Python's
   `raise message` (:593) raises `TypeError: exceptions must derive from BaseException`.
3. A str subclass whose `__class__` raises ValueError: C shows the warning, Python's
   `isinstance` raises the ValueError (one that raises AttributeError is cleared, and both
   agree).
4. A Warning subclass instance whose `__class__` returns another class: C files the warning
   (and the registry key) under its real type, Python under the class `__class__` gives.

<details><summary>Reproducer</summary>

```python
import sys
import warnings, _warnings
import _py_warnings as pw
class Lie(str):
    @property
    def __class__(self):
        return UserWarning
got = {}
for name, mod in (("c", _warnings), ("py", pw)):
    with warnings.catch_warnings(record=True) as log:
        warnings.simplefilter("always")
        try:
            mod.warn(Lie("hi"), 5)
            got[name] = [m.category.__name__ for m in log]
        except TypeError as e:
            got[name] = "TypeError"
print(got)
```

</details>

#### 64. warnings: filterwarnings(lineno=2**63) is accepted, then every warning raises OverflowError

filterwarnings and simplefilter check that lineno is an int >= 0 but set no upper bound. The C
filter search converts each filter's lineno with PyLong_AsSsize_t, so once a filter with
lineno >= 2**63 is installed, every warning that reaches it (warnings.warn, warn_explicit, and
warnings raised by C code such as DeprecationWarning) raises "OverflowError: Python int too large to
convert to C ssize_t" instead of being filtered. The pure-Python twin compares ints and simply
never matches that filter. -W and PYTHONWARNINGS go through _setoption, which checks lineno < 0
only, so `python -W "ignore::Warning::99999999999999999999"` installs the same filter at startup.

<details><summary>Reproducer</summary>

```python
import warnings
warnings.filterwarnings('ignore', lineno=2**63)
try:
    warnings.warn('x')
    print('no error')
except OverflowError as e:
    print('OverflowError:', e)
```

</details>

#### 65. warnings 'once' shows a warning once per module in C (duplicate of gh-159792)

Under the 'once' action the C warn_explicit records (text, category) in the caller's registry when
there is one, and in the global once registry only when there is none, so the same warning from
two modules is shown twice. _py_warnings always uses the global once registry. The C once registry
also carries a 'version' and is cleared whenever the filters change (gh-153128). Already reported
upstream as gh-159792, with an open PR (gh-159829).

<details><summary>Reproducer</summary>

```python
import warnings
warnings.simplefilter('once')
shown = []
warnings._showwarnmsg = lambda m: shown.append(m.filename)
warnings.warn_explicit('hello', UserWarning, 'a.py', 1, module='a', registry={})
warnings.warn_explicit('hello', UserWarning, 'b.py', 2, module='b', registry={})
print(shown)
```

</details>

#### 66. warnings: some invalid -W / PYTHONWARNINGS options make 'import warnings' fail instead of being ignored

`_processoptions` (run while `warnings` is imported, Lib/warnings.py:94) catches only
`_OptionError` and prints "Invalid -W option ignored: ...". Three kinds of invalid option raise
something else from `_setoption`, so the exception escapes, the import of `warnings` fails
("'import warnings' failed; traceback: ..." at startup) and every later `import warnings` raises
the same error, so the program does not run:
1. a category field naming a builtin or module attribute that is not a class:
   `-W ignore::print`, `-W ignore::os.path`: `issubclass(cat, Warning)` (:436) raises
   `TypeError: issubclass() arg 1 must be a class`;
2. a category field whose module part is empty: `-W ignore::.Foo`: `__import__('')` (:429)
   raises `ValueError: Empty module name`, and only `ImportError` is caught (:430);
3. a raw regular expression whose repetition count overflows: `-W 'ignore:/a{4294967296}/'`:
   `re.compile` raises `OverflowError`, and only `re.PatternError` is caught (:392-404).
bpo-39056 (gh-83237) fixed case 1 for names that are not attributes at all (`-Wignore::0`) by
catching `AttributeError`; a name that is an attribute but not a class still escapes.

<details><summary>Reproducer</summary>

```python
import subprocess, sys
hits = []
for opt in ['ignore::print', 'ignore::.Foo', 'ignore:/a{4294967296}/']:
    r = subprocess.run([sys.executable, '-W', opt, '-c', 'import warnings; print("ran")'],
                       capture_output=True, text=True)
    last = (r.stderr.strip().splitlines() or [''])[-1]
    print(opt, '->', r.returncode, repr(r.stdout), last)
    if r.returncode != 0 and 'ran' not in r.stdout and 'Invalid -W option ignored' not in r.stderr:
        hits.append(opt)
```

</details>

#### 67. _py_warnings.warn and the Python defaults differ from C: stacklevel <= 0, skip_file_prefixes, huge stacklevel, non-str __name__, the '__main__' default filter

The pure-Python `warn` (used when `_warnings` is unavailable, and by the test suite) against the
C one, from a model of both (Warn/WarnCall.lean) and differential cases:
1. `stacklevel` 0 or negative: C attributes the warning to the caller (the C function has no
   frame, :1046-1050); Python calls `sys._getframe(stacklevel)` (:490), which for 0 or less is
   `warn`'s own frame, so the warning is reported at `_py_warnings.py:505`, module
   `_py_warnings`, and lands in `_py_warnings`'s own `__warningregistry__`.
2. `skip_file_prefixes` holding a tuple of strs: C raises "Found non-str 'tuple' in
   skip_file_prefixes." up front (:1027-1041); Python passes it to `str.startswith`, which
   accepts a tuple. A non-str element raises in C always, in Python only if the walk reaches a
   frame that is not internal, with a different message.
3. `stacklevel` outside C `Py_ssize_t` (2**63): C's argument conversion raises OverflowError;
   Python walks off the stack and reports `<sys>:0`. `stacklevel` below -2**31 (or above 2**31
   - 1 when the caller is internal): Python's `sys._getframe` raises OverflowError, C reports
   the caller.
4. A module whose `__name__` is not a str and not None: C uses "<string>" (:1098-1104);
   Python passes the object itself as `module`, and a filter with a module regex then raises
   TypeError in `re.match`. `__name__` None: C drops the warning (warn_explicit :812-813),
   Python applies the filters.
5. Category errors name the class differently: C formats `%N`/`%T` (module-qualified, e.g.
   "not class 'collections.OrderedDict'"), Python `__name__` ("not class 'OrderedDict'"); and C
   converts and checks `stacklevel` and the type of `skip_file_prefixes` before the category,
   Python after.
6. Without `_warnings`, `_setup_defaults` (:920-928) installs `re.compile('__main__')` where C's
   `init_filters` (:101-132) has the plain str '__main__', which `check_matched` compares for
   equality (:186-195): a DeprecationWarning from a module named `__main__x` (or, via
   warn_explicit without a module, from a file `__main__.py`) is shown by the Python defaults
   and ignored by C's.
7. `del warnings.filters`: C keeps searching the list it read last (`get_warnings_filters`
   keeps `st->filters`, :346-353); Python's `_GlobalContext._filters` returns a fresh `[]`
   (:76-80), so `filterwarnings` then changes nothing C sees. `Py_SETREF` (:352) caches
   whatever was read before the list check (:355-360), so after `warnings.filters = (...)`
   (C raises ValueError) and `del warnings.filters`, C keeps raising "_warnings.filters must be
   a list" while Python shows the warning (filterListTwinsCached_refuted).
warn_explicit, measured on 3.15.2 (Warn/Props.lean, the WarnTwinsModuleState, WarnTwinsGlobals,
WarnTwinsLineObj, WarnTwinsRegObj and WarnTwinsItemShape refutations):
8. `warnings.filters` (or a context's `_filters`) a tuple: C raises ValueError
   "_warnings.filters must be a list" (:356-360, :332-337); Python iterates the tuple.
9. `warnings._showwarnmsg` deleted: C falls back to `show_warning` and prints (:750-755);
   Python raises AttributeError. Not callable: C "warnings._showwarnmsg() must be set to a
   callable" (`PyCallable_Check`, :757-761), Python "'int' object is not callable"
   (warnTwinsModuleState_refuted_noncallable). `WarningMessage` deleted:
   C RuntimeError "unable to get warnings.WarningMessage", Python AttributeError.
10. `warnings.onceregistry` not a dict, with the `once` action: C TypeError (:416-422), Python
   AttributeError from `.get`. Deleted: C uses the dict it read last, Python AttributeError.
   `warnings.defaultaction` deleted: likewise (C the cached str, :437-444).
11. `module_globals` given: C checks its type and runs `get_source_line` before anything else
   (:1328-1341), so `warn_explicit(..., module_globals=5)` or a dict whose loader's
   `get_source` raises fails even for an ignored warning; Python returns None (it only passes
   `module_globals` to `linecache.getlines` when it shows the warning).
12. A registry that is a mapping but not a dict: C TypeError "'registry' must be a dict or
   None"; Python uses it.
13. A filter whose line is not an int: C TypeError "an integer is required"
   (`PyLong_AsSsize_t`, :519-524); Python never matches it. A filter action that is unhashable:
   Python's `action in {"always", "all"}` (:601) raises TypeError about hashing, C "action must
   be a string".
14. A deleted `defaultaction`, `onceregistry`, `_showwarnmsg` or `WarningMessage` with a module
   `__getattr__` that raises an AttributeError subclass: C's `PyObject_GetOptionalAttr`
   clears it (Objects/moduleobject.c:1395-1399) and uses the cached value, falls back to
   `show_warning`, or raises "unable to get warnings.WarningMessage"; Python's `_wm.x` raises
   it (the warnTwinsModuleState_refuted_*Getattr theorems). With a `__getattr__` raising
   anything else both raise it (LookupRaisesTwins, proven).

<details><summary>Reproducer</summary>

```python
import sys
from test.support import import_helper
py = import_helper.import_fresh_module('_py_warnings')
py._set_module(py)
c = import_helper.import_fresh_module('warnings', fresh=['_warnings', '_py_warnings'])
c._set_module(c)
sys.modules['warnings'] = c
got = {}
for name, mod in (('c', c), ('py', py)):
    mod.filters[:] = []
    mod.simplefilter('always')
    seen = []
    mod._showwarnmsg = lambda m, seen=seen: seen.append((m.filename.rsplit('/', 1)[-1], m.module))
    mod.warn('x', stacklevel=0)
    try:
        mod.warn('x', skip_file_prefixes=(('/nonexistent',),))
        seen.append('ok')
    except TypeError as e:
        seen.append('TypeError')
    got[name] = seen
print(got)
if got['c'][0][1] == '__main__' and got['py'][0][1] == '_py_warnings' and \
        got['c'][1] == 'TypeError' and got['py'][1] != 'TypeError':
```

</details>

#### 68. _py_warnings.warn_explicit differs from C: line-0 warnings vanish under 'module', UnboundLocalError for an unknown default action, and nine smaller differences

The pure-Python warn_explicit (used when _warnings is unavailable, and by the test suite) against
the C one, found by a model of both and 180k differential cases:
1. Under the 'module' action Python marks "seen in this module" with the key (text, category, 0),
   which is also the key of the warning itself when its lineno is 0. So a warning at line 0 is
   never shown at all under 'module'. C uses (text, category) and shows it once.
2. With an empty filters list and an unrecognized defaultaction, Python's RuntimeError message
   formats `item`, the loop variable the empty loop never bound: UnboundLocalError. (With filters
   present, it names the last filter, which did not match.) C names None.
3. module=None passed explicitly: C returns at once (meant for interpreter shutdown,
   _warnings.c:812-813); Python treats it as omitted and applies the filters.
4. C evaluates a filter's message regex, module regex and issubclass before using any of them;
   Python short-circuits. A filter whose message doesn't match but whose category's metaclass
   __subclasscheck__ raises is skipped by Python and raises in C.
5. C converts lineno with the int converter: 2**31 raises OverflowError, 5.0 and '5' TypeError;
   Python's int(lineno) takes all three.
6. An unrecognized action: C has already stored registry[key] = True when it raises RuntimeError,
   so the same call next time returns silently; Python raises again.
7. A filter whose pattern is a plain str (what C's own default filters hold, e.g. the '__main__'
   module filter): C compares it with the module name; Python calls str.match: AttributeError.
8. A filters-list item that is a 5-element list: C raises ValueError ("isn't a 5-tuple"); Python
   unpacks it. A non-str action: C TypeError; Python's unknown-action RuntimeError. A non-str
   defaultaction: C TypeError; Python RuntimeError (or UnboundLocalError, see 2).
9. A registry that is neither dict nor None: C TypeError("'registry' must be a dict or None");
   Python AttributeError from registry.get.
10. A message that cannot be built (category(message) raising): Python raises it first; C checks
    module=None and the registry type before building it.
11. A registry 'version' of True: C treats it as stale (PyLong_CheckExact) and clears the
    registry; Python compares with != and keeps it when the filters version is 1.

<details><summary>Reproducer</summary>

```python
import _py_warnings as pw
pw._set_module(pw)
shown = []
pw._showwarnmsg = lambda m: shown.append(m.lineno)
pw.resetwarnings(); pw.simplefilter('module')
pw.warn_explicit('hello', UserWarning, 'a.py', 0, module='a', registry={})
pw.resetwarnings(); pw.defaultaction = 'bogus'
try:
    pw.warn_explicit('x', UserWarning, 'a.py', 1, module='a')
    err = None
except Exception as e:
    err = type(e).__name__
print('shown:', shown, 'unknown action:', err)
```

</details>

#### 69. warnings: a registry 'version' outside C long makes warn_explicit leak an OverflowError (SystemError)

already_warned compares the registry's 'version' with PyLong_AsLong(version_obj) and never checks
for an error. A 'version' of 2**63 or more (or below -2**63) makes PyLong_AsLong return -1 with
OverflowError set; the code treats -1 as a stale version, clears the registry and carries on with
the exception still set. What surfaces depends on what runs next: SystemError("<built-in function
warn_explicit> returned a result with an exception set") for 'ignore', SystemError from
__import__ when the warning is shown, the OverflowError itself when a filter's regex runs, and the
warning when the action is 'error'. warnings.warn hits it through a module's __warningregistry__.
The pure-Python twin (_py_warnings) clears the registry and shows the warning.

<details><summary>Reproducer</summary>

```python
import warnings
warnings.simplefilter('ignore')
try:
    warnings.warn_explicit('x', UserWarning, 'a.py', 1, registry={'version': 2**64})
    print('no error')
except SystemError as e:
    print('SystemError:', e, '| context:', repr(e.__context__))
```

</details>

#### 70. C warn_explicit imports warnings for every shown warning: an import hook that raises makes the warning raise (the Python twin shows it)

C `call_show_warning` finds `_showwarnmsg` with `GET_WARNINGS_ATTR(interp, _showwarnmsg, 1)`
(Python/_warnings.c:749), and `get_warnings_attr` with `try_import` runs
`PyImport_Import("warnings")` (:229-238), which goes through `builtins.__import__`. Only an
ImportError from it is cleared (and the warning then printed by C's `show_warning`); any other
exception propagates out of `warnings.warn`. The Python twin looks `_showwarnmsg` up on its
module reference `_wm` and never imports. Measured on 3.15.2: with a `builtins.__import__`
wrapper that raises RuntimeError for 'warnings' (an import hook that refuses a module, a
sandbox), `_warnings.warn_explicit(...)` raises the RuntimeError while
`_py_warnings.warn_explicit(...)` shows the warning. The same wrapper makes every C
`warnings.warn` of a warning that gets shown raise (an ignored one never reaches
`call_show_warning`), though `warnings` is already imported.

<details><summary>Reproducer</summary>

```python
import builtins, warnings, _warnings
import _py_warnings as pw
real = builtins.__import__
def hook(name, *a, **k):
    if name == "warnings":
        raise RuntimeError("no import")
    return real(name, *a, **k)
got = {}
for name, mod in (("c", _warnings), ("py", pw)):
    with warnings.catch_warnings(record=True) as log:
        warnings.simplefilter("always")
        builtins.__import__ = hook
        try:
            mod.warn_explicit("x", UserWarning, "a.py", 1, module="m")
            got[name] = len(log)
        except RuntimeError:
            got[name] = "RuntimeError"
        finally:
            builtins.__import__ = real
print(got)
```

</details>

#### 71. With sys.modules['warnings'] = None, C warnings bypass catch_warnings(record=True) and print to stderr

`sys.modules['warnings'] = None` makes C's `PyImport_Import("warnings")` in
`get_warnings_attr` (Python/_warnings.c:229-238) raise ModuleNotFoundError, which it clears;
`call_show_warning` (:749-755) then prints through its own `show_warning`, which neither
`_showwarnmsg` nor a `catch_warnings(record=True)` log sees. The Python twin shows through
`_wm._showwarnmsg` and records it. Measured on 3.15.2: inside
`warnings.catch_warnings(record=True)` with `sys.modules['warnings'] = None`,
`_warnings.warn_explicit("x", UserWarning, "a.py", 1, module="m")` records nothing and writes
"a.py:1: UserWarning: x" to stderr; `_py_warnings.warn_explicit(...)` records it.

<details><summary>Reproducer</summary>

```python
import io, sys, warnings, _warnings
import _py_warnings as pw
W = sys.modules["warnings"]
got = {}
for name, mod in (("c", _warnings), ("py", pw)):
    err, old = io.StringIO(), sys.stderr
    sys.stderr = err
    try:
        with warnings.catch_warnings(record=True) as log:
            warnings.simplefilter("always")
            sys.modules["warnings"] = None
            try:
                mod.warn_explicit("x", UserWarning, "a.py", 1, module="m")
            finally:
                sys.modules["warnings"] = W
            got[name] = (len(log), err.getvalue() != "")
    finally:
        sys.stderr = old
print(got)
```

</details>

#### 72. deepcopy of a WeakKeyDictionary or WeakValueDictionary that refers to itself makes two copies of it

WeakValueDictionary.__deepcopy__ (Lib/weakref.py:151-158) and WeakKeyDictionary.__deepcopy__
(:347-354) create `new = self.__class__()` and then deep-copy the keys (WVD) or the values (WKD)
with the caller's memo, but never record `memo[id(self)] = new`. copy.deepcopy only records the
result after __deepcopy__ returns (Lib/copy.py:159-161). So when a key or value refers back to the
dictionary, copying it calls deepcopy(self, memo) again, which misses memo and builds a second new
dictionary; the outer call then overwrites memo[id(self)] with the first one. The copy's key/value
points at the second copy, not at the returned one. For `d = WeakKeyDictionary(); d[k] = [d];
c = deepcopy(d)`, `c[k][0] is c` is False (it is a third dictionary, neither c nor d), while a plain
dict gives True. The same holds for a WeakValueDictionary whose key has an attribute referring to
the dictionary.

<details><summary>Reproducer</summary>

```python
import copy, weakref
class B:
    pass
k, v = B(), B()
d = weakref.WeakKeyDictionary()
d[k] = [d]
c = copy.deepcopy(d)
wv = weakref.WeakValueDictionary()
key = B()
key.back = wv
wv[key] = v
cv = copy.deepcopy(wv)
ck = next(iter(cv.keys()))
p = {}
p['a'] = [p]
cp = copy.deepcopy(p)
outcome = {'wkd': c[k][0] is c, 'wvd': ck.back is cv, 'dict': cp['a'][0] is cp}
print(outcome)
```

</details>

#### 73. WeakValueDictionary.pop accepts any number of defaults and silently uses the first

WeakValueDictionary.pop is `def pop(self, key, *args)` (Lib/weakref.py:211-222) and returns
`args[0]` for a missing or dead key, ignoring the rest. dict.pop, MutableMapping.pop
(`pop(self, key, default=__marker)`, Lib/_collections_abc.py:930) and WeakKeyDictionary.pop, which
forwards `*args` to dict.pop (Lib/weakref.py:404-405), all raise "TypeError: pop expected at most 2
arguments, got 3". So `WeakValueDictionary().pop('k', 1, 2)` returns 1, while the same call on a
WeakKeyDictionary or a dict raises. When the key is present, the extra arguments are ignored as
well.

<details><summary>Reproducer</summary>

```python
import weakref
class B:
    pass
def res(f):
    try:
        return f()
    except TypeError as e:
        return 'TypeError'
o = B()
outcome = {
    'wvd': res(lambda: weakref.WeakValueDictionary().pop('k', 1, 2)),
    'wkd': res(lambda: weakref.WeakKeyDictionary().pop(o, 1, 2)),
    'dict': res(lambda: {}.pop('k', 1, 2)),
}
print(outcome)
```

</details>

#### 74. functools.wraps(Placeholder) raises TypeError, where update_wrapper(f, Placeholder) works

wraps is partial(update_wrapper, wrapped=wrapped, assigned=assigned, updated=updated), and since 3.14 partial refuses
Placeholder as a keyword. So wraps(Placeholder) fails with "Placeholder cannot be passed as a keyword argument",
which names something the caller did not do, while the direct call works.

<details><summary>Reproducer</summary>

```python
from functools import Placeholder, update_wrapper, wraps
def f():
    pass
update_wrapper(f, Placeholder)
try:
    wraps(Placeholder)
    r = 'no error'
except TypeError as e:
    r = str(e)
print(r)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
