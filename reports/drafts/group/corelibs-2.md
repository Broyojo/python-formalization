<!-- title: Small inconsistencies in functools, enum, random and other core library modules found by a formal model (part 2 of 2) -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. singledispatch keeps a stale dispatch after ABC.register when the ABC was registered through a union

singledispatch caches dispatch results and clears the cache when abc.get_cache_token() changes, but it only starts watching the token once an ABC is registered. The test at Lib/functools.py:994 is `hasattr(cls, '__abstractmethods__')`, on the argument of register. For register(Sized | int, impl), cls is the UnionType, which has no such attribute, so cache_token stays None. A class dispatched before Sized.register(C) then stays on the old implementation forever, while the same code with register(Sized, impl) picks up the new implementation.

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

#### 2. statistics.mean and variance raise ValueError for IntEnum data when the result is not a member

_convert ends with `T(value)`, where T is the common type of the data. For an int subclass whose constructor rejects some ints, that call fails when the mean happens to be a whole number outside the class. `mean([Level.LOW, Level.HIGH])` with LOW = 1, HIGH = 3 raises `ValueError: Fraction(2, 1) is not a valid Level`, while `mean([Level.LOW, Level.LOW, Level.HIGH])` gives 1.666..., and `fmean`, `median`, `stdev` work on the same data. When the whole number happens to be a member, the mean silently comes back as that enum member.

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

#### 3. UserDict subclasses with __missing__: pop(k, default) raises KeyError, setdefault stores nothing, items() contains absent keys

UserDict.__getitem__ calls __missing__, and the inherited MutableMapping methods use `self[key]` and treat KeyError as "absent". With __missing__ defined there is no KeyError, so for a key that is not present: - pop(k, default) gets the __missing__ value, then `del self[key]` raises KeyError: the default is ignored. A dict subclass with __missing__ returns the default. - setdefault(k, v) returns the __missing__ value and stores nothing. A dict subclass stores v and returns it. - (k, m) in d.items() is True for the __missing__ value m, while `k in d` is False and the item is not listed by iteration. A dict subclass says False. UserDict.get and __contains__ were fixed for exactly this reason (gh-83445), and the comment above them says they exist "to work like dict does when __missing__ is present".

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

#### 4. UserString.replace(old, new, count=n) raises TypeError: the parameter is named maxsplit

str.replace accepts `count` as a keyword since 3.13. UserString.replace is declared `replace(self, old, new, maxsplit=-1)`, a name str.replace never had, so u.replace('a', 'b', count=1) raises TypeError while u.replace('a', 'b', maxsplit=1), which str rejects, works. Code that moves to the 3.13 keyword form breaks on UserString only.

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

#### 5. warnings.catch_warnings(action=...): a bad action leaves the module patched; with record=True every later warning is swallowed

`catch_warnings.__enter__` first saves and replaces the module state (a copy of `warnings.filters`, or a new context in context-aware mode; with `record=True`, `_showwarnmsg_impl = log.append` or `context.log = log`, and `showwarning` reset), bumps the filters version, and only then calls `simplefilter(*self._filter)` for the `action`, `category`, `lineno`, `append` arguments (:723-724). When that call raises (an invalid action such as 'bogus' or 'Ignore', a negative or non-int lineno), `__enter__` raises after the state was changed, and a `with` statement does not call `__exit__` when `__enter__` raises. So the module stays patched: with `record=True`, every later warning in the program is appended to a list nobody holds and is never shown; without it, `warnings.filters` is left as a copy (filters installed later are dropped from view when an enclosing catch_warnings exits) and, in context-aware mode, the thread's context stays switched.

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

#### 6. warnings: filterwarnings(lineno=2**63) is accepted, then every warning raises OverflowError

filterwarnings and simplefilter check that lineno is an int >= 0 but set no upper bound. The C filter search converts each filter's lineno with PyLong_AsSsize_t, so once a filter with lineno >= 2**63 is installed, every warning that reaches it (warnings.warn, warn_explicit, and warnings raised by C code such as DeprecationWarning) raises "OverflowError: Python int too large to convert to C ssize_t" instead of being filtered. The pure-Python twin compares ints and simply never matches that filter. -W and PYTHONWARNINGS go through _setoption, which checks lineno < 0 only, so `python -W "ignore::Warning::99999999999999999999"` installs the same filter at startup.

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

#### 7. warnings: some invalid -W / PYTHONWARNINGS options make 'import warnings' fail instead of being ignored

`_processoptions` (run while `warnings` is imported, Lib/warnings.py:94) catches only `_OptionError` and prints "Invalid -W option ignored: ...". Three kinds of invalid option raise something else from `_setoption`, so the exception escapes, the import of `warnings` fails ("'import warnings' failed; traceback: ..." at startup) and every later `import warnings` raises the same error, so the program does not run: 1. a category field naming a builtin or module attribute that is not a class: `-W ignore::print`, `-W ignore::os.path`: `issubclass(cat, Warning)` (:436) raises `TypeError: issubclass() arg 1 must be a class`; 2. a category field whose module part is empty: `-W ignore::.Foo`: `__import__('')` (:429) raises `ValueError: Empty module name`, and only `ImportError` is caught (:430); 3. a raw regular expression whose repetition count overflows: `-W 'ignore:/a{4294967296}/'`: `re.compile` raises `OverflowError`, and only `re.PatternError` is caught (:392-404). bpo-39056 (gh-83237) fixed case 1 for names that are not attributes at all (`-Wignore::0`) by catching `AttributeError`; a name that is an attribute but not a class still escapes.

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

#### 8. warnings: a registry 'version' outside C long makes warn_explicit leak an OverflowError (SystemError)

already_warned compares the registry's 'version' with PyLong_AsLong(version_obj) and never checks for an error. A 'version' of 2**63 or more (or below -2**63) makes PyLong_AsLong return -1 with OverflowError set; the code treats -1 as a stale version, clears the registry and carries on with the exception still set. What surfaces depends on what runs next: SystemError("<built-in function warn_explicit> returned a result with an exception set") for 'ignore', SystemError from __import__ when the warning is shown, the OverflowError itself when a filter's regex runs, and the warning when the action is 'error'. warnings.warn hits it through a module's __warningregistry__. The pure-Python twin (_py_warnings) clears the registry and shows the warning.

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

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
