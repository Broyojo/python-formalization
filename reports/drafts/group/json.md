<!-- title: json: 10 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. json: C and pure-Python encoders treat list and dict subclasses differently (known)

For a subclass of list, tuple, dict or frozendict the C encoder materialises the container
first (`PySequence_Fast`, i.e. `list(seq)`; `PyMapping_Items`, i.e. `list(dct.items())`) and
tests emptiness by that list or by the stored size (`PyDict_GET_SIZE`), while the Python encoder
tests `not lst` / `not dct` (`__len__`, `__bool__`) and iterates lazily, writing `'['` only with
the first item. So: a non-empty list subclass whose `__iter__` yields nothing gives `[]` in C
and `]` in Python; a list subclass with `__len__` returning 0 gives `[1]` in C and `[]` in Python;
a dict subclass with `__len__` 0 but entries gives `{"z": 1}` in C and `{}` in Python; `items()`
yielding 2-element lists is a ValueError ('items must return 2-tuples') in C and accepted in
Python; `items()` returning a non-iterable is 'DN.items() must return an iterable, not int' vs
"'int' object is not iterable"; an iterator that raises after one bad item raises the
iterator's error in C and the item's error (with a note) in Python.
These are known and were reported before; recorded here because the Lean model now covers the
non-exact branches (EncFull.lean: seqSub, mapSub) and refutes the twin agreement with subclasses
twice: json-dumps-twins-subclass (the list subclass L) and json-dumps-twins-dict-subclass (DF,
which overrides only __len__: C tests PyDict_GET_SIZE and iterates PyMapping_Items through
_encoder_iterate_mapping_lock_held), the proven agreement being for exact containers
(json-dumps-twins).

<details><summary>Reproducer</summary>

```python
import json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
class L(list):
    def __iter__(self):
        return iter([])
class LF(list):
    def __len__(self):
        return 0
class DF(dict):
    def __len__(self):
        return 0
class DL(dict):
    def items(self):
        return [['a', 1]]
def run(mod, v):
    try:
        return mod.dumps(v)
    except Exception as e:
        return f'{type(e).__name__}: {e}'
rows = [('L', L([1, 2])), ('LF', LF([1])), ('DF', DF(z=1)), ('DL', DL(z=1))]
res = [(n, run(json, v), run(pyjson, v)) for n, v in rows]
for n, c, p in res:
    print(f'{n:3s} C {c!r:45s} Python {p!r}')
```

</details>

#### 2. json: c_make_encoder(...)(o, level) builds the indent for `level` before encoding, so a scalar fails at a huge level where _make_iterencode returns

The second argument of the C encoder object (`_current_indent_level`) starts the indent cache:
`encoder_call` calls `create_indent_cache(s, indent_level)` (Modules/_json.c:1465-1471), which
computes `'\n' + indent * indent_level` with `PySequence_Repeat` before anything is encoded.
The pure-Python twin `_make_iterencode(...)(o, _current_indent_level)` repeats the indent only
when it opens a list or a dict (Lib/json/encoder.py:281, :340). So with indent='  ':
`c_make_encoder(...)(1, 2**62)` raises OverflowError('repeated string is too long')
(`unicode_repeat`, Objects/unicodeobject.c:12573-12576), and at 2**62 - 1 MemoryError
(`PyUnicode_New`'s size check, :1325-1326), while `_make_iterencode(...)(1, 2**62)` returns '1'.
A second difference at negative levels: C's cache starts from '\n' (the repeat gives ''), so
level -1 indents like level 0 ('[\n  1\n]'), while Python computes `indent * (level + 1)` and
gives '[\n1\n]'.
Lean: json-encoder-call-twins (EncoderCallTwins) is refuted with the first witness;
json-encoder-call (EncoderCallX) is proven once the cache is built, and json-indent-cache
(IndentCacheSpec) gives every outcome of create_indent_cache. The negative-level difference is
not refuted in Lean: the Python model takes a Nat level.

<details><summary>Reproducer</summary>

```python
import json.encoder as E
from _json import make_encoder as c_make_encoder
def dflt(o):
    raise TypeError('x')
def c(level, o):
    enc = c_make_encoder(None, dflt, E.encode_basestring_ascii, '  ', ': ', ', ', False, False, True)
    try:
        return enc(o, level)[0]
    except Exception as e:
        return f'{type(e).__name__}: {e}'
def py(level, o):
    it = E._make_iterencode({}, dflt, E.encode_basestring_ascii, '  ', float.__repr__, ': ', ', ',
                            False, False, True)
    try:
        return ''.join(it(o, level))
    except Exception as e:
        return f'{type(e).__name__}: {e}'
rows = [(2**62, 1), (2**62 - 1, 1), (-1, [1])]
out = [(lv, o, c(lv, o), py(lv, o)) for lv, o in rows]
for lv, o, a, b in out:
    print(f'level {lv} {o!r}: C {a!r}  Python {b!r}')
if (out[0][2] == 'OverflowError: repeated string is too long' and out[0][3] == '1'
        and out[1][2].startswith('MemoryError') and out[1][3] == '1'
        and out[2][2] == '[\n  1\n]' and out[2][3] == '[\n1\n]'):
```

</details>

#### 3. json: a sort_keys, skipkeys or allow_nan whose __bool__ raises fails every C encode, but only the Python encode that reads it

c_make_encoder converts sort_keys, skipkeys and allow_nan with the `p` format unit
(Modules/_json.c:1320, PyObject_IsTrue) when the encoder object is made, so a value whose
__bool__ raises makes JSONEncoder(sort_keys=X()).encode(v) raise for every v that is not a str.
The pure-Python encoder stores the objects and tests them only where they matter: sort_keys and
skipkeys inside _iterencode_dict for a non-empty dict (encoder.py:346, :367), allow_nan inside
floatstr for a non-finite float (:241). So with X.__bool__ raising ZeroDivisionError:
JSONEncoder(sort_keys=X()).encode([1]) raises in C and returns '[1]' in Python; the same for
skipkeys=X() and allow_nan=X() on [1], and for sort_keys=X() on 1 and on {}. A dict with items
(sort_keys, skipkeys with a bad key) or a NaN (allow_nan) raises in both. ensure_ascii and
check_circular are tested in iterencode itself (:217, :221) and raise in both twins.
Recorded from a probe only; the Lean model takes the three options as Bool (a stated type
invariant of encoder_new) and has no refutation for this.

<details><summary>Reproducer</summary>

```python
import json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
class X:
    def __bool__(self):
        raise ZeroDivisionError('boom')
def run(mod, v, **kw):
    try:
        return mod.JSONEncoder(**kw).encode(v)
    except Exception as e:
        return type(e).__name__
rows = [({'sort_keys': X()}, [1]), ({'sort_keys': X()}, {}), ({'skipkeys': X()}, [1]),
        ({'allow_nan': X()}, [1]), ({'sort_keys': X()}, {'b': 1, 'a': 2})]
out = [(kw, v, run(json, v, **kw), run(pyjson, v, **kw)) for kw, v in rows]
for kw, v, a, b in out:
    print(f'{list(kw)[0]}=X(), {v!r}: C {a!r}  Python {b!r}')
if ([a for _, _, a, _ in out] == ['ZeroDivisionError'] * 5
        and [b for _, _, _, b in out] == ['[1]', '{}', '[1]', '[1]', 'ZeroDivisionError']):
```

</details>

#### 4. json: C and pure-Python encoders print different exception notes and key-type messages (original vs converted key, %T vs __name__)

The notes added by gh-122163 differ between the twins in three ways, and so does the TypeError
for a key of an unsupported type:
1. A failing dict value is noted with its key. C formats the original key with %R
   (`_PyErr_FormatNote("when serializing %T item %R", dct, key)`), Python formats the key after
   its conversion to str (`f'... item {key!r}'` after `key = int.__repr__(key)` etc.):
   `json.dumps({1: set()})` notes `when serializing dict item 1` with `_json` and
   `when serializing dict item '1'` without it; `{True: ...}` gives `True` vs `'true'`,
   `{None: ...}` `None` vs `'null'`, `{1.5: ...}` `1.5` vs `'1.5'`.
2. C's %T prints the fully qualified name (`_PyType_GetFullyQualifiedName`: module and
   __qualname__ unless the module is builtins or __main__), Python `type(o).__name__`: an object
   of class `Foo` in module `mymod` whose default() result fails is noted `when serializing
   mymod.Foo object` vs `when serializing Foo object`; the same for dict and list subclasses
   and nested classes (`mymod.A.B` vs `B`).
3. `keys must be str, int, float, bool or None, not %.100s` uses `tp_name` in C and
   `key.__class__.__name__` in Python: `not datetime.date` vs `not date`, `not decimal.Decimal`
   vs `not Decimal`.
The Lean model records each note's kind, type and key (Note, EncFull.lean) and proves that on
exact containers, when neither twin hits its recursion limit, the notes correspond one to one
(json-dumps-twins); printed, they differ only as above (json-dumps-twins-notes, refuted).

<details><summary>Reproducer</summary>

```python
import json, datetime
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
class Foo: pass
Foo.__module__ = 'mymod'
def default(o):
    if isinstance(o, Foo):
        return [set()]
    raise TypeError(f'Object of type {type(o).__name__} is not JSON serializable')
def err(mod, v, **kw):
    try:
        mod.dumps(v, **kw)
    except (TypeError, ValueError) as e:
        return str(e), getattr(e, '__notes__', [])
rows = [({1: set()}, {}), (Foo(), {'default': default}), ({datetime.date(2020, 1, 1): 1}, {})]
out = [(err(json, v, **kw), err(pyjson, v, **kw)) for v, kw in rows]
for (c, p), (v, _) in zip(out, rows):
    print(type(v).__name__)
    print('   C     :', c)
    print('   Python:', p)
if (out[0][0][1] == ['when serializing dict item 1'] and out[0][1][1] == ["when serializing dict item '1'"]
        and 'when serializing mymod.Foo object' in out[1][0][1] and 'when serializing Foo object' in out[1][1][1]
        and out[2][0][0].endswith('not datetime.date') and out[2][1][0].endswith('not date')):
```

</details>

#### 5. json: dumps(cyclic, check_circular=False, indent=1) with the C encoder uses gigabytes before RecursionError (quadratic in depth)

With check_circular=False a reference cycle recurses until the recursion check stops it. The C
encoder is limited by the C stack (about 51,000 lists with the default 8 MB stack), not by
sys.getrecursionlimit(). With an indent, every level adds two cached strings of length
proportional to the level and writes one more such string, so memory is quadratic in the depth:
at depth n, about n^2 * len(indent) characters in the indent cache and n^2/2 * len(indent) in
the output writer. json.dumps(l, check_circular=False, indent=1) with l = []; l.append(l) peaks
at 3.9 GB (1.6 s) before RecursionError, and indent=4 hits a 6 GB address-space limit
(MemoryError); without an indent the same call peaks at 22 MB and takes 0.03 s. The pure-Python
encoder raises RecursionError at depth 1000 straight away. Lean: IndentCacheSize gives the exact
length of every cache entry, and json-indent-cache proves the cache contents.

<details><summary>Reproducer</summary>

```python
import json, resource
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
assert pyjson.encoder.c_make_encoder is None
l = []
l.append(l)
def run(mod, **kw):
    try:
        mod.dumps(l, check_circular=False, **kw)
        return 'returned'
    except BaseException as e:
        return type(e).__name__
py = run(pyjson, indent=1)
limit = 2 * 2**30
resource.setrlimit(resource.RLIMIT_AS, (limit, limit))
plain = run(json)
indented = run(json, indent=1)
print('Python encoder, indent=1:', py)
print('C encoder, no indent, 2 GiB address space:', plain)
print('C encoder, indent=1, 2 GiB address space:', indented)
```

</details>

#### 6. json: pure-Python raw_decode() accepts a negative idx and returns garbage (C raises ValueError('idx cannot be negative'))

JSONDecoder.raw_decode(s, idx) with the C scanner rejects idx < 0 with
ValueError('idx cannot be negative') (the check added for bpo-21529, CVE-2014-4616). The
pure-Python scanner has no such check: `string[idx]` wraps around, slices and
`NUMBER_RE.match(string, idx)` (which clamps a negative pos to 0) then read from unrelated
places, and it can return a value and even a negative end index:
raw_decode('12', -1) == (12, 2) (string[-1] is '2', then the number is matched from index 0),
raw_decode('{}x', -3) == ({}, -1), raw_decode('null ', -5) == (None, -1), and
raw_decode('12', -3) raises JSONDecodeError('Expecting value: line 1 column -2 (char -3)').
For idx > sys.maxsize C raises OverflowError while Python raises JSONDecodeError. For
0 <= idx <= sys.maxsize the twins agree (Lean: json-raw-decode-twins-in-range). The helper one
level down has the same gap: c_scanstring(s, end) raises ValueError('end is out of bounds') for
end outside [0, len(s)], while py_scanstring('ab', 5) raises JSONDecodeError naming char 4, past
the end of the document (Lean: json-scanstring-twins; for 0 <= end <= len(s) the twins agree,
json-scanstring-twins-in-range).

<details><summary>Reproducer</summary>

```python
import json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
assert pyjson.scanner.make_scanner is pyjson.scanner.py_make_scanner
def run(mod, s, idx):
    try:
        return repr(mod.JSONDecoder().raw_decode(s, idx))
    except Exception as e:
        return f'{type(e).__name__}: {e}'
cases = [('12', -1), ('[1, 2]', -1), ('{}x', -3), ('null ', -5), ('12', -3), ('12', 2**63)]
out = []
for s, idx in cases:
    c, p = run(json, s, idx), run(pyjson, s, idx)
    out.append((c, p))
    print(f'raw_decode({s!r}, {idx}): C {c} | Python {p}')
def scan(f):
    try:
        return repr(f('ab', 5))
    except Exception as e:
        return f'{type(e).__name__}: {e}'
c_scan = scan(json.decoder.c_scanstring)
py_scan = scan(pyjson.decoder.py_scanstring)
print(f"scanstring('ab', 5): C {c_scan} | Python {py_scan}")
if (out[0][0].startswith('ValueError: idx cannot be negative') and out[0][1] == '(12, 2)'
        and c_scan == 'ValueError: end is out of bounds' and py_scan.startswith('JSONDecodeError')):
```

</details>

#### 7. json: loads(dumps(s)) != s when s contains a high surrogate followed by a low surrogate (ensure_ascii=True)

With the default ensure_ascii=True, json.dumps escapes every non-ASCII code point separately,
so the two-code-point str '𝄞' becomes '"\\ud834\\udd1e"', and json.loads joins an
escaped high surrogate followed by an escaped low surrogate into one character:
json.loads(json.dumps('𝄞')) == '\U0001d11e'. Both encoders and both decoders behave
the same. The Lean model proves that this is the only way a str fails to round-trip:
loads(dumps(t)) == t for every str t with ensure_ascii=False, and with ensure_ascii=True
whenever t has no high surrogate immediately followed by a low surrogate, for strings alone
and inside any JSON-representable value (json-roundtrip).

<details><summary>Reproducer</summary>

```python
import json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
s = '𝄞'
c = json.loads(json.dumps(s))
p = pyjson.loads(pyjson.dumps(s))
print('dumps:', json.dumps(s), pyjson.dumps(s))
print('C:', ascii(c), 'Python:', ascii(p))
print('ensure_ascii=False:', ascii(json.loads(json.dumps(s, ensure_ascii=False))))
```

</details>

#### 8. json: C and pure-Python decoders report invalid escapes at different positions (and both string errors with different messages)

For an invalid backslash escape the C scanner raises JSONDecodeError('Invalid \\escape') at the
index of the backslash, while the pure-Python py_scanstring raises
JSONDecodeError("Invalid \\escape: 'x'") at the index of the character after it. So `pos`,
`colno` and the message all differ: json.loads('"\\x"') gives pos=1, colno=2 with _json and
pos=2, colno=3 without it. For a raw control character inside a string (strict=True) the
position agrees but the message does not: C says 'Invalid control character at', Python
"Invalid control character '\\x01' at".
The Lean model proves these are the only differences: for every document and every
strict / object_pairs_hook / parse_int setting, json.loads agrees between the twins (value,
or exception class, msg, pos, lineno, colno) except for exactly these two errors
(json-loads-twins-scan), and the same holds for raw_decode(s, idx) with
0 <= idx <= sys.maxsize (json-raw-decode-twins-in-range).

<details><summary>Reproducer</summary>

```python
import json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
assert pyjson.decoder.scanstring is pyjson.decoder.py_scanstring
def err(mod, s):
    try:
        mod.loads(s)
        return None
    except ValueError as e:
        return (e.msg, e.pos, e.lineno, e.colno)
rows = [(s, err(json, s), err(pyjson, s)) for s in ['"\\x"', '["ab\\y"]', '"a\x01b"', '{"k":\n "\t"}']]
for s, c, p in rows:
    print(repr(s))
    print('   C     :', c)
    print('   Python:', p)
esc_c, esc_p = rows[0][1], rows[0][2]
ctl_c, ctl_p = rows[2][1], rows[2][2]
```

</details>

#### 9. json: the C encoder writes str() of str-subclass separators and custom-encoder results (gh-148241 fixed only the values)

gh-148241 (3.15 regression: str-enum values serialized as `str(obj)`) was fixed by making
`write_escaped_ascii`/`write_escaped_unicode` write the characters of a str subclass instead of
calling `PyUnicodeWriter_WriteStr()`, which calls `str()` on anything but an exact str
(Objects/unicode_writer.c:313-331). The other `PyUnicodeWriter_WriteStr()` calls of the encoder
were left alone: `key_separator` (always), `item_separator` when `indent` is None (with an
indent the separator is a concatenation, an exact str), and `_steal_accumulate` of what a custom
`encoder` returns. So with `class S(str): __str__ = lambda s: 'X'`,
`json.dumps({'a': [1, 2]}, separators=(S(','), S(':')))` is `'{"a"X[1X2]}'` with `_json` and
`'{"a":[1,2]}'` without it (and with `''.join(JSONEncoder(...).iterencode(...))`, which always
uses the Python encoder). A `__str__` that raises makes `json.dumps` raise in C only; a str-enum
separator is written as `Sep.COMMA`. `c_make_encoder` with an encoder returning a str subclass
writes `X` where `_make_iterencode` with the same encoder writes the text.
The Lean model writes separators and encoder results as objects (SObj, EncFull.lean); the twins
agree on exact-str separators (json-dumps-twins) and differ with subclasses
(json-dumps-twins-separators, json-encoder-string-raw, both refuted).

<details><summary>Reproducer</summary>

```python
import json, _json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
class S(str):
    __str__ = lambda s: 'X'
v = {'a': [1, 2]}
c = json.dumps(v, separators=(S(','), S(':')))
p = pyjson.dumps(v, separators=(S(','), S(':')))
it = ''.join(json.JSONEncoder(separators=(S(','), S(':'))).iterencode(v))
ci = json.dumps(v, separators=(S(','), S(':')), indent=1)
enc = _json.make_encoder(None, None, lambda s: S('"' + s + '"'), None, ':', ',', False, False, True)
pyenc = pyjson.encoder._make_iterencode(None, None, lambda s: S('"' + s + '"'), None, float.__repr__,
                                       ':', ',', False, False, True)
ce, pe = enc(['ab'], 0)[0], ''.join(pyenc(['ab'], 0))
print('dumps C        :', c)
print('dumps Python   :', p)
print('iterencode     :', it)
print('dumps C indent :', repr(ci))
print('encoder C      :', ce)
print('encoder Python :', pe)
```

</details>

#### 10. json: the C and pure-Python twins stop at different nesting depths (C stack limit vs sys.getrecursionlimit())

Since 3.14, `_Py_EnterRecursiveCall` in `_json` is a check of the machine stack pointer, not a
count, so the C decoder and encoder go as deep as the thread's C stack allows (about 100000
levels on Linux with an 8 MB stack), while the pure-Python twins push Python frames and stop at
`sys.getrecursionlimit()`: two frames per array or object level when decoding (`_scan_once` and
`JSONArray`/`JSONObject`), one per container level when encoding (a generator), plus the string
scanners and `default`. At the default limit of 1000, `json.loads('[' * 1000 + ']' * 1000)`
succeeds with `_json` and raises RecursionError without it; so does `json.dumps` of lists 1000
deep. Conversely, with a raised recursion limit the Python twins decode documents the C twin
rejects with "Stack overflow (used N kB) while decoding a JSON array from a unicode string".
The Lean model has both limits as parameters (the C stack room in levels, the Python frames
left): the decoder twins agree exactly when neither raises its RecursionError, C needs exactly
k levels for `'[' * k + ']' * k` and Python exactly 2k + 1 frames
(json-loads-twins-scan, json-raw-decode-twins-in-range); the encoder needs k + 1 levels and
k + 3 frames for lists k + 1 deep (json-dumps-twins). The statements for every limit are
refuted (json-loads-twins-rec, json-raw-decode-twins-rec, json-dumps-twins-rec).

<details><summary>Reproducer</summary>

```python
import sys, json
from test.support.import_helper import import_fresh_module
pyjson = import_fresh_module('json', blocked=['_json'])
doc = '[' * 1000 + ']' * 1000
def run(f):
    try:
        f()
        return 'ok'
    except RecursionError as e:
        return 'RecursionError: ' + str(e)
lst = []
for _ in range(999):
    lst = [lst]
rows = {'loads C': run(lambda: json.loads(doc)), 'loads Python': run(lambda: pyjson.loads(doc)),
        'dumps C': run(lambda: json.dumps(lst)), 'dumps Python': run(lambda: pyjson.dumps(lst))}
for k, v in rows.items():
    print(f'{k:13s} {v}')
print('recursion limit', sys.getrecursionlimit())
if (rows['loads C'] == 'ok' and rows['loads Python'].startswith('RecursionError')
        and rows['dumps C'] == 'ok' and rows['dumps Python'].startswith('RecursionError')):
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
