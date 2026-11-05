<!-- title: Small inconsistencies in json found by a formal model -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. json: C and pure-Python encoders print different exception notes and key-type messages (original vs converted key, %T vs __name__)

The notes added by gh-122163 differ between the twins in three ways, and so does the TypeError for a key of an unsupported type: 1. A failing dict value is noted with its key. C formats the original key with %R (`_PyErr_FormatNote("when serializing %T item %R", dct, key)`), Python formats the key after its conversion to str (`f'... item {key!r}'` after `key = int.__repr__(key)` etc.): `json.dumps({1: set()})` notes `when serializing dict item 1` with `_json` and `when serializing dict item '1'` without it; `{True: ...}` gives `True` vs `'true'`, `{None: ...}` `None` vs `'null'`, `{1.5: ...}` `1.5` vs `'1.5'`. 2. C's %T prints the fully qualified name (`_PyType_GetFullyQualifiedName`: module and __qualname__ unless the module is builtins or __main__), Python `type(o).__name__`: an object of class `Foo` in module `mymod` whose default() result fails is noted `when serializing mymod.Foo object` vs `when serializing Foo object`; the same for dict and list subclasses and nested classes (`mymod.A.B` vs `B`). 3. `keys must be str, int, float, bool or None, not %.100s` uses `tp_name` in C and `key.__class__.__name__` in Python: `not datetime.date` vs `not date`, `not decimal.Decimal` vs `not Decimal`. The Lean model records each note's kind, type and key (Note, EncFull.lean) and proves that on exact containers, when neither twin hits its recursion limit, the notes correspond one to one (json-dumps-twins); printed, they differ only as above (json-dumps-twins-notes, refuted).

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

#### 2. json: pure-Python raw_decode() accepts a negative idx and returns garbage (C raises ValueError('idx cannot be negative'))

JSONDecoder.raw_decode(s, idx) with the C scanner rejects idx < 0 with ValueError('idx cannot be negative') (the check added for bpo-21529, CVE-2014-4616). The pure-Python scanner has no such check: `string[idx]` wraps around, slices and `NUMBER_RE.match(string, idx)` (which clamps a negative pos to 0) then read from unrelated places, and it can return a value and even a negative end index: raw_decode('12', -1) == (12, 2) (string[-1] is '2', then the number is matched from index 0), raw_decode('{}x', -3) == ({}, -1), raw_decode('null ', -5) == (None, -1), and raw_decode('12', -3) raises JSONDecodeError('Expecting value: line 1 column -2 (char -3)'). For idx > sys.maxsize C raises OverflowError while Python raises JSONDecodeError. For 0 <= idx <= sys.maxsize the twins agree (Lean: json-raw-decode-twins-in-range). The helper one level down has the same gap: c_scanstring(s, end) raises ValueError('end is out of bounds') for end outside [0, len(s)], while py_scanstring('ab', 5) raises JSONDecodeError naming char 4, past the end of the document (Lean: json-scanstring-twins; for 0 <= end <= len(s) the twins agree, json-scanstring-twins-in-range).

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

#### 3. json: C and pure-Python decoders report invalid escapes at different positions (and both string errors with different messages)

For an invalid backslash escape the C scanner raises JSONDecodeError('Invalid \\escape') at the index of the backslash, while the pure-Python py_scanstring raises JSONDecodeError("Invalid \\escape: 'x'") at the index of the character after it. So `pos`, `colno` and the message all differ: json.loads('"\\x"') gives pos=1, colno=2 with _json and pos=2, colno=3 without it. For a raw control character inside a string (strict=True) the position agrees but the message does not: C says 'Invalid control character at', Python "Invalid control character '\\x01' at". The Lean model proves these are the only differences: for every document and every strict / object_pairs_hook / parse_int setting, json.loads agrees between the twins (value, or exception class, msg, pos, lineno, colno) except for exactly these two errors (json-loads-twins-scan), and the same holds for raw_decode(s, idx) with 0 <= idx <= sys.maxsize (json-raw-decode-twins-in-range).

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

#### 4. json: the C encoder writes str() of str-subclass separators and custom-encoder results (gh-148241 fixed only the values)

gh-148241 (3.15 regression: str-enum values serialized as `str(obj)`) was fixed by making `write_escaped_ascii`/`write_escaped_unicode` write the characters of a str subclass instead of calling `PyUnicodeWriter_WriteStr()`, which calls `str()` on anything but an exact str (Objects/unicode_writer.c:313-331). The other `PyUnicodeWriter_WriteStr()` calls of the encoder were left alone: `key_separator` (always), `item_separator` when `indent` is None (with an indent the separator is a concatenation, an exact str), and `_steal_accumulate` of what a custom `encoder` returns. So with `class S(str): __str__ = lambda s: 'X'`, `json.dumps({'a': [1, 2]}, separators=(S(','), S(':')))` is `'{"a"X[1X2]}'` with `_json` and `'{"a":[1,2]}'` without it (and with `''.join(JSONEncoder(...).iterencode(...))`, which always uses the Python encoder). A `__str__` that raises makes `json.dumps` raise in C only; a str-enum separator is written as `Sep.COMMA`. `c_make_encoder` with an encoder returning a str subclass writes `X` where `_make_iterencode` with the same encoder writes the text. The Lean model writes separators and encoder results as objects (SObj, EncFull.lean); the twins agree on exact-str separators (json-dumps-twins) and differ with subclasses (json-dumps-twins-separators, json-encoder-string-raw, both refuted).

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

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
