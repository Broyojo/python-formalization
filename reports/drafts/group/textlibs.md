<!-- title: textlibs: 50 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. base64.decode raises on input that base64.decodebytes accepts, when a group spans a line break

`base64.decode` passes each `readline()` to `binascii.a2b_base64` on its own, and
`base64.decodebytes` passes the whole input. A four-character group split by a line break is valid
for the second and raises for the first: `b'YW\nJj\n'` is `b'abc'` for `decodebytes`, and
`binascii.Error: Incorrect padding` for `decode`. Output of `encode` and `encodebytes` never does
this, because they write whole groups, so only base64 from other encoders is affected.

<details><summary>Reproducer</summary>

```python
import base64, binascii, io
data = b'YW\nJj\n'
whole = base64.decodebytes(data)
try:
    base64.decode(io.BytesIO(data), io.BytesIO())
    lines = None
except binascii.Error as e:
    lines = str(e)
print(whole, lines)
```

</details>

#### 2. binascii: the reverse-table cache is keyed by the alphabet object, so a bytes subclass can get another alphabet's table

The decoders that take `alphabet=` (a2b_base64, a2b_base32, a2b_base85, new in 3.15) build a
256-byte reverse table and cache it in a module dict keyed by the alphabet object itself
(Modules/binascii.c:673 PyDict_GetItemRef, :691 PyDict_SetItem). The argument is a
PyBytesObject, so a bytes subclass is accepted, and the dict asks its `__hash__` and `__eq__`.
A subclass whose `__hash__` equals that of an alphabet already used and whose `__eq__` says yes
is given the stored alphabet's table instead of one built from its own bytes. After
`a2b_base64(b'AAAA', alphabet=URLSAFE_BASE64_ALPHABET)`, an `Alpha(BASE64_ALPHABET)` of that kind
decodes `b'-_-_'` to `b'\xfb\xff\xbf'`, and strict mode rejects `b'+/8='`, which
`b2a_base64(b'\xfb\xff', alphabet=a)` itself wrote ("Only base64 data is allowed"). For base32 it is
silent wrong data: with `A32(BASE32_ALPHABET)` hashing like BASE32HEX_ALPHABET,
`a2b_base32(b2a_base32(b'\xff', alphabet=b), alphabet=b)` returns `b'9'`. The same lookup lets a
raising `__hash__` or `__eq__` escape from the decoder (ValueError from `__hash__` here).
The damage is not confined to the caller that passed the subclass: once a subclass alphabet is
stored, later callers passing the plain module constants are affected too, because a stored subclass
key is compared first with its own `__eq__`. After `A32(BASE32_ALPHABET)` (hashing like
BASE32HEX_ALPHABET, `__eq__` always true) has been used once, `a2b_base32(b'VS======',
alphabet=BASE32HEX_ALPHABET)` returns `b'\xac'` instead of `b'\xff'` for every caller in the process;
after a subclass whose `__eq__` raises has been stored under the hash of BASE64_ALPHABET,
`a2b_base64(..., alphabet=BASE64_ALPHABET)` raises that ValueError.

<details><summary>Reproducer</summary>

```python
import binascii
URL = binascii.URLSAFE_BASE64_ALPHABET
binascii.a2b_base64(b"AAAA", alphabet=URL)
class Alpha(bytes):
    def __hash__(self): return hash(URL)
    def __eq__(self, o): return True
a = Alpha(binascii.BASE64_ALPHABET)
enc = binascii.b2a_base64(b"\xfb\xff", alphabet=a, newline=False)
try:
    r1 = binascii.a2b_base64(enc, alphabet=a, strict_mode=True)
except binascii.Error as e:
    r1 = "Error: %s" % e
r2 = binascii.a2b_base64(b"-_-_", alphabet=a)
r3 = binascii.a2b_base64(enc, alphabet=bytes(a), strict_mode=True)
print(enc, r1, r2, r3)
# later callers with the plain module constants
class A32(bytes):
    def __hash__(self): return hash(binascii.BASE32HEX_ALPHABET)
    def __eq__(self, o): return True
binascii.a2b_base32(b"", alphabet=A32(binascii.BASE32_ALPHABET))
r4 = binascii.a2b_base32(b"VS======", alphabet=binascii.BASE32HEX_ALPHABET)
# a raising __eq__, in a module whose cache does not hold BASE64_ALPHABET yet
import importlib.util
spec = importlib.util.find_spec("binascii")
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
class R(bytes):
    def __hash__(self): return hash(m.BASE64_ALPHABET)
    def __eq__(self, o): raise ValueError("eq")
m.a2b_base64(b"", alphabet=R(m.URLSAFE_BASE64_ALPHABET))
try:
    m.a2b_base64(b"AAAA", alphabet=m.BASE64_ALPHABET)
    r5 = "no error"
except ValueError as e:
    r5 = "ValueError: %s" % e
print(r4, r5)
if (enc == b"+/8=" and r1 == "Error: Only base64 data is allowed" and r2 == b"\xfb\xff\xbf" and r3 == b"\xfb\xff"
        and r4 == b"\xac" and r5 == "ValueError: eq"):
```

</details>

#### 3. binascii.a2b_base32: with '=' in ignorechars, an ignored '=' before data still counts as padding

With `ignorechars=b'='` the docs say the pad characters "presented before the end of the encoded
data ... will be ignored". a2b_base32 counts every '=' in `pads` and, unlike a2b_base64 (which sets
`pads = 0` after each data character, Modules/binascii.c:873), never resets it after a data
character. An ignored '=' in the middle therefore still pays for the padding at the end:
`a2b_base32(b'AAAAAAA', ignorechars=b'=')` raises "Incorrect padding", but
`a2b_base32(b'AAAA=AAA', ignorechars=b'=')` returns `b'\x00\x00\x00\x00'`, and
`a2b_base32(b'AA====AA', ignorechars=b'=')` returns `b'\x00\x00'` (seven or four data characters,
no padding after them). a2b_base64 with the same options gives "Incorrect padding" for
`b'AAA'`, `b'AA=A'` and `b'A=AA'` alike. base64.b32decode passes ignorechars through, so it behaves
the same way.

<details><summary>Reproducer</summary>

```python
import binascii
def dec(s):
    try:
        return binascii.a2b_base32(s, ignorechars=b"=")
    except binascii.Error as e:
        return "Error: %s" % e
a, b, c = dec(b"AAAAAAA"), dec(b"AAAA=AAA"), dec(b"AA====AA")
d = None
try:
    binascii.a2b_base64(b"AA=A", ignorechars=b"=")
except binascii.Error as e:
    d = str(e)
print(a, b, c, d)
```

</details>

#### 4. binascii.b2a_qp writes lines longer than its own MAXLINESIZE of 76 before a line ending

`binascii.b2a_qp(b'a' * 75 + b' \n')` returns a 78-character line, and `b'a' * 74 + b' \n'` a
77-character one, although MAXLINESIZE is 76 and the encoder inserts soft line breaks to respect
it. The soft-break test is skipped when the next byte is a newline, so the space is written raw
at column 76 at most. The line-end branch then rewrites that trailing space as `=20`, adding two
characters after the length was checked.

<details><summary>Reproducer</summary>

```python
import binascii
out = binascii.b2a_qp(b'a' * 75 + b' \n')
longest = max(len(line) for line in out.split(b'\n'))
print(out, longest)
```

</details>

#### 5. csv.reader, csv.writer and register_dialect run a _csv.Dialect subclass's __init__ again, with the instance as its argument

`_call_dialect` calls the type `_csv.Dialect` with the dialect instance as an argument. `dialect_new`
returns that same instance when it can be reused, and `type_call` then runs `tp_init` on the result,
because it is an instance of the type called. For a subclass that is the subclass's own `__init__`,
called with the instance as an extra argument. A subclass with `def __init__(self)` gives
`TypeError: D.__init__() takes 1 positional argument but 2 were given` from
`csv.reader([], D())`, and one that accepts `*args` is re-initialised by every reader and writer
made from it.

<details><summary>Reproducer</summary>

```python
import _csv, csv

class D(_csv.Dialect):
    def __init__(self):
        pass

d = D()
try:
    csv.reader([], d)
    r = None
except TypeError as e:
    r = str(e)
print(r)
```

</details>

#### 6. _csv.Dialect.lineterminator returns NULL with no exception on a half-built instance

`Dialect_get_lineterminator` is `return Py_XNewRef(self->lineterminator)`. `dialect_new` allocates the
object, and a bad `delimiter` argument fails before `_set_str` fills that slot. A subclass `__del__`
runs while the object is released and can read the attribute, which then returns NULL with no
exception set. The interpreter reports `SystemError: error return without exception set`. On a
debug build the same return would be an assertion failure in the result check. No other getter
does this, because the rest read C fields.

<details><summary>Reproducer</summary>

```python
import _csv
seen = []

class D(_csv.Dialect):
    def __del__(self):
        try:
            self.lineterminator
        except SystemError as e:
            seen.append(str(e))

try:
    D(delimiter=5)
except TypeError:
    pass
print(seen)
```

</details>

#### 7. csv.writer silently drops delimiters after 2**31 fields, because num_fields is a C int

WriterObj.num_fields is a C int (Modules/_csv.c:149), incremented with no check for every field
(:1297). join_append_data writes a delimiter when num_fields > 0 (:1173). With a row of more than
INT_MAX fields the count wraps negative, which is undefined behaviour in C and in practice a wrap,
and every later field is written with no delimiter and no error. Fields run together silently. The
Lean model, where the count is a C int, predicted the exact figure below before it was measured: a
row of 2147483653 fields gets 2147483647 delimiters, not 2147483652.

<details><summary>Reproducer</summary>

```python
import csv, itertools
n = 2**31 + 5
got = []
class W:
    def write(self, line):
        got.append(line.count(','))
csv.writer(W(), lineterminator='\n').writerow(itertools.repeat('', n))
print('fields', n, 'delimiters', got[0], 'expected', n - 1)
```

</details>

#### 8. NOT FOR FILING: the csv round trip does not hold past two documented limits

This records why CsvRoundTripNoSkip carries two assumptions; it is not a defect report. With
lineterminator='x', the reader takes the terminator as field text, so 'a' reads back as 'ax'. And a
field over field_size_limit() is written, but the reader raises csv.Error. Both are documented.

<details><summary>Reproducer</summary>

```python
import csv, io
buf = io.StringIO(newline='')
csv.writer(buf, lineterminator='x').writerow(['a'])
terminator = next(csv.reader([buf.getvalue()], lineterminator='x'))
buf = io.StringIO(newline='')
csv.writer(buf).writerow(['a' * 200000])
try:
    next(csv.reader([buf.getvalue()]))
    limit = None
except csv.Error as e:
    limit = str(e)
print(terminator, limit)
```

</details>

#### 9. csv.writer does not quote a leading space under skipinitialspace=True, so the reader silently drops it

With skipinitialspace=True, `csv.writer` writes the field ' a' unquoted, and `csv.reader` with the
same dialect reads 'a'. A field ' ' reads back as ''. The data changes silently: no error is
raised, and the dialect is the same on both sides. In a sweep of 300000 random dialects and rows,
every round trip failure had skipinitialspace=True; with it off, none failed, and for QUOTE_MINIMAL
and QUOTE_ALL with a newline terminator that is proved (CsvRoundTripNoSkip). The Lean refutation is
CsvRoundTrip.

<details><summary>Reproducer</summary>

```python
import csv, io
rows = [[' a', 'b']]
buf = io.StringIO(newline='')
csv.writer(buf, skipinitialspace=True).writerows(rows)
back = list(csv.reader(io.StringIO(buf.getvalue(), newline=''), skipinitialspace=True))
print(repr(buf.getvalue()), back)
```

</details>

#### 10. SequenceMatcher.get_opcodes caches an empty list before computing, so after an exception the next call returns []

`get_opcodes` does `self.opcodes = answer = []` and only then calls `get_matching_blocks`, filling the
list afterwards. If `get_matching_blocks` raises, the empty list stays in the cache, and the next
`get_opcodes()` on the matcher returns `[]` with no error. Empty opcodes are what two empty sequences
give, so the caller is told that there is nothing to do. `a` is not hashed until the matcher runs, so
`SequenceMatcher(None, [[1], 2], [2, 3])` is built without complaint, the first `get_opcodes()` raises
TypeError, and the second returns `[]`. Any exception does the same, including KeyboardInterrupt or a
timeout raised by a signal handler during a long comparison. `ratio()` and `get_matching_blocks()`
have no such problem: they assign their cache when they are done, and raise again on a second call.

<details><summary>Reproducer</summary>

```python
import difflib
s = difflib.SequenceMatcher(None, [[1], 2], [2, 3])
try:
    s.get_opcodes()
    first = None
except TypeError as e:
    first = str(e)
second = s.get_opcodes()
print(repr(first), second)
```

</details>

#### 11. SequenceMatcher.get_grouped_opcodes overwrites the cached opcodes, so later calls give wrong results

`get_grouped_opcodes` does `codes = self.get_opcodes()`, which is the cached list, and then assigns to
`codes[0]` and `codes[-1]` to trim the context. After that, `get_opcodes()` on the same matcher no
longer starts at 0 or ends at the end of the sequences, and a second `get_grouped_opcodes` with a larger
`n` gives less context than a fresh matcher does. With a = "abcdefghx" and b = "abcdefghy" as lists,
`get_opcodes()` is `[('equal', 0, 8, 0, 8), ('replace', 8, 9, 8, 9)]` before a call of
`get_grouped_opcodes(1)` and `[('equal', 7, 8, 7, 8), ('replace', 8, 9, 8, 9)]` after it.

<details><summary>Reproducer</summary>

```python
import difflib
a = list('abcdefgh') + ['x']
b = list('abcdefgh') + ['y']
s = difflib.SequenceMatcher(None, a, b)
before = list(s.get_opcodes())
list(s.get_grouped_opcodes(1))
after = s.get_opcodes()
again = list(s.get_grouped_opcodes(3))
fresh = list(difflib.SequenceMatcher(None, a, b).get_grouped_opcodes(3))
print(before, after)
print(again, fresh)
```

</details>

#### 12. difflib.unified_diff formats non-str lines since the f-strings of color, the garbling _check_types exists to stop

`_check_types` looks only at `a[0]` and `b[0]`, and relies on the later `'-' + line` to raise for the
rest. The `color` change replaced those concatenations in `unified_diff` with f-strings, which format
any object. So `unified_diff(['a', b'x'], ['a', b'y'], lineterm='')` now yields `-b'x'` and `+b'y'`,
and a line that is an int or None is formatted too. `context_diff`, which still concatenates, raises
TypeError for the same arguments. 3.14 raises TypeError from `unified_diff` as well. The comment in
`_check_types` names this outcome as what it is there to prevent: "the alternative is garbled output
when someone passes mixed bytes and str".

<details><summary>Reproducer</summary>

```python
import difflib
a, b = ['a', b'x'], ['a', b'y']
u = list(difflib.unified_diff(a, b, lineterm=''))
try:
    list(difflib.context_diff(a, b, lineterm=''))
    c = None
except TypeError as e:
    c = str(e)
print(u, c)
```

</details>

#### 13. email: group display name that is only a comment raises IndexError in DisplayName.display_name (duplicate of gh-151857)

For `(c)`, `get_phrase` returns a phrase holding one CFWS token (with the defect "phrase does not
start with word"). `DisplayName.display_name` copies it, pops the leading CFWS, and then reads
`res[-1]` of the now empty list: IndexError. `DisplayName.value` calls `display_name` whenever
the name has defects. So the group `(c):;` or `(x): a@b.com;` in To/Cc makes
`msg['To']` raise IndexError with the modern policy (AddressHeader.parse reads `display_name`).

<details><summary>Reproducer</summary>

```python
import email
from email import policy, _header_value_parser as P
dn, _ = P.get_display_name('(c)')
out = []
for f in (lambda: dn.display_name, lambda: dn.value):
    try:
        f()
        out.append(None)
    except IndexError as e:
        out.append(str(e))
m = email.message_from_string('To: (x): a@b.com;\n\nbody\n', policy=policy.default)
try:
    m['To']
    hdr = None
except IndexError as e:
    hdr = str(e)
print(out, hdr)
```

</details>

#### 14. email: MIME-Version '²' raises ValueError from int() in parse_mime_version (duplicate of gh-158708)

`parse_mime_version` checks the major and minor numbers with `digits.isdigit()` and then calls
`int(digits)`. `'²'.isdigit()` is true and `int('²')` raises ValueError, so the header value `²`
(or `1.²`, or a 4301-digit number) makes the MIME-Version header parser raise instead of adding
"Expected MIME major version number" as it does for other junk.

<details><summary>Reproducer</summary>

```python
from email import _header_value_parser as P
out = []
for v in ('²', '1.²', '1' * 4301):
    try:
        P.parse_mime_version(v)
        out.append(None)
    except ValueError as e:
        out.append(type(e).__name__)
print(out)
```

</details>

#### 15. email: reading a header with a few hundred nested comments raises RecursionError (policy.default, HeaderRegistry)

`get_comment` (Lib/email/_header_value_parser.py:1287-1309) parses a nested comment by calling
itself (:1300-1301), and `Comment.__str__` / `Comment.quote` (:290-299) and `Comment.content`
recurse the same way over the result. Nothing bounds the nesting depth, so a header value with a
few hundred `(` (well within any line-length limit a mail server enforces on a folded header)
exhausts the Python stack. The RecursionError is not a `HeaderParseError`, so the parser's
recovery paths do not catch it: it propagates out of `HeaderRegistry()(name, value)` and out of
`msg['To']` on a message parsed with `policy.default`, where malformed input is otherwise reported
as defects.

<details><summary>Reproducer</summary>

```python
import email, email.policy
from email.headerregistry import HeaderRegistry
def outcome(n):
    v = 'a@b ' + '(' * n + ')' * n
    out = []
    try:
        str(HeaderRegistry()('To', v)); out.append('ok')
    except Exception as e:
        out.append(type(e).__name__)
    try:
        m = email.message_from_string('To: ' + v + '\n\n', policy=email.policy.default)
        str(m['To']); out.append('ok')
    except Exception as e:
        out.append(type(e).__name__)
    return out
shallow, deep = outcome(20), outcome(500)
print('depth 20:', shallow, 'depth 500:', deep)
```

</details>

#### 16. email: Content-Type parameter ending in '*' raises IndexError in get_parameter (duplicate of gh-151857)

`get_parameter` reads the attribute, sees `*`, tries `get_section` (which raises
HeaderParseError, ignored, when no digits follow), checks `if not value`, then takes the `*` as
the extended-parameter marker with `value = value[1:]`, and goes on to `if value[0] != '='`
without checking that `value` is still non-empty. For `text/plain; a*` that is `''[0]`:
IndexError, which `parse_mime_parameters` does not catch. Reading `msg['Content-Type']`, or
`get_content_type()` (and so `message_from_string` itself, through the feed parser's
`get_content_type()` call) raises with email.policy.default.

<details><summary>Reproducer</summary>

```python
import email
from email import policy, _header_value_parser as P
out = []
for f, v in ((P.parse_content_type_header, 'text/plain; a*'),
             (P.parse_content_disposition_header, 'attachment; filename*')):
    try:
        f(v)
        out.append(None)
    except IndexError as e:
        out.append(str(e))
try:
    email.message_from_string('Content-Type: text/plain; name*\n\nbody\n', policy=policy.default)
    msg = None
except IndexError as e:
    msg = str(e)
print(out, msg)
```

</details>

#### 17. email: _get_ptext_to_endchars sets had_qp only for '\\\\', so get_dtext misses the obsolete quoted-pair defect for '[a\\b]'

The docstring of `_get_ptext_to_endchars` says its third result is "a flag that is True iff there
were any quoted printables decoded". The loop sets `had_qp` only in the branch for a backslash
after a backslash; any other quoted pair (`\b`, `\]`, `\"`) is decoded with the flag left False.
`get_dtext` uses the flag to add ObsoleteHeaderDefect("quoted printable found in domain-literal"),
so the domain literal `[a\\b]` (an escaped backslash) gets the defect and `[a\b]` and `[a\]b]` do
not, although all three use the obsolete quoted-pair form of RFC 5322 obs-dtext. For `[a\]b]` the
`domain` property then reads `[a]b]`, a domain literal that is no longer well formed, with no
defect recorded.

<details><summary>Reproducer</summary>

```python
from email import _header_value_parser as P
a = P._get_ptext_to_endchars('a\\b', '[]')
b = P._get_ptext_to_endchars('a\\\\b', '[]')
d1 = [type(d).__name__ for d in P.get_domain_literal('[a\\b]')[0].all_defects]
d2 = [type(d).__name__ for d in P.get_domain_literal('[a\\\\b]')[0].all_defects]
print(a, b, d1, d2)
```

</details>

#### 18. email: str() of a quoted string drops the quoted pair that kept '=?...?=' literal, so reparsing decodes it

The parser decodes an RFC 2047 encoded word inside a quoted string (with the defect "encoded word
inside quoted string"), testing `value[:2] == '=?'` at each position. A sender can keep the text
literal with a quoted pair: in `"\=?utf-8?q?a?="` the `\=` hides the `=?`, and the value is the
literal `=?utf-8?q?a?=`. `str()` of that token writes it back with `make_quoted_pairs`, which
escapes only `\` and `"`, giving `"=?utf-8?q?a?="`; parsing that decodes the encoded word, and the
value becomes `a`. So `str()`, which the module docstring calls the canonical form of the parsed
text, is not a fixed point: a display name changes when a parsed header is re-serialised from its
parse tree and parsed again.

<details><summary>Reproducer</summary>

```python
from email import _header_value_parser as P
q, rest = P.get_quoted_string('"\\=?utf-8?q?a?="')
s = str(q)
q2, rest2 = P.get_quoted_string(s)
print(repr(q.value), repr(s), repr(q2.value), rest, rest2)
```

</details>

#### 19. email: RFC 2231 section number '²' raises ValueError from int() in get_section (duplicate of gh-87112)

`get_section` takes digits with `str.isdigit()`, which is true for characters such as `²`
(Numeric_Type=Digit) that `int()` rejects, then calls `int(digits)`. The ValueError escapes
`get_parameter`, which only catches HeaderParseError, so `text/plain; a*²=x` makes
parse_content_type_header (and msg['Content-Type'] with the modern policy) raise ValueError.
A section of more than 4300 ASCII digits raises the int max-str-digits ValueError the same way.

<details><summary>Reproducer</summary>

```python
from email import _header_value_parser as P
out = []
for v in ('*²', '*' + '1' * 4301):
    try:
        P.get_section(v)
        out.append(None)
    except ValueError as e:
        out.append(type(e).__name__)
try:
    P.parse_content_type_header('text/plain; a*²=x')
    ct = None
except ValueError as e:
    ct = str(e)
print(out, ct)
```

</details>

#### 20. copy.copy of a C Element shares its attrib dict with the original (and drops the subclass)

Element.__copy__ in C passes self->extra->attrib to create_new_element, which stores that same
dict in the copy (create_extra). After c = copy.copy(e), c.set('z', '1') also gives e the
attribute z, and c.attrib is e.attrib. The children are copied into a new array, so only the
attributes are shared. The pure-Python Element copies through makeelement ->
self.__class__(tag, attrib), whose __init__ builds a new dict, so the original is unaffected.
The same call also makes an exact Element: copy.copy and copy.deepcopy of an Element subclass
(and the subclass children a deepcopy recreates) come back as plain Element in C and keep their
class in the twin.

<details><summary>Reproducer</summary>

```python
import copy
import xml.etree.ElementTree as ET
e = ET.Element('r', {'k': 'v'})
c = copy.copy(e)
c.set('z', '1')
class Sub(ET.Element):
    pass
s = copy.copy(Sub('r'))
print('original:', e.attrib, 'shared:', c.attrib is e.attrib, 'copy class:', type(s).__name__)
```

</details>

#### 21. Pure-Python Element.__setitem__ consumes an iterator before storing it, so slice assignment from a generator inserts nothing

Element.__setitem__ checks a slice value with `for elt in element: self._assert_is_element(elt)`
and then runs `self._children[index] = element`, which iterates the value a second time. A
generator or any other one-shot iterator is exhausted by the first loop, so
e[1:1] = (x for x in new) inserts nothing, and e[:] = iter(new) empties the element. The C
accelerator calls PySequence_Fast once and stores every item.
Element.extend differs the other way on a failing iterator: C materialises the iterable with
PySequence_Fast before appending, so an iterator that yields two Elements and then raises leaves
the element unchanged in C and with both appended in the twin (which, like list.extend, appends
as it goes). Neither is documented; recorded as a twin difference.
Element.remove checks its argument only after list.remove has searched: e.remove(5) with a child
whose __eq__ returns True removes that child in the twin, while C's Argument Clinic refuses 5
with TypeError before searching (3.15 added the twin's TypeError to match C, but after the
search).
The twin also checks the value before the index, so e[100] = 5 raises TypeError there and
IndexError in C; that difference is cosmetic and is recorded only for completeness.
e.extend(e) never returns in the twin: Element has no __iter__, so the loop iterates e by index
while appending to it and grows without bound (list.extend special-cases its own list); C
takes a sequence snapshot and doubles the children. Likewise insert(2**63, 5) raises TypeError
in the twin and OverflowError in C, whose Argument Clinic converts the index first. (Found by
the second review pass of the etree rows; checked on 3.15.2.)

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

#### 22. HTMLParser with convert_charrefs=False reports a different entity name depending on where the feed splits

`feed('&amp-->')` calls `handle_entityref('amp--')`. `feed('&amp--')` then `feed('>')` calls
`handle_entityref('amp-')`, followed by data `->`. The entity regex needs one character after the
name, and `-` is allowed in the name, so at the end of a chunk the match backtracks and takes the
last `-` as the terminator. The parser accepts that match and does not wait for more input. The
default `convert_charrefs=True` is not affected.

<details><summary>Reproducer</summary>

```python
from html.parser import HTMLParser

class P(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=False)
        self.names = []
    def handle_entityref(self, name):
        self.names.append(name)

a = P()
a.feed('&amp-->')
a.close()
b = P()
b.feed('&amp--')
b.feed('>')
b.close()
print(a.names, b.names)
```

</details>

#### 23. DUPLICATE of #158719 (closed, not planned): html.unescape raises ValueError on a long decimal reference

`html.unescape('&#' + '1' * 4301 + ';')` raises ValueError, from the digit limit of int(). So does
`'&#' + '0' * 4301`, whose value is 0. The hexadecimal form is not limited, and gives U+FFFD. HTMLParser
with the default convert_charrefs=True raises too, in text and in attribute values, so a short piece
of hostile HTML stops a parser that is otherwise forgiving. The HTML 5 rule is U+FFFD for any number
past 0x10FFFF.

<details><summary>Reproducer</summary>

```python
import html
print(ascii(html.unescape('&#x' + '1' * 5000 + ';')))
try:
    html.unescape('&#' + '1' * 4301 + ';')
except ValueError as e:
    print(str(e)[:44])
```

</details>

#### 24. os.path.join calls an os.PathLike object not a path, and hides what __fspath__ raised

`posixpath.join('a', PL(b'x'))`, where `PL.__fspath__` returns bytes, raises
`TypeError: join() argument must be str, bytes, or os.PathLike object, not 'PL'`, though `PL` is an
os.PathLike object. The real problem is the mix of str and bytes, which `join('a', b'x')` reports
as "Can't mix strings and bytes in path components". Also, a `TypeError` or `AttributeError` raised
inside `__fspath__` is replaced by the same message, so a bug in the user's method is reported as a
wrong argument type. ntpath.join does the same. `commonpath` and `relpath` report the mix correctly.

<details><summary>Reproducer</summary>

```python
import posixpath

class PL:
    def __init__(self, v):
        self.v = v
    def __fspath__(self):
        if isinstance(self.v, Exception):
            raise self.v
        return self.v

out = []
for arg in (PL(b'x'), PL(TypeError('mine'))):
    try:
        posixpath.join('a', arg)
    except TypeError as e:
        out.append(str(e))
print(out)
want = "join() argument must be str, bytes, or os.PathLike object, not 'PL'"
```

</details>

#### 25. DUPLICATE of #100162: ntpath.normpath turns the relative path .\\c:\\x into the absolute c:\\x

`ntpath.normpath('.\\c:\\windows')` is `c:\windows`. `ntpath.isabs` is False for the input and True
for the result, so a check made before normalising is void. `pathlib.PureWindowsPath` keeps the `.\`
for this reason. The same holds for `.\c:foo` and for `x\..\c:\windows`.

<details><summary>Reproducer</summary>

```python
import ntpath, pathlib
p = '.\\c:\\windows'
n = ntpath.normpath(p)
q = str(pathlib.PureWindowsPath(p))
print(n, ntpath.isabs(p), ntpath.isabs(n), q)
```

</details>

#### 26. plistlib: a binary plist written from datetime.max cannot be read back (InvalidFileException)

The binary writer stores a datetime as the double (value - datetime(2001, 1, 1)).total_seconds()
(Lib/plistlib.py:808-815). Near datetime.max that double is only accurate to about 30
microseconds, and total_seconds() rounds 9999-12-31 23:59:59.999999 up to 252423993600.0, which is
10000-01-01. The reader (:587-595) computes datetime(2001, 1, 1) + timedelta(seconds=f), which
overflows, and parse turns the OverflowError into InvalidFileException. So
plistlib.dumps(datetime.datetime.max, fmt=FMT_BINARY) succeeds and plistlib.loads of the result
raises InvalidFileException("Invalid file"); so does any datetime within about 15 microseconds of
datetime.max. The XML writer drops the microseconds and round-trips the same value. Far from 2001
the binary round trip also silently loses microseconds (datetime(1, 1, 1, 0, 0, 0, 1) reads back
as datetime(1, 1, 1)), which is inherent in the format's double; the exception is not.

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

#### 27. plistlib: the binary writer turns -0.0 into 0.0 when 0.0 was written first

_flatten shares scalar objects by value: it looks up (type(value), value) in self._objtable
(Lib/plistlib.py:717-719, :727-728), and _getrefnum resolves references the same way (:752-754).
0.0 == -0.0 and they hash alike, so in [0.0, -0.0] the second float is written as a reference to
the first, and loads(dumps([0.0, -0.0], fmt=FMT_BINARY)) is [0.0, 0.0]. A lone -0.0 survives, and
the XML writer (repr) keeps both signs, so the two formats disagree. Every other float keeps its
bits (equal floats have equal bits, and NaNs are only shared when they are the same object).

<details><summary>Reproducer</summary>

```python
import math, plistlib
value = [0.0, -0.0]
b = plistlib.loads(plistlib.dumps(value, fmt=plistlib.FMT_BINARY))
x = plistlib.loads(plistlib.dumps(value, fmt=plistlib.FMT_XML))
signs = lambda l: [math.copysign(1.0, v) for v in l]
print("binary:", b, signs(b))
print("xml:   ", x, signs(x))
print("lone -0.0 binary:", math.copysign(1.0, plistlib.loads(plistlib.dumps(-0.0, fmt=plistlib.FMT_BINARY))))
```

</details>

#### 28. NOT FOR FILING: plistlib reads binary plists only as deeply nested as the recursion limit allows

This records why LoadsBinaryInvalidOnly carries a frame bound; it is not a defect report.
_read_object recurses once per nested array or dict, and parse catches OSError, IndexError,
struct.error, OverflowError and ValueError, not RecursionError, so a binary plist of n nested
one-element arrays raises RecursionError("maximum recursion depth exceeded") from loads when fewer
than n + 6 frames are left: three for loads, load and parse, one _read_object per array, and
three below the innermost array's _read_object for _read_refs, _read_ints and _read (the
string's _read_object and its _read need only two). Cycles do not recurse: a container is stored in self._objects before its
elements are read, so the depth is bounded by the number of objects, which the proof uses.

<details><summary>Reproducer</summary>

```python
import sys, plistlib

def chain(n):
    objs = [b"\xa1" + (i + 1).to_bytes(2, "big") for i in range(n)] + [b"\x54seed"]
    offs, body = [], b""
    for o in objs:
        offs.append(8 + len(body))
        body += o
    tbl = 8 + len(body)
    table = b"".join(x.to_bytes(4, "big") for x in offs)
    trailer = (bytes(6) + bytes([4, 2]) + len(objs).to_bytes(8, "big")
               + (0).to_bytes(8, "big") + tbl.to_bytes(8, "big"))
    return b"bplist00" + body + table + trailer

def run(frames, data):
    f, depth = sys._getframe(), 0
    while f is not None:
        depth += 1
        f = f.f_back
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(depth + frames)
    try:
        plistlib.loads(data)
        return "ok"
    except RecursionError:
        return "RecursionError"
    finally:
        sys.setrecursionlimit(old)

for _ in range(5):
    plistlib.loads(chain(2))
res = [run(16, chain(n)) for n in (1, 5, 10, 11)]
print("16 frames, 1/5/10/11 nested arrays:", res)
try:
    plistlib.loads(chain(5000))
    deep = "parsed"
except RecursionError as e:
    deep = "RecursionError: " + str(e)
print("5000 nested arrays at the default limit:", deep)
```

</details>

#### 29. DUPLICATE of #64320: b2a_qp rewrites line ends, so mixed text does not round-trip

In text mode b2a_qp takes the kind of line end from the first line and writes every later line end
that way. `a2b_qp(b2a_qp(b'\\n\\r\\n'))` is `b'\\n\\n'`, and `b'\\r\\n\\n'` comes back as
`b'\\r\\n\\r\\n'`. With `istext=False`, or no `\\r\\n` in the data, the round trip is proven for all
bytes.

<details><summary>Reproducer</summary>

```python
import binascii, quopri
a = binascii.a2b_qp(binascii.b2a_qp(b'\n\r\n'))
b = quopri.decodestring(quopri.encodestring(b'\r\n\n'))
print(a, b)
```

</details>

#### 30. DUPLICATE of #158739 (closed, not planned): quopri's pure-Python encoder splits =XY at a soft break

The pure-Python encoder cuts a long line at 75 characters without looking at what is there, so the
line of 74 `a` and one `\\xff` becomes 74 `a`, `==`, newline, `FF`, which decodes to something else.
This body runs only if binascii cannot be imported.

<details><summary>Reproducer</summary>

```python
import quopri
saved = quopri.a2b_qp, quopri.b2a_qp
quopri.a2b_qp = quopri.b2a_qp = None
s = b'a' * 74 + b'\xff'
e = quopri.encodestring(s)
d = quopri.decodestring(e)
quopri.a2b_qp, quopri.b2a_qp = saved
print(e, d)
```

</details>

#### 31. DUPLICATE of #62222 and #60677: quopri's pure-Python bodies differ from binascii

encodestring(b' ', header=True) is `=20` from binascii and `_` from the pure-Python body. For decoding,
binascii drops a final `=` that the pure-Python body keeps, and in 3.15.2 binascii keeps trailing
whitespace before a newline that the pure-Python body strips. The pure-Python bodies run only if
binascii cannot be imported, which no current build does.

<details><summary>Reproducer</summary>

```python
import binascii, quopri
c1 = quopri.encodestring(b' ', False, True)
c2 = quopri.decodestring(b'=')
saved = quopri.a2b_qp, quopri.b2a_qp
quopri.a2b_qp = quopri.b2a_qp = None
p1 = quopri.encodestring(b' ', False, True)
p2 = quopri.decodestring(b'=')
quopri.a2b_qp, quopri.b2a_qp = saved
print(c1, p1, c2, p2)
```

</details>

#### 32. DUPLICATE of #156513: an IGNORECASE backreference ignores the characters a literal matches

`re.fullmatch(r'(s)s', 'sſ', re.I)` matches and `re.fullmatch(r'(s)\1', 'sſ', re.I)` does
not. All 56 pairs of `_casefix._EXTRA_CASES` differ this way, in both orders: 112 ordered pairs.

<details><summary>Reproducer</summary>

```python
import re
a = re.fullmatch(r'(s)s', 'sſ', re.I)
b = re.fullmatch(r'(s)\1', 'sſ', re.I)
print(a, b)
```

</details>

#### 33. re: a conditional inside the group it tests sees the end mark of a failed path

`re.fullmatch(r'(()(?:(?(1)b))??)', 'b')` matches, and the same pattern with a greedy `?` does not.
Greedy and lazy order the same alternatives, so whether a fullmatch exists should not depend on it.
The lazy repeat first tries the tail, which closes group 1 with an empty span and fails because
the end was not reached. That leaves mark[1] set. Group 2 has already raised lastmark past it, so
LASTMARK_RESTORE does not hide it, and with no enclosing repeat there is no MARK_PUSH to restore
it. The next iteration's `(?(1)b)` then sees group 1 as set, while the group is still open.

<details><summary>Reproducer</summary>

```python
import re
lazy = re.fullmatch(r'(()(?:(?(1)b))??)', 'b')
greedy = re.fullmatch(r'(()(?:(?(1)b))?)', 'b')
print(lazy, greedy)
```

</details>

#### 34. re: a number past the int/str digit limit raises a bare ValueError instead of the error a smaller number gets

`re.compile('a{' + '9' * 5000 + '}')` raises ValueError "Exceeds the limit (4300 digits) for integer
string conversion", while 50 digits raise OverflowError "the repetition number is too large". The
same happens in a conditional group, where 50 digits give PatternError "invalid group reference"
and 5000 digits give ValueError, and in a replacement template's `\g<...>`. The parser calls
`int()` on the digit string before it can apply its own range checks.

<details><summary>Reproducer</summary>

```python
import re
seen = []
for pat in ('a{' + '9' * 50 + '}', 'a{' + '9' * 5000 + '}',
            '(a)(?(' + '9' * 50 + ')b)', '(a)(?(' + '9' * 5000 + ')b)'):
    try:
        re.compile(pat)
        seen.append('no error')
    except Exception as e:
        seen.append(type(e).__name__)
print(seen)
```

</details>

#### 35. DUPLICATE of #160316: Pattern.match finds a match when endpos is less than pos

`re.compile('').match('\n', 1, 0)` returns a match at (1, 1), past endpos, though the docs say no
match will be found when endpos is less than pos. `search` returns None, since SRE(search) tests
`ptr > end` first, which is proved in the model. `match`, `fullmatch` and `findall` run the engine.

<details><summary>Reproducer</summary>

```python
import re
m = re.compile('').match('\n', 1, 0)
s = re.compile('').search('\n', 1, 0)
print(m, s)
```

</details>

#### 36. re: x{m,n}+ with m >= 2 is not equivalent to (?>x{m,n}), as the docs say it is

The docs say "x{m,n}+ is equivalent to (?>x{m,n})". They differ when m >= 2 and x can match more
than one way: `re.fullmatch(r'(?:a|ab){2}+', 'aba')` is None, and
`re.fullmatch(r'(?>(?:a|ab){2})', 'aba')` matches. `re.match(r'(?:a+){2}+', 'aa')` is None, and
`re.match(r'(?>(?:a+){2})', 'aa')` matches. An atomic group forbids backtracking into it once it is
finished, so inside it the iterations can still trade characters to reach the minimum. The
possessive loop makes each iteration atomic alone, so the first iteration cannot give back what
the second needs. No difference appears with m <= 1, so x*+, x++ and x?+ keep the sentence the docs
state for them. The Lean declarative semantics agrees with CPython on 150000 of 150000 random
cases once this is modelled, and the documented form is refuted.

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

#### 37. re.Scanner compiles str phrases without UNICODE and ignores their inline flags

`re.Scanner([(r'\w+', 'W')]).scan('é')` returns `([], 'é')`, while `re.match(r'\w+', 'é')` matches.
Each phrase is parsed on its own and `fix_flags` adds UNICODE in that parse's state, but the
combined pattern is compiled from a separate state whose flags stay at what the caller passed.
So `\w`, `\d`, `\s` and `IGNORECASE` act as ASCII. Inline global flags in a phrase are lost in the
same way: `re.Scanner([(r'(?i)a', 'A')]).scan('A')` finds nothing, and `(?s)` too. Passing
`re.UNICODE` or `re.I` to the constructor works.

<details><summary>Reproducer</summary>

```python
import re
a = re.Scanner([(r'\w+', 'W')]).scan('\xe9')
b = re.match(r'\w+', '\xe9')
c = re.Scanner([(r'(?i)a', 'A')]).scan('A')
d = re.Scanner([(r'a', 'A')], re.I).scan('A')
print(a, b, c, d)
```

</details>

#### 38. DUPLICATE of #149280: shlex.quote returns '' for any false object, past its own type check

`shlex.quote(None)`, `shlex.quote(0)`, `shlex.quote([])` and `shlex.quote(b'')` all return `''`, an
empty shell word, because `if not s` comes before the `isinstance(s, str)` check. `shlex.quote(1)`
raises TypeError. So `shlex.join(['rm', None])` silently builds `rm ''` where a missing value was
meant to be an error, which is what the check is for.

<details><summary>Reproducer</summary>

```python
import shlex
out = [shlex.quote(x) for x in (None, 0, [], b'')]
try:
    shlex.quote(1)
    one = None
except TypeError as e:
    one = str(e)
print(out, one)
```

</details>

#### 39. SimpleQueue.get(timeout=inf) raises OverflowError even with an item ready (C), and the twins disagree on NaN and tiny negative timeouts

The C SimpleQueue.get converts a blocking timeout with _PyTime_FromSecondsObject before it looks
at the queue. So q.put(1); q.get(timeout=float('inf')) raises OverflowError ("timestamp out of
range for C PyTime_t") although the item is there; so do 1e300 and 2**63, and NaN raises
ValueError. queue.Queue.get and the pure-Python queue._PySimpleQueue return the item in all four
cases. The conversion also rounds up: timeout=-1e-10 becomes 0 ns, so C returns the item where
the twin raises ValueError("'timeout' must be a non-negative number").

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

#### 40. struct: a str-subclass format poisons the module cache, so later plain formats get another format's Struct

The module functions cache `Struct` objects in a dict keyed by the format object itself
(Modules/_struct.c:2640-2657). A str subclass whose `__eq__`/`__hash__` ignore case stores
`Struct('B')` under its key; a later plain `'b'` hashes the same and, because the subclass's
`__eq__` is asked first, matches it. So after `struct.calcsize(CI('B'))`,
`struct.unpack('b', b'\xff')` returns `(255,)` instead of `(-1,)`, and keeps doing so for every
module-level call with `'b'` until `struct._clearcache()` or until 100 other formats evict it.
A second face of the same lookup: a hashable object that is not a str at all, but hashes and
compares equal to a cached str key, gets that key's Struct, so `struct.calcsize(K())` returns 1
after `struct.calcsize('b')`, where `Struct(K())` raises TypeError.

<details><summary>Reproducer</summary>

```python
import struct
class CI(str):
    def __eq__(self, o):
        return isinstance(o, str) and self.lower() == o.lower()
    def __hash__(self):
        return hash(self.lower())
struct._clearcache()
struct.calcsize(CI('B'))
r = struct.unpack('b', b'\xff')
struct._clearcache()
s = struct.unpack('b', b'\xff')
print(r, s)
class K:
    def __hash__(self):
        return hash('b')
    def __eq__(self, o):
        return o == 'b'
struct._clearcache()
try:
    struct.calcsize(K())
    k1 = 'accepted'
except TypeError:
    k1 = 'TypeError'
struct.calcsize('b')
try:
    k2 = struct.calcsize(K())
except TypeError:
    k2 = 'TypeError'
print(k1, k2)
```

</details>

#### 41. struct: unpack quiets a signalling NaN in some modes and preserves it in others

`nu_float` and `nu_float_complex` convert with a C cast, which quiets a signalling NaN, while
PyFloat_Unpack4 deliberately preserves one. On 3.15.2 `f`, `<f`, `F` and `<F` quiet while `>f` and
`>F` preserve: `init_endian_tables` swaps the native routines into the little-endian table, floats
included, so byte order decides whether the signal survives. Unpacking 0100807f gives
000000200000f87f with `<f` and 000000200000f07f with `>f` on its reversed bytes.

<details><summary>Reproducer</summary>

```python
import struct
sn = bytes.fromhex('0100807f')
bits = lambda x: struct.pack('<d', x).hex()
native_c = bits(struct.unpack('F', sn + sn)[0].real)
big_c = bits(struct.unpack('>F', sn[::-1] * 2)[0].real)
native_f = bits(struct.unpack('f', sn)[0])
little_f = bits(struct.unpack('<f', sn)[0])
print(native_f, little_f, native_c, big_c)
```

</details>

#### 42. struct: pack_into('4s', ba, 0, ba) writes zeros: the argument is read after the memset of its target

`s_pack_internal` clears the struct's bytes in the target first (`memset`, Modules/_struct.c:2340)
and reads each argument only when it packs that item. When an `s` (or `p`) argument is the very
bytearray being packed into, it is read after the clear, so `pack_into('4s', ba, 0, ba)` turns
`ba` into zeros instead of leaving it as it was, unlike passing `bytes(ba)`.

<details><summary>Reproducer</summary>

```python
import struct
ba = bytearray(b'\x01\x02\x03\x04')
struct.pack_into('4s', ba, 0, ba)
cb = bytearray(b'\x01\x02\x03\x04')
struct.pack_into('4s', cb, 0, bytes(cb))
print(ba, cb)
```

</details>

#### 43. struct: '>q'/'>Q' let an OverflowError from __index__ escape where '<q'/'<Q' raise struct.error

For an object whose `__index__` raises OverflowError, `struct.pack('<q', obj)` raises
struct.error "'q' format requires ... <= number <= ...", while `struct.pack('>q', obj)` raises
the OverflowError itself. On a little-endian build `init_endian_tables` puts `np_longlong` into
the '<' table; `np_longlong` turns any OverflowError from its conversion into struct.error
(Modules/_struct.c:708-715). `bp_longlong` calls `get_pylong` and then `_PyLong_AsByteArray` with
exceptions off, so a failure of `__index__` comes out unchanged (1056-1058). Every other integer
code in every table, including '>i' and '>l', goes through `get_long`/`get_ulong` and gives
struct.error. Same for 'Q'.

<details><summary>Reproducer</summary>

```python
import struct
class I:
    def __index__(self):
        raise OverflowError('boom')
out = []
for fmt in ('<q', '>q', '<Q', '>Q'):
    try:
        struct.pack(fmt, I())
    except Exception as e:
        out.append(type(e).__name__)
print(out)
```

</details>

#### 44. struct: 'P' lets OverflowError escape for __index__ objects but raises struct.error for the equal int

`struct.pack('P', 2**64)` raises struct.error "int too large to convert", while the same value
through an `__index__` object raises a bare OverflowError. Every other integer code turns the
overflow into struct.error itself; `np_void_p` has no RANGE_ERROR and relies on the rewrite in
`s_pack_internal`, which only applies when `PyLong_Check(v)`.

<details><summary>Reproducer</summary>

```python
import struct
class I:
    def __index__(self):
        return 2**64
try:
    struct.pack('P', 2**64)
except Exception as e:
    a = type(e).__name__
try:
    struct.pack('P', I())
except Exception as e:
    b = type(e).__name__
print(a, b)
```

</details>

#### 45. DUPLICATE of bugforge textwrap-c1: lines exceed width when an indent leaves no room

`textwrap.wrap('a', width=1, initial_indent=' ')` returns `[' a']`, of length 2. An indent as long as
width or longer leaves no room, and the code still places one character per line, so the docstring
of `wrap` ("lines of no more than 'self.width' columns") is not met.

<details><summary>Reproducer</summary>

```python
import textwrap
out = textwrap.wrap('a', width=1, initial_indent=' ')
print(out)
```

</details>

#### 46. DUPLICATE of #160043: textwrap.shorten raises for text that fits, when the placeholder does not

`textwrap.shorten('ab', width=4)` raises `ValueError: placeholder too large for max width`, though
the text fits and the placeholder is not needed. The check at the top of `_wrap_chunks` runs before
the text is looked at.

<details><summary>Reproducer</summary>

```python
import textwrap
try:
    print(textwrap.shorten('ab', width=4))
except ValueError as e:
    print(e)
```

</details>

#### 47. tomllib: TOMLDecodeError.pos is one past the end of the document for a trailing backslash in a basic string

When a document ends with a backslash inside a basic string (one-line or multi-line, value or
key), loads raises TOMLDecodeError("Unescaped '\\' in a string") with pos = len(doc) + 1, one past
the end of the document, and colno one past the end of the line. 'a = "\' (length 6) gives
pos 7, colno 8; 'a = """\' (length 8) gives pos 9; '"\' (a key, length 2) gives pos 3. The docs
describe pos as "The index of doc where parsing failed". str(e) is unaffected: it says
"(at end of document)" for every pos >= len(doc).
Duplicate of python/cpython#158566 (open) and hukkin/tomli#312 (open): tomllib is vendored from
tomli, and the CPython thread asks for the fix to go into tomli first.

<details><summary>Reproducer</summary>

```python
import tomllib
seen = []
for doc in ['a = "\\', 'a = """\\', '"\\']:
    try:
        tomllib.loads(doc)
        seen.append((doc, None))
    except tomllib.TOMLDecodeError as e:
        seen.append((doc, len(doc), e.pos, e.colno, str(e)))
print(seen)
```

</details>

#### 48. NOT FOR FILING: tomllib parses nested arrays only as deep as the recursion limit allows

This records why ArrayTableSpec and DocRoundTrip carry a frame bound; it is not a defect report.
parse_value and parse_array recurse, two Python frames per level of array (three per inline
table, with parse_key_value_pair), so 'x = ' + '[' * n + ']' * n parses exactly when 2n + 5
frames are left when loads is called (sys.getrecursionlimit() minus the frames on the stack), and
raises RecursionError("maximum recursion depth exceeded") otherwise. With the default limit of
1000, called from a function of a script (two frames on the stack), 496 levels parse and 497 raise.

<details><summary>Reproducer</summary>

```python
import sys, tomllib

def run(frames, doc):
    f, depth = sys._getframe(), 0
    while f is not None:
        depth += 1
        f = f.f_back
    old = sys.getrecursionlimit()
    sys.setrecursionlimit(depth + frames)
    try:
        return tomllib.loads(doc)
    except RecursionError:
        return None
    finally:
        sys.setrecursionlimit(old)

for _ in range(8):
    tomllib.loads("a = [1]")
ok = True
for n in range(1, 41):
    doc = "x = " + "[" * n + "]" * n
    for frames in range(2 * n + 1, 2 * n + 10):
        got = run(frames, doc) is not None
        if got != (2 * n + 5 <= frames):
            ok = False
            print("threshold differs", n, frames, got)
try:
    tomllib.loads("x = " + "[" * 1000 + "]" * 1000)
    deep = "parsed"
except RecursionError as e:
    deep = str(e)
print("x = [[...]] (1000 levels):", deep)
```

</details>

#### 49. urlunsplit(urlsplit(u, allow_fragments=False, missing_as_none=True)) inserts a '/' before a '#' path

With allow_fragments=False, `_urlsplit` still ends the netloc at `#` (`_splitnetloc` stops at
any of `/?#`) but no longer splits the fragment off, so `urlsplit('http://h#x',
allow_fragments=False)` returns netloc 'h' and path '#x'. `_urlunsplit` then sees a path that does
not start with '/' after a netloc and inserts one, so rebuilding gives 'http://h/#x'. This holds
with the new missing_as_none=True / keep_empty mode, which 3.15 documents as the way to rebuild
a parsed URL, and for geturl(), whose docs list only scheme case and empty components as changes.

<details><summary>Reproducer</summary>

```python
from urllib.parse import urlsplit, urlunsplit, urlparse, urlunparse
r = urlsplit('http://h#x', allow_fragments=False, missing_as_none=True)
out = (r, urlunsplit(r), r.geturl(),
       urlunparse(urlparse('http://h#x', allow_fragments=False, missing_as_none=True)))
print(out)
```

</details>

#### 50. DUPLICATE of #77523: urlsplit rejects brackets in the userinfo by validating the plain host as an IP literal

`_urlsplit` runs `_check_bracketed_netloc` whenever the netloc contains both `[` and `]`, even
when they are in the userinfo. Since the CVE-2025-0938 fix the check looks only at the part
after the last `@`; when that part has no `[` it still calls `_check_bracketed_host` on the
plain host, so `urlsplit('http://user:p[ss]@example.com/')` raises "'example.com' does not
appear to be an IPv4 or IPv6 address", and `urlsplit('http://[a]@1.2.3.4/')` raises "An IPv4
address cannot be in brackets" for an address that is not in brackets. Database URLs with
brackets in the password (the case reported in #105704 and #77523) still fail on 3.15.2, now
with a misleading message.

<details><summary>Reproducer</summary>

```python
from urllib.parse import urlsplit
res = []
for u in ('http://user:p[ss]@example.com/', 'http://[a]@1.2.3.4/', 'http://u[x]@h:80/'):
    try:
        res.append(urlsplit(u).netloc)
    except ValueError as e:
        res.append('ValueError: ' + str(e))
print(res)
```

</details>

### CPython versions tested on

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
