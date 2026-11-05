<!-- title: Small inconsistencies in text and binary codecs found by a formal model (part 1 of 2) -->
### Bug report

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. binascii.b2a_qp writes lines longer than its own MAXLINESIZE of 76 before a line ending

`binascii.b2a_qp(b'a' * 75 + b' \n')` returns a 78-character line, and `b'a' * 74 + b' \n'` a 77-character one, although MAXLINESIZE is 76 and the encoder inserts soft line breaks to respect it. The soft-break test is skipped when the next byte is a newline, so the space is written raw at column 76 at most. The line-end branch then rewrites that trailing space as `=20`, adding two characters after the length was checked.

<details><summary>Reproducer</summary>

```python
import binascii
out = binascii.b2a_qp(b'a' * 75 + b' \n')
longest = max(len(line) for line in out.split(b'\n'))
print(out, longest)
```

</details>

#### 2. csv.writer silently drops delimiters after 2**31 fields, because num_fields is a C int

WriterObj.num_fields is a C int (Modules/_csv.c:149), incremented with no check for every field (:1297). join_append_data writes a delimiter when num_fields > 0 (:1173). With a row of more than INT_MAX fields the count wraps negative, which is undefined behaviour in C and in practice a wrap, and every later field is written with no delimiter and no error. Fields run together silently. The Lean model, where the count is a C int, predicted the exact figure below before it was measured: a row of 2147483653 fields gets 2147483647 delimiters, not 2147483652.

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

#### 3. csv.writer does not quote a leading space under skipinitialspace=True, so the reader silently drops it

With skipinitialspace=True, `csv.writer` writes the field ' a' unquoted, and `csv.reader` with the same dialect reads 'a'. A field ' ' reads back as ''. The data changes silently: no error is raised, and the dialect is the same on both sides. In a sweep of 300000 random dialects and rows, every round trip failure had skipinitialspace=True; with it off, none failed, and for QUOTE_MINIMAL and QUOTE_ALL with a newline terminator that is proved (CsvRoundTripNoSkip). The Lean refutation is CsvRoundTrip.

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

#### 4. SequenceMatcher.get_opcodes caches an empty list before computing, so after an exception the next call returns []

`get_opcodes` does `self.opcodes = answer = []` and only then calls `get_matching_blocks`, filling the list afterwards. If `get_matching_blocks` raises, the empty list stays in the cache, and the next `get_opcodes()` on the matcher returns `[]` with no error. Empty opcodes are what two empty sequences give, so the caller is told that there is nothing to do. `a` is not hashed until the matcher runs, so `SequenceMatcher(None, [[1], 2], [2, 3])` is built without complaint, the first `get_opcodes()` raises TypeError, and the second returns `[]`. Any exception does the same, including KeyboardInterrupt or a timeout raised by a signal handler during a long comparison. `ratio()` and `get_matching_blocks()` have no such problem: they assign their cache when they are done, and raise again on a second call.

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

#### 5. SequenceMatcher.get_grouped_opcodes overwrites the cached opcodes, so later calls give wrong results

`get_grouped_opcodes` does `codes = self.get_opcodes()`, which is the cached list, and then assigns to `codes[0]` and `codes[-1]` to trim the context. After that, `get_opcodes()` on the same matcher no longer starts at 0 or ends at the end of the sequences, and a second `get_grouped_opcodes` with a larger `n` gives less context than a fresh matcher does. With a = "abcdefghx" and b = "abcdefghy" as lists, `get_opcodes()` is `[('equal', 0, 8, 0, 8), ('replace', 8, 9, 8, 9)]` before a call of `get_grouped_opcodes(1)` and `[('equal', 7, 8, 7, 8), ('replace', 8, 9, 8, 9)]` after it.

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

#### 6. difflib.unified_diff formats non-str lines since the f-strings of color, the garbling _check_types exists to stop

`_check_types` looks only at `a[0]` and `b[0]`, and relies on the later `'-' + line` to raise for the rest. The `color` change replaced those concatenations in `unified_diff` with f-strings, which format any object. So `unified_diff(['a', b'x'], ['a', b'y'], lineterm='')` now yields `-b'x'` and `+b'y'`, and a line that is an int or None is formatted too. `context_diff`, which still concatenates, raises TypeError for the same arguments. 3.14 raises TypeError from `unified_diff` as well. The comment in `_check_types` names this outcome as what it is there to prevent: "the alternative is garbled output when someone passes mixed bytes and str".

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

#### 7. email: reading a header with a few hundred nested comments raises RecursionError (policy.default, HeaderRegistry)

`get_comment` (Lib/email/_header_value_parser.py:1287-1309) parses a nested comment by calling itself (:1300-1301), and `Comment.__str__` / `Comment.quote` (:290-299) and `Comment.content` recurse the same way over the result. Nothing bounds the nesting depth, so a header value with a few hundred `(` (well within any line-length limit a mail server enforces on a folded header) exhausts the Python stack. The RecursionError is not a `HeaderParseError`, so the parser's recovery paths do not catch it: it propagates out of `HeaderRegistry()(name, value)` and out of `msg['To']` on a message parsed with `policy.default`, where malformed input is otherwise reported as defects.

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

#### 8. copy.copy of a C Element shares its attrib dict with the original (and drops the subclass)

Element.__copy__ in C passes self->extra->attrib to create_new_element, which stores that same dict in the copy (create_extra). After c = copy.copy(e), c.set('z', '1') also gives e the attribute z, and c.attrib is e.attrib. The children are copied into a new array, so only the attributes are shared. The pure-Python Element copies through makeelement -> self.__class__(tag, attrib), whose __init__ builds a new dict, so the original is unaffected. The same call also makes an exact Element: copy.copy and copy.deepcopy of an Element subclass (and the subclass children a deepcopy recreates) come back as plain Element in C and keep their class in the twin.

*May be intended:* Possibly for the sharing (a shallow copy may share contained objects), but it is inconsistent: the C copy duplicates the children list and not the attrib dict, and the Python twin duplicates both. Dropping the subclass looks unintended; __deepcopy__ has the same create_new_element call.

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

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 and on main and the text checked before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
