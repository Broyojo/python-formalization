<!-- title: email: Message-ID '<a@[ x]>' raises UnboundLocalError -->
# Bug report

### Bug description

`_get_ptext_to_endchars` splits off the text before the first space or tab and loops over it with `for pos in range(len(fragment)): ... else: pos = pos + 1`. When the value starts with a space or tab the fragment is empty, the loop body never runs, and the `else` clause reads the unbound `pos`: `UnboundLocalError: cannot access local variable 'pos' where it is not associated with a value`. gh-134152 reported the same error for an empty value (`<T@[`) and was fixed by an early return for `not value`; a value that starts with whitespace still reaches the loop.

```python
import email
from email import policy, _header_value_parser as P
results = []
for f in (P.parse_message_id, P.parse_message_ids):
    try:
        f('<a@[ x]>')
        results.append(None)
    except UnboundLocalError as e:
        results.append(str(e))
m = email.message_from_string('Message-ID: <a@[ x]>\n\nbody\n', policy=policy.default)
try:
    m['Message-ID']
    hdr = None
except UnboundLocalError as e:
    hdr = str(e)
print(results, hdr)
```

**Expected:** A MessageID token list (or an InvalidMessageID with an InvalidHeaderDefect), as for any other malformed id.

**Actual:** python3 3.15.2: UnboundLocalError from parse_message_id, parse_message_ids and msg['Message-ID']. main 3.16.0a1+dev (ef1fce0): the same.

**Cause:** Lib/email/_header_value_parser.py:1045-1066: the `if not value` guard added for gh-134152 does not cover a value whose first character is in WSP, for which `fragment` (line 1047) is empty and line 1065 reads `pos` unbound. get_no_fold_literal (:2100) calls get_dtext right after the `[`, without the WSP check that get_domain_literal has (:1626-1628).

**Possible fix:** Initialise `pos = 0` before the loop in _get_ptext_to_endchars (then an empty fragment returns ('', value, False)), or have get_no_fold_literal raise HeaderParseError when the text after `[` starts with whitespace (RFC 5322 no-fold-literal has no FWS).

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/textlibs-email-msgid-no-fold-literal-space.yaml
