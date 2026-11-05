<!-- title: email: UnboundLocalError when a Message-ID's [domain literal] starts with a space -->
### Bug report

gh-134152 fixed an `UnboundLocalError` in `_get_ptext_to_endchars` for an empty value. A value that starts with a space or tab still reaches the same code: the text before the first whitespace is empty, the loop body never runs, and the `else` clause reads the unbound `pos`. `get_no_fold_literal` (the `[...]` part of a msg-id) calls it right after the `[` without skipping whitespace, as `get_domain_literal` does.

```python
import email
from email import policy, _header_value_parser as P

P.parse_message_id('<a@[ x]>')    # UnboundLocalError: cannot access local variable 'pos' ...

m = email.message_from_string('Message-ID: <a@[ x]>\n\nbody\n', policy=policy.default)
m['Message-ID']                   # the same error
```

I'd expect the header to parse with a defect recorded, as other malformed msg-ids do, rather than an `UnboundLocalError` from inside the parser.

Cause: Lib/email/_header_value_parser.py:1045-1066. The `if not value` guard does not cover a value whose first character is whitespace, for which `fragment` (:1047) is empty and :1065 reads `pos` unbound. `get_no_fold_literal` (:2100) has no whitespace check before `get_dtext`, unlike `get_domain_literal` (:1626-1628).

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). AI tools (Claude and Codex) helped investigate the findings and prepare these drafts. Results in the body are taken from the bug records; final interpreter reruns and human review are pending. Record: [textlibs-email-msgid-no-fold-literal-space](https://github.com/Broyojo/python-formalization/blob/main/bugs/textlibs-email-msgid-no-fold-literal-space.yaml)
