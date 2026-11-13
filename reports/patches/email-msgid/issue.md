<!-- title: email: UnboundLocalError parsing a Message-ID whose domain literal starts with whitespace -->
### Bug report

`email._header_value_parser.parse_message_id` and `parse_message_ids` raise `UnboundLocalError` when the part after `@` is a domain literal that starts with a space or tab, such as `<a@[ x]>`. Because of this, reading `Message-ID`, `References` or `In-Reply-To` from such a message with `policy.default` raises instead of returning a header with a defect. gh-134152 fixed the same error for an empty literal (`<T@[`), but a literal that begins with whitespace still reaches the same code.

```python
import email
from email import policy
from email._header_value_parser import parse_message_id

parse_message_id('<a@[ x]>')

msg = email.message_from_string('Message-ID: <a@[ x]>\n\nbody\n', policy=policy.default)
msg['Message-ID']
```

Actual:

```
UnboundLocalError: cannot access local variable 'pos' where it is not associated with a value
```

Expected: no exception. The header should parse with a defect, the same way `<a@[x ]>` already does (it gives a `MessageID` with an `ObsoleteHeaderDefect`, "obsolete id-right in msg-id").

The cause is in `_get_ptext_to_endchars`: when `value` starts with whitespace, the first fragment from `_wsp_splitter` is empty, the `for pos in ...` loop never runs, and the `else` clause reads `pos` before it is assigned.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux

---
AI tools (Claude) helped find this and prepare the fix; I reviewed and tested it.
