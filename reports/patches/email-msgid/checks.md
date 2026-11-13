# Checks for the email Message-ID UnboundLocalError patch

Bug record: bugs/textlibs-email-msgid-no-fold-literal-space.yaml

## Duplicate searches (2026-11-13)

All searches ran against python/cpython with `gh search issues` and `gh search prs`, unquoted words, open and closed.

| Query | Issues | PRs |
|---|---|---|
| Message-ID UnboundLocalError | gh-134152, gh-82879, gh-82889, gh-83300 (all closed, older or empty-literal cases) | gh-17277/17476 (bpo-38698, merged 2019), gh-13397, gh-134194: unrelated |
| _get_ptext_to_endchars | gh-134152 (closed) | gh-134233 + backports gh-134677/134678 (the empty-literal fix, merged) |
| get_no_fold_literal | gh-134152, gh-90593 (closed IndexError, different) | gh-13397 (the original parser) |
| email header parser UnboundLocalError pos | gh-134152 | none |
| domain literal whitespace msg-id | gh-134082 (unrelated) | none |
| no-fold-literal email | gh-134152, gh-90593, unrelated others | unrelated |
| UnboundLocalError email | gh-134759 (get_payload, other function), gh-134152, gh-82879, gh-89402: none for this input | fixes for gh-134759 and gh-134152 only |
| msg-id UnboundLocalError | gh-134152, gh-82879, gh-82889 | none relevant |
| parse_message_id | gh-136063 (open, quadratic complexity), gh-105802, gh-86650, gh-90593, gh-94306: all different | gh-134194, gh-17277: different |
| get_dtext | gh-134152 | none |
| email _header_value_parser UnboundLocalError | gh-134152, gh-82879 | gh-134233 and backports |
| References header UnboundLocalError | none | unrelated |
| message id domain literal space / Message-ID domain literal | unrelated | gh-134194: unrelated |
| _header_value_parser msg-id whitespace | gh-79986 (folding, different) | none |
| open PRs `_header_value_parser` | n/a | gh-138231 (folding loop, unrelated), gh-152710 (open WIP refactor for gh-136063) |

gh-152710 marks `_get_ptext_to_endchars` deprecated but leaves the loop and the `if not value` guard unchanged, so it does not fix this. It touches the same lines, so whichever PR merges second needs a rebase.

gh-151857 (open) covers three IndexError cases in this module (MIME parameters and display names), not this input.

Upstream main: `Lib/email/_header_value_parser.py` at main still has only the `if not value` guard. Commits to the file since 2026-10-01: 5a22a62b96 (gh-87720, refolding), which is unrelated.

Result: no duplicate and no upstream fix found.

## Build and tests

Built on Linux (GCC 11.4.0), shallow clone of main at 2c2d8018a20da33c749f42cc6a4ae55664a88321 (3.16.0a2+dev), `./configure --with-pydebug -q && make -j16 -s`.

- Reproducer from the bug record on unpatched main: `REPRODUCED` (UnboundLocalError from parse_message_id, parse_message_ids and `msg['Message-ID']`).
- Reproducer with the patch: `[None, None] None`, so it no longer reproduces.
- New tests (`test_get_dtext_leading_wsp`, `test_parse_message_id_with_wsp_in_literal`) without the library change: both ERROR with UnboundLocalError. With it: both pass.
- `./python -m unittest test.test_email.test__header_value_parser`: 391 tests, OK.
- `./python -m test test_email -j8`: 1825 run, 2 failures, `test_formatdate` and `test_formatdate_with_localtime` in test_utils. Unpatched main fails the same 2 tests in that environment (1823 run), because the build machine has no `/usr/share/zoneinfo`. They do not involve this change.
- `./python -m test test_email -j8 -i test_formatdate -i test_formatdate_with_localtime`: 1822 run, SUCCESS.
- `make patchcheck`: ran in the shallow clone and reported 3 changed files, the NEWS entry present, and no problems.

Behaviour after the patch (parse_message_id and parse_message_ids give the same token and defects):

| Input | Result |
|---|---|
| `<T@[ x]>` | message-id `<T@[ x]>`, ObsoleteHeaderDefect "obsolete id-right in msg-id" |
| `<T@[x ]>` (already worked) | same shape as above |
| `<T@[ ]>` | message-id `<T@[ ]>`, ObsoleteHeaderDefect |
| `<T@[ ` / `<T@[\t` | message-id `<T@[ ]>`, ObsoleteHeaderDefect plus two InvalidHeaderDefects (missing `>`, end of input inside domain-literal), same as the gh-134152 case |

## Notes for the reviewer

- The fix moves the gh-134152 guard below the split and tests `not fragment`. `_wsp_splitter('', 1)` is `['']`, so the empty-value case still returns `('', '', False)`. The only other behaviour change is for input that starts with whitespace, which used to raise.
- `get_no_fold_literal` is unchanged. RFC 5322 no-fold-literal has no FWS, so rejecting `[ x]` there and falling back to obs-id-right (through `get_domain_literal`, which allows FWS) is the right path.
- Issue number placeholder: replace `XXXXXX` in the NEWS filename and the PR title once the issue exists.
