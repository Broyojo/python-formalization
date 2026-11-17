# Checks for the binascii.b2a_qp line-length fix

Date: 2026-11-17 (extended the same day with the quopri and binary-mode fixes). Bug record: `bugs/textlibs-binascii-qp-line-length.yaml`.

## Duplicate search (python/cpython, issues and PRs, open and closed, unquoted words)

`gh search issues --repo python/cpython --include-prs <words>`:

| Query | Results |
|---|---|
| b2a_qp line length | #64320 (open, quopri_codec newline handling) |
| b2a_qp 76 | #76 (PR, copyright years), #64320 |
| quoted printable line too long | #62222, #64946, #134082, #49680, #121515, #88088, #49020, #49019, #32682, #47550 (none about encoder line length) |
| b2a_qp trailing whitespace | none |
| quopri line length binascii | #64320, #64331, #134082; PRs #102753, #143216, #95253 (unrelated) |
| b2a_qp MAXLINESIZE | none |
| quopri trailing space soft line break | #62222, #134082 |
| b2a_qp soft line break | #64320 |
| quopri encodestring long line | #43702, #55365, #49019 (unrelated) |
| quoted printable 76 characters | #76, #78206, #78981, #64320, #64946, #134082, #49680, #121515, #116051, #49018 |
| b2a_qp | #64320, #41875, #34489, #64350, #54205, #39420, #35183 |

Read in full: #64320 (open since 2014). It is about newline handling (CR/LF conversion);
martin.panter's v2 patch there mentions a different line-break issue (binascii breaking a
76-character line too early when it would end in an escape). Not this bug. #78206 is the email
policy's max_line_length (78 vs 76), not b2a_qp. #41875 (2005) is about control characters.

Bugforge: `quopri-20261003-074352-c3` (not filed) is the pure-Python fallback quoting a space
before a soft line break; a different code path. #158740/#158739 (closed) are the pure-Python
encoder splitting escapes.

No duplicate found.

## Upstream main

- `gh api 'repos/python/cpython/commits?path=Modules/binascii.c&since=2026-09-01'`: only
  ab5187ce84 (gh-62222, quoted-printable decoding). It does not touch `b2a_qp`.
- Commits on `Lib/quopri.py` since 2026-01-01: only ab5187ce84 (decoding; `encode()` unchanged).
- `binascii_b2a_qp_impl` on main is identical to 3.15.2's, and so is `quopri.encode()`.

## Reproduction

Issue example (`binascii.b2a_qp` line lengths, then `quopri.encodestring`'s):

| Build | `a*75 + ' \n'` | `a*74 + '\t\n'` | `a*74 + ' \r\n'` |
|---|---|---|---|
| v3.15.2 (built on the pod, first round) | [78] [78] | [77] [77] | [77] [77] |
| main, unpatched | [78] [78] | [77] [77] | [77] [77] |
| main, patched | [76, 3] [76, 3] | [75, 3] [75, 3] | [75, 3] [75, 3] |

Pure-Python encoder (`quopri.b2a_qp = None`), and the binary-mode case:

| Build | `a*75 + ' \n'` | `a*74 + '\t\n'` | `a*75 + ' '` | `b2a_qp(a*76 + '\n', istext=False)` |
|---|---|---|---|---|
| 3.15.2 `Lib/quopri.py` | [78] | [77] | [78] | not run (C body identical to main) |
| main, unpatched | [78] | [77] | [78] | [77, 3] |
| main, patched | [76, 3] | [75, 3] | [76, 3] | [76, 4] |

The record's reproducer prints `REPRODUCED textlibs-binascii-qp-line-length` on 3.15.2 and
unpatched main, and nothing on the patched build.

## Build and tests

Pod `cpybatch`, clone of python/cpython main at 3ad9316217ba4e2788abc7d19f469762c6c38309
(2026-11-17), `./configure --with-pydebug -q && make -j4 -s`, plus an unpatched worktree of the
same commit built the same way. No compiler warnings.

- New tests on the unpatched tree: `test_b2a_qp_whitespace_before_line_break` and
  `test_b2a_qp_binary_line_length` fail in all 4 type variants (bytes, bytearray, memoryview,
  array); `test_quopri.test_encode_whitespace_before_line_break` fails (9 tests, 15 failures).
- With the C fix but the old `Lib/quopri.py`, the new test_quopri test still fails (9 subtest
  failures, from the pure-Python pass), so the quopri change is needed.
- With the full fix: all 9 new tests pass.
- `./python -m test test_binascii test_quopri test_codecs test_email -j4`: test_binascii,
  test_quopri and test_codecs pass; test_email has 2 failures, `test_formatdate` and
  `test_formatdate_with_localtime`. The pod has no `/usr/share/zoneinfo`, and unpatched main gives
  the same 2 failures.
- test_quopri runs its tests with both the binascii and the pure-Python encoder
  (`withpythonimplementation`); all pass.
- `./python -m test test_binascii test_quopri -R 3:3`: SUCCESS (run=259). Hypothesis is not
  installed on the pod, so the hypothesis round-trip tests were skipped.
- `make patchcheck` (after `git remote add upstream` and `git fetch -q --depth 50 upstream main`):
  5 files, NEWS entry found, nothing to fix. `git diff --cached --check`: clean.

## Random-input comparison

3 seeds x 40,000 inputs over {a, space, tab, LF, CRLF, CR, =, 0xFF, ., _, NUL} (all flag
combinations), and 3 seeds x 40,000 over {a, space, tab, LF} (istext, no quotetabs, random
header). Patched main against the unpatched worktree; per seed:

| | full alphabet | whitespace alphabet |
|---|---|---|
| `b2a_qp` outputs changed | 169, 164, 156 | 40, 31, 40 |
| ... of which old output had no line over 76 | 0 | 0 |
| `b2a_qp` outputs with a line over 76, after | 0 | 0 |
| `a2b_qp` of old and new `b2a_qp` output differ | 0 | 0 |
| pure-Python outputs changed | 60, 50, 56 | 184, 156, 155 |
| ... of which old output had no line over 76 | 0 | 0 |
| pure-Python decode of old and new differs | 0 | 0 |
| pure-Python outputs over 76: before -> after | 113->53, 90->40, 97->41 | 254->70, 237->81, 232->77 |
| C and Python agree: before -> after (of ~32,000 / 40,000 text cases) | 13407->13452, 13388->13426, 13371->13410 | 38704->38848, 38659->38784, 38727->38842 |
| agreed before, differ after | 0 | 0 |

The C and Python encoders do not agree on all inputs, before or after. Classifying the remaining
differences (one more seed, 40,000 each):

| Cause (all present before this change) | full | whitespace |
|---|---|---|
| Python encodes `\r` as `=0D` (C keeps CRLF and lone CR) | 18,471 | - |
| Python splits an `=XX` escape across a soft line break (gh-158740, closed in a bulk cleanup) | 187 | 0 |
| header mode, space at end of data: C `=20`, Python `_` | 132 | 1,028 |
| Python encodes whitespace right before a soft line break (bugforge quopri c3; up to 78 chars) | 15 | 68 |
| C breaks one column early when a line ends with an escape (Python allows 76) | 102 | 57 |

The remaining pure-Python lines over 76 are all from the "whitespace right before a soft line
break" case (e.g. `b'a'*74 + b' bb'` gives [78, 2]) or from `\r` handling. Not changed here.
