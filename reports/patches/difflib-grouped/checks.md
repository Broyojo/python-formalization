# Checks for the difflib get_grouped_opcodes fix

Date: 2026-11-13. Bug record: `bugs/textlibs-difflib-grouped-opcodes-mutates-cache.yaml`.

## Duplicate search (python/cpython, issues and PRs, open and closed, unquoted words)

| Query | Issues | PRs |
|---|---|---|
| get_grouped_opcodes mutates | #54194 (closed) | none |
| get_grouped_opcodes cache | #54194 (closed) | none |
| SequenceMatcher get_opcodes modified | #71896, #47235 (closed, unrelated) | none |
| difflib opcodes changed after get_grouped_opcodes | #150184 (closed not planned, C accelerator, unrelated) | none |
| difflib grouped opcodes side effect | none | #144208 (unrelated) |
| get_grouped_opcodes | #84868, #150184, #40453, #40461, #54194, #55956 (all closed) | #156227, #153959 (merged, unrelated) |
| difflib get_opcodes cached | #54194 (closed) | #106877 (closed, find_longest_match cache, unrelated) |
| difflib opcodes mutated | #150184, #134082 (unrelated) | none |
| SequenceMatcher caching | #138669, #54194, #65834 (closed) | #27434 (unrelated) |

Also viewed: `gh issue view 54194 --comments`, `gh issue view 150184 --comments`.

**Prior report:** gh-54194 ("difflib.SequenceMatcher has slightly buggy and undocumented
caching behavior", 2010) describes this exact problem in its second half ("get_grouped_opcodes
mutates the result of get_opcodes (a cached list)"). It was closed as completed in 2019 with a
pointer to bpo-21635 / gh-65834, which only fixed `get_matching_blocks()`. The
`get_grouped_opcodes()` mutation was never fixed. No open issue or PR covers it. The issue text
links gh-54194; a human may prefer to ask for it to be reopened instead of filing a new one.

## Upstream main

- `gh api repos/python/cpython/contents/Lib/difflib.py`: line 573 is still
  `codes = self.get_opcodes()`, followed by the assignments to `codes[0]` and `codes[-1]`.
- Commits on `Lib/difflib.py` since 2026-09-01: 1f25c333a2 (gh-156505, HtmlDiff speedup) and
  bc977f450b (gh-118150, autojunk flag). Neither touches this.

## Build and tests

On the build pod, clone of python/cpython main at 2c2d8018a20da33c749f42cc6a4ae55664a88321
(2026-11-13), `./configure --with-pydebug -q && make -j16 -s` (3.16.0a2+dev).

- Before the fix: the bug record's reproducer prints `REPRODUCED
  textlibs-difflib-grouped-opcodes-mutates-cache`; the issue example prints
  `[('equal', 4, 5, 4, 5), ('replace', 5, 6, 5, 6), ('equal', 6, 7, 6, 7)]`.
- New test without the fix (fix reverted, test kept):
  `./python -m test test_difflib -m test_grouped_opcodes_keep_cached_opcodes` fails (1 failure).
- With the fix: `./python -m test test_difflib -j8`: Result SUCCESS, run=68 (doctests included).
- With the fix: reproducer prints `NOT REPRODUCED`; the issue example prints
  `[('equal', 0, 5, 0, 5), ('replace', 5, 6, 5, 6), ('equal', 6, 10, 6, 10)]`.
- `git diff --cached --check`: clean.

## Notes on the fix

`get_grouped_opcodes()` only assigns new tuples to `codes[0]` and `codes[-1]` and reads the
rest, so `list(self.get_opcodes())` (a shallow copy) is enough. Copying in `get_opcodes()`
instead would break `test_opcode_caching`, which checks that `get_opcodes()` returns the same
object each time.
