# Checks for the array('w').fromunicode('') SystemError patch

Bug record: bugs/sequences-array-w-fromunicode-empty.yaml

## Duplicate searches (2026-11-17)

All searches ran against python/cpython through the search API (`gh api search/issues -f q="<words> repo:python/cpython"`), unquoted words, issues and PRs, open and closed. A first pass with `gh search issues` sent each query as a quoted phrase and was then rate-limited, so it was redone this way.

| Query | Results (issues and PRs) |
|---|---|
| fromunicode | 65 hits. Relevant to this code: gh-154759 (open PR, remove Py_UNICODE), gh-128942 (open issue, array not free-thread safe), gh-161787 and gh-130771 (open PRs for gh-128942), gh-128943 (closed PR). The rest are older Py_UNICODE / legacy API issues. None report this bug. |
| array fromunicode empty | gh-154759, gh-130771 (open PRs), gh-45962 (unrelated) |
| array w fromunicode | gh-128942, gh-154759, gh-71446, gh-112437, gh-53236, gh-43063, gh-45962: none about an empty string |
| array('w') fromunicode | gh-128942, gh-112437 |
| fromunicode empty string | gh-72584, gh-154759, gh-130771, gh-47330, gh-45962 |
| arraymodule fromunicode empty string | gh-130771 |
| fromunicode SystemError | gh-45962 (unrelated) |
| PyUnicode_AsUCS4 array | gh-119609 (unrelated, PEP 756) |
| array exception set fromunicode | gh-130771, gh-45962 |
| array typecode w empty string | gh-134082, gh-45599 (unrelated) |

Open PRs that touch `array_array_fromunicode_impl`, checked with `gh pr diff`:

- gh-161787 (nascheme, open, updated 2026-11-11, free-threading rewrite of array): its rewrite of this function adds `if (ustr_length == 0) { Py_RETURN_NONE; }` before `array_reserve()`. That would fix this bug as a side effect, but the PR does not mention it, has no test for it, and is a large change unlikely to be backported. Whichever merges second has a small conflict.
- gh-130771 (open, last updated 2026-07-14, superseded by gh-161787): changes the 'w' branch's types but keeps the unguarded `PyUnicode_AsUCS4()` call.
- gh-154759 (open): no change to the `PyUnicode_AsUCS4` call.

Upstream commits to Modules/arraymodule.c since 2026-09-01 (`gh api repos/python/cpython/commits?path=Modules/arraymodule.c&since=2026-09-01`):
- ab01d18474 gh-142083: document the 'w' type code in the docstring
- c0bc6fad25 gh-156865: overflow detection for "e", "f", "Zf"

Neither touches fromunicode. Main at 715d34fc38 still has the unguarded call.

Result: no duplicate issue and no merged fix. gh-161787 would fix it incidentally (see above).

## Build and tests (main)

Built on Linux (GCC 11.4.0), shallow clone of main at 715d34fc38f84bbccf9feaf937477290e575b060 (3.16.0a2+dev), `./configure --with-pydebug -q && make -j4 -s`.

- Unpatched main: `array.array('w').fromunicode('')` aborts with `Modules/arraymodule.c:1989: array_array_fromunicode_impl: Assertion 'u != NULL' failed.` The same happens for `array('w', [])` and for `array('w', 'x' * 100)` after `del a[:]` (shrinking by 16 or more items to zero frees the buffer). `array('w', 'x').fromunicode('')` works.
- New test `test_fromunicode_empty` with the test change only (C change reverted, rebuilt): the test run aborts on the same assertion.
- With the patch: `array('w')`, `array('w', 'x')` and the `del a[:]` case all accept `''`, and a later non-empty call still appends. `fromunicode('')` while a memoryview is exported still succeeds.
- `./python -m test test_array -j4`: 1040 tests, SUCCESS.
- `./python -m test test_array -R 3:3`: SUCCESS, no leaks reported.
- `make patchcheck` (after `git remote add upstream`, `git fetch -q --depth 50 upstream main`, and staging the new NEWS file so it is seen): 3 files changed, "Misc/NEWS.d updated with `blurb` ... yes", no whitespace problems.

## 3.15 backport check

Main has no `'u'` type code, so the 'u' half was checked on the 3.15 branch: shallow clone of `3.15` at 094f7fe8c1 (3.15.2+dev), debug build, the same test added to `UnicodeTest` (3.15 has `test_issue17223` after `test_unicode`, so only the anchor differs), and the same five-line early return added to the `else` ('w') branch.

- Test only, C unpatched: `UCS4Test.test_fromunicode_empty` ('w') aborts at `Modules/arraymodule.c:2040: Assertion 'u != NULL' failed`. The 'u' body passes, because the 'u' branch already has `if (ustr_length > 1)`.
- With the C change: `UnicodeTest.test_fromunicode_empty` ('u') ok, `UCS4Test.test_fromunicode_empty` ('w') ok.
- `./python -m test test_array -j4`: 1100 tests, SUCCESS. `-R 3:3`: SUCCESS.

The fix applies to 3.15 with the hunk reindented by four spaces (it sits inside the `else` block); the backport bot or a manual backport will need that.

## Notes for the reviewer

- The "Actual" output in issue.md for a 3.15.2 release build comes from the bug record (the reproducer printed `REPRODUCED` on 3.15.2 and on main ef1fce0 in the project's run). Line 2558 of Objects/unicodeobject.c in v3.15.2 is the `PyErr_BadInternalCall()` in `PyUnicode_AsUCS4`. The debug-build assertion on main was observed directly here. The `File "<string>", line 4` frame in the issue was not copied from a run; rerun the snippet before filing and paste the real traceback.
- The bug record notes that in a specialized call the result check can be skipped, so the pending exception surfaced at a later unrelated call in the project's difftest. That was not reproduced here and is not claimed in the issue.
- 3.14 has the identical 'w' branch (Modules/arraymodule.c:1895-1911 in 3.14.7), so the fix applies there too.
