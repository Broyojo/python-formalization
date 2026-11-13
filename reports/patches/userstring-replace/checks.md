# Checks: UserString.replace count keyword

Bug record: `bugs/corelibs-userstring-replace-count-keyword.yaml`.

## Duplicate searches (2026-11-13)

`gh search issues` and `gh search prs`, `--repo python/cpython`, open and closed, words unquoted:

| query | issues | PRs |
|---|---|---|
| UserString replace count | unrelated only (98567, 84120, 70176, 57912, 45962, 46235) | 96356 (clinic docstrings), 13138 (bpo-36582, UserString.encode) |
| UserString replace maxsplit | none | none |
| UserString keyword count TypeError | none | none |
| collections UserString replace signature | none | 13138 |
| UserString maxsplit | 35956, 39195 (old split docs / rsplit) | 26222 (split keepempty) |
| UserString replace | unrelated (60601 is about mixing str and UserString in operators) | 160932, 96356, 112351, 10497, 13138 |
| UserString count keyword argument | unrelated | unrelated |

Related, not duplicates:
- gh-106487 / PR gh-106488 (3.13): made `str.replace` accept `count=`. That PR changed only `str` and added `test_count_keyword` with `str` literals, which is why the test never ran on `UserString`. None of its comments mention UserString.
- gh-147856 (3.15): the same change for `bytes.replace` / `bytearray.replace`. Closed; listed in What's New in 3.15.
- gh-150148 (open): `(str|bytes).(r)find` don't take kwargs. Different methods.
- bugforge-results README: no UserString entries (per the bug record).

Upstream main: `gh api repos/python/cpython/contents/Lib/collections/__init__.py` still has
`def replace(self, old, new, maxsplit=-1):` (line 1614). Commits on that path since 2026-09-01:
c3fe3c3b85 (gh-160929, ChainMap unions) and c99097ee97 (gh-159868, UserString startswith/endswith accept
UserString). Neither touches `replace`. **No duplicate and no existing fix found.**

## Compatibility

- After the plain rename, `UserString(...).replace(old, new, maxsplit=n)` raises `TypeError`. Positional
  calls are unaffected. `maxsplit` was never documented (the docs list no UserString method signatures and
  say it "simulates a string object"), and `str.replace` has never accepted `maxsplit`, so the only callers it
  breaks are ones that read the source. The name dates back to Python 2's `UserString.py`, so it is old.
- No caller found: `grep` over CPython 3.15 `Lib/` finds no `replace(..., maxsplit=` outside the definition.
  `gh search code UserString replace( maxsplit=` returns only vendored copies of `UserString.py` itself
  (code search is token-based, so this is weak evidence).
- If reviewers want a transition, precedent exists for keeping an old keyword name with a
  `DeprecationWarning`: hashlib `string=` (gh-134978, 3.15, removal 3.19), logging handler `strm=`
  (gh-115032, 3.14), `functools.reduce` keyword args (gh-121676, 3.14). A shim would look like
  `def replace(self, old, new, count=-1, **kwargs):` that pops `maxsplit`, calls
  `warnings._deprecated("maxsplit", ..., remove=(3, 17))`, and rejects other keywords. Given the name is
  undocumented and str rejects it, the plain rename seems the better default; the reviewer may ask for a shim
  if this is to be backported. Backport: the bug exists on 3.13+ (where str accepts `count=`); whether a
  rename counts as a bug fix for 3.13/3.14 is the maintainers' call.

## Build and tests (build pod, Linux x86_64, GCC 11.4)

Clone: `git clone --depth 50 https://github.com/python/cpython.git`, main at
2c2d8018a20da33c749f42cc6a4ae55664a88321 (2026-11-13). `./configure --with-pydebug -q && make -j16 -s`:
build OK, `Python 3.16.0a2+dev (heads/main:2c2d801)`.

Before the fix (main 2c2d801):
```
'baa'
TypeError UserString.replace() got an unexpected keyword argument 'count'
```
The bug record also has it reproduced on python3 3.15.2 and on main ef1fce0.

Old `test_count_keyword` passes on the unpatched code (it only exercised `str`). The new
`test_count_keyword` with the old `Lib/collections/__init__.py`:
`./python -m test test_userstring -m test_count_keyword` -> FAILURE (`TypeError: ... unexpected keyword argument 'count'`).

After the fix:
- reproducer prints `'baa'` twice; `U('aaa').replace(U('a'), U('b'), count=2)` -> `'bba'`; positional
  `replace('a', 'b', 1)` -> `'baa'`; `maxsplit=1` now raises `TypeError ... unexpected keyword argument 'maxsplit'`.
- `./python -m test test_userstring test_collections test_str test_bytes -j8` -> SUCCESS, all 4 test files
  OK, 681 tests run, 17 skipped. (`test_str` and `test_bytes` are included because the shared
  `string_tests.BaseTest.test_count_keyword` now runs for str, bytes and bytearray through `checkequal`.)
- `Tools/patchcheck/patchcheck.py`: no whitespace issues. The NEWS entry was untracked at that point, so
  patchcheck did not see it.

NEWS: `Misc/NEWS.d/next/Library/2026-11-13-00-00-00.gh-issue-XXXXXX.Kq3vRw.rst`. Replace `XXXXXX` with the
issue number in the file name and the PR title. It uses `:meth:` with `!` for `UserString.replace`, which has
no doc target, to avoid a Sphinx nitpick warning.

The pod clone (`~/pf/patches/userstring-replace`) was deleted afterwards; no processes were left running.
