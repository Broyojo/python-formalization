# First batch of CPython fixes

Each folder is one issue plus its PR: `fix.diff` (fix, regression test, NEWS entry), `issue.md`, `pr.md`, and `checks.md` (duplicate searches and test runs). All were built and tested against CPython main (2c2d8018a2, 2026-11-13) with a `--with-pydebug` build; each new test fails before the fix and passes after.

| Folder | Bug | Fix |
|---|---|---|
| `email-msgid` | `<a@[ x]>` in Message-ID raises UnboundLocalError | guard in `_get_ptext_to_endchars` covers input starting with whitespace |
| `inplace-mul` | `x *= [1]` fails for int subclasses / IntEnum | `else if` -> `if` in `PyNumber_InPlaceMultiply` |
| `userstring-replace` | `UserString.replace(count=...)` rejected | rename `maxsplit` to `count` |
| `cmath-log` | `cmath.log(0, base)` returns `(-inf+nanj)` | keep the errno from the first `c_log` |
| `difflib-grouped` | `get_grouped_opcodes()` corrupts the cached opcodes | work on a copy of the list |

## Filing, per fix

1. Sign the PSF CLA (https://cla.python.org) once, before the first PR.
2. Re-run the duplicate search in `checks.md` on the day of filing.
3. Open the issue from `issue.md` (title from its first line); note the number NNNNNN.
4. In a branch of your CPython fork, apply `fix.diff`, rename the NEWS file's `gh-issue-XXXXXX` to the issue number (re-run `blurb` if preferred), and replace `XXXXXX` in the PR title.
5. Open the PR from `pr.md`. Don't force-push after review starts.
