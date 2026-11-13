# Checks for the cmath.log(0, base) fix

Bug record: `bugs/mathint-cmath-log-base-errno.yaml`. Checked 2026-11-13.

## Duplicate search (python/cpython, issues and PRs, open and closed)

`gh search issues --repo python/cpython --include-prs -- <words>` (unquoted words):

| Query | Result |
|---|---|
| cmath log 0 base | no match (hits: #89381 signature, #153148 atan2 errno, #60200 complex pow, unrelated build issues) |
| cmath.log zero base ValueError | #47418 (Solaris cmath test failure, 2008), unrelated |
| cmath log errno second argument | #153148, #155527 (abs errno), unrelated |
| cmath_log_impl errno | #156145 (feature: stop relying on platform errno), #154034 (rect converter), unrelated |
| cmath log(0, 10) | invalid query syntax (parentheses); covered by the others |
| cmath log base errno | no match |
| cmath log domain error base | no match (#124299/#101492 math error messages) |
| cmath log inf nanj | #66734 (bpo-22544), see below; #69639, #76352 unrelated |
| cmath log two arguments zero | no match |
| cmath c_log errno | #156145, #154034, unrelated |
| cmath errno | #133895, #153144/#153148, #156145, #156968, #155527; none touches log(0, base) |
| cmath log base | no match |

Closest related, not a duplicate:
- #66734 (bpo-22544, "Inconsistent cmath.log behaviour", closed won't fix 2016): `cmath.log(complex(-0.0, -inf), 10)` gives `(inf+nanj)` while `log10` gives a finite imaginary part. That is about infinities in complex division, not a lost domain error. Mark Dickinson closed it saying two-argument log is "a rather unnatural beast" and infinities/nans there are unlikely to matter; worth knowing for the reviewer, but log(0, base) disagrees with log(0) itself, which is a plain error-handling bug.
- #156145 (open): proposes not relying on libm errno. This fix only uses errno that `c_log()` itself sets, so it does not conflict.
- #153148 (open PR, gh-153144): edits `cmath_phase_impl`, not `cmath_log_impl`; no textual overlap.
- #156968 (open PR, gh-156695): rewrites `_Py_c_quot`; keeps "EDOM on zero divisor, errno otherwise unchanged", which is what this fix relies on.

Upstream source: `gh api repos/python/cpython/contents/Modules/cmathmodule.c` (main at 2c2d8018a2, 2026-11-13): `cmath_log_impl` unchanged, bug present. Commits on that path since 2026-09-01: only e5d4fa281c (gh-155526, `abs()`/`polar()` errno), unrelated. 3.15 (`vendor/cpython-3.15`) has the same code. `vendor/bugforge-results`: not listed (per the bug record).

## Expected behaviour, for consistency

On unpatched main (debug build, 2c2d801):

| Call | cmath | math |
|---|---|---|
| log(0) | ValueError: math domain error | ValueError: expected a positive input |
| log(0, 2), log(0, 10), log(-0.0, 2) | (-inf+nanj) | ValueError: expected a positive input |
| log(0, -1), log(0, 1j) | (nan+infj) | ValueError (-1) |
| log(0, inf), log(0, nan) | (nan+nanj) | ValueError |
| log(0, 1e-320) | (inf+nanj) | ValueError |
| log(0, 0), log(0, 1), log(2, 0), log(2, 1) | ValueError: math domain error | ValueError / ZeroDivisionError |

After the fix every log(0, base) row raises `ValueError: math domain error`; the other rows and valid inputs (log(2, 10), log(-1, 10), log(1e-320, 2), log(5e-324, 0.5)) are unchanged.

## Edge cases considered

- Which error wins: `c_log()` only sets errno to 0 or EDOM, and `_Py_c_quot()` only sets EDOM (zero divisor) or leaves errno alone, so every possible error is EDOM. The patch keeps an error from the base or the division if there is one, else restores the error from log(z).
- Base 0: `c_log(0)` sets EDOM; still raises. Base 1: `c_log(1) == 0`, division by zero sets EDOM; still raises. Complex zero `0j`, `-0.0`, `complex(-0.0, -0.0)`: all raise with any base.
- Invalid base type (`cmath.log(0, 'spam')`): TypeError from `PyComplex_AsCComplex` still wins; the saved errno is not consulted before conversion. Saving errno before the conversion also means a `__complex__` method that touches errno cannot affect the result.
- Special bases (inf, nan) go through `SPECIAL_VALUE`, which sets errno to 0; the saved EDOM is restored, so they raise too.

## Tests (build pod, `./configure --with-pydebug -q && make -j16 -s`, main 2c2d801)

- Reproducer from the bug record, unpatched: `log(0, 2): (-inf+nanj)`, prints `REPRODUCED mathint-cmath-log-base-errno`. Patched: `log(0, 2): ValueError: math domain error`, not reproduced.
- New test before the C change: `./python -m test test_cmath -m test_log_base_domain_error` -> FAILURE (45 subtest failures).
- After: `./python -m test test_cmath test_math -j8` -> SUCCESS, 123 tests, 3 skipped.
- `./python -m test test_cmath -R 3:3` -> SUCCESS (no refleaks).
- `./python -m test test_complex` -> SUCCESS.
- `git diff --check` clean; `fix.diff` applies cleanly (`git apply --check`) to upstream main files at 2c2d8018a2.
- Pod clone removed afterwards.
