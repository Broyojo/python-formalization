# Checks v2: deprecate `maxsplit=` (follow-up commit 5bc1249)

Run on the build pod on 2026-11-14, in `~/pf/patches/userstring-v2/cpython`. That is a
`--depth 30` clone of `Broyojo/cpython` branch `gh-161970-userstring-replace-count`,
and HEAD is `5bc1249` on top of `9d45abf`, with no rebase. The build is
`./configure --with-pydebug -q && make -j16 -s`, and it reports
`3.16.0a2+dev` with GCC 11.4.0.

## Test suite

`./python -m test test_userstring test_collections test_str test_bytes test_warnings -j16`

```
All 5 tests OK.
Total tests: run=886 skipped=23
Result: SUCCESS
```

- `./python -m test test_userstring -v -m 'test_replace*' -m test_count_keyword`
  lists the following as ok: `test_count_keyword`, `test_replace`,
  `test_replace_count`, `test_replace_maxsplit_deprecated`,
  `test_replace_uses_two_way_maxcount` and `test_replace_overflow`, which is
  skipped because it only runs on 32-bit platforms.
- `./python -W error::DeprecationWarning -m test test_userstring` gives SUCCESS,
  so no other test hits the deprecated path.
- Regression check: with `Lib/collections/__init__.py` reverted to the first commit,
  `test_replace*` FAILS. With the fix, it passes.

## Smoke test (`./python`)

```
inspect.signature(UserString.replace) -> (self, old, new, count=-1, *, maxsplit=MISSING)
help() header                         -> replace(self, old, new, count=-1, *, maxsplit=MISSING)
u = UserString('aaa')
u.replace('a','b') / (…, 2) / (…, count=1) -> 'bbb' 'bba' 'baa'
u.replace('a','b', maxsplit=1)        -> 'baa' + DeprecationWarning, attributed to the caller's file and line:
  the 'maxsplit' keyword parameter is deprecated since Python 3.16 and slated for removal
  in Python 3.18; use the 'count' keyword parameter or pass the count as a positional argument instead
u.replace('a','b', 1, maxsplit=2)     -> TypeError: 'count' and 'maxsplit' are mutually exclusive and
                                         support for 'maxsplit' keyword parameter is slated for removal in Python 3.18
u.replace('a','b', count=1, maxsplit=2) -> same TypeError
u.replace('a','b', -1, maxsplit=2)    -> 'bba' + DeprecationWarning  (known limitation, see below)
-W error::DeprecationWarning          -> maxsplit= raises DeprecationWarning
```

## patchcheck

`make patchcheck` (base `upstream/main`):

```
Docs modified ... yes
Misc/NEWS.d updated with `blurb` ... yes
configure regenerated ... not needed
pyconfig.h.in regenerated ... not needed
```

It made no whitespace complaints. The "31 files" count includes upstream commits,
because the clone is shallow.

## Docs

- `sphinx-lint` on `library/collections.rst`, `whatsnew/3.16.rst`,
  `deprecations/pending-removal-in-3.18.rst` and the NEWS entry reports "No problems found."
- `make html SPHINXOPTS="-j 32 -n"` uses the Doc venv on 3.15.2 with `LC_ALL=C.UTF-8`.
  It built, and the nitpicky warnings it printed (912 in the whole tree, with -n
  as errors) are pre-existing: none are in `collections.rst`,
  `whatsnew/3.16.rst` or `pending-removal-in-3.18.rst`. The rendered
  `library/collections.html` shows "Deprecated since version 3.16, will be removed
  in version 3.18". The new entries also appear in `whatsnew/3.16.html` and
  `deprecations/index.html`, with no include wiring needed because the 3.18 file
  is already included.

## Known limitation / likely review points

- `count=-1` is the visible default, so the code cannot tell an explicit
  `replace(o, n, -1, maxsplit=k)` from the default. In that case it uses `maxsplit`
  with the warning instead of raising `TypeError`. Detecting it would require a
  sentinel default for `count`, which `help()` would then show instead of `-1`.
- The warning and error messages copy hashlib's wording from gh-134978. hashlib
  calls `warnings.warn` with literal text. This commit instead uses
  `warnings._deprecated(remove=(3, 18))`, as `abc` and `tkinter.filedialog` do,
  so the deprecation fails loudly once 3.18 leaves alpha.
- The `maxsplit` parameter shows in `help()` as `maxsplit=MISSING`. hashlib's
  `string=` is also visible in its signatures.
- The What's New credit line reads "Contributed by Broyojo". Change it to the
  author's preferred name if needed.
