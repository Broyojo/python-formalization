# Checks for the zoneinfo truncated/malformed TZif fix

Bug record: `bugs/datetime-zoneinfo-load-data-not-valueerror.yaml`. Checked 2026-11-17.

## Which code path

Both implementations use `zoneinfo._common.load_data()`: C `Modules/_zoneinfo.c` calls it via `PyObject_CallMethod(state->_common_mod, "load_data", ...)` (3.15 line 986), and pure Python `Lib/zoneinfo/_zoneinfo.py:231` calls `_common.load_data(...)`. The C module does no TZif byte parsing of its own, so the fix is Python-only and covers both. The tests run on `WeirdZoneTest` and `CWeirdZoneTest`.

## Duplicate search (python/cpython, issues and PRs, open and closed)

`gh search issues --repo python/cpython --include-prs -- <words>` (unquoted words). A first pass ran the words as an exact phrase by mistake and hit the search rate limit; it was redone with the words split.

| Query | Result |
|---|---|
| zoneinfo from_file struct.error | no match |
| zoneinfo truncated tzif | #143241 / PR #143243 (+ backports #143251, #143252): infinite loop on truncated footer, fixed. Related, see below |
| zoneinfo load_data ValueError | #161097 (gh-161096 charcnt), #143241/#143243, #88992 (Windows device names), none a duplicate |
| zoneinfo AssertionError tzif | no match |
| ZoneInfo invalid file error | unrelated (#96463 long key OSError, #85702 IsADirectoryError, #138432 reset_tzpath, ...) |
| zoneinfo struct error | unrelated (#146102/#146103 umbrella issues, #111306, #142782, ...) |
| zoneinfo assert newline footer | no match |
| zoneinfo unexpected end of file | #161563 (overlong key OSError), #143241, unrelated |
| zoneinfo malformed tzif | #161096, #152847, #145883 / PR #145885 (C heap overflows), #143243, #86826: none about the exception type |
| zoneinfo corrupt file | #146102, #145885, unrelated |
| tzif ValueError | #161096, #160420, #152212, #152248, #152847, #143241, #88992, #85702: none a duplicate |
| zoneinfo assert | #111306, #142782, #146092 (missing PyErr_NoMemory), unrelated |
| ZoneInfo from_file invalid | #152248/#152249, #143243, unrelated |
| _common load_data struct | no match |
| zoneinfo negative count | #161096 only |
| tzif header truncated | #143241 only |
| zoneinfo OSError seek | #96463, unrelated |

Umbrella issues #146102 and #146103 (cpython-review-toolkit) list only `_zoneinfo` C findings (get_weak_cache SEGV #146076, missing PyErr_NoMemory #146092), not this.

Closest related, not duplicates:
- #143241 / PR #143243 (merged): fixed the infinite loop when the footer has no trailing newline by raising `ValueError("Invalid TZif file: unexpected end of file")`. In review, picnixz asked to document that `ValueError` is raised for invalid TZif data, which added the sentence in `Doc/library/zoneinfo.rst` that this issue relies on. The `assert` two lines above was left in place.
- #161096 / PR #161097 (merged 2026-11-01): rejects `charcnt` outside 0..512 with `ValueError`. It shows the maintainers want `ValueError` for malformed headers; it does not touch the struct.error paths or the assert.
- #156067, #154892, #145883: C-side error handling in `_zoneinfo.c`, unrelated to `_common.py`.

Upstream source: `gh api repos/python/cpython/commits?path=...&since=2026-06-01`. On `Lib/zoneinfo`, `Modules/_zoneinfo.c` and `Lib/test/test_zoneinfo`, the only commit that touches `load_data` is e9f37a3663 (gh-161096, charcnt). Main at 715d34fc38 (2026-11-17) and at 3ad9316217 (2026-11-17 22:15 UTC, used for the trimmed patch; no zoneinfo changes between them) still has the bug. `vendor/bugforge-results`: no zoneinfo entry (per the bug record).

## Behaviour before and after (both implementations, BytesIO and a real file)

Probe of 17 inputs, run with `zoneinfo` imported fresh with and without `_zoneinfo`:

| Input | v3.15.2 and unpatched main | patched main |
|---|---|---|
| valid v1, valid v2 | loads | loads |
| header cut after version / mid-counts | `struct.error: unpack requires a buffer of 24 bytes` | ValueError |
| short transitions / indices / ttinfo (v1 and v2) | `struct.error` (8, 2, 6 bytes) | ValueError |
| v2 footer without leading `\n` / empty footer | `AssertionError: b'U'` / `b''` | ValueError |
| same under `-O` | loads, first byte dropped (`EST5` becomes `ST5`, tzname `ST`) / ValueError | ValueError |
| timecnt = -1 | `struct.error: bad char in struct format` (BytesIO), ValueError from `BufferedReader.read(-8)` (file) | ValueError (incidentally: `read(-8)` returns the rest of the data, so `_read_exact` sees a length mismatch) |
| leapcnt = -1 in a v1 file | loads | loads (unchanged, out of scope) |
| negative count in the v1 header of a v2 file | `AssertionError` (BytesIO), `OSError: [Errno 22] Invalid argument` from `seek()` (file) | ValueError (BytesIO, via the footer check), `OSError` (file, unchanged, out of scope) |
| typecnt = -1 | ValueError (already) | ValueError |

C and pure Python agree on every row before and after.

Scope: an earlier version of the patch also rejected negative header counts. That was dropped to keep the change minimal, so the two "unchanged, out of scope" rows remain, and pr.md says they could be rejected in a follow-up.

## Tests (pod cpybatch)

Main: `git clone --depth 50`, `./configure --with-pydebug -q && make -j4 -s`, commit 3ad9316217 (trimmed patch; the first version was tested on 715d34fc38). 3.15.2: `git clone --depth 1 --branch v3.15.2`, release build, `Python 3.15.2 (tags/v3.15.2:5e58eaa)`.

- New test `test_truncated_or_malformed_file` before the fix: FAILURE, all 7 subtests fail in both `WeirdZoneTest` and `CWeirdZoneTest` (5 errors with `struct.error`, 2 failures with `AssertionError` from the footer `assert`). After the fix: SUCCESS.
- After: `./python -m test test_zoneinfo -j4` -> SUCCESS, 271 tests, 31 skipped (unpatched main: 269 tests, 31 skipped; the two new tests are the C and Python variants).
- `./python -O -m test test_zoneinfo -j4` -> SUCCESS, 271 tests, 31 skipped.
- Under `-O`, footer `EST5` without its newline: v3.15.2 and unpatched main load it as tzname `ST`, offset UTC-5; patched main raises `ValueError: Invalid TZif file: footer must start with a newline`.
- `./python -m test test_zoneinfo -m test_truncated_or_malformed_file -m test_bad_zones -R 3:3` -> SUCCESS (no refleaks).
- Bug-record reproducer: 3.15.2 and unpatched main print `['error', 'AssertionError', 'error', 'AssertionError']` and `REPRODUCED datetime-zoneinfo-load-data-not-valueerror`; patched main prints `['ValueError', 'ValueError', 'ValueError', 'ValueError']`.
- Issue reproducer (`issue.md`): 3.15.2 and unpatched main print the "Actual" lines; patched main prints `ValueError: Invalid TZif file: unexpected end of file` and `ValueError: Invalid TZif file: footer must start with a newline`.
- `make patchcheck` (after `git remote add upstream` and `git fetch -q --depth 50 upstream main`, with the change committed locally so the NEWS file is seen): 3 files, "Misc/NEWS.d updated with `blurb` ... yes", no whitespace complaints.
- `git apply --check fix.diff` on v3.15.2 fails because 3.15.2 predates gh-161096 (context lines differ); a backport needs a manual cherry-pick.

## Files

- `fix.diff`: `git diff upstream/main...HEAD` against 3ad9316217 (Lib/zoneinfo/_common.py, Lib/test/test_zoneinfo/test_zoneinfo.py, NEWS `2026-11-17-00-00-00.gh-issue-XXXXXX.KdLb1R.rst`). Rename the NEWS file once the issue number is known.
