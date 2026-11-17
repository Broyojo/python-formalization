# Checks: except* / split() set __suppress_context__ on the parts

Bug record: `bugs/typeobj-exc-split-sets-suppress-context.yaml`.

## Duplicate searches (2026-11-17)

`gh search issues` and `gh search prs`, `--repo python/cpython`, open and closed, words unquoted. A first batch hit the search rate limit and was rerun with pauses; the results below are from the rerun.

No results (issues and PRs both): `except* suppress_context`, `ExceptionGroup split __suppress_context__`, `except star traceback context hidden`, `exceptiongroup_split context`, `except* __context__ lost`, `exceptiongroup_subset`, `suppress_context split subgroup`, `except* During handling of the above exception`, `ExceptionGroup context missing traceback`, `PyException_SetCause suppress_context`, `exception group split context traceback`, `except star context not shown`, `exception group __context__`, `ExceptionGroup split context`, `ExceptionGroup suppress`, `except star chained exception`, `exception group chained traceback`, `ExceptionGroup subgroup cause`, `split cause context ExceptionGroup`, `except star context`, `exception group During handling`, `exception_group_projection`, `ExceptionGroup derive context cause`, `split __cause__ __context__`, `subgroup __context__`, `ExceptionGroup __cause__ split`.

Unrelated results only:
- `__suppress_context__`: issues 83906, 74283, 63061, 155704, 111917, 59010, 87312, ... (about `from None` display and docs); PRs 106676, 113057, 24179 (pdb, docs, TracebackException). None about exception groups.
- `PrepReraiseStar`: 105071 / PR 105072 (exposing `PyUnstable_Exc_PrepReraiseStar`), 157197, 162144.
- `except* __context__`, `except* chaining`: 61902, 87214, 106670, 47358, PR 161536. Unrelated.
- `ExceptionGroup split` (sanity check that search works): 137889, 129025, 125825, 128049, 119287, 105730. None about metadata.

Related, not a duplicate: gh-99619 (closed), a docs fix saying `derive()` does not copy `__cause__` etc. because `split()` does it.
bugforge-results README: no `Objects/exceptions.c` entries (per the bug record).

Upstream main: commits touching `Objects/exceptions.c` since 2026-09-01 are f767423095 (gh-161242, AC vectorcall), 7e5227fb8c (gh-160773, OSError.__str__), 2507a7fa73 (gh-159294, MemoryError when creating an ExceptionGroup), 45538495be (gh-114258, AC `__str__`), 6b5d4143f3 (gh-113318, AC getters). Tests: f4043ab1be (gh-160659, except* handlers raising BaseException), 2507a7fa73. None touch `exceptiongroup_subset` or `suppress_context`; main still has the `PyException_SetCause(eg, PyException_GetCause(orig));` line with nothing after it. **No duplicate and no existing fix found.**

## Intended or a bug?

Arguments that it is a bug:
- `exceptiongroup_subset()` is documented in its own comment as making a group "with metadata from _orig". It copies `__context__` and then hides it; neither "keep the context" nor "drop the context" describes the result.
- The docs of `subgroup()` and `derive()` say the parts keep `__traceback__`, `__cause__`, `__context__` and `__notes__`. Keeping `__context__` while suppressing it defeats that for display, which is what the context is for.
- Consistency with plain `except`: an `except TypeError:` that does not match lets the original group propagate with `__suppress_context__ == False`, so the traceback shows "During handling of the above exception". `except* TypeError:` that handles part of the group re-raises a `split()` part, which loses that section. PEP 654 says `subgroup()` returns "an exception group that has the same metadata (message, cause, context, traceback) as the original group", and that in `except*` "the reraised exceptions and the unhandled exceptions are subgroups of the original group, and share its metadata (cause, context, traceback)". It never mentions `__suppress_context__`.
- The flag is a side effect: `PyException_SetCause()` sets `suppress_context = 1` unconditionally (its job is to implement `raise ... from ...`), including for a `NULL` cause.
- No test checks the current value. Every test in test_exception_group and test_except_star passes with the fix, apart from the new assertions which fail without it.

Arguments that it could be intended:
- `__suppress_context__` is not in the docs' list of copied fields, so the docs do not promise it.
- The pure-Python `exceptiongroup` backport (agronholm/exceptiongroup, `src/exceptiongroup/_exceptions.py:57`) copies the cause with `eg.__cause__ = self.__cause__`, which sets the flag in the same way. So the C code and the backport agree. I found no discussion choosing it on purpose, and both look like the same accident: assigning `__cause__` for copying rather than for chaining.

Judgement: a bug, low severity (diagnostics only; no data is lost, only hidden in tracebacks). Groups with a real cause, or raised `from None`, already had the flag set and are unchanged by the fix.

## Fix

In `exceptiongroup_subset()`, after `PyException_SetCause(eg, ...)`, copy `suppress_context` from `orig`. Direct field access via `PyBaseExceptionObject_CAST` matches other code in the file (e.g. `is_same_exception_metadata`); the `__suppress_context__` member is a plain `Py_T_BOOL` without locking.

## Build and tests (build pod `cpybatch`, Linux x86_64, GCC 11.4)

Clone: `git clone --depth 50 https://github.com/python/cpython.git`, main at
715d34fc38f84bbccf9feaf937477290e575b060 (2026-11-17). `./configure --with-pydebug -q && make -j4 -s`:
`Python 3.16.0a2+dev (heads/main:715d34f)`.

Before the fix (main 715d34f): the reproducer in `issue.md` prints only the ExceptionGroup traceback, without the `ValueError: context` section; attribute check prints `False True True` / `True`. The bug record also has it reproduced on python3 3.15.2 (`scripts/check_bugs.py`); `Objects/exceptions.c` has the same two lines there (3.15.2 lines 1195-1196, `PyException_SetCause` at 547-554). The 3.15.2 build pod was not reachable today, so 3.15.2 was not rerun for this patch.

With only the new tests applied (C change reverted):
`./python -m test test_except_star test_exception_group` -> test_except_star 16 failures, test_exception_group 7 failures.

With the fix:
- Reproducer shows "ValueError: context / During handling of the above exception, another exception occurred:" before the group; attribute check prints `False False False` / `True`.
- `./python -m test test_except_star test_exception_group test_exceptions test_traceback -j4`: SUCCESS, 4 files, run=680 skipped=4.
- `./python -m test test_except_star test_exception_group -R 3:3`: SUCCESS (no leaks), run=120.
- Also `./python -m test test_contextlib test_contextlib_async test_asyncio.test_taskgroups test_capi.test_exceptions -j4` (other users of `split()` and `PyUnstable_Exc_PrepReraiseStar`): SUCCESS, run=336.
- `make patchcheck` (after `git remote add upstream ...; git fetch -q --depth 50 upstream main`): 4 files changed, NEWS entry found, no whitespace complaints.

`fix.diff` is `git diff --cached` against 715d34f (equal to upstream/main at fetch time) and contains the C fix, the tests and the NEWS entry `Misc/NEWS.d/next/Core_and_Builtins/2026-11-17-00-00-00.gh-issue-XXXXXX.tV-0C309.rst`. The pod clone was removed afterwards.
