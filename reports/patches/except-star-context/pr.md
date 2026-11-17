# gh-XXXXXX: Keep `__suppress_context__` when splitting an exception group

`exceptiongroup_subset()` copies the original group's cause with `PyException_SetCause()`, which always sets `suppress_context`, so every part made by `split()`, `subgroup()` or `except*` had `__suppress_context__` set even when the original did not. The parts kept `__context__` but tracebacks no longer showed it, so a group partly handled by `except*` inside an `except` block lost its "During handling of the above exception" section. This copies `suppress_context` from the original after setting the cause.

Tests: the split/subgroup sanity checks in `test_exception_group` and `assertMetadataEqual` in `test_except_star` now compare `__suppress_context__` too, and there are new tests for all four cause/suppress combinations and for `except*` re-raise with and without `from None`. Without the C change, 7 tests in `test_exception_group` and 16 in `test_except_star` fail.

Notes for reviewers:
- Groups with an explicit cause or raised `from None` already had `__suppress_context__` set, and still do. Only groups with `__suppress_context__ == False` (the implicit-context case) change.
- The docs for `subgroup()` and `derive()` list `__traceback__`, `__cause__`, `__context__` and `__notes__` as copied. I left them unchanged; adding `__suppress_context__` to that list would be a small follow-up if wanted.
- The `exceptiongroup` backport has the same behaviour (it assigns `eg.__cause__ = self.__cause__`, which also sets the flag), so code that relied on it there would see the same change on 3.11+ after this fix.
