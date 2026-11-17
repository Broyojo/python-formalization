# Follow-up: deprecate `maxsplit=` instead of removing it

Branch `gh-161970-userstring-replace-count`, new commit `5bc1249` on top of
`9d45abf` (no rebase, so a plain push works). Built and tested on the pod at
`~/pf/patches/userstring-v2/cpython`; patch in `followup.diff`, results in
`checks-v2.md`. Not pushed.

## Commit message

```
gh-161970: Deprecate UserString.replace() maxsplit keyword instead of removing it

Keep accepting the old keyword name for a deprecation period instead of
breaking callers that pass maxsplit= (typeshed spells the parameter
maxsplit). Passing maxsplit= now emits a DeprecationWarning and is slated
for removal in Python 3.18; passing both count and maxsplit raises
TypeError. This mirrors the deprecation of the 'string' keyword parameter
in hashlib (gh-134978), with a two-year period.
```

The first commit on the branch has no `Co-Authored-By` trailer and the user's
earlier patch drafts dropped AI lines from upstream text, so this commit has
none either.

## Reply to picnixz

> Typeshed spells the parameter `maxsplit` (`maxsplit: SupportsIndex = -1`), so
> type-checked code may well pass it by keyword. A GitHub code search found only
> definitions of `maxsplit`, in vendored copies of Python 2's `UserString.py`
> (and of `collections/__init__.py`) and in ctypesgen's copy and the bindings it
> generates, and no calls that pass `maxsplit=`. I've pushed a commit
> that keeps `maxsplit=` working with a `DeprecationWarning`, slated for removal
> in Python 3.18, following the hashlib `string=` deprecation (gh-134978), with
> a regression test; passing both `count` and `maxsplit` raises `TypeError`.

## What the commit does

- `Lib/collections/__init__.py`: `replace(self, old, new, count=-1, *,
  maxsplit=MISSING)`, where `MISSING` is a module-private `sentinel("MISSING")`
  (PEP 661 builtin, already used by `os`, `functools`, `dataclasses`), so
  `help()` shows `replace(self, old, new, count=-1, *, maxsplit=MISSING)`.
  `maxsplit=` warns via `warnings._deprecated(..., remove=(3, 18))`, which also
  turns into a `RuntimeError` once 3.18 leaves alpha, so the removal cannot be
  forgotten. The warning and `TypeError` texts copy hashlib's wording.
- `Lib/test/test_userstring.py`: positional and `count=` calls; `maxsplit=`
  warns (exact message, attributed to the caller's file) and still works and
  keeps the subclass type; both given raises `TypeError` (positional and
  keyword `count`). `string_tests.test_count_keyword` from the first commit
  still covers `count=` for str and UserString.
- Docs: `deprecated-removed:: 3.16 3.18` note under `UserString` in
  `Doc/library/collections.rst`; entry under "New deprecations" in
  `Doc/whatsnew/3.16.rst`; entry in `Doc/deprecations/pending-removal-in-3.18.rst`
  (already included by What's New and `deprecations/index.rst`, so no wiring).
- NEWS entry rewritten in place (same file).

## Removal version

Main is 3.16.0a2, so the deprecation starts in 3.16. Two annual releases later
is 3.18 (about October 2028), the "2 years instead of 5" picnixz asked for.
`urllib.parse` (gh-63293) already uses the same 3.16 -> 3.18 window.
