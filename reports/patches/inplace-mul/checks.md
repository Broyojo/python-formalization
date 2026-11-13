# Checks: inplace-mul (bug record bugs/corelibs-inplace-mul-heap-left.yaml)

## Duplicate searches (2026-11-13, python/cpython, issues and PRs, open and closed)

`gh search issues --repo python/cpython --include-prs <words>` with unquoted words:

| query | result |
|---|---|
| inplace multiply int subclass list TypeError | none |
| IntEnum *= list | nothing relevant (enum feature issues) |
| PyNumber_InPlaceMultiply sq_repeat | none |
| imul int subclass sequence repeat | none |
| x *= [1] TypeError | nothing relevant |
| PyNumber_InPlaceMultiply | #63270 (weakref.proxy in-place ops), #149317 (see below), #36443 (2002, float), #77334 (tuple crash): none about this |
| sq_inplace_repeat | #99196 (tests for PySequence_[InPlace]Repeat), #37334 (sq_concat vs __radd__, 2002): not this |
| imul sequence TypeError | #55686 (operand precedence for C sequences, open; related, not this), #36718/#36723 (2002 `__imul__` on new-style classes, fixed in 2.2.2): not this |
| inplace repeat int subclass | nothing relevant |
| augmented multiplication list int subclass | none |
| unsupported operand *= int subclass list | nothing relevant |

Bugforge results README (vendor/bugforge-results/README.md): no match for imul / `*=`.

Upstream main: `gh api repos/python/cpython/commits?path=Objects/abstract.c&since=2026-05-01` shows 3 commits
(d4f52c445b, a5568d0eb7, 70bd1c2dd2), none touching PyNumber_InPlaceMultiply. Fresh clone at
2c2d8018a2 (2026-11-13) still has `else if (mw != NULL)`.

Related, for the reviewer: gh-149180 (open) proposes making `tp_as_sequence` non-NULL for every
ready type. Its closed PRs #149317 and #149476 kept this `if/else if` shape (#149476 replaced the
NULL tests with `_PyType_HasOwnSequenceMethods`). If that idea lands, the `else if` here would also
need this fix to keep `int *= list` working; the two changes are compatible.

Status: no duplicate found, no upstream fix.

## Build and tests (build pod, Linux x86_64, GCC 11.4.0)

Clone: `git clone --depth 50 https://github.com/python/cpython.git`, HEAD 2c2d8018a20da33c749f42cc6a4ae55664a88321
(3.16.0a2+dev). `./configure --with-pydebug -q && make -j16 -s`: OK, no warnings after patch.

- Reproducer from the bug record, unpatched main: `REPRODUCED corelibs-inplace-mul-heap-left`.
- New test `testSequenceRepeatRightOperand`, unpatched: test_augassign FAILED (16 errors).
- Reproducer, patched: prints `[1, 1]`, `[1, 1]`, `ok ok [1, 1]`; no REPRODUCED line.
- `./python -m test test_augassign test_operator test_enum test_list test_capi test_binop test_bytes test_tuple test_userlist test_descr -j16`: SUCCESS, 10/10, 3,537 tests.
- `./python -m test test_grammar test_opcache test_compile test_unittest test_collections test_array -j16`: SUCCESS, 6/6.
- `./python -m test test_augassign -R 3:3`: SUCCESS (no refleaks).
- `git diff --check`: clean.

## Behaviour change

Only cases where the left operand's type has `tp_as_sequence` but neither `sq_inplace_repeat` nor
`sq_repeat`, and the in-place/binary number slots return NotImplemented. Before: always
`TypeError: unsupported operand type(s) for *=`. After: the right operand's `sq_repeat` is tried,
exactly as for `*`. So index-like left operands now work, and non-index left operands that have
sequence methods (dict, range, Python classes) get the same error as `*`:
`{} *= [1]` now says "can't multiply sequence by non-int of type 'dict'". The right operand is
never repeated in place (unchanged; checked in the test). Types with a repeat slot on the left are
unaffected because that branch returns first.
