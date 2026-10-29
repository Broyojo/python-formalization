# Playbook: formalizing a CPython module

Follow this for each new module. The goal is a model that is provably faithful
enough to trust, properties a maintainer would agree with, and bug reports a
maintainer would want to read.

## 1. Model (`lean/PyLean/<Module>/Model.lean`)

- Mirror the source line by line: same branch order, same check order, same
  early returns. Cite `Lib/<file>.py:<lines>` in each docstring.
- Python `int` → `Int`/`Nat`. Exceptions → `Py α` (`Except PyExc α`) with the
  source's exact message; prefix with `~` only if the message embeds formatted
  objects the model does not render.
- C code (`Objects/`, `Modules/`): model `Py_ssize_t` narrowing and its
  `OverflowError` explicitly. This is where Python's equivalent of Julia's
  integer-wraparound bugs lives.
- Loops use fuel; `PyExc.modelFuel` is never a Python outcome.

## 2. Differential test (`difftest/<module>_diff.py`)

- Add the functions to `lean/DiffMain.lean`; generate edge-heavy cases (0, -1,
  limits, empty, `sys.maxsize`, boundaries of every `if` in the source).
- The model must agree on 100% of cases before any property is stated. When
  you have a twin implementation (`_pydatetime`/`_datetime`, `_pydecimal`/
  `_decimal`, `_pyio`/`_io`, pure-Python vs C `heapq`/`bisect`/`functools`),
  diff all three: C vs Python disagreements are bugs on their own.

## 3. Properties (`lean/PyLean/<Module>/<Area>.lean` + registry entry)

- Each property quantifies over all inputs and cites its source: docstring,
  library docs, or "invariant". Prefer, in order: (a) the implementation
  disagreeing with itself (C vs Python, method A vs method B, round-trips);
  (b) invariants nobody would dispute (no crash, no internal error message,
  results in range); (c) explicit sentences from the docs read *in context*.
- Do not read single sentences as formal specs. CPython maintainers have
  explicitly rejected that (python/cpython#158786); docs assume real-number
  arithmetic and sane inputs. Floats: subnormal/overflow edge cases are
  expected IEEE behaviour unless the docs promise otherwise.
- Smoke-test every statement numerically against CPython before proving.

## 4. Prove or refute

- Proven: `theorem fooBar_proven : FooBar`. Refuted: `theorem fooBar_refuted : ¬FooBar`
  plus `bugs/<id>.yaml` whose reproducer prints `REPRODUCED <id>`.
- Never weaken a statement to get a proof. If it is false, refute it.
- Forbidden: `sorry`, `admit`, `native_decide`, `bv_decide`, `ofReduceBool`,
  new axioms, `implemented_by`, `@[extern]`. `scripts/audit.sh` enforces this
  and checks each theorem's type against the registry.

## 5. Triage before anything leaves this repo

- Search the tracker (`gh search issues --repo python/cpython ...`) and
  record the queries in the YAML. Also check `augusto-rehfeldt/bugforge-results`,
  which already swept much of the stdlib with property testing.
- Classify: `bug`, `maybe_intended`, `docs`. Write `likelihood` honestly.
- Nothing is filed automatically. A human reads every report, can explain it
  in their own words (devguide AI policy), and files related findings for a
  module as one issue, ideally with a PR and tests.
