# Playbook: formalizing a CPython module

The goal per module: a model that is demonstrably faithful, properties a
CPython maintainer would agree with, every property proven or refuted, and
bug records a maintainer would want to read. Fewer, better findings beat many
weak ones.

## Layout (one directory per module; touch only your own)

```
lean/PyLean/<M>.lean          registry: `def entries : List Entry` (yours to fill)
lean/PyLean/<M>/Model.lean    the model (create; split into more files freely)
lean/PyLean/<M>/Diff.lean     `handler` for `"mod": "<key>"` difftest cases (stub exists)
lean/PyLean/<M>/*.lean        properties + proofs, imported from lean/PyLean/<M>.lean
difftest/<key>_diff.py        uses difftest/common.py (see ipaddress_diff.py)
bugs/<key>-<slug>.yaml        one per distinct defect (see bugs/ipaddress-*.yaml)
```

Shared files (`Core.lean`, `DiffCore.lean`, `Registry.lean`, `DiffMain.lean`,
`PyLean.lean`, `Audit.lean`, `scripts/`) are already wired for every module.
Do not edit them. If you truly need a new `PyExc` constructor or helper, put a
local definition in your module and mention it in your report.

Sources (absolute paths; `vendor/` is not in git worktrees):
- CPython 3.14.7 source (matches `python3`, cite these line numbers):
  `/Users/broyojo/code/projects/python-formalization/vendor/cpython-3.14`
- CPython main source: `/Users/broyojo/code/projects/python-formalization/vendor/cpython-main`
- CPython main interpreter (to check bugs still exist on main):
  `/Users/broyojo/code/projects/python-formalization/vendor/cpython-main/python.exe`
- Prior automated findings (for duplicate checks):
  `/Users/broyojo/code/projects/python-formalization/vendor/bugforge-results/README.md`

## 1. Model

- Mirror the source line by line: same branch order, same check order, same
  early returns. Cite `Lib/<file>.py:<lines>` or `Objects/<file>.c:<lines>`.
- Python `int` → `Int`/`Nat`. Exceptions → `Py α` with the source's exact
  message; prefix the message with `~` only when it embeds formatted objects.
- C code: model `Py_ssize_t` narrowing, C integer types (use `Int` plus
  explicit wrap/overflow functions), fast paths vs slow paths, and the
  `OverflowError`s, exactly as written. Fast-path/slow-path disagreement and
  silent wraparound are the highest-value bugs here.
- Strings/bytes: `String`/`List Char` or `List UInt8`/`List Nat` as convenient.
- Floats: Lean's `Float` cannot be reasoned about in proofs (and `decide`
  cannot evaluate it). Keep proven/refuted properties to exact (integer,
  rational, string) behaviour. Float paths may be modelled for difftesting only.
- Loops use fuel; `PyExc.modelFuel` is never a Python outcome.
- Twins: when both a C and a pure-Python implementation exist, model both if
  they differ structurally, and state "C and Python agree" properties.

## 2. Differential test (before stating any property)

- Edge-heavy generation: 0, ±1, boundaries of every `if` in the source,
  `sys.maxsize`, ±2**63, ±2**64, empty inputs, huge ints.
- Reach 100% agreement on ≥50k cases with several seeds. A mismatch is a model
  bug until proven otherwise; a mismatch between CPython's own C and Python
  twins is a finding.

## 3. Properties (quality rubric; reviewers will check every one)

- Quantify over all inputs. Every hypothesis must be a documented
  precondition or a type invariant, and the docstring says which. Never assume
  away the interesting case ("no overflow", "index in range", "small input").
  In the Julia project, 128 of 130 quick "proofs" turned out to assume the
  index was in bounds.
- Source, in order of preference: (a) the implementation disagreeing with
  itself (C vs Python twin, fast vs slow path, method vs equivalent method,
  round-trips, str vs bytes); (b) undisputed invariants (no crash, no internal
  error leaking, results in range, no hang); (c) explicit doc sentences read in
  context. Docs assume real-number arithmetic and sane inputs; CPython
  maintainers have rejected literal one-sentence readings
  (python/cpython#158786).
- Smoke-test every statement numerically against CPython before proving it.
- Aim for 8-20 meaningful properties per module, not hundreds of trivial ones.

## 4. Prove or refute

- `theorem fooBar_proven : FooBar` or `theorem fooBar_refuted : ¬FooBar`; the
  registry entry names both. A refutation needs `bugs/<id>.yaml` whose
  reproducer prints `REPRODUCED <id>` on python3 3.14.7; also run it with the
  main interpreter and record the result.
- Never weaken a statement to get a proof. If it is false, refute it.
- Forbidden: `sorry`, `admit`, `native_decide`, `bv_decide`, `ofReduceBool`,
  new axioms, `implemented_by`, `@[extern]`. Run `scripts/audit.sh`-style checks:
  `cd lean && lake build && lake env lean Audit.lean`.
- If a proof is intractable after serious effort, leave the entry `.open`
  with a note on what is missing, rather than weakening it.

## 5. Triage (read-only; nothing leaves this repo)

- NEVER create, comment on, or react to GitHub issues/PRs, and never contact
  anyone. `gh search issues --repo python/cpython ...`, `gh issue view` and
  `gh api` GETs are fine. Record every query in the YAML.
- Check the bugforge list above too; mark duplicates.
- Fill `priority`, `kind`, `likelihood` (honest), `maybe_intended`,
  `promised_by`, `cause` (with line numbers), `possible_fix`.
- A human reviews everything before any report is filed, and related findings
  for a module go upstream as one issue.
