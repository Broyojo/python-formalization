# Playbook: formalizing a CPython module

The goal is to formalize Python: model as much of CPython as possible, the way
julia-in-lean models Julia Base. Coverage is the headline number and bugs are a
by-product of it. `coverage/methods/` lists every function, opcode and grammar
rule; `python3 scripts/check_coverage.py` reports how many are modelled.

A file you own is finished when every row for it is modelled or excluded with
a reason. Work breadth first: mirror every function in the file, difftest them,
give each at least one property, and settle what is cheap. Do not spend your
effort on a few deep proofs while the rest of the file has no model. A hard
property stays `.open` in the registry with a note; do not drop it, and do not
weaken it.

Bug reports stay held to a high bar: fewer, better findings beat many weak ones.

## Coverage rules

- List EVERY function a proven or refuted entry covers in its `pyFns`, helpers
  included, using the name in the inventory (`coverage/methods/<file>.tsv`). A
  function counts as modelled only through such an entry. `scripts/check_coverage.py
  --prefill` matches these names after merge.
- A row with no behaviour worth modelling becomes `excluded` in its tsv, with a
  note starting `no-behaviour:`, `deprecated:`, `internal-bootstrap:`,
  `platform:`, `vendored:`, `test-support:` or `generated:` and a justification.
  Exclude honestly: reference counting, GC traversal, and allocator plumbing are
  `no-behaviour:` when they have no Python-visible effect; anything with an
  observable result is not.
- Generic functions are modelled over an abstract element type with explicit
  assumptions, as julia-in-lean does (for example, "if the element type's `__lt__`
  is a strict weak order"), not by picking `int` and stopping.
- Every model is later reviewed against `coverage/REVIEW_PROMPT.md`. Hollow
  entries get withdrawn, so mirror the body rather than specifying its result,
  and check every source citation against the file instead of from memory.
- The first review found a quarter of `modelled` claims hollow, in the same places
  every time, so check these before you claim a row:
  - Failure paths are part of the body. Mirror what happens when a callback,
    `__eq__`, `__index__` or iterator raises, not only the success path.
  - Re-entrancy guards too: "already running" checks, re-checks after calling
    Python code. These are where CPython's real memory-safety bugs live.
  - Non-int inputs. `count(2.5, 0.5)` is documented; an int-only model of it is
    hollow. Use `lean/PyLean/Binary64/` for floats.
  - A row needs a theorem that unfolds that function's body. Listing a name in
    `pyFns`, or an alias restated as a conjunct, is not coverage. A refutation
    covers only the functions its counterexample runs.
- GC traversal rows are `no-behaviour:` by policy, as a stated scope limit: we have
  no heap model, though `gc.get_referents()` can observe them. This covers
  `tp_traverse` only. `tp_clear` and `tp_dealloc` that run weakref callbacks or
  finalizers are Python-visible, so they are not `no-behaviour:`.

## Compute: nothing heavy on this machine

Do not run `lake`, `lean`, difftests, reproducers or any other CPU- or
memory-heavy command locally. Run them on the build pod through the wrapper,
from inside your worktree:

```
/Users/broyojo/code/projects/python-formalization/scripts/r lake build      # from lean/
/Users/broyojo/code/projects/python-formalization/scripts/r lake env lean Audit.lean
/Users/broyojo/code/projects/python-formalization/scripts/r python3 difftest/foo_diff.py --cases 50000
/Users/broyojo/code/projects/python-formalization/scripts/r python3 scripts/check_bugs.py \
    --python /Users/broyojo/code/projects/python-formalization/vendor/cpython-main/python.exe
```

The wrapper syncs your worktree to the pod and runs the command there, so edit
files locally as usual; do not edit on the pod, because the next sync overwrites
it. `python3` on the pod is 3.14.7 and the `vendor/` paths below work there too.
Reading files, git and `gh` stay local. Scratch `.lean` files must live inside
your worktree to be synced (not under `lean/PyLean/`, and do not commit them).

The pod is shared by many agents. Kill your own stray processes by PID, never
with `pkill -f` or a pattern, which can hit another agent's work. A watchdog kills
any Lean process above 64 GB of resident memory. If `lake build` fails, an
`Audit.lean` run still reports results from the old build, so always chain them
with `&&` and confirm the build passed before trusting the audit.

The pod is pinned to our own Kubernetes cluster. Never launch compute on a paid
cloud, and never touch the other clusters in `sky status`.

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

## Reference modules (finished; copy their patterns)

- `Datetime`: modelling C and Python twins side by side, parsers over UTF-8 bytes.
- `RangeSlice`: C `Py_ssize_t`/unsigned-long fast paths vs PyLong slow paths;
  a C-API finding reproduced with a tiny compiled extension.
- `Accel`: layered twin properties (broad "C == Py" refuted, narrowed version
  proven, so every excluded case is on record as a refutation).
- `Binary64`: exact IEEE-754 doubles for proofs. Use `F64` in `Binary64.Model`.
- `Fractions`: exact arithmetic proofs, the 4300-digit int/str limit, format specs.
- `StrSearch`: str vs bytes vs bytearray agreement.

Lessons so far: the C arithmetic is usually right. Findings came from
parsers (`datetime.fromisoformat`), missing error checks after
`PyLong_AsSsize_t`-style conversions, NUL-terminator assumptions in C, and
validation done in the wrong order. Look there first.

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
  cannot evaluate it). Use the exact binary64 model in `lean/PyLean/Binary64/`.
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
- Expect about one meaningful property per function. A property may cover several
  functions when they form one behaviour, but list them all in `pyFns`.

## 4. Prove or refute

- `theorem fooBar_proven : FooBar` or `theorem fooBar_refuted : ¬FooBar`; the
  registry entry names both. A refutation needs `bugs/<id>.yaml` whose
  reproducer prints `REPRODUCED <id>` on python3 3.14.7; also run it with the
  main interpreter and record the result.
- Never weaken a statement to get a proof. If it is false, refute it.
- Forbidden: `sorry`, `admit`, `native_decide`, `bv_decide`, `ofReduceBool`,
  new axioms, `implemented_by`, `@[extern]`. Check with `lake build` and
  `lake env lean Audit.lean` from `lean/`, through `scripts/r`.
- If a proof is not cheap, leave the entry `.open` with a note on what is
  missing and move on; come back once the file has full coverage.

## 5. Triage (read-only; nothing leaves this repo)

- NEVER create, comment on, or react to GitHub issues/PRs, and never contact
  anyone. `gh search issues --repo python/cpython ...`, `gh issue view` and
  `gh api` GETs are fine. Record every query in the YAML.
- `gh search issues "two words"` searches for the exact phrase, so an empty
  result means little. Search with unquoted words, and try several spellings.
- Check the bugforge list above too; mark duplicates.
- Fill `priority`, `kind`, `likelihood` (honest), `maybe_intended`,
  `promised_by`, `cause` (with line numbers), `possible_fix`.
- A human reviews everything before any report is filed, and related findings
  for a module go upstream as one issue.
