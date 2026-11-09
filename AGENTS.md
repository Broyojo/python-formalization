# Playbook: formalizing a CPython module

The goal is to formalize Python: model as much of CPython as possible, the way
julia-in-lean models Julia Base. Coverage is the headline number and bugs are a
by-product of it. `coverage/methods/` lists every function, opcode and grammar
rule; `python3 scripts/check_coverage.py` reports how many are modelled.

The number that matters is rows that pass review, not rows marked `modelled`.
An earlier version of this brief asked for breadth first and at least one
property per function. Agents did that, and independent review then found fewer
than half of the rows it checked held up (21% in `functools.py`). Do not repeat
that: a file is finished when its rows would survive review. Prefer fewer, deeper
properties over many thin ones. A hard property stays `.open` in the registry with
a note; do not drop it, and do not weaken it.

Bug reports stay held to a high bar: fewer, better findings beat many weak ones.

## Coverage rules

- List EVERY function a proven or refuted entry covers in its `pyFns`, helpers
  included, using the name in the inventory (`coverage/methods/<file>.tsv`). A
  function counts as modelled only through such an entry. `scripts/check_coverage.py
  --prefill` matches these names after merge.
- A row with no behaviour worth modelling becomes `excluded` in its tsv, with a
  note starting `no-behaviour:`, `deprecated:`, `internal-bootstrap:`,
  `platform:`, `vendored:`, `test-support:`, `generated:` or `trivial:` and a
  justification. `trivial:` is only for a body that returns one field with no
  branch; it says there is nothing to prove, and it does not count as coverage. A
  getter with a released-object check has a branch, so state the refusal.
  Exclude honestly: reference counting, GC traversal, and allocator plumbing are
  `no-behaviour:` when they have no Python-visible effect; anything with an
  observable result is not.
- Generic functions are modelled over an abstract element type with explicit
  assumptions, as julia-in-lean does (for example, "if the element type's `__lt__`
  is a strict weak order"), not by picking `int` and stopping.
- Every model is later reviewed against `coverage/REVIEW_PROMPT.md`. Hollow
  entries get withdrawn, so mirror the body rather than specifying its result,
  and check every source citation against the file instead of from memory.
- A theorem can be proven and still false about CPython, if the model is wrong
  where the difftest does not reach. Review found four. Before relying on a
  statement, run that exact statement against the real interpreter.
- Review keeps finding the same failures, so check these before you claim a row:
  - Failure paths are part of the body. Mirror what happens when a callback,
    `__eq__`, `__index__` or iterator raises, not only the success path.
  - Re-entrancy guards too: "already running" checks, re-checks after calling
    Python code. These are where CPython's real memory-safety bugs live.
  - Non-int inputs. `count(2.5, 0.5)` is documented; an int-only model of it is
    hollow. Use `lean/PyLean/Binary64/` for floats.
  - Model iterators and callbacks as fallible: `Py`-valued, able to raise and
    re-enter. A model over plain lists cannot express these paths at all.
  - A row needs a theorem that unfolds that function's body. Listing a name in
    `pyFns`, or an alias restated as a conjunct, is not coverage. If the theorem
    would still hold for any function, or discards the mirror through a
    `bind_ok`-style step, it does not count. Nor does `rfl` on a one-line
    definition, a hard-coded constant, or a single-example instance. A refutation
    covers only the functions its counterexample runs.
  - Test a theorem by asking what wrong function would also satisfy it. If
    `fun _ => .error` or "always take the first" passes, it pins nothing, even
    when the mirror above it is exact. Rebuilt files mostly fail here now.
  - Do not force `Bool` where Python returns an arbitrary object, do not use `=`
    on value structures to claim object identity, and do not merge a twin
    difference into one model (duck typing in Python, an exact type check in C).
- Classes may be modelled by identity, as a stated scope limit: a metaclass that
  overrides `__eq__`, `__hash__` or `__repr__` is out of scope.
- GC traversal rows are `no-behaviour:` by policy, as a stated scope limit: we have
  no heap model, though `gc.get_referents()` can observe them. `tp_clear` and
  `tp_dealloc` that only drop references are excluded the same way, because we
  have no finalization model, even though dropping the last reference can run
  `__del__` or close a file. Explicit effects are not excluded: a call such as
  `PyObject_ClearWeakRefs`, or a finalizer the function invokes itself.

## Compute: nothing heavy on this machine

`$PF` below is the path of the main checkout (not a worktree); `vendor/` lives only there.

Do not run `lake`, `lean`, difftests, reproducers or any other CPU- or
memory-heavy command locally. Run them on the build pod through the wrapper,
from inside your worktree:

```
$PF/scripts/r lake build      # from lean/
$PF/scripts/r lake env lean Audit.lean
$PF/scripts/r python3 difftest/foo_diff.py --cases 50000
$PF/scripts/r python3 scripts/check_bugs.py \
    --python $PF/vendor/cpython-main/python.exe
```

The wrapper syncs your worktree to the pod and runs the command there, so edit
files locally as usual; do not edit on the pod, because the next sync overwrites
it. `python3` on the pod is 3.15.2 and the `vendor/` paths below work there too.
Reading files, git and `gh` stay local. Scratch `.lean` files must live inside
your worktree to be synced (not under `lean/PyLean/`, and do not commit them).

The pod is shared by many agents. Kill your own stray processes by PID, never
with `pkill -f` or a pattern, which can hit another agent's work. A watchdog kills
any Lean process above 64 GB of resident memory. If `lake build` fails, an
`Audit.lean` run still reports results from the old build, so always chain them
with `&&` and confirm the build passed before trusting the audit.

The pod is pinned to Chao Zhang's Kubernetes cluster. Never launch compute on a paid
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

Python version: the project formalizes CPython 3.15.2, the latest release, and only
that version. A bug counts if it reproduces on 3.15.2. Main gets reproducers only.

Moving from 3.14.7, where the project started. `scripts/repin.py` compared every
function with its 3.15.2 body:
- A row with an unchanged body kept its status, but only that function's own text
  was compared. A changed callee, macro, header or clinic converter does not show,
  so the difftest on 3.15.2 is what checks it.
- A changed or new row is `todo` with a note starting `changed-in-3.15:`, and
  `check_coverage.py --prefill` will not credit it. Mirror the 3.15.2 body, update
  the theorem, then delete the note from the row. Deleting the note is your claim
  that the model now matches that body, so do not delete it for any other reason.
- `coverage/repin-3.15.2.tsv` lists every changed, moved, removed and new row, with
  the entries they used to have. Use it as your worklist, most-modelled file first.
- A citation that fell in changed code reads `Objects/x.c@3.14.7:12`, or `@3.14.7:12`
  when bare. `grep -rn '@3.14.7:' lean/PyLean/<M>` lists yours. Each is a line nobody
  has checked against 3.15.2, so fix it when you recheck that function.
- `coverage/difftest-migrating.txt` lists difftests that still fail on 3.15.2. A
  failure there does not fail the audit. A mismatch on 3.15.2 is a real model change
  until proven otherwise: fix the model and reach 100% on several seeds, as always,
  then remove your line. Do not delete a generator case to get there.
- `coverage/gone-in-3.15.txt` lists bug records and entries for 3.14.7 behaviour
  that 3.15.2 does not have. `check_bugs.py` skips them and they credit no row. The
  model of that function still describes 3.14.7: update it, state what is true now,
  and remove the id once the entry describes 3.15.2.
- Reviews of changed rows are in `coverage/review/archive-3.14.7/`. They no longer
  count, but they say what the last reviewer found wrong.

Sources (absolute paths; `vendor/` is not in git worktrees):
- CPython 3.15.2 source (matches `python3`, cite these line numbers):
  `$PF/vendor/cpython-3.15`
- CPython 3.14.7 source, only for diffing what changed:
  `$PF/vendor/cpython-3.14`
- CPython main source: `$PF/vendor/cpython-main`
- CPython main interpreter (to check bugs still exist on main):
  `$PF/vendor/cpython-main/python.exe`
- Prior automated findings (for duplicate checks):
  `$PF/vendor/bugforge-results/README.md`

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
  reproducer prints `REPRODUCED <id>` on python3 3.15.2; also run it with the
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
