# python-formalization

A Lean 4 model of CPython 3.15.2, written by AI agents, tested against the real interpreter, and reviewed function by function. Along the way it found hundreds of bugs in CPython.

**Write-up:** [broyojo.com/python-formalization](https://broyojo.com/python-formalization/)

<!-- stats:start -->
| | |
|---|---|
| Lean code | 613,318 lines in 1,539 files |
| Theorems and lemmas | 18,898, all checked on every build |
| Top-level properties | 3,834 proven, 588 refuted, 94 open |
| Functions reviewed faithful | 4,071 of 26,004 in scope (15.7%) |
| Bug records | 418 that reproduce on 3.15.2, each with a reproducer |
<!-- stats:end -->

## How it works

Every function, bytecode instruction and grammar rule in the CPython 3.15.2 source tree is a row in an inventory (`coverage/methods/`). Each row goes through four steps:

1. **Mirror.** An agent writes a Lean model that follows the C or Python source line by line: same branch order, same error messages, same integer overflow. Each step cites the 3.15.2 source. Python callbacks are modelled as code that can raise, change state and re-enter.
2. **Differential test.** The model and the real `python3` run side by side on generated inputs (`difftest/`) until they agree on at least 50,000 cases across several seeds.
3. **Prove or refute.** Properties are stated over all inputs and proved in Lean. A false statement is refuted with a counterexample, never weakened. The build rejects `sorry`, `native_decide` and new axioms.
4. **Review.** A separate agent that did not write the model checks it against the source, runs each property on the real interpreter, and asks whether a broken implementation would also satisfy the theorem. Only rows marked `FAITHFUL` in `coverage/review/` count as covered.

When a refuted property turns out to be CPython's fault, it becomes a bug record in `bugs/`: a reproducer that prints `REPRODUCED` on 3.15.2, the cause with line numbers, a duplicate search of the CPython tracker, and a priority.

## Layout

```
lean/PyLean/<Area>/        models and proofs, one directory per area of CPython
lean/PyLean/Registry.lean  one entry per property: source citation, status, theorem
lean/Audit.lean            checks every registry theorem and the axioms it uses
lean/DiffMain.lean         `pydiff`, the Lean side of the differential tests
difftest/                  case generators and the harness that compares Lean with CPython
coverage/methods/          the inventory: one row per function with its status
coverage/review/           independent review verdicts (FAITHFUL / HOLLOW) per row
bugs/                      one YAML record per finding; FINDINGS.md lists them
reports/                   triage of bug records and draft upstream issues
site/                      generator for the write-up (docs/index.html)
AGENTS.md                  instructions the modelling agents follow
coverage/REVIEW_PROMPT.md  instructions the reviewing agents follow
```

## Running it

You need the Lean toolchain pinned in `lean/lean-toolchain` (Lean 4.35.0, installed by `elan`) and a CPython 3.15.2 build on `PATH` as `python3`. A full build is large: plan for a machine with 64 GB of RAM or more.

```sh
cd lean && lake build && lake env lean Audit.lean      # build every model and proof, then audit
python3 difftest/rangeslice_diff.py --cases 50000       # one area's model against CPython
python3 scripts/check_bugs.py                           # every bug record still reproduces
python3 scripts/check_coverage.py                       # coverage totals from the inventory
```

We ran heavy jobs on a build machine on Chao Zhang's Kubernetes cluster. `sky/builder.yaml` sets it up with SkyPilot, and `scripts/r <command>` syncs the checkout and runs the command there.

## Doing this for another project

Nothing here is specific to Python. To apply the method to another language, library or format:

- Start from `AGENTS.md` and `coverage/REVIEW_PROMPT.md`, and replace the CPython specifics.
- Build an inventory of every function in one pinned version (`scripts/list_python_functions.py` is ours).
- Keep coverage counted only through independent review (`scripts/check_coverage.py`).

The write-up's last sections list the practices that mattered most.

## Contributing

Help is welcome. Most of CPython is still unmodelled, and the method needs more reviewers as much as more models. See [CONTRIBUTING.md](CONTRIBUTING.md).

## License

Apache License 2.0 (see `LICENSE`). Excerpts of CPython quoted in the models remain under the PSF License; see `NOTICE`.

## Credits

Built by David Andrews with AI agents running Claude Opus 5.5 in Claude Code. Inspired by Miles Cranmer's [julia-in-lean](https://github.com/MilesCranmer/julia-in-lean).

Thanks to Chao Zhang for discussions about applying this approach to other languages, and for the compute that ran the builds and tests.
