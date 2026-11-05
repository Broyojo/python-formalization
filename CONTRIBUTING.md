# Contributing

Help is welcome, whether you run your own agents or write Lean by hand. About 16% of the in-scope functions of CPython 3.15.2 are modelled and reviewed so far; the rest is open.

## Ways to help

- **Model a file.** Rows marked `todo` in `coverage/methods/<file>.tsv` are unclaimed. `python3 scripts/check_coverage.py` shows totals per area. Follow `AGENTS.md`: mirror the source line by line, difftest against CPython 3.15.2 until it agrees on at least 50,000 cases, then prove or refute properties.
- **Review.** Run a review of any file with `coverage/REVIEW_PROMPT.md` and record verdicts in `coverage/review/`. A well-argued HOLLOW verdict is as useful as a new model.
- **Check a bug record.** If a record in `bugs/` is wrong, no longer reproduces, or is already known upstream, open an issue here with the evidence.
- **Apply the method elsewhere.** If you formalize another language or library this way, open an issue and we'll link it.

## Before you start

- For a whole file or area, open an issue first so two people don't model the same thing.
- One pinned version only: CPython 3.15.2. Cite its line numbers.
- Pull requests must pass `lake build` and `lake env lean Audit.lean` from `lean/` (a full build needs about 64 GB of RAM), and the difftest for the area you touched.
- No `sorry`, `admit`, `native_decide`, `bv_decide`, new axioms, `implemented_by` or `@[extern]`.
- Coverage counts only rows an independent review marks `FAITHFUL`. Never weaken a statement to get a proof; refute it instead.
- Nothing from this project goes to the CPython tracker without a human reading it first. If you find a CPython bug, add a record under `bugs/` and say so in your pull request.

By contributing you agree that your contributions are licensed under the Apache License 2.0 (see `LICENSE`).
