# Coverage review (fixed criteria)

Adapted from julia-in-lean. This procedure checks whether registry entries
really model the CPython functions they claim to cover. A row marked `modelled`
is only a claim until it passes this review. Read the pinned source in
`vendor/cpython-3.14` (see `coverage/SOURCE_COMMIT`). Review the source and the
proofs by reading them; do not execute Lean or Python.

Your input is `coverage/methods/{FILE}.tsv`. For every row with status
`modelled`, read the function at the row's `line` to `endline`, and for each
registry id in the row's `entry`, read the entry in `lean/PyLean/*.lean`, its
`prop` definition, and every definition it uses, including ones imported from
other modules. Then answer three questions:

1. MIRROR: Does the proposition use a Lean function that mirrors THIS function's
   body (its branches, checks, loops, arithmetic and calls, in the same order),
   rather than a different function of the same name, a hand-written
   specification, or a bare variable standing for the function's result? Do
   the model's source citations point at the right lines?
2. PROPERTY: Does the proposition state something about this function's
   behaviour that its docstring, the documentation, or an obvious invariant
   promises, quantified over all allowed inputs (not only worked examples), with
   hypotheses that are only type invariants or documented preconditions?
3. SETTLED: Is the entry proven or refuted, and for a refuted entry, does
   `bugs/<id>.yaml` exist?

For every row with status `excluded`, answer one question instead: does the
note's reason truly apply to this function?

The verdict is FAITHFUL only if every answer is yes; otherwise HOLLOW. Be
strict: when unsure, answer no and say what is missing.

Write `coverage/review/{FILE}.tsv` with header
`file	line	name	verdict	mirror	property	settled	reason`, one row per
modelled or excluded row, `yes`/`no`/`-` in the answer columns, and a
one-sentence reason naming what is missing for every `no`. Report the totals as
`REVIEW {FILE} FAITHFUL <n> HOLLOW <m>`.
