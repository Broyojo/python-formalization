# python-formalization

Formalizing CPython in Lean 4 to find bugs, after
[julia-in-lean](https://github.com/MilesCranmer/julia-in-lean)
([discussion](https://discourse.julialang.org/t/formalizing-julia-in-lean-and-finding-400-bugs-in-base/140243)).

Each stdlib function gets a Lean model that follows the source line by line.
The model is differentially tested against the real interpreter until they agree.
Properties from docstrings and invariants are then stated over *all* inputs and
proven, or refuted with a counterexample that a plain Python script reproduces.

## Layout

```
lean/PyLean/Core.lean            Py α = Except PyExc α, bitLength, Py_ssize_t limits
lean/PyLean/Registry.lean        one entry per property: source, status, theorem
lean/PyLean/<Module>/Model.lean  the model, with Lib/<file>.py line citations
lean/PyLean/<Module>/*.lean      properties + proofs / refutations
lean/DiffMain.lean               `pydiff`: JSON-lines driver for differential tests
lean/Audit.lean                  checks every registry theorem's type and axioms
difftest/                        generates cases, runs CPython and `pydiff`, compares
bugs/*.yaml                      refutations with reproducers, cause, dup search
scripts/audit.sh                 build + forbidden-escape grep + audit + difftest + repros
AGENTS.md                        playbook for modelling a new module
```

## Running

```sh
cd lean && lake build && cd ..
python3 difftest/ipaddress_diff.py --cases 50000   # model vs CPython
python3 scripts/check_bugs.py                      # every bug still reproduces
scripts/audit.sh                                   # everything, fails on any open property
```

## Status

Pilot module: `Lib/ipaddress.py` integer core (network construction,
`summarize_address_range`, `subnets`, `supernet`, indexing, containment,
`overlaps`, `subnet_of`, `address_exclude`). The model agrees with CPython
3.14.7 on 200k differential cases. 11 properties: 9 proven for every input,
2 refuted (`bugs/`). The proofs hold for any address width, not just 32/128.
