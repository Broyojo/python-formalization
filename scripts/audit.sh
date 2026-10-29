#!/usr/bin/env bash
# Build the Lean project, reject forbidden proof escapes, audit the registry,
# re-run the differential tests, and check that every bug still reproduces.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."

(cd lean && lake build)

if grep -rnwE 'sorry|admit|native_decide|bv_decide|ofReduceBool|implemented_by|extern' \
    --include='*.lean' lean/PyLean lean/PyLean.lean; then
    echo "FAIL forbidden proof escape found (see lines above)"
    exit 1
fi

(cd lean && lake env lean Audit.lean)
for t in difftest/*_diff.py; do python3 "$t" --cases 50000; done
python3 scripts/check_bugs.py
