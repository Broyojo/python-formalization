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
# Difftests run in parallel, and every one runs, so one failing harness cannot
# hide the results of the others. Each module's agent has already run its own at
# 50000 cases on several seeds; this is the cross-module check on merged code.
cases=${AUDIT_CASES:-20000}
logs=$(mktemp -d)
ls difftest/*_diff.py | xargs -P 8 -I{} sh -c \
    'n=$(basename {}); python3 {} --cases '"$cases"' > '"$logs"'/$n.log 2>&1; echo "$? $n $(tail -1 '"$logs"'/$n.log | cut -c1-60)"' \
    | sort -k2 | tee "$logs/status"
# A module still moving to 3.15.2 is listed in coverage/difftest-migrating.txt, one
# script per line with no blank lines. Its failures show above but do not fail the
# audit. The owner removes the line once the difftest passes on 3.15.2.
touch coverage/difftest-migrating.txt
failed=$(awk '$1 != 0 { print $2 }' "$logs/status" | grep -vxFf coverage/difftest-migrating.txt | tr '\n' ' ' || true)
python3 scripts/check_bugs.py || failed="$failed check_bugs"
if [ -n "$failed" ]; then
    echo "FAIL audit:$failed"
    exit 1
fi
echo "AUDIT PASSED"
