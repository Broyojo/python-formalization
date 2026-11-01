#!/usr/bin/env bash
# Merge a module and update coverage, one at a time: audits share a directory on
# the pod, so overlapping ones are meaningless. Usage as for merge_module.sh.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
until mkdir .git/merge.lock 2>/dev/null; do sleep 10; done
trap 'rmdir .git/merge.lock' EXIT
scripts/merge_module.sh "$1" "$2" "$3" 2>&1 |
    grep -E '^FAIL|AUDIT PASSED|Build completed|properties|not reproduced|NOT REPRO|error:|CONFLICT|touches' | cut -c1-130 | tail -8
status=${PIPESTATUS[0]}
if [ "$status" -ne 0 ]; then
    echo "MERGE GATE FAILED ($status) for $2"
    exit "$status"
fi
scripts/update_coverage.sh "$2 merged"
