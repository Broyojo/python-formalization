#!/usr/bin/env bash
# Build, audit, then run each listed difftest on three seeds in parallel, and
# print one line per run. For finishing the 3.15.2 migration; runs on the pod.
#   scripts/r scripts/migrate_check.sh [cases] [script ...]
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
cases=${1:-50000}
shift || true
scripts=("$@")
[ ${#scripts[@]} -gt 0 ] || mapfile -t scripts < coverage/difftest-migrating.txt

(cd lean && lake build 2>&1 | grep -E 'error|Build completed|Some required' | tail -8 && lake env lean Audit.lean 2>&1 | tail -1) || exit 1

logs=$(mktemp -d)
for s in "${scripts[@]}"; do
    for seed in 1 2 3; do
        echo "$s $seed"
    done
done | xargs -P 8 -L 1 sh -c '
    log='"$logs"'/$(basename "$0").$1.log
    python3 difftest/$0 --cases '"$cases"' --seed $1 > "$log" 2>&1
    echo "$? $0 seed $1: $(tail -1 "$log" | cut -c1-70)"
' | sort -k2,2 -k4,4n
echo "logs in $logs"
