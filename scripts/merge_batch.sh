#!/usr/bin/env bash
# Merge several modules, then run one audit and one coverage update. The audit
# takes long enough that one per merge is wasteful, and modules are each verified
# on their own branch first. Arguments are branch:Module:key triples.
set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
until mkdir .git/merge.lock 2>/dev/null; do sleep 10; done
trap 'rmdir .git/merge.lock' EXIT
for spec in "$@"; do
    IFS=: read -r branch mod key <<< "$spec"
    echo "=== $mod"
    SKIP_AUDIT=1 scripts/merge_module.sh "$branch" "$mod" "$key" 2>&1 | tail -3 | cut -c1-110
done
git status --short | grep -v '^??' | head -5
log=$(mktemp)
scripts/r scripts/audit.sh > "$log" 2>&1
echo "audit exit $?"
grep -E 'Build completed|properties:|^FAIL|AUDIT PASSED|not reproduced' "$log" | cut -c1-120 | tail -8
scripts/update_coverage.sh "batch merge" 2>&1 | tail -10 | cut -c1-125
