#!/usr/bin/env bash
# Merge a module agent's branch after checking it only touched its own paths,
# then run the full audit. Usage: scripts/merge_module.sh <branch> <Module> <key>
# e.g. scripts/merge_module.sh worktree-agent-abc Fractions fractions
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
branch=$1 mod=$2 key=$3
base=$(git merge-base HEAD "$branch")

outside=$(git diff --name-only "$base" "$branch" | grep -vE \
  "^(lean/PyLean/$mod\.lean|lean/PyLean/$mod/|difftest/${key}_diff\.py|bugs/${key}-[^/]*\.yaml)$" || true)
if [ -n "$outside" ]; then
    echo "FAIL $branch touches files outside its module:"
    echo "$outside"
    exit 1
fi
git diff --stat "$base" "$branch" | tail -1
git merge --no-ff -q -m "Merge $mod module ($branch)" "$branch"
scripts/audit.sh
