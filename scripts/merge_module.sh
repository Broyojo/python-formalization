#!/usr/bin/env bash
# Merge a module agent's branch after checking it only touched its own paths,
# then run the full audit. Usage: scripts/merge_module.sh <branch> <Module> <key>
# e.g. scripts/merge_module.sh worktree-agent-abc Fractions fractions
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
branch=$1 mod=$2 key=$3
base=$(git merge-base HEAD "$branch")

outside=$(git diff --name-only "$base" "$branch" | grep -vE \
  "^(\.gitignore|lean/PyLean/$mod\.lean|lean/PyLean/$mod/.*|difftest/${key}(_[a-z0-9_]+)?\.py|bugs/${key}-[^/]*\.yaml|coverage/registry\.tsv|coverage/methods/[^/]*\.tsv|coverage/review/[^/]*\.tsv)$" || true)
if [ -n "$outside" ]; then
    echo "FAIL $branch touches files outside its module:"
    echo "FAIL path: $outside"
    exit 1
fi
git diff --stat "$base" "$branch" | tail -1
if ! git merge --no-ff -q -m "Merge $mod module ($branch)" "$branch"; then
    # Coverage rows conflict with main's auto-filled ones: the module's own rows
    # win, and the registry is regenerated after the merge anyway.
    conflicts=$(git diff --name-only --diff-filter=U)
    if echo "$conflicts" | grep -qv '^coverage/'; then
        echo "FAIL $branch has conflicts outside coverage/:"
        echo "$conflicts"
        git merge --abort
        exit 1
    fi
    echo "$conflicts" | xargs git checkout --theirs --
    echo "$conflicts" | xargs git add
    git commit -q --no-edit
fi
# Batch merges set SKIP_AUDIT and run one full audit afterwards.
[ -n "${SKIP_AUDIT:-}" ] || scripts/r scripts/audit.sh
