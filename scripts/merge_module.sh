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
    # A module's own rows win in coverage/methods, and the registry is regenerated
    # after the merge anyway. Reviews always keep main's verdicts: an author must
    # never overwrite an independent review.
    conflicts=$(git diff --name-only --diff-filter=U)
    if echo "$conflicts" | grep -qv '^coverage/'; then
        echo "FAIL $branch has conflicts outside coverage/:"
        echo "$conflicts"
        git merge --abort
        exit 1
    fi
    for f in $conflicts; do
        case "$f" in
            coverage/review/*) git checkout --ours -- "$f" ;;
            *) git checkout --theirs -- "$f" ;;
        esac
        git add "$f"
    done
    git commit -q --no-edit
fi
# Batch merges set SKIP_AUDIT and run one full audit afterwards.
[ -n "${SKIP_AUDIT:-}" ] || scripts/r scripts/audit.sh
