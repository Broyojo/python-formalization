#!/usr/bin/env bash
# After a merge: export the registry on the pod, settle coverage rows and commit.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
scripts/r bash -c 'cd lean && lake env lean Report.lean' 2>/dev/null > coverage/registry.tsv
python3 scripts/check_coverage.py --prefill 2>&1 | tail -9 | cut -c1-100
git add -A coverage
git commit -qm "Update coverage: ${1:-after merge}

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01YWjP4qJwNFDpaToxpZGnPi"
