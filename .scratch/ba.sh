cd lean && lake build 2>&1 | tail -2
echo "=== AUDIT ==="
lake env lean Audit.lean 2>&1 | tail -20
