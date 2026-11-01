cd lean && lake build 2>&1 | grep -E "error:" | cut -c1-160 | head -50
