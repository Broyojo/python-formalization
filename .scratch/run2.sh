cd lean && lake build 2>&1 | grep -E "^error|✖" | cut -c1-300 | tail -5
cd ..
timeout 500 python3 .scratch/dbg.py ${1:-1500} ${2:-0} ${3:-8} $4 2>&1 | cut -c1-600
