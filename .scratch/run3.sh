cd lean && lake build 2>&1 | grep -E "^error|✖" | cut -c1-400 | tail -12
timeout 200 lake env lean ../.scratch/s1.lean 2>&1 | cut -c1-500 | head -30
cd ..
timeout 280 python3 .scratch/dbg.py ${1:-2000} ${2:-5} ${3:-6} $4 2>&1 | cut -c1-600
