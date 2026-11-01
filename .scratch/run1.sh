cd lean && lake build 2>&1 | grep -E "^error|Build completed|✖" | cut -c1-300 | tail -5
cd ..
timeout 500 python3 difftest/bytecode_diff.py --cases ${1:-1500} --seed ${2:-0} 2>&1 | tail -${3:-46} | cut -c1-900
