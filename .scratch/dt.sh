echo "=== bytecode main diff, 3 seeds ==="
for sd in 0 1 2; do python3 difftest/bytecode_diff.py --cases 20000 --seed $sd 2>/dev/null | tail -1; done
echo "=== frame/iter diff, 3 seeds ==="
for sd in 0 1 2; do python3 difftest/bytecode_frame_diff.py --cases 20000 --seed $sd 2>/dev/null | tail -1; done
