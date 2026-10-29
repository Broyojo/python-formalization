"""Run every bugs/*.yaml reproducer on this Python and check it still reproduces.

Each reproducer must print `REPRODUCED <id>` when the bug is present. Usage:
  python3 scripts/check_bugs.py [--python /path/to/python] [bug-id ...]
Exits non-zero if a bug no longer reproduces (fixed upstream, or a broken reproducer).
"""

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def load_reproducer(path):
    # Minimal YAML reading: the `reproducer: |` block scalar, without a YAML dependency.
    text = path.read_text()
    m = re.search(r"^reproducer: \|\n((?:  .*\n|\n)+)", text, re.M)
    if not m:
        raise ValueError(f"{path.name}: no `reproducer: |` block")
    return "".join(line[2:] if line.startswith("  ") else line for line in m.group(1).splitlines(True))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--python", default=sys.executable)
    ap.add_argument("ids", nargs="*")
    args = ap.parse_args()

    version = subprocess.run([args.python, "-c", "import sys; print(sys.version.split()[0])"],
                             capture_output=True, text=True, check=True).stdout.strip()
    failures = 0
    for path in sorted((ROOT / "bugs").glob("*.yaml")):
        bug_id = path.stem
        if args.ids and bug_id not in args.ids:
            continue
        r = subprocess.run([args.python, "-I", "-c", load_reproducer(path)],
                           capture_output=True, text=True, timeout=120)
        ok = f"REPRODUCED {bug_id}" in r.stdout
        failures += not ok
        print(f"{'REPRODUCED' if ok else 'NOT REPRODUCED':15s} {bug_id}")
        if not ok:
            print(r.stdout + r.stderr)
    print(f"python {version}: {failures} not reproduced")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
