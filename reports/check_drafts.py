"""Run every ```python block in the issue drafts, so what we post is what we tested.

  python3 reports/check_drafts.py [--python EXE ...]

Each block runs in its own process (isolated mode, 60 s timeout); a block whose first line says
PYTHONMALLOC=debug runs with that setting. Prints, per block, the exit status and the last lines of
output; a negative status is a signal (-11 SIGSEGV, -6 SIGABRT, -8 SIGFPE).
"""

import argparse
import os
import re
import subprocess
import sys
from pathlib import Path

DRAFTS = Path(__file__).resolve().parent / "drafts"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--python", action="append", default=None)
    args = ap.parse_args()
    exes = args.python or [sys.executable]
    for path in sorted((DRAFTS / "single").glob("*.md")) + sorted((DRAFTS / "group").glob("*.md")):
        blocks = re.findall(r"```python\n(.*?)```", path.read_text(), re.S)
        for i, code in enumerate(blocks, 1):
            env = dict(os.environ)
            if "PYTHONMALLOC=debug" in code.splitlines()[0]:
                env["PYTHONMALLOC"] = "debug"
            for exe in exes:
                try:
                    r = subprocess.run([exe, "-I", "-c", code], capture_output=True, text=True,
                                       timeout=60, env=env, cwd="/tmp")
                    status = r.returncode
                    tail = (r.stdout + r.stderr).strip().splitlines()[-3:]
                except subprocess.TimeoutExpired:
                    status, tail = "timeout", []
                print(f"{path.parent.name}/{path.name} block {i} [{Path(exe).name}] status {status}")
                for line in tail:
                    print("    " + line[:200])
            sys.stdout.flush()


if __name__ == "__main__":
    main()
