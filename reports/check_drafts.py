"""Run every ```python block in the issue drafts, so what we post is what we tested.

  python3 reports/check_drafts.py [--python EXE ...]

Each block runs in its own process (isolated mode, 60 s timeout); a block whose first line says
PYTHONMALLOC=debug uses -s -P and a cleaned Python environment, since -I ignores PYTHONMALLOC.
Prints, per block, the exit status and the last lines of
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
    ap.add_argument("--full-output", action="store_true", help="save all output lines for review")
    ap.add_argument("--draft", action="append", help="check only this relative draft path (repeatable)")
    args = ap.parse_args()
    exes = args.python or [sys.executable]
    paths = sorted((DRAFTS / "single").glob("*.md")) + sorted((DRAFTS / "group").glob("*.md"))
    if args.draft:
        unknown = set(args.draft) - {p.relative_to(DRAFTS).as_posix() for p in paths}
        if unknown:
            ap.error("unknown draft(s): " + ", ".join(sorted(unknown)))
        paths = [p for p in paths if p.relative_to(DRAFTS).as_posix() in args.draft]
    for path in paths:
        blocks = re.findall(r"```python\n(.*?)```", path.read_text(), re.S)
        for i, code in enumerate(blocks, 1):
            env = dict(os.environ)
            flags = ["-I"]
            if "PYTHONMALLOC=debug" in code.splitlines()[0]:
                env = {k: v for k, v in env.items() if not k.startswith("PYTHON")}
                env["PYTHONMALLOC"] = "debug"
                flags = ["-s", "-P"]
            for exe in exes:
                try:
                    r = subprocess.run([exe, *flags, "-u", "-c", code], capture_output=True, text=True,
                                       timeout=60, env=env, cwd="/tmp")
                    status = r.returncode
                    lines = (r.stdout + r.stderr).strip().splitlines()
                    tail = lines if args.full_output else lines[-3:]
                except subprocess.TimeoutExpired:
                    status, tail = "timeout", []
                print(f"{path.parent.name}/{path.name} block {i} [{Path(exe).name}] status {status}")
                for line in tail:
                    print("    " + line[:200])
            sys.stdout.flush()


if __name__ == "__main__":
    main()
