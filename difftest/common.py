"""Shared driver for differential tests: Lean model (`pydiff`) vs. the running CPython.

A module's test script supplies `gen_case(rng) -> dict | None` (the dict carries
"mod" and "fn"; None skips) and `run_python(case) -> {"ok": v} | {"exc": cls, "msg": m}`,
then calls `main(gen_case, run_python)`.

Results compare as JSON. An exception matches on class name, and on message
unless the model's message starts with "~" (formatted text the model does not render).
"""

import argparse
import json
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PYDIFF = ROOT / "lean" / ".lake" / "build" / "bin" / "pydiff"


def py_result(thunk):
    """Run `thunk()` and encode its value or exception the way the model does."""
    try:
        return {"ok": thunk()}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


def run_lean(cases):
    proc = subprocess.run([str(PYDIFF)], input="".join(json.dumps(c) + "\n" for c in cases),
                          capture_output=True, text=True, check=True)
    out = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(out) == len(cases), (len(out), len(cases))
    return out


def agree(py, lean):
    if "ok" in py or "ok" in lean:
        return py == lean
    if py["exc"] != lean.get("exc"):
        return False
    return lean["msg"].startswith("~") or py["msg"] == lean["msg"]


def main(gen_case, run_python, default_cases=20000):
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=default_cases)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    cases = []
    while len(cases) < args.cases:
        c = gen_case(rng)
        if c is not None:
            cases.append(c)

    mismatches, by_fn = 0, {}
    for c, lo in zip(cases, run_lean(cases)):
        py = run_python(c)
        ok = "harness_error" not in lo and agree(py, lo)
        tot = by_fn.setdefault(c["fn"], [0, 0])
        tot[0] += 1
        tot[1] += ok
        if not ok:
            mismatches += 1
            if mismatches <= 20:
                print(f"MISMATCH {json.dumps(c)}\n  python: {py}\n  lean:   {lo}", file=sys.stderr)

    for fn, (n, good) in sorted(by_fn.items()):
        print(f"{fn:20s} {good}/{n}")
    print(f"python {sys.version.split()[0]}: {len(cases) - mismatches}/{len(cases)} agree")
    sys.exit(1 if mismatches else 0)
