"""Export the numbers behind the progress dashboard as JSON files in dashboard/data/.

Reads only the repository (coverage tables, registry export, bug records, git history), so it is
cheap enough to run locally. Run from anywhere: python3 dashboard/export.py
"""

import collections
import json
import re
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "dashboard" / "data"


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def coverage_areas():
    out = subprocess.run([sys.executable, "scripts/check_coverage.py"], cwd=ROOT, capture_output=True,
                         text=True).stdout
    rows = []
    for line in out.splitlines():
        m = re.match(r"^(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)$", line.strip())
        if m and m.group(1) != "total":
            area, total, modelled, faithful, excluded, todo = m.groups()
            total, modelled, faithful, excluded, todo = map(int, (total, modelled, faithful, excluded, todo))
            rows.append({"area": area, "rows": total, "in_scope": total - excluded, "modelled": modelled,
                         "reviewed": faithful, "excluded": excluded, "todo": todo})
    return rows


def coverage_history():
    log = git("log", "--format=%H %cI", "--", "coverage/methods")
    hist = []
    for line in reversed(log.splitlines()):
        sha, when = line.split()
        counts = collections.Counter()
        for status in ("modelled", "excluded"):
            res = subprocess.run(["git", "grep", "-c", "-P", rf"\t{status}\t", sha, "--", "coverage/methods/"],
                                 cwd=ROOT, capture_output=True, text=True).stdout
            counts[status] = sum(int(x.rsplit(":", 1)[1]) for x in res.splitlines() if x)
        res = subprocess.run(["git", "grep", "-c", "-P", r"\t", sha, "--", "coverage/methods/"],
                             cwd=ROOT, capture_output=True, text=True).stdout
        total = sum(int(x.rsplit(":", 1)[1]) - 1 for x in res.splitlines() if x)  # minus header
        hist.append({"at": when, "commit": sha[:8], "modelled": counts["modelled"],
                     "in_scope": total - counts["excluded"]})
    # one point per hour: the last of the hour
    by_hour = {}
    for h in hist:
        by_hour[h["at"][:13]] = h
    return [by_hour[k] for k in sorted(by_hour)]


def properties():
    per = collections.defaultdict(collections.Counter)
    for line in (ROOT / "coverage" / "registry.tsv").read_text().splitlines():
        parts = line.split("\t")
        if len(parts) < 2:
            continue
        module = parts[0].split("-")[0]
        per[module][parts[1]] += 1
    return [{"module": m, "proven": c["proven"], "refuted": c["refuted"], "open": c["open"],
             "total": sum(c.values())} for m, c in sorted(per.items(), key=lambda kv: -sum(kv[1].values()))]


def properties_history():
    log = git("log", "--format=%H %cI", "--", "coverage/registry.tsv")
    by_hour = {}
    for line in reversed(log.splitlines()):
        sha, when = line.split()
        c = collections.Counter()
        for row in git("show", f"{sha}:coverage/registry.tsv").splitlines():
            parts = row.split("\t")
            if len(parts) > 1:
                c[parts[1]] += 1
        by_hour[when[:13]] = {"at": when, "proven": c["proven"], "refuted": c["refuted"], "open": c["open"]}
    return [by_hour[k] for k in sorted(by_hour)]


def field(text, name):
    m = re.search(rf"^{name}:\s*(.*)$", text, re.M)
    if not m:
        return ""
    v = m.group(1).strip()
    if len(v) >= 2 and v[0] == v[-1] and v[0] in "\"'":
        v = v[1:-1]
    return v


DUP = re.compile(r'relation:\s*"?(duplicate|same bug|same defect|same root)', re.I)


def known_upstream(text):
    """True when the record names an upstream issue for this same defect (not a nearby one)."""
    m = re.search(r"^duplicates:\s*\n((?:[ \t].*\n?)*)", text, re.M)
    if not m:
        return False
    block = m.group(1)
    if DUP.search(block):
        return True
    im = re.search(r"^\s*issues:\s*(\[.+\])\s*$", block, re.M)
    return bool(im and im.group(1) != "[]" and re.search(r"duplicate", block, re.I))


def bugs():
    added = {}
    log = git("log", "--diff-filter=A", "--format=@%cI", "--name-only", "--", "bugs/")
    day = None
    for line in log.splitlines():
        if line.startswith("@"):
            day = line[1:]
        elif line.startswith("bugs/") and line.endswith(".yaml"):
            added[Path(line).stem] = day  # log is newest first; keep overwriting to get the first add
    gone = set((ROOT / "coverage" / "gone-in-3.15.txt").read_text().split())
    rows = []
    for p in sorted((ROOT / "bugs").glob("*.yaml")):
        t = p.read_text()
        bid = field(t, "id") or p.stem
        rows.append({"id": bid, "module": field(t, "module") or bid.split("-")[0],
                     "priority": field(t, "priority") or "?", "kind": field(t, "kind") or "?",
                     "title": field(t, "title"), "added": (added.get(p.stem) or "")[:10],
                     "added_at": added.get(p.stem, ""),
                     "upstream": "already reported" if known_upstream(t) else "new",
                     "on_3_15_2": "no (3.14.7 only)" if bid in gone else "yes"})
    return rows


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now(timezone.utc).isoformat(timespec="seconds")
    data = {"coverage_areas": coverage_areas(), "coverage_history": coverage_history(),
            "properties": properties(), "properties_history": properties_history(), "bugs": bugs()}
    for name, rows in data.items():
        (OUT / f"{name}.json").write_text(json.dumps({"rows": rows}, indent=0))
        print(name, len(rows))
    print("exported at", stamp)


if __name__ == "__main__":
    main()
