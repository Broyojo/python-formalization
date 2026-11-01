"""Validate coverage/methods/*.tsv against the registry and report whole-Python coverage.

Export the registry first, on the pod:
  scripts/r bash -c 'cd lean && lake env lean Report.lean' > coverage/registry.tsv

  python3 scripts/check_coverage.py             validate and print totals
  python3 scripts/check_coverage.py --prefill   settle todo rows from registry function names

--prefill settles a row only on a unique match, in the entry's own file first
and then across the whole manifest. Ambiguous names become `candidates:` notes
for a person or review agent to settle. Exits 1 on a malformed row, and
with --strict while any todo remains.

`modelled` is a claim by the author of the entry. It counts as reviewed only
once coverage/review/ says FAITHFUL (see coverage/REVIEW_PROMPT.md).
"""

import argparse
import csv
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
METHODS = ROOT / "coverage" / "methods"
REVIEW = ROOT / "coverage" / "review"
FIELDS = ["file", "line", "endline", "name", "signature", "status", "entry", "note"]
EXCLUSION_REASONS = ("no-behaviour:", "deprecated:", "internal-bootstrap:", "platform:",
                     "vendored:", "test-support:", "generated:", "trivial:")


def read_registry():
    registry = {}
    for number, line in enumerate((ROOT / "coverage" / "registry.tsv").read_text().splitlines(), 1):
        fields = line.split("\t")
        if len(fields) != 4 or fields[0] in registry:
            raise ValueError(f"registry.tsv:{number}: malformed or duplicate entry")
        registry[fields[0]] = {"status": fields[1], "file": fields[2],
                               "fns": [f for f in fields[3].split(",") if f]}
    return registry


def read_rows(path):
    with path.open(newline="") as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\"))


def write_rows(path, rows):
    with path.open("w", newline="") as f:
        writer = csv.DictWriter(f, FIELDS, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\",
                                lineterminator="\n")
        writer.writeheader()
        writer.writerows(rows)


def row_problems(row, registry):
    problems = []
    entries = [e for e in row["entry"].split(",") if e]
    if row["status"] == "modelled":
        if not entries:
            problems.append("modelled without entry")
        for entry in entries:
            if entry not in registry:
                problems.append(f"missing registry id {entry}")
            elif registry[entry]["status"] not in {"proven", "refuted"}:
                problems.append(f"registry id {entry} is {registry[entry]['status']}")
    elif row["status"] == "excluded":
        if entries:
            problems.append("excluded with entry")
        if not any(row["note"].startswith(r) and row["note"][len(r):].strip()
                   for r in EXCLUSION_REASONS):
            problems.append("excluded without allowed reason and justification")
    elif row["status"] == "todo":
        if entries:
            problems.append("todo with entry")
    else:
        problems.append(f"unknown status {row['status']!r}")
    return problems


def name_forms(fn):
    """Spellings of a registry function name. `math.isqrt` and `int.to_bytes`
    are Python names; the C definitions are math_isqrt(_impl), int_to_bytes(_impl)."""
    fn = re.sub(r"\(.*$", "", fn).strip()
    fn = re.sub(r"^(C|Py|py|c)\s+", "", fn)
    flat = fn.replace(".", "_")
    forms = [fn, flat, flat + "_impl", fn.split(".")[-1]]
    return list(dict.fromkeys(forms))


def read_reviews():
    """(file, line) of reviewed rows, split by verdict."""
    faithful, hollow = set(), {}
    for path in sorted(REVIEW.glob("*.tsv")) if REVIEW.exists() else []:
        for row in read_rows(path):
            key = (row["file"], row["line"])
            if row["verdict"] == "FAITHFUL":
                faithful.add(key)
            else:
                hollow[key] = row["reason"]
    return faithful, hollow


def withdraw_hollow(by_file, hollow):
    """A row a review found hollow is todo until its review is redone."""
    for rows in by_file.values():
        for row in rows:
            reason = hollow.get((row["file"], row["line"]))
            if reason is not None and row["status"] != "todo":
                row["status"], row["entry"] = "todo", ""
                row["note"] = "review: " + reason


def module_files(registry):
    """Files each module's entries name, by id prefix: a credit stays inside them."""
    files = defaultdict(set)
    for entry, info in registry.items():
        files[entry.split("-")[0]].add(info["file"])
    return files


def withdraw_stale(by_file, registry):
    """A modelled row keeps only entries that exist, are settled and still name it."""
    for rows in by_file.values():
        for row in rows:
            if row["status"] != "modelled":
                continue
            keep = []
            for entry in filter(None, row["entry"].split(",")):
                info = registry.get(entry)
                if info and info["status"] in {"proven", "refuted"} and any(
                        form in (row["name"], row["name"].split(".")[-1])
                        for fn in info["fns"] for form in name_forms(fn)):
                    keep.append(entry)
            row["entry"] = ",".join(keep)
            if not keep:
                row["status"] = "todo"


def prefill(by_file, registry, hollow):
    allowed = module_files(registry)
    index = defaultdict(list)
    for rows in by_file.values():
        for row in rows:
            index[row["name"]].append(row)
            index[row["name"].split(".")[-1]].append(row)
    settled, candidates = defaultdict(set), defaultdict(set)
    unmatched = Counter()
    for entry, info in registry.items():
        if info["status"] not in {"proven", "refuted"}:
            continue
        for fn in info["fns"]:
            found = None
            for form in name_forms(fn):
                matches = [r for r in {id(r): r for r in index.get(form, [])}.values()
                           if r["file"] in allowed[entry.split("-")[0]]]
                local = [r for r in matches if r["file"] == info["file"]]
                if len(local) == 1 or (not local and len(matches) == 1):
                    found = (local or matches)[0]
                    break
                for row in local or matches:
                    candidates[id(row)].add(entry)
            if found:
                settled[id(found)].add(entry)
            elif not any(index.get(form) for form in name_forms(fn)):
                unmatched[fn] += 1
    for rows in by_file.values():
        for row in rows:
            if row["status"] != "todo" or (row["file"], row["line"]) in hollow:
                continue
            if settled[id(row)]:
                row["status"] = "modelled"
                row["entry"] = ",".join(sorted(settled[id(row)]))
            elif candidates[id(row)]:
                note = "candidates:" + ",".join(sorted(candidates[id(row)]))
                row["note"] = "; ".join(filter(None, [row["note"].split("candidates:")[0].strip("; "), note]))
    if unmatched:
        print(f"{len(unmatched)} registry function names match no row, e.g. "
              f"{sorted(unmatched)[:12]}", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--prefill", action="store_true")
    ap.add_argument("--strict", action="store_true")
    args = ap.parse_args()

    registry = read_registry()
    by_file = {p: read_rows(p) for p in sorted(METHODS.glob("*.tsv"))}
    reviewed, hollow = read_reviews()
    if args.prefill:
        withdraw_hollow(by_file, hollow)
        withdraw_stale(by_file, registry)
        prefill(by_file, registry, hollow)
        for path, rows in by_file.items():
            write_rows(path, rows)

    problems = 0
    totals = defaultdict(Counter)
    claimed = set()
    for path, rows in by_file.items():
        for row in rows:
            for problem in row_problems(row, registry):
                print(f"{path.name}:{row['line']} {row['name']}: {problem}", file=sys.stderr)
                problems += 1
            area = row["file"].split("/")[0]
            totals[area][row["status"]] += 1
            totals[area]["faithful"] += (row["file"], row["line"]) in reviewed
            claimed.update(e for e in row["entry"].split(",") if e)

    print(f"{'area':10s} {'rows':>7s} {'modelled':>9s} {'faithful':>9s} {'excluded':>9s} {'todo':>7s}")
    grand = Counter()
    for area, c in sorted(totals.items()):
        rows = c["modelled"] + c["excluded"] + c["todo"]
        print(f"{area:10s} {rows:7d} {c['modelled']:9d} {c['faithful']:9d} {c['excluded']:9d} {c['todo']:7d}")
        grand.update(c)
    rows = grand["modelled"] + grand["excluded"] + grand["todo"]
    in_scope = rows - grand["excluded"]
    print(f"{'total':10s} {rows:7d} {grand['modelled']:9d} {grand['faithful']:9d} "
          f"{grand['excluded']:9d} {grand['todo']:7d}")
    print(f"{100 * grand['modelled'] / max(in_scope, 1):.1f}% of in-scope rows modelled, "
          f"{100 * grand['faithful'] / max(in_scope, 1):.1f}% reviewed faithful; "
          f"{len(set(registry) - claimed)} registry entries cover no row; "
          f"{len(hollow)} rows withdrawn by review")
    sys.exit(1 if problems or (args.strict and grand["todo"]) else 0)


if __name__ == "__main__":
    main()
