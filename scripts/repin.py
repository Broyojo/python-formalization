"""Move the inventory to another CPython source, keeping only what still applies.

A row keeps its status, entry and reviews only if its body is unchanged, comments
and docstrings aside. A changed body goes back to `todo` with a `changed-in-3.15:`
note, which stops `check_coverage.py --prefill` from crediting it again until an
agent has checked the model against the new body and removed the note. A row
excluded for its own body is rechecked the same way; one excluded for its whole
file stays excluded. Reviews of changed rows stay in coverage/review/archive-3.14.7/.

This compares each function's own text. It cannot see a change in a callee, a
macro, a header, a clinic converter or a class attribute, so an unchanged row is
"nothing changed here", not "still correct". The difftest on the new interpreter
is what checks the rest.

Dry run by default; --apply writes.
  python3 scripts/repin.py vendor/cpython-3.14 vendor/cpython-3.15 [--apply]
"""

import argparse
import ast
import csv
import re
import shutil
import subprocess
import sys
import textwrap
from collections import Counter, defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import check_coverage as cc  # noqa: E402
import list_python_functions as lpf  # noqa: E402

ROOT = Path(__file__).resolve().parent.parent
METHODS = ROOT / "coverage" / "methods"
REVIEW = ROOT / "coverage" / "review"
REPORT = ROOT / "coverage" / "repin-3.15.2.tsv"
CHANGED = "changed-in-3.15:"

C_TOKEN = re.compile(r'"(?:\\.|[^"\\\n])*"|\'(?:\\.|[^\'\\\n])*\'|/\*.*?\*/|//[^\n]*', re.S)


def source_lines(path):
    text = path.read_text(encoding="utf8", errors="replace")
    # ast counts only newlines; c_rows counted with splitlines, so slice the same way.
    return text.split("\n") if path.suffix == ".py" else text.splitlines()


def normal_c(text):
    kept = C_TOKEN.sub(lambda m: m.group() if m.group()[0] in "\"'" else " ", text)
    return re.sub(r"\s+", " ", kept).strip()


def normal_py(text):
    try:
        tree = ast.parse(textwrap.dedent(text))
    except SyntaxError:
        return re.sub(r"\s+", " ", text).strip()
    node = tree.body[0] if tree.body else None
    if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and ast.get_docstring(node) is not None:
        node.body = node.body[1:] or [ast.Pass()]
    return ast.dump(tree)


def normal_gram(text):
    return re.sub(r"\s+", " ", re.sub(r"(?m)^\s*#.*$", " ", text)).strip()


def bodies(path, rel, rows):
    """Normal form of each (line, end) in `rows`. Opcode and grammar rows record only
    their first line, so those run to the row after them."""
    lines = source_lines(path)
    starts = sorted({line for line, _ in rows})
    following = dict(zip(starts, starts[1:] + [len(lines) + 1]))
    normal = {".py": normal_py, ".gram": normal_gram}.get(path.suffix, normal_c)
    out = {}
    for line, end in rows:
        stop = following[line] - 1 if line == end else end
        out[line, end] = normal("\n".join(lines[line - 1:stop]))
    return out


def old_inventory():
    return {p.name: cc.read_rows(p) for p in sorted(METHODS.glob("*.tsv"))}


def new_inventory(src):
    """{rel: [row...]} from the new source, with a body and the file's exclusion reason."""
    out = {}
    for path, rel, lister, patterns in lpf.list_sources(src):
        try:
            found = lister(path, rel)
        except SyntaxError:
            print(f"skipped, does not parse: {rel}", file=sys.stderr)
            continue
        if not found:
            continue
        reason = lpf.exclusion(rel, patterns)
        forms = bodies(path, rel, [(line, end) for line, end, _, _ in found])
        out[rel] = [{"file": rel, "line": str(line), "endline": str(end), "name": name,
                     "signature": sig.replace("\t", " "), "body": forms[line, end],
                     "reason": reason} for line, end, name, sig in found]
    return out


def pair_rows(old_rows, new_rows):
    """Match on (name, signature), then on name alone in file order."""
    free = list(new_rows)
    pairs = []
    rest = []
    for row in old_rows:
        hit = next((n for n in free if (n["name"], n["signature"]) == (row["name"], row["signature"])), None)
        if hit:
            free.remove(hit)
            pairs.append((row, hit))
        else:
            rest.append(row)
    unmatched = []
    for row in rest:
        hit = next((n for n in free if n["name"] == row["name"]), None)
        if hit:
            free.remove(hit)
            pairs.append((row, hit))
        else:
            unmatched.append(row)
    return pairs, unmatched, free


def settle(old, new, same, tally):
    """The row for `new`, given its 3.14.7 row. Returns the row dict."""
    row = {k: new[k] for k in cc.FIELDS if k in new}
    row.update(status=old["status"], entry=old["entry"], note=old["note"])
    if same:
        tally["same", old["status"]] += 1
        return row
    tally["changed", old["status"]] += 1
    if old["status"] == "modelled":
        row.update(status="todo", entry="", note=f"{CHANGED} was {old['entry']}")
    elif old["status"] == "excluded" and not new["reason"]:
        row.update(status="todo", note=f"{CHANGED} was excluded: {old['note']}")
    elif old["status"] == "todo":
        row["note"] = f"{CHANGED} {old['note']}".strip()
    return row


def repin(old_src, new_src):
    new = new_inventory(new_src)
    used = set()
    results, line_of, report = defaultdict(list), {}, []
    tally = Counter()
    orphans = []
    old = old_inventory()
    by_rel = defaultdict(list)
    for rows in old.values():
        for row in rows:
            by_rel[row["file"]].append(row)

    for rel, old_rows in sorted(by_rel.items()):
        path = old_src / rel
        forms = bodies(path, rel, [(int(r["line"]), int(r["endline"])) for r in old_rows]) if path.exists() else {}
        for row in old_rows:
            row["body"] = forms.get((int(row["line"]), int(row["endline"])), "")
        pairs, unmatched, _ = pair_rows(old_rows, new.get(rel, []))
        for old_row, new_row in pairs:
            used.add(id(new_row))
            same = old_row["body"] == new_row["body"]
            settled = settle(old_row, new_row, same, tally)
            results[rel].append((new_row, settled))
            if same:
                line_of[rel, old_row["line"]] = (rel, new_row["line"])
            else:
                report.append(("changed", rel, old_row["line"], new_row["line"], old_row["name"],
                               old_row["status"], old_row["entry"]))
        orphans.extend(unmatched)

    # A function that left its file with its body intact has moved.
    spare = defaultdict(list)
    for rel, rows in new.items():
        for row in rows:
            if id(row) not in used:
                spare[row["name"], row["body"]].append(row)
    for row in orphans:
        hits = spare.get((row["name"], row["body"]))
        if hits:
            target = hits.pop(0)
            used.add(id(target))
            results[target["file"]].append((target, settle(row, target, True, tally)))
            line_of[row["file"], row["line"]] = (target["file"], target["line"])
            report.append(("moved", row["file"], row["line"], f"{target['file']}:{target['line']}",
                           row["name"], row["status"], row["entry"]))
        else:
            tally["removed", row["status"]] += 1
            report.append(("removed", row["file"], row["line"], "", row["name"], row["status"], row["entry"]))

    for rel, rows in new.items():
        for row in rows:
            if id(row) not in used:
                status = "excluded" if row["reason"] else "todo"
                tally["new", status] += 1
                fresh = {k: row[k] for k in cc.FIELDS if k in row}
                # Blocked too: prefill reads a registry `delta_new` as `delta_new_impl`,
                # and that entry describes the 3.14.7 function, not this new one.
                fresh.update(status=status, entry="", note=row["reason"] or f"{CHANGED} new function")
                results[rel].append((row, fresh))
                report.append(("new", rel, "", row["line"], row["name"], status, ""))
    return results, line_of, report, tally


def rewrite_reviews(line_of):
    """Carry reviews of unchanged rows to their new lines; the archive keeps every original."""
    archive = REVIEW / "archive-3.14.7"
    archive.mkdir(exist_ok=True)
    kept = dropped = 0
    for path in sorted(REVIEW.glob("*.tsv")):
        shutil.copy2(path, archive / path.name)
        with path.open(newline="") as f:
            reader = csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\")
            fields, rows = reader.fieldnames, list(reader)
        out = []
        for row in rows:
            target = line_of.get((row["file"], row["line"]))
            if target:
                row["file"], row["line"] = target
                out.append(row)
                kept += 1
            else:
                dropped += 1
        with path.open("w", newline="") as f:
            writer = csv.DictWriter(f, fields, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\",
                                    lineterminator="\n")
            writer.writeheader()
            writer.writerows(out)
    return kept, dropped


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old", type=Path)
    ap.add_argument("new", type=Path)
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    results, line_of, report, tally = repin(args.old.resolve(), args.new.resolve())
    for key, count in sorted(tally.items()):
        print(f"{key[0]:8s} {key[1]:9s} {count}")
    modelled = {k: v for k, v in tally.items() if k[1] == "modelled"}
    print("modelled rows:", modelled)
    if not args.apply:
        return

    for path in METHODS.glob("*.tsv"):
        path.unlink()
    for rel, pairs in results.items():
        rows = sorted((settled for _, settled in pairs), key=lambda r: int(r["line"]))
        cc.write_rows(lpf.manifest_path(rel), rows)
    print("reviews kept, dropped:", rewrite_reviews(line_of))
    with REPORT.open("w") as f:
        f.write("kind\tfile\told_line\tnew_line\tname\tstatus\tentry\n")
        for row in sorted(report):
            f.write("\t".join(map(str, row)) + "\n")
    commit = subprocess.run(["git", "-C", str(args.new), "rev-parse", "HEAD"], capture_output=True,
                            text=True, check=True).stdout.strip()
    (ROOT / "coverage" / "SOURCE_COMMIT").write_text(commit + "\n")


if __name__ == "__main__":
    main()
