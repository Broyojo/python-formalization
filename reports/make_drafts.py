"""Turn bug records into draft CPython issues for human review.

Reads reports/triage.tsv (proposed_action per record) and bugs/*.yaml, and writes:
  reports/drafts/single/<name>.md       one issue per hand-written body in reports/issue_text/
  reports/drafts/group/<module>-<n>.md  grouped issues, at most GROUP_MAX findings each
  reports/drafts/INDEX.md               checklist: tick a box to approve that draft for filing
Nothing here talks to GitHub; reports/file_issues.py files the ticked drafts.
Run: python3 reports/make_drafts.py
"""

import csv
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DRAFTS = ROOT / "reports" / "drafts"
PAGE = "https://broyojo.com/python-formalization/"
REPO = "https://github.com/Broyojo/python-formalization"
GROUP_MAX = 8
GROUP_PRIORITIES = {"P3"}  # P4/P5 stay in bugs/ and are offered in the Discourse post, not filed

MODULE_NAMES = {"corelibs": "functools, enum, random and other core library modules", "textlibs": "text and binary codecs",
                "datetime": "datetime", "bytesobj": "bytes, bytearray and memoryview", "pyio": "io and _pyio",
                "typeobj": "type objects", "pygrammar": "the parser and grammar", "pickle": "pickle",
                "decimal": "decimal", "accel": "C accelerator modules", "sequences": "array and collections",
                "json": "json", "bytecode": "the bytecode interpreter", "binary64": "float and complex",
                "calstat": "calendar and statistics", "ipaddress": "ipaddress", "itertools": "itertools",
                "longobj": "int", "mathint": "math", "fractions": "fractions", "unicodeobj": "str",
                "dictset": "dict and set", "getargs": "argument parsing", "rangeslice": "range and slice"}


def field(t, k):
    m = re.search(rf"^{k}:\s*\|\s*\n((?:[ ]{{2}}.*\n|[ ]*\n)+)", t, re.M)
    if m:
        lines = m.group(1).splitlines()
        return "\n".join(l[2:] if l.startswith("  ") else l for l in lines).strip()
    m = re.search(rf"^{k}:\s*(.+)$", t, re.M)
    return m.group(1).strip().strip('"') if m else ""


def inner_code(repro):
    """The script inside a subprocess wrapper (code = r'''...'''), without REPRODUCED checks."""
    m = re.search(r'code\s*=\s*r?("""|\'\'\')\n(.*?)\1', repro, re.S)
    code = m.group(2) if m else repro
    keep = [l for l in code.splitlines() if "REPRODUCED" not in l
            and not re.match(r"\s*import resource", l) and "RLIMIT_CORE" not in l]
    while keep and re.match(r"\s*if .*:\s*$", keep[-1]):
        keep.pop()
    return "\n".join(keep).strip()


def clean(s):
    s = " ".join(s.split())
    s = re.sub(r"\s*REPRODUCED( by check_bugs\.py)?\.?", "", s)
    s = re.sub(r"@3\.14\.7:", ":", s)  # flagged in INDEX; citations to re-check
    return s.strip()


def first_para(s):
    return s.split("\n\n")[0].strip()


TEXT = ROOT / "reports" / "issue_text"
VV = ROOT / "reports" / "python-VV.txt"  # output of `python3 -VV` on the test machine
FOOTER = ("Found while building a Lean 4 model of CPython ({page}). I used AI tools (Claude) to find this "
          "and draft the report, then reproduced it on 3.15.2 and on main and checked the text myself.")


def single(path):
    """A hand-written body from reports/issue_text/, inside the headings of CPython's issue forms."""
    text = path.read_text()
    title = re.search(r"<!-- title: (.*?) -->", text).group(1)
    form = re.search(r"<!-- form: (\w+) -->", text).group(1)
    records = re.search(r"<!-- records: (.*?) -->", text).group(1).split()
    desc = re.sub(r"<!-- .*? -->\n", "", text).strip()
    body = ["### Crash report" if form == "crash" else "### Bug report", "", desc, "",
            "### CPython versions tested on:", "", "3.15, CPython main branch", "",
            "### Operating systems tested on:", "", "Linux", ""]
    if form == "crash":
        vv = VV.read_text().strip() if VV.exists() else "TODO: output of python3 -VV"
        body += ["### Output from running 'python -VV' on the command line:", "", vv, ""]
    links = ", ".join(f"[{r}]({REPO}/blob/main/bugs/{r}.yaml)" for r in records)
    body += ["---", FOOTER.format(page=PAGE) + " Record: " + links]
    return title, records, "\n".join(body) + "\n"


def group(mod, items, part, parts):
    name = MODULE_NAMES.get(mod, mod)
    suffix = f" (part {part} of {parts})" if parts > 1 else ""
    title = f"Small inconsistencies in {name} found by a formal model{suffix}"
    body = ["### Bug report", "",
            f"While modelling CPython 3.15.2 in Lean 4 ({PAGE}), we found the cases below, where the "
            "implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with "
            "its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on "
            "3.15.2 and on main. They are grouped so they can be triaged together; we're happy to split "
            "out any that deserve their own issue.", ""]
    for i, (bid, t) in enumerate(items, 1):
        mi = field(t, "maybe_intended")
        note = f"\n\n*May be intended:* {clean(first_para(mi))}" if re.match(r"(?i)(likely|probably|yes|possibly)", mi) else ""
        body += [f"#### {i}. {clean(field(t, 'title'))}", "", clean(first_para(field(t, "summary"))) + note, "",
                 "<details><summary>Reproducer</summary>", "", "```python", inner_code(field(t, "reproducer")),
                 "```", "", "</details>", ""]
    body += ["### CPython versions tested on:", "", "3.15, CPython main branch", "",
             "### Operating systems tested on:", "", "Linux", "", "---",
             "I used AI tools (Claude) to find these and draft the report; each case was reproduced on 3.15.2 "
             f"and on main and the text checked before filing. Records: {REPO}/tree/main/bugs"]
    return title, "\n".join(body) + "\n"


def main():
    rows = list(csv.DictReader(open(ROOT / "reports/triage.tsv"), delimiter="\t"))
    for d in ("single", "group"):
        (DRAFTS / d).mkdir(parents=True, exist_ok=True)
        for old in (DRAFTS / d).glob("*.md"):
            old.unlink()
    groups, stale, minor, alone = {}, [], [], {}
    for r in rows:
        a = r["proposed_action"]
        if a == "file-alone":
            alone[r["id"]] = r["priority"]
        elif a.startswith("group:") and r["priority"] in GROUP_PRIORITIES:
            groups.setdefault(r["module"], []).append((r["id"], (ROOT / "bugs" / f"{r['id']}.yaml").read_text()))
        elif a.startswith("group:") or a == "ask-in-group":
            minor.append(r["id"])
        elif a == "check-main":
            stale.append(r["id"])

    index = ["# Draft issues for python/cpython", "",
             "Change `[ ]` to `[x]` for each draft you have read and can explain in your own words "
             "(CPython's AI-tools policy requires it). `python3 reports/file_issues.py` files only ticked drafts "
             "and does nothing without `--go`.", "", "## Single issues", ""]
    covered = set()
    for path in sorted(TEXT.glob("*.md")):
        title, records, body = single(path)
        covered.update(records)
        (DRAFTS / "single" / path.name).write_text(f"<!-- title: {title} -->\n" + body)
        pri = min(alone.get(r, "P9") for r in records)
        index.append(f"- [ ] {pri if pri != 'P9' else ''} [{title}](single/{path.name})")
    todo = sorted(set(alone) - covered)
    index += ["", f"## Still to write ({len(todo)})", "",
              "Each has a full record with a reproducer and the cause. Write the body as "
              "reports/issue_text/<name>.md (copy the three header lines of an existing one), then run this "
              "script again.", ""]
    index += [f"- {alone[r]} [{r}](../../bugs/{r}.yaml)" for r in todo]

    index += ["", f"## Grouped issues (at most {GROUP_MAX} findings each)", ""]
    ng = 0
    for mod, items in sorted(groups.items(), key=lambda x: -len(x[1])):
        chunks = [items[i:i + GROUP_MAX] for i in range(0, len(items), GROUP_MAX)]
        for n, chunk in enumerate(chunks, 1):
            title, body = group(mod, chunk, n, len(chunks))
            name = f"{mod}-{n}.md"
            (DRAFTS / "group" / name).write_text(f"<!-- title: {title} -->\n" + body)
            index.append(f"- [ ] [{title}](group/{name})")
            ng += 1
    index += ["", f"## Waiting on a re-run on main ({len(stale)})", "",
              "These are filed only after scripts/check_bugs.py confirms them on main: " + ", ".join(stale) + ".", "",
              f"## Not filed at launch ({len(minor)} minor or possibly intended findings)", "",
              "P4/P5 findings, and ones whose record says they are probably intended, stay in bugs/ and are offered "
              "in the Discourse post. Duplicates of existing issues and 3.14-only behaviour are not filed either; "
              "see reports/triage.tsv."]
    (DRAFTS / "INDEX.md").write_text("\n".join(index) + "\n")
    print(f"{len(list(TEXT.glob('*.md')))} single drafts covering {len(covered & set(alone))} records, "
          f"{len(todo)} still to write, {ng} grouped drafts, {len(stale)} waiting on main, {len(minor)} minor not filed")


if __name__ == "__main__":
    main()
