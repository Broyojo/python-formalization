"""Turn bug records into draft CPython issues for human review.

Reads reports/triage.tsv (proposed_action per record) and bugs/*.yaml, and writes:
  reports/drafts/single/<id>.md     one issue per 'file-alone' record
  reports/drafts/group/<module>.md  one issue per module for 'group:' and 'ask-in-group' records
  reports/drafts/INDEX.md           checklist for review
Nothing here talks to GitHub. Run: python3 reports/make_drafts.py
"""

import csv
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DRAFTS = ROOT / "reports" / "drafts"
PAGE = "https://broyojo.com/python-formalization/"
MAIN_SHA = "ef1fce0"


def field(t, k):
    m = re.search(rf"^{k}:\s*\|\s*\n((?:[ ]{{2}}.*\n|[ ]*\n)+)", t, re.M)
    if m:
        lines = m.group(1).splitlines()
        return "\n".join(l[2:] if l.startswith("  ") else l for l in lines).strip()
    m = re.search(rf"^{k}:\s*(.+)$", t, re.M)
    return m.group(1).strip().strip('"') if m else ""


def inner_code(repro):
    """Pull the script out of a subprocess wrapper (code = r'''...''') and drop REPRODUCED lines."""
    m = re.search(r'code\s*=\s*r?("""|\'\'\')\n(.*?)\1', repro, re.S)
    code = m.group(2) if m else repro
    keep = [l for l in code.splitlines() if "REPRODUCED" not in l
            and not re.match(r"\s*import resource", l) and "RLIMIT_CORE" not in l]
    # drop a trailing 'if ...:' that only guarded the REPRODUCED print
    while keep and re.match(r"\s*if .*:\s*$", keep[-1]):
        keep.pop()
    return "\n".join(keep).strip()


def short_title(title):
    t = title.strip().rstrip(".")
    if len(t) <= 72:
        return t
    cut = t[:72]
    cut = cut[: cut.rfind(" ")] if " " in cut else cut
    return cut.rstrip(",;:") + " …"


def first_para(s):
    return s.split("\n\n")[0].strip()


def single(bid, t):
    title = short_title(field(t, "title"))
    body = [
        "# Bug report", "", "### Bug description", "",
        first_para(field(t, "summary")), "",
        "```python", inner_code(field(t, "reproducer")), "```", "",
        "**Expected:** " + " ".join(field(t, "expected").split()), "",
        "**Actual:** " + " ".join(first_para(field(t, "observed")).split()), "",
    ]
    cause, fix = field(t, "cause"), field(t, "possible_fix")
    if cause:
        body += ["**Cause:** " + " ".join(cause.split()), ""]
    if fix:
        body += ["**Possible fix:** " + " ".join(fix.split()), ""]
    body += [
        "### CPython versions tested on", "", f"3.15, CPython main branch ({MAIN_SHA})", "",
        "### Operating systems tested on", "", "Linux", "", "---",
        f"Found while building a Lean 4 model of CPython ({PAGE}). The report was drafted with AI "
        "assistance; I reproduced it on 3.15.2 and on main and reviewed it before filing.",
    ]
    return title, "\n".join(body) + "\n"


def group(mod, items):
    title = f"{mod}: {len(items)} small behaviour inconsistencies found by a formal model"
    body = ["# Bug report", "", "### Bug description", "",
            f"While modelling this area of CPython 3.15.2 in Lean 4 ({PAGE}), we found the cases below "
            "where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) "
            "or with its documentation. Some may be intended; we list them together so they can be "
            "triaged at once. Each reproduces on 3.15.2 and on main.", ""]
    for i, (bid, t) in enumerate(items, 1):
        body += [f"#### {i}. {field(t, 'title')}", "", first_para(field(t, "summary")), "",
                 "<details><summary>Reproducer</summary>", "", "```python",
                 inner_code(field(t, "reproducer")), "```", "", "</details>", ""]
    body += ["### CPython versions tested on", "", f"3.15, CPython main branch ({MAIN_SHA})", "",
             "### Operating systems tested on", "", "Linux", "", "---",
             "Drafted with AI assistance; each case was reproduced and the report reviewed before filing."]
    return title, "\n".join(body) + "\n"


def main():
    rows = list(csv.DictReader(open(ROOT / "reports/triage.tsv"), delimiter="\t"))
    for d in ("single", "group"):
        (DRAFTS / d).mkdir(parents=True, exist_ok=True)
    index = ["# Draft issues for review", "",
             "Tick a box once you have read the draft and can explain it in your own words "
             "(CPython's AI-tools policy). Only ticked drafts get filed.", "", "## Single issues", ""]
    groups = {}
    for r in rows:
        t = (ROOT / "bugs" / f"{r['id']}.yaml").read_text()
        a = r["proposed_action"]
        if a == "file-alone":
            title, body = single(r["id"], t)
            (DRAFTS / "single" / f"{r['id']}.md").write_text(f"<!-- title: {title} -->\n" + body)
            index.append(f"- [ ] {r['priority']} [{title}](single/{r['id']}.md)")
        elif a.startswith("group:") or a == "ask-in-group":
            groups.setdefault(r["module"], []).append((r["id"], t))
    index += ["", "## Grouped issues (one per module)", ""]
    for mod, items in sorted(groups.items(), key=lambda x: -len(x[1])):
        title, body = group(mod, items)
        (DRAFTS / "group" / f"{mod}.md").write_text(f"<!-- title: {title} -->\n" + body)
        index.append(f"- [ ] [{title}](group/{mod}.md)")
    skipped = [r for r in rows if r["proposed_action"] in ("skip", "link-existing", "check-main")]
    index += ["", f"## Not filed ({len(skipped)})", "",
              "Duplicates of existing issues, 3.14-only behaviour, or not yet re-checked on main. "
              "See reports/triage.tsv."]
    (DRAFTS / "INDEX.md").write_text("\n".join(index) + "\n")
    print(f"{sum(r['proposed_action'] == 'file-alone' for r in rows)} single drafts, "
          f"{len(groups)} group drafts, {len(skipped)} not filed")


if __name__ == "__main__":
    main()
