"""Build the project page (docs/index.html) from the repository's own records.

Reads coverage/methods, coverage/review, coverage/registry.tsv and bugs/*.yaml.
Bug records are reported as counts only: details stay private until they are
reported upstream. Run: python3 site/build.py
"""

import collections
import csv
import glob
import html
import re
import subprocess
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = ROOT / "site" / "template.html"
OUT = ROOT / "docs" / "index.html"


def rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\"))


def coverage():
    faithful = set()
    for p in glob.glob(str(ROOT / "coverage/review/*.tsv")):
        for r in rows(p):
            if r["verdict"] == "FAITHFUL":
                faithful.add((r["file"], r["line"]))
    areas = collections.defaultdict(collections.Counter)
    files = collections.defaultdict(collections.Counter)
    for p in glob.glob(str(ROOT / "coverage/methods/*.tsv")):
        for r in rows(p):
            area = r["file"].split("/")[0]
            c, fc = areas[area], files[r["file"]]
            for k in (c, fc):
                k["rows"] += 1
                k[r["status"]] += 1
                if r["status"] == "modelled" and (r["file"], r["line"]) in faithful:
                    k["faithful"] += 1
    return areas, files


def registry():
    c = collections.Counter()
    for line in (ROOT / "coverage/registry.tsv").read_text().splitlines():
        c[line.split("\t")[1]] += 1
    return c


def bugs():
    pri, kind = collections.Counter(), collections.Counter()
    groups = {"twin": "C and Python twins disagree", "memory-safety": "memory safety",
              "crash": "crash", "wrong-result": "wrong result", "wrong-exception": "wrong exception",
              "doc-mismatch": "differs from the documentation"}
    for p in glob.glob(str(ROOT / "bugs/*.yaml")):
        t = Path(p).read_text()
        m = re.search(r"^priority:\s*(\S+)", t, re.M)
        pri[m.group(1) if m else "?"] += 1
        k = re.search(r"^kind:\s*(\S+)", t, re.M)
        k = k.group(1) if k else "other"
        label = next((v for key, v in groups.items() if k.startswith(key)), "other")
        kind[label] += 1
    return pri, kind


def pct(a, b):
    return f"{100 * a / b:.1f}%" if b else "–"


def main():
    areas, files = coverage()
    reg = registry()
    pri, kind = bugs()
    tot = collections.Counter()
    for c in areas.values():
        tot.update(c)
    in_scope = tot["rows"] - tot["excluded"]

    area_names = {"Grammar": "Grammar rules (Grammar/python.gram)", "Lib": "Standard library in Python (Lib/)",
                  "Modules": "C extension modules (Modules/)", "Objects": "Built-in types (Objects/)",
                  "Parser": "Parser and tokenizer (Parser/)", "Python": "Interpreter core (Python/)"}
    area_rows = []
    for a in sorted(areas):
        c = areas[a]
        scope = c["rows"] - c["excluded"]
        share = c["faithful"] / scope if scope else 0
        area_rows.append(
            f'<tr><th scope="row">{html.escape(area_names.get(a, a))}</th>'
            f'<td class="num">{scope:,}</td><td class="num">{c["faithful"]:,}</td>'
            f'<td class="bar"><span style="--w:{100 * share:.1f}%"></span><b>{pct(c["faithful"], scope)}</b></td></tr>')

    done = []
    for f, c in files.items():
        if c["modelled"] >= 15 and c["faithful"] == c["modelled"]:
            done.append((c["faithful"], f))
    done.sort(reverse=True)
    done_items = "".join(f'<li><code>{html.escape(f)}</code><span>{n}</span></li>' for n, f in done[:24])

    kind_items = "".join(f'<li><span>{html.escape(k)}</span><b>{n}</b></li>'
                         for k, n in kind.most_common())
    pri_items = "".join(f'<li><span>{p}</span><b>{pri[p]}</b></li>' for p in ["P1", "P2", "P3", "P4", "P5"])

    values = {
        "PROPS": f'{sum(reg.values()):,}', "PROVEN": f'{reg["proven"]:,}', "REFUTED": f'{reg["refuted"]:,}',
        "OPEN": f'{reg["open"]:,}', "INSCOPE": f"{in_scope:,}", "FAITHFUL": f'{tot["faithful"]:,}',
        "FAITHFULPCT": pct(tot["faithful"], in_scope), "BUGS": f"{sum(pri.values()):,}",
        "AREAROWS": "\n".join(area_rows), "DONE": done_items, "DONECOUNT": str(len(done)),
        "KINDS": kind_items, "PRIS": pri_items, "DATE": date.today().strftime("%-d %B %Y"),
        "COMMIT": subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                                 capture_output=True, text=True).stdout.strip(),
    }
    page = TEMPLATE.read_text()
    for k, v in values.items():
        page = page.replace("{{" + k + "}}", v)
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(page)
    print(f"wrote {OUT.relative_to(ROOT)}: {values['FAITHFUL']} faithful of {values['INSCOPE']} "
          f"in scope ({values['FAITHFULPCT']}), {len(done)} files fully reviewed")


if __name__ == "__main__":
    main()
