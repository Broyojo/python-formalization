"""Build the project page (docs/index.html) from the repository's own records.

Reads coverage/methods, coverage/review, coverage/registry.tsv and bugs/*.yaml.
Individual bug records are not published here; only counts, plus the showcase
findings named in SHOWCASE, which are written into the template by hand.
Run: python3 site/build.py
"""

import collections
import csv
import glob
import html
import json
import re
import subprocess
from datetime import date
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEMPLATE = ROOT / "site" / "template.html"
OUT = ROOT / "docs" / "index.html"
AREA_ORDER = ["Python", "Objects", "Modules", "Parser", "Grammar", "Lib"]
AREA_NAMES = {"Grammar": "Grammar rules", "Lib": "Standard library", "Modules": "C modules",
              "Objects": "Built-in types", "Parser": "Parser", "Python": "Interpreter core"}


def rows(path):
    with open(path, newline="") as f:
        return list(csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\"))


def coverage():
    faithful = set()
    for p in glob.glob(str(ROOT / "coverage/review/*.tsv")):
        for r in rows(p):
            if r["verdict"] == "FAITHFUL":
                faithful.add((r["file"], r["line"]))
    files = collections.defaultdict(collections.Counter)
    for p in glob.glob(str(ROOT / "coverage/methods/*.tsv")):
        for r in rows(p):
            c = files[r["file"]]
            c["rows"] += 1
            if r["status"] == "modelled":
                c["faithful" if (r["file"], r["line"]) in faithful else "modelled"] += 1
            else:
                c[r["status"]] += 1
    return files


def registry():
    c = collections.Counter()
    for line in (ROOT / "coverage/registry.tsv").read_text().splitlines():
        c[line.split("\t")[1]] += 1
    return c


def bugs():
    kind = collections.Counter()
    groups = [("twin", "C and Python versions disagree"), ("sibling", "C and Python versions disagree"),
              ("memory-safety", "Memory corruption"), ("crash", "Crash"),
              ("wrong-result", "Wrong result"), ("wrong-exception", "Wrong error or message"),
              ("doc", "Doesn't match the docs"), ("missing-validation", "Missing input check"),
              ("logic", "Wrong result")]
    total = 0
    # Records for 3.14.7 behaviour that 3.15.2 no longer has do not count (coverage/gone-in-3.15.txt).
    gone = {l.split()[0] for l in (ROOT / "coverage/gone-in-3.15.txt").read_text().splitlines()
            if l.strip() and not l.startswith("#")}
    for p in glob.glob(str(ROOT / "bugs/*.yaml")):
        if Path(p).stem in gone:
            continue
        t = Path(p).read_text()
        k = re.search(r"^kind:\s*(\S+)", t, re.M)
        k = k.group(1) if k else ""
        kind[next((v for key, v in groups if k.startswith(key)), "Other")] += 1
        total += 1
    return total, kind


TRAJ_FILES = ["Objects/typeobject.c", "Objects/genobject.c", "Objects/setobject.c", "Modules/_json.c",
              "Lib/enum.py", "Lib/random.py", "Objects/abstract.c", "Objects/rangeobject.c",
              "Lib/pickletools.py", "Modules/binascii.c"]


def trajectories():
    """Faithful / reviewed counts in every committed version of a file's review table."""
    out = []
    for f in TRAJ_FILES:
        path = "coverage/review/" + f.replace("/", "__") + ".tsv"
        log = subprocess.run(["git", "log", "--reverse", "--format=%h", "--", path], cwd=ROOT,
                             capture_output=True, text=True).stdout.split()
        pts = []
        for h in log:
            text = subprocess.run(["git", "show", f"{h}:{path}"], cwd=ROOT, capture_output=True,
                                  text=True).stdout
            lines = text.splitlines()[1:]
            if not lines:
                continue
            fa = sum(1 for l in lines if l.split("\t")[3:4] == ["FAITHFUL"])
            if pts and pts[-1] == (fa, len(lines)):
                continue
            pts.append((fa, len(lines)))
        if len(pts) >= 2:
            out.append({"file": f, "pts": pts})
    return out


def traj_svg(t):
    w, h, left, pad, bot = 220, 116, 30, 8, 20
    pts = t["pts"]
    n = len(pts)
    total = max(tot for _, tot in pts)
    xs = [left + (w - left - pad) * (i / (n - 1)) for i in range(n)]
    ys = [h - bot - (h - bot - pad) * min(1, fa / total) for fa, _ in pts]
    path = " ".join(("M" if i == 0 else "L") + f"{x:.1f},{y:.1f}" for i, (x, y) in enumerate(zip(xs, ys)))
    dots = "".join(
        f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{3 if i == n - 1 else 2.2}" '
        f'class="{"dot end" if i == n - 1 else "dot"}"><title>review {i + 1}: {fa} of {total} accepted</title></circle>'
        for i, ((fa, _), x, y) in enumerate(zip(pts, xs, ys)))
    last = pts[-1][0]
    return (f'<figure class="spark"><svg viewBox="0 0 {w} {h}" role="img" aria-label="{html.escape(t["file"])}: '
            f'{pts[0][0]} of {total} accepted after the first review, {last} after {n} reviews">'
            f'<line x1="{left}" x2="{w - pad}" y1="{pad}" y2="{pad}" class="full"/>'
            f'<line x1="{left}" x2="{w - pad}" y1="{h - bot}" y2="{h - bot}" class="base"/>'
            f'<text x="{left - 6}" y="{pad + 3}" class="ax">100%</text>'
            f'<text x="{left - 6}" y="{h - bot + 3}" class="ax">0%</text>'
            f'<text x="{left}" y="{h - 5}" class="ax start">review 1</text>'
            f'<text x="{w - pad}" y="{h - 5}" class="ax">review {n}</text>'
            f'<path d="{path}" class="trace"/>{dots}</svg>'
            f'<figcaption><code>{html.escape(t["file"])}</code><span><b>{last} of {total}</b> accepted · {n} reviews</span></figcaption></figure>')


KEYWORDS = {
    "c": {"static", "if", "else", "return", "const", "struct", "while", "for"},
    "lean": {"def", "theorem", "if", "then", "else", "let", "fun", "match", "with", "by", "do"},
    "py": {"for", "in", "class", "def", "return", "pass", "import", "from", "if", "else", "try", "except"},
}
TYPES = {"c": {"unsigned", "long", "int", "void", "char"}, "lean": {"Int", "Nat", "Prop", "Bool"},
         "py": {"Enum"}}
FUNCS = {"c": {"get_len_of_range"}, "lean": {"getLenOfRange", "uadd", "usub", "toU"},
         "py": {"range", "pickle", "dumps", "_dumps", "a2b_base32", "_add_value_alias_", "__repr__",
                "__init_subclass__"}}
TOKEN = re.compile(r"(&[a-z]+;|&#\d+;)|(#.*$|--.*$)|(b?\"[^\"]*\"|b?'[^']*')|(\b\d+(?:UL)?\b)|([A-Za-z_][A-Za-z_0-9]*)|(∧)",
                   re.M)


def highlight_text(text, lang):
    def sub(m):
        ent, com, s, num, word, op = m.groups()
        if ent:
            return ent
        if com:
            return f'<span class="t-cm">{com}</span>' if lang in ("py", "lean") and (
                com.startswith("#") if lang == "py" else com.startswith("--")) else com
        if s:
            return f'<span class="t-str">{s}</span>' if lang == "py" else s
        if num:
            return f'<span class="t-num">{num}</span>'
        if op:
            return f'<span class="t-op">{op}</span>'
        if word in KEYWORDS[lang]:
            return f'<span class="t-kw">{word}</span>'
        if word in TYPES[lang]:
            return f'<span class="t-ty">{word}</span>'
        if word in FUNCS[lang]:
            return f'<span class="t-fn">{word}</span>'
        return word
    return TOKEN.sub(sub, text)


def highlight(page):
    """Colour tokens inside <pre data-lang="..."> blocks, touching only text between tags."""
    def block(m):
        lang, body = m.group(1), m.group(2)
        parts = re.split(r"(<[^>]+>)", body)
        inside_cm = False
        out = []
        for part in parts:
            if part.startswith("<"):
                if 'class="c"' in part or 'class="ln c"' in part:
                    inside_cm = True
                elif part.startswith("</span") and inside_cm:
                    inside_cm = False
                out.append(part)
            else:
                out.append(part if inside_cm else highlight_text(part, lang))
        return f'<pre data-lang="{lang}">{"".join(out)}</pre>'
    return re.sub(r'<pre data-lang="(\w+)">(.*?)</pre>', block, page, flags=re.S)


def main():
    files = coverage()
    reg = registry()
    nbugs, kinds = bugs()

    area = collections.defaultdict(collections.Counter)
    for f, c in files.items():
        area[f.split("/")[0]].update(c)
    tot = collections.Counter()
    for c in area.values():
        tot.update(c)
    in_scope = tot["rows"] - tot["excluded"]

    # Map data: one entry per file, in area order then file name: [file, faithful, modelled, excluded, todo].
    mapdata = []
    for a in AREA_ORDER:
        for f in sorted(x for x in files if x.split("/")[0] == a):
            c = files[f]
            mapdata.append([f, c["faithful"], c["modelled"], c["excluded"], c["todo"]])

    area_rows = []
    for a in AREA_ORDER:
        c = area[a]
        scope = c["rows"] - c["excluded"]
        share = 100 * c["faithful"] / scope if scope else 0
        area_rows.append(
            f'<tr><td>{AREA_NAMES[a]}</td><td class="r mono">{scope:,}</td>'
            f'<td class="r mono">{c["faithful"]:,}</td><td class="r mono">{share:.1f}%</td></tr>')

    area_bars = []
    for a in ["ALL"] + AREA_ORDER:
        c = tot if a == "ALL" else area[a]
        scope = c["rows"] - c["excluded"]
        if not scope:
            continue
        f1, f2 = 100 * c["faithful"] / scope, 100 * c["modelled"] / scope
        area_bars.append(
            f'<li{" class=\"all\"" if a == "ALL" else ""}><span>{"All of CPython" if a == "ALL" else AREA_NAMES[a]}</span><span class="bar"><i style="width:{f1:.2f}%;background:var(--blue)"></i>'
            f'<i style="width:{f2:.2f}%;background:var(--blue-2)"></i></span><b>{f1:.0f}%</b></li>')

    done = sorted(((c["faithful"], f) for f, c in files.items()
                   if c["faithful"] >= 15 and c["modelled"] == 0), reverse=True)
    done_items = "".join(f'<li><code>{html.escape(f)}</code><span>{n}</span></li>' for n, f in done[:30])

    kmax = max(kinds.values())
    kind_items = "".join(
        f'<li><span>{html.escape(k)}</span><i style="--w:{100 * n / kmax:.1f}%"></i><b>{n}</b></li>'
        for k, n in kinds.most_common())
    trajs = "".join(traj_svg(t) for t in trajectories())
    modelled_claimed = tot["faithful"] + tot["modelled"]
    funnel = [("Rows in the inventory", tot["rows"]), ("In scope", in_scope),
              ("Modelled in Lean", modelled_claimed), ("Reviewed faithful", tot["faithful"])]
    fmax = funnel[0][1]
    funnel_html = "".join(
        f'<li><span>{label}</span><i style="--w:{100 * n / fmax:.2f}%"></i><b>{n:,}</b></li>'
        for label, n in funnel)
    first_commit = subprocess.run(["git", "log", "--reverse", "--format=%ad", "--date=format:%-d %B %Y"],
                                  cwd=ROOT, capture_output=True, text=True).stdout.splitlines()[0]
    ncommits = subprocess.run(["git", "rev-list", "--count", "HEAD"], cwd=ROOT, capture_output=True,
                              text=True).stdout.strip()

    lean_files = sorted((ROOT / "lean" / "PyLean").rglob("*.lean"))
    lean_text = [f.read_text() for f in lean_files]
    lean_lines = sum(x.count("\n") for x in lean_text)
    theorems = sum(len(re.findall(r"^\s*(?:private |protected )?(?:theorem|lemma) ", x, re.M)) for x in lean_text)

    values = {
        "PROPS": f'{sum(reg.values()):,}', "PROVEN": f'{reg["proven"]:,}', "REFUTED": f'{reg["refuted"]:,}',
        "OPEN": f'{reg["open"]:,}', "INSCOPE": f"{in_scope:,}", "FAITHFUL": f'{tot["faithful"]:,}',
        "FAITHFULPCT": f'{100 * tot["faithful"] / in_scope:.1f}%', "BUGS": f"{nbugs:,}",
        "TOTALROWS": f'{tot["rows"]:,}', "AREAROWS": "\n".join(area_rows), "DONE": done_items,
        "DONECOUNT": str(len(done)), "KINDS": kind_items, "DATE": date.today().strftime("%-d %B %Y"),
        "MEMSAFE": str(kinds["Memory corruption"]), "TRAJ": trajs, "FUNNEL": funnel_html,
        "CRASHY": str(kinds["Memory corruption"] + kinds["Crash"]),
        "STARTED": first_commit, "COMMITS": f"{int(ncommits):,}", "MODELLED": f"{modelled_claimed:,}",
        "LEANLINES": f"{lean_lines:,}", "LEANFILES": f"{len(lean_files):,}", "THEOREMS": f"{theorems:,}", "AREABARS": "".join(area_bars), "MAPDATA": json.dumps(mapdata, separators=(",", ":")),
        "COMMIT": subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT,
                                 capture_output=True, text=True).stdout.strip(),
    }
    page = TEMPLATE.read_text()
    for k, v in values.items():
        page = page.replace("{{" + k + "}}", v)
    page = highlight(page)
    missing = re.findall(r"\{\{[A-Z]+\}\}", page)
    if missing:
        raise SystemExit(f"unfilled placeholders: {missing}")
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(page)
    readme = ROOT / "README.md"
    r = readme.read_text()
    stats = (f"| | |\n|---|---|\n| Lean code | {values['LEANLINES']} lines in {values['LEANFILES']} files |\n"
             f"| Theorems and lemmas | {values['THEOREMS']}, all checked on every build |\n"
             f"| Top-level properties | {values['PROVEN']} proven, {values['REFUTED']} refuted, {values['OPEN']} open |\n"
             f"| Functions reviewed faithful | {values['FAITHFUL']} of {values['INSCOPE']} in scope ({values['FAITHFULPCT']}) |\n"
             f"| Bug records | {values['BUGS']} that reproduce on 3.15.2, each with a reproducer |\n")
    r = re.sub(r"(<!-- stats:start -->\n).*?(<!-- stats:end -->)", lambda m: m.group(1) + stats + m.group(2), r, flags=re.S)
    readme.write_text(r)
    print(f"wrote {OUT.relative_to(ROOT)}: {values['FAITHFUL']} faithful of {values['INSCOPE']} "
          f"({values['FAITHFULPCT']}), {len(done)} files fully reviewed, {len(mapdata)} files mapped")


if __name__ == "__main__":
    main()
