"""Repair the bare `:12` citations recite.py mapped through the wrong file.

recite.py carried "the file named most recently" across a whole Lean file, so a
bare citation could take its line map from an unrelated earlier comment. It also
left bare continuations in Lean strings, as in `Doc/a.rst:1-2, :3-4`, on old numbers.

This recomputes every citation from the text before the re-pin. A bare citation
goes to the file whose cited lines contain the most identifiers from the words
around it. Ties go to a file named in the same comment, then to the file this
file cites most. A file that cites only one source needs no evidence. Otherwise,
with no evidence for any file, the citation is marked @3.14.7.

A fix is applied only to a line still exactly as recite.py left it, so a line
somebody has since edited is left alone, and running this twice changes nothing.
Dry run by default; --apply writes.
  python3 scripts/fix_bare_citations.py vendor/cpython-3.14 vendor/cpython-3.15 [--apply] [paths...]
"""

import argparse
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import recite  # noqa: E402

ROOT = recite.ROOT
BEFORE, RECITED = "c043897~1", "c043897"
WORD = re.compile(r"[A-Za-z_][A-Za-z0-9_]{3,}")
COMMON = {"this", "that", "with", "from", "when", "then", "same", "line", "lines", "here", "only", "after",
          "before", "returns", "return", "raises", "case", "first", "while", "which", "does", "have", "them"}
JOIN = re.compile(r"(?:,\s*|\s+and\s+)")
WINDOW = 90


def show(rev, path):
    r = subprocess.run(["git", "show", f"{rev}:{path}"], cwd=ROOT, capture_output=True, text=True, errors="replace")
    return r.stdout if r.returncode == 0 else None


class Repair:
    def __init__(self, sources):
        self.sources = sources
        self.text = {}

    def old_lines(self, rel):
        if rel not in self.text:
            self.text[rel] = (self.sources.old / rel).read_text(encoding="utf8", errors="replace").split("\n")
        return self.text[rel]

    def score(self, rel, first, last, words):
        lines = self.old_lines(rel)
        if first > len(lines):
            return -1
        # Allow the comment to name something just outside the span, such as the function above it.
        body = "\n".join(lines[max(first - 3, 0):min(last + 1, len(lines))])
        return sum(1 for word in words if word in body)

    def choose(self, near, first, last, here, cited):
        """The file a bare citation means, or None with no evidence."""
        words = set(WORD.findall(near)) - COMMON
        scored = [(self.score(rel, first, last, words), rel == here, cited[rel], rel) for rel in cited]
        scored = [s for s in scored if s[0] >= 0]
        if not scored:
            return None
        best = max(scored)
        if best[0] > 0 or best[1] or len(scored) == 1:
            return best[3]
        return None

    def segment(self, kind, part, cited, tally):
        here = None
        previous = None

        def sub(m):
            nonlocal here, previous
            if m["path"]:
                rel = self.sources.resolve(m["path"])
                if rel:
                    here = rel
                previous = m.end()
                if rel is None or not m["a"]:
                    return m[0]
                span = recite.map_span(self.sources.mapper(rel), m["a"], m["b"])
                suffix = f"-{m['b']}" if m["b"] else ""
                return f"{m['path']}:{span}" if span else f"{m['path']}{recite.MARK}:{m['a']}{suffix}"
            continued = previous is not None and JOIN.fullmatch(part[previous:m.start()])
            if kind == "string" and not continued:
                return m[0]
            previous = m.end()
            first, last = int(m["x"]), int(m["y"] or m["x"])
            near = part[max(0, m.start() - WINDOW):m.end() + WINDOW]
            rel = here if continued else self.choose(near, first, last, here, cited)
            suffix = f"-{m['y']}" if m["y"] else ""
            if rel is None:
                tally["no evidence"] += 1
                return f"{recite.MARK}:{m['x']}{suffix}"
            span = recite.map_span(self.sources.mapper(rel), m["x"], m["y"])
            return f":{span}" if span else f"{recite.MARK}:{m['x']}{suffix}"

        return recite.TOKEN.sub(sub, part)

    def cited(self, text):
        found = Counter()
        for m in recite.TOKEN.finditer(text):
            rel = self.sources.resolve(m["path"]) if m["path"] else None
            if rel:
                found[rel] += 1
        return found

    def lean(self, text, tally):
        cited = self.cited(text)
        return "".join(part if kind == "code" else self.segment(kind, part, cited, tally)
                       for kind, part in recite.lean_segments(text))

    def yaml(self, text, tally):
        cited = self.cited(text)
        parts = re.split(r"(?m)^(reproducer: \|\n(?:(?:  .*)?\n)+)", text)
        out = []
        for i, part in enumerate(parts):
            if i % 2:
                out.append(part)
                continue
            fields = re.split(r"(?m)^(?=[a-z_]+:)", part)
            out.extend(self.segment("comment", field, cited, tally) for field in fields)
        return "".join(out)


def tracked(prefix):
    out = subprocess.run(["git", "ls-tree", "-r", "--name-only", RECITED, prefix], cwd=ROOT,
                         capture_output=True, text=True).stdout
    return out.split()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old", type=Path)
    ap.add_argument("new", type=Path)
    ap.add_argument("paths", nargs="*")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--show", action="store_true")
    args = ap.parse_args()
    repair = Repair(recite.Sources(args.old.resolve(), args.new.resolve()))
    gone = set((ROOT / "coverage" / "gone-in-3.15.txt").read_text().split())

    targets = [p for p in tracked("lean/PyLean") if p.endswith(".lean")]
    targets += [p for p in tracked("bugs") if p.endswith(".yaml") and Path(p).stem not in gone]
    if args.paths:
        targets = [p for p in targets if any(q in p for q in args.paths)]

    tally = Counter()
    for path in targets:
        before, recited = show(BEFORE, path), show(RECITED, path)
        target = ROOT / path
        if before is None or recited is None or not target.exists():
            continue
        fixed = repair.yaml(before, tally) if path.endswith(".yaml") else repair.lean(before, tally)
        old, new = recited.split("\n"), fixed.split("\n")
        if len(old) != len(new):
            tally["line count differs"] += 1
            continue
        current = target.read_text(encoding="utf8").split("\n")
        changed = False
        for i, (was, should) in enumerate(zip(old, new)):
            if was == should:
                continue
            tally["wrong"] += 1
            if i < len(current) and current[i] == was:
                index = i
            else:
                hits = [j for j, line in enumerate(current) if line == was]
                index = hits[0] if len(hits) == 1 else None
            if index is None:
                tally["line since edited, left alone"] += 1
                continue
            if args.show:
                print(f"{path}:{index + 1}\n  - {was.strip()[:150]}\n  + {should.strip()[:150]}")
            current[index] = should
            changed = True
            tally["fixed"] += 1
        if changed and args.apply:
            target.write_text("\n".join(current), encoding="utf8")
    print(dict(tally))


if __name__ == "__main__":
    sys.exit(main())
