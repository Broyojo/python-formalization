"""Rewrite source citations (`Objects/x.c:12-30`, and bare `:12`) from one CPython to another.

Line numbers map through `git diff`. A cited line inside a changed hunk has no
new line, so it is marked in place, `Objects/x.c@3.14.7:12`, for whoever rechecks
that function: `grep -rn '@3.14.7:'` lists what is left. A marked citation is one
nobody has checked against the new source yet.

A bare `:12` takes the file named most recently before it. Bare numbers are only
rewritten in comments, YAML prose and tsv notes, never in Lean strings or code,
where `:12` could be part of a modelled message. Reproducers are left alone.

Run this once, on a tree nobody else is editing: running it twice shifts twice.
Dry run by default; --apply writes.
  python3 scripts/recite.py vendor/cpython-3.14 vendor/cpython-3.15 [--apply]
"""

import argparse
import re
import subprocess
import sys
from bisect import bisect_right
from collections import Counter, defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TREES = ("Lib", "Objects", "Modules", "Python", "Parser", "Grammar", "Include", "Doc", "Tools")
SUFFIXES = {".c", ".h", ".py", ".gram", ".rst", ".asdl"}
MARK = "@3.14.7"

PATH = r"(?:[A-Za-z0-9_.-]+/)*[A-Za-z0-9_.-]+\.(?:c|h|py|gram|rst|asdl)"
# A citation may be followed by a colon, as in `Lib/a.py:12: the test`, but not by
# more digits. ` (3.14.7)` after one is dropped: every citation names 3.15.2 now.
SPAN = r"(?P<a>\d+)(?:-(?P<b>\d+))?(?!\w|:\d)(?P<label> \(3\.14(?:\.7)?\))?"
TOKEN = re.compile(rf"(?<![\w/.-])(?P<path>{PATH})(?::{SPAN})?|(?<=[\s(,`])(?P<bare>:)(?P<x>\d+)(?:-(?P<y>\d+))?(?!\w|:\d)")
HUNK = re.compile(r"^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@", re.M)


class LineMap:
    def __init__(self, old, new):
        out = subprocess.run(["git", "diff", "--no-index", "-U0", "--no-color", "--minimal", str(old), str(new)],
                             capture_output=True, text=True, errors="replace").stdout
        self.starts, self.ends, self.deltas = [], [], []
        previous, delta = 1, 0
        for m in HUNK.finditer(out):
            a, c = int(m[1]), int(m[3])
            b = 1 if m[2] is None else int(m[2])
            d = 1 if m[4] is None else int(m[4])
            first = a if b else a + 1
            self.add(previous, first - 1, delta)
            previous = first + b
            delta = (c if d else c + 1) + d - previous
        self.add(previous, 10 ** 9, delta)

    def add(self, start, end, delta):
        if start <= end:
            self.starts.append(start)
            self.ends.append(end)
            self.deltas.append(delta)

    def __call__(self, line):
        i = bisect_right(self.starts, line) - 1
        return line + self.deltas[i] if i >= 0 and line <= self.ends[i] else None


class Sources:
    def __init__(self, old, new):
        self.old, self.new = old, new
        self.maps = {}
        self.basenames = defaultdict(set)
        for tree in TREES:
            for path in (old / tree).rglob("*"):
                if path.suffix in SUFFIXES and path.is_file():
                    self.basenames[path.name].add(path.relative_to(old).as_posix())

    def resolve(self, cited):
        """The source file a citation names, or None for one of this repo's files."""
        if (self.old / cited).is_file():
            return cited if cited.split("/")[0] in TREES else None
        hits = {rel for rel in self.basenames.get(cited.rsplit("/", 1)[-1], ()) if rel.endswith("/" + cited)}
        return hits.pop() if len(hits) == 1 else None

    def mapper(self, rel):
        if rel not in self.maps:
            old, new = self.old / rel, self.new / rel
            self.maps[rel] = LineMap(old, new) if new.is_file() else (lambda line: None)
        return self.maps[rel]


def map_span(mapper, a, b):
    first, last = mapper(int(a)), mapper(int(b or a))
    if first is None or last is None:
        return None
    return f"{first}-{last}" if b else str(first)


def rewrite(text, sources, state, bare, tally):
    def sub(m):
        if m["path"]:
            rel = sources.resolve(m["path"])
            if rel:
                state["file"] = rel
            if rel is None or not m["a"]:
                return m[0]
            span = map_span(sources.mapper(rel), m["a"], m["b"])
            tally["mapped" if span else "marked"] += 1
            return f"{m['path']}:{span}" if span else f"{m['path']}{MARK}:{m['a']}" + (f"-{m['b']}" if m["b"] else "")
        if not bare:
            return m[0]
        if not state.get("file"):
            tally["bare, no file"] += 1
            return m[0]
        span = map_span(sources.mapper(state["file"]), m["x"], m["y"])
        tally["mapped bare" if span else "marked bare"] += 1
        return f":{span}" if span else f"{MARK}:{m['x']}" + (f"-{m['y']}" if m["y"] else "")
    return TOKEN.sub(sub, text)


def lean_segments(text):
    """(kind, text) in order, where kind is code, comment or string."""
    i, n, start = 0, len(text), 0
    out = []

    def flush(end, kind="code"):
        nonlocal start
        if end > start:
            out.append((kind, text[start:end]))
        start = end

    while i < n:
        two = text[i:i + 2]
        if two == "--":
            flush(i)
            end = text.find("\n", i)
            i = n if end < 0 else end
            flush(i, "comment")
        elif two == "/-":
            flush(i)
            depth, i = 1, i + 2
            while i < n and depth:
                pair = text[i:i + 2]
                if pair == "/-":
                    depth, i = depth + 1, i + 2
                elif pair == "-/":
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            flush(i, "comment")
        elif text[i] == "'" and re.match(r"'(?:\\.|[^\\'])'", text[i:i + 4]):
            i += re.match(r"'(?:\\.|[^\\'])'", text[i:i + 4]).end()
        elif text[i] == '"':
            flush(i)
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            flush(i, "string")
        else:
            i += 1
    flush(n)
    return out


def rewrite_lean(text, sources, tally):
    state = {}
    out = []
    for kind, part in lean_segments(text):
        out.append(part if kind == "code" else rewrite(part, sources, state, kind == "comment", tally))
    return "".join(out)


def rewrite_yaml(text, sources, tally):
    state = {}
    parts = re.split(r"(?m)^(reproducer: \|\n(?:(?:  .*)?\n)+)", text)
    return "".join(p if i % 2 else rewrite(p, sources, state, True, tally) for i, p in enumerate(parts))


def rewrite_tsv(text, sources, tally):
    # Each row starts with its own file, so a note's bare `:12` reads against that row.
    return "".join(rewrite(line, sources, {}, True, tally) for line in text.splitlines(True))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("old", type=Path)
    ap.add_argument("new", type=Path)
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    sources = Sources(args.old.resolve(), args.new.resolve())

    targets = [(p, rewrite_lean) for p in sorted((ROOT / "lean").rglob("*.lean")) if ".lake" not in p.parts]
    # A record of behaviour 3.15.2 no longer has keeps citing the code it describes.
    gone = set((ROOT / "coverage" / "gone-in-3.15.txt").read_text().split())
    targets += [(p, rewrite_yaml) for p in sorted((ROOT / "bugs").glob("*.yaml")) if p.stem not in gone]
    targets += [(p, lambda t, s, c: rewrite(t, s, {}, False, c)) for p in sorted((ROOT / "difftest").glob("*.py"))]
    targets += [(p, rewrite_tsv) for p in sorted((ROOT / "coverage" / "review").glob("*.tsv"))]
    targets += [(p, rewrite_tsv) for p in sorted((ROOT / "coverage" / "methods").glob("*.tsv"))]

    total, files = Counter(), 0
    for path, rewriter in targets:
        text = path.read_text(encoding="utf8")
        tally = Counter()
        result = rewriter(text, sources, tally)
        total.update(tally)
        if result != text:
            files += 1
            if args.apply:
                path.write_text(result, encoding="utf8")
    print(f"{files} files {'rewritten' if args.apply else 'would change'}: {dict(total)}")


if __name__ == "__main__":
    sys.exit(main())
