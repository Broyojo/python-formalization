"""Write the whole-Python function inventory to coverage/methods/*.tsv.

The inventory is the denominator of "formalize Python": every function, method,
opcode and grammar rule in the pinned CPython source gets one row, with status
modelled, excluded (with a reason) or todo. Re-running keeps the status, entry
and note of rows that still exist. Sources are parsed, never run.

Usage: python3 scripts/list_python_functions.py <cpython-source-root>
"""

import ast
import csv
import re
import subprocess
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIELDS = ["file", "line", "endline", "name", "signature", "status", "entry", "note"]

# Whole subtrees that are not part of Python's behaviour at all stay out of the
# manifest; things that are, but which we will not model, are rows with a reason.
SKIP_DIRS = {"test", "tests", "__pycache__", "lib2to3", "__phello__", "pydoc_data"}

LIB_EXCLUDED = [
    (r"^Lib/(idlelib|tkinter|turtledemo)/|^Lib/turtle\.py$", "platform: GUI toolkit"),
    (r"^Lib/ensurepip/|^Lib/venv/", "platform: installs pip and creates environments"),
    (r"^Lib/_(android|ios|osx|aix)_support\.py$", "platform: single-OS support"),
    (r"^Lib/asyncio/windows_|^Lib/multiprocessing/popen_spawn_win32\.py$"
     r"|^Lib/_pyrepl/windows|^Lib/encodings/(mbcs|oem)\.py$", "platform: Windows only"),
]
C_EXCLUDED = [
    (r"^Modules/(expat|_hacl|cjkcodecs|_decimal/libmpdec|_ctypes/libffi)", "vendored: third-party code"),
    (r"^Modules/(_test|xx|_xx)|^Modules/_testcapi|^Modules/_testlimitedcapi|^Modules/_testinternalcapi",
     "test-support: only for CPython's own tests"),
    (r"^Modules/(_tkinter|tkappinit|_curses|_gdbm|_dbm)", "platform: binds an external library"),
    (r"^Parser/parser\.c$", "generated: produced from Grammar/python.gram, which is listed"),
    (r"^Modules/_ssl|^Modules/_hashopenssl", "platform: binds an external library"),
]


def compact(text):
    return re.sub(r"\s+", " ", text).strip()


def python_rows(path, rel):
    tree = ast.parse(path.read_text(encoding="utf8", errors="replace"))
    rows = []

    def walk(node, prefix):
        for child in ast.iter_child_nodes(node):
            if isinstance(child, ast.ClassDef):
                walk(child, f"{prefix}{child.name}.")
            elif isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                # Functions nested in functions belong to their parent's body.
                rows.append((child.lineno, child.end_lineno, prefix + child.name,
                             f"{child.name}({compact(ast.unparse(child.args))})"))
            elif isinstance(child, (ast.If, ast.Try)):
                walk(child, prefix)

    walk(tree, "")
    return rows


C_DEF = re.compile(r"^(?:[A-Za-z_][\w ]*[ *]+)?\*?([A-Za-z_]\w*)\s*\(")


def c_rows(path):
    lines = path.read_text(encoding="utf8", errors="replace").splitlines()
    rows = []
    i = 0
    while i < len(lines):
        line = lines[i]
        match = C_DEF.match(line)
        if (not match or line.startswith(("typedef", "extern", "#", "static PyMethodDef", "PyDoc_"))
                or match.group(1).isupper()):
            i += 1
            continue
        # A definition's parameters run to a `{` alone on a line (PEP 7), or
        # at the end of the header. A `;` first means a declaration.
        j, body = i, None
        while j < len(lines) and j < i + 40:
            text = lines[j].split("//")[0].rstrip()
            if text == "{" or (text.endswith("{") and j == i + 0 and ")" in text):
                body = j
                break
            if text.endswith(";") or text == "" or text.startswith("#"):
                break
            j += 1
        if body is None:
            i += 1
            continue
        end = body
        while end < len(lines) and not lines[end].startswith("}"):
            end += 1
        rows.append((i + 1, min(end, len(lines) - 1) + 1, match.group(1),
                     compact(" ".join(lines[i:body + (lines[body] != "{")]))))
        i = end + 1
    return rows


OPCODE = re.compile(r"^\s+(?:\w+(?:\(\d+\))?\s+)*(inst|op|macro)\((\w+)")


def opcode_rows(path):
    rows = []
    for n, line in enumerate(path.read_text(encoding="utf8").splitlines(), 1):
        match = OPCODE.match(line)
        if match:
            rows.append((n, n, f"opcode:{match.group(2)}", compact(line)))
    return rows


GRAMMAR_RULE = re.compile(r"^([a-z_]\w*)(?:\[[^\]]*\])?(?: \(memo\))?:")


def grammar_rows(path):
    return [(n, n, f"rule:{m.group(1)}", compact(line))
            for n, line in enumerate(path.read_text(encoding="utf8").splitlines(), 1)
            if (m := GRAMMAR_RULE.match(line))]


def exclusion(rel, patterns):
    return next((reason for pattern, reason in patterns if re.search(pattern, rel)), "")


def manifest_path(rel):
    return ROOT / "coverage" / "methods" / (rel.replace("/", "__") + ".tsv")


def main():
    src = Path(sys.argv[1]).resolve()
    commit = subprocess.run(["git", "-C", str(src), "rev-parse", "HEAD"], capture_output=True,
                            text=True, check=True).stdout.strip()
    (ROOT / "coverage").mkdir(exist_ok=True)
    (ROOT / "coverage" / "methods").mkdir(exist_ok=True)
    (ROOT / "coverage" / "SOURCE_COMMIT").write_text(commit + "\n")

    sources = []
    for path in sorted((src / "Lib").rglob("*.py")):
        rel = path.relative_to(src).as_posix()
        if not SKIP_DIRS & set(rel.split("/")[1:-1]) and not path.name.startswith("test_"):
            sources.append((path, rel, python_rows, LIB_EXCLUDED))
    for pattern in ("Objects/*.c", "Objects/stringlib/*.h", "Modules/*.c", "Modules/*/*.c",
                    "Python/*.c", "Parser/*.c", "Parser/*/*.c"):
        for path in sorted(src.glob(pattern)):
            rel = path.relative_to(src).as_posix()
            if rel == "Python/bytecodes.c":
                sources.append((path, rel, lambda p, r=None: opcode_rows(p), C_EXCLUDED))
            elif "/clinic/" not in rel:
                sources.append((path, rel, lambda p, r=None: c_rows(p), C_EXCLUDED))
    sources.append((src / "Grammar/python.gram", "Grammar/python.gram",
                    lambda p, r=None: grammar_rows(p), []))

    totals = Counter()
    for path, rel, lister, patterns in sources:
        try:
            rows = lister(path, rel)
        except SyntaxError:
            print(f"skipped, does not parse: {rel}", file=sys.stderr)
            continue
        if not rows:
            continue
        target = manifest_path(rel)
        old = {}
        if target.exists():
            with target.open(newline="") as f:
                for row in csv.DictReader(f, delimiter="\t", quoting=csv.QUOTE_NONE):
                    old[row["name"], row["signature"]] = row
        reason = exclusion(rel, patterns)
        with target.open("w", newline="") as f:
            writer = csv.writer(f, delimiter="\t", quoting=csv.QUOTE_NONE, escapechar="\\",
                                lineterminator="\n")
            writer.writerow(FIELDS)
            for line, end, name, signature in rows:
                previous = old.get((name, signature), {})
                status = previous.get("status", "excluded" if reason else "todo")
                writer.writerow([rel, line, end, name, signature.replace("\t", " "), status,
                                 previous.get("entry", ""), previous.get("note", reason)])
                totals[status] += 1
    print(f"{sum(totals.values())} rows from {len(sources)} files at {commit[:12]}: {dict(totals)}")


if __name__ == "__main__":
    main()
