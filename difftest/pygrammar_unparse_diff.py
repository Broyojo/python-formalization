"""Difftest of `ast.unparse`: Lean model vs `Lib/_ast_unparse.py`, on trees of real sources."""

import ast
import random
import sys
import warnings
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
import pygrammar_ast as pa  # noqa: E402

warnings.simplefilter("ignore")
_argv, sys.argv = sys.argv, sys.argv[:1]
import pygrammar_diff as pd  # noqa: E402
sys.argv = _argv

sys.setrecursionlimit(5000)

EDGE = [r'f"{x:\x7b}"', r'f"{x:\x7d}"', r'f"{x:\x00}"', r'f"{x:\r}"', r'f"{x:\ud800}"', r'u"a" f"{x}"',
        "t'''{\"\\\"#x\" #c\n}'''", "f'''{\"\\\"#x\"=#c\n}'''", "t'''\"\"\"\\'\\'\\'{x\n}'''", "t'{x!r:{y}}'",
        "1e999", "1e999j", "1e308", "1e16", "1e15", "1e-4", "1e-5", "1e22", "1e23", "5e-324", "2.5", "0.1", "1.0",
        "1e100", "123456789012345678.0", "0.0001", "0.00001", "4.35", "2.2250738585072014e-308", "9007199254740993.0",
        "1j", "1.5j", "1e16j", "1e-5j", "0j", "0.0j", "1e999j", "0x" + "f" * 3560, "0x" + "f" * 3600, "'\\ud800'",
        "'\\x00\\x7f\\xa0\\xad\\u200b\\U0001f600'", "b'\\x00\\xff\\'\"'", "b'\"'", "b\"'\"", "'\"'", '"\'"', "'\\'\"'",
        "def f():\n  '''a'''\n", "def f():\n  u'''a'''\n", "def f():\n  ''''''\n", "def f():\n  '\"\"\"'\n",
        "def f():\n  '\\'\\'\\'\"\"\"'\n", "def f():\n  '\"'\n", "def f():\n  \"'\"\n", "def f():\n  '\\n'\n", "def f():\n  '\\\\'\n"]


def gen_case(rng):
    r = rng.random()
    if r < 0.2:
        s = rng.choice(EDGE)
    elif r < 0.55:
        s = pd.gen_source(rng)
    elif r < 0.95:
        s = rng.choice(pd.CORPUS)
    else:
        path = rng.choice(pd.LIBFILES)
        s = path.read_text(encoding="utf-8", errors="replace")
    mode = rng.choice(["exec", "exec", "exec", "eval", "single"])
    tc = rng.random() < 0.1
    try:
        t = ast.parse(s, mode=mode, type_comments=tc)
        enc = pa.enc(t)
    except (SyntaxError, ValueError, RecursionError):
        return None
    return {"mod": "pygrammar", "fn": "unparse.py", "tree": enc, "_t": t}


def run_python(c):
    if c["fn"] == "unparse.py":
        try:
            return {"ok": [ord(x) for x in ast.unparse(c["_t"])]}
        except AssertionError as e:
            return {"exc": "AssertionError", "msg": ""}
        except ValueError as e:
            return {"exc": "ValueError", "msg": str(e)}


if __name__ == "__main__":
    import json

    orig_dumps = json.dumps

    def dumps(o, *a, **k):
        if isinstance(o, dict) and "_t" in o:
            o = {k2: v for k2, v in o.items() if k2 != "_t"}
        return orig_dumps(o, *a, **k)

    common.json.dumps = dumps
    common.main(gen_case, run_python, default_cases=5000)
