"""Difftest of `Python/ast.c` and `Python/ast_preprocess.c`.

`check.validate`: a tree from `ast.parse`, usually mutated, against the validator as
`compile(tree, "x", mode, flags=PyCF_OPTIMIZED_AST)` runs it. `check.preprocess`: the tree
of `ast.parse` against `compile(src, ..., flags=PyCF_OPTIMIZED_AST, optimize=n)`.
"""

import ast
import copy
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

FOLD = ["__debug__", "if __debug__: pass", "x = __debug__", "__debug__ = 1", "def f():\n  '''d'''\n",
        "def f():\n  '''d'''\n  x\n", "class C:\n  '''d'''\n", "'''d'''", "'''d'''\nx", "'a' '%s' % (x,)",
        "'%s' % (x,)\n", "def f():\n  '%s' % (x,)\n", "'%d' % (x,)", "'%s%s' % (x,y)", "'%%s %r' % (x,)",
        "'%a|%5s|%-5s|%.3s|%5.3s' % (a,b,c,d,e)", "'%s' % (x,y)", "'%s %s' % (x,)", "'a' % ()", "'%' % ()",
        "'%s' % (*x,)", "'%1000s' % (x,)", "'%#s' % (x,)", "'% s' % (x,)", "'%0s' % (x,)", "'%+s' % (x,)",
        "'%.s' % (x,)", "'%123s' % (x,)", "'%12s' % (x,)", "b'%s' % (x,)",
        "match x:\n  case -1: pass\n", "match x:\n  case 1+2j: pass\n", "match x:\n  case -1-2j: pass\n",
        "match x:\n  case -1.5+0j: pass\n", "match x:\n  case -0.0+1j: pass\n", "match x:\n  case 0.0-1j: pass\n",
        "match x:\n  case -0.0-1j: pass\n", "match x:\n  case {-1: y, 1+2j: z}: pass\n",
        "match x:\n  case [-1, (-2 | 3), C(-4, a=-5)] as y: pass\n",
        "match x:\n  case " + "1" + "0" * 400 + "+1j: pass\n", "from __future__ import annotations\nx: __debug__ = 1",
        "from __future__ import annotations\ndef f(a: __debug__) -> __debug__: pass",
        "from __future__ import braces", "from __future__ import nope", "'doc'\nfrom __future__ import nope",
        "x\nfrom __future__ import nope", "from __future__ import division, nope", "from . import nope",
        "from __future__ import *"]


def src_case(rng):
    r = rng.random()
    if r < 0.35:
        s = rng.choice(FOLD)
    elif r < 0.65:
        s = pd.gen_source(rng)
    elif r < 0.9:
        s = rng.choice(pd.CORPUS)
    else:
        path = rng.choice(pd.LIBFILES)
        s = path.read_text(encoding="utf-8", errors="replace")
    try:
        return s, ast.parse(s)
    except Exception:
        return None


FIELDS_NODES = [ast.Pass(lineno=1, col_offset=0, end_lineno=1, end_col_offset=4)]


def all_nodes(t):
    return [n for n in ast.walk(t) if n._fields or n._attributes]


def mk_expr(rng):
    loc = dict(lineno=1, col_offset=0, end_lineno=1, end_col_offset=1)
    return rng.choice([ast.Name("x", ast.Load(), **loc), ast.Name("None", ast.Load(), **loc),
                       ast.Name("x", ast.Store(), **loc), ast.Constant(1, **loc),
                       ast.Constant(None, **loc), ast.Constant(..., **loc), ast.Constant((1, 2), **loc),
                       ast.Tuple([], ast.Load(), **loc), ast.Tuple([], ast.Del(), **loc),
                       ast.List([ast.Name("y", ast.Load(), **loc)], ast.Store(), **loc),
                       ast.Starred(ast.Name("y", ast.Load(), **loc), ast.Load(), **loc),
                       ast.UnaryOp(ast.USub(), ast.Constant(1j, **loc), **loc),
                       ast.UnaryOp(ast.USub(), ast.Constant("s", **loc), **loc),
                       ast.BinOp(ast.Constant(1, **loc), ast.Add(), ast.Constant(1j, **loc), **loc),
                       ast.BinOp(ast.Constant(1j, **loc), ast.Add(), ast.Constant(1j, **loc), **loc),
                       ast.BinOp(ast.Constant(1, **loc), ast.Mult(), ast.Constant(1j, **loc), **loc),
                       ast.Attribute(ast.Name("y", ast.Load(), **loc), "a", ast.Load(), **loc),
                       ast.JoinedStr([], **loc), ast.TemplateStr([], **loc)])


def mutate_tree(t, rng):
    nodes = all_nodes(t)
    for _ in range(rng.choice([1, 1, 2, 3])):
        if not nodes:
            break
        n = rng.choice(nodes)
        k = rng.random()
        if k < 0.25 and "lineno" in n._attributes:
            a = rng.choice(["lineno", "col_offset", "end_lineno", "end_col_offset"])
            setattr(n, a, rng.choice([-2, -1, 0, 1, 2, 100, getattr(n, a, 1) + 1, getattr(n, a, 1) - 1]))
        elif n._fields:
            f = rng.choice(n._fields)
            v = getattr(n, f, None)
            if isinstance(v, list):
                z = rng.random()
                if z < 0.4:
                    setattr(n, f, [])
                elif z < 0.6 and v:
                    v.pop()
                elif z < 0.8 and v:
                    v[rng.randrange(len(v))] = None
                elif v and isinstance(v[0], ast.expr):
                    v.append(mk_expr(rng))
            elif isinstance(v, ast.expr_context):
                setattr(n, f, rng.choice([ast.Load(), ast.Store(), ast.Del()]))
            elif isinstance(v, ast.expr):
                setattr(n, f, mk_expr(rng))
            elif isinstance(v, str):
                setattr(n, f, rng.choice(["None", "True", "False", "_", "x"]))
            elif isinstance(v, int) and not isinstance(v, bool):
                setattr(n, f, rng.choice([-1, 0, 1, 2]))
            elif v is None and f in ("cause", "rest", "name", "guard", "value", "pattern", "msg"):
                pass
    return t


def gen_case(rng):
    got = src_case(rng)
    if got is None:
        return None
    s, t = got
    if rng.random() < 0.5:
        mode = {ast.Module: "exec"}.get(type(t), "exec")
        t2 = mutate_tree(copy.deepcopy(t), rng) if rng.random() < 0.9 else t
        try:
            enc = pa.enc(t2)
            import json
            json.dumps(enc)
        except Exception:
            return None
        return {"mod": "pygrammar", "fn": "check.validate", "tree": enc, "pytree": None,
                "_t": t2, "_mode": mode}
    o = rng.choice([-1, 0, 1, 2])
    return {"mod": "pygrammar", "fn": "check.preprocess", "tree": pa.enc(t), "optimize": o,
            "syntax_only": False, "src": s}


class Enc(dict):
    pass


def run_python(c):
    if c["fn"] == "check.validate":
        try:
            compile(c["_t"], "x", c["_mode"], flags=ast.PyCF_OPTIMIZED_AST)
            return {"ok": None}
        except SyntaxError as e:
            # past the validator: the future check of the next stage
            return {"ok": None}
        except (ValueError, TypeError) as e:
            return {"exc": type(e).__name__, "msg": str(e)}
        except RecursionError:
            return {"ok": None}
    try:
        t = compile(c["src"], "<unknown>", "exec", flags=ast.PyCF_OPTIMIZED_AST,
                    optimize=c["optimize"])
        return {"ok": pa.enc(t)}
    except SyntaxError as e:
        return {"exc": "SyntaxError",
                "msg": f"{e.msg}|{e.lineno}|{e.offset}|{e.end_lineno}|{e.end_offset}|None"}


if __name__ == "__main__":
    import json

    orig_dumps = json.dumps

    def dumps(o, *a, **k):
        if isinstance(o, dict) and "_t" in o:
            o = {k2: v for k2, v in o.items() if k2 not in ("_t", "pytree")}
        return orig_dumps(o, *a, **k)

    common.json.dumps = dumps
    common.main(gen_case, run_python, default_cases=5000)
