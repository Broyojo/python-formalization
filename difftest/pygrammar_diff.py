"""Differential tests of `PyGrammar`: Lean model vs the running CPython.

  --part peg       the whole parser, against `compile(..., PyCF_ONLY_AST)` (default)
  --part lexer     `_tokenize.TokenizerIter`, with and without extra_tokens
  --part check     `Python/ast.c` and `Python/ast_preprocess.c`
  --part unparse   `Lib/_ast_unparse.py` and `Python/ast_unparse.c`

Source text comes from four places: a random derivation of `Grammar/python.gram`, read with pegen,
invalid_ rules included; mutations of such programs and of corpus snippets; every string in
CPython's own syntax tests that looks like code; lines and whole files of `Lib/`.

Trees are exchanged in the JSON encoding of `lean/PyLean/PyGrammar/Ast.lean`:
  node        {"c": name, "l": [lineno, col, end_lineno, end_col] | null, "f": [fields]}
  seq         JSON array;  None for an absent optional field: null
  identifier  {"id": [cps]};  string {"s": [cps]};  int {"n": i}
  constant    {"k": kind, "v": value}
Errors compare by class, message, lineno, offset, end_lineno, end_offset and text.
"""

import _tokenize
import ast
import builtins
import copy
import io
import json
import os
import random
import re
import struct
import sys
import tokenize
import types as _types
import unicodedata
import warnings
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402

warnings.simplefilter("ignore")


# ---- encoding of ast trees

def bits(x):
    return str(struct.unpack("<Q", struct.pack("<d", x))[0])


def enc_const(v):
    if v is None:
        return {"k": "None"}
    if v is True:
        return {"k": "True"}
    if v is False:
        return {"k": "False"}
    if v is Ellipsis:
        return {"k": "Ellipsis"}
    if isinstance(v, int):
        return {"k": "int", "v": str(v)}
    if isinstance(v, float):
        return {"k": "float", "v": bits(v)}
    if isinstance(v, complex):
        return {"k": "complex", "v": [bits(v.real), bits(v.imag)]}
    if isinstance(v, str):
        return {"k": "str", "v": [ord(c) for c in v]}
    if isinstance(v, bytes):
        return {"k": "bytes", "v": list(v)}
    if isinstance(v, tuple):
        return {"k": "tuple", "v": [enc_const(x) for x in v]}
    if isinstance(v, frozenset):
        return {"k": "frozenset", "v": [enc_const(x) for x in v]}
    raise TypeError(f"not a constant: {v!r}")


def enc_cps(s):
    return [ord(c) for c in s]


ATTRS = ("lineno", "col_offset", "end_lineno", "end_col_offset")


def _enc_field(typ, v):
    """`typ` is one of identifier/int/string/constant or anything else for a node."""
    if v is None and typ != "constant":
        return None
    if isinstance(v, list):
        return [_enc_field(typ, x) for x in v]
    if typ == "identifier":
        return {"id": enc_cps(v)}
    if typ == "string":
        return {"s": enc_cps(v)}
    if typ == "int":
        return {"n": v}
    if typ == "constant":
        return enc_const(v)
    return enc(v)


def enc(node):
    """Encode an `ast.AST`. Field order and builtin types come from `_field_types`."""
    fields = []
    types = getattr(node, "_field_types", {})
    for name in node._fields:
        t = types.get(name)
        v = getattr(node, name, None)
        fields.append(_enc_field(_base(t), v))
    has_loc = "lineno" in node._attributes
    loc = [getattr(node, a, None) for a in ATTRS] if has_loc else None
    if loc is not None:
        loc = [-1 if x is None else x for x in loc]
    return {"c": type(node).__name__, "l": loc, "f": fields}


def _base(t):
    """Reduce an `_field_types` annotation to the ASDL base name."""
    if isinstance(t, _types.UnionType):
        args = [a for a in t.__args__ if a is not _types.NoneType]
        return _base(args[0]) if args else "constant"
    origin = getattr(t, "__origin__", None)
    if origin is list:
        return _base(t.__args__[0])
    if t is str:
        return "string"
    if t is int:
        return "int"
    if t is object:
        return "constant"
    name = getattr(t, "__name__", "")
    if name == "_Identifier" or name == "identifier":
        return "identifier"
    return "node"


# `_field_types` calls identifiers `str` too, so the exact ASDL types come from this
# table of the identifier-typed fields in Python.asdl.
_IDENT = {("FunctionDef", "name"), ("AsyncFunctionDef", "name"), ("ClassDef", "name"),
          ("ImportFrom", "module"), ("Global", "names"), ("Nonlocal", "names"),
          ("Attribute", "attr"), ("Name", "id"), ("ExceptHandler", "name"),
          ("arg", "arg"), ("keyword", "arg"), ("alias", "name"), ("alias", "asname"),
          ("MatchMapping", "rest"), ("MatchClass", "kwd_attrs"), ("MatchStar", "name"),
          ("MatchAs", "name"), ("TypeVar", "name"), ("ParamSpec", "name"),
          ("TypeVarTuple", "name")}


def _fix_ident(node, fields):
    cls = type(node).__name__
    for i, name in enumerate(node._fields):
        if (cls, name) in _IDENT:
            f = fields[i]
            if isinstance(f, dict):
                fields[i] = {"id": f["s"]}
            elif isinstance(f, list):
                fields[i] = [{"id": x["s"]} for x in f]
    return fields


_enc = enc


def enc(node):  # noqa: F811
    r = _enc(node)
    _fix_ident(node, r["f"])
    return r


# ---- part peg

for V in (Path(os.environ.get("CPYTHON_SRC", Path(__file__).resolve().parents[1] / "vendor" / "cpython-3.15")),
          Path.home() / "pf" / "vendor" / "cpython-3.15"):
    if V.exists():
        break
sys.path.insert(0, str(V / "Tools" / "peg_generator"))
from pegen import grammar as G  # noqa: E402
from pegen.grammar_parser import GeneratedParser  # noqa: E402
from pegen.tokenizer import Tokenizer  # noqa: E402

warnings.simplefilter("ignore")

with open(V / "Grammar" / "python.gram") as f:
    GRAMMAR = GeneratedParser(Tokenizer(tokenize.generate_tokens(f.readline))).start()
RULES = GRAMMAR.rules

NAMES = ["a", "b", "c", "x", "y", "foo", "print", "exec", "match", "case", "type", "_",
         "é", "数", "None_", "self", "__debug__", "async_", "lambda_", "ª"]
NUMBERS = ["0", "1", "42", "1_000", "0x1F", "0o17", "0b101", "1.5", "1e3", "1e-3", "2j", ".5",
           "1.", "1_0.0_1e1_0j", "0_0", "00", "9" * 20, "1e400", "4.9e-324", "1.7976931348623157e308",
           "2.2250738585072009e-308", "0.1", "123456789012345678901234567890"]
STRINGS = ["''", '""', "'a'", '"b"', "'''c'''", 'r"\\d"', "b'x'", "rb'\\n'", "u'u'", "'\\n'",
           "'\\x41'", "'\\u00e9'", "'\\N{BULLET}'", "'é'", "'''\na\n'''", "'\\\n'", "b'\\x00'",
           "'\\777'", "'\\q'", "b'\\q'", "b'\\400'", "R'x'", "U'x'", "Rb''", "bR''"]
FSTR = ["f''", 'f"a"', "f'{x}'", "f'{x!r}'", "f'{x:>3}'", "f'{x=}'", "f'{x!s:{y}}'", "f'{{}}'",
        "f'''{\nx\n}'''", "rf'\\d{x}'", "f'{x:{y:{z}}}'", "f'{x = }'", "f'{x=!r}'", "f'{x=:3}'",
        "f'\\N{BULLET}{x}'", "f'{f\"{x}\"}'", "t''", "t'{x}'", "t'a{x!r:3}b'", "t'{x=}'", "rt'\\d{x}'",
        "f'{x#c\n}'", "f'''{x=#c\n}'''", "t'''{x=\n}'''", "f'\\{x}'"]


def gen_item(it, depth, rng, out):
    if isinstance(it, G.NamedItem):
        return gen_item(it.item, depth, rng, out)
    if isinstance(it, (G.PositiveLookahead, G.NegativeLookahead, G.Cut)):
        return
    if isinstance(it, G.Forced):
        return gen_item(it.node, depth, rng, out)
    if isinstance(it, G.Opt):
        if rng.random() < (0.5 if depth < 12 else 0.1):
            gen_item(it.node, depth, rng, out)
        return
    if isinstance(it, G.Repeat0):
        for _ in range(rng.choice([0, 0, 1, 2] if depth < 12 else [0])):
            gen_item(it.node, depth, rng, out)
        return
    if isinstance(it, G.Repeat1):
        for _ in range(rng.choice([1, 1, 2] if depth < 12 else [1])):
            gen_item(it.node, depth, rng, out)
        return
    if isinstance(it, G.Gather):
        n = rng.choice([1, 1, 2, 3] if depth < 12 else [1])
        for i in range(n):
            if i:
                gen_item(it.separator, depth, rng, out)
            gen_item(it.node, depth, rng, out)
        return
    if isinstance(it, G.Group):
        return gen_rhs(it.rhs, depth, rng, out)
    if isinstance(it, G.Rhs):
        return gen_rhs(it, depth, rng, out)
    if isinstance(it, G.StringLeaf):
        out.append(ast.literal_eval(it.value))
        return
    if isinstance(it, G.NameLeaf):
        v = it.value
        if v == "NAME":
            out.append(rng.choice(NAMES))
        elif v == "NUMBER":
            out.append(rng.choice(NUMBERS))
        elif v == "STRING":
            out.append(rng.choice(STRINGS))
        elif v == "NEWLINE":
            out.append("\n")
        elif v == "INDENT":
            out.append("\x01")
        elif v == "DEDENT":
            out.append("\x02")
        elif v == "ENDMARKER":
            pass
        elif v == "TYPE_COMMENT":
            out.append("# type: int\n")
        elif v in ("FSTRING_START", "TSTRING_START"):
            out.append(v[0].lower() + "'")
        elif v in ("FSTRING_END", "TSTRING_END"):
            out.append("'")
        elif v in ("FSTRING_MIDDLE", "TSTRING_MIDDLE"):
            out.append("m")
        elif v == "SOFT_KEYWORD":
            out.append(rng.choice(["match", "case", "type", "_"]))
        elif v in RULES:
            gen_rule(v, depth + 1, rng, out)
        return


def gen_rhs(rhs, depth, rng, out):
    alts = rhs.alts
    if depth >= 14:
        # prefer the shortest alternatives once deep
        alts = sorted(alts, key=lambda a: len(a.items))[:max(1, len(alts) // 3)]
    alt = rng.choice(alts)
    for it in alt.items:
        gen_item(it, depth, rng, out)


def gen_rule(name, depth, rng, out):
    if depth > 26:
        out.append(rng.choice(NAMES))
        return
    gen_rhs(RULES[name].rhs, depth, rng, out)


def render(tokens):
    """Join a token list into source, turning INDENT/DEDENT markers into indentation."""
    lines, cur, indent, parts = [], [], 0, []
    src = ""
    prev = ""
    at_line_start = True
    for t in tokens:
        if t == "\x01":
            indent += 1
            continue
        if t == "\x02":
            indent = max(0, indent - 1)
            continue
        if t == "\n" or t.endswith("\n") and t.startswith("#"):
            src += " " + t if t.startswith("#") else t
            at_line_start = True
            prev = ""
            continue
        if at_line_start:
            src += "    " * indent
            at_line_start = False
        elif prev and t and (prev[-1].isalnum() or prev[-1] in "_'\"") and (t[0].isalnum() or t[0] in "_'\""):
            src += " "
        elif t in ("=", "==", ":", "->", "+", "-", "if", "else", "in", "for") or prev in (",",):
            src += " "
        src += t
        prev = t
    return src


def gen_source(rng):
    r = rng.random()
    out = []
    if r < 0.45:
        gen_rule("statements", 0, rng, out)
    elif r < 0.7:
        gen_rule("expressions", 3, rng, out)
    elif r < 0.85:
        names = [n for n in RULES if n.startswith("invalid_")]
        gen_rule(rng.choice(names), 3, rng, out)
    else:
        gen_rule(rng.choice(["compound_stmt", "simple_stmts", "match_stmt", "class_def",
                             "function_def", "try_stmt", "with_stmt", "for_stmt", "lambdef",
                             "strings", "fstring", "tstring", "type_alias", "import_stmt"]),
                 2, rng, out)
    src = render(out)
    if rng.random() < 0.3 and "\n" not in src[:-1]:
        src = src.rstrip("\n")
    return src


# ---- corpus of snippets from CPython's tests

def corpus():
    base = V / "Lib" / "test"
    out = []
    for name in ["test_syntax.py", "test_exceptions.py", "test_fstring.py", "test_tstring.py",
                 "test_grammar.py", "test_string_literals.py", "test_future_stmt/test_future.py",
                 "test_patma.py", "test_type_params.py", "test_type_aliases.py", "test_tokenize.py",
                 "test_named_expressions.py", "test_positional_only_arg.py", "test_unpack_ex.py",
                 "test_generators.py", "test_coroutines.py", "test_compile.py", "test_ast/test_ast.py",
                 "test_unparse.py", "test_eof.py", "test_keywordonlyarg.py", "test_with.py"]:
        p = base / name
        if not p.exists():
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        try:
            tree = ast.parse(text)
        except SyntaxError:
            continue
        for n in ast.walk(tree):
            if isinstance(n, ast.Constant) and isinstance(n.value, str) and 0 < len(n.value) < 400:
                if "\0" in n.value:
                    continue
                if name == "test_syntax.py" and ">>>" in n.value:
                    for m in re.finditer(r">>> (.*(?:\n\.\.\. .*)*)", n.value):
                        s = re.sub(r"\n\.\.\. ?", "\n", m.group(1))
                        out.append(s)
                out.append(n.value)
    return sorted(set(out))


CORPUS = corpus()

REPIN = [
    # lazy imports, PEP 810
    "lazy import a\n", "lazy import a.b as c, d\n", "lazy from a import b\n", "lazy from . import b\n",
    "lazy from .a import b as c\n", "lazy from a import (b, c)\n", "lazy from a import *\n",
    "lazy from ... import b\n", "def f():\n  lazy import a\n", "try:\n  lazy import a\nfinally: pass\n",
    "lazy from __future__ import annotations\n", "lazy from __future__ import barry_as_FLUFL\n",
    "lazy = 1\n", "lazy\n", "lazy.a\n", "lazy(1)\n", "lazy import\n", "lazy from\n", "lazy from a\n",
    "lazy lazy import a\n", "lazy import lazy\n", "from lazy import lazy\n", "lazy: int\n",
    # `_warn_relative_import_of_lazy`
    "from . lazy import a\n", "from .. lazy import a\n", "from ... lazy import a\n", "from . . lazy import a\n",
    "from .lazy import a\n", "from ..lazy import a\n", "from .\\\n lazy import a\n", "from . lazy.b import a\n",
    "from . lazy2 import a\n", "from lazy import a\n", "x = 1\nfrom .  lazy import a\n",
    "from a lazy import b\n", "from . a lazy import b\n", "from a.b lazy import *\n",
    # `tok->barry_as_bdfl`
    "1 <> 2\n", "a <> b\n", "a<>b\n", "a <>= b\n", "(a <> b)\n",
    "from __future__ import barry_as_FLUFL\n1 <> 2\n", "from __future__ import barry_as_FLUFL\n1 != 2\n",
    "from __future__ import barry_as_FLUFL; 1 <> 2\n", "from __future__ import division, barry_as_FLUFL\na<>b\n",
    "from . import barry_as_FLUFL\n1 <> 2\n", "from __future__ import barry_as_FLUFL as x\n1 <> 2\n",
    # DictComp with no value
    "{**d for d in x}\n", "{**d for d in x if d}\n", "{**d async for d in x}\n", "{**a, **b for a in x}\n",
    "{**a: b for a in x}\n", "{a: **b for a in x}\n", "{*a for a in x}\n", "[*a for a in x]\n",
    "(*a for a in x)\n", "{a: *b for a in x}\n", "{**(a or b) for a in x}\n", "f(**a for a in x)\n",
    # signed patterns
    "match x:\n  case +1: pass\n", "match x:\n  case +1.5: pass\n", "match x:\n  case +1j: pass\n",
    "match x:\n  case +1+2j: pass\n", "match x:\n  case +1-2j: pass\n", "match x:\n  case {+1: a}: pass\n",
    "match x:\n  case +'a': pass\n", "match x:\n  case +x: pass\n", "match x:\n  case ++1: pass\n",
    "match x:\n  case -+1: pass\n", "match x:\n  case [+1, *a]: pass\n", "match x:\n  case 1+-2j: pass\n",
    # a missing comma
    "(a b)\n", "[a b]\n", "{a b}\n", "(a\nb)\n", "('a'\n 'b'\n c)\n", "(print a)\n", "print a\n", "exec a\n",
    "(1 2)\n", "f(a b)\n", "x = (1\n 'a'\n 2)\n", "a b\n", "[a\n b\n c]\n", "(a if b c)\n", "(a.b c.d)\n",
    "(print a b)\n", "('''a\nb''' c)\n", "(a\\\n b)\n", "{1: a b}\n", "[x for x in y z]\n",
    # `expecting '}'`
    "f'{a\n", "f'''{a\n\n'''\n", "f'{{a'\n", "f\"{a\n\"\n", "t'''{a\n'''\n", "f'''{\n\nx\n'''\n", "f'''{a:{b\n}'''\n",
    "f'''\n{a\n'''\n", "f'''{a\n{b\n'''\n", "x = f'''{(\n'''\n", "f'''{[a,\nb'''\n", "f'''{a}{b\n'''\n",
    # interpolation text
    "t'{x}'", "t'{x=}'", "t'{x = }'", "t'{ x = !r}'", "t'{x=:>3}'", "t'''{x=\n}'''", "t'''{x=\\\n}'''",
    "t'''{x=\\\n\\\n}'''", "t'''{x= \\\n }'''", "t'{x = y}'", "t'{x==y}'", "t'{x==y=}'", "t'{x   }'", "t'  {  x  }'",
    "t'''{x # c\n=}'''", "t'''{x=#c\n}'''", "t'''{'#'=}'''", "t'''{\"\\\"#x\"=#c\n}'''", "t'{a=!s:{b}}'",
    "f'''{\"\\\"#x\"=#c\n}'''", "f'''{'\\'#'=}'''", "f'''{x=#c\n}'''", "f'''{x#c\n=}'''", "f'''{x=\n#c\n}'''",
    "t'{x\u00a0=\u00a0}'", "t'''{x=\u2028}'''", "f'''{'é#'=#c\n}'''", "f'''{\"\\\\\"=#c\n}'''",
    # decode errors at a known location
    "f'\\N{foo}'", "f'''\n\\N{foo}'''", "t'\\xZ'", "f'a\\N{foo}b{x}'", "f'{x}\\U00110000'", "f'\\N{'", "'\\N{foo}'",
    "f'''a\nb\\xZ{x}'''", "x = f'\\u12'\n", "rf'\\N{foo}'", "f'{x:\\N{foo}}'",
    # lexer columns are characters now
    "é (]\n", "é = 0x\n", "é = 1__0\n", "é = 1e\n", "é = 012\n", "é = 0b2\n", "é = 0o8\n", "'é' 0xg\n",
    "éé = 1_\n", "数 = 0_\n", "'😀' = 0x\n", "é = 1é\n", "é = 0777\n", "é = 1.2.3e\n", "x = 'é'; y = 0b\n",
    # handler and alias names, as the parser sees them
    "try: pass\nexcept A as None: pass\n", "try: pass\nexcept* A as None: pass\n", "import a as None\n",
    "from a import b as True\n", "def None(): pass\n", "class False: pass\n", "async def None(): pass\n",
    "try: pass\nexcept A as b: pass\n", "try: pass\nexcept* A as b: pass\n",
]
LIBFILES = sorted(p for p in (V / "Lib").glob("*.py") if p.stat().st_size < 60000)


def mutate(src, rng):
    try:
        import io
        toks = [t.string for t in tokenize.generate_tokens(io.StringIO(src).readline)
                if t.type not in (tokenize.ENDMARKER,)]
    except Exception:
        toks = re.findall(r"\w+|\s+|.", src)
    if not toks:
        return src
    i = rng.randrange(len(toks))
    k = rng.random()
    if k < 0.3:
        del toks[i]
    elif k < 0.6:
        toks.insert(i, rng.choice(["(", ")", "[", "]", "{", "}", ":", ",", "=", "==", "*", "**", "if",
                                   "else", "for", "in", "lambda", "not", "yield", "await", "async",
                                   "1", "x", "'s'", "f'", "\\", "\n", "    ", "\t", "#", ".", "...",
                                   "->", ":=", "!", "@", "$", "?", "`", "None", "True", "import",
                                   "from", "as", "del", "class", "def", "return", "pass", "try",
                                   "except", "finally", "while", "with", "match", "case", "type"]))
    elif k < 0.8:
        j = rng.randrange(len(toks))
        toks[i], toks[j] = toks[j], toks[i]
    else:
        toks[i] = toks[i][:len(toks[i]) // 2]
    out = ""
    for t in toks:
        if out and out[-1].isalnum() and t[:1].isalnum():
            out += " "
        out += t
    return out


def source_names(src):
    """Runs of identifier characters in `src`. `\\w` will not do: an identifier may
    hold combining marks, which are XID_Continue but not alphanumeric."""
    run = ""
    for c in src + " ":
        if ("a" + c).isidentifier():
            run += c
        else:
            word = run.lstrip("0123456789")
            if word:
                yield word
            run = ""


def oracle_tables(src):
    """The two explicit oracles of the model (`Cfg`): names and NFKC."""
    ucn = {}
    for m in re.finditer(r"\\N\{([^}]*)\}", src):
        n = m.group(1)
        try:
            ucn[n] = ord(unicodedata.lookup(n))
        except (KeyError, TypeError):
            pass
    nfkc = []
    for w in source_names(src):
        if not w.isascii():
            n = unicodedata.normalize("NFKC", w)
            if n != w:
                nfkc.append([[ord(c) for c in w], [ord(c) for c in n]])
    return [[k, v] for k, v in ucn.items() if k.isascii()], nfkc


def make_case(src, rng):
    try:
        data = src.encode("utf-8")
    except UnicodeEncodeError:
        return None
    mode = rng.choices(["exec", "eval", "single", "func_type"], [80, 10, 8, 2])[0]
    ucn, nfkc = oracle_tables(src)
    c = {"mod": "pygrammar", "fn": "peg.parse", "src": list(data), "mode": mode,
         "ucn": ucn, "nfkc": nfkc}
    if rng.random() < 0.1:
        c["type_comments"] = True
    if rng.random() < 0.05:
        c["feature_version"] = rng.choice([4, 5, 6, 7, 8, 9, 10, 12, 13, 14])
    if rng.random() < 0.15:
        # PyCF_DONT_IMPLY_DEDENT, PyCF_ALLOW_INCOMPLETE_INPUT, CO_FUTURE_BARRY_AS_BDFL
        c["flags"] = rng.choice([0x200, 0x4000, 0x4200, 0x400000, 0x404200])
    return c


# ---- statements of the rules with rule-specific theorems (Peg/Rules/)

RULE_EXPRS = ["x", "a.b", "f(x)", "1", "-1", "+1", "~x", "(a, b)", "x if y else z", "lambda: 0",
              "await x", "[x]", "x ** y", "not x", "*x", "x := 1", "(x := 1)", "yield", "from",
              "import", "lazy", "raise", "1 2", "", "a, b", "-x ** -y", "2 ** 3 ** 4"]
RULE_NAMES = ["a", "a.b", "a.b.c", "a as b", "a, b", "lazy", "a as", ".a", "", "(a)", "*"]
RULE_FORMS = [
    "raise {e}", "raise {e} from {f}", "raise from {e}", "raise {e} from", "raise", "raise from",
    "return {e}", "return", "return {e}, {f}", "yield {e}", "yield from {e}", "yield",
    "x = yield {e}", "x = yield from {e}", "assert {e}", "assert {e}, {f}", "assert {e} = {f}",
    "assert {e}, {f} = {e}", "assert {e} := {f}", "import {n}", "lazy import {n}", "import",
    "lazy import", "import {n} from {m}", "lazy import {n} from {m}", "lazy from {n} import {m}",
    "lazy from {n} import", "from {n} import", "from {n} lazy import {m}", "lazy {n}",
    "match x:\n case {s}{k}: pass", "match x:\n case {s}{k} | {s}{k}j: pass",
    "{u}{u}{e}", "{e} ** {u}{f}", "{e} ** {f} ** {e}", "{u}{e} ** {f}", "await {e} ** {f}",
    "pass", "break", "continue", "pass; break", "x += {e}", "x @= {e}", "x **= {e}", "x //= {e}",
    "for {n} in {e}:\n pass", "for {n} in {e}:\n pass\nelse:\n pass", "for {n} in :\n pass",
    "for {n} in {e} pass", "async for {n} in {e}:\n pass", "@{n}\nclass C: pass", "@{n}\ndef f(): pass",
    "class C({e}): pass", "while {e}:\n pass", "try:\n pass\nfinally:\n pass", "match {e}:\n case {k}: pass",
    "match = {e}", "type = {e}", "type X = {e}", "global {n}", "nonlocal {n}", "global",
    "not {e}", "not not {e}", "{e} < {f}", "{e} < {f} <= {e}", "{e} not in {f}", "{e} is not {f}",
    "x: {e}", "x: {e} = {f}", "(x): {e}", "x.y: {e} = {f}", "{n} = {e}", "a = b = {e}", "{e} = {f}",
    "x = {e} = {f}", "x += ", "x += {e} = {f}", "{n} += {e}", "from {n} import {m}", "from . import {m}",
    "from .. {n} import {m}", "lazy from . import {m}", "from {n} import", "from import {m}",
    "async def f():\n async for {n} in {e}:\n  pass", "x = {e} = {f} = 2", "f() = {e}", "del f()",
    "del {e}", "if {e}:\n pass\nelif {f}:\n pass\nelse:\n pass", "if {e}: pass\nelse pass",
    "if {e}:\npass", "while {e}:\n pass\nelse:\n pass", "while {e}: {f}", "if {e}: {f}; {e}",
    "{e}, {f}", "{e},", "{e}, {f},", "x = {e} if {f} else {e}", "lambda: {e}", "type X[T] = {e}",
    # try / except / except* / finally / elif (Peg/Rules/Try.lean, Except.lean)
    "try:\n pass\nexcept {e}:\n pass", "try:\n pass\nexcept {e} as {n}:\n pass",
    "try:\n pass\nexcept {e}, {f}:\n pass", "try:\n pass\nexcept:\n pass\nelse:\n pass\nfinally:\n pass",
    "try:\n pass\nexcept* {e}:\n pass", "try:\n pass\nexcept* {e} as {n}:\n pass",
    "try:\n pass\nexcept* {e}, {f}:\n pass", "try:\n pass\nexcept*:\n pass", "try pass", "try:\n pass",
    "try:\n pass\nfinally pass", "try:\n pass\nfinally:\n pass", "try:\n pass\nexcept {e}:\n pass\nexcept* {f}:\n pass",
    "try:\n pass\nexcept {e} {f}:\n pass", "try:\n pass\nexcept* {e} as {f}:\n pass", "try:\n pass\nelse:\n pass",
    "if {e}:\n pass\nelif {f}:\n pass\nelif {e}:\n pass", "if {e}:\n pass\nelif {f} pass", "if {e}:\n pass\nelif:\n pass",
    # with (Peg/Rules/With.lean)
    "with {e}:\n pass", "with {e} as {n}:\n pass", "with ({e}, {f}):\n pass", "with ({e} as x, {f} as y,):\n pass",
    "with ({e}, {f}) as {n}:\n pass", "with ({e}): # type: int\n pass", "async with ({e}, {f}): # type: int\n pass",
    "async with ({e} as x): # type: int\n pass", "async with {e} as {n}: # type: int\n pass",
    "with {e} as {n}, {f}: # type: int\n pass", "async with ({e}):\n pass", "with {e} as {f} {e}:\n pass",
    "with {e}\n pass", "with ({e} as {f}):\n pass", "async with {e}:\n pass", "with:\n pass",
    # imports, definitions, annotations, defaults (Peg/Rules/Defs.lean)
    "from x import ({n})", "from x import ({n},)", "from x import {n},", "from x import *", "from x import (*)",
    "from x import {n} {m}", "@{e}\nclass C: pass", "@{e}\n@{f}\nclass C({e}): pass", "class C[T]({e}, x={f}): pass",
    "class C(): pass", "class {n}: pass", "class C:\npass", "@{e}\ndef f(): pass", "@{e}\nasync def f(): pass",
    "def f({n}) -> {e}: pass", "def f[T](x: {e} = {f}, *a: *{e}): pass", "async def f(x={e}): pass",
    "def f(x=): pass", "def f(): # type: () -> int\n pass", "def f(*a: {e}): pass", "def f(x: {e}, y={f}): pass",
    "@{e}\nx = 1", "def f({e}): pass", "lambda x={e}: x",
    # left-recursive operators and invalid_assert_stmt (Peg/Rules/LeftRec*.lean, InvalidAssert.lean)
    "{e} - {f} - {e}", "{e} + {f} - {e} + {f}", "{e} * {f} @ {e}", "{e} @ {f}", "{e} // {f} % {e} / {f}",
    "{e} << {f} >> {e}", "{e} | {f} ^ {e} & {f}", "{e} | {f} | {e}", "{e} + not {f}", "{e} * not {f}",
    "{e} << not {f}", "{e} -", "{e} & & {f}", "assert {e}, {f} := {e}", "assert {e} = {f}, {e}",
    "assert ({e}) = {f}", "assert {e}, ({f}) = {e}",
    # match_stmt and decorators (Peg/Rules/Match.lean, Decorators.lean)
    "match {e}:\n case 1: pass", "match {e}\n case 1: pass", "match {e}:\ncase 1: pass", "match {e}, {f}:\n case _: pass",
    "match:\n case 1: pass", "@{e}\n@{f}\n@{e}\ndef g(): pass", "@{e} @{f}\ndef g(): pass", "@\ndef g(): pass",
    "@{e}\n\ndef g(): pass", "@{e}\nclass C: pass",
    # primary, t_primary, atom, slices, targets (Peg/Rules/Primary.lean, TPrimary.lean, Atom.lean,
    # Targets.lean, Targets2.lean)
    "{e}.b(c)[d]", "f({e} for x in y)", "f({e} for x in y, 1)", "f({e})({f})", "f(x for x in {e})[0]",
    "a[{e}:{f}:{e}]", "a[{e}, {f}]", "a[{e},]", "a[*{e}]", "a[::]", "a[{e}:]", "a[:{f}]", "a[{e}, *{f}]",
    "{e}.b = 1", "{e}[0] = 1", "{e}.b.c = 1", "{e}(x).b = 1", "*{e}, = 1", "{e}, {f} = 1", "[{e}, *{f}] = 1",
    "({e}) = 1", "({e}, {f}) = 1", "[{e}] = 1", "* {e} = 1", "**{e}, = 1", "{e}(x for x in y).b = 1",
    "del {e}.x, {f}[0]", "del ({e}, {f})", "del [{e}]", "del {e},", "del ({e})", "del {e}[{f}:]",
    "a.{n}", "True.x", "None[0]", "...", "...[0]", "f(**{e})", "a.b(c)[{e}].d = {f}", "x[a := 1]",
    "x[a, b:c]", "{e}.", "{e}[", "{e}(", "{e}[]", "(x for x in {e})", "[{e}]", "{{{e}}}", "{{{e}: {f}}}",
    "'s'.x", "1 .real", "1.real", "f'{e}'.x", "for {e}.x in y: pass", "for {e}[0] in y: pass",
    "with a as {e}.b: pass", "with a as ({e}, {f}): pass", "x: {e}[0] = 1", "{e}.x: int",
    # imports, patterns, invalid assignments (Peg/Rules/Imports.lean, Patterns.lean, InvalidTargets.lean)
    "import {n}.x as y", "import a . b . c", "import a.b as {n}", "from x import a as b, c as {n}",
    "from x import ({n}, a as b,)", "import a, b.c as d, {n}",
    "match {e}:\n case (a): pass", "match {e}:\n case (a,): pass", "match {e}:\n case a | {k}: pass",
    "match {e}, {f}:\n case _: pass", "match {e},:\n case [a, *_]: pass", "match {e}:\n case (): pass",
    "match {e}:\n case a.b | c.d: pass", "match {e}:\n case (a | b) as c: pass", "match {e}:\n case {k}, *r: pass",
    "match {e}:\n case [{k}, (a, b)]: pass", "match {e}:\n case _ | _: pass", "match *{e}, {f}:\n case _: pass",
    "({e}, {f}): int", "[{e}]: int", "(({e}, {f})): int", "{e}, {f}: int", "{e}: int", "{e} += 1",
    "({e}) += 1", "{e}, {f} += 1", "del {e}, f()", "del ({e}, {e} + 1)", "{e} = yield = 1",
    # invalid_assignment '=' alternatives, t_primary fallbacks, import-as targets
    # (Peg/Rules/InvalidTargets.lean, TPrimary.lean, AsTarget2.lean)
    "x = {e} = 1", "x = y = {e} = 1", "a, {e} = 1", "x = yield {e} = 1", "yield = {e}", "x = (yield) = {e}",
    "[a, {e}] = 1", "x = {e}, {f} = 1", "{e}[0] = 1", "{e}(x) = 1", "{e}(x for x in y) = 1",
    "{e}[0](1) = 2", "a.b[{e}].c = 1", "for {e}(x)[0] in y: pass", "del {e}(x)[0]", "{e}.b(c)[d] = 1",
    "import a as {e}", "from x import a as {e}", "import a.b as {e}, c", "from x import (a as {e})",
    "import a as {n} {m}", "from x import a as {n}; y", "import a as b{u}", "import a as ({n})",
    "if x: import a as b else: pass", "import a as b = {e}", "from x import a as b, c as {e}",
    # patterns (Peg/Rules/Patterns2.lean)
    "match x:\n case {s}{k} {s}{k}j: pass", "match x:\n case {s}1.5 + 2j: pass", "match x:\n case -1 - 1j: pass",
    "match x:\n case 1 + 1: pass", "match x:\n case 1j + 1j: pass", "match x:\n case -{k}: pass",
    "match x:\n case None | True | False: pass", "match x:\n case 'a' 'b' | f'{e}': pass",
    "match x:\n case a.b.c: pass", "match x:\n case a.b(): pass", "match x:\n case a.b = 1: pass",
    "match x:\n case a.b as {n}: pass", "match x:\n case {k} as _: pass", "match x:\n case {k} as y.z: pass",
    "match x:\n case {{}}: pass", "match x:\n case {{**r}}: pass", "match x:\n case {{**r,}}: pass",
    "match x:\n case {{{k}: a}}: pass", "match x:\n case {{{k}: a, **r}}: pass", "match x:\n case {{{k}: a,}}: pass",
    "match x:\n case {{a.b: c, 'k': d, None: e, -1: f, 1+2j: g}}: pass", "match x:\n case {{**_}}: pass",
    "match x:\n case {{{k}: a, **r, }}: pass", "match x:\n case {{**r, {k}: a}}: pass", "match x:\n case {{x: 1}}: pass",
    "match x:\n case C(): pass", "match x:\n case C({k}): pass", "match x:\n case C({k},): pass",
    "match x:\n case C(a={k}): pass", "match x:\n case C(a={k},): pass", "match x:\n case C({k}, a={k}): pass",
    "match x:\n case a.b.C({k}, *r): pass", "match x:\n case C(a=1, {k}): pass", "match x:\n case C(a.b=1): pass",
    "match x:\n case [*_, *r]: pass", "match x:\n case [*{n}]: pass", "match x:\n case (*a, b): pass",
    "match x:\n case *a: pass", "match x:\n case {k} if {e}: pass", "match x:\n case {k} if {e} := 1: pass",
    "match x:\n case {k} if: pass", "match x:\n case {k}:\n  pass\n case _:\n  pass",
    "match x:\n case {k} if {e}:\n  {f}", "match x:\n case a, b if {e}: pass",
    # parameters and their lambda twins, group/invalid_group, star sequences
    # (Peg/Rules/Params*.lean, Invalid2.lean, Exprs4.lean)
    "def f({p}): pass", "def f({p}, /): pass", "def f({p}, /, {q}): pass", "def f({p}, *, {q}): pass",
    "def f({p}, *{n}, {q}): pass", "def f(*, {q}): pass", "def f({p}, **{n}): pass", "def f(*{n}: *{e}): pass",
    "def f({p}, *{n}, {q}, **k): pass", "def f(a=1, {p}): pass", "def f({p}, /, *, {q}, **k,): pass",
    "def f(\n {p}, # type: int\n {q}\n): pass", "def f({p}, # type: int\n): pass", "def f(*, **k): pass",
    "def f(**k, {p}): pass", "def f(/, {p}): pass", "def f({p}, /, /): pass", "def f(*a, *b): pass",
    "lambda {p}: 0", "lambda {p}, /: 0", "lambda {p}, /, {q}: 0", "lambda {p}, *, {q}: 0",
    "lambda {p}, *{n}, {q}: 0", "lambda *, {q}: 0", "lambda {p}, **{n}: 0", "lambda *{n}, {q}, **k: 0",
    "lambda a=1, {p}: 0", "lambda ({p}): 0", "lambda {p}, /, *, {q}, **k,: 0", "lambda **k, {p}: 0",
    "lambda /, {p}: 0", "lambda *, **k: 0", "lambda {p} {q}: 0", "lambda *a, *b: 0", "lambda {p}, (b): 0",
    "({e})", "(*{e})", "(**{e})", "(*{e}, {f})", "({e}, *{f})", "(yield {e})", "({e} := 1)", "(*{e} for x in y)",
    "[*{e}]", "[{e}, *{f},]", "{{*{e}, {f}}}", "({e},)", "(*{e},)", "[*{e} if x else y]", "{{*{e} or z}}",
    "(**{e} for x in y)", "f(**{e}, *{f})", "print((*{e}))", "x = (**{e})",
    # displays, comprehensions, call arguments, type parameters
    # (Peg/Rules/Comps*.lean, Args*.lean)
    "{{{e}: {f}, **{e}}}", "{{**{e}, {f}: 1,}}", "{{{e}:}}", "{{{e}: {f} for x in y}}", "{{**{e} for x in y}}",
    "{{**{e} for x in y if {f}}}", "[{e} for x in y if {f} if z]", "{{{e} for x in y}}", "({e} for x in y)",
    "({e} async for x in y)", "[{e} async for x in y]", "[{e} for x in]", "[{e} for {f} in y]",
    "[{e} for x in y for z in {f}]", "({e} := 1 for x in y)", "(*{e} for x in y)", "[*{e} for x in y]",
    "{{*{e} for x in y}}", "async def g():\n [{e} async for x in y]", "{e}, {f}, {e}", "({e}, {f},)",
    "f({e}, {f})", "f({e}, *{f})", "f({e}, x={f})", "f(**{e}, x={f})", "f(x={e}, *{f})", "f(*{e}, **{f})",
    "f({e}, {f}=1)", "f({e} for x in y)", "f(x={e} for x in y)", "f({e},)", "f(x={e},)", "f(**{e}, *{f})",
    "f(x=1, {e})", "f({e} := 1)", "f(x := {e})", "f(*{e} if x else y)",
    "def f[{n}](): pass", "def f[{n}: {e}](): pass", "def f[{n} = {e}](): pass", "def f[*{n}](): pass",
    "def f[*{n} = *{e}](): pass", "def f[**{n}](): pass", "def f[**{n} = {e}](): pass", "class C[{n},]: pass",
    "type X[{n}: {e} = {f}] = int", "def f[{n}, *Ts, **P](): pass", "def f[](): pass", "def f[*{n}: {e}](): pass",
    # rules stated as equations (Peg/Rules/Spec*.lean): invalid_ rules, statements, targets, strings
    "def f(**{n}={e}): pass", "def f(**{n}, {p}): pass", "def f(**{n}, *a): pass", "def f(**{n}, /): pass",
    "lambda **{n}={e}: 0", "lambda **{n}, {p}: 0", "lambda **{n}, **b: 0", "class C[]: pass", "type X[] = {e}",
    "{e} <> {f}", "{e} < > {f}", "{e} <>", "f(*)", "print(*)", "x = {e} if {f} else *{e}",
    "x = {e} if {f} else **{e}", "{{**{e} if {f} else {e}}}", "{{*{e}: 1}}", "{{**{e}: 1}}", "{{{e}: *{f}}}",
    "{{{e}: **{f}}}", "{{{e}: 1, {f}}}", "{{{e}:}}", "{{{e}:,}}", "{{{e}: 1, *{f}: 2}}", "{u}not {e}",
    "{e} + not {f}", "{e} // not {f}", "{e} @ not {f}", "{e} % not {f}", "{e} | not {f}",
    "if {e}\n pass", "if {e}:\npass", "if x:\n pass\nelif {e}\n pass", "if x:\n pass\nelif {e}:\npass",
    "if x:\n pass\nelse:\npass", "if x:\n pass\nelse:\n pass\nelif {e}:\n pass", "while {e}\n pass",
    "while {e}:\npass", "for {n} in {e}\n pass", "for {n} in {e}:\npass", "async def g():\n async for {n} in {e}:\n pass",
    "def f({p}):\npass", "async def f({p}) -> {e}:\npass", "def f[T]({p}):\npass", "def f:\n pass", "def f({p}) pass",
    "class C\n pass", "class C({e}):\npass", "class C[T]({e})\n pass", "try:\npass", "try:\n pass\n{e}",
    "try:\n pass\nexcept {e}, {f} as y:\n pass", "try:\n pass\nexcept {e}\n pass", "try:\n pass\nexcept\n pass",
    "try:\n pass\nexcept {e} as {f}:\n pass", "try:\n pass\nexcept* {e}, {f} as y:\n pass",
    "try:\n pass\nexcept* {e}\n pass", "try:\n pass\nexcept*:\n pass", "try:\n pass\nexcept*\n pass",
    "try:\n pass\nexcept* {e} as {f}:\n pass", "try:\n pass\nfinally:\npass", "try:\n pass\nexcept {e}:\npass",
    "try:\n pass\nexcept:\npass", "try:\n pass\nexcept* {e}:\npass", "try:\n pass\nexcept* {e}:\n pass\nexcept {f}:\n pass",
    "match {e}\n case 1: pass", "match {e}:\ncase 1: pass", "case {k}:\n pass", "match x:\n case {k}\n  pass",
    "match x:\n case {k}:\n pass", "with {e}, {f},:\n pass", "with {e}\n pass", "with ({e}, {f})\n pass",
    "with {e}:\npass", "async def g():\n async with ({e} as b):\n pass", "with {e} as {f}:\n pass",
    "with {e} as ({f}, 1):\n pass", "for {e} in x: pass", "[x for {e} in y]", "[x for a {e} in y]",
    "from {n} lazy import {m}", "from .{n} lazy import ({m})", "from a import {m},\n", "from a import\n",
    "match x:\n case a as {e}: pass", "match x:\n case C(a=1, {k}): pass", "match x:\n case C({k}, a=1, b, c): pass",
    "match x:\n case {{**r, {k}: a}}: pass", "match x:\n case {{{k}: a, **r, 2: b,}}: pass",
    "f(**{e}, *{f})", "f({e} for a in b, {f})", "f({n}={e} for a in b)", "f({e}, {n}=)", "f({n}=)",
    "f({e}, {f} for b in c)", "f({e}, {f} for b in c, d)", "f({n}=1, {e})", "f(**{e}, {f})", "f(True=1)",
    "f(None=1)", "f({e}={f})", "f(**{e}={f})", "print {e}", "exec {e}", "{n} {e}", "def f[*T: {e}](): pass",
    "def f[**P: {e}](): pass", "'a' {e} 'b'", "{e} {f}", "{e} if {f}", "{e} if {f} else pass",
    "pass if {e} else pass", "f'{{lambda x: {e}}}'", "t'{{lambda x: {e}}}'", "({e} := 1) := 2",
    "{e} := 1", "if {n} = {e}: pass", "if {e} = 1: pass", "if ({e}) = 1: pass", "[**{e} for a in b]",
    "(**{e} for a in b)", "[{e}, {f} for a in c]", "{{{e}, {f} for a in c}}", "[{e}, for a in c]",
    "def f(*): pass", "def f(*, **k): pass", "def f(*{n}={e}): pass", "def f(*a, *b): pass", "def f(*, # type: int\n): pass",
    "lambda *: 0", "lambda *, **k: 0", "lambda *{n}={e}: 0", "lambda *,: 0", "lambda {n}=: 0", "lambda {p}=, b: 0",
    "type X = {e}", "type {n}[T] = {e}", "x = 1; {e}", "{e};", "{e}; {f};", "del ({e}, {f}), [{e}]",
    "[{e}, *{f}] = 1", "({e}, {f},) = 1", "[] = {e}", "() = {e}", "{e}.x: int = 1", "{e}[0]: int",
    "f'{{{e}}}'", "f'{{{e}!r}}'", "f'{{{e}=}}'", "f'{{{e}:>{f}}}'", "f'{{{e}!}}'", "f'{{{e}!z}}'", "f'{{{e}:{{{f}}}}}'",
    "t'{{{e}}}'", "t'{{{e}!r}}'", "t'{{{e}=}}'", "t'{{{e}:>{f}}}'", "t'{{{e}!}}'", "t'{{{e}!z}}'", "t'{{{e}:{{{f}}}}}'",
    "f'{{x:{{{e}:}}'", "t'{{x:{{{e}:}}'", "t'{{x:{{{e}}}'", "f'{{{e}'", "t'{{{e}'", "f'{{'", "t'{{'", "f'{{=}}'",
    "t'{{!}}'", "f'{{:}}'", "t'{{}}}}'", "'a' t'{{{e}}}'", "t'{{{e}}}' 'a'", "t'a' t'b'", "f'a' 'b' f'{{{e}}}'",
    "b'a' t'b'", "u'a' 'b'", "'a' b'b'",
]
RULE_PARAMS = ["a", "a, b", "a=1", "a, b=2", "a: int", "a: int = 1", "a=1, b", "*a", "**a", "a, *b",
               "a=1, /", "a, /", "*, a", "a, b, /, c", "a=1, b=2", "a=", "1", "(a)", "a:", "a b", ""]


def gen_rule_target(rng):
    def pick(xs):
        return rng.choice(xs)
    form = pick(RULE_FORMS)
    src = form.format(e=pick(RULE_EXPRS), f=pick(RULE_EXPRS), n=pick(RULE_NAMES),
                      m=pick(RULE_NAMES), s=pick(["", "+", "-", "+ ", "- ", "--", "~"]),
                      k=pick(["1", "0", "1.5", "1j", "0x10", "1_0", "x", "(1)"]),
                      u=pick(["", "-", "+", "~", "not ", "- "]),
                      p=pick(RULE_PARAMS), q=pick(RULE_PARAMS))
    if rng.random() < 0.3:
        src = "def f():\n    " + src.replace("\n", "\n    ")
    if rng.random() < 0.2:
        src = rng.choice(["while x:\n    ", "for a in b:\n    ", "if x:\n    "]) + src
    return src + rng.choice(["\n", "\n", "", " \n", "\nx\n", ";\n", " # c\n"])


# ---- the string helpers of Parser/action_helpers.c (Peg/HelperProps.lean): literal parts and
# their escapes, conversions (repr of the name, ZWJ), debug fields, format specs (\N{...} splits a
# spec into two constants), concatenation of u/U/b/B/r/f/t literals, invalid escapes in multi-line
# strings (the warning lines)

STR_BODIES = ["", "a", "ab", r"\d", r"\n", r"a\db", r"\x41", r"\N{DIGIT ONE}", r"\N{BEL}x",
              r"\u00e9", r"\101", r"\777", r"\8", "é", r"é\d", "\\\n", "\n\\d\n", "a\nb",
              r"\{", r"\xZ", r"\N{foo}", "''", r"\'", "\n\n\\d"]
STR_FIELDS = ["{x}", "{x!r}", "{x!s}", "{x!a}", "{x!z}", "{x!ab}", "{x! r}", "{x!r }", "{x!\u200d}",
              "{x!a\u200d}", "{x!\ufb01}", "{x=}", "{x = }", "{x=!r}", "{x=:>3}", "{x=!s:^{w}}",
              "{x:}", "{x:>3}", "{x:{y}}", "{x:a{y}b}", r"{x:\N{DIGIT ONE}b}", r"{x:\N{DIGIT ONE}}",
              r"{x:\N{DIGIT ONE}\N{DIGIT TWO}}", r"{x:a\N{BEL}}", r"{x:{y}\N{BEL}}", r"{x:\xZ}",
              r"{x:\d}", "{x:{{}}}", "{{", "}}", "{x:{y=}}", "{ x }", "{x\n=}", "{x:{y:{z}}}"]
STR_PREFIXES = ["", "u", "U", "r", "R", "b", "B", "rb", "Br", "f", "F", "rf", "fR", "t", "T", "rt",
                "tR"]
STR_QUOTES = ["'", '"', "'" * 3, '"' * 3]


def gen_str_literal(rng):
    pfx = rng.choice(STR_PREFIXES)
    q = rng.choice(STR_QUOTES)
    fields = "f" in pfx.lower() or "t" in pfx.lower()
    parts = []
    for _ in range(rng.choice([0, 1, 1, 2, 3])):
        parts.append(rng.choice(STR_FIELDS if fields and rng.random() < 0.5 else STR_BODIES))
    body = "".join(parts)
    if len(q) == 1 and rng.random() < 0.9:
        body = body.replace("\n", "")
    return pfx + q + body + q


def gen_string_helpers(rng):
    lits = [gen_str_literal(rng) for _ in range(rng.choice([1, 1, 2, 2, 3]))]
    src = rng.choice([" ", "", "\n "]).join(lits)
    head = rng.choice(["x = ", "", "f(", "(", "print("])
    if head.endswith("("):
        return head + src + ")\n"
    if "\n " in src:
        src = "(" + src + ")"
    return head + src + "\n"


LAZY_FORMS = ["from {d} lazy import x\n", "from {d}lazy import x\n", "from {d} lazy import (a,\n b)\n",
              "x = 1\nfrom {d} lazy import x\n", "from {d} lazy import x\ny = (\n",
              "from {d} lazy import x\nfrom {d} lazy import y\n", "lazy from {d} import x\n",
              "from {d} lazy import *\n", "def f():\n    from {d} lazy import x\n",
              "from {d}  lazy import x as y, z\n", "from {d} lazy import x\n1 +\n",
              "if x:\n  from {d} lazy import x\nelse:\n  pass\n", "from {d} lazy.b import x\n",
              "from {d} lazy import x; from {d} lazy import y\n", "from {d} \\\n lazy import x\n",
              "from {d}\tlazy import x\n", "from {d} lazy import x # c\n", "from {d} lazy import\n",
              "from {d} lazy import x\n'\\d'\n", "lazy from {d} lazy import x\n"]
LAZY_DOTS = [".", "..", "...", ". .", ". ...", "....", ".. .", "", "a"]


def gen_lazy_case(rng):
    """`_warn_relative_import_of_lazy` under a warnings filter that may turn it into an error."""
    src = rng.choice(LAZY_FORMS).replace("{d}", rng.choice(LAZY_DOTS))
    c = make_case(src, rng)
    if c is None:
        return None
    c["fn"] = "peg.parse"
    c["mode"] = rng.choice(["exec", "exec", "exec", "single"])
    c.pop("flags", None)
    c.pop("feature_version", None)
    # Only warnings the model turns into errors may be present.
    with warnings.catch_warnings(record=True) as seen:
        warnings.simplefilter("always")
        try:
            compile(src, "<unknown>", c["mode"], flags=ast.PyCF_ONLY_AST, dont_inherit=True)
        except Exception:
            pass
    if any(not str(w.message).startswith("'from ") for w in seen):
        return c
    c["warn_error"] = rng.choice([["SyntaxWarning"], ["SyntaxWarning", "DeprecationWarning"],
                                  ["DeprecationWarning"], []])
    return c


def gen_case_peg(rng):
    if rng.random() < 0.04:
        return gen_lazy_case(rng)
    if rng.random() < 0.15:
        c = make_case(gen_string_helpers(rng), rng)
        if c is not None and rng.random() < 0.35:
            c["fn"] = "peg.warn"
        return c
    if rng.random() < 0.3:
        c = make_case(gen_rule_target(rng), rng)
        # the rule statements pin type comments and CHECK_VERSION paths: reach them more often
        if c is not None and c["mode"] == "exec":
            if rng.random() < 0.2:
                c["type_comments"] = True
            if rng.random() < 0.1:
                c["feature_version"] = rng.choice([4, 9, 10, 13])
        return c
    if rng.random() < 0.12:
        src = rng.choice(REPIN)
        if rng.random() < 0.3:
            src = mutate(src, rng)
        c = make_case(src, rng)
        if c is not None and rng.random() < 0.4:
            c["fn"] = "peg.warn"
        return c
    r = rng.random()
    if r < 0.4:
        src = gen_source(rng)
    elif r < 0.5:
        src = mutate(gen_source(rng), rng)
    elif r < 0.75:
        src = rng.choice(CORPUS)
    elif r < 0.95:
        src = mutate(rng.choice(CORPUS), rng)
    elif r < 0.995:
        path = rng.choice(LIBFILES)
        text = path.read_text(encoding="utf-8", errors="replace")
        lines = text.splitlines(True)
        i = rng.randrange(len(lines))
        src = "".join(lines[i:i + rng.choice([1, 2, 5, 20])])
    else:
        src = rng.choice(LIBFILES).read_text(encoding="utf-8", errors="replace")
    return make_case(src, rng)


def run_python_peg(c):
    src = bytes(c["src"]).decode("utf-8")
    flags = ast.PyCF_ONLY_AST | c.get("flags", 0)
    if c.get("type_comments"):
        flags |= ast.PyCF_TYPE_COMMENTS
    fv = c.get("feature_version", -1)
    if c["fn"] == "peg.warn":
        with warnings.catch_warnings(record=True) as seen:
            warnings.simplefilter("always")
            try:
                compile(src, "<unknown>", c["mode"], flags=flags, _feature_version=fv, dont_inherit=True)
            except Exception:
                pass
        return {"ok": [[w.category.__name__, str(w.message), w.lineno] for w in seen]}
    try:
        with warnings.catch_warnings():
            for cat in c.get("warn_error", []):
                warnings.simplefilter("error", getattr(builtins, cat))
            t = compile(src, "<unknown>", c["mode"], flags=flags, _feature_version=fv, dont_inherit=True)
        return {"ok": enc(t)}
    except SyntaxError as e:
        text = None if e.text is None else [ord(x) for x in e.text]
        return {"exc": type(e).__name__,
                "msg": f"{e.msg}|{e.lineno}|{e.offset}|{e.end_lineno}|{e.end_offset}|"
                       + (str(text).replace(" ", "") if text is not None else "None")}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": f"{e}|None|None|None|None|None"}




# ---- part lexer

LEX_EDGE = ["", "\n", "\r", "\r\n", "\n\n", " ", "\t", "\f", "\\", "\\\n", "\\\r\n", "\\\n\n", "\\x", "#", "# c",
        "#\n", "  #\n", "a", "a\n", "if x:\n  y\n", "if x:\n\ty\n        z\n", "if x:\n        y\n\tz\n",
        "if x:\n    y\n  z\n", "(", ")", "(]", "[)", "{", "}", "((\n))", "(\n", "'", '"', "'''", '"""',
        "'a", "'a\\", "'a\\\n", "'''a", "'''a\n", "b'é'", "0x", "0xg", "0o8", "0o", "0b2", "0b", "1_", "1__0",
        "0_0", "00", "01", "0777", "1e", "1e+", "1ea", "1if x else y", "1and 2", "1or 2", "1in x", "1is x",
        "1not in x", "0x1for x in y", "0b1or 1", "1jif x else y", "1.2.3", "1..", "...", "..", ".", ".5",
        "$", "?", "!", "`", "!=", "<>", "->", ":=", "**=", "//=", ">>=", "<<=", "@=", "é", "数", "€", "a€",
        "\u00a0", "a\u00a0", "\u200b", "f'", "f'{", "f'{x", "f'{x}", "f'{x!", "f'{x!r", "f'{x:", "f'{x:y",
        "f'}'", "f'{}'", "f'{{'", "f'}}'", "f'{{}}'", "f'{x}}'", "f'{x:{y}}'", "f'{x:{y:{z}}}'",
        "f'{x:{y:{z:{w}}}}'", "f'{a:{b:{c:{d:{e}}}}}'", "f'{(}'", "f'{)}'", "f'{]}'", "f'''{\n}'''",
        "f'''\n{x}\n'''", "f'{x\n}'", "f'''{x:\n}'''", "f'{x:\n}'", "t'{x=}'", "t'''{x=\n}'''",
        "f'\\N{BULLET}'", "f'\\N'", "f'\\{x}'", "rf'\\{x}'", "f'\\'", "f'{x=!r:^3}'", "f'{x=#\n}'",
        "f'''{x #c\n=}'''", "ub''", "bf''", "ft''", "tb''", "ur''", "BR''", "Rb''", "rF''", "fR''", "Tr''",
        "    a\n", "\ta\n", "\f\ta\n", "\\\n    a\n", "   \\\n a\n", "a\\\n", "a\\", "x = 1 \\\n  + 2\n",
        "def f():\n\tpass\n        pass\n",
        "(]\n", "[)\n", "{)\n", "(\n]\n", "[\n}\n", "f'{(]}'\n", "f'{[)}'\n", "f'{{(]}}'\n", "f'{a(]}'\n",
        "f'{)}'\n", "f'{]}'\n", "f\'\'\'{(\n]}\'\'\'\n", "f'{x:{(]}}'\n", "t'{(]}'\n", "f'{(}'\n", "f'{[}'\n",
        "1 <> 2\n", "a<>b\n", "<>\n", "<>=\n", "a <>= b\n", "<<>\n", "<>>\n",
        "é (]\n", "é )\n", "é = 0x\n", "é = 1__0\n", "\'é\' $\n", "é ?\n", "数 = 1e\n", "f'é{(]}'\n",
        "f'{a\n", "f\'\'\'{a\n\n\'\'\'\n", "f\'\'\'{(\n\'\'\'\n", "f\'\'\'{a}{b\n\'\'\'\n", "t\'\'\'{a\n\'\'\'\n",
        "f\'\'\'{\"\\\"#x\"=#c\n}\'\'\'\n", "t\'\'\'{\'\\\'#\'=}\'\'\'\n", "t\'\'\'{x=#c\n}\'\'\'\n",
        "f\'\'\'{x=!r\n}aaa\'\'\'\n", "lazy import a\n", "lazy from a import b\n", "from . lazy import a\n"]
LEX_EDGE.append("def f(a):pass\nf\"{f lambda a=(:'\u00e0'\n)}\"")
LEX_EDGE.append("(" * 201 + ")" * 201)
LEX_EDGE.append("".join(" " * i + "if x:\n" for i in range(102)))
LEX_EDGE.append("f'{" * 151)
LEX_EDGE.append("f'''{x=!r\n}" + "a" * 40 + "'''\n")
LEX_EDGE.append("t'''{x\n!r\n}" + "a" * 40 + "'''\n")


def gen_text(rng):
    r = rng.random()
    if r < 0.3:
        return rng.choice(LEX_EDGE)
    if r < 0.4:
        return mutate(rng.choice(LEX_EDGE), rng)
    if r < 0.6:
        return gen_source(rng)
    if r < 0.9:
        return mutate(rng.choice(CORPUS), rng)
    if r < 0.999:
        path = rng.choice(LIBFILES)
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines(True)
        i = rng.randrange(len(lines))
        return "".join(lines[i:i + rng.choice([1, 2, 5, 20, 60])])
    return rng.choice(LIBFILES).read_text(encoding="utf-8", errors="replace")


COOKIES = ["# coding: latin-1\n", "#coding=utf-8\n", "# -*- coding: ascii -*-\n", "# vim: set fileencoding=utf_8 :\n",
           "  # coding: UTF-8\n", "\f# coding: Latin_1-unix\n", "x = 1 # coding: latin-1\n", "#\n# coding: latin-1\n",
           "\n# coding: latin-1\n", "x\n# coding: latin-1\n", "#\n#\n# coding: latin-1\n", "# coding:\n", "# coding: \n",
           "# coding : latin-1\n", "# encoding: iso-8859-1\n", "# coding: iso_latin_1-x\n", "#coding:utf8\n", "# coding=", "#cod",
           "", "\n", "# nothing\n", "#\r# coding: ascii\n", "#\r\n# coding: ascii\r\n"]


def gen_case_lex(rng):
    r = rng.random()
    if r < 0.1:
        return {"mod": "pygrammar", "fn": "lex.cookie", "src": list(rng.choice(COOKIES).encode())}
    if r < 0.25:
        text = gen_text(rng)
        try:
            text.encode("utf-8")
            list(tokenize.generate_tokens(io.StringIO(text).readline))
        except Exception:
            return None
        if "\0" in text:
            return None
        return {"mod": "pygrammar", "fn": "lex.untokenize", "text": [ord(c) for c in text]}
    text = gen_text(rng)
    if rng.random() < 0.1:
        text = text.replace("\n", rng.choice(["\r\n", "\r", "\n\n", "\n\f", " \n", "\t\n"]))
    try:
        text.encode("utf-8")
    except UnicodeEncodeError:
        return None
    if "\0" in text:
        return None
    return {"mod": "pygrammar", "fn": "lex.tokens", "text": [ord(c) for c in text],
            "extra": rng.random() < 0.7}


def run_python_lex(c):
    if c["fn"] == "lex.cookie":
        try:
            enc = tokenize.detect_encoding(io.BytesIO(bytes(c["src"])).readline)[0]
        except SyntaxError as e:
            enc = e.msg.rsplit(": ", 1)[1]
        return {"ok": [ord(x) for x in enc]}
    if c["fn"] == "lex.untokenize":
        text = "".join(map(chr, c["text"]))
        try:
            out = tokenize.untokenize(tokenize.generate_tokens(io.StringIO(text).readline))
            return {"ok": [ord(x) for x in out]}
        except (ValueError, IndexError):
            return {"ok": None}
    text = "".join(map(chr, c["text"]))
    toks = []
    err = None
    try:
        for t in _tokenize.TokenizerIter(io.StringIO(text).readline, extra_tokens=c["extra"]):
            toks.append([t[0], [ord(x) for x in t[1]], t[2][0], t[2][1], t[3][0], t[3][1],
                         [len(t[4]), sum(map(ord, t[4]))]])
    except SyntaxError as e:
        tx = "None" if e.text is None else "[" + ",".join(str(ord(x)) for x in e.text) + "]"
        err = f"{type(e).__name__}|{e.msg}|{e.lineno}|{e.offset}|{tx}"
    except Exception as e:
        err = f"{type(e).__name__}|{e}|None|None|None"
    return {"ok": [toks, err]}




# ---- part check

FOLD = ["__debug__", "if __debug__: pass", "x = __debug__", "__debug__ = 1", "def f():\n  '''d'''\n",
        "def f[T: __debug__ = __debug__](): pass\n", "class C[*Ts = __debug__]: pass\n",
        "def g[**P = __debug__](): pass\n", "type X[T: __debug__ = __debug__] = __debug__\n",
        "match x:\n  case __debug__.y: pass\n", "match x:\n  case {__debug__.y: 1}: pass\n",
        "match x:\n  case __debug__(a=1): pass\n", "match x:\n  case [__debug__.y, *z] if __debug__: pass\n",
        "def f(a=__debug__, *, b=__debug__): pass\n", "lambda a=__debug__: __debug__\n",
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
        "from __future__ import *",
        # `%.100s` of the feature name cuts UTF-8 bytes: 51 'é' print as 50, a cut inside a character.
        "from __future__ import " + "\u00e9" * 51, "from __future__ import a" + "\u00e9" * 50,
        "from __future__ import " + "\u4e2d" * 34, "from __future__ import " + "x" * 101,
        "match x:\n  case +1: pass\n", "match x:\n  case +1.5: pass\n", "match x:\n  case +1j: pass\n",
        "match x:\n  case +1+2j: pass\n", "match x:\n  case +1-2j: pass\n", "match x:\n  case +0.0+1j: pass\n",
        "match x:\n  case -0.0+1j: pass\n", "match x:\n  case +0.0-1j: pass\n", "match x:\n  case {+1: y, +1+2j: z}: pass\n",
        "match x:\n  case [+1, (+2 | 3), C(+4, a=+5)] as y: pass\n",
        "{**__debug__ for a in b}\n", "{**a for a in __debug__}\n", "{**a for a in b if __debug__}\n",
        "lazy import a\n", "lazy from a import b\n", "lazy from .a import b as c\n",
        "from __future__ import annotations as b\n", "lazy from a import __debug__\n",
        "try: pass\nexcept A as b: pass\n", "try: pass\nexcept* A as b: pass\n",
        "import a as b\nfrom c import d as e\n", "def f(): pass\nclass C: pass\nasync def g(): pass\n"]


def src_case(rng):
    r = rng.random()
    if r < 0.35:
        s = rng.choice(FOLD)
    elif r < 0.65:
        s = gen_source(rng)
    elif r < 0.99:
        s = rng.choice(CORPUS)
    else:
        path = rng.choice(LIBFILES)
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
                       ast.UnaryOp(ast.UAdd(), ast.Constant(1, **loc), **loc),
                       ast.UnaryOp(ast.UAdd(), ast.Constant(1j, **loc), **loc),
                       ast.UnaryOp(ast.UAdd(), ast.Constant("s", **loc), **loc),
                       ast.UnaryOp(ast.Not(), ast.Constant(1, **loc), **loc),
                       ast.UnaryOp(ast.Invert(), ast.Constant(1, **loc), **loc),
                       ast.BinOp(ast.UnaryOp(ast.UAdd(), ast.Constant(1, **loc), **loc), ast.Add(),
                                 ast.Constant(1j, **loc), **loc),
                       ast.BinOp(ast.UnaryOp(ast.Not(), ast.Constant(1, **loc), **loc), ast.Add(),
                                 ast.Constant(1j, **loc), **loc),
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
                elif z < 0.8 and v and isinstance(v[0], (ast.expr, ast.stmt)):
                    v[rng.randrange(len(v))] = None
                elif v and isinstance(v[0], ast.expr):
                    v.append(mk_expr(rng))
            elif isinstance(v, ast.expr_context):
                setattr(n, f, rng.choice([ast.Load(), ast.Store(), ast.Del()]))
            elif isinstance(n, ast.DictComp) and f == "value" and rng.random() < 0.5:
                n.value = None
            elif isinstance(v, ast.expr):
                setattr(n, f, mk_expr(rng))
            elif isinstance(v, str):
                setattr(n, f, rng.choice(["None", "True", "False", "_", "x"]))
            elif isinstance(v, int) and not isinstance(v, bool):
                setattr(n, f, rng.choice([-1, 0, 1, 2]))
            elif v is None and f in ("cause", "rest", "name", "guard", "value", "pattern", "msg"):
                if isinstance(n, ast.ExceptHandler) and f == "name":
                    n.name = rng.choice(["None", "True", "False", "_", "x"])
                elif isinstance(n, ast.DictComp) and f == "value":
                    n.value = mk_expr(rng)
            elif v is None and f == "asname":
                n.asname = rng.choice(["None", "True", "False", "_", "x"])
    return t


CRASHES = 0


def survives(tree, mode):
    """Compile a mutated tree in a forked child, since a malformed tree can kill the process."""
    global CRASHES
    pid = os.fork()
    if pid == 0:
        try:
            compile(tree, "x", mode, flags=ast.PyCF_OPTIMIZED_AST)
        except BaseException:
            pass
        os._exit(0)
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status):
        CRASHES += 1
        if CRASHES <= 8:
            print("CRASH", os.WTERMSIG(status), ast.dump(tree)[:600], file=sys.stderr)
        return False
    return True


def gen_case_check(rng):
    got = src_case(rng)
    if got is None:
        return None
    s, t = got
    if rng.random() < 0.5:
        mode = {ast.Module: "exec"}.get(type(t), "exec")
        t2 = mutate_tree(copy.deepcopy(t), rng) if rng.random() < 0.9 else t
        try:
            tree = enc(t2)
            json.dumps(tree)
        except Exception:
            return None
        if not survives(t2, mode):
            return None
        try:
            compile(t2, "x", mode, flags=ast.PyCF_OPTIMIZED_AST)
        except TypeError as e:
            # raised by obj2ast in Python/Python-ast.c, before the validator runs
            if "required field" in str(e) or "expected some sort of" in str(e) \
                    or "field " in str(e):
                return None
        except Exception:
            pass
        return {"mod": "pygrammar", "fn": "check.validate", "tree": tree, "pytree": None,
                "_t": t2, "_mode": mode}
    o = rng.choice([-1, 0, 1, 2])
    if rng.random() < 0.1:
        # `astfold_mod` on `Expression`
        e = rng.choice(["__debug__", "(__debug__, x)", "'%s' % (__debug__,)", "[__debug__ for x in y]",
                        "lambda a=__debug__: __debug__", "f'{__debug__}'", "x[__debug__:]", "'%s' % (x,)"])
        return {"mod": "pygrammar", "fn": "check.preprocess", "tree": enc(ast.parse(e, mode="eval")),
                "optimize": o, "syntax_only": False, "src": e, "pmode": "eval"}
    return {"mod": "pygrammar", "fn": "check.preprocess", "tree": enc(t), "optimize": o,
            "syntax_only": False, "src": s}


def run_python_check(c):
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
        t = compile(c["src"], "<unknown>", c.get("pmode", "exec"), flags=ast.PyCF_OPTIMIZED_AST,
                    optimize=c["optimize"])
        return {"ok": enc(t)}
    except SyntaxError as e:
        return {"exc": "SyntaxError",
                "msg": f"{e.msg}|{e.lineno}|{e.offset}|{e.end_lineno}|{e.end_offset}|None"}




# ---- part unparse

sys.setrecursionlimit(5000)

UNP_EDGE = ["lazy import a", "lazy import a.b as c, d", "lazy from a import b", "lazy from . import b",
        "lazy from ..a import b as c", "lazy from a import *", "lazy from a import (b, c)",
        "{**d for d in x}", "{**d for d in x if d}", "{**(a or b) for a in x}", "{**(yield) for a in x}",
        "{**d async for d in x}", "{**(lambda: 0) for a in x}", "{**(a := 1) for a in x}", "{**{**a for a in x} for b in y}",
        r'f"{x:\x7b}"', r'f"{x:\x7d}"', r'f"{x:\x00}"', r'f"{x:\r}"', r'f"{x:\ud800}"', r'u"a" f"{x}"',
        "t'''{\"\\\"#x\" #c\n}'''", "f'''{\"\\\"#x\"=#c\n}'''", "t'''\"\"\"\\'\\'\\'{x\n}'''", "t'{x!r:{y}}'",
        "1e999", "1e999j", "1e308", "1e16", "1e15", "1e-4", "1e-5", "1e22", "1e23", "5e-324", "2.5", "0.1", "1.0",
        "1e100", "123456789012345678.0", "0.0001", "0.00001", "4.35", "2.2250738585072014e-308", "9007199254740993.0",
        "1j", "1.5j", "1e16j", "1e-5j", "0j", "0.0j", "1e999j", "0x" + "f" * 3560, "0x" + "f" * 3600, "'\\ud800'",
        "'\\x00\\x7f\\xa0\\xad\\u200b\\U0001f600'", "b'\\x00\\xff\\'\"'", "b'\"'", "b\"'\"", "'\"'", '"\'"', "'\\'\"'",
        "def f():\n  '''a'''\n", "def f():\n  u'''a'''\n", "def f():\n  ''''''\n", "def f():\n  '\"\"\"'\n",
        "def f():\n  '\\'\\'\\'\"\"\"'\n", "def f():\n  '\"'\n", "def f():\n  \"'\"\n", "def f():\n  '\\n'\n", "def f():\n  '\\\\'\n"]


def gen_case_unparse(rng):
    r = rng.random()
    if r < 0.2:
        s = rng.choice(UNP_EDGE)
    elif r < 0.55:
        s = gen_source(rng)
    elif r < 0.95:
        s = rng.choice(CORPUS)
    else:
        path = rng.choice(LIBFILES)
        s = path.read_text(encoding="utf-8", errors="replace")
    if rng.random() < 0.3:
        return c_case(rng, s)
    mode = rng.choice(["exec", "exec", "exec", "eval", "single"])
    tc = rng.random() < 0.1
    try:
        t = ast.parse(s, mode=mode, type_comments=tc)
        tree = enc(t)
    except (SyntaxError, ValueError, RecursionError):
        return None
    return {"mod": "pygrammar", "fn": "unparse.py", "tree": tree, "_t": t}


def c_case(rng, s):
    """An annotation: `Python/ast_unparse.c` runs under the future import."""
    try:
        t = ast.parse(s, mode="eval")
    except (SyntaxError, ValueError, RecursionError):
        return None
    src = "from __future__ import annotations\nx: (\n" + s + "\n)\n"
    try:
        ns = {}
        exec(compile(src, "x", "exec"), ns)
        ann = ns["__annotations__"]["x"]
        e = ast.parse(src).body[1].annotation
    except (SyntaxError, ValueError, RecursionError, KeyError, MemoryError):
        return None
    return {"mod": "pygrammar", "fn": "unparse.c", "tree": enc(e), "_ann": [ord(x) for x in ann]}


def run_python_unparse(c):
    if c["fn"] == "unparse.c":
        return {"ok": c["_ann"]}
    if c["fn"] == "unparse.py":
        try:
            return {"ok": [ord(x) for x in ast.unparse(c["_t"])]}
        except AssertionError as e:
            return {"exc": "AssertionError", "msg": ""}
        except ValueError as e:
            return {"exc": "ValueError", "msg": str(e)}




PARTS = {"peg": (gen_case_peg, run_python_peg), "lexer": (gen_case_lex, run_python_lex),
         "check": (gen_case_check, run_python_check),
         "unparse": (gen_case_unparse, run_python_unparse)}

if __name__ == "__main__":
    part = "peg"
    if "--part" in sys.argv:
        i = sys.argv.index("--part")
        part = sys.argv[i + 1]
        del sys.argv[i:i + 2]
    orig_dumps = json.dumps

    def dumps(o, *a, **k):
        # keys starting with `_` are Python objects for `run_python`, not for Lean
        if isinstance(o, dict) and any(str(x).startswith("_") for x in o):
            o = {k2: v for k2, v in o.items() if not str(k2).startswith("_")}
        return orig_dumps(o, *a, **k)

    common.json.dumps = dumps
    gen, run = PARTS[part]
    common.main(gen, run, default_cases=5000)
