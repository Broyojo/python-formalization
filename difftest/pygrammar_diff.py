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

for V in (Path("/Users/broyojo/code/projects/python-formalization/vendor/cpython-3.14"),
          Path.home() / "pf" / "cpython-3.14"):
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


NAME_RE = re.compile(r"[^\W\d]\w*")


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
    for m in NAME_RE.finditer(src):
        w = m.group(0)
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
        c["feature_version"] = rng.choice([4, 5, 6, 7, 8, 9, 10, 12, 13])
    return c


def gen_case_peg(rng):
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
    flags = ast.PyCF_ONLY_AST
    if c.get("type_comments"):
        flags |= ast.PyCF_TYPE_COMMENTS
    fv = c.get("feature_version", -1)
    try:
        t = compile(src, "<unknown>", c["mode"], flags=flags, _feature_version=fv)
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
        "def f():\n\tpass\n        pass\n"]
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
        s = gen_source(rng)
    elif r < 0.9:
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
            elif isinstance(v, ast.expr):
                setattr(n, f, mk_expr(rng))
            elif isinstance(v, str):
                setattr(n, f, rng.choice(["None", "True", "False", "_", "x"]))
            elif isinstance(v, int) and not isinstance(v, bool):
                setattr(n, f, rng.choice([-1, 0, 1, 2]))
            elif v is None and f in ("cause", "rest", "name", "guard", "value", "pattern", "msg"):
                pass
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
        t = compile(c["src"], "<unknown>", "exec", flags=ast.PyCF_OPTIMIZED_AST,
                    optimize=c["optimize"])
        return {"ok": enc(t)}
    except SyntaxError as e:
        return {"exc": "SyntaxError",
                "msg": f"{e.msg}|{e.lineno}|{e.offset}|{e.end_lineno}|{e.end_offset}|None"}




# ---- part unparse

sys.setrecursionlimit(5000)

UNP_EDGE = [r'f"{x:\x7b}"', r'f"{x:\x7d}"', r'f"{x:\x00}"', r'f"{x:\r}"', r'f"{x:\ud800}"', r'u"a" f"{x}"',
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
