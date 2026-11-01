"""Difftest of the whole parser: Lean model vs `compile(..., PyCF_ONLY_AST)`.

Source text comes from four places:
  * a random derivation of `Grammar/python.gram`, read with pegen, invalid_ rules included;
  * mutations of such programs and of corpus snippets (token deletion, swap, insertion);
  * every string in CPython's own syntax tests that looks like code
    (`test_syntax`, `test_exceptions`, `test_fstring`, `test_tstring`, `test_grammar`, ...);
  * lines and whole files of `Lib/`.

Trees are compared through `pygrammar_ast.enc`, errors by class, message, lineno, offset,
end_lineno, end_offset and text.
"""

import ast
import random
import re
import sys
import tokenize
import unicodedata
import warnings
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402
import pygrammar_ast as pa  # noqa: E402

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


def gen_case(rng):
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


def run_python(c):
    src = bytes(c["src"]).decode("utf-8")
    flags = ast.PyCF_ONLY_AST
    if c.get("type_comments"):
        flags |= ast.PyCF_TYPE_COMMENTS
    fv = c.get("feature_version", -1)
    try:
        t = compile(src, "<unknown>", c["mode"], flags=flags, _feature_version=fv)
        return {"ok": pa.enc(t)}
    except SyntaxError as e:
        text = None if e.text is None else [ord(x) for x in e.text]
        return {"exc": type(e).__name__,
                "msg": f"{e.msg}|{e.lineno}|{e.offset}|{e.end_lineno}|{e.end_offset}|"
                       + (str(text).replace(" ", "") if text is not None else "None")}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": f"{e}|None|None|None|None|None"}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=5000)
