"""Difftest of the tokenizer: Lean model vs `_tokenize.TokenizerIter`, with and without
extra_tokens, on text from the parser difftest's generators plus lexer edge cases."""

import _tokenize
import io
import random
import sys
import warnings
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import common  # noqa: E402

warnings.simplefilter("ignore")
_argv, sys.argv = sys.argv, sys.argv[:1]
import pygrammar_diff as pd  # noqa: E402
sys.argv = _argv

EDGE = ["", "\n", "\r", "\r\n", "\n\n", " ", "\t", "\f", "\\", "\\\n", "\\\r\n", "\\\n\n", "\\x", "#", "# c",
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
EDGE.append("(" * 201 + ")" * 201)
EDGE.append("".join(" " * i + "if x:\n" for i in range(102)))
EDGE.append("f'{" * 151)
EDGE.append("f'''{x=!r\n}" + "a" * 40 + "'''\n")
EDGE.append("t'''{x\n!r\n}" + "a" * 40 + "'''\n")


def gen_text(rng):
    r = rng.random()
    if r < 0.3:
        return rng.choice(EDGE)
    if r < 0.4:
        return pd.mutate(rng.choice(EDGE), rng)
    if r < 0.6:
        return pd.gen_source(rng)
    if r < 0.9:
        return pd.mutate(rng.choice(pd.CORPUS), rng)
    if r < 0.995:
        path = rng.choice(pd.LIBFILES)
        lines = path.read_text(encoding="utf-8", errors="replace").splitlines(True)
        i = rng.randrange(len(lines))
        return "".join(lines[i:i + rng.choice([1, 2, 5, 20, 60])])
    return rng.choice(pd.LIBFILES).read_text(encoding="utf-8", errors="replace")


def gen_case(rng):
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


def run_python(c):
    text = "".join(map(chr, c["text"]))
    toks = []
    err = None
    try:
        for t in _tokenize.TokenizerIter(io.StringIO(text).readline, extra_tokens=c["extra"]):
            toks.append([t[0], [ord(x) for x in t[1]], t[2][0], t[2][1], t[3][0], t[3][1],
                         [ord(x) for x in t[4]]])
    except SyntaxError as e:
        tx = "None" if e.text is None else "[" + ",".join(str(ord(x)) for x in e.text) + "]"
        err = f"{type(e).__name__}|{e.msg}|{e.lineno}|{e.offset}|{tx}"
    except Exception as e:
        err = f"{type(e).__name__}|{e}|None|None|None"
    return {"ok": [toks, err]}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=5000)
