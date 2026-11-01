#!/usr/bin/env python3
"""Generate the grammar as Lean data from `Grammar/python.gram`.

The grammar is read with CPython's own pegen (`Tools/peg_generator`) and normalised
by its `CParserGenerator`, so artificial rules (`_tmp_N`, `_loop0_N`, `_gather_N`) and
every item's C call are exactly those of `Parser/parser.c`. With `--check`:

  1. the same generator run on the same inputs must reproduce `Parser/parser.c`
     byte for byte, so the objects read here are what CPython compiles;
  2. the committed `Peg/GrammarData.lean` must match what this script writes.

C actions are parsed by the small expression parser below into the `AE` type of
`Peg/Syntax.lean`, so no rule or action is transcribed by hand.
"""

import io
import re
import sys
import tokenize
from pathlib import Path

V = Path("/Users/broyojo/code/projects/python-formalization/vendor/cpython-3.14")
if not V.exists():
    V = Path.home() / "pf" / "cpython-3.14"
sys.path.insert(0, str(V / "Tools" / "peg_generator"))

from pegen.c_generator import CParserGenerator  # noqa: E402
from pegen.grammar import Cut, NamedItem  # noqa: E402
from pegen.grammar_parser import GeneratedParser  # noqa: E402
from pegen.tokenizer import Tokenizer  # noqa: E402
from pegen.build import generate_token_definitions  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT = HERE.parent / "Peg" / "GrammarData.lean"
HELPERS_OUT = HERE.parent / "Peg" / "Helpers.lean"


def load():
    with open(V / "Grammar" / "python.gram") as f:
        tok = Tokenizer(tokenize.generate_tokens(f.readline))
        grammar = GeneratedParser(tok).start()
    with open(V / "Grammar" / "Tokens") as f:
        all_tokens, exact, non_exact = generate_token_definitions(f)
    buf = io.StringIO()
    gen = CParserGenerator(grammar, all_tokens, exact, non_exact, buf)
    gen.generate("python.gram")
    return grammar, gen, buf.getvalue(), all_tokens


# ---------------------------------------------------------------- C action parser

TOKEN_RE = re.compile(r"""
    \s*(?:
      (?P<str>"(?:[^"\\]|\\.)*")
    | (?P<chr>'(?:[^'\\]|\\.)')
    | (?P<num>\d+)
    | (?P<id>[A-Za-z_][A-Za-z_0-9]*)
    | (?P<op>->|==|!=|&&|\|\||[()\[\],?:.!*\-+])
    )""", re.X)


def lex(s):
    out, i = [], 0
    while i < len(s):
        m = TOKEN_RE.match(s, i)
        if not m:
            if not s[i:].strip():
                break
            raise SyntaxError(f"cannot lex {s[i:]!r} in {s!r}")
        i = m.end()
        out.append((m.lastgroup, m.group(m.lastgroup)))
    return out


TYPES = {"expr_ty", "stmt_ty", "arg_ty", "arguments_ty", "pattern_ty", "keyword_ty", "alias_ty",
         "withitem_ty", "excepthandler_ty", "comprehension_ty", "void", "mod_ty", "type_param_ty",
         "asdl_seq", "asdl_stmt_seq", "asdl_expr_seq", "asdl_arg_seq", "asdl_keyword_seq",
         "asdl_alias_seq", "asdl_pattern_seq", "asdl_identifier_seq", "asdl_int_seq",
         "asdl_comprehension_seq", "asdl_withitem_seq", "asdl_excepthandler_seq",
         "asdl_match_case_seq", "asdl_type_param_seq", "Token", "CmpopExprPair",
         "KeyValuePair", "KeyPatternPair", "NameDefaultPair", "SlashWithDefault", "StarEtc",
         "AugOperator", "KeywordOrStarred", "ResultTokenWithMetadata", "PyObject",
         "PegenAlias", "TARGETS_TYPE", "int", "match_case_ty"}

ENUMS = {"Load", "Store", "Del", "And", "Or", "Add", "Sub", "Mult", "MatMult", "Div", "Mod", "Pow",
         "LShift", "RShift", "BitOr", "BitXor", "BitAnd", "FloorDiv", "Invert", "Not", "UAdd",
         "USub", "Eq", "NotEq", "Lt", "LtE", "Gt", "GtE", "Is", "IsNot", "In", "NotIn"}

PRODUCTS = {"arguments", "arg", "keyword", "alias", "withitem", "comprehension", "match_case"}


class P:
    def __init__(self, text, env):
        self.toks = lex(text)
        self.i = 0
        self.env = env
        self.text = text
        self.helpers = set()

    def peek(self, k=0):
        j = self.i + k
        return self.toks[j] if j < len(self.toks) else (None, None)

    def next(self):
        t = self.peek()
        self.i += 1
        return t

    def eat(self, v):
        if self.peek()[1] == v:
            self.i += 1
            return True
        return False

    def expect(self, v):
        if not self.eat(v):
            raise SyntaxError(f"expected {v} at {self.toks[self.i:]} in {self.text}")

    def expr(self):
        c = self.orexpr()
        if self.eat("?"):
            a = self.expr()
            self.expect(":")
            b = self.expr()
            return f"(.ite {c} {a} {b})"
        return c

    def orexpr(self):
        a = self.andexpr()
        while self.eat("||"):
            a = f"(.or_ {a} {self.andexpr()})"
        return a

    def andexpr(self):
        a = self.eqexpr()
        while self.eat("&&"):
            a = f"(.and_ {a} {self.eqexpr()})"
        return a

    def eqexpr(self):
        a = self.addexpr()
        while True:
            if self.eat("=="):
                a = f"(.eq {a} {self.addexpr()})"
            elif self.eat("!="):
                a = f"(.not_ (.eq {a} {self.addexpr()}))"
            else:
                return a

    def addexpr(self):
        a = self.unary()
        while True:
            if self.eat("-"):
                a = f"(.sub {a} {self.unary()})"
            elif self.eat("+"):
                a = f"(.add {a} {self.unary()})"
            else:
                return a

    def unary(self):
        if self.eat("!"):
            return f"(.not_ {self.unary()})"
        if self.eat("-"):
            return f"(.sub (.int 0) {self.unary()})"
        if self.peek()[1] == "(" and self.is_cast():
            self.next()
            self.next()
            while self.eat("*"):
                pass
            self.expect(")")
            return self.unary()
        return self.postfix()

    def is_cast(self):
        return self.peek(1)[1] in TYPES and self.peek(2)[1] in (")", "*")

    def postfix(self):
        e = self.primary()
        while True:
            if self.eat("->"):
                path = [self.next()[1]]
                while self.peek()[1] == "." and self.peek(1)[0] == "id":
                    self.next()
                    path.append(self.next()[1])
                if path[0] == "v":
                    # `x->v.Name.id`: constructor name then field
                    e = f'(.field {e} "{path[2]}")'
                elif path[0] == "kind":
                    e = f"(.kind {e})"
                else:
                    e = f'(.attr {e} "{path[0]}")'
            else:
                return e

    def args(self):
        out = []
        self.expect("(")
        if self.eat(")"):
            return out
        while True:
            out.extend(self.arg())
            if self.eat(")"):
                return out
            self.expect(",")

    def arg(self):
        if self.peek()[1] == "EXTRA" and self.peek(1)[1] in (",", ")"):
            self.next()
            return [".extra0", ".extra1", ".extra2", ".extra3"]
        if self.peek() == ("id", "p") and self.peek(1)[1] == "->" and self.peek(2)[1] == "arena":
            self.i += 3
            return []
        if self.peek() == ("id", "p") and self.peek(1)[1] in (",", ")"):
            self.next()
            return []
        return [self.expr()]

    def primary(self):
        kind, v = self.next()
        if v == "(":
            e = self.expr()
            self.expect(")")
            return e
        if kind == "num":
            return f"(.int {v})"
        if kind == "str":
            # adjacent literals concatenate
            s = v[1:-1]
            while self.peek()[0] == "str":
                s += self.next()[1][1:-1]
            return f'(.str "{s}")'
        if kind == "id":
            if v == "NULL":
                return ".null"
            if v == "p":
                # p->tokens[p->mark-1]  or p->tok
                self.expect("->")
                f = self.next()[1]
                if f == "tokens":
                    self.expect("[")
                    for x in ("p", "->", "mark", "-", "1"):
                        self.expect(x)
                    self.expect("]")
                    return ".lastTok"
                if f == "tok":
                    return ".tokState"
                raise SyntaxError(f"p->{f}")
            if v in self.env:
                return f"(.var {self.env[v]})"
            if v == "PyExc_SyntaxError":
                return '(.str "SyntaxError")'
            if v == "Py_None":
                return ".pyNone"
            if v == "Py_True":
                return ".pyTrue"
            if v == "Py_False":
                return ".pyFalse"
            if v == "Py_Ellipsis":
                return ".pyEllipsis"
            if v in ENUMS:
                return f"(.ctor .{v})"
            if v.endswith("_kind"):
                return f"(.ctor .{v[:-5]})"
            if v in ("STAR_TARGETS", "DEL_TARGETS", "FOR_TARGETS"):
                return f"(.int {['STAR_TARGETS', 'DEL_TARGETS', 'FOR_TARGETS'].index(v)})"
            if v in ("NEWLINE", "NAME"):
                raise SyntaxError(v)
            if self.peek()[1] == "(":
                return self.call(v)
            raise SyntaxError(f"unknown identifier {v} in {self.text}")
        raise SyntaxError(f"bad primary {kind} {v} in {self.text}")

    def call(self, name):
        args = self.call_args(name)
        if name.startswith("_PyAST_"):
            c = name[len("_PyAST_"):]
            c = c + "_" if c in PRODUCTS else c
            return f"(.mk .{c} [{', '.join(args)}])"
        if name in ("CHECK", "CHECK_NULL_ALLOWED"):
            # first argument was a type name; the C macro keeps only the second
            h = "check" if name == "CHECK" else "checkNull"
            return f"(.{h} {args[-1]})"
        if name == "CHECK_VERSION":
            return f"(.checkVersion {args[1]} {args[2]} {args[3]})"
        if name in ("PyPegen_last_item", "PyPegen_first_item"):
            n = "seq_last_item" if "last" in name else "seq_first_item"
            self.helpers.add(n)
            return f"(.call .{n} [{args[0]}])"
        h = name
        for pre in ("_PyPegen_", "_Pypegen_"):
            if h.startswith(pre):
                h = h[len(pre):]
        self.helpers.add(h)
        return f"(.call .{h} [{', '.join(args)}])"

    def call_args(self, name):
        if name in ("CHECK", "CHECK_NULL_ALLOWED", "CHECK_VERSION", "PyPegen_last_item",
                    "PyPegen_first_item"):
            # A type name appears as an ordinary argument of these macros.
            self.expect("(")
            out = []
            while True:
                if self.peek()[1] in TYPES:
                    self.next()
                    while self.eat("*"):
                        pass
                    out.append(".null")
                else:
                    out.extend(self.arg())
                if self.eat(")"):
                    return out
                self.expect(",")
        return self.args()


def parse_action(text, env, helpers):
    p = P(text, env)
    e = p.expr()
    if p.i != len(p.toks):
        raise SyntaxError(f"trailing {p.toks[p.i:]} in {text}")
    helpers |= p.helpers
    return e


# ---------------------------------------------------------------- rules


def lean_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def bytes_list(s):
    return "[" + ", ".join(str(b) for b in s.encode()) + "]"


def call_expr(call, rule_ids, gen):
    """The Lean `Call` for a pegen FunctionCall (function + arguments)."""
    f, args = call.function, call.arguments
    if f == "_PyPegen_expect_token":
        t = args[1]
        if isinstance(t, str):
            t = gen_token_number[t]
        return f"(.tok {t})"
    if f == "_PyPegen_name_token":
        return ".name"
    if f == "_PyPegen_number_token":
        return ".number"
    if f == "_PyPegen_string_token":
        return ".string"
    if f == "_PyPegen_soft_keyword_token":
        return ".softKeywordToken"
    if f == "_PyPegen_expect_soft_keyword":
        return f"(.softKw {bytes_list(eval(args[1]))})"
    if f == "_PyPegen_expect_forced_token":
        return f"(.forcedTok {args[1]} {args[2]})"
    if f == "_PyPegen_expect_forced_result":
        inner = args[1]
        m = re.match(r"^(\w+)_rule\(p\)$", inner)
        assert m, inner
        return f"(.forcedRule {rule_ids[m.group(1)]} {lean_str(eval(args[2]))})"
    if f.endswith("_rule"):
        return f"(.rule {rule_ids[f[:-5]]})"
    raise ValueError(f"unknown call {f}")


def lookahead_call(call, rule_ids):
    """Decode `_PyPegen_lookahead*(positive, fn, p[, arg])`."""
    positive, fn, *rest = call.arguments
    inner = type(call)(function=fn, arguments=rest)
    if fn in ("_PyPegen_expect_token",):
        inner.arguments = ["p", rest[1]]
    elif fn == "_PyPegen_expect_soft_keyword":
        inner.arguments = ["p", rest[1]]
    return bool(positive), inner


gen_token_number = {}


def item_expr(item, gen, rule_ids, env, names):
    """One conjunct of an alternative. Returns the Lean `Item`."""
    call = gen.callmakervisitor.generate_call(item)
    if call.function == "1":  # Cut
        names.append("_cut_var")
        return ".cut"
    if call.function.startswith("_PyPegen_lookahead"):
        positive, inner = lookahead_call(call, rule_ids)
        return f"(.look {'true' if positive else 'false'} {call_expr(inner, rule_ids, gen)})"
    var = item.name if item.name else call.assigned_variable
    slot = len(names)
    names.append(var)
    if var not in env:
        env[var] = slot
    c = call_expr(call, rule_ids, gen)
    if call.force_true:
        return f"(.opt {c})"
    return f"(.call {c})"


def main():
    grammar, gen, text, all_tokens = load()
    for num, name in all_tokens.items():
        gen_token_number[name] = num
    if "--check" in sys.argv:
        vendored = (V / "Parser" / "parser.c").read_text()
        if text != vendored:
            sys.exit("pegen output differs from Parser/parser.c")
        print("pegen reproduces Parser/parser.c")

    rule_ids = {name: i for i, name in enumerate(gen.all_rules)}
    helpers = set()
    defs = []
    for name, rule in gen.all_rules.items():
        i = rule_ids[name]
        rhs = rule.flatten()
        is_loop, is_gather = rule.is_loop(), rule.is_gather()
        alts = []
        for alt in rhs.alts:
            env, names, items = {}, [], []
            for it in alt.items:
                items.append(item_expr(it, gen, rule_ids, env, names))
            guarded = len(alt.items) == 1 and str(alt.items[0]).startswith("invalid_")
            action = alt.action
            if action:
                act = "(some " + parse_action(action, env, helpers) + ")"
            else:
                act = "none"
            extra = "true" if action and "EXTRA" in action else "false"
            alts.append(f"{{ items := [{', '.join(items)}], action := {act}, "
                        f"nvars := {len(names)}, guardInvalid := {str(guarded).lower()}, "
                        f"extra := {extra} }}")
        kind = ".loop1" if name.startswith("_loop1") else ".loop0" if is_loop else \
            ".gather" if is_gather else ".normal"
        memo = rule.memo and not rule.left_recursive
        leader = bool(rule.left_recursive and rule.leader)
        rule_extra = any(a.action and "EXTRA" in a.action for a in rhs.alts)
        wi = name.endswith("without_invalid")
        body = (f"def r{i} : Rule := {{ name := {lean_str(name)}, kind := {kind}, "
                f"memo := {str(memo).lower()}, leftRec := {str(bool(rule.left_recursive)).lower()}, "
                f"leader := {str(leader).lower()}, extra := {str(rule_extra).lower()}, "
                f"withoutInvalid := {str(wi).lower()}, alts := [\n  "
                + ",\n  ".join(alts) + "] }")
        defs.append(body)

    n = len(rule_ids)

    def tree(lo, hi):
        if hi - lo == 1:
            return f"r{lo}"
        mid = (lo + hi) // 2
        return f"if id < {mid} then {tree(lo, mid)} else {tree(mid, hi)}"

    start = {k: rule_ids[k] for k in ("file", "interactive", "eval", "func_type")}
    kw = sorted(gen.keywords.items(), key=lambda kv: kv[1])
    out = ["import PyLean.PyGrammar.Peg.Syntax", "",
           "/-! GENERATED by `gen/gen_grammar.py` from `Grammar/python.gram` via pegen's",
           "`CParserGenerator`, whose output is checked byte for byte against `Parser/parser.c`.",
           "Do not edit. -/", "", "set_option maxRecDepth 8000", "",
           "namespace PyLean.PyGrammar.Peg", "", ""]
    out = out[:-1]
    for d in defs:
        out.append(d)
        out.append("")
    out.append("/-- The rule with number `id` (a balanced decision tree over `Nat.blt`). -/")
    out.append(f"def ruleOf (id : Nat) : Rule :=\n  {tree(0, n)}")
    out.append("")
    out.append(f"/-- Number of rules, artificial ones included (`Parser/parser.c`). -/")
    out.append(f"def ruleCount : Nat := {n}")
    out.append("")
    for k, v in start.items():
        out.append(f"def rule_{k} : Nat := {v}")
    out.append("")
    out.append("/-- `reserved_keywords` of `Parser/parser.c`: spelling and token type. -/")
    out.append("def keywords : List (List Nat × Nat) := [" +
               ", ".join(f"({bytes_list(k)}, {t})" for k, t in kw) + "]")
    out.append("")
    out.append("/-- `soft_keywords` of `Parser/parser.c`. -/")
    out.append("def softKeywords : List (List Nat) := [" +
               ", ".join(bytes_list(k) for k in sorted(s.strip('"') for s in gen.soft_keywords)) + "]")
    out.append("")
    out.append("end PyLean.PyGrammar.Peg")
    data = "\n".join(out) + "\n"

    helper_text = "\n".join([
        "/-! GENERATED by `gen/gen_grammar.py`: every helper function the grammar's",
        "actions call. Do not edit. -/", "", "namespace PyLean.PyGrammar.Peg", "",
        "/-- A C helper named in an action of `Grammar/python.gram`. -/",
        "inductive Helper where",
        *[f"  | {h}" for h in sorted(helpers)],
        "  deriving DecidableEq, Repr", "", "end PyLean.PyGrammar.Peg", ""])

    if "--check" in sys.argv:
        if OUT.read_text() != data or HELPERS_OUT.read_text() != helper_text:
            sys.exit("Peg/GrammarData.lean or Peg/Helpers.lean is stale")
        print("GrammarData.lean matches python.gram")
    else:
        OUT.write_text(data)
        HELPERS_OUT.write_text(helper_text)
        print(len(defs), "rules", len(helpers), "helpers")
        print(sorted(helpers))


if __name__ == "__main__":
    main()
