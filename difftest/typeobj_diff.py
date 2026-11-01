"""Differential test: the Lean object model (lean/PyLean/TypeObj) vs. the running CPython.

Usage: python3 difftest/typeobj_diff.py [--cases N] [--seed S]

A case is a scenario: a random class hierarchy with special methods, descriptors,
metaclasses and __slots__, then probes (attribute access, operators, comparisons, truth,
hashing, containment, iteration, calls, isinstance, class creation failures...). The
scenario is a JSON tree. run_python renders it as Python source and execs it; the Lean
side interprets the same tree against the model. Both produce the trace of `_log` events
and probe outcomes, compared line by line, so dispatch order is checked call by call.

Each statement's tree format is parsed in lean/PyLean/TypeObj/Diff.lean.
"""

import re
import sys
import types
import warnings

import common

BIN = ["+", "-", "*", "@", "%", "//", "/", "<<", ">>", "&", "|", "^", "**"]
CMP = ["<", "<=", "==", "!=", ">", ">="]
BIN_DUNDER = {"+": "add", "-": "sub", "*": "mul", "@": "matmul", "%": "mod", "//": "floordiv",
              "/": "truediv", "<<": "lshift", ">>": "rshift", "&": "and", "|": "or", "^": "xor",
              "**": "pow"}
CMP_DUNDER = {"<": "lt", "<=": "le", "==": "eq", "!=": "ne", ">": "gt", ">=": "ge"}


# Rendering trees as Python source.

def lit_src(v):
    if isinstance(v, list):
        if v[0] == "notimpl":
            return "NotImplemented"
        if v[0] == "ellipsis":
            return "Ellipsis"
        return v[1]
    return repr(v)


def expr_src(e):
    t = e[0]
    if t == "lit":
        return lit_src(e[1])
    if t == "name":
        return e[1]
    if t == "attr":
        return f"({expr_src(e[1])}).{e[2]}"
    if t == "call":
        parts = [expr_src(a) for a in e[2]] + [f"{k}={expr_src(v)}" for k, v in e[3]]
        return f"({expr_src(e[1])})({', '.join(parts)})"
    if t == "bin":
        return f"(({expr_src(e[2])}) {e[1]} ({expr_src(e[3])}))"
    if t == "un":
        return f"({e[1]} ({expr_src(e[2])}))"
    if t == "cmp":
        return f"(({expr_src(e[2])}) {e[1]} ({expr_src(e[3])}))"
    if t == "is":
        return f"(({expr_src(e[1])}) is ({expr_src(e[2])}))"
    if t == "in":
        return f"(({expr_src(e[1])}) in ({expr_src(e[2])}))"
    if t == "notin":
        return f"(({expr_src(e[1])}) not in ({expr_src(e[2])}))"
    if t == "tuple":
        return "(" + "".join(expr_src(x) + ", " for x in e[1]) + ")"
    if t == "list":
        return "[" + ", ".join(expr_src(x) for x in e[1]) + "]"
    if t == "dict":
        return "{" + ", ".join(f"{expr_src(k)}: {expr_src(v)}" for k, v in e[1]) + "}"
    if t == "sub":
        return f"({expr_src(e[1])})[{expr_src(e[2])}]"
    if t == "super":
        return "super()"
    raise ValueError(t)


def params_src(p):
    pos = list(p["pos"])
    nd = len(p["defaults"])
    parts = []
    for i, n in enumerate(pos):
        if i >= len(pos) - nd:
            parts.append(f"{n}={expr_src(p['defaults'][i - (len(pos) - nd)])}")
        else:
            parts.append(n)
        if p["posonly"] and i == p["posonly"] - 1:
            parts.append("/")
    if p["varargs"]:
        parts.append("*" + p["varargs"])
    elif p["kwonly"]:
        parts.append("*")
    kwd = dict(p["kwdefaults"])
    for n in p["kwonly"]:
        parts.append(f"{n}={expr_src(kwd[n])}" if n in kwd else n)
    if p["varkw"]:
        parts.append("**" + p["varkw"])
    return ", ".join(parts)


def block_src(stmts, codes, indent, out):
    if not stmts:
        out.append(" " * indent + "pass")
    for s in stmts:
        stmt_src(s, codes, indent, out)


def stmt_src(s, codes, indent, out):
    pad = " " * indent
    t = s[0]
    if t == "expr":
        out.append(f"{pad}{expr_src(s[1])}")
    elif t == "assign":
        out.append(f"{pad}{s[1]} = {expr_src(s[2])}")
    elif t == "setattr":
        out.append(f"{pad}({expr_src(s[1])}).{s[2]} = {expr_src(s[3])}")
    elif t == "delattr":
        out.append(f"{pad}del ({expr_src(s[1])}).{s[2]}")
    elif t == "setitem":
        out.append(f"{pad}({expr_src(s[1])})[{expr_src(s[2])}] = {expr_src(s[3])}")
    elif t == "delitem":
        out.append(f"{pad}del ({expr_src(s[1])})[{expr_src(s[2])}]")
    elif t == "aug":
        out.append(f"{pad}{s[1]} {s[2]}= {expr_src(s[3])}")
    elif t == "ret":
        out.append(f"{pad}return {expr_src(s[1])}")
    elif t == "raise":
        out.append(f"{pad}raise {expr_src(s[1])}")
    elif t == "raisefrom":
        out.append(f"{pad}raise {expr_src(s[1])} from {expr_src(s[2])}")
    elif t == "log":
        out.append(f"{pad}_log({s[1]!r})")
    elif t == "def":
        out.append(f"{pad}def {s[1]}({params_src(s[3])}):")
        block_src(codes[s[4]], codes, indent + 4, out)
    elif t == "class":
        parts = [expr_src(b) for b in s[2]] + [f"{k}={expr_src(v)}" for k, v in s[3]]
        out.append(f"{pad}class {s[1]}({', '.join(parts)}):")
        block_src(codes[s[5]], codes, indent + 4, out)
    elif t == "try":
        out.append(f"{pad}try:")
        block_src(s[1], codes, indent + 4, out)
        out.append(f"{pad}except {expr_src(s[2])} as {s[3]}:")
        block_src(s[4], codes, indent + 4, out)
    elif t == "if":
        out.append(f"{pad}if {expr_src(s[1])}:")
        block_src(s[2], codes, indent + 4, out)
        out.append(f"{pad}else:")
        block_src(s[3], codes, indent + 4, out)
    elif t == "probe":
        out.append(f"{pad}_probe({s[1]!r}, lambda: {expr_src(s[2])})")
    elif t == "probes":
        out.append(f"{pad}try:")
        block_src(s[2], codes, indent + 4, out)
        out.append(f"{pad}    _note({s[1]!r}, 'ok')")
        out.append(f"{pad}except BaseException as _e:")
        out.append(f"{pad}    _note({s[1]!r}, _text(_e))")
    else:
        raise ValueError(t)


def canon(v, depth=12):
    if depth == 0:
        return "<deep>"
    d = depth - 1
    if v is None:
        return "None"
    if v is NotImplemented:
        return "NotImplemented"
    if v is Ellipsis:
        return "Ellipsis"
    if v is True:
        return "True"
    if v is False:
        return "False"
    tv = type(v)
    if tv is int:
        return str(v)
    if tv is str:
        return repr(v)
    if tv is float:
        return "<float>"
    if tv is tuple:
        return "(" + ", ".join(canon(x, d) for x in v) + ")"
    # Everything below reads C fields directly: the probes must not run user __getattribute__.
    if issubclass(tv, type):
        return f"<class {type.__dict__['__name__'].__get__(v)}>"
    tn = type.__dict__["__name__"].__get__(tv)
    if issubclass(tv, list):
        body = "[" + ", ".join(canon(x, d) for x in list.__iter__(v)) + "]"
        return body if tv is list else f"<{tn} {body}>"
    if issubclass(tv, dict):
        body = "{" + ", ".join(canon(k, d) + ": " + canon(x, d) for k, x in dict.items(v)) + "}"
        return body if tv is dict else f"<{tn} {body}>"
    if issubclass(tv, int):
        return f"<{tn} {int.__repr__(v)}>"
    if issubclass(tv, str):
        return f"<{tn} {str.__repr__(v)}>"
    if issubclass(tv, tuple):
        return f"<{tn} (" + ", ".join(canon(x, d) for x in tuple.__iter__(v)) + ")>"
    if tv is types.FunctionType:
        return f"<function {v.__qualname__}>"
    if tv is types.MethodType:
        return f"<method {canon(v.__func__, d)} of {canon(v.__self__, d)}>"
    if tv is types.BuiltinFunctionType:
        return "<builtin>"
    if issubclass(tv, BaseException):
        args = BaseException.__dict__["args"].__get__(v)
        return f"<{tn} (" + ", ".join(canon(x, d) for x in args) + ")>"
    return f"<{tn}>"


ADDR = re.compile(r"0x[0-9a-f]+")


warnings.simplefilter("ignore")


def run_python(case):
    src_lines = []
    block_src(case["main"], case["codes"], 0, src_lines)
    trace = []

    def text(e):
        try:
            s = str(e)
        except BaseException:
            s = "<str failed>"
        return f"!{type(e).__name__}: {ADDR.sub('0x0', s)}"

    def probe(tag, f):
        try:
            out = canon(f())
        except BaseException as e:
            out = text(e)
        trace.append(f"{tag}={ADDR.sub('0x0', out)}")

    def note(tag, out):
        trace.append(f"{tag}={out}")

    def hash_probe(x):
        h = hash(x)
        mro = type.__dict__["__mro__"].__get__(type(x))
        tdict = type.__dict__["__dict__"]
        user = next((isinstance(tdict.__get__(c)["__hash__"], types.FunctionType)
                     for c in mro if "__hash__" in tdict.__get__(c)), False)
        return h if user or issubclass(type(x), int) else "<h>"

    env = {"__name__": "__main__", "_log": trace.append, "_probe": probe, "_note": note,
           "_text": text, "_hash": hash_probe}
    try:
        exec(compile("\n".join(src_lines) + "\n", "<scenario>", "exec"), env)
    except BaseException as e:
        trace.append(f"UNCAUGHT {type(e).__name__}: {e}")
    return {"ok": trace}


# Scenario generation.

def lit(v):
    return ["lit", v]


NONE = lit(None)
NOTIMPL = lit(["notimpl"])


def name(n):
    return ["name", n]


def call(f, *args, kw=()):
    return ["call", f, list(args), [list(p) for p in kw]]


def attr(o, n):
    return ["attr", o, n]


class G:
    """Builds one scenario."""

    def __init__(self, rng):
        self.rng = rng
        self.codes = []
        self.main = []
        self.tag = 0
        self.classes = []  # (name, may_instantiate)

    def code(self, body):
        self.codes.append(body)
        return len(self.codes) - 1

    def next_tag(self):
        self.tag += 1
        return f"p{self.tag}"

    def probe(self, e):
        self.main.append(["probe", self.next_tag(), e])

    def probes(self, *stmts):
        self.main.append(["probes", self.next_tag(), list(stmts)])

    def value(self):
        r = self.rng
        return r.choice([NONE, NONE, NOTIMPL, NOTIMPL, lit(True), lit(False), lit(0), lit(1),
                         lit(2), lit(-1), lit(7), lit("s"), lit(""),
                         ["tuple", [lit(1), lit("a")]], ["tuple", []]])

    def exc(self):
        return self.rng.choice(["AttributeError", "TypeError", "ValueError", "IndexError",
                                "KeyError", "StopIteration", "RuntimeError", "LookupError"])

    def body(self, tagname, self_name="self", first_args=()):
        """A method body: log, then return or raise."""
        r = self.rng
        out = [["log", tagname]]
        k = r.random()
        if k < 0.62:
            out.append(["ret", self.value()])
        elif k < 0.72:
            out.append(["ret", name(self_name)])
        elif k < 0.80 and first_args:
            out.append(["ret", name(first_args[0])])
        elif k < 0.90:
            out.append(["raise", call(name(self.exc()), lit("boom"))])
        else:
            out.append(["raise", name(self.exc())])
        return out

    def method(self, n, qual, params, body, staticm=False):
        return ["def", n, qual, {"pos": params, "posonly": 0, "kwonly": [], "varargs": None,
                                 "varkw": None, "defaults": [], "kwdefaults": []},
                self.code(body)]

    def descr_classes(self):
        """Helper descriptor classes used as class attributes."""
        r = self.rng
        # Data descriptor D, non-data descriptor N.
        d = [self.method("__get__", "D.__get__", ["self", "obj", "objtype"],
                         [["log", "D.__get__"], ["ret", self.value()]]),
             self.method("__set__", "D.__set__", ["self", "obj", "value"],
                         self.body("D.__set__")),
             self.method("__delete__", "D.__delete__", ["self", "obj"],
                         self.body("D.__delete__"))]
        if r.random() < 0.3:
            d.pop(r.randrange(3))
        if r.random() < 0.3:
            d.append(self.method("__set_name__", "D.__set_name__", ["self", "owner", "n"],
                                 [["log", "D.__set_name__"]] +
                                 ([["raise", call(name("ValueError"), lit("sn"))]]
                                  if r.random() < 0.1 else [])))
        self.main.append(["class", "D", [], [], False, self.code(d or [["assign", "zz", lit(1)]])])
        n = [self.method("__get__", "N.__get__", ["self", "obj", "objtype"],
                         self.body("N.__get__", first_args=("obj",)))]
        self.main.append(["class", "N", [], [], False, self.code(n)])

    def attr_stmts(self, cname):
        """Class body statements for ordinary and descriptor attributes."""
        r = self.rng
        out = []
        for a in ["x", "y"]:
            if r.random() < 0.55:
                kind = r.randrange(8)
                q = f"{cname}.{a}"
                if kind == 0:
                    out.append(["assign", a, self.value()])
                elif kind == 1:
                    out.append(self.method(a, q, ["self"], self.body(q)))
                elif kind == 2:
                    out.append(["assign", a, call(name("D"))])
                elif kind == 3:
                    out.append(["assign", a, call(name("N"))])
                elif kind == 4:
                    out.append(self.method(a, q, ["self"], self.body(q)))
                    out.append(["assign", a, call(name("property"), name(a))])
                elif kind == 5:
                    out.append(self.method(a, q, ["cls"], self.body(q, "cls")))
                    out.append(["assign", a, call(name("classmethod"), name(a))])
                elif kind == 6:
                    out.append(self.method(a, q, [], [["log", q], ["ret", self.value()]]))
                    out.append(["assign", a, call(name("staticmethod"), name(a))])
                else:
                    out.append(["assign", a, NONE])
        return out

    def dunder_stmts(self, cname, can_super):
        r = self.rng
        out = []
        q = lambda n: f"{cname}.{n}"
        def m(n, params, body=None):
            out.append(self.method(n, q(n), params, body or self.body(q(n))))

        for op in r.sample(BIN, r.choice([0, 0, 1, 1, 2, 3])):
            d = BIN_DUNDER[op]
            for pre in r.sample(["", "r", "i"], r.choice([1, 1, 2, 3])):
                n = f"__{pre}{d}__"
                m(n, ["self", "other"])
        for op in r.sample(CMP, r.choice([0, 0, 1, 2])):
            n = f"__{CMP_DUNDER[op]}__"
            m(n, ["self", "other"])
        if r.random() < 0.25:
            out.append(["assign", "__hash__", NONE] if r.random() < 0.4 else
                       self.method("__hash__", q("__hash__"), ["self"],
                                   [["log", q("__hash__")],
                                    ["ret", r.choice([lit(7), lit(-1), lit("s"), lit(0),
                                                      lit(["bigint", str(2**64)]),
                                                      lit(["bigint", str(-2**70)]), NONE])]]))
        if r.random() < 0.3:
            if r.random() < 0.2:
                out.append(["assign", "__bool__", NONE])
            else:
                m("__bool__", ["self"], [["log", q("__bool__")],
                                         ["ret", r.choice([lit(True), lit(False), lit(1), NONE])]])
        if r.random() < 0.3:
            m("__len__", ["self"], [["log", q("__len__")],
                                    ["ret", r.choice([lit(0), lit(3), lit(-1), lit("s"), NONE,
                                                      lit(True),
                                                      lit(["bigint", str(2**63)]),
                                                      lit(["bigint", str(2**63 - 1)])])]])
        if r.random() < 0.2:
            if r.random() < 0.3:
                out.append(["assign", "__contains__", NONE])
            else:
                m("__contains__", ["self", "item"], [["log", q("__contains__")],
                                                     ["ret", self.value()]])
        if r.random() < 0.25:
            if r.random() < 0.2:
                out.append(["assign", "__iter__", NONE])
            else:
                m("__iter__", ["self"], [["log", q("__iter__")],
                                         ["ret", r.choice([name("self"),
                                                           call(name("iter"), ["list", [lit(1), lit(2)]]),
                                                           lit(3)])]])
        if r.random() < 0.2:
            m("__next__", ["self"], [["log", q("__next__")],
                                     ["raise", r.choice([name("StopIteration"),
                                                         call(name("ValueError"), lit("n"))])]])
        if r.random() < 0.3:
            body = [["log", q("__getitem__")],
                    ["if", ["cmp", ">", name("key"), lit(2)],
                     [["raise", name(r.choice(["IndexError", "StopIteration", "KeyError"]))]],
                     [["ret", ["tuple", [lit("item"), name("key")]]]]]]
            m("__getitem__", ["self", "key"], body)
        if r.random() < 0.15:
            m("__setitem__", ["self", "key", "value"])
        if r.random() < 0.15:
            m("__delitem__", ["self", "key"])
        if r.random() < 0.2:
            m("__index__", ["self"], [["log", q("__index__")],
                                      ["ret", r.choice([lit(2), lit(True), lit("s"), NONE,
                                                        lit(["bigint", str(2**63)]),
                                                        lit(["bigint", str(-2**63 - 1)])])]])
        if r.random() < 0.15:
            m("__int__", ["self"], [["log", q("__int__")],
                                    ["ret", r.choice([lit(2), lit(True), lit("s")])]])
        if r.random() < 0.25:
            m("__call__", ["self"], self.body(q("__call__")))
        if r.random() < 0.2:
            m("__repr__", ["self"], [["log", q("__repr__")],
                                     ["ret", r.choice([lit("R"), lit(1), NONE])]])
        if r.random() < 0.2:
            m("__str__", ["self"], [["log", q("__str__")],
                                    ["ret", r.choice([lit("S"), lit(1)])]])
        if r.random() < 0.1:
            m("__format__", ["self", "spec"], [["log", q("__format__")],
                                               ["ret", r.choice([lit("F"), lit(1)])]])
        if r.random() < 0.25:
            m("__getattr__", ["self", "name"], self.body(q("__getattr__")))
        if r.random() < 0.1:
            body = [["log", q("__getattribute__")]]
            k = r.random()
            if k < 0.4:
                body.append(["raise", call(name("AttributeError"), lit("ga"))])
            elif k < 0.7 and can_super:
                body.append(["ret", ["call", ["attr", ["super"], "__getattribute__"], [name("name")], []]])
            else:
                body.append(["ret", call(attr(name("object"), "__getattribute__"), name("self"),
                                         name("name"))])
            m("__getattribute__", ["self", "name"], body)
        if r.random() < 0.15:
            body = [["log", q("__setattr__")]]
            if r.random() < 0.6:
                body.append(["expr", call(attr(name("object"), "__setattr__"), name("self"),
                                          name("name"), name("value"))])
            m("__setattr__", ["self", "name", "value"], body)
        if r.random() < 0.1:
            body = [["log", q("__delattr__")]]
            if r.random() < 0.6:
                body.append(["expr", call(attr(name("object"), "__delattr__"), name("self"),
                                          name("name"))])
            m("__delattr__", ["self", "name"], body)
        if r.random() < 0.25:
            k = r.random()
            params = ["self"] if k < 0.7 else ["self", "a"]
            body = [["log", q("__init__")]]
            if r.random() < 0.15:
                body.append(["ret", lit(1)])
            m("__init__", params, body)
        if r.random() < 0.15:
            cls = name("cls")
            k = r.random()
            ret = (["ret", call(attr(name("object"), "__new__"), cls)] if k < 0.5 else
                   ["ret", ["call", ["attr", ["super"], "__new__"], [cls], []]] if k < 0.75 and can_super else
                   ["ret", lit(5)])
            m("__new__", ["cls"], [["log", q("__new__")], ret])
        if r.random() < 0.12:
            out.append(["def", "__init_subclass__", q("__init_subclass__"),
                        {"pos": ["cls"], "posonly": 0, "kwonly": [], "varargs": None,
                         "varkw": "kw", "defaults": [], "kwdefaults": []},
                        self.code([["log", q("__init_subclass__")]])])
        if r.random() < 0.1:
            m("__class_getitem__", ["cls", "item"], [["log", q("__class_getitem__")],
                                                     ["ret", name("item")]])
        if r.random() < 0.1:
            out.append(["assign", "__slots__", r.choice([
                ["tuple", []], lit("a"), ["tuple", [lit("a"), lit("b")]],
                ["tuple", [lit("__dict__")]], ["tuple", [lit("__weakref__")]],
                ["list", [lit("a")]], ["tuple", [lit("1a")]], ["tuple", [lit(1)]],
                ["tuple", [lit("x")]], ["tuple", [lit("__p")]], lit(5)])])
        return out

    def make_classes(self):
        r = self.rng
        n = r.choice([2, 3, 3, 4, 5])
        names = ["A", "B", "C", "E", "F"][:n]
        metas = []
        if r.random() < 0.3:
            body = []
            if r.random() < 0.5:
                body.append(self.method("__new__", "M.__new__", ["mcls", "name", "bases", "ns"],
                                        [["log", "M.__new__"],
                                         ["ret", call(attr(name("type"), "__new__"), name("mcls"),
                                                      name("name"), name("bases"), name("ns"))]]))
            if r.random() < 0.3:
                body.append(self.method("x", "M.x", ["cls"], self.body("M.x", "cls")))
            if r.random() < 0.3:
                body.append(["assign", "y", self.value()])
            if r.random() < 0.3:
                body.append(self.method("__call__", "M.__call__", ["cls"],
                                        [["log", "M.__call__"],
                                         ["ret", ["call", ["attr", ["super"], "__call__"], [], []]]]))
            if r.random() < 0.25:
                body.append(self.method("__add__", "M.__add__", ["cls", "o"],
                                        self.body("M.__add__", "cls")))
            self.main.append(["class", "M", [name("type")], [], True, self.code(body or [["assign", "zz", lit(1)]])])
            metas.append("M")
            if r.random() < 0.3:
                self.main.append(["class", "M2", [name("type")], [], False,
                                  self.code([["assign", "zz", lit(2)]])])
                metas.append("M2")
        for i, c in enumerate(names):
            earlier = names[:i]
            k = r.random()
            bases = []
            if earlier and k < 0.75:
                bases = r.sample(earlier, r.choice([1, 1, 2, 2, min(3, len(earlier))]) if len(earlier) >= 3
                                 else r.choice([1, min(2, len(earlier))]))
            if r.random() < 0.28:
                b = r.choice(["int", "str", "list", "tuple", "dict", "Exception", "object", "bool",
                              "property", "type", "ValueError", "KeyError"])
                bases.insert(r.randrange(len(bases) + 1), b)
            kw = []
            if metas and r.random() < 0.5:
                kw.append(["metaclass", name(r.choice(metas))])
            if r.random() < 0.06:
                kw.append(["flag", lit(1)])
            body = self.attr_stmts(c) + self.dunder_stmts(c, True)
            cell = True
            self.main.append(["probes", self.next_tag(),
                              [["class", c, [name(b) for b in bases], kw, cell,
                                self.code(body or [["assign", "zz", lit(1)]])]]])
        self.classes = names

    def instances(self):
        """Create instances; a failed class leaves the name unbound and probes say so."""
        r = self.rng
        self.objs = []
        for c in self.classes:
            v = "o" + c
            self.main.append(["probes", self.next_tag(),
                              [["assign", v, call(name(c))]]])
            self.objs.append(v)

    def operand(self):
        r = self.rng
        k = r.random()
        if k < 0.65 and self.objs:
            return name(r.choice(self.objs))
        if k < 0.85:
            return r.choice([lit(1), lit(0), lit("s"), lit(True), NONE, ["tuple", [lit(1)]],
                             ["list", [lit(1)]], lit(2)])
        return name(r.choice(self.classes))

    def probes_random(self, count):
        r = self.rng
        for _ in range(count):
            k = r.randrange(22)
            a, b = self.operand(), self.operand()
            an = r.choice(["x", "y", "zzz", "__class__", "__dict__", "a"])
            if k == 0:
                self.probe(attr(a, an))
            elif k == 1:
                self.probe(["bin", r.choice(BIN), a, b])
            elif k == 2:
                self.probe(["cmp", r.choice(CMP), a, b])
            elif k == 3:
                self.probe(call(name("len"), a))
            elif k == 4:
                self.probe(["un", "not", a])
            elif k == 5:
                self.probe(call(name("_hash"), a))
            elif k == 6:
                self.probe(["in", b, a])
            elif k == 7:
                self.probe(call(name("list"), a))
            elif k == 8:
                self.probe(call(a))
            elif k == 9:
                self.probe(call(name("isinstance"), a, b))
            elif k == 10:
                self.probe(call(name("issubclass"), a, b))
            elif k == 11:
                self.probes(["setattr", a, r.choice(["x", "y", "a", "q"]), lit(1)])
            elif k == 12:
                self.probes(["delattr", a, r.choice(["x", "y", "a", "q"])])
            elif k == 13:
                self.probe(["sub", a, b])
            elif k == 14:
                self.probes(["setitem", a, b, lit(1)])
            elif k == 15:
                self.probes(["delitem", a, b])
            elif k == 16:
                self.probe(call(attr(a, r.choice(["x", "y"]))))
            elif k == 17:
                self.probe(call(name("repr"), a))
            elif k == 18:
                self.probe(call(name("str"), a))
            elif k == 19:
                v = self.rng.choice(self.objs) if self.objs else "oA"
                self.probes(["aug", v, r.choice(BIN), b])
            elif k == 20:
                self.probe(call(name("int"), a))
            else:
                self.probe(call(name("format"), a))


def gen_case(rng):
    g = G(rng)
    g.descr_classes()
    g.make_classes()
    g.instances()
    g.probes_random(rng.randrange(6, 16))
    return {"mod": "typeobj", "fn": "scenario", "codes": g.codes, "main": g.main}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=2000)
