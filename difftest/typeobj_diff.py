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
                # Not / or **: floats are opaque in the model, and the name is used again.
                self.probes(["aug", v, r.choice([o for o in BIN if o not in ("/", "**")]), b])
            elif k == 20:
                self.probe(call(name("int"), a))
            else:
                self.probe(call(name("format"), a))


# Targeted scenario families: each exercises one protocol with edge cases.

def cls(g, name_, bases=(), body=None, kw=(), cell=True):
    g.main.append(["probes", g.next_tag(),
                   [["class", name_, [b if isinstance(b, list) else name(b) for b in bases],
                     [list(p) for p in kw], cell, g.code(body or [["assign", "zz", lit(1)]])]]])


def simple_method(g, n, q, params, ret, extra=()):
    return g.method(n, q, params, [["log", q]] + list(extra) + [["ret", ret]])


def fam_calls(g):
    """Argument binding: signatures, defaults, keywords, __defaults__ assignment."""
    r = g.rng
    pos = ["a", "b", "c", "d"][:r.randrange(5)]
    posonly = r.randrange(len(pos) + 1) if r.random() < 0.4 else 0
    nd = r.randrange(len(pos) + 1) if r.random() < 0.7 else 0
    kwonly = ["e", "f", "g"][:r.choice([0, 0, 1, 2, 3])]
    kwd = [[k, lit(k + "d")] for k in kwonly if r.random() < 0.5]
    va = "args" if r.random() < 0.35 else None
    vk = "kw" if r.random() < 0.35 else None
    params = {"pos": pos, "posonly": posonly, "kwonly": kwonly, "varargs": va, "varkw": vk,
              "defaults": [lit(i + 100) for i in range(nd)], "kwdefaults": kwd}
    names = pos + kwonly + [x for x in (va, vk) if x]
    body = [["ret", ["tuple", [name(n) for n in names]]]]
    g.main.append(["def", "f", "f", params, g.code(body)])
    for _ in range(r.randrange(2, 7)):
        if r.random() < 0.15:
            k = r.randrange(5)
            v = (["tuple", [lit(i) for i in range(r.randrange(6))]] if k < 2 else
                 NONE if k == 2 else lit(1) if k == 3 else ["list", []])
            g.probes(["setattr", name("f"), "__defaults__", v])
        if r.random() < 0.1:
            k = r.randrange(3)
            v = (["dict", [[lit(n), lit(9)] for n in kwonly]] if k == 0 else NONE if k == 1 else lit(1))
            g.probes(["setattr", name("f"), "__kwdefaults__", v])
        n_pos = r.randrange(7)
        args = [lit(i) for i in range(n_pos)]
        pool = pos + kwonly + ["zzzzzzzzz", "yyyyyyyyyy"]
        kws = r.sample(pool, r.randrange(min(4, len(pool)) + 1))
        g.probe(["call", name("f"), args, [[k, lit(k)] for k in kws]])
    g.probe(attr(name("f"), "__defaults__"))
    g.probe(attr(name("f"), "__name__"))
    g.probes(["setattr", name("f"), "__name__", r.choice([lit("h"), lit(1)])])
    g.probe(attr(name("f"), "__qualname__"))
    g.probes(["setattr", name("f"), "attr1", lit(1)])
    g.probe(attr(name("f"), "attr1"))


def fam_property(g):
    r = g.rng
    getter = g.method("g", "g", ["self"], [["log", "g"], ["ret", lit(1)]])
    g.main.append(getter)
    g.main.append(g.method("s", "s", ["self", "v"], [["log", "s"]]))
    g.main.append(g.method("dl", "dl", ["self"], [["log", "dl"]]))
    if r.random() < 0.4:
        cls(g, "P", ["property"], [["assign", "__doc__", lit("pdoc")]] if r.random() < 0.3 else None)
        pn = "P"
    else:
        pn = "property"
    args = r.choice([[], [name("g")], [name("g"), name("s")], [name("g"), name("s"), name("dl")],
                     [NONE, NONE, NONE, lit("doc")], [name("g"), NONE, NONE, lit("doc")],
                     [name("g"), name("s"), name("dl"), lit("d"), lit(5)]])
    kw = r.choice([[], [], [["doc", lit("kd")]], [["fget", name("g")]], [["zz", lit(1)]]])
    body = [["assign", "x", ["call", name(pn), args, kw]],
            ["assign", "y", call(attr(name("x"), r.choice(["setter", "getter", "deleter"])),
                                 r.choice([name("s"), name("g"), NONE]))]]
    cls(g, "C", (), body)
    g.main.append(["probes", g.next_tag(), [["assign", "o", call(name("C"))]]])
    for a in ["x", "y"]:
        g.probe(attr(name("o"), a))
        g.probes(["setattr", name("o"), a, lit(2)])
        g.probes(["delattr", name("o"), a])
        p = attr(name("C"), a)
        g.probe(attr(p, "__doc__"))
        g.probe(attr(p, "fget"))
        g.probe(attr(p, "fset"))
        g.probe(attr(p, "fdel"))
        g.probe(attr(p, "__name__"))
        g.probe(attr(p, "__isabstractmethod__"))
        if r.random() < 0.3:
            g.probes(["setattr", p, "__doc__", lit("nd")])
        g.probe(call(attr(p, "__get__"), name("o")))
        g.probe(call(attr(p, "__get__"), NONE, name("C")))
        g.probe(call(attr(p, "__set__"), name("o"), lit(1)))
        g.probe(call(attr(p, "__delete__"), name("o")))
        if r.random() < 0.3:
            g.probe(call(attr(p, "__set_name__"), name("C"), lit("nn")))
            g.probe(attr(p, "__name__"))


def fam_super(g):
    r = g.rng
    cls(g, "A", (), [simple_method(g, "m", "A.m", ["self"], lit("A")),
                     g.method("cm", "A.cm", ["cls"], [["log", "A.cm"], ["ret", name("cls")]]),
                     ["assign", "cm", call(name("classmethod"), name("cm"))],
                     g.method("sm", "A.sm", [], [["log", "A.sm"], ["ret", lit("sm")]]),
                     ["assign", "sm", call(name("staticmethod"), name("sm"))],
                     ["assign", "v", lit(5)]])
    cls(g, "B", ["A"], [g.method("m", "B.m", ["self"],
                                 [["log", "B.m"], ["ret", ["call", attr(["super"], "m"), [], []]]])])
    cls(g, "C", ["A"], [g.method("m", "C.m", ["self"],
                                 [["log", "C.m"], ["ret", ["call", attr(["super"], "m"), [], []]]])])
    cls(g, "D", ["B", "C"], [g.method("m", "D.m", ["self"],
                                      [["log", "D.m"], ["ret", ["call", attr(["super"], "m"), [], []]]])])
    g.main.append(["assign", "d", call(name("D"))])
    g.probe(call(attr(name("d"), "m")))
    t = lambda: name(r.choice(["A", "B", "C", "D", "object"]))
    for _ in range(r.randrange(3, 9)):
        s = call(name("super"), t(), r.choice([name("d"), t(), lit(1), NONE]))
        g.probe(attr(s, r.choice(["m", "cm", "sm", "v", "zz", "__class__", "__thisclass__",
                                  "__self__", "__self_class__"])))
    g.probe(call(attr(call(name("super"), name("B"), name("d")), "m")))
    g.probe(call(name("super"), lit(1)))
    g.probe(call(name("super"), name("B"), lit(1), lit(2)))
    u = call(name("super"), name("B"))
    g.probe(call(attr(u, "__get__"), name("d")))
    g.probe(attr(call(attr(u, "__get__"), name("d")), "v"))
    g.probe(call(attr(u, "__get__"), NONE))
    g.probe(attr(u, r.choice(["m", "__thisclass__", "__self__", "zz"])))
    g.probes(["setattr", call(name("super"), name("B"), name("d")), "v", lit(1)])


def fam_mro(g):
    """C3 failures, duplicate bases, custom mro(), __bases__ assignment."""
    r = g.rng
    names = ["A", "B", "C", "E", "F", "H", "I"]
    made = []
    for i, n in enumerate(names):
        k = r.randrange(len(made) + 1)
        bases = r.sample(made, min(k, 3)) if made else []
        if r.random() < 0.08 and bases:
            bases.append(bases[0])
        cls(g, n, bases)
        g.probe(attr(name(n), "__mro__"))
        made.append(n)
    for _ in range(r.randrange(1, 4)):
        c, d = r.choice(names), r.choice(names)
        g.probes(["setattr", name(c), "__bases__",
                  r.choice([["tuple", [name(d)]], ["tuple", [name("object")]], ["tuple", []],
                            lit(1), ["tuple", [lit(1)]],
                            ["tuple", [name(d), name(r.choice(names))]]])])
        g.probe(attr(name(c), "__mro__"))
        g.probe(attr(name(c), "__bases__"))
        g.probe(attr(name(c), "__base__"))
        g.probe(call(attr(name(d), "__subclasses__")))
    g.probe(call(attr(name("type"), "mro"), name("A")))
    g.probe(call(attr(name("C"), "mro")))
    # A custom mro().
    k = r.randrange(5)
    body = {0: ["ret", ["list", [name("cls"), name("object")]]],
            1: ["ret", ["tuple", []]],
            2: ["ret", lit(1)],
            3: ["ret", ["list", [lit(1)]]],
            4: ["ret", ["call", ["attr", ["super"], "mro"], [], []]]}[k]
    cls(g, "M", ["type"], [g.method("mro", "M.mro", ["cls"], [["log", "M.mro"], body])])
    cls(g, "X", ["A"], None, kw=[["metaclass", name("M")]])
    g.probe(attr(name("X"), "__mro__"))
    g.probe(call(name("X")))


def fam_class_stmt(g):
    """Class creation: metaclass, __prepare__, __init_subclass__, __set_name__, type()."""
    r = g.rng
    body = []
    if r.random() < 0.5:
        body.append(g.method("__prepare__", "M.__prepare__", ["mcls", "name", "bases"],
                             [["log", "M.__prepare__"],
                              ["ret", r.choice([["dict", []], lit(1), NONE])]]))
        body.append(["assign", "__prepare__", call(name("classmethod"), name("__prepare__"))])
    if r.random() < 0.5:
        body.append(g.method("__init__", "M.__init__", ["cls", "name", "bases", "ns"],
                             [["log", "M.__init__"]]))
    if r.random() < 0.5:
        body.append(g.method("__new__", "M.__new__", ["mcls", "name", "bases", "ns"],
                             [["log", "M.__new__"],
                              r.choice([["ret", call(attr(name("type"), "__new__"), name("mcls"),
                                                     name("name"), name("bases"), name("ns"))],
                                        ["ret", lit(1)],
                                        ["ret", ["call", attr(["super"], "__new__"),
                                                 [name("mcls"), name("name"), name("bases"), name("ns")], []]]])]))
    cls(g, "M", ["type"], body)
    cls(g, "M2", ["type"], None)
    cls(g, "M3", ["M"], None)
    cls(g, "A", (), [["def", "__init_subclass__", "A.__init_subclass__",
                      {"pos": ["cls"], "posonly": 0, "kwonly": [], "varargs": None,
                       "varkw": "kw", "defaults": [], "kwdefaults": []},
                      g.code([["log", "A.__init_subclass__"]] +
                             ([["expr", ["call", attr(["super"], "__init_subclass__"), [], []]]]
                              if r.random() < 0.5 else []))]])
    cls(g, "SN", (), [g.method("__set_name__", "SN.__set_name__", ["self", "owner", "n"],
                               [["log", "SN.__set_name__"]] +
                               ([["raise", call(name("ValueError"), lit("bad"))]]
                                if r.random() < 0.2 else []))])
    for i in range(r.randrange(2, 6)):
        n = f"K{i}"
        bases = r.sample(["A", "object", "int", "str", "list", "dict", "tuple", "Exception",
                          "bool", "type", "M"], r.choice([0, 1, 1, 2]))
        kw = []
        k = r.random()
        if k < 0.4:
            kw.append(["metaclass", name(r.choice(["M", "M2", "M3", "type"]))])
        elif k < 0.55:
            kw.append(["metaclass", r.choice([lit(1), name("len")])])
        if r.random() < 0.2:
            kw.append(["flag", lit(1)])
        bodyk = []
        if r.random() < 0.4:
            bodyk.append(["assign", "d", call(name("SN"))])
        if r.random() < 0.3:
            bodyk.append(["assign", "__qualname__", r.choice([lit("Q"), lit(1)])])
        if r.random() < 0.2:
            bodyk.append(["assign", "__module__", lit("mm")])
        if r.random() < 0.25:
            bodyk.append(["assign", "__slots__", r.choice([
                ["tuple", []], lit("a"), ["tuple", [lit("a"), lit("a")]], lit("__dict__"),
                ["tuple", [lit("__dict__"), lit("__dict__")]],
                ["tuple", [lit("__weakref__"), lit("__weakref__")]],
                ["tuple", [lit("__p"), lit("__q__")]], ["list", [lit("b"), lit("a")]],
                ["tuple", [lit("d")]], lit(1), ["tuple", [lit("1")]], lit("a b"),
                ["tuple", [lit("__qualname__")]], ["tuple", [lit("__classcell__")]]])])
        cls(g, n, bases, bodyk, kw=kw)
        g.probe(attr(name(n), "__mro__"))
        g.probe(call(name("type"), name(n)))
        g.probe(attr(name(n), "__qualname__"))
        g.probe(attr(name(n), "__module__"))
        g.probe(attr(name(n), "__name__"))
        g.probe(attr(name(n), "__base__"))
        g.probe(attr(name(n), "__basicsize__"))
        g.probe(attr(name(n), "__itemsize__"))
        g.probe(attr(name(n), "__dictoffset__"))
        g.probe(attr(name(n), "__weakrefoffset__"))
        g.probes(["assign", "o" + n, call(name(n))])
        g.probe(attr(name("o" + n), "__dict__"))
        g.probes(["setattr", name("o" + n), "a", lit(1)])
        g.probe(attr(name("o" + n), "a"))
        g.probe(attr(name("o" + n), "_K%d__p" % i))
        g.probes(["setattr", name("o" + n), "_K%d__p" % i, lit(1)])
        g.probes(["setattr", name("o" + n), "__dict__", ["dict", [[lit("a"), lit(2)]]]])
        g.probes(["delattr", name("o" + n), "a"])
        g.probe(attr(name("o" + n), "__weakref__"))
    for args in ([lit("T"), ["tuple", []], ["dict", []]], [lit(1), ["tuple", []], ["dict", []]],
                 [lit("T"), lit(1), ["dict", []]], [lit("T"), ["tuple", []], lit(1)],
                 [lit("a\x00b"), ["tuple", []], ["dict", []]],
                 [lit("T"), ["tuple", [lit(1)]], ["dict", []]],
                 [lit("T"), ["tuple", [name("bool")]], ["dict", []]],
                 [lit("T"), ["tuple", [name("int"), name("str")]], ["dict", []]],
                 [lit("T")], [lit("T"), lit(1)]):
        g.probe(["call", name("type"), args, []])
        g.probe(["call", name("M2"), args, []])


def fam_class_assign(g):
    """__class__ assignment and layouts."""
    r = g.rng
    spec = {"A": ((), None), "B": ((), None), "C": (("A",), None), "S1": ((), ("a",)),
            "S2": ((), ("a",)), "S3": ((), ("b",)), "S4": ((), ()), "I1": (("int",), None),
            "I2": (("int",), None), "L1": (("list",), None), "E1": (("Exception",), None),
            "W": ((), ("__weakref__",)), "Dd": ((), ("__dict__",)),
            "T1": (("tuple",), None)}
    for n, (bases, slots) in spec.items():
        body = []
        if slots is not None:
            body.append(["assign", "__slots__", ["tuple", [lit(s) for s in slots]]])
        cls(g, n, bases, body)
    ns = list(spec)
    for n in ns:
        g.probes(["assign", "o" + n, call(name(n))])
    for _ in range(r.randrange(4, 12)):
        o, c = r.choice(ns), r.choice(ns + ["int", "object", "list"])
        g.probes(["setattr", name("o" + o), "__class__", name(c)])
        g.probe(call(name("type"), name("o" + o)))
    g.probes(["setattr", name("oA"), "__class__", lit(1)])
    g.probes(["delattr", name("oA"), "__class__"])
    g.probes(["setattr", lit(1), "__class__", name("I1")])


def fam_wrappers(g):
    """Slot wrappers called directly, object.__setattr__ on types, tp_new_wrapper."""
    r = g.rng
    cls(g, "A", (), [simple_method(g, "__add__", "A.__add__", ["self", "o"], lit("add")),
                     simple_method(g, "__eq__", "A.__eq__", ["self", "o"], lit(True)),
                     ["assign", "__hash__", NONE]])
    cls(g, "B", ["int"], None)
    cls(g, "C", ["list"], None)
    cls(g, "M", ["type"], None)
    cls(g, "D", ("A", "B") if False else ("B",), None, kw=[["metaclass", name("M")]])
    g.main.append(["assign", "a", call(name("A"))])
    g.main.append(["assign", "b", call(name("B"), lit(3))])
    g.main.append(["assign", "c", call(name("C"))])
    objs = [name("a"), name("b"), name("c"), lit(1), lit("s"), NONE, name("A"), name("int"),
            name("object"), name("type"), ["list", [lit(1)]], ["tuple", [lit(1)]],
            ["dict", []], lit(True)]
    types_ = ["object", "int", "str", "list", "tuple", "dict", "type", "A", "B", "bool"]
    dunders = ["__add__", "__radd__", "__mul__", "__rmul__", "__eq__", "__ne__", "__lt__",
               "__repr__", "__str__", "__len__", "__getitem__", "__contains__", "__iter__",
               "__bool__", "__int__", "__index__", "__neg__", "__abs__", "__pow__", "__rpow__",
               "__getattribute__", "__setattr__", "__delattr__", "__init__", "__new__",
               "__call__", "__format__", "__init_subclass__",
               "__subclasshook__", "__setitem__", "__delitem__", "__mod__", "__rmod__",
               "__iadd__", "__imul__", "__or__", "__ror__", "__and__", "__floordiv__",
               "__divmod__", "__lshift__", "__invert__", "__next__", "append", "mro"]
    for _ in range(r.randrange(8, 20)):
        t, d = r.choice(types_), r.choice(dunders)
        k = r.randrange(6)
        args = [r.choice(objs) for _ in range(r.randrange(4))]
        f = attr(name(t), d)
        if k == 0:
            g.probe(f)
        elif k < 4:
            g.probe(["call", f, args, []])
        elif k == 4:
            g.probe(["call", attr(r.choice(objs), d), args[:2], []])
        else:
            g.probe(["call", f, args, [["zz", lit(1)]]])
    g.probe(call(attr(name("object"), "__setattr__"), name("A"), lit("x"), lit(1)))
    g.probe(call(attr(name("object"), "__delattr__"), name("A"), lit("x")))
    g.probe(call(attr(name("type"), "__setattr__"), name("A"), lit("x"), lit(1)))
    g.probe(attr(name("A"), "x"))
    g.probe(call(attr(name("type"), "__setattr__"), name("D"), lit("x"), lit(1)))
    g.probe(call(attr(name("object"), "__setattr__"), name("D"), lit("x"), lit(1)))
    g.probe(call(attr(name("object"), "__setattr__"), name("int"), lit("x"), lit(1)))
    g.probes(["setattr", name("int"), "x", lit(1)])
    g.probes(["delattr", name("int"), "real"])
    for t in types_[:7]:
        g.probe(call(attr(name("object"), "__new__"), name(t)))
        g.probe(call(attr(name(r.choice(types_)), "__new__"), name(t)))
    g.probe(call(attr(name("object"), "__new__"), lit(1)))
    g.probe(call(attr(name("object"), "__new__")))
    g.probe(call(attr(name("object"), "__new__"), name("A"), lit(1)))
    g.probe(call(attr(name("object"), "__init__"), name("a"), lit(1)))
    g.probe(call(name("object"), lit(1)))
    g.probe(call(name("A"), lit(1)))


def fam_abstract(g):
    r = g.rng
    cls(g, "A", (), [simple_method(g, "m", "A.m", ["self"], lit(1))])
    k = r.randrange(5)
    v = {0: ["tuple", [lit("m"), lit("n")]], 1: ["tuple", []], 2: lit(1), 3: ["list", [lit(1)]],
         4: ["list", [lit("b"), lit("a")]]}[k]
    g.probes(["setattr", name("A"), "__abstractmethods__", v])
    g.probe(attr(name("A"), "__abstractmethods__"))
    g.probe(call(name("A")))
    cls(g, "B", ["A"], None)
    g.probe(call(name("type"), call(name("B"))))
    g.probe(attr(name("B"), "__abstractmethods__"))
    g.probes(["delattr", name("A"), "__abstractmethods__"])
    g.probe(call(name("type"), call(name("A"))))
    g.probes(["delattr", name("A"), "__abstractmethods__"])
    g.probe(attr(name("type"), "__abstractmethods__"))
    g.probe(attr(name("int"), "__abstractmethods__"))


def fam_type_attrs(g):
    r = g.rng
    cls(g, "A", (), [["assign", "__doc__", r.choice([lit("d"), lit(1), NONE])]])
    cls(g, "B", ["A"], None)
    cls(g, "M", ["type"], [["assign", "mv", lit(1)],
                           simple_method(g, "mm", "M.mm", ["cls"], lit(2))])
    cls(g, "C", (), None, kw=[["metaclass", name("M")]])
    for n, v in [("__name__", lit("Z")), ("__name__", lit(1)), ("__name__", lit("a\x00")),
                 ("__qualname__", lit("Y")), ("__qualname__", lit(1)), ("__module__", lit("m")),
                 ("__doc__", lit("nd")), ("__mro__", ["tuple", []]), ("__dict__", ["dict", []]),
                 ("__base__", name("object")), ("__basicsize__", lit(1))]:
        if r.random() < 0.5:
            t = r.choice(["A", "B"] if n == "__doc__" else ["A", "B", "int"])
            g.probes(["setattr", name(t), n, v])
            g.probe(attr(name(t), n))
            if r.random() < 0.3:
                g.probes(["delattr", name(t), n])
    for t in ["A", "B", "C"]:
        for n in ["__doc__", "__name__", "__qualname__", "__module__", "__base__", "__bases__"]:
            g.probe(attr(name(t), n))
        g.probe(attr(name(t), "mv"))
        g.probe(call(attr(name(t), "mm")))
        g.probe(attr(call(name(t)), "mv"))
        g.probes(["setattr", name(t), "newattr", lit(1)])
        g.probe(attr(name(t), "newattr"))
        g.probes(["delattr", name(t), "newattr"])
        g.probes(["delattr", name(t), "newattr"])
        g.probe(call(name("isinstance"), name(t), name("M")))
        g.probe(call(name("repr"), name(t)))
        g.probe(call(name("repr"), call(name(t))))
        g.probe(call(name("str"), name(t)))
    g.probe(call(name("dir"), name("B")))
    g.probe(call(name("dir"), call(name("B"))))
    g.probe(call(attr(name("object"), "__subclasses__")) if False else NONE)
    # __hash__ inheritance through assignment.
    cls(g, "H", (), [simple_method(g, "__eq__", "H.__eq__", ["s", "o"], lit(True))])
    g.probe(attr(name("H"), "__hash__"))
    g.probe(call(name("_hash"), call(name("H"))))
    cls(g, "H2", ["H"], None)
    g.probe(attr(name("H2"), "__hash__"))
    g.probes(["setattr", name("H"), "__hash__", attr(name("object"), "__hash__")])
    g.probe(call(name("_hash"), call(name("H"))))
    g.probe(call(name("_hash"), call(name("H2"))))
    cls(g, "H3", ["H"], [simple_method(g, "__hash__", "H3.__hash__", ["s"], lit(4))])
    g.probe(call(name("_hash"), call(name("H3"))))
    g.probes(["delattr", name("H3"), "__hash__"])
    g.probe(call(name("_hash"), call(name("H3"))))


def fam_slot_updates(g):
    """Assigning dunders after class creation updates slots in subclasses."""
    r = g.rng
    cls(g, "A", (), None)
    cls(g, "B", ["A"], None)
    cls(g, "C", ["B"], [simple_method(g, "__len__", "C.__len__", ["s"], lit(1))] if r.random() < 0.5 else None)
    fs = {"__add__": ["s", "o"], "__radd__": ["s", "o"], "__len__": ["s"], "__bool__": ["s"],
          "__eq__": ["s", "o"], "__hash__": ["s"], "__getitem__": ["s", "k"], "__iter__": ["s"],
          "__call__": ["s"], "__getattr__": ["s", "n"], "__repr__": ["s"],
          "__contains__": ["s", "x"], "__index__": ["s"], "__next__": ["s"], "__get__": ["s", "o", "t"]}
    for n, ps in fs.items():
        g.main.append(g.method("f" + n, "f" + n, ps, [["log", "f" + n], ["ret", lit(1)]]))
    def probes():
        o = name(r.choice(["oA", "oB", "oC"]))
        k = r.randrange(9)
        g.probe({0: ["bin", "+", o, lit(1)], 1: ["bin", "+", lit(1), o], 2: call(name("len"), o),
                 3: ["un", "not", o], 4: ["cmp", "==", o, lit(1)], 5: call(name("_hash"), o),
                 6: ["sub", o, lit(0)], 7: call(o), 8: attr(o, "zz")}[k])
    for c in "ABC":
        g.main.append(["assign", "o" + c, call(name(c))])
    for _ in range(r.randrange(5, 14)):
        n = r.choice(list(fs))
        t = r.choice("ABC")
        k = r.random()
        if k < 0.55:
            g.probes(["setattr", name(t), n, name("f" + n)])
        elif k < 0.75:
            g.probes(["setattr", name(t), n, NONE])
        else:
            g.probes(["delattr", name(t), n])
        probes()
        probes()


def fam_descriptors(g):
    """Descriptor objects used directly; bound method identity."""
    r = g.rng
    g.main.append(g.method("f", "f", ["self"], [["log", "f"], ["ret", name("self")]]))
    cls(g, "A", (), [["assign", "__slots__", ["tuple", [lit("s")]]],
                     ["assign", "m", name("f")],
                     ["assign", "cm", call(name("classmethod"), name("f"))],
                     ["assign", "sm", call(name("staticmethod"), name("f"))]])
    cls(g, "B", ["A"], None)
    cls(g, "Z", (), None)
    g.main.append(["assign", "a", call(name("A"))])
    g.main.append(["assign", "b", call(name("B"))])
    g.main.append(["assign", "z", call(name("Z"))])
    desc = [attr(name("A"), "m"), attr(name("A"), "s"), attr(name("list"), "append"),
            attr(name("object"), "__class__") if False else attr(name("int"), "real"),
            attr(name("object"), "__repr__"), attr(name("str"), "__add__"),
            ["sub", attr(name("A"), "__dict__"), lit("cm")],
            ["sub", attr(name("A"), "__dict__"), lit("sm")],
            ["sub", attr(name("A"), "__dict__"), lit("s")],
            ["sub", attr(name("type"), "__dict__"), lit("__name__")],
            ["sub", attr(name("type"), "__dict__"), lit("__dict__")],
            ["sub", attr(name("object"), "__dict__"), lit("__class__")]]
    for _ in range(r.randrange(6, 14)):
        d = r.choice(desc)
        k = r.randrange(6)
        o = r.choice([name("a"), name("b"), name("z"), lit(1), NONE, ["list", []]])
        c = r.choice([name("A"), name("B"), name("Z"), NONE, lit(1), name("int")])
        if k == 0:
            g.probe(call(attr(d, "__get__"), o))
        elif k == 1:
            g.probe(call(attr(d, "__get__"), o, c))
        elif k == 2:
            g.probe(call(attr(d, "__set__"), o, lit(1)))
        elif k == 3:
            g.probe(call(attr(d, "__delete__"), o))
        elif k == 4:
            g.probe(attr(d, r.choice(["__name__", "__objclass__", "__qualname__"])))
        else:
            g.probe(call(attr(d, "__get__")))
    g.probes(["setattr", name("a"), "s", lit(1)])
    g.probe(attr(name("a"), "s"))
    g.probes(["delattr", name("a"), "s"])
    g.probes(["delattr", name("a"), "s"])
    g.probe(attr(name("a"), "s"))
    g.probe(attr(name("a"), "__dict__"))
    g.probes(["setattr", name("a"), "zz", lit(1)])
    g.probe(["cmp", "==", attr(name("a"), "m"), attr(name("a"), "m")])
    g.probe(["cmp", "!=", attr(name("a"), "m"), attr(name("b"), "m")])
    g.probe(["is", attr(name("a"), "m"), attr(name("a"), "m")])
    g.probe(["cmp", "==", attr(lit(1), "__add__"), attr(lit(1), "__add__")])
    g.probe(["cmp", "==", attr(["list", []], "append"), attr(["list", []], "append")])
    g.probe(attr(attr(name("a"), "m"), "__self__"))
    g.probe(attr(attr(name("a"), "m"), "__func__"))
    g.probe(attr(attr(name("a"), "m"), "__name__"))
    g.probe(attr(attr(name("a"), "m"), "__doc__"))
    g.probe(attr(attr(name("a"), "m"), "zz"))
    g.probes(["setattr", attr(name("a"), "m"), "zz", lit(1)])
    g.probe(call(attr(name("a"), "cm")))
    g.probe(call(attr(name("b"), "cm")))
    g.probe(call(attr(name("B"), "cm")))
    g.probe(call(attr(name("a"), "sm"), lit(1)))
    g.probe(attr(["sub", attr(name("A"), "__dict__"), lit("cm")], "__func__"))
    g.probe(attr(["sub", attr(name("A"), "__dict__"), lit("sm")], "__wrapped__"))
    g.probe(call(name("classmethod")))
    g.probe(call(name("staticmethod"), lit(1), lit(2)))
    g.probe(call(call(name("staticmethod"), name("f")), lit(1)))
    g.probe(call(call(name("classmethod"), name("f")), lit(1)))
    g.probe(attr(call(name("staticmethod"), name("f")), "__name__"))
    g.probe(attr(call(name("classmethod"), name("f")), "__doc__"))


def fam_iter_seq(g):
    """Sequence protocol edge cases through __getitem__, negative indexes, __length_hint__."""
    r = g.rng
    body = []
    ln = r.choice([lit(2), lit(0), lit(-1), lit("s"), lit(["bigint", str(2**63)]), None])
    if ln is not None:
        body.append(simple_method(g, "__len__", "S.__len__", ["s"], ln))
    if r.random() < 0.8:
        body.append(g.method("__getitem__", "S.__getitem__", ["s", "i"],
                             [["log", "S.__getitem__"],
                              ["if", ["cmp", ">=", name("i"), lit(r.choice([0, 1, 2]))],
                               [["raise", name(r.choice(["IndexError", "StopIteration", "ValueError"]))]],
                               [["ret", name("i")]]]]))
    if r.random() < 0.4:
        body.append(simple_method(g, "__length_hint__", "S.__length_hint__", ["s"],
                                  r.choice([lit(1), lit(-1), lit("s"), NOTIMPL, lit(["bigint", str(2**64)])])))
    if r.random() < 0.2:
        body.append(g.method("__length_hint__", "S.__length_hint__", ["s"],
                             [["raise", call(name(r.choice(["TypeError", "ValueError"])), lit("h"))]]))
    if r.random() < 0.3:
        body.append(simple_method(g, "__mul__", "S.__mul__", ["s", "o"], NOTIMPL))
    cls(g, "S", (), body)
    g.main.append(["assign", "s", call(name("S"))])
    for e in [call(name("list"), name("s")), call(name("tuple"), name("s")),
              ["in", lit(1), name("s")], ["in", lit(0), name("s")], ["sub", name("s"), lit(-1)],
              call(name("iter"), name("s")), call(name("next"), call(name("iter"), name("s"))),
              call(attr(name("object"), "__len__"), name("s")),
              ["bin", "*", lit(2), ["list", [name("s")]]],
              ["bin", "*", name("s"), lit(2)], ["bin", "*", lit(2), name("s")]]:
        g.probe(e)
    g.probe(["bin", "*", ["list", [lit(1)]], lit(True)])
    g.probe(["bin", "*", ["list", [lit(1)]], lit(-1)])
    g.probe(["bin", "*", lit("ab"), lit(0)])
    g.probe(["bin", "*", ["tuple", [lit(1)]], lit(2)])
    g.probe(["bin", "+", ["list", [lit(1)]], ["list", [lit(2)]]])
    g.probe(["bin", "+", ["tuple", [lit(1)]], ["tuple", [lit(2)]]])
    g.probe(["bin", "+", lit("a"), lit("b")])
    g.probe(["cmp", "==", ["list", [name("s")]], ["list", [name("s")]]])
    g.probe(["cmp", "<", ["tuple", [lit(1), name("s")]], ["tuple", [lit(2), name("s")]]])
    g.probe(["cmp", "<", ["tuple", [lit(1), name("s")]], ["tuple", [lit(1), lit(0)]]])
    g.probe(["cmp", "==", ["dict", [[lit(1), lit(2)]]], ["dict", [[lit(1), lit(2)]]]])
    g.probe(["in", name("s"), ["list", [name("s")]]])
    g.probe(call(name("list"), ["dict", [[lit("a"), lit(1)]]]))
    g.probe(call(name("next"), lit(1)))
    g.probe(call(name("next"), call(name("iter"), ["list", []]), lit("dflt")))
    # Exhausted iterators stay exhausted.
    g.main.append(["assign", "it", call(name("iter"), ["list", [lit(1)]])])
    g.probe(call(name("next"), name("it")))
    g.probe(call(name("next"), name("it")))
    g.probe(call(name("next"), name("it"), lit(0)))


def fam_numbers(g):
    r = g.rng
    vals = [lit(0), lit(1), lit(-7), lit(3), lit(True), lit(False), lit(100),
            lit(["bigint", str(2**64)]), lit(["bigint", str(-2**70)])]
    ops = ["+", "-", "*", "%", "//", "<<", ">>", "&", "|", "^", "**"]
    for _ in range(r.randrange(6, 16)):
        a, b = r.choice(vals), r.choice(vals)
        op = r.choice(ops)
        if op == "**" or op == "<<":
            b = r.choice([lit(0), lit(1), lit(3), lit(True), lit(-1)])
        g.probe(["bin", op, a, b])
        g.probe(["cmp", r.choice(CMP), a, b])
        g.probe(["un", r.choice(["-", "+", "~", "not"]), a])
    g.probe(call(name("divmod"), r.choice(vals), r.choice(vals)))
    g.probe(call(name("abs"), r.choice(vals)))
    g.probe(call(name("pow"), lit(2), lit(3)))
    g.probe(call(name("pow"), lit(2), lit(3), lit("s")))
    g.probe(call(name("int"), lit("12")))
    g.probe(call(name("int"), lit(" -3 ")))
    g.probe(call(name("int"), lit("x")))
    g.probe(call(name("int"), NONE))
    g.probe(call(name("float"), NONE))
    g.probe(call(name("bool"), lit(0)))
    g.probe(call(name("bool"), lit(1), lit(2)))
    g.probe(call(name("str"), lit(1)))
    g.probe(call(name("str"), NONE))
    g.probe(call(name("str"), lit(True)))
    g.probe(call(name("repr"), lit("a'b")))
    g.probe(call(name("repr"), ["tuple", [lit(1)]]))
    g.probe(call(name("repr"), ["list", [lit("a"), NONE]]))
    g.probe(call(name("repr"), ["dict", [[lit("k"), lit(1)]]]))
    g.probe(call(name("format"), lit(1)))
    g.probe(call(name("format"), lit("s"), lit("")))
    g.probe(call(name("format"), NONE, lit("x")))
    g.probe(call(name("_hash"), r.choice(vals)))
    cls(g, "I", ["int"], None)
    g.probe(["bin", "+", call(name("I"), lit(1)), lit(2)])
    g.probe(call(name("I"), lit("x")))
    g.probe(call(name("repr"), call(name("I"), lit(5))))


def fam_list_extend(g):
    """list += and list.__init__: the items before a raising __next__ stay in the list, the
    iterator can change the list, self-extension runs no Python code, and the size hint."""
    r = g.rng
    k = r.choice([0, 1, 2, 3])
    exc = r.choice(["ValueError", "TypeError", "StopIteration", "KeyError"])
    reenter = r.random() < 0.4
    # Sizes that fail the allocator's check at once: nothing large is allocated.
    hint = r.choice([None, None, lit(0), lit(1), lit(-1), lit("s"), NOTIMPL,
                     lit(["bigint", str(2**63 - 1)]), lit(["bigint", str(2**61)])])
    step = [["log", "It.__next__"],
            ["setattr", name("s"), "n", ["bin", "+", attr(name("s"), "n"), lit(1)]],
            ["if", ["cmp", ">", attr(name("s"), "n"), lit(k)],
             [["raise", call(name(exc), lit("e"))]], []]]
    if reenter:
        step.append(["expr", call(attr(attr(name("s"), "t"), "append"), lit(99))])
    step.append(["ret", attr(name("s"), "n")])
    body = [g.method("__iter__", "It.__iter__", ["s"], [["log", "It.__iter__"], ["ret", name("s")]]),
            g.method("__next__", "It.__next__", ["s"], step)]
    if hint is not None:
        body.append(simple_method(g, "__length_hint__", "It.__length_hint__", ["s"], hint))
    cls(g, "It", (), body)
    lbody = []
    if r.random() < 0.4:
        lbody.append(simple_method(g, "__len__", "L.__len__", ["s"], lit(3)))
    if r.random() < 0.4:
        lbody.append(g.method("__iter__", "L.__iter__", ["s"], [["log", "L.__iter__"], ["ret", lit(3)]]))
    cls(g, "L", ["list"], lbody or None)

    def fresh():
        new = ["list", [lit(1)]]
        if r.random() < 0.5:
            new = call(name("L"), new)
        g.main.append(["assign", "l", new])
        g.main.append(["assign", "it", call(name("It"))])
        g.main.append(["setattr", name("it"), "n", lit(0)])
        g.main.append(["setattr", name("it"), "t", name("l")])

    fresh()
    g.probes(["aug", "l", "+", name("it")])
    g.probe(name("l"))
    fresh()
    g.probe(call(attr(name("l"), "__init__"), name("it")))
    g.probe(name("l"))
    fresh()
    g.probes(["aug", "l", "+", name("l")])
    g.probe(name("l"))
    fresh()
    g.probe(call(attr(name("l"), "__init__"), name("l")))
    g.probe(name("l"))
    fresh()
    g.probe(call(attr(name("l"), "__init__"), call(name("iter"), name("l"))))
    g.probe(name("l"))
    fresh()
    g.probe(call(name("list"), name("it")))
    for v in [["tuple", [lit(5)]], ["list", [lit(5)]], ["dict", [[lit(5), lit(6)]]],
              call(attr(["dict", [[lit(5), lit(6)]]], "keys")), lit("ab"), lit(5), NONE,
              call(name("L"), ["list", [lit(5)]])]:
        fresh()
        g.probes(["aug", "l", "+", v])
        g.probe(name("l"))


def fam_repr(g):
    """Containers' repr: the recursion guard, its release on error, key then value order, and a
    __repr__ that mutates the container."""
    r = g.rng
    kind = r.choice(["log", "raise", "mutate", "raise-once"])
    def repr_body(q):
        out = [["log", q]]
        if kind == "raise":
            out.append(["raise", call(name(r.choice(["ValueError", "TypeError"])), lit("r"))])
        elif kind == "raise-once":
            out.append(["if", attr(name("s"), "armed"),
                        [["setattr", name("s"), "armed", lit(False)],
                         ["raise", call(name("ValueError"), lit("r"))]], []])
        elif kind == "mutate":
            out.append(["if", ["cmp", "<", call(name("len"), attr(name("s"), "t")), lit(4)],
                        [["expr", call(attr(attr(name("s"), "t"), "append"), lit(7))]], []])
        out.append(["ret", lit(q)])
        return out
    cls(g, "K", (), [g.method("__repr__", "K.__repr__", ["s"], repr_body("K")),
                     g.method("__hash__", "K.__hash__", ["s"], [["ret", lit(1)]])])
    cls(g, "V", (), [g.method("__repr__", "V.__repr__", ["s"], repr_body("V"))])
    g.main.append(["assign", "t", ["list", []]])
    g.main.append(["assign", "k", call(name("K"))])
    g.main.append(["assign", "v", call(name("V"))])
    for o in ("k", "v"):
        g.main.append(["setattr", name(o), "t", name("t")])
        g.main.append(["setattr", name(o), "armed", lit(True)])
    g.main.append(["expr", call(attr(name("t"), "append"), name("k"))])
    g.main.append(["expr", call(attr(name("t"), "append"), name("v"))])
    g.probe(call(name("repr"), name("t")))
    g.probe(call(name("repr"), ["dict", [[name("k"), name("v")], [lit(2), name("v")]]]))
    g.probe(call(name("repr"), ["tuple", [name("k"), name("v")]]))
    g.probe(call(name("repr"), ["tuple", [name("v")]]))
    # Cycles through a list, a dict and a tuple.
    g.main.append(["assign", "c", ["list", [lit(1)]]])
    g.main.append(["expr", call(attr(name("c"), "append"), name("c"))])
    g.probe(call(name("repr"), name("c")))
    g.main.append(["assign", "d", ["dict", [[lit(1), lit(2)]]]])
    g.main.append(["setitem", name("d"), lit(3), name("d")])
    g.probe(call(name("repr"), name("d")))
    g.main.append(["assign", "e", ["list", []]])
    g.main.append(["assign", "u", ["tuple", [name("e")]]])
    g.main.append(["expr", call(attr(name("e"), "append"), name("u"))])
    g.probe(call(name("repr"), name("e")))
    g.probe(call(name("repr"), name("u")))
    g.probe(call(name("repr"), ["list", [name("e"), name("e")]]))
    g.probe(call(name("repr"), ["dict", []]))
    g.probe(call(name("repr"), ["tuple", []]))
    g.probe(call(name("repr"), ["list", []]))
    cls(g, "DL", ["dict"], None)
    g.main.append(["assign", "x", call(name("DL"))])
    g.main.append(["setitem", name("x"), name("k"), name("x")])
    g.probe(call(name("repr"), name("x")))
    g.probe(call(name("format"), name("x")))
    g.probe(call(name("str"), name("c")))
    # The guard was released: the same objects print again.
    g.probe(call(name("repr"), name("t")))


FAMILIES = [fam_calls, fam_property, fam_super, fam_mro, fam_class_stmt, fam_class_assign,
            fam_wrappers, fam_abstract, fam_type_attrs, fam_slot_updates, fam_descriptors,
            fam_iter_seq, fam_numbers, fam_list_extend, fam_repr]


def gen_case(rng):
    g = G(rng)
    if rng.random() < 0.5:
        g.descr_classes()
        g.make_classes()
        g.instances()
        g.probes_random(rng.randrange(6, 16))
    else:
        rng.choice(FAMILIES)(g)
    return {"mod": "typeobj", "fn": "scenario", "codes": g.codes, "main": g.main}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=2000)
