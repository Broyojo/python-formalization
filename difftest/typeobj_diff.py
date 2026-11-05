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

import operator
import re
import struct
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
        if v[0] == "float":
            return repr(struct.unpack("<d", int(v[1]).to_bytes(8, "little"))[0])
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
        return float.__repr__(v)
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
    if issubclass(tv, float):
        return f"<{tn} {float.__repr__(v)}>"
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


# Object addresses only: " at 0x7f..." in reprs. A bare hex number elsewhere ("can't decode byte
# 0xc3") is part of the message and is compared as it is.
ADDR = re.compile(r" at 0x[0-9a-f]+")


warnings.simplefilter("ignore")


def run_sized(case):
    import _testlimitedcapi
    _, sub, _, _, off, size = _testlimitedcapi.make_sized_heaptypes(case["extra"], case["spec"])
    return {"ok": [sub.__basicsize__, off, size]}


def run_python(case):
    if case["fn"] == "fromspec_sizes":
        return run_sized(case)
    src_lines = []
    block_src(case["main"], case["codes"], 0, src_lines)
    trace = []

    def text(e):
        try:
            s = str(e)
        except BaseException:
            s = "<str failed>"
        return f"!{type(e).__name__}: {ADDR.sub(' at 0x0', s)}"

    def probe(tag, f):
        try:
            out = canon(f())
        except BaseException as e:
            out = text(e)
        trace.append(f"{tag}={ADDR.sub(' at 0x0', out)}")

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
           "_text": text, "_hash": hash_probe, "countOf": operator.countOf,
           "indexOf": operator.indexOf}
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
        if r.random() < 0.1:
            # `%.100s`/`%.200s` of `tp_name` cut UTF-8 bytes, not characters.
            names[-1] = r.choice(LONG_CLASS_NAMES)
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

# Class names around the byte limits of `%.50s`, `%.100s` and `%.200s`: 2-, 3- and 4-byte
# characters, and cuts that fall inside one.
LONG_CLASS_NAMES = ["\u00e9" * 101, "a" + "\u00e9" * 50, "\u4e2d" * 34, "ab" + "\U00010000" * 50,
                    "X" * 99 + "\u00e9"]


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


def fam_descr_proto(g):
    """Protocols of the descriptor family, on their failure paths: a mappingproxy over a user
    mapping that can raise, a bound method whose __func__ or __self__ misbehaves, and the two
    argument parsers of super."""
    r = g.rng
    fail = r.choice(["ok", "raise", "ok"])

    def body(q, ret):
        out = [["log", q]]
        if fail == "raise":
            out.append(["raise", call(name(r.choice(["ValueError", "TypeError", "KeyError"])), lit("m"))])
        out.append(["ret", ret])
        return out

    m = [g.method("__getitem__", "M.__getitem__", ["s", "k"], body("M.__getitem__", name("k"))),
         g.method("__len__", "M.__len__", ["s"], body("M.__len__", lit(3))),
         g.method("__contains__", "M.__contains__", ["s", "k"], body("M.__contains__", lit(True))),
         g.method("__iter__", "M.__iter__", ["s"], body("M.__iter__", call(name("iter"), ["list", [lit(1)]]))),
         g.method("__eq__", "M.__eq__", ["s", "o"], body("M.__eq__", lit(1))),
         g.method("__or__", "M.__or__", ["s", "o"], body("M.__or__", lit(2))),
         g.method("__ror__", "M.__ror__", ["s", "o"], body("M.__ror__", lit(3))),
         g.method("__repr__", "M.__repr__", ["s"], body("M.__repr__", lit("mr"))),
         g.method("__str__", "M.__str__", ["s"], body("M.__str__", lit("ms")))]
    if r.random() < 0.5:
        m.append(g.method("__hash__", "M.__hash__", ["s"], body("M.__hash__", lit(5))))
    cls(g, "M", (), m)
    cls(g, "A", (), [g.method("m", "A.m", ["s"], [["ret", lit(1)]]),
                     g.method("__repr__", "A.__repr__", ["s"], body("A.__repr__", lit("ar")))])
    g.main.append(["assign", "a", call(name("A"))])
    g.main.append(["assign", "Proxy", call(name("type"), attr(name("A"), "__dict__"))])
    g.main.append(["assign", "Meth", call(name("type"), attr(name("a"), "m"))])
    g.probes(["assign", "p", call(name("Proxy"), call(name("M")))])
    for e in [call(name("len"), name("p")), ["sub", name("p"), lit(1)], ["in", lit(1), name("p")],
              call(name("next"), call(name("iter"), name("p"))), call(name("_hash"), name("p")),
              call(name("str"), name("p")), call(name("repr"), name("p")),
              ["cmp", "==", name("p"), lit(1)], ["cmp", "!=", name("p"), lit(1)],
              ["cmp", "<", name("p"), lit(1)], ["bin", "|", name("p"), lit(1)],
              ["bin", "|", lit(1), name("p")], call(attr(name("p"), "__ior__"), lit(1)),
              call(name("Proxy"), name("p")), call(name("Proxy"), ["list", []]),
              call(name("Proxy"), ["tuple", []]), call(name("Proxy"), lit(1)), call(name("Proxy")),
              call(name("Proxy"), lit(1), lit(2)), call(name("Proxy"), ["dict", [[lit(1), lit(2)]]]),
              # Lengths: the class dict holds __firstlineno__, a line of the generated source.
              call(name("len"), ["bin", "|", attr(name("A"), "__dict__"), ["dict", []]]),
              call(name("len"), ["bin", "|", ["dict", []], attr(name("A"), "__dict__")]),
              ["in", lit("m"), attr(name("A"), "__dict__")],
              call(name("repr"), call(name("Proxy"), ["dict", [[lit(1), name("a")]]]))]:
        g.probe(e)
    g.probes(["aug", "p", "|", lit(1)])
    # Bound methods.
    cls(g, "C", (), [g.method("__call__", "C.__call__", ["s", "*a"] if False else ["s"], [["ret", lit(1)]]),
                     ["assign", "__hash__", NONE],
                     ["assign", "__qualname__", lit(1)] if False else ["assign", "zz", lit(1)]])
    g.main.append(["assign", "c", call(name("C"))])
    for e in [call(name("Meth"), lit(1), lit(2)), call(name("Meth"), name("c"), NONE),
              call(name("Meth"), name("c")), call(name("Meth")),
              call(name("Meth"), name("c"), name("a")),
              call(name("repr"), call(name("Meth"), name("c"), name("a"))),
              call(name("_hash"), call(name("Meth"), name("c"), name("a"))),
              call(name("_hash"), attr(name("a"), "m")),
              call(name("repr"), attr(name("a"), "m")),
              ["cmp", "==", attr(name("a"), "m"), attr(name("a"), "m")],
              ["cmp", "==", attr(name("a"), "m"), attr(call(name("A")), "m")],
              ["cmp", "<", attr(name("a"), "m"), attr(name("a"), "m")],
              call(name("repr"), attr(name("A"), "m")), call(name("repr"), name("len")),
              call(name("repr"), attr(["list", []], "append")),
              call(name("repr"), attr(name("list"), "append")),
              call(name("repr"), attr(name("int"), "__add__")),
              call(name("repr"), attr(lit(1), "__add__")),
              call(name("repr"), ["sub", attr(name("type"), "__dict__"), lit("__bases__")]),
              call(name("repr"), call(name("classmethod"), attr(name("A"), "m"))),
              call(name("repr"), call(name("staticmethod"), attr(name("a"), "m"))),
              ["sub", name("type"), lit(1)]]:
        g.probe(e)
    # A __set_name__ that raises: the note goes on as a __notes__ attribute.
    cls(g, "SN", (), [g.method("__set_name__", "SN.__set_name__", ["s", "o", "n"],
                               [["raise", call(name(r.choice(["ValueError", "TypeError"])), lit("sn"))]])])
    g.main.append(["assign", "nn", NONE])
    g.main.append(["try", [["assign", "T", call(name("type"), lit("T"), ["tuple", []],
                                                ["dict", [[lit("x"), call(name("SN"))]]])]],
                   name("BaseException"), "t",
                   [["assign", "nn", call(name("getattr"), name("t"), lit("__notes__"), NONE)]]])
    g.probe(name("nn"))
    # The two parsers of super: exact super is super_vectorcall, the rest super_init.
    cls(g, "S", ["super"], None)
    for f in ["super", "S"]:
        for args in [[lit(1)], [name("A"), lit(1)], [name("A"), name("a"), lit(1)],
                     [name("int"), lit("s")], [name("A")], [name("A"), name("a")]]:
            g.probe(call(name("repr"), call(name(f), *args)))
    g.probe(call(attr(call(name("super"), name("A")), "__init__"), lit(1)))
    g.probe(call(attr(call(name("super"), name("A")), "__init__"), name("A"), name("a"), lit(1)))
    g.probe(call(name("repr"), attr(call(name("super"), name("A"), name("a")), "m")))
    g.probe(call(attr(["dict", []], "__ior__"), lit(1)))
    g.probe(call(attr(["dict", []], "__ior__"), ["list", [["tuple", [lit(1), lit(2)]]]]))
    g.probe(call(attr(["dict", []], "__or__"), lit(1)))


def fam_dict_update(g):
    """dict update paths, which all store as they go: the pairs before a failure stay, an update
    merges into what the dict holds, and the iterators and keys() are live."""
    r = g.rng
    k = r.choice([0, 1, 2, 3])
    exc = r.choice(["ValueError", "TypeError", "KeyError", "StopIteration"])
    item = r.choice([["tuple", [attr(name("s"), "n"), lit(1)]],
                     ["list", [attr(name("s"), "n"), lit(1)]],
                     ["tuple", [lit(1), lit(2), lit(3)]], ["tuple", [lit(1)]], lit(5), NONE,
                     ["tuple", [["list", []], lit(1)]], lit("ab"), lit("abc")])
    step = [["log", "P.__next__"],
            ["setattr", name("s"), "n", ["bin", "+", attr(name("s"), "n"), lit(1)]],
            ["if", ["cmp", ">", attr(name("s"), "n"), lit(k)],
             [["raise", call(name(exc), lit("e"))]], []],
            ["ret", ["tuple", [attr(name("s"), "n"), lit(1)]] if r.random() < 0.6 else item]]
    p = [g.method("__iter__", "P.__iter__", ["s"], [["log", "P.__iter__"], ["ret", name("s")]]),
         g.method("__next__", "P.__next__", ["s"], step),
         simple_method(g, "__len__", "P.__len__", ["s"], lit(3))]
    cls(g, "P", (), p)
    getit = [["log", "K.__getitem__"]]
    if r.random() < 0.4:
        getit.append(["expr", call(attr(attr(name("s"), "ks"), "append"), lit(9))])
    getit.append(["if", ["cmp", ">", name("x"), lit(k)],
                  [["raise", call(name(exc), lit("e"))]], []])
    getit.append(["ret", name("x")])
    keys_ret = r.choice([attr(name("s"), "ks"), call(name("tuple"), attr(name("s"), "ks")),
                         lit(5), NONE])
    cls(g, "K", (), [g.method("keys", "K.keys", ["s"], [["log", "K.keys"], ["ret", keys_ret]]),
                     g.method("__getitem__", "K.__getitem__", ["s", "x"], getit)])
    cls(g, "DS", ["dict"], [g.method("__iter__", "DS.__iter__", ["s"],
                                     [["log", "DS.__iter__"], ["ret", lit(3)]])])

    def src(kind):
        if kind == "pairs":
            g.main.append(["assign", "x", call(name("P"))])
            g.main.append(["setattr", name("x"), "n", lit(0)])
        else:
            g.main.append(["assign", "x", call(name("K"))])
            g.main.append(["setattr", name("x"), "ks", ["list", [lit(0), lit(1), lit(2), lit(3)]]])

    for kind in ("pairs", "keys"):
        for tgt in (["dict", [[lit(9), lit(9)]]], call(name("DS"), ["dict", [[lit(9), lit(9)]]])):
            src(kind)
            g.main.append(["assign", "d", tgt])
            g.main.append(["assign", "nn", NONE])
            # The note on a TypeError from an item that is not a sequence.
            g.main.append(["try", [["aug", "d", "|", name("x")]], name("BaseException"), "t",
                           [["assign", "nn", call(name("getattr"), name("t"), lit("__notes__"), NONE)]]])
            g.probe(name("nn"))
            g.probe(name("d"))
            src(kind)
            g.main.append(["assign", "d", tgt])
            g.probe(call(attr(name("d"), "__init__"), name("x")))
            g.probe(name("d"))
            src(kind)
            g.main.append(["assign", "d", tgt])
            g.probe(["bin", "|", name("d"), name("x")])
            g.probe(name("d"))
        src(kind)
        g.probe(call(name("dict"), name("x")))
    g.main.append(["assign", "d", ["dict", [[lit(9), lit(9)]]]])
    g.probe(call(attr(name("d"), "__init__")))
    g.probe(name("d"))
    g.probe(call(attr(name("d"), "__init__"), ["dict", [[lit(1), lit(2)]]]))
    g.probe(name("d"))
    g.probe(call(attr(name("d"), "__init__"), ["list", [["tuple", [lit(3), lit(4)]]]]))
    g.probe(name("d"))
    g.main.append(["assign", "e", call(name("DS"), ["dict", [[lit(5), lit(6)]]])])
    g.probe(call(name("dict"), name("e")))
    g.probe(["bin", "|", ["dict", []], name("e")])
    g.probe(call(attr(name("d"), "__init__"), name("e")))
    g.probe(name("d"))


def fam_dict_lookup(g):
    """dict lookup: __eq__ runs only on equal stored hashes, not on identity, and its result, its
    exception and its changes to the dict all count."""
    r = g.rng
    mode = r.choice(["true", "false", "raise", "notimpl", "truthy", "falsy-raises", "clear", "other"])
    eq = [["log", "K.__eq__"]]
    if mode == "raise":
        eq.append(["raise", call(name(r.choice(["ValueError", "TypeError", "KeyError"])), lit("q"))])
    elif mode == "clear":
        # Deletes an earlier entry: C leaves the entry under comparison where it is.
        eq.append(["if", ["in", lit(51), name("target")],
                   [["delitem", name("target"), lit(51)]], []])
        eq.append(["ret", lit(False)])
    elif mode == "other":
        eq.append(["setitem", name("other"), lit(70), lit(1)])
        eq.append(["ret", lit(False)])
    else:
        eq.append(["ret", {"true": lit(True), "false": lit(False), "notimpl": NOTIMPL,
                           "truthy": lit("yes"), "falsy-raises": call(name("B"))}[mode]])
    cls(g, "B", (), [g.method("__bool__", "B.__bool__", ["s"],
                              [["log", "B.__bool__"], ["raise", call(name("ValueError"), lit("b"))]])])
    cls(g, "K", (), [g.method("__hash__", "K.__hash__", ["s"],
                              [["log", "K.__hash__"], ["ret", attr(name("s"), "h")]]),
                     g.method("__eq__", "K.__eq__", ["s", "o"], eq),
                     g.method("__repr__", "K.__repr__", ["s"], [["ret", lit("K")]])])
    g.main.append(["assign", "target", ["dict", []]])
    g.main.append(["assign", "other", ["dict", []]])

    def key(v, h):
        g.main.append(["assign", v, call(name("K"))])
        g.main.append(["setattr", name(v), "h", lit(h)])

    h = r.choice([1, 2, 7])
    key("k1", h)
    key("k2", h)
    key("k3", r.choice([h, h + 1]))
    if mode == "clear":
        # 51 has a home slot of its own: reuse of a freed slot among keys of equal hash needs the
        # real table, and the model visits such keys in insertion order (see `dictProbe`).
        g.main.append(["setitem", name("target"), lit(51), lit(0)])
    g.probes(["setitem", name("target"), name("k1"), lit("one")])
    for e in [name("target"), ["in", name("k1"), name("target")], ["in", name("k2"), name("target")],
              ["in", name("k3"), name("target")], ["sub", name("target"), name("k1")],
              ["sub", name("target"), name("k2")], ["sub", name("target"), name("k3")],
              ["in", lit(h), name("target")], ["sub", name("target"), lit(h)], name("target")]:
        g.probe(e)
    g.probes(["setitem", name("target"), name("k2"), lit("two")])
    g.probe(name("target"))
    g.probes(["setitem", name("target"), lit(h), lit("int")])
    g.probe(name("target"))
    g.probes(["delitem", name("target"), name("k3")])
    g.probe(name("target"))
    g.probes(["delitem", name("target"), name("k1")])
    g.probe(name("target"))
    # Numbers and strs that compare equal share a key, and the first key object stays.
    for e in [["dict", [[lit(1), lit("a")], [lit(True), lit("b")]]],
              ["dict", [[lit(True), lit("a")], [lit(1), lit("b")]]],
              ["dict", [[lit(0), lit("a")], [lit(False), lit("b")], [lit(2), lit("c")]]],
              ["in", lit(True), ["dict", [[lit(1), lit("a")]]]],
              ["sub", ["dict", [[lit(1), lit("a")]]], lit(True)],
              ["sub", ["dict", [[lit(-1), lit("a")]]], lit(-2)],
              ["in", lit(-2), ["dict", [[lit(-1), lit("a")]]]],
              ["sub", ["dict", [[lit(["bigint", str(2**61 - 1)]), lit("a")]]], lit(0)],
              ["in", lit(2**31), ["dict", [[lit(2**31), lit("a")]]]],
              ["sub", ["dict", [[["tuple", [lit(1), lit("a")]], lit(5)]]], ["tuple", [lit(1), lit("a")]]],
              ["sub", ["dict", [[["tuple", [lit(True)]], lit(5)]]], ["tuple", [lit(1)]]],
              ["dict", [[["list", []], lit(1)]]], ["sub", ["dict", []], ["list", []]],
              ["in", ["dict", []], ["dict", []]],
              ["dict", [[lit("a"), lit(1)], [lit("a"), lit(2)]]]]:
        g.probe(e)
    # str subclass keys: the stored key is what the comparison starts from.
    cls(g, "S", ["str"], [g.method("__eq__", "S.__eq__", ["s", "o"], [["log", "S.__eq__"], ["ret", lit(True)]]),
                          g.method("__hash__", "S.__hash__", ["s"], [["log", "S.__hash__"],
                                                                     ["ret", call(name("hash"), lit("zz"))]])])
    for e in [["sub", ["dict", [[call(name("S"), lit("x")), lit(1)]]], lit("zz")],
              ["sub", ["dict", [[lit("zz"), lit(1)]]], call(name("S"), lit("x"))],
              ["in", lit("x"), ["dict", [[call(name("S"), lit("x")), lit(1)]]]]]:
        g.probe(e)
    # __missing__ belongs to subclasses, looked up on the type.
    miss = r.choice([[["ret", name("k")]], [["raise", call(name("ValueError"), name("k"))]]])
    cls(g, "MD", ["dict"], [g.method("__missing__", "MD.__missing__", ["s", "k"],
                                     [["log", "MD.__missing__"]] + miss)])
    cls(g, "ND", ["dict"], None)
    g.main.append(["assign", "md", call(name("MD"), ["dict", [[lit(1), lit(2)]]])])
    g.main.append(["assign", "nd", call(name("ND"))])
    g.main.append(["setattr", name("nd"), "__missing__", lit(1)])
    for e in [["sub", name("md"), lit(1)], ["sub", name("md"), lit(9)], ["in", lit(9), name("md")],
              ["sub", name("nd"), lit(9)]]:
        g.probe(e)
    # dict_equal compares aval with bval, after a lookup with the stored hash.
    g.main.append(["assign", "x", ["dict", [[lit(1), call(name("K"))]]]])
    g.main.append(["assign", "y", ["dict", [[lit(1), call(name("K"))]]]])
    g.probe(["cmp", "==", name("x"), name("y")])
    g.probe(["cmp", "!=", name("x"), name("y")])
    g.probe(["cmp", "<", name("x"), name("y")])
    g.probe(["cmp", "==", ["dict", [[name("k1"), lit(1)]]], ["dict", [[name("k2"), lit(1)]]]])
    g.probe(["cmp", "==", ["dict", [[lit(1), lit(1)]]], ["dict", [[lit(True), lit(True)]]]])
    g.probe(["cmp", "==", ["dict", [[lit(1), lit(1)]]], ["dict", [[lit(2), lit(1)]]]])
    # A merge into a dict that holds something compares keys, and sees a change to the source.
    g.main.append(["assign", "other", ["dict", [[name("k1"), lit(1)], [lit(3), lit(4)]]]])
    g.main.append(["assign", "target", ["dict", [[name("k2"), lit(2)]]]])
    g.probes(["aug", "target", "|", name("other")])
    g.probe(name("target"))
    g.probe(name("other"))
    # tuple_hash, against real values.
    for t in [(), (1,), (1, 2), (1, (2, 3)), (None,), (True, False), (-1,), (2**61 - 1, 2**64)]:
        def tv(x):
            if isinstance(x, tuple):
                return ["tuple", [tv(i) for i in x]]
            return lit(["bigint", str(x)]) if isinstance(x, int) and not isinstance(x, bool) and abs(x) > 2**31 else lit(x)
        g.probe(["cmp", "==", call(name("hash"), tv(t)), lit(["bigint", str(hash(t))])])


def fam_reduce(g):
    """object.__getstate__, __reduce__ and __reduce_ex__, with copyreg: the validation of
    __getnewargs_ex__ and __slotnames__, slots, and overrides that raise or lie."""
    r = g.rng
    body = [g.method("m", "A.m", ["s"], [["ret", lit(1)]])]
    slots = r.choice([None, None, ["tuple", []], ["tuple", [lit("a"), lit("b")]], lit("a"),
                      ["list", [lit("a"), lit("__dict__")]], ["tuple", [lit("__p"), lit("__q__")]]])
    if slots is not None:
        body.append(["assign", "__slots__", slots])
    ng = r.choice(["none", "none", "good", "kw", "notuple", "len3", "firstbad", "secondbad", "raise"])
    if ng != "none":
        ret = {"good": ["tuple", [["tuple", [lit(1)]], ["dict", []]]],
               "kw": ["tuple", [["tuple", [lit(1)]], ["dict", [[lit("k"), lit(2)]]]]],
               "notuple": lit(5), "len3": ["tuple", [lit(1), lit(2), lit(3)]],
               "firstbad": ["tuple", [lit(1), ["dict", []]]],
               "secondbad": ["tuple", [["tuple", []], lit(1)]], "raise": NONE}[ng]
        b = [["log", "__getnewargs_ex__"]]
        b.append(["raise", call(name("ValueError"), lit("g"))] if ng == "raise" else ["ret", ret])
        body.append(g.method("__getnewargs_ex__", "A.__getnewargs_ex__", ["s"], b))
    na = r.choice(["none", "none", "good", "bad"])
    if na != "none":
        body.append(simple_method(g, "__getnewargs__", "A.__getnewargs__", ["s"],
                                  ["tuple", [lit(2)]] if na == "good" else lit(3)))
    gs = r.choice(["none", "none", "none", "value", "falsy", "raise", "deleted"])
    if gs in ("value", "falsy"):
        body.append(simple_method(g, "__getstate__", "A.__getstate__", ["s"],
                                  lit("st") if gs == "value" else lit(0)))
    elif gs == "raise":
        body.append(g.method("__getstate__", "A.__getstate__", ["s"],
                             [["raise", call(name(r.choice(["ValueError", "AttributeError"])), lit("s"))]]))
    rd = r.choice(["none", "none", "none", "override", "raise"])
    if rd == "override":
        body.append(simple_method(g, "__reduce__", "A.__reduce__", ["s"], lit("rd")))
    elif rd == "raise":
        body.append(g.method("__reduce__", "A.__reduce__", ["s"],
                             [["raise", call(name("ValueError"), lit("r"))]]))
    sn = r.choice(["none", "none", "none", "none", "list", "nonev", "bad", "nonstr"])
    if sn != "none":
        body.append(["assign", "__slotnames__",
                     {"list": ["list", [lit("a"), lit("zz")]], "nonev": NONE, "bad": lit(1),
                      "nonstr": ["list", [lit(1)]]}[sn]])
    base = r.choice([[], [], ["int"], ["str"], ["list"], ["tuple"]])
    if slots is not None and slots != ["tuple", []] and base in (["int"], ["tuple"]):
        slots = None
        body = [b for b in body if not (b[0] == "assign" and b[1] == "__slots__")]
    g.main.append(["expr", lit(0)])
    cls(g, "A", base, body)
    g.main.append(["assign", "a", call(name("A"))])
    g.probes(["setattr", name("a"), "a", lit(1)])
    g.probes(["setattr", name("a"), "x", lit(2)])
    for p in (0, 1, 2, 3, -1):
        g.probe(call(attr(name("a"), "__reduce_ex__"), lit(p)))
    g.probe(call(attr(name("a"), "__reduce__")))
    g.probe(call(attr(name("a"), "__getstate__")))
    g.probe(call(attr(name("object"), "__getstate__"), name("a")))
    g.probe(call(attr(name("object"), "__reduce_ex__"), name("a"), lit(2)))
    g.probe(call(attr(name("object"), "__reduce__"), name("a")))
    g.probe(call(attr(name("a"), "__reduce_ex__"), lit("s")))
    g.probe(call(attr(name("a"), "__reduce_ex__"), lit(["bigint", str(2**40)])))
    g.probe(["in", lit("__slotnames__"), attr(name("A"), "__dict__")])
    g.probe(["sub", attr(name("A"), "__dict__"), lit("__slotnames__")])
    for v in [lit(1), lit("s"), lit(True), ["tuple", [lit(1)]], ["list", [lit(1)]], NONE,
              name("NotImplemented"), name("Ellipsis"), lit(["bigint", str(2**64)])]:
        g.probe(call(attr(v, "__reduce_ex__"), lit(2)))
        g.probe(call(attr(v, "__reduce_ex__"), lit(0)))
        g.probe(call(attr(v, "__getstate__")))
    g.probe(call(attr(name("int"), "__getnewargs__"), lit(5)))
    g.probe(call(attr(lit("s"), "__getnewargs__")))
    g.probe(call(attr(["tuple", [lit(1)]], "__getnewargs__")))
    # A getter that changes __slotnames__ while it is walked.
    cls(g, "G", (), [["assign", "__slots__", ["tuple", [lit("p"), lit("q")]]],
                     g.method("__getattribute__", "G.__getattribute__", ["s", "n"],
                              [["if", ["cmp", "==", name("n"), lit("p")],
                                [["expr", call(attr(attr(name("G"), "__slotnames__"), "append"), lit("z"))]],
                                []],
                               ["ret", call(attr(name("object"), "__getattribute__"), name("s"), name("n"))]])])
    g.main.append(["assign", "gg", call(name("G"))])
    g.probes(["setattr", name("G"), "__slotnames__", ["list", [lit("p"), lit("q")]]])
    g.probe(call(attr(name("object"), "__getstate__"), name("gg")))


def fam_attrs(g):
    """The attributes of functions, classes and C callables: the annotation getters write to what
    they read from, and a callable __annotate__ can return anything or raise."""
    r = g.rng
    ret = r.choice([["dict", [[lit("x"), lit(1)]]], ["dict", []], lit(5), NONE])
    ann = [["log", "annotate"]]
    if r.random() < 0.25:
        ann.append(["raise", call(name("ValueError"), lit("a"))])
    ann.append(["ret", ret])
    g.main.append(["def", "annf", "annf", {"pos": ["fmt"], "posonly": 0, "kwonly": [], "varargs": None,
                                           "varkw": None, "defaults": [], "kwdefaults": []}, g.code(ann)])
    g.main.append(["def", "f", "f", {"pos": ["a"], "posonly": 0, "kwonly": [], "varargs": None,
                                     "varkw": None, "defaults": [], "kwdefaults": []},
                   g.code([["ret", name("a")]])])
    cls(g, "A", (), [g.method("m", "A.m", ["s"], [["ret", lit(1)]])])
    if r.random() < 0.5:
        cls(g, "B", ["A"], None)
    else:
        cls(g, "B", ["A"], [["assign", "__annotations__", ["dict", [[lit("y"), lit(2)]]]]])
    keys = ["__annotate_func__", "__annotations_cache__", "__annotations__", "__annotate__"]

    def show():
        for k in keys:
            g.probe(["in", lit(k), attr(name("B"), "__dict__")])

    show()
    g.probe(attr(name("B"), "__annotate__"))
    show()
    g.probe(attr(name("B"), "__annotations__"))
    show()
    g.probes(["setattr", name("B"), "__annotate__", r.choice([name("annf"), NONE, lit(1)])])
    show()
    g.probe(attr(name("B"), "__annotations__"))
    g.probe(attr(name("B"), "__annotations__"))
    show()
    g.probes(["setattr", name("B"), "__annotations__", ["dict", [[lit("z"), lit(3)]]]])
    show()
    g.probe(attr(name("B"), "__annotations__"))
    g.probes(["delattr", name("B"), "__annotations__"])
    show()
    g.probes(["delattr", name("B"), "__annotations__"])
    g.probes(["delattr", name("B"), "__annotate__"])
    g.probes(["setattr", name("int"), "__annotate__", NONE])
    g.probes(["setattr", name("int"), "__annotations__", ["dict", []]])
    g.probes(["setattr", name("B"), "__type_params__", ["tuple", [lit(1)]]])
    g.probes(["setattr", name("int"), "__type_params__", ["tuple", []]])
    for e in [attr(name("B"), "__type_params__"), attr(name("A"), "__type_params__"),
              attr(name("type"), "__type_params__"), attr(name("int"), "__type_params__"),
              attr(name("int"), "__annotate__"), attr(name("int"), "__annotations__"),
              attr(call(name("A")), "__annotations__"), attr(name("f"), "__annotate__"),
              attr(name("f"), "__annotations__"), attr(name("f"), "__type_params__")]:
        g.probe(e)
    g.probes(["setattr", name("f"), "__annotate__", r.choice([name("annf"), NONE, lit(1)])])
    g.probe(attr(name("f"), "__annotations__"))
    g.probe(attr(name("f"), "__annotations__"))
    g.probes(["setattr", name("f"), "__annotations__", r.choice([NONE, lit(1), ["dict", [[lit("q"), lit(1)]]]])])
    g.probe(attr(name("f"), "__annotate__"))
    g.probe(attr(name("f"), "__annotations__"))
    g.probes(["delattr", name("f"), "__annotations__"])
    g.probe(attr(name("f"), "__annotations__"))
    g.probes(["delattr", name("f"), "__annotate__"])
    g.probes(["setattr", name("f"), "__type_params__", r.choice([["tuple", [lit(1)]], lit(1)])])
    g.probes(["delattr", name("f"), "__type_params__"])
    g.probe(attr(name("f"), "__type_params__"))
    # classmethod and staticmethod keep these in their own __dict__.
    for w in ["classmethod", "staticmethod"]:
        g.main.append(["assign", "c", call(name(w), name("f"))])
        g.probe(attr(name("c"), "__annotations__"))
        g.probe(attr(name("c"), "__dict__"))
        g.probe(attr(name("c"), "__annotate__"))
        g.probes(["setattr", name("c"), "__annotate__", lit(7)])
        g.probe(attr(name("c"), "__annotate__"))
        g.probes(["delattr", name("c"), "__annotations__"])
        g.probes(["delattr", name("c"), "__annotations__"])
        g.probe(attr(name("c"), "__annotations__"))
        g.main.append(["assign", "c", call(name(w), lit(1))])
        g.probe(attr(name("c"), "__annotations__"))
    # C callables.
    for v in [attr(["list", []], "append"), attr(name("A"), "__call__"), attr(lit(1), "__add__"),
              attr(name("dict"), "keys")]:
        for n in ["__name__", "__qualname__", "__objclass__", "__module__"]:
            g.probe(attr(v, n))
    for n in ["__name__", "__qualname__", "__module__"]:
        g.probe(attr(name("len"), n))
    g.probe(attr(attr(["list", []], "append"), "__self__"))
    g.probe(attr(attr(lit(1), "__add__"), "__self__"))
    g.probe(call(attr(["dict", [[lit(1), lit(2)]]], "keys")))
    g.probe(attr(call(attr(["dict", [[lit(1), lit(2)]]], "keys")), "mapping"))
    g.probe(call(name("repr"), attr(call(attr(["dict", [[lit(1), lit(2)]]], "keys")), "mapping")))


def fl(x):
    """A float literal, by its bits. NaN and the infinities have none in the source text."""
    return lit(["float", str(int.from_bytes(struct.pack("<d", x), "little"))])


def fam_float(g):
    """float against CPython's real values: arithmetic, exact comparison with ints, hashes, repr,
    identity in containers, and __float__ on its failure paths."""
    r = g.rng
    edge = [0.0, -0.0, 1.0, -1.0, 0.5, 1.5, 0.1, 2.5, -2.5, 1e308, 5e-324, 2.0**53, 2.0**53 + 2,
            1e22, 123.456]
    ints = [0, 1, -1, 2, True, 7, 2**53, 2**53 + 1, 2**64, -2**64, 10**308]

    def iv(n):
        return lit(n) if isinstance(n, bool) or abs(n) < 2**31 else lit(["bigint", str(n)])

    g.main.append(["assign", "nan", call(name("float"), lit("nan"))])
    g.main.append(["assign", "inf", call(name("float"), lit("inf"))])
    g.main.append(["assign", "ninf", call(name("float"), lit("-inf"))])
    vals = [fl(x) for x in edge] + [name("nan"), name("inf"), name("ninf")]
    nums = vals + [iv(n) for n in ints]
    for _ in range(r.randrange(14, 26)):
        a, b = r.choice(nums), r.choice(nums)
        g.probe(["bin", r.choice(["+", "-", "*", "/", "//", "%"]), a, b])
        g.probe(["cmp", r.choice(CMP), a, b])
        g.probe(call(name("divmod"), a, b))
    for x in r.sample(edge, 6):
        g.probe(["un", "-", fl(x)])
        g.probe(["un", "+", fl(x)])
        g.probe(call(name("abs"), fl(x)))
        g.probe(call(name("bool"), fl(x)))
        g.probe(call(name("repr"), fl(x)))
        g.probe(call(name("str"), fl(x)))
        g.probe(call(name("int"), fl(x)))
        g.probe(call(name("float"), fl(x)))
        g.probe(["cmp", "==", call(name("hash"), fl(x)), lit(["bigint", str(hash(x))])])
        g.probe(call(attr(fl(x), "__float__")))
        g.probe(call(attr(fl(x), "__int__")))
        g.probe(call(attr(fl(x), "__repr__")))
    for n in ints:
        g.probe(call(name("float"), iv(n)))
        g.probe(["bin", "/", iv(n), lit(3)])
        g.probe(["bin", "/", lit(1), iv(n)])
        g.probe(["bin", "/", iv(n), iv(n)])
        g.probe(call(attr(iv(n), "__float__")))
    for e in [["bin", "/", lit(0), lit(-1)], ["bin", "/", lit(["bigint", str(10**400)]), lit(1)],
              ["bin", "/", lit(1), lit(["bigint", str(10**400)])],
              ["bin", "/", lit(-1), lit(["bigint", str(10**400)])],
              call(name("float"), lit(["bigint", str(10**400)])),
              ["bin", "+", fl(1.0), lit(["bigint", str(10**400)])]]:
        g.probe(e)
    # pow, where the true value is a double, so the C library has only one answer to give.
    for base, exps in [(2.0, [-3, -1, 0, 1, 2, 10, 1023, 1024, -1074, -1075]), (0.5, [-2, 2, 3]),
                       (1.5, [0, 1, 2, 3]), (-2.0, [2, 3, -1]), (1.0, [5, -5, 0.5]),
                       (0.0, [0, 1, -1, 2.0]), (-0.0, [1, 3, -1, 2])]:
        for e in exps:
            g.probe(["bin", "**", fl(base), fl(float(e)) if isinstance(e, float) else lit(e)])
    for e in [["bin", "**", name("inf"), lit(2)], ["bin", "**", name("nan"), lit(0)],
              ["bin", "**", name("nan"), lit(1)], ["bin", "**", lit(2), lit(-1)],
              ["bin", "**", lit(-2), lit(-3)], ["bin", "**", lit(0), lit(-1)],
              call(name("pow"), fl(2.0), lit(2), lit(3)), call(name("pow"), lit(2), fl(2.0))]:
        g.probe(e)
    for t in ["1.5", " 2.5 ", "1e3", "-0.0", "nan", "-inf", "1_000.5", "", "x", "1e400", "0X10", "١"]:
        g.probe(call(name("float"), lit(t)))
    for x in r.sample(edge, 4) + [float("nan"), float("inf")]:
        v = fl(x) if x == x and abs(x) != float("inf") else call(name("float"), lit(repr(x)))
        for n in ["is_integer", "__trunc__", "__floor__", "__ceil__", "conjugate", "__getnewargs__",
                  "as_integer_ratio", "__round__"]:
            g.probe(call(attr(v, n)))
        # Compared with the real text: printed, it would look like an address to the runner.
        g.probe(["cmp", "==", call(attr(v, "hex")), lit(x.hex())])
        g.probe(attr(v, "real"))
        g.probe(attr(v, "imag"))
        g.probe(call(attr(v, "__round__"), lit(1)))
        g.probe(call(attr(v, "__round__"), lit(-1)))
        g.probe(call(attr(v, "__round__"), NONE))
    for t in ["0x1p0", "0x1.8p1", "-0x0p0", "inf", "nan", "x", ""]:
        g.probe(call(attr(name("float"), "fromhex"), lit(t)))
    g.probe(call(attr(name("float"), "fromhex"), lit(1)))
    # Identity: a NaN object equals itself only through the shortcut.
    for e in [["cmp", "==", name("nan"), name("nan")], ["cmp", "!=", name("nan"), name("nan")],
              ["is", name("nan"), name("nan")],
              ["cmp", "==", ["list", [name("nan")]], ["list", [name("nan")]]],
              ["cmp", "==", ["tuple", [name("nan")]], ["tuple", [name("nan")]]],
              ["cmp", "==", ["list", [call(name("float"), lit("nan"))]],
               ["list", [call(name("float"), lit("nan"))]]],
              ["in", name("nan"), ["list", [name("nan")]]],
              ["in", call(name("float"), lit("nan")), ["list", [name("nan")]]],
              ["in", name("nan"), ["dict", [[name("nan"), lit(1)]]]],
              ["in", call(name("float"), lit("nan")), ["dict", [[name("nan"), lit(1)]]]],
              ["sub", ["dict", [[name("nan"), lit(1)]]], name("nan")],
              ["is", call(name("float"), name("inf")), name("inf")],
              ["is", ["un", "+", name("inf")], name("inf")],
              ["is", ["un", "-", name("inf")], name("inf")],
              ["dict", [[fl(1.0), lit("a")], [lit(1), lit("b")]]],
              ["dict", [[lit(1), lit("a")], [fl(1.0), lit("b")], [lit(True), lit("c")]]],
              ["in", fl(0.0), ["dict", [[fl(-0.0), lit(1)]]]],
              ["sub", ["dict", [[lit(2), lit("i")]]], fl(2.0)],
              ["in", fl(2.5), ["list", [fl(2.5)]]]]:
        g.probe(e)
    # __float__ and __index__ on their failure paths, and a subclass.
    cls(g, "F", ["float"], [g.method("__repr__", "F.__repr__", ["s"], [["ret", lit("F!")]])])
    ret = r.choice([fl(2.5), call(name("F"), fl(2.5)), lit(1), lit("s"), NONE])
    b = [["log", "C.__float__"]]
    if r.random() < 0.2:
        b.append(["raise", call(name("ValueError"), lit("c"))])
    b.append(["ret", ret])
    cls(g, "C", (), [g.method("__float__", "C.__float__", ["s"], b)])
    cls(g, "D", (), [g.method("__index__", "D.__index__", ["s"], [["log", "D.__index__"], ["ret", lit(3)]])])
    for e in [call(name("float"), call(name("C"))), call(name("float"), call(name("D"))),
              call(name("F"), call(name("C"))), call(name("F"), lit("1.5")), call(name("F")),
              call(name("F"), fl(1.5)), call(name("repr"), call(name("F"), fl(1.5))),
              call(name("str"), call(name("F"), fl(1.5))),
              ["bin", "+", call(name("F"), fl(1.5)), lit(1)], ["bin", "+", lit(1), call(name("F"), fl(1.5))],
              ["un", "+", call(name("F"), fl(1.5))], ["un", "-", call(name("F"), fl(1.5))],
              ["cmp", "==", call(name("F"), fl(1.5)), fl(1.5)],
              call(attr(call(name("F"), fl(1.5)), "__float__")),
              call(name("float"), call(name("F"), fl(1.5))), call(name("float"), NONE),
              call(name("float"), ["list", []]), call(name("float"), lit("a"), lit("b")),
              call(name("float"), kw=[("x", lit(1))]), call(name("int"), name("nan")),
              call(name("int"), name("inf")), ["bin", "*", ["list", [lit(1)]], fl(2.0)],
              ["sub", ["list", [lit(1)]], fl(0.0)]]:
        g.probe(e)


def fam_funcattrs(g):
    """The attributes of a function keep the objects assigned to them: subclasses of str, tuple and
    dict stay themselves, __kwdefaults__ is read at each call, and a key of the same hash can run
    __eq__ from inside the call. That __eq__ raises or returns True, because a False lets the
    probe sequence meet the same entry again, which depends on the hash seed."""
    r = g.rng
    cls(g, "S", ["str"], None)
    cls(g, "T", ["tuple"], None)
    cls(g, "D", ["dict"], None)
    fail = r.choice(["ok", "raise"])
    eqb = [["log", "K.__eq__"]]
    if fail == "raise":
        eqb.append(["raise", call(name("ValueError"), lit("k"))])
    eqb.append(["ret", lit(True)])
    cls(g, "K", (), [g.method("__hash__", "K.__hash__", ["s"], [["ret", call(name("hash"), lit("k"))]]),
                     g.method("__eq__", "K.__eq__", ["s", "o"], eqb)])
    params = {"pos": ["a", "b"], "posonly": 0, "kwonly": ["k", "m"], "varargs": None, "varkw": None,
              "defaults": [lit(5)] if r.random() < 0.5 else [],
              "kwdefaults": [["m", lit(8)]] if r.random() < 0.5 else []}
    g.main.append(["def", "f", "f", params,
                   g.code([["ret", ["tuple", [name(x) for x in ["a", "b", "k", "m"]]]]])])
    F = name("f")

    def shows():
        for a in ["__name__", "__qualname__", "__doc__", "__module__", "__defaults__",
                  "__kwdefaults__", "__type_params__"]:
            g.probe(attr(F, a))

    g.main.append(["assign", "sn", call(name("S"), lit("sn"))])
    g.main.append(["assign", "tp", call(name("T"), ["tuple", [lit(1), lit(2)]])])
    for a, good, bad in [("__name__", name("sn"), lit(1)), ("__qualname__", name("sn"), NONE),
                         ("__defaults__", name("tp"), ["list", []]),
                         ("__type_params__", name("tp"), ["list", []]),
                         ("__doc__", name("sn"), None), ("__module__", name("tp"), None)]:
        if bad is not None:
            g.probes(["setattr", F, a, bad])
        g.probes(["setattr", F, a, good])
        g.probe(["is", attr(F, a), good])
        g.probe(call(name("type"), attr(F, a)))
        if r.random() < 0.5:
            g.probes(["delattr", F, a])
            g.probe(attr(F, a))
    shows()
    d = r.choice([["dict", [[lit("k"), lit(1)]]], ["dict", []],
                  call(name("D"), ["dict", [[lit("k"), lit(2)]]]),
                  ["dict", [[lit(1), lit(2)], [lit("k"), lit(3)]]],
                  ["dict", [[call(name("K")), lit(4)]]],
                  ["dict", [[call(name("K")), lit(4)]]] if fail == "raise" else
                  ["dict", [[call(name("K")), lit(4)], [lit("k"), lit(5)]]]])
    g.main.append(["assign", "d", d])
    g.probes(["setattr", F, "__kwdefaults__", name("d")])
    g.probe(["is", attr(F, "__kwdefaults__"), name("d")])
    g.probe(["is", attr(F, "__kwdefaults__"), attr(F, "__kwdefaults__")])
    g.probe(call(F, lit(1), lit(2)))
    g.probe(call(F, lit(1), lit(2), kw=[("k", lit(0)), ("m", lit(0))]))
    g.probe(call(F, lit(1), lit(2), kw=[("m", lit(0))]))
    g.probe(call(F, lit(1), lit(2), lit(3), lit(4)))
    g.probe(call(F))
    g.probes(["setitem", name("d"), lit("m"), lit(7)])
    g.probe(call(F, lit(1), lit(2), kw=[("k", lit(0))]))
    g.probes(["delitem", name("d"), lit("m")] if r.random() < 0.5 else
             ["setattr", F, "__kwdefaults__", r.choice([NONE, lit(1), ["list", []]])])
    g.probe(call(F, lit(1), lit(2), kw=[("k", lit(0))]))
    if r.random() < 0.5:
        g.probes(["delattr", F, "__kwdefaults__"])
        g.probe(attr(F, "__kwdefaults__"))
        g.probe(call(F, lit(1), lit(2)))
    g.probes(["setattr", F, "__defaults__", ["tuple", []]])
    g.probe(attr(F, "__defaults__"))
    g.probes(["setattr", F, "__defaults__", NONE])
    g.probe(attr(F, "__defaults__"))
    g.probes(["delattr", F, "__type_params__"])
    g.probes(["setattr", F, "__name__", ["list", []]])
    g.probes(["delattr", F, "__name__"])
    g.probes(["delattr", F, "__qualname__"])
    g.probe(call(name("repr"), F))
    shows()


def fam_repin(g):
    """What 3.15 changed in the data model: frozendict as a class namespace and a proxy operand, the
    one __dict__ and __weakref__ getset shared by all classes, __slots__ on variable-size bases,
    the layout checks of __class__ and __bases__ assignment, deleting special attributes, private
    names in method.__reduce__, ImportError.__repr__ and the repr of a group with replaced args."""
    r = g.rng
    which = r.randrange(10)
    fd = name("frozendict")
    cls(g, "A", (), [g.method("m", "A.m", ["s"], [["ret", lit(1)]])])
    # The source does not mangle, so the private method goes in by hand.
    g.main.append(["def", "pp", "pp", {"pos": ["s"], "posonly": 0, "kwonly": [], "varargs": None,
                                       "varkw": None, "defaults": [], "kwdefaults": []},
                   g.code([["ret", lit(2)]])])
    g.main.append(["setattr", name("pp"), "__name__", lit("__p")])
    g.main.append(["setattr", name("A"), "_A__p", name("pp")])
    cls(g, "B", ["A"], None)
    g.main.append(["assign", "a", call(name("A"))])
    g.main.append(["assign", "b", call(name("B"))])
    if which == 0:
        args = [["dict", [[lit("x"), lit(1)]]], ["dict", []], ["dict", [[lit("__slots__"), ["tuple", [lit("q")]]]]]]
        g.main.append(["assign", "fd", call(fd, r.choice(args))])
        g.probe(name("fd"))
        g.probe(call(name("repr"), name("fd")))
        g.probe(call(name("type"), lit("T"), ["tuple", []], name("fd")))
        g.probe(attr(call(name("type"), lit("T"), ["tuple", []], name("fd")), "x"))
        g.probe(call(name("type"), lit("T"), ["tuple", []], lit(1)))
        g.probe(call(name("type"), lit("T"), ["tuple", []], name("a")))
        g.probe(call(fd, lit(1), lit(2)))
        g.probe(call(fd, kw=[("k", lit(1))]))
        g.main.append(["assign", "P", call(name("type"), attr(name("A"), "__dict__"))])
        g.main.append(["assign", "p", call(name("P"), ["dict", [[lit("x"), lit(1)]]])])
        for w in [name("fd"), call(fd, ["dict", [[lit("x"), lit(1)]]]), ["dict", [[lit("x"), lit(1)]]],
                  call(name("P"), ["dict", [[lit("x"), lit(1)]]]), lit(1), name("a")]:
            for op in ["==", "!=", "<", ">="]:
                g.probe(["cmp", op, name("p"), w])
                g.probe(["cmp", op, w, name("p")])
    elif which == 1:
        # An empty dict copies without running anything, whatever its type overrides.
        ga = [["log", "O.__getattribute__"]]
        ga.append(["raise", call(name("AttributeError"), lit("ga"))] if r.random() < 0.5 else
                  ["ret", call(attr(name("object"), "__getattribute__"), name("s"), name("n"))])
        cls(g, "O", ["dict"], [g.method("__iter__", "O.__iter__", ["s"], [["log", "O.__iter__"],
                                                                         ["ret", call(name("iter"), ["list", []])]]),
                               g.method("__getattribute__", "O.__getattribute__", ["s", "n"], ga)])
        for x in [call(name("O")), call(name("O"), ["dict", [[lit("k"), lit(1)]]])]:
            for y in [call(name("O")), call(name("O"), ["dict", [[lit("j"), lit(2)]]]), ["dict", []]]:
                g.probe(["bin", "|", x, y])
                g.probe(["bin", "|", y, x])
        sink = [["log", "E.__eq__"]]
        if r.random() < 0.3:
            sink.append(["raise", call(name("ValueError"), lit("e"))])
        sink.append(["ret", r.choice([lit(True), lit(False), lit(5)])])
        body = [g.method("__eq__", "E.__eq__", ["s", "o"], sink),
                g.method("__ne__", "E.__ne__", ["s", "o"], [["log", "E.__ne__"], ["ret", lit(0)]]),
                ["assign", "__hash__", NONE]]
        cls(g, "E", (), body)
        cls(g, "D", ["dict"], None)
        g.main.append(["assign", "P", call(name("type"), attr(name("A"), "__dict__"))])
        g.main.append(["assign", "d", ["dict", [[lit("x"), lit(1)]]]])
        for m in [name("d"), call(name("D"), name("d")), attr(name("A"), "__dict__")]:
            g.main.append(["assign", "p", call(name("P"), m)])
            for w in [call(name("E")), name("d"), call(name("D"), name("d")), name("p")]:
                g.probe(["cmp", "==", name("p"), w])
                g.probe(["cmp", "!=", name("p"), w])
                g.probe(["cmp", "<", name("p"), w])
    elif which == 2:
        cls(g, "S1", (), [["assign", "__slots__", ["tuple", []]]])
        cls(g, "W", (), [["assign", "__slots__", ["tuple", [lit("__weakref__")]]]])
        cls(g, "DD", (), [["assign", "__slots__", ["tuple", [lit("__dict__")]]]])
        cls(g, "U", (), [["assign", "__dict__", lit(5)]])
        
        for k in ["__dict__", "__weakref__"]:
            d = ["sub", attr(name("A"), "__dict__"), lit(k)]
            g.probe(d)
            g.probe(call(name("repr"), d))
            g.probe(["is", d, ["sub", attr(name("W") if k == "__weakref__" else name("DD"), "__dict__"), lit(k)]])
            for a in ["__name__", "__qualname__", "__objclass__"]:
                g.probe(attr(d, a))
            g.probe(call(attr(d, "__reduce__")))
            for o in [lit(1), name("a"), call(name("S1")), attr(name("A"), "m"), name("A"), call(name("ValueError"), lit(1)),
                      call(name("DD")), call(name("W"))]:
                # tp_subclasses holds a weak reference to every class; none are modelled.
                if not (k == "__weakref__" and o == name("A")):
                    g.probe(call(attr(d, "__get__"), o))
                g.probe(call(attr(d, "__set__"), o, ["dict", []]))
                g.probe(call(attr(d, "__set__"), o, lit(1)))
                g.probe(call(attr(d, "__delete__"), o))
        g.probe(attr(name("U"), "__dict__"))
        g.probe(["sub", attr(name("U"), "__dict__"), lit("__dict__")])
        g.probe(attr(call(name("U")), "__dict__"))
        g.probe(call(name("list"), attr(name("A"), "__dict__")))
        g.probe(call(name("list"), attr(name("DD"), "__dict__")))
        g.probe(call(name("list"), attr(name("W"), "__dict__")))
    elif which == 3:
        base = r.choice(["tuple", "int", "str", "bytes", "list", "dict", "float", "type", "ValueError", "object"])
        slots = r.choice([["a"], ["a", "b"], ["__dict__"], ["__weakref__"], ["a", "__dict__", "__weakref__"],
                          ["__dict__", "__dict__"], [], ["1x"], ["a", "a"], [1]])
        src = call(name("type"), lit("T"), ["tuple", [name(base)]],
                   ["dict", [[lit("__slots__"), ["tuple", [lit(x) for x in slots]]]]])
        g.probe(src)
        g.probe(attr(src, "__basicsize__"))
        g.probe(attr(src, "__itemsize__"))
        g.probe(attr(src, "__dictoffset__"))
        g.probe(attr(src, "__weakrefoffset__"))
        g.probe(call(name("list"), attr(src, "__dict__")))
        if base == "tuple":
            g.main.append(["assign", "T", src] if all(isinstance(x, str) and x.isidentifier() for x in slots)
                          and len(set(slots)) == len(slots) else ["assign", "T", name("tuple")])
            g.main.append(["assign", "t", call(name("T"), ["tuple", [lit(1), lit(2)]])])
            g.probe(name("t"))
            g.probe(call(name("len"), name("t")))
            g.probes(["setattr", name("t"), "a", lit(9)])
            g.probe(attr(name("t"), "a"))
            g.probe(attr(name("t"), "__dict__"))
            g.probe(attr(name("t"), "__weakref__"))
            g.probes(["delattr", name("t"), "a"])
            g.probe(attr(name("t"), "a"))
    elif which == 4:
        slots = [[], ["a"], ["b"], ["__dict__"], ["__weakref__"], ["__dict__", "__weakref__"], None]
        names = []
        bases = ["object", "A", "ValueError", "list", "int", "dict"]
        for i in range(5):
            s = r.choice(slots)
            b = r.choice(bases)
            ns = [] if s is None else [[lit("__slots__"), ["tuple", [lit(x) for x in s]]]]
            n = f"C{i}"
            g.main.append(["assign", n, call(name("type"), lit(n), ["tuple", [name(b)]], ["dict", ns])] if b != "int" or not s
                          else ["assign", n, call(name("type"), lit(n), ["tuple", [name("object")]], ["dict", []])])
            names.append(n)
        # A failure below a grandchild has to undo the MRO of the whole hierarchy.
        g.main.append(["assign", "Z1", call(name("type"), lit("Z1"), ["tuple", [name("A")]], ["dict", []])])
        g.main.append(["assign", "Z2", call(name("type"), lit("Z2"), ["tuple", [name("Z1")]], ["dict", []])])
        g.main.append(["assign", "Y", call(name("type"), lit("Y"), ["tuple", []], ["dict", []])])
        g.main.append(["assign", "Z3", call(name("type"), lit("Z3"), ["tuple", [name("Y"), name("Z2")]], ["dict", []])])
        g.probes(["setattr", name("A"), "__bases__", ["tuple", [name("Y")]]])
        for n in ["A", "Z1", "Z2", "Z3"]:
            g.probe(attr(name(n), "__mro__"))
        for _ in range(10):
            x, y = r.choice(names), r.choice(names + ["object", "A", "ValueError", "list", "dict"])
            if r.random() < 0.5:
                g.probes(["setattr", name(x), "__bases__", ["tuple", [name(y)]]])
                g.probe(attr(name(x), "__bases__"))
                g.probe(attr(name(x), "__base__"))
            else:
                g.probes(["setattr", call(name(x)), "__class__", name(y)])
    elif which == 5:
        for t in ["int", "A", "type", "object"]:
            for a in ["__name__", "__qualname__", "__module__", "__doc__", "__bases__", "__abstractmethods__",
                      "__type_params__", "__annotations__", "__annotate__"]:
                g.probes(["delattr", name(t), a])
                g.probes(["setattr", name(t), a, r.choice([lit("x"), ["tuple", []], lit(1)])])
    elif which == 6:
        cls(g, "_", (), None)
        cls(g, "__U", (), None)
        for o, n in [("a", "_A__p"), ("b", "_A__p"), ("A", "_A__p"), ("a", "m")]:
            g.probe(call(attr(attr(name(o), n), "__reduce__")))
        g.main.append(["assign", "MT", call(name("type"), attr(name("a"), "m"))])
        for f, s in [(attr(name("A"), "m"), name("a")), (attr(name("A"), "_A__p"), name("b")),
                     (attr(name("A"), "_A__p"), name("A")), (attr(name("A"), "_A__p"), lit(1)),
                     (name("len"), lit("x")), (attr(name("A"), "_A__p"), call(name("_"))),
                     (attr(name("A"), "_A__p"), call(name("__U")))]:
            g.probe(call(attr(call(name("MT"), f, s), "__reduce__")))
        g.main.append(["assign", "fn", attr(name("A"), "m")])
        for nm in ["__x", "__x__", "__", "___", "_x", "__x_", "a.b", "__a.b"]:
            g.probes(["setattr", name("fn"), "__name__", lit(nm)])
            g.probe(call(attr(attr(name("a"), "m"), "__reduce__")))
    elif which == 7:
        kw = r.choice([[], [("name", lit("n"))], [("path", lit("p"))], [("name", NONE)], [("path", NONE), ("name", lit(1))]])
        cn = r.choice(["ImportError", "ModuleNotFoundError", "ImportCycleError"])
        for a in [[], [lit("m")], [lit(1), lit(2)]]:
            g.main.append(["assign", "e", call(name(cn), *a, kw=kw)])
            g.probe(call(name("repr"), name("e")))
            g.probe(call(name("str"), name("e")))
            g.probes(["setattr", name("e"), "name", r.choice([NONE, lit("z")])])
            g.probe(call(name("repr"), name("e")))
            g.probes(["setattr", name("e"), "args", ["tuple", []]])
            g.probe(call(name("repr"), name("e")))
        g.probe(attr(name("ImportCycleError"), "__mro__"))
        g.probe(call(name("issubclass"), name("ImportCycleError"), name("ImportError")))
    elif which == 8:
        ctor = name(r.choice(["classmethod", "staticmethod"]))
        fail = r.random() < 0.3
        cls(g, "G", (), [g.method("__call__", "G.__call__", ["s"], [["ret", lit(4)]]),
                         ["assign", "__doc__", lit("gdoc")]])
        cls(g, "H", [], [g.method("__getattr__", "H.__getattr__", ["s", "n"], [["log", "H.__getattr__"]] +
                                  ([["raise", call(name("ValueError"), lit("h"))]] if fail else []) +
                                  [["raise", call(name("AttributeError"), lit("n"))]]),
                         g.method("__call__", "H.__call__", ["s"], [["ret", lit(5)]])])
        cls(g, "CM", [ctor[1]], [g.method("__init__", "CM.__init__", ["s", "x"], [["log", "CM.__init__"]])])
        g.main.append(["assign", "f", attr(name("A"), "m")])
        g.main.append(["assign", "c", call(ctor, name("f"))])
        for e in [attr(name("c"), "__name__"), attr(name("c"), "__qualname__"), attr(name("c"), "__doc__"),
                  attr(name("c"), "__module__"), attr(name("c"), "__func__"), attr(name("c"), "__wrapped__"),
                  call(name("list"), attr(name("c"), "__dict__"))]:
            g.probe(e)
        g.probes(["setattr", name("f"), "__name__", lit("renamed")])
        g.probe(call(attr(name("c"), "__init__"), name("f")))
        g.probe(attr(name("c"), "__name__"))
        g.main.append(["assign", "other", call(name("G"))])
        g.probe(call(attr(name("c"), "__init__"), name("other")))
        g.probe(call(name("repr"), call(name("type"), attr(name("c"), "__func__"))))
        g.probe(attr(name("c"), "__doc__"))
        g.probe(call(ctor))
        g.probe(call(ctor, lit(1), lit(2)))
        g.probe(call(ctor, name("f"), kw=[("k", lit(1))]))
        g.probe(call(attr(ctor, "__new__"), ctor))
        g.probe(call(name("repr"), call(name("type"), call(attr(call(attr(ctor, "__new__"), ctor, name("f")), "__get__"), name("a")))))
        g.probe(call(attr(ctor, "__new__"), name("int"), name("f")))
        g.probe(call(attr(call(ctor, name("f")), "__init__")))
        g.probe(call(attr(call(ctor, name("f")), "__init__"), name("f"), kw=[("k", lit(1))]))
        g.probe(call(ctor, call(name("H"))))
        g.probe(call(name("CM"), name("f")))
        g.probe(attr(call(name("CM"), name("f")), "__func__"))
        g.probe(attr(call(name("CM"), name("f")), "__name__"))
        g.probe(attr(call(name("CM"), NONE), "__func__"))
        g.probe(call(ctor, NONE))
        cls(g, "K", (), [g.method("__new__", "K.__new__", ["c"], [["ret", call(attr(name("object"), "__new__"), name("c"))]]),
                         g.method("__init_subclass__", "K.__init_subclass__", ["c"], [["ret", NONE]]),
                         g.method("__class_getitem__", "K.__class_getitem__", ["c", "x"], [["ret", name("x")]])])
        for k in ["__new__", "__init_subclass__", "__class_getitem__"]:
            d = ["sub", attr(name("K"), "__dict__"), lit(k)]
            g.probe(attr(d, "__name__"))
            g.probe(attr(d, "__qualname__"))
            g.probe(call(name("list"), attr(d, "__dict__")))
    else:
        g.main.append(["assign", "e", call(name("ExceptionGroup"), lit("x"),
                                           r.choice([["list", [call(name("ValueError"), lit(1))]],
                                                     ["tuple", [call(name("ValueError"), lit(1))]]]))])
        g.probe(call(name("repr"), name("e")))
        for args in [["tuple", []], ["tuple", [lit(1)]], ["tuple", [lit(1), ["list", []]]],
                     ["tuple", [lit(1), ["tuple", []]]], ["tuple", [lit(1), lit(2), ["list", []]]]]:
            g.main.append(["assign", "e", call(name("ExceptionGroup"), lit("x"),
                                               ["tuple", [call(name("ValueError"), lit(1))]])])
            g.probes(["setattr", name("e"), "args", args])
            g.probe(call(name("repr"), name("e")))
        g.main.append(["assign", "e", call(name("ExceptionGroup"), lit("x"),
                                           ["list", [call(name("ValueError"), lit(1))]])])
        g.probe(call(attr(name("e"), "__init__"), *r.choice([[], [lit(1)], [lit(1), ["list", []]], [lit(1), lit(2), lit(3)]])))
        g.probe(call(name("repr"), name("e")))


def fam_methods(g):
    """Bound methods, builtin methods and method-wrappers: equality, the hash that must agree with
    it, rebinding, __reduce__, and the failure paths through __func__."""
    r = g.rng
    fail = r.choice(["ok", "ok", "hash", "eq"])
    body = []
    if fail == "hash":
        body.append(g.method("__hash__", "C.__hash__", ["s"],
                             [["log", "C.__hash__"], ["raise", call(name("ValueError"), lit("h"))]]))
    elif fail == "eq":
        body.append(g.method("__eq__", "C.__eq__", ["s", "o"],
                             [["log", "C.__eq__"], ["raise", call(name("KeyError"), lit("e"))]]))
        body.append(["assign", "__hash__", NONE] if r.random() < 0.5 else
                    g.method("__hash__", "C.__hash__", ["s"], [["ret", lit(7)]]))
    else:
        body.append(g.method("__eq__", "C.__eq__", ["s", "o"], [["log", "C.__eq__"], ["ret", lit(r.choice([True, False, 1, 0]))]]))
        body.append(g.method("__hash__", "C.__hash__", ["s"], [["ret", lit(7)]]))
    body.append(g.method("__call__", "C.__call__", ["s", "x"], [["log", "C.__call__"], ["ret", name("x")]]))
    cls(g, "C", (), body)
    cls(g, "A", (), [g.method("m", "A.m", ["s"], [["ret", lit(1)]]),
                     g.method("n", "A.n", ["s"], [["ret", lit(2)]])])
    g.main.append(["assign", "a", call(name("A"))])
    g.main.append(["assign", "b", call(name("A"))])
    g.main.append(["assign", "c", call(name("C"))])
    g.main.append(["assign", "d", call(name("C"))])
    mt = call(name("type"), attr(name("a"), "m"))
    g.main.append(["assign", "MT", mt])
    pairs = [(attr(name("a"), "m"), attr(name("a"), "m")), (attr(name("a"), "m"), attr(name("b"), "m")),
             (attr(name("a"), "m"), attr(name("a"), "n")),
             (call(name("MT"), name("c"), name("a")), call(name("MT"), name("c"), name("a"))),
             (call(name("MT"), name("c"), name("a")), call(name("MT"), name("d"), name("a"))),
             (call(name("MT"), name("c"), name("a")), call(name("MT"), name("d"), name("b"))),
             (attr(name("a"), "__str__"), attr(name("a"), "__str__")),
             (attr(name("a"), "__str__"), attr(name("b"), "__str__")),
             (attr(name("a"), "__str__"), attr(name("a"), "__repr__")),
             (attr(name("a"), "__sizeof__"), attr(name("a"), "__sizeof__")),
             (attr(name("a"), "__sizeof__"), attr(name("b"), "__sizeof__")),
             (attr(name("a"), "__sizeof__"), attr(name("a"), "__dir__")),
             (name("len"), name("len")), (name("len"), name("abs")),
             (attr(lit("x"), "format"), attr(lit("x"), "format")),
             (attr(name("a"), "m"), attr(name("a"), "__str__")),
             (attr(name("a"), "m"), lit(1)), (name("len"), lit(1)), (attr(name("a"), "__str__"), lit(1))]
    for x, y in pairs:
        g.probe(["cmp", "==", x, y])
        g.probe(["cmp", "!=", x, y])
        g.probe(["cmp", r.choice(["<", "<=", ">", ">="]), x, y])
        g.probe(["cmp", "==", call(name("hash"), x), call(name("hash"), y)])
    for e in [attr(name("a"), "m"), attr(name("a"), "__str__"), attr(name("a"), "__sizeof__"), name("len"),
              attr(lit("x"), "format"), attr(name("object"), "__str__"), attr(name("str"), "format"),
              attr(name("object"), "__sizeof__"), attr(name("type"), "__dict__"),
              ["sub", attr(name("A"), "__dict__"), lit("__dict__")],
              ["sub", attr(name("A"), "__dict__"), lit("__weakref__")],
              attr(name("dict"), "fromkeys"), ["sub", attr(name("dict"), "__dict__"), lit("fromkeys")],
              call(name("MT"), name("c"), name("a")), call(name("MT"), name("len"), name("a"))]:
        g.probe(call(attr(e, "__reduce__")))
    for meth in [attr(name("a"), "m"), call(name("MT"), name("c"), name("a"))]:
        g.probe(["is", call(attr(meth, "__get__"), name("b")), meth] if False else
                call(attr(meth, "__get__"), name("b")))
        g.probe(call(attr(meth, "__get__"), NONE, name("A")))
    g.probe(attr(call(name("MT"), name("c"), name("a")), "__doc__"))
    g.probe(attr(attr(name("a"), "m"), "__name__"))
    g.probe(attr(attr(name("a"), "m"), "__qualname__"))
    g.probe(attr(attr(name("a"), "m"), "nope"))
    g.probe(call(name("MT"), lit(1), name("a")))
    g.probe(call(name("MT"), name("c"), NONE))
    g.probe(call(name("MT"), name("c")))
    g.probe(call(name("MT"), name("c"), name("a"), name("a")))
    g.probe(call(name("MT"), name("c"), kw=[("x", lit(1))]))


def fam_exact(g):
    """The changed models of the typeobject.c fixes: abstract names sorted before joining,
    slot_tp_iter's None test before __getitem__, object.__eq__ by identity, slot_sq_length on an
    int subclass result, MRO conflicts and duplicates, and __class__ assignment comparing
    str-subclass slot names with their __eq__."""
    r = g.rng
    k = r.randrange(6)
    if k == 0:
        cls(g, "A", (), [simple_method(g, "m", "A.m", ["self"], lit(1))])
        items = r.choice([[lit("a"), lit(1)], [lit(1), lit("a")], [lit(1)], [lit(2), lit(1)],
                          [lit("b"), lit("a")], [lit("b"), lit("a"), lit("c")], [NONE, lit("x")],
                          [lit("x"), lit(1.5) if False else lit(True)], [lit("zz"), lit("Z"), lit("a")],
                          [lit(1), lit(1)], [lit(1), NONE], []])
        v = r.choice([["list", items], ["tuple", items]])
        g.probes(["setattr", name("A"), "__abstractmethods__", v])
        g.probe(call(name("A")))
        g.probe(call(name("A"), lit(1)))
    elif k == 1:
        # A __getitem__ descriptor whose __get__ logs and raises or returns.
        get_body = [["log", "G.__get__"]]
        if r.random() < 0.6:
            get_body.append(["raise", call(name(r.choice(["ValueError", "AttributeError", "KeyError"])), lit("g"))])
        else:
            get_body.append(["ret", name("o")])
        cls(g, "G", (), [g.method("__get__", "G.__get__", ["self", "o", "t"], get_body)])
        body = [["assign", "__getitem__", call(name("G"))]]
        it = r.randrange(3)
        if it == 0:
            body.append(["assign", "__iter__", NONE])
        elif it == 1:
            # __iter__ found but missing: a property raising AttributeError.
            body.append(g.method("_it", "It._it", ["self"], [["log", "It._it"], ["raise", call(name("AttributeError"), lit("i"))]]))
            body.append(["assign", "__iter__", call(name("property"), name("_it"))])
        cls(g, "It", (), body)
        g.probe(call(name("iter"), call(name("It"))))
        g.probe(call(name("list"), call(name("It"))))
        g.probe(["in", lit(1), call(name("It"))])
    elif k == 2:
        cls(g, "C", (), [simple_method(g, "__eq__", "C.__eq__", ["self", "o"], g.value())])
        g.main.append(["assign", "a", call(name("C"))])
        g.main.append(["assign", "b", call(name("C"))])
        for x, y in [("a", "a"), ("a", "b"), ("b", "a")]:
            g.probe(call(attr(name("object"), "__eq__"), name(x), name(y)))
            g.probe(call(attr(name("object"), "__ne__"), name(x), name(y)))
        for x, y in [(lit(5), lit(5)), (lit(1), lit(2)), (NONE, NONE), (lit("a"), lit("a")),
                     (lit("a"), lit("b")), (lit(True), lit(1)), (["tuple", []], ["tuple", []])]:
            g.probe(call(attr(name("object"), "__eq__"), x, y))
            g.probe(call(attr(name("object"), "__ne__"), x, y))
        g.probe(call(attr(name("object"), "__lt__"), name("a"), name("b")))
    elif k == 3:
        cls(g, "I", ["int"], None)
        v = r.choice([lit(["bigint", str(2**70)]), lit(-1), lit(3), lit(["bigint", str(2**63 - 1)]),
                      lit(["bigint", str(2**63)]), lit(0)])
        cls(g, "L", (), [simple_method(g, "__len__", "L.__len__", ["self"], call(name("I"), v))])
        g.probe(call(name("len"), call(name("L"))))
        g.probe(call(name("bool"), call(name("L"))))
        cls(g, "L2", (), [simple_method(g, "__len__", "L2.__len__", ["self"], v)])
        g.probe(call(name("len"), call(name("L2"))))
    elif k == 4:
        # MRO: the earliest-base rule, conflicts, duplicates.
        cls(g, "X", ())
        cls(g, "Y", ())
        cls(g, "B", ["X"])
        cls(g, "Cc", ["Y"])
        shapes = [["B", "Cc"], ["Cc", "B"], ["X", "B"], ["B", "X"], ["B", "B"], ["X", "Y", "X"],
                  ["B", "Cc", "X"], ["X", "Y"], ["Y", "X"]]
        bases = r.choice(shapes)
        cls(g, "D", bases)
        g.probe(attr(name("D"), "__mro__"))
        cls(g, "P", ["X", "Y"])
        cls(g, "Q", ["Y", "X"])
        cls(g, "Z", r.choice([["P", "Q"], ["Q", "P"], ["P", "Y"], ["X", "P"]]))
        g.probe(attr(name("Z"), "__mro__"))
    else:
        # __class__ assignment between classes whose __slots__ name is a str subclass.
        ret = r.choice([lit(True), lit(False), NOTIMPL, None])
        eq_body = [["log", "S.__eq__"]]
        if ret is None:
            eq_body.append(["raise", call(name("ValueError"), lit("eq"))])
        else:
            eq_body.append(["ret", ret])
        cls(g, "S", ["str"], [g.method("__eq__", "S.__eq__", ["self", "o"], eq_body),
                              ["assign", "__hash__", attr(name("str"), "__hash__")]])
        shared = r.random() < 0.3
        if shared:
            g.main.append(["assign", "sx", call(name("S"), lit("x"))])
            ax = bx = name("sx")
        else:
            ax = call(name("S"), lit("x"))
            bx = call(name("S"), lit(r.choice(["x", "y"])))
        cls(g, "A", (), [["assign", "__slots__", ["tuple", [ax]]]])
        cls(g, "Bb", (), [["assign", "__slots__", ["tuple", [bx]]]])
        g.probes(["assign", "oa", call(name("A"))])
        g.probes(["setattr", name("oa"), "__class__", name("Bb")])
        g.probe(call(name("type"), name("oa")))
        g.probes(["setattr", name("oa"), "__class__", name("A")])
        g.probe(call(name("type"), name("oa")))

def fam_exact3(g):
    """The re-reviewed typeobject.c rows: set_mro_error's names (non-str, NUL, str subclass,
    raising, AttributeError, long), find_best_base's first failure, object.__ne__'s slot,
    object.__format__ with a str subclass from __str__, the getstate slot-name message,
    __bases__ assignment layouts and __class__ assignment on a class."""
    r = g.rng
    k = r.randrange(6)
    if k == 0:
        cls(g, "S", ["str"], None)
        cls(g, "R", (), [g.method("__get__", "R.__get__", ["s", "o", "t"],
                                  [["log", "R.__get__"],
                                   ["raise", call(name(r.choice(["ValueError", "AttributeError", "KeyError"])), lit("nm"))]])])
        cls(g, "M", ["type"], [g.method("_nm", "M._nm", ["cls"],
                                        [["log", "M._nm"], ["ret", attr(name("cls"), "nm")]]),
                               ["assign", "__name__", call(name("property"), name("_nm"))]])
        def nmval():
            c = r.randrange(9)
            if c == 0:
                return lit(42)
            if c == 1:
                return lit("a\u0000b")
            if c == 2:
                return call(name("S"), lit("sub"))
            if c == 3:
                return call(name("R"))
            if c == 4:
                return lit(r.choice(["N", "Q", "x"]) * r.choice([300, 470, 480, 600, 999]))
            if c == 5:
                return lit("é" * r.choice([10, 100, 200]))
            if c == 6:
                return NONE
            return lit(r.choice(["X", "Y", "Zed", ""]))
        cls(g, "X", (), [["assign", "nm", nmval()]], kw=[["metaclass", name("M")]])
        cls(g, "Y", ["X"], [["assign", "nm", nmval()]])
        cls(g, "Z", (), [["assign", "nm", nmval()]], kw=[["metaclass", name("M")]])
        cls(g, "W", ["Z", "X"], [["assign", "nm", nmval()]])
        bases = r.choice([["X", "Y"], ["Y", "X", "X"], ["Z", "W", "X"], ["X", "W"], ["Z", "X", "W"],
                          ["W", "Z", "Y", "X"]])
        cls(g, "C", bases)
        g.probe(call(name("type"), lit("C2"), ["tuple", [name(b) for b in bases]], ["dict", []]))
    elif k == 1:
        cls(g, "P", ())
        cls(g, "I", ["int"])
        cls(g, "Sl", (), [["assign", "__slots__", ["tuple", [lit("a")]]]])
        pool = [name("int"), name("str"), name("bool"), name("list"), name("dict"), name("tuple"),
                name("P"), name("I"), name("Sl"), name("object"), call(name("object")), lit(1),
                name("type"), name("BaseException"), name("float")]
        for _ in range(r.randrange(2, 6)):
            bs = [r.choice(pool) for _ in range(r.randrange(1, 5))]
            g.probe(attr(call(name("type"), lit("C"), ["tuple", bs], ["dict", []]), "__base__"))
    elif k == 2:
        ret = r.choice([lit(True), lit(False), NOTIMPL, lit(0), lit(""), lit("s"), None])
        body = [["log", "E.__eq__"]]
        body.append(["raise", call(name("ValueError"), lit("eq"))] if ret is None else ["ret", ret])
        cls(g, "E", (), [g.method("__eq__", "E.__eq__", ["s", "o"], body)])
        cls(g, "F", ())
        cls(g, "G", ["E"], [["assign", "__eq__", attr(name("object"), "__eq__")]])
        for x, y in [("E", "F"), ("F", "E"), ("E", "E"), ("G", "E"), ("E", "G"), ("F", "F")]:
            g.probe(call(attr(name("object"), "__ne__"), call(name(x)), call(name(y))))
            g.probe(["cmp", "!=", call(name(x)), call(name(y))])
    elif k == 3:
        cls(g, "S", ["str"], None)
        ret = r.choice([call(name("S"), lit("a")), lit("b"), lit(1), call(name("S"), lit("")), None])
        body = [["log", "Z.__str__"]]
        body.append(["raise", call(name("ValueError"), lit("st"))] if ret is None else ["ret", ret])
        cls(g, "Z", (), [g.method("__str__", "Z.__str__", ["s"], body)])
        for spec in [lit(""), lit("x"), call(name("S"), lit(""))]:
            g.probe(call(attr(name("object"), "__format__"), call(name("Z")), spec))
        g.probe(call(name("format"), call(name("Z")), lit("")))
        g.probe(call(name("format"), call(name("Z"))))
        g.probe(call(name("str"), call(name("Z"))))
        g.probe(call(name("type"), call(attr(name("object"), "__format__"), call(name("Z")), lit(""))))
    elif k == 4:
        ln = r.choice(["L" * 250, "L" * 199, "é" * 120, "Lq"])
        cls(g, ln, ())
        cls(g, "A", (), [["assign", "__slots__", ["tuple", [lit("a"), lit("b")]]]])
        g.main.append(["assign", "a", call(name("A"))])
        g.probes(["setattr", name("a"), "a", lit(1)])
        g.probes(["setattr", name("A"), "__slotnames__",
                  ["list", r.choice([[lit("a"), call(name(ln))], [call(name(ln))], [lit("b"), lit("a")],
                                     [lit("zz"), lit("a")], [lit(5)]])]])
        g.probe(call(attr(name("a"), "__getstate__")))
        g.probe(call(attr(name("a"), "__reduce_ex__"), lit(2)))
    else:
        spec = {"B1": ((), None), "B2": ((), None), "SB": ((), ("z",)), "SB2": ((), ("z",)),
                "WD": ((), ("__weakref__",)), "DD": ((), ("__dict__",)), "LD": (("list",), None),
                "E0": ((), ())}
        for n, (bases, slots) in spec.items():
            body = []
            if slots is not None:
                body.append(["assign", "__slots__", ["tuple", [lit(x) for x in slots]]])
            cls(g, n, bases, body)
        cls(g, "D", [r.choice(list(spec))])
        pool = list(spec) + ["list", "object", "int"]
        for _ in range(r.randrange(2, 6)):
            nb = [name(r.choice(pool)) for _ in range(r.randrange(1, 3))]
            g.probes(["setattr", name("D"), "__bases__", ["tuple", nb]])
            g.probe(attr(name("D"), "__mro__"))
        cls(g, "MA", ["type"])
        cls(g, "MB", ["type"])
        cls(g, "MS", ["type"], [["assign", "__slots__", ["tuple", [lit("q")]]]])
        cls(g, "CC", (), None, kw=[["metaclass", name("MA")]])
        for _ in range(r.randrange(1, 4)):
            g.probes(["setattr", name("CC"), "__class__", name(r.choice(["MA", "MB", "MS", "type", "object", "D"]))])
            g.probe(call(name("type"), name("CC")))
            g.probe(attr(name("CC"), "__mro__"))


FAMILIES = [fam_calls, fam_property, fam_super, fam_mro, fam_class_stmt, fam_class_assign,
            fam_wrappers, fam_abstract, fam_type_attrs, fam_slot_updates, fam_descriptors,
            fam_iter_seq, fam_numbers, fam_list_extend, fam_repr, fam_descr_proto,
            fam_dict_update, fam_dict_lookup, fam_reduce, fam_attrs, fam_float, fam_methods,
            fam_funcattrs, fam_repin, fam_exact, fam_exact, fam_exact, fam_exact3, fam_exact3]


def gen_sized(rng):
    """PyType_FromMetaclass's layout (_align_up): a base of 16 + extra bytes and a subclass spec
    of a negative (extend), zero (inherit) or large enough positive basicsize."""
    extra = rng.choice([0, 1, 7, 8, 15, 16, 17, 31, 32, 33, 100, rng.randrange(0, 5000)])
    k = rng.randrange(3)
    if k == 0:
        spec = -rng.choice([1, 8, 15, 16, 17, 32, 33, 100, rng.randrange(1, 5000)])
    elif k == 1:
        spec = 0
    else:
        spec = 16 + extra + rng.choice([0, 1, 15, 16, rng.randrange(0, 1000)])
    return {"mod": "typeobj", "fn": "fromspec_sizes", "extra": extra, "spec": spec}


def gen_case(rng):
    if rng.random() < 0.03:
        return gen_sized(rng)
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
