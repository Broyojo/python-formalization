"""Differential test of Objects/exceptions.c: the Lean object model vs. the running CPython.

Usage: python3 difftest/typeobj_exc_diff.py [--cases N] [--seed S]

Each case is a "typeobj" scenario (see typeobj_diff.py) built from blocks that exercise one
family of exceptions: construction with edge arguments, str/repr, attributes and setters,
chaining, notes, __reduce__, ExceptionGroup construction errors, split/subgroup with type,
tuple and callable matchers over nested groups, derive overrides, and the C API through
_testcapi (Lean binds the same names to its model of those functions).

Probes stay away from two things the model leaves out on purpose:
 * __suppress_context__ = True on an exact MemoryError: the freelist would leak it into the
   next scenario (bug typeobj-exc-memoryerror-freelist-state).
 * the keyword "Did you mean" suggestion of getargs.c: the bad keyword is never close to a
   good one.
"""

import re
import warnings

import _testcapi

import common
import typeobj_diff as T
from typeobj_diff import NONE, attr, call, canon, lit, name

warnings.simplefilter("ignore")

ADDR = re.compile(r"0x[0-9a-f]{6,}")

SIMPLE = ["BaseException", "Exception", "TypeError", "ValueError", "KeyError", "LookupError",
          "IndexError", "ArithmeticError", "ZeroDivisionError", "OverflowError", "RuntimeError",
          "NotImplementedError", "RecursionError", "AssertionError", "BufferError", "EOFError",
          "ReferenceError", "SystemError", "Warning", "UserWarning", "DeprecationWarning",
          "GeneratorExit", "KeyboardInterrupt", "StopAsyncIteration", "UnicodeError",
          "StopIteration", "SystemExit", "NameError", "UnboundLocalError", "AttributeError",
          "ImportError", "ModuleNotFoundError", "OSError", "FileNotFoundError",
          "PermissionError", "BlockingIOError", "ConnectionError", "BrokenPipeError",
          "TimeoutError", "SyntaxError", "IndentationError", "TabError", "EnvironmentError",
          "IOError", "MemoryError"]
ALLATTRS = ["value", "code", "name", "obj", "path", "name_from", "msg", "errno", "strerror",
            "filename", "filename2", "text", "lineno", "offset", "end_lineno", "end_offset",
            "print_file_and_line", "_metadata", "encoding", "object", "start", "end", "reason",
            "characters_written", "message", "exceptions"]
ERRNOS = [1, 2, 3, 4, 10, 11, 13, 17, 20, 21, 32, 103, 104, 108, 110, 111, 114, 115, 5, 0, -1, 999]
TUPLE = lambda *xs: ["tuple", list(xs)]
LIST = lambda *xs: ["list", list(xs)]


def big(v):
    return lit(["bigint", str(v)]) if abs(v) > 2 ** 52 else lit(v)


EDGE_INTS = [0, 1, -1, 2, 3, 4, 5, 7, 255, 2 ** 31, 2 ** 63 - 1, 2 ** 63, -2 ** 63, -2 ** 63 - 1,
             2 ** 64, -2 ** 64]
TEXT = ["", "s", "abc", "a/b/c", "/x", "x/", "/", "é", "€uro", "😀!", "a'b", 'a"b', "line\nnext"]


class X(T.G):
    def __init__(self, rng):
        super().__init__(rng)
        self.n = 0
        self.objs = []

    def fresh(self, base="v"):
        self.n += 1
        return f"{base}{self.n}"

    def st(self, *stmts):
        self.main.extend(stmts)

    def anyval(self):
        r = self.rng
        return r.choice([NONE, lit(True), lit(False), lit(0), lit(1), lit(-1), lit(7),
                         lit("s"), lit(""), TUPLE(), TUPLE(lit(1)), TUPLE(lit(1), lit("a")),
                         LIST(lit(1)), LIST(), big(2 ** 64)])

    def textv(self):
        return lit(self.rng.choice(TEXT))

    def intv(self):
        return big(self.rng.choice(EDGE_INTS))

    def bytesv(self):
        r = self.rng
        n = r.randrange(5)
        return call(name(r.choice(["_bytes", "_bytes", "_bytearray"])),
                    *[lit(r.choice([0, 1, 97, 127, 128, 255])) for _ in range(n)])

    def assign(self, var, e):
        self.probes(["assign", var, e])

    def fn(self, n, params, body, varargs=None, varkw=None):
        return ["def", n, n, {"pos": params, "posonly": 0, "kwonly": [], "varargs": varargs,
                              "varkw": varkw, "defaults": [], "kwdefaults": []},
                self.code(body)]

    def cls(self, n, bases, body):
        self.st(["class", n, [name(b) for b in bases], [], True,
                 self.code(body or [["assign", "zz", lit(1)]])])

    # Common probes.

    def probe_exc(self, v, attrs=()):
        r = self.rng
        self.probe(name(v))
        self.probe(call(name("str"), name(v)))
        self.probe(call(name("repr"), name(v)))
        self.probe(attr(name(v), "args"))
        for a in attrs:
            self.probe(attr(name(v), a))
        if r.random() < 0.5:
            self.probe(call(attr(name(v), "__reduce__")))
        if r.random() < 0.3:
            self.probe(attr(name(v), "__dict__"))
        if r.random() < 0.3:
            for a in ["__cause__", "__context__", "__suppress_context__", "__traceback__"]:
                self.probe(attr(name(v), a))

    def mutate(self, v, memoryerror=False, plain=True):
        r = self.rng
        o = name(v)
        k = r.randrange(17)
        if k == 12 and not plain:
            # A custom tp_getattro binds the method first, which changes the name in the
            # arity error (`E.add_note()` for `BaseException.add_note()`).
            k = 16
        if k == 0:
            x = r.choice([TUPLE(), TUPLE(lit(1), lit(2)), LIST(lit(1)), lit("ab"), lit(5), NONE,
                          ["dict", [[lit("k"), lit(1)]]]])
            self.probes(["setattr", o, "args", x])
        elif k == 1:
            self.probes(["delattr", o, r.choice(["args", "__cause__", "__context__", "__traceback__",
                                                 "__suppress_context__", "__dict__"])])
        elif k == 2 and not memoryerror:
            self.probes(["setattr", o, "__cause__",
                         r.choice([NONE, lit(1), call(name("ValueError"), lit("c")), name("ValueError")])])
        elif k == 3:
            self.probes(["setattr", o, "__context__",
                         r.choice([NONE, lit(1), call(name("KeyError"), lit("c")), name("KeyError")])])
        elif k == 4 and not memoryerror:
            self.probes(["setattr", o, "__suppress_context__", r.choice([lit(True), lit(False), lit(1), NONE])])
        elif k == 5:
            self.probes(["setattr", o, "__traceback__", r.choice([NONE, lit(1), lit("tb")])])
        elif k == 6:
            self.probe(call(attr(o, "with_traceback"), r.choice([NONE, lit(1)])))
        elif k == 7:
            self.probe(call(attr(o, "add_note"), r.choice([lit("n1"), lit(1), NONE, lit("")])))
            self.probe(attr(o, "__notes__"))
        elif k == 8:
            self.probes(["setattr", o, "__notes__", r.choice([LIST(), LIST(lit("a")), TUPLE(lit("a")), lit(1), lit("x")])])
            self.probe(call(attr(o, "add_note"), lit("n2")))
            self.probe(attr(o, "__notes__"))
        elif k == 9:
            self.probe(call(attr(o, "__setstate__"),
                            r.choice([NONE, lit(1), LIST(), ["dict", [[lit("a"), lit(1)]]],
                                      ["dict", [[lit(1), lit(1)]]],
                                      ["dict", [[lit("args"), TUPLE(lit(9))], [lit("b"), lit(2)]]]])))
            self.probe(attr(o, "__dict__"))
        elif k == 10:
            self.probes(["setattr", o, "__dict__", r.choice([["dict", []], lit(1), NONE])])
        elif k == 11:
            self.probes(["setattr", o, "q", lit(1)])
            self.probe(call(attr(o, "__reduce__")))
        elif k == 12:
            self.probe(call(attr(o, "__setstate__")))
            self.probe(call(attr(o, "__reduce__"), lit(1)))
            self.probe(call(attr(o, "with_traceback")))
            self.probe(call(attr(o, "add_note")))
        elif k == 13:
            a = r.choice(ALLATTRS)
            self.probes(["setattr", o, a, self.anyval()])
            self.probe(attr(o, a))
        elif k == 14:
            a = r.choice(ALLATTRS)
            self.probes(["delattr", o, a])
            self.probe(attr(o, a))
        elif k == 15:
            self.probes(["expr", call(attr(o, "__init__"), *[self.anyval() for _ in range(r.randrange(3))])])
        else:
            self.probe(call(name("isinstance"), o, name(r.choice(SIMPLE))))

    # Blocks.

    def block_generic(self):
        r = self.rng
        c = r.choice(SIMPLE)
        v = self.fresh("e")
        args = [self.anyval() for _ in range(r.choice([0, 1, 1, 2, 3]))]
        kw = []
        if r.random() < 0.12:
            kw.append([r.choice(["name", "path", "name_from", "obj", "zzq"]), self.anyval()])
        if r.random() < 0.03:
            kw.append(["zzr", lit(1)])
        self.assign(v, call(name(c), *args, kw=kw))
        self.probe_exc(v, r.sample(ALLATTRS, 4))
        for _ in range(r.randrange(4)):
            self.mutate(v, memoryerror=c == "MemoryError")
        self.probe_exc(v)
        if r.random() < 0.2:
            self.probe(call(attr(name(c), "__new__"), name(c), *args))
        if r.random() < 0.1:
            self.probe(attr(call(attr(name(c), "__new__"), name(c), *args), "args"))

    def block_subclass(self):
        r = self.rng
        base = r.choice(SIMPLE)
        k = self.fresh("K")
        body = []
        q = lambda n: f"{k}.{n}"
        if r.random() < 0.4:
            m = r.randrange(3)
            b = [["log", q("__init__")]]
            params = ["self", "a"] if m else ["self"]
            if m == 1:
                b.append(["expr", ["call", ["attr", ["super"], "__init__"], [name("a")], []]])
            if m == 2:
                b.append(["expr", call(attr(name(base), "__init__"), name("self"), name("a"), lit(2))])
            body.append(self.method("__init__", q("__init__"), params, b))
        if r.random() < 0.25:
            body.append(self.method("__str__", q("__str__"), ["self"],
                                    [["log", q("__str__")], ["ret", r.choice([lit("S"), lit(1)])]]))
        if r.random() < 0.25:
            body.append(self.method("__repr__", q("__repr__"), ["self"],
                                    [["log", q("__repr__")], ["ret", r.choice([lit("R"), lit(1)])]]))
        if r.random() < 0.2:
            body.append(self.method("__reduce__", q("__reduce__"), ["self"],
                                    [["ret", ["call", ["attr", ["super"], "__reduce__"], [], []]]]))
        if r.random() < 0.2:
            body.append(self.method("__getattr__", q("__getattr__"), ["self", "n"],
                                    [["log", q("__getattr__")], ["raise", call(name("AttributeError"), name("n"))]]))
        if r.random() < 0.2:
            body.append(self.method("__setattr__", q("__setattr__"), ["self", "n", "x"],
                                    [["log", q("__setattr__")],
                                     ["expr", call(attr(name("object"), "__setattr__"), name("self"), name("n"), name("x"))]]))
        self.probes(["class", k, [name(base)], [], True, self.code(body or [["assign", "zz", lit(1)]])])
        v = self.fresh("e")
        self.assign(v, call(name(k), *[self.anyval() for _ in range(r.choice([0, 1, 1, 2]))]))
        self.probe_exc(v)
        self.mutate(v, memoryerror=False, plain=False)
        self.probe_exc(v)

    def block_chain(self):
        r = self.rng
        a, b = self.fresh("a"), self.fresh("b")
        inner = r.choice(["ValueError", "KeyError", "OSError"])
        outer = r.choice(["TypeError", "RuntimeError", "ImportError"])
        k = r.randrange(3)
        raising = {0: ["raise", call(name(outer), lit("o"))],
                   1: ["raisefrom", call(name(outer), lit("o")), NONE],
                   2: ["raisefrom", call(name(outer), lit("o")), call(name("LookupError"), lit("c"))]}[k]
        self.st(["try", [["try", [["raise", call(name(inner), lit("i"))]], name(inner), a, [["assign", b + "i", name(a)], raising]]],
                 name(outer), b, [["assign", b + "k", name(b)]]])
        v = b + "k"
        for x in ["__context__", "__cause__", "__suppress_context__"]:
            self.probe(attr(name(v), x))
        self.probe(["is", attr(name(v), "__context__"), name(b + "i")])
        self.probe(["is", attr(name(v), "__traceback__"), NONE])
        self.probe(call(attr(name(v), "with_traceback"), attr(name(v), "__traceback__")))
        self.probe(["is", attr(call(attr(call(name("ValueError")), "with_traceback"),
                                    attr(name(v), "__traceback__")), "__traceback__"),
                    attr(name(v), "__traceback__")])
        self.mutate(v)

    def block_oserror(self):
        r = self.rng
        v = self.fresh("e")
        cname = r.choice(["OSError", "OSError", "OSError", "IOError", "EnvironmentError",
                          "BlockingIOError", "BlockingIOError", "FileNotFoundError", "ConnectionError"])
        kind = r.randrange(5)
        if kind == 1:
            k = self.fresh("K")
            self.cls(k, [cname], [self.method("__init__", k + ".__init__", ["self", "a", "b"],
                                              [["log", k + ".__init__"],
                                               ["expr", ["call", ["attr", ["super"], "__init__"], [name("a"), name("b")], []]]])])
            cname = k
        elif kind == 2:
            k = self.fresh("K")
            self.cls(k, [cname], [self.method("__new__", k + ".__new__", ["cls", "a", "b"],
                                              [["log", k + ".__new__"],
                                               ["ret", ["call", ["attr", ["super"], "__new__"], [name("cls"), name("a"), name("b")], []]]])])
            cname = k
        elif kind == 3:
            k = self.fresh("K")
            self.cls(k, [cname], [self.method("__init__", k + ".__init__", ["self", "a", "b", "c"],
                                              [["log", k + ".__init__"]])])
            cname = k
        n = r.choice([0, 1, 2, 2, 3, 3, 3, 4, 5, 5, 6])
        pool = [lit(r.choice(ERRNOS)), r.choice([lit(True), lit(False), lit(1), lit(2), lit("x"), NONE, big(2 ** 64)]),
                r.choice([lit("msg"), lit(""), NONE, lit(1)]),
                r.choice([lit("file"), lit("a/b"), NONE, lit(0), lit(7), lit(-1), big(2 ** 63), lit("")]),
                r.choice([NONE, lit(5), lit("w")]),
                r.choice([lit("file2"), NONE, lit(9)]),
                lit("extra")]
        pool = pool[1:] if False else pool
        args = [pool[0] if r.random() < 0.75 else pool[1]] + pool[2:]
        kw = [["x", lit(1)]] if r.random() < 0.05 else []
        self.assign(v, call(name(cname), *args[:n], kw=kw))
        self.probe_exc(v, ["errno", "strerror", "filename", "filename2", "characters_written"])
        self.probe(call(name("type"), name(v)))
        for _ in range(r.randrange(3)):
            c = r.randrange(5)
            if c == 0:
                self.probes(["setattr", name(v), "characters_written",
                             r.choice([lit(5), lit(0), lit(-1), big(2 ** 63), lit("x"), lit(True), NONE])])
                self.probe(attr(name(v), "characters_written"))
            elif c == 1:
                self.probes(["delattr", name(v), "characters_written"])
                self.probe(attr(name(v), "characters_written"))
            elif c == 2:
                self.probes(["setattr", name(v), r.choice(["errno", "strerror", "filename", "filename2"]),
                             r.choice([NONE, lit(1), lit("z")])])
            elif c == 3:
                self.probes(["expr", call(attr(name(v), "__init__"), *[self.anyval() for _ in range(r.randrange(4))])])
            else:
                self.probes(["delattr", name(v), r.choice(["errno", "strerror", "filename", "filename2"])])
            self.probe(call(name("str"), name(v)))
            self.probe(call(attr(name(v), "__reduce__")))
            self.probe(attr(name(v), "args"))

    def block_kwargs(self):
        r = self.rng
        c = r.choice(["ImportError", "ModuleNotFoundError", "NameError", "UnboundLocalError", "AttributeError"])
        keys = {"ImportError": ["name", "path", "name_from"], "ModuleNotFoundError": ["name", "path", "name_from"],
                "NameError": ["name"], "UnboundLocalError": ["name"], "AttributeError": ["name", "obj"]}[c]
        v = self.fresh("e")
        kw = [[k, self.anyval()] for k in keys if r.random() < 0.5]
        if r.random() < 0.15:
            kw.append(["zzq", lit(1)])
        args = r.choice([[], [lit("m")], [lit(1)], [lit("a"), lit("b")]])
        self.assign(v, call(name(c), *args, kw=kw))
        self.probe_exc(v, keys + ["msg"])
        if c.endswith("Error") and "AttributeError" == c:
            self.probe(call(attr(name(v), "__getstate__")))
        for _ in range(r.randrange(3)):
            a = r.choice(keys + ["msg", "q"])
            self.probes(["setattr", name(v), a, self.anyval()] if r.random() < 0.7 else ["delattr", name(v), a])
            self.probe(call(name("str"), name(v)))
            self.probe(call(attr(name(v), "__reduce__")))
        if r.random() < 0.3:
            self.probes(["expr", call(attr(name(v), "__init__"), lit("r"), kw=[[keys[0], lit("n2")]])])
            self.probe(attr(name(v), keys[0]))
            self.probe(attr(name(v), "args"))

    def block_syntax(self):
        r = self.rng
        c = r.choice(["SyntaxError", "IndentationError", "TabError", "_IncompleteInputError"])
        c = "SyntaxError" if c == "_IncompleteInputError" else c
        v = self.fresh("e")
        fn = r.choice([lit("a/b.py"), lit("/x/y"), lit("x/"), lit("/"), lit(""), lit("plain"), NONE, lit(1)])
        ln = r.choice([lit(1), lit(0), lit(-1), lit(True), NONE, lit("3"), big(2 ** 63 - 1), big(2 ** 63), big(-2 ** 63 - 1)])
        tail = [lit("txt"), lit(9), lit(10), lit("meta"), lit("over")]
        n = r.choice([0, 1, 2, 3, 4, 4, 4, 5, 6, 7, 8])
        items = ([fn, ln, lit(3)] + tail)[:n] if n <= 3 else [fn, ln, lit(3), tail[0]] + tail[1:][:n - 4]
        info = r.choice([TUPLE(*items), TUPLE(*items), LIST(*items), lit(5), lit("ab")])
        args = r.choice([[], [self.textv()], [lit("m"), info], [lit("m"), info], [lit("m"), info], [NONE, info],
                         [lit("m"), info, lit(1)], [lit(5)]])
        self.assign(v, call(name(c), *args))
        self.probe_exc(v, ["msg", "filename", "lineno", "offset", "text", "end_lineno", "end_offset",
                           "print_file_and_line", "_metadata"])
        for _ in range(r.randrange(3)):
            a = r.choice(["msg", "filename", "lineno"])
            self.probes(["setattr", name(v), a, r.choice([NONE, fn, ln, lit("mm")])] if r.random() < 0.8
                        else ["delattr", name(v), a])
            self.probe(call(name("str"), name(v)))

    def unicode_args(self, kind):
        r = self.rng
        obj_txt = r.choice(["abc", "", "a", "é€😀", "ab😀", "\xffĀ", "x" * 6])
        start, end = self.intv(), self.intv()
        if r.random() < 0.6:
            start = lit(r.randrange(-1, 8))
            end = lit(r.randrange(-1, 8))
        if r.random() < 0.05:
            start = r.choice([lit("x"), NONE, lit(True)])
        if r.random() < 0.05:
            end = r.choice([lit("x"), NONE, lit(False)])
        reason = r.choice([lit("why"), lit(""), lit(1) if r.random() < 0.2 else lit("r")])
        enc = lit("enc") if r.random() < 0.9 else lit(1)
        if kind == "translate":
            obj = lit(obj_txt) if r.random() < 0.95 else lit(5)
            return [obj, start, end, reason]
        if kind == "encode":
            obj = lit(obj_txt) if r.random() < 0.95 else self.bytesv()
        else:
            obj = self.bytesv() if r.random() < 0.9 else r.choice([lit(1), lit("a")])
        return [enc, obj, start, end, reason]

    def block_unicode(self):
        r = self.rng
        kind = r.choice(["encode", "decode", "translate"])
        cname = {"encode": "UnicodeEncodeError", "decode": "UnicodeDecodeError",
                 "translate": "UnicodeTranslateError"}[kind]
        v = self.fresh("e")
        args = self.unicode_args(kind)
        if r.random() < 0.08:
            args = args[:r.randrange(len(args))]
        kw = [["zz", lit(1)]] if r.random() < 0.03 else []
        if r.random() < 0.1:
            self.assign(v, call(attr(name(cname), "__new__"), name(cname)))
        else:
            self.assign(v, call(name(cname), *args, kw=kw))
        fields = ["encoding", "object", "start", "end", "reason"]
        self.probe(call(name("str"), name(v)))
        if kind != "decode":
            self.probe(call(name("repr"), name(v)))
        for a in fields:
            self.probe(attr(name(v), a))
        capi = r.choice(["encode", "decode", "translate", kind, kind])
        self.probe(call(name(f"_unicode_{capi}_get_start"), name(v)))
        self.probe(call(name(f"_unicode_{capi}_get_end"), name(v)))
        for _ in range(r.randrange(5)):
            c = r.randrange(8)
            if c == 0:
                self.probes(["setattr", name(v), r.choice(["start", "end"]), self.intv()])
            elif c == 1:
                self.probes(["setattr", name(v), r.choice(["start", "end"]),
                             r.choice([lit("x"), NONE, lit(True), TUPLE()])])
            elif c == 2:
                self.probes(["setattr", name(v), "object",
                             r.choice([lit("xyz"), lit(""), self.bytesv(), lit(5), NONE, lit("é")])])
            elif c == 3:
                self.probes(["setattr", name(v), r.choice(["reason", "encoding"]),
                             r.choice([lit("rr"), lit(5), NONE, TUPLE()])])
            elif c == 4:
                self.probes(["delattr", name(v), r.choice(fields)])
            elif c == 5:
                f = r.choice(["set_start", "set_end"])
                # In range only: _testcapi tests PyArg_ParseTuple() with `< 0`, so an
                # overflow there is a SystemError of the test helper.
                self.probe(call(name(f"_unicode_{capi}_{f}"), name(v), big(r.choice(EDGE_INTS[:11] + [-2 ** 63]))))
            elif c == 6:
                self.probe(call(name(f"_unicode_{capi}_{r.choice(['get_start', 'get_end'])}"), r.choice([lit(1), name(v)])))
            else:
                self.probes(["expr", call(attr(name(v), "__init__"), *self.unicode_args(kind))])
            for a in r.sample(fields, 2):
                self.probe(attr(name(v), a))
            self.probe(call(name("str"), name(v)))
            self.probe(call(name(f"_unicode_{capi}_get_start"), name(v)))
            self.probe(call(name(f"_unicode_{capi}_get_end"), name(v)))

    def block_unicode_reentrant(self):
        """A __str__ of `reason` that replaces `object` under UnicodeError.__str__."""
        r = self.rng
        kind = r.choice(["encode", "decode", "translate"])
        v = self.fresh("e")
        cname = {"encode": "UnicodeEncodeError", "decode": "UnicodeDecodeError",
                 "translate": "UnicodeTranslateError"}[kind]
        k = self.fresh("R")
        repl = r.choice([lit(5), lit("abcd"), self.bytesv(), NONE])
        act = r.choice([["setattr", name(v), "object", repl], ["delattr", name(v), "object"]])
        self.cls(k, [], [self.method("__str__", k + ".__str__", ["self"],
                                     [["log", k + ".__str__"], act, ["ret", lit("why")]])])
        args = self.unicode_args(kind)
        self.assign(v, call(name(cname), *args))
        self.probes(["setattr", name(v), "reason", call(name(k))])
        self.probe(call(name("str"), name(v)))

    def leaf(self):
        r = self.rng
        pool = ["ValueError", "ValueError", "TypeError", "KeyError", "OSError", "RuntimeError",
                "UnicodeError", "Exception"]
        if self.allow_base or r.random() < 0.04:
            pool += ["SystemExit", "KeyboardInterrupt"]
        c = r.choice(pool)
        if self.klasses and r.random() < 0.3:
            c = r.choice(self.klasses)
        v = self.fresh("x")
        self.assign(v, call(name(c), lit(r.randrange(4))))
        return name(v)

    def tree(self, depth, base_ok):
        """An expression building a group; nested groups come out as variables."""
        r = self.rng
        n = r.choice([1, 2, 2, 3])
        kids = []
        for _ in range(n):
            if depth > 0 and r.random() < 0.4:
                kids.append(self.tree(depth - 1, base_ok))
            else:
                kids.append(self.leaf())
        c = r.choice(self.groups)
        v = self.fresh("g")
        seq = r.choice([LIST, LIST, TUPLE])
        self.assign(v, call(name(c), lit(r.choice(["g", "h", ""])), seq(*kids)))
        return name(v)

    def group_classes(self):
        r = self.rng
        self.klasses = []
        self.allow_base = r.random() < 0.3
        self.groups = (["BaseExceptionGroup"] if self.allow_base
                       else ["ExceptionGroup", "ExceptionGroup", "BaseExceptionGroup"])
        if r.random() < 0.4:
            self.cls("MyErr", ["ValueError"], [])
            self.klasses.append("MyErr")
        if self.allow_base and r.random() < 0.4:
            self.cls("MyBase", ["BaseException"], [])
            self.klasses.append("MyBase")
        if r.random() < 0.08:
            self.cls("Sneaky", ["BaseException"],
                     [self.method("c", "Sneaky.c", ["self"], [["ret", name("ValueError")]]),
                      ["assign", "__class__", call(name("property"), name("c"))]])
            self.klasses.append("Sneaky")
        k = r.random()
        if k < 0.45:
            b = "BaseExceptionGroup" if self.allow_base else r.choice(["ExceptionGroup", "BaseExceptionGroup"])
            body = []
            d = r.randrange(7)
            q = "MyGroup.derive"
            ret = [lambda: ["ret", call(name("MyGroup"), attr(name("self"), "message"), name("excs"))],
                   lambda: ["ret", call(name("BaseExceptionGroup"), lit("derived"), name("excs"))],
                   lambda: ["ret", lit(1)],
                   lambda: ["raise", call(name("ValueError"), lit("no derive"))],
                   lambda: ["ret", name("self")],
                   lambda: ["ret", ["call", ["attr", ["super"], "derive"], [name("excs")], []]],
                   lambda: ["assign", "derive", NONE]][d]()
            if d == 6:
                body.append(ret)
            else:
                body.append(self.method("derive", q, ["self", "excs"], [["log", q], ret]))
            if r.random() < 0.15:
                body.append(self.method("__init__", "MyGroup.__init__", ["self", "m", "e"],
                                        [["log", "MyGroup.__init__"],
                                         ["expr", ["call", ["attr", ["super"], "__init__"], [name("m"), name("e")], []]]]))
            self.cls("MyGroup", [b], body)
            self.groups.append("MyGroup")

    def matcher(self):
        r = self.rng
        k = r.randrange(11)
        if k <= 2:
            return name(r.choice(["ValueError", "TypeError", "KeyError", "OSError", "Exception",
                                  "BaseException", "LookupError", "ExceptionGroup", "BaseExceptionGroup"]))
        if k == 3:
            return TUPLE(name("ValueError"), name("KeyError"))
        if k == 4:
            return r.choice([TUPLE(), TUPLE(name("ValueError"), lit(1)), TUPLE(TUPLE(name("KeyError"))), lit(1), NONE,
                             name("int"), LIST(name("ValueError"))])
        p = self.fresh("p")
        mode = r.randrange(6)
        body = [["log", p]]
        if mode == 0:
            body.append(["ret", lit(True)])
        elif mode == 1:
            body.append(["ret", lit(False)])
        elif mode == 2:
            body.append(["ret", call(name("isinstance"), name("e"), name("ValueError"))])
        elif mode == 3:
            body.append(["ret", call(name("isinstance"), name("e"), name("BaseExceptionGroup"))])
        elif mode == 4:
            body.append(["raise", call(name("RuntimeError"), lit("pred"))])
        else:
            body.append(["ret", r.choice([NONE, lit(0), lit("yes"), TUPLE()])])
        self.st(self.fn(p, ["e"], body))
        return name(p)

    def probe_group(self, e, depth=1):
        self.probe(e)
        self.probe(call(name("repr"), e))
        self.probe(call(name("str"), e))
        for a in ["message", "exceptions", "__cause__", "__context__", "__suppress_context__", "__notes__", "__dict__"]:
            self.probe(attr(e, a))

    def decorate_group(self, v):
        r = self.rng
        o = name(v)
        if r.random() < 0.4:
            self.probes(["setattr", o, "__cause__", r.choice([NONE, call(name("KeyError"), lit("c"))])])
        if r.random() < 0.3:
            self.probes(["setattr", o, "__context__", call(name("IndexError"), lit("ctx"))])
        if r.random() < 0.3:
            self.probe(call(attr(o, "add_note"), lit("note1")))
        if r.random() < 0.15:
            self.probes(["setattr", o, "__notes__", r.choice([TUPLE(lit("a")), lit("ab"), lit(5), LIST(lit("b"))])])
        if r.random() < 0.4:
            k = self.fresh("c")
            self.st(["try", [["raise", o]], name("BaseException"), k, [["assign", v, name(k)]]])
        if r.random() < 0.15:
            self.probes(["setattr", o, "q", lit(1)])

    def block_group(self):
        r = self.rng
        self.group_classes()
        t = self.tree(r.choice([0, 1, 1, 2]), True)
        v = self.fresh("g")
        self.assign(v, t)
        self.decorate_group(v)
        self.probe_group(name(v))
        for _ in range(r.randrange(1, 4)):
            m = self.matcher()
            kind = r.randrange(3)
            if kind == 0:
                self.probe(call(attr(name(v), "subgroup"), m))
                s = self.fresh("s")
                self.assign(s, call(attr(name(v), "subgroup"), m))
                self.probe(["is", name(s), name(v)])
                self.probe_group(name(s))
            else:
                s = self.fresh("s")
                self.assign(s, call(attr(name(v), "split"), m))
                self.probe(name(s))
                for i in [0, 1]:
                    self.probe(["is", ["sub", name(s), lit(i)], name(v)])
                    self.probe_group(["sub", name(s), lit(i)])
                    self.probe(["is", attr(["sub", name(s), lit(i)], "__traceback__"), attr(name(v), "__traceback__")])
        if r.random() < 0.3:
            self.probe(call(attr(name(v), "derive"), LIST(call(name("ValueError"), lit(1)))))
            self.probe(call(attr(name(v), "derive"), r.choice([lit(1), LIST()])))
            self.probe(call(attr(name(v), "split")))
            self.probe(call(attr(name(v), "subgroup"), lit(1), lit(2)))
        if r.random() < 0.15:
            self.probe(call(attr(name(v), "__reduce__")))
        if r.random() < 0.2:
            self.probes(["setattr", name(v), r.choice(["message", "exceptions"]), lit(1)])
            self.probes(["delattr", name(v), r.choice(["message", "exceptions"])])
        if r.random() < 0.1:
            self.probes(["setattr", name(v), "args",
                         r.choice([TUPLE(lit(1), lit(2)), TUPLE(lit(1), LIST(lit(2))), TUPLE(), TUPLE(lit(1)),
                                   TUPLE(lit(1), lit(2), LIST(lit(2)))])])
            self.probe(call(name("repr"), name(v)))

    def block_group_ctor(self):
        r = self.rng
        self.klasses = []
        c = r.choice(["ExceptionGroup", "BaseExceptionGroup", "ExceptionGroup"])
        k = r.randrange(5)
        if k == 1:
            self.cls("MyG", [c], [])
            c = "MyG"
        elif k == 2:
            self.cls("MyG", ["BaseExceptionGroup", "ValueError"], [])
            c = "MyG"
        ok = call(name("ValueError"), lit(1))
        badseq = self.fresh("Q")
        n = r.choice([0, 1, 2, 3])
        if r.random() < 0.3:
            ln = r.choice([0, 1, 2])
            body = [self.method("__len__", badseq + ".__len__", ["self"], [["log", badseq + ".__len__"], ["ret", lit(ln)]]),
                    self.method("__getitem__", badseq + ".__getitem__", ["self", "i"],
                                [["log", badseq + ".__getitem__"],
                                 ["if", ["cmp", ">=", name("i"), lit(ln)], [["raise", name("IndexError")]],
                                  [["ret", call(name("ValueError"), name("i"))]]]])]
            if r.random() < 0.5:
                body.append(self.method("__repr__", badseq + ".__repr__", ["self"],
                                        [["log", badseq + ".__repr__"],
                                         ["ret", r.choice([lit("SEQ"), lit("SEQ"), lit(1)])]]))
            self.cls(badseq, [], body)
            second = call(name(badseq))
        else:
            second = r.choice([LIST(ok), TUPLE(ok), LIST(), TUPLE(), LIST(lit(1)), TUPLE(ok, lit(2)), lit(1), lit("ab"), NONE,
                               ["dict", []], LIST(ok, call(name("KeyboardInterrupt"))),
                               TUPLE(call(name("SystemExit"), lit(1))), LIST(name("ValueError"))])
        args = [r.choice([lit("msg"), lit(""), lit(1), NONE]) if r.random() < 0.2 else lit("msg"), second, lit("extra")][:n]
        if n == 2 and r.random() < 0.7:
            args[0] = lit("msg")
        kw = [["x", lit(1)]] if r.random() < 0.05 else []
        v = self.fresh("g")
        self.assign(v, call(name(c), *args, kw=kw))
        self.probe(call(name("type"), name(v)))
        self.probe_group(name(v))

    def block_prep(self):
        r = self.rng
        self.group_classes()
        self.groups = [g for g in self.groups if g != "MyGroup"] or ["ExceptionGroup"]
        v = self.fresh("g")
        if r.random() < 0.8:
            self.assign(v, self.tree(1, True))
        else:
            self.assign(v, self.leaf())
        if r.random() < 0.3:
            self.probes(["setattr", name(v), "__cause__", call(name("KeyError"), lit("c"))])
        if r.random() < 0.9:
            k = self.fresh("c")
            self.st(["try", [["raise", name(v)]], name("BaseException"), k, [["assign", v, name(k)]]])
        parts = []
        for _ in range(r.randrange(4)):
            c = r.randrange(7)
            if c == 0:
                parts.append(NONE)
            elif c == 1:
                parts.append(call(name("ValueError"), lit("new")))
            elif c == 2:
                parts.append(call(attr(name(v), "subgroup"), r.choice([name("ValueError"), name("BaseException"), name("KeyError")])))
            elif c == 3:
                parts.append(["sub", call(attr(name(v), "split"), r.choice([name("ValueError"), name("TypeError")])), lit(1)])
            elif c == 4:
                parts.append(name(v))
            elif c == 5:
                parts.append(call(name("ExceptionGroup"), lit("other"), LIST(call(name("KeyError"), lit(1)))))
            else:
                parts.append(lit(r.choice([1, "x"])))
        excs = LIST(*parts) if r.random() < 0.95 else lit(1)
        orig = name(v) if r.random() < 0.95 else lit(1)
        res = self.fresh("r")
        self.assign(res, call(name("_prep_reraise_star"), orig, excs))
        self.probe(name(res))
        self.probe(["is", name(res), name(v)])
        self.probe(call(name("repr"), name(res)))

    def block_memory(self):
        r = self.rng
        k = r.randrange(3)
        if k == 0:
            self.probe(attr(call(name("MemoryError"), lit("x")), "args"))
            self.probe(attr(call(attr(name("MemoryError"), "__new__"), name("MemoryError"), lit("x")), "args"))
        elif k == 1:
            self.cls("M2", ["MemoryError"], [])
            self.probe(attr(call(attr(name("MemoryError"), "__new__"), name("M2"), lit("x")), "args"))
            self.probe(attr(call(name("M2"), lit("x")), "args"))
        else:
            self.probe(call(name("repr"), call(name("MemoryError"))))
            self.probe(call(name("str"), call(name("MemoryError"), lit("a"), lit("b"))))

    def user_classes(self):
        """Objects that log when the C code calls back into Python."""
        r = self.rng
        def logged(q, ret):
            return [["log", q], ["ret", ret]]
        self.cls("Ix", [], [self.method("__index__", "Ix.__index__", ["self"],
                                        logged("Ix.__index__", r.choice([lit(2), lit(-1), lit(0), big(2 ** 63), lit("s"), lit(True)])))])
        self.cls("Tx", [], [self.method("__str__", "Tx.__str__", ["self"], logged("Tx.__str__", r.choice([lit("T"), lit("T"), lit(1)]))),
                            self.method("__repr__", "Tx.__repr__", ["self"], logged("Tx.__repr__", r.choice([lit("R"), lit("R"), lit(1)])))])
        self.cls("Ss", ["str"], [])
        self.cls("Ii", ["int"], [])
        self.cls("Hh", ["int"], [self.method("__hash__", "Hh.__hash__", ["self"], logged("Hh.__hash__", lit(2))),
                                 self.method("__eq__", "Hh.__eq__", ["self", "o"], logged("Hh.__eq__", r.choice([lit(True), lit(False)])))])
        self.cls("It", [], [self.method("__iter__", "It.__iter__", ["self"],
                                        logged("It.__iter__", call(name("iter"), LIST(lit(1), lit("b")))))])
        self.cls("Sq", [], [self.method("__len__", "Sq.__len__", ["self"], logged("Sq.__len__", lit(2))),
                            self.method("__getitem__", "Sq.__getitem__", ["self", "i"],
                                        [["log", "Sq.__getitem__"],
                                         ["if", ["cmp", ">=", name("i"), lit(2)], [["raise", name("IndexError")]], [["ret", lit("note")]]]])])

    def block_userobj(self):
        r = self.rng
        self.user_classes()
        v = self.fresh("e")
        k = r.randrange(9)
        tx, ix, ss = call(name("Tx")), call(name("Ix")), call(name("Ss"), lit("a/b"))
        if k == 0:
            self.assign(v, call(name(r.choice(["OSError", "PermissionError"])), r.choice([tx, lit(5)]), tx, tx, NONE, tx))
            self.probe(call(name("str"), name(v)))
            self.probe(call(name("repr"), name(v)))
        elif k == 1:
            self.assign(v, call(name("BlockingIOError"), lit(1), lit("x"), ix))
            self.probe(attr(name(v), "characters_written"))
            self.probe(attr(name(v), "filename"))
        elif k == 2:
            self.assign(v, call(name("OSError"), lit(0), lit("x")))
            self.probes(["setattr", name(v), "characters_written", ix])
            self.probe(attr(name(v), "characters_written"))
        elif k == 3:
            n = r.choice(ERRNOS)
            self.assign(v, call(name("OSError"), call(name(r.choice(["Ii", "Hh"])), lit(n)), lit("x")))
            self.probe(call(name("type"), name(v)))
            self.probe(attr(name(v), "errno"))
        elif k == 4:
            cn = r.choice(["UnicodeEncodeError", "UnicodeTranslateError"])
            a = [ss, ix, ix, lit("r")] if cn == "UnicodeTranslateError" else [ss, ss, ix, ix, ss]
            self.assign(v, call(name(cn), *a))
            self.probe(call(name("str"), name(v)))
            self.probe(attr(name(v), "start"))
            self.probes(["setattr", name(v), "reason", tx])
            self.probe(call(name("str"), name(v)))
        elif k == 5:
            self.assign(v, call(name("SyntaxError"), r.choice([tx, ss]),
                                TUPLE(ss, call(name("Ii"), lit(3)), lit(1), r.choice([tx, lit("t")]))))
            self.probe(call(name("str"), name(v)))
            self.probe(attr(name(v), "filename"))
            self.assign(v + "b", call(name("SyntaxError"), lit("m"), call(name("It"))))
            self.assign(v + "c", call(name("SyntaxError"), lit("m"), call(name("Sq"))))
        elif k == 6:
            self.assign(v, call(name("ValueError"), tx))
            self.probes(["setattr", name(v), "args", r.choice([call(name("It")), call(name("Sq")), lit(1)])])
            self.probe(attr(name(v), "args"))
            self.probe(call(name("str"), name(v)))
            self.probe(call(attr(name(v), "add_note"), ss))
            self.probe(attr(name(v), "__notes__"))
        elif k == 7:
            self.assign(v, call(name("ExceptionGroup"), r.choice([ss, lit("m")]), LIST(call(name("ValueError"), lit(1)), call(name("KeyError"), lit(2)))))
            self.probe(call(name("str"), name(v)))
            self.probe(call(name("repr"), name(v)))
            self.probes(["setattr", name(v), "__notes__", r.choice([call(name("Sq")), call(name("It")), lit("ab"), TUPLE(lit("a"))])])
            s_ = self.fresh("s")
            self.assign(s_, call(attr(name(v), "split"), name("ValueError")))
            self.probe(attr(["sub", name(s_), lit(0)], "__notes__"))
            self.probe(attr(["sub", name(s_), lit(1)], "__notes__"))
            self.probe(attr(["sub", name(s_), lit(0)], "__suppress_context__"))
        else:
            self.assign(v, call(name("ImportError"), r.choice([ss, tx, lit("m")])))
            self.probe(call(name("str"), name(v)))
            self.assign(v + "b", call(name("KeyError"), tx))
            self.probe(call(name("str"), name(v + "b")))
            self.probe(call(name("repr"), name(v + "b")))

    def block_iter(self):
        r = self.rng
        v = self.fresh("e")
        k = r.randrange(3)
        cls = r.choice(["StopIteration", "SystemExit"])
        self.assign(v, call(name(cls), *[self.anyval() for _ in range(k)]))
        self.probe(attr(name(v), "value" if cls == "StopIteration" else "code"))
        self.probes(["expr", call(attr(name(v), "__init__"), *[self.anyval() for _ in range(r.randrange(3))])])
        self.probe(attr(name(v), "value" if cls == "StopIteration" else "code"))
        self.probe(attr(name(v), "args"))
        self.probes(["expr", call(attr(name(v), "__init__"), lit(1), kw=[["zz", lit(1)]])])
        self.probe(attr(name(v), "args"))


    def block_longname(self):
        """`%.200s` of `_PyArg_NoKeywords` on long and non-ASCII class names."""
        r = self.rng
        base = r.choice(["Exception", "ValueError", "OSError", "KeyError", "StopIteration",
                         "SystemExit", "SyntaxError", "ExceptionGroup", "BlockingIOError"])
        k = r.choice(["L" * 199, "L" * 200, "L" * 201, "L" * 300, "a" + "é" * 150, "é" * 99 + "xy",
                      "Lé" * 70, "K" + "ü" * 120])
        self.probes(["class", k, [name(base)], [], True, self.code([["assign", "zz", lit(1)]])])
        args = [lit("m"), LIST(call(name("ValueError")))] if base == "ExceptionGroup" else [lit(1)]
        self.probe(call(name(k), *args, kw=[["x", lit(1)]]))
        v = self.fresh("e")
        self.assign(v, call(name(k), *args))
        self.probe(call(attr(name(v), "__init__"), *args, kw=[["q", lit(2)]]))
        self.probe(attr(name(v), "args"))

    def block_setstate_live(self):
        """`__setstate__` walks the live dict: keys a `__setattr__` adds are set too."""
        r = self.rng
        st, k, v = self.fresh("st"), self.fresh("S"), self.fresh("e")
        extra = r.choice([0, 1, 3, 20])
        body = [["log", f"{k}.__setattr__"],
                ["if", ["cmp", "==", name("n"), lit("a")],
                 [["setitem", name(st), lit(f"b{i}"), lit(i)] for i in range(extra)] or [["assign", "zz", lit(1)]],
                 [["assign", "zz", lit(2)]]],
                ["expr", call(attr(name("object"), "__setattr__"), name("self"), name("n"), name("x"))]]
        self.cls(k, [r.choice(["Exception", "OSError", "ImportError"])],
                 [self.method("__setattr__", f"{k}.__setattr__", ["self", "n", "x"], body)])
        items = [[lit("a"), lit(1)]] + ([[lit("c"), lit(3)]] if r.random() < 0.5 else [])
        if r.random() < 0.2:
            items.append([lit(5), lit(5)])
        self.assign(st, ["dict", items])
        self.assign(v, call(name(k)))
        self.probe(call(attr(name(v), "__setstate__"), name(st)))
        self.probe(attr(name(v), "__dict__"))
        self.probe(name(st))

    def block_oserror_reentrant(self):
        """`OSError_str` formats the members it read at the start, even when a conversion
        reassigns one. The old values are constants, so nothing is freed."""
        r = self.rng
        k, v = self.fresh("En"), self.fresh("e")
        target = r.choice(["filename", "filename2", "strerror", "errno"])
        body = [["log", f"{k}.__str__"], ["setattr", name(v), target, r.choice([lit("new"), NONE])],
                ["ret", lit("9")]]
        self.cls(k, [], [self.method("__str__", f"{k}.__str__", ["self"], body)])
        args = [call(name(k)), lit("s")]
        m = r.randrange(3)
        if m >= 1:
            args += [lit("old")]
        if m == 2:
            args += [NONE, lit("old2")]
        self.assign(v, call(name(r.choice(["OSError", "FileNotFoundError"])), *args))
        self.probe(call(name("str"), name(v)))
        self.probe(attr(name(v), target))
        self.probe(call(name("str"), name(v)))


BLOCKS = ["block_longname", "block_setstate_live", "block_oserror_reentrant",
          "block_generic", "block_generic", "block_subclass", "block_chain", "block_oserror",
          "block_oserror", "block_kwargs", "block_syntax", "block_syntax", "block_unicode",
          "block_unicode", "block_unicode_reentrant", "block_group", "block_group", "block_group",
          "block_group_ctor", "block_prep", "block_memory", "block_iter", "block_userobj",
          "block_userobj"]


def gen_case(rng):
    g = X(rng)
    for _ in range(rng.choice([1, 1, 2])):
        getattr(g, rng.choice(BLOCKS))()
    return {"mod": "typeobj", "fn": "scenario", "codes": g.codes, "main": g.main}


def run_python(case):
    src_lines = []
    T.block_src(case["main"], case["codes"], 0, src_lines)
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

    env = {"__name__": "__main__", "_log": trace.append, "_probe": probe, "_note": note,
           "_text": text, "_bytes": lambda *a: bytes(a), "_bytearray": lambda *a: bytearray(a),
           "_prep_reraise_star": _testcapi.unstable_exc_prep_reraise_star}
    for k in ["encode", "decode", "translate"]:
        for op in ["get_start", "set_start", "get_end", "set_end"]:
            env[f"_unicode_{k}_{op}"] = getattr(_testcapi, f"unicode_{k}_{op}")
    try:
        exec(compile("\n".join(src_lines) + "\n", "<scenario>", "exec"), env)
    except BaseException as e:
        trace.append(f"UNCAUGHT {type(e).__name__}: {e}")
    return {"ok": trace}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=2000)
