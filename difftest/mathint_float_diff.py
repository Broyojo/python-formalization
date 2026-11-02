"""Differential test: Lean model of Modules/mathmodule.c (the float functions of `math`)
vs. the running CPython.

Usage: python3 difftest/mathint_float_diff.py [--cases N] [--seed S]

Arguments are floats, ints, bools, float subclasses and objects with `__float__`,
`__index__`, `__floor__`, `__ceil__`, `__trunc__` that return or raise. The C library's
transcendental functions are the model's parameters; the Lean side instantiates them with
the platform's own, so this also checks the wrappers around them. Exits non-zero on any
mismatch. See difftest/common.py.
"""

import math
import struct
import sys
import warnings

sys.set_int_max_str_digits(0)
warnings.simplefilter("ignore")

import common

P31, P63, P64 = 1 << 31, 1 << 63, 1 << 64


def f2b(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def b2f(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


MAXF = 1.7976931348623157e308
MINN = 2.2250738585072014e-308
TINY = 5e-324
SPECIAL = [0.0, -0.0, 1.0, -1.0, 2.0, -2.0, 0.5, -0.5, 3.0, -3.0, 1.5, -1.5, 0.25, 4.0,
           math.inf, -math.inf, math.nan, -math.nan, TINY, -TINY, MINN, -MINN, MINN / 2,
           MAXF, -MAXF, 2.0 ** 52, 2.0 ** 53, 2.0 ** 53 + 2, -(2.0 ** 63), 2.0 ** 63, 1e308,
           1e-308, 1e300, -1e300, math.pi, math.e, 0.1, 10.0, 100.0, 1e-20, 1e-21, 170.5,
           171.0, 171.5, 171.6, 171.7, 172.0, 200.0, 200.5, -200.5, 199.5, -190.5, 140.0,
           139.5, 5.0, 4.5, 5.524680040776729, 23.0, 24.0, 22.0, -0.5, -1.5, -2.5, 1e-9,
           0.9999999999999999, 1.0000000000000002, 2.0 ** -1022, 2.0 ** -1074, 2.0 ** 1023]


def edge_float(rng):
    r = rng.random()
    if r < 0.35:
        x = rng.choice(SPECIAL)
    elif r < 0.55:
        x = b2f(rng.getrandbits(64))
    elif r < 0.7:
        x = rng.uniform(-10, 10)
    elif r < 0.8:
        x = float(rng.randrange(-30, 30)) + rng.choice([0.0, 0.0, 0.5, 1e-9, -1e-9, 0.25])
    elif r < 0.9:
        x = math.ldexp(rng.uniform(0.5, 1.0), rng.randrange(-1076, 1024)) * rng.choice([1, -1])
    else:
        # a neighbour of a special value
        x = rng.choice(SPECIAL)
        if math.isfinite(x):
            for _ in range(rng.randrange(1, 4)):
                x = math.nextafter(x, rng.choice([math.inf, -math.inf]))
    return x


def edge_int(rng):
    r = rng.random()
    if r < 0.4:
        v = rng.choice([0, 1, 2, 3, 10, 2 ** 52, 2 ** 53, 2 ** 53 + 1, P31 - 1, P31, P63 - 1, P63,
                        P64 - 1, P64, P64 + 1, 2 ** 1023, 2 ** 1024, 2 ** 1024 - 2 ** 970,
                        2 ** 1024 - 2 ** 970 - 1, 10 ** 308, 10 ** 309, 10 ** 400, 2 ** 3000,
                        3037000499, 3037000500])
    elif r < 0.7:
        v = rng.randrange(-100, 100)
    else:
        v = rng.getrandbits(rng.randrange(1, 1200))
    return -v if rng.random() < 0.3 else v


NAMES = ["Foo", "Bar", "Num"]


def gen_ret(rng, kind):
    """What a dunder returns: mostly the right type, sometimes not."""
    r = rng.random()
    if kind == "float":
        if r < 0.6:
            return {"f": f2b(edge_float(rng))}
        if r < 0.7:
            return {"fs": f2b(edge_float(rng)), "fq": "FSub"}
        if r < 0.85:
            return {"i": edge_int(rng)}
        return {"o": "Thing"}
    if kind == "index":
        if r < 0.75:
            return {"i": edge_int(rng)}
        if r < 0.85:
            return {"is": rng.randrange(2), "fq": "bool"}
        if r < 0.92:
            return {"f": f2b(edge_float(rng))}
        return {"o": "Thing"}
    # floor/ceil/trunc: anything
    if r < 0.6:
        return {"i": edge_int(rng)}
    if r < 0.8:
        return {"f": f2b(edge_float(rng))}
    return {"o": "Thing"}


def gen_dunder(rng, kind):
    if rng.random() < 0.15:
        exc = rng.choice(["ValueError", "OverflowError", "RuntimeError", "TypeError"])
        return {"raise": {"exc": exc, "msg": "boom"}}
    return {"ret": gen_ret(rng, kind)}


def gen_arg(rng, fl=None):
    """An argument: mostly a float `fl` (or a fresh edge float)."""
    r = rng.random()
    if r < 0.72:
        return {"f": f2b(edge_float(rng) if fl is None else fl)}
    if r < 0.82:
        return {"i": edge_int(rng)}
    if r < 0.85:
        return {"b": rng.random() < 0.5}
    if r < 0.89:
        spec = {"fs": f2b(edge_float(rng)), "fq": "FSub"}
        for k in ("floor", "ceil", "trunc"):
            if rng.random() < 0.2:
                spec[k] = gen_dunder(rng, k)
        return spec
    name = rng.choice(NAMES)
    spec = {"o": name, "fq": name}
    has = rng.random()
    if has < 0.4:
        spec["float"] = gen_dunder(rng, "float")
    elif has < 0.75:
        spec["index"] = gen_dunder(rng, "index")
    elif has < 0.9:
        spec["float"] = gen_dunder(rng, "float")
        spec["index"] = gen_dunder(rng, "index")
    for k in ("floor", "ceil", "trunc"):
        if rng.random() < 0.4:
            spec[k] = gen_dunder(rng, k)
    return spec


def int_arg(rng):
    r = rng.random()
    if r < 0.75:
        return {"i": edge_int(rng)}
    if r < 0.8:
        return {"b": rng.random() < 0.5}
    if r < 0.9:
        return {"f": f2b(edge_float(rng))}
    return gen_arg(rng)


def gen_it(rng, gen_item, n_max=8):
    items = [gen_item(rng) for _ in range(rng.randrange(0, n_max))]
    it = {"items": items}
    if rng.random() < 0.08:
        it["err"] = {"exc": rng.choice(["ValueError", "RuntimeError"]), "msg": "iter boom"}
    return it


FUNC1 = ["acos", "acosh", "asin", "asinh", "atan", "atanh", "cbrt", "cos", "cosh", "exp",
         "exp2", "fabs", "sin", "sinh", "sqrt", "tan", "tanh"]
UNARY = ["frexp", "modf", "isfinite", "isnan", "isinf", "isnormal", "issubnormal", "signbit",
         "ulp", "floor", "ceil", "trunc", "degrees", "radians", "log2", "log10", "gamma",
         "lgamma"]


def float_item(rng):
    r = rng.random()
    if r < 0.85:
        return {"f": f2b(edge_float(rng))}
    if r < 0.95:
        return {"i": edge_int(rng)}
    return gen_arg(rng)


def prod_item(rng):
    r = rng.random()
    if r < 0.45:
        return {"i": rng.choice([0, 1, -1, 2, 3, 7, P31, P63 - 1, -P63, P63, 3037000499,
                                 3037000500, -3037000500, 2 ** 32 + 1, rng.randrange(-1000, 1000),
                                 rng.randrange(-P64, P64)])}
    if r < 0.75:
        return {"f": f2b(edge_float(rng))}
    if r < 0.85:
        return {"b": rng.random() < 0.5}
    if r < 0.95:
        return {"fs": f2b(edge_float(rng)), "fq": "FSub"}
    return {"o": "Thing", "fq": "Thing"}


def gen_case(rng):
    r = rng.random()
    c = {"mod": "mathint"}
    if r < 0.18:
        fn = rng.choice(UNARY)
        c["x"] = gen_arg(rng)
        if fn in ("log2", "log10") and rng.random() < 0.3:
            c["x"] = int_arg(rng)
    elif r < 0.3:
        fn = rng.choice(FUNC1)
        c["x"] = gen_arg(rng)
    elif r < 0.35:
        fn = "log"
        n = rng.choice([1, 1, 2, 2, 0, 3])
        c["args"] = [int_arg(rng) if rng.random() < 0.3 else gen_arg(rng) for _ in range(n)]
    elif r < 0.39:
        fn = "ldexp"
        c["x"] = gen_arg(rng)
        c["i"] = int_arg(rng) if rng.random() < 0.85 else gen_arg(rng)
        if "i" in c["i"] and rng.random() < 0.5:
            c["i"] = {"i": rng.choice([P31 - 1, P31, -P31, -P31 - 1, P63 - 1, P63, -P63, -P63 - 1,
                                       1074, 1075, -1074, -1075, -1076, 1023, 1024, 2000, -2000])
                      + rng.randrange(-2, 3)}
    elif r < 0.43:
        fn = rng.choice(["fmod", "pow"])
        c["x"], c["y"] = gen_arg(rng), gen_arg(rng)
    elif r < 0.48:
        fn = rng.choice(["remainder", "copysign", "atan2"])
        n = 2 if rng.random() < 0.95 else rng.choice([0, 1, 3])
        c["args"] = [gen_arg(rng) for _ in range(n)]
        if fn == "remainder" and n == 2 and rng.random() < 0.5:
            # ties and near-ties: x = (k + 1/2) * y
            y = edge_float(rng)
            k = rng.choice([0, 1, 2, 3, 4, 5, 10, 11, rng.randrange(1 << 20)])
            x = (k + 0.5) * y
            if rng.random() < 0.3:
                x = math.nextafter(x, rng.choice([math.inf, -math.inf]))
            c["args"] = [{"f": f2b(x)}, {"f": f2b(y)}]
    elif r < 0.52:
        fn = "fma"
        c["x"], c["y"], c["z"] = gen_arg(rng), gen_arg(rng), gen_arg(rng)
    elif r < 0.57:
        fn = "isclose"
        c["a"], c["b"] = gen_arg(rng), gen_arg(rng)
        if rng.random() < 0.4 and "f" in c["a"]:
            a = b2f(c["a"]["f"])
            c["b"] = {"f": f2b(a * (1 + rng.choice([1e-9, 1e-10, 2e-9, -1e-9, 1e-8, 0.0])))}
        if rng.random() < 0.5:
            c["rel_tol"] = gen_arg(rng, abs(edge_float(rng)) if rng.random() < 0.5 else
                                   rng.choice([1e-9, 0.0, 1e-5, 0.5, 1.0, -1e-9]))
        if rng.random() < 0.5:
            c["abs_tol"] = gen_arg(rng, rng.choice([0.0, 1e-300, 1e-9, 1.0, -0.0, -1.0, math.inf]))
    elif r < 0.63:
        fn = "nextafter"
        c["x"], c["y"] = gen_arg(rng), gen_arg(rng)
        if rng.random() < 0.7:
            s = rng.random()
            if s < 0.6:
                c["steps"] = {"i": rng.choice([0, 1, 2, 3, 10, rng.randrange(1 << 12),
                                               rng.randrange(1 << 64), P64 - 1, P64, P64 + 5,
                                               2 ** 100, -1, -P64, 2 ** 52, 2 ** 62, P63])}
            else:
                c["steps"] = int_arg(rng)
    elif r < 0.7:
        fn = "fsum"
        c["it"] = gen_it(rng, float_item, 10)
    elif r < 0.75:
        fn = "hypot"
        c["args"] = [float_item(rng) for _ in range(rng.randrange(0, 6))]
    elif r < 0.79:
        fn = "dist"
        n = rng.randrange(0, 5)
        c["p"] = {"items": [float_item(rng) for _ in range(n)]}
        c["q"] = {"items": [float_item(rng) for _ in range(n if rng.random() < 0.9 else
                                                          rng.randrange(0, 5))]}
        for k in ("p", "q"):
            if rng.random() < 0.3:
                c[k]["gen"] = True
                if rng.random() < 0.2:
                    c[k]["err"] = {"exc": "RuntimeError", "msg": "iter boom"}
    elif r < 0.85:
        fn = "prod"
        c["it"] = gen_it(rng, prod_item, 7)
        if rng.random() < 0.6:
            c["start"] = prod_item(rng)
    elif r < 0.92:
        fn = rng.choice(["gamma", "lgamma"])
        x = edge_float(rng)
        if rng.random() < 0.5:
            x = rng.choice([float(rng.randrange(-30, 30)), rng.uniform(-205, 205),
                            float(rng.randrange(-300, 300)) + 0.5, rng.uniform(-1e-19, 1e-19)])
        c["x"] = {"f": f2b(x)} if rng.random() < 0.9 else gen_arg(rng, x)
    else:
        fn = rng.choice(["log", "log2", "log10"])
        a = rng.choice([{"i": edge_int(rng)},
                        {"o": "Big", "fq": "Big",
                         "index": {"ret": {"i": edge_int(rng)}}},
                        {"o": "Big", "fq": "Big",
                         "float": {"raise": {"exc": "OverflowError", "msg": "too big"}},
                         "index": {"ret": {"i": edge_int(rng)}}}])
        if fn == "log":
            c["args"] = [a] if rng.random() < 0.7 else [a, rng.choice([a, gen_arg(rng)])]
        else:
            c["x"] = a
    c["fn"] = "m." + fn
    return c


# -- building Python objects -------------------------------------------------------

class FSub(float):
    pass


class Thing:
    pass


def build_ret(v):
    if "f" in v:
        return b2f(v["f"])
    if "fs" in v:
        return FSub(b2f(v["fs"]))
    if "i" in v:
        return v["i"]
    if "is" in v:
        return bool(v["is"])
    return Thing()


EXC = {"ValueError": ValueError, "OverflowError": OverflowError, "RuntimeError": RuntimeError,
       "TypeError": TypeError}


def make_method(d):
    if "raise" in d:
        e = d["raise"]

        def m(self):
            raise EXC[e["exc"]](e["msg"])
    else:
        val = d["ret"]

        def m(self):
            return build_ret(val)
    return m


def build(spec):
    if "f" in spec:
        return b2f(spec["f"])
    if "i" in spec:
        return spec["i"]
    if "b" in spec:
        return spec["b"]
    dunders = {}
    for key, name in (("float", "__float__"), ("index", "__index__"), ("floor", "__floor__"),
                      ("ceil", "__ceil__"), ("trunc", "__trunc__")):
        if key in spec:
            dunders[name] = make_method(spec[key])
    if "fs" in spec:
        cls = type("FSub", (float,), dunders)
        return cls(b2f(spec["fs"]))
    if not dunders and spec["o"] == "Thing":
        return Thing()
    cls = type(spec["o"], (), dunders)
    return cls()


def fq(o):
    t = type(o)
    return t.__qualname__ if t.__module__ in ("builtins", "__main__") else t.__module__ + "." + t.__qualname__


def enc_f(x):
    return "nan" if x != x else f2b(x)


def enc_ret(o):
    if type(o) is float:
        return {"f": enc_f(o)}
    if isinstance(o, float):
        return {"fs": enc_f(o), "fq": fq(o)}
    if type(o) is int:
        return {"i": o}
    if isinstance(o, int):
        return {"is": int(o), "fq": fq(o)}
    return {"o": fq(o)}


def call(c):
    fn = c["fn"][2:]
    if fn in ("frexp",):
        m, e = math.frexp(build(c["x"]))
        return [enc_f(m), e]
    if fn == "modf":
        return [enc_f(v) for v in math.modf(build(c["x"]))]
    if fn in ("isfinite", "isnan", "isinf", "isnormal", "issubnormal", "signbit"):
        return getattr(math, fn)(build(c["x"]))
    if fn in ("floor", "ceil", "trunc"):
        return enc_ret(getattr(math, fn)(build(c["x"])))
    if fn in UNARY or fn in FUNC1:
        return enc_f(getattr(math, fn)(build(c["x"])))
    if fn == "log":
        return enc_f(math.log(*[build(a) for a in c["args"]]))
    if fn == "ldexp":
        return enc_f(math.ldexp(build(c["x"]), build(c["i"])))
    if fn in ("fmod", "pow"):
        return enc_f(getattr(math, fn)(build(c["x"]), build(c["y"])))
    if fn in ("remainder", "copysign", "atan2"):
        return enc_f(getattr(math, fn)(*[build(a) for a in c["args"]]))
    if fn == "fma":
        return enc_f(math.fma(build(c["x"]), build(c["y"]), build(c["z"])))
    if fn == "isclose":
        kw = {k: build(c[k]) for k in ("rel_tol", "abs_tol") if k in c}
        return math.isclose(build(c["a"]), build(c["b"]), **kw)
    if fn == "nextafter":
        if "steps" in c:
            return enc_f(math.nextafter(build(c["x"]), build(c["y"]), steps=build(c["steps"])))
        return enc_f(math.nextafter(build(c["x"]), build(c["y"])))
    if fn == "fsum":
        return enc_f(math.fsum(build_gen(c["it"])))
    if fn == "hypot":
        return enc_f(math.hypot(*[build(a) for a in c["args"]]))
    if fn == "dist":
        p, q = c["p"], c["q"]
        pp = build_gen(p) if p.get("gen") else tuple(build(s) for s in p["items"])
        qq = build_gen(q) if q.get("gen") else tuple(build(s) for s in q["items"])
        return enc_f(math.dist(pp, qq))
    if fn == "prod":
        if "start" in c:
            return enc_ret(math.prod(build_gen(c["it"]), start=build(c["start"])))
        return enc_ret(math.prod(build_gen(c["it"])))
    raise ValueError(fn)


def build_gen(it):
    items = [build(s) for s in it["items"]]
    err = it.get("err")

    def g():
        yield from items
        if err:
            raise EXC[err["exc"]](err["msg"])
    return g()


def run_python(c):
    return common.py_result(lambda: call(c))


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
