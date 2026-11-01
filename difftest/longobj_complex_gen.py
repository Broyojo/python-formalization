"""Case generation and CPython side of the `Objects/complexobject.c` difftest.

`gen_case(rng)` returns one JSON-able case; `run_python(case)` runs it on this
interpreter and encodes the result the way `lean/PyLean/LongObj/DiffComplex.lean`
does. Doubles cross JSON as IEEE-754 bit patterns, so NaN, infinities and signed
zero survive; a NaN result is `"nan"`.

Objects are described by a spec that both sides decode, so a method's behaviour
is the same on both. `cx_new` and friends compare a log of Python-level calls and
warnings, so a difference in check order shows up even when the call raises.
"""

import ctypes
import math
import struct
import sys
import unicodedata
import warnings

import _testcapi

LIBM = ctypes.CDLL("libm.so.6")
LIBM.hypot.restype = ctypes.c_double
LIBM.hypot.argtypes = [ctypes.c_double, ctypes.c_double]
for _name, _args in (("atan2", 2), ("log", 1)):
    getattr(LIBM, _name).restype = ctypes.c_double
    getattr(LIBM, _name).argtypes = [ctypes.c_double] * _args
LIBM.sincos.restype = None
LIBM.sincos.argtypes = [ctypes.c_double, ctypes.POINTER(ctypes.c_double), ctypes.POINTER(ctypes.c_double)]

NAN = float("nan")
NEG_NAN = struct.unpack("<d", struct.pack("<Q", 0xFFF8000000000000))[0]
INF = float("inf")
DBL_MAX = sys.float_info.max
DBL_MIN = sys.float_info.min
TINY = 5e-324
EDGE = [
    0.0, -0.0, 1.0, -1.0, 0.5, -0.5, 2.0, -2.0, 3.0, 100.0, -100.0, 100.5, 101.0, 1.5,
    INF, -INF, NAN, NEG_NAN, DBL_MAX, -DBL_MAX, DBL_MIN, -DBL_MIN, TINY, -TINY,
    1e308, -1e308, 1e200, 1e-200, -1e-200, 1e154, 1e-154, 1e16, 1e15, 1e-4, 1e-5,
    2.0**53, 2.0**63, -(2.0**63), 2.0**64, 2.0**1023, 0.1, 0.2, 0.3, 4503599627370497.5,
]
INTS = [
    0, 1, -1, 2, -2, 3, 100, -100, 101, 2**31, 2**53, 2**53 + 1, -(2**53) - 1, 2**63 - 1,
    2**63, -(2**63), 2**64, -(2**64), 2**1023, 2**1024, -(2**1024), 10**308, 10**309,
    2**1024 - 2**970, 2**1024 - 2**970 - 1, -(2**1024) + 2**970, -(2**1024) + 2**970 + 1,
    2**1024 - 2**971, 10**400,
]


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def unbits(b):
    return struct.unpack("<d", struct.pack("<Q", b))[0]


def enc(x):
    return "nan" if x != x else bits(x)


def enc_cx(z):
    return {"re": enc(z.real), "im": enc(z.imag)}


def rand_double(rng):
    r = rng.random()
    if r < 0.6:
        return rng.choice(EDGE)
    if r < 0.75:
        return float(rng.randint(-100, 100))
    if r < 0.85:
        return unbits(rng.getrandbits(64))
    return rng.uniform(-10, 10)


def cx_spec(z):
    return {"re": bits(z.real), "im": bits(z.imag)}


def rand_cx(rng):
    return complex(rand_double(rng), rand_double(rng))


# Object specs -------------------------------------------------------------

def builtin_spec(tp, val, dc="a", nf="a", ni="a", num=True, exact=True, fq=None):
    return {"tp": tp, "fq": fq or tp, "num": num, "exact": exact, "val": val,
            "dc": dc, "nf": nf, "ni": ni}


def s_complex(z):
    return builtin_spec("complex", {"k": "c", **cx_spec(z)}, dc="b")


def s_float(x):
    return builtin_spec("float", {"k": "f", "x": bits(x)}, nf="b")


def s_int(n):
    return builtin_spec("int", {"k": "i", "n": n}, nf="b", ni="b")


def s_bool(b):
    return builtin_spec("bool", {"k": "i", "n": int(b)}, nf="b", ni="b", exact=False)


def s_str(s):
    return builtin_spec("str", {"k": "s", "s": [ord(c) for c in s], "r": repr(s)})


def s_none():
    return builtin_spec("NoneType", {"k": "none"})


def s_list():
    return builtin_spec("list", {"k": "o"}, num=False)


def s_object():
    return builtin_spec("object", {"k": "o"}, num=False)


def rand_int(rng):
    return rng.choice(INTS) if rng.random() < 0.8 else rng.randint(-10**6, 10**6)


def rand_ret_exc(rng):
    return {"raises": {"cls": "RuntimeError", "msg": "boom"}}


def rand_method_ret(rng, base):
    """What a user `__complex__`/`__float__`/`__index__` does."""
    r = rng.random()
    if r < 0.15:
        return rand_ret_exc(rng)
    if r < 0.55:
        return {"ret": {"complex": s_complex(rand_cx(rng)),
                        "float": s_float(rand_double(rng)),
                        "int": s_int(rand_int(rng))}[base]}
    if r < 0.75:  # strict subclass of the right type: deprecated
        return {"ret": sub_of(rng, base, plain=True)}
    return {"ret": rng.choice([s_str("x"), s_none(), s_list()])}


COUNTER = [0]


def sub_of(rng, base, plain=False):
    """An instance of a fresh subclass of `base`."""
    COUNTER[0] += 1
    name = f"C{COUNTER[0] % 10}"
    fq = f"m.{name}"
    if base == "complex":
        spec = builtin_spec(name, {"k": "c", **cx_spec(rand_cx(rng))}, dc="b", exact=False, fq=fq)
    elif base == "float":
        spec = builtin_spec(name, {"k": "f", "x": bits(rand_double(rng))}, nf="b", exact=False, fq=fq)
    elif base == "int":
        spec = builtin_spec(name, {"k": "i", "n": rand_int(rng)}, nf="b", ni="b", exact=False, fq=fq)
    elif base == "str":
        spec = builtin_spec(name, {"k": "s", "s": [49], "r": "'1'"}, exact=False, fq=fq)
    else:
        spec = builtin_spec(name, {"k": "o"}, exact=False, fq=fq)
    if not plain:
        if rng.random() < 0.4:
            spec["dc"] = rand_method_ret(rng, "complex")
        if rng.random() < 0.4:
            spec["nf"] = rand_method_ret(rng, "float")
        if rng.random() < 0.3:
            spec["ni"] = rand_method_ret(rng, "int")
    return spec


def rand_obj(rng):
    r = rng.random()
    if r < 0.2:
        return s_complex(rand_cx(rng))
    if r < 0.4:
        return s_float(rand_double(rng))
    if r < 0.55:
        return s_int(rand_int(rng))
    if r < 0.6:
        return s_bool(rng.random() < 0.5)
    if r < 0.65:
        return rng.choice([s_str("1+2j"), s_str("x"), s_none(), s_list(), s_object()])
    return sub_of(rng, rng.choice(["complex", "float", "int", "object", "str"]))


TRACE = []


def method(name, slot, build_obj):
    def m(self):
        TRACE.append(f"call {name}")
        if "raises" in slot:
            raise RuntimeError(slot["raises"]["msg"])
        return build_obj(slot["ret"])
    return m


def build(spec):
    """The Python object a spec describes."""
    val = spec["val"]
    k = val["k"]
    if spec["exact"] and spec["tp"] != "bool":
        if k == "c":
            return complex(unbits(val["re"]), unbits(val["im"]))
        if k == "f":
            return unbits(val["x"])
        if k == "i":
            return val["n"]
        if k == "s":
            return "".join(chr(c) for c in val["s"])
        if k == "none":
            return None
        return [] if spec["tp"] == "list" else object()
    if spec["tp"] == "bool":
        return bool(val["n"])
    base = {"c": complex, "f": float, "i": int, "s": str, "o": object}[k]
    ns = {"__module__": "m"}
    for key, name in (("dc", "__complex__"), ("nf", "__float__"), ("ni", "__index__")):
        slot = spec[key]
        if isinstance(slot, dict):
            ns[name] = method(name, slot, build)
    cls = type(spec["tp"], (base,), ns)
    if k == "c":
        return cls(unbits(val["re"]), unbits(val["im"]))
    if k == "f":
        return cls(unbits(val["x"]))
    if k == "i":
        return cls(val["n"])
    if k == "s":
        return cls("".join(chr(c) for c in val["s"]))
    return cls()


# Strings -------------------------------------------------------------------

FLOATS = ["0", "1", "1.5", ".5", "5.", "1e5", "1E5", "1e+5", "1e-5", "1e400", "1e-400", "-0", "+0",
          "nan", "NaN", "-nan", "+nan", "inf", "-inf", "+inf", "Infinity", "-INFINITY", "infinit",
          "1_000", "1_0.0_1", "1e1_0", "0.1", "123456789012345678", "1e", "1e+", ".", "e5", "+", "-",
          "0e5", "00", "007", "1.7976931348623157e308", "1.7976931348623159e308", "5e-324", "2e-324",
          "3e-324", "0." + "0" * 400 + "1", "1" + "0" * 400, "0" * 500 + "1"]
WS = ["", "", "", " ", "  ", "\t", "\n", "\r", "\x0b", "\x0c", "\xa0", " ", "\x85", "　", "\x1c", "\x1f"]
JUNK = ["\x00", "_", "__", "?", "(", ")", "é", "\x7f", "١", "٢", "\ud800", "\U0001d7d8", "x", "j", "+", "-", ",", "1", "e"]


def uni_digits(rng, s):
    return "".join(chr(0x0660 + ord(c) - 48) if c.isdigit() and rng.random() < 0.3 else c for c in s)


def rand_complex_str(rng):
    a = rng.choice(FLOATS)
    b = rng.choice(FLOATS)
    j = rng.choice(["j", "J"])
    sign = rng.choice(["+", "-"])
    body = rng.choice([
        a, a + j, j, "+" + j, "-" + j, a + sign + j,
        a + sign + b + j, a + sign + b.lstrip("+-") + j, a + sign + b, a + j + sign + b,
    ])
    if rng.random() < 0.2:
        body = uni_digits(rng, body)
    r = rng.random()
    if r < 0.25:
        body = "(" + rng.choice(WS) + body + rng.choice(WS) + ")"
    elif r < 0.3:
        body = "(" + body
    elif r < 0.35:
        body = body + ")"
    s = rng.choice(WS) + body + rng.choice(WS)
    r = rng.random()
    if r < 0.3:
        k = rng.randint(0, len(s))
        s = s[:k] + rng.choice(JUNK) + s[k:]
    elif r < 0.4 and s:
        k = rng.randrange(len(s))
        s = s[:k] + s[k + 1:]
    return s


def uni_db(s):
    sp = sorted({ord(c) for c in s if ord(c) >= 127 and c.isspace()})
    dec = sorted({(ord(c), unicodedata.decimal(c)) for c in s
                  if ord(c) >= 127 and unicodedata.decimal(c, None) is not None})
    return {"sp": sp, "dec": [list(p) for p in dec]}


# Cases ---------------------------------------------------------------------

KEEP = []  # objects whose address feeds the NaN hash


def base(fn, **kw):
    return {"mod": "longobj", "fn": fn, **kw}


def hypot_bits(z):
    return bits(LIBM.hypot(z.real, z.imag))


def sincos_field(a, b):
    """`sincos` at the phase of `_Py_c_pow`, which is what the compiled source calls:
    GCC merges the `cos` and `sin` of lines 333-334."""
    at = LIBM.atan2(a.imag, a.real)
    phase = at * b.real
    if b.imag != 0.0:
        phase += b.imag * LIBM.log(LIBM.hypot(a.real, a.imag))
    s, c = ctypes.c_double(), ctypes.c_double()
    LIBM.sincos(phase, ctypes.byref(s), ctypes.byref(c))
    return [bits(phase), bits(c.value), bits(s.value)]


def spec_cx(spec):
    """The complex value of a number spec, or None when it has none."""
    v = spec["val"]
    if v["k"] == "c":
        return complex(unbits(v["re"]), unbits(v["im"]))
    if v["k"] == "f":
        return complex(unbits(v["x"]), 0.0)
    if v["k"] == "i" and abs(v["n"]) < 2**1024 - 2**970:
        return complex(float(v["n"]), 0.0)
    return None


def gen_case(rng):
    fn = rng.choice([
        "cx_add", "cx_sub", "cx_mul", "cx_div", "cx_pow", "cx_pow", "cx_powi", "cx_neg", "cx_pos",
        "cx_dcomplex", "cx_abs", "cx_abs", "cx_bool", "cx_conj", "cx_getnewargs", "cx_repr",
        "cx_format", "cx_hash", "cx_cmp", "cx_cmp", "cx_new", "cx_new", "cx_new", "cx_new",
        "cx_from_number", "cx_real_as", "cx_imag_as", "cx_as_c", "cx_from_c", "cx_from_d",
        "cx_parse", "cx_parse", "cx_parse", "cx_parse_float", "cx_c_sum", "cx_c_diff", "cx_c_prod",
        "cx_c_quot", "cx_c_pow", "cx_c_neg", "cx_c_abs",
    ])
    if fn in ("cx_add", "cx_sub", "cx_mul", "cx_div"):
        o = lambda: rng.choice([s_complex(rand_cx(rng)), s_complex(rand_cx(rng)), s_float(rand_double(rng)),
                                s_int(rand_int(rng)), s_bool(True), s_str("x"), s_none(),
                                sub_of(rng, "float", plain=True), sub_of(rng, "int", plain=True),
                                sub_of(rng, "complex", plain=True)])
        v, w = o(), o()
        if v["val"]["k"] != "c" and w["val"]["k"] != "c":
            return None
        if fn == "cx_div" and rng.random() < 0.25:  # every operand shape over a zero
            v = s_complex(rand_cx(rng))
            w = rng.choice([s_complex(complex(rng.choice([0.0, -0.0]), rng.choice([0.0, -0.0]))),
                            s_float(rng.choice([0.0, -0.0])), s_int(0), s_bool(False)])
            if rng.random() < 0.5:
                v, w = rng.choice([s_float(rand_double(rng)), s_int(rand_int(rng))]), \
                    s_complex(complex(rng.choice([0.0, -0.0]), rng.choice([0.0, -0.0])))
        return base(fn, v=v, w=w)
    if fn in ("cx_pow", "cx_powi"):
        a = rand_cx(rng)
        if fn == "cx_powi":
            w = rng.choice([
                s_int(rng.randint(-101, 101)), s_float(float(rng.randint(-101, 101))),
                s_complex(complex(rng.randint(-101, 101), rng.choice([0.0, -0.0])))])
            return base("cx_pow", v=s_complex(a), w=w, z=s_none(), hy=hypot_bits(a),
                        sc=sincos_field(a, spec_cx(w)))
        v = rng.choice([s_complex(a), s_complex(a), s_float(a.real), s_int(rand_int(rng))])
        b = rand_cx(rng)
        w = rng.choice([s_complex(b), s_complex(b), s_float(b.real), s_int(rand_int(rng)), s_str("x"), s_none()])
        z = s_none() if rng.random() < 0.85 else rng.choice([s_int(3), s_float(1.0), s_complex(1j)])
        if v["val"]["k"] != "c" and w["val"]["k"] != "c":
            return None
        h, bv = spec_cx(v), spec_cx(w)
        if h is None or bv is None:
            return base("cx_pow", v=v, w=w, z=z, hy=0)
        return base("cx_pow", v=v, w=w, z=z, hy=hypot_bits(h), sc=sincos_field(h, bv))
    if fn == "cx_pos" or fn == "cx_dcomplex":
        return base(fn, o=rng.choice([s_complex(rand_cx(rng)), sub_of(rng, "complex", plain=True)]))
    if fn == "cx_abs":
        z = rand_cx(rng)
        return base(fn, z=cx_spec(z), hy=hypot_bits(z), errno=rng.choice([0, 0, 34, 33]))
    if fn in ("cx_neg", "cx_bool", "cx_conj", "cx_getnewargs", "cx_repr"):
        return base(fn, z=cx_spec(rand_cx(rng)))
    if fn == "cx_format":
        return base(fn, z=cx_spec(rand_cx(rng)),
                    spec=rng.choice([[], [], [ord(rng.choice("dxXobcs%i"))]]))
    if fn == "cx_hash":
        z = rand_cx(rng) if rng.random() < 0.7 else complex(rand_double(rng), rng.choice([0.0, -0.0]))
        KEEP.append(z)
        return base(fn, z=cx_spec(z), ptr=object.__hash__(z), id=len(KEEP) - 1)
    if fn == "cx_cmp":
        z = rand_cx(rng)
        if rng.random() < 0.5:
            x = rng.choice(INTS)
            if rng.random() < 0.7 and abs(x) < 2**1024 - 2**970:
                z = complex(float(x), rng.choice([0.0, -0.0, 0.0, 1.0, NAN]))
        w = rng.choice([s_int(rand_int(rng)), s_float(rand_double(rng)), s_complex(rand_cx(rng)),
                        s_float(z.real), s_complex(z), s_int(int(z.real) if math.isfinite(z.real) else 0),
                        s_bool(True), s_str("x"), s_none(), sub_of(rng, "int", plain=True)])
        return base(fn, z=cx_spec(z), w=w, op=rng.choice(["eq", "eq", "ne", "ne", "lt", "le", "gt", "ge"]))
    if fn == "cx_new":
        c = base(fn, warnerr=rng.random() < 0.15)
        if rng.random() < 0.2:
            c["sub"] = "m.CSub"
        n = rng.choice([0, 1, 1, 1, 2, 2, 2, 3])
        c["args"] = [rand_obj(rng) for _ in range(n)]
        c["kw"] = []
        if rng.random() < 0.3:
            names = rng.sample(["real", "imag", "x"], rng.choice([1, 1, 2]))
            c["kw"] = [[k, rand_obj(rng)] for k in names]
        return c
    if fn == "cx_from_number":
        c = base(fn, o=rand_obj(rng), warnerr=rng.random() < 0.15)
        if rng.random() < 0.3:
            c["sub"] = "m.CSub"
        return c
    if fn in ("cx_real_as", "cx_imag_as", "cx_as_c"):
        return base(fn, o=rand_obj(rng), warnerr=rng.random() < 0.15)
    if fn in ("cx_from_c", "cx_from_d", "cx_c_neg"):
        return base(fn, z=cx_spec(rand_cx(rng)))
    if fn == "cx_c_abs":
        z = rand_cx(rng)
        return base(fn, z=cx_spec(z), hy=hypot_bits(z))
    if fn in ("cx_parse", "cx_parse_float"):
        s = rand_complex_str(rng)
        if rng.random() < 0.5:  # a plain float string: accepted by both parsers
            s = rng.choice(WS) + rng.choice(FLOATS) + rng.choice(WS)
        return base(fn, s=[ord(c) for c in s], repr=repr(s), db=uni_db(s))
    a, b = rand_cx(rng), rand_cx(rng)
    if fn == "cx_c_pow" and rng.random() < 0.5:
        b = complex(rng.randint(-5, 5), 0.0)
    return base(fn, a=cx_spec(a), b=cx_spec(b), hy=hypot_bits(a), sc=sincos_field(a, b))


def get_cx(c, key):
    d = c[key]
    return complex(unbits(d["re"]), unbits(d["im"]))


def enc_bin(r):
    if r is NotImplemented:
        return "NotImplemented"
    return enc_cx(r)


def enc_made(r, arg=None, sub=None):
    tp = type(r)
    name = "complex" if tp is complex else f"{tp.__module__}.{tp.__qualname__}"
    return {"tp": name, "re": enc(r.real), "im": enc(r.imag), "isarg": r is arg}


def traced(thunk, warnerr):
    """Run `thunk`, returning `{"ok": {"r": ..., "log": [...]}}`."""
    TRACE.clear()

    def show(message, category, filename, lineno, file=None, line=None):
        TRACE.append(f"warn {message}")

    with warnings.catch_warnings():
        warnings.simplefilter("error" if warnerr else "always", DeprecationWarning)
        warnings.showwarning = show
        try:
            r = thunk()
        except Exception as e:
            r = {"exc": type(e).__name__, "msg": str(e)}
    return {"ok": {"r": r, "log": list(TRACE)}}


class CC(ctypes.Structure):
    _fields_ = [("real", ctypes.c_double), ("imag", ctypes.c_double)]


_real_as = ctypes.pythonapi.PyComplex_RealAsDouble
_real_as.restype, _real_as.argtypes = ctypes.c_double, [ctypes.py_object]
_imag_as = ctypes.pythonapi.PyComplex_ImagAsDouble
_imag_as.restype, _imag_as.argtypes = ctypes.c_double, [ctypes.py_object]
_as_c = ctypes.pythonapi.PyComplex_AsCComplex
_as_c.restype, _as_c.argtypes = CC, [ctypes.py_object]
_from_d = ctypes.pythonapi.PyComplex_FromDoubles
_from_d.restype, _from_d.argtypes = ctypes.py_object, [ctypes.c_double, ctypes.c_double]


def ok(v):
    return {"ok": v}


def run_python(c):
    fn = c["fn"]
    if fn in ("cx_add", "cx_sub", "cx_mul", "cx_div"):
        v, w = build(c["v"]), build(c["w"])
        name = {"cx_add": "add", "cx_sub": "sub", "cx_mul": "mul", "cx_div": "truediv"}[fn]
        try:
            if isinstance(v, complex):
                return ok(enc_bin(getattr(complex, f"__{name}__")(v, w)))
            return ok(enc_bin(getattr(complex, f"__r{name}__")(w, v)))
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "cx_pow":
        v, w, z = build(c["v"]), build(c["w"]), build(c["z"])
        try:
            if isinstance(v, complex):
                return ok(enc_bin(complex.__pow__(v, w, z)))
            return ok(enc_bin(complex.__rpow__(w, v, z)))
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "cx_neg":
        return ok(enc_cx(-get_cx(c, "z")))
    if fn == "cx_pos":
        o = build(c["o"])
        return ok(enc_made(complex.__pos__(o), o))
    if fn == "cx_dcomplex":
        o = build(c["o"])
        return ok(enc_made(complex.__complex__(o), o))
    if fn == "cx_abs":
        z = get_cx(c, "z")
        try:
            _testcapi.set_errno(c["errno"])
            return ok(enc(complex.__abs__(z)))
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "cx_bool":
        return ok(bool(get_cx(c, "z")))
    if fn == "cx_conj":
        return ok(enc_cx(get_cx(c, "z").conjugate()))
    if fn == "cx_getnewargs":
        return ok([enc(x) for x in get_cx(c, "z").__getnewargs__()])
    if fn == "cx_repr":
        return ok(repr(get_cx(c, "z")))
    if fn == "cx_format":
        try:
            return ok(format(get_cx(c, "z"), "".join(chr(x) for x in c["spec"])))
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "cx_hash":
        return ok(hash(KEEP[c["id"]]))
    if fn == "cx_cmp":
        z, w = get_cx(c, "z"), build(c["w"])
        r = getattr(complex, f"__{c['op']}__")(z, w)
        return ok("NotImplemented" if r is NotImplemented else r)
    if fn == "cx_new":
        args = [build(s) for s in c["args"]]
        kw = {k: build(s) for k, s in c["kw"]}
        cls = complex
        if "sub" in c:
            cls = type("CSub", (complex,), {"__module__": "m"})
        first = args[0] if len(args) == 1 and not kw else None
        return traced(lambda: enc_made(cls(*args, **kw), first), c["warnerr"])
    if fn == "cx_from_number":
        o = build(c["o"])
        cls = complex
        if "sub" in c:
            cls = type("CSub", (complex,), {"__module__": "m"})
        return traced(lambda: enc_made(cls.from_number(o), o), c["warnerr"])
    if fn == "cx_real_as":
        o = build(c["o"])
        return traced(lambda: enc(_real_as(o)), c["warnerr"])
    if fn == "cx_imag_as":
        o = build(c["o"])
        return traced(lambda: enc(_imag_as(o)), c["warnerr"])
    if fn == "cx_as_c":
        o = build(c["o"])
        def as_c():
            r = _as_c(o)
            return enc_cx(complex(r.real, r.imag))
        return traced(as_c, c["warnerr"])
    if fn == "cx_from_c":
        return ok(enc_made(_testcapi.complex_fromccomplex(get_cx(c, "z"))))
    if fn == "cx_from_d":
        z = get_cx(c, "z")
        return ok(enc_made(_from_d(z.real, z.imag)))
    if fn in ("cx_parse", "cx_parse_float"):
        s = "".join(chr(x) for x in c["s"])
        try:
            if fn == "cx_parse":
                return ok(enc_cx(complex(s)))
            return ok(enc(float(s)))
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "cx_c_neg":
        return ok(enc_cx(_testcapi._py_c_neg(get_cx(c, "z"))))
    if fn == "cx_c_abs":
        v, e = _testcapi._py_c_abs(get_cx(c, "z"))
        return ok([enc(v), e])
    if fn in ("cx_c_sum", "cx_c_diff", "cx_c_prod", "cx_c_quot", "cx_c_pow"):
        name = "_py_" + fn[3:]
        v, e = getattr(_testcapi, name)(get_cx(c, "a"), get_cx(c, "b"))
        return ok([enc_cx(v), e])
    raise ValueError(fn)
