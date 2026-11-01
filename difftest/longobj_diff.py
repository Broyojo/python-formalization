"""Differential test: digit-level Lean model of Objects/longobject.c vs. the running CPython.

Usage: python3 difftest/longobj_diff.py [--cases N] [--seed S]

The generator aims at the branches of the C kernels: operands around every digit
boundary, the compact path, the KARATSUBA_CUTOFF and KARATSUBA_SQUARE_CUTOFF sizes, the
lopsided path, the add-back branch of Algorithm D, the _pylong division switch, every
shift split, and the exponent sizes that select each path of long_pow.

Exits non-zero on any mismatch. See difftest/common.py.
"""

import ctypes
import sys
import warnings

sys.set_int_max_str_digits(0)
warnings.simplefilter("ignore", DeprecationWarning)

import common

API = ctypes.pythonapi
for _name, _res in [("PyLong_AsLong", ctypes.c_long), ("PyLong_AsInt", ctypes.c_int),
                    ("PyLong_AsSsize_t", ctypes.c_ssize_t), ("PyLong_AsUnsignedLong", ctypes.c_ulong),
                    ("PyLong_AsSize_t", ctypes.c_size_t), ("PyLong_AsUnsignedLongMask", ctypes.c_ulong),
                    ("PyLong_AsUnsignedLongLongMask", ctypes.c_ulonglong)]:
    getattr(API, _name).restype = _res
    getattr(API, _name).argtypes = [ctypes.py_object]
API.PyLong_AsLongAndOverflow.restype = ctypes.c_long
API.PyLong_AsLongAndOverflow.argtypes = [ctypes.py_object, ctypes.POINTER(ctypes.c_int)]
API.PyLong_FromLongLong.restype = ctypes.py_object
API.PyLong_FromLongLong.argtypes = [ctypes.c_longlong]
API.PyLong_FromUnsignedLongLong.restype = ctypes.py_object
API.PyLong_FromUnsignedLongLong.argtypes = [ctypes.c_ulonglong]
for _name, _res in [("PyLong_AsLongLong", ctypes.c_longlong),
                    ("PyLong_AsUnsignedLongLong", ctypes.c_ulonglong),
                    ("PyLong_AsVoidPtr", ctypes.c_void_p)]:
    getattr(API, _name).restype = _res
    getattr(API, _name).argtypes = [ctypes.py_object]
API.PyLong_AsNativeBytes.restype = ctypes.c_ssize_t
API.PyLong_AsNativeBytes.argtypes = [ctypes.py_object, ctypes.c_void_p, ctypes.c_ssize_t, ctypes.c_int]
FIXED = {(4, False): ("PyLong_AsInt32", ctypes.c_int32), (8, False): ("PyLong_AsInt64", ctypes.c_int64),
         (4, True): ("PyLong_AsUInt32", ctypes.c_uint32), (8, True): ("PyLong_AsUInt64", ctypes.c_uint64)}
for (_n, _u), (_name, _ct) in FIXED.items():
    getattr(API, _name).restype = ctypes.c_int
    getattr(API, _name).argtypes = [ctypes.py_object, ctypes.POINTER(_ct)]
API.PyLong_GetSign.restype = ctypes.c_int
API.PyLong_GetSign.argtypes = [ctypes.py_object, ctypes.POINTER(ctypes.c_int)]

B = 1 << 30
P63, P64 = 1 << 63, 1 << 64


def digits(rng, n):
    """An n-digit magnitude, biased to all-ones and all-zero digits."""
    v = 0
    style = rng.randrange(4)
    for _ in range(n):
        if style == 0:
            d = rng.randrange(B)
        elif style == 1:
            d = rng.choice([0, 1, B - 1, B - 2, B >> 1, (B >> 1) - 1])
        elif style == 2:
            d = B - 1
        else:
            d = rng.choice([0, 0, 0, 1])
        v = (v << 30) | d
    return v


def edge_nat(rng, kind):
    if kind == "small":
        return rng.choice([0, 1, 2, 3, 4, 5, 256, 257, 258, B - 2, B - 1, B, B + 1, 2 * B - 1,
                           B * B - 1, B * B, P63 - 1, P63, P63 + 1, P64 - 1, P64, P64 + 1,
                           rng.randrange(1 << 20), rng.randrange(B), rng.randrange(1 << 64)])
    if kind == "digits":
        return digits(rng, rng.randrange(1, 12))
    if kind == "kara":
        return digits(rng, rng.choice([69, 70, 71, 72, 139, 140, 141, 142, 200, 300]))
    if kind == "huge":
        return digits(rng, rng.randrange(150, 900))
    raise ValueError(kind)


def edge_int(rng, kinds=("small", "small", "digits", "digits", "kara")):
    v = edge_nat(rng, rng.choice(kinds))
    if rng.random() < 0.1 and v > 0:
        v += rng.choice([-1, 1])
    return -v if rng.random() < 0.4 else v


def knuth_pair(rng):
    """Operands of x_divrem aimed at the q-hat correction and the add-back branch:
    a divisor with a top digit at BASE/2 and low digits at both extremes."""
    n = rng.randrange(2, 8)
    k = rng.randrange(0, 8)
    w = (B >> 1) + rng.choice([0, 0, 1, rng.randrange(B >> 1)])
    for _ in range(n - 1):
        w = (w << 30) | rng.choice([0, 1, B - 1, B - 2, rng.randrange(B)])
    v = rng.randrange(w) if rng.random() < 0.5 else w - 1
    for _ in range(k):
        v = (v << 30) | rng.choice([0, 1, B - 1, B - 2, rng.randrange(B)])
    return v, w


def gen_case(rng):
    fn = rng.choice(["add", "sub", "mul", "mul", "square", "divmod", "divmod", "floordiv", "mod",
                     "rshift", "lshift", "and", "or", "xor", "invert", "neg", "abs", "bool",
                     "pow", "powmod", "lopsided", "balanced", "balanced", "bigsquare", "knuth", "bigdiv",
                     "as_long_overflow", "as_long", "sizeof", "ratio", "int_info", "as_longlong",
                     "as_ulonglong", "void_ptr", "native", "native", "fixed",
                     "as_int", "as_ssize", "as_ulong", "as_size_t", "as_mask", "from_c", "get_sign",
                     "bit_length", "bit_count", "hash", "bool_repr", "bool_invert", "bool_op"])
    c = {"mod": "longobj", "fn": fn}
    if fn in ("add", "sub", "mul", "and", "or", "xor"):
        c["a"], c["b"] = edge_int(rng), edge_int(rng)
    elif fn in ("square", "invert", "neg", "abs", "bool", "get_sign", "bit_length", "bit_count",
                "hash", "sizeof", "ratio"):
        c["a"] = edge_int(rng)
    elif fn == "native":
        n = rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 16, 17])
        c["n"], c["ub"] = n, rng.random() < 0.5
        k = 8 * n + rng.choice([-2, -1, 0, 1, 2])
        v = (1 << k) + rng.choice([-1, 0, 0, 1])
        c["a"] = rng.choice([v, -v, edge_int(rng, ("small", "digits")), 1 << (8 * n - 1), -(1 << (8 * n - 1))])
    elif fn == "fixed":
        n, u = rng.choice([4, 8]), rng.random() < 0.5
        c["n"], c["ub"] = n, u
        k = 8 * n + rng.choice([-2, -1, 0, 1])
        v = (1 << k) + rng.choice([-1, 0, 1])
        c["a"] = rng.choice([v, -v, edge_int(rng, ("small", "digits"))])
    elif fn in ("as_long_overflow", "as_long", "as_int", "as_ssize", "as_ulong", "as_size_t", "as_mask",
                "as_longlong", "as_ulonglong", "void_ptr"):
        base = rng.choice([0, 1, B - 1, B, 1 << 31, (1 << 31) - 1, P63, P63 - 1, P64, P64 - 1, 1 << 90])
        v = base + rng.randrange(-2, 3)
        c["a"] = rng.choice([v, -v, edge_int(rng)])
    elif fn == "from_c":
        v = rng.choice([0, 1, 5, 6, 256, 257, B - 1, B, B + 1, 1 << 31, P63 - 1, rng.randrange(P63)])
        c["a"] = rng.choice([v, -v, P63, P64 - 1, -P63])
    elif fn in ("bool_repr", "bool_invert"):
        c["a"] = rng.random() < 0.5
    elif fn == "bool_op":
        c["op"] = rng.choice(["and", "or", "xor"])
        c["a"] = rng.choice([True, False, edge_int(rng), 0, 1])
        c["b"] = rng.choice([True, False, edge_int(rng), 0, 1])
    elif fn in ("divmod", "floordiv", "mod"):
        c["a"], c["b"] = edge_int(rng), edge_int(rng)
    elif fn == "lopsided":
        c["fn"] = "mul"
        n = rng.randrange(71, 110)
        c["a"] = digits(rng, n) * rng.choice([1, -1])
        c["b"] = digits(rng, rng.randrange(2 * n, 5 * n)) * rng.choice([1, -1])
    elif fn == "balanced":
        # the Karatsuba split itself: both operands above the cutoff, within a factor of two
        c["fn"] = "mul"
        n = rng.randrange(71, 320)
        c["a"] = digits(rng, n) * rng.choice([1, -1])
        c["b"] = digits(rng, rng.randrange(n, 2 * n)) * rng.choice([1, -1])
    elif fn == "bigsquare":
        c["fn"] = "square"
        c["a"] = digits(rng, rng.randrange(139, 420)) * rng.choice([1, -1])
    elif fn == "knuth":
        v, w = knuth_pair(rng)
        c["fn"] = rng.choice(["divmod", "floordiv", "mod"])
        c["a"], c["b"] = v * rng.choice([1, -1]), w * rng.choice([1, -1])
    elif fn == "bigdiv":
        c["fn"] = rng.choice(["divmod", "floordiv", "mod"])
        c["a"] = digits(rng, rng.randrange(450, 700)) * rng.choice([1, -1])
        c["b"] = (digits(rng, rng.randrange(290, 320)) + 1) * rng.choice([1, -1])
    elif fn == "rshift":
        c["a"] = edge_int(rng)
        c["b"] = rng.choice([0, 1, 29, 30, 31, 59, 60, 61, 90, rng.randrange(400), rng.randrange(-3, 3),
                             P63 - 1, P63, P64, 1 << 70])
    elif fn == "lshift":
        c["a"] = edge_int(rng)
        c["b"] = rng.choice([0, 1, 29, 30, 31, 59, 60, 61, 90, rng.randrange(400), rng.randrange(-3, 3)])
        if rng.random() < 0.05 and c["a"]:
            c["b"] = rng.choice([P63, P64, 1 << 70])
    elif fn == "pow":
        c["a"] = rng.choice([0, 1, -1, 2, -2, 3, 10, B - 1, rng.randrange(-50, 50)])
        c["b"] = rng.choice([0, 1, 2, 3, 4, 5, 7, 31, 32, 63, 64, 65, rng.randrange(120)])
    elif fn == "powmod":
        c["a"] = edge_int(rng, ("small", "digits"))
        c["c"] = rng.choice([0, 1, -1, 2, -2, 3, 7, B - 1, B, B + 1,
                             edge_int(rng, ("small", "digits")),
                             edge_int(rng, ("small", "digits"))])
        c["b"] = rng.choice([0, 1, 2, 3, 4, 5, 6, 7, 8, B - 1, B, B + 1, B * B - 1, B * B, B * B + 1,
                             digits(rng, 3), digits(rng, 4), rng.randrange(-5, 0),
                             digits(rng, rng.randrange(1, 4))])
    return c


def run_python(c):
    fn = c["fn"]
    a = c.get("a")
    b = c.get("b")

    def thunk():
        if fn == "add":
            return a + b
        if fn == "sub":
            return a - b
        if fn == "mul":
            return a * b
        if fn == "square":
            return a * a
        if fn == "divmod":
            return list(divmod(a, b))
        if fn == "floordiv":
            return a // b
        if fn == "mod":
            return a % b
        if fn == "rshift":
            return a >> b
        if fn == "lshift":
            return a << b
        if fn == "and":
            return a & b
        if fn == "or":
            return a | b
        if fn == "xor":
            return a ^ b
        if fn == "invert":
            return ~a
        if fn == "neg":
            return -a
        if fn == "abs":
            return abs(a)
        if fn == "bool":
            return bool(a)
        if fn == "pow":
            return a ** b
        if fn == "powmod":
            return pow(a, b, c["c"])
        if fn == "as_long_overflow":
            o = ctypes.c_int(0)
            r = API.PyLong_AsLongAndOverflow(a, ctypes.byref(o))
            return [r, o.value]
        if fn == "as_long":
            return API.PyLong_AsLong(a)
        if fn == "as_int":
            return API.PyLong_AsInt(a)
        if fn == "as_ssize":
            return API.PyLong_AsSsize_t(a)
        if fn == "as_ulong":
            return API.PyLong_AsUnsignedLong(a)
        if fn == "as_size_t":
            return API.PyLong_AsSize_t(a)
        if fn == "as_mask":
            x, y = API.PyLong_AsUnsignedLongMask(a), API.PyLong_AsUnsignedLongLongMask(a)
            assert x == y
            return x
        if fn == "as_longlong":
            return API.PyLong_AsLongLong(a)
        if fn == "as_ulonglong":
            return API.PyLong_AsUnsignedLongLong(a)
        if fn == "void_ptr":
            return API.PyLong_AsVoidPtr(a) or 0
        if fn == "native":
            n = c["n"]
            buf = (ctypes.c_ubyte * n)()
            r = API.PyLong_AsNativeBytes(a, buf, n, 1 | (4 if c["ub"] else 0))
            return [r, int.from_bytes(bytes(buf), "little")]
        if fn == "fixed":
            name, ct = FIXED[(c["n"], c["ub"])]
            out = ct(0)
            getattr(API, name)(a, ctypes.byref(out))
            return out.value
        if fn == "from_c":
            return API.PyLong_FromUnsignedLongLong(a) if a >= 0 else API.PyLong_FromLongLong(a)
        if fn == "get_sign":
            o = ctypes.c_int(9)
            API.PyLong_GetSign(a, ctypes.byref(o))
            return o.value
        if fn == "bit_length":
            return a.bit_length()
        if fn == "bit_count":
            return a.bit_count()
        if fn == "hash":
            return hash(a)
        if fn == "sizeof":
            return a.__sizeof__()
        if fn == "ratio":
            r = a.as_integer_ratio()
            return [r[0], r[1], a.real, a.imag, a.numerator, a.denominator, a.conjugate(),
                    a.__getnewargs__()[0], a.is_integer()]
        if fn == "int_info":
            return list(sys.int_info)
        if fn == "bool_repr":
            return repr(a)
        if fn == "bool_invert":
            return ~a
        if fn == "bool_op":
            return {"and": a & b, "or": a | b, "xor": a ^ b}[c["op"]]
        raise ValueError(fn)

    return common.py_result(thunk)


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
