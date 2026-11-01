"""Differential test for CoreLibs: Lean model vs the running CPython.

One section per area. `CORELIBS_AREA=coll,rand` restricts the run to those areas;
the default is every area that has a generator:
  scripts/r env CORELIBS_AREA=coll python3 difftest/corelibs_diff.py --cases 50000 --seed 1
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import main, py_result  # noqa: E402

# ====== BEGIN AREA coll (Lib/collections/__init__.py (everything except OrderedDict)) ======
# Everything for this area stays between these two markers; prefix top-level names with coll_.
coll_gen = None  # replace with def coll_gen(rng) -> case dict with "fn": "coll.<name>"
coll_run = None  # replace with def coll_run(case) -> common.py_result-style dict
# ====== END AREA coll ======

# ====== BEGIN AREA collabc (Lib/_collections_abc.py, Lib/collections/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with collabc_.
collabc_gen = None  # replace with def collabc_gen(rng) -> case dict with "fn": "collabc.<name>"
collabc_run = None  # replace with def collabc_run(case) -> common.py_result-style dict
# ====== END AREA collabc ======

# ====== BEGIN AREA functools (Lib/functools.py, Modules/_functoolsmodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with functools_.
functools_gen = None  # replace with def functools_gen(rng) -> case dict with "fn": "functools.<name>"
functools_run = None  # replace with def functools_run(case) -> common.py_result-style dict
# ====== END AREA functools ======

# ====== BEGIN AREA operator (Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with operator_.
operator_gen = None  # replace with def operator_gen(rng) -> case dict with "fn": "operator.<name>"
operator_run = None  # replace with def operator_run(case) -> common.py_result-style dict
# ====== END AREA operator ======

# ====== BEGIN AREA enumdc (Lib/enum.py, Lib/dataclasses.py) ======
# Everything for this area stays between these two markers; prefix top-level names with enumdc_.
enumdc_gen = None  # replace with def enumdc_gen(rng) -> case dict with "fn": "enumdc.<name>"
enumdc_run = None  # replace with def enumdc_run(case) -> common.py_result-style dict
# ====== END AREA enumdc ======

# ====== BEGIN AREA misc (Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py) ======
# Everything for this area stays between these two markers; prefix top-level names with misc_.
misc_gen = None  # replace with def misc_gen(rng) -> case dict with "fn": "misc.<name>"
misc_run = None  # replace with def misc_run(case) -> common.py_result-style dict
# ====== END AREA misc ======

# ====== BEGIN AREA calstat (Lib/calendar.py, Lib/statistics.py) ======
# Everything for this area stays between these two markers; prefix top-level names with calstat_.
calstat_gen = None  # replace with def calstat_gen(rng) -> case dict with "fn": "calstat.<name>"
calstat_run = None  # replace with def calstat_run(case) -> common.py_result-style dict
# ====== END AREA calstat ======

# ====== BEGIN AREA rand (Lib/random.py, Modules/_randommodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with rand_.
import _random as rand_c  # noqa: E402
import contextlib as rand_contextlib  # noqa: E402
import io as rand_io  # noqa: E402
import math as rand_math  # noqa: E402
import operator as rand_operator  # noqa: E402
import os as rand_os  # noqa: E402
import pickle as rand_pickle  # noqa: E402
import random as rand_random  # noqa: E402
import struct as rand_struct  # noqa: E402
import warnings as rand_warnings  # noqa: E402

rand_NAN_BITS = 0x7ff8000000000000


def rand_ienc(n):
    """JSON cannot carry ints past the 4300-digit limit: those cross as hex strings."""
    return n if abs(n) < 10**4000 else {"x": hex(n)}


def rand_idec(v):
    return int(v["x"], 16) if isinstance(v, dict) else v


def rand_bits(x):
    if x != x:
        return rand_NAN_BITS
    return rand_struct.unpack('<Q', rand_struct.pack('<d', x))[0]


def rand_float(b):
    return rand_struct.unpack('<d', rand_struct.pack('<Q', b))[0]


def rand_optf(b):
    return None if b is None else rand_float(b)


class rand_Sub(rand_random.Random):
    """Overrides random() only, so __init_subclass__ picks _randbelow_without_getrandbits."""

    def random(self):
        return super().random()


class rand_I(int):
    """An int subclass whose __abs__ must not be called (bpo-31478)."""

    def __abs__(self):
        raise RuntimeError("called")


class rand_H:
    def __init__(self, h):
        self.h = h

    def __hash__(self):
        return self.h


class rand_BadMod:
    """__mod__ raises ValueError, the only way into Lib/random.py:194."""

    def __mod__(self, other):
        raise ValueError("no")


def rand_mk(case):
    cls = rand_Sub if case.get("sub") else rand_random.Random
    r = cls(rand_idec(case.get("seed", 0)))
    for _ in range(case.get("burn", 0)):
        rand_c.Random.getrandbits(r, 32)
    return r


def rand_fp(r):
    st = rand_c.Random.getstate(r)
    return [st[624], st[0], st[311], st[623], rand_c.Random.getrandbits(r, 32)]


def rand_py(thunk):
    res = py_result(thunk)
    if "exc" in res:
        m = res["msg"]
        if res["exc"] == "ValueError" and (m.startswith("expected ") or m == "math domain error"):
            res["msg"] = "~domain"
        if res["exc"] == "UnicodeEncodeError":
            res["msg"] = "~surrogate"
    return res


def rand_wrap(res, r):
    return {"ok": {"r": res, "fp": rand_fp(r)}}


def rand_obj(ty):
    return {"float": 1.5, "NoneType": None, "str": "a", "bytes": b"x", "list": [1], "BadMod": rand_BadMod()}[ty]


def rand_arg(d):
    if "i" in d:
        return rand_idec(d["i"])
    if "b" in d:
        return d["b"]
    return rand_obj(d["o"])


def rand_elems(xs):
    return [rand_obj(x) if isinstance(x, str) else x for x in xs]


def rand_num(d):
    return rand_float(d["f"]) if "f" in d else rand_idec(d["i"])


def rand_call(case, thunk):
    r = rand_mk(case)
    return rand_wrap(rand_py(lambda: thunk(r)), r)


def rand_f(case, name, *keys):
    args = [rand_float(case[k]) for k in keys]
    return rand_call(case, lambda r: rand_bits(getattr(r, name)(*args)))


def rand_stub(r):
    real = rand_os.urandom

    def stub(n):
        if not isinstance(n, int) or n < 0 or n >= 2**20:
            return real(n)
        return bytes(rand_c.Random.getrandbits(r, 32) >> 24 for _ in range(n))
    return stub


def rand_sys(case, thunk):
    r = rand_mk(case)
    sr = rand_random.SystemRandom()
    saved = rand_random._urandom
    rand_random._urandom = rand_stub(r)
    try:
        res = rand_py(lambda: thunk(sr))
    finally:
        rand_random._urandom = saved
    return rand_wrap(res, r)


def rand_carg(case):
    k = case["kind"]
    if k == "int":
        return rand_idec(case["n"])
    if k == "intsub":
        return rand_I(rand_idec(case["n"]))
    if k == "hash":
        return rand_H(case["h"])
    return [1]


def rand_seedobj(case):
    k = case["kind"]
    if k == "none":
        return None
    if k == "int":
        return rand_idec(case["n"])
    if k == "intsub":
        return case["obj_bool"] if "obj_bool" in case else rand_I(rand_idec(case["n"]))
    if k == "float":
        return rand_float(case["x"])
    if k == "str":
        return ''.join(map(chr, case["b"]))
    if k == "bytes":
        return bytes(case["b"])
    if k == "bytearray":
        return bytearray(case["b"])
    return (1, 2)


def rand_h_cseed(c):
    r = rand_mk(c)
    return rand_wrap(rand_py(lambda: rand_c.Random.seed(r, rand_carg(c))), r)


def rand_h_cinit(c):
    r = rand_mk(c)
    res = {"ok": None}
    try:
        o = rand_c.Random(rand_carg(c))
    except Exception as e:
        res = {"exc": type(e).__name__, "msg": str(e)}
        o = r
    return rand_wrap(res, o)


def rand_h_getstate(c):
    r = rand_mk(c)
    acc = 0
    for i, x in enumerate(rand_c.Random.getstate(r)):
        acc = (acc + x * (i + 1)) % (2**61 - 1)
    return rand_wrap({"ok": acc}, r)


def rand_h_csetstate(c):
    r = rand_mk(c)
    st = tuple(rand_elems(c["xs"])) if c["ikind"] == "tuple" else list(rand_elems(c["xs"]))
    return rand_wrap(rand_py(lambda: rand_c.Random.setstate(r, st)), r)


def rand_state(c):
    sk = c["skind"]
    if sk == "notsub":
        return 3 if c["sty"] == "int" else None
    if sk == "emptytuple":
        return ()
    if sk == "emptylist":
        return []
    ik = c["ikind"]
    if ik == "tuple":
        inner = tuple(rand_elems(c["xs"]))
    elif ik == "list":
        inner = rand_elems(c["xs"])
    else:
        inner = 5
    full = (c["vobj"], inner, rand_optf(c.get("gauss")), 0, 0)
    return full[:c["len"]]


def rand_obj_result(res, r):
    g = r.gauss_next
    return {"ok": {"v": rand_wrap(res, r), "o": {"gauss": None if g is None else rand_bits(g)}}}


def rand_h_pysetstate(c):
    r = rand_mk(c)
    r.gauss_next = rand_optf(c.get("gauss0"))
    st = rand_state(c)
    return rand_obj_result(rand_py(lambda: r.setstate(st)), r)


def rand_h_pyseed(c):
    r = rand_mk(c)
    r.gauss_next = 1.5
    x = rand_seedobj(c)
    return rand_obj_result(rand_py(lambda: r.seed(x, version=c["version"])), r)


def rand_h_pickle(c):
    r = rand_mk(c)
    r.gauss_next = rand_optf(c.get("gauss0"))
    r2 = rand_pickle.loads(rand_pickle.dumps(r))
    return rand_obj_result({"ok": None}, r2)


def rand_h_new(c):
    o = rand_c.Random.__new__(rand_c.Random)
    for _ in range(c["skip"]):
        o.getrandbits(32)
    words = [o.getrandbits(32) for _ in range(c["n"])]
    return rand_wrap({"ok": words}, o)


def rand_h_time_pid(c):
    now, mono, pid = c["now"], c["mono"], c["pid"]
    key = [now & 0xffffffff, (now >> 32) & 0xffffffff, pid & 0xffffffff,
           mono & 0xffffffff, (mono >> 32) & 0xffffffff]
    o = rand_c.Random(sum(w << (32 * i) for i, w in enumerate(key)))
    return rand_wrap({"ok": key}, o)


def rand_randrange(r, c):
    kw = {}
    if "stop" in c and c["stop"] is not None:
        kw["stop"] = rand_arg(c["stop"])
    if "step" in c and c["step"] is not None:
        kw["step"] = rand_arg(c["step"])
    return r.randrange(rand_arg(c["start"]), **kw)


def rand_shuffle(r, c):
    imm = c.get("imm")
    if imm == "tuple":
        r.shuffle(tuple(c["x"]))
        return c["x"]
    if imm == "str":
        r.shuffle(''.join(map(str, c["x"])))
        return c["x"]
    y = list(c["x"])
    r.shuffle(y)
    return y


def rand_sample(r, c):
    pop = set(c["pop"]) if c["seqkind"] == "set" else list(c["pop"])
    counts = c.get("counts")
    if isinstance(counts, str):
        counts = rand_obj(counts) if counts != "int" else 5
    elif counts is not None:
        counts = [1.5 if x is None else x for x in counts]
    return r.sample(pop, c["k"], counts=counts)


def rand_choices(r, c):
    pop = list(c["pop"])
    w = c["weights"]
    if isinstance(w, dict):
        w = rand_arg(w["wint"]) if "wint" in w else rand_obj(w["wother"])
    elif w is not None:
        w = [rand_num(x) for x in w]
    cum = c["cum"]
    if cum is not None:
        cum = [rand_num(x) for x in cum]
    return r.choices(pop, w, cum_weights=cum, k=c["k"])


def rand_h_gauss(c):
    def go(r):
        r.gauss_next = rand_optf(c.get("gauss0"))
        v = r.gauss(rand_float(c["a"]), rand_float(c["b"]))
        n = r.gauss_next
        return {"v": rand_bits(v), "next": None if n is None else rand_bits(n)}
    return rand_call(c, go)


def rand_h_without(c):
    def go(r):
        with rand_warnings.catch_warnings():
            rand_warnings.simplefilter("ignore")
            return r._randbelow_without_getrandbits(c["n"])
    return rand_call(c, go)


rand_warnings.filterwarnings("ignore", message="Underlying random", category=UserWarning)


def rand_setsize(k):
    s = 21
    if k > 5:
        s += 4 ** rand_math.ceil(rand_math.log(k * 3, 4))
    return s


def rand_h_init_subclass(c):
    made, out = [], []
    for i, spec in enumerate(c["classes"]):
        d = {}
        if spec.get("rb"):
            d["_randbelow"] = lambda self, n: 0
            d["_randbelow"].__name__ = spec["rb"]
        if spec["gb"]:
            d["getrandbits"] = lambda self, k: 0
        if spec["rnd"]:
            d["random"] = lambda self: 0.0
        bases = tuple(rand_random.Random if b == -1 else made[b] for b in spec["bases"])
        cls = type(f"C{i}", bases, d)
        made.append(cls)
        f = getattr(cls, "_randbelow", None)
        out.append(f.__name__ if f is not None else None)
    return {"ok": {"r": {"ok": out}, "fp": rand_fp(rand_mk(c))}}


def rand_h_main(c):
    r = rand_random._inst
    r.seed(rand_idec(c.get("seed", 0)))
    for _ in range(c.get("burn", 0)):
        rand_c.Random.getrandbits(r, 32)

    def go():
        out = rand_random.main(c["argv"])
        if isinstance(out, float):
            return {"f": rand_bits(out)}
        if isinstance(out, int):
            return {"i": rand_ienc(out)}
        if out.startswith("usage:"):
            return {"s": "HELP"}
        return {"s": out}
    return rand_wrap(rand_py(go), r)


rand_handlers = {
    "words": lambda c: rand_call(c, lambda r: [r.getrandbits(32) for _ in range(c["n"])]),
    "random": lambda c: rand_call(c, lambda r: (lambda xs: {"bits": [rand_bits(x) for x in xs],
                                                            "nums": [int(x * 2**53) for x in xs]})(
        [r.random() for _ in range(c["n"])])),
    "getrandbits": lambda c: rand_call(c, lambda r: rand_ienc(r.getrandbits(rand_arg(c["k"])))),
    "cseed": rand_h_cseed,
    "cinit": rand_h_cinit,
    "getstate": rand_h_getstate,
    "csetstate": rand_h_csetstate,
    "pysetstate": rand_h_pysetstate,
    "pyseed": rand_h_pyseed,
    "pickle": rand_h_pickle,
    "new": rand_h_new,
    "time_pid": rand_h_time_pid,
    "randbelow_with": lambda c: rand_call(c, lambda r: r._randbelow_with_getrandbits(c["n"])),
    "randbelow_without": rand_h_without,
    "randbytes": lambda c: rand_call(c, lambda r: list(r.randbytes(rand_arg(c["n"])))),
    "randrange": lambda c: rand_call(c, lambda r: rand_ienc(rand_randrange(r, c))),
    "randint": lambda c: rand_call(c, lambda r: rand_ienc(r.randint(rand_arg(c["a"]), rand_arg(c["b"])))),
    "choice": lambda c: rand_call(c, lambda r: r.choice(c["pop"])),
    "choice_obj": lambda c: rand_call(c, lambda r: r.choice(dict(zip(c["keys"], c["vals"])))),
    "shuffle": lambda c: rand_call(c, lambda r: rand_shuffle(r, c)),
    "sample": lambda c: rand_call(c, lambda r: rand_sample(r, c)),
    "sample_range": lambda c: rand_call(c, lambda r: r.sample(range(c["n"]), c["k"])),
    "setsize": lambda c: rand_call(c, lambda r: rand_setsize(c["k"])),
    "choices": lambda c: rand_call(c, lambda r: rand_choices(r, c)),
    "uniform": lambda c: rand_f(c, "uniform", "a", "b"),
    "triangular": lambda c: rand_call(c, lambda r: rand_bits(r.triangular(
        rand_float(c["a"]), rand_float(c["b"]), rand_optf(c.get("c"))))),
    "normalvariate": lambda c: rand_f(c, "normalvariate", "a", "b"),
    "gauss": rand_h_gauss,
    "lognormvariate": lambda c: rand_f(c, "lognormvariate", "a", "b"),
    "expovariate": lambda c: rand_f(c, "expovariate", "a"),
    "vonmisesvariate": lambda c: rand_f(c, "vonmisesvariate", "a", "b"),
    "gammavariate": lambda c: rand_f(c, "gammavariate", "a", "b"),
    "betavariate": lambda c: rand_f(c, "betavariate", "a", "b"),
    "paretovariate": lambda c: rand_f(c, "paretovariate", "a"),
    "weibullvariate": lambda c: rand_f(c, "weibullvariate", "a", "b"),
    "binomialvariate": lambda c: rand_call(c, lambda r: r.binomialvariate(c["n"], rand_float(c["p"]))),
    "sys_random": lambda c: rand_sys(c, lambda sr: rand_bits(sr.random())),
    "sys_getrandbits": lambda c: rand_sys(c, lambda sr: rand_ienc(sr.getrandbits(rand_arg(c["k"])))),
    "sys_randbytes": lambda c: rand_sys(c, lambda sr: list(sr.randbytes(rand_arg(c["n"])))),
    "sys_randrange": lambda c: rand_sys(c, lambda sr: rand_ienc(rand_randrange(sr, c))),
    "sys_seed": lambda c: rand_sys(c, lambda sr: sr.seed(1, 2, x=3)),
    "sys_state": lambda c: rand_sys(c, lambda sr: sr.getstate()),
    "init_subclass": rand_h_init_subclass,
    "main": rand_h_main,
}


def rand_run(case):
    return rand_handlers[case["fn"].split(".", 1)[1]](case)


rand_INTS = [0, 1, -1, 2, -2, 3, 7, 8, 31, 32, 33, 63, 64, 65, 255, 256, 1000, 2**31 - 1, 2**31, 2**32 - 1,
             2**32, 2**32 + 1, 2**53 - 1, 2**53, 2**53 + 1, 2**63 - 1, 2**63, -2**63, 2**64 - 1, 2**64, -2**64,
             2**128 + 5, 10**30, -10**30, 10**4300 - 1, 10**4300, -10**4300]
rand_SMALL_FLOATS = [0.0, -0.0, 1.0, -1.0, 0.5, 2.0, 3.0, 10.0, 1e-3, 0.25, 0.9, 1.5, 100.0, 1e-300, 1e300]
rand_ALL_FLOATS = rand_SMALL_FLOATS + [float('inf'), float('-inf'), float('nan'), 5e-324, 1.7976931348623157e308]


def rand_seed_val(rng):
    if rng.random() < 0.7:
        return rng.getrandbits(rng.choice([8, 32, 64, 256]))
    return rand_ienc(rng.choice([0, 1, -1, 2, 42, 2**32 - 1, 2**32, 2**32 + 1, 2**64 - 1, 2**64, -2**64, 2**63,
                                 2**128 + 5, (1 << 2000) + 3, (1 << 20000) + 1, 2**31, 2**19937 - 1]))


def rand_burn(rng):
    return rng.choice([0, 0, 1, 2, 3, 623, 624, 625, 1247, 1248, rng.randrange(1400)])


def rand_base(rng, name):
    return {"fn": "rand." + name, "seed": rand_seed_val(rng), "burn": rand_burn(rng)}


def rand_intarg(rng, vals=None, others=("float", "NoneType", "str", "bytes")):
    p = rng.random()
    if p < 0.05:
        return {"b": rng.random() < 0.5}
    if p < 0.1:
        return {"o": rng.choice(others)}
    if vals is not None and rng.random() < 0.5:
        return {"i": rand_ienc(rng.choice(vals))}
    if rng.random() < 0.5:
        return {"i": rand_ienc(rng.choice(rand_INTS))}
    return {"i": rng.randrange(-300, 301)}


def rand_clamp(d, lo, hi, *big):
    """Keep ints in [lo, hi] or among `big`, so that no case tries a huge allocation that may succeed."""
    if "i" not in d:
        return d
    v = rand_idec(d["i"])
    if v in big or v <= hi:
        return d
    return {"i": rand_ienc(big[int(v) % len(big)])}


def rand_pos(rng):
    p = rng.random()
    if p < 0.4:
        return rng.randrange(1, 300)
    if p < 0.7:
        return 1 << rng.randrange(1, 130)
    if p < 0.85:
        return (1 << rng.randrange(1, 130)) + rng.randrange(-1, 2) + 1
    return rng.getrandbits(rng.randrange(1, 200)) + 1


def rand_pop(rng, n=None):
    if n is None:
        n = rng.choice([0, 1, 2, 3, 5, 6, 7, 21, 22, 40, rng.randrange(120)])
    return [rng.randrange(1000) for _ in range(n)]


def rand_gen_core(rng, c):
    fn = c["fn"]
    if fn == "rand.words":
        c["n"] = rng.choice([1, 2, 3, 623, 624, 625, 1300])
    elif fn == "rand.random":
        c["n"] = rng.choice([1, 2, 3, 312, 313])
    elif fn == "rand.getrandbits":
        c["k"] = rand_intarg(rng, [0, 1, 2, 31, 32, 33, 63, 64, 65, 95, 96, 97, 1000, 19937, -1,
                                   2**64 - 1, 2**64, -2**64, 2**60, 2**63], ("float", "NoneType", "str"))
        c["k"] = rand_clamp(c["k"], 0, 2**20, 2**64 - 1, 2**63, 2**64, 2**60, 2**128)
    elif fn in ("rand.cseed", "rand.cinit"):
        k = rng.choice(["int", "int", "intsub", "hash", "unhashable"])
        c["kind"] = k
        if k in ("int", "intsub"):
            c["n"] = rand_seed_val(rng)
        elif k == "hash":
            c["h"] = rng.choice([0, 1, -2, 2**63 - 1, -2**63, rng.getrandbits(63), -rng.getrandbits(63) - 2])
        else:
            c["ty"] = "list"
    elif fn == "rand.time_pid":
        c["now"] = rng.choice([0, 1, -1, 1 << 62, -(1 << 62), rng.getrandbits(62), -rng.getrandbits(62)])
        c["mono"] = rng.getrandbits(62) | (1 << 40)
        c["pid"] = rng.getrandbits(32) + 1
    elif fn == "rand.new":
        c["n"] = rng.choice([1, 3, 700])
        c["skip"] = rng.choice([0, 1, 623, 624, 625, 1300])


def rand_state_xs(rng, c):
    base = list(rand_random.Random(rand_idec(c["seed"])).getstate()[1])
    n = rng.random()
    if n < 0.1:
        base = base[:rng.choice([0, 1, 624])]
    elif n < 0.15:
        base = base + [0]
    elif n < 0.5:
        base[624] = rng.choice([-1, 0, 1, 311, 623, 624, 625, 2**31, 2**63 - 1, 2**63, -2**63 - 1, 2**64,
                                "float", "NoneType"])
    elif n < 0.8:
        i = rng.choice([0, 1, 311, 623])
        base[i] = rng.choice([-1, 2**32 - 1, 2**32, 2**64 - 1, 2**64, -2**64, "float", "NoneType"])
    return base


def rand_gen_state(rng, c):
    fn = c["fn"]
    if fn == "rand.csetstate":
        c["ikind"] = rng.choice(["tuple"] * 5 + ["list"])
        c["xs"] = rand_state_xs(rng, c)
    elif fn == "rand.pysetstate":
        c["gauss0"] = rng.choice([None, rand_bits(0.25)])
        p = rng.random()
        if p < 0.05:
            c["skind"] = "notsub"
            c["sty"] = rng.choice(["int", "NoneType"])
        elif p < 0.1:
            c["skind"] = rng.choice(["emptytuple", "emptylist"])
        else:
            c["skind"] = "seq"
            c["len"] = rng.choice([3, 3, 3, 3, 3, 3, 1, 2, 4, 5])
            vobj, vval = rng.choice([(3, 3), (3, 3), (3, 3), (2, 2), (2, 2), (3.0, 3), (2.0, 2), (1, 1), (0, 0),
                                     (True, 1), (4, 4), ("3", None), ("x", None), (2.5, None)])
            c["vobj"], c["vval"], c["vtext"] = vobj, vval, str(vobj)
            c["ikind"] = rng.choice(["tuple", "tuple", "tuple", "list", "other"])
            c["ity"] = "int"
            c["gauss"] = rng.choice([None, rand_bits(1.5)])
            c["xs"] = rand_state_xs(rng, c)
            if vval == 2 and rng.random() < 0.3:
                i = rng.randrange(625) if c["xs"] else 0
                if c["xs"]:
                    c["xs"][i % len(c["xs"])] = rng.choice(["BadMod", "NoneType", "float", -1, -2**70, 2**70])
    elif fn == "rand.pickle":
        c["gauss0"] = rng.choice([None, rand_bits(0.25)])
    elif fn == "rand.pyseed":
        c["version"] = rng.choice([2, 2, 2, 1, 1, 0, 3])
        k = rng.choice(["none_skip", "int", "intsub", "float", "str", "bytes", "bytearray", "other"])
        if k == "none_skip":
            k = "int"
        c["kind"] = k
        if k in ("int", "intsub"):
            c["n"] = rand_seed_val(rng)
            if k == "intsub" and rng.random() < 0.3:
                c["n"] = 1
                c["obj_bool"] = True
        elif k == "float":
            x = rng.choice(rand_SMALL_FLOATS + [rng.random(), float('inf'), float('-inf')])
            c["x"] = rand_bits(x)
            c["h"] = hash(x)
        elif k in ("str", "bytes", "bytearray"):
            n = rng.choice([0, 1, 2, 3, 55, 111, 112, 127, 128, 129, 300])
            top = 256 if k != "str" else rng.choice([128, 256, 0x800, 0x10000, 0x110000])
            b = [rng.randrange(top) for _ in range(n)]
            if k == "str" and rng.random() < 0.1 and b:
                b[rng.randrange(n)] = rng.randrange(0xD800, 0xE000)
            elif k == "str":
                b = [x if not 0xD800 <= x < 0xE000 else 65 for x in b]
            c["b"] = b
            if k == "str":
                c["h"] = hash(''.join(map(chr, b)))
            elif k == "bytes":
                c["h"] = hash(bytes(b))


def rand_gen_exact(rng, c):
    fn = c["fn"]
    c["sub"] = rng.random() < 0.3 and fn in ("rand.randrange", "rand.randint", "rand.choice", "rand.shuffle",
                                             "rand.sample", "rand.sample_range", "rand.main")
    if fn == "rand.randbelow_with":
        c["n"] = rand_pos(rng)
    elif fn == "rand.randbelow_without":
        c["n"] = rand_pos(rng) if rng.random() < 0.8 else rng.choice([2**53 - 1, 2**53, 2**53 + 1, 2**60, 10**400])
    elif fn == "rand.randbytes":
        c["n"] = rand_intarg(rng, [0, 1, 2, 3, 4, 5, 7, 8, 9, 16, 1000, -1, 2**61, 2**62, 2**64])
        c["n"] = rand_clamp(c["n"], 0, 2**17, 2**61, 2**62, 2**64)
    elif fn == "rand.randrange":
        c["start"] = rand_intarg(rng)
        if rng.random() < 0.8:
            c["stop"] = rand_intarg(rng)
            if rng.random() < 0.6:
                c["step"] = rand_intarg(rng, [1, -1, 2, -2, 0, 3, 10, 2**64, -2**64, 2**100])
        elif rng.random() < 0.3:
            c["step"] = rand_intarg(rng, [1, 1, 2])
    elif fn == "rand.randint":
        c["a"] = rand_intarg(rng)
        c["b"] = rand_intarg(rng)
    elif fn == "rand.choice":
        c["pop"] = rand_pop(rng)
    elif fn == "rand.choice_obj":
        c["keys"] = rng.choice([[0, 1], [0, 2], [5], [1, 0, 2], [0]])
        c["vals"] = [rng.randrange(100) for _ in c["keys"]]
    elif fn == "rand.shuffle":
        c["x"] = rand_pop(rng)
        if rng.random() < 0.15:
            c["imm"] = rng.choice(["tuple", "str"])
            c["x"] = [rng.randrange(10) for _ in range(rng.choice([0, 1, 2, 3, 9]))]
    elif fn == "rand.sample":
        c["pop"] = rand_pop(rng)
        c["seqkind"] = rng.choice(["list"] * 19 + ["set"])
        n = len(c["pop"])
        p = rng.random()
        c["k"] = rng.choice([-1, 0, 1, n - 1, n, n + 1, rng.randrange(n + 1), rng.randrange(n + 1), 5, 6, 7])
        if p < 0.4:
            q = rng.random()
            if q < 0.03:
                c["counts"] = "int"
            elif q < 0.06:
                c["counts"] = [1] * (n + 1)
            elif q < 0.5:
                c["counts"] = [rng.randrange(6) for _ in range(n)]
                c["k"] = rng.randrange(sum(c["counts"]) + 2)
            elif q < 0.7:
                c["counts"] = [rng.randrange(-3, 6) for _ in range(n)]
                c["k"] = rng.randrange(0, max(1, sum(c["counts"]) + 2))
            elif q < 0.8:
                c["counts"] = [rng.choice([None, 1, 2]) for _ in range(n)]
            elif q < 0.9:
                c["counts"] = [2**rng.randrange(62, 66) for _ in range(n)]
                c["k"] = rng.randrange(0, 5)
            else:
                c["counts"] = [rng.randrange(40) for _ in range(n)]
                c["k"] = rng.randrange(0, max(1, sum(c["counts"])))
    elif fn == "rand.sample_range":
        c["n"] = rng.choice([0, 1, 21, 22, 40, 100, 1000, 10**6, 2**31, 2**62, 2**63 - 1, 2**63, 2**64, 10**30])
        c["k"] = rng.choice([0, 1, 2, 5, 6, 7, 20, 21, 22, 30, 100, 300])
    elif fn == "rand.setsize":
        c["k"] = rng.choice([0, 1, 5, 6, 7, 8, 21, 22, 85, 86, 341, 342, 1365, 1366, 5461, 5462,
                             rng.randrange(10**6), rng.randrange(2**40), (4**rng.randrange(1, 20) + 2) // 3,
                             (4**rng.randrange(1, 20) - 1) // 3])
    elif fn == "rand.choices":
        c["pop"] = rand_pop(rng)
        c["seqkind"] = "list"
        n = len(c["pop"])
        c["k"] = rng.choice([-1, 0, 1, 2, 5, 20])
        c["weights"], c["cum"] = None, None
        p = rng.random()

        def num():
            q = rng.random()
            if q < 0.5:
                return {"i": rng.randrange(0, 6)}
            if q < 0.9:
                return {"f": rand_bits(rng.choice([0.0, 0.5, 1.5, 1e-3, rng.random()]))}
            return rng.choice([{"i": -1}, {"i": 2**70}, {"i": 10**400}, {"f": rand_bits(float('inf'))},
                               {"f": rand_bits(float('nan'))}, {"f": rand_bits(-0.5)}])
        if p < 0.3:
            pass
        elif p < 0.6:
            c["weights"] = [num() for _ in range(n)]
        elif p < 0.8:
            acc, cum = 0, []
            for _ in range(n):
                acc += rng.randrange(0, 4)
                cum.append({"i": acc})
            c["cum"] = cum
        elif p < 0.9:
            c["cum"] = [num() for _ in range(n)]
        elif p < 0.93:
            c["weights"] = [num() for _ in range(n + 1)]
        elif p < 0.96:
            c["weights"] = {"wint": rng.choice([{"i": 2}, {"b": True}])}
        elif p < 0.98:
            c["weights"] = {"wother": "float"}
        else:
            c["weights"] = [{"i": 1} for _ in range(n)]
            c["cum"] = [{"i": 1} for _ in range(n)]


def rand_gen_dist(rng, c):
    fn = c["fn"]

    def f(pool=rand_ALL_FLOATS):
        return rand_bits(rng.choice(pool + [rng.uniform(-5, 5)]))

    def pos(pool=(0.01, 0.1, 0.5, 0.9, 1.0, 1.0, 1.1, 2.0, 3.5, 20.0, 200.0, 1e4, 1e-3, 1e-5, 1e300)):
        return rand_bits(rng.choice(list(pool) + [rng.random() + 1e-3, rng.uniform(1, 50)]))
    if fn in ("rand.uniform", "rand.normalvariate", "rand.lognormvariate", "rand.gauss"):
        c["a"], c["b"] = f(), f()
        if fn == "rand.gauss":
            c["gauss0"] = rng.choice([None, None, rand_bits(0.75)])
    elif fn == "rand.triangular":
        c["a"], c["b"] = f(), f()
        c["c"] = rng.choice([None, c["a"], c["b"], f()])
    elif fn in ("rand.expovariate", "rand.paretovariate"):
        c["a"] = f()
    elif fn == "rand.weibullvariate":
        c["a"], c["b"] = f(), f()
    elif fn == "rand.vonmisesvariate":
        c["a"] = f()
        c["b"] = rand_bits(rng.choice([0.0, 1e-7, 1e-6, 2e-6, 0.5, 1.0, 4.0, 100.0, 1e6, -1.0, float('inf')]))
    elif fn == "rand.gammavariate":
        c["a"], c["b"] = pos(), pos()
        if rng.random() < 0.15:
            c["a"] = rand_bits(rng.choice([0.0, -1.0, -0.0]))
        elif rng.random() < 0.15:
            c["b"] = rand_bits(rng.choice([0.0, -1.0, float('nan'), float('inf')]))
    elif fn == "rand.betavariate":
        c["a"], c["b"] = pos(), pos()
        if rng.random() < 0.05:
            c["b"] = rand_bits(-1.0)
    elif fn == "rand.binomialvariate":
        c["n"] = rng.choice([-1, 0, 1, 2, 3, 10, 19, 20, 21, 100, 1000, 10**6, 10**15, 2**53, 2**64, 10**400])
        c["p"] = rand_bits(rng.choice([0.0, -0.0, 1.0, 0.5, 0.1, 0.9, 1e-9, 1 - 1e-9, 0.3, 0.7, 1.5, -0.1, 1e-20,
                                       float('nan'), float('inf'), rng.random()]))


def rand_gen_sys(rng, c):
    fn = c["fn"]
    if fn == "rand.sys_getrandbits":
        c["k"] = rand_intarg(rng, [0, 1, 7, 8, 9, 16, 17, -1, 2**70], ("float", "NoneType", "str"))
        c["k"] = rand_clamp(c["k"], 0, 2**15, 2**70)
    elif fn == "rand.sys_randbytes":
        c["n"] = rand_intarg(rng, [0, 1, 2, 7, 8, -1, 2**70], ("float", "NoneType", "str"))
        c["n"] = rand_clamp(c["n"], 0, 2**15, 2**70)
    elif fn == "rand.sys_randrange":
        c["start"] = {"i": rand_pos(rng) if rng.random() < 0.8 else rng.choice([0, -1])}
        if rng.random() < 0.5:
            c["stop"] = {"i": c["start"]["i"] + rng.randrange(-1, 100)}
            if rng.random() < 0.2:
                c["start"] = {"i": 5000}


def rand_gen_subclass(rng, c):
    specs, made = [], []
    for i in range(rng.randrange(1, 6)):
        mixin = rng.random() < 0.25
        if mixin or not made:
            bases = [] if mixin else [-1]
        else:
            k = rng.randrange(1, min(3, len(made)) + 1)
            bases = rng.sample(range(len(made)), k)
            if rng.random() < 0.3:
                bases.insert(rng.randrange(len(bases) + 1), -1)
        spec = {"bases": bases, "mixin": mixin, "gb": rng.random() < 0.3, "rnd": rng.random() < 0.3}
        if not mixin and rng.random() < 0.15:
            spec["rb"] = f"custom{i}"
        d = {}
        for name, flag in (("getrandbits", spec["gb"]), ("random", spec["rnd"]), ("_randbelow", spec.get("rb"))):
            if flag:
                d[name] = lambda self, *a: 0
        try:
            cls = type(f"G{i}", tuple(rand_random.Random if b == -1 else made[b] for b in bases), d)
        except TypeError:
            return None
        made.append(cls)
        mro = []
        for k_ in cls.__mro__:
            if k_ is rand_random.Random:
                break
            if k_ is not object:
                mro.append(made.index(k_))
        spec["mro"] = mro
        spec["random"] = issubclass(cls, rand_random.Random)
        specs.append(spec)
    c["classes"] = specs
    return c


def rand_gen_main(rng, c):
    p = rng.random()
    if p < 0.5:
        val = rng.choice(["0", "-5", "1", "5", "10", "1.5", "-1.5", "0.0", "1e3", "inf", "nan", "-inf", "a b c", "abc",
                          " ", "", "  x  ", "1_000", "-1", "-" + "1" + "0" * 400, "1" + "0" * 400, "1" + "0" * 5000,
                          str(rng.randrange(-20, 200)), str(rng.uniform(-3, 3))])
        argv = ["--", val] if val.startswith("-") and rng.random() < 0.5 else [val]
    elif p < 0.65:
        argv = [rng.choice(["a", "b", "1", "2.5"]) for _ in range(rng.randrange(2, 6))]
    elif p < 0.75:
        argv = [rng.choice(["-c", "--choice"])] + [rng.choice(["a", "b", "c"]) for _ in range(rng.randrange(1, 5))]
    elif p < 0.85:
        argv = [rng.choice(["-i", "--integer"]), str(rng.choice([0, 1, 5, -3, 100]))]
    elif p < 0.93:
        argv = [rng.choice(["-f", "--float"]), rng.choice(["0", "1.5", "-2.5", "100"])]
    elif p < 0.97:
        argv = []
    else:
        argv = ["--test", "0", rng.choice(["5", "a"])]
    c["argv"] = argv
    try:
        with rand_contextlib.redirect_stderr(rand_io.StringIO()):
            args, _ = rand_random._parse_args(argv)
    except SystemExit:
        return None

    def inp(x):
        try:
            ai = int(x)
        except ValueError:
            ai = None
        try:
            af = rand_bits(float(x))
        except ValueError:
            af = None
        return {"asint": ai, "asfloat": af, "words": x.split()}
    c["choice"] = args.choice
    c["integer"] = args.integer
    c["float"] = None if args.float is None else rand_bits(args.float)
    c["test"] = args.test
    c["input"] = [inp(x) for x in args.input]
    c["inputstrs"] = list(args.input)
    return c


rand_GROUPS = {
    rand_gen_core: ["words", "random", "getrandbits", "cseed", "cinit", "getstate", "new", "time_pid"],
    rand_gen_state: ["csetstate", "pysetstate", "pyseed", "pickle"],
    rand_gen_exact: ["randbelow_with", "randbelow_without", "randbytes", "randrange", "randrange", "randint",
                     "choice", "choice_obj", "shuffle", "sample", "sample", "sample", "sample_range", "setsize",
                     "choices", "choices"],
    rand_gen_dist: ["uniform", "triangular", "normalvariate", "gauss", "lognormvariate", "expovariate",
                    "vonmisesvariate", "gammavariate", "betavariate", "paretovariate", "weibullvariate",
                    "binomialvariate", "binomialvariate"],
    rand_gen_sys: ["sys_random", "sys_getrandbits", "sys_randbytes", "sys_randrange", "sys_seed", "sys_state"],
}
rand_TABLE = [(g, n) for g, names in rand_GROUPS.items() for n in names]


def rand_gen(rng):
    p = rng.random()
    if p < 0.03:
        return rand_gen_subclass(rng, rand_base(rng, "init_subclass"))
    if p < 0.09:
        c = rand_base(rng, "main")
        c["sub"] = False
        return rand_gen_main(rng, c)
    g, n = rng.choice(rand_TABLE)
    c = rand_base(rng, n)
    r = g(rng, c)
    return c if r is None else r
# ====== END AREA rand ======


AREAS = {name: (globals()[name + "_gen"], globals()[name + "_run"])
         for name in ['coll', 'collabc', 'functools', 'operator', 'enumdc', 'misc', 'calstat', 'rand']}
selected = os.environ.get("CORELIBS_AREA")
ACTIVE = [a for a in (selected.split(",") if selected else AREAS) if AREAS[a][0] is not None]


def gen_case(rng):
    case = AREAS[rng.choice(ACTIVE)][0](rng)
    if case is not None:
        case["mod"] = "corelibs"
    return case


def run_python(case):
    return AREAS[case["fn"].split(".")[0]][1](case)


if __name__ == "__main__":
    main(gen_case, run_python)
