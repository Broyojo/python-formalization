"""Differential test: Lean model of `range`/`slice` vs. the running CPython.

Usage: python3 difftest/rangeslice_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py. Huge ranges are
never iterated to the end: iterator cases take the first k values, then
compare `__length_hint__()`, the range in `__reduce__()` and its last k values,
which pins down the remaining values arithmetically. Independently of the
model, every CPython answer is also checked against an arithmetic oracle
(`oracle` below: mathematical length, membership by divmod, element formulas);
an oracle failure is reported as a mismatch.
"""

import itertools
import sys

import common

M = sys.maxsize
LIST_MAX = 70  # list lengths for `listslice`


def edge_int(rng):
    """0, +-1, and values at and around every C boundary (2**31, 2**62,
    2**63, 2**64), plus huge and random ints."""
    # 30, 60 and 90 are PyLong digit boundaries, where 3.15's rewritten
    # PyLong_AsLongAndOverflow (unroll_digits_ulong) changes loop.
    b = rng.choice([0, 1, 2, 3, 30, 31, 32, 60, 61, 62, 63, 63, 63, 64, 64, 65, 90, 91, 100])
    v = rng.choice([0, 1, 2, 3, 2 ** b, 2 ** b - 1, 2 ** b + 1, 2 ** b - 2, 2 ** b + 2,
                    rng.randrange(2 ** b + 1), M, M - 1, M + 1, M + 2, rng.randrange(20)])
    return v if rng.random() < 0.5 else -v


def near(rng, x):
    return x + rng.randint(-3, 3)


def rand_step(rng):
    s = rng.choice([1, 1, -1, 2, -2, 3, -3, edge_int(rng), edge_int(rng), edge_int(rng)])
    return s


def rand_range(rng):
    """(start, stop, step|None, nargs), steering stop near start and the C limits."""
    nargs = rng.choice([1, 2, 3, 3, 3, 3])
    a = edge_int(rng)
    s = rand_step(rng) if nargs == 3 else None
    if nargs == 3 and rng.random() < 0.02:
        s = 0
    st = s or 1
    choice = rng.random()
    if choice < 0.3:
        b = edge_int(rng)
    elif choice < 0.7:
        b = a + st * rng.randint(-2, 6) + rng.randint(-1, 1)
    else:
        b = near(rng, rng.choice([M, -M - 1, M + 1, -M - 2, 2 ** 64, -2 ** 64, 0]))
    if rng.random() < 0.3:
        a = near(rng, rng.choice([M, -M - 1, 2 ** 64, -2 ** 64, 0]))
    if nargs == 1:
        a = 0
    return [a, b, s], nargs


def make_range(r, nargs):
    a, b, s = r
    if nargs == 1:
        return range(b)
    if nargs == 2:
        return range(a, b)
    return range(a, b, s)


def math_len(a, b, s):
    if s > 0:
        return max(0, (b - a + s - 1) // s)
    return max(0, (a - b - s - 1) // (-s))


def rand_slice_part(rng, length):
    return rng.choice([None, None, edge_int(rng), rng.randint(-5, 5),
                       near(rng, length), near(rng, -length), rng.randint(-length - 2, length + 2)])


def rand_slice(rng, length):
    step = rng.choice([None, rand_step(rng), rng.randint(-4, 4)])
    return [rand_slice_part(rng, length), rand_slice_part(rng, length), step]


def gen_case(rng):
    fn = rng.choice(["new", "len", "getitem", "slice", "contains", "index", "count", "eq",
                     "iter", "iterfor", "reversed", "setstate", "setstate_obj", "indices", "listslice", "slicehash"])
    c = {"mod": "rangeslice", "fn": fn}
    if fn == "slicehash":
        c.update(parts=[edge_int(rng) if rng.random() < 0.7 else rng.choice([-1, -2, 0, 1, 2**61 - 1, 2**61 - 2, -(2**61 - 1)]) for _ in range(3)])
        return c
    if fn == "indices":
        n = rng.choice([0, 1, 5, edge_int(rng), abs(edge_int(rng)), rng.randrange(100)])
        c.update(s=rand_slice(rng, abs(n)), n=n)
        return c
    if fn == "listslice":
        n = rng.randrange(LIST_MAX)
        c.update(s=rand_slice(rng, n), n=n)
        return c
    r, nargs = rand_range(rng)
    c.update(r=r, nargs=nargs)
    if r[2] == 0 or nargs != 3:
        L = math_len(r[0] if nargs > 1 else 0, r[1], r[2] if nargs == 3 and r[2] else 1)
    else:
        L = math_len(*r)
    elem = lambda k: (r[0] if nargs > 1 else 0) + k * (r[2] if nargs == 3 and r[2] else 1)
    if fn == "getitem":
        c["i"] = rng.choice([0, 1, -1, L, -L, L - 1, -L - 1, edge_int(rng), rng.randint(-L - 2, L + 2)])
    elif fn == "slice":
        c["s"] = rand_slice(rng, L)
    elif fn in ("contains", "index", "count"):
        c["x"] = rng.choice([elem(0), elem(1), elem(L - 1), elem(L), elem(-1), r[1], near(rng, r[1]),
                             near(rng, elem(rng.randint(0, max(L - 1, 0)))), edge_int(rng)])
    elif fn == "eq":
        if rng.random() < 0.5:
            r2, n2 = rand_range(rng)
        else:
            # Same start, possibly the same elements written differently.
            n2 = 3
            s2 = r[2] if (nargs == 3 and r[2]) else 1
            if rng.random() < 0.3:
                s2 = rand_step(rng) or 1
            r2 = [elem(0), near(rng, elem(L)) if rng.random() < 0.7 else elem(L) + rng.randint(-3, 3) * s2, s2]
        c.update(r2=r2, nargs2=n2)
    elif fn in ("iter", "iterfor", "reversed"):
        c["k"] = rng.choice([0, 1, 2, 3, 5])
    elif fn == "setstate":
        c["k"] = rng.choice([0, 1, 3])
        c["rev"] = rng.random() < 0.5
        c["state"] = rng.choice([0, 1, -1, L, L + 1, L - 1, edge_int(rng), rng.randint(-2, L + 2)])
    elif fn == "setstate_obj":
        c.update(k=rng.choice([0, 1, 3]), k0=rng.choice([0, 0, 1, 2]), rev=rng.random() < 0.5)
        v = rng.choice([0, 1, -1, L, L + 1, L - 1, edge_int(rng), rng.randint(-2, L + 2)])
        c["state"] = rng.choice([
            v, {"kind": "subclass", "tp": "bool", "v": rng.choice([0, 1])},
            {"kind": "subclass", "tp": "IntSub", "v": v},
            {"kind": "index", "tp": "Idx", "v": v},
            {"kind": "raises", "tp": "IdxRaises", "exc": "RuntimeError", "msg": "from __index__"},
            {"kind": "raises", "tp": "IdxBad", "exc": "TypeError",
             "msg": "IdxBad.__index__() must return an int, not str"},
            {"kind": "other", "tp": rng.choice(["float", "str", "NoneType", "list"])}])
    return c


class IntSub(int):
    pass


class Idx:
    def __init__(self, v):
        self.v = v

    def __index__(self):
        return self.v


class IdxRaises:
    def __index__(self):
        raise RuntimeError("from __index__")


class IdxBad:
    def __index__(self):
        return "x"


def make_state(st):
    if isinstance(st, int):
        return st
    tp = st["tp"]
    if tp == "bool":
        return bool(st["v"])
    if tp == "IntSub":
        return IntSub(st["v"])
    if tp == "Idx":
        return Idx(st["v"])
    return {"IdxRaises": IdxRaises, "IdxBad": IdxBad, "float": lambda: 1.5, "str": lambda: "x",
            "NoneType": lambda: None, "list": list}[tp]()


def drive_for(it, k):
    """`next()` by a `for` loop: once this function is warm, FOR_ITER_RANGE specialises
    and `_ITER_NEXT_RANGE` runs in place of `rangeiter_next`."""
    xs = []
    if k:
        for x in it:
            xs.append(x)
            if len(xs) == k:
                break
    return xs


def enc_range(r):
    return [r.start, r.stop, r.step]


def run_python(c):
    fn = c["fn"]
    try:
        if fn == "indices":
            return {"ok": list(slice(*c["s"]).indices(c["n"]))}
        if fn == "listslice":
            return {"ok": list(range(c["n"]))[slice(*c["s"])]}
        if fn == "slicehash":
            return {"ok": hash(slice(*c["parts"]))}
        r = make_range(c["r"], c["nargs"])
        if fn == "new":
            v = enc_range(r)
        elif fn == "len":
            v = len(r)
        elif fn == "getitem":
            v = r[c["i"]]
        elif fn == "slice":
            v = enc_range(r[slice(*c["s"])])
        elif fn == "contains":
            v = c["x"] in r
        elif fn == "index":
            v = r.index(c["x"])
        elif fn == "count":
            v = r.count(c["x"])
        elif fn == "eq":
            r2 = make_range(c["r2"], c["nargs2"])
            e = r == r2
            v = [e, e and hash(r) == hash(r2)]
        elif fn in ("iter", "iterfor", "reversed"):
            it = reversed(r) if fn == "reversed" else iter(r)
            name = type(it).__name__
            xs = drive_for(it, c["k"]) if fn == "iterfor" else list(itertools.islice(it, c["k"]))
            red = it.__reduce__()[1][0]
            tail = list(red[-c["k"]:]) if c["k"] else []
            v = [name, xs, it.__length_hint__(), enc_range(red), tail]
        elif fn == "setstate":
            it = reversed(r) if c["rev"] else iter(r)
            name = type(it).__name__
            it.__setstate__(c["state"])
            xs = list(itertools.islice(it, c["k"]))
            v = [name, xs, it.__length_hint__()]
        elif fn == "setstate_obj":
            it = reversed(r) if c["rev"] else iter(r)
            name = type(it).__name__
            list(itertools.islice(it, c["k0"]))
            it.__setstate__(make_state(c["state"]))
            xs = list(itertools.islice(it, c["k"]))
            v = [name, xs, it.__length_hint__(), enc_range(it.__reduce__()[1][0])]
        res = {"ok": v}
    except Exception as e:
        res = {"exc": type(e).__name__, "msg": str(e)}
    if not oracle(c, res):
        # CPython disagrees with the arithmetic oracle: never matches the model.
        return {"exc": "OracleMismatch", "msg": repr(res)}
    return res


def seq(a, b, s):
    """(length, element function) of the mathematical sequence range(a, b, s)."""
    return math_len(a, b, s), (lambda k: a + k * s)


def oracle(c, res):
    """Independent arithmetic checks of CPython's answer (huge ranges are never iterated)."""
    fn = c["fn"]
    if fn == "indices":
        if c["n"] < 0 or c["s"][2] == 0:
            return "exc" in res
        a, b, st = res["ok"]
        L, e = seq(a, b, st)
        return st == (c["s"][2] or 1) and all(0 <= e(k) < c["n"] for k in (0, L - 1) if L)
    if fn == "listslice":
        if c["s"][2] == 0:
            return "exc" in res
        return res["ok"] == list(range(*slice(*c["s"]).indices(c["n"])))
    a, b, s = c["r"]
    if c["nargs"] == 1:
        a = 0
    if c["nargs"] < 3:
        s = 1
    if s == 0:
        return res.get("exc") == "ValueError"
    L, e = seq(a, b, s)
    if fn == "len":
        return res == ({"ok": L} if L <= M else {"exc": "OverflowError", "msg": res.get("msg")})
    if fn == "getitem":
        i = c["i"]
        if -L <= i < L:
            return res == {"ok": e(i % L)}
        return res.get("exc") == "IndexError"
    if fn in ("contains", "index", "count"):
        q, rem = divmod(c["x"] - a, s)
        mem = rem == 0 and 0 <= q < L
        if fn == "contains":
            return res == {"ok": mem}
        if fn == "count":
            return res == {"ok": int(mem)}
        return res == {"ok": q} if mem else res.get("exc") == "ValueError"
    if fn == "slice":
        if c["s"][2] == 0:
            return res.get("exc") == "ValueError"
        ia, ib, ic = slice(*c["s"]).indices(L)
        sa, sb, ss = res["ok"]
        SL, se = seq(sa, sb, ss)
        return SL == math_len(ia, ib, ic) and all(se(k) == e(ia + k * ic) for k in (0, 1, SL - 1) if 0 <= k < SL)
    if fn in ("iter", "iterfor", "reversed"):
        name, xs, hint, red, tail = res["ok"]
        f = (lambda k: e(L - 1 - k)) if fn == "reversed" else e
        j = min(c["k"], L)
        RL, re_ = seq(*red)
        return (xs == [f(k) for k in range(j)] and hint == L - j and RL == L - j
                and all(re_(k) == f(j + k) for k in (0, RL - 1) if RL)
                and tail == [f(k) for k in range(max(j, L - c["k"]), L)])
    return True


if __name__ == "__main__":
    common.main(gen_case, run_python)
