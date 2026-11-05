"""Differential test: the hooks of Objects/setobject.c, against the Lean model (CPython 3.15.2).

Usage: python3 difftest/dictset_sethooks_diff.py [--cases N] [--seed S]

Every case is a `dictset` scenario (see dictset_diff.py) built around the Python code a set calls:
  - `__hash__` that first changes the target set (clears it, pops, or pops and adds) and then
    answers, raises TypeError, raises a subclass of TypeError, or raises ValueError (KH);
  - a set subclass with such a `__hash__` (SH), so `in`, `remove` and `discard` retry with the
    frozenset hash, also for the TypeError subclass, and the frozensets those keys equal;
  - `__eq__` that changes the target set and may raise (KEvil), on a pool sharing one hash so
    that probes compare, restart and refill dummies;
  - operands that are generators changing the target set between items, generators that raise,
    and a set subclass whose `__iter__` yields something else than its table (SSub), for
    `isdisjoint`'s PyAnySet_CheckExact branch.
After every operation the result and the exact table order of every set are compared.
"""

import common
import dictset_diff as D


def edge_hash(rng):
    return rng.choice([0, 1, 8, 16, 700, -2, 2 ** 61 - 1, rng.randint(0, 7), rng.randint(0, 7) << 32])


def sethooks_pool(rng):
    pool = D.Pool()
    h = edge_hash(rng)
    plain = [pool.add("K", [i, h if rng.random() < 0.7 else i], ("K", i)) for i in range(rng.randint(2, 6))]
    fresh = pool.add("K", [50, 1000 + rng.randrange(1000)], ("K", 50))
    acts = [0, 1, 2, 10 + fresh]
    for i in range(rng.randint(0, 3)):
        act = rng.choice(acts[1:])
        rs = rng.random() < 0.3
        pool.add("Kev", [100 + i, h, act, rs], ("Kev", i), a=act, r=rs)
    for i in range(rng.randint(1, 5)):
        hh = h if rng.random() < 0.6 else edge_hash(rng)
        pool.add("kh", [200 + i, hh, rng.choice(acts), rng.choice([0, 0, 1, 2, 3])], ("KH", 200 + i))
    contents = [rng.sample(range(1, 6), rng.randint(0, 3)) for _ in range(rng.randint(1, 3))]
    for c in contents:
        key = ("fs",) + tuple(sorted(c))
        pool.add("fz", c, key)
        if rng.random() < 0.5:
            pool.add("st", c, key, fs=hash(frozenset(c)), sb=list(c))
        for _ in range(rng.randint(0, 2)):
            pool.add("sh", [c, rng.choice(acts), rng.choice([1, 2, 2, 3])], key)
    D.int_pool(pool, rng, rng.randint(2, 5), 8)
    if rng.random() < 0.3:
        pool.add("hraise", 0)
    return pool, plain


def hashable(spec):
    return spec["py"][0] in ("K", "int", "fz", "Kev") or (spec["py"][0] == "kh" and spec["hr"] == 0)


def gen_case(rng):
    pool, plain = sethooks_pool(rng)
    specs = pool.specs
    n = len(specs)
    hk = [i for i in range(n) if hashable(specs[i])]
    k = lambda: rng.randrange(n)
    target = rng.choice(["s0", "s1"])

    def arg():
        o = rng.random()
        if o < 0.3:
            return ["s", rng.randrange(3)]
        if o < 0.5:
            return ["l", [k() for _ in range(rng.randint(0, 6))]]
        if o < 0.7:
            items = [k() for _ in range(rng.randint(0, 6))]
            return ["h", items, rng.randint(0, 6), rng.choice([1, 2]), rng.random() < 0.2]
        if o < 0.8:
            return ["g", [k() for _ in range(rng.randint(0, 4))]]
        return ["S", [rng.choice(hk) for _ in range(rng.randint(0, 4))],
                [k() for _ in range(rng.randint(0, 4))]]

    ops = []
    for _ in range(rng.randint(2, 14)):
        ops.append(["sadd", rng.randrange(2), rng.choice(hk)])
    if rng.random() < 0.5:
        ops.append(["sdisc", rng.randrange(2), rng.choice(hk)])
    for _ in range(rng.randint(3, 14)):
        o = rng.random()
        s = rng.randrange(2)
        if o < 0.22:
            ops.append([rng.choice(["sadd", "sdisc", "srem"]), s, k()])
        elif o < 0.40:
            ops.append(["sin", rng.randrange(3), k()])
        elif o < 0.48:
            ops.append(["fnew", s, ["s", s]])
            ops.append(["fin", 2, k()])
        elif o < 0.52:
            ops.append(["fin", rng.randrange(3), k()])
        elif o < 0.70:
            ops.append([rng.choice(["supd", "sinter", "sunion", "sdiffupd", "sinterupd", "sdiff"]), s,
                        [arg() for _ in range(rng.randint(1, 2))]])
        elif o < 0.88:
            ops.append([rng.choice(["sdisj", "sdisj", "ssuper", "ssubset", "ssymupd", "ssym"]), s, arg()])
        elif o < 0.94:
            ops.append([rng.choice(["sand", "sor", "sisub", "siand"]), s, rng.randrange(3)])
        else:
            ops.append([rng.choice(["shash", "slen", "spop", "scopy"]), s])
    return {"mod": "dictset", "fn": "scenario", "pool": specs, "ops": ops, "target": target}


if __name__ == "__main__":
    common.main(gen_case, D.run_python, default_cases=2000)
