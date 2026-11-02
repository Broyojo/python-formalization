"""Differential test: Lean model of list.sort (Objects/listobject.c) vs. the running CPython.

Usage: python3 difftest/listsort_diff.py [--cases N] [--seed S]

fn "sort":  the sorted list and the exact number of `<` calls. The items (or,
            with key=, the keys) are wrapped in `W`, whose `__lt__` increments a
            counter, so the merge policy, run detection, binary insertion and
            galloping are all checked call for call against the model.
fn "plain": the sorted list for bare ints (CPython then uses the type-specialised
            unsafe_long_compare, or unsafe_object_compare for big ints).
fn "evil":  the same for an inconsistent `__lt__`, which reaches the merge branches a
            consistent comparison cannot and backs the "every comparison function"
            properties.
fn "runs":  the length of every run the main loop pushes, for shuffled distinct ints.
            Reading them off the comparisons observes minrun_next and merge_init
            directly, not only through a count.
fn "objcmp": two objects whose __lt__ and __gt__ answer as the case says, which is
            exactly one call of unsafe_object_compare.
fn "minrun", "powerloop": the C helpers, checked against line-by-line Python
            transcriptions.
Exits non-zero on any mismatch. See difftest/common.py.
"""

import common

# Must match keyFn in lean/PyLean/ListSort/Diff.lean.
KEYS = {"none": None, "neg": lambda x: -x, "div3": lambda x: x // 3,
        "mod7": lambda x: x % 7, "abs": abs}

COUNT = [0]


class W:
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v

    def __lt__(self, other):
        COUNT[0] += 1
        return self.v < other.v


# Must match evilLt in lean/PyLean/ListSort/Diff.lean.
EVIL = {"noisy": lambda x, y, m: (x < y) != ((x * y + x + 3 * y) % m == 0),
        "hash": lambda x, y, m: ((7 * x + 13 * y + x * y) % m) * 2 < m}


class E:
    __slots__ = ("v", "lt")

    def __init__(self, v, lt):
        self.v = v
        self.lt = lt

    def __lt__(self, other):
        COUNT[0] += 1
        return self.lt(self.v, other.v)


class T:
    """An item that logs which two original positions each `<` compares."""
    __slots__ = ("v", "i")

    def __init__(self, v, i):
        self.v = v
        self.i = i

    def __lt__(self, other):
        LOG.append(max(self.i, other.i))
        return self.v < other.v


LOG = []


class B:
    def __bool__(self):
        raise ValueError("bool")


# Must match richOf in lean/PyLean/ListSort/Diff.lean.
RES = {"true": True, "false": False, "notimpl": NotImplemented, "one": 1, "zero": 0,
       "full": [0], "empty": [], "none": None, "badbool": B()}


def answer(mode):
    if mode == "raise":
        raise ValueError("cmp")
    return RES[mode]


def obj_pair(lt, gt):
    class O:
        __slots__ = ("i",)

        def __init__(self, i):
            self.i = i

        def __lt__(self, other):
            return answer(lt)

        def __gt__(self, other):
            return answer(gt)

    return [O(0), O(1)]


BIG = [2**30 - 1, 2**30, -2**30, 2**63 - 1, 2**63, -2**63, 2**64, -2**64 - 1, 2**100, -2**100]


def runs_list(rng, n, span):
    """Concatenated ascending/descending runs (descending ones with repeats)."""
    out = []
    while len(out) < n:
        m = rng.choice([1, 2, 3, 5, 8, rng.randrange(1, 40), rng.randrange(1, 200)])
        base = rng.randint(-span, span)
        kind = rng.random()
        if kind < 0.4:
            seg = sorted(rng.randint(base, base + span) for _ in range(m))
        elif kind < 0.8:
            seg = sorted((rng.randint(base, base + rng.choice([1, 2, 5, span])) for _ in range(m)),
                         reverse=True)
        else:
            seg = [base] * m
        out.extend(seg)
    return out[:n]


def gallop_list(rng, n):
    """Blocks that interleave in long stretches, so merges enter galloping mode."""
    k = rng.choice([2, 3, 4, 6])
    blocks = []
    for _ in range(k):
        lo = rng.randrange(0, 4 * n + 1)
        blocks.append(sorted(rng.randrange(lo, lo + rng.choice([n // 4 + 1, n + 1, 4 * n + 1]))
                             for _ in range(max(1, n // k))))
    out = [x for b in blocks for x in b]
    for _ in range(rng.choice([0, 0, 1, 3, 10])):
        if out:
            out[rng.randrange(len(out))] = rng.randrange(0, 4 * n + 1)
    return out


def edge_size(rng):
    """A length on a boundary of `while (list_size >> mr_e >= MAX_MINRUN)` or of the
    worked examples in listsort.txt: 315 and 2112, and 2**15 + 1 now and then."""
    k = rng.randrange(6, 13)
    return rng.choice([2**k - 1, 2**k, 2**k + 1, 63 * 2**(k - 6), 63 * 2**(k - 6) + 1,
                       64 * 2**(k - 6) - 1, 33 * 2**(k - 6), 315, 2112])


def gen_list(rng):
    n = rng.choice([0, 1, 2, 3, 4, 5, 7, 8, 15, 31, 32, 33, 63, 64, 65, 127, 128, 129,
                    rng.randrange(0, 64), rng.randrange(64, 300), rng.randrange(64, 300),
                    rng.randrange(300, 1500), edge_size(rng)]
                   + ([rng.randrange(1500, 6000)] if rng.random() < 0.08 else []))
    span = rng.choice([1, 3, 10, 100, 10**6, 2**70])
    kind = rng.random()
    if kind < 0.25:
        a = [rng.randint(-span, span) for _ in range(n)]
    elif kind < 0.5:
        a = runs_list(rng, n, span)
    elif kind < 0.65:
        a = gallop_list(rng, n)
    elif kind < 0.75:
        a = sorted(rng.randint(-span, span) for _ in range(n))
        if rng.random() < 0.5:
            a.reverse()
        for _ in range(rng.choice([0, 1, 3])):
            if n:
                i, j = rng.randrange(n), rng.randrange(n)
                a[i], a[j] = a[j], a[i]
    elif kind < 0.85:
        # sawtooth / organ pipe / descending with equal elements
        p = rng.randrange(1, 70)
        shape = rng.choice(["saw", "pipe", "desc_eq"])
        if shape == "saw":
            a = [i % p for i in range(n)]
        elif shape == "pipe":
            a = [min(i, n - i) for i in range(n)]
        else:
            a = [-(i // p) for i in range(n)]
    else:
        a = [rng.choice(BIG + [0, 1, -1]) + rng.randint(-2, 2) for _ in range(n)]
    return a


def gen_runs(rng):
    n = rng.choice([edge_size(rng), edge_size(rng), rng.randrange(2, 64), rng.randrange(64, 3000)]
                   + ([2**15 + 1] if rng.random() < 0.01 else []))
    a = list(range(n))
    rng.shuffle(a)
    return {"mod": "listsort", "fn": "runs", "a": a}


def gen_case(rng):
    extra = rng.random()
    if extra < 0.1:
        return gen_runs(rng)
    if extra < 0.2:
        return {"mod": "listsort", "fn": "objcmp", "lt": rng.choice(list(RES) + ["raise"]),
                "gt": rng.choice(list(RES) + ["raise"])}
    r = rng.random()
    if r < 0.03:
        n = rng.choice([0, 1, 2, 63, 64, 65, 127, 128, 129, 315, 2112, 2**15 + 1, 2**20, 2**20 + 1,
                        2**62, 2**63 - 1, rng.randrange(0, 1000), rng.randrange(0, 2**63)])
        return {"mod": "listsort", "fn": "minrun", "n": n, "k": rng.choice([0, 1, 2, 8, 33, 64])}
    if r < 0.06:
        n = rng.choice([2, 3, 10, 100, 2**20, 2**62, 2**63 - 1, rng.randrange(2, 10**6)])
        s1 = rng.randrange(0, n - 1)
        n1 = rng.randrange(1, n - s1)
        n2 = rng.randrange(1, n - s1 - n1 + 1)
        return {"mod": "listsort", "fn": "powerloop", "s1": s1, "n1": n1, "n2": n2, "n": n}
    if r < 0.26:
        mode = rng.choice(["noisy", "noisy", "hash"])
        m = rng.choice([5, 11, 37, 101, 1009, 10007] if mode == "noisy" else [3, 5, 8, 16, 101])
        return {"mod": "listsort", "fn": "evil", "a": gen_list(rng), "mode": mode, "m": m,
                "reverse": rng.random() < 0.3}
    fn = "sort" if r < 0.85 else "plain"
    return {"mod": "listsort", "fn": fn, "a": gen_list(rng),
            "key": rng.choice(["none", "none", "none", "neg", "div3", "mod7", "abs"]),
            "reverse": rng.random() < 0.3}


def py_minrun(n, k):
    """merge_init (listobject.c:2282-2288), then k calls of minrun_next (:2767-2775)."""
    mr_e = 0
    while n >> mr_e >= 64:
        mr_e += 1
    mr_mask = (1 << mr_e) - 1
    mr_current = 0
    out = []
    for _ in range(k):
        mr_current += n
        out.append(mr_current >> mr_e)
        mr_current &= mr_mask
    return out


def run_lengths(a):
    """The runs of `a.sort()`, from the comparisons. Run detection and binary insertion
    reach new positions one at a time, and merges stay behind them, but the first
    comparison of a run forced to minrun skips a position: it is lo[1] < lo[0] of the
    next run, and lo[0] was never compared. A natural run reaching minrun would end
    without that skip; on shuffled lists of 64 or more items it does not happen. A last
    run of one item is never compared at all."""
    n = len(a)
    if n < 2:
        return []
    LOG.clear()
    ts = [T(v, i) for i, v in enumerate(a)]
    ts.sort()
    starts, hi = [0], -1
    for m in LOG:
        if m > hi:
            if hi >= 0 and m == hi + 2:
                starts.append(m - 1)
            hi = m
    if hi == n - 2:
        starts.append(n - 1)
    return [b - a for a, b in zip(starts, starts[1:] + [n])]


def py_powerloop(s1, n1, n2, n):
    result = 0
    a = 2 * s1 + n1
    b = a + n1 + n2
    while True:
        result += 1
        if a >= n:
            a -= n
            b -= n
        elif b >= n:
            break
        a <<= 1
        b <<= 1
    return result


def run_python(c):
    fn = c["fn"]
    if fn == "minrun":
        return {"ok": py_minrun(c["n"], c["k"])}
    if fn == "runs":
        return {"ok": run_lengths(c["a"])}
    if fn == "objcmp":
        l = obj_pair(c["lt"], c["gt"])
        r = common.py_result(lambda: l.sort())
        return {"ok": [o.i for o in l]} if "ok" in r else r
    if fn == "powerloop":
        return {"ok": py_powerloop(c["s1"], c["n1"], c["n2"], c["n"])}
    if fn == "evil":
        lt = EVIL[c["mode"]]
        m = c["m"]
        COUNT[0] = 0
        es = [E(x, lambda a, b: lt(a, b, m)) for x in c["a"]]
        es.sort(reverse=c["reverse"])
        return {"ok": [[e.v for e in es], COUNT[0]]}
    f = KEYS[c["key"]]
    if fn == "plain":
        return common.py_result(lambda: sorted(c["a"], key=f, reverse=c["reverse"]))
    COUNT[0] = 0
    if f is None:
        ws = [W(x) for x in c["a"]]
        ws.sort(reverse=c["reverse"])
        res = [w.v for w in ws]
    else:
        res = list(c["a"])
        res.sort(key=lambda x: W(f(x)), reverse=c["reverse"])
    return {"ok": [res, COUNT[0]]}


if __name__ == "__main__":
    common.main(gen_case, run_python)
