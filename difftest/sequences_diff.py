"""Differential test: Lean model of list / array.array / collections.deque
mutating methods vs. the running CPython.

Usage: python3 difftest/sequences_diff.py [--cases N] [--seed S]

A case builds one object and applies a random sequence of operations; after
every operation it records the result (value or exception and message) and
the contents. For deques the state also includes the number of 64-slot
blocks in use, read from `__sizeof__()`, which pins down `leftindex` up to
block boundaries, so the model's block arithmetic is checked, not only the
contents. Exceptions compare exactly (class and message).

Results that would need gigabytes of memory are never requested: repeat
counts are steered to small values unless the C code's explicit overflow
check rejects them (MemoryError) or `maxlen` bounds the result.
"""

import sys
from array import array
from collections import deque

import common

M = sys.maxsize
BIG = 10 ** 5           # largest result the generator lets CPython allocate
TC_RANGE = {"b": (-128, 127), "B": (0, 255), "h": (-2 ** 15, 2 ** 15 - 1),
            "i": (-2 ** 31, 2 ** 31 - 1), "q": (-2 ** 63, 2 ** 63 - 1)}
ITEMSIZE = {"b": 1, "B": 1, "h": 2, "i": 4, "q": 8}
BLOCK = 64 * 8 + 16
DEQUE_BASE = deque().__sizeof__() - BLOCK


def blocks(d):
    return (d.__sizeof__() - DEQUE_BASE) // BLOCK


def edge_index(rng, n):
    """Indices around 0, +-n and every Py_ssize_t / size_t boundary."""
    return rng.choice([0, 1, -1, 2, -2, n, -n, n - 1, -n - 1, n + 1, -n + 1,
                       rng.randint(-n - 3, n + 3), rng.randint(-n - 3, n + 3),
                       M, -M, -M - 1, M + 1, -M - 2, 2 ** 64, -2 ** 64, 2 ** 64 - 1,
                       2 ** 62, -2 ** 62, 10 ** 30, -10 ** 30, 64, -64, 65, 128])


def elem(rng, tc=None):
    """Small values so that searches hit; edge values for arrays."""
    if tc is not None and rng.random() < 0.3:
        lo, hi = TC_RANGE[tc]
        return rng.choice([lo, hi, lo - 1, hi + 1, 2 ** 63, -2 ** 63 - 1, 2 ** 64, -2 ** 64,
                           2 ** 31, -2 ** 31 - 1, 2 ** 15, -2 ** 15 - 1, 128, -129, 256, 2 ** 70])
    return rng.randint(0, 5)


def in_range(rng, tc):
    lo, hi = TC_RANGE[tc]
    if rng.random() < 0.2:
        return rng.choice([lo, hi])
    return rng.randint(max(lo, 0), min(hi, 5))


def gen_items(rng, n, tc=None):
    return [in_range(rng, tc) if tc else elem(rng) for _ in range(n)]


def rand_len(rng, kind):
    if kind == "deque" and rng.random() < 0.4:
        return rng.choice([31, 32, 33, 62, 63, 64, 65, 66, 95, 96, 127, 128, 129, 130, 200])
    return rng.choice([0, 0, 1, 1, 2, 3, 4, 5, 6, 7, 8, 10, 13, rng.randrange(40)])


def rand_slice(rng, n):
    part = lambda: rng.choice([None, None, edge_index(rng, n), rng.randint(-n - 2, n + 2)])
    step = rng.choice([None, None, 1, -1, 2, -2, 3, -3, 5, edge_index(rng, n) or 1])
    if rng.random() < 0.02:
        step = 0
    return [part(), part(), step]


def slice_len(n, s):
    try:
        return len(range(*slice(*s).indices(n)))
    except ValueError:
        return 0


def repeat_factor(rng, size, maxlen, itemsize=None, inplace=True):
    """A factor that is either small, or large enough that CPython's explicit
    overflow check fires, or bounded by maxlen. Returns None to skip."""
    n = rng.choice([-2, -1, 0, 1, 2, 3, 2, 3, -M - 1, -2 ** 64, M, M + 1, 2 ** 62, 2 ** 61,
                    2 ** 64, M // max(size, 1), M // max(size, 1) + 1, 10 ** 30, -10 ** 30])
    if not (-M - 1 <= n <= M):
        return n            # OverflowError in the conversion
    if n <= 1 or size == 0:
        return n
    if itemsize is not None:
        nbytes = size * itemsize
        if (inplace and nbytes * n > M) or (not inplace and (n > M // size or size * n > M // itemsize)):
            return n
        return n if size * n <= BIG else None
    if maxlen is not None:
        if size == 1 or size * n > M or n * size <= BIG:
            return n
        return n            # bounded by maxlen (the result has <= maxlen items)
    if size * n > M:
        return n
    return n if size * n <= BIG else None


def gen_op(rng, kind, n, tc, maxlen):
    x = elem(rng, tc)
    ops = ["insert", "pop", "index", "count", "remove", "getitem", "setitem", "delitem",
           "imul", "mul"]
    if kind == "deque":
        ops += ["append", "appendleft", "pop", "popleft", "extend", "extendleft", "extend_self",
                "extendleft_self", "iadd", "iadd_self", "rotate", "rotate", "rotate", "reverse",
                "copy", "add", "add_self", "clear", "init", "init_self", "index", "index"]
    else:
        ops += ["append", "setslice", "setslice", "setslice_self", "delslice", "delslice",
                "extend", "index", "index"]
        if kind == "list":
            ops += ["init", "init_self"]
        else:
            ops += ["extend_arr"]
    op = rng.choice(ops)
    if op in ("append", "appendleft", "count", "remove"):
        return [op, x]
    if op in ("pop",):
        if kind == "deque" or rng.random() < 0.3:
            return [op]
        return [op, edge_index(rng, n)]
    if op == "popleft" or op in ("extend_self", "extendleft_self", "iadd_self", "reverse", "copy",
                                  "add_self", "clear"):
        return [op]
    if op == "insert":
        return [op, edge_index(rng, n), x]
    if op == "index":
        k = rng.choice([1, 2, 2, 3, 3])
        return [op, x] + [edge_index(rng, n) for _ in range(k - 1)]
    if op == "getitem" or op == "delitem":
        return [op, edge_index(rng, n)]
    if op == "setitem":
        return [op, edge_index(rng, n), x]
    if op in ("extend", "extendleft", "iadd", "init", "extend_arr"):
        k = rng.choice([0, 1, 2, 3, 5, 64, 70])
        xs = gen_items(rng, k, tc if op == "extend_arr" else None) if op != "extend" or kind != "array" \
            else [elem(rng, tc) for _ in range(k)]
        if op == "init" and kind == "deque":
            ml = rng.choice([None, None, 0, 1, 3, 10, -1, M + 1])
            return [op, xs] + ([] if ml is None else [ml])
        return [op, xs]
    if op == "init_self":
        if kind == "deque":
            ml = rng.choice([None, 2])
            return [op] + ([] if ml is None else [ml])
        return [op]
    if op == "rotate":
        if rng.random() < 0.1:
            return [op]
        return [op, rng.choice([edge_index(rng, n), rng.randint(-3 * n - 3, 3 * n + 3),
                                rng.randint(-70, 70)])]
    if op in ("imul", "mul"):
        f = repeat_factor(rng, n, maxlen, ITEMSIZE.get(tc), inplace=(op == "imul"))
        if f is None:
            return None
        if kind == "deque" and maxlen is None and n * max(f, 0) > BIG and n * f <= M:
            return None
        return [op, f]
    if op == "add":
        k = rng.choice([0, 1, 2, 3, 70])
        return [op, gen_items(rng, k), rng.choice([None, None, k, k + 2])]
    if op in ("setslice", "delslice", "setslice_self"):
        s = rand_slice(rng, n)
        if op == "setslice":
            L = slice_len(n, s)
            k = rng.choice([L, L, L, 0, L + 1, max(L - 1, 0), 2])
            return [op, s, gen_items(rng, k, tc)]
        return [op, s]
    raise AssertionError(op)


def make(c):
    kind = c["fn"]
    if kind == "list":
        return list(c["init"])
    if kind == "array":
        return array(c["tc"], c["init"])
    return deque(c["init"], c["maxlen"])


def gen_case(rng):
    """Generate the operations while running them on a live object, so that
    every repeat factor is chosen from the exact current length."""
    kind = rng.choice(["list", "array", "deque", "deque"])
    n = rand_len(rng, kind)
    c = {"mod": "sequences", "fn": kind}
    tc = None
    if kind == "array":
        tc = rng.choice(list(TC_RANGE))
        c["tc"] = tc
        init = gen_items(rng, n, tc)
        if rng.random() < 0.05:
            init.append(elem(rng, tc))
    elif kind == "deque":
        c["maxlen"] = rng.choice([None, None, None, 0, 1, 2, 3, 5, 64, 65, n, n + 1, n + 3])
        init = gen_items(rng, n)
    else:
        init = gen_items(rng, n)
    c["init"] = init
    try:
        obj = make(c)
    except Exception:
        c["ops"] = []
        return c
    ops = []
    for _ in range(rng.randint(1, 8)):
        maxlen = obj.maxlen if kind == "deque" else None
        op = gen_op(rng, kind, len(obj), tc, maxlen)
        if op is None:
            continue
        ops.append(op)
        py_res(lambda: run_list(obj, op, kind, tc))
        if len(obj) > 3000:
            break
    c["ops"] = ops
    return c


def py_res(thunk):
    try:
        v = thunk()
        return {"ok": v}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


def deque_j(d):
    return [list(d), d.maxlen, blocks(d)]


def run_list(obj, op, kind, tc):
    name, args = op[0], op[1:]
    if name == "append":
        return obj.append(args[0])
    if name == "insert":
        return obj.insert(*args)
    if name == "pop":
        return obj.pop(*args)
    if name == "popleft":
        return obj.popleft()
    if name == "index":
        return obj.index(*args)
    if name == "count":
        return obj.count(*args)
    if name == "remove":
        return obj.remove(*args)
    if name == "getitem":
        return obj[args[0]]
    if name == "setitem":
        obj[args[0]] = args[1]
        return None
    if name == "delitem":
        del obj[args[0]]
        return None
    if name == "setslice":
        obj[slice(*args[0])] = array(tc, args[1]) if kind == "array" else args[1]
        return None
    if name == "setslice_self":
        obj[slice(*args[0])] = obj
        return None
    if name == "delslice":
        del obj[slice(*args[0])]
        return None
    if name == "imul":
        r = obj.__imul__(args[0])
        assert r is obj
        return None
    if name == "mul":
        r = obj * args[0]
        return deque_j(r) if kind == "deque" else list(r)
    if name == "init":
        obj.__init__(*args)
        return None
    if name == "init_self":
        obj.__init__(obj, *args)
        return None
    if name in ("extend", "extendleft"):
        getattr(obj, name)(args[0])
        return None
    if name == "extend_arr":
        obj.extend(array(tc, args[0]))
        return None
    if name in ("extend_self", "extendleft_self"):
        getattr(obj, name[:-5])(obj)
        return None
    if name == "iadd":
        r = obj.__iadd__(args[0])
        assert r is obj
        return None
    if name == "iadd_self":
        r = obj.__iadd__(obj)
        assert r is obj
        return None
    if name == "rotate":
        return obj.rotate(*args)
    if name == "reverse":
        return obj.reverse()
    if name == "copy":
        return deque_j(obj.copy())
    if name == "add":
        return deque_j(obj + deque(args[0], args[1]))
    if name == "add_self":
        return deque_j(obj + obj)
    if name == "appendleft":
        return obj.appendleft(args[0])
    if name == "clear":
        return obj.clear()
    raise AssertionError(name)


def run_python(c):
    kind = c["fn"]
    try:
        obj = make(c)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    out = []
    for op in c["ops"]:
        r = py_res(lambda: run_list(obj, op, kind, c.get("tc")))
        st = [list(obj), blocks(obj)] if kind == "deque" else list(obj)
        out.append([r, st])
    return {"ok": out}


if __name__ == "__main__":
    common.main(gen_case, run_python)
