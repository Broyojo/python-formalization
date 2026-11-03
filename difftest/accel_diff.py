"""Differential test: Lean model of bisect/heapq (C and pure-Python twins) vs. the running CPython.

Usage: python3 difftest/accel_diff.py [--cases N] [--seed S]

Each case names its twin with "impl": "c" runs the `_bisect`/`_heapq`
accelerator, "py" the pure-Python module imported with the accelerator
blocked. nsmallest/nlargest/merge exist only in Python; "c" there means the
stock `heapq` module, whose helpers then call the C heap functions.
Heap cases run with scripted comparisons (class `E`): comparison k logs its operands and
then runs the case's actions for k, which may mutate the heap list, flip the answer, raise,
or return an object whose `__bool__` raises. The returned item, the exception, the final
list and the comparison log are all compared. C cases whose script mutates the list run in
a forked child, so a crash is a recorded outcome (`{"crash": true}`).

Exits non-zero on any mismatch. See difftest/common.py.
"""

import json
import os

from test.support.import_helper import import_fresh_module

import common

MODS = {
    "c": {"bisect": import_fresh_module("bisect", fresh=["_bisect"]),
          "heapq": import_fresh_module("heapq", fresh=["_heapq"])},
    "py": {"bisect": import_fresh_module("bisect", blocked=["_bisect"]),
           "heapq": import_fresh_module("heapq", blocked=["_heapq"])},
}
assert type(MODS["c"]["bisect"].bisect_left).__name__ == "builtin_function_or_method"
assert type(MODS["py"]["bisect"].bisect_left).__name__ == "function"
assert type(MODS["c"]["heapq"].heappop_max).__name__ == "builtin_function_or_method"
assert type(MODS["py"]["heapq"].heappop_max).__name__ == "function"

# Must match keyFn in lean/PyLean/Accel/Diff.lean.
KEYS = {"none": None, "neg": lambda x: -x, "div3": lambda x: x // 3,
        "mod3": lambda x: x % 3, "abs": abs}

BIG = [2**63 - 1, 2**63, 2**63 + 1, -2**63, -2**63 - 1, 2**64, -2**64, 2**100]


class Sized:
    """Iterates `items`, but `len()` gives `size`, which need not match them: a count,
    or {"exc": class name, "msg": message} for a `__len__` that raises."""

    def __init__(self, items, size):
        self.items, self.size = items, size

    def __iter__(self):
        return iter(self.items)

    def __len__(self):
        if isinstance(self.size, dict):
            raise {"TypeError": TypeError, "AttributeError": AttributeError,
                   "RuntimeError": RuntimeError, "ValueError": ValueError}[self.size["exc"]](self.size["msg"])
        return self.size


def small_list(rng, n=None):
    if n is None:
        n = rng.choice([0, 0, 1, 2, 3, 4, 5, 7, 8, rng.randrange(20), rng.randrange(40)])
    span = rng.choice([1, 3, 10, 100])
    return [rng.randint(-span, span) for _ in range(n)]


def gen_bisect(rng, fn):
    key = rng.choice(["none", "none", "neg", "div3", "mod3", "abs"])
    a = small_list(rng)
    if rng.random() < 0.85:
        k = KEYS[key] or (lambda v: v)
        a.sort(key=k)
    n = len(a)
    edge = [0, 1, 2, -1, -2, n - 1, n, n + 1, n + 2, 2 * n, rng.randrange(n + 3)]
    lo = rng.choice(edge + [0, 0, 0] + ([rng.choice(BIG)] if rng.random() < 0.15 else []))
    hi = rng.choice(edge + [None, None, None, None] + ([rng.choice(BIG)] if rng.random() < 0.15 else []))
    x = rng.randint(-12, 12) if rng.random() < 0.9 else rng.choice(BIG)
    if rng.random() < 0.1:
        # 3.15 refuses a negative lo in the clinic converter, so before hi is converted.
        # This pairs the boundaries of both, which is where the order of the checks shows.
        lo = rng.choice([-1, -2, -2**63, -2**63 + 1, -2**63 - 1, 2**63 - 1, 2**63])
        hi = rng.choice(BIG + [None, -1, 0, n, 2**63 - 2])
    return {"a": a, "x": x, "lo": lo, "hi": hi, "key": key}


MUTATING = ("append", "pop", "clear", "set")


def gen_action(rng, n, mutate):
    kinds = ["raise", "boolraise", "flip"] + (["append", "pop", "clear", "set", "set", "append"]
                                              if mutate else [])
    a = rng.choice(kinds)
    if a == "append":
        return ["append", rng.randint(-15, 15)]
    if a == "set":
        return ["set", rng.randrange(n + 3), rng.randint(-15, 15)]
    return [a]


def gen_heap(rng, fn):
    if fn == "heapify" and rng.random() < 0.01:
        n = rng.choice([2499, 2500, 2501, 2502, 2600, 4095, 4096, 4097])
        heap = [rng.randint(-50, 50) for _ in range(n)]
        kmax = rng.choice([5, 50, 3000, 6000])
    else:
        heap = small_list(rng, rng.choice([0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 15,
                                           rng.randrange(25)]))
        kmax = 2 * len(heap).bit_length() + 4
    is_max = rng.random() < 0.5
    if fn != "heapify" and rng.random() < 0.6:
        m = MODS["c"]["heapq"]
        (m.heapify_max if is_max else m.heapify)(heap)
    u = rng.random()
    arg = "list" if u < 0.93 else ("tuple" if u < 0.97 else "none")
    if arg == "none":
        heap = []
    script = []
    if rng.random() < 0.75:
        for k in sorted(rng.sample(range(1, kmax + 1), min(kmax, rng.choice([1, 1, 2, 3])))):
            script.append([k, [gen_action(rng, len(heap), arg == "list")
                               for _ in range(rng.choice([1, 1, 1, 2]))]])
    return {"heap": heap, "max": is_max, "item": rng.randint(-12, 12), "arg": arg,
            "script": script}


class Bad:
    """What a scripted `__lt__` returns for "boolraise": its truth test raises."""

    def __init__(self, k):
        self.k = k

    def __bool__(self):
        raise TypeError(f"bool {self.k}")


class E:
    """A heap item compared through a scripted `__lt__` (Lean: `Heapq.scriptCmp`)."""

    ctx = None
    __slots__ = ("v",)

    def __init__(self, v):
        self.v = v

    def __lt__(self, other):
        st = E.ctx
        st["k"] += 1
        k = st["k"]
        st["log"].append([self.v, other.v])
        res = self.v < other.v
        h = st["heap"]
        for act in st["script"].get(k, ()):
            op = act[0]
            if op == "append":
                h.append(E(act[1]))
            elif op == "pop":
                if h:
                    h.pop()
            elif op == "clear":
                h.clear()
            elif op == "set":
                if act[1] < len(h):
                    h[act[1]] = E(act[2])
            elif op == "flip":
                res = not res
            elif op == "raise":
                raise ValueError(f"cmp {k}")
            elif op == "boolraise":
                return Bad(k)
        return res


def run_heap(c):
    f = getattr(MODS[c["impl"]]["heapq"], c["fn"] + ("_max" if c["max"] else ""))
    items = [E(v) for v in c["heap"]]
    heap = {"list": items, "tuple": tuple(items), "none": None}[c["arg"]]
    st = {"k": 0, "log": [], "heap": heap, "script": {k: acts for k, acts in c["script"]}}
    E.ctx = st
    args = (E(c["item"]),) if c["fn"] in ("heappush", "heapreplace", "heappushpop") else ()
    try:
        r = f(heap, *args)
        out = {"r": r.v if isinstance(r, E) else None, "exc": None}
    except Exception as e:
        out = {"r": None, "exc": [type(e).__name__, str(e)]}
    out["heap"] = [x.v for x in heap] if heap is not None else []
    out["log"] = st["log"]
    return {"ok": out}


def in_child(thunk):
    """Run `thunk` in a forked child; a child killed by a signal is `{"ok": {"crash": true}}`."""
    rfd, wfd = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(rfd)
        try:
            data = json.dumps(thunk()).encode()
        except BaseException as e:  # harness failure, not a model outcome
            data = json.dumps({"harness_error": repr(e)}).encode()
        with os.fdopen(wfd, "wb") as fh:
            fh.write(data)
        os._exit(0)
    os.close(wfd)
    with os.fdopen(rfd, "rb") as fh:
        data = fh.read()
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status):
        return {"ok": {"crash": True}}
    return json.loads(data)


def gen_select(rng, fn):
    it = small_list(rng)
    n = len(it)
    nn = rng.choice([-2, -1, 0, 1, 1, 2, 3, n - 1, n, n + 1, rng.randrange(-3, 45),
                     rng.choice(BIG)])
    c = {"n": nn, "it": it, "key": rng.choice(["none", "none", "neg", "div3", "mod3", "abs"])}
    if rng.random() < 0.7:
        # A list has the right len(); len() of an iterator is a TypeError, which nsmallest
        # catches, so its message never reaches the result.
        if rng.random() < 0.5:
            c.update(kind="list", size=n)
        else:
            c.update(kind="iter", size={"exc": "TypeError", "msg": "no len()"})
    elif rng.random() < 0.75:
        # A __len__ that disagrees with the items reaches `return sorted(...)` with n below
        # the item count, the only case in which 3.15's dropped `[:n]` shows.
        size = rng.choice([0, 0, 1, 2, 3, n, n + 1, n + 3, rng.randrange(6), max(n - 1, 0)])
        c.update(kind="obj", size=size, n=rng.choice([nn, 0, 2, 3, size, size + 1, size - 1]))
    else:
        c.update(kind="obj", size={"exc": rng.choice(["TypeError", "AttributeError", "RuntimeError",
                                                      "ValueError"]), "msg": "from __len__"})
    return c


def gen_merge(rng, fn):
    key = rng.choice(["none", "none", "neg", "div3", "mod3", "abs"])
    rev = rng.random() < 0.5
    its = [small_list(rng, rng.choice([0, 1, 2, 3, 5, rng.randrange(12)]))
           for _ in range(rng.choice([0, 1, 2, 2, 3, 4, rng.randrange(8)]))]
    if rng.random() < 0.9:
        for it in its:
            it.sort(key=KEYS[key], reverse=rev)
    return {"its": its, "key": key, "reverse": rev}


GENS = {
    "bisect_left": gen_bisect, "bisect_right": gen_bisect,
    "insort_left": gen_bisect, "insort_right": gen_bisect,
    "heappush": gen_heap, "heappop": gen_heap, "heapreplace": gen_heap,
    "heappushpop": gen_heap, "heapify": gen_heap,
    "nsmallest": gen_select, "nlargest": gen_select, "merge": gen_merge,
}


def gen_case(rng):
    fn = rng.choice(list(GENS))
    c = {"mod": "accel", "fn": fn, "impl": rng.choice(["c", "py"])}
    c.update(GENS[fn](rng, fn))
    return c


def run_python(c):
    fn, mods = c["fn"], MODS[c["impl"]]
    key = KEYS[c.get("key", "none")]
    if fn.startswith("bisect"):
        f = getattr(mods["bisect"], fn)
        return common.py_result(lambda: f(list(c["a"]), c["x"], c["lo"], c["hi"], key=key))
    if fn.startswith("insort"):
        a = list(c["a"])
        r = common.py_result(lambda: getattr(mods["bisect"], fn)(a, c["x"], c["lo"], c["hi"], key=key))
        if "ok" in r:
            return {"ok": a}
        return r if a == c["a"] else {"exc": r["exc"], "msg": r["msg"] + " [list mutated]"}
    if fn.startswith("heap"):
        mutates = any(a[0] in MUTATING for _, acts in c["script"] for a in acts)
        if c["impl"] == "c" and mutates:
            return in_child(lambda: run_heap(c))
        return run_heap(c)
    hq = mods["heapq"]
    if fn in ("nsmallest", "nlargest"):
        it = {"list": list, "iter": iter}.get(c["kind"], lambda v: Sized(v, c["size"]))(c["it"])
        return common.py_result(lambda: getattr(hq, fn)(c["n"], it, key=key))
    if fn == "merge":
        return common.py_result(lambda: list(hq.merge(*[iter(x) for x in c["its"]],
                                                       key=key, reverse=c["reverse"])))
    raise ValueError(fn)


if __name__ == "__main__":
    common.main(gen_case, run_python)
