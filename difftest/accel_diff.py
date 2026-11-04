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


# A type whose name `%.50s` cuts inside a character: 61 bytes, printed as "a" and 24 'é'.
LONG_OBJ = type("a" + "\u00e9" * 30, (), {})()


def run_heap(c):
    f = getattr(MODS[c["impl"]]["heapq"], c["fn"] + ("_max" if c["max"] else ""))
    items = [E(v) for v in c["heap"]]
    heap = {"list": items, "tuple": tuple(items), "none": None, "long": LONG_OBJ}[c["arg"]]
    st = {"k": 0, "log": [], "heap": heap, "script": {k: acts for k, acts in c["script"]}}
    E.ctx = st
    args = (E(c["item"]),) if c["fn"] in ("heappush", "heapreplace", "heappushpop") else ()
    try:
        r = f(heap, *args)
        out = {"r": r.v if isinstance(r, E) else None, "exc": None}
    except Exception as e:
        out = {"r": None, "exc": [type(e).__name__, str(e)]}
    out["heap"] = [x.v for x in heap] if isinstance(heap, (list, tuple)) else []
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


SKINDS = ["lt", "eq", "key", "next", "iter", "len"]


def gen_script(rng, bound):
    if rng.random() < 0.3:
        return []
    out = []
    for _ in range(rng.choice([1, 1, 2, 3])):
        kind = rng.choice(SKINDS + ["lt", "eq", "next"])
        acts = ["raise", "stop"] + (["boolraise", "flip"] if kind in ("lt", "eq") else [])
        out.append([kind, rng.randint(1, max(1, bound)), rng.choice(acts)])
    return out


def gen_objs(rng, m):
    """Element values, and the object index of each of `m` items (some objects repeat)."""
    span = rng.choice([1, 3, 10, 100])
    vals, idx = [], []
    for _ in range(m):
        if vals and rng.random() < 0.15:
            idx.append(rng.randrange(len(vals)))
        else:
            vals.append(rng.randint(-span, span))
            idx.append(len(vals) - 1)
    return vals, idx


def gen_src(rng, name, items):
    static = rng.random() < 0.1
    if rng.random() < 0.3:
        return {"kind": "it", "name": name, "items": items, "static": static}
    u = rng.random()
    if u < 0.25:
        ln = None
    elif u < 0.75:
        ln = len(items)
    elif u < 0.85:
        ln = rng.choice([0, 1, 2, len(items) + 1, max(len(items) - 1, 0)])
    else:
        ln = {"exc": rng.choice(["TypeError", "AttributeError", "ValueError", "RuntimeError"]),
              "msg": "from __len__"}
    return {"kind": "src", "name": name, "items": items, "len": ln, "static": static}


def gen_select(rng, fn):
    m = rng.choice([0, 1, 2, 3, 4, 5, 6, 8, 10, 12, rng.randrange(20), rng.randrange(41)])
    vals, idx = gen_objs(rng, m)
    n = rng.choice([-2, -1, 0, 1, 1, 2, 3, m - 1, m, m + 1, rng.randrange(-3, 45)])
    key = rng.choice(["none", "none", "neg", "div3", "mod3", "abs"])
    return {"objs": vals, "src": gen_src(rng, "s", idx), "n": n, "key": key,
            "script": gen_script(rng, 3 * m + 6)}


def gen_merge(rng, fn):
    key = rng.choice(["none", "none", "neg", "div3", "mod3", "abs"])
    rev = rng.random() < 0.5
    k = rng.choice([0, 1, 2, 2, 3, 4, rng.randrange(7)])
    vals, srcs, total = [], [], 0
    span = rng.choice([1, 3, 10, 100])
    for i in range(k):
        m = rng.choice([0, 1, 2, 3, 5, rng.randrange(9)])
        vs = [rng.randint(-span, span) for _ in range(m)]
        if rng.random() < 0.9:
            vs.sort(key=KEYS[key], reverse=rev)
        items = []
        for v in vs:
            if vals and rng.random() < 0.1:
                items.append(rng.randrange(len(vals)))
            else:
                vals.append(v)
                items.append(len(vals) - 1)
        total += m
        srcs.append(gen_src(rng, f"s{i}", items))
    return {"objs": vals, "srcs": srcs, "key": key, "reverse": rev,
            "script": gen_script(rng, 3 * total + 6)}


class SCtx:
    cur = None


def s_bump(kind):
    c = SCtx.cur
    c["ctr"][kind] = c["ctr"].get(kind, 0) + 1
    j = c["ctr"][kind]
    return j, c["script"].get((kind, j))


class SBad:
    def __init__(self, msg):
        self.msg = msg

    def __bool__(self):
        raise TypeError(self.msg)


class SE:
    """An element; `<` and `==` are scripted (Lean: `SelDiff.cmpCall`)."""

    __slots__ = ("v",)
    __hash__ = None

    def __init__(self, v):
        self.v = v

    def _cmp(self, kind, other, res):
        SCtx.cur["log"].append([kind, self.v, other.v])
        j, a = s_bump(kind)
        if a == "raise":
            raise ValueError(f"{kind} {j}")
        if a == "stop":
            raise StopIteration
        if a == "boolraise":
            return SBad(f"bool {kind} {j}")
        if a == "flip":
            return not res
        return res

    def __lt__(self, other):
        return self._cmp("lt", other, self.v < other.v)

    def __eq__(self, other):
        return self._cmp("eq", other, self.v == other.v)


class SKey:
    def __init__(self, f):
        self.f = f

    def __call__(self, x):
        SCtx.cur["log"].append(["key", x.v])
        j, a = s_bump("key")
        if a == "raise":
            raise ValueError(f"key {j}")
        if a == "stop":
            raise StopIteration
        return SE(self.f(x.v))


class It:
    def __init__(self, name, items):
        self.name, self.items, self.i = name, items, 0

    def __iter__(self):
        SCtx.cur["log"].append(["iter", self.name])
        j, a = s_bump("iter")
        if a == "raise":
            raise ValueError(f"iter {j}")
        if a == "stop":
            raise StopIteration
        return self

    def __next__(self):
        SCtx.cur["log"].append(["next", self.name])
        j, a = s_bump("next")
        if a == "raise":
            raise ValueError(f"next {j}")
        if a == "stop":
            raise StopIteration
        if self.i < len(self.items):
            self.i += 1
            return self.items[self.i - 1]
        raise StopIteration


def make_it(name, items, static):
    """An `It`; with `static`, its `__next__` is a staticmethod, so `it.__next__.__self__`
    raises AttributeError (bugforge heapq-20261003-022813-c1)."""
    it = It(name, items)
    if static:
        cls = type("It", (It,), {})
        cls.__next__ = staticmethod(lambda: It.__next__(it))
        it.__class__ = cls
    return it


class Src:
    def __init__(self, name, items, ln=None, static=False):
        self.name, self.items, self.ln, self.static = name, items, ln, static

    def __iter__(self):
        SCtx.cur["log"].append(["iter", self.name])
        j, a = s_bump("iter")
        if a == "raise":
            raise ValueError(f"iter {j}")
        if a == "stop":
            raise StopIteration
        return make_it(self.name + "'", self.items, self.static)


class SrcLen(Src):
    def __len__(self):
        SCtx.cur["log"].append(["len", self.name])
        j, a = s_bump("len")
        if a == "raise":
            raise ValueError(f"len {j}")
        if a == "stop":
            raise StopIteration
        if isinstance(self.ln, dict):
            raise {"TypeError": TypeError, "AttributeError": AttributeError,
                   "ValueError": ValueError, "RuntimeError": RuntimeError}[self.ln["exc"]](self.ln["msg"])
        return self.ln


def make_src(d, objs):
    items = [objs[i] for i in d["items"]]
    if d["kind"] == "it":
        return make_it(d["name"], items, d.get("static", False))
    if d.get("len") is None:
        return Src(d["name"], items, None, d.get("static", False))
    return SrcLen(d["name"], items, d["len"], d.get("static", False))


def run_select(c):
    hq = MODS[c["impl"]]["heapq"]
    objs = [SE(v) for v in c["objs"]]
    SCtx.cur = {"ctr": {}, "log": [], "script": {(k, j): a for k, j, a in c["script"]}}
    key = None if c["key"] == "none" else SKey(KEYS[c["key"]])
    out = {"r": [], "exc": None}
    if c["fn"] == "merge":
        g = hq.merge(*[make_src(d, objs) for d in c["srcs"]], key=key, reverse=c["reverse"])
        while True:
            try:
                out["r"].append(next(g).v)
            except StopIteration:
                break
            except Exception as e:
                out["exc"] = [type(e).__name__, str(e)]
                break
        try:
            v = next(g)
            out["after"] = v.v
        except StopIteration:
            out["after"] = "stop"
        except Exception as e:
            out["after"] = [type(e).__name__, str(e)]
    else:
        try:
            r = getattr(hq, c["fn"])(c["n"], make_src(c["src"], objs), key=key)
            out["r"] = [x.v for x in r]
        except Exception as e:
            out["exc"] = [type(e).__name__, str(e)]
    out["log"] = SCtx.cur["log"]
    return {"ok": out}


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
    if c["impl"] == "c" and c.get("arg") == "none" and rng.random() < 0.5:
        c["arg"] = "long"
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
    if fn in ("nsmallest", "nlargest", "merge"):
        return run_select(c)
    raise ValueError(fn)


if __name__ == "__main__":
    common.main(gen_case, run_python)
