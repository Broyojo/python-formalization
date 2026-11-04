"""Differential test: Lean models of itertools (C and doc equivalents) vs. the running CPython.

Usage: python3 difftest/itertools_diff.py [--cases N] [--seed S]

Each case names its side with "impl": "c" runs the `itertools` C object and
compares it with the Lean C model; "doc" runs the "Roughly equivalent to" code
of Doc/library/itertools.rst (copied below, verbatim apart from names) and
compares it with the Lean doc model. Iterators are drained into
[items, null | [class, message]]; islice also reports how many input items
were consumed; count/repeat/groupby/tee run a sequence of operations. Inputs
may be non-iterable or raise after their items, callbacks may raise, and the
private constructors (`_grouper`, `_tee`, `_tee_dataobject`) and `__sizeof__`
are exercised on the C side.

Allocation sizes between ~10**6 and 2**50 items are never requested: whether
those succeed depends on the machine (see lean/PyLean/Itertools/Model.lean).
Exits non-zero on any mismatch. See difftest/common.py.
"""

import itertools
import json
import math
import operator
import os
import resource
import signal
import struct
import sys
import weakref

import common

M = sys.maxsize

# ---------------------------------------------------------------------------
# Doc equivalents, Doc/library/itertools.rst (3.15).  islice is used by
# batched exactly as in the docs (the C islice).

def doc_accumulate(iterable, function=operator.add, *, initial=None):
    iterator = iter(iterable)
    total = initial
    if initial is None:
        try:
            total = next(iterator)
        except StopIteration:
            return
    yield total
    for element in iterator:
        total = function(total, element)
        yield total


def doc_batched(iterable, n, *, strict=False):
    if n < 1:
        raise ValueError('n must be at least one')
    iterator = iter(iterable)
    while batch := tuple(itertools.islice(iterator, n)):
        if strict and len(batch) != n:
            raise ValueError('batched(): incomplete batch')
        yield batch


def doc_chain(*iterables):
    for iterable in iterables:
        yield from iterable


def doc_from_iterable(iterables):
    for iterable in iterables:
        yield from iterable


def doc_combinations(iterable, r):
    pool = tuple(iterable)
    n = len(pool)
    if r > n:
        return
    indices = list(range(r))
    yield tuple(pool[i] for i in indices)
    while True:
        for i in reversed(range(r)):
            if indices[i] != i + n - r:
                break
        else:
            return
        indices[i] += 1
        for j in range(i+1, r):
            indices[j] = indices[j-1] + 1
        yield tuple(pool[i] for i in indices)


def doc_cwr(iterable, r):
    pool = tuple(iterable)
    n = len(pool)
    if not n and r:
        return
    indices = [0] * r
    yield tuple(pool[i] for i in indices)
    while True:
        for i in reversed(range(r)):
            if indices[i] != n - 1:
                break
        else:
            return
        indices[i:] = [indices[i] + 1] * (r - i)
        yield tuple(pool[i] for i in indices)


def doc_compress(data, selectors):
    return (datum for datum, selector in zip(data, selectors) if selector)


def doc_count(start=0, step=1):
    n = start
    while True:
        yield n
        n += step


def doc_cycle(iterable):
    saved = []
    for element in iterable:
        yield element
        saved.append(element)
    while saved:
        for element in saved:
            yield element


def doc_dropwhile(predicate, iterable):
    iterator = iter(iterable)
    for x in iterator:
        if not predicate(x):
            yield x
            break
    for x in iterator:
        yield x


def doc_filterfalse(predicate, iterable):
    if predicate is None:
        predicate = bool
    for x in iterable:
        if not predicate(x):
            yield x


def doc_groupby(iterable, key=None):
    keyfunc = (lambda x: x) if key is None else key
    iterator = iter(iterable)
    exhausted = False

    def _grouper(target_key):
        nonlocal curr_value, curr_key, exhausted
        yield curr_value
        for curr_value in iterator:
            curr_key = keyfunc(curr_value)
            if curr_key != target_key:
                return
            yield curr_value
        exhausted = True

    try:
        curr_value = next(iterator)
    except StopIteration:
        return
    curr_key = keyfunc(curr_value)

    while not exhausted:
        target_key = curr_key
        curr_group = _grouper(target_key)
        yield curr_key, curr_group
        if curr_key == target_key:
            for _ in curr_group:
                pass


def doc_islice(iterable, *args):
    s = slice(*args)
    start = 0 if s.start is None else s.start
    stop = s.stop
    step = 1 if s.step is None else s.step
    if start < 0 or (stop is not None and stop < 0) or step <= 0:
        raise ValueError
    indices = itertools.count() if stop is None else range(max(start, stop))
    next_i = start
    for i, element in zip(indices, iterable):
        if i == next_i:
            yield element
            next_i += step


def doc_pairwise(iterable):
    iterator = iter(iterable)
    a = next(iterator, None)
    for b in iterator:
        yield a, b
        a = b


def doc_permutations(iterable, r=None):
    pool = tuple(iterable)
    n = len(pool)
    r = n if r is None else r
    if r > n:
        return
    indices = list(range(n))
    cycles = list(range(n, n-r, -1))
    yield tuple(pool[i] for i in indices[:r])
    while n:
        for i in reversed(range(r)):
            cycles[i] -= 1
            if cycles[i] == 0:
                indices[i:] = indices[i+1:] + indices[i:i+1]
                cycles[i] = n - i
            else:
                j = cycles[i]
                indices[i], indices[-j] = indices[-j], indices[i]
                yield tuple(pool[i] for i in indices[:r])
                break
        else:
            return


def doc_product(*iterables, repeat=1):
    if repeat < 0:
        raise ValueError('repeat argument cannot be negative')
    pools = [tuple(pool) for pool in iterables] * repeat
    result = [[]]
    for pool in pools:
        result = [x+[y] for x in result for y in pool]
    for prod in result:
        yield tuple(prod)


def doc_repeat(object, times=None):
    if times is None:
        while True:
            yield object
    else:
        for i in range(times):
            yield object


def doc_starmap(function, iterable):
    for args in iterable:
        yield function(*args)


def doc_takewhile(predicate, iterable):
    for x in iterable:
        if not predicate(x):
            break
        yield x


def doc_tee(iterable, n=2):
    if n < 0:
        raise ValueError
    if n == 0:
        return ()
    iterator = _tee(iterable)
    result = [iterator]
    for _ in range(n - 1):
        result.append(_tee(iterator))
    return tuple(result)


class IntLike:
    """An int-like object: only `__index__`."""

    def __init__(self, value):
        self.value = value

    def __index__(self):
        return self.value


class _tee:

    def __init__(self, iterable):
        it = iter(iterable)
        if isinstance(it, _tee):
            self.iterator = it.iterator
            self.link = it.link
        else:
            self.iterator = it
            self.link = [None, None]

    def __iter__(self):
        return self

    def __next__(self):
        link = self.link
        if link[1] is None:
            link[0] = next(self.iterator)
            link[1] = [None, None]
        value, self.link = link
        return value


def doc_zip_longest(*iterables, fillvalue=None):
    iterators = list(map(iter, iterables))
    num_active = len(iterators)
    if not num_active:
        return
    while True:
        values = []
        for i, iterator in enumerate(iterators):
            try:
                value = next(iterator)
            except StopIteration:
                num_active -= 1
                if not num_active:
                    return
                iterators[i] = itertools.repeat(fillvalue)
                value = fillvalue
            values.append(value)
        yield tuple(values)


DOC = {"accumulate": doc_accumulate, "batched": doc_batched, "chain": doc_chain,
       "chain_from": doc_from_iterable,
       "combinations": doc_combinations, "cwr": doc_cwr, "compress": doc_compress,
       "count": doc_count, "cycle": doc_cycle, "dropwhile": doc_dropwhile,
       "filterfalse": doc_filterfalse, "groupby": doc_groupby, "islice": doc_islice,
       "pairwise": doc_pairwise, "permutations": doc_permutations, "product": doc_product,
       "repeat": doc_repeat, "starmap": doc_starmap, "takewhile": doc_takewhile,
       "tee": doc_tee, "zip_longest": doc_zip_longest}
C = {"accumulate": itertools.accumulate, "batched": itertools.batched, "chain": itertools.chain,
     "combinations": itertools.combinations, "cwr": itertools.combinations_with_replacement,
     "compress": itertools.compress, "count": itertools.count, "cycle": itertools.cycle,
     "dropwhile": itertools.dropwhile, "filterfalse": itertools.filterfalse,
     "groupby": itertools.groupby, "islice": itertools.islice, "pairwise": itertools.pairwise,
     "permutations": itertools.permutations, "product": itertools.product,
     "repeat": itertools.repeat, "starmap": itertools.starmap, "takewhile": itertools.takewhile,
     "tee": itertools.tee, "zip_longest": itertools.zip_longest}

# Must match predFn/keyFnI/binopFn/starFn in lean/PyLean/Itertools/Diff.lean.
def boom(msg, ok):
    """A callback that raises ValueError(msg) when the value is 3."""
    def f(*a):
        if 3 in a:
            raise ValueError(msg)
        return ok(*a)
    return f


def boom2(a, b):
    if b == 3:
        raise ValueError("binop")
    return a + b


PREDS = {"lt5": lambda x: x < 5, "even": lambda x: x % 2 == 0, "pos": lambda x: x > 0,
         "nz": operator.truth, "none": None, "r3": boom("pred", lambda x: x < 5)}
KEYS = {"r3": boom("key", lambda x: x), "eqr": None, "eqh": None, "id": lambda x: x, "div3": lambda x: x // 3, "mod2": lambda x: x % 2, "abs": abs,
        "neg": lambda x: -x}
BINOPS = {"add": operator.add, "mul": operator.mul, "max": max, "min": min,
          "sub": operator.sub, "r3": boom2}
STARS = {"sum": lambda *a: sum(a), "len": lambda *a: len(a),
         "r3": boom("star", lambda *a: sum(a))}


class Source:
    """An input iterator: yields `items`, then ends or raises ValueError(err)
    once, like a generator; counts what it handed out."""

    def __init__(self, items, err):
        self.items, self.err, self.pulled, self.pos = items, err, 0, 0
        self.hooks, self.run = [], None

    def __iter__(self):
        return self

    def __next__(self):
        if self.pos < len(self.items):
            self.pos += 1
            self.pulled += 1
            v = self.items[self.pos - 1]
            if self.hooks:  # after taking the item, as a map() function runs
                self.run(self.hooks.pop(0))
            return v
        if self.err is not None:
            e, self.err = self.err, None
            raise ValueError(e)
        raise StopIteration


class Reiter(Source):
    """An iterator whose __iter__ does not return itself: it returns `second`, or raises."""

    def __init__(self, items, err, second):
        super().__init__(items, err)
        self.second = second

    def __iter__(self):
        if isinstance(self.second, str):
            raise ValueError(self.second)
        return self.second


class Wrap:
    """An iterable whose __iter__ returns the given iterator."""

    def __init__(self, it):
        self.it = it

    def __iter__(self):
        return self.it


class OwnedSource:
    """`Source` for islice_r: counts into `counter`, and after taking an item makes the
    next of `hooks` calls on the islice through `call`. Holds no reference to itself, so
    when the islice drops it, it is freed. __next__ on a freed object is a crash."""

    def __init__(self, items, err, counter, hooks, call, dead):
        self.items, self.err, self.pos = items, err, 0
        self.counter, self.hooks, self.call, self.dead = counter, hooks, call, dead

    def __iter__(self):
        return self

    def __next__(self):
        try:  # on a freed object even reading the flag fails
            dead = self.dead[0]
        except BaseException:
            dead = True
        if dead:
            os.kill(os.getpid(), signal.SIGSEGV)
        if self.pos < len(self.items):
            self.pos += 1
            self.counter[0] += 1
            v = self.items[self.pos - 1]
            if self.hooks:
                for _ in range(self.hooks.pop(0)):
                    self.call()
            return v
        if self.err is not None:
            e, self.err = self.err, None
            raise ValueError(e)
        raise StopIteration

    def __del__(self):
        self.dead[0] = True


def run_islice_r(c):
    spec_, counter, ref, out = c["obj"], [0], [None], []

    def call():
        try:
            out.append(next(ref[0]))
        except StopIteration:
            out.append(None)
        except ValueError as e:
            out.append(["exc"] + enc_exc(e))

    src = 5 if "bad" in spec_ else OwnedSource(spec_["l"], spec_["err"], counter, list(c["hooks"]), call, [False])
    try:
        ref[0] = itertools.islice(src, *c["args"])
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    keep = None if c["sole"] else src
    del src
    for _ in range(c["calls"]):
        call()
    del keep
    return {"ok": [out, counter[0]]}


def obj(spec):
    """The Python object for a `decObj` spec."""
    if "bad" in spec:
        return 5
    return Source(spec["l"], spec["err"])


def objobj(spec):
    """An iterable of objects: `decObjObj`."""
    if "bad" in spec:
        return 5
    return Source([obj(o) for o in spec["ls"]], spec["err"])

# ---------------------------------------------------------------------------
# Generation

HUGE = [M, M - 1, M + 1, 2**63, 2**64, 2**100, -M - 1, -M - 2, -2**64,
        2**60 - 1, 2**60, 2**60 - 5, 2**60 - 4, 2**61, 2**50, M // 8, M // 8 + 1,
        (M - 32) // 8, (M - 32) // 8 + 1]


def small_list(rng, maxlen=12, span=None):
    n = rng.choice([0, 1, 2, 3, 4, 5, rng.randrange(maxlen + 1)])
    span = span if span is not None else rng.choice([1, 3, 10, 2**70])
    return [rng.randint(-span, span) for _ in range(n)]


def islice_val(rng, n):
    return rng.choice([None, None, 0, 1, 2, 3, -1, -2, n, n + 1, n - 1, rng.randrange(n + 3),
                       M, M - 1, M - 2, M + 1, 2**63, 2**64, -2**63, -2**63 - 1, -2**64,
                       M // 2, M // 2 + 1, M - n, rng.choice(HUGE)])


class Raising:
    """A number by PyNumber_Check, whose addition raises."""

    def __float__(self):
        return 0.0

    def __add__(self, other):
        raise ValueError("add")

    __radd__ = __add__

    def __repr__(self):
        return "Raising()"


class RaisingInt(int):
    """An int, so `count` takes the fast path with it, whose addition raises."""

    def __add__(self, other):
        raise ValueError("add")

    __radd__ = __add__


class SubCount(itertools.count):
    pass


class SubChain(itertools.chain):
    def __init__(self, *args, **kwargs):
        pass


class SubIslice(itertools.islice):
    def __init__(self, *args, **kwargs):
        pass


BIG = 10 ** 4300


def big(v):
    """An int past the int/str limit travels as hex: json cannot print or read it."""
    return {"x": hex(v)}


def dec_val(v):
    if isinstance(v, dict) and "x" in v:
        return int(v["x"], 16)
    if isinstance(v, dict):
        return struct.unpack("<d", struct.pack("<Q", v["f"]))[0]
    return {"bad": Raising, "str": lambda: "a", "badint": lambda: RaisingInt(1)}[v]() if isinstance(v, str) else v


def enc_val(v):
    if type(v) is int and abs(v) >= BIG:
        return big(v)
    if isinstance(v, float):
        return "nan" if math.isnan(v) else {"f": struct.unpack("<Q", struct.pack("<d", v))[0]}
    return "bad" if isinstance(v, Raising) else "badint" if isinstance(v, RaisingInt) else v


def f_val(x):
    return {"f": struct.unpack("<Q", struct.pack("<d", x))[0]}


def forked(f):
    """Run `f` in a child, since the model may predict that it dies."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        try:
            data = json.dumps(f())
        except BaseException as e:
            data = json.dumps({"exc": "HARNESS", "msg": repr(e)})
        with os.fdopen(w, "w") as out:
            out.write(data)
        os._exit(0)
    os.close(w)
    with os.fdopen(r) as inp:
        data = inp.read()
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status):
        return {"ok": "CRASH"}
    return json.loads(data)


def spec(rng, l):
    """An input object: usually `l`, sometimes raising after it, sometimes not iterable."""
    x = rng.random()
    if x < 0.07:
        return {"bad": "int"}
    return {"l": l, "err": "boom" if x < 0.2 else None}


def gen_islice(rng):
    l = small_list(rng)
    n = len(l)
    nargs = rng.choice([1, 2, 2, 3, 3, 3])
    args = [islice_val(rng, n) for _ in range(nargs)]
    if nargs == 3 and rng.random() < 0.5:
        # Steer start + step past sys.maxsize (lz->next += step wraps).
        args[0] = rng.choice([0, 1, 2, 3, n - 1, n])
        args[2] = rng.choice([M, M - 1, M - 2, M - 3, M - rng.randrange(12), M // 2 + 1, 1, 2])
        args[1] = rng.choice([None, None, n, M, rng.randrange(n + 2)])
    # C side only: the same ints as __index__ objects (PyNumber_AsSsize_t).
    return {"obj": spec(rng, l), "args": args, "index": rng.random() < 0.3}


def iter2(rng):
    """What `__iter__` of the iterator returns when tee() calls PyObject_GetIter on it again."""
    if rng.random() < 0.4:
        return {"raise": "iter2"}
    return {"l": list(range(100, 100 + rng.randrange(70))), "err": "boom" if rng.random() < 0.2 else None}


def gen_case(rng):
    fn = rng.choice(["islice", "islice", "islice", "islice_arity", "batched", "accumulate", "chain",
                     "chain_from", "compress", "cycle", "dropwhile", "takewhile", "filterfalse",
                     "pairwise", "pairwise_r", "starmap", "zip_longest", "product", "combinations", "cwr",
                     "permutations", "sizeof", "count", "count", "count", "count_reentry", "repeat", "groupby",
                     "groupby", "groupby", "tee", "tee", "tee_wrap", "teedata", "teeweak",
                     "islice_r", "islice_r", "groupby", "tee"])
    impl = rng.choice(["c", "doc"])
    c = {"mod": "itertools", "fn": fn, "impl": impl}
    if fn == "islice":
        c.update(gen_islice(rng))
    elif fn == "islice_arity":
        c.update(impl="c", nargs=rng.randrange(7), kw=rng.random() < 0.3, sub=rng.random() < 0.3)
    elif fn == "batched":
        n = rng.choice([1, 1, 2, 2, 3, 4, 5, 0, -1, -2**63, 10**6, rng.choice(HUGE)])
        c.update(obj=spec(rng, small_list(rng)), n=n, strict=rng.random() < 0.5)
    elif fn == "accumulate":
        c.update(obj=spec(rng, small_list(rng, span=4)), f=rng.choice(list(BINOPS)),
                 initial=rng.choice([None, None, 0, 7, -3, 2**70]))
    elif fn == "chain":
        c.update(objs=[spec(rng, small_list(rng, 4)) for _ in range(rng.randrange(5))])
        if impl == "c" and rng.random() < 0.15:
            c.update(kw=True, sub=rng.random() < 0.5)
    elif fn == "chain_from":
        src = rng.choice([{"bad": "int"}, {"ls": [spec(rng, small_list(rng, 4)) for _ in range(rng.randrange(5))],
                                            "err": rng.choice([None, None, "boom"])}])
        c.update(src=src)
    elif fn == "compress":
        c.update(data=spec(rng, small_list(rng)), sel=spec(rng, small_list(rng, span=1)))
    elif fn == "cycle":
        o = spec(rng, small_list(rng, 5))
        c.update(obj=o, k=rng.randrange(1 if "bad" in o else 0, 20))
    elif fn in ("dropwhile", "takewhile", "filterfalse"):
        preds = ["lt5", "even", "pos", "nz", "r3"] + (["none"] if fn == "filterfalse" else [])
        c.update(obj=spec(rng, small_list(rng, span=rng.choice([4, 10]))), pred=rng.choice(preds))
    elif fn == "pairwise":
        c.update(obj=spec(rng, small_list(rng)), hold=rng.randrange(3))
    elif fn == "pairwise_r":
        c.update(impl="c", obj=spec(rng, small_list(rng)), calls=rng.randrange(8),
                 hooks=[rng.randrange(5) for _ in range(rng.randrange(5))])
    elif fn == "starmap":
        c.update(src={"ls": [spec(rng, small_list(rng, 3, span=4)) for _ in range(rng.randrange(5))],
                      "err": rng.choice([None, None, "boom"])} if rng.random() > 0.05 else {"bad": "int"},
                 f=rng.choice(list(STARS)))
    elif fn == "zip_longest":
        f = rng.choice([None, 0, 9])
        kw = rng.choice([[], [["fillvalue", f]]])
        if impl == "c" and rng.random() < 0.08:
            kw = rng.choice([[["x", 1]], [["fillvalue", 1], ["x", 2]]])
        c.update(objs=[spec(rng, small_list(rng, 5)) for _ in range(rng.randrange(4))], kw=kw)
    elif fn == "product":
        rep = rng.choice([None, None, 0, 1, 2, 3, -1, -2**63 - 1, M, 2**63, 2**61, M // 8,
                          M // 16, 2**59])
        npools = rng.randrange(4) if rep is None or not (0 < rep <= 3) else rng.randrange(3)
        if rep is not None and rep > 3 and impl == "doc":
            npools = 0 if rng.random() < 0.5 else npools  # [pools] * huge
        c.update(objs=[spec(rng, small_list(rng, 3, span=3)) for _ in range(npools)], repeat=rep,
                 hold=rng.randrange(3))
    elif fn in ("combinations", "cwr", "permutations"):
        l = small_list(rng, 6, span=5)
        n = len(l)
        r = rng.choice([0, 1, 2, 3, n, n - 1, n + 1, n + 2, rng.randrange(n + 3), -1, -2,
                        -2**63, -2**63 - 1, 2**63, M, 2**50, 2**60, 10**5])
        if fn == "permutations" and rng.random() < 0.2:
            r = None
        if impl == "doc" and r is not None and r > n + 3:
            r = rng.choice([n + 3, 10**5, M, 2**63])  # the doc returns at once
        if fn == "cwr" and r is not None and 12 < r and n > 0:
            r = rng.choice([2**50, 2**60, M, 2**63, -1]) if impl == "c" else n + 1
        c.update(obj=spec(rng, l), r=r, hold=rng.randrange(3))
        if r is not None and r < 0 and rng.random() < 0.5:
            # A negative r on an input whose own failure would otherwise win.
            c.update(obj=rng.choice([{"bad": "int"}, {"l": l, "err": "boom"}]))
        if fn != "permutations" and impl == "c" and rng.random() < 0.15:
            c["index"] = True
        if fn == "permutations" and impl == "c" and rng.random() < 0.05:
            c["badr"] = True
    elif fn == "sizeof":
        kind = rng.choice(["combinations", "cwr", "permutations", "product"])
        l = small_list(rng, 6, span=5)
        n = len(l)
        r = rng.choice([0, 1, 2, n, n + 1, n + 3, -1, 2**63, M, 2**50])
        if kind == "cwr" and n > 0 and r > 12:
            r = rng.choice([0, 1, 2, 2**50, M])
        c.update(impl="c", kind=kind, basic=getattr(itertools, KIND[kind]).__basicsize__, r=r)
        if kind == "product":
            c.update(objs=[spec(rng, small_list(rng, 3)) for _ in range(rng.randrange(4))],
                     r=rng.choice([None, 0, 1, 2, 3, -1]), obj={"l": [], "err": None})
        else:
            c.update(obj=spec(rng, l))
    elif fn == "count":
        ints = [0, 1, -1, 2, 5, M, M - 1, M - 2, M - 3, M + 1, -M - 1, -M - 2, 2**64, -2**64,
                10**400, -10**400, 2**53, rng.randint(-10, 10),
                # around the 4300-digit limit of %R
                BIG - 1, -(BIG - 1), BIG - 2, big(BIG), big(-BIG), big(BIG + 1), big(10**5000)]
        floats = [f_val(x) for x in (0.5, -0.5, 1.0, 0.0, -0.0, 2.5, 0.1, 1e308, 1.7976931348623157e308,
                                     5e-324, 2.0**53, math.inf, -math.inf, math.nan)]
        others = [True, False, "bad", "badint"] + (["str"] if impl == "c" else [])

        def arg():
            return rng.choice(rng.choice([ints, floats, others]))

        def step():
            return rng.choice(rng.choice([[1, 1, 0, -1, 2, 3, M, -M - 1, M + 1, 2**64, -2**64,
                                           BIG - 1, -(BIG - 1), big(BIG), big(-BIG)], floats, others]))

        ops = [rng.choice("nnr" if impl == "c" else "n") for _ in range(rng.randrange(8))]
        c.update(ops=ops, sub=impl == "c" and rng.random() < 0.1)
        if rng.random() < 0.85:
            c["start"] = arg()
        if rng.random() < 0.7:
            c["step"] = step()
        if rng.random() < 0.15:
            # Fast mode up to sys.maxsize, where count_nextlong switches and the add fails.
            c.update(start=rng.choice([M, M - 1, M - 2]), step="badint", ops=ops + ["n", "r", "n"])
    elif fn == "count_reentry":
        # A step whose __radd__ calls next() on the count at the chosen add numbers. The values
        # stay small ints, which are immortal, so the double hand-out of python/cpython#154670
        # frees nothing.
        c.update(impl="c", start=rng.randint(90, 110), d=rng.randint(-2, 2),
                 reenter=sorted(rng.sample(range(12), rng.randrange(5))),
                 k=rng.randrange(9))
        c["raise"] = sorted(rng.sample(range(12), rng.choice([0, 0, 1, 2])))
    elif fn == "repeat":
        times = rng.choice([None, None, 0, 1, 2, 3, -1, -5, M, -M - 1, M + 1, 2**64, -2**64])
        c.update(elem=rng.randint(-3, 3), ops=[rng.choice("nrh") for _ in range(rng.randrange(8))])
        if times is not None:
            c["times"] = times
    elif fn == "groupby":
        l = small_list(rng, 12, span=rng.choice([1, 2, 4]))
        keys = list(KEYS) if impl == "c" else [k for k in KEYS if k not in ("r3", "eqr", "eqh")]
        key = rng.choice(keys + ["r3", "eqr", "eqh", "eqh"] * (impl == "c"))
        if key in ("r3", "eqr"):
            l.insert(rng.randrange(len(l) + 1), 3)  # the value they raise on
        # Failing inputs, keys and comparisons are C only: the doc generators die at
        # the first exception, and the Lean doc model has no failing calls.
        o = spec(rng, l) if impl == "c" else rng.choice([{"l": l, "err": None}] * 12 + [{"bad": "int"}])
        ops = [rng.choice(["o", "o", rng.randrange(4)]) for _ in range(rng.randrange(25))]
        if "bad" in o:
            ops = ["o"] + ops
        if impl == "c" and rng.random() < 0.3:
            # Read the new grouper: it is numbered after those made so far.
            p = rng.randrange(len(ops) + 1)
            made = sum(1 for x in ops[:p] if x == "o")
            # A key that occurs, or the grouper only ever stops.
            vals = [x for x in l if x != 3 or key != "r3"]
            tgt = (vals and rng.random() < 0.8 and rng.choice(vals)) or rng.randint(-2, 2)
            if key not in ("eqr", "eqh"):
                tgt = KEYS[key](tgt) if tgt in vals else tgt
            ops[p:p] = [["d", tgt], made, made, made]
        c.update(obj=o, key=key, ops=ops)
        if key == "eqh":
            # What successive __eq__ calls do: next(groupby), and reading a group.
            c["hooks"] = [[rng.choice(["o", "o", rng.randrange(5)]) for _ in range(rng.randrange(1, 4))]
                          for _ in range(rng.randrange(1, 4))]
        if impl == "c" and rng.random() < 0.35:
            # What successive key-function calls do before they answer.
            c["khooks"] = [[rng.choice(["o", "o", rng.randrange(4)]) for _ in range(rng.randrange(3))]
                           for _ in range(rng.randrange(1, 6))]
        if impl == "c" and "bad" not in o and rng.random() < 0.35:
            # What the input's __next__ does after taking successive items.
            c["ihooks"] = [[rng.choice(["o", "o", rng.randrange(4)]) for _ in range(rng.randrange(3))]
                           for _ in range(rng.randrange(1, 6))]
    elif fn == "tee":
        n = rng.choice([0, 1, 2, 2, 3, -1])
        if impl == "c" and rng.random() < 0.1:
            n = rng.choice([2**63, -2**63 - 1, M, 2**60])
        L = rng.choice([0, 3, 56, 57, 58, 114, 115, rng.randrange(130)])
        ops = []
        for _ in range(rng.choice([10, 60, 200, 400])):
            x = rng.random()
            k = rng.randrange(4)
            if x < 0.85:
                ops.append(["n", k])
            elif x < 0.91:
                ops.append(["t", k, rng.randrange(3)])
            elif x < 0.96:
                ops.append(["c", k])
            else:
                ops.append(["k", k])
        c.update(obj=spec(rng, list(range(L))), n=n, ops=ops)
        if impl == "c" and rng.random() < 0.15:
            c["index"] = True
        if impl == "c" and rng.random() < 0.3:
            c["hooks"] = [[[rng.choice("nnnc"), rng.randrange(4)] for _ in range(rng.randrange(1, 3))]
                          for _ in range(rng.randrange(1, 6))]
        if impl == "c" and rng.random() < 0.25:
            c["iter2"] = iter2(rng)
    elif fn == "tee_wrap":
        L = rng.choice([0, 3, 56, 57, 58, rng.randrange(70)])
        c.update(impl="c", obj=spec(rng, list(range(L))),
                 ops=[[rng.choice("nnnnck"), rng.randrange(3)] for _ in range(rng.choice([5, 80]))])
        if rng.random() < 0.3:
            c["hooks"] = [[["n", rng.randrange(3)]] for _ in range(rng.randrange(1, 4))]
        if rng.random() < 0.25:
            c["iter2"] = iter2(rng)
    elif fn == "islice_r":
        # An input whose __next__ calls next() on the islice after taking an item; `sole`:
        # the islice holds the only reference to it (python/cpython#142732 when it is freed).
        l = small_list(rng, 8, span=3)
        n = len(l)
        nargs = rng.choice([1, 2, 2, 3])
        args = [rng.choice([None, 0, 1, 2, 3, n, n + 1, rng.randrange(n + 3)]) for _ in range(nargs)]
        if nargs == 3 and args[2] is not None and args[2] < 1:
            args[2] = rng.choice([1, 2, 3])
        c.update(impl="c", obj=spec(rng, l), args=args, sole=rng.random() < 0.4,
                 hooks=[rng.choice([0, 0, 1, 1, 2, 3]) for _ in range(rng.randrange(6))],
                 calls=rng.randrange(n + 5))
    elif fn == "teeweak":
        ids = list(range(rng.randrange(6)))
        refs = list(ids)
        for _ in range(rng.randrange(3)):
            refs.insert(rng.randrange(len(refs) + 1), "b")
        c.update(impl="c", refs=refs, raising=[i for i in ids if rng.random() < 0.3])
    elif fn == "teedata":
        k = rng.choice([0, 1, 56, 57, 58, 100, rng.randrange(60)])
        c.update(impl="c", len=k, next=rng.choice(["none", "none", "data", "other"]))
    return c


KIND = {"combinations": "combinations", "cwr": "combinations_with_replacement",
        "permutations": "permutations", "product": "product"}


# ---------------------------------------------------------------------------
# Running CPython

def enc_exc(e):
    return [type(e).__name__, str(e)]


def drain(make, enc=lambda v: v, limit=None):
    items = []
    try:
        it = make()
        for v in it:
            items.append(enc(v))
            if limit is not None and len(items) >= limit:
                break
    except Exception as e:
        return [items, enc_exc(e)]
    return [items, None]


def drain_tuples(make, hold):
    """`drain` for an iterator that reuses its result tuple when it holds the only
    reference: the C code then fills it in place, and copies it otherwise
    (`_PyObject_IsUniquelyReferenced`, then `PyTuple_FromArray` or `_PyTuple_Recycle`).
    hold 0 keeps the last tuple alive across next(), hold 1 keeps every tuple, hold 2
    keeps none. The results must not depend on it."""
    if hold == 0:
        return drain(make, list)
    items, kept = [], []
    try:
        it = make()
        if hold == 1:
            for v in it:
                kept.append(v)
                items.append(list(v))
        else:
            for v in map(list, it):
                items.append(v)
    except Exception as e:
        return [items, enc_exc(e)]
    return [items, None]


def run_ops(obj_thunk, ops, enc=lambda v: v):
    try:
        obj = obj_thunk()
    except Exception as e:
        return [["exc"] + enc_exc(e)]
    out = []
    for o in ops:
        try:
            if o == "n":
                out.append(enc(next(obj)))
            elif o == "r":
                out.append(repr(obj))
            else:
                out.append(obj.__length_hint__())
        except StopIteration:
            out.append(None)
        except Exception as e:
            out.append(["exc"] + enc_exc(e))
    return out


class ReStep:
    """A number (by __index__) whose __radd__ answers other + d, raises ValueError('add') on
    the add numbers in `bad`, and first calls next() on the count on those in `reenter`."""

    def __init__(self, d, reenter, bad, log, cref):
        self.d, self.reenter, self.bad, self.log, self.cref, self.n = d, reenter, bad, log, cref, 0

    def __index__(self):
        return self.d

    def __radd__(self, other):
        n = self.n
        self.n += 1
        if n in self.bad:
            raise ValueError("add")
        if n in self.reenter:
            try:
                self.log.append(next(self.cref[0]))
            except Exception as e:
                self.log.append(["exc"] + enc_exc(e))
        return other + self.d


def run_count_reentry(c):
    """Every value next() returned or exception it raised, inner calls included, in the order
    the calls returned."""
    log, cref = [], [None]
    cref[0] = itertools.count(c["start"], ReStep(c["d"], set(c["reenter"]), set(c["raise"]), log, cref))
    for _ in range(c["k"]):
        try:
            log.append(next(cref[0]))
        except Exception as e:
            log.append(["exc"] + enc_exc(e))
    return {"ok": log}


def cmsg(f):
    """Raise-or-None as `{"ok": null}` / `{"exc": ..., "msg": ...}`."""
    try:
        f()
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    return {"ok": None}


def run_groupby(c):
    F = (C if c["impl"] == "c" else DOC)["groupby"]
    hooks, key = list(c.get("hooks") or []), c["key"]
    interned = {}

    class K:
        """Interned, so equal values are one object and `__eq__` sees distinct objects."""
        __hash__ = None

        def __init__(self, v):
            self.v = v

        def __eq__(self, other):
            if hooks:
                for o in hooks.pop(0):
                    do(o)
            if key == "eqr" and 3 in (self.v, other.v):
                raise ValueError("eq")
            return False

    def intern(x):
        return interned.setdefault(x, K(x))

    objkey = key in ("eqr", "eqh")
    khooks = list(c.get("khooks") or [])
    base = intern if objkey else KEYS[key]

    def keyf(x):
        if khooks:
            for o in khooks.pop(0):
                do(o)
        return base(x)

    src = obj(c["obj"])
    if isinstance(src, Source):
        src.hooks = list(c.get("ihooks") or [])

        def run(ops):
            for o in ops:
                do(o)
        src.run = run
    try:
        g = F(src, keyf if c.get("khooks") else base)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    groups, out = [], []

    def do(o):
        try:
            if o == "o":
                k, grp = next(g)
                groups.append(grp)
                out.append(k.v if objkey else k)
            elif isinstance(o, list):
                groups.append(itertools._grouper(g, intern(o[1]) if objkey else o[1]))
            elif o < len(groups):
                out.append(next(groups[o]))
        except StopIteration:
            out.append(None)
        except ValueError as e:
            out.append(["exc"] + enc_exc(e))

    try:
        for o in c["ops"]:
            do(o)
    except TypeError as e:  # the doc generator reads a non-iterable on the first next()
        return {"exc": type(e).__name__, "msg": str(e)}
    return {"ok": out}


def run_tee(c, F):
    src = obj(c["obj"])
    iterable = src
    sp = c.get("iter2")
    if sp is not None and isinstance(src, Source):
        # Wrap(first): tee() calls __iter__ on `first` again, _tee() does not.
        second = sp["raise"] if "raise" in sp else Source(sp["l"], sp["err"])
        first = Reiter(src.items, src.err, second)
        iterable = Wrap(first)
        src = second if c["fn"] == "tee" and isinstance(second, Source) else first
    try:
        n = IntLike(c["n"]) if c.get("index") else c.get("n")
        tees = [itertools._tee(iterable)] if c["fn"] == "tee_wrap" else list(F(iterable, n))
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    out = []

    def do(op):
        k = op[1]
        if k >= len(tees):
            return
        if op[0] == "n":
            try:
                out.append(next(tees[k]))
            except StopIteration:
                out.append(None)
            except Exception as e:
                out.append(["exc"] + enc_exc(e))
        elif op[0] == "t":
            tees.extend(F(tees[k], op[2]))
        elif c["impl"] == "c":
            tees.append(tees[k].__copy__() if op[0] == "c" else itertools._tee(tees[k]))
        else:
            tees.append(_tee(tees[k]))

    if isinstance(src, Source):
        src.hooks = list(c.get("hooks") or [])

        def run(ops):
            for op in ops:
                do(op)
        src.run = run
    for op in c["ops"]:
        do(op)
    return {"ok": [out, src.pulled if isinstance(src, Source) else 0]}


def run_pairwise(c):
    src = obj(c["obj"])
    try:
        p = itertools.pairwise(src)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    out = []

    def call():
        try:
            out.append(list(next(p)))
        except StopIteration:
            out.append(None)
        except ValueError as e:
            out.append(["exc"] + enc_exc(e))

    if isinstance(src, Source):
        src.hooks = list(c["hooks"])

        def run(n):
            for _ in range(n):
                call()
        src.run = run
    for _ in range(c["calls"]):
        call()
    return {"ok": out}


def run_teeweak(c):
    log, keep, raising = [], [], set(c["raising"])

    def callback(i):
        def f(ref):
            log.append(["called" if ref() is None else "alive", i])
            if i in raising:
                e = ValueError("cb")
                e.i = i
                raise e
        return f

    def hook(u):
        log.append(["unraisable", u.exc_value.i, type(u.exc_value).__name__, str(u.exc_value)])

    old, sys.unraisablehook = sys.unraisablehook, hook
    try:
        a, b = itertools.tee([1, 2, 3])
        for r in c["refs"]:
            keep.append(weakref.ref(a) if r == "b" else weakref.ref(a, callback(r)))
        del a
    finally:
        sys.unraisablehook = old
    return {"ok": log}


def run_python(c):
    fn, impl = c["fn"], c["impl"]
    F = (C if impl == "c" else DOC).get(fn)
    tup = lambda t: list(t)
    if fn == "islice":
        it = obj(c["obj"])
        args = c["args"]
        if impl == "c" and c["index"]:
            args = [a if a is None else IntLike(a) for a in args]
        r = drain(lambda: F(it, *args))
        return {"ok": r + [it.pulled if isinstance(it, Source) else 0]}
    if fn == "islice_arity":
        a = [[]] + [None] * (c["nargs"] - 1) if c["nargs"] else []
        cls = SubIslice if c["sub"] else itertools.islice
        return cmsg(lambda: cls(*a, **({"stop": 1} if c["kw"] else {})))
    if fn == "batched":
        return {"ok": drain(lambda: F(obj(c["obj"]), c["n"], strict=c["strict"]), tup)}
    if fn == "accumulate":
        kw = {} if c["initial"] is None else {"initial": c["initial"]}
        return {"ok": drain(lambda: F(obj(c["obj"]), BINOPS[c["f"]], **kw))}
    if fn == "chain":
        if c.get("kw"):
            if c["sub"]:
                return {"ok": drain(lambda: SubChain(*[obj(o) for o in c["objs"]], x=1))}
            return cmsg(lambda: itertools.chain([], x=1))
        return {"ok": drain(lambda: F(*[obj(o) for o in c["objs"]]))}
    if fn == "chain_from":
        G = itertools.chain.from_iterable if impl == "c" else lambda x: DOC["chain_from"](x)
        return {"ok": drain(lambda: G(objobj(c["src"])))}
    if fn == "compress":
        return {"ok": drain(lambda: F(obj(c["data"]), obj(c["sel"])))}
    if fn == "cycle":
        if impl == "c" and "bad" in c["obj"] or c["k"]:
            return {"ok": drain(lambda: F(obj(c["obj"])), limit=c["k"] or None)}
        return {"ok": [[], None]}
    if fn in ("dropwhile", "takewhile", "filterfalse"):
        return {"ok": drain(lambda: F(PREDS[c["pred"]], obj(c["obj"])))}
    if fn == "pairwise":
        return {"ok": drain_tuples(lambda: F(obj(c["obj"])), c["hold"])}
    if fn == "pairwise_r":
        return run_pairwise(c)
    if fn == "teeweak":
        return run_teeweak(c)
    if fn == "starmap":
        return {"ok": drain(lambda: F(STARS[c["f"]], objobj(c["src"])))}
    if fn == "zip_longest":
        kw = dict(c["kw"])
        if len(c["kw"]) == 2:
            return {"ok": drain(lambda: F(*[obj(o) for o in c["objs"]], **kw), tup)}
        return {"ok": drain(lambda: F(*[obj(o) for o in c["objs"]], **kw), tup)}
    if fn == "product":
        kw = {} if c["repeat"] is None else {"repeat": c["repeat"]}
        return {"ok": drain_tuples(lambda: F(*[obj(o) for o in c["objs"]], **kw), c["hold"])}
    if fn in ("combinations", "cwr"):
        r = IntLike(c["r"]) if c.get("index") else c["r"]
        return {"ok": drain_tuples(lambda: F(obj(c["obj"]), r), c["hold"])}
    if fn == "permutations":
        if c.get("badr"):
            return {"ok": drain(lambda: itertools.permutations(obj(c["obj"]), 1.5), tup)}
        return {"ok": drain_tuples(lambda: F(obj(c["obj"]), c["r"]), c["hold"])}
    if fn == "sizeof":
        f = getattr(itertools, KIND[c["kind"]])
        try:
            if c["kind"] == "product":
                kw = {} if c["r"] is None else {"repeat": c["r"]}
                return {"ok": f(*[obj(o) for o in c["objs"]], **kw).__sizeof__()}
            return {"ok": f(obj(c["obj"]), c["r"]).__sizeof__()}
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "count":
        kw = {k: dec_val(c[k]) for k in ("start", "step") if k in c}
        if impl == "c":
            cls = SubCount if c["sub"] else itertools.count
            return {"ok": run_ops(lambda: cls(**kw), c["ops"], enc_val)}
        k = c["ops"].count("n")
        return {"ok": [[], None] if k == 0 else drain(lambda: doc_count(**kw), enc_val, k)}
    if fn == "count_reentry":
        return run_count_reentry(c)
    if fn == "repeat":
        make = (lambda: F(c["elem"], c["times"])) if "times" in c else (lambda: F(c["elem"]))
        if impl == "c":
            return {"ok": run_ops(make, c["ops"])}
        k = c["ops"].count("n")
        return {"ok": [v for v, _ in zip(make(), range(k))]}
    if fn == "groupby":
        hooked = c.get("hooks") or c.get("khooks") or c.get("ihooks")
        return forked(lambda: run_groupby(c)) if hooked else run_groupby(c)
    if fn == "islice_r":
        return forked(lambda: run_islice_r(c)) if c["sole"] else run_islice_r(c)
    if fn in ("tee", "tee_wrap"):
        return run_tee(c, F)
    if fn == "teedata":
        nxt = {"none": None, "data": itertools._tee_dataobject(iter([]), [], None), "other": 3}[c["next"]]
        return cmsg(lambda: itertools._tee_dataobject(iter([]), [0] * c["len"], nxt))
    raise ValueError(fn)


if __name__ == "__main__":
    common.main(gen_case, run_python)
