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
import operator
import sys

import common

M = sys.maxsize

# ---------------------------------------------------------------------------
# Doc equivalents, Doc/library/itertools.rst (3.14).  islice is used by
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
KEYS = {"r3": boom("key", lambda x: x), "id": lambda x: x, "div3": lambda x: x // 3, "mod2": lambda x: x % 2, "abs": abs,
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

    def __iter__(self):
        return self

    def __next__(self):
        if self.pos < len(self.items):
            self.pos += 1
            self.pulled += 1
            return self.items[self.pos - 1]
        if self.err is not None:
            e, self.err = self.err, None
            raise ValueError(e)
        raise StopIteration


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


def gen_case(rng):
    fn = rng.choice(["islice", "islice", "islice", "islice_arity", "batched", "accumulate", "chain",
                     "chain_from", "compress", "cycle", "dropwhile", "takewhile", "filterfalse",
                     "pairwise", "starmap", "zip_longest", "product", "combinations", "cwr",
                     "permutations", "sizeof", "count", "count", "count_check", "repeat", "groupby",
                     "groupby", "tee", "tee", "teedata"])
    impl = rng.choice(["c", "doc"])
    c = {"mod": "itertools", "fn": fn, "impl": impl}
    if fn == "islice":
        c.update(gen_islice(rng))
    elif fn == "islice_arity":
        c.update(impl="c", nargs=rng.randrange(7), kw=rng.random() < 0.3)
    elif fn == "batched":
        n = rng.choice([1, 1, 2, 2, 3, 4, 5, 0, -1, -2**63, 10**6, rng.choice(HUGE)])
        c.update(obj=spec(rng, small_list(rng)), n=n, strict=rng.random() < 0.5)
    elif fn == "accumulate":
        c.update(obj=spec(rng, small_list(rng, span=4)), f=rng.choice(list(BINOPS)),
                 initial=rng.choice([None, None, 0, 7, -3, 2**70]))
    elif fn == "chain":
        c.update(objs=[spec(rng, small_list(rng, 4)) for _ in range(rng.randrange(5))])
        if impl == "c" and rng.random() < 0.1:
            c["kw"] = True
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
        c.update(obj=spec(rng, small_list(rng)))
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
        c.update(objs=[spec(rng, small_list(rng, 3, span=3)) for _ in range(npools)], repeat=rep)
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
        c.update(obj=spec(rng, l), r=r)
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
        def arg():
            return rng.choice([None, 0, 1, -1, 2, 5, M, M - 1, M - 2, M - 3, M + 1, -M - 1,
                               -M - 2, 2**64, -2**64, rng.randint(-10, 10)])
        c.update(start=arg(), step=rng.choice([None, None, 1, 1, 0, -1, 2, 3, M, -M - 1,
                                                M + 1, 2**64, -2**64]),
                 ops=[rng.choice("nnr") for _ in range(rng.randrange(8))])
        if c["start"] is None:
            del c["start"]
        if c["step"] is None:
            del c["step"]
    elif fn == "count_check":
        c.update(impl="c", a=rng.random() < 0.5, b=rng.random() < 0.5)
    elif fn == "repeat":
        times = rng.choice([None, None, 0, 1, 2, 3, -1, -5, M, -M - 1, M + 1, 2**64, -2**64])
        c.update(elem=rng.randint(-3, 3), ops=[rng.choice("nrh") for _ in range(rng.randrange(8))])
        if times is not None:
            c["times"] = times
    elif fn == "groupby":
        l = small_list(rng, 12, span=rng.choice([1, 2, 4]))
        keys = list(KEYS) if impl == "c" else [k for k in KEYS if k != "r3"]
        key = rng.choice(keys + ["r3"] * (impl == "c"))
        if key == "r3":
            l.insert(rng.randrange(len(l) + 1), 3)  # the value it raises on
        # Failing inputs and keys are C only: the doc generators die at the first
        # exception, and the Lean doc model has no failing calls.
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
            tgt = KEYS[key](rng.choice(vals)) if vals and rng.random() < 0.8 else rng.randint(-2, 2)
            ops[p:p] = [["d", tgt], made, made, made]
        c.update(obj=o, key=key, ops=ops)
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


def run_ops(obj_thunk, ops):
    try:
        obj = obj_thunk()
    except Exception as e:
        return [["exc"] + enc_exc(e)]
    out = []
    for o in ops:
        try:
            if o == "n":
                out.append(next(obj))
            elif o == "r":
                out.append(repr(obj))
            else:
                out.append(obj.__length_hint__())
        except StopIteration:
            out.append(None)
        except Exception as e:
            out.append(["exc"] + enc_exc(e))
    return out


def cmsg(f):
    """Raise-or-None as `{"ok": null}` / `{"exc": ..., "msg": ...}`."""
    try:
        f()
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    return {"ok": None}


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
        return cmsg(lambda: itertools.islice(*a, **({"stop": 1} if c["kw"] else {})))
    if fn == "batched":
        return {"ok": drain(lambda: F(obj(c["obj"]), c["n"], strict=c["strict"]), tup)}
    if fn == "accumulate":
        kw = {} if c["initial"] is None else {"initial": c["initial"]}
        return {"ok": drain(lambda: F(obj(c["obj"]), BINOPS[c["f"]], **kw))}
    if fn == "chain":
        if c.get("kw"):
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
        return {"ok": drain(lambda: F(obj(c["obj"])), tup)}
    if fn == "starmap":
        r = drain(lambda: F(STARS[c["f"]], objobj(c["src"])))
        if impl == "doc" and r[1] and "argument after *" in r[1][1]:
            r[1][1] = "~argument after * must be an iterable"
        return {"ok": r}
    if fn == "zip_longest":
        kw = dict(c["kw"])
        if len(c["kw"]) == 2:
            return {"ok": drain(lambda: F(*[obj(o) for o in c["objs"]], **kw), tup)}
        return {"ok": drain(lambda: F(*[obj(o) for o in c["objs"]], **kw), tup)}
    if fn == "product":
        kw = {} if c["repeat"] is None else {"repeat": c["repeat"]}
        return {"ok": drain(lambda: F(*[obj(o) for o in c["objs"]], **kw), tup)}
    if fn in ("combinations", "cwr"):
        return {"ok": drain(lambda: F(obj(c["obj"]), c["r"]), tup)}
    if fn == "permutations":
        if c.get("badr"):
            return cmsg(lambda: itertools.permutations(obj(c["obj"]), 1.5))
        return {"ok": drain(lambda: F(obj(c["obj"]), c["r"]), tup)}
    if fn == "sizeof":
        f = getattr(itertools, KIND[c["kind"]])
        try:
            if c["kind"] == "product":
                kw = {} if c["r"] is None else {"repeat": c["r"]}
                return {"ok": f(*[obj(o) for o in c["objs"]], **kw).__sizeof__()}
            return {"ok": f(obj(c["obj"]), c["r"]).__sizeof__()}
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "count_check":
        return cmsg(lambda: itertools.count(*(0 if c["a"] else "a", 1 if c["b"] else "b")))
    if fn in ("count", "repeat"):
        if fn == "count":
            kw = {k: c[k] for k in ("start", "step") if k in c}
            make = lambda: F(**kw)
        else:
            make = (lambda: F(c["elem"], c["times"])) if "times" in c else (lambda: F(c["elem"]))
        if impl == "c":
            return {"ok": run_ops(make, c["ops"])}
        k = c["ops"].count("n")
        return {"ok": [v for v, _ in zip(make(), range(k))]}
    if fn == "groupby":
        try:
            g = F(obj(c["obj"]), KEYS[c["key"]])
            groups, out = [], []
            for o in c["ops"]:
                if o == "o":
                    try:
                        k, grp = next(g)
                        groups.append(grp)
                        out.append(k)
                    except StopIteration:
                        out.append(None)
                    except ValueError as e:
                        out.append(["exc"] + enc_exc(e))
                elif isinstance(o, list):
                    groups.append(itertools._grouper(g, o[1]))
                elif o < len(groups):
                    try:
                        out.append(next(groups[o]))
                    except StopIteration:
                        out.append(None)
                    except ValueError as e:
                        out.append(["exc"] + enc_exc(e))
            return {"ok": out}
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
    if fn == "tee":
        src = obj(c["obj"])
        try:
            tees = list(F(src, c["n"]))
        except Exception as e:
            return {"exc": type(e).__name__, "msg": str(e)}
        out = []
        for op in c["ops"]:
            k = op[1]
            if k >= len(tees):
                continue
            if op[0] == "n":
                try:
                    out.append(next(tees[k]))
                except StopIteration:
                    out.append(None)
                except Exception as e:
                    out.append(["exc"] + enc_exc(e))
            elif op[0] == "t":
                tees.extend(F(tees[k], op[2]))
            elif impl == "c":
                tees.append(tees[k].__copy__() if op[0] == "c" else itertools._tee(tees[k]))
            else:
                tees.append(_tee(tees[k]))
        return {"ok": [out, src.pulled if isinstance(src, Source) else 0]}
    if fn == "teedata":
        nxt = {"none": None, "data": itertools._tee_dataobject(iter([]), [], None), "other": 3}[c["next"]]
        return cmsg(lambda: itertools._tee_dataobject(iter([]), [0] * c["len"], nxt))
    raise ValueError(fn)


if __name__ == "__main__":
    common.main(gen_case, run_python)
