"""Differential test: Lean models of itertools (C and doc equivalents) vs. the running CPython.

Usage: python3 difftest/itertools_diff.py [--cases N] [--seed S]

Each case names its side with "impl": "c" runs the `itertools` C object and
compares it with the Lean C model; "doc" runs the "Roughly equivalent to" code
of Doc/library/itertools.rst (copied below, verbatim apart from names) and
compares it with the Lean doc model. Iterators are drained into
[items, null | [class, message]]; islice also reports how many input items
were consumed; count/repeat/groupby/tee run a sequence of operations.

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
PREDS = {"lt5": lambda x: x < 5, "even": lambda x: x % 2 == 0, "pos": lambda x: x > 0,
         "nz": operator.truth, "none": None}
KEYS = {"id": lambda x: x, "div3": lambda x: x // 3, "mod2": lambda x: x % 2, "abs": abs,
        "neg": lambda x: -x}
BINOPS = {"add": operator.add, "mul": operator.mul, "max": max, "min": min,
          "sub": operator.sub}
STARS = {"sum": lambda *a: sum(a), "len": lambda *a: len(a)}

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
    return {"l": l, "args": args}


def gen_case(rng):
    fn = rng.choice(["islice", "islice", "islice", "batched", "accumulate", "chain", "compress",
                     "cycle", "dropwhile", "takewhile", "filterfalse", "pairwise", "starmap",
                     "zip_longest", "product", "combinations", "cwr", "permutations",
                     "count", "count", "repeat", "groupby", "groupby", "tee", "tee"])
    impl = rng.choice(["c", "doc"])
    c = {"mod": "itertools", "fn": fn, "impl": impl}
    if fn == "islice":
        c.update(gen_islice(rng))
    elif fn == "batched":
        n = rng.choice([1, 1, 2, 2, 3, 4, 5, 0, -1, -2**63, 10**6, rng.choice(HUGE)])
        c.update(l=small_list(rng), n=n, strict=rng.random() < 0.5)
    elif fn == "accumulate":
        c.update(l=small_list(rng), f=rng.choice(list(BINOPS)),
                 initial=rng.choice([None, None, 0, 7, -3, 2**70]))
    elif fn == "chain":
        c.update(ls=[small_list(rng, 4) for _ in range(rng.randrange(5))])
    elif fn == "compress":
        c.update(data=small_list(rng), sel=small_list(rng, span=1))
    elif fn == "cycle":
        c.update(l=small_list(rng, 5), k=rng.randrange(20))
    elif fn in ("dropwhile", "takewhile", "filterfalse"):
        preds = ["lt5", "even", "pos", "nz"] + (["none"] if fn == "filterfalse" else [])
        c.update(l=small_list(rng), pred=rng.choice(preds))
    elif fn == "pairwise":
        c.update(l=small_list(rng))
    elif fn == "starmap":
        c.update(ls=[small_list(rng, 3) for _ in range(rng.randrange(5))],
                 f=rng.choice(list(STARS)))
    elif fn == "zip_longest":
        c.update(ls=[small_list(rng, 5) for _ in range(rng.randrange(4))],
                 fill=rng.choice([None, 0, 9]))
    elif fn == "product":
        rep = rng.choice([None, None, 0, 1, 2, 3, -1, -2**63 - 1, M, 2**63, 2**61, M // 8,
                          M // 16, 2**59])
        npools = rng.randrange(4) if rep is None or not (0 < rep <= 3) else rng.randrange(3)
        if rep is not None and rep > 3 and impl == "doc":
            npools = 0 if rng.random() < 0.5 else npools  # [pools] * huge
        c.update(ls=[small_list(rng, 3, span=3) for _ in range(npools)], repeat=rep)
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
        c.update(l=l, r=r)
    elif fn == "count":
        def arg():
            return rng.choice([None, 0, 1, -1, 2, 5, M, M - 1, M - 2, M - 3, M + 1, -M - 1,
                               -M - 2, 2**64, -2**64, rng.randint(-10, 10)])
        c.update(start=arg(), step=rng.choice([None, None, 1, 1, 0, -1, 2, 3, M, -M - 1,
                                                M + 1, 2**64, -2**64, True and 1]),
                 ops=[rng.choice("nnr") for _ in range(rng.randrange(8))])
        if c["start"] is None:
            del c["start"]
        if c["step"] is None:
            del c["step"]
    elif fn == "repeat":
        times = rng.choice([None, None, 0, 1, 2, 3, -1, -5, M, -M - 1, M + 1, 2**64, -2**64])
        c.update(elem=rng.randint(-3, 3), ops=[rng.choice("nrh") for _ in range(rng.randrange(8))])
        if times is not None:
            c["times"] = times
        if impl == "doc" and times is not None and times > M:
            pass  # range(times) is fine in the doc
    elif fn == "groupby":
        c.update(l=small_list(rng, 12, span=rng.choice([1, 2, 4])),
                 key=rng.choice(list(KEYS)),
                 ops=[rng.choice(["o", "o", rng.randrange(4)]) for _ in range(rng.randrange(25))])
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
            elif x < 0.93:
                ops.append(["t", k, rng.randrange(3)])
            else:
                ops.append(["c", k])
        c.update(l=list(range(L)), n=n, ops=ops)
    return c


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


def run_python(c):
    fn, impl = c["fn"], c["impl"]
    F = (C if impl == "c" else DOC)[fn]
    tup = lambda t: list(t)
    if fn == "islice":
        it = iter(c["l"])
        r = drain(lambda: F(it, *c["args"]))
        rest = list(it)
        return {"ok": r + [len(c["l"]) - len(rest)]}
    if fn == "batched":
        return {"ok": drain(lambda: F(c["l"], c["n"], strict=c["strict"]), tup)}
    if fn == "accumulate":
        kw = {} if c["initial"] is None else {"initial": c["initial"]}
        return {"ok": drain(lambda: F(c["l"], BINOPS[c["f"]], **kw))}
    if fn == "chain":
        if impl == "c" and len(c["ls"]) % 2:
            return {"ok": drain(lambda: itertools.chain.from_iterable(iter(c["ls"])))}
        return {"ok": drain(lambda: F(*c["ls"]))}
    if fn == "compress":
        return {"ok": drain(lambda: F(c["data"], c["sel"]))}
    if fn == "cycle":
        return {"ok": drain(lambda: F(c["l"]), limit=c["k"]) if c["k"] else [[], None]}
    if fn in ("dropwhile", "takewhile"):
        return {"ok": drain(lambda: F(PREDS[c["pred"]], c["l"]))}
    if fn == "filterfalse":
        return {"ok": drain(lambda: F(PREDS[c["pred"]], c["l"]))}
    if fn == "pairwise":
        return {"ok": drain(lambda: F(c["l"]), tup)}
    if fn == "starmap":
        return {"ok": drain(lambda: F(STARS[c["f"]], c["ls"]))}
    if fn == "zip_longest":
        return {"ok": drain(lambda: F(*c["ls"], fillvalue=c["fill"]), tup)}
    if fn == "product":
        kw = {} if c["repeat"] is None else {"repeat": c["repeat"]}
        return {"ok": drain(lambda: F(*c["ls"], **kw), tup)}
    if fn in ("combinations", "cwr"):
        return {"ok": drain(lambda: F(c["l"], c["r"]), tup)}
    if fn == "permutations":
        return {"ok": drain(lambda: F(c["l"], c["r"]), tup)}
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
        g = F(c["l"], KEYS[c["key"]])
        groups, out = [], []
        for o in c["ops"]:
            if o == "o":
                try:
                    k, grp = next(g)
                    groups.append(grp)
                    out.append(k)
                except StopIteration:
                    out.append(None)
            elif o < len(groups):
                out.append(next(groups[o], None))
        return {"ok": out}
    if fn == "tee":
        src = iter(c["l"])
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
                out.append(next(tees[k], None))
            elif op[0] == "t":
                tees.extend(F(tees[k], op[2]))
            elif impl == "c":
                tees.append(tees[k].__copy__())
            else:
                tees.append(_tee(tees[k]))
        return {"ok": [out, len(c["l"]) - len(list(src))]}
    raise ValueError(fn)


if __name__ == "__main__":
    common.main(gen_case, run_python)
