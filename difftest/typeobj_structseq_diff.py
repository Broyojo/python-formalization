"""Differential test of Objects/structseq.c: the Lean model (TypeObj/StructSeqC.lean) vs. CPython.

Usage: python3 difftest/typeobj_structseq_diff.py [--cases N] [--seed S]

Each case carries a `PyStructSequence_Desc`. The Python side builds the type with
`PyStructSequence_NewType` through ctypes, or takes the real type the desc was read back from
(`os.terminal_size`, `time.struct_time`, `sys.flags`, ...); the Lean side builds it with its model
of `_PyStructSequence_NewType`. Then one of:

 * ss_newtype: the three size attributes, `__match_args__`, `__basicsize__`, and which slot each
   member attribute reads (found through `PyStructSequence_New`/`SetItem` and `getattr`);
 * ss_repr:    `repr()` of an object filled through the C API, with items whose `__repr__`
   returns or raises, `NULL` items, the size attributes rebound and the type renamed;
 * ss_capi:    `PyStructSequence_New`, then `SetItem`/`GetItem` at in-block indices;
 * ss_new:     the constructor with the size attributes rebound (missing, non-int, bool, int
               subclass, negative, too large, other ints), any sequence, any dict argument;
 * ss_reduce:  `__reduce__` after rebinding `n_unnamed_fields`;
 * ss_replace: `__replace__` with positional arguments, keywords, and rebound sizes.

The model reports undefined behaviour (out-of-bounds memory) as the class "UB", which never
agrees with Python. Rebindings that make CPython touch memory out of bounds crash the
interpreter, so the generator only rebinds sizes in ways that stay in bounds (the conditions are
in `safe_*`); those crashes are the bug record typeobj-structseq-mutable-size-attrs. Every
rebinding is undone after the case.
"""

import copy
import ctypes
import grp
import os
import pwd
import resource
import signal
import sys
import time

import common

api = ctypes.pythonapi


class Field(ctypes.Structure):
    _fields_ = [("name", ctypes.c_void_p), ("doc", ctypes.c_char_p)]


class Desc(ctypes.Structure):
    _fields_ = [("name", ctypes.c_char_p), ("doc", ctypes.c_char_p),
                ("fields", ctypes.POINTER(Field)), ("n_in_sequence", ctypes.c_int)]


UNNAMED = ctypes.c_void_p.in_dll(api, "PyStructSequence_UnnamedField").value
api.PyStructSequence_NewType.restype = ctypes.py_object
api.PyStructSequence_NewType.argtypes = [ctypes.POINTER(Desc)]
api.PyStructSequence_New.restype = ctypes.py_object
api.PyStructSequence_New.argtypes = [ctypes.py_object]
api.PyStructSequence_SetItem.restype = None
api.PyStructSequence_SetItem.argtypes = [ctypes.py_object, ctypes.c_ssize_t, ctypes.py_object]
api.PyStructSequence_GetItem.restype = ctypes.py_object
api.PyStructSequence_GetItem.argtypes = [ctypes.py_object, ctypes.c_ssize_t]
api.Py_IncRef.argtypes = [ctypes.py_object]

KEEP = []
TYPES = {}
KEYS = ["n_sequence_fields", "n_fields", "n_unnamed_fields"]


def mk_type(name, fields, nseq, fresh=False):
    """PyStructSequence_NewType on a desc; the C buffers are kept alive for good. A `fresh` type is
    for a case that renames it: setting `__name__` replaces `tp_name` for good."""
    key = (name, tuple(fields), nseq)
    if key in TYPES and not fresh:
        return TYPES[key]
    bufs = []
    arr = (Field * (len(fields) + 1))()
    for i, f in enumerate(fields):
        if f is None:
            arr[i].name = UNNAMED
        else:
            b = ctypes.create_string_buffer(bytes(f))
            bufs.append(b)
            arr[i].name = ctypes.cast(b, ctypes.c_void_p).value
    arr[len(fields)].name = None
    nb = ctypes.create_string_buffer(bytes(name))
    bufs.append(nb)
    d = Desc(ctypes.cast(nb, ctypes.c_char_p), None, arr, nseq)
    KEEP.append((bufs, arr, d))
    try:
        t = ("ok", api.PyStructSequence_NewType(ctypes.byref(d)))
    except Exception as e:
        t = ("exc", e)
    if not fresh:
        TYPES[key] = t
    return t


def std_desc(T):
    """The desc a real struct sequence type was built from, read back from the type."""
    ma = list(T.__match_args__)
    hidden = [k for k, v in T.__dict__.items()
              if type(v).__name__ == "member_descriptor" and k not in ma]
    fields = [k.encode() for k in ma] + [None] * T.n_unnamed_fields + [k.encode() for k in hidden]
    assert len(fields) == T.n_fields, T
    return {"name": list(f"{T.__module__}.{T.__name__}".encode()),
            "fields": [None if f is None else list(f) for f in fields],
            "nseq": T.n_sequence_fields}


# Real types whose tp_new is structseq_new (stat_result, statvfs_result and sched_param have
# their own), heap types whose attributes can be rebound.
STD_NEW = [os.terminal_size, time.struct_time, os.times_result, os.uname_result,
           os.waitid_result, resource.struct_rusage, pwd.struct_passwd, grp.struct_group,
           signal.struct_siginfo]
STD_HEAP = STD_NEW + [os.stat_result, os.statvfs_result, os.sched_param]
STD_STATIC = [type(sys.flags), type(sys.float_info), type(sys.int_info), type(sys.hash_info),
              type(sys.thread_info), type(sys.version_info)]
STATIC_OBJ = {type(o): o for o in [sys.flags, sys.float_info, sys.int_info, sys.hash_info,
                                   sys.thread_info, sys.version_info]}
STD_BY_NAME = {f"{T.__module__}.{T.__name__}": T for T in STD_HEAP + STD_STATIC}

NAMES = [b"a", b"b", b"c", b"x", b"yy", b"z1", "é".encode(), "ñame".encode(), "日本".encode(),
         b"unnamed field", b"k" * 40, b"F", b"_p", b"q_"]
TPNAMES = [b"m.T", b"m.S", b"T", b"pkg.mod.Name", "m.Tü".encode(), b"m." + b"Q" * 300, b"a.b"]


def rand_desc(rng, valid=True):
    n = rng.choice([0, 1, 1, 2, 2, 3, 3, 4, 5, 6, 8])
    names = rng.sample(NAMES, n)
    nseq = rng.randint(0, n)
    fields = list(names)
    # unnamed fields only among the visible ones (Objects/structseq.c:23-24)
    for i in range(nseq):
        if rng.random() < 0.2:
            fields[i] = None
    if not valid:
        if nseq < n and rng.random() < 0.3:
            # an unnamed hidden field, which structseq.c:23-24 forbids and NewType accepts
            fields[rng.randrange(nseq, n)] = None
        else:
            nseq = rng.choice([n + 1, n + 2, n + 3, n + 5, n + 6, n + 9, -1, -2, -7])
    return {"name": list(rng.choice(TPNAMES)), "fields": [None if f is None else list(f) for f in fields],
            "nseq": nseq}


def pick_type(rng, kinds=("ctypes", "std")):
    """A desc, and how the Python side gets the type."""
    kind = rng.choice(kinds)
    if kind == "std":
        T = rng.choice(STD_NEW)
        return std_desc(T), ("std", f"{T.__module__}.{T.__name__}")
    d = rand_desc(rng)
    return d, ("ctypes",)


def get_type(case, fresh=False):
    d = case["desc"]
    if case["src"][0] == "ctypes":
        return mk_type(bytes(d["name"]), [None if f is None else bytes(f) for f in d["fields"]], d["nseq"],
                       fresh)
    return ("ok", STD_BY_NAME[case["src"][1]])


def layout(d):
    n = len(d["fields"])
    named = [i for i, f in enumerate(d["fields"]) if f is not None]
    return n, d["nseq"], n - d["nseq"], len(named), [bytes(d["fields"][i]).decode() for i in named], named


# --- size-attribute rebindings ---------------------------------------------------------------

class IndexOnly:
    def __index__(self):
        return 1


class IntSub(int):
    pass


def lie_value(lie):
    if lie == "other":
        return None  # chosen by the runner
    if lie.get("bool"):
        return bool(lie["int"])
    if lie.get("sub"):
        return IntSub(lie["int"])
    return lie["int"]


OTHERS = [1.5, "3", IndexOnly(), None, (), 2.0]


def rand_err_lie(rng):
    return rng.choice(["del", "other", {"int": -1}, {"int": -2}, {"int": -(2 ** 40)},
                       {"int": 2 ** 63}, {"int": -2 ** 63 - 1}, {"int": 2 ** 64}, {"int": -1, "sub": True}])


def rand_int_lie(rng, base):
    v = rng.choice([0, 1, 2, base, base + 1, base + 2, max(0, base - 1), rng.randint(0, 12)])
    r = rng.random()
    if r < 0.1 and v in (0, 1):
        return {"int": v, "bool": True}
    if r < 0.2:
        return {"int": v, "sub": True}
    return {"int": v}


def read_order(lies, honest, order):
    """The values the reads in `order` see, or None once one of them fails or is negative."""
    out = []
    for k in order:
        lie = lies.get(k)
        if lie is None:
            out.append(honest[k])
            continue
        if lie in ("del", "other"):
            return None
        v = lie["int"]
        if v < 0 or v > 2 ** 63 - 1:
            return None
        out.append(v)
    return out


def apply_lies(T, lies, rng_other):
    saved = {k: T.__dict__[k] for k in KEYS}
    for k, lie in lies.items():
        if lie == "del":
            delattr(T, k)
        elif lie == "other":
            setattr(T, k, rng_other)
        else:
            setattr(T, k, lie_value(lie))
    return saved


def restore(T, saved):
    for k, v in saved.items():
        setattr(T, k, v)


def enc(r):
    if "exc" in r and r["exc"] == "ValueError" and r["msg"] == "PyObject is NULL":
        return {"exc": "SystemError", "msg": "NULL without exception (through ctypes)"}
    return r


def val_out(v):
    return v


# --- generators ------------------------------------------------------------------------------

VALS = [0, 1, -1, 2 ** 63, None, "s", "é", 7, 42]


def gen_newtype(rng):
    if rng.random() < 0.25:
        T = rng.choice(STD_HEAP + STD_STATIC)
        return {"desc": std_desc(T), "src": ["std", f"{T.__module__}.{T.__name__}"]}
    return {"desc": rand_desc(rng, valid=rng.random() < 0.75), "src": ["ctypes"]}


def item_kind(rng):
    k = rng.random()
    if k < 0.25:
        return ["int", rng.choice([0, 1, -5, 10 ** 30, 2 ** 64])]
    if k < 0.3:
        return ["bigint"]
    if k < 0.45:
        return ["str", rng.choice(["", "a", "é😀", "x'y", 'q"'])]
    if k < 0.5:
        return ["none"]
    if k < 0.8:
        return ["custom", rng.choice(["", "R", "é", "日本語", "x" * 50, "a, b=c", "(", ")"])]
    return ["raise", rng.choice(["ValueError", "RuntimeError", "ZeroDivisionError"]),
            rng.choice(["boom", "", "é"])]


def item_obj(kind):
    if kind[0] == "int":
        return kind[1]
    if kind[0] == "bigint":
        return 10 ** 5000
    if kind[0] == "str":
        return kind[1]
    if kind[0] == "none":
        return None
    if kind[0] == "custom":
        text = kind[1]

        class R:
            def __repr__(self):
                return text
        return R()
    cls = {"ValueError": ValueError, "RuntimeError": RuntimeError,
           "ZeroDivisionError": ZeroDivisionError}[kind[1]]
    msg = kind[2]

    class E:
        def __repr__(self):
            raise cls(msg)
    return E()


def item_beh(kind):
    """What repr() of the item does, as the model's `rep` takes it."""
    try:
        return {"r": repr(item_obj(kind))}
    except Exception as e:
        return {"e": [type(e).__name__, str(e)]}


def gen_repr(rng):
    if rng.random() < 0.08:
        T = rng.choice(STD_STATIC)
        o = STATIC_OBJ[T]
        sets = [[i, {"r": repr(o[i])}] for i in range(T.n_sequence_fields)]
        return {"desc": std_desc(T), "src": ["static", f"{T.__module__}.{T.__name__}"], "lies": {},
                "rename": None, "rename_s": None, "sets": sets, "kinds": []}
    d, src = pick_type(rng)
    n, v, h, nn, _, _ = layout(d)
    lies = {}
    a, b = v, n
    if rng.random() < 0.4:
        b = rng.choice([n, n + 1, n + 3, rng.randint(0, 10)])
        a = rng.randint(0, max(0, b - h)) if b >= h else None
        if a is None:
            b, a = n, v
        lies = {"n_fields": {"int": b}, "n_sequence_fields": {"int": a}}
    sets, kinds = [], []
    for i in range(b):
        if rng.random() < 0.85:
            k = item_kind(rng)
            kinds.append([i, k])
            sets.append([i, item_beh(k)])
    rename = None
    if src[0] == "ctypes" and rng.random() < 0.2:
        rename = rng.choice(["Z", "Zé😀", "Q" * 700, "x.y", "名前"])
    return {"desc": d, "src": list(src), "lies": lies,
            "rename": list(rename.encode()) if rename else None, "rename_s": rename,
            "sets": sets, "kinds": kinds}


def gen_capi(rng):
    d, src = pick_type(rng)
    n, v, h, _, _, _ = layout(d)
    lies, a, b = {}, v, n
    if rng.random() < 0.3:
        b = rng.choice([n, n + 2, rng.randint(h, h + 6)])
        a = rng.randint(0, max(0, b - h))
        lies = {"n_fields": {"int": b}, "n_sequence_fields": {"int": a}}
    cap = h + b
    ops, setidx = [], set()
    for _ in range(rng.randint(0, 8)):
        if cap and rng.random() < 0.6:
            i = rng.randrange(cap)
            ops.append(["set", i, rng.choice(VALS)])
            setidx.add(i)
        else:
            cands = [i for i in range(b)] + sorted(setidx)
            if cands:
                ops.append(["get", rng.choice(cands)])
    return {"desc": d, "src": list(src), "lies": lies, "ops": ops}


def rand_seq(rng, d, nmin, nmax):
    ln = rng.choice([nmin, nmax, rng.randint(max(0, nmin - 1), nmax + 1), 0])
    return [rng.choice(VALS) for _ in range(ln)]


def rand_dict(rng, d):
    n, v, h, _, names, idx = layout(d)
    hidden = [bytes(d["fields"][i]).decode() for i in range(v, n) if d["fields"][i] is not None]
    r = rng.random()
    if r < 0.4:
        return None
    if r < 0.45:
        return "notdict"
    keys = set()
    for _ in range(rng.randint(0, 3)):
        r = rng.random()
        if r < 0.6 and hidden:
            keys.add(rng.choice(hidden))
        elif r < 0.8 and names:
            keys.add(rng.choice(names))
        else:
            keys.add(rng.choice(["bogus", "n_fields", "zz"]))
    return [[k, rng.choice(VALS)] for k in sorted(keys)]


def honest_of(d):
    n, v, _, _, _, _ = layout(d)
    u = sum(1 for f in d["fields"] if f is None)
    return {"n_sequence_fields": v, "n_fields": n, "n_unnamed_fields": u}


def rand_lies(rng, d, keys=KEYS):
    hon = honest_of(d)
    lies = {}
    for k in keys:
        r = rng.random()
        if r < 0.15:
            lies[k] = rand_err_lie(rng)
        elif r < 0.45:
            lies[k] = rand_int_lie(rng, hon[k])
    return lies


def safe_new(case):
    """The constructor stays in bounds: a failing read stops it before the allocation; else the
    block (hidden + n_fields slots) must hold the copied items and Py_SIZE + hidden (dealloc),
    and the dict loop must index tp_members inside the array."""
    d = case["desc"]
    n, v, h, nn, _, _ = layout(d)
    vals = read_order(case["lies"], honest_of(d), ["n_sequence_fields", "n_fields", "n_unnamed_fields"])
    if vals is None:
        return True
    a, b, c = vals
    if case["seq"] == "notseq" or case["dict"] == "notdict":
        return True
    ln = len(case["seq"])
    if (a != b and (ln < a or ln > b)) or (a == b and ln != a):
        return True
    if b > 64:
        return b > 2 ** 45  # MemoryError before anything is written
    if a + h > b:
        return False
    if case["dict"]:
        return all(0 <= i - c < nn for i in range(ln, b))
    return True


def gen_new(rng):
    d, src = pick_type(rng)
    n, v, _, _, _, _ = layout(d)
    for _ in range(50):
        lies = rand_lies(rng, d)
        if rng.random() < 0.05:
            lies["n_fields"] = {"int": 2 ** 50}
        case = {"desc": d, "src": list(src), "lies": lies,
                "seq": "notseq" if rng.random() < 0.05 else rand_seq(rng, d, v, n),
                "seqkind": rng.choice(["list", "tuple", "gen"]),
                "dict": rand_dict(rng, d), "other": rng.randrange(len(OTHERS))}
        if safe_new(case):
            return case
    return None


def honest_init(rng, d):
    n, v, _, _, _, _ = layout(d)
    seq = [rng.choice(VALS) for _ in range(rng.randint(v, n))]
    hidden = [bytes(d["fields"][i]).decode() for i in range(len(seq), n) if d["fields"][i] is not None]
    dct = [[k, rng.choice(VALS)] for k in hidden if rng.random() < 0.7]
    return seq, dct


def safe_reduce(case):
    d = case["desc"]
    n, v, h, nn, _, _ = layout(d)
    vals = read_order(case["lies"], honest_of(d), ["n_unnamed_fields"])
    if vals is None:
        return True
    c = vals[0]
    return all(0 <= i - c < nn for i in range(v, n))


def gen_reduce(rng):
    d, src = pick_type(rng)
    for _ in range(50):
        seq, dct = honest_init(rng, d)
        case = {"desc": d, "src": list(src), "seq": seq, "seqkind": "tuple", "dict": dct or None,
                "lies": rand_lies(rng, d, ["n_unnamed_fields", "n_fields"]),
                "other": rng.randrange(len(OTHERS))}
        if safe_reduce(case):
            return case
    return None


def safe_replace(case):
    d = case["desc"]
    n, v, h, nn, _, _ = layout(d)
    if case["nargs"]:
        return True
    vals = read_order(case["lies"], honest_of(d), ["n_unnamed_fields"])
    if vals is None or vals[0] > 0:
        return True
    if nn < n:  # n_unnamed_fields rebound to 0 on a type with unnamed fields
        return False
    vals = read_order(case["lies"], honest_of(d), ["n_fields", "n_sequence_fields"])
    if vals is None:
        return True
    b, a = vals
    if b > 64:
        return b > 2 ** 45
    return b >= v and a <= v and a + h <= b


def gen_replace(rng):
    d, src = pick_type(rng)
    n, v, _, nn, names, _ = layout(d)
    for _ in range(50):
        seq, dct = honest_init(rng, d)
        kws = None
        if rng.random() < 0.8:
            ks = set()
            for _ in range(rng.randint(0, 3)):
                ks.add(rng.choice(names + ["bogus", "zz"]) if names else "bogus")
            kws = [[k, rng.choice(VALS)] for k in sorted(ks)]
        case = {"desc": d, "src": list(src), "seq": seq, "seqkind": "tuple", "dict": dct or None,
                "lies": rand_lies(rng, d) if rng.random() < 0.5 else {},
                "nargs": 1 if rng.random() < 0.05 else 0, "kws": kws,
                "other": rng.randrange(len(OTHERS))}
        if safe_replace(case):
            return case
    return None


GENS = [("ss_newtype", gen_newtype, 2), ("ss_repr", gen_repr, 3), ("ss_capi", gen_capi, 2),
        ("ss_new", gen_new, 4), ("ss_reduce", gen_reduce, 2), ("ss_replace", gen_replace, 3)]


def gen_case(rng):
    fn, g, _ = rng.choices(GENS, weights=[w for _, _, w in GENS])[0]
    c = g(rng)
    if c is None:
        return None
    c["mod"] = "typeobj"
    c["fn"] = fn
    return c


# --- the Python side ---------------------------------------------------------------------------

def visible(o):
    return list(tuple(o))


def reduce_out(o):
    cls, (tup, dct) = o.__reduce__()
    return [list(tup), [[k, v] for k, v in dct.items()]]


def make_seq(case):
    s = case["seq"]
    if s == "notseq":
        return 5
    if case.get("seqkind") == "list":
        return list(s)
    if case.get("seqkind") == "gen":
        return (x for x in s)
    return tuple(s)


def make_dict(case):
    d = case["dict"]
    if d is None:
        return None
    if d == "notdict":
        return []
    return {k: v for k, v in d}


def construct(T, case):
    dct = make_dict(case)
    if dct is None:
        return T(make_seq(case))
    return T(make_seq(case), dct)


def run_newtype(case):
    if case["src"][0] == "std":
        T = STD_BY_NAME[case["src"][1]]
    else:
        kind, T = get_type(case)
        if kind == "exc":
            raise T
    d = case["desc"]
    n = len(d["fields"])
    members = []
    if T in STATIC_OBJ:
        # no new instances of a static type: the slot of each member is read off the desc,
        # which std_desc built from the member descriptors' order
        members = [[bytes(f).decode(), i] for i, f in enumerate(d["fields"]) if f is not None]
    else:
        o = api.PyStructSequence_New(T)
        for i in range(n):
            val = ("slot", i)
            api.Py_IncRef(val)
            api.PyStructSequence_SetItem(o, i, val)
        for f in d["fields"]:
            if f is not None:
                nm = bytes(f).decode()
                members.append([nm, getattr(o, nm)[1]])
    return [T.n_sequence_fields, T.n_fields, T.n_unnamed_fields, list(T.__match_args__),
            T.__basicsize__, members]


def run_repr(case):
    if case["src"][0] == "static":
        return repr(STATIC_OBJ[STD_BY_NAME[case["src"][1]]])
    kind, T = get_type(case, fresh=case["rename_s"] is not None)
    if kind == "exc":
        raise T
    if case["rename_s"] is not None:
        T.__name__ = case["rename_s"]
    saved = apply_lies(T, case["lies"], None)
    try:
        o = api.PyStructSequence_New(T)
        for i, k in case["kinds"]:
            x = item_obj(k)
            api.Py_IncRef(x)
            api.PyStructSequence_SetItem(o, i, x)
    finally:
        restore(T, saved)
    return repr(o)


def run_capi(case):
    kind, T = get_type(case)
    if kind == "exc":
        raise T
    saved = apply_lies(T, case["lies"], None)
    try:
        o = api.PyStructSequence_New(T)
    finally:
        restore(T, saved)
    outs = []
    for op in case["ops"]:
        if op[0] == "set":
            api.Py_IncRef(op[2])
            api.PyStructSequence_SetItem(o, op[1], op[2])
        else:
            try:
                outs.append(api.PyStructSequence_GetItem(o, op[1]))
            except ValueError as e:
                if str(e) != "PyObject is NULL":
                    raise
                outs.append("NULL")
    return [len(o), outs]


def run_new(case):
    kind, T = get_type(case)
    if kind == "exc":
        raise T
    saved = apply_lies(T, case["lies"], OTHERS[case["other"]])
    try:
        o = construct(T, case)
    finally:
        restore(T, saved)
    return visible(o)


def run_reduce(case):
    kind, T = get_type(case)
    if kind == "exc":
        raise T
    o = construct(T, case)
    saved = apply_lies(T, case["lies"], OTHERS[case["other"]])
    try:
        return reduce_out(o)
    finally:
        restore(T, saved)


def run_replace(case):
    kind, T = get_type(case)
    if kind == "exc":
        raise T
    o = construct(T, case)
    saved = apply_lies(T, case["lies"], OTHERS[case["other"]])
    try:
        kws = {k: v for k, v in case["kws"]} if case["kws"] is not None else {}
        r = o.__replace__(*([1] * case["nargs"]), **kws)
    finally:
        restore(T, saved)
    return [visible(r), reduce_out(r)]


RUN = {"ss_newtype": run_newtype, "ss_repr": run_repr, "ss_capi": run_capi, "ss_new": run_new,
       "ss_reduce": run_reduce, "ss_replace": run_replace}


def run_python(case):
    return enc(common.py_result(lambda: RUN[case["fn"]](case)))


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=50000)
