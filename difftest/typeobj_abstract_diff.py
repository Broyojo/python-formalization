"""Differential test of the Objects/abstract.c protocols in the TypeObj model.

Usage: python3 difftest/typeobj_abstract_diff.py [--cases N] [--seed S]

The scenarios are those of typeobj_diff.py (same tree format, same Lean handler), generated to
reach every branch of PyObject_GetItem, the binary and in-place number dispatch, iteration,
_PySequence_IterSearch (through `in`, operator.countOf and operator.indexOf), isinstance and
issubclass (unions, tuples, __instancecheck__, __class__, __bases__), with hooks that log,
return odd values, raise, and re-enter. A second kind of case compares PyBuffer_IsContiguous on
_testbuffer.ndarray views of random shape, strides and suboffsets.
"""

import sys

import common
import typeobj_diff as td
from typeobj_diff import G, NONE, NOTIMPL, attr, call, cls, lit, name

EXC = ["AttributeError", "TypeError", "ValueError", "IndexError", "StopIteration", "KeyError"]


def ret_or_raise(g, q, vals, p_raise=0.25, excs=EXC):
    """A method body: log `q`, then return one of `vals` or raise."""
    r = g.rng
    if r.random() < p_raise:
        return [["log", q], ["raise", call(name(r.choice(excs)), lit("boom"))]]
    return [["log", q], ["ret", r.choice(vals)]]


def meth(g, n, q, params, body):
    return g.method(n, q, params, body)


def fam_getitem(g):
    """PyObject_GetItem: mp_subscript, sq_item, type[...], __class_getitem__, both errors."""
    r = g.rng
    mbody = []
    if r.random() < 0.4:
        mbody.append(meth(g, "__getitem__", "M.__getitem__", ["c", "k"],
                          ret_or_raise(g, "M.__getitem__", [lit(1), name("k"), NONE])))
    if r.random() < 0.3:
        # A __class_getitem__ found on the metaclass, as a property that renames the class:
        # the "not subscriptable" message reads tp_name after the lookup.
        mbody.append(meth(g, "_cg", "M._cg", ["c"],
                          [["log", "M._cg"], ["setattr", name("c"), "__name__", lit("Renamed")],
                           ["ret", r.choice([NONE, name("_f")])]]))
        mbody.append(["assign", "__class_getitem__", call(name("property"), name("_cg"))])
    cls(g, "M", ["type"], mbody or None)
    g.main.append(["def", "_f", "_f", {"pos": ["k"], "posonly": 0, "kwonly": [], "varargs": None,
                                       "varkw": None, "defaults": [], "kwdefaults": []},
                   g.code([["log", "_f"], ["ret", name("k")]])])
    kbody = []
    k = r.randrange(5)
    if k == 0:
        kbody.append(meth(g, "__class_getitem__", "K.__class_getitem__", ["c", "item"],
                          ret_or_raise(g, "K.__class_getitem__", [name("item"), lit(7)])))
    elif k == 1:
        kbody.append(["assign", "__class_getitem__", NONE])
    elif k == 2:
        kbody.append(["assign", "__class_getitem__", lit(3)])
    if r.random() < 0.5:
        kbody.append(meth(g, "__getitem__", "K.__getitem__", ["s", "i"],
                          ret_or_raise(g, "K.__getitem__", [name("i"), lit(0)])))
    meta = [("metaclass", name("M"))] if r.random() < 0.5 else []
    cls(g, "K", [], kbody or None, kw=meta)
    cls(g, "L", ["K"], None)
    g.main.append(["probes", g.next_tag(), [["assign", "k", call(name("K"))]]])
    keys = [lit(0), lit(-1), lit(5), lit("a"), NONE, lit(True), lit(["bigint", str(2**64)]),
            lit(["bigint", str(-2**63 - 1)]), name("int"), ["tuple", [lit(1)]]]
    for o in [name("K"), name("L"), name("k"), name("M"), name("int"), name("object"),
              name("type"), lit(1), NONE, ["list", [lit(1), lit(2)]], ["tuple", [lit(1)]],
              lit("ab"), ["dict", [[lit(0), lit("z")]]]]:
        g.probe(["sub", o, r.choice(keys)])
    g.probe(["is", ["sub", name("type"), name("int")], ["sub", name("type"), name("int")]])
    g.probe(attr(name("K"), "__name__"))


def num_class(g, cname, ops, vals, base=()):
    """A class whose dunders for `ops` log and return or raise."""
    body = []
    for n in ops:
        q = f"{cname}.{n}"
        params = ["s", "o", "m"] if n in ("__pow__", "__rpow__") and g.rng.random() < 0.3 \
            else ["s", "o"]
        body.append(meth(g, n, q, params, ret_or_raise(g, q, vals, p_raise=0.15)))
    if g.rng.random() < 0.3:
        body.append(meth(g, "__index__", f"{cname}.__index__", ["s"],
                         ret_or_raise(g, f"{cname}.__index__",
                                      [lit(2), lit(0), lit(-1), lit("x"), lit(True),
                                       lit(["bigint", str(2**63)])], p_raise=0.1)))
    cls(g, cname, base, body or None)


def fam_binops(g):
    """binary_op1's slot order and subclass rule, PyNumber_Add/Multiply fallbacks, binary_iop,
    PyNumber_InPlaceAdd and ternary_iop, with NotImplemented, raising and odd results."""
    r = g.rng
    vals = [NOTIMPL, NOTIMPL, lit(1), lit("r"), NONE, name("s"), name("o")]
    pick = lambda names: r.sample(names, r.randrange(len(names) + 1))
    num_class(g, "A", pick(["__add__", "__radd__", "__iadd__", "__mul__", "__rmul__", "__imul__",
                            "__pow__", "__rpow__", "__ipow__", "__sub__", "__isub__"]), vals)
    num_class(g, "B", pick(["__add__", "__radd__", "__mul__", "__rmul__", "__pow__", "__rpow__",
                            "__iadd__", "__ipow__"]), vals,
              base=r.choice([(), ("A",)]))
    num_class(g, "C", pick(["__radd__", "__rmul__", "__rpow__", "__add__"]), vals)
    for v in ["a", "b", "c"]:
        g.main.append(["probes", g.next_tag(), [["assign", v, call(name(v.upper()))]]])
    ops = [name("a"), name("b"), name("c"), lit(2), lit("ab"), ["list", [lit(1)]],
           ["tuple", [lit(1)]], NONE, lit(True)]
    for _ in range(r.randrange(8, 16)):
        x, y = r.choice(ops), r.choice(ops)
        g.probe(["bin", r.choice(["+", "*", "-", "**"]), x, y])
    # In-place forms, on fresh bindings so each starts from a known value.
    for _ in range(r.randrange(4, 9)):
        tgt = r.choice(["a", "b", "c", "lst", "tup", "n", "st"])
        init = {"a": call(name("A")), "b": call(name("B")), "c": call(name("C")),
                "lst": ["list", [lit(1)]], "tup": ["tuple", [lit(1)]], "n": lit(3),
                "st": lit("ab")}[tgt]
        g.main.append(["probes", g.next_tag(), [["assign", "t", init]]])
        op = r.choice(["+", "*", "-", "**"])
        g.probes(["aug", "t", op, r.choice(ops)])
        g.probe(name("t"))


def fam_iter(g):
    """PyObject_GetIter, PyIter_Next, _PySequence_IterSearch (in, countOf, indexOf)."""
    r = g.rng
    cls(g, "Stop", ["StopIteration"], None)
    body = []
    k = r.randrange(6)
    if k == 0:
        body.append(meth(g, "__iter__", "I.__iter__", ["s"],
                         ret_or_raise(g, "I.__iter__", [name("s"), lit(1), NONE, call(
                             name("iter"), ["list", [lit(1), lit(2)]])], p_raise=0.15)))
    elif k == 1:
        body.append(["assign", "__iter__", NONE])
    elif k == 2:
        body.append(meth(g, "__iter__", "I.__iter__", ["s"], [["log", "I.__iter__"],
                                                              ["ret", name("s")]]))
    if r.random() < 0.7:
        # __next__ counts up through `s.n`, then stops in one of several ways.
        stop = r.choice([["raise", name("StopIteration")], ["raise", call(name("Stop"))],
                         ["raise", call(name(r.choice(["ValueError", "IndexError"])), lit("nx"))]])
        limit = r.choice([0, 1, 2, 3])
        body.append(meth(g, "__next__", "I.__next__", ["s"], [
            ["log", "I.__next__"],
            ["if", ["cmp", ">=", attr(name("s"), "n"), lit(limit)], [stop],
             [["setattr", name("s"), "n", ["bin", "+", attr(name("s"), "n"), lit(1)]],
              ["ret", attr(name("s"), "n")]]]]))
    if r.random() < 0.5:
        limit = r.choice([0, 1, 2])
        body.append(meth(g, "__getitem__", "I.__getitem__", ["s", "i"], [
            ["log", "I.__getitem__"],
            ["if", ["cmp", ">=", name("i"), lit(limit)],
             [["raise", name(r.choice(["IndexError", "StopIteration", "KeyError"]))]],
             [["ret", ["bin", "+", name("i"), lit(1)]]]]]))
    if r.random() < 0.2:
        body.append(meth(g, "__contains__", "I.__contains__", ["s", "x"],
                         ret_or_raise(g, "I.__contains__", [lit(0), lit(1), NONE, lit("")])))
    body.append(["assign", "n", lit(0)])
    cls(g, "I", [], body)
    # Items whose __eq__ answers oddly or raises.
    cls(g, "E", [], [meth(g, "__eq__", "E.__eq__", ["s", "o"],
                          ret_or_raise(g, "E.__eq__", [lit(True), lit(False), NOTIMPL, lit(0),
                                                       lit("y")], p_raise=0.3))])
    targets = [lit(1), lit(2), lit(3), lit(9), call(name("E")), NONE]
    for _ in range(r.randrange(5, 10)):
        g.main.append(["probes", g.next_tag(), [["assign", "it", call(name("I"))]]])
        k = r.randrange(9)
        if k == 0:
            g.probe(call(name("list"), name("it")))
        elif k == 1:
            g.probe(call(name("iter"), name("it")))
        elif k == 2:
            g.probe(call(name("next"), call(name("iter"), name("it"))))
        elif k == 3:
            g.probe(["in", r.choice(targets), name("it")])
        elif k == 4:
            g.probe(call(name("countOf"), name("it"), r.choice(targets)))
        elif k == 5:
            g.probe(call(name("indexOf"), name("it"), r.choice(targets)))
        elif k == 6:
            seq = r.choice([["list", [lit(1), call(name("E")), lit(2), lit(1)]],
                            ["tuple", [call(name("E")), lit(3)]], lit("abca"), lit(5), NONE,
                            ["list", []]])
            g.probe(call(name(r.choice(["countOf", "indexOf"])), seq,
                         r.choice(targets + [lit("a")])))
        elif k == 7:
            g.probe(["in", r.choice(targets), r.choice([lit(5), NONE, ["list", [lit(1)]]])])
        else:
            g.probe(call(name("next"), name("it")))


def fam_isinstance(g):
    """object_recursive_isinstance, object_isinstance, recursive_issubclass,
    abstract_issubclass and abstract_get_bases, through every hook."""
    r = g.rng
    mbody = []
    if r.random() < 0.5:
        mbody.append(meth(g, "__instancecheck__", "M.__instancecheck__", ["c", "x"],
                          ret_or_raise(g, "M.__instancecheck__",
                                       [lit(True), lit(False), lit(0), lit("s"), NONE])))
    if r.random() < 0.5:
        mbody.append(meth(g, "__subclasscheck__", "M.__subclasscheck__", ["c", "x"],
                          ret_or_raise(g, "M.__subclasscheck__",
                                       [lit(True), lit(False), lit(1), lit(""), NONE])))
    cls(g, "M", ["type"], mbody or None)
    cls(g, "P", [], None, kw=[("metaclass", name("M"))] if r.random() < 0.5 else [])
    cls(g, "Q", ["P"], None)
    cls(g, "R", [], None)
    # An instance whose __class__ is a property: another class, a non-class, or a raise.
    cbody = [meth(g, "_c", "X._c", ["s"],
                  ret_or_raise(g, "X._c", [name("Q"), name("R"), lit(1), name("X"), name("ab")],
                               p_raise=0.3, excs=["AttributeError", "ValueError"])),
             ["assign", "__class__", call(name("property"), name("_c"))]]
    cls(g, "X", [], cbody if r.random() < 0.7 else None)
    # "Abstract classes": objects with a __bases__ property, used where classes go.
    # ab's bases may name ac, ac's never name either, so no walk cycles (a cycle through
    # one base loops forever in CPython, abstract.c:2546-2564, with no recursion check).
    for nm in ["ac", "ab"]:
        extra = [["tuple", [name("ac")]], ["tuple", [name("R"), name("ac")]]] if nm == "ab" else []
        bb = [meth(g, "_b", f"{nm}._b", ["s"],
                   ret_or_raise(g, f"{nm}._b",
                                [["tuple", []], ["tuple", [name("P")]],
                                 ["tuple", [name("R"), name("P")]], lit(1),
                                 ["list", [name("P")]]] + extra,
                                p_raise=0.25, excs=["AttributeError", "ValueError"])),
              ["assign", "__bases__", call(name("property"), name("_b"))]]
        cls(g, nm.upper(), [], bb)
        g.main.append(["probes", g.next_tag(), [["assign", nm, call(name(nm.upper()))]]])
    for v in ["P", "Q", "R", "X"]:
        g.main.append(["probes", g.next_tag(), [["assign", v.lower(), call(name(v))]]])
    unions = [["bin", "|", name("int"), name("str")], ["bin", "|", name("P"), NONE],
              ["bin", "|", ["bin", "|", name("R"), name("Q")], name("R")],
              ["bin", "|", name("Q"), name("Q")], ["bin", "|", NONE, NONE],
              ["bin", "|", name("int"), lit(1)]]
    clss = [name("P"), name("Q"), name("R"), name("X"), name("M"), name("int"), name("object"),
            name("ab"), name("ac"), lit(1), ["tuple", []], ["tuple", [name("R"), name("P")]],
            ["tuple", [["tuple", [name("Q")]], name("ab")]], r.choice(unions), r.choice(unions)]
    insts = [name("p"), name("q"), name("r"), name("x"), lit(1), lit(True), NONE, name("ab"),
             name("P"), name("int")]
    for _ in range(r.randrange(8, 16)):
        if r.random() < 0.55:
            g.probe(call(name("isinstance"), r.choice(insts), r.choice(clss)))
        else:
            g.probe(call(name("issubclass"), r.choice(insts[4:] + [name("Q"), name("R")]),
                         r.choice(clss)))
    # type.__instancecheck__ and __subclasscheck__ reach object_isinstance and
    # recursive_issubclass directly.
    g.probe(call(attr(name("type"), "__instancecheck__"), r.choice(clss[:7]), r.choice(insts)))
    g.probe(call(attr(name("type"), "__subclasscheck__"), r.choice(clss[:7]),
                 r.choice(insts[4:] + [name("ab"), name("Q")])))


FAMS = [fam_getitem, fam_binops, fam_iter, fam_isinstance]


def gen_buffer(rng):
    """A _testbuffer.ndarray view: shape, strides (multiples of the item size, possibly
    negative or zero), offset chosen so the view fits, with or without suboffsets, or a
    re-export without strides."""
    fmt, itemsize = rng.choice([("B", 1), ("i", 4), ("d", 8)])
    ndim = rng.choice([0, 1, 1, 2, 2, 2, 3, 3])
    shape = [rng.choice([0, 1, 1, 2, 3, 4]) for _ in range(ndim)]
    kind = rng.random()
    if kind < 0.3 and ndim > 0:
        # Contiguous strides in C or Fortran order, then perhaps one perturbed.
        order = rng.choice("CF")
        dims = range(ndim - 1, -1, -1) if order == "C" else range(ndim)
        strides = [0] * ndim
        sd = itemsize
        for i in dims:
            strides[i] = sd
            sd *= shape[i]
        if rng.random() < 0.5:
            i = rng.randrange(ndim)
            strides[i] = rng.choice([0, itemsize, -strides[i], strides[i] * 2, 2 * itemsize])
    else:
        strides = [rng.choice([-3, -2, -1, 0, 1, 2, 3, 4, 6, 12]) * itemsize for _ in range(ndim)]
    lo = sum((s - 1) * st for s, st in zip(shape, strides) if st < 0 and s > 0)
    hi = sum((s - 1) * st for s, st in zip(shape, strides) if st > 0 and s > 0)
    offset = -lo
    nitems = max(1, (hi - lo) // itemsize + 1)
    pil = ndim > 0 and rng.random() < 0.15
    noStrides = ndim > 0 and not pil and rng.random() < 0.2
    case = {"mod": "typeobj", "fn": "buffer_contig", "fmt": fmt, "itemsize": itemsize,
            "ndim": ndim, "shape": shape, "strides": strides, "offset": offset,
            "nitems": nitems, "pil": pil, "nostrides": noStrides,
            "order": rng.choice("CFA")}
    return case


def run_buffer(case):
    import _testbuffer as tb
    flags = tb.ND_WRITABLE | (tb.ND_PIL if case["pil"] else 0)
    kw = {}
    if case["ndim"] > 0:
        kw = {"shape": case["shape"], "strides": case["strides"], "offset": case["offset"]}
    else:
        kw = {"shape": []}
    try:
        nd = tb.ndarray([0] * case["nitems"], format=case["fmt"], flags=flags, **kw)
        if case["nostrides"]:
            nd = tb.ndarray(nd, getbuf=tb.PyBUF_ND)
    except (ValueError, TypeError, BufferError) as e:
        return {"skip": str(e)}
    # The Py_buffer of the view, as PyBuffer_IsContiguous reads it.
    case["len"] = nd.nbytes
    case["suboffsets"] = bool(nd.suboffsets)
    case["strides"] = None if case["nostrides"] or case["ndim"] == 0 else list(nd.strides)
    case["shape"] = list(nd.shape)
    return {"ok": tb.is_contiguous(nd, case["order"])}


def gen_case(rng):
    if rng.random() < 0.25:
        while True:
            c = gen_buffer(rng)
            py = run_buffer(c)
            if "skip" not in py:
                c["expected"] = py
                return c
    g = G(rng)
    rng.choice(FAMS)(g)
    return {"mod": "typeobj", "fn": "scenario", "codes": g.codes, "main": g.main}


def run_python(case):
    if case["fn"] == "buffer_contig":
        return case["expected"]
    return td.run_python(case)


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=2000)
