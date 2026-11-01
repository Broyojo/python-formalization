"""Differential test for CoreLibs: Lean model vs the running CPython.

One section per area. `CORELIBS_AREA=coll,rand` restricts the run to those areas;
the default is every area that has a generator:
  scripts/r env CORELIBS_AREA=coll python3 difftest/corelibs_diff.py --cases 50000 --seed 1
"""

import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from common import main, py_result  # noqa: E402

# ====== BEGIN AREA coll (Lib/collections/__init__.py (everything except OrderedDict)) ======
# Everything for this area stays between these two markers; prefix top-level names with coll_.
coll_gen = None  # replace with def coll_gen(rng) -> case dict with "fn": "coll.<name>"
coll_run = None  # replace with def coll_run(case) -> common.py_result-style dict
# ====== END AREA coll ======

# ====== BEGIN AREA collabc (Lib/_collections_abc.py, Lib/collections/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with collabc_.
collabc_gen = None  # replace with def collabc_gen(rng) -> case dict with "fn": "collabc.<name>"
collabc_run = None  # replace with def collabc_run(case) -> common.py_result-style dict
# ====== END AREA collabc ======

# ====== BEGIN AREA functools (Lib/functools.py, Modules/_functoolsmodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with functools_.
functools_gen = None  # replace with def functools_gen(rng) -> case dict with "fn": "functools.<name>"
functools_run = None  # replace with def functools_run(case) -> common.py_result-style dict
# ====== END AREA functools ======

# ====== BEGIN AREA operator (Lib/operator.py, Modules/_operator.c, Lib/copy.py, Lib/abc.py) ======
# Everything for this area stays between these two markers; prefix top-level names with operator_.
operator_gen = None  # replace with def operator_gen(rng) -> case dict with "fn": "operator.<name>"
operator_run = None  # replace with def operator_run(case) -> common.py_result-style dict
# ====== END AREA operator ======

# ====== BEGIN AREA enumdc (Lib/enum.py, Lib/dataclasses.py) ======
# Everything for this area stays between these two markers; prefix top-level names with enumdc_.
enumdc_gen = None  # replace with def enumdc_gen(rng) -> case dict with "fn": "enumdc.<name>"
enumdc_run = None  # replace with def enumdc_run(case) -> common.py_result-style dict
# ====== END AREA enumdc ======

# ====== BEGIN AREA misc (Lib/contextlib.py, Lib/numbers.py, Lib/keyword.py, Lib/types.py, Lib/weakref.py, Lib/graphlib.py, Lib/sched.py, Lib/queue.py) ======
# Everything for this area stays between these two markers; prefix top-level names with misc_.
import graphlib as misc_graphlib  # noqa: E402


def misc_res(thunk):
    """One operation's outcome: ["ok", value] or ["exc", class, message]."""
    try:
        return ["ok", thunk()]
    except Exception as e:
        return ["exc", type(e).__name__, str(e)]


# --- graphlib ---

def misc_gl_dump(ts):
    return [[[i.node, i.npredecessors, list(i.successors)] for i in ts._node2info.values()],
            None if ts._ready_nodes is None else list(ts._ready_nodes),
            ts._npassedout, ts._nfinished]


def misc_gen_graphlib(rng):
    n = rng.choice([1, 2, 3, 4, 6, 8])
    nodes = list(range(n))
    def preds():
        return [rng.choice(nodes) for _ in range(rng.choice([0, 0, 1, 1, 2, 3]))]
    dag = rng.random() < 0.6
    def dag_preds(v):
        return [rng.randrange(v) for _ in range(rng.choice([0, 1, 1, 2]))] if v else []
    graph = None
    if rng.random() < 0.6:
        graph = []
        for v in rng.sample(nodes, rng.randint(0, n)):
            graph.append([v, dag_preds(v) if dag else preds()])
    ops = []
    for _ in range(rng.randint(0, 3)):
        v = rng.choice(nodes)
        ops.append(["add", v, dag_preds(v) if dag else preds()])
    style = rng.choice(["static", "drive", "drive", "chaos"])
    if style == "static":
        if rng.random() < 0.3:
            ops.append(["prepare"])
        ops.append(["static_order"])
        ops.append(["static_order"])
    elif style == "drive":
        ops.append(["prepare"])
        for _ in range(n + 2):
            ops.append(["is_active"])
            ops.append(["get_ready"])
            ops.append(["done_ready"])
        ops.append(["bool"])
    else:
        for _ in range(rng.randint(1, 12)):
            ops.append(rng.choice([
                ["prepare"], ["get_ready"], ["is_active"], ["bool"],
                ["done", [rng.choice(nodes + [99]) for _ in range(rng.randint(0, 3))]],
                ["add", rng.choice(nodes), preds()], ["done_ready"], ["static_order"]]))
    return {"fn": "misc.graphlib", "graph": graph, "ops": ops}


def misc_run_graphlib(case):
    graph = case["graph"]
    if graph is not None:
        graph = {k: v for k, v in graph}
    # The case's graph may repeat no key: rng.sample picks distinct nodes.
    ts = misc_graphlib.TopologicalSorter(graph)
    out = []
    last = []
    for op in case["ops"]:
        name = op[0]
        if name == "add":
            r = misc_res(lambda: ts.add(op[1], *op[2]))
        elif name == "prepare":
            r = misc_res(ts.prepare)
        elif name == "get_ready":
            r = misc_res(ts.get_ready)
            if r[0] == "ok":
                last = list(r[1])
                r = ["ok", last]
        elif name == "is_active":
            r = misc_res(ts.is_active)
        elif name == "bool":
            r = misc_res(lambda: bool(ts))
        elif name == "done":
            r = misc_res(lambda: ts.done(*op[1]))
        elif name == "done_ready":
            r = misc_res(lambda: ts.done(*last))
            last = []
        else:
            r = misc_res(lambda: list(ts.static_order()))
        out.append(r)
    out.append(misc_gl_dump(ts))
    return {"ok": out}


# --- sched ---

import sched as misc_sched  # noqa: E402


def misc_gen_sched(rng):
    def tv(strs=0.05):
        return "x" if rng.random() < strs else rng.choice([0, 0, 1, 1, 2, 3, 5, -1, 2**63, -2**64])
    def act(depth=0):
        k = rng.random()
        if k < 0.6 or depth > 1:
            return ["log", rng.randint(0, 9)]
        if k < 0.7:
            return ["boom"]
        if k < 0.85:
            return ["enterabs", tv(), tv(), act(depth + 1)]
        return ["cancel", rng.randint(0, 5)]
    def args():
        return [rng.randint(0, 3) for _ in range(rng.randint(0, 2))]
    def kw():
        return None if rng.random() < 0.7 else [["a", 1], ["b", rng.randint(0, 3)]][:rng.randint(0, 2)]
    ops = []
    for _ in range(rng.randint(1, 12)):
        k = rng.random()
        if k < 0.45:
            ops.append(["enterabs", tv(), tv(), act(), args(), kw()])
        elif k < 0.6:
            ops.append(["enter", rng.choice([0, 1, 2, 5, -1, "x"]) if rng.random() < .2 else rng.randint(0, 4),
                        tv(), act(), args(), kw()])
        elif k < 0.7:
            ops.append(["cancel", rng.randint(0, 6)])
        elif k < 0.75:
            ops.append(["empty"])
        elif k < 0.85:
            ops.append(["queue"])
        else:
            ops.append(["run", rng.random() < 0.3, rng.choice([None, None, 0, 1])])
    return {"fn": "misc.sched", "tick": rng.choice([0, 0, 1, 2]), "ops": ops}


def misc_run_sched(case):
    tick = case["tick"]
    w = {"clock": 0, "raise": None}
    log = []
    handles = []

    def timefunc():
        t = w["clock"]
        w["clock"] += tick
        return t

    def delayfunc(d):
        log.append(["delay", d])
        if w["raise"] is not None:
            if w["raise"] == 0:
                w["raise"] = None
                raise RuntimeError("delay failed")
            w["raise"] -= 1
            return
        if isinstance(d, int):
            w["clock"] += d

    sc = misc_sched.scheduler(timefunc, delayfunc)

    def action(a):
        tag = a[1] if a[0] == "log" else a[0]
        def f(*args, **kwargs):
            log.append(["call", tag, list(args), [list(kv) for kv in kwargs.items()]])
            if a[0] == "boom":
                raise RuntimeError("action failed")
            if a[0] == "enterabs":
                handles.append(sc.enterabs(a[1], a[2], action(a[3])))
            if a[0] == "cancel" and a[1] < len(handles):
                sc.cancel(handles[a[1]])
        return f

    def ev5(ev):
        return [ev.time, ev.priority, ev.sequence, list(ev.argument), [list(kv) for kv in ev.kwargs.items()]]

    def ev3(ev):
        return [ev.time, ev.priority, ev.sequence]

    out = []
    for op in case["ops"]:
        name = op[0]
        if name in ("enterabs", "enter"):
            kw = {} if op[5] is None else {"kwargs": dict(op[5])}
            f = sc.enterabs if name == "enterabs" else sc.enter
            def thunk():
                ev = f(op[1], op[2], action(op[3]), tuple(op[4]), **kw)
                handles.append(ev)
                return ev5(ev)
            r = misc_res(thunk)
        elif name == "cancel":
            r = misc_res(lambda: sc.cancel(handles[op[1]])) if op[1] < len(handles) else ["ok", None]
        elif name == "empty":
            r = misc_res(sc.empty)
        elif name == "queue":
            r = misc_res(lambda: [ev3(e) for e in sc.queue])
        else:
            w["raise"] = op[2]
            r = misc_res(lambda: sc.run(op[1]))
            w["raise"] = None
        out.append(r)
    out.append([[ev3(e) for e in sc._queue], next(sc._sequence_generator), w["clock"], log])
    return {"ok": out}


MISC_GENS = [misc_gen_graphlib, misc_gen_sched]
MISC_RUNS = {"misc.graphlib": misc_run_graphlib, "misc.sched": misc_run_sched}


def misc_gen(rng):
    return rng.choice(MISC_GENS)(rng)


def misc_run(case):
    return MISC_RUNS[case["fn"]](case)
# ====== END AREA misc ======

# ====== BEGIN AREA calstat (Lib/calendar.py, Lib/statistics.py) ======
# Everything for this area stays between these two markers; prefix top-level names with calstat_.
calstat_gen = None  # replace with def calstat_gen(rng) -> case dict with "fn": "calstat.<name>"
calstat_run = None  # replace with def calstat_run(case) -> common.py_result-style dict
# ====== END AREA calstat ======

# ====== BEGIN AREA rand (Lib/random.py, Modules/_randommodule.c) ======
# Everything for this area stays between these two markers; prefix top-level names with rand_.
rand_gen = None  # replace with def rand_gen(rng) -> case dict with "fn": "rand.<name>"
rand_run = None  # replace with def rand_run(case) -> common.py_result-style dict
# ====== END AREA rand ======


AREAS = {name: (globals()[name + "_gen"], globals()[name + "_run"])
         for name in ['coll', 'collabc', 'functools', 'operator', 'enumdc', 'misc', 'calstat', 'rand']}
selected = os.environ.get("CORELIBS_AREA")
ACTIVE = [a for a in (selected.split(",") if selected else AREAS) if AREAS[a][0] is not None]


def gen_case(rng):
    case = AREAS[rng.choice(ACTIVE)][0](rng)
    if case is not None:
        case["mod"] = "corelibs"
    return case


def run_python(case):
    return AREAS[case["fn"].split(".")[0]][1](case)


if __name__ == "__main__":
    main(gen_case, run_python)
