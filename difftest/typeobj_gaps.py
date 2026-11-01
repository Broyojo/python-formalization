"""Which branches of the TypeObj model does Python actually reach, and what happens there?

Usage: python3 difftest/typeobj_gaps.py [--seed S] [--limit N] [--out FILE]

The difftest only sees what its generator produces, and at 100% agreement every `gap%` is silent.
This sweep calls every attribute of the values the model knows, and every protocol on them, then
sorts each case: agree, a `gap%` site, out of fuel, a real disagreement (a model bug), or a crash.

Each case runs on the Python side in a forked child with a memory cap and an alarm, because a
sweep over builtin descriptors can reach interpreter crashes. A crash is recorded with its
source and nothing more is done with it.
"""

import argparse
import collections
import glob
import json
import os
import random
import re
import resource
import signal
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import common
import typeobj_diff as td
from typeobj_diff import G, NONE, attr, call, lit, name

GIB = 1 << 30
ARGS = [[], [NONE], [lit(1)], [lit("s")], [name("int")], [name("o")], [lit(1), lit(2)]]


def prelude(g):
    """`class A`, an instance `a`, and a function `f`, in every case."""
    g.main.append(["class", "A", [], [], False, g.code([
        g.method("m", "A.m", ["s"], [["log", "A.m"], ["ret", lit(1)]]),
        ["assign", "x", lit(1)]])])
    g.main.append(["assign", "a", call(name("A"))])


VALUES = [
    NONE, name("NotImplemented"), name("Ellipsis"), lit(True), lit(0), lit(1),
    lit(["bigint", str(2**64)]), lit(""), lit("s"), ["tuple", []], ["tuple", [lit(1)]],
    ["list", []], ["list", [lit(1)]], ["dict", []], ["dict", [[lit(1), lit(2)]]],
    name("object"), name("type"), name("int"), name("str"), name("list"), name("dict"),
    name("tuple"), name("bool"), name("A"), name("a"), attr(name("a"), "m"), attr(name("A"), "m"),
    call(name("property"), attr(name("A"), "m")), call(name("classmethod"), attr(name("A"), "m")),
    call(name("staticmethod"), attr(name("A"), "m")),
    call(name("super"), name("A"), name("a")), call(name("super"), name("A")),
    name("len"), name("isinstance"), attr(name("int"), "__add__"),
    attr(lit(1), "__add__"), attr(name("list"), "append"), attr(["list", []], "append"),
    ["sub", attr(name("type"), "__dict__"), lit("__bases__")],
    ["sub", attr(name("object"), "__dict__"), lit("__class__")],
    attr(name("A"), "__dict__"), call(name("iter"), ["list", [lit(1)]]),
    call(name("iter"), ["tuple", [lit(1)]]), call(name("iter"), lit("s")),
    call(name("iter"), ["dict", [[lit(1), lit(2)]]]),
    call(attr(["dict", [[lit(1), lit(2)]]], "keys")),
    call(name("ValueError"), lit("x")), name("ValueError"),
]


def protocols(v):
    """The language-level operations on a value, as expressions."""
    two = ["bin", "+", v, v]
    return [call(name("len"), v), call(name("iter"), v), call(name("hash"), v),
            call(name("repr"), v), call(name("str"), v), call(name("bool"), v),
            call(name("int"), v), call(name("float"), v), call(name("format"), v),
            call(name("dir"), v), call(name("isinstance"), lit(1), v),
            call(name("issubclass"), name("int"), v), call(v), two, ["bin", "*", v, lit(2)],
            ["bin", "%", v, v], ["bin", "**", v, lit(2)], ["un", "-", v], ["un", "~", v],
            ["cmp", "==", v, v], ["cmp", "<", v, v], ["sub", v, lit(0)], ["in", lit(1), v],
            attr(v, "zz"), call(name("list"), v), call(name("tuple"), v), call(name("dict"), v)]


def case_for(expr, setup=()):
    g = G(random.Random(0))
    prelude(g)
    g.main.extend(setup)
    g.probe(expr)
    return {"mod": "typeobj", "fn": "scenario", "codes": g.codes, "main": g.main}


def source(case):
    out = []
    td.block_src(case["main"], case["codes"], 0, out)
    return "\n".join(out)


def names_of(v):
    """`dir` of the value, from a real evaluation of its expression."""
    case = case_for(v)
    env = {"__name__": "__main__", "_log": lambda s: None, "_note": lambda *a: None,
           "_text": str, "_hash": hash}
    box = {}

    def probe(tag, f):
        box["v"] = f()

    env["_probe"] = probe
    exec(source(case), env)
    return sorted(dir(box["v"]))


def build_cases():
    out = []
    for v in VALUES:
        for e in protocols(v):
            out.append(case_for(e))
        setup = [["assign", "o", v]]
        for n in names_of(v):
            if n in ("__class_getitem__",):
                continue
            out.append(case_for(attr(v, n)))
            for a in ARGS:
                out.append(case_for(call(attr(name("o"), n), *a), setup))
    return out


def run_forked(case, seconds=8):
    """`run_python` in a child. Returns (trace or None, signal number or 0)."""
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        try:
            resource.setrlimit(resource.RLIMIT_AS, (8 * GIB, 8 * GIB))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
            signal.signal(signal.SIGALRM, signal.SIG_DFL)
            signal.alarm(seconds)
            devnull = os.open(os.devnull, os.O_WRONLY)
            os.dup2(devnull, 1)
            os.dup2(devnull, 2)
            data = json.dumps(td.run_python(case)["ok"]).encode()
            with os.fdopen(w, "wb") as f:
                f.write(data)
        finally:
            os._exit(0)
    os.close(w)
    with os.fdopen(r, "rb") as f:
        data = f.read()
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status):
        return None, os.WTERMSIG(status)
    return (json.loads(data) if data else None), 0


def static_sites():
    """Every `gap%` in the model, as the site strings the harness reports."""
    pat = re.compile(r"(?<![\w`])gap%")
    sites = {}
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "lean", "PyLean", "TypeObj")
    for p in sorted(glob.glob(os.path.join(root, "*.lean"))):
        base = os.path.basename(p)
        if base == "Gap.lean":
            continue
        cur = "?"
        for i, line in enumerate(open(p), 1):
            m = re.match(r"\s*(?:private |partial |protected )?(?:def|abbrev)\s+(\S+)", line)
            if m:
                cur = m.group(1)
            if pat.search(line.split("--")[0]):
                sites[f"{base}:{i}"] = cur
    return sites


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    cases = build_cases()
    random.Random(args.seed).shuffle(cases)
    if args.limit:
        cases = cases[:args.limit]
    res = common.run_lean(cases)
    cats = collections.Counter()
    sites = collections.Counter()
    example = {}
    bad = []
    crash = []
    for c, lo in zip(cases, res):
        py, sig = run_forked(c)
        if py is None:
            kind = {signal.SIGALRM: "timeout"}.get(sig, f"crash-{sig}")
            cats[kind] += 1
            crash.append((kind, source(c).split("\n")[-1]))
            continue
        lean = lo.get("ok")
        if lean is None:
            cats["harness"] += 1
            bad.append(("harness", source(c).split("\n")[-1], str(lo)[:160], py[-1:]))
            continue
        if lean == py:
            cats["agree"] += 1
            continue
        hit = [x for x in lean if "MODEL-GAP" in x or "MODEL-FUEL" in x]
        if hit:
            m = re.search(r"MODEL-(GAP@[^']*|FUEL)", hit[0])
            s = m.group(1)
            sites[s] += 1
            cats["gap"] += 1
            example.setdefault(s, (source(c).split("\n")[-1], py[-1:]))
        else:
            cats["disagree"] += 1
            bad.append(("disagree", source(c).split("\n")[-1], lean[-1:], py[-1:]))
    known = static_sites()
    fired = {s[4:] for s in sites if s.startswith("GAP@")}
    print(f"cases {len(cases)}: {dict(cats)}")
    print(f"gap% sites {len(known)}, fired {len(fired & set(known))}, "
          f"never fired {len(set(known) - fired)}")
    print("top sites:")
    for s, n in sites.most_common(30):
        print(f"  {n:6d} {s} {known.get(s[4:], '')}")
    if args.out:
        with open(args.out, "w") as f:
            json.dump({"cats": cats, "sites": sites, "example": example, "bad": bad,
                       "crash": crash, "known": known}, f, indent=0)
    for k, src in crash[:40]:
        print("CRASH", k, src[:150])


if __name__ == "__main__":
    main()
