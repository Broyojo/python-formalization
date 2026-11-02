"""Differential test of `frame_lineno_set_impl`: the model's decision against what
a real `frame.f_lineno = n` does from a trace function, on small functions with
loops, `with`, `try` and multi-line expressions.

Each jump runs in a forked child, which reports the decision and leaves from inside
the trace function, so the jumped frame is never resumed. What the test compares is
the decision. Resuming is another matter: CPython approves jumps that crash when the
frame runs on (bytecode-flineno-iter-index-as-object, bytecode-flineno-null-on-stack),
and with the jump in this process those end the whole run with a segfault at whichever
case first reaches them. These cases stay in the generator on purpose.

Also covers the standalone iterator, enumerate, reversed and cell models.
"""

import json
import os
import random
import signal
import sys
import warnings
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from common import main

BODIES = [
    "for i in [1, 2]:\n    x = i\n    y = x\nz = 1\nreturn z",
    "for i in [1]:\n    for j in [2]:\n        x = j\n    y = 1\nz = 2\nreturn z",
    "try:\n    x = 1\n    y = 2\nexcept ValueError:\n    z = 3\nfinally:\n    w = 4\nreturn 5",
    "try:\n    raise ValueError\nexcept ValueError:\n    x = 1\n    y = 2\nz = 3\nreturn z",
    "with C():\n    x = 1\n    y = 2\nz = 3\nreturn z",
    "with C() as a:\n    with C() as b:\n        x = 1\n    y = 2\nz = 3\nreturn z",
    "x = (p,\n     q,\n     r)\ny = 1\nreturn x",
    "x = [p,\n     q]\nfor i in x:\n    y = i\nreturn 1",
    "x = f(p,\n      q)\ny = (x,\n     x)\nreturn y",
    "while p:\n    x = 1\n    if q:\n        break\n    p = 0\ny = 2\nreturn y",
    "x = 1\nif x:\n    y = 2\nelse:\n    y = 3\nz = 4\nreturn z",
    "a = [i for i in [1, 2]]\nb = [j\n     for j in a]\nreturn b",
    "x, y = p, q\ny, x = x, y\nz = 1\nreturn z",
    # GET_ITER pushes two slots on 3.15, whatever the iterable: the iterable and a
    # tagged index for an exact list, tuple, str or bytes (Python/ceval.c:1134-1138),
    # the iterator and NULL for the rest (:1139-1162). mark_stacks gives both Iterator.
    "x = [p,\n     q]\nfor i in iter(x):\n    y = i\nreturn 1",
    "x = [p,\n     q]\nfor i in (v for v in x):\n    y = i\nreturn 1",
    "x = (p,\n     q)\nfor i in x:\n    y = i\nreturn 1",
    "x = f(p,\n      q)\nfor i in 'ab':\n    y = i\nz = (y,\n     y)\nreturn z",
    "x = [p,\n     q,\n     r]\nfor i in b'ab':\n    for j in range(2):\n        y = (i,\n             j)\nreturn y",
    # POP_ITER takes the two slots, on the normal exit and through `break`.
    "for i in [1, 2]:\n    if i:\n        break\n    x = 1\nelse:\n    y = 2\nz = 3\nreturn z",
    "for i in [1]:\n    for j in [2]:\n        if j:\n            break\n    x = 1\ny = (x,\n     x)\nreturn y",
    "with C():\n    for i in [1, 2]:\n        x = i\n    y = 2\nz = 3\nreturn z",
    "try:\n    for i in [1, 2]:\n        x = i\nfinally:\n    y = 1\nreturn y",
    # SEND and END_SEND see the two slots of GET_ITER, YIELD_VALUE and RESUME are
    # between them. The jump is taken at a line event, so not at a suspended frame.
    "x = yield p\ny = (x,\n     q)\nreturn y",
    "yield from [p, q]\nx = 1\ny = (x,\n     x)\nreturn y",
    "x = yield from (v for v in [p])\nfor i in [x]:\n    y = i\nreturn 1",
    # GET_AITER has its own arm on 3.15 and pushes one slot, and END_ASYNC_FOR pops two.
    "async for i in A():\n    x = i\n    y = x\nz = 1\nreturn z",
    "x = [p,\n     q]\nasync for i in A():\n    y = i\nawait B()\nreturn 1",
    "async with D():\n    x = await B()\n    y = 2\nz = 3\nreturn z",
]

HEAD = ("class C:\n    def __enter__(self):\n        return 1\n    def __exit__(self, *a):\n        return False\n"
        "def f(*a):\n    return 1\n"
        "class A:\n    def __init__(self):\n        self.n = 0\n    def __aiter__(self):\n        return self\n"
        "    async def __anext__(self):\n        self.n += 1\n        if self.n > 2:\n            raise StopAsyncIteration\n"
        "        return self.n\n"
        "class B:\n    def __await__(self):\n        yield 1\n        return 2\n"
        "class D:\n    async def __aenter__(self):\n        return 1\n    async def __aexit__(self, *a):\n        return False\n")


def build(body):
    head = "async def" if ("async " in body or "await " in body) else "def"
    src = HEAD + head + " victim(p=1, q=2, r=3):\n" + "\n".join("    " + l for l in body.split("\n")) + "\n"
    ns = {}
    exec(compile(src, "<v>", "exec"), ns)
    return ns


def line_table(co):
    """`marklines`, lines 1580-1604 of Objects/frameobject.c."""
    n = len(co.co_code) // 2
    lines = [-1] * n
    last = -1
    for start, end, line in co.co_lines():
        if line is not None and line != last:
            lines[start // 2] = line
            last = line
    return lines


def drive(r):
    """Run what calling the victim made, when that is a generator or coroutine."""
    if hasattr(r, "send"):
        while True:
            r.send(None)


def attempt_here(body, frm, to, report):
    """The child's half of `attempt`: `report` gets the decision and does not return."""
    ns = build(body)
    v = ns["victim"]
    done = [False]

    def tracer(frame, event, arg):
        if frame.f_code is v.__code__ and event == "line" and not done[0] and frame.f_lineno == frm:
            done[0] = True
            out = {"lasti": frame.f_lasti // 2}
            try:
                frame.f_lineno = to
                out["res"] = ["ok", frame.f_lasti // 2]
            except ValueError as e:
                out["res"] = ["err", str(e)]
            except Exception as e:
                out["res"] = ["other", type(e).__name__]
            report(out)
        return tracer

    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        sys.settrace(tracer)
        try:
            drive(v())
        except BaseException:
            pass
        sys.settrace(None)
    report({})


def attempt(body, frm, to):
    """The decision of `frame.f_lineno = to` at the first line event on `frm`, or {}
    when the frame never reaches that line. A child that dies is a harness error, not
    a skipped case: the decision itself must never crash."""
    rd, wr = os.pipe()
    sys.stdout.flush()
    sys.stderr.flush()
    pid = os.fork()
    if pid == 0:
        os.close(rd)

        def report(out):
            os.write(wr, json.dumps(out).encode())
            os._exit(0)

        try:
            attempt_here(body, frm, to, report)
        finally:
            os._exit(70)
    os.close(wr)
    data = b""
    while chunk := os.read(rd, 65536):
        data += chunk
    os.close(rd)
    _, status = os.waitpid(pid, 0)
    if status != 0 or not data:
        why = signal.Signals(-os.waitstatus_to_exitcode(status)).name if os.WIFSIGNALED(status) else status
        raise RuntimeError(f"child died ({why}) on {body!r} {frm} -> {to}")
    return json.loads(data)


def gen_frame(r):
    body = r.choice(BODIES)
    ns = build(body)
    co = ns["victim"].__code__
    lines = sorted({l for _, _, l in co.co_lines() if l is not None})
    frm = r.choice(lines)
    to = r.choice(lines + [lines[0] - 1, lines[-1] + 1, lines[-1] + 5])
    out = attempt(body, frm, to)
    if "res" not in out:
        return None
    code = [[co.co_code[i], co.co_code[i + 1]] for i in range(0, len(co.co_code), 2)]
    return dict(mod="bytecode", fn="frame_jump", code=code, table=list(co.co_exceptiontable),
                lines=line_table(co), first=co.co_firstlineno, value=to, lasti=out["lasti"],
                res=out["res"])


SCRIPT = [0, 1, 2, 3, -1, -2, -3]


class Seq:
    def __init__(self, script, has_len):
        self.script = script

    def __getitem__(self, i):
        a = self.script[i] if i < len(self.script) else -1
        if a == -1:
            raise IndexError("out")
        if a == -2:
            raise StopIteration
        if a == -3:
            raise ValueError("v")
        return a


class SeqLen(Seq):
    def __len__(self):
        return len(self.script)


def run_seq(script, ops, rev):
    s = SeqLen(script, True)
    it = reversed(s) if rev else iter(s)
    out = []
    for op, arg in ops:
        try:
            if op == "next":
                out.append(next(it))
            elif op == "hint":
                out.append(it.__length_hint__())
            elif op == "set":
                it.__setstate__(arg)
                out.append("set")
            else:
                r = it.__reduce__()
                out.append(r[2] if len(r) > 2 else None)
        except StopIteration:
            out.append("stop")
        except Exception as e:
            out.append(type(e).__name__)
    return out


def gen_iter(r):
    k = r.random()
    if k < 0.45:
        script = [r.choice(SCRIPT) for _ in range(r.randint(0, 5))]
        ops = [[r.choice(["next", "next", "hint", "set", "reduce"]), r.choice([-5, -1, 0, 1, 2, 7, 2**63 - 1])]
               for _ in range(r.randint(1, 7))]
        rev = r.random() < 0.5
        return dict(mod="bytecode", fn="iter_seq", script=script, ops=ops, rev=rev,
                    res=run_seq(script, ops, rev))
    if k < 0.8:
        start = r.choice([0, 1, -1, 2**63 - 2, 2**63 - 1, 2**63, -2**63, -2**63 - 1, 2**64, -2**64, 10**20])
        n = r.randint(0, 5)
        e = enumerate(range(100), start)
        got = [next(e)[0] for _ in range(n)]
        return dict(mod="bytecode", fn="enum_counts", start=str(start), n=n,
                    res=[[str(x) for x in got], str(e.__reduce__()[1][1])])
    CT = type((lambda x: lambda: x)(0).__closure__[0])
    a, b = r.choice([None, 0, 1, 2]), r.choice([None, 0, 1, 2])
    ca, cb = CT(a) if a is not None else CT(), CT(b) if b is not None else CT()
    res = [ca < cb, ca <= cb, ca == cb, ca != cb, ca > cb, ca >= cb]
    return dict(mod="bytecode", fn="cell_cmp", a=a, b=b, res=res)


def gen_case(rng):
    return gen_frame(rng) if rng.random() < 0.6 else gen_iter(rng)


def run_python(case):
    return {"ok": case["res"]}


if __name__ == "__main__":
    main(gen_case, run_python, default_cases=5000)
