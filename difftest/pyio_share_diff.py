"""Differential test: io.BytesIO's copy-on-write buffer, with object identity, vs. the Lean
model in lean/PyLean/PyIO/BytesShare.lean (fn "share_c").

Usage: python3 difftest/pyio_share_diff.py [--cases N] [--seed S]

The program keeps every bytes object that getvalue(), read() and readline() return in a
list `held` (and, if "keep", the initial value), until a "drop" op deletes it; "hash h"
compares hash(held[h]) with the hash of a fresh copy of its contents, "same h k" is
held[h] is held[k]. getbuffer() views are kept in `views`; "viewset" stores a byte
through one, "viewbytes" reads it, "release" releases it. Positions are kept small or
at least 2**60, so no case asks the allocator for a size between 2**24 and 2**60 bytes.
"""

import io
import sys

import common

M = sys.maxsize
BYTES = [97, 98, 10, 0, 255]


def gen_bytes(rng, n=6):
    return [rng.choice(BYTES) for _ in range(rng.randint(0, n))]


def opt_int(rng, n):
    r = rng.random()
    if r < 0.2:
        return None
    if r < 0.27:
        return rng.choice([M, M + 1, -M - 1, 2**63, 2**64, -2**63 - 1])
    return rng.choice([-1, 0, 1, 2, 3, rng.randint(0, n + 3), n])


def gen_case(rng):
    init = gen_bytes(rng, rng.choice([0, 1, 2, 4, 8, 12]))
    n = len(init)
    keep = rng.random() < 0.4
    held = 1 if keep else 0
    views = 0
    ops = []
    for _ in range(rng.randint(1, 18)):
        k = rng.choice(["write", "write", "write", "getvalue", "getvalue", "getvalue", "read", "read",
                        "readline", "seek", "seek", "seek", "tell", "truncate", "truncate", "getbuffer",
                        "viewset", "viewset", "viewbytes", "release", "close", "closed", "drop", "drop",
                        "drop", "hash", "hash", "hash", "same", "same"])
        op = {"op": k}
        if k == "write":
            op["b"] = gen_bytes(rng)
        elif k in ("read", "readline", "truncate"):
            op["n"] = opt_int(rng, n + 4)
        elif k == "seek":
            w = rng.choice([0, 0, 0, 1, 1, 2, 2, 3])
            p = rng.choice([0, 0, 1, 2, 3, n, n + 2, -1, -2, rng.randint(0, 10)])
            if rng.random() < 0.06:
                p = rng.choice([M, M - 1, M - 2, 2**62, 2**63, -M - 1])
            op.update(pos=p, whence=w)
        elif k in ("viewset", "viewbytes", "release"):
            if views == 0:
                continue
            op["v"] = rng.randrange(views)
            if k == "viewset":
                op["i"] = rng.choice([0, 0, 1, 2, rng.randint(0, 12)])
                op["x"] = rng.choice([120, 121, 0, 255, 256])
        elif k == "close":
            if rng.random() < 0.6:
                continue
        elif k in ("drop", "hash"):
            if held == 0:
                continue
            op["h"] = rng.randrange(held)
        elif k == "same":
            if held == 0:
                continue
            op.update(h=rng.randrange(held), k=rng.randrange(held))
        ops.append(op)
        if k in ("getvalue", "read", "readline"):
            held += 1
            if rng.random() < 0.3:
                # hash the result and drop it: the buffer is unshared again with a cached hash
                ops += [{"op": "hash", "h": held - 1}, {"op": "drop", "h": held - 1}]
                held -= 1
        elif k == "drop":
            held -= 1
        elif k == "getbuffer":
            views += 1
    ops += [{"op": "release", "v": v} for v in range(views)]
    ops += [{"op": "getvalue"}, {"op": "hash", "h": held}, {"op": "tell"}, {"op": "closed"}]
    return {"mod": "pyio", "fn": "share_c", "init": init, "keep": keep, "ops": ops}


def enc(v):
    if v is None or isinstance(v, (bool, int)):
        return v
    if isinstance(v, (bytes, bytearray)):
        return {"b": list(v)}
    raise TypeError(type(v))


def apply(f, op, held, views):
    k = op["op"]
    if k == "write":
        if not f.closed:
            p = f.tell()
            assert p < 2**24 or p > 2**60, ("unsafe allocation", p)
        return f.write(bytes(op["b"]))
    if k in ("getvalue", "read", "readline"):
        v = f.getvalue() if k == "getvalue" else getattr(f, k)(op["n"])
        held.append(v)
        return bytes(bytearray(v))
    if k == "seek":
        return f.seek(op["pos"], op["whence"])
    if k == "tell":
        return f.tell()
    if k == "truncate":
        return f.truncate(op["n"])
    if k == "getbuffer":
        views.append(f.getbuffer())
        return None
    if k in ("viewset", "viewbytes", "release") and op["v"] >= len(views):
        # a view index past the end (a failed getbuffer() was counted) acts as a released view
        if k == "release":
            return None
        raise ValueError("operation forbidden on released memoryview object")
    if k == "viewset":
        views[op["v"]][op["i"]] = op["x"]
        return None
    if k == "viewbytes":
        return bytes(views[op["v"]])
    if k == "release":
        views[op["v"]].release()
        return None
    if k == "close":
        return f.close()
    if k == "closed":
        return f.closed
    # An index past the end (the generator counts a failed getvalue/read as kept) is a
    # no-op for drop, True for hash, and None for same, as in the model.
    if k == "drop":
        if op["h"] < len(held):
            del held[op["h"]]
        return None
    if k == "hash":
        if op["h"] >= len(held):
            return True
        x = held[op["h"]]
        return hash(x) == hash(bytes(bytearray(x)))
    if k == "same":
        def get(i):
            return held[i] if i < len(held) else None
        return get(op["h"]) is get(op["k"])
    raise ValueError(k)


def run_python(c):
    x = bytes(c["init"])
    f = io.BytesIO(x)
    held = [x] if c["keep"] else []
    del x
    views, out = [], []
    for op in c["ops"]:
        try:
            out.append({"ok": enc(apply(f, op, held, views))})
        except AssertionError as e:
            if e.args and e.args[0] == "unsafe allocation":
                raise
            out.append({"exc": type(e).__name__, "msg": str(e)})
        except Exception as e:
            out.append({"exc": type(e).__name__, "msg": str(e)})
    for v in views:
        v.release()
    return {"ok": out}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
