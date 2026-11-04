"""Differential test: io.BytesIO and _pyio.BytesIO calling Python code while they run, vs. the
Lean models in lean/PyLean/PyIO/BytesCallbacks.lean (fn "bytescb_c" / "bytescb_py").

Usage: python3 difftest/pyio_callback_diff.py [--cases N] [--seed S]

The ordinary BytesIO operations of pyio_diff.py, interleaved with:
* "writeitem" x: f.write(x), where x is bytes, a str, a non-buffer, or a Buf whose
  __buffer__ runs stream actions (close, getbuffer, tell, seek, write; their exceptions
  swallowed) and then returns memoryview(bytes(r)) or raises ValueError('boom');
* "reinititem" x: f.__init__(x) with the same kinds of x;
* "writelinesit": f.writelines(it) for a generator whose __next__ runs actions and then
  yields an item or raises KeyError('k'), or for a non-iterable (5, None).
"""

import io
import random
import sys

import _pyio

import common
import pyio_diff

WOBJ = {"int": 1, "NoneType": None, "float": 1.5, "list": [1]}
CLASSES = {"bytescb_c": io.BytesIO, "bytescb_py": _pyio.BytesIO}


class Buf:
    """A write() argument whose __buffer__ acts on the stream first."""

    def __init__(self, f, a, views):
        self.f, self.a, self.views = f, a, views

    def __buffer__(self, flags):
        for h in self.a["hook"]:
            try:
                pyio_diff.run_hook(self.f, h, self.views)
            except Exception:
                pass
        if self.a["r"] is None:
            raise ValueError("boom")
        return memoryview(bytes(self.a["r"]))


def gen_hooks(rng):
    return [pyio_diff.gen_hook(rng) for _ in range(rng.choice([0, 0, 1, 1, 2, 3]))]


def gen_item(rng):
    r = rng.random()
    if r < 0.35:
        return {"kind": "data", "b": pyio_diff.gen_bytes(rng)}
    if r < 0.85:
        return {"kind": "hooked", "hook": gen_hooks(rng),
                "r": None if rng.random() < 0.15 else pyio_diff.gen_bytes(rng)}
    if r < 0.92:
        return {"kind": "str", "s": pyio_diff.gen_bytes(rng, 3)}
    return {"kind": "obj", "t": rng.choice(list(WOBJ))}


def gen_case(rng):
    fn = rng.choice(list(CLASSES))
    c = {"mod": "pyio", "fn": fn}
    c.update(pyio_diff.gen_bytesio(rng, fn))
    for _ in range(rng.randint(1, 5)):
        k = rng.choice(["writeitem", "writeitem", "writeitem", "reinititem", "writelinesit", "writelinesit"])
        op = {"op": k}
        if k in ("writeitem", "reinititem"):
            op["x"] = gen_item(rng)
        elif rng.random() < 0.1:
            op["notiter"] = rng.choice(["int", "NoneType"])
        else:
            steps = []
            for _ in range(rng.randint(0, 4)):
                st = {"hook": gen_hooks(rng)}
                if rng.random() > 0.12:
                    st["item"] = gen_item(rng)
                steps.append(st)
            op["steps"] = steps
        c["ops"].insert(rng.randint(0, len(c["ops"])), op)
    return c


def make_item(f, x, views):
    k = x["kind"]
    if k == "data":
        return bytes(x["b"])
    if k == "hooked":
        return Buf(f, x, views)
    if k == "str":
        return "".join(map(chr, x["s"]))
    return WOBJ[x["t"]]


def steps_iter(f, steps, views):
    for st in steps:
        for h in st["hook"]:
            try:
                pyio_diff.run_hook(f, h, views)
            except Exception:
                pass
        if "item" not in st:
            raise KeyError("k")
        yield make_item(f, st["item"], views)


def safe(f, fn):
    if not f.closed:
        p = f._pos if fn == "bytescb_py" else f.tell()
        assert p < 2**24 or p > 2**60, ("unsafe allocation", p)


def apply(f, op, fn, views):
    k = op["op"]
    if k == "writeitem":
        safe(f, fn)
        return f.write(make_item(f, op["x"], views))
    if k == "reinititem":
        return f.__init__(make_item(f, op["x"], views))
    if k == "writelinesit":
        safe(f, fn)
        if "notiter" in op:
            return f.writelines({"int": 5, "NoneType": None}[op["notiter"]])
        return f.writelines(steps_iter(f, op["steps"], views))
    return pyio_diff.apply(f, op, "bytesio_c" if fn == "bytescb_c" else "bytesio_py", views)


def run_python(c):
    fn = c["fn"]
    f = CLASSES[fn](bytes(c["init"]))
    out, views = [], []
    for op in c["ops"]:
        try:
            out.append({"ok": pyio_diff.enc(apply(f, op, fn, views))})
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except AssertionError as e:
            if e.args and e.args[0] == "unsafe allocation":
                raise
            out.append(pyio_diff.norm(e))
        except Exception as e:
            out.append(pyio_diff.norm(e))
    for v in views:
        v.release()
    return {"ok": out}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
