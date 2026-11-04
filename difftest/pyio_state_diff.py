"""Differential test: io.BytesIO.__getstate__/__setstate__ with arbitrary state objects and the
instance dict, vs. lean/PyLean/PyIO/BytesState.lean (fn "bytesstate_c").

Usage: python3 difftest/pyio_state_diff.py [--cases N] [--seed S]

The ordinary BytesIO operations of pyio_diff.py, interleaved with attribute stores
("setattr"), reads of f.__dict__ ("getdict", which creates the dict), "getstate" (whose dict,
if any, the harness then mutates, so a later "getdict" would show an alias), and "setstate"
of tuples of every length with bytes, bytearray, int, bool, None, dict and other items, or
of a non-tuple. A dict slot is reported as [None] or [True, key, value, ...].
"""

import io

import common
import pyio_diff

OTHER = {"str": "s", "float": 1.5, "list": [1]}
NONTUPLE = {"list": [b"", 0, None], "int": 5, "NoneType": None}
KEYS = ["a", "b", "c"]


def gen_item(rng, slot):
    r = rng.random()
    good = {0: ["bytes", "bytes", "bytearray"], 1: ["int", "int", "int", "bool"], 2: ["none", "dict", "dict"]}[slot]
    k = rng.choice(good) if r < 0.8 else rng.choice(["bytes", "bytearray", "int", "bool", "none", "dict", "other"])
    if k in ("bytes", "bytearray"):
        return {"k": k, "b": pyio_diff.gen_bytes(rng)}
    if k == "int":
        return {"k": k, "v": pyio_diff.an_int(rng, 8)}
    if k == "bool":
        return {"k": k, "v": rng.random() < 0.5}
    if k == "dict":
        keys = rng.sample(KEYS, rng.randint(0, 3))
        return {"k": k, "kv": [[key, rng.randint(-3, 9)] for key in keys]}
    if k == "other":
        return {"k": k, "t": rng.choice(list(OTHER))}
    return {"k": "none"}


def gen_case(rng):
    c = {"mod": "pyio", "fn": "bytesstate_c"}
    c.update(pyio_diff.gen_bytesio(rng, "bytesio_c"))
    for _ in range(rng.randint(1, 6)):
        k = rng.choice(["setattr", "setattr", "getdict", "getstate", "getstate", "setstate", "setstate", "setstate"])
        op = {"op": k}
        if k == "setattr":
            op.update(key=rng.choice(KEYS), v=rng.randint(-3, 9))
        if k == "setstate":
            if rng.random() < 0.1:
                op["a"] = {"other": rng.choice(list(NONTUPLE))}
            else:
                n = rng.choice([3, 3, 3, 3, 0, 1, 2, 4])
                op["a"] = {"tuple": [gen_item(rng, min(i, 2)) for i in range(n)]}
        c["ops"].insert(rng.randint(0, len(c["ops"])), op)
    return c


def encdict(d):
    if d is None:
        return [None]
    return [True] + [x for k, v in d.items() for x in (k, v)]


def make_item(it):
    k = it["k"]
    if k == "bytes":
        return bytes(it["b"])
    if k == "bytearray":
        return bytearray(it["b"])
    if k in ("int", "bool"):
        return it["v"]
    if k == "dict":
        return {key: v for key, v in it["kv"]}
    if k == "other":
        return OTHER[it["t"]]
    return None


def apply(f, op, views):
    k = op["op"]
    if k == "setattr":
        setattr(f, op["key"], op["v"])
        return None
    if k == "getdict":
        return encdict(f.__dict__)
    if k == "getstate":
        st = f.__getstate__()
        r = [st[0], st[1]] + encdict(st[2])
        if st[2] is not None:
            st[2]["zz_probe"] = 99  # a copy: this must not reach f.__dict__
        return r
    if k == "setstate":
        a = op["a"]
        state = NONTUPLE[a["other"]] if "other" in a else tuple(make_item(it) for it in a["tuple"])
        return f.__setstate__(state)
    return pyio_diff.apply(f, op, "bytesio_c", views)


def run_python(c):
    f = io.BytesIO(bytes(c["init"]))
    out, views = [], []
    for op in c["ops"]:
        try:
            out.append({"ok": pyio_diff.enc(apply(f, op, views))})
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
