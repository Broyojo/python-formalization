"""Differential test: IncrementalNewlineDecoder (C and _pyio) against the Lean models.

Usage: python3 difftest/pyio_text_diff.py [--cases N] [--seed S]

The wrapped decoder is None (input is str) or the incremental UTF-8 decoder
(input is bytes). Exits non-zero on any mismatch. See difftest/common.py.
"""

import codecs
import io

import _pyio

import common
import pyio_diff

M = {"c": io, "py": _pyio}
CH = [97, 98, 13, 13, 10, 10, 233, 8364, 0]


def text(rng, inner):
    s = [rng.choice(CH) for _ in range(rng.randint(0, 6))]
    if inner:
        b = "".join(map(chr, s)).encode()
        if rng.random() < 0.3:
            b = b[:rng.randint(0, len(b))]
        if rng.random() < 0.05:
            b = bytes([0xff]) + b
        return list(b)
    return s


def gen_case(rng):
    fn = rng.choice(["nldec_c", "nldec_py"])
    inner = rng.random() < 0.4
    ops = []
    for _ in range(rng.randint(1, 8)):
        k = rng.choice(["decode"] * 6 + ["getstate", "setstate", "reset", "newlines", "newlines"])
        op = {"op": k}
        if k == "decode":
            op.update(s=text(rng, inner), final=rng.random() < 0.3)
        if k == "setstate":
            op.update(b=[] if rng.random() < 0.7 else [0xc3], flag=rng.choice([0, 1, 2, 3, 2**64, 2**64 + 1, -1]))
        ops.append(op)
    ops += [{"op": "getstate"}, {"op": "newlines"}]
    return {"mod": "pyio", "fn": fn, "translate": rng.random() < 0.5, "inner": inner, "ops": ops}


def run_python(c):
    m = M[c["fn"].split("_")[1]]
    inner = codecs.getincrementaldecoder("utf-8")() if c["inner"] else None
    d = m.IncrementalNewlineDecoder(inner, c["translate"])
    out = []
    for op in c["ops"]:
        k = op["op"]
        try:
            if k == "decode":
                data = bytes(op["s"]) if c["inner"] else "".join(map(chr, op["s"]))
                v = d.decode(data, op["final"])
            elif k == "getstate":
                v = list(d.getstate())
            elif k == "setstate":
                v = d.setstate((bytes(op["b"]), op["flag"]))
            elif k == "reset":
                v = d.reset()
            else:
                v = d.newlines
            out.append({"ok": pyio_diff.enc(v)})
        except Exception as e:
            out.append(pyio_diff.norm(e))
    return {"ok": out}


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
