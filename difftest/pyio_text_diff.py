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


SMALL = [None, -1, 0, 1, 2, 3, 5, 8, 12, 100]
ENCS = ["utf-8", "utf-8", "utf-8", "ascii", "latin-1", "utf-16", "utf-16-le", "utf-16-be", "utf-32",
        "utf-32-le", "utf-32-be"]
ALPHA = {"utf-8": [97, 98, 13, 10, 233, 8364, 128512, 0], "ascii": [97, 98, 13, 10, 0],
         "latin-1": [97, 13, 10, 233, 0]}


def gen_text(rng, enc):
    al = ALPHA.get(enc, [97, 13, 10, 233, 8364, 128512])
    r = rng.random()
    if r < 0.05:
        return [rng.choice(al)] * rng.choice([8190, 8191, 8192, 8193, 2047, 2048, 2049])
    if r < 0.05 + 0.02:
        return [rng.choice([233, 8364, 97, 13])] * rng.choice([2047, 4095, 4096, 8192])
    s = [rng.choice(al + ([200000] if rng.random() < 0.02 else [])) for _ in range(rng.randint(0, 8))]
    return s


def enc_bytes(s, enc):
    return list("".join(map(chr, s)).encode(enc, "surrogatepass" if enc == "utf-8" else "ignore"))


def drop_stale_tell(ops):
    """Remove tell after next() followed by anything that re-enables telling.

    next() stops updating the snapshot and flush() (also via truncate and
    reconfigure) re-enables tell(), which then reads past the snapshot in C and
    fails an assertion in _pyio. That outcome is not a function of the case.
    """
    out, nexted, stale = [], False, False
    for op in ops:
        k = op["op"]
        if stale and (k in ("tell", "seektell") or (k == "seek" and op.get("whence") == 1)):
            continue
        if k in ("next", "readlines"):  # readlines iterates, so it also stops telling
            nexted = True
        if nexted and k in ("flush", "truncate", "reconfigure"):
            stale = True
        out.append(op)
    return out


# what is left to call on a detached or uninitialized TextIOWrapper: each goes
# through CHECK_ATTACHED or buffer_access_safe
UNATTACHED = ["buffer", "detach", "closed", "fileno", "name", "seekable", "readable", "writable", "isatty",
              "flush", "close", "chunkdel"]


def gen_tiow(rng):
    fn = rng.choice(["tiow_c", "tiow_py", "tiow_py"])
    c_side = fn == "tiow_c"
    enc = rng.choice(ENCS) if c_side else "utf-8"
    errors = rng.choice(["strict", "surrogatepass"]) if c_side and enc == "utf-8" else ("surrogatepass" if enc == "utf-8" else "strict")
    readable = enc in ("utf-8", "ascii", "latin-1")
    data = enc_bytes(gen_text(rng, enc), enc) if readable else []
    nl = pyio_diff.NEWLINES[rng.randrange(30)]
    names = ["write", "write", "write", "flush", "tell", "seektell", "closed", "encoding", "errors", "newlines",
             "line_buffering", "write_through", "seekable", "readable", "writable", "isatty", "fileno", "name",
             "chunkget", "bufvalue", "buffer", "chunkdel"]
    if readable:
        names += ["read"] * 4 + ["readline"] * 4 + ["next", "next", "readlines", "seek", "seek", "truncate"]
    if c_side:
        names += ["chunkset", "reconfigure"]
    ops = []
    for _ in range(rng.randint(1, 14)):
        k = rng.choice(names)
        op = {"op": k}
        if k in ("read", "readline", "readlines", "truncate"):
            op["n"] = rng.choice(SMALL + [8191, 8192, 8193, 2048, 2049])
            if k == "truncate" and op["n"] is None:
                op["n"] = None
        if k == "write":
            op["b"] = gen_text(rng, enc)
        if k == "seek":
            op["pos"] = rng.choice([0, 0, 0, 1, 2, 5, -1, len(data), len(data) + 2, 2**64, 2**64 + 1, 2**160])
            op["whence"] = rng.choice([0, 0, 0, 1, 2, 3])
        if k == "chunkset":
            op["v"] = rng.choice([1, 2, 3, 7, 4096, 8192, 0, -1, 2**64])
        if k == "reconfigure":
            op.update(lb=rng.choice([None, True, False]), wt=rng.choice([None, True, False]))
            if rng.random() < 0.5:
                op.update(hasnl=True, newline=rng.choice(pyio_diff.NEWLINES[:5]))
        ops.append(op)
    if rng.random() < 0.15:
        ops.append({"op": "close"})
    if c_side and rng.random() < 0.08:
        ops += [{"op": "detach"}, {"op": "closed"}]
        ops += [{"op": rng.choice(UNATTACHED)} for _ in range(rng.randint(0, 3))]
    else:
        ops = drop_stale_tell(ops + [{"op": "flush"}, {"op": "bufvalue"}, {"op": "tell"}, {"op": "newlines"}, {"op": "closed"}])
    uninit = c_side and rng.random() < 0.04
    if uninit:
        ops = [{"op": rng.choice(UNATTACHED + ["tell", "chunkget"])} for _ in range(rng.randint(1, 6))]
    return {"mod": "pyio", "fn": fn, "data": data, "enc": enc, "errors": errors, "newline": nl,
            "lb": c_side and rng.random() < 0.15, "wt": c_side and rng.random() < 0.15, "ops": ops, "uninit": uninit}


def gen_stringx(rng):
    fn = rng.choice(["stringx_c", "stringx_py"])
    c = {"mod": "pyio", "fn": fn}
    c.update(pyio_diff.gen_stringio(rng, fn))
    for _ in range(rng.randint(1, 5)):
        k = rng.choice(["readable", "writable", "seekable", "flush", "isatty", "fileno", "detach", "encoding",
                        "errors", "line_buffering", "name", "getstate", "setstate", "truncobj", "truncobj"])
        op = {"op": k}
        if k in ("getstate", "setstate", "truncobj") and fn == "stringx_py":
            continue
        if k == "truncobj":
            op["a"] = pyio_diff.gen_targ(rng, 8)
        if k == "setstate":
            op.update(v=None if rng.random() < 0.2 else [97, 13, 10, 98], nl=rng.choice(pyio_diff.NEWLINES),
                      pos=rng.choice([0, 1, 3, 100, -1, 2**63]))
        c["ops"].insert(rng.randint(0, len(c["ops"])), op)
    return c


def gen_case(rng):
    r = rng.random()
    if r < 0.6:
        return gen_tiow(rng)
    if r < 0.8:
        return gen_stringx(rng)
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


def apply_tiow(f, b, op, key):
    k = op["op"]
    if k in ("read", "readline", "readlines", "truncate"):
        return getattr(f, k)(op["n"])
    if k == "write":
        return f.write("".join(map(chr, op["b"])))
    if k == "seek":
        return f.seek(op["pos"], op["whence"])
    if k == "seektell":
        return f.seek(f.tell())
    if k == "next":
        return next(f)
    if k == "detach":
        f.detach()
        return None
    if k in ("closed", "encoding", "errors", "newlines", "line_buffering", "write_through", "name"):
        return getattr(f, k)
    if k == "chunkget":
        return f._CHUNK_SIZE
    if k == "chunkset":
        f._CHUNK_SIZE = op["v"]
        return None
    if k == "chunkdel":
        del f._CHUNK_SIZE
        return None
    if k == "buffer":
        return f.buffer is b
    if k == "reconfigure":
        kw = {"line_buffering": op["lb"], "write_through": op["wt"]}
        if op.get("hasnl"):
            kw["newline"] = None if op["newline"] is None else "".join(map(chr, op["newline"]))
        f.reconfigure(**kw)
        return None
    if k == "bufvalue":
        return b.getvalue()
    return getattr(f, k)()


def run_tiow(c):
    key = c["fn"].split("_")[1]
    m = M[key]
    nl = None if c["newline"] is None else "".join(map(chr, c["newline"]))
    b = m.BytesIO(bytes(c["data"]))
    try:
        if c["uninit"]:
            f = m.TextIOWrapper.__new__(m.TextIOWrapper)
        else:
            f = m.TextIOWrapper(b, encoding=c["enc"], errors=c["errors"], newline=nl,
                                line_buffering=c["lb"], write_through=c["wt"])
    except Exception as e:
        return pyio_diff.norm(e)
    out = []
    for op in c["ops"]:
        try:
            out.append({"ok": pyio_diff.enc(apply_tiow(f, b, op, key))})
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except AssertionError as e:
            out.append(pyio_diff.norm(e))
        except Exception as e:
            out.append(pyio_diff.norm(e))
    return {"ok": out}


def run_stringx(c):
    key = c["fn"].split("_")[1]
    m = M[key]
    init = None if c["init"] is None else "".join(map(chr, c["init"]))
    nl = None if c["newline"] is None else "".join(map(chr, c["newline"]))
    try:
        f = m.StringIO(init, nl)
    except Exception as e:
        return pyio_diff.norm(e)
    out = []
    for op in c["ops"]:
        k = op["op"]
        try:
            if k in ("encoding", "errors", "line_buffering", "name"):
                v = getattr(f, k)
            elif k == "getstate":
                st = f.__getstate__()
                v = list(st)
            elif k == "setstate":
                val = None if op["v"] is None else "".join(map(chr, op["v"]))
                n = None if op["nl"] is None else "".join(map(chr, op["nl"]))
                v = f.__setstate__((val, n, op["pos"], None))
            elif k == "truncobj":
                # readline(0) realizes the stream: a closing __index__ on a stream
                # still accumulating is the crash in bugs/pyio-stringio-truncate-index-close-crash.yaml
                if not f.closed:
                    f.readline(0)
                v = f.truncate(pyio_diff.make_targ(f, op["a"], []))
            elif k in ("readable", "writable", "seekable", "flush", "isatty", "fileno", "detach"):
                v = getattr(f, k)()
            else:
                v = pyio_diff.apply(f, op, "stringio_" + key, [])
            out.append({"ok": pyio_diff.enc(v)})
        except StopIteration:
            out.append({"exc": "StopIteration", "msg": ""})
        except Exception as e:
            out.append(pyio_diff.norm(e))
    return {"ok": out}


def run_python(c):
    if c["fn"].startswith("tiow"):
        return run_tiow(c)
    if c["fn"].startswith("stringx"):
        return run_stringx(c)
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
