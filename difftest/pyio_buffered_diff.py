"""Differential test: BufferedReader/Writer/Random (C and _pyio) over a scripted,
re-entrant raw stream.

Usage: python3 difftest/pyio_buffered_diff.py [--cases N] [--seed S]

The raw stream is a RawIOBase subclass holding bytes and a position. Scripts
force short reads and writes, None (would block), int answers that move no byte
(out of range, or in range: a lie), a str answer, and exceptions; the `closed`
property has its own script (honest, a lie, an exception). Hooks re-enter the
buffered object from inside a raw callback. Each operation's result, the raw call
log (with the outcomes of re-entered calls), and the raw's final contents and
position are compared with the Lean models (`buf_c`, `buf_py`).

A C case with hooks runs in a forked child, so a crash is an outcome ("crash").
A case the model calls undefined behaviour ("ub") is not compared or counted in
"agree"; only the operations that finished before the UB are (see `main`).
_pyio's locks are swapped for ones that raise instead of blocking forever when
taken twice by the same thread, so a deadlock is an outcome too ("hang").
"""

import builtins
import errno
import json
import os
import select
import signal
import sys
import time
import warnings

import _pyio
import io

import common
import pyio_diff

warnings.simplefilter("ignore")
sys.unraisablehook = lambda u: None
M = sys.maxsize
MODS = {"c": io, "py": _pyio}
# (class, message, errno): `_PyIO_trap_eintr` retries an OSError whose errno is EINTR,
# whatever its class; InterruptedError("x") has no errno and is not retried
class MyOSError(OSError):
    """A user subclass: `_PyIO_trap_eintr` follows the MRO, not a list of names."""


class MyBlockingError(BlockingIOError):
    """`_buffered_check_blocking_error` matches subclasses too."""


CLASSES = {c.__name__: c for c in (ValueError, OSError, InterruptedError, PermissionError,
                                   FileExistsError, ConnectionResetError, io.UnsupportedOperation, MyOSError,
                                   MyBlockingError)}
EXC = [("ValueError", "boom", None), ("OSError", "bad", None), ("InterruptedError", "x", errno.EINTR),
       ("InterruptedError", "x", None), ("PermissionError", "x", errno.EINTR), ("PermissionError", "x", None),
       ("FileExistsError", "x", errno.EINTR), ("ConnectionResetError", "x", errno.EINTR),
       ("UnsupportedOperation", "x", errno.EINTR), ("MyOSError", "x", errno.EINTR), ("MyOSError", "x", None),
       ("MyBlockingError", "x", None)]
CUR_RAW = [None]
# sizes PyBytesWriter_Create refuses, on both sides of the "byte string is too large" bound
HUGE = [M, M - 1, M - 32, M - 33, 2**62, 2**48]


class Deadlock(BaseException):
    """A `with lock:` on a lock this thread holds: the real program blocks forever."""


CTX = {"hung": False}


class DLock:
    def __init__(self):
        self.held, self.ctx = False, CTX

    def __enter__(self):
        if self.held:
            self.ctx["hung"] = True
            raise Deadlock()
        self.held = True

    def __exit__(self, *a):
        self.held = False


_pyio.Lock = DLock


def raised(r):
    cls = CLASSES.get(r["raise"]) or getattr(builtins, r["raise"])
    if r.get("errno") is not None:
        raise cls(r["errno"], r["msg"])
    raise cls(r["msg"])


def outcome(thunk):
    try:
        return {"ok": pyio_diff.enc(thunk())}
    except StopIteration:
        return {"exc": "StopIteration", "msg": ""}
    except Exception as e:
        return norm(e)


def make_raw_class(mod):
    class Raw(mod.RawIOBase):
        def setup(self, c):
            self.d, self.p = bytearray(c["data"]), 0
            self.rs, self.ws, self.ss = list(c["rs"]), list(c["ws"]), list(c["ss"])
            self.cs, self.hooks = list(c["cs"]), {n: op for n, op in c["hooks"]}
            self.qs, self.fr = list(c["qs"]), c["flushRet"]
            self.fl, self.cf, self.calls = c["flags"], c["closeFail"], []
            self.n, self.buf, self.shut, self.mask = 0, None, False, c["mask"]

        def enter(self, entry):
            self.calls.append(entry)
            self.n += 1
            op = self.hooks.pop(self.n, None) if self.buf is not None else None
            if op is not None and self.buf is not None:
                r = outcome(lambda: apply(self.buf, op))
                self.calls.append(["re", mask(r) if self.mask else r])

        def _inq(self, name, flag):
            self.enter([name])
            if self.qs:
                s = self.qs.pop(0)
                if s is not None:
                    if "raise" in s:
                        raised(s)
                    return s["int"]
            return bool(flag)

        def readable(self):
            return self._inq("readable", self.fl[0])

        def writable(self):
            return self._inq("writable", self.fl[1])

        def seekable(self):
            return self._inq("seekable", self.fl[2])

        @property
        def closed(self):
            self.enter(["closed"])
            if self.cs:
                s = self.cs.pop(0)
                if s is not None:
                    if "raise" in s:
                        raised(s)
                    return s["lie"]
            return self.shut

        def readinto(self, b):
            self.enter(["readinto", len(b)])
            if self.shut:
                raise ValueError("raw closed")
            k = len(b)
            if self.rs:
                s = self.rs.pop(0)
                if s is None:
                    return None
                if "raise" in s:
                    raised(s)
                if "bad" in s:
                    return s["bad"]
                if "wrong" in s:
                    return "x"
                k = min(k, s["short"])
            d = bytes(self.d[self.p:self.p + k])
            b[:len(d)] = d
            self.p += len(d)
            return len(d)

        def write(self, b):
            b = bytes(b)
            self.enter(["write", list(b)])
            if self.shut:
                raise ValueError("raw closed")
            k = len(b)
            if self.ws:
                s = self.ws.pop(0)
                if s is None:
                    return None
                if "raise" in s:
                    raised(s)
                if "bad" in s:
                    return s["bad"]
                if "wrong" in s:
                    return "x"
                k = min(k, s["short"])
            d = b[:k]
            if d:
                if self.p > len(self.d):
                    self.d.extend(bytes(self.p - len(self.d)))
                self.d[self.p:self.p + len(d)] = d
            self.p += len(d)
            return len(d)

        def _sstep(self):
            if self.ss:
                s = self.ss.pop(0)
                if s is not None:
                    if "raise" in s:
                        raised(s)
                    return "x" if "wrong" in s else s["bad"]
            return None

        def seek(self, p, w=0):
            self.enter(["seek", p, w])
            if self.shut:
                raise ValueError("raw closed")
            r = self._sstep()
            if r is not None:
                return r
            if not self.fl[2]:
                raise OSError("unseekable")
            n = p if w == 0 else self.p + p if w == 1 else len(self.d) + p if w == 2 else -1
            if n < 0:
                raise ValueError("bad seek")
            self.p = n
            return n

        def tell(self):
            self.enter(["tell"])
            if self.shut:
                raise ValueError("raw closed")
            r = self._sstep()
            if r is not None:
                return r
            if not self.fl[2]:
                raise OSError("unseekable")
            return self.p

        def truncate(self, p=None):
            self.enter(["truncate", None if isinstance(p, str) else p])
            if self.shut:
                raise ValueError("raw closed")
            n = self.p if p is None else p
            if n < 0:
                raise ValueError("bad truncate")
            if n > 2**24:
                raise OverflowError("too big")
            del self.d[n:]
            self.d.extend(bytes(n - len(self.d)))
            return n

        def flush(self):
            self.enter(["flush"])
            if self.shut:
                raise ValueError("I/O operation on closed file.")
            return self.fr

        def close(self):
            self.enter(["close"])
            if self.cf:
                c, self.cf = self.cf, None
                raise getattr(builtins, c[0])(c[1])
            self.shut = True

        def isatty(self):
            self.enter(["isatty"])
            if self.shut:
                raise ValueError("I/O operation on closed file.")
            return False

        def disarm(self):
            self.hooks, self.cs, self.rs, self.ws, self.ss, self.cf, self.qs = {}, [], [], [], [], None, []
            self.buf = None
    return Raw


RAWS = {k: make_raw_class(m) for k, m in MODS.items()}
CLS = {("c", 0): io.BufferedReader, ("c", 1): io.BufferedWriter, ("c", 2): io.BufferedRandom,
       ("py", 0): _pyio.BufferedReader, ("py", 1): _pyio.BufferedWriter, ("py", 2): _pyio.BufferedRandom}


def rstep(rng, key, write):
    r = rng.random()
    if r < 0.5:
        return {"short": rng.choice([0, 1, 1, 2, 3, 5, 8])}
    if r < 0.68:
        return None
    if r < 0.86:
        bads = [10**6, 2**64, 0, 1, 2, 3]
        if key == "c" or write:
            bads.append(-1)
        return {"bad": rng.choice(bads)}
    if r < 0.9:
        return {"wrong": 1}
    c, m, e = rng.choice(EXC)
    return {"raise": c, "msg": m, "errno": e, "mro": [k.__name__ for k in CLASSES[c].__mro__]}


def sstep(rng):
    r = rng.random()
    if r < 0.55:
        return None
    if r < 0.8:
        return {"bad": rng.choice([-1, -5, 2**64, 0, 3])}
    if r < 0.85:
        return {"wrong": 1}
    # a BlockingIOError subclass from seek counts as blocking in the write path
    c, m = rng.choice([("ValueError", "boom"), ("OSError", "bad"), ("MyBlockingError", "x")])
    return {"raise": c, "msg": m, "mro": [k.__name__ for k in CLASSES[c].__mro__]}


def qstep(rng):
    r = rng.random()
    if r < 0.5:
        return None
    if r < 0.85:
        return {"int": rng.choice([0, 1, 2, -1])}
    c, m, _ = rng.choice(EXC[:2])
    return {"raise": c, "msg": m}


def cstep(rng):
    r = rng.random()
    if r < 0.6:
        return None
    if r < 0.9:
        return {"lie": rng.random() < 0.5}
    c, m, _ = rng.choice(EXC[:2])
    return {"raise": c, "msg": m}


def gen_op(rng, k, size, key, data):
    op = {"op": k}
    if k == "reinit":
        # a refused size is stored before it is refused; 2**48 frees the buffer and
        # then fails to allocate
        op["size"] = rng.choice([size, 4, 8, 0, -1, -5, 2**48])
    if k in ("read", "readline"):
        op["n"] = rng.choice([None, -1, -2, 0, 1, 2, 3, size, size + 1, 2 * size, 3 * size + 1, 30])
        if key == "c" and rng.random() < 0.05:
            op["n"] = rng.choice([M + 1, -M - 2])
        if key == "c" and k == "read" and rng.random() < 0.04:
            op["n"] = rng.choice(HUGE)
    if k == "read1":
        op["n"] = rng.choice([-1, 0, 1, 2, size, 2 * size])
        if key == "c" and rng.random() < 0.08:
            op["n"] = rng.choice(HUGE)
    if k == "peek":
        op["n"] = rng.choice([0, 1, 2, size])
    if k in ("readinto", "readinto1"):
        op["n"] = max(0, rng.choice([0, 1, 2, size, size + 1, 2 * size + 1, 20]))
    if k == "write":
        op["b"] = [rng.choice([97, 98, 10]) for _ in range(rng.choice(
            [0, 1, 2, 3, size - 1 if size > 1 else 1, size, size + 1, 2 * size, 3 * size + 2]))]
    if k == "seek":
        op["pos"] = rng.choice([0, 0, 1, 2, -1, -2, 5, 20, len(data), len(data) + 3]
                               + ([M + 1, 2**64] if key == "c" else []))
        op["whence"] = rng.choice([0, 0, 0, 1, 1, 2, 2, 3, 5, -1])
    if k == "truncate":
        op["n"] = rng.choice([None, 0, 1, 5, 20, -1])
    return op


HOOK_OPS = ["read", "read1", "peek", "readinto", "readline", "write", "flush", "tell", "seek",
            "truncate", "close", "close", "detach", "detach", "closed", "isatty", "reinit", "reinit"]


def gen_stale_mro(rng):
    """A seek that raises a BlockingIOError subclass, caught, then the raw's own
    ValueError from a later seek: each exception carries its own class, so the second
    is not taken for blocking (`BufferedRandom(raw, 4)` over b'abcdefgh' whose readinto
    answers 4 without storing)."""
    fn = rng.choice(["buf_c", "buf_py"])
    c = {"mod": "pyio", "fn": fn, "kind": 2, "size": rng.choice([2, 4, 8]),
         "data": list(b"abcdefgh"), "flags": [1, 1, 1],
         "rs": [{"bad": rng.choice([1, 2, 4])}], "ws": [],
         "ss": [None] * rng.choice([0, 0, 1]) + [sstep(rng) if rng.random() < 0.3 else
                {"raise": "MyBlockingError", "msg": "x",
                 "mro": [k.__name__ for k in CLASSES["MyBlockingError"].__mro__]}],
         "cs": [], "hooks": [], "qs": [], "flushRet": None, "closeFail": None}
    c["mask"] = fn == "buf_c"
    ops = [{"op": "seek", "pos": rng.choice([0, 1]), "whence": 0}, {"op": "read", "n": 1},
           {"op": "write", "b": list(b"zz")}, {"op": "write", "b": list(b"yyyy")}]
    if rng.random() < 0.5:
        ops.insert(rng.randrange(1, len(ops)), {"op": rng.choice(["tell", "flush", "seek"]), "pos": -1, "whence": 1})
    c["ops"] = ops + [{"op": "closed"}]
    return c


def gen_case(rng):
    fn = rng.choice(["buf_c", "buf_py"])
    key = fn.split("_")[1]
    kind = rng.choice([0, 1, 2, 2])
    size = rng.choice([1, 2, 3, 4, 5, 8, 16, 16, 32])
    if rng.random() < 0.03:
        size = rng.choice([0, -1])
    data = [rng.choice([97, 98, 10, 0]) for _ in range(rng.choice([0, 3, 10, 40, 70]))]
    flags = [1, 1, 1]
    if rng.random() < 0.12:
        flags[rng.randrange(3)] = 0
    c = {"mod": "pyio", "fn": fn, "kind": kind, "size": size, "data": data, "flags": flags,
         "rs": [rstep(rng, key, False) for _ in range(rng.choice([0, 0, 2, 5]))],
         "ws": [rstep(rng, key, True) for _ in range(rng.choice([0, 0, 2, 5]))],
         "ss": [sstep(rng) for _ in range(rng.choice([0, 0, 0, 2]))],
         "cs": [cstep(rng) for _ in range(rng.choice([0, 0, 0, 2, 4]))],
         "hooks": [],
         "qs": [qstep(rng) for _ in range(rng.choice([0, 0, 0, 0, 1, 2, 4]))],
         "flushRet": rng.choice([None, None, None, 42]),
         "closeFail": ["ValueError", "cl"] if rng.random() < 0.1 else None}
    if rng.random() < 0.4:
        ticks = rng.sample(range(1, 12), rng.choice([1, 1, 2, 3]))
        c["hooks"] = [[t, gen_op(rng, rng.choice(HOOK_OPS), size, key, data)] for t in ticks]
    # an int answer in range that moves no byte: the C buffer then holds bytes
    # nobody wrote, which compare by length only
    c["mask"] = key == "c" and any(s and "bad" in s and 0 < s["bad"] < 2**63 for s in c["rs"])
    names = ["seek", "seek", "tell", "tell", "flush", "closed", "readable", "writable", "seekable",
             "isatty", "fileno", "name", "mode", "getstate", "truncate", "reinit"]
    if kind != 1:
        names += ["read"] * 4 + ["read1", "read1", "peek", "peek", "readinto", "readinto", "readinto1",
                                 "readline", "readline", "next"]
    if kind != 0:
        names += ["write"] * 5
    ops = [gen_op(rng, rng.choice(names), size, key, data) for _ in range(rng.randint(1, 10))]
    if rng.random() < 0.3:
        ops.append({"op": "close"})
    if rng.random() < 0.3:
        ops += [{"op": rng.choice(["read", "tell", "flush", "peek", "write", "seek", "closed"]),
                 "n": 1, "b": [97], "pos": 0, "whence": 0}]
    if rng.random() < 0.15:
        # a second close, and what is left to do after one that failed
        ops += [{"op": "close"}, {"op": rng.choice(["close", "read1", "write", "flush", "closed"]),
                                  "n": rng.choice([0, 1]), "b": [97]}]
    if rng.random() < 0.12:
        ops.append({"op": "detach"})
    ops.append({"op": "closed"})
    # a re-entered __init__ can leave a C method reading a buffer nobody filled
    if key == "c" and any(h[1]["op"] == "reinit" for h in c["hooks"]):
        c["mask"] = True
    if c["mask"]:
        # where readline stops depends on the uninitialized bytes it scans for b"\n",
        # which no model can predict: those cases read instead
        for op in ops + [h[1] for h in c["hooks"]]:
            if op["op"] in ("readline", "next"):
                op["op"], op["n"] = "read", op.get("n")
    c["ops"] = ops
    return c


def apply(f, op):
    k = op["op"]
    if k in ("read", "readline"):
        return getattr(f, k)(op["n"])
    if k == "read1":
        return f.read1(op["n"])
    if k == "peek":
        return f.peek(op["n"])
    if k in ("readinto", "readinto1"):
        b = bytearray(b"\xff" * op["n"])
        r = getattr(f, k)(b)
        return [r, bytes(b)]
    if k == "write":
        return f.write(bytes(op["b"]))
    if k == "seek":
        return f.seek(op["pos"], op["whence"])
    if k == "truncate":
        return f.truncate(op["n"])
    if k == "next":
        return next(f)
    if k == "closed":
        return f.closed
    if k == "detach":
        f.detach()
        return None
    if k == "name":
        return f.name
    if k == "mode":
        return f.mode
    if k == "reinit":
        f.__init__(CUR_RAW[0], op["size"])
        return None
    if k == "getstate":
        return f.__getstate__()
    return getattr(f, k)()


def norm(e):
    if type(e) is BlockingIOError:
        return {"exc": "BlockingIOError", "msg": f"{e.strerror}|{e.characters_written}"}
    if type(e) is SystemError and ("without setting an exception" in str(e)
                                   or str(e) == "error return without exception set"):
        # the text depends on whether the call site was specialized; the model's `~` text
        return {"exc": "SystemError", "msg": "~NULL without an exception"}
    return pyio_diff.norm(e)


def mask(r):
    """Bytes compare by length: {"b": [...]} becomes zeros."""
    if isinstance(r, dict):
        if set(r) == {"b"}:
            return {"b": [0] * len(r["b"])}
        return {k: mask(v) for k, v in r.items()}
    if isinstance(r, list):
        return [mask(x) for x in r]
    return r


def run_case(c):
    global CTX
    CTX = {"hung": False}
    key = c["fn"].split("_")[1]
    raw = RAWS[key]()
    raw.setup(c)
    CUR_RAW[0] = raw
    cls = CLS[key, c["kind"]]
    f = cls.__new__(cls)
    # _pyio's constructors build the object as they go, so its hooks are armed (and
    # counted) only once __init__ has returned; C's run during __init__, where `ok` is 0
    raw.buf = f if key == "c" else None
    try:
        try:
            f.__init__(raw, c["size"])
        except Exception as e:
            return norm(e)
        if key == "py":
            raw.buf, raw.n = f, 0
        out = []
        for op in c["ops"]:
            out.append(outcome(lambda: apply(f, op)))
            if CTX["hung"]:
                return {"ok": None, "hang": True}
    except Deadlock:
        return {"ok": None, "hang": True}
    finally:
        # finalizing `f` after this returns flushes and closes the raw
        raw.disarm()
    if c["mask"]:
        out = mask(out)
    return {"ok": out, "log": list(raw.calls), "data": list(raw.d), "pos": raw.p}


# A child that has not answered by then is blocked for good: its outcome is a hang.
HANG_SECONDS = 5


def run_forked(c):
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        os.close(r)
        # an abort prints "Fatal Python error" there
        os.dup2(os.open(os.devnull, os.O_WRONLY), 2)
        try:
            data = json.dumps(run_case(c)).encode()
        except BaseException as e:
            data = json.dumps({"harness": repr(e)}).encode()
        with os.fdopen(w, "wb") as fo:
            fo.write(data)
        os._exit(0)
    os.close(w)
    chunks, deadline = [], time.monotonic() + HANG_SECONDS
    with os.fdopen(r, "rb") as fi:
        while True:
            left = deadline - time.monotonic()
            ready = select.select([fi], [], [], max(left, 0))[0]
            if not ready:
                os.kill(pid, signal.SIGKILL)
                os.waitpid(pid, 0)
                return {"ok": None, "hang": True}
            chunk = os.read(fi.fileno(), 1 << 16)
            if not chunk:
                break
            chunks.append(chunk)
    _, status = os.waitpid(pid, 0)
    if os.WIFSIGNALED(status):
        return {"ok": None, "crash": True} if os.WTERMSIG(status) in (signal.SIGSEGV, signal.SIGBUS, signal.SIGABRT, signal.SIGFPE) else {
            "signal": os.WTERMSIG(status)}
    return json.loads(b"".join(chunks))


def run_python(c):
    # a case that calls back into the object can crash or block the process
    if c["hooks"]:
        return run_forked(c)
    return run_case(c)


# CHUNK_START=k skips the first k cases of the seed, so one seed's cases can be run in
# chunks (`--cases` is then the chunk length)
_SEEN = [0]


def gen_chunk(rng):
    c = gen_case(rng)
    _SEEN[0] += 1
    return c if _SEEN[0] > int(os.environ.get("CHUNK_START", "0")) else None


def main():
    """common.main, except for a case the model calls undefined behaviour ("ub": a
    memcpy of a negative length, a store through a stale or NULL pointer above the
    unmapped page). Its outcome is not compared, and it is not counted in "agree":
    only the results of the operations that finished before the UB are, by running
    those operations alone (forked) and comparing their results with the model's.
    A UB inside `__init__` has no such prefix."""
    import argparse
    import random
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = random.Random(args.seed)
    cases = []
    while len(cases) < args.cases:
        c = gen_chunk(rng)
        if c is not None:
            cases.append(c)
    # 2% more cases from their own generator, so a seed's other cases stay as they were
    extra = random.Random(f"{args.seed}-{os.environ.get('CHUNK_START', '0')}")
    cases += [gen_stale_mro(extra) for _ in range(args.cases // 50)]
    mismatches, bad, by_fn = 0, 0, {}
    ub, ub_init, ub_pre_ok, ub_ops = 0, 0, 0, 0

    def report(c, py, lo):
        nonlocal mismatches
        mismatches += 1
        if mismatches <= 20:
            print(f"MISMATCH {json.dumps(c)}\n  python: {py}\n  lean:   {lo}", file=sys.stderr)

    for c, lo in zip(cases, common.run_lean(cases)):
        tot = by_fn.setdefault(c["fn"], [0, 0, 0])
        if lo.get("ub"):
            ub += 1
            tot[2] += 1
            pre = lo.get("prefix")
            if pre is None:
                ub_init += 1
                continue
            # the operations before the one the model calls UB, in a fresh process
            py = run_forked(dict(c, ops=c["ops"][:len(pre)]))
            if py.get("ok") == pre:
                ub_pre_ok += 1
                ub_ops += len(pre)
            else:
                report(c, py, lo)
            continue
        tot[0] += 1
        py = run_python(c)
        ok = "harness_error" not in lo and common.agree(py, lo)
        tot[1] += ok
        if not ok:
            bad += 1
            report(c, py, lo)
    for fn, (n, good, u) in sorted(by_fn.items()):
        print(f"{fn:20s} {good}/{n} agree ({u} ub, not compared)")
    compared = len(cases) - ub
    print(f"ub cases: {ub} ({ub_init} in __init__); the results before the UB agree in "
          f"{ub_pre_ok}/{ub - ub_init} ({ub_ops} operations)")
    print(f"python {sys.version.split()[0]}: {compared - bad}/{compared} agree ({ub} ub, not compared)")
    sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
