"""Differential test: Lean models of zoneinfo (both twins) vs. the running CPython.

Usage: python3 difftest/datetime_zoneinfo_diff.py [--cases N] [--seed S]

Cases ("mod": "datetime", "fn" starting with "zi_"):
  zi_data      zoneinfo._common.load_data on generated TZif bytes (the reader both twins share)
  zi_c, zi_py  ZoneInfo.from_file(io.BytesIO(data)) of the C or the pure-Python class, then
               utcoffset/dst/tzname for None and for query datetimes, and fromutc
  zi_cache_*   a run of ZoneInfo(key) / clear_cache calls on keys under a temporary TZPATH
  zi_cerr_*    the same on the base class or a fresh subclass, with keys that are plain str
               (separate objects sharing a text) or str subclasses whose __eq__ raises (with their own or a shared hash),
               only_keys iterators that raise after their keys, and del Sub._weak_cache

TZif files range from well-formed v1-v4 files to truncated and inconsistent ones: counts at
their boundaries, indices out of range, designations without NUL or not UTF-8, extreme
transition times and offsets, isdst bytes other than 0/1, and footers built from the POSIX
TZ grammar and then mutated.
"""

import datetime as dtm
import io
import os
import struct
import sys
import tempfile
import warnings
import weakref

import common

warnings.simplefilter("ignore")

# The C class, captured before import_fresh_module rebinds the package.
import zoneinfo as CZ_PKG  # noqa: E402
import zoneinfo._common as ZCOMMON  # noqa: E402
CZI = CZ_PKG.ZoneInfo
assert type(CZI.__dict__["utcoffset"]).__name__ == "method_descriptor"
from test.support import import_helper  # noqa: E402
PZ_PKG = import_helper.import_fresh_module("zoneinfo", blocked=["_zoneinfo"])
PZI = PZ_PKG.ZoneInfo
assert PZI is not CZI and type(PZI.__dict__["utcoffset"]).__name__ == "function"
TZPATH_MODS = {id(m): m for m in (sys.modules.get("zoneinfo._tzpath"), PZ_PKG._tzpath,
                                  CZ_PKG._tzpath) if m is not None}.values()

EPOCH = dtm.datetime(1970, 1, 1)
MIN_TS = int((dtm.datetime(1, 1, 1) - EPOCH).total_seconds())
MAX_TS = int((dtm.datetime(9999, 12, 31, 23, 59, 59) - EPOCH).total_seconds())


class Sub(dtm.datetime):
    pass


# ---- TZ strings -------------------------------------------------------------

def gen_abbr(rng):
    r = rng.random()
    if r < 0.7:
        return "".join(rng.choice("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz")
                       for _ in range(rng.choice([1, 2, 3, 3, 3, 4, 5])))
    if r < 0.98:
        return "<" + "".join(rng.choice("ABCXYZ0123456789+-") for _ in range(rng.choice([1, 2, 3, 3, 5]))) + ">"
    return rng.choice(["<>", "<", "A<B>", "<A", "", "1AB"])


def gen_hms(rng, signed, hmax):
    s = ""
    if signed and rng.random() < 0.5:
        s += rng.choice("+-")
    edge = rng.random() < 0.15
    if edge:
        h = rng.choice([24, 25, 99, 100, 166, 167, 168, 999, 1000])
    else:
        h = rng.randint(0, hmax)
    s += rng.choice([str(h), str(h).zfill(2), str(h).zfill(3)]) if h < 1000 else str(h)
    if rng.random() < 0.5:
        s += ":" + (rng.choice(["60", "99", "5", "123"]) if edge and rng.random() < 0.5
                    else rng.choice(["00", "30", "45", "59", "15"]))
        if rng.random() < 0.4:
            s += ":" + (rng.choice(["99", "1", "600"]) if edge and rng.random() < 0.5
                        else rng.choice(["00", "15", "59", "30"]))
    return s


def gen_rule(rng):
    r = rng.random()
    if r < 0.55:
        edge = rng.random() < 0.1
        m = rng.choice([0, 13, 99]) if edge else rng.choice([1, 2, 3, 10, 11, 12, rng.randint(1, 12)])
        w = rng.choice([0, 6, 9]) if edge and rng.random() < 0.5 else rng.choice([1, 2, 3, 4, 5, 5])
        d = rng.choice([7, 8]) if edge and rng.random() < 0.5 else rng.choice([0, 1, 6, 0, rng.randint(0, 6)])
        s = f"M{m}.{w}.{d}"
        if rng.random() < 0.05:
            s = rng.choice([f"M{m}.{w}", f"M{m}{w}.{d}", f"M0{m}.{w}.{d}", f"M{m}.{w}.{d}0", "M", f"M{m}:{w}.{d}"])
    elif r < 0.8:
        s = "J" + str(rng.choice([0, 366, 1000]) if rng.random() < 0.08 else rng.choice([1, 59, 60, 61, 100, 365, rng.randint(1, 365)]))
    else:
        s = str(rng.choice([366, 999, 1000]) if rng.random() < 0.08 else rng.choice([0, 1, 58, 59, 60, 100, 200, 364, 365, rng.randint(0, 365)]))
    if rng.random() < 0.5:
        s += "/" + gen_hms(rng, True, 167 if rng.random() < 0.3 else 26)
    return s


def gen_tzstr(rng):
    r = rng.random()
    s = gen_abbr(rng)
    if r < 0.03:
        return s
    s += gen_hms(rng, True, 24)
    if r < 0.25:
        return s
    s += gen_abbr(rng)
    if rng.random() < 0.6:
        s += gen_hms(rng, True, 24)
    if rng.random() < 0.95:
        s += "," + gen_rule(rng)
        if rng.random() < 0.95:
            s += "," + gen_rule(rng)
    return s


def mutate(rng, b):
    b = bytearray(b)
    for _ in range(rng.choice([1, 1, 2])):
        k = rng.random()
        pos = rng.randint(0, len(b))
        if k < 0.25 and b:
            del b[min(pos, len(b) - 1)]
        elif k < 0.45:
            b[pos:pos] = bytes([0])
        elif k < 0.6:
            b[pos:pos] = bytes([rng.choice([0xff, 0xc3, 0xe2, 0x80])]) + (bytes([0xa9]) if rng.random() < 0.5 else b"")
        else:
            b[pos:pos] = rng.choice([b",", b"/", b":", b"<", b">", b"+", b"-", b"5", b"A", b" ", b"\n", b".", b"J", b"M"])
    return bytes(b)


def gen_footer(rng):
    s = gen_tzstr(rng).encode()
    if rng.random() < 0.15:
        s = mutate(rng, s)
    if rng.random() < 0.05:
        s = b""
    return s


# ---- TZif files -------------------------------------------------------------

def gen_time(rng):
    r = rng.random()
    if r < 0.85:
        return rng.randint(-2**31, 2**32)
    if r < 0.95:
        return rng.randint(MIN_TS - 10**6, MAX_TS + 10**6)
    return rng.choice([2**63 - 1, -2**63, 2**63 - 3600, -2**63 + 1800, 2**59, -2**59])


def gen_offset(rng):
    r = rng.random()
    if r < 0.85:
        return rng.choice([0, 3600, -3600, 7200, -18000, -14400, 19800, 1800, 3600 * 14, -3600 * 12,
                           rng.randint(-86400, 86400)])
    if r < 0.95:
        return rng.choice([-86400, 86400, 86399, -86399, 100000])
    return rng.choice([2**31 - 1, -2**31, 2**30])


def pack_block(rng, version, trans, idx, types, abbrs, leapcnt, isstd, isut, tsize, counts):
    timecnt, typecnt, charcnt = counts
    h = b"TZif" + version + bytes(15) + struct.pack(">6l", isut, isstd, leapcnt, timecnt, typecnt, charcnt)
    fmt = ">q" if tsize == 8 else ">l"
    body = b""
    for t in trans:
        body += struct.pack(fmt, t) if tsize == 8 else struct.pack(fmt, max(-2**31, min(2**31 - 1, t)))
    body += bytes(i & 0xff for i in idx)
    for (u, d, a) in types:
        body += struct.pack(">lBB", u, d & 0xff, a & 0xff)
    body += abbrs
    body += bytes(rng.randint(0, 255) for _ in range(leapcnt * (tsize + 4) + isstd + isut))
    return h + body


def gen_tzif(rng):
    version = rng.choice([b"2", b"2", b"3", b"4", b"\x00", b"1", b"0", b"9", bytes([rng.randint(0, 255)])])
    ntypes = rng.choice([1, 1, 2, 2, 3, 4, 6, 0])
    names = []
    abbrs = b""
    for _ in range(max(ntypes, 1)):
        n = rng.choice(["LMT", "EST", "EDT", "CET", "CEST", "UTC", "AB", "X", "+05", "-0330"])
        if rng.random() < 0.03:
            n = rng.choice(["\xe9T", "€X"])
        names.append(len(abbrs))
        abbrs += n.encode()
        abbrs += b"\x00"
    if rng.random() < 0.05:
        abbrs = abbrs[:-1]
    if rng.random() < 0.03:
        abbrs += b"\xff\x00"
        names.append(len(abbrs) - 2)
    types = []
    for i in range(ntypes):
        isdst = rng.choice([0, 0, 1, 1]) if rng.random() < 0.95 else rng.choice([2, 255, 128, 3])
        a = rng.choice(names) if rng.random() < 0.95 else rng.choice([len(abbrs), len(abbrs) + 3, 255, 128, 1])
        types.append((gen_offset(rng), isdst, a))
    ntrans = rng.choice([0, 0, 1, 1, 2, 3, 5, 8, 12])
    if ntypes == 0 and rng.random() < 0.8:
        ntrans = 0
    base = rng.randint(-2**31, 2**31)
    trans = sorted(base + rng.randint(-10**8, 10**8) * rng.choice([1, 1, 3]) for _ in range(ntrans))
    if rng.random() < 0.1 and trans:
        trans[rng.randrange(len(trans))] = gen_time(rng)
    if rng.random() < 0.05:
        rng.shuffle(trans)
    idx = [rng.randrange(max(ntypes, 1)) for _ in trans]
    if rng.random() < 0.03 and idx:
        idx[rng.randrange(len(idx))] = rng.choice([ntypes, 255])
    leapcnt = rng.choice([0, 0, 0, 1, 2])
    isstd = rng.choice([0, ntypes])
    isut = rng.choice([0, ntypes])
    counts = [len(trans), ntypes, len(abbrs)]
    if rng.random() < 0.06:
        k = rng.randrange(3)
        counts[k] = rng.choice([counts[k] + 1, counts[k] - 1, 0, -1, -2**31, 2**31 - 1, counts[k] + 6])
    v2 = version not in (b"\x00", b"1")
    if v2:
        if rng.random() < 0.5:
            v1 = pack_block(rng, version, trans, idx, types, abbrs, leapcnt, isstd, isut, 4, counts)
        else:
            v1 = b"TZif" + version + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 0, 0)
        if rng.random() < 0.02:
            v1 = v1[:rng.randint(0, len(v1))]
        data = v1 + pack_block(rng, version, trans, idx, types, abbrs, leapcnt, isstd, isut, 8, counts)
        footer = gen_footer(rng)
        r = rng.random()
        if r < 0.9:
            data += b"\n" + footer + b"\n"
        elif r < 0.94:
            data += b"\n" + footer
        elif r < 0.97:
            data += footer + b"\n"
        else:
            data += b"\n"
    else:
        data = pack_block(rng, version, trans, idx, types, abbrs, leapcnt, isstd, isut, 4, counts)
    if rng.random() < 0.04:
        data = data[:rng.randint(0, len(data))]
    return data, trans


def gen_footer_only(rng):
    """A v2 file with no transitions, one type, and a generated footer: mostly the TZ parser."""
    version = rng.choice([b"2", b"3", b"4"])
    hdr0 = b"TZif" + version + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 0, 0)
    ntypes = rng.choice([0, 1])
    hdr = b"TZif" + version + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, ntypes, 4 * ntypes)
    body = struct.pack(">lBB", 0, 0, 0) + b"UTC\x00" if ntypes else b""
    return hdr0 + hdr + body + b"\n" + gen_footer(rng) + b"\n", []


def ts_to_fields(t):
    t = max(MIN_TS, min(MAX_TS, t))
    d = EPOCH + dtm.timedelta(seconds=t)
    return [d.year, d.month, d.day, d.hour, d.minute, d.second]


def gen_queries(rng, trans):
    qs, us = [], []
    for _ in range(rng.choice([4, 6, 8])):
        r = rng.random()
        if r < 0.45 and trans:
            t = rng.choice(trans) + rng.choice([-86400, -3601, -3600, -1, 0, 1, 1800, 3599, 3600, 7200, 86400])
        elif r < 0.8:
            y = rng.choice([1970, 2000, 2021, 2024, 2037, 2100, 1900, rng.randint(1971, 2200)])
            mo = rng.choice([1, 3, 3, 10, 10, 11, 12, rng.randint(1, 12)])
            d = rng.randint(1, 28)
            t = int((dtm.datetime(y, mo, d) - EPOCH).total_seconds()) + rng.randint(-2, 26) * 3600 + rng.choice([0, 1, -1, 1800])
        else:
            t = rng.randint(MIN_TS, MAX_TS) if rng.random() < 0.5 else rng.choice([MIN_TS, MAX_TS, MIN_TS + 3600, MAX_TS - 86400])
        f = ts_to_fields(t)
        sub = 1 if rng.random() < 0.15 else 0
        qs.append(f + [rng.choice([0, 1]), sub])
        if rng.random() < 0.7:
            us.append(f + [0, sub])
    return qs, us


def gen_case(rng):
    r = rng.random()
    if r < 0.3:
        data, _ = gen_tzif(rng) if rng.random() < 0.7 else gen_footer_only(rng)
        return {"mod": "datetime", "fn": "zi_data", "data": list(data)}
    if r < 0.9:
        data, trans = gen_tzif(rng) if rng.random() < 0.6 else gen_footer_only(rng)
        qs, us = gen_queries(rng, trans)
        return {"mod": "datetime", "fn": rng.choice(["zi_c", "zi_py"]), "data": list(data), "q": qs, "u": us}
    if rng.random() < 0.5:
        return gen_cerr(rng)
    ops = []
    for _ in range(rng.randint(1, 30)):
        k = rng.random()
        if k < 0.85:
            ops.append(["get", rng.randrange(14)])
        elif k < 0.9:
            ops.append(["clear"])
        else:
            ops.append(["keys", [rng.randrange(14) for _ in range(rng.randint(0, 3))]])
    return {"mod": "datetime", "fn": rng.choice(["zi_cache_c", "zi_cache_py"]), "ops": ops,
            "loads": LOADABLE}


def gen_cerr(rng):
    nkeys = 10
    # hold: the harness keeps every instance it gets referenced, so a C eject cannot collect a zone
    # (and remove its weak entry) inside clear_cache; unhashable keys (kind 3) only then
    hold = rng.random() < 0.5
    kinds = [rng.choice([0, 0, 0, 1, 2, 3] if hold else [0, 0, 0, 1, 2]) if rng.random() < 0.6 else 0
             for _ in range(nkeys)]
    # separate str objects with equal text compare equal
    texts = [i if rng.random() < 0.6 else rng.randrange(nkeys) for i in range(nkeys)]
    sub = rng.random() < 0.4
    ops = []
    for _ in range(rng.randint(1, 25)):
        r = rng.random()
        if r < 0.7:
            ops.append(["get", rng.randrange(nkeys)])
        elif r < 0.77:
            ops.append(["clear"])
        elif r < 0.95 or not sub:
            ops.append(["keys", [rng.randrange(nkeys) for _ in range(rng.randint(0, 4))],
                        rng.random() < 0.3])
        else:
            ops.append(["del"])
    return {"mod": "datetime", "fn": rng.choice(["zi_cerr_c", "zi_cerr_py"]), "ops": ops,
            "kinds": kinds, "texts": texts, "loads": LOADABLE, "sub": sub, "hold": hold}


# ---- running CPython --------------------------------------------------------

def td_s(td):
    return None if td is None else td.days * 86400 + td.seconds


def enc_name(n):
    return None if n is None else list(n.encode("utf-8"))


def enc_exc(e):
    return {"exc": type(e).__name__, "msg": str(e)}


def lookup(z, arg):
    try:
        return {"ok": [td_s(z.utcoffset(arg)), td_s(z.dst(arg)), enc_name(z.tzname(arg))]}
    except Exception as e:
        return enc_exc(e)


def mkdt(q, tz=None):
    cls = Sub if q[7] else dtm.datetime
    return cls(*q[:6], fold=q[6], tzinfo=tz)


def run_zone(case, Z):
    try:
        z = Z.from_file(io.BytesIO(bytes(case["data"])))
    except Exception as e:
        return enc_exc(e)
    out = {"none": lookup(z, None), "q": [lookup(z, mkdt(q)) for q in case["q"]], "u": []}
    for q in case["u"]:
        dt = mkdt(q, z)
        try:
            r = z.fromutc(dt)
            off = r.replace(tzinfo=None) - dt.replace(tzinfo=None)
            out["u"].append({"ok": [td_s(off), bool(r.fold)]})
        except Exception as e:
            out["u"].append(enc_exc(e))
    return {"ok": out}


TMP = tempfile.mkdtemp(prefix="zi_diff_")
LOADABLE = list(range(8))
for k in LOADABLE:
    hdr = b"TZif2" + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 1, 4)
    blob = hdr + struct.pack(">lBB", 3600 * k, 0, 0) + b"ABC\x00"
    with open(os.path.join(TMP, f"k{k}"), "wb") as f:
        f.write(blob + blob + b"\nABC-%d\n" % k)
for m in TZPATH_MODS:
    m.reset_tzpath([TMP])


def run_cache(case, Z):
    Z.clear_cache()
    raised, refs = [], {}
    for op in case["ops"]:
        if op[0] == "get":
            try:
                inst = Z(f"k{op[1]}")
                refs.setdefault(op[1], []).append(weakref.ref(inst))
                del inst
                raised.append(False)
            except Exception:
                raised.append(True)
        elif op[0] == "clear":
            Z.clear_cache()
            raised.append(False)
        else:
            Z.clear_cache(only_keys=[f"k{k}" for k in op[1]])
            raised.append(False)
    # no gc.collect(): zones hold no cycles, so refcounting frees them at once
    if Z is PZI:
        keys = [int(k[1:]) for k in reversed(Z._strong_cache)]
    else:
        keys = sorted(k for k, rs in refs.items() if any(r() is not None for r in rs))
    Z.clear_cache()
    return {"ok": [keys, raised]}


class RaiseKey(str):
    def __eq__(self, other):
        raise RuntimeError("eq")
    __hash__ = str.__hash__


class SameHashKey(RaiseKey):
    def __hash__(self):
        return 0


class NoHashKey(str):
    __hash__ = None


def run_cerr(case, Z):
    Z.clear_cache()
    keys = [(str, RaiseKey, SameHashKey, NoHashKey)[kd]("".join(["k", str(t)]))
            for kd, t in zip(case["kinds"], case["texts"])]
    assert len({id(k) for k in keys}) == len(keys)
    index = {id(k): i for i, k in enumerate(keys)}
    if case["sub"]:
        class Sub(Z):
            pass
        cls = Sub
    else:
        cls = Z
    seen = []  # weakrefs, numbered by first appearance
    held = []

    def canon(inst):
        for n, r in enumerate(seen):
            if r() is inst:
                return n
        seen.append(weakref.ref(inst))
        return len(seen) - 1

    outs = []
    for op in case["ops"]:
        try:
            if op[0] == "get":
                inst = cls(keys[op[1]])
                if case["hold"]:
                    held.append(inst)
                outs.append({"ok": [index[id(inst.key)], canon(inst)]})
                del inst
            elif op[0] == "clear":
                cls.clear_cache()
                outs.append({"ok": None})
            elif op[0] == "keys":
                def it(ks=[keys[k] for k in op[1]], err=op[2]):
                    yield from ks
                    if err:
                        raise ValueError("it")
                cls.clear_cache(only_keys=it())
                outs.append({"ok": None})
            else:
                del cls._weak_cache
                outs.append({"ok": None})
        except Exception as e:
            outs.append({"exc": type(e).__name__})
    strong = None
    if Z is PZI:
        strong = [[index[id(k)], canon(v)] for k, v in cls._strong_cache.items()]
    alive = sorted({n for n, r in enumerate(seen) if r() is not None})
    try:
        cls.clear_cache()
    except AttributeError:  # C subclass after del Sub._weak_cache
        pass
    Z.clear_cache()
    return {"ok": [outs, alive, strong]}


def run_python(case):
    fn = case["fn"]
    if fn == "zi_data":
        def f():
            ti, tu, uo, dst, ab, tz = ZCOMMON.load_data(io.BytesIO(bytes(case["data"])))
            return [list(ti), list(tu), list(uo), list(dst), [list(a.encode()) for a in ab],
                    None if tz is None else list(tz)]
        return common.py_result(f)
    if fn in ("zi_c", "zi_py"):
        return run_zone(case, CZI if fn == "zi_c" else PZI)
    if fn in ("zi_cerr_c", "zi_cerr_py"):
        return run_cerr(case, CZI if fn == "zi_cerr_c" else PZI)
    return run_cache(case, CZI if fn == "zi_cache_c" else PZI)


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
