"""Differential test: Lean model of pickle (C `_pickle` and pure-Python twins) vs. the running CPython.

Usage: python3 difftest/pickle_diff.py [--cases N] [--seed S]

Three kinds of case, each run on one twin ("impl": "c" is `pickle.dumps` /
`pickle.loads`, "py" is `pickle._dumps` / `pickle._loads`):

* dumps: the exact bytes of `dumps(val, proto)` for plain data (None, bool,
  int, str, bytes, bytearray, tuple, list, dict, set, frozenset) with shared
  sub-objects, at protocols 0-5 and a few out-of-range protocol arguments.
* roundtrip: `loads(dumps(val, proto))` for every encoder/decoder pairing.
* loads: hand-crafted streams made only of data opcodes. A scanner that
  follows both unpicklers' argument boundaries rejects any stream in which a
  code-running opcode (GLOBAL, REDUCE, INST, ...) could be executed. Declared
  lengths and memo indices need no limit since 3.15: payloads are read in
  chunks and sparse memo keys go to a dict. As a second line of defence
  `__import__` is disabled while hand-crafted streams are loaded. `memo_stream`
  drives the memo array, its dict and MEMOIZE; `chunk_stream` drives the 1 MiB
  chunks of BINBYTES and BYTEARRAY8 across the end of a frame.

* genops, optimize, dis: `pickletools` over real pickles, hand-crafted streams,
  mutations of both and random bytes. Nothing here runs a stream: `genops` only
  parses it and `optimize` only copies it. Streams with a FLOAT byte are
  skipped (`float()` of text needs the binary64 model), and for `dis` so are
  floats and non-Latin-1 characters, whose repr the model does not render.

Values are sent to the model with their object identity: every memoizable
object carries an id derived from `id()`, except CPython's cached
one-character Latin-1 strs and one-byte bytes, which use canonical ids so the
model can tell when a temporary the pickler creates is the same object.
Exits non-zero on any mismatch. See difftest/common.py.
"""

import _colorize
import builtins
import codecs
import io
import json
import pickle
import pickletools
import struct
import sys
import warnings

import common

SSIZE_MAX = sys.maxsize
OBJS = {}  # case number -> the Python object (kept alive while the test runs)

# ---------------------------------------------------------------- values


INT_EDGES = [0, 1, -1, 2, 127, 128, 255, 256, 257, -128, -129, -255, -256, -257, 0xFFFF, 0x10000,
             -0x8000, -0x8001, 0x7FFF, 0x8000, 2**31 - 1, 2**31, -2**31, -2**31 - 1,
             2**63 - 1, 2**63, -2**63, -2**63 - 1, 2**64, -2**64, 2**64 - 1]
for _k in (8, 16, 24, 32, 40, 63, 64, 127, 128, 2039, 2040, 2041, 2047, 2048, 2049, 4000):
    INT_EDGES += [2**_k, 2**_k - 1, -2**_k, -2**_k + 1, -2**_k - 1, 2**(_k - 1), -2**(_k - 1)]
CHARS = ['a', 'b', 'Z', '0', ' ', '\\', '\n', '\r', '\x00', '\x1a', '\x7f', '\x80', '\xe9', '\xff',
         'Ā', '€', '\ud800', '\udfff', '\ud83d', '�', '\U0001f600', '\U0010ffff', 'u', 'U']


class ValueGen:
    def __init__(self, rng):
        self.rng = rng
        self.pool_h = []   # hashable objects created so far (for sharing)
        self.pool_m = []   # mutable/unhashable objects created so far

    def int_(self):
        r = self.rng
        k = r.random()
        if k < 0.5:
            return r.choice(INT_EDGES) + r.choice([0, 0, 0, 1, -1])
        if k < 0.8:
            return r.randint(-300, 70000)
        if k < 0.97:
            return r.randint(-2**70, 2**70)
        return r.choice([10**4299, 10**4300, -10**4300 + 1, 10**4300 - 1, 2**14300])

    def text(self):
        r = self.rng
        n = r.choice([0, 1, 1, 2, 3, 5, 8, r.randrange(20), r.choice([84, 85, 127, 128, 255, 256, 257])])
        if r.random() < 0.004:
            n = r.choice([65530, 65535, 65536, 65540])
        return ''.join(r.choice(CHARS) for _ in range(n))

    def str_(self):
        s = self.text()
        if len(s) > 1:
            s = ''.join(list(s))  # a fresh, non-interned object
        return s

    def bytes_(self):
        r = self.rng
        n = r.choice([0, 1, 1, 2, 3, 6, r.randrange(30), r.choice([255, 256, 257])])
        if r.random() < 0.004:
            n = r.choice([65535, 65536, 65537])
        return bytes(r.randrange(256) if r.random() < 0.5 else r.choice([0, 10, 92, 97, 255]) for _ in range(n))

    def hashable(self, depth):
        r = self.rng
        if self.pool_h and r.random() < 0.15:
            return r.choice(self.pool_h)
        k = r.randrange(8 if depth < 3 else 6)
        if k == 0:
            x = r.choice([None, True, False])
        elif k in (1, 2):
            x = self.int_()
        elif k == 3:
            x = self.str_()
        elif k == 4:
            x = self.bytes_()
        elif k == 5:
            x = r.choice([0, 1, True, 'a', ''])
        elif k == 6:
            x = tuple(self.hashable(depth + 1) for _ in range(r.choice([0, 1, 2, 3, 4, 5])))
        else:
            x = frozenset(self.hashable(depth + 1) for _ in range(r.choice([0, 1, 2, 3])))
        self.pool_h.append(x)
        return x

    def big_size(self):
        return self.rng.choice([999, 1000, 1001, 1002, 1999, 2000, 2001])

    def value(self, depth=0):
        r = self.rng
        if self.pool_m and r.random() < 0.08:
            return r.choice(self.pool_m)
        k = r.randrange(11 if depth < 3 else 4)
        if k < 3:
            return self.hashable(depth)
        if k == 3:
            x = bytearray(self.bytes_())
        elif k == 4:
            x = tuple(self.value(depth + 1) for _ in range(r.choice([0, 1, 2, 3, 4, 6])))
            if r.random() < 0.3:
                self.pool_h.append(x) if _hashable(x) else self.pool_m.append(x)
            return x
        elif k in (5, 6):
            n = r.choice([0, 1, 2, 3, 5])
            if r.random() < 0.03:
                return [r.choice([None, 1, 'a', 300]) for _ in range(self.big_size())]
            x = [self.value(depth + 1) for _ in range(n)]
        elif k == 7:
            n = r.choice([0, 1, 2, 3])
            if r.random() < 0.03:
                return {i: (i if r.random() < 0.5 else None) for i in range(self.big_size())}
            x = {self.hashable(depth + 1): self.value(depth + 1) for _ in range(n)}
        elif k == 8:
            if r.random() < 0.03:
                return set(range(self.big_size()))
            x = {self.hashable(depth + 1) for _ in range(r.choice([0, 1, 2, 3]))}
        elif k == 9:
            return self.hashable(depth)
        else:
            x = frozenset(self.hashable(depth + 1) for _ in range(r.choice([0, 1, 2, 3])))
            self.pool_h.append(x)
            return x
        self.pool_m.append(x)
        return x


def _hashable(x):
    try:
        hash(x)
        return True
    except TypeError:
        return False


def encode_value(x):
    """The value as model JSON, with object ids from id()."""
    ids = {}

    def oid(o):
        if type(o) is str and len(o) == 1 and ord(o) < 256 and o is chr(ord(o)):
            return {"s1": ord(o)}
        if type(o) is bytes and len(o) == 1 and o is bytes([o[0]]):
            return {"b1": o[0]}
        return {"u": ids.setdefault(id(o), len(ids))}

    def enc(o):
        t = type(o)
        if o is None:
            return {"t": "none"}
        if t is bool:
            return {"t": "bool", "v": o}
        if t is int:
            return {"t": "int", "v": hex(o)}
        if t is str:
            return {"t": "str", "o": oid(o), "v": [ord(c) for c in o]}
        if t is bytes:
            return {"t": "bytes", "o": oid(o), "v": list(o)}
        if t is bytearray:
            return {"t": "bytearray", "o": oid(o), "v": list(o)}
        if t is tuple:
            return {"t": "tuple", "o": oid(o), "v": [enc(e) for e in o]}
        if t is list:
            return {"t": "list", "o": oid(o), "v": [enc(e) for e in o]}
        if t is dict:
            return {"t": "dict", "o": oid(o), "v": [[enc(k), enc(v)] for k, v in o.items()]}
        if t is set:
            return {"t": "set", "o": oid(o), "v": [enc(e) for e in o]}
        if t is frozenset:
            return {"t": "frozenset", "o": oid(o), "v": [enc(e) for e in o]}
        raise TypeError(t)

    return enc(x)


def compact(j):
    return json.dumps(j, sort_keys=True, separators=(',', ':'))


def decoded(x):
    """A decoded object as model JSON (see lean/PyLean/Pickle/Diff.lean)."""
    path = []

    def mk(t, v):
        return {"t": t, "v": v}

    def enc(o):
        t = type(o)
        if o is None:
            return mk("none", None)
        if t is bool:
            return mk("bool", o)
        if t is int:
            return mk("int", hex(o))
        if t is str:
            return mk("str", [ord(c) for c in o])
        if t is bytes:
            return mk("bytes", list(o))
        if t is tuple:
            return mk("tuple", [enc(e) for e in o])
        if t is frozenset:
            return mk("frozenset", sorted((enc(e) for e in o), key=compact))
        if t in (list, dict, set, bytearray):
            if id(o) in path:
                return mk("rec", path.index(id(o)))
            path.append(id(o))
            try:
                if t is list:
                    return mk("list", [enc(e) for e in o])
                if t is dict:
                    return mk("dict", [[enc(k), enc(v)] for k, v in o.items()])
                if t is set:
                    return mk("set", sorted((enc(e) for e in o), key=compact))
                return mk("bytearray", list(o))
            finally:
                path.pop()
        if o in (bytes, bytearray, set, frozenset):
            return mk("glob", o.__name__)
        raise TypeError(t)

    return enc(x)


# ---------------------------------------------------------------- streams

def numtxt(rng):
    return rng.choice([
        b'0', b'1', b'00', b'01', b' 1', b'+1', b'-0', b'-1', b' 0', b'+0', b'12', b'1_0', b'_1', b'1_',
        b'1__0', b'1 ', b'\t3', b'99999999999999999999', b'-9223372036854775808', b'9223372036854775807',
        b'9223372036854775808', b'-9223372036854775809', b'0x1', b'', b' ', b'1\x0b', b'\x0c2', b'3\r',
        b'1e3', b'--1', b'+-1', b'1\x00', b'1\x00junk', b'\x00', b'12\x00', b'1\x00\x00', b'\xff', b'1\xff',
        b'0' * rng.randrange(1, 6) + b'7', str(rng.randrange(-300, 300)).encode(),
        b'0' * rng.choice([4299, 4300, 4301, 5000]) + rng.choice([b'', b'1', b'7']),
        b'1' * rng.choice([19, 20, 4300, 4301]), b'-' + b'0' * 4400 + b'5',
    ])


def u32(n): return struct.pack('<I', n)
def i32(n): return struct.pack('<i', n)
def u64(n): return struct.pack('<Q', n)


def hand_op(rng):
    k = rng.randrange(44)
    if k < 2: return b'('
    if k == 2: return b'N'
    if k in (3, 4): return b'I' + numtxt(rng) + b'\n'
    if k == 5: return b'L' + numtxt(rng) + rng.choice([b'L', b'', b'LL']) + b'\n'
    if k == 6: return b'K' + bytes([rng.randrange(256)])
    if k == 7: return b'M' + struct.pack('<H', rng.randrange(65536))
    if k == 8: return b'J' + i32(rng.choice([0, 1, -1, 2**31 - 1, -2**31, rng.randrange(-2**31, 2**31)]))
    if k == 9:
        d = bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 2, 3, 8])))
        return b'\x8a' + bytes([len(d)]) + d
    if k == 10:
        d = bytes(rng.randrange(256) for _ in range(rng.choice([0, 1, 2])))
        return b'\x8b' + i32(rng.choice([len(d), len(d), -1, -2**31])) + d
    if k == 11: return rng.choice([b')', b']', b'}', b'\x8f'])
    if k == 12: return rng.choice([b't', b'l', b'd', b'\x91'])
    if k == 13: return rng.choice([b'\x85', b'\x86', b'\x87'])
    if k in (14, 15): return rng.choice([b'a', b'e', b's', b'u', b'\x90'])
    if k == 16: return rng.choice([b'0', b'1', b'2'])
    if k == 17: return rng.choice([b'\x94', b'q' + bytes([rng.randrange(4)]), b'r' + u32(rng.randrange(4))])
    if k == 18: return rng.choice([b'h' + bytes([rng.randrange(4)]), b'j' + u32(rng.choice([0, 1, 2, 300, 2**32 - 1]))])
    if k == 19: return rng.choice([b'g', b'p']) + rng.choice([numtxt(rng), b'0', b'1', b'2', b'-1']) + b'\n'
    if k == 20: return rng.choice([b'\x88', b'\x89'])
    if k == 21:
        s = ''.join(rng.choice('abé€\U0001f600') for _ in range(rng.randrange(3))).encode()
        if rng.random() < 0.25:
            s += rng.choice([b'\xff', b'\xed\xa0\x80', b'\xc3', b'\xed\xbf\xbf', b'\xf4\x90\x80\x80', b'\xc0\x80'])
        return rng.choice([b'\x8c' + bytes([len(s)]) + s, b'X' + u32(len(s)) + s, b'\x8d' + u64(len(s)) + s])
    if k == 22:
        d = bytes(rng.randrange(256) for _ in range(rng.randrange(3)))
        return rng.choice([b'C' + bytes([len(d)]) + d, b'B' + u32(len(d)) + d, b'\x8e' + u64(len(d)) + d,
                           b'\x96' + u64(len(d)) + d])
    if k == 23:
        return b'V' + rng.choice([b'a', b'\\u00e9', b'\\x', b'\\', b'\\U0001f600', b'\\u12', b'', b'\\\\u0041',
                                  b'\\U00110000', b'\\uzzzz', b'\xe9', b'\\u00']) + b'\n'
    if k == 24:
        return b'S' + rng.choice([b"'a'", b'"b"', b"'\\x41'", b"'", b"a", b"''", b"'\\'", b"'\\x4'", b"'\\101\\0'",
                                  b"'\\777'", b"'\\q'", b"'\\n\\t'", b"'\\x80'", b"'\xe9'", b'"\'']) + b'\n'
    if k == 25:
        d = bytes(rng.randrange(256) if rng.random() < 0.2 else rng.randrange(128) for _ in range(rng.randrange(3)))
        return rng.choice([b'U' + bytes([len(d)]) + d, b'T' + i32(rng.choice([len(d), len(d), -1])) + d])
    if k == 26: return b'\x80' + bytes([rng.choice([0, 1, 2, 3, 4, 5, 6, 255])])
    if k == 27:  # declared lengths past the end of the data
        return rng.choice([b'C\x05ab', b'X\x09\x00\x00\x00ab', b'\x8d\xff\xff\xff\xff\xff\xff\xff\x7f',
                           b'\x8d\x00\x00\x00\x00\x00\x00\x00\x80', b'\x8e\x00\x00\x00\x00\x00\x00\x00\x80',
                           b'\x96\x00\x00\x00\x00\x00\x00\x00\x80', b'\x96\x03\x00\x00\x00\x00\x00\x00\x00ab',
                           b'\x8a\x05ab', b'T\x05\x00\x00\x00ab', b'U\x04a'])
    if k == 28: return bytes([rng.choice([0x00, 0x03, 0x2f, 0x7e, 0xa0, 0xff, 0x27, 0x5c])])  # bad keys
    if k == 29:  # declared lengths far past the data, and not past sys.maxsize
        n = rng.choice([2**20 - 1, 2**20, 2**20 + 1, 2**31, 2**32 - 1, 2**40, 2**63 - 1])
        return rng.choice([b'B' + u32(min(n, 2**32 - 1)), b'\x8e' + u64(n), b'\x96' + u64(n)]) + b'ab'
    return rng.choice([b'N', b'K\x01', b']', b'(', b'K\x02', b'}', b'\x8f', b'N', b'.'])


MEMO_SMALL = [0, 1, 2, 3, 5, 31, 32, 33, 40, 62, 63, 64, 65, 100, 128, 200, 255]
MEMO_BIG = [256, 1000, 65536, 2**20, 2**31 - 1, 2**31, 2**32 - 1]


def memo_index(rng):
    return rng.choice(MEMO_SMALL) if rng.random() < 0.85 else rng.choice(MEMO_BIG)


def memo_put(rng, i):
    forms = [b'r' + u32(i), b'p' + str(i).encode() + b'\n']
    if i < 256:
        forms.append(b'q' + bytes([i]))
    return rng.choice(forms)


def memo_get(rng, i):
    forms = [b'j' + u32(i), b'g' + str(i).encode() + b'\n']
    if i < 256:
        forms.append(b'h' + bytes([i]))
    return rng.choice(forms)


def memo_stream(rng):
    """Puts, gets and MEMOIZE around `_Unpickler_MemoPut`'s array and dict.

    A dense prefix grows `memo_len`, so a later key can resize the array over keys
    that went to the dict, which `_Unpickler_MemoGet` then moves into the array."""
    s = b'N'
    if rng.random() < 0.5:
        for j in range(rng.choice([1, 5, 16, 20, 30, 31, 32, 33, 40, 64, 70])):
            s += b'K' + bytes([j & 255]) + memo_put(rng, j) + b'0'
    for _ in range(rng.randrange(1, 16)):
        k = rng.randrange(8)
        if k < 2:
            s += rng.choice([b'N', b'K' + bytes([rng.randrange(256)]), b']', b'\x88'])
        elif k < 4:
            s += memo_put(rng, memo_index(rng))
        elif k == 4:
            s += b'\x94'
        elif k < 7:
            s += memo_get(rng, memo_index(rng))
        else:
            s += b'0'
    return s + b'.'


def chunk_stream(rng):
    """A counted payload around the 1 MiB chunk size, with a frame ending inside it."""
    K = 1 << 20
    size = rng.choice([K - 1, K, K + 1, 2 * K - 1, 2 * K, 2 * K + 1, 3 * K])
    head = rng.choice([b'B' + u32(size), b'\x8e' + u64(size), b'\x96' + u64(size)])
    have = rng.choice([size, size, size, size - 1, K, K - 1, K + 1, 0])
    have = min(have, size)
    if rng.random() < 0.7:
        cut = min(rng.choice([K, K, 2 * K, K - 1, K + 1, have]), have)
        return b'\x95' + u64(len(head) + cut) + head + bytes(cut) + bytes(have - cut) + b'.'
    return head + bytes(have) + b'.'


def hand_stream(rng):
    r = rng.random()
    if r < 0.12:
        return memo_stream(rng)
    if r < 0.1205:
        return chunk_stream(rng)
    s = b''.join(hand_op(rng) for _ in range(rng.randrange(0, 10)))
    r = rng.random()
    if r < 0.65:
        s += b'.'
    elif r < 0.8 and s:
        s = s[:rng.randrange(len(s))]
    if rng.random() < 0.2:
        cut = rng.randrange(len(s) + 1)
        head, body = s[:cut], s[cut:]
        n = len(body) + rng.choice([0, 0, 0, -1, -2, 1, 5])
        if rng.random() < 0.1:
            n = rng.choice([2**63, 2**64 - 1])
        frame = b'\x95' + u64(max(n, 0))
        if rng.random() < 0.3:  # a second frame inside the first
            k = rng.randrange(len(body) + 1)
            body = body[:k] + b'\x95' + u64(max(0, len(body) - k + rng.choice([0, 1, -1]))) + body[k:]
        s = head + frame + body
    if rng.random() < 0.1:
        s = b'\x80' + bytes([rng.choice([2, 3, 4, 5])]) + s
    return s


# Opcodes the scanner allows, with their argument shape.
# ('n', k): k fixed bytes; 'line'; ('count', k, signed): k-byte length then data;
# 'frame': 8-byte size, the frame body is parsed as opcodes.
ARGS = {}
for _c in b'(N.012)]}tldesau\x8f\x90\x91\x85\x86\x87\x88\x89\x94':
    ARGS[_c] = ('n', 0)
ARGS.update({ord('K'): ('n', 1), ord('M'): ('n', 2), ord('J'): ('n', 4), ord('h'): ('n', 1),
             ord('j'): ('n', 4), ord('q'): ('n', 1), ord('r'): ('n', 4), 0x80: ('n', 1),
             ord('I'): 'line', ord('L'): 'line', ord('g'): 'line', ord('p'): 'line',
             ord('V'): 'line', ord('S'): 'line',
             0x8a: ('count', 1, False), 0x8b: ('count', 4, True), ord('C'): ('count', 1, False),
             ord('B'): ('count', 4, False), 0x8e: ('count', 8, False), 0x96: ('count', 8, False),
             0x8c: ('count', 1, False), ord('X'): ('count', 4, False), 0x8d: ('count', 8, False),
             ord('U'): ('count', 1, False), ord('T'): ('count', 4, True), 0x95: 'frame'})
BAD_KEYS = {0x00, 0x03, 0x2f, 0x7e, 0xa0, 0xff, 0x27, 0x5c}  # unused opcode bytes (invalid load key)


def safe_stream(s):
    """True if no code-running opcode can execute."""
    pos = 0
    while pos < len(s):
        op = s[pos]
        pos += 1
        if op in BAD_KEYS:
            return True  # both unpicklers stop here
        if op not in ARGS:
            return False
        if op == ord('.'):
            return True
        a = ARGS[op]
        if a == 'line':
            nl = s.find(b'\n', pos)
            if nl < 0:
                return True
            pos = nl + 1
        elif a == 'frame':
            if pos + 8 > len(s):
                return True
            pos += 8
        elif a[0] == 'n':
            pos += a[1]
        else:
            k, signed = a[1], a[2]
            if pos + k > len(s):
                return True
            n = int.from_bytes(s[pos:pos + k], 'little', signed=signed)
            pos += k
            if n < 0:
                return True
            if n > SSIZE_MAX:
                return True
            pos += n
    return True


# ---------------------------------------------------------------- cases

COUNTER = [0]


class NoTell:
    """A file without `tell`: `_genops` reports no positions."""

    def __init__(self, data):
        self.f = io.BytesIO(data)

    def read(self, n):
        return self.f.read(n)

    def readline(self):
        return self.f.readline()


STRING_OPS = {'STRING', 'BINSTRING', 'SHORT_BINSTRING'}
STACK_OBJECTS = {o.name: o for op in pickletools.opcodes for o in op.stack_before + op.stack_after}
BAD_KEY_BYTES = [bytes([b]) for b in sorted(BAD_KEYS)]
PLAIN_OPS = b'()0212.Nabdeltu}]\x85\x86\x87\x88\x89\x8f\x90\x91\x93\x94\x97\x98Rbo\x81\x92Qs'
MARK_OPS = b'(((000\x85\x862t1ae\x94'


def tool_op(rng):
    """One opcode with an edge-case argument, for the branches of the readers and of `dis`."""
    line = rng.choice([b'', b'0', b'1', b'00', b'01', b'-1', b' 1', b'+5', b'1_0', b'12', b'5L', b'L',
                       b'x', b'\\', b'a\\', b'\\x41', b'\\x4', b'\\n', b'\xff', b'\xc3\xa9', b"'", b'"',
                       b"''", b'""', b"'a'", b'"a"', b"'a\"", b"\"a'", b"'\\''", b'9' * 30, b'1' * 4301])
    count = rng.choice([0, 1, 2, 3, 255, 256, 2**31 - 1, 2**32 - 1, 2**63 - 1, 2**63, 2**64 - 1])
    i32_count = rng.choice([0, 1, 2, -1, -2**31, 2**31 - 1])
    tail = bytes(rng.choice(b'ab\xc3\xa9\xed\xa0\x80\x00\n') for _ in range(rng.randrange(5)))
    return rng.choice([
        lambda: b'I' + line + b'\n', lambda: b'L' + line + b'\n', lambda: b'S' + line + b'\n',
        lambda: b'V' + line + b'\n', lambda: b'p' + line + b'\n', lambda: b'g' + line + b'\n',
        lambda: b'P' + line + b'\n', lambda: b'c' + line + b'\n' + line + b'\n',
        lambda: b'i' + line + b'\n' + line + b'\n',
        lambda: b'S' + line, lambda: b'I' + line,
        lambda: b'J' + i32(i32_count), lambda: b'K' + bytes([count & 255]), lambda: b'M' + bytes([count & 255, 1]),
        lambda: b'T' + i32(i32_count) + tail, lambda: b'U' + bytes([rng.randrange(6)]) + tail,
        lambda: b'\x8a' + bytes([rng.randrange(6)]) + tail, lambda: b'\x8b' + i32(i32_count) + tail,
        lambda: b'B' + u32(min(count, 2**32 - 1)) + tail, lambda: b'C' + bytes([rng.randrange(6)]) + tail,
        lambda: b'X' + u32(min(count, 2**32 - 1)) + tail, lambda: b'\x8c' + bytes([rng.randrange(6)]) + tail,
        lambda: b'\x8d' + u64(count) + tail, lambda: b'\x8e' + u64(count) + tail,
        lambda: b'\x96' + u64(count) + tail, lambda: b'\x95' + u64(count),
        lambda: b'q' + bytes([rng.randrange(4)]), lambda: b'r' + u32(rng.choice([0, 1, 2, 2**32 - 1])),
        lambda: b'h' + bytes([rng.randrange(4)]), lambda: b'j' + u32(rng.choice([0, 1, 2, 2**32 - 1])),
        lambda: b'\x80' + bytes([rng.choice([0, 1, 2, 3, 4, 5, 6, 255])]), lambda: b'\x82' + bytes([count & 255]),
        lambda: b'\x83' + bytes([1, 2]), lambda: b'\x84' + i32(i32_count), lambda: b'G' + bytes(8),
        lambda: bytes([rng.choice(PLAIN_OPS)]),
        lambda: bytes([rng.choice(MARK_OPS)]),
        lambda: rng.choice(BAD_KEY_BYTES),
    ])()


def tool_stream(rng):
    k = rng.random()
    if k < 0.35:
        try:
            s = rng.choice([pickle.dumps, pickle._dumps])(ValueGen(rng).value(), rng.randrange(6))
        except Exception:
            s = b'N.'
    elif k < 0.55:
        s = hand_stream(rng)
    elif k < 0.92:
        s = b''.join(tool_op(rng) for _ in range(rng.randrange(9)))
        if rng.random() < 0.8:
            s += b'.'
    else:
        s = bytes(rng.randrange(256) for _ in range(rng.randrange(24)))
    if s and rng.random() < 0.3:
        b = bytearray(s)
        m = rng.random()
        i = rng.randrange(len(b))
        if m < 0.5:
            b[i] = rng.randrange(256)
        elif m < 0.8:
            del b[i:]
        else:
            b[i:i] = tool_op(rng)
        s = bytes(b)
    return s


def dis_renders(s):
    try:
        for op, arg, _ in pickletools.genops(s):
            if isinstance(arg, float):
                return False
            if isinstance(arg, str) and op.name not in STRING_OPS and any(ord(c) > 0xff for c in arg):
                return False
    except Exception:
        pass
    return True


def tool_case(rng):
    s = tool_stream(rng)
    if 0x46 in s:
        return None
    c = {"mod": "pickle", "data": list(s), "tell": rng.random() < 0.85}
    r = rng.random()
    if r < 0.35:
        return {**c, "fn": "genops"}
    if r < 0.6:
        return {**c, "fn": "optimize"}
    if not dis_renders(s):
        return None
    memo = [[rng.choice([0, 1, 2, 5]), rng.choice(['any', 'int', 'list'])] for _ in range(rng.choice([0, 0, 0, 1, 2]))]
    return {**c, "fn": "dis", "indent": rng.choice([4, 4, 0, 1, 7]), "annotate": rng.choice([0, 0, 1, 20, 40, 60]),
            "memo": memo, "color": rng.random() < 0.25}


def run_tool(c):
    data = bytes(c["data"])
    src = data if c["tell"] else NoTell(data)
    if c["fn"] == "genops":
        def enc(a):
            if a is None:
                return None
            if isinstance(a, bool):
                return {"t": "bool", "v": a}
            if isinstance(a, int):
                return {"t": "int", "v": hex(a)}
            if isinstance(a, bytes):
                return {"t": "bytes", "v": list(a)}
            if isinstance(a, bytearray):
                return {"t": "bytearray", "v": list(a)}
            if isinstance(a, str):
                return {"t": "str", "v": [ord(x) for x in a]}
            return {"t": "float", "v": list(struct.pack('>d', a))}

        def walk():
            ops = list(pickletools._genops(src, yield_end_pos=True))
            public = list(pickletools.genops(NoTell(data) if not c["tell"] else data))
            assert [o[:3] for o in ops] == public
            return [[o.name, enc(a), p, e] for o, a, p, e in ops]
        return common.py_result(walk)
    if c["fn"] == "optimize":
        return common.py_result(lambda: list(pickletools.optimize(data)))
    out = io.StringIO()
    memo = {k: STACK_OBJECTS[n] for k, n in c["memo"]}
    # With colour, `dis` measures each line through `decolor`. The model has no
    # theme, so its text is compared with the output once the colours are removed.
    plain = pickletools.get_theme
    if c["color"]:
        pickletools.get_theme = lambda **kw: plain(force_color=True)
    try:
        try:
            pickletools.dis(src, out=out, memo=memo, indentlevel=c["indent"], annotate=c["annotate"])
        finally:
            pickletools.get_theme = plain
    except Exception as e:
        return {"exc": type(e).__name__, "msg": _colorize.decolor(out.getvalue()) + "\x00" + str(e)}
    return {"ok": _colorize.decolor(out.getvalue())}


# ---------------------------------------------------------------- recursion limits and arguments
# (lean/PyLean/Pickle/EncRec.lean)

def frame_depth():
    """The depth of the caller's frame."""
    f = sys._getframe(1)
    n = 0
    while f is not None:
        n += 1
        f = f.f_back
    return n


PROTO_ARGS = [None, 0, 1, 2, 3, 4, 5, -1, 6, True, False, -2**63 - 1, 2.5, 0.5, 0.0, -0.0, 1.0, 4.999,
              5.0, 5.5, -1.5, float('nan'), float('inf'), float('-inf'), 3.0, 2.9999999, 1e300, "2", b"3"]


def enc_proto(p):
    if p is None:
        return {"k": "none"}
    if type(p) in (int, bool):
        return {"k": "int", "v": hex(int(p))}
    if type(p) is float:
        return {"k": "float", "bits": struct.unpack('<Q', struct.pack('<d', p))[0]}
    return {"k": "other", "t": type(p).__name__}


def nested(rng):
    """A value nested k deep, with sharing, to drive both recursion limits."""
    v = rng.choice([None, 1, 2**40, -2**40, 'a', 'x' * 300, b'xy', b'', bytearray(b'z'), bytearray(),
                    set(), {1, 2}, frozenset({1}), (), []])
    for _ in range(rng.randrange(0, 14)):
        v = rng.choice([lambda v: [v], lambda v: (v,), lambda v: (v, v), lambda v: {1: v},
                        lambda v: [v, v], lambda v: (1, 2, 3, v), lambda v: {'k': v, 2: None},
                        lambda v: frozenset([(v,)]) if _hashable(v) else [v],
                        lambda v: {v} if _hashable(v) else (v,)])(v)
    return v


def rec_case(rng):
    impl = rng.choice(["c", "py"])
    x = nested(rng) if rng.random() < 0.6 else ValueGen(rng).value()
    COUNTER[0] += 1
    OBJS[COUNTER[0]] = x
    p = rng.choice(PROTO_ARGS) if rng.random() < 0.5 else rng.choice([None, 0, 1, 2, 3, 4, 5])
    PROTOS[COUNTER[0]] = p
    frames = rng.choice([rng.randrange(1, 80), rng.randrange(1, 30), 1000])
    return {"mod": "pickle", "fn": "dumpsr", "impl": impl, "proto": enc_proto(p),
            "bufcb": rng.random() < 0.25, "frames": frames, "val": encode_value(x), "key": COUNTER[0]}


PROTOS = {}


def run_py_frames(x, proto, cb, frames):
    # The codecs are looked up at import (below), so this measures the interpreter whose
    # raw-unicode-escape codec is cached, the scope of EncRec.lean. On a fresh interpreter the
    # first protocol 0 str costs about 9 more frames (encodings.search_function, importlib),
    # which the model does not have.
    d = frame_depth()
    old = sys.getrecursionlimit()
    # this frame is at depth d: `frames` are left where pickle._dumps is called
    sys.setrecursionlimit(d + frames)
    try:
        r = pickle._dumps(x, proto, buffer_callback=cb)
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}
    finally:
        sys.setrecursionlimit(old)
    return {"ok": list(r)}


def gen_case(rng):
    if rng.random() < 0.3:
        return rec_case(rng)
    if rng.random() < 0.35:
        return tool_case(rng)
    k = rng.random()
    impl = rng.choice(["c", "py"])
    if k < 0.45:
        s = hand_stream(rng)
        if not safe_stream(s):
            return None
        return {"mod": "pickle", "fn": "loads", "impl": impl, "data": list(s)}
    x = ValueGen(rng).value()
    COUNTER[0] += 1
    OBJS[COUNTER[0]] = x
    proto = rng.choice([0, 1, 2, 3, 4, 5, 0, 1, 2, 3, 4, 5, -1, 6, -2**63 - 1, 2**63, -2**63])
    if k < 0.75:
        return {"mod": "pickle", "fn": "dumps", "impl": impl, "proto": proto, "val": encode_value(x),
                "key": COUNTER[0]}
    if proto > 5 or proto < -1:
        proto = rng.randrange(6)
    return {"mod": "pickle", "fn": "roundtrip", "enc": impl, "dec": rng.choice(["c", "py"]),
            "proto": proto, "val": encode_value(x), "key": COUNTER[0]}


class ImportBlocked(Exception):
    pass


# Codec lookups import `encodings.*` on first use; do that before imports are blocked.
for _enc in ("ascii", "latin-1", "utf-8", "raw-unicode-escape"):
    codecs.lookup(_enc)


def no_import(*a, **k):
    raise ImportBlocked(a[0] if a else '?')


def run_python(c):
    fn = c["fn"]
    if fn in ("genops", "optimize", "dis"):
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")  # invalid escapes in read_stringnl
            return run_tool(c)
    if fn == "loads":
        f = pickle.loads if c["impl"] == "c" else pickle._loads
        data = bytes(c["data"])
        saved = builtins.__import__
        with warnings.catch_warnings():
            # STRING escapes like '\\q' warn; showing a warning imports modules.
            warnings.simplefilter("ignore")
            builtins.__import__ = no_import
            try:
                r = common.py_result(lambda: decoded(f(data)))
            finally:
                builtins.__import__ = saved
        assert r.get("exc") != "ImportBlocked", c
        return r
    x = OBJS[c["key"]]
    if fn == "dumpsr":
        proto = PROTOS[c["key"]]
        cb = (lambda b: None) if c["bufcb"] else None
        if c["impl"] == "c":
            return common.py_result(lambda: list(pickle.dumps(x, proto, buffer_callback=cb)))
        return run_py_frames(x, proto, cb, c["frames"])
    if fn == "dumps":
        f = pickle.dumps if c["impl"] == "c" else pickle._dumps
        return common.py_result(lambda: list(f(x, c["proto"])))
    enc = pickle.dumps if c["enc"] == "c" else pickle._dumps
    dec = pickle.loads if c["dec"] == "c" else pickle._loads
    return common.py_result(lambda: decoded(dec(enc(x, c["proto"]))))


if __name__ == "__main__":
    common.main(gen_case, run_python)
