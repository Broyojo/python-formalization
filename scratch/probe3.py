import io, struct, datetime as dt, warnings, sys, tempfile, os, weakref
warnings.simplefilter('ignore')
from test.support import import_helper
Cz = import_helper.import_fresh_module('zoneinfo')
Pz = import_helper.import_fresh_module('zoneinfo', blocked=['_zoneinfo'])


def tzif(trans, idx, types, abbr, footer=b''):
    v1 = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, 0, 0, 0)
    h = b'TZif2' + bytes(15) + struct.pack('>6l', 0, 0, 0, len(trans), len(types), len(abbr))
    body = b''.join(struct.pack('>q', t) for t in trans) + bytes(idx)
    body += b''.join(struct.pack('>lBB', *t) for t in types) + abbr
    return v1 + h + body + b'\n' + footer + b'\n'


def both(data, f):
    out = []
    for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
        try:
            out.append(f(Z.from_file(io.BytesIO(data), key='k')))
        except Exception as e:
            out.append(type(e).__name__ + str(e))
    return out


class Big(dt.datetime):
    def toordinal(self):
        return super().toordinal() + 2**32


data = tzif([2**40], [1], [(0, 0, 0), (25200, 0, 2)], b'A\x00B\x00')
print("sub-toordinal", both(data, lambda z: z.utcoffset(Big(2021, 1, 1))))


class F(dt.datetime):
    @property
    def fold(self):
        return 1


T = 1005782400
data2 = tzif([T], [1], [(10800, 0, 0), (7200, 0, 4)], b'AAA\x00BBB\x00')
print("sub-fold", both(data2, lambda z: (z.utcoffset(F(2001, 11, 15, 2, 30)),
                                         z.utcoffset(dt.datetime(2001, 11, 15, 2, 30, fold=1)))))
data3 = tzif([0, 1000], [1, 2], [(0, 0, 0), (3600, 0, 4), (7200, 0, 8)], b'AAA\x00BBB\x00CCC\x00', b'XXX0')


def f3(z):
    u = dt.datetime(2000, 1, 1, tzinfo=z)
    r = z.fromutc(u)
    return (r.replace(tzinfo=None) - u.replace(tzinfo=None), r.utcoffset())


print("fromutc-static", both(data3, f3))
T2 = tempfile.mkdtemp()
blob = b"TZif2" + bytes(15) + struct.pack(">6l", 0, 0, 0, 0, 1, 4) + struct.pack(">lBB", 0, 0, 0) + b"UTC\x00"
open(os.path.join(T2, "k"), "wb").write(blob + blob + b"\nUTC0\n")
for m in {id(x): x for x in (sys.modules.get('zoneinfo._tzpath'), Cz._tzpath, Pz._tzpath)}.values():
    m.reset_tzpath([T2])
for Z in (Cz.ZoneInfo, Pz.ZoneInfo):
    class S(Z):
        pass
    r = weakref.ref(S("k"))
    print("subclass cache", Z.__module__, r() is not None, type(S.__dict__.get('_weak_cache')).__name__,
          S._weak_cache is not Z._weak_cache)
