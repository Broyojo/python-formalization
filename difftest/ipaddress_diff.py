"""Differential test: Lean model of ipaddress vs. the running CPython.

Usage: python3 difftest/ipaddress_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py.
"""

import ipaddress
import warnings

import common

NET = {32: ipaddress.IPv4Network, 128: ipaddress.IPv6Network}
ADDR = {32: ipaddress.IPv4Address, 128: ipaddress.IPv6Address}
MAX_LIST = 1 << 12  # skip cases whose output would be larger than this


def edge_addr(rng, bits):
    top = (1 << bits) - 1
    k = rng.randrange(bits + 1)
    return rng.choice([
        0, 1, top, top - 1, 1 << k, (1 << k) - 1, min(top, (1 << k) + 1),
        rng.randrange(top + 1), rng.randrange(top + 1),
    ]) & top


def edge_prefix(rng, bits):
    return rng.choice([0, 1, bits - 1, bits, rng.randrange(bits + 1), rng.randrange(bits + 1)])


def rand_net(rng, bits):
    p = edge_prefix(rng, bits)
    mask = ((1 << bits) - 1) ^ (((1 << bits) - 1) >> p)
    return (edge_addr(rng, bits) & mask, p)


def edge_int(rng, lo, hi):
    return rng.choice([lo, hi, lo - 1, hi + 1, 0, 1, -1, rng.randint(lo, hi)])


V4_PIECES = ["0", "1", "9", "10", "99", "100", "199", "255", "256", "300", "999", "1000", "00", "01",
             "001", "010", "0x1", "-1", "+1", " 1", "1 ", "", "a", "\u0663", "\uff11", "1\n", "25\u0665",
             "2\u00b2", "'", "\\"]


def gen_v4(rng):
    k = rng.random()
    if k < 0.3:
        n = rng.choice([0, 1, 255, 256, 2**24, 2**32 - 1, rng.randrange(2**32)])
        return ["str", str(ipaddress.IPv4Address(n))]
    if k < 0.75:
        parts = [rng.choice(V4_PIECES) if rng.random() < 0.4 else str(rng.randrange(256))
                 for _ in range(rng.choice([4, 4, 4, 3, 5, 1, 0]))]
        s = ".".join(parts)
        if rng.random() < 0.05:
            s = s.replace(".", "/", 1)
        if rng.random() < 0.05:
            s = s + rng.choice(["\n", " ", ".", "%"])
        return ["str", s]
    if k < 0.88:
        return ["int", rng.choice([-1, 0, 2**32 - 1, 2**32, -(2**40), 2**64, rng.randrange(2**32)])]
    return ["bytes", [rng.randrange(256) for _ in range(rng.choice([4, 4, 3, 5, 0, 16]))]]


def gen_case(rng):
    if rng.random() < 0.3:
        return {"mod": "ipaddress", "fn": "v4init", "bits": 32, "arg": gen_v4(rng)}
    bits = rng.choice([32, 128])
    fn = rng.choice(["summarize", "mknet", "subnets", "supernet", "getitem",
                     "contains", "overlaps", "subnet_of", "address_exclude",
                     "exploded", "iface_unspecified", "getattr"])
    c = {"mod": "ipaddress", "fn": fn, "bits": bits}
    if fn == "exploded":
        ip = rng.choice([edge_addr(rng, 128), 0, 1, rand_net(rng, 128)[0],
                         0xffff00000000 | rng.randrange(1 << 32), 0xffff00000000])
        p = edge_prefix(rng, 128)
        kind = rng.choice(["address", "interface", "network"])
        if kind == "network":
            ip, p = rand_net(rng, 128) if rng.random() < 0.8 else ((0xffff00000000 | rng.randrange(1 << 32)), 128)
        c.update(bits=128, kind=kind, ip=ip, prefixlen=p,
                 scope=rng.choice([None, None, "eth0", "1", "a.b", "z"]))
    elif fn == "iface_unspecified":
        p = edge_prefix(rng, bits)
        c.update(ip=rng.choice([0, 0, edge_addr(rng, bits)]), prefixlen=p)
    elif fn == "getattr":
        c.update(name=rng.choice(["__version__", "__version__", "foo", "_nope", "__all__x"]))
    elif fn == "summarize":
        a, b = edge_addr(rng, bits), edge_addr(rng, bits)
        if rng.random() < 0.8:
            a, b = min(a, b), max(a, b)
        c.update(first=a, last=b)
    elif fn == "mknet":
        c.update(addr=edge_int(rng, 0, (1 << bits) - 1) if rng.random() < 0.3 else edge_addr(rng, bits),
                 prefixlen=edge_int(rng, 0, bits))
    elif fn in ("subnets", "supernet"):
        net = rand_net(rng, bits)
        c.update(net=net, diff=1 if rng.random() < 0.5 else edge_int(rng, -2, bits + 2),
                 new_prefix=None if rng.random() < 0.5 else edge_int(rng, 0, bits))
        if fn == "subnets":
            d = c["diff"] if c["new_prefix"] is None else c["new_prefix"] - net[1]
            if 0 <= d and net[1] + d <= bits and d > 12:
                return None
    elif fn == "getitem":
        net = rand_net(rng, bits)
        size = 1 << (bits - net[1])
        c.update(net=net, i=edge_int(rng, -size, size - 1))
    elif fn == "contains":
        c.update(net=rand_net(rng, bits), addr=edge_addr(rng, bits))
    else:
        a = rand_net(rng, bits)
        if fn == "address_exclude" and rng.random() < 0.8:
            # Pick b inside a, so the exclusion actually runs.
            q = rng.randint(a[1], bits)
            mask = ((1 << bits) - 1) ^ (((1 << bits) - 1) >> q)
            hostbits = (1 << (bits - a[1])) - 1
            b = ((a[0] | (edge_addr(rng, bits) & hostbits)) & mask, q)
        else:
            b = rand_net(rng, bits)
        c.update(a=a, b=b)
    return c


def enc_net(n):
    return [int(n.network_address), n.prefixlen]


def make_v6(c):
    text = str(ipaddress.IPv6Address(c["ip"]))
    if c["scope"]:
        text += "%" + c["scope"]
    if c["kind"] == "address":
        return ipaddress.IPv6Address(text)
    return {"interface": ipaddress.IPv6Interface, "network": ipaddress.IPv6Network}[c["kind"]](
        f"{text}/{c['prefixlen']}")


def module_attr(name):
    with warnings.catch_warnings():
        warnings.simplefilter("ignore", DeprecationWarning)
        return getattr(ipaddress, name)


def run_python(c):
    bits = c["bits"]
    Net = NET[bits]
    mk = lambda t: Net(tuple(t))
    try:
        fn = c["fn"]
        if fn == "v4init":
            kind, val = c["arg"]
            a = ipaddress.IPv4Address(bytes(val) if kind == "bytes" else val)
            v = [a._ip, str(a)]
        elif fn == "exploded":
            v = make_v6(c).exploded
        elif fn == "iface_unspecified":
            cls = {32: ipaddress.IPv4Interface, 128: ipaddress.IPv6Interface}[bits]
            v = cls((c["ip"], c["prefixlen"])).is_unspecified
        elif fn == "getattr":
            v = module_attr(c["name"])
        elif fn == "summarize":
            v = [enc_net(n) for n in ipaddress.summarize_address_range(
                ADDR[bits](c["first"]), ADDR[bits](c["last"]))]
        elif fn == "mknet":
            v = enc_net(Net((c["addr"], c["prefixlen"])))
        elif fn == "subnets":
            v = [enc_net(n) for n in mk(c["net"]).subnets(c["diff"], c["new_prefix"])]
        elif fn == "supernet":
            v = enc_net(mk(c["net"]).supernet(c["diff"], c["new_prefix"]))
        elif fn == "getitem":
            v = int(mk(c["net"])[c["i"]])
        elif fn == "contains":
            v = ADDR[bits](c["addr"]) in mk(c["net"])
        elif fn == "overlaps":
            v = mk(c["a"]).overlaps(mk(c["b"]))
        elif fn == "subnet_of":
            v = mk(c["a"]).subnet_of(mk(c["b"]))
        elif fn == "address_exclude":
            v = [enc_net(n) for n in mk(c["a"]).address_exclude(mk(c["b"]))]
        return {"ok": v}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


if __name__ == "__main__":
    common.main(gen_case, run_python)
