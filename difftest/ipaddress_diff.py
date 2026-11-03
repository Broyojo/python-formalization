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


def gen_mask(rng):
    k = rng.random()
    if k < 0.3:
        p = rng.randint(0, 40)
        return rng.choice(["", "0", "00"]) + str(p) if rng.random() < 0.2 else str(p)
    if k < 0.75:
        p = rng.randint(0, 32)
        m = ((1 << 32) - 1) ^ (((1 << 32) - 1) >> p)
        if rng.random() < 0.5:
            m ^= (1 << 32) - 1
        if rng.random() < 0.2:
            m ^= 1 << rng.randrange(32)
        return str(ipaddress.IPv4Address(m))
    if k < 0.9:
        return str(ipaddress.IPv4Address(rng.randrange(1 << 32)))
    return rng.choice([" 24", "24 ", "+24", "-1", "", "\u0662\u0664", "1.2.3", "255.255.255.0.0",
                       "0x18", "1e1", "255.255.255.00", "'", "24\n"])


V6_TOKS = ["0", "1", "ffff", "FFFF", "0000", "00000", "12345", "abcd", "g", "", "db8", "001",
           "1.2.3.4", "01.2.3.4", "255.255.255.255", "1.2.3", "300.1.1.1", " 1", "a.b"]


def gen_v6(rng):
    k = rng.random()
    if k < 0.35:
        n = rng.choice([0, 1, 2**128 - 1, 0xffff00000000 | rng.randrange(2**32), rng.randrange(2**128),
                        rng.randrange(2**16) << (16 * rng.randrange(8)),
                        int("".join(rng.choice(["0000", "%04x" % rng.randrange(65536)]) for _ in range(8)), 16)])
        s = str(ipaddress.IPv6Address(n))
        if rng.random() < 0.3:
            s = ipaddress.IPv6Address(n).exploded
        if rng.random() < 0.2:
            s = s.upper()
    else:
        parts = [rng.choice(V6_TOKS) for _ in range(rng.randint(1, 11))]
        s = ":".join(parts)
        if rng.random() < 0.3:
            s = s.replace(":", "::", 1)
    if rng.random() < 0.15:
        s += "%" + rng.choice(["eth0", "1", "", "a%b", "x y"])
    if rng.random() < 0.03:
        s = rng.choice(["", "::/1", "1" * 46, "1:" * 60, "%", "::%"])
    return s


def gen_operand(rng, bits):
    """An address, a network of either version, or an object without `version`."""
    k = rng.random()
    if k < 0.15:
        return {"k": "other", "ty": rng.choice(["int", "NoneType"])}
    b = bits if rng.random() < 0.75 else (160 - bits)
    if k < 0.5:
        return {"k": "addr", "bits": b, "ip": edge_addr(rng, b)}
    return {"k": "net", "bits": b, "net": list(rand_net(rng, b))}


HEX_CHARS = "0123456789abcdefABCDEF"


def gen_hextet(rng):
    k = rng.random()
    if k < 0.6:
        return "".join(rng.choice(HEX_CHARS) for _ in range(rng.randint(1, 4)))
    if k < 0.75:
        return "".join(rng.choice(HEX_CHARS) for _ in range(rng.randint(5, 7)))
    return rng.choice(["", "g", "0x1", " 1", "1 ", "\u0661", "+1", "-1", "1.2", "'", "%"])


def gen_v6_spelling(rng):
    """Uncompressed, compressed or dotted-quad spellings in mixed case with leading zeros."""
    k = rng.random()
    n = rng.choice([rng.randrange(2**128), 0, 2**128 - 1, rng.randrange(2**16) << (16 * rng.randrange(8))])
    groups = ["%x" % ((n >> (16 * (7 - i))) & 0xffff) for i in range(8)]
    groups = [g.zfill(rng.randint(len(g), 4)) for g in groups]
    groups = [g.upper() if rng.random() < 0.3 else g for g in groups]
    if k < 0.4:
        return ":".join(groups)
    if k < 0.7:
        i = rng.randrange(8)
        j = rng.randrange(i, 9)
        return ":".join(groups[:i]) + "::" + ":".join(groups[j:])
    q = ".".join(str(rng.randrange(256)) for _ in range(4))
    if k < 0.85:
        return ":".join(groups[:6]) + ":" + q
    i = rng.randrange(7)
    return ":".join(groups[:i]) + "::" + ":".join(groups[i:6]) + (":" if i < 6 else "") + q


def gen_addr_arg(rng, bits):
    k = rng.random()
    if k < 0.6:
        return ["str", gen_v6(rng) if rng.random() < 0.6 else gen_v6_spelling(rng)]
    if k < 0.8:
        top = (1 << bits) - 1
        return ["int", rng.choice([-1, 0, top, top + 1, -(2**200), 2**200, rng.randrange(top + 1)])]
    return ["bytes", [rng.randrange(256) for _ in range(rng.choice([16, 16, 15, 17, 4, 0, 1]))]]


def gen_mask_arg(rng, bits):
    if rng.random() < 0.3:
        return ["int", rng.choice([-1, 0, 1, bits - 1, bits, bits + 1, 2**64, rng.randint(-5, bits + 5)])]
    k = rng.random()
    if bits == 32 and k < 0.5:
        return ["str", gen_mask(rng)]
    p = rng.randint(0, bits + 3)
    return ["str", rng.choice([str(p), "0" + str(p), "00" + str(p), " " + str(p), str(p) + "\n", "+" + str(p),
                               "", "\u0661\u0662", "1e1", "0x10", "0" * 5000, "0" * 4300, "0" * 4299 + "1",
                               "255.255.255.0", "ffff::"])]


def gen_case(rng):
    if rng.random() < 0.15:
        if rng.random() < 0.5:
            return {"mod": "ipaddress", "fn": "v6init", "bits": 128, "arg": ["str", gen_v6(rng)]}
        return {"mod": "ipaddress", "fn": "v6init", "bits": 128, "arg": gen_addr_arg(rng, 128)}
    if rng.random() < 0.12:
        fn = rng.choice(["mask", "prefix_from_ip_int", "string_from_ip_int", "mapped_to_str", "v6_ip_int",
                         "parse_hextet", "parse_octet"])
        bits = rng.choice([32, 128])
        c = {"mod": "ipaddress", "fn": fn, "bits": bits}
        if fn == "mask":
            c["arg"] = gen_mask_arg(rng, bits)
        elif fn == "prefix_from_ip_int":
            p = rng.randint(0, bits)
            m = ((1 << bits) - 1) ^ (((1 << bits) - 1) >> p)
            c["n"] = rng.choice([m, m ^ ((1 << bits) - 1), m ^ (1 << rng.randrange(bits)), rng.randrange(1 << bits),
                                 0, (1 << bits) - 1])
        elif fn == "string_from_ip_int":
            c["n"] = rng.choice([None, 2**128, 2**128 - 1, 2**200, edge_addr(rng, 128)])
        elif fn == "mapped_to_str":
            c["ip"] = rng.choice([0xffff00000000 | rng.randrange(1 << 32), edge_addr(rng, 128), 0xffff00000000])
        elif fn == "v6_ip_int":
            c["s"] = gen_v6(rng).split("%")[0] if rng.random() < 0.5 else gen_v6_spelling(rng)
        elif fn == "parse_hextet":
            c["s"] = gen_hextet(rng)
        else:
            c["s"] = rng.choice(V4_PIECES + [str(rng.randrange(1000)), "0" * rng.randint(1, 5)])
        return c
    if rng.random() < 0.1:
        return {"mod": "ipaddress", "fn": "mask4", "bits": 32, "s": gen_mask(rng)}
    if rng.random() < 0.3:
        return {"mod": "ipaddress", "fn": "v4init", "bits": 32, "arg": gen_v4(rng)}
    if rng.random() < 0.15:
        bits = rng.choice([32, 128])
        p = bits - rng.choice([0, 0, 1, 1, 2, 3, 4, 7, 10])
        a = edge_addr(rng, bits) & (((1 << bits) - 1) ^ ((1 << (bits - p)) - 1))
        return {"mod": "ipaddress", "fn": "hosts", "bits": bits, "net": [a, p]}
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
        first = {"k": "addr", "bits": bits, "ip": a}
        last = {"k": "addr", "bits": bits, "ip": b}
        if rng.random() < 0.15:
            first = gen_operand(rng, bits)
        if rng.random() < 0.15:
            last = gen_operand(rng, bits)
        c.update(first=first, last=last)
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
        other = {"k": "addr", "bits": bits, "ip": edge_addr(rng, bits)}
        if rng.random() < 0.3:
            other = gen_operand(rng, bits)
        c.update(net=rand_net(rng, bits), other=other)
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
        other = {"k": "net", "bits": bits, "net": list(b)}
        if rng.random() < 0.25:
            other = gen_operand(rng, bits)
        if fn == "address_exclude" and other["k"] == "net" and other["net"][1] - a[1] > 12 and \
                other["bits"] == bits:
            return None
        c.update(a=a, other=other)
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


def make_operand(o):
    if o["k"] == "addr":
        return ADDR[o["bits"]](o["ip"])
    if o["k"] == "net":
        return NET[o["bits"]](tuple(o["net"]))
    return {"int": 5, "NoneType": None}[o["ty"]]


def make_arg(arg):
    kind, val = arg
    return bytes(val) if kind == "bytes" else val


def run_python(c):
    bits = c["bits"]
    Net = NET[bits]
    mk = lambda t: Net(tuple(t))
    try:
        fn = c["fn"]
        if fn == "v6init":
            a = ipaddress.IPv6Address(make_arg(c["arg"]))
            return {"ok": [a._ip, a.scope_id, str(a)]}
        if fn == "mask4":
            return {"ok": ipaddress.IPv4Network._make_netmask(c["s"])[1]}
        if fn == "mask":
            return {"ok": NET[bits]._make_netmask(c["arg"][1])[1]}
        if fn == "prefix_from_ip_int":
            return {"ok": NET[bits]._prefix_from_ip_int(c["n"])}
        if fn == "string_from_ip_int":
            if c["n"] is None:
                return {"ok": ipaddress.IPv6Address._string_from_ip_int()}
            return {"ok": ipaddress.IPv6Address._string_from_ip_int(c["n"])}
        if fn == "mapped_to_str":
            return {"ok": ipaddress.IPv6Address(c["ip"])._ipv4_mapped_ipv6_to_str()}
        if fn == "v6_ip_int":
            return {"ok": ipaddress.IPv6Address._ip_int_from_string(c["s"])}
        if fn == "parse_hextet":
            return {"ok": ipaddress.IPv6Address._parse_hextet(c["s"])}
        if fn == "parse_octet":
            return {"ok": ipaddress.IPv4Address._parse_octet(c["s"])}
        if fn == "hosts":
            net = NET[bits](tuple(c["net"]))
            return {"ok": [[int(x) for x in net], [int(x) for x in net.hosts()], net.num_addresses]}
        if fn == "v4init":
            a = ipaddress.IPv4Address(make_arg(c["arg"]))
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
                make_operand(c["first"]), make_operand(c["last"]))]
        elif fn == "mknet":
            v = enc_net(Net((c["addr"], c["prefixlen"])))
        elif fn == "subnets":
            v = [enc_net(n) for n in mk(c["net"]).subnets(c["diff"], c["new_prefix"])]
        elif fn == "supernet":
            v = enc_net(mk(c["net"]).supernet(c["diff"], c["new_prefix"]))
        elif fn == "getitem":
            v = int(mk(c["net"])[c["i"]])
        elif fn == "contains":
            v = make_operand(c["other"]) in mk(c["net"])
        elif fn == "overlaps":
            v = mk(c["a"]).overlaps(make_operand(c["other"]))
        elif fn == "subnet_of":
            v = mk(c["a"]).subnet_of(make_operand(c["other"]))
        elif fn == "address_exclude":
            v = [enc_net(n) for n in mk(c["a"]).address_exclude(make_operand(c["other"]))]
        return {"ok": v}
    except Exception as e:
        return {"exc": type(e).__name__, "msg": str(e)}


if __name__ == "__main__":
    common.main(gen_case, run_python)
