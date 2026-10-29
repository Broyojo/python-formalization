"""Differential test: Lean model of ipaddress vs. the running CPython.

Usage: python3 difftest/ipaddress_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. The model binary is lean/.lake/build/bin/pydiff.
"""

import argparse
import ipaddress
import json
import random
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PYDIFF = ROOT / "lean" / ".lake" / "build" / "bin" / "pydiff"

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


def gen_case(rng):
    bits = rng.choice([32, 128])
    fn = rng.choice(["summarize", "mknet", "subnets", "supernet", "getitem",
                     "contains", "overlaps", "subnet_of", "address_exclude"])
    c = {"fn": fn, "bits": bits}
    if fn == "summarize":
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


def run_python(c):
    bits = c["bits"]
    Net = NET[bits]
    mk = lambda t: Net(tuple(t))
    try:
        fn = c["fn"]
        if fn == "summarize":
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


def agree(py, lean):
    if "ok" in py or "ok" in lean:
        return py == lean
    if py["exc"] != lean.get("exc"):
        return False
    return lean["msg"].startswith("~") or py["msg"] == lean["msg"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", type=int, default=20000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    rng = random.Random(args.seed)

    cases = []
    while len(cases) < args.cases:
        c = gen_case(rng)
        if c is not None:
            cases.append(c)

    proc = subprocess.run([str(PYDIFF)], input="".join(json.dumps(c) + "\n" for c in cases),
                          capture_output=True, text=True, check=True)
    lean_out = [json.loads(line) for line in proc.stdout.splitlines()]
    assert len(lean_out) == len(cases), (len(lean_out), len(cases))

    mismatches, by_fn = 0, {}
    for c, lo in zip(cases, lean_out):
        if "harness_error" in lo:
            print("HARNESS", c, lo, file=sys.stderr)
            mismatches += 1
            continue
        py = run_python(c)
        ok = agree(py, lo)
        tot = by_fn.setdefault(c["fn"], [0, 0])
        tot[0] += 1
        tot[1] += ok
        if not ok:
            mismatches += 1
            if mismatches <= 20:
                print(f"MISMATCH {json.dumps(c)}\n  python: {py}\n  lean:   {lo}", file=sys.stderr)

    for fn, (n, good) in sorted(by_fn.items()):
        print(f"{fn:16s} {good}/{n}")
    print(f"python {sys.version.split()[0]}: {len(cases) - mismatches}/{len(cases)} agree")
    sys.exit(1 if mismatches else 0)


if __name__ == "__main__":
    main()
