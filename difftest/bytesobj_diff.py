"""Differential test: Lean model of tuple, list, bytes, bytearray and memoryview
vs. the running CPython.

Usage: python3 difftest/bytesobj_diff.py [--cases N] [--seed S] [--family F]

Each family below supplies `gen_<family>(rng)` and `run_<family>(case)`. Cases
carry "mod": "bytesobj" and a `fn` starting with the family prefix.
"""

import sys

import common


def choose_family():
    """`--family seq|bytes|mem` restricts the run; the option is removed from argv."""
    if "--family" not in sys.argv:
        return None
    i = sys.argv.index("--family")
    family = sys.argv[i + 1]
    del sys.argv[i:i + 2]
    return family


# ===== family seq: tuple and list =====================================


def gen_seq(rng):
    return None


def run_seq(case):
    raise NotImplementedError(case["fn"])


# ===== end of family seq ==============================================


# ===== family bytes: bytes and bytearray ==============================


def gen_bytes(rng):
    return None


def run_bytes(case):
    raise NotImplementedError(case["fn"])


# ===== end of family bytes ============================================


# ===== family mem: memoryview =========================================


def gen_mem(rng):
    return None


def run_mem(case):
    raise NotImplementedError(case["fn"])


# ===== end of family mem ==============================================


FAMILIES = {"seq": (gen_seq, run_seq), "bytes": (gen_bytes, run_bytes), "mem": (gen_mem, run_mem)}
PREFIXES = {"tuple": "seq", "list": "seq", "bytes": "bytes", "bytearray": "bytes", "mem": "mem"}


def main():
    only = choose_family()
    names = [only] if only else list(FAMILIES)

    def gen_case(rng):
        return FAMILIES[rng.choice(names)][0](rng)

    def run_python(case):
        return FAMILIES[PREFIXES[case["fn"].split(".")[0]]][1](case)

    common.main(gen_case, run_python)


if __name__ == "__main__":
    main()
