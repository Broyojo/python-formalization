"""Differential test: Lean model of str (Objects/unicodeobject.c and friends)
vs. the running CPython.

Usage: python3 difftest/unicodeobj_diff.py [--cases N] [--seed S]
Set UO_SLICE=object|codec|format|text to run one slice only.

Strings and bytes travel as lists of ints, because JSON and Lean's `String` have
no lone surrogates. A slice registers generators with `@gen(slice, weight)` and
python sides with `@run("fn")`; `ONCE` holds cases emitted once, before the random
ones (the all-code-point table sweeps). Each slice edits its own section only.
"""

import os
import sys

import common

M = sys.maxsize
GENS = []  # (slice, weight, generator)
RUNS = {}  # fn name -> function(case) -> JSON-able result (exceptions are captured)
ONCE = []  # (slice, case)
SLICE = os.environ.get("UO_SLICE")


def gen(slice_name, weight=1):
    def register(f):
        GENS.append((slice_name, weight, f))
        return f
    return register


def run(name):
    def register(f):
        RUNS[name] = f
        return f
    return register


def s_of(cps):
    return "".join(map(chr, cps))


def cps_of(s):
    return [ord(c) for c in s]


# ==== object slice (fn names obj_*) ====

# ==== end object slice ====


# ==== codec slice (fn names codec_*) ====

# ==== end codec slice ====


# ==== format slice (fn names fmt_*) ====

# ==== end format slice ====


# ==== text slice (fn names text_*) ====

# ==== end text slice ====


active = [(w, f) for s, w, f in GENS if SLICE in (None, s)]
pending = [c for s, c in ONCE if SLICE in (None, s)]
total_weight = sum(w for w, _ in active)


def gen_case(rng):
    if pending:
        return pending.pop()
    r = rng.uniform(0, total_weight)
    for w, f in active:
        r -= w
        if r <= 0:
            return f(rng)
    return active[-1][1](rng)


def run_python(case):
    return common.py_result(lambda: RUNS[case["fn"]](case))


if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=20000)
