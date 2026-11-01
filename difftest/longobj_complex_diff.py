"""Differential test: Lean model of `Objects/complexobject.c` vs. the running CPython.

Usage: python3 difftest/longobj_complex_diff.py [--cases N] [--seed S]

Exits non-zero on any mismatch. See difftest/common.py and longobj_complex_gen.py.
"""

import common
import longobj_complex_gen as gen

if __name__ == "__main__":
    common.main(gen.gen_case, gen.run_python, default_cases=50000)
