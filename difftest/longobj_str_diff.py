"""Differential test of the int/str conversions and `_pylong` (see longobj_str_gen.py)."""

import common
from longobj_str_gen import gen_case, run_python

if __name__ == "__main__":
    common.main(gen_case, run_python, default_cases=50000)
