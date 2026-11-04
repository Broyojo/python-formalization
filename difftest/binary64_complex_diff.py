"""Differential test: the complex cases of binary64_diff.py alone (Objects/complexobject.c).

Usage: python3 difftest/binary64_complex_diff.py [--cases N] [--seed S]

The same generator and handler as binary64_diff.py, where complex cases are 15% of the mix.
"""

import common
import binary64_diff as b

if __name__ == "__main__":
    common.main(b.gen_complex_case, b.run_complex, default_cases=50000)
