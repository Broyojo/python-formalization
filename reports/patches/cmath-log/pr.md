# gh-XXXXXX: Raise ValueError for cmath.log(0, base)

`cmath_log_impl()` computes `c_log(z)` and then `c_log(base)`, and `c_log()` sets `errno` to 0 on success, so the domain error from `log(0)` was lost and `cmath.log(0, 2)` returned `(-inf+nanj)`. Keep the `errno` from the first call and use it when computing the base's log and the division did not report an error. Errors in the base argument (TypeError from conversion, base 0 or 1) behave as before.

AI tools (Claude) helped find this and prepare the fix; I reviewed and tested it.
