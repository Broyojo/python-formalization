# gh-XXXXXX: Rename UserString.replace() parameter maxsplit to count

`collections.UserString.replace()` called its third parameter `maxsplit`, so `UserString('aa').replace('a', 'b', count=1)` raised `TypeError` even though `str.replace()` has accepted `count` as a keyword since 3.13. This renames it to `count` to match `str.replace()`.

The existing `test_count_keyword` in `Lib/test/string_tests.py` called `replace` on `str` literals, so it never ran against `UserString` (or `bytes`/`bytearray`). It now goes through `checkequal`, which exercises every type that shares these tests.

Compatibility: a caller passing `maxsplit=` by keyword now gets `TypeError`. That name was never documented and `str.replace()` never accepted it, and I found no callers in the stdlib.

AI tools (Claude) helped find this and prepare the fix; I reviewed and tested it.
