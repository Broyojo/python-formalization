# gh-XXXXXX: Don't modify the cached opcodes in difflib.SequenceMatcher.get_grouped_opcodes()

`get_grouped_opcodes()` trimmed the leading and trailing `equal` opcodes in place, on the list that `get_opcodes()` caches, so later `get_opcodes()` and `get_grouped_opcodes()` calls on the same matcher returned wrong results. It now works on a shallow copy; the tuples themselves are replaced rather than modified, so a copy of the list is enough. Added a regression test.

AI tools (Claude) helped find this and prepare the fix; I reviewed and tested it.
