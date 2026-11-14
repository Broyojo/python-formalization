<!-- title: SequenceMatcher.get_grouped_opcodes() changes the result of later get_opcodes() calls -->
### Bug report

`SequenceMatcher.get_opcodes()` caches its result and returns the same list on every call. `get_grouped_opcodes()` takes that list and overwrites its first and last entries to trim the context, so after one call the matcher's opcodes no longer cover the whole input, and a later `get_grouped_opcodes()` with a larger `n` shows less context than it should.

This was mentioned in gh-54194 back in 2010, but that issue was closed after only the `get_matching_blocks()` part was fixed (gh-65834); the `get_grouped_opcodes()` part is still there.

```python
import difflib

old = ["line %d\n" % i for i in range(10)]
new = old[:]
new[5] = "changed\n"

sm = difflib.SequenceMatcher(None, old, new)
for group in sm.get_grouped_opcodes(1):
    pass  # show the hunks with one line of context
print(sm.get_opcodes())
```

Actual:

```
[('equal', 4, 5, 4, 5), ('replace', 5, 6, 5, 6), ('equal', 6, 7, 6, 7)]
```

Expected (what `get_opcodes()` returns before the `get_grouped_opcodes()` call):

```
[('equal', 0, 5, 0, 5), ('replace', 5, 6, 5, 6), ('equal', 6, 10, 6, 10)]
```

`unified_diff()` and `context_diff()` are not affected because they make a new matcher each time.

### CPython versions tested on:

3.15, CPython main branch

### Operating systems tested on:

Linux
