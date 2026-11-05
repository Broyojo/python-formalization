<!-- title: compile() segfaults on a small hand-built AST with None in Try.handlers -->
<!-- form: crash -->
<!-- records: pygrammar-check-none-in-list-segfault -->
<!-- versions: 3.15.2, CPython main branch -->
A `None` element in a hand-built AST's `Try.handlers` reaches the validator as a NULL handler. The tree is small; this is not the documented limitation on deeply nested or very large ASTs. The malformed tree should raise an exception.

```python
import subprocess, sys
code = ("import ast\n"
        "L = dict(lineno=1, col_offset=0, end_lineno=1, end_col_offset=1)\n"
        "compile(ast.Module([ast.Try([ast.Pass(**L)], [None], [], [], **L)], []), 'x', 'exec')\n")
r = subprocess.run([sys.executable, '-c', code], capture_output=True)
print(r.returncode)
```

The draft reproducer prints `-11` (SIGSEGV) on both 3.15.2 and main in the final prelaunch rerun. The saved record checks also confirm reproduction on both interpreters.

Cause: Python/ast.c:890-893 reads a `Try` handler and immediately uses `VALIDATE_POSITIONS(handler)` without rejecting NULL; the `TryStar` loop at :918-921 instead dereferences the handler's fields directly. The generated AST conversion accepts `None` as NULL for these nodes. The expression and statement list validators already reject forbidden NULL entries; these handler loops should do likewise.

The record also reports the same missing validation across pattern lists, mapping keys, class-pattern keyword attributes, type parameters and `Global.names`. In particular, `validate_patterns` at :1017-1025 forwards NULL, while `validate_type_params` at :1057-1067 skips it and leaves it for later compiler code. These additional cases need their own final reruns before being included as tested variants.
