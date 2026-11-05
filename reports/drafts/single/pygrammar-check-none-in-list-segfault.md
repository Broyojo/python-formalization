<!-- title: compile() segfaults on an AST with None in a list field -->
# Bug report

### Bug description

obj2ast for a sum type turns None into NULL, so a list element None becomes a NULL entry. The validator guards this for expressions and statements ("None disallowed in expression list") but not for the other sum-typed lists. compile(ast.Module([ast.Try([ast.Pass()], [None], [], [])], []), ...) reaches VALIDATE_POSITIONS(handler) with handler NULL and the interpreter dies with SIGSEGV. MatchSequence([None]) does the same through validate_patterns and validate_pattern. TypeAlias(type_params=[None]) passes validation, since validate_type_params skips NULL, and crashes later in the compiler. Product types are not affected, because their obj2ast raises 'required field missing'. The crash needs no deep nesting: each tree here has a handful of nodes. Replacing one element by None in every list field of a tree that uses all of them gives SIGSEGV for Try.handlers, TryStar.handlers, MatchSequence.patterns, MatchOr.patterns, MatchMapping.patterns, MatchMapping.keys, MatchClass.patterns, MatchClass.kwd_patterns, MatchClass.kwd_attrs, FunctionDef.type_params and Global.names. MatchMapping.keys dies in validate_pattern at key->kind, kwd_attrs in validate_name, Global.names past the validator.

```python
import subprocess, sys
code = ("import ast\n"
        "L = dict(lineno=1, col_offset=0, end_lineno=1, end_col_offset=1)\n"
        "compile(ast.Module([ast.Try([ast.Pass(**L)], [None], [], [], **L)], []), 'x', 'exec')\n")
r = subprocess.run([sys.executable, '-c', code], capture_output=True)
print(r.returncode)
```

**Expected:** ValueError, as "None disallowed in expression list" for expressions.

**Actual:** 

**Cause:** Python/ast.c, validate_stmt: the handler loops of Try_kind and TryStar_kind use `handler` with no NULL check; validate_patterns passes NULL to validate_pattern; validate_type_params skips NULL entries rather than rejecting them; validate_pattern reads key->kind for a NULL key in MatchMapping and passes a NULL name to validate_name for kwd_attrs; nothing checks Global.names.

**Possible fix:** Reject NULL in those loops with ValueError, the way validate_stmts and validate_exprs do; better, have the generated obj2ast list code in Parser/asdl_c.py reject None for non-optional elements.

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Found while building a Lean 4 model of CPython (https://broyojo.com/python-formalization/). The report was drafted with AI assistance (Claude); I reproduced it on 3.15.2 and on main and reviewed it before filing.
Record: https://github.com/Broyojo/python-formalization/blob/main/bugs/pygrammar-check-none-in-list-segfault.yaml
