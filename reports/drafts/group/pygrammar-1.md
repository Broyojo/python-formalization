<!-- title: Small inconsistencies in the parser and grammar found by a formal model -->
# Bug report

### Bug description

While modelling CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below, where the implementation disagrees with itself (C and pure-Python versions, fast and slow paths) or with its documentation. Some may be intended; where we suspected that, it is noted. Each reproduces on 3.15.2 and on main. They are grouped here so they can be triaged together; we're happy to split out any that deserve their own issue.

#### 1. _PyAST_Validate does not validate NamedExpr.target: Name('None') passes and reaches an assert in codegen_nameop; the Load and Del contexts pass too

The NamedExpr case of validate_expr checks only that the target is a Name, then validates the value. It never calls validate_expr on the target, so validate_name and the context check are skipped for it. compile(Expression(NamedExpr(Name('None', Store()), Constant(1)))) succeeds, where Name('None', Load()) anywhere else raises ValueError. The code object then stores to a global called None, and codegen_nameop asserts the name is not None, True or False, so a debug build aborts. NamedExpr(Name('x', Load()), ...) passes as well and compiles into a load where a store belongs: `(x := 1)` then raises NameError.

<details><summary>Reproducer</summary>

```python
import ast
L = dict(lineno=1, col_offset=0, end_lineno=1, end_col_offset=1)
plain = ast.Expression(ast.Name('None', ast.Load(), **L))
walrus = ast.Expression(ast.NamedExpr(ast.Name('None', ast.Store(), **L), ast.Constant(1, **L), **L))
try:
    compile(plain, 'x', 'eval')
    a = 'accepted'
except ValueError as e:
    a = str(e)
b = eval(compile(walrus, 'x', 'eval'), {})
print(a, b)
```

</details>

#### 2. ast.unparse corrupts f-string format specs holding braces or control characters written as escapes: output is invalid or means something else

A literal part of a format spec is written by _write_ftstring_inner with only `\`, quotes and newline escaped, after doubling `{` and `}`. Three things go wrong for valid source:

<details><summary>Reproducer</summary>

```python
import ast
def rt(src):
    t = ast.parse(src)
    u = ast.unparse(t)
    try:
        return ast.compare(t, ast.parse(u)), u
    except (SyntaxError, ValueError) as e:
        return False, u
a = rt(r'''f"{x:\x7d}"''')
b = rt(r'''f"{x:\x7b}"''')
c = rt(r'''f"{x:\x00}"''')
print(a, b, c)
```

</details>

### CPython versions tested on

3.15, CPython main branch

### Operating systems tested on

Linux

---
Drafted with AI assistance (Claude); each case was reproduced on 3.15.2 and on main and the report reviewed before filing. Records: https://github.com/Broyojo/python-formalization/tree/main/bugs
