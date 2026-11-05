<!-- title: pygrammar: 15 small behaviour inconsistencies found by a formal model -->
# Bug report

### Bug description

While modelling this area of CPython 3.15.2 in Lean 4 (https://broyojo.com/python-formalization/), we found the cases below where the implementation disagrees with itself (C vs pure-Python twin, fast vs slow path) or with its documentation. Some may be intended; we list them together so they can be triaged at once. Each reproduces on 3.15.2 and on main.

#### 1. With type_comments=True, a parenthesized `async with` followed by a type comment is a SyntaxError or parses as one tuple item; the gh-111420 fix covered only `with`

gh-111420 (PR #111468, merged 2023-10-31) found that `ast.parse(..., type_comments=True)` rejected
`with (a as b): # type: T` and read `with (a, b): # type: T` as one withitem holding a Tuple, and
fixed it by adding `tc=[TYPE_COMMENT]` to the parenthesized `with` alternative of with_stmt. The
parenthesized `async with` alternative right below it (python.gram:427-428) was left without it,
so the same two failures still happen with `async`: `async with (a as b): # type: T` is a
SyntaxError ("invalid syntax" at the comment), and `async with (a, b): # type: T` gives
AsyncWith(items=[withitem(Tuple(a, b))], type_comment='T') instead of two withitems. Without
type_comments, or without the comment, both parse as the sync forms do.

<details><summary>Reproducer</summary>

```python
import ast
def parse(src):
    try:
        return repr([ast.dump(i) for i in ast.parse(src, type_comments=True).body[0].items])
    except SyntaxError as e:
        return "SyntaxError: " + e.msg
a = parse("with (a as b): # type: int\n    pass\n")
b = parse("async with (a as b): # type: int\n    pass\n")
c = parse("with (a, b): # type: int\n    pass\n")
d = parse("async with (a, b): # type: int\n    pass\n")
print(a)
print(b)
print(c)
print(d)
```

</details>

#### 2. __debug__ in a match value pattern or mapping key is not folded, so it ignores compile(..., optimize=N)

astfold_expr replaces Name('__debug__', Load) with a constant chosen from the optimize level of
this compile. astfold_pattern sends MatchValue.value and each MatchMapping key to
fold_const_match_patterns, which only folds negative and complex literals and does not walk the
expression. So in `case __debug__.real:` the name survives, and at run time it reads the builtin,
whose value comes from the process's -O, not from compile(). With compile(src, 'x', 'exec',
optimize=1) in a process without -O, `__debug__.real` in an expression is 0 while the same
expression in a case pattern is 1. The same source therefore sees two values of __debug__.
MatchClass.cls is walked, so `case __debug__(a=1):` is folded; a guard is folded as well.

<details><summary>Reproducer</summary>

```python
src = '''
match 1:
    case __debug__.real:
        hit = 1
    case _:
        hit = 0
expr = __debug__.real
'''
ns = {}
exec(compile(src, 'x', 'exec', optimize=1), ns)
print(ns['expr'], ns['hit'])
import sys
```

</details>

#### 3. _PyAST_Validate does not validate NamedExpr.target: Name('None') passes and reaches an assert in codegen_nameop; the Load and Del contexts pass too

The NamedExpr case of validate_expr checks only that the target is a Name, then validates the
value. It never calls validate_expr on the target, so validate_name and the context check are
skipped for it. compile(Expression(NamedExpr(Name('None', Store()), Constant(1)))) succeeds, where
Name('None', Load()) anywhere else raises ValueError. The code object then stores to a global
called None, and codegen_nameop asserts the name is not None, True or False, so a debug build
aborts. NamedExpr(Name('x', Load()), ...) passes as well and compiles into a load where a store
belongs: `(x := 1)` then raises NameError.

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

#### 4. _PyAST_Validate checks ExceptHandler positions and names for Try but not for TryStar, and lets a bare except* through to an internal 'Invalid CFG' error

validate_stmt has two copies of the handler loop, and the TryStar copy lacks two checks the Try
copy has. VALIDATE_POSITIONS(handler): compile() of a tree with a handler whose lineno exceeds
its end_lineno raises "AST node line range (5, 1) is not valid" for Try and passes validation
for TryStar. validate_name(handler->v.ExceptHandler.name), added to the Try copy in 3.15:
ExceptHandler(name='None') raises "identifier field can't represent 'None' constant" for Try,
and for TryStar compiles to a store to a name called None, which codegen_nameop asserts against.
Separately, ExceptHandler.type=None is accepted for TryStar although `except*:` has no
syntax; compile then fails with the internal message "Invalid CFG, stack underflow" from the
flow graph code rather than a validation error.

<details><summary>Reproducer</summary>

```python
import ast
L = dict(lineno=1, col_offset=0, end_lineno=1, end_col_offset=1)
def tree(cls, ty):
    h = ast.ExceptHandler(ty, None, [ast.Pass(**L)], lineno=5, col_offset=0, end_lineno=1, end_col_offset=0)
    return ast.Module([cls([ast.Pass(**L)], [h], [], [], **L)], [])
x = ast.Name('x', ast.Load(), **L)
res = []
for c in (ast.Try, ast.TryStar):
    try:
        compile(tree(c, x), 'x', 'exec')
        res.append('ok')
    except ValueError as e:
        res.append(str(e))
print(res)
names = []
for c in (ast.Try, ast.TryStar):
    h = ast.ExceptHandler(x, 'None', [ast.Pass(**L)], **L)
    try:
        compile(ast.Module([c([ast.Pass(**L)], [h], [], [], **L)], []), 'x', 'exec')
        names.append('ok')
    except ValueError as e:
        names.append(str(e))
print(names)
if (res[0].startswith('AST node line range') and res[1] == 'ok'
        and names[0].startswith('identifier field') and names[1] == 'ok'):
```

</details>

#### 5. A format spec with a \\N{...} escape followed by more text is a Constant in the AST, not a JoinedStr

ast.FormattedValue.format_spec and ast.Interpolation.format_spec are documented as a JoinedStr
(Doc/library/ast.rst:319-320, 402-405), and python/cpython#122300 (3.13 regression) restored
that for `f'{e:.3}'`: gh-122308 added the branch at Parser/action_helpers.c:1069-1072 that wraps
zero or one constant in a JoinedStr. With two or more constants and no replacement field,
_PyPegen_setup_full_format_spec still calls _PyPegen_concatenate_strings, whose all-str branch
(_build_concatenated_unicode) returns a bare Constant, and that Constant becomes the format spec.
The lexer ends an FSTRING_MIDDLE at the closing brace of a \N{...} escape, so any format spec
with \N{...} followed by more text, or two \N{...} escapes, arrives as two constants:
ast.parse(r"f'{x:\N{DIGIT ONE}b}'") has format_spec=Constant('1b'), while f'{x:1b}' and
f'{x:\N{DIGIT ONE}}' have JoinedStr([Constant(...)]). The t-string twin is the same.

<details><summary>Reproducer</summary>

```python
import ast

def spec(src):
    return ast.parse(src).body[0].value.values[0].format_spec

a = spec(r"f'{x:\N{DIGIT ONE}b}'")
b = spec(r"f'{x:1b}'")
c = spec(r"t'{x:\N{DIGIT ONE}b}'")
d = spec(r"f'{x:\N{DIGIT ONE}}'")
print(ast.dump(a), ast.dump(b), ast.dump(c), ast.dump(d))
if (type(a).__name__ == 'Constant' and type(b).__name__ == 'JoinedStr'
        and type(c).__name__ == 'Constant' and type(d).__name__ == 'JoinedStr'):
```

</details>

#### 6. An invalid escape in a multi-line f-string or t-string is warned about on the wrong line

The SyntaxWarning for an invalid escape sequence names the line of the escape for a plain
string, but for the literal text of an f-string or t-string it names a line counted from the
string's closing quote. warn_invalid_escape_sequence (Parser/string_parser.c:53-66) starts at
t->lineno and adds the newlines before the escape in the decoded text. For a STRING token t is
the string itself; for an f-string part, _get_resized_exprs (Parser/action_helpers.c:1401)
calls _PyPegen_decode_fstring_part(p, is_raw, item, b) with b the FSTRING_END/TSTRING_END
token, which _PyPegen_decode_string passes on (:1333). So

<details><summary>Reproducer</summary>

```python
import warnings

def lines(src):
    with warnings.catch_warnings(record=True) as w:
        warnings.simplefilter('always')
        compile(src, '<s>', 'exec')
    return [x.lineno for x in w if issubclass(x.category, SyntaxWarning)]

def err_line(src):
    with warnings.catch_warnings():
        warnings.simplefilter('error')
        try:
            compile(src, '<s>', 'exec')
        except SyntaxError as e:
            return e.lineno

plain = lines("x = '''\n\\d\n'''\n")
fstr = lines("x = f'''\n\\d\n'''\n")
tstr = lines("x = t'''\n\\d\n'''\n")
first = lines("x = f'''\\d\n\n\n'''\n")
werr = (err_line("x = '''\n\\d\n'''\n"), err_line("x = f'''\n\\d\n'''\n"))
print(plain, fstr, tstr, first, werr)
```

</details>

#### 7. PEP 798: `(*a or b for x in y)` parses but `[*a or b for x in y]` and `{*a or b for x in y}` are SyntaxErrors; the reference says generator expressions have list-comprehension syntax

3.15 adds unpacking in comprehensions (PEP 798). `listcomp` and `setcomp` take
`star_named_expression` (python.gram:1058-1064), whose star form is `'*' bitwise_or`
(python.gram:745-747). `genexp` takes `( assignment_expression | expression !':=' |
starred_expression )` (python.gram:1066-1068), and `starred_expression` is the call-argument
rule `'*' expression` (python.gram:1094-1097). So a starred element that is not a `bitwise_or`
is accepted only in a generator expression:

<details><summary>Reproducer</summary>

```python
import ast
def ok(src):
    try:
        ast.parse(src)
        return True
    except SyntaxError:
        return False
gen = [ok(f"({e} for x in y)") for e in ["*a or b", "*not a", "*a if c else d"]]
lst = [ok(f"[{e} for x in y]") for e in ["*a or b", "*not a", "*a if c else d"]]
st = [ok(f"{{{e} for x in y}}") for e in ["*a or b", "*not a", "*a if c else d"]]
print("genexp", gen, "listcomp", lst, "setcomp", st)
```

</details>

#### 8. Grammar comment says invalid_ rules are not used in the first pass, but dict calls invalid_double_starred_kvpairs unguarded

The comment at the top of Grammar/python.gram says rules starting with invalid_ "are NOT used in
the first pass of the parser". c_generator.py guards an alternative with
`if (p->call_invalid_rules)` only when it consists of a single invalid_ item (visit_Alt). The
second alternative of dict, `'{' invalid_double_starred_kvpairs '}'`, has three items, so it runs
in the first pass. Of all 268 rules this is the only such alternative. An error it raises sets
error_indicator, and reset_parser_state_for_error_pass does not clear that, so the second pass
returns at once and SyntaxError._metadata stays (0, 0): the "did you mean" keyword suggestion in
tracebacks sees no statement location.

<details><summary>Reproducer</summary>

```python
def meta(src):
    try:
        compile(src, 'x', 'exec')
    except SyntaxError as e:
        return e._metadata[:2]
first = meta("if 1:\n    pass\n{1: *a}\n")
second = meta("if 1:\n    pass\nprint 1\n")
print(first, second)
```

</details>

#### 9. `lazy import` with no names, or `lazy import a.b from c`, gets 'invalid syntax' instead of the messages `import` gets

3.15 lets `import_name` start with the soft keyword `lazy` (PEP 810), python.gram:227-228. The
error rule for it, `invalid_import` (python.gram:1433-1437), starts with `'import'` and has no
`"lazy"?`, so at a `lazy` token it fails at once and the second pass falls back to the generic
message. `import` alone says "Expected one or more names after 'import'"; `lazy import` alone
says "invalid syntax". `import a.b from c` says "Did you mean to use 'from ... import ...'
instead?"; `lazy import a.b from c` says "invalid syntax". The `from` forms are consistent:
`lazy from x import` gets "Expected one or more names after 'import'" from
`invalid_import_from_targets`, which is reached through `import_from_targets` whatever came
before.

<details><summary>Reproducer</summary>

```python
def msg(src):
    try:
        compile(src, "<s>", "exec")
    except SyntaxError as e:
        return e.msg
a, b = msg("import\n"), msg("lazy import\n")
c, d = msg("import a.b from c\n"), msg("lazy import a.b from c\n")
print(repr(a), repr(b))
print(repr(c), repr(d))
if a == "Expected one or more names after 'import'" and b == "invalid syntax" and \
   c.startswith("Did you mean") and d == "invalid syntax":
```

</details>

#### 10. tokenize.detect_encoding and the compiler read different encodings from a source with bare CR line endings

PEP 263 limits the cookie to the first two lines. The C tokenizer runs translate_newlines first, so
a bare CR ends a line. detect_encoding splits with readline, which on bytes stops only at LF, so
all the CR-terminated lines count as one, and cookie_re's `.*?` runs across them. For
b'#\r#\r# coding: latin-1\n' the compiler sees the cookie on line 3 and ignores it, while
detect_encoding returns iso-8859-1. A file with non-UTF-8 bytes and this header compiles under one
and not the other.

<details><summary>Reproducer</summary>

```python
import io, tokenize
src = b'#\r#\r# coding: latin-1\nx = "\xe9"\n'
enc = tokenize.detect_encoding(io.BytesIO(src).readline)[0]
try:
    compile(src, 'x', 'exec')
    c = 'compiled'
except SyntaxError:
    c = 'SyntaxError'
print(enc, c)
```

</details>

#### 11. tokenize.untokenize loses the indentation of a block indented through a backslash continuation, breaking its round-trip guarantee on valid source

A body may take its indentation from a backslash-continued line: `if x:\n    \\\ny\n` is valid, and
cont_line_col gives the block its depth (lexer.c:490-499). In readline mode the continuation reads
the next line, which moves tok->buf, so INDENT has p_start = tok->buf = p_end and an empty string
(lexer.c:585-591). Untokenizer stores that empty indent, so the text it writes has no indentation
before `y`. Its docstring guarantees that the output tokenizes back to the same types and strings.

<details><summary>Reproducer</summary>

```python
import io, tokenize
src = "if x:\n    \\\ny\n"
compile(src, 'x', 'exec')
key = lambda s: [(t.type, t.string) for t in tokenize.generate_tokens(io.StringIO(s).readline)]
a = key(src)
out = tokenize.untokenize(tokenize.generate_tokens(io.StringIO(src).readline))
b = key(out)
print(repr(out), a == b)
```

</details>

#### 12. A bad escape in an f-string format spec escapes compile() as UnicodeDecodeError, not SyntaxError

_PyPegen_decoded_constant_from_token returns NULL when _PyPegen_decode_string fails, with the
UnicodeDecodeError still set. Its two siblings first call the raiser that turns that error into
a SyntaxError: _PyPegen_decode_fstring_part and _PyPegen_constant_from_string. So
compile(r"f'\N{foo}'") raises "SyntaxError: (unicode error) ..." with a location, and
compile(r"f'{x:\N{foo}}'") raises a bare UnicodeDecodeError with none. This duplicates the open
python/cpython#157890, found while migrating the model to 3.15.2.

<details><summary>Reproducer</summary>

```python
good = bad = None
try:
    compile(r"f'\N{foo}'", 'x', 'exec')
except Exception as e:
    good = type(e).__name__
try:
    compile(r"f'{x:\N{foo}}'", 'x', 'exec')
except Exception as e:
    bad = type(e).__name__
print(good, bad)
```

</details>

#### 13. A malformed replacement field nested in a t-string's format spec is reported as an 'f-string:' error

invalid_tstring_replacement_field (python.gram:1609-1625) is the t-string copy of
invalid_fstring_replacement_field (1587-1603), with every message prefixed "t-string:". Its
tenth alternative, line 1622, still reads
    | '{' annotated_rhs '='? ['!' NAME] ':' fstring_format_spec* !'}' { ... "t-string: ..." }
with the f-string format-spec loop. Inside a t-string, fstring_format_spec never matches a
TSTRING_MIDDLE (it wants FSTRING_MIDDLE), so it reaches fstring_replacement_field, whose
second-pass alternative invalid_fstring_replacement_field raises its own "f-string: ..."
message for a nested field. So `t'{x:{a:}'` fails with "f-string: expecting '}', or format
specs", while `t'{x:{a}'` gets "t-string: expecting '}', or format specs" and
`t'{x:{a:{}'` gets "t-string: valid expression required before '}'". The location differs too:
the f-string twin `f'{x:{a:}'` reports offset 10..11, the t-string offset 9..9.

<details><summary>Reproducer</summary>

```python
def msg(src):
    try:
        compile(src, "<s>", "exec")
    except SyntaxError as e:
        return e.msg
f = msg("f'{x:{a:}'\n")
t = msg("t'{x:{a:}'\n")
t2 = msg("t'{x:{a}'\n")
print(repr(f), repr(t), repr(t2))
if f == "f-string: expecting '}', or format specs" and \
   t == "f-string: expecting '}', or format specs" and \
   t2 == "t-string: expecting '}', or format specs":
```

</details>

#### 14. Stringified annotations misquote f-strings: Python/ast_unparse.c applies repr() to a body holding source text, so nested strings and quotes change or do not parse

Under `from __future__ import annotations`, _PyAST_ExprAsUnicode writes an f-string by building its
body as text, replacement fields included, and then taking repr() of the whole body. repr escapes
what it sees, so the source text of the expressions inside is escaped a second time. For
x: f"{'\n'}" the stored annotation is f"{'\\n'}", where the nested string is a backslash and an n,
not a newline. When the body holds both kinds of quote, repr writes \' inside a replacement field,
which is not valid source. ast.unparse has no such problem, since _ftstring_helper keeps the
expression parts out of the escaping.

<details><summary>Reproducer</summary>

```python
import ast
src = "from __future__ import annotations\nx: f\"{'\\n'}\"\n"
ns = {}
exec(compile(src, 'x', 'exec'), ns)
s = ns['__annotations__']['x']
a = ast.parse(src).body[1].annotation
b = ast.parse(s, mode='eval').body
print(repr(s), ast.dump(b))
```

</details>

#### 15. ast.unparse corrupts f-string format specs holding braces or control characters written as escapes: output is invalid or means something else

A literal part of a format spec is written by _write_ftstring_inner with only `\`, quotes and
newline escaped, after doubling `{` and `}`. Three things go wrong for valid source:

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

3.15, CPython main branch (ef1fce0)

### Operating systems tested on

Linux

---
Drafted with AI assistance; each case was reproduced and the report reviewed before filing.
