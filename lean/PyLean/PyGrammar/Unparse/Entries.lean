import PyLean.Registry
import PyLean.PyGrammar.Unparse.AstPy

/-! Registry entries for `Lib/ast.py`. The round trips need the parser, so they sit in
`Peg/Entries.lean`, which imports both. -/

namespace PyLean.PyGrammar.Unparse

open PyLean.Registry

def entries : List Entry := [
  { id := "pygrammar-ast-increment-lineno"
    pyFile := "Lib/ast.py"
    pyFns := ["increment_lineno"]
    statement := "increment_lineno by -n undoes increment_lineno by n, for every tree."
    source := "Lib/ast.py increment_lineno docstring: 'move code'"
    status := .proven
    prop := ``IncrementLinenoReversible
    thm := some ``incrementLinenoReversible_proven },
  { id := "pygrammar-ast-splitlines"
    pyFile := "Lib/ast.py"
    pyFns := ["_splitlines_no_ff"]
    statement := "Joining the lines of _splitlines_no_ff gives the source back."
    source := "invariant"
    status := .proven
    prop := ``SplitLinesLossless
    thm := some ``splitLinesLossless_proven },
  { id := "pygrammar-ast-pad-whitespace"
    pyFile := "Lib/ast.py"
    pyFns := ["_pad_whitespace"]
    statement := "_pad_whitespace keeps the length, and yields only space, tab and form feed."
    source := "Lib/ast.py _pad_whitespace docstring"
    status := .proven
    prop := ``PadKeepsColumns
    thm := some ``padKeepsColumns_proven },
  { id := "pygrammar-ast-docstring-twins"
    pyFile := "Lib/ast.py"
    pyFns := ["get_docstring"]
    statement := "get_docstring(clean=False), Unparser.get_raw_docstring and C " ++
      "_PyAST_GetDocString find the same docstring in every body."
    source := "Lib/_ast_unparse.py: 'Logic mirrored from _PyAST_GetDocString'"
    status := .proven
    prop := ``DocstringTwins
    thm := some ``docstringTwins_proven },
  { id := "pygrammar-ast-literal-eval"
    pyFile := "Lib/ast.py"
    pyFns := ["literal_eval"]
    statement := "literal_eval refuses every call with arguments."
    source := "Lib/ast.py literal_eval docstring"
    status := .proven
    prop := ``LiteralRefusesCalls
    thm := some ``literalRefusesCalls_proven }
]

end PyLean.PyGrammar.Unparse
