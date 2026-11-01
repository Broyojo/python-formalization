import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Lexer.Props
import PyLean.PyGrammar.Lexer.Stacks

/-! Registry entries for the `Lexer` part of `PyGrammar`. -/

namespace PyLean.PyGrammar.Lexer

open PyLean.Registry

def entries : List Entry := [
  { id := "pygrammar-lex-stacks"
    pyFile := "Parser/lexer/lexer.c"
    pyFns := Rows.lex_stacks
    statement := "Across any call of tok_get on a sound state, level matches parenstack, indent " ++
      "matches indstack and altindstack, tok_mode_stack_index matches the mode stack, each stays " ++
      "within its fixed C array, indentation columns strictly increase, and the mode index is " ++
      "never decremented at the regular mode."
    source := "invariant: writes to the fixed-size arrays of struct tok_state stay in bounds"
    status := .proven
    prop := ``LexStacks
    thm := some ``lexStacks_proven
    notes := "Says nothing about which tokens come out. Depends on the bracket, indentation and " ++
      "f-string mode code; the number, string and identifier branches only have to leave the " ++
      "stacks alone." },
  { id := "pygrammar-lex-accepts-valid"
    pyFile := "Parser/lexer/lexer.c"
    pyFns := Rows.lex_accepts_valid
    statement := "Every source the compiler accepts tokenizes through TokenizerIter with no " ++
      "exception: the string and readline front ends of the lexer agree on validity."
    source := "invariant"
    status := .refuted
    prop := ``TokenizeAcceptsValid
    thm := some ``tokenizeAcceptsValid_refuted
    bug := some "pygrammar-lex-tokenize-memoryerror"
    notes := "Reproduces on 3.14.7, not on main." },
  { id := "pygrammar-lex-debug-text"
    pyFile := "Parser/lexer/lexer.c"
    pyFns := Rows.lex_debug_text
    statement := "The debug text of f'{expr=}' ends with '=' and optional whitespace."
    source := "docs: f-strings, the '=' specifier"
    status := .refuted
    prop := ``DebugTextKeepsEquals
    thm := some ``debugTextKeepsEquals_refuted
    bug := some "pygrammar-lex-debug-text-escaped-quote"
    notes := "Reproduces on 3.14.7, not on main. Upstream #141271." },
  { id := "pygrammar-lex-exact-tokens"
    pyFile := "Parser/token.c"
    pyFns := Rows.lex_exact_tokens
    statement := "Every spelling in Grammar/Tokens resolves to its token."
    source := "invariant"
    status := .proven
    prop := ``ExactTokensResolve
    thm := some ``exactTokensResolve_proven },
  { id := "pygrammar-lex-nextc-in-buffer"
    pyFile := "Parser/lexer/lexer.c"
    pyFns := Rows.lex_nextc_in_buffer
    statement := "For every tokenizer state with cur <= inp, one tok_nextc keeps cur <= inp."
    source := "Parser/lexer/state.h:79 'buf <= cur <= inp <= end'"
    status := .proven
    prop := ``NextcStaysInBuffer
    thm := some ``nextcStaysInBuffer_proven },
  { id := "pygrammar-lex-translate-newlines"
    pyFile := "Parser/tokenizer/helpers.c"
    pyFns := ["_PyTokenizer_translate_newlines"]
    statement := "With preserve_crlf false, translate_newlines leaves no carriage return."
    source := "invariant"
    status := .proven
    prop := ``TranslateRemovesCr
    thm := some ``translateRemovesCr_proven },
  { id := "pygrammar-lex-token-predicates"
    pyFile := "Lib/token.py"
    pyFns := []
    statement := "ISTERMINAL and ISNONTERMINAL partition the numbers; all kinds are terminal; " ++
      "only ENDMARKER is EOF."
    source := "invariant"
    status := .proven
    prop := ``TokenPredicates
    thm := some ``tokenPredicates_proven },
  { id := "pygrammar-lex-exact-type"
    pyFile := "Lib/tokenize.py"
    pyFns := []
    statement := "An OP token with an exact spelling has that spelling's token as exact_type."
    source := "Lib/tokenize.py TokenInfo.exact_type"
    status := .proven
    prop := ``ExactTypeResolves
    thm := some ``exactTypeResolves_proven },
  { id := "pygrammar-lex-normal-name-twin"
    pyFile := "Lib/tokenize.py"
    pyFns := []
    statement := "_get_normal_name and C get_normal_name agree on every name without a NUL."
    source := "Lib/tokenize.py docstring: 'Imitates get_normal_name'"
    status := .proven
    prop := ``NormalNameTwin
    thm := some ``normalNameTwin_proven },
  { id := "pygrammar-lex-cookie-twin"
    pyFile := "Lib/tokenize.py"
    pyFns := []
    statement := "detect_encoding and the compiler read the same coding cookie from any bytes."
    source := "the implementation against itself; PEP 263"
    status := .refuted
    prop := ``CookieTwin
    thm := some ``cookieTwin_refuted
    bug := some "pygrammar-lex-cookie-cr" },
  { id := "pygrammar-lex-untokenize-lossless"
    pyFile := "Lib/tokenize.py"
    pyFns := ["Untokenizer.add_whitespace", "Untokenizer.add_backslash_continuation"]
    statement := "untokenize of the tokens of a valid source tokenizes back to the same types " ++
      "and strings."
    source := "Lib/tokenize.py untokenize docstring"
    status := .refuted
    prop := ``UntokenizeLossless
    thm := some ``untokenizeLossless_refuted
    bug := some "pygrammar-lex-untokenize-continuation" }
]

end PyLean.PyGrammar.Lexer
