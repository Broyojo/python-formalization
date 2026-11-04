import PyLean.Registry
import PyLean.PyGrammar.RowNames
import PyLean.PyGrammar.Peg.Rules.Patterns2

/-! Registry entries for the pattern rules of `Peg/Rules/Patterns2.lean` and after, in the scheme
of `Entries.lean`. -/

namespace PyLean.PyGrammar.Peg

open PyLean.Registry

private def scheme : String :=
  "Rule-specific: callRule on this rule's data from any entry state (no error, below MAXSTACK, " ++
  "mark within the tokens, token under the mark read), for every result of the sub-rule calls " ++
  "and token reads, given as equations. Written from the rule text, not the data, so another " ++
  "order of alternatives, a dropped lookahead or another action fails it."

def patternEntries : List Entry := [
  { id := "pygrammar-rule-literal-pattern"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_literal_pattern
    statement := "literal_pattern: signed_number not followed by '+'/'-' (_tmp_41, which takes " ++
      "exactly those two) gives MatchValue(value); once that fails, complex_number gives " ++
      "MatchValue(BinOp); then strings MatchValue(strings); then 'None' 'True' 'False' " ++
      "MatchSingleton of that constant spanning the keyword; any other token NULL with the mark back."
    source := "Grammar/python.gram:533-540"
    status := .proven
    prop := ``LiteralPatternRule
    thm := some ``literalPatternRule_proven
    notes := scheme ++ " Tmp41 (tmp41_proven) states the '+'/'-' group." },
  { id := "pygrammar-rule-literal-expr"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_literal_expr
    statement := "literal_expr: in literal_pattern's order, signed_number !('+'|'-'), " ++
      "complex_number and (behind the STRING/FSTRING_START/TSTRING_START lookahead) strings give " ++
      "the expression itself; 'None' 'True' 'False' give Constant(None/True/False, NULL) " ++
      "spanning the keyword; any other token NULL with the mark back."
    source := "Grammar/python.gram:542-548"
    status := .proven
    prop := ``LiteralExpr
    thm := some ``literalExpr_proven
    notes := scheme },
  { id := "pygrammar-rule-complex-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_complex_number
    statement := "complex_number: signed_real_number '+' imaginary_number gives BinOp(real, Add, " ++
      "imag); once that fails with no error, signed_real_number '-' imaginary_number from the " ++
      "start mark gives BinOp(real, Sub, imag); an error in the first (ensure_imaginary " ++
      "raising) gives NULL; both failing NULL with the mark back."
    source := "Grammar/python.gram:550-554"
    status := .proven
    prop := ``ComplexNumber
    thm := some ``complexNumber_proven
    notes := scheme },
  { id := "pygrammar-rule-signed-real-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_signed_real_number
    statement := "signed_real_number: real_number is the result; without it, '+' real_number " ++
      "gives UnaryOp(UAdd), '-' real_number UnaryOp(USub); any other token NULL with the mark back."
    source := "Grammar/python.gram:561-564"
    status := .proven
    prop := ``SignedRealNumber
    thm := some ``signedRealNumber_proven
    notes := scheme },
  { id := "pygrammar-rule-real-imaginary-number"
    pyFile := "Grammar/python.gram"
    pyFns := Rows.rule_real_imaginary_number
    statement := "real_number: a NUMBER that is a non-complex Constant is the result, a complex " ++
      "one raises \"real number required in complex literal\" over it; imaginary_number: a " ++
      "complex Constant is the result, any other raises \"imaginary number required in complex " ++
      "literal\"; no NUMBER NULL with the mark back (_PyPegen_ensure_real/_imaginary)."
    source := "Grammar/python.gram:566-570; Parser/action_helpers.c:853-871"
    status := .proven
    prop := ``RealImaginaryNumber
    thm := some ``realImaginaryNumber_proven
    notes := scheme }
]

end PyLean.PyGrammar.Peg
