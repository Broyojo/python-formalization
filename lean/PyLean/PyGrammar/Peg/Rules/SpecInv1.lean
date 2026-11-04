import PyLean.PyGrammar.Peg.Rules.Spec

/-! `invalid_` rules as equations (`Spec.lean`), with their exact messages and locations:
`invalid_kwds`, `invalid_lambda_kwds`, `invalid_block`, `invalid_double_type_comments`,
`invalid_type_params`, `invalid_noteq`, `invalid_factor`, `invalid_arithmetic`,
`invalid_starred_expression`, `invalid_if_expression`, `invalid_kvpair_unpacking`,
`invalid_kvpair`, and the token groups they use. Token numbers are those of
`Include/internal/pycore_token.h` (`(` 7, `)` 8, `[` 9, `]` 10, `:` 11, `,` 12, `+` 14, `-` 15,
`*` 16, `/` 17, `<` 20, `>` 21, `=` 22, `%` 24, `}` 26, `~` 31, `**` 35, `//` 47, `@` 49,
`NEWLINE` 4, `INDENT` 5, `TYPE_COMMENT` 57; keywords `if` 700, `else` 704, `not` 721). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `invalid_kwds`, `invalid_lambda_kwds` -/

/-- `_tmp_129: '*' | '**' | '/'`. -/
def Tmp129 : Prop := TokGroup 406 [16, 35, 17]
theorem tmp129_proven : Tmp129 := tokGroup_of (by simp) rfl

/-- `invalid_kwds` (`Grammar/python.gram:1381-1384`), and `invalid_lambda_kwds` (1409-1412) with
`lambda_param` (159) for `param` (49):
```
    | '**' param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-keyword parameter cannot have default value") }
    | '**' param ',' a=param { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "parameters cannot follow var-keyword parameter") }
    | '**' param ',' a[Token*]=('*'|'**'|'/') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "parameters cannot follow var-keyword parameter") }
```
-/
def InvalidKwdsOf (id prm : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) id p = finish (specAlts f [
    ⟨[.call (.tok 35), .call (.rule prm), .call (.tok 22)], false,
      oKL 2 "var-keyword parameter cannot have default value"⟩,
    ⟨[.call (.tok 35), .call (.rule prm), .call (.tok 12), .call (.rule prm)], false,
      oKL 3 "parameters cannot follow var-keyword parameter"⟩,
    ⟨[.call (.tok 35), .call (.rule prm), .call (.tok 12), .call (.rule 406)], false,
      oKL 3 "parameters cannot follow var-keyword parameter"⟩] p.mark (0, 0) p.enter)

def InvalidKwds : Prop := InvalidKwdsOf 226 49 ∧ Tmp129
def InvalidLambdaKwds : Prop := InvalidKwdsOf 231 159 ∧ Tmp129

theorem invalidKwds_proven : InvalidKwds := by
  refine ⟨fun f p he hl => ?_, tmp129_proven⟩
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 226 = r226 from rfl, r226]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

theorem invalidLambdaKwds_proven : InvalidLambdaKwds := by
  refine ⟨fun f p he hl => ?_, tmp129_proven⟩
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 231 = r231 from rfl, r231]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-! ### `invalid_block`, `invalid_double_type_comments`, `invalid_type_params`,
`invalid_starred_expression` -/

/-- `invalid_block: NEWLINE !INDENT { RAISE_INDENTATION_ERROR("expected an indented block") }`
(`Grammar/python.gram:1348-1349`): an `IndentationError` at the last token read. -/
def InvalidBlock : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (f + 2) 221 p = finish (specAlts f [
    ⟨[.call (.tok 4), .look false (.tok 5)], false,
      oMsg "IndentationError" false (fun _ => "expected an indented block")⟩] p.mark (0, 0) p.enter)

theorem invalidBlock_proven : InvalidBlock := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 221 = r221 from rfl, r221]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-- `invalid_double_type_comments: TYPE_COMMENT NEWLINE TYPE_COMMENT NEWLINE INDENT {
RAISE_SYNTAX_ERROR("Cannot have two type comments on def") }` (`Grammar/python.gram:1413-1415`). -/
def InvalidDoubleTypeComments : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 232 p = finish (specAlts f [
    ⟨[.call (.tok 57), .call (.tok 4), .call (.tok 57), .call (.tok 4), .call (.tok 5)], false,
      oMsg "SyntaxError" false (fun _ => "Cannot have two type comments on def")⟩] p.mark (0, 0) p.enter)

theorem invalidDoubleTypeComments_proven : InvalidDoubleTypeComments := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 232 = r232 from rfl, r232]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-- `invalid_type_params: '[' token=']' { RAISE_SYNTAX_ERROR_STARTING_FROM(token, "Type parameter
list cannot be empty")}` (`Grammar/python.gram:1642-1646`): from the `]` to the end of the line. -/
def InvalidTypeParams : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 276 p = finish (specAlts f [
    ⟨[.call (.tok 9), .call (.tok 10)], false, oFrom 1 "Type parameter list cannot be empty"⟩]
    p.mark (0, 0) p.enter)

theorem invalidTypeParams_proven : InvalidTypeParams := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 276 = r276 from rfl, r276]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-- `invalid_starred_expression: '*' { RAISE_SYNTAX_ERROR("Invalid star expression") }`
(`Grammar/python.gram:1585-1586`). -/
def InvalidStarredExpression : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 268 p = finish (specAlts f [
    ⟨[.call (.tok 16)], false, oMsg "SyntaxError" false (fun _ => "Invalid star expression")⟩]
    p.mark (0, 0) p.enter)

theorem invalidStarredExpression_proven : InvalidStarredExpression := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 268 = r268 from rfl, r268]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-! ### `invalid_noteq` -/

/-- `_PyPegen_tokens_are_adjacent(a, b)` (`Parser/pegen.h:212-216`): `a` ends where `b` starts. -/
def tokensAdjacent : Ast → Ast → Bool
  | .tok x, .tok y => x.endLineno == y.lineno && x.endColOffset == y.colOffset
  | _, _ => false

def noteqMsg : String := "invalid syntax.  Maybe you meant '!=' instead of '<>'?"

/-- `invalid_noteq` (`Grammar/python.gram:1648-1653`):
```
    | a='<' b='>' {
        _PyPegen_tokens_are_adjacent(a, b)
        ? RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax.  Maybe you meant '!=' instead of '<>'?")
        : NULL
    }
```
`<` (20) and `>` (21) next to each other raise over both; with space between them the action's
`NULL` (no exception) is the result, with the mark after `>`. -/
def InvalidNoteq : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (f + 2) 277 p = finish (specAlts f [
    ⟨[.call (.tok 20), .call (.tok 21)], false, fun env _ s =>
      if tokensAdjacent (env.getD 0 .null) (env.getD 1 .null) then
        (none, raisedAt (env.getD 0 .null) (env.getD 1 .null) noteqMsg s)
      else pureRes .null s⟩] p.mark (0, 0) p.enter)

theorem callHelper_adjacent (a b : Ast) (s : PS) :
    callHelper .tokens_are_adjacent [a, b] s = (.int (if tokensAdjacent a b then 1 else 0), s) := by
  cases a <;> cases b <;> simp [callHelper, tokensAdjacent] <;> rfl

theorem invalidNoteq_proven : InvalidNoteq := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 277 = r277 from rfl, r277]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil
  have ht : ∀ ex, evalA env ex (.call .tokens_are_adjacent [.var 0, .var 1]) s =
      (.int (if tokensAdjacent (env.getD 0 .null) (env.getD 1 .null) then 1 else 0), s) := by
    intro ex
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, List.getD_cons_zero,
      List.getD_cons_succ]
    exact callHelper_adjacent _ _ _
  dsimp only
  cases hadj : tokensAdjacent (env.getD 0 .null) (env.getD 1 .null)
  · rw [altResult_pure rfl (fun ex => by
      rw [evalA_ite, ht, hadj]
      rfl)]
    rfl
  · rw [altResult_raise rfl (fun ex => by
      rw [evalA_ite, ht, hadj]
      exact evalA_kr env ex 0 1 noteqMsg s (by decide +kernel)) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl

/-! ### `invalid_factor`, `invalid_arithmetic` -/

/-- `_tmp_158: '+' | '-' | '~'`. -/
def Tmp158 : Prop := TokGroup 435 [14, 15, 31]
theorem tmp158_proven : Tmp158 := tokGroup_of (by simp) rfl

/-- `_tmp_157: '+' | '-' | '*' | '/' | '%' | '//' | '@'`. -/
def Tmp157 : Prop := TokGroup 434 [14, 15, 16, 17, 24, 47, 49]
theorem tmp157_proven : Tmp157 := tokGroup_of (by simp) rfl

def notParenMsg : String := "'not' after an operator must be parenthesized"

/-- `invalid_factor: ('+' | '-' | '~') a='not' b=factor { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b,
"'not' after an operator must be parenthesized") }` (`Grammar/python.gram:1639-1640`): over `not`
.. the operand. -/
def InvalidFactor : Prop := (∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (f + 2) 275 p = finish (specAlts f [
    ⟨[.call (.rule 435), .call (.tok 721), .call (.rule 141)], false, oKR 1 2 notParenMsg⟩]
    p.mark (0, 0) p.enter)) ∧ Tmp158

theorem invalidFactor_proven : InvalidFactor := by
  refine ⟨fun f p he hl => ?_, tmp158_proven⟩
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 275 = r275 from rfl, r275]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-- `invalid_arithmetic: sum ('+'|'-'|'*'|'/'|'%'|'//'|'@') a='not' b=inversion {
RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "'not' after an operator must be parenthesized") }`
(`Grammar/python.gram:1637-1638`): `sum` (139), the operator group, `not` and an `inversion`
(122), over `not` .. the operand. -/
def InvalidArithmetic : Prop := (∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 274 p = finish (specAlts f [
    ⟨[.call (.rule 139), .call (.rule 434), .call (.tok 721), .call (.rule 122)], false,
      oKR 2 3 notParenMsg⟩] p.mark (0, 0) p.enter)) ∧ Tmp157

theorem invalidArithmetic_proven : InvalidArithmetic := by
  refine ⟨fun f p he hl => ?_, tmp157_proven⟩
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 274 = r274 from rfl, r274]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-! ### `invalid_if_expression` -/

/-- `invalid_if_expression` (`Grammar/python.gram:1281-1285`):
```
   | disjunction 'if' b=disjunction 'else' a='*' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot unpack only part of a conditional expression") }
   | disjunction 'if' b=disjunction 'else' a='**' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use dict unpacking on only part of a conditional expression") }
```
`disjunction` is rule 120. -/
def InvalidIfExpression : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 214 p = finish (specAlts f [
    ⟨[.call (.rule 120), .call (.tok 700), .call (.rule 120), .call (.tok 704), .call (.tok 16)], false,
      oKL 4 "cannot unpack only part of a conditional expression"⟩,
    ⟨[.call (.rule 120), .call (.tok 700), .call (.rule 120), .call (.tok 704), .call (.tok 35)], false,
      oKL 4 "cannot use dict unpacking on only part of a conditional expression"⟩] p.mark (0, 0) p.enter)

theorem invalidIfExpression_proven : InvalidIfExpression := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 214 = r214 from rfl, r214]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-! ### `invalid_kvpair_unpacking`, `invalid_kvpair` -/

/-- `invalid_kvpair_unpacking` (`Grammar/python.gram:1564-1570`), new in 3.15:
```
    | a='**' b=if_expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid double starred expression. Did you forget to wrap the conditional expression in parentheses?") }
    | a='*' b=bitwise_or ':' expression { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot use a starred expression in a dictionary key") }
    | a='**' b=bitwise_or ':' expression { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot use dict unpacking in a dictionary key") }
    | expression ':' a='*' b=bitwise_or { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot use a starred expression in a dictionary value") }
    | expression ':' a='**' b=bitwise_or { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot use dict unpacking in a dictionary value") }
```
`if_expression` 110, `bitwise_or` 135, `expression` 109. -/
def InvalidKvpairUnpacking : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 264 p = finish (specAlts f [
    ⟨[.call (.tok 35), .call (.rule 110)], false,
      oKR 0 1 "invalid double starred expression. Did you forget to wrap the conditional expression in parentheses?"⟩,
    ⟨[.call (.tok 16), .call (.rule 135), .call (.tok 11), .call (.rule 109)], false,
      oKR 0 1 "cannot use a starred expression in a dictionary key"⟩,
    ⟨[.call (.tok 35), .call (.rule 135), .call (.tok 11), .call (.rule 109)], false,
      oKR 0 1 "cannot use dict unpacking in a dictionary key"⟩,
    ⟨[.call (.rule 109), .call (.tok 11), .call (.tok 16), .call (.rule 135)], false,
      oKR 2 3 "cannot use a starred expression in a dictionary value"⟩,
    ⟨[.call (.rule 109), .call (.tok 11), .call (.tok 35), .call (.rule 135)], false,
      oKR 2 3 "cannot use dict unpacking in a dictionary value"⟩] p.mark (0, 0) p.enter)

theorem invalidKvpairUnpacking_proven : InvalidKvpairUnpacking := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 264 = r264 from rfl, r264]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

/-- `_tmp_151: '}' | ','`. -/
def Tmp151 : Prop := TokGroup 428 [26, 12]
theorem tmp151_proven : Tmp151 := tokGroup_of (by simp) rfl

def kvColonMsg : String := "':' expected after dictionary key"

/-- `RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, a->lineno, a->end_col_offset - 1,
a->end_lineno, -1, msg)` (`Parser/pegen.h:187-200`): from the last column of `a` to the end of
its last line. -/
def raisedKvColon (a : Ast) (s : PS) : PS :=
  { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno ((locOf a).endColOffset - 1)
      (locOf a).endLineno (-1) kvColonMsg s).2 with errorIndicator := true }

/-- `invalid_kvpair` (`Grammar/python.gram:1571-1576`):
```
    | a=expression !(':') {
        RAISE_ERROR_KNOWN_LOCATION(p, PyExc_SyntaxError, a->lineno, a->end_col_offset - 1, a->end_lineno, -1, "':' expected after dictionary key") }
    | expression ':' a='*' bitwise_or { RAISE_SYNTAX_ERROR_STARTING_FROM(a, "cannot use a starred expression in a dictionary value") }
    | expression ':' a='**' bitwise_or { RAISE_SYNTAX_ERROR_STARTING_FROM(a, "cannot use dict unpacking in a dictionary value") }
    | expression a=':' &('}'|',') {RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expression expected after dictionary key and ':'") }
```
-/
def InvalidKvpair : Prop := (∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  callRule (f + 2) 265 p = finish (specAlts f [
    ⟨[.call (.rule 109), .look false (.tok 11)], false,
      fun env _ s => (none, raisedKvColon (env.getD 0 .null) s)⟩,
    ⟨[.call (.rule 109), .call (.tok 11), .call (.tok 16), .call (.rule 135)], false,
      oFrom 2 "cannot use a starred expression in a dictionary value"⟩,
    ⟨[.call (.rule 109), .call (.tok 11), .call (.tok 35), .call (.rule 135)], false,
      oFrom 2 "cannot use dict unpacking in a dictionary value"⟩,
    ⟨[.call (.rule 109), .call (.tok 11), .look true (.rule 428)], false,
      oKL 1 "expression expected after dictionary key and ':'"⟩] p.mark (0, 0) p.enter)) ∧ Tmp151

theorem invalidKvpair_proven : InvalidKvpair := by
  refine ⟨fun f p he hl => ?_, tmp151_proven⟩
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 265 = r265 from rfl, r265]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) ?_
  rotate_left
  · spec_alts
  have hm : msgOf [.str (kvColonMsg.toList.map Char.toNat)] = kvColonMsg := by decide +kernel
  have hev : ∀ ex, evalA env ex (.call .RAISE_ERROR_KNOWN_LOCATION [.str "SyntaxError",
      .attr (.var 0) "lineno", .sub (.attr (.var 0) "end_col_offset") (.int 1),
      .attr (.var 0) "end_lineno", .sub (.int 0) (.int 1), .str kvColonMsg]) s =
      (.null, (raiseErrorKnownLocation "SyntaxError" (locOf (env.getD 0 .null)).lineno
        ((locOf (env.getD 0 .null)).endColOffset - 1) (locOf (env.getD 0 .null)).endLineno (-1)
        kvColonMsg s).2) := by
    intro ex
    simp (config := { decide := true }) only [evalA, evalA.evalList, bind, StateT.bind, pure,
      StateT.pure, callHelper, attrOf, List.drop_succ_cons, List.drop_zero, ↓reduceIte, hm]
    rfl
  rw [altResult_raise rfl hev (errOcc_raiseEKL _ _ _ _ _ _ _)]
  rfl

end PyLean.PyGrammar.Peg
