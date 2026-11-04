import PyLean.PyGrammar.Peg.Rules.SpecInv3

/-! More `invalid_` rules as equations (`Spec.lean`): `invalid_expression`,
`invalid_named_expression`, `invalid_comprehension`, the parameter rules (`invalid_parameters`,
`invalid_parameters_helper`, `invalid_star_etc` and their lambda twins) and
`invalid_double_starred_kvpairs`, with the groups and loops they call. Parameter rules:
`slash_no_default` 41, `slash_with_default` 42, `param_no_default` 45, `param_with_default` 47,
`param_maybe_default` 48, `param` 49, and the lambda ones 152, 153, 156, 157, 158, 159;
`double_starred_kvpair` 179, `invalid_kvpair` 265, `invalid_kvpair_unpacking` 264. Tokens
`/` 17, `STRING`, `SOFT_KEYWORD`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN(msg)`: at the token under the mark. -/
abbrev oNext (m : String) := oMsg "SyntaxError" true (fun _ => m)

/-! ### `invalid_expression` -/

/-- `_loop1_115: (!STRING expression_without_invalid)+` over `_tmp_171`; `_tmp_116: NAME STRING |
SOFT_KEYWORD`; `_tmp_117: 'else' | ':'`; `_tmp_118: pass_stmt | break_stmt | continue_stmt`. -/
def Tmp171 : Prop := PlainSpec 448 [⟨[.look false .string, .call (.rule 210)], false, oVar0⟩]
theorem tmp171_proven : Tmp171 := by plain_spec
def Loop1_115 : Prop := Loop1Over 392 448
theorem loop1_115_proven : Loop1_115 := loop1Over_of rfl
def Tmp116 : Prop := PlainSpec 393 [⟨[.call .name, .call .string], false, oDummy⟩,
  ⟨[.call .softKeywordToken], false, oVar0⟩]
theorem tmp116_proven : Tmp116 := by plain_spec
def Tmp117 : Prop := TokGroup 394 [704, 11]
theorem tmp117_proven : Tmp117 := tokGroup_of (by simp) rfl
def Tmp118 : Prop := PlainSpec 395 [⟨[.call (.rule 16)], false, oVar0⟩, ⟨[.call (.rule 17)], false, oVar0⟩,
  ⟨[.call (.rule 18)], false, oVar0⟩]
theorem tmp118_proven : Tmp118 := by plain_spec

/-- `invalid_expression` (`Grammar/python.gram:1263-1279`):
```
   |  STRING a=(!STRING expression_without_invalid)+ STRING {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE( PyPegen_first_item(a, expr_ty), PyPegen_last_item(a, expr_ty),
        "invalid syntax. Is this intended to be part of the string?") }
   | !(NAME STRING | SOFT_KEYWORD) a=disjunction b=expression_without_invalid {
        _PyPegen_raise_error_for_missing_comma(p, a, b) }
   | a=disjunction 'if' b=disjunction !('else'|':') { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "expected 'else' after 'if' expression") }
   | a=disjunction 'if' b=disjunction 'else' !expression {
        RAISE_SYNTAX_ERROR_ON_NEXT_TOKEN("expected expression after 'else', but statement is given") }
   | a[stmt_ty]=(pass_stmt|break_stmt|continue_stmt) 'if' b=disjunction 'else' c=simple_stmt {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION (a, "expected expression before 'if', but statement is given") }
   | a='lambda' [lambda_params] b=':' &FSTRING_MIDDLE  {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "f-string: lambda expressions are not allowed without parentheses") }
   | a='lambda' [lambda_params] b=':' &TSTRING_MIDDLE  {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "t-string: lambda expressions are not allowed without parentheses") }
```
The second alternative's action is `_PyPegen_raise_error_for_missing_comma` (`raiseErrorForMissingComma`,
its own entry `pygrammar-peg-missing-comma`). -/
def InvalidExpression : Prop := PlainSpec 213 [
  ⟨[.call .string, .call (.rule 392), .call .string], false, fun env _ s =>
    (none, raisedAt ((seqOf (env.getD 1 .null)).headD .null) ((seqOf (env.getD 1 .null)).getLastD .null)
      "invalid syntax. Is this intended to be part of the string?" s)⟩,
  ⟨[.look false (.rule 393), .call (.rule 120), .call (.rule 210)], false, fun env _ s =>
    pureRes (raiseErrorForMissingComma (env.getD 0 .null) (env.getD 1 .null) s).1
      (raiseErrorForMissingComma (env.getD 0 .null) (env.getD 1 .null) s).2⟩,
  ⟨[.call (.rule 120), .call (.tok 700), .call (.rule 120), .look false (.rule 394)], false,
    oKR 0 2 "expected 'else' after 'if' expression"⟩,
  ⟨[.call (.rule 120), .call (.tok 700), .call (.rule 120), .call (.tok 704), .look false (.rule 109)], false,
    oNext "expected expression after 'else', but statement is given"⟩,
  ⟨[.call (.rule 395), .call (.tok 700), .call (.rule 120), .call (.tok 704), .call (.rule 9)], false,
    oKL 0 "expected expression before 'if', but statement is given"⟩,
  ⟨[.call (.tok 622), .opt (.rule 150), .call (.tok 11), .look true (.tok 60)], false,
    oKR 0 2 "f-string: lambda expressions are not allowed without parentheses"⟩,
  ⟨[.call (.tok 622), .opt (.rule 150), .call (.tok 11), .look true (.tok 63)], false,
    oKR 0 2 "t-string: lambda expressions are not allowed without parentheses"⟩]
def InvalidExpressionRule : Prop :=
  InvalidExpression ∧ Loop1_115 ∧ Tmp171 ∧ Tmp116 ∧ Tmp117 ∧ Tmp118
theorem invalidExpressionRule_proven : InvalidExpressionRule :=
  ⟨by plain_spec, loop1_115_proven, tmp171_proven, tmp116_proven, tmp117_proven, tmp118_proven⟩

/-! ### `invalid_named_expression` -/

/-- `_tmp_119: '=' | ':='`; `_tmp_120: list | tuple | genexp | 'True' | 'None' | 'False'`. -/
def Tmp119 : Prop := TokGroup 396 [22, 53]
theorem tmp119_proven : Tmp119 := tokGroup_of (by simp) rfl
def Tmp120 : Prop := PlainSpec 397 [⟨[.call (.rule 174)], false, oVar0⟩, ⟨[.call (.rule 175)], false, oVar0⟩,
  ⟨[.call (.rule 185)], false, oVar0⟩, ⟨[.call (.tok 627)], false, oVar0⟩, ⟨[.call (.tok 628)], false, oVar0⟩,
  ⟨[.call (.tok 629)], false, oVar0⟩]
theorem tmp120_proven : Tmp120 := by plain_spec

/-- `invalid_named_expression(memo)` (`Grammar/python.gram:1287-1295`):
```
    | a=expression ':=' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use assignment expressions with %s", _PyPegen_get_expr_name(a)) }
    | a=NAME '=' b=bitwise_or !('='|':=') {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?") }
    | !(list|tuple|genexp|'True'|'None'|'False') a=bitwise_or b='=' bitwise_or !('='|':=') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot assign to %s here. Maybe you meant '==' instead of '='?",
                                          _PyPegen_get_expr_name(a)) }
```
A `(memo)` rule: at a position with no memo entry the result is memoized. -/
def InvalidNamedExpression : Prop := MemoSpec 215 [
  ⟨[.call (.rule 109), .call (.tok 53), .call (.rule 109)], false,
    oKLName 0 "cannot use assignment expressions with " ""⟩,
  ⟨[.call .name, .call (.tok 22), .call (.rule 135), .look false (.rule 396)], false, oKR 0 2 eqMsg⟩,
  ⟨[.look false (.rule 397), .call (.rule 135), .call (.tok 22), .call (.rule 135), .look false (.rule 396)], false,
    oKLName 0 "cannot assign to " " here. Maybe you meant '==' instead of '='?"⟩]
def InvalidNamedExpressionRule : Prop := InvalidNamedExpression ∧ Tmp119 ∧ Tmp120
theorem invalidNamedExpressionRule_proven : InvalidNamedExpressionRule :=
  ⟨by memo_spec, tmp119_proven, tmp120_proven⟩

/-! ### `invalid_comprehension` -/

/-- `_tmp_123: '[' | '{'`. -/
def Tmp123 : Prop := TokGroup 400 [9, 25]
theorem tmp123_proven : Tmp123 := tokGroup_of (by simp) rfl

def compParenMsg : String := "did you forget parentheses around the comprehension target?"

/-- `invalid_comprehension` (`Grammar/python.gram:1350-1359`):
```
    | '[' a='**' b=expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot use dict unpacking in list comprehension") }
    | '(' a='**' b=expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot use dict unpacking in generator expression") }
    | ('[' | '{') a=star_named_expression ',' b=star_named_expressions for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, PyPegen_last_item(b, expr_ty),
        "did you forget parentheses around the comprehension target?") }
    | ('[' | '{') a=star_named_expression b=',' for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "did you forget parentheses around the comprehension target?") }
```
-/
def InvalidComprehension : Prop := PlainSpec 222 [
  ⟨[.call (.tok 9), .call (.tok 35), .call (.rule 109), .call (.rule 181)], false,
    oKR 1 2 "cannot use dict unpacking in list comprehension"⟩,
  ⟨[.call (.tok 7), .call (.tok 35), .call (.rule 109), .call (.rule 181)], false,
    oKR 1 2 "cannot use dict unpacking in generator expression"⟩,
  ⟨[.call (.rule 400), .call (.rule 116), .call (.tok 12), .call (.rule 114), .call (.rule 181)], false,
    fun env _ s => (none, raisedAt (env.getD 1 .null) ((seqOf (env.getD 3 .null)).getLastD .null) compParenMsg s)⟩,
  ⟨[.call (.rule 400), .call (.rule 116), .call (.tok 12), .call (.rule 181)], false, oKR 1 2 compParenMsg⟩]
def InvalidComprehensionRule : Prop := InvalidComprehension ∧ Tmp123
theorem invalidComprehensionRule_proven : InvalidComprehensionRule := ⟨by plain_spec, tmp123_proven⟩

/-! ### Parameters -/

/-- The groups and loops of the parameter rules: `_tmp_124: slash_no_default |
slash_with_default`, `_loop0_31: param_maybe_default*`, `_loop0_27: param_no_default*`,
`_loop1_29: param_no_default+`, `_tmp_125: ',' | param_no_default`, `_loop1_32:
param_maybe_default+`, `_tmp_127: ')' | ',' (')' | '**')` with `_tmp_172: ')' | '**'`, `_tmp_128:
param_no_default | ','`, `_loop1_30: param_with_default+`; and the lambda twins `_tmp_130`,
`_loop0_76`, `_loop0_72`, `_gather_132` (`','.lambda_param+`), `_tmp_133`, `_loop1_77`,
`_tmp_134: ':' | ',' (':' | '**')` with `_tmp_173: ':' | '**'`, `_tmp_135`, `_loop1_75`. -/
def ParamGroups : Prop :=
  PlainSpec 401 [⟨[.call (.rule 41)], false, oVar0⟩, ⟨[.call (.rule 42)], false, oVar0⟩] ∧
  Loop0Over 308 48 ∧ Loop0Over 304 45 ∧ Loop1Over 306 45 ∧
  PlainSpec 402 [⟨[.call (.tok 12)], false, oVar0⟩, ⟨[.call (.rule 45)], false, oVar0⟩] ∧
  Loop1Over 309 48 ∧
  PlainSpec 404 [⟨[.call (.tok 8)], false, oVar0⟩, ⟨[.call (.tok 12), .call (.rule 449)], false, oDummy⟩] ∧
  TokGroup 449 [8, 35] ∧
  PlainSpec 405 [⟨[.call (.rule 45)], false, oVar0⟩, ⟨[.call (.tok 12)], false, oVar0⟩] ∧
  Loop1Over 307 47
def LambdaParamGroups : Prop :=
  PlainSpec 407 [⟨[.call (.rule 152)], false, oVar0⟩, ⟨[.call (.rule 153)], false, oVar0⟩] ∧
  Loop0Over 353 158 ∧ Loop0Over 349 156 ∧ GatherSep 409 408 159 ∧
  PlainSpec 410 [⟨[.call (.tok 12)], false, oVar0⟩, ⟨[.call (.rule 156)], false, oVar0⟩] ∧
  Loop1Over 354 158 ∧
  PlainSpec 411 [⟨[.call (.tok 11)], false, oVar0⟩, ⟨[.call (.tok 12), .call (.rule 450)], false, oDummy⟩] ∧
  TokGroup 450 [11, 35] ∧
  PlainSpec 412 [⟨[.call (.rule 156)], false, oVar0⟩, ⟨[.call (.tok 12)], false, oVar0⟩] ∧
  Loop1Over 352 157

theorem paramGroups_proven : ParamGroups :=
  ⟨by plain_spec, loop0Over_of rfl, loop0Over_of rfl, loop1Over_of rfl, by plain_spec, loop1Over_of rfl,
    by plain_spec, tokGroup_of (by simp) rfl, by plain_spec, loop1Over_of rfl⟩
theorem lambdaParamGroups_proven : LambdaParamGroups :=
  ⟨by plain_spec, loop0Over_of rfl, loop0Over_of rfl, gatherSep_of rfl rfl, by plain_spec, loop1Over_of rfl,
    by plain_spec, tokGroup_of (by simp) rfl, by plain_spec, loop1Over_of rfl⟩

/-- `invalid_parameters` (`Grammar/python.gram:1360-1372`):
```
    | a="/" ',' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "at least one parameter must precede /") }
    | (slash_no_default | slash_with_default) param_maybe_default* a='/' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "/ may appear only once") }
    | slash_no_default? param_no_default* invalid_parameters_helper a=param_no_default {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "parameter without a default follows parameter with a default") }
    | param_no_default* a='(' param_no_default+ ','? b=')' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "Function parameters cannot be parenthesized") }
    | (slash_no_default | slash_with_default)? param_maybe_default* '*' (',' | param_no_default) param_maybe_default* a='/' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "/ must be ahead of *") }
    | param_maybe_default+ '/' a='*' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expected comma between / and *") }
```
`invalid_lambda_parameters` (1388-1400) is the same with the lambda rules, except that its
parenthesized alternative takes `','.lambda_param+` and says "Lambda expression parameters
cannot be parenthesized". -/
def InvalidParametersOf (id snd loop0md loop0nd helper pnd parens slashGroup tmpComma loop1md : Nat)
    (parenMsg : String) : Prop := PlainSpec id [
  ⟨[.call (.tok 17), .call (.tok 12)], false, oKL 0 "at least one parameter must precede /"⟩,
  ⟨[.call (.rule slashGroup), .call (.rule loop0md), .call (.tok 17)], false, oKL 2 "/ may appear only once"⟩,
  ⟨[.opt (.rule snd), .call (.rule loop0nd), .call (.rule helper), .call (.rule pnd)], false,
    oKL 3 "parameter without a default follows parameter with a default"⟩,
  ⟨[.call (.rule loop0nd), .call (.tok 7), .call (.rule parens), .opt (.tok 12), .call (.tok 8)], false,
    oKR 1 4 parenMsg⟩,
  ⟨[.opt (.rule slashGroup), .call (.rule loop0md), .call (.tok 16), .call (.rule tmpComma), .call (.rule loop0md),
    .call (.tok 17)], false, oKL 5 "/ must be ahead of *"⟩,
  ⟨[.call (.rule loop1md), .call (.tok 17), .call (.tok 16)], false, oKL 2 "expected comma between / and *"⟩]

def InvalidParameters : Prop :=
  InvalidParametersOf 223 41 308 304 227 45 306 401 402 309 "Function parameters cannot be parenthesized" ∧
  ParamGroups
def InvalidLambdaParameters : Prop :=
  InvalidParametersOf 228 152 353 349 229 156 409 407 410 354
    "Lambda expression parameters cannot be parenthesized" ∧ LambdaParamGroups
theorem invalidParameters_proven : InvalidParameters := ⟨by plain_spec, paramGroups_proven⟩
theorem invalidLambdaParameters_proven : InvalidLambdaParameters := ⟨by plain_spec, lambdaParamGroups_proven⟩

/-- `invalid_parameters_helper` (`Grammar/python.gram:1385-1387`), and
`invalid_lambda_parameters_helper` (1401-1403) with the lambda rules:
```
    | a=slash_with_default { _PyPegen_singleton_seq(p, a) }
    | param_with_default+
```
-/
def InvalidParametersHelperOf (id swd loop1wd : Nat) : Prop := PlainSpec id [
  ⟨[.call (.rule swd)], false, oPure (fun env => .seq [env.getD 0 .null])⟩,
  ⟨[.call (.rule loop1wd)], false, oVar0⟩]
def InvalidParametersHelper : Prop := InvalidParametersHelperOf 227 42 307 ∧ Loop1Over 307 47
def InvalidLambdaParametersHelper : Prop := InvalidParametersHelperOf 229 153 352 ∧ Loop1Over 352 157
theorem invalidParametersHelper_proven : InvalidParametersHelper := ⟨by plain_spec, loop1Over_of rfl⟩
theorem invalidLambdaParametersHelper_proven : InvalidLambdaParametersHelper :=
  ⟨by plain_spec, loop1Over_of rfl⟩

/-- `invalid_star_etc` (`Grammar/python.gram:1375-1380`):
```
    | a='*' (')' | ',' (')' | '**')) { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "named parameters must follow bare *") }
    | '*' ',' TYPE_COMMENT { RAISE_SYNTAX_ERROR("bare * has associated type comment") }
    | '*' param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-positional parameter cannot have default value") }
    | '*' (param_no_default | ',') param_maybe_default* a='*' (param_no_default | ',') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "* may appear only once") }
```
-/
def InvalidStarEtc : Prop := PlainSpec 225 [
  ⟨[.call (.tok 16), .call (.rule 404)], false, oKL 0 "named parameters must follow bare *"⟩,
  ⟨[.call (.tok 16), .call (.tok 12), .call (.tok 57)], false, oSyn "bare * has associated type comment"⟩,
  ⟨[.call (.tok 16), .call (.rule 49), .call (.tok 22)], false,
    oKL 2 "var-positional parameter cannot have default value"⟩,
  ⟨[.call (.tok 16), .call (.rule 405), .call (.rule 308), .call (.tok 16), .call (.rule 405)], false,
    oKL 3 "* may appear only once"⟩]
def InvalidStarEtcRule : Prop := InvalidStarEtc ∧ ParamGroups
theorem invalidStarEtcRule_proven : InvalidStarEtcRule := ⟨by plain_spec, paramGroups_proven⟩

/-- `invalid_lambda_star_etc` (`Grammar/python.gram:1404-1408`):
```
    | '*' (':' | ',' (':' | '**')) { RAISE_SYNTAX_ERROR("named parameters must follow bare *") }
    | '*' lambda_param a='=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "var-positional parameter cannot have default value") }
    | '*' (lambda_param_no_default | ',') lambda_param_maybe_default* a='*' (lambda_param_no_default | ',') {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "* may appear only once") }
```
Unlike `invalid_star_etc`, the first message is located at the last token read, not at the `*`. -/
def InvalidLambdaStarEtc : Prop := PlainSpec 230 [
  ⟨[.call (.tok 16), .call (.rule 411)], false, oSyn "named parameters must follow bare *"⟩,
  ⟨[.call (.tok 16), .call (.rule 159), .call (.tok 22)], false,
    oKL 2 "var-positional parameter cannot have default value"⟩,
  ⟨[.call (.tok 16), .call (.rule 412), .call (.rule 353), .call (.tok 16), .call (.rule 412)], false,
    oKL 3 "* may appear only once"⟩]
def InvalidLambdaStarEtcRule : Prop := InvalidLambdaStarEtc ∧ LambdaParamGroups
theorem invalidLambdaStarEtcRule_proven : InvalidLambdaStarEtcRule :=
  ⟨by plain_spec, lambdaParamGroups_proven⟩

/-! ### `invalid_double_starred_kvpairs` -/

/-- `_gather_86: ','.double_starred_kvpair+`; `_tmp_150: invalid_kvpair | invalid_kvpair_unpacking`
(both `invalid_`, so second pass only). -/
def Gather86 : Prop := GatherSep 363 362 179
theorem gather86_proven : Gather86 := gatherSep_of rfl rfl
def Tmp150 : Prop := PlainSpec 427 [⟨[.call (.rule 265)], true, oVar0⟩, ⟨[.call (.rule 264)], true, oVar0⟩]
theorem tmp150_proven : Tmp150 := by plain_spec

/-- `invalid_double_starred_kvpairs` (`Grammar/python.gram:1560-1563`):
```
    | invalid_kvpair_unpacking [',']
    | ','.double_starred_kvpair+ ',' (invalid_kvpair | invalid_kvpair_unpacking)
    | expression a=':' &('}'|',') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expression expected after dictionary key and ':'") }
```
The first two alternatives have no action (the dummy result when their `invalid_` rule matched
without raising). -/
def InvalidDoubleStarredKvpairs : Prop := PlainSpec 263 [
  ⟨[.call (.rule 264), .opt (.tok 12)], false, oDummy⟩,
  ⟨[.call (.rule 363), .call (.tok 12), .call (.rule 427)], false, oDummy⟩,
  ⟨[.call (.rule 109), .call (.tok 11), .look true (.rule 428)], false,
    oKL 1 "expression expected after dictionary key and ':'"⟩]
def InvalidDoubleStarredKvpairsRule : Prop := InvalidDoubleStarredKvpairs ∧ Gather86 ∧ Tmp150 ∧ Tmp151
theorem invalidDoubleStarredKvpairsRule_proven : InvalidDoubleStarredKvpairsRule :=
  ⟨by plain_spec, gather86_proven, tmp150_proven, tmp151_proven⟩

end PyLean.PyGrammar.Peg
