import PyLean.PyGrammar.Peg.Rules.SpecInv1

/-! The statement-level `invalid_` rules as equations (`Spec.lean`), with their exact messages
and locations, and the groups, loops and gathers they call. Keywords: `if` 700, `elif` 705,
`else` 704, `while` 707, `for` 712, `in` 713, `async` 716, `def` 717, `class` 719, `try` 674,
`finally` 691, `except` 695, `as` 698, `with` 665, `from` 650, `import` 651; soft keywords
`match` [109, 97, 116, 99, 104], `case` [99, 97, 115, 101], `lazy` [108, 97, 122, 121], `_` [95];
tokens `NEWLINE` 4, `INDENT` 5, `(` 7, `)` 8, `:` 11, `,` 12, `*` 16, `.` 23, `{` 25, `}` 26,
`->` 51, `...` 52. Rules: `named_expression` 119, `block` 33, `star_targets` 193,
`star_expressions` 112, `expression` 109, `expressions` 108, `NAME`, `type_params` 102, `params`
39, `arguments` 187, `func_type_comment` 207, `subject_expr` 66, `patterns` 69, `guard` 68,
`except_block` 62, `except_star_block` 63, `bitwise_or` 135, `star_target` 196, `dotted_name`
32, `import_from_targets` 27, `import_from_as_names` 28, `or_pattern` 72, `name_or_attr` 86,
`items_pattern` 94, `double_star_pattern` 96, `positional_patterns` 98, `keyword_patterns` 99. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Groups, loops and gathers -/

/-- `_tmp_21: 'as' z=NAME { z }`. -/
def Tmp21 : Prop := PlainSpec 298 [⟨[.call (.tok 698), .call .name], false, oVar 1⟩]
theorem tmp21_proven : Tmp21 := by plain_spec

/-- `_tmp_144: 'except' | 'finally'`. -/
def Tmp144 : Prop := TokGroup 421 [695, 691]
theorem tmp144_proven : Tmp144 := tokGroup_of (by simp) rfl

/-- `_loop0_145: block*`. -/
def Loop0_145 : Prop := Loop0Over 422 33
theorem loop0_145_proven : Loop0_145 := loop0Over_of rfl

/-- `_loop1_36: except_block+`, `_loop1_37: except_star_block+`. -/
def Loop1_36 : Prop := Loop1Over 313 62
theorem loop1_36_proven : Loop1_36 := loop1Over_of rfl
def Loop1_37 : Prop := Loop1Over 314 63
theorem loop1_37_proven : Loop1_37 := loop1Over_of rfl

/-- `_tmp_146: expression ['as' NAME]`. -/
def Tmp146 : Prop := PlainSpec 423 [⟨[.call (.rule 109), .opt (.rule 298)], false, oDummy⟩]
theorem tmp146_proven : Tmp146 := by plain_spec

/-- `_tmp_147: NEWLINE | ':'`. -/
def Tmp147 : Prop := TokGroup 424 [4, 11]
theorem tmp147_proven : Tmp147 := tokGroup_of (by simp) rfl

/-- `_tmp_180: 'as' star_target`, `_tmp_176: expression ['as' star_target]`,
`_tmp_177: expressions ['as' star_target]`, and their `','.x+` gathers `_gather_141` (`_loop0_140`)
and `_gather_143` (`_loop0_142`). -/
def Tmp180 : Prop := PlainSpec 457 [⟨[.call (.tok 698), .call (.rule 196)], false, oDummy⟩]
theorem tmp180_proven : Tmp180 := by plain_spec
def Tmp176 : Prop := PlainSpec 453 [⟨[.call (.rule 109), .opt (.rule 457)], false, oDummy⟩]
theorem tmp176_proven : Tmp176 := by plain_spec
def Tmp177 : Prop := PlainSpec 454 [⟨[.call (.rule 108), .opt (.rule 457)], false, oDummy⟩]
theorem tmp177_proven : Tmp177 := by plain_spec
def Gather141 : Prop := GatherSep 418 417 453
theorem gather141_proven : Gather141 := gatherSep_of rfl rfl
def Gather143 : Prop := GatherSep 420 419 454
theorem gather143_proven : Gather143 := gatherSep_of rfl rfl

/-- `_tmp_25: '(' z=[arguments] ')' { z }`, `_tmp_26: '->' z=expression { z }`. -/
def Tmp25 : Prop := PlainSpec 302 [⟨[.call (.tok 7), .opt (.rule 187), .call (.tok 8)], false, oVar 1⟩]
theorem tmp25_proven : Tmp25 := by plain_spec
def Tmp26 : Prop := PlainSpec 303 [⟨[.call (.tok 51), .call (.rule 109)], false, oVar 1⟩]
theorem tmp26_proven : Tmp26 := by plain_spec

/-- `_tmp_136: bitwise_or (',' bitwise_or)* [',']`, with `_loop0_174` over `_tmp_179`. -/
def Tmp179 : Prop := PlainSpec 456 [⟨[.call (.tok 12), .call (.rule 135)], false, oDummy⟩]
theorem tmp179_proven : Tmp179 := by plain_spec
def Loop0_174 : Prop := Loop0Over 451 456
theorem loop0_174_proven : Loop0_174 := loop0Over_of rfl
def Tmp136 : Prop := PlainSpec 413 [⟨[.call (.rule 135), .call (.rule 451), .opt (.tok 12)], false, oDummy⟩]
theorem tmp136_proven : Tmp136 := by plain_spec

/-- `_tmp_35: ',' | ')' | ':'`. -/
def Tmp35 : Prop := TokGroup 312 [12, 8, 11]
theorem tmp35_proven : Tmp35 := tokGroup_of (by simp) rfl

/-- `_loop0_17: ('.' | '...')*` over `_tmp_160`. -/
def Tmp160 : Prop := TokGroup 437 [23, 52]
theorem tmp160_proven : Tmp160 := tokGroup_of (by simp) rfl
def Loop0_17 : Prop := Loop0Over 294 437
theorem loop0_17_proven : Loop0_17 := loop0Over_of rfl

/-- `_tmp_148: items_pattern ','`, `_tmp_149: positional_patterns ','`. -/
def Tmp148 : Prop := PlainSpec 425 [⟨[.call (.rule 94), .call (.tok 12)], false, oDummy⟩]
theorem tmp148_proven : Tmp148 := by plain_spec
def Tmp149 : Prop := PlainSpec 426 [⟨[.call (.rule 98), .call (.tok 12)], false, oDummy⟩]
theorem tmp149_proven : Tmp149 := by plain_spec

/-! ### `if`, `elif`, `else`, `while`, `for`, `def`, `class` -/

/-- `invalid_if_stmt` (`Grammar/python.gram:1531-1534`):
```
    | 'if' named_expression NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='if' a=named_expression ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'if' statement on line %d", a->lineno) }
```
(`a` is bound twice; pegen names the second `a_1`, so `a->lineno` is the `if` token's line,
`Parser/parser.c:26196`.) -/
def InvalidIfStmt : Prop := PlainSpec 256 [
  ⟨[.call (.tok 700), .call (.rule 119), .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.call (.tok 700), .call (.rule 119), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'if' statement on line " 0⟩]
theorem invalidIfStmt_proven : InvalidIfStmt := by plain_spec

/-- `invalid_elif_stmt` (`Grammar/python.gram:1535-1538`), as `invalid_if_stmt` with `elif`. -/
def InvalidElifStmt : Prop := PlainSpec 257 [
  ⟨[.call (.tok 705), .call (.rule 119), .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.call (.tok 705), .call (.rule 119), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'elif' statement on line " 0⟩]
theorem invalidElifStmt_proven : InvalidElifStmt := by plain_spec

/-- `invalid_else_stmt` (`Grammar/python.gram:1539-1542`):
```
    | a='else' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'else' statement on line %d", a->lineno) }
    | 'else' ':' block 'elif' { RAISE_SYNTAX_ERROR("'elif' block follows an 'else' block")}
```
-/
def InvalidElseStmt : Prop := PlainSpec 258 [
  ⟨[.call (.tok 704), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'else' statement on line " 0⟩,
  ⟨[.call (.tok 704), .call (.tok 11), .call (.rule 33), .call (.tok 705)], false,
    oSyn "'elif' block follows an 'else' block"⟩]
theorem invalidElseStmt_proven : InvalidElseStmt := by plain_spec

/-- `invalid_while_stmt` (`Grammar/python.gram:1543-1546`), as `invalid_if_stmt` with `while`. -/
def InvalidWhileStmt : Prop := PlainSpec 259 [
  ⟨[.call (.tok 707), .call (.rule 119), .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.call (.tok 707), .call (.rule 119), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'while' statement on line " 0⟩]
theorem invalidWhileStmt_proven : InvalidWhileStmt := by plain_spec

/-- `invalid_for_stmt` (`Grammar/python.gram:1547-1550`):
```
    | ['async'] 'for' star_targets 'in' star_expressions NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | ['async'] a='for' star_targets 'in' star_expressions ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'for' statement on line %d", a->lineno) }
```
The line is that of `for` (value 1, after the optional `async`). -/
def InvalidForStmt : Prop := PlainSpec 260 [
  ⟨[.opt (.tok 716), .call (.tok 712), .call (.rule 193), .call (.tok 713), .call (.rule 112),
    .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.opt (.tok 716), .call (.tok 712), .call (.rule 193), .call (.tok 713), .call (.rule 112),
    .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'for' statement on line " 1⟩]
theorem invalidForStmt_proven : InvalidForStmt := by plain_spec

/-- `invalid_def_raw` (`Grammar/python.gram:1551-1554`):
```
    | ['async'] a='def' NAME [type_params] '(' [params] ')' ['->' expression] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after function definition on line %d", a->lineno) }
    | ['async'] 'def' NAME [type_params] &&'(' [params] ')' ['->' expression] &&':' [func_type_comment] block
```
The second alternative has no action: the dummy result (a matched `def` with its block), so
that `function_def_raw`'s `invalid_def_raw` alternative succeeds; its forced `(` and `:` raise
"expected '('" and "expected ':'". `['->' expression]` is `_tmp_26` (303). -/
def InvalidDefRaw : Prop := PlainSpec 261 [
  ⟨[.opt (.tok 716), .call (.tok 717), .call .name, .opt (.rule 102), .call (.tok 7), .opt (.rule 39),
    .call (.tok 8), .opt (.rule 303), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after function definition on line " 1⟩,
  ⟨[.opt (.tok 716), .call (.tok 717), .call .name, .opt (.rule 102), .call (.forcedTok 7 "("),
    .opt (.rule 39), .call (.tok 8), .opt (.rule 303), .call (.forcedTok 11 ":"), .opt (.rule 207),
    .call (.rule 33)], false, oDummy⟩]
def InvalidDefRawRule : Prop := InvalidDefRaw ∧ Tmp26
theorem invalidDefRawRule_proven : InvalidDefRawRule := ⟨by plain_spec, tmp26_proven⟩

/-- `invalid_class_def_raw` (`Grammar/python.gram:1555-1558`):
```
    | 'class' NAME [type_params] ['(' [arguments] ')'] NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='class' NAME [type_params] ['(' [arguments] ')'] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after class definition on line %d", a->lineno) }
```
`['(' [arguments] ')']` is `_tmp_25` (302). -/
def InvalidClassDefRaw : Prop := PlainSpec 262 [
  ⟨[.call (.tok 719), .call .name, .opt (.rule 102), .opt (.rule 302), .call (.tok 4)], false,
    oSyn "expected ':'"⟩,
  ⟨[.call (.tok 719), .call .name, .opt (.rule 102), .opt (.rule 302), .call (.tok 11), .call (.tok 4),
    .look false (.tok 5)], false, oIndent "expected an indented block after class definition on line " 0⟩]
def InvalidClassDefRawRule : Prop := InvalidClassDefRaw ∧ Tmp25
theorem invalidClassDefRawRule_proven : InvalidClassDefRawRule := ⟨by plain_spec, tmp25_proven⟩

/-! ### `try`, `except`, `except*`, `finally` -/

/-- `invalid_try_stmt` (`Grammar/python.gram:1469-1476`):
```
    | a='try' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'try' statement on line %d", a->lineno) }
    | 'try' ':' block !('except' | 'finally') { RAISE_SYNTAX_ERROR("expected 'except' or 'finally' block") }
    | 'try' ':' block* except_block+ a='except' b='*' expression ['as' NAME] ':' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot have both 'except' and 'except*' on the same 'try'") }
    | 'try' ':' block* except_star_block+ a='except' [expression ['as' NAME]] ':' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot have both 'except' and 'except*' on the same 'try'") }
```
Groups: `_tmp_144` (421) `'except' | 'finally'`, `_loop0_145` (422) `block*`, `_loop1_36` (313)
and `_loop1_37` (314), `_tmp_21` (298) `'as' NAME`, `_tmp_146` (423). -/
def InvalidTryStmt : Prop := PlainSpec 244 [
  ⟨[.call (.tok 674), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'try' statement on line " 0⟩,
  ⟨[.call (.tok 674), .call (.tok 11), .call (.rule 33), .look false (.rule 421)], false,
    oSyn "expected 'except' or 'finally' block"⟩,
  ⟨[.call (.tok 674), .call (.tok 11), .call (.rule 422), .call (.rule 313), .call (.tok 695),
    .call (.tok 16), .call (.rule 109), .opt (.rule 298), .call (.tok 11)], false,
    oKR 4 5 "cannot have both 'except' and 'except*' on the same 'try'"⟩,
  ⟨[.call (.tok 674), .call (.tok 11), .call (.rule 422), .call (.rule 314), .call (.tok 695),
    .opt (.rule 423), .call (.tok 11)], false,
    oKL 4 "cannot have both 'except' and 'except*' on the same 'try'"⟩]
def InvalidTryStmtRule : Prop := InvalidTryStmt ∧ Tmp144 ∧ Loop0_145 ∧ Loop1_36 ∧ Loop1_37 ∧ Tmp21 ∧ Tmp146
theorem invalidTryStmtRule_proven : InvalidTryStmtRule :=
  ⟨by plain_spec, tmp144_proven, loop0_145_proven, loop1_36_proven, loop1_37_proven, tmp21_proven,
    tmp146_proven⟩

/-- `invalid_except_stmt` (`Grammar/python.gram:1477-1484`):
```
    | 'except' a=expression ',' expressions 'as' NAME  ':' {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "multiple exception types must be parenthesized when using 'as'") }
    | a='except' expression ['as' NAME ] NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='except' NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | 'except' expression 'as' a=expression ':' block {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use except statement with %s", _PyPegen_get_expr_name(a)) }
```
-/
def InvalidExceptStmt : Prop := PlainSpec 245 [
  ⟨[.call (.tok 695), .call (.rule 109), .call (.tok 12), .call (.rule 108), .call (.tok 698), .call .name,
    .call (.tok 11)], false, oFrom 1 "multiple exception types must be parenthesized when using 'as'"⟩,
  ⟨[.call (.tok 695), .call (.rule 109), .opt (.rule 298), .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.call (.tok 695), .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.call (.tok 695), .call (.rule 109), .call (.tok 698), .call (.rule 109), .call (.tok 11),
    .call (.rule 33)], false, oKLName 3 "cannot use except statement with " ""⟩]
def InvalidExceptStmtRule : Prop := InvalidExceptStmt ∧ Tmp21
theorem invalidExceptStmtRule_proven : InvalidExceptStmtRule := ⟨by plain_spec, tmp21_proven⟩

/-- `invalid_except_star_stmt` (`Grammar/python.gram:1485-1492`):
```
    | 'except' '*' a=expression ',' expressions 'as' NAME  ':' {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "multiple exception types must be parenthesized when using 'as'") }
    | a='except' '*' expression ['as' NAME ] NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a='except' '*' (NEWLINE | ':') { RAISE_SYNTAX_ERROR("expected one or more exception types") }
    | 'except' '*' expression 'as' a=expression ':' block {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use except* statement with %s", _PyPegen_get_expr_name(a)) }
```
`(NEWLINE | ':')` is `_tmp_147` (424). -/
def InvalidExceptStarStmt : Prop := PlainSpec 246 [
  ⟨[.call (.tok 695), .call (.tok 16), .call (.rule 109), .call (.tok 12), .call (.rule 108),
    .call (.tok 698), .call .name, .call (.tok 11)], false,
    oFrom 2 "multiple exception types must be parenthesized when using 'as'"⟩,
  ⟨[.call (.tok 695), .call (.tok 16), .call (.rule 109), .opt (.rule 298), .call (.tok 4)], false,
    oSyn "expected ':'"⟩,
  ⟨[.call (.tok 695), .call (.tok 16), .call (.rule 424)], false,
    oSyn "expected one or more exception types"⟩,
  ⟨[.call (.tok 695), .call (.tok 16), .call (.rule 109), .call (.tok 698), .call (.rule 109),
    .call (.tok 11), .call (.rule 33)], false, oKLName 4 "cannot use except* statement with " ""⟩]
def InvalidExceptStarStmtRule : Prop := InvalidExceptStarStmt ∧ Tmp21 ∧ Tmp147
theorem invalidExceptStarStmtRule_proven : InvalidExceptStarStmtRule :=
  ⟨by plain_spec, tmp21_proven, tmp147_proven⟩

/-- `invalid_finally_stmt: a='finally' ':' NEWLINE !INDENT { RAISE_INDENTATION_ERROR("expected an
indented block after 'finally' statement on line %d", a->lineno) }` (`Grammar/python.gram:1493-1495`). -/
def InvalidFinallyStmt : Prop := PlainSpec 247 [
  ⟨[.call (.tok 691), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'finally' statement on line " 0⟩]
theorem invalidFinallyStmt_proven : InvalidFinallyStmt := by plain_spec

/-- `invalid_except_stmt_indent` (`Grammar/python.gram:1496-1499`):
```
    | a='except' expression ['as' NAME ] ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'except' statement on line %d", a->lineno) }
    | a='except' ':' NEWLINE !INDENT { RAISE_INDENTATION_ERROR("expected an indented block after 'except' statement on line %d", a->lineno) }
```
-/
def InvalidExceptStmtIndent : Prop := PlainSpec 248 [
  ⟨[.call (.tok 695), .call (.rule 109), .opt (.rule 298), .call (.tok 11), .call (.tok 4),
    .look false (.tok 5)], false, oIndent "expected an indented block after 'except' statement on line " 0⟩,
  ⟨[.call (.tok 695), .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'except' statement on line " 0⟩]
def InvalidExceptStmtIndentRule : Prop := InvalidExceptStmtIndent ∧ Tmp21
theorem invalidExceptStmtIndentRule_proven : InvalidExceptStmtIndentRule := ⟨by plain_spec, tmp21_proven⟩

/-- `invalid_except_star_stmt_indent: a='except' '*' expression ['as' NAME ] ':' NEWLINE !INDENT {
RAISE_INDENTATION_ERROR("expected an indented block after 'except*' statement on line %d",
a->lineno) }` (`Grammar/python.gram:1500-1502`). -/
def InvalidExceptStarStmtIndent : Prop := PlainSpec 249 [
  ⟨[.call (.tok 695), .call (.tok 16), .call (.rule 109), .opt (.rule 298), .call (.tok 11),
    .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'except*' statement on line " 0⟩]
def InvalidExceptStarStmtIndentRule : Prop := InvalidExceptStarStmtIndent ∧ Tmp21
theorem invalidExceptStarStmtIndentRule_proven : InvalidExceptStarStmtIndentRule :=
  ⟨by plain_spec, tmp21_proven⟩

/-! ### `match`, `case` -/

/-- `CHECK_VERSION(void*, 10, "Pattern matching is", RAISE_SYNTAX_ERROR("expected ':'"))`: the
raise runs first and its `NULL` makes `CHECK_VERSION` set `error_indicator` (`Parser/pegen.h`,
`INVALID_VERSION_CHECK`), whatever the feature version. -/
@[irreducible] def oMatchColon : Array Ast → Int × Int → PS → Option Ast × PS := fun _ _ s =>
  let r := (raiseError "SyntaxError" false "expected ':'" s).2
  if r.errOccurred then (none, { r with errorIndicator := true })
  else (some .null, { r with errorIndicator := true })

/-- `invalid_match_stmt` (`Grammar/python.gram:1503-1510`):
```
    | "match" subject_expr NEWLINE { CHECK_VERSION(void*, 10, "Pattern matching is", RAISE_SYNTAX_ERROR("expected ':'") ) }
    | a="match" subject=subject_expr ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'match' statement on line %d", a->lineno) }
    | a="case" patterns guard? b=':' block {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b,
            "case statement must be inside match statement") }
```
-/
def InvalidMatchStmt : Prop := PlainSpec 250 [
  ⟨[.call (.softKw [109, 97, 116, 99, 104]), .call (.rule 66), .call (.tok 4)], false, oMatchColon⟩,
  ⟨[.call (.softKw [109, 97, 116, 99, 104]), .call (.rule 66), .call (.tok 11), .call (.tok 4),
    .look false (.tok 5)], false, oIndent "expected an indented block after 'match' statement on line " 0⟩,
  ⟨[.call (.softKw [99, 97, 115, 101]), .call (.rule 69), .opt (.rule 68), .call (.tok 11),
    .call (.rule 33)], false, oKR 0 3 "case statement must be inside match statement"⟩]

theorem invalidMatchStmt_proven : InvalidMatchStmt := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) ?_
  · unfold oMatchColon
    have hm : msgOf [.str ("expected ':'".toList.map Char.toNat)] = "expected ':'" := by decide +kernel
    have hev : ∀ ex, evalA env ex (.checkVersion (.int 10) (.str "Pattern matching is")
        (.call .RAISE_SYNTAX_ERROR [.str "expected ':'"])) s =
        (.null, { (raiseError "SyntaxError" false "expected ':'" s).2 with errorIndicator := true }) := by
      intro ex
      have hn : evalA env ex (.call .RAISE_SYNTAX_ERROR [.str "expected ':'"]) s =
          (.null, (raiseError "SyntaxError" false "expected ':'" s).2) := by
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, hm]
        rfl
      simp only [evalA, bind, StateT.bind, hn]
      rfl
    rw [altResult_plain rfl rfl]
    simp only [hev, nonNull]
    generalize (raiseError "SyntaxError" false "expected ':'" s).2 = r
    cases hx : r.errOccurred <;> simp_all [PS.errOccurred]
  · spec_alts

/-- `invalid_case_block` (`Grammar/python.gram:1511-1514`):
```
    | "case" patterns guard? NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | a="case" patterns guard? ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'case' statement on line %d", a->lineno) }
```
-/
def InvalidCaseBlock : Prop := PlainSpec 251 [
  ⟨[.call (.softKw [99, 97, 115, 101]), .call (.rule 69), .opt (.rule 68), .call (.tok 4)], false,
    oSyn "expected ':'"⟩,
  ⟨[.call (.softKw [99, 97, 115, 101]), .call (.rule 69), .opt (.rule 68), .call (.tok 11), .call (.tok 4),
    .look false (.tok 5)], false, oIndent "expected an indented block after 'case' statement on line " 0⟩]
theorem invalidCaseBlock_proven : InvalidCaseBlock := by plain_spec

/-! ### `with` -/

/-- `invalid_with_stmt` (`Grammar/python.gram:1458-1462`):
```
    | ['async'] 'with' ','.(expression ['as' star_target])+ trailing=',' ':' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(trailing, "the last 'with' item has a trailing comma") }
    | ['async'] 'with' ','.(expression ['as' star_target])+ NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
    | ['async'] 'with' '(' ','.(expressions ['as' star_target])+ ','? ')' NEWLINE { RAISE_SYNTAX_ERROR("expected ':'") }
```
The gathers are `_gather_141` (418, of `_tmp_176`) and `_gather_143` (420, of `_tmp_177`). -/
def InvalidWithStmt : Prop := PlainSpec 242 [
  ⟨[.opt (.tok 716), .call (.tok 665), .call (.rule 418), .call (.tok 12), .call (.tok 11)], false,
    oKL 3 "the last 'with' item has a trailing comma"⟩,
  ⟨[.opt (.tok 716), .call (.tok 665), .call (.rule 418), .call (.tok 4)], false, oSyn "expected ':'"⟩,
  ⟨[.opt (.tok 716), .call (.tok 665), .call (.tok 7), .call (.rule 420), .opt (.tok 12), .call (.tok 8),
    .call (.tok 4)], false, oSyn "expected ':'"⟩]

def WithGathers : Prop := Gather141 ∧ Gather143 ∧ Tmp176 ∧ Tmp177 ∧ Tmp180
theorem withGathers_proven : WithGathers :=
  ⟨gather141_proven, gather143_proven, tmp176_proven, tmp177_proven, tmp180_proven⟩

def InvalidWithStmtRule : Prop := InvalidWithStmt ∧ WithGathers
theorem invalidWithStmtRule_proven : InvalidWithStmtRule := ⟨by plain_spec, withGathers_proven⟩

/-- `invalid_with_stmt_indent` (`Grammar/python.gram:1463-1467`):
```
    | ['async'] a='with' ','.(expression ['as' star_target])+ ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'with' statement on line %d", a->lineno) }
    | ['async'] a='with' '(' ','.(expressions ['as' star_target])+ ','? ')' ':' NEWLINE !INDENT {
        RAISE_INDENTATION_ERROR("expected an indented block after 'with' statement on line %d", a->lineno) }
```
-/
def InvalidWithStmtIndent : Prop := PlainSpec 243 [
  ⟨[.opt (.tok 716), .call (.tok 665), .call (.rule 418), .call (.tok 11), .call (.tok 4),
    .look false (.tok 5)], false, oIndent "expected an indented block after 'with' statement on line " 1⟩,
  ⟨[.opt (.tok 716), .call (.tok 665), .call (.tok 7), .call (.rule 420), .opt (.tok 12), .call (.tok 8),
    .call (.tok 11), .call (.tok 4), .look false (.tok 5)], false,
    oIndent "expected an indented block after 'with' statement on line " 1⟩]
def InvalidWithStmtIndentRule : Prop := InvalidWithStmtIndent ∧ WithGathers
theorem invalidWithStmtIndentRule_proven : InvalidWithStmtIndentRule :=
  ⟨by plain_spec, withGathers_proven⟩

/-- `invalid_with_item: expression 'as' a=expression &(',' | ')' | ':') {
RAISE_SYNTAX_ERROR_INVALID_TARGET(STAR_TARGETS, a) }` (`Grammar/python.gram:1416-1418`), the
lookahead `_tmp_35` (312). -/
def InvalidWithItem : Prop := PlainSpec 233 [
  ⟨[.call (.rule 109), .call (.tok 698), .call (.rule 109), .look true (.rule 312)], false, oTarget 0 2⟩]
def InvalidWithItemRule : Prop := InvalidWithItem ∧ Tmp35
theorem invalidWithItemRule_proven : InvalidWithItemRule := ⟨by plain_spec, tmp35_proven⟩

/-! ### `for` targets and clauses -/

/-- `invalid_for_target: 'async'? 'for' a=star_expressions { RAISE_SYNTAX_ERROR_INVALID_TARGET(FOR_TARGETS, a) }`
(`Grammar/python.gram:1424-1426`). -/
def InvalidForTarget : Prop := PlainSpec 235 [
  ⟨[.opt (.tok 716), .call (.tok 712), .call (.rule 112)], false, oTarget 2 2⟩]
theorem invalidForTarget_proven : InvalidForTarget := by plain_spec

/-- `invalid_for_if_clause: 'async'? 'for' (bitwise_or (',' bitwise_or)* [',']) !'in' {
RAISE_SYNTAX_ERROR("'in' expected after for-loop variables") }` (`Grammar/python.gram:1420-1422`),
the group `_tmp_136` (413). -/
def InvalidForIfClause : Prop := PlainSpec 234 [
  ⟨[.opt (.tok 716), .call (.tok 712), .call (.rule 413), .look false (.tok 713)], false,
    oSyn "'in' expected after for-loop variables"⟩]
def InvalidForIfClauseRule : Prop := InvalidForIfClause ∧ Tmp136 ∧ Loop0_174 ∧ Tmp179
theorem invalidForIfClauseRule_proven : InvalidForIfClauseRule :=
  ⟨by plain_spec, tmp136_proven, loop0_174_proven, tmp179_proven⟩

/-! ### Imports -/

/-- `invalid_import_from` (`Grammar/python.gram:1447-1450`), new in 3.15:
```
    | 'from' ('.' | '...')* dotted_name a="lazy" 'import' import_from_targets {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a,
            "use 'lazy from ... ' instead of 'from ... lazy import'") }
```
`('.' | '...')*` is `_loop0_17` (294) over `_tmp_160` (437). -/
def InvalidImportFrom : Prop := PlainSpec 240 [
  ⟨[.call (.tok 650), .call (.rule 294), .call (.rule 32), .call (.softKw [108, 97, 122, 121]),
    .call (.tok 651), .call (.rule 27)], false,
    oKL 3 "use 'lazy from ... ' instead of 'from ... lazy import'"⟩]
def InvalidImportFromRule : Prop := InvalidImportFrom ∧ Loop0_17 ∧ Tmp160
theorem invalidImportFromRule_proven : InvalidImportFromRule :=
  ⟨by plain_spec, loop0_17_proven, tmp160_proven⟩

/-- `invalid_import_from_targets` (`Grammar/python.gram:1452-1456`):
```
    | import_from_as_names ',' NEWLINE {
        RAISE_SYNTAX_ERROR("trailing comma not allowed without surrounding parentheses") }
    | token=NEWLINE {
        RAISE_SYNTAX_ERROR_STARTING_FROM(token, "Expected one or more names after 'import'") }
```
-/
def InvalidImportFromTargets : Prop := PlainSpec 241 [
  ⟨[.call (.rule 28), .call (.tok 12), .call (.tok 4)], false,
    oSyn "trailing comma not allowed without surrounding parentheses"⟩,
  ⟨[.call (.tok 4)], false, oFrom 0 "Expected one or more names after 'import'"⟩]
theorem invalidImportFromTargets_proven : InvalidImportFromTargets := by plain_spec

/-! ### Patterns -/

/-- `invalid_as_pattern` (`Grammar/python.gram:1515-1519`):
```
    | or_pattern 'as' a="_" { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use '_' as a target") }
    | or_pattern 'as' a=expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
            a, "cannot use %s as pattern target", _PyPegen_get_expr_name(a)) }
```
-/
def InvalidAsPattern : Prop := PlainSpec 252 [
  ⟨[.call (.rule 72), .call (.tok 698), .call (.softKw [95])], false, oKL 2 "cannot use '_' as a target"⟩,
  ⟨[.call (.rule 72), .call (.tok 698), .call (.rule 109)], false,
    oKLName 2 "cannot use " " as pattern target"⟩]
theorem invalidAsPattern_proven : InvalidAsPattern := by plain_spec

/-- `invalid_class_pattern: name_or_attr '(' a=invalid_class_argument_pattern {
RAISE_SYNTAX_ERROR_KNOWN_RANGE(PyPegen_first_item(a, pattern_ty), PyPegen_last_item(a,
pattern_ty), "positional patterns follow keyword patterns") }` (`Grammar/python.gram:1520-1524`):
over the positional patterns after the keyword ones. -/
def InvalidClassPattern : Prop := PlainSpec 253 [
  ⟨[.call (.rule 86), .call (.tok 7), .call (.rule 255)], false, fun env _ s =>
    (none, raisedAt ((seqOf (env.getD 2 .null)).headD .null) ((seqOf (env.getD 2 .null)).getLastD .null)
      "positional patterns follow keyword patterns" s)⟩]

theorem invalidClassPattern_proven : InvalidClassPattern := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil
  have hm : msgOf [.str ("positional patterns follow keyword patterns".toList.map Char.toNat)] =
      "positional patterns follow keyword patterns" := by decide +kernel
  rw [altResult_raise rfl (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
      List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
    rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
  rfl

/-- `invalid_mapping_pattern` (`Grammar/python.gram:1525-1528`), new in 3.15:
```
    | '{' (items_pattern ',')? rest=double_star_pattern ',' items_pattern ','? '}' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(
        rest,
        "double star pattern must be the last (right-most) subpattern in the mapping pattern") }
```
`(items_pattern ',')` is `_tmp_148` (425). -/
def InvalidMappingPattern : Prop := PlainSpec 254 [
  ⟨[.call (.tok 25), .opt (.rule 425), .call (.rule 96), .call (.tok 12), .call (.rule 94), .opt (.tok 12),
    .call (.tok 26)], false,
    oKL 2 "double star pattern must be the last (right-most) subpattern in the mapping pattern"⟩]
def InvalidMappingPatternRule : Prop := InvalidMappingPattern ∧ Tmp148
theorem invalidMappingPatternRule_proven : InvalidMappingPatternRule := ⟨by plain_spec, tmp148_proven⟩

/-- `invalid_class_argument_pattern[asdl_pattern_seq*]: [positional_patterns ','] keyword_patterns
',' a=positional_patterns { a }` (`Grammar/python.gram:1529-1530`): the positional patterns after
the keyword ones. `[positional_patterns ',']` is `_tmp_149` (426). -/
def InvalidClassArgumentPattern : Prop := PlainSpec 255 [
  ⟨[.opt (.rule 426), .call (.rule 99), .call (.tok 12), .call (.rule 98)], false, oVar 3⟩]
def InvalidClassArgumentPatternRule : Prop := InvalidClassArgumentPattern ∧ Tmp149
theorem invalidClassArgumentPatternRule_proven : InvalidClassArgumentPatternRule :=
  ⟨by plain_spec, tmp149_proven⟩

end PyLean.PyGrammar.Peg
