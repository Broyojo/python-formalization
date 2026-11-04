import PyLean.PyGrammar.Peg.Rules.SpecInv2

/-! Statement, target and typing rules as equations (`Spec.lean`), with the nodes their actions
build: `statements`, `single_compound_stmt`, `statement_newline`, `simple_stmts`,
`annotated_rhs`, `type_alias`, `star_targets_list_seq`, `star_targets_tuple_seq`, `star_atom`,
`single_subscript_attribute_target`, `del_t_atom`, `type_expressions`, `func_type_comment`,
`expression_without_invalid`. Rules: `statement` 5, `compound_stmt` 10, `single_compound_stmt`
6, `simple_stmt` 9, `simple_stmts` 8, `yield_expr` 111, `star_expressions` 112, `type_params` 102,
`expression` 109, `star_target` 196, `target_with_star_atom` 197, `star_targets_tuple_seq` 195,
`star_targets_list_seq` 194, `t_primary` 201, `t_lookahead` 202, `slices` 145, `del_target` 204,
`del_targets` 203, `disjunction` 120, `lambdef` 149, `invalid_double_type_comments` 232; tokens
`ENDMARKER` 0, `NEWLINE` 4, `INDENT` 5, `(` 7, `)` 8, `[` 9, `]` 10, `,` 12, `;` 13, `*` 16, `=` 22,
`.` 23, `**` 35, `TYPE_COMMENT` 57; `if` 700, `else` 704; soft keyword `type`
[116, 121, 112, 101]. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Statements -/

/-- `_loop1_2: statement+`. -/
def Loop1_2 : Prop := Loop1Over 279 5
theorem loop1_2_proven : Loop1_2 := loop1Over_of rfl

/-- `statements[asdl_stmt_seq*]: a=statement+ { (asdl_stmt_seq*)_PyPegen_seq_flatten(p, a) }`
(`Grammar/python.gram:97`): the statements of every `statement` (each a sequence), in order. -/
def StatementsSpec : Prop := PlainSpec 4 [
  ⟨[.call (.rule 279)], false, oPure (fun env => .seq ((seqOf (env.getD 0 .null)).flatMap seqOf))⟩]
def StatementsRule : Prop := StatementsSpec ∧ Loop1_2
theorem statementsRule_proven : StatementsRule := ⟨by plain_spec, loop1_2_proven⟩

/-- `single_compound_stmt[asdl_stmt_seq*]: a=compound_stmt { _PyPegen_register_stmts(p,
(asdl_stmt_seq*)_PyPegen_singleton_seq(p, a)) }` (`Grammar/python.gram:105-107`): the one
statement as a sequence, recorded by `_PyPegen_register_stmts` (`registerStmts`: in the second
pass, the start of the last statement, for the "invalid syntax" location). -/
def SingleCompoundStmt : Prop := PlainSpec 6 [
  ⟨[.call (.rule 10)], false, fun env _ s =>
    pureRes (registerStmts (.seq [env.getD 0 .null]) s).1 (registerStmts (.seq [env.getD 0 .null]) s).2⟩]
theorem singleCompoundStmt_proven : SingleCompoundStmt := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  exact altsAre_cons rfl rfl (fun env st s => altResult_pure2 rfl (fun _ => rfl)) altsAre_nil

/-- `statement_newline` (`Grammar/python.gram:109-113`):
```
    | a=single_compound_stmt NEWLINE { a }
    | simple_stmts
    | NEWLINE { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, CHECK(stmt_ty, _PyAST_Pass(EXTRA))) }
    | ENDMARKER { _PyPegen_interactive_exit(p) }
```
A blank line is one `Pass` spanning the `NEWLINE` (`EXTRA` from the start token to the last
token that is not whitespace); `ENDMARKER` gives `NULL` (`_PyPegen_interactive_exit`). -/
def StatementNewline : Prop := ExtraSpec 7 [
  ⟨[.call (.rule 6), .call (.tok 4)], false, oVar 0⟩,
  ⟨[.call (.rule 8)], false, oVar0⟩,
  ⟨[.call (.tok 4)], false, oPureX (fun _ l => .seq [mkAt .Pass [] l])⟩,
  ⟨[.call (.tok 0)], false, oPure (fun _ => .null)⟩]
theorem statementNewline_proven : StatementNewline := by extra_spec

/-- `simple_stmts` (`Grammar/python.gram:115-117`):
```
    | a=simple_stmt !';' NEWLINE { (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a) } # Not needed, there for speedup
    | a[asdl_stmt_seq*]=';'.simple_stmt+ [';'] NEWLINE { a }
```
`';'.simple_stmt+` is `_gather_4` (281), pinned by `Gather4`. -/
def SimpleStmts : Prop := PlainSpec 8 [
  ⟨[.call (.rule 9), .look false (.tok 13), .call (.tok 4)], false, oPure (fun env => .seq [env.getD 0 .null])⟩,
  ⟨[.call (.rule 281), .opt (.tok 13), .call (.tok 4)], false, oVar 0⟩]
theorem simpleStmts_proven : SimpleStmts := by plain_spec

/-- `';'.simple_stmt+` (`Grammar/python.gram:117`): `_gather_4` (281) is `simple_stmt _loop0_3`
and `_loop0_3` (280) is `(';' simple_stmt)*`, separator `;` (13): the first `simple_stmt` (rule 9),
then one more for every `;` followed by a `simple_stmt`, all in source order, stopping before a
`;` that no statement follows (the `[';']` of `simple_stmts` reads it); no first statement gives
`NULL` with the mark back. -/
def Gather4 : Prop := GatherSepTok 13 281 280 9
theorem gather4_proven : Gather4 := gatherSepTok_of rfl rfl

/-- `simple_stmts` with its gather pinned. -/
def SimpleStmtsRule : Prop := SimpleStmts ∧ Gather4
theorem simpleStmtsRule_proven : SimpleStmtsRule := ⟨simpleStmts_proven, gather4_proven⟩

/-- `annotated_rhs[expr_ty]: yield_expr | star_expressions` (`Grammar/python.gram:168`). -/
def AnnotatedRhs : Prop := PlainSpec 12 [
  ⟨[.call (.rule 111)], false, oVar0⟩, ⟨[.call (.rule 112)], false, oVar0⟩]
theorem annotatedRhs_proven : AnnotatedRhs := by plain_spec

/-! ### `type_alias` -/

def typeStmtMsg : String := "Type statement is only supported in Python 3.12 and greater"

/-- The action of `type_alias`: `_PyPegen_set_expr_context(p, n, Store)` under `CHECK`
(`error_indicator` when `NULL`), the `TypeAlias` node with `EXTRA`, then `CHECK_VERSION(stmt_ty,
12, "Type statement is", ...)`: below feature version 12, `error_indicator` and
`RAISE_SYNTAX_ERROR("%s only supported in Python 3.%i and greater", ...)`. -/
@[irreducible] def oTypeAlias : Array Ast → Int × Int → PS → Option Ast × PS := fun env st s =>
  let c := setExprContext (opNode .Store) 100000 (env.getD 1 .null)
  let s1 := if nonNull c then s else { s with errorIndicator := true }
  let n := mkAt .TypeAlias [c, env.getD 2 .null, env.getD 4 .null] (locFrom st s)
  if (s1.featureVersion : Int) < 12 then
    (none, { (raiseError0 "SyntaxError" typeStmtMsg { s1 with errorIndicator := true }).2 with
      errorIndicator := true })
  else pureRes n s1

/-- `type_alias[stmt_ty]: "type" n=NAME t=[type_params] '=' b=expression {
CHECK_VERSION(stmt_ty, 12, "Type statement is", _PyAST_TypeAlias(CHECK(expr_ty,
_PyPegen_set_expr_context(p, n, Store)), t, b, EXTRA)) }` (`Grammar/python.gram:680-683`). -/
def TypeAlias : Prop := ExtraSpec 101 [
  ⟨[.call (.softKw [116, 121, 112, 101]), .call .name, .opt (.rule 102), .call (.tok 22), .call (.rule 109)],
    false, oTypeAlias⟩]

theorem evalA_cv_ok' {env : Array Ast} {ex : Extra} {v : Int} {m : String} {node : AE} {s s1 : PS}
    {n : Ast} (hn : evalA env ex node s = (n, s1)) (hnn : n ≠ .null)
    (hv : ¬ (s1.featureVersion : Int) < v) :
    evalA env ex (.checkVersion (.int v) (.str m) node) s = (n, s1) := by
  simp only [evalA, bind, StateT.bind, hn, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get]
  cases n with
  | null => exact absurd rfl hnn
  | _ => simp [hv, StateT.pure]; rfl

theorem evalA_cv_low' {env : Array Ast} {ex : Extra} {v : Int} {m : String} {node : AE} {s s1 : PS}
    {n : Ast} (hn : evalA env ex node s = (n, s1)) (hnn : n ≠ .null)
    (hv : (s1.featureVersion : Int) < v) :
    evalA env ex (.checkVersion (.int v) (.str m) node) s =
      (.null, (raiseError0 "SyntaxError"
        s!"{cpsStr (m.toList.map Char.toNat)} only supported in Python 3.{v} and greater"
        { s1 with errorIndicator := true }).2) := by
  simp only [evalA, bind, StateT.bind, hn, pure, StateT.pure, get, getThe, MonadStateOf.get,
    StateT.get]
  cases n with
  | null => exact absurd rfl hnn
  | _ =>
    simp only [hv, ↓reduceIte, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.modifyGet, StateT.bind]
    rfl

theorem typeAlias_proven : TypeAlias := by
  intro f p q h
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil
  unfold oTypeAlias
  rw [altResult_extra rfl rfl]
  have hmsg : s!"{cpsStr ("Type statement is".toList.map Char.toNat)} only supported in Python 3.{(12 : Int)} and greater" = typeStmtMsg := by
    decide +kernel
  dsimp only
  generalize hc : setExprContext (opNode .Store) 100000 (env.getD 1 .null) = c
  have hcall : callHelper .set_expr_context [env.getD 1 .null, .node .Store [] none] s = (c, s) := by
    simp only [callHelper, List.getD_cons_zero, List.getD_cons_succ]
    rw [show setExprContext (Ast.node Ctor.Store [] none) 100000 (env.getD 1 .null) = c from hc]
    rfl
  have hnode : ∀ ex : Extra, evalA env ex (.mk .TypeAlias [.check (.call .set_expr_context [.var 1, .ctor .Store]),
      .var 2, .var 4, .extra0, .extra1, .extra2, .extra3]) s =
      (mkAst .TypeAlias [c, env.getD 2 .null, env.getD 4 .null, .int ex.startLine, .int ex.startCol,
        .int ex.endLine, .int ex.endCol], if nonNull c then s else { s with errorIndicator := true }) := by
    intro ex
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, hcall]
    cases c <;> rfl
  generalize hs1 : (if nonNull c then s else { s with errorIndicator := true }) = s1 at hnode
  have hnn : mkAst .TypeAlias [c, env.getD 2 .null, env.getD 4 .null,
      .int (mkExtra st (lastNonWhitespaceToken s)).startLine, .int (mkExtra st (lastNonWhitespaceToken s)).startCol,
      .int (mkExtra st (lastNonWhitespaceToken s)).endLine,
      .int (mkExtra st (lastNonWhitespaceToken s)).endCol] ≠ .null := by simp [mkAst]
  by_cases hv : (s1.featureVersion : Int) < 12
  · rw [evalA_cv_low' (hnode _) hnn hv, hmsg]
    have he := (raises_raiseError0 "SyntaxError" typeStmtMsg).2 { s1 with errorIndicator := true }
    generalize raiseError0 "SyntaxError" typeStmtMsg { s1 with errorIndicator := true } = r at he
    obtain ⟨u, r⟩ := r
    simp only at he
    simp [hv, nonNull, he]
  · rw [evalA_cv_ok' (hnode _) hnn hv]
    simp only [hv, ↓reduceIte, pureRes, locFrom, mkExtra, mkAt, locArgs]
    rfl

/-! ### Targets -/

/-- `_tmp_168: ',' c=star_target { c }` and `_loop1_100: (',' c=star_target { c })+`;
`_gather_99: ','.star_target+` (`_loop0_98`). -/
def Tmp168 : Prop := PlainSpec 445 [⟨[.call (.tok 12), .call (.rule 196)], false, oVar 1⟩]
theorem tmp168_proven : Tmp168 := by plain_spec
def Loop1_100 : Prop := Loop1Over 377 445
theorem loop1_100_proven : Loop1_100 := loop1Over_of rfl
def Gather99 : Prop := GatherSep 376 375 196
theorem gather99_proven : Gather99 := gatherSep_of rfl rfl

/-- `star_targets_list_seq[asdl_expr_seq*]: a[asdl_expr_seq*]=','.star_target+ [','] { a }`
(`Grammar/python.gram:1123`). -/
def StarTargetsListSeq : Prop := PlainSpec 194 [
  ⟨[.call (.rule 376), .opt (.tok 12)], false, oVar 0⟩]
def StarTargetsListSeqRule : Prop := StarTargetsListSeq ∧ Gather99
theorem starTargetsListSeqRule_proven : StarTargetsListSeqRule := ⟨by plain_spec, gather99_proven⟩

/-- `star_targets_tuple_seq` (`Grammar/python.gram:1125-1127`):
```
    | a=star_target b=(',' c=star_target { c })+ [','] { (asdl_expr_seq*) _PyPegen_seq_insert_in_front(p, a, b) }
    | a=star_target ',' { (asdl_expr_seq*) _PyPegen_singleton_seq(p, a) }
```
-/
def StarTargetsTupleSeq : Prop := PlainSpec 195 [
  ⟨[.call (.rule 196), .call (.rule 377), .opt (.tok 12)], false,
    oPure (fun env => .seq (env.getD 0 .null :: seqOf (env.getD 1 .null)))⟩,
  ⟨[.call (.rule 196), .call (.tok 12)], false, oPure (fun env => .seq [env.getD 0 .null])⟩]
def StarTargetsTupleSeqRule : Prop := StarTargetsTupleSeq ∧ Loop1_100 ∧ Tmp168
theorem starTargetsTupleSeqRule_proven : StarTargetsTupleSeqRule :=
  ⟨by plain_spec, loop1_100_proven, tmp168_proven⟩

/-- `star_atom[expr_ty]` (`Grammar/python.gram:1139-1143`):
```
    | a=NAME { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=target_with_star_atom ')' { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=[star_targets_tuple_seq] ')' { _PyAST_Tuple(a, Store, EXTRA) }
    | '[' a=[star_targets_list_seq] ']' { _PyAST_List(a, Store, EXTRA) }
```
-/
def StarAtom : Prop := ExtraSpec 198 [
  ⟨[.call .name], false, oPure (fun env => setExprContext (opNode .Store) 100000 (env.getD 0 .null))⟩,
  ⟨[.call (.tok 7), .call (.rule 197), .call (.tok 8)], false,
    oPure (fun env => setExprContext (opNode .Store) 100000 (env.getD 1 .null))⟩,
  ⟨[.call (.tok 7), .opt (.rule 195), .call (.tok 8)], false,
    oPureX (fun env l => mkAt .Tuple [env.getD 1 .null, opNode .Store] l)⟩,
  ⟨[.call (.tok 9), .opt (.rule 194), .call (.tok 10)], false,
    oPureX (fun env l => mkAt .List [env.getD 1 .null, opNode .Store] l)⟩]
theorem starAtom_proven : StarAtom := by extra_spec

/-- `single_subscript_attribute_target[expr_ty]` (`Grammar/python.gram:1150-1152`):
```
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Store, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Store, EXTRA) }
```
-/
def SingleSubscriptAttributeTarget : Prop := ExtraSpec 200 [
  ⟨[.call (.rule 201), .call (.tok 23), .call .name, .look false (.rule 202)], false,
    oPureX (fun env l => mkAt .Attribute [env.getD 0 .null, fieldOf (env.getD 2 .null) "id", opNode .Store] l)⟩,
  ⟨[.call (.rule 201), .call (.tok 9), .call (.rule 145), .call (.tok 10), .look false (.rule 202)], false,
    oPureX (fun env l => mkAt .Subscript [env.getD 0 .null, env.getD 2 .null, opNode .Store] l)⟩]
theorem singleSubscriptAttributeTarget_proven : SingleSubscriptAttributeTarget := by extra_spec

/-- `del_t_atom[expr_ty]` (`Grammar/python.gram:1178-1182`):
```
    | a=NAME { _PyPegen_set_expr_context(p, a, Del) }
    | '(' a=del_target ')' { _PyPegen_set_expr_context(p, a, Del) }
    | '(' a=[del_targets] ')' { _PyAST_Tuple(a, Del, EXTRA) }
    | '[' a=[del_targets] ']' { _PyAST_List(a, Del, EXTRA) }
```
-/
def DelTAtom : Prop := ExtraSpec 205 [
  ⟨[.call .name], false, oPure (fun env => setExprContext (opNode .Del) 100000 (env.getD 0 .null))⟩,
  ⟨[.call (.tok 7), .call (.rule 204), .call (.tok 8)], false,
    oPure (fun env => setExprContext (opNode .Del) 100000 (env.getD 1 .null))⟩,
  ⟨[.call (.tok 7), .opt (.rule 203), .call (.tok 8)], false,
    oPureX (fun env l => mkAt .Tuple [env.getD 1 .null, opNode .Del] l)⟩,
  ⟨[.call (.tok 9), .opt (.rule 203), .call (.tok 10)], false,
    oPureX (fun env l => mkAt .List [env.getD 1 .null, opNode .Del] l)⟩]
theorem delTAtom_proven : DelTAtom := by extra_spec

/-! ### Typing elements -/

/-- `_gather_105: ','.expression+` (`_loop0_104`). -/
def Gather105 : Prop := GatherSep 382 381 109
theorem gather105_proven : Gather105 := gatherSep_of rfl rfl

/-- `type_expressions[asdl_expr_seq*]` (`Grammar/python.gram:1188-1203`): the seven
alternatives in order; `*` and `**` arguments are appended to the plain ones. -/
def TypeExpressions : Prop := PlainSpec 206 [
  ⟨[.call (.rule 382), .call (.tok 12), .call (.tok 16), .call (.rule 109), .call (.tok 12), .call (.tok 35),
    .call (.rule 109)], false,
    oPure (fun env => .seq ((seqOf (env.getD 0 .null) ++ [env.getD 3 .null]) ++ [env.getD 6 .null]))⟩,
  ⟨[.call (.rule 382), .call (.tok 12), .call (.tok 16), .call (.rule 109)], false,
    oPure (fun env => .seq (seqOf (env.getD 0 .null) ++ [env.getD 3 .null]))⟩,
  ⟨[.call (.rule 382), .call (.tok 12), .call (.tok 35), .call (.rule 109)], false,
    oPure (fun env => .seq (seqOf (env.getD 0 .null) ++ [env.getD 3 .null]))⟩,
  ⟨[.call (.tok 16), .call (.rule 109), .call (.tok 12), .call (.tok 35), .call (.rule 109)], false,
    oPure (fun env => .seq [env.getD 1 .null, env.getD 4 .null])⟩,
  ⟨[.call (.tok 16), .call (.rule 109)], false, oPure (fun env => .seq [env.getD 1 .null])⟩,
  ⟨[.call (.tok 35), .call (.rule 109)], false, oPure (fun env => .seq [env.getD 1 .null])⟩,
  ⟨[.call (.rule 382)], false, oVar 0⟩]
def TypeExpressionsRule : Prop := TypeExpressions ∧ Gather105
theorem typeExpressionsRule_proven : TypeExpressionsRule := ⟨by plain_spec, gather105_proven⟩

/-- `_tmp_106: NEWLINE INDENT`. -/
def Tmp106 : Prop := PlainSpec 383 [⟨[.call (.tok 4), .call (.tok 5)], false, oDummy⟩]
theorem tmp106_proven : Tmp106 := by plain_spec

/-- `func_type_comment[Token*]` (`Grammar/python.gram:1205-1208`):
```
    | NEWLINE t=TYPE_COMMENT &(NEWLINE INDENT) { t }  # Must be followed by indented block
    | invalid_double_type_comments
    | TYPE_COMMENT
```
-/
def FuncTypeComment : Prop := PlainSpec 207 [
  ⟨[.call (.tok 4), .call (.tok 57), .look true (.rule 383)], false, oVar 1⟩,
  ⟨[.call (.rule 232)], true, oVar0⟩,
  ⟨[.call (.tok 57)], false, oVar0⟩]
def FuncTypeCommentRule : Prop := FuncTypeComment ∧ Tmp106
theorem funcTypeCommentRule_proven : FuncTypeCommentRule := ⟨by plain_spec, tmp106_proven⟩

/-! ### `expression_without_invalid` -/

/-- `expression_without_invalid[expr_ty]` (`Grammar/python.gram:1242-1245`):
```
    | a=disjunction 'if' b=disjunction 'else' c=expression { _PyAST_IfExp(b, a, c, EXTRA) }
    | disjunction
    | lambdef
```
The `_without_invalid` suffix makes the rule function run with `call_invalid_rules` off and put
it back (`Tools/peg_generator/pegen/c_generator.py`), so no `invalid_` rule runs under it. -/
def ExpressionWithoutInvalid : Prop := NoInvExtraSpec 210 [
  ⟨[.call (.rule 120), .call (.tok 700), .call (.rule 120), .call (.tok 704), .call (.rule 109)], false,
    oPureX (fun env l => mkAt .IfExp [env.getD 2 .null, env.getD 0 .null, env.getD 4 .null] l)⟩,
  ⟨[.call (.rule 120)], false, oVar0⟩,
  ⟨[.call (.rule 149)], false, oVar0⟩]

theorem expressionWithoutInvalid_proven : ExpressionWithoutInvalid := by
  intro f p q h
  rw [callRule_noinv_extra rfl rfl rfl rfl rfl h]
  have key : ∀ a b : Option Ast × PS, a = b →
      ((a.1.getD .null, { a.2.leave with callInvalidRules := p.callInvalidRules }) : Ast × PS) =
        (let c := finish b; (c.1, { c.2 with callInvalidRules := p.callInvalidRules })) := by
    intro a b h
    subst h
    rfl
  refine key _ _ (runAlts_spec f _ _ ?_ _ _ _)
  spec_alts

end PyLean.PyGrammar.Peg
