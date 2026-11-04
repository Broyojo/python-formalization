import PyLean.PyGrammar.Peg.Rules.SpecPos

/-! Expression-level `invalid_` rules as equations (`Spec.lean`): `invalid_arguments`,
`invalid_kwarg`, `invalid_legacy_expression`, `invalid_type_param`, `invalid_expression`,
`invalid_named_expression`, `invalid_comprehension`, and their groups. Rules: `expression`
109, `for_if_clauses` 181, `args` 188, `kwargs` 189, `starred_expression` 190, `_gather_91`
368, `star_expressions` 112, `disjunction` 120, `expression_without_invalid` 210, `simple_stmt`
9, `pass_stmt` 16, `break_stmt` 17, `continue_stmt` 18, `lambda_params` 150, `bitwise_or` 135,
`list` 174, `tuple` 175, `genexp` 185, `star_named_expression` 116, `star_named_expressions` 114;
tokens `(` 7, `)` 8, `[` 9, `:` 11, `,` 12, `*` 16, `=` 22, `{` 25, `**` 35, `:=` 53,
`FSTRING_MIDDLE` 60, `TSTRING_MIDDLE` 63; `lambda` 622, `True` 627, `None` 628, `False` 629,
`if` 700, `else` 704. -/

namespace PyLean.PyGrammar.Peg

open Lexer

def genexpMsg : String := "Generator expression must be parenthesized"
def eqMsg : String := "invalid syntax. Maybe you meant '==' or ':=' instead of '='?"

/-! ### `invalid_arguments` -/

/-- `_tmp_169: ','.(starred_expression | ...)+ ',' kwargs` (the gather `_gather_91`, pinned for
`args`); `_tmp_107: _tmp_169 | kwargs`. -/
def Tmp169 : Prop := PlainSpec 446 [⟨[.call (.rule 368), .call (.tok 12), .call (.rule 189)], false, oDummy⟩]
theorem tmp169_proven : Tmp169 := by plain_spec
def Tmp107 : Prop := PlainSpec 384 [⟨[.call (.rule 446)], false, oVar0⟩, ⟨[.call (.rule 189)], false, oVar0⟩]
theorem tmp107_proven : Tmp107 := by plain_spec

/-- `_gather_109: ','.(starred_expression !'=')+` (`_loop0_108` of `_tmp_170`). -/
def Tmp170 : Prop := PlainSpec 447 [⟨[.call (.rule 190), .look false (.tok 22)], false, oVar0⟩]
theorem tmp170_proven : Tmp170 := by plain_spec
def Gather109 : Prop := GatherSep 386 385 447
theorem gather109_proven : Gather109 := gatherSep_of rfl rfl

/-- `_tmp_110: args | expression for_if_clauses`, `_tmp_111: args ','`, `_tmp_112: ',' | ')'`. -/
def Tmp110 : Prop := PlainSpec 387 [⟨[.call (.rule 188)], false, oVar0⟩,
  ⟨[.call (.rule 109), .call (.rule 181)], false, oDummy⟩]
theorem tmp110_proven : Tmp110 := by plain_spec
def Tmp111 : Prop := PlainSpec 388 [⟨[.call (.rule 188), .call (.tok 12)], false, oDummy⟩]
theorem tmp111_proven : Tmp111 := by plain_spec
def Tmp112 : Prop := TokGroup 389 [12, 8]
theorem tmp112_proven : Tmp112 := tokGroup_of (by simp) rfl

/-- `_PyPegen_nonparen_genexp_in_call(p, a, b)` (`Parser/action_helpers.c:1290-1312`): with more than one
positional argument, "Generator expression must be parenthesized" from the last one to the last
item of the last comprehension; otherwise `NULL` without an exception. -/
@[irreducible] def oNonparen : Array Ast → Int × Int → PS → Option Ast × PS := fun env _ s =>
  let cargs := seqOf (fieldOf (env.getD 0 .null) "args")
  if cargs.length ≤ 1 then pureRes .null s
  else (none, raisedAt (cargs.getLastD .null)
    (lastComprehensionItem ((seqOf (env.getD 1 .null)).getLastD .null)) genexpMsg s)

/-- Whether a keyword of the call is `**` unpacking (`arg` is `NULL`), for
`_PyPegen_arguments_parsing_error`. -/
def kwUnpack (e : Ast) : Bool :=
  (seqOf (fieldOf e "keywords")).any fun k => match fieldOf k "arg" with
    | .null => true
    | _ => false

/-- `_PyPegen_arguments_parsing_error(p, a)` (`Parser/action_helpers.c:1271-1288`): "positional argument
follows keyword argument unpacking" when a `**` keyword is present, "positional argument follows
keyword argument" otherwise, at the last token read. -/
@[irreducible] def oArgsErr : Array Ast → Int × Int → PS → Option Ast × PS := fun env _ s =>
  (none, { (raiseError0 "SyntaxError" (argumentErrorMessage (kwUnpack (env.getD 0 .null))) s).2 with
    errorIndicator := true })

/-- `invalid_arguments` (`Grammar/python.gram:1217-1229`):
```
    | ((','.(starred_expression | ( assignment_expression | expression !':=') !'=')+ ',' kwargs) | kwargs) a=',' ','.(starred_expression !'=')+ {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "iterable argument unpacking follows keyword argument unpacking") }
    | a=expression b=for_if_clauses ',' [args | expression for_if_clauses] {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, _PyPegen_get_last_comprehension_item(PyPegen_last_item(b, comprehension_ty)), "Generator expression must be parenthesized") }
    | a=NAME b='=' expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?")}
    | (args ',')? a=NAME b='=' &(',' | ')') {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "expected argument value expression")}
    | a=args b=for_if_clauses { _PyPegen_nonparen_genexp_in_call(p, a, b) }
    | args ',' a=expression b=for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, _PyPegen_get_last_comprehension_item(PyPegen_last_item(b, comprehension_ty)), "Generator expression must be parenthesized") }
    | a=args ',' args { _PyPegen_arguments_parsing_error(p, a) }
```
-/
def InvalidArguments : Prop := PlainSpec 208 [
  ⟨[.call (.rule 384), .call (.tok 12), .call (.rule 386)], false,
    oFrom 1 "iterable argument unpacking follows keyword argument unpacking"⟩,
  ⟨[.call (.rule 109), .call (.rule 181), .call (.tok 12), .opt (.rule 387)], false, fun env _ s =>
    (none, raisedAt (env.getD 0 .null) (lastComprehensionItem ((seqOf (env.getD 1 .null)).getLastD .null))
      genexpMsg s)⟩,
  ⟨[.call .name, .call (.tok 22), .call (.rule 109), .call (.rule 181)], false, oKR 0 1 eqMsg⟩,
  ⟨[.opt (.rule 388), .call .name, .call (.tok 22), .look true (.rule 389)], false,
    oKR 1 2 "expected argument value expression"⟩,
  ⟨[.call (.rule 188), .call (.rule 181)], false, oNonparen⟩,
  ⟨[.call (.rule 188), .call (.tok 12), .call (.rule 109), .call (.rule 181)], false, fun env _ s =>
    (none, raisedAt (env.getD 2 .null) (lastComprehensionItem ((seqOf (env.getD 3 .null)).getLastD .null))
      genexpMsg s)⟩,
  ⟨[.call (.rule 188), .call (.tok 12), .call (.rule 188)], false, oArgsErr⟩]

theorem invalidArguments_proven : InvalidArguments := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun _ _ _ => altResult_from rfl (by decide +kernel)) ?_
  refine altsAre_cons rfl rfl (fun _ _ _ => altResult_krv rfl (fun _ => rfl) (fun _ => rfl)
    (by decide +kernel)) ?_
  refine altsAre_cons rfl rfl (fun _ _ _ => altResult_kr rfl (by decide +kernel)) ?_
  refine altsAre_cons rfl rfl (fun _ _ _ => altResult_kr rfl (by decide +kernel)) ?_
  refine altsAre_cons rfl rfl (fun env st s => ?_) ?_
  · unfold oNonparen
    have hm : msgOf [.str (genexpMsg.toList.map Char.toNat)] = genexpMsg := by decide +kernel
    by_cases hc : (seqOf (fieldOf (env.getD 0 .null) "args")).length ≤ 1
    · rw [altResult_pure rfl (fun ex => by
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
          nonparenGenexp, List.getD_cons_zero, List.getD_cons_succ, hc, ↓reduceIte]
        rfl)]
      dsimp only
      rw [if_pos hc]
    · rw [altResult_raise rfl (fun ex => by
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
          nonparenGenexp, List.getD_cons_zero, List.getD_cons_succ, hc, ↓reduceIte]
        rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
      dsimp only
      rw [if_neg hc]
      rfl
  refine altsAre_cons rfl rfl (fun _ _ _ => altResult_krv rfl (fun _ => rfl) (fun _ => rfl)
    (by decide +kernel)) ?_
  refine altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil
  unfold oArgsErr
  exact altResult_raise rfl (fun ex => rfl) ((raises_raiseError0 _ _).2 _)

def InvalidArgumentsRule : Prop :=
  InvalidArguments ∧ Tmp107 ∧ Tmp169 ∧ Gather109 ∧ Tmp170 ∧ Tmp110 ∧ Tmp111 ∧ Tmp112
theorem invalidArgumentsRule_proven : InvalidArgumentsRule :=
  ⟨invalidArguments_proven, tmp107_proven, tmp169_proven, gather109_proven, tmp170_proven,
    tmp110_proven, tmp111_proven, tmp112_proven⟩

/-! ### `invalid_kwarg` -/

/-- `_tmp_113: 'True' | 'False' | 'None'`, `_tmp_114: NAME '='`. -/
def Tmp113 : Prop := TokGroup 390 [627, 629, 628]
theorem tmp113_proven : Tmp113 := tokGroup_of (by simp) rfl
def Tmp114 : Prop := PlainSpec 391 [⟨[.call .name, .call (.tok 22)], false, oDummy⟩]
theorem tmp114_proven : Tmp114 := by plain_spec

/-- `invalid_kwarg` (`Grammar/python.gram:1230-1240`):
```
    | a[Token*]=('True'|'False'|'None') b='=' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to %s", PyBytes_AS_STRING(a->bytes)) }
    | a=NAME b='=' expression for_if_clauses {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid syntax. Maybe you meant '==' or ':=' instead of '='?")}
    | !(NAME '=') a=expression b='=' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b, "expression cannot contain assignment, perhaps you meant \"==\"?") }
    | a='**' expression '=' b=expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to keyword argument unpacking") }
```
The first message names the keyword by its bytes. -/
def InvalidKwarg : Prop := PlainSpec 209 [
  ⟨[.call (.rule 390), .call (.tok 22)], false, fun env _ s =>
    (none, raisedAt (env.getD 0 .null) (env.getD 1 .null)
      ("cannot assign to " ++ fmtPiece 's' (attrOf (env.getD 0 .null) "bytes")) s)⟩,
  ⟨[.call .name, .call (.tok 22), .call (.rule 109), .call (.rule 181)], false, oKR 0 1 eqMsg⟩,
  ⟨[.look false (.rule 391), .call (.rule 109), .call (.tok 22)], false,
    oKR 0 1 "expression cannot contain assignment, perhaps you meant \"==\"?"⟩,
  ⟨[.call (.tok 35), .call (.rule 109), .call (.tok 22), .call (.rule 109)], false,
    oKR 0 3 "cannot assign to keyword argument unpacking"⟩]

theorem invalidKwarg_proven : InvalidKwarg := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) ?_
  · have hm : ∀ x, msgOf [.str ("cannot assign to %s".toList.map Char.toNat), x] =
        "cannot assign to " ++ fmtPiece 's' x := by
      intro x
      have := msg_pct_s "cannot assign to " "" (by decide) (by decide) x
      simpa using this
    rw [altResult_raise rfl (fun ex => by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
        List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
      rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl
  · spec_alts

def InvalidKwargRule : Prop := InvalidKwarg ∧ Tmp113 ∧ Tmp114
theorem invalidKwargRule_proven : InvalidKwargRule := ⟨invalidKwarg_proven, tmp113_proven, tmp114_proven⟩

/-! ### `invalid_legacy_expression`, `invalid_type_param` -/

/-- `invalid_legacy_expression: a=NAME !'(' b=star_expressions { _PyPegen_check_legacy_stmt(p, a)
? RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "Missing parentheses in call to '%U'. Did you mean
%U(...)?", a->v.Name.id, a->v.Name.id) : NULL}` (`Grammar/python.gram:1246-1249`): for `print`
and `exec` (`_PyPegen_check_legacy_stmt`, `Parser/action_helpers.c:950-962`, `isLegacyStmt`) the message over the name .. the
expressions; for another name the action's `NULL` without an exception. -/
def InvalidLegacyExpression : Prop := PlainSpec 211 [
  ⟨[.call .name, .look false (.tok 7), .call (.rule 112)], false, fun env _ s =>
    if isLegacyStmt (env.getD 0 .null) then
      (none, raisedAt (env.getD 0 .null) (env.getD 1 .null)
        ("Missing parentheses in call to '" ++ fmtPiece 'U' (fieldOf (env.getD 0 .null) "id") ++
          "'. Did you mean " ++ fmtPiece 'U' (fieldOf (env.getD 0 .null) "id") ++ "(...)?") s)
    else pureRes .null s⟩]

theorem invalidLegacyExpression_proven : InvalidLegacyExpression := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil
  have ht : ∀ ex, evalA env ex (.call .check_legacy_stmt [.var 0]) s =
      (.int (if isLegacyStmt (env.getD 0 .null) then 1 else 0), s) := fun _ => rfl
  dsimp only
  cases hl : isLegacyStmt (env.getD 0 .null)
  · rw [altResult_pure rfl (fun ex => by rw [evalA_ite, ht, hl]; rfl)]
    rfl
  · have hm : ∀ x, msgOf [.str ("Missing parentheses in call to '%U'. Did you mean %U(...)?".toList.map
        Char.toNat), x, x] = "Missing parentheses in call to '" ++ fmtPiece 'U' x ++
          "'. Did you mean " ++ fmtPiece 'U' x ++ "(...)?" := by
      intro x
      simp only [msgOf]
      have e : (cpsStr ("Missing parentheses in call to '%U'. Did you mean %U(...)?".toList.map
          Char.toNat)).toList = "Missing parentheses in call to '".toList ++ '%' :: 'U' ::
            ("'. Did you mean ".toList ++ '%' :: 'U' :: "(...)?".toList) := by decide +kernel
      rw [e, formatMsg_pct _ _ _ _ _ (by decide) (by decide), formatMsg_pct _ _ _ _ _ (by decide) (by decide),
        formatMsg_plain _ (by decide)]
      simp [String.append_assoc]
    rw [altResult_raise rfl (fun ex => by
      rw [evalA_ite, ht, hl]
      simp only [truth, ↓reduceIte, evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
        raiseRange, List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
      rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
    rfl

/-- The `kind` of a node as the action's `e->kind` compares it (the model's `.kind`). -/
def kindAst : Ast → Ast
  | .node .PAugOperator [k] _ => k
  | .node c _ _ => .node c [] none
  | _ => .null

/-- `invalid_type_param` (`Grammar/python.gram:1251-1261`):
```
    | '*' a=NAME colon=':' e=expression {
            RAISE_SYNTAX_ERROR_STARTING_FROM(colon, e->kind == Tuple_kind
                ? "cannot use constraints with TypeVarTuple"
                : "cannot use bound with TypeVarTuple")
        }
    | '**' a=NAME colon=':' e=expression {
            RAISE_SYNTAX_ERROR_STARTING_FROM(colon, e->kind == Tuple_kind
                ? "cannot use constraints with ParamSpec"
                : "cannot use bound with ParamSpec")
        }
```
From the `:` to the end of the line. -/
def InvalidTypeParam : Prop := PlainSpec 212 [
  ⟨[.call (.tok 16), .call .name, .call (.tok 11), .call (.rule 109)], false, fun env _ s =>
    (none, raisedFrom (env.getD 2 .null) (if kindAst (env.getD 3 .null) == opNode .Tuple then
      "cannot use constraints with TypeVarTuple" else "cannot use bound with TypeVarTuple") s)⟩,
  ⟨[.call (.tok 35), .call .name, .call (.tok 11), .call (.rule 109)], false, fun env _ s =>
    (none, raisedFrom (env.getD 2 .null) (if kindAst (env.getD 3 .null) == opNode .Tuple then
      "cannot use constraints with ParamSpec" else "cannot use bound with ParamSpec") s)⟩]

theorem msgOf_plain (m : String) (hp : '%' ∉ m.toList) : msgOf [.str (m.toList.map Char.toNat)] = m := by
  simp only [msgOf, cpsStr_toList, formatMsg_plain _ hp, String.ofList_toList]

theorem altResult_fromv {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i : Nat} {me : AE} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_STARTING_FROM [.var i, me]))
    (hme : ∀ ex, evalA env ex me s = (.str (m.toList.map Char.toNat), s)) (hp : '%' ∉ m.toList) :
    altResult a g env st s = (none, raisedFrom (env.getD i .null) m s) := by
  rw [altResult_raise h1 (fun ex => by
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    rw [hme ex]
    simp only [callHelper, List.drop_succ_cons, List.drop_zero, List.getD_cons_zero, msgOf_plain m hp]
    rfl) (errOcc_raiseEKL _ _ _ _ _ _ _)]
  rfl

theorem evalA_kindTuple (env : Array Ast) (ex : Extra) (s : PS) (m1 m2 : String) :
    evalA env ex (.ite (.eq (.kind (.var 3)) (.ctor .Tuple)) (.str m1) (.str m2)) s =
      (.str ((if kindAst (env.getD 3 .null) == opNode .Tuple then m1 else m2).toList.map Char.toNat), s) := by
  rw [evalA_ite]
  have he : evalA env ex (.eq (.kind (.var 3)) (.ctor .Tuple)) s =
      (.int (if kindAst (env.getD 3 .null) == opNode .Tuple then 1 else 0), s) := by
    simp only [evalA, bind, StateT.bind, pure, StateT.pure]
    generalize env.getD 3 .null = e
    cases e <;> try rfl
    rename_i c fs l
    cases c <;> try rfl
    cases fs with
    | nil => rfl
    | cons k t => cases t <;> rfl
  rw [he]
  cases (kindAst (env.getD 3 .null) == opNode .Tuple) <;> rfl

theorem invalidTypeParam_proven : InvalidTypeParam := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  refine congrArg finish (runAlts_spec f _ _ ?_ _ _ _)
  refine altsAre_cons rfl rfl (fun env st s => ?_) (altsAre_cons rfl rfl (fun env st s => ?_) altsAre_nil)
  all_goals
    exact altResult_fromv rfl (fun ex => evalA_kindTuple env ex s _ _) (by split <;> decide)

end PyLean.PyGrammar.Peg
