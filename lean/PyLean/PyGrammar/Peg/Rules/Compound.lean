import PyLean.PyGrammar.Peg.Rules.Base

/-! Compound statements of `Grammar/python.gram`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `for_stmt` -/

/-- `for_stmt` (`Grammar/python.gram:410-416`):
```
    | invalid_for_stmt
    | 'for' t=star_targets 'in' ~ ex=star_expressions ':' tc=[TYPE_COMMENT] b=block el=[else_block] {
        _PyAST_For(t, ex, b, el, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | 'async' 'for' t=star_targets 'in' ~ ex=star_expressions ':' tc=[TYPE_COMMENT] b=block el=[else_block] {
        CHECK_VERSION(stmt_ty, 5, "Async for loops are", _PyAST_AsyncFor(t, ex, b, el, NEW_TYPE_COMMENT(p, tc), EXTRA)) }
    | invalid_for_target
```
With `t` the token under the mark:
* first pass, neither `for` nor `async`: `NULL`, mark unmoved;
* first pass, the `for` alternative matching: `For(t, ex, b, el, type_comment)`;
* first pass, `async for ...` matching: `AsyncFor(...)` when `feature_version` is at least 5, and
  with a lower one `NULL` with the exception for "Async for loops are only supported in Python 3.5
  and greater";
* first pass, `star_expressions` failing after `in`: the cut ends the rule, `NULL` with the mark
  back;
* second pass: an error from `invalid_for_stmt` ends the rule; with `invalid_for_stmt` returning
  `NULL` and no error, a failure after the cut ends the rule without running `invalid_for_target`,
  while a failure before the cut (no `star_targets` after `for`) lets `invalid_for_target`, the
  last alternative, decide. -/
def ForStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ 712 → t.type ≠ 716 → p.callInvalidRules = false →
    callRule (f + 16) 58 p = (.null, q.leave)) ∧
  (t.type = 712 → p.callInvalidRules = false →
    ∀ (tg it body orelse tcm : Ast) (ti tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 9) 193 { q with mark := p.mark + 1 } = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 6) 112 s3 = (it, s4) → it ≠ .null →
    expectToken 11 s4 = (.tok tc, s5) → expectToken 57 s5 = (tcm, s6) → s6.errorIndicator = false →
    callRule (f + 3) 33 s6 = (body, s7) → body ≠ .null →
    callRule (f + 2) 56 s7 = (orelse, s8) → s8.errorIndicator = false →
    callRule (f + 16) 58 p =
      (mkAt .For [tg, it, body, orelse, typeCommentOf tcm] (extraLoc t s8), s8.leave)) ∧
  (t.type = 716 → p.callInvalidRules = false →
    ∀ (tg it body orelse tcm : Ast) (tf ti tc : Token) (s1 s2 s3 s4 s5 s6 s7 s8 : PS),
    expectToken 712 { q with mark := p.mark + 1 } = (.tok tf, s1) →
    callRule (f + 7) 193 s1 = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 4) 112 s3 = (it, s4) → it ≠ .null →
    expectToken 11 s4 = (.tok tc, s5) → expectToken 57 s5 = (tcm, s6) → s6.errorIndicator = false →
    callRule (f + 1) 33 s6 = (body, s7) → body ≠ .null →
    callRule f 56 s7 = (orelse, s8) → s8.errorIndicator = false →
    (5 ≤ s8.featureVersion → callRule (f + 16) 58 p =
      (mkAt .AsyncFor [tg, it, body, orelse, typeCommentOf tcm] (extraLoc t s8), s8.leave)) ∧
    (s8.featureVersion < 5 →
      (callRule (f + 16) 58 p).1 = .null ∧ (callRule (f + 16) 58 p).2.errorIndicator = true ∧
      (callRule (f + 16) 58 p).2.tok = (raiseError0 "SyntaxError"
        "Async for loops are only supported in Python 3.5 and greater"
        { s8 with errorIndicator := true }).2.tok)) ∧
  (t.type = 712 → p.callInvalidRules = false →
    ∀ (tg : Ast) (ti : Token) (s2 s3 s4 : PS),
    callRule (f + 9) 193 { q with mark := p.mark + 1 } = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 6) 112 s3 = (.null, s4) →
    callRule (f + 16) 58 p = (.null, { s4 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 11) 260 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 16) 58 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 712 → p.callInvalidRules = true →
    ∀ (tg : Ast) (ti : Token) (s0 s2 s3 s4 : PS),
    callRule (f + 11) 260 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 9) 193 { s0 with mark := p.mark + 1 } = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 6) 112 s3 = (.null, s4) →
    callRule (f + 16) 58 p = (.null, { s4 with mark := p.mark }.leave)) ∧
  (t.type = 712 → p.callInvalidRules = true →
    ∀ (v : Ast) (s0 s2 s3 : PS),
    callRule (f + 11) 260 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 9) 193 { s0 with mark := p.mark + 1 } = (.null, s2) → s2.errorIndicator = false →
    s2.callInvalidRules = true →
    callRule (f + 8) 235 { s2 with mark := p.mark } = (v, s3) →
    v = .null → callRule (f + 16) 58 p = (.null, { s3 with mark := p.mark }.leave))

theorem forStmt_proven : ForStmt := by
  intro f p q h
  obtain ⟨he, -, hci, hfv, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 58 = r58 from rfl, r58]
  have tok_ok : ∀ g ty, (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ g ty, (q.tokenAt p.mark).type ≠ ty → runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  refine ⟨fun h1 h2 hinv => ?_,
    fun ht hinv tg it body orelse tcm ti tc s2 s3 s4 s5 s6 s7 s8 h1 htg h2 h3 hit h4 h5 h5e
      h6 hb h7 h7e => ?_,
    fun ht hinv tg it body orelse tcm tf ti tc s1 s2 s3 s4 s5 s6 s7 s8 h0 h1 htg h2 h3 hit h4 h5 h5e
      h6 hb h7 h7e => ?_,
    fun ht hinv tg ti s2 s3 s4 h1 htg h2 h3 => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv tg ti s0 s2 s3 s4 h0 h0e h1 htg h2 h3 => ?_,
    fun ht hinv v s0 s2 s3 h0 h0e h1 h1e h1i h3 hv => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ h1)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h2)), hq, alts_skip (by simp [hci, hinv]),
      alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call (by rw [call_rule, h3]) hit, items_call (by rw [call_tok, h4]) (by simp),
        items_opt (by rw [call_tok, h5]) h5e, items_call (by rw [call_rule, h6]) hb,
        items_opt (by rw [call_rule, h7]) h7e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h7e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))),
      hq, alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h0]) (by simp),
        items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call (by rw [call_rule, h3]) hit, items_call (by rw [call_tok, h4]) (by simp),
        items_opt (by rw [call_tok, h5]) h5e, items_call (by rw [call_rule, h6]) hb,
        items_opt (by rw [call_rule, h7]) h7e, items_nil]), altResult_extra rfl rfl]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · have h5' : ¬ ((s8.featureVersion : Int) < 5) := by omega
      have hE : evalA (((((((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok tf)).push
          tg).push (.tok ti)).push (.int 1)).push it).push (.tok tc)).push tcm).push body).push orelse)
          (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s8))
          (.checkVersion (.int 5) (.str "Async for loops are")
            (.mk .AsyncFor [.var 2, .var 5, .var 8, .var 9, .call .NEW_TYPE_COMMENT [.var 7], .extra0,
              .extra1, .extra2, .extra3])) s8 =
          (mkAt .AsyncFor [tg, it, body, orelse, typeCommentOf tcm] (extraLoc (q.tokenAt p.mark) s8), s8) := by
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
          MonadStateOf.get, StateT.get, mkAst, callHelper]
        rw [ite_f h5']
        simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, StateT.pure, pure]
      rw [hE]
      simp [mkAst, mkAt, nonNull, h7e]
    · have h5' : (s8.featureVersion : Int) < 5 := by omega
      have hE : evalA (((((((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok tf)).push
          tg).push (.tok ti)).push (.int 1)).push it).push (.tok tc)).push tcm).push body).push orelse)
          (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s8))
          (.checkVersion (.int 5) (.str "Async for loops are")
            (.mk .AsyncFor [.var 2, .var 5, .var 8, .var 9, .call .NEW_TYPE_COMMENT [.var 7], .extra0,
              .extra1, .extra2, .extra3])) s8 =
          (.null, (raiseError0 "SyntaxError" "Async for loops are only supported in Python 3.5 and greater"
            { s8 with errorIndicator := true }).2) := by
        have hmsg : toString (cpsStr ("Async for loops are".toList.map Char.toNat)) ++
            toString " only supported in Python 3." ++ toString (5 : Int) ++ toString " and greater" =
            "Async for loops are only supported in Python 3.5 and greater" := by decide +kernel
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
          MonadStateOf.get, StateT.get, mkAst, callHelper]
        rw [ite_t h5']
        simp only [hmsg]
        rfl
      rw [hE]
      have hei := (frame_raiseError0 "SyntaxError"
        "Async for loops are only supported in Python 3.5 and greater"
        { s8 with errorIndicator := true }).grows.err rfl
      generalize raiseError0 "SyntaxError" "Async for loops are only supported in Python 3.5 and greater"
        { s8 with errorIndicator := true } = r at hei ⊢
      dsimp only
      split <;> simp [hei, PS.leave]
  · rw [alts_skip (by simp [hci, hinv]), alts_cut (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call_null (by rw [call_rule, h3])])]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    have e1 : runCall (f + 11) (.tok 712) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_cut (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call_null (by rw [call_rule, h3])])]
    rfl
  · subst hv
    have g0 : TokGrows q s0 := tg_call h0
    have g2 : TokGrows q s2 := g0.trans (tg_mark' (tg_call h1) _)
    have e1 : runCall (f + 11) (.tok 712) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    have e2 : runCall (f + 10) (.tok 716) { s2 with mark := p.mark } = (.null, { s2 with mark := p.mark }) := by
      rw [call_tok, expect_again g2 hlt, ite_f (by omega)]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
        dsimp only; rw [items_call e1 (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (items_call_null e2),
      alts_fail (by simp [h1i]) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]), alts_nil]
    rfl

/-! ### `assignment`, the augmented alternative -/

/-- `assignment` (`Grammar/python.gram:151-166`), its fourth alternative
`a=single_target b=augassign ~ c=annotated_rhs { _PyAST_AugAssign(a, b->kind, c, EXTRA) }`,
reached on `x += ...`: the annotated forms fail (`x` is a `NAME` not followed by `:`, and the
artificial `_tmp_11` of the parenthesised / subscript targets fails), and no `star_targets '='`
prefix matches (`_loop1_12`). Then:
* `annotated_rhs` succeeding gives `AugAssign(a, op, c)`, `op` the operator `augassign` returned;
* `annotated_rhs` failing hits the cut: `NULL` with the mark back, in either pass, so
  `invalid_assignment` (the last alternative) never runs after an augmented operator. -/
def AssignmentAug : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  ∀ (n a op k c : Ast) (tn : Token) (s0 s1 s2 s3 s4 s5 s6 : PS),
  nameToken q = (n, s0) → n ≠ .null → expectToken 11 s0 = (.null, s1) → s1.errorIndicator = false →
  callRule (f + 5) 288 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
  callRule (f + 4) 289 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
  callRule (f + 3) 199 { s3 with mark := p.mark } = (a, s4) → a ≠ .null →
  callRule (f + 2) 13 s4 = (op, s5) → op = rec_ .PAugOperator [k] →
  callRule f 12 s5 = (c, s6) →
  (c ≠ .null → s6.errorIndicator = false →
    callRule (f + 11) 11 p = (mkAt .AugAssign [a, k, c] (extraLoc (q.tokenAt p.mark) s6), s6.leave)) ∧
  (c = .null → callRule (f + 11) 11 p = (.null, { s6 with mark := p.mark }.leave))

theorem assignmentAug_proven : AssignmentAug := by
  intro f p q h n a op k c tn s0 s1 s2 s3 s4 s5 s6 h0 hn h1 h1e h2 h2e h3 h3e h4 ha h5 hop h6
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 11 = r11 from rfl, r11]
  have hop' : op ≠ .null := by rw [hop]; simp [rec_]
  refine ⟨fun hc h6e => ?_, fun hc => ?_⟩
  · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_name, h0]) hn, items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_ok (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h3e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h4]) ha, items_call (by rw [call_rule, h5]) hop', items_cut,
          items_call (by rw [call_rule, h6]) hc, items_nil]), altResult_extra rfl rfl]
    subst hop
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h6e,
      Bool.or_false, mkAt, extraLoc, locArgs, rec_]
    simp [mkAst, nonNull, h6e, StateT.pure, pure]
  · subst hc
    rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_name, h0]) hn, items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_cut (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h3e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h4]) ha, items_call (by rw [call_rule, h5]) hop', items_cut,
          items_call_null (by rw [call_rule, h6])])]
    rfl

/-- `assignment`'s first and third alternatives (`Grammar/python.gram:152-163`):
* `x: T [= v]`: `NAME ':' expression ['=' annotated_rhs]` gives, under `CHECK_VERSION(6, ...)`,
  `AnnAssign(x, T, v, simple=1)` with the name's context set to `Store`;
* `(x): T [= v]` and other non-`NAME` targets: with no `NAME` first, the artificial `_tmp_11`
  (`'(' single_target ')' | single_subscript_attribute_target`) gives the target, and the result
  is `AnnAssign(target, T, v, simple=0)`, under the same version check;
* `x = v` (the annotated forms failing as in `AssignmentAug`): the targets `(star_targets '=')+`,
  then `annotated_rhs` not followed by another `=` (a negative lookahead, nothing consumed), and an
  optional `TYPE_COMMENT`, give `Assign(targets, v, type_comment)`. -/
def AssignmentAnnPlain : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (∀ (id ctx b c : Ast) (l : Option Loc) (tc : Token) (s0 s1 s2 s3 : PS),
    nameToken q = (.node .Name [id, ctx] l, s0) → expectToken 11 s0 = (.tok tc, s1) →
    callRule (f + 4) 109 s1 = (b, s2) → b ≠ .null → callRule (f + 3) 287 s2 = (c, s3) →
    s3.errorIndicator = false → 6 ≤ s3.featureVersion →
    callRule (f + 11) 11 p =
      (mkAt .AnnAssign [.node .Name [id, opNode .Store] l, b, c, .int 1]
        (extraLoc (q.tokenAt p.mark) s3), s3.leave)) ∧
  (∀ (a b c : Ast) (tc : Token) (s0 s1 s2 s3 s4 : PS),
    nameToken q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 5) 288 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 3) 109 s2 = (b, s3) → b ≠ .null →
    callRule (f + 2) 287 s3 = (c, s4) → s4.errorIndicator = false → 6 ≤ s4.featureVersion →
    callRule (f + 11) 11 p =
      (mkAt .AnnAssign [a, b, c, .int 0] (extraLoc (q.tokenAt p.mark) s4), s4.leave)) ∧
  (∀ (n ts b tcm : Ast) (s0 s1 s2 s3 s4 s5 s6 : PS),
    nameToken q = (n, s0) → n ≠ .null → expectToken 11 s0 = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 288 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 289 { s2 with mark := p.mark } = (ts, s3) → ts ≠ .null →
    callRule (f + 3) 12 s3 = (b, s4) → b ≠ .null →
    expectToken 22 s4 = (.null, s5) →
    expectToken 57 { s5 with mark := s4.mark } = (tcm, s6) → s6.errorIndicator = false →
    callRule (f + 11) 11 p =
      (mkAt .Assign [ts, b, typeCommentOf tcm] (extraLoc (q.tokenAt p.mark) s6), s6.leave))

theorem assignmentAnnPlain_proven : AssignmentAnnPlain := by
  intro f p q h
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 11 = r11 from rfl, r11]
  refine ⟨fun id ctx b c l tc s0 s1 s2 s3 h0 h1 h2 hb h3 h3e hv => ?_,
    fun a b c tc s0 s1 s2 s3 s4 h0 h0e h1 ha h2 h3 hb h4 h4e hv => ?_,
    fun n ts b tcm s0 s1 s2 s3 s4 s5 s6 h0 hn h1 h1e h2 h2e h3 hts h4 hb h5 h6 h6e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h0]) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) hb, items_opt (by rw [call_rule, h3]) h3e, items_nil]),
      altResult_extra rfl rfl]
    have h6 : ¬ ((s3.featureVersion : Int) < 6) := by omega
    have hE : evalA ((((#[] : Array Ast).push (.node .Name [id, ctx] l)).push (.tok tc)).push b |>.push c)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s3))
        (.checkVersion (.int 6) (.str "Variable annotation syntax is")
          (.mk .AnnAssign [.check (.call .set_expr_context [.var 0, .ctor .Store]), .var 2, .var 3,
            .int 1, .extra0, .extra1, .extra2, .extra3])) s3 =
        (mkAt .AnnAssign [.node .Name [id, opNode .Store] l, b, c, .int 1]
          (extraLoc (q.tokenAt p.mark) s3), s3) := by
      have hsec : setExprContext (opNode .Store) 100000 (.node .Name [id, ctx] l) =
          .node .Name [id, opNode .Store] l := rfl
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, mkAst, callHelper]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
        Array.size_empty, List.getD, Option.getD_some]
      simp only [Nat.reduceEqDiff, ↓reduceIte, Option.getD_some, List.getElem?_cons_succ,
        List.getElem?_cons_zero, hsec]
      simp only [bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
      rw [ite_f h6]
      simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, StateT.pure, pure]
    rw [hE]
    simp [mkAst, mkAt, nonNull, h3e]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
          items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_extra rfl rfl]
    have h6 : ¬ ((s4.featureVersion : Int) < 6) := by omega
    have hE : evalA ((((#[] : Array Ast).push a).push (.tok tc)).push b |>.push c)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s4))
        (.checkVersion (.int 6) (.str "Variable annotations syntax is")
          (.mk .AnnAssign [.var 0, .var 2, .var 3, .int 0, .extra0, .extra1, .extra2, .extra3])) s4 =
        (mkAt .AnnAssign [a, b, c, .int 0] (extraLoc (q.tokenAt p.mark) s4), s4) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, mkAst]
      rw [ite_f h6]
      simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, StateT.pure, pure]
    rw [hE]
    simp [mkAst, mkAt, nonNull, h4e]
  · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_name, h0]) hn, items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) hts, items_call (by rw [call_rule, h4]) hb,
          items_look (b := false) (by rw [call_tok, h5]) rfl,
          items_opt (by rw [call_tok, h6]) h6e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h6e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h6e, StateT.pure, pure]

/-- `assignment` in the second pass: when no alternative matches without passing a cut (here: no
`NAME`, no `_tmp_11` target, no `star_targets '='`, no `single_target`), `invalid_assignment`, the
last alternative, runs from the start mark and its outcome is the rule's. -/
def AssignmentInvalid : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  ∀ (v : Ast) (s0 s1 s2 s3 s4 : PS),
  nameToken q = (.null, s0) → s0.errorIndicator = false →
  callRule (f + 5) 288 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
  callRule (f + 4) 289 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
  callRule (f + 3) 199 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
  s3.callInvalidRules = true →
  callRule (f + 2) 216 { s3 with mark := p.mark } = (v, s4) →
  (v = .null → callRule (f + 11) 11 p = (.null, { s4 with mark := p.mark }.leave))

theorem assignmentInvalid_proven : AssignmentInvalid := by
  intro f p q h v s0 s1 s2 s3 s4 h0 h0e h1 h1e h2 h2e h3 h3e h3i h4 hv
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  subst hv
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 11 = r11 from rfl, r11]
  rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h0])]),
    alts_fail (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
    alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
    alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
    alts_fail (by simp [h3i]) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h3e)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h4])]), alts_nil]
  rfl

/-- The rest of `assignment` (`Grammar/python.gram:151-166`):
* `x: T [= v]` and `(x): T [= v]` under a `feature_version` below 6: `CHECK_VERSION(6, ...)` fails,
  `NULL` with the exception for "Variable annotation syntax is only supported in Python 3.6 and
  greater" (first alternative) or "Variable annotations syntax is ..." (second);
* `x = v = w` where the third alternative's `!'='` fails after `v`: that alternative fails, the
  mark goes back, and with `augassign` not matching either, the first pass ends in `NULL`;
* second pass, `f() = 1`: a `NAME` not followed by `:`, then no `_tmp_11` target, no
  `star_targets '='`, no `single_target`: `invalid_assignment` decides. -/
def AssignmentMore : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (∀ (id ctx b c : Ast) (l : Option Loc) (tc : Token) (s0 s1 s2 s3 : PS),
    nameToken q = (.node .Name [id, ctx] l, s0) → expectToken 11 s0 = (.tok tc, s1) →
    callRule (f + 4) 109 s1 = (b, s2) → b ≠ .null → callRule (f + 3) 287 s2 = (c, s3) →
    s3.errorIndicator = false → s3.featureVersion < 6 →
    (callRule (f + 11) 11 p).1 = .null ∧ (callRule (f + 11) 11 p).2.errorIndicator = true ∧
    (callRule (f + 11) 11 p).2.tok = (raiseError0 "SyntaxError"
      "Variable annotation syntax is only supported in Python 3.6 and greater"
      { s3 with errorIndicator := true }).2.tok) ∧
  (∀ (a b c : Ast) (tc : Token) (s0 s1 s2 s3 s4 : PS),
    nameToken q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 5) 288 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 3) 109 s2 = (b, s3) → b ≠ .null →
    callRule (f + 2) 287 s3 = (c, s4) → s4.errorIndicator = false → s4.featureVersion < 6 →
    (callRule (f + 11) 11 p).1 = .null ∧ (callRule (f + 11) 11 p).2.errorIndicator = true ∧
    (callRule (f + 11) 11 p).2.tok = (raiseError0 "SyntaxError"
      "Variable annotations syntax is only supported in Python 3.6 and greater"
      { s4 with errorIndicator := true }).2.tok) ∧
  (∀ (n ts b a : Ast) (te : Token) (s0 s1 s2 s3 s4 s5 s6 s7 : PS),
    nameToken q = (n, s0) → n ≠ .null → expectToken 11 s0 = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 288 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 289 { s2 with mark := p.mark } = (ts, s3) → ts ≠ .null →
    callRule (f + 3) 12 s3 = (b, s4) → b ≠ .null →
    expectToken 22 s4 = (.tok te, s5) → s5.errorIndicator = false →
    callRule (f + 3) 199 { s5 with mark := p.mark } = (a, s6) → a ≠ .null →
    callRule (f + 2) 13 s6 = (.null, s7) → s7.errorIndicator = false →
    s7.callInvalidRules = false →
    callRule (f + 11) 11 p = (.null, { s7 with mark := p.mark }.leave)) ∧
  (∀ (n v : Ast) (s0 s1 s2 s3 s4 s5 : PS),
    nameToken q = (n, s0) → n ≠ .null → expectToken 11 s0 = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 288 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 289 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 199 { s3 with mark := p.mark } = (.null, s4) → s4.errorIndicator = false →
    s4.callInvalidRules = true →
    callRule (f + 2) 216 { s4 with mark := p.mark } = (v, s5) → v = .null →
    callRule (f + 11) 11 p = (.null, { s5 with mark := p.mark }.leave))

theorem assignmentMore_proven : AssignmentMore := by
  intro f p q h
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 11 = r11 from rfl, r11]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun id ctx b c l tc s0 s1 s2 s3 h0 h1 h2 hb h3 h3e hv => ?_,
    fun a b c tc s0 s1 s2 s3 s4 h0 h0e h1 ha h2 h3 hb h4 h4e hv => ?_,
    fun n ts b a te s0 s1 s2 s3 s4 s5 s6 s7 h0 hn h1 h1e h2 h2e h3 hts h4 hb h5 h5e h6 ha h7 h7e h7i => ?_,
    fun n v s0 s1 s2 s3 s4 s5 h0 hn h1 h1e h2 h2e h3 h3e h4 h4e h4i h5 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h0]) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) hb, items_opt (by rw [call_rule, h3]) h3e, items_nil]),
      altResult_extra rfl rfl]
    have h6 : (s3.featureVersion : Int) < 6 := by omega
    have hsec : setExprContext (opNode .Store) 100000 (.node .Name [id, ctx] l) =
        .node .Name [id, opNode .Store] l := rfl
    have hE : evalA ((((#[] : Array Ast).push (.node .Name [id, ctx] l)).push (.tok tc)).push b |>.push c)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s3))
        (.checkVersion (.int 6) (.str "Variable annotation syntax is")
          (.mk .AnnAssign [.check (.call .set_expr_context [.var 0, .ctor .Store]), .var 2, .var 3,
            .int 1, .extra0, .extra1, .extra2, .extra3])) s3 =
        (.null, (raiseError0 "SyntaxError"
          "Variable annotation syntax is only supported in Python 3.6 and greater"
          { s3 with errorIndicator := true }).2) := by
      have hmsg : toString (cpsStr ("Variable annotation syntax is".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (6 : Int) ++ toString " and greater" =
          "Variable annotation syntax is only supported in Python 3.6 and greater" := by decide +kernel
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, mkAst, callHelper]
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
        Array.size_empty, List.getD, Option.getD_some]
      simp only [Nat.reduceEqDiff, ↓reduceIte, Option.getD_some, List.getElem?_cons_succ,
        List.getElem?_cons_zero, hsec]
      simp only [bind, StateT.bind, pure, StateT.pure, get, getThe, MonadStateOf.get, StateT.get]
      rw [ite_t h6]
      simp only [hmsg]
      rfl
    rw [hE]
    have hei := (frame_raiseError0 "SyntaxError"
      "Variable annotation syntax is only supported in Python 3.6 and greater"
      { s3 with errorIndicator := true }).grows.err rfl
    generalize raiseError0 "SyntaxError"
      "Variable annotation syntax is only supported in Python 3.6 and greater"
      { s3 with errorIndicator := true } = r at hei ⊢
    dsimp only
    split <;> simp [hei, PS.leave]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
          items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_extra rfl rfl]
    have h6 : (s4.featureVersion : Int) < 6 := by omega
    have hE : evalA ((((#[] : Array Ast).push a).push (.tok tc)).push b |>.push c)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s4))
        (.checkVersion (.int 6) (.str "Variable annotations syntax is")
          (.mk .AnnAssign [.var 0, .var 2, .var 3, .int 0, .extra0, .extra1, .extra2, .extra3])) s4 =
        (.null, (raiseError0 "SyntaxError"
          "Variable annotations syntax is only supported in Python 3.6 and greater"
          { s4 with errorIndicator := true }).2) := by
      have hmsg : toString (cpsStr ("Variable annotations syntax is".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (6 : Int) ++ toString " and greater" =
          "Variable annotations syntax is only supported in Python 3.6 and greater" := by decide +kernel
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, mkAst]
      rw [ite_t h6]
      simp only [hmsg]
      rfl
    rw [hE]
    have hei := (frame_raiseError0 "SyntaxError"
      "Variable annotations syntax is only supported in Python 3.6 and greater"
      { s4 with errorIndicator := true }).grows.err rfl
    generalize raiseError0 "SyntaxError"
      "Variable annotations syntax is only supported in Python 3.6 and greater"
      { s4 with errorIndicator := true } = r at hei ⊢
    dsimp only
    split <;> simp [hei, PS.leave]
  · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_name, h0]) hn, items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) hts, items_call (by rw [call_rule, h4]) hb,
          items_look_fail (b := false) (by rw [call_tok, h5]) rfl]),
      alts_fail (by rfl) (E s5 h5e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h6]) ha, items_call_null (by rw [call_rule, h7])]),
      alts_skip (by simp [h7i]), alts_nil]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_name, h0]) hn, items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by dsimp only; rw [items_call_null (by rw [call_rule, h4])]),
      alts_fail (by simp [h4i]) (E s4 h4e) (by dsimp only; rw [items_call_null (by rw [call_rule, h5])]),
      alts_nil]
    rfl

/-! ### `compound_stmt` -/

/-- `compound_stmt` (`Grammar/python.gram:137-145`), dispatch by positive lookahead, in order:
```
    | &('def' | '@' | 'async') function_def
    | &'if' if_stmt
    | &('class' | '@') class_def
    | &('with' | 'async') with_stmt
    | &('for' | 'async') for_stmt
    | &'try' try_stmt
    | &'while' while_stmt
    | match_stmt
```
The lookaheads consume nothing (the `('def' | '@' | 'async')` groups are the artificial rules
`_tmp_6` to `_tmp_9`). Clauses: the first lookahead holding and `function_def` succeeding gives
its statement; at `if`, `if_stmt`'s; at a decorator, `function_def` failing falls through to
`class_def` (the `@` lookahead of the third alternative); and with every lookahead failing,
`match_stmt` decides. -/
def CompoundStmt : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (x v : Ast) (s0 s1 : PS), callRule (f + 7) 283 p.enter = (x, s0) → x ≠ .null →
    callRule (f + 6) 37 { s0 with mark := p.mark } = (v, s1) → v ≠ .null →
    s1.errorIndicator = false → callRule (f + 12) 10 p = (v, s1.leave)) ∧
  (∀ (v : Ast) (ti : Token) (s0 s1 s2 : PS), callRule (f + 7) 283 p.enter = (.null, s0) →
    s0.errorIndicator = false → expectToken 700 { s0 with mark := p.mark } = (.tok ti, s1) →
    callRule (f + 5) 54 { s1 with mark := p.mark } = (v, s2) → v ≠ .null →
    s2.errorIndicator = false → callRule (f + 12) 10 p = (v, s2.leave)) ∧
  (∀ (x y v : Ast) (s0 s1 s2 s3 s4 : PS), callRule (f + 7) 283 p.enter = (x, s0) → x ≠ .null →
    callRule (f + 6) 37 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    expectToken 700 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 5) 284 { s2 with mark := p.mark } = (y, s3) → y ≠ .null →
    callRule (f + 4) 35 { s3 with mark := p.mark } = (v, s4) → v ≠ .null →
    s4.errorIndicator = false → callRule (f + 12) 10 p = (v, s4.leave)) ∧
  (∀ (v : Ast) (s0 s1 s2 s3 s4 s5 s6 s7 : PS),
    callRule (f + 7) 283 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 700 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 5) 284 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 285 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 286 { s3 with mark := p.mark } = (.null, s4) → s4.errorIndicator = false →
    expectToken 674 { s4 with mark := p.mark } = (.null, s5) → s5.errorIndicator = false →
    expectToken 707 { s5 with mark := p.mark } = (.null, s6) → s6.errorIndicator = false →
    callRule f 65 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s7.leave))

theorem compoundStmt_proven : CompoundStmt := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 10 = r10 from rfl, r10]
  have nn : ∀ v : Ast, v ≠ .null → nonNull v = true := fun v hv => by
    cases v <;> simp_all [nonNull]
  refine ⟨fun x v s0 s1 h0 hx h1 hv h1e => ?_, fun v ti s0 s1 s2 h0 h0e h1 h2 hv h2e => ?_,
    fun x y v s0 s1 s2 s3 s4 h0 hx h1 h1e h2 h2e h3 hy h4 hv h4e => ?_,
    fun v s0 s1 s2 s3 s4 s5 s6 s7 h0 h0e h1 h1e h2 h2e h3 h3e h4 h4e h5 h5e h6 h6e h7 hv => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_look (by rw [call_rule, h0]) (nn x hx), PS.enter_mark, items_call (by rw [call_rule, h1]) hv,
        items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h1]) rfl, items_call (by rw [call_rule, h2]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_look (by rw [call_rule, h0]) (nn x hx), PS.enter_mark, items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h2]) rfl]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h3]) (nn y hy), items_call (by rw [call_rule, h4]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_fail (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h1]) rfl]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h3]) rfl]),
      alts_fail (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h3e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h4]) rfl]),
      alts_fail (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h5]) rfl]),
      alts_fail (by rfl) (show ({ s5 with mark := p.mark } : PS).errorIndicator = false from h5e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h6]) rfl]),
      alts_ok (by rfl) (show ({ s6 with mark := p.mark } : PS).errorIndicator = false from h6e) (by
        dsimp only; rw [items_call (by rw [call_rule, h7]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl

/-- The other dispatches of `compound_stmt` (`Grammar/python.gram:137-145`), each lookahead
holding with the earlier ones failing: `class_def` behind `&('class' | '@')`; `with_stmt` behind
`&('with' | 'async')`; `for_stmt` behind `&('for' | 'async')`, both for `for` and for `async for`,
where `function_def` and then `with_stmt` are tried first and fail; `try_stmt` behind `&'try'`;
`while_stmt` behind `&'while'`. -/
def CompoundStmtMore : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (y v : Ast) (s0 s1 s2 s3 : PS),
    callRule (f + 7) 283 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 700 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 5) 284 { s1 with mark := p.mark } = (y, s2) → y ≠ .null →
    callRule (f + 4) 35 { s2 with mark := p.mark } = (v, s3) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s3.leave)) ∧
  (∀ (y v : Ast) (s0 s1 s2 s3 s4 : PS),
    callRule (f + 7) 283 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 700 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 5) 284 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 285 { s2 with mark := p.mark } = (y, s3) → y ≠ .null →
    callRule (f + 3) 59 { s3 with mark := p.mark } = (v, s4) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s4.leave)) ∧
  (∀ (x y z v : Ast) (s0 s1 s2 s3 s4 s5 s6 s7 : PS),
    callRule (f + 7) 283 p.enter = (x, s0) → x ≠ .null →
    callRule (f + 6) 37 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    expectToken 700 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 5) 284 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 4) 285 { s3 with mark := p.mark } = (y, s4) → y ≠ .null →
    callRule (f + 3) 59 { s4 with mark := p.mark } = (.null, s5) → s5.errorIndicator = false →
    callRule (f + 3) 286 { s5 with mark := p.mark } = (z, s6) → z ≠ .null →
    callRule (f + 2) 58 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s7.leave)) ∧
  (∀ (z v : Ast) (s0 s1 s2 s3 s4 s5 : PS),
    callRule (f + 7) 283 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 700 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 5) 284 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 285 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 286 { s3 with mark := p.mark } = (z, s4) → z ≠ .null →
    callRule (f + 2) 58 { s4 with mark := p.mark } = (v, s5) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s5.leave)) ∧
  (∀ (v : Ast) (tt : Token) (s0 s1 s2 s3 s4 s5 s6 : PS),
    callRule (f + 7) 283 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 700 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 5) 284 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 285 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 286 { s3 with mark := p.mark } = (.null, s4) → s4.errorIndicator = false →
    expectToken 674 { s4 with mark := p.mark } = (.tok tt, s5) →
    callRule (f + 1) 61 { s5 with mark := p.mark } = (v, s6) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s6.leave)) ∧
  (∀ (v : Ast) (tw : Token) (s0 s1 s2 s3 s4 s5 s6 s7 : PS),
    callRule (f + 7) 283 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 700 { s0 with mark := p.mark } = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 5) 284 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 285 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 286 { s3 with mark := p.mark } = (.null, s4) → s4.errorIndicator = false →
    expectToken 674 { s4 with mark := p.mark } = (.null, s5) → s5.errorIndicator = false →
    expectToken 707 { s5 with mark := p.mark } = (.tok tw, s6) →
    callRule f 57 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 12) 10 p = (v, s7.leave))

theorem compoundStmtMore_proven : CompoundStmtMore := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 10 = r10 from rfl, r10]
  have nn : ∀ v : Ast, v ≠ .null → nonNull v = true := fun v hv => by
    cases v <;> simp_all [nonNull]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun y v s0 s1 s2 s3 h0 h0e h1 h1e h2 hy h3 hv => ?_,
    fun y v s0 s1 s2 s3 s4 h0 h0e h1 h1e h2 h2e h3 hy h4 hv => ?_,
    fun x y z v s0 s1 s2 s3 s4 s5 s6 s7 h0 hx h1 h1e h2 h2e h3 h3e h4 hy h5 h5e h6 hz h7 hv => ?_,
    fun z v s0 s1 s2 s3 s4 s5 h0 h0e h1 h1e h2 h2e h3 h3e h4 hz h5 hv => ?_,
    fun v tt s0 s1 s2 s3 s4 s5 s6 h0 h0e h1 h1e h2 h2e h3 h3e h4 h4e h5 h6 hv => ?_,
    fun v tw s0 s1 s2 s3 s4 s5 s6 s7 h0 h0e h1 h1e h2 h2e h3 h3e h4 h4e h5 h5e h6 h7 hv => ?_⟩
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h1]) rfl]),
      alts_ok (by rfl) (E s1 h1e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h2]) (nn y hy), items_call (by rw [call_rule, h3]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h3]) (nn y hy), items_call (by rw [call_rule, h4]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_look (by rw [call_rule, h0]) (nn x hx), PS.enter_mark,
        items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h3]) rfl]),
      alts_fail (by rfl) (E s3 h3e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h4]) (nn y hy), items_call_null (by rw [call_rule, h5])]),
      alts_ok (by rfl) (E s5 h5e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h6]) (nn z hz), items_call (by rw [call_rule, h7]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h3]) rfl]),
      alts_ok (by rfl) (E s3 h3e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h4]) (nn z hz), items_call (by rw [call_rule, h5]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h3]) rfl]),
      alts_fail (by rfl) (E s3 h3e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h4]) rfl]),
      alts_ok (by rfl) (E s4 h4e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h5]) rfl, items_call (by rw [call_rule, h6]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h0]) rfl, PS.enter_mark]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h3]) rfl]),
      alts_fail (by rfl) (E s3 h3e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h4]) rfl]),
      alts_fail (by rfl) (E s4 h4e) (by dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h5]) rfl]),
      alts_ok (by rfl) (E s5 h5e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h6]) rfl, items_call (by rw [call_rule, h7]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl

end PyLean.PyGrammar.Peg
