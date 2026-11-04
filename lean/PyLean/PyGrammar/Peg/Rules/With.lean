import PyLean.PyGrammar.Peg.Rules.Base2

/-! `with_stmt` and `with_item` (`Grammar/python.gram:421-437`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `with_stmt` -/

/-- `with_stmt` (`Grammar/python.gram:421-431`):
```
    | invalid_with_stmt_indent
    | 'with' '(' a[asdl_withitem_seq*]=','.with_item+ ','? ')' ':' tc=[TYPE_COMMENT] b=block {
       _PyAST_With(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | 'with' a[asdl_withitem_seq*]=','.with_item+ ':' tc=[TYPE_COMMENT] b=block {
        _PyAST_With(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA) }
    | 'async' 'with' '(' a[asdl_withitem_seq*]=','.with_item+ ','? ')' ':' b=block {
       CHECK_VERSION(stmt_ty, 5, "Async with statements are", _PyAST_AsyncWith(a, b, NULL, EXTRA)) }
    | 'async' 'with' a[asdl_withitem_seq*]=','.with_item+ ':' tc=[TYPE_COMMENT] b=block {
       CHECK_VERSION(stmt_ty, 5, "Async with statements are", _PyAST_AsyncWith(a, b, NEW_TYPE_COMMENT(p, tc), EXTRA)) }
    | invalid_with_stmt
```
`','.with_item+` is the gather `_gather_34` (rule 311). First pass, with `t` the token under the
mark:
* neither `with` nor `async`: `NULL`;
* `with (items,?): tc? b` gives `With(items, b, tc)`;
* `with` not followed by `(`, or `with (...)` not followed by `:` (as in `with (a, b) as c:`),
  backs up and the second alternative gives `With(items', b, tc)` from the items read without
  parentheses;
* `async with (items,?): b` gives `AsyncWith(items, b, NULL)` under `CHECK_VERSION(5)`: this
  alternative has no `[TYPE_COMMENT]`, so a type comment after the `:` makes its `block` fail and
  the rule backs up to the fourth alternative, which reads the parenthesised items as one
  expression;
* `async with items: tc? b` gives `AsyncWith(items, b, tc)`, under the same check.
Second pass: an error from `invalid_with_stmt_indent` ends the rule, its `NULL` leads to the first
alternative, and when `with` is followed by neither `(` nor items, `invalid_with_stmt` decides. -/
def WithStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  let low (r : Ast × PS) (s : PS) : Prop := r.1 = .null ∧ r.2.errorIndicator = true ∧
    r.2.tok = (raiseError0 "SyntaxError"
      "Async with statements are only supported in Python 3.5 and greater"
      { s with errorIndicator := true }).2.tok
  (t.type ≠ 665 → t.type ≠ 716 → p.callInvalidRules = false →
    callRule (f + 15) 59 p = (.null, q.leave)) ∧
  (t.type = 665 → p.callInvalidRules = false →
    ∀ (a c b tcm : Ast) (to tr tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    expectToken 7 s1 = (.tok to, s2) → callRule (f + 7) 311 s2 = (a, s3) → a ≠ .null →
    expectToken 12 s3 = (c, s4) → s4.errorIndicator = false → expectToken 8 s4 = (.tok tr, s5) →
    expectToken 11 s5 = (.tok tc, s6) → expectToken 57 s6 = (tcm, s7) → s7.errorIndicator = false →
    callRule (f + 2) 33 s7 = (b, s8) → b ≠ .null → s8.errorIndicator = false →
    callRule (f + 15) 59 p = (mkAt .With [a, b, typeCommentOf tcm] (extraLoc t s8), s8.leave)) ∧
  (t.type = 665 → p.callInvalidRules = false →
    ∀ (a b tcm : Ast) (tc : Token) (s2 s3 s4 s5 s6 : PS),
    expectToken 7 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 7) 311 { s2 with mark := p.mark + 1 } = (a, s3) → a ≠ .null →
    expectToken 11 s3 = (.tok tc, s4) → expectToken 57 s4 = (tcm, s5) → s5.errorIndicator = false →
    callRule (f + 4) 33 s5 = (b, s6) → b ≠ .null → s6.errorIndicator = false →
    callRule (f + 15) 59 p = (mkAt .With [a, b, typeCommentOf tcm] (extraLoc t s6), s6.leave)) ∧
  (t.type = 665 → p.callInvalidRules = false →
    ∀ (a0 c0 a b tcm : Ast) (to tr tc : Token) (s2 s3 s4 s5 s6 s7 s8 s9 s10 : PS),
    expectToken 7 s1 = (.tok to, s2) → callRule (f + 7) 311 s2 = (a0, s3) → a0 ≠ .null →
    expectToken 12 s3 = (c0, s4) → s4.errorIndicator = false → expectToken 8 s4 = (.tok tr, s5) →
    expectToken 11 s5 = (.null, s6) → s6.errorIndicator = false →
    callRule (f + 7) 311 { s6 with mark := p.mark + 1 } = (a, s7) → a ≠ .null →
    expectToken 11 s7 = (.tok tc, s8) → expectToken 57 s8 = (tcm, s9) → s9.errorIndicator = false →
    callRule (f + 4) 33 s9 = (b, s10) → b ≠ .null → s10.errorIndicator = false →
    callRule (f + 15) 59 p = (mkAt .With [a, b, typeCommentOf tcm] (extraLoc t s10), s10.leave)) ∧
  (t.type = 716 → p.callInvalidRules = false →
    ∀ (a c b : Ast) (tw to tr tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    expectToken 665 s1 = (.tok tw, s2) → expectToken 7 s2 = (.tok to, s3) →
    callRule (f + 4) 311 s3 = (a, s4) → a ≠ .null →
    expectToken 12 s4 = (c, s5) → s5.errorIndicator = false → expectToken 8 s5 = (.tok tr, s6) →
    expectToken 11 s6 = (.tok tc, s7) →
    callRule f 33 s7 = (b, s8) → b ≠ .null → s8.errorIndicator = false →
    (5 ≤ s8.featureVersion →
      callRule (f + 15) 59 p = (mkAt .AsyncWith [a, b, .null] (extraLoc t s8), s8.leave)) ∧
    (s8.featureVersion < 5 → low (callRule (f + 15) 59 p) s8)) ∧
  (t.type = 716 → p.callInvalidRules = false →
    ∀ (a b tcm : Ast) (tw tw' tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    expectToken 665 s1 = (.tok tw, s2) → expectToken 7 s2 = (.null, s3) → s3.errorIndicator = false →
    expectToken 665 { s3 with mark := p.mark + 1 } = (.tok tw', s4) →
    callRule (f + 4) 311 s4 = (a, s5) → a ≠ .null →
    expectToken 11 s5 = (.tok tc, s6) → expectToken 57 s6 = (tcm, s7) → s7.errorIndicator = false →
    callRule (f + 1) 33 s7 = (b, s8) → b ≠ .null → s8.errorIndicator = false →
    (5 ≤ s8.featureVersion → callRule (f + 15) 59 p =
      (mkAt .AsyncWith [a, b, typeCommentOf tcm] (extraLoc t s8), s8.leave)) ∧
    (s8.featureVersion < 5 → low (callRule (f + 15) 59 p) s8)) ∧
  (t.type = 716 → p.callInvalidRules = false →
    ∀ (a0 c0 a b tcm : Ast) (tw to tr tc tw' tc' : Token)
      (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 : PS),
    expectToken 665 s1 = (.tok tw, s2) → expectToken 7 s2 = (.tok to, s3) →
    callRule (f + 4) 311 s3 = (a0, s4) → a0 ≠ .null →
    expectToken 12 s4 = (c0, s5) → s5.errorIndicator = false → expectToken 8 s5 = (.tok tr, s6) →
    expectToken 11 s6 = (.tok tc, s7) → callRule f 33 s7 = (.null, s8) → s8.errorIndicator = false →
    expectToken 665 { s8 with mark := p.mark + 1 } = (.tok tw', s9) →
    callRule (f + 4) 311 s9 = (a, s10) → a ≠ .null →
    expectToken 11 s10 = (.tok tc', s11) → expectToken 57 s11 = (tcm, s12) →
    s12.errorIndicator = false →
    callRule (f + 1) 33 s12 = (b, s13) → b ≠ .null → s13.errorIndicator = false →
    5 ≤ s13.featureVersion → callRule (f + 15) 59 p =
      (mkAt .AsyncWith [a, b, typeCommentOf tcm] (extraLoc t s13), s13.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 10) 243 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 15) 59 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 665 → p.callInvalidRules = true →
    ∀ (a c b tcm : Ast) (to tr tc : Token) (s0 s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 10) 243 q = (.null, s0) → s0.errorIndicator = false →
    expectToken 7 { s0 with mark := p.mark + 1 } = (.tok to, s2) →
    callRule (f + 7) 311 s2 = (a, s3) → a ≠ .null →
    expectToken 12 s3 = (c, s4) → s4.errorIndicator = false → expectToken 8 s4 = (.tok tr, s5) →
    expectToken 11 s5 = (.tok tc, s6) → expectToken 57 s6 = (tcm, s7) → s7.errorIndicator = false →
    callRule (f + 2) 33 s7 = (b, s8) → b ≠ .null → s8.errorIndicator = false →
    callRule (f + 15) 59 p = (mkAt .With [a, b, typeCommentOf tcm] (extraLoc t s8), s8.leave)) ∧
  (t.type = 665 → p.callInvalidRules = true → ∀ (v : Ast) (s0 s2 s3 s4 : PS),
    callRule (f + 10) 243 q = (.null, s0) → s0.errorIndicator = false →
    expectToken 7 { s0 with mark := p.mark + 1 } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 7) 311 { s2 with mark := p.mark + 1 } = (.null, s3) → s3.errorIndicator = false →
    s3.callInvalidRules = true → callRule (f + 5) 242 { s3 with mark := p.mark } = (v, s4) →
    v = .null → callRule (f + 15) 59 p = (.null, { s4 with mark := p.mark }.leave))

theorem withStmt_proven : WithStmt := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 59 = r59 from rfl, r59]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have tok_ok : ∀ g ty, (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ g ty, (q.tokenAt p.mark).type ≠ ty → runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  have again : ∀ g ty (s : PS), TokGrows q s → (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) { s with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 }) :=
    fun g ty s gs ht => by rw [call_tok, expect_again gs hlt, ite_t ht]
  have again_no : ∀ g ty (s : PS), TokGrows q s → (q.tokenAt p.mark).type ≠ ty →
      runCall (g + 1) (.tok ty) { s with mark := p.mark } = (.null, { s with mark := p.mark }) :=
    fun g ty s gs ht => by rw [call_tok, expect_again gs hlt, ite_f ht]
  have hmsg : toString (cpsStr ("Async with statements are".toList.map Char.toNat)) ++
      toString " only supported in Python 3." ++ toString (5 : Int) ++ toString " and greater" =
      "Async with statements are only supported in Python 3.5 and greater" := by decide +kernel
  refine ⟨fun h1 h2 hinv => ?_,
    fun ht hinv a c b tcm to tr tc s2 s3 s4 s5 s6 s7 s8 h2 h3 ha h4 h4e h5 h6 h7 h7e h8 hb h8e => ?_,
    fun ht hinv a b tcm tc s2 s3 s4 s5 s6 h2 h2e h3 ha h4 h5 h5e h6 hb h6e => ?_,
    fun ht hinv a0 c0 a b tcm to tr tc s2 s3 s4 s5 s6 s7 s8 s9 s10 h2 h3 ha0 h4 h4e h5 h6 h6e h7 ha
      h8 h9 h9e h10 hb h10e => ?_,
    fun ht hinv a c b tw to tr tc s2 s3 s4 s5 s6 s7 s8 h2 h3 h4 ha h5 h5e h6 h7 h8 hb h8e => ?_,
    fun ht hinv a b tcm tw tw' tc s2 s3 s4 s5 s6 s7 s8 h2 h3 h3e h4 h5 ha h6 h7 h7e h8 hb h8e => ?_,
    fun ht hinv a0 c0 a b tcm tw to tr tc tw' tc' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 h2 h3 h4
      ha0 h5 h5e h6 h7 h8 h8e h9 h10 ha h11 h12 h12e h13 hb h13e hv => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv a c b tcm to tr tc s0 s2 s3 s4 s5 s6 s7 s8 h0 h0e h2 h3 ha h4 h4e h5 h6 h7 h7e h8 hb
      h8e => ?_,
    fun ht hinv v s0 s2 s3 s4 h0 h0e h2 h2e h3 h3e h3i h4 hv => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ h1)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h1)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h2)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h2)), hq,
      alts_skip (by simp [hci, hinv]), alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ha, items_opt (by rw [call_tok, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_tok, h6]) (by simp),
        items_opt (by rw [call_tok, h7]) h7e, items_call (by rw [call_rule, h8]) hb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h8e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · have g2 : TokGrows q s2 := tg_mark' (tg_expect h2) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (again _ _ _ g2 ht) (by simp), items_call (by rw [call_rule, h3]) ha,
        items_call (by rw [call_tok, h4]) (by simp), items_opt (by rw [call_tok, h5]) h5e,
        items_call (by rw [call_rule, h6]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h6e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · have g6 : TokGrows q s6 := tg_mark' (((((tg_expect h2).trans (tg_call h3)).trans
      (tg_expect h4)).trans (tg_expect h5)).trans (tg_expect h6)) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ha0, items_opt (by rw [call_tok, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_call_null (by rw [call_tok, h6])]),
      alts_ok (by rfl) (E s6 h6e) (by
      dsimp only
      rw [items_call (again _ _ _ g6 ht) (by simp), items_call (by rw [call_rule, h7]) ha,
        items_call (by rw [call_tok, h8]) (by simp), items_opt (by rw [call_tok, h9]) h9e,
        items_call (by rw [call_rule, h10]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h10e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))),
      hq, alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_tok, h3]) (by simp),
        items_call (by rw [call_rule, h4]) ha, items_opt (by rw [call_tok, h5]) h5e,
        items_call (by rw [call_tok, h6]) (by simp), items_call (by rw [call_tok, h7]) (by simp),
        items_call (by rw [call_rule, h8]) hb, items_nil]),
      altResult_extra rfl rfl]
    have hn : evalA (((((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok tw)).push
          (.tok to)).push a).push c).push (.tok tr)).push (.tok tc)).push b)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s8))
        (.mk .AsyncWith [(.var 3), (.var 7), .null, .extra0, .extra1, .extra2, .extra3]) s8 =
        (mkAt .AsyncWith [a, b, .null] (extraLoc (q.tokenAt p.mark) s8), s8) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs]
      rfl
    have hnn : mkAt .AsyncWith [a, b, .null] (extraLoc (q.tokenAt p.mark) s8) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 5) (m := "Async with statements are") hn hnn (by omega)]
      simp [mkAst, mkAt, nonNull, h8e]
    · rw [evalA_cv_low (v := 5) (m := "Async with statements are") hn hnn (by omega)]
      simp only [hmsg]
      exact cv_low_result _ rfl
  · have g3 : TokGrows q s3 := tg_mark' ((tg_expect h2).trans (tg_expect h3)) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))),
      hq, alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_tok, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ _ g3 ht) (by simp), items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) ha,
        items_call (by rw [call_tok, h6]) (by simp), items_opt (by rw [call_tok, h7]) h7e,
        items_call (by rw [call_rule, h8]) hb, items_nil]),
      altResult_extra rfl rfl]
    have hn : evalA (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok tw')).push
          a).push (.tok tc)).push tcm).push b)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s8))
        (.mk .AsyncWith [(.var 2), (.var 5), (.call .NEW_TYPE_COMMENT [(.var 4)]), .extra0, .extra1,
          .extra2, .extra3]) s8 =
        (mkAt .AsyncWith [a, b, typeCommentOf tcm] (extraLoc (q.tokenAt p.mark) s8), s8) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs, callHelper]
      rfl
    have hnn : mkAt .AsyncWith [a, b, typeCommentOf tcm] (extraLoc (q.tokenAt p.mark) s8) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 5) (m := "Async with statements are") hn hnn (by omega)]
      simp [mkAst, mkAt, nonNull, h8e]
    · rw [evalA_cv_low (v := 5) (m := "Async with statements are") hn hnn (by omega)]
      simp only [hmsg]
      exact cv_low_result _ rfl
  · have g8 : TokGrows q s8 := tg_mark' (((((((tg_expect h2).trans (tg_expect h3)).trans
      (tg_call h4)).trans (tg_expect h5)).trans (tg_expect h6)).trans (tg_expect h7)).trans
      (tg_call h8)) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))),
      hq, alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_tok, h3]) (by simp),
        items_call (by rw [call_rule, h4]) ha0, items_opt (by rw [call_tok, h5]) h5e,
        items_call (by rw [call_tok, h6]) (by simp), items_call (by rw [call_tok, h7]) (by simp),
        items_call_null (by rw [call_rule, h8])]),
      alts_ok (by rfl) (E s8 h8e) (by
      dsimp only
      rw [items_call (again _ _ _ g8 ht) (by simp), items_call (by rw [call_tok, h9]) (by simp),
        items_call (by rw [call_rule, h10]) ha,
        items_call (by rw [call_tok, h11]) (by simp), items_opt (by rw [call_tok, h12]) h12e,
        items_call (by rw [call_rule, h13]) hb, items_nil]),
      altResult_extra rfl rfl]
    have hn : evalA (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok tw')).push
          a).push (.tok tc')).push tcm).push b)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s13))
        (.mk .AsyncWith [(.var 2), (.var 5), (.call .NEW_TYPE_COMMENT [(.var 4)]), .extra0, .extra1,
          .extra2, .extra3]) s13 =
        (mkAt .AsyncWith [a, b, typeCommentOf tcm] (extraLoc (q.tokenAt p.mark) s13), s13) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs, callHelper]
      rfl
    have hnn : mkAt .AsyncWith [a, b, typeCommentOf tcm] (extraLoc (q.tokenAt p.mark) s13) ≠ .null := by
      simp [mkAt, mkAst]
    rw [evalA_cv_ok (v := 5) (m := "Async with statements are") hn hnn (by omega)]
    simp [mkAst, mkAt, nonNull, h13e]
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (again _ _ _ g0 ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ha, items_opt (by rw [call_tok, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_tok, h6]) (by simp),
        items_opt (by rw [call_tok, h7]) h7e, items_call (by rw [call_rule, h8]) hb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h8e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · subst hv
    have g0 : TokGrows q s0 := tg_call h0
    have g2 : TokGrows q s2 := g0.trans (tg_mark' (tg_expect h2) _)
    have g3 : TokGrows q s3 := g2.trans (tg_mark' (tg_call h3) _)
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (again _ _ _ g0 ht) (by simp), items_call_null (by rw [call_tok, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (again _ _ _ g2 ht) (by simp), items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (items_call_null (again_no _ _ _ g3 (by omega))),
      alts_fail (by rfl) (E s3 h3e) (items_call_null (again_no _ _ _ g3 (by omega))),
      alts_fail (by simp [h3i]) (E s3 h3e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h4])]), alts_nil]
    rfl

/-! ### `with_item` -/

/-- `with_item` (`Grammar/python.gram:433-436`):
```
    | e=expression 'as' t=star_target &(',' | ')' | ':') { _PyAST_withitem(e, t, p->arena) }
    | invalid_with_item
    | e=expression { _PyAST_withitem(e, NULL, p->arena) }
```
No `EXTRA`. `e as t` followed by `,`, `)` or `:` (the lookahead `_tmp_34`, rule 312, which consumes
nothing) gives `withitem(e, t)`, ending after `t`; `e` with no `as`, or `e as t` followed by
anything else, backs up: in the first pass the third alternative gives `withitem(e', NULL)`; in
the second, `invalid_with_item` runs first, and its error ends the rule while its `NULL` leads to
the third alternative. -/
def WithItem : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (e tg v : Ast) (ta : Token) (s1 s2 s3 s4 : PS),
    callRule (f + 3) 109 p.enter = (e, s1) → e ≠ .null → expectToken 698 s1 = (.tok ta, s2) →
    callRule (f + 1) 196 s2 = (tg, s3) → tg ≠ .null → callRule f 312 s3 = (v, s4) → v ≠ .null →
    s4.errorIndicator = false →
    callRule (f + 8) 60 p = (mkAst .withitem_ [e, tg], { s4 with mark := s3.mark }.leave)) ∧
  (∀ (e e' : Ast) (s1 s2 s3 : PS),
    callRule (f + 3) 109 p.enter = (e, s1) → e ≠ .null → expectToken 698 s1 = (.null, s2) →
    s2.errorIndicator = false → s2.callInvalidRules = false →
    callRule (f + 1) 109 { s2 with mark := p.mark } = (e', s3) → e' ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 8) 60 p = (mkAst .withitem_ [e', .null], s3.leave)) ∧
  (∀ (e tg e' : Ast) (ta : Token) (s1 s2 s3 s4 s5 : PS),
    callRule (f + 3) 109 p.enter = (e, s1) → e ≠ .null → expectToken 698 s1 = (.tok ta, s2) →
    callRule (f + 1) 196 s2 = (tg, s3) → tg ≠ .null → callRule f 312 s3 = (.null, s4) →
    s4.errorIndicator = false → s4.callInvalidRules = false →
    callRule (f + 1) 109 { s4 with mark := p.mark } = (e', s5) → e' ≠ .null →
    s5.errorIndicator = false →
    callRule (f + 8) 60 p = (mkAst .withitem_ [e', .null], s5.leave)) ∧
  (∀ (e : Ast) (s1 s2 s3 : PS),
    callRule (f + 3) 109 p.enter = (e, s1) → e ≠ .null → expectToken 698 s1 = (.null, s2) →
    s2.errorIndicator = false → s2.callInvalidRules = true →
    callRule (f + 2) 233 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = true →
    callRule (f + 8) 60 p = (.null, { s3 with mark := p.mark }.leave)) ∧
  (∀ (e e' : Ast) (s1 s2 s3 s4 : PS),
    callRule (f + 3) 109 p.enter = (e, s1) → e ≠ .null → expectToken 698 s1 = (.null, s2) →
    s2.errorIndicator = false → s2.callInvalidRules = true →
    callRule (f + 2) 233 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 1) 109 { s3 with mark := p.mark } = (e', s4) → e' ≠ .null →
    s4.errorIndicator = false →
    callRule (f + 8) 60 p = (mkAst .withitem_ [e', .null], s4.leave)) ∧
  (∀ (s1 s2 : PS), callRule (f + 3) 109 p.enter = (.null, s1) → s1.errorIndicator = false →
    s1.callInvalidRules = false → callRule (f + 1) 109 { s1 with mark := p.mark } = (.null, s2) →
    callRule (f + 8) 60 p = (.null, { s2 with mark := p.mark }.leave))

theorem withItem_proven : WithItem := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 60 = r60 from rfl, r60]
  refine ⟨fun e tg v ta s1 s2 s3 s4 h1 hE h2 h3 ht h4 hv h4e => ?_,
    fun e e' s1 s2 s3 h1 hE h2 h2e h2i h3 hE' h3e => ?_,
    fun e tg e' ta s1 s2 s3 s4 s5 h1 hE h2 h3 ht h4 h4e h4i h5 hE' h5e => ?_,
    fun e s1 s2 s3 h1 hE h2 h2e h2i h3 h3e => ?_,
    fun e e' s1 s2 s3 s4 h1 hE h2 h2e h2i h3 h3e h4 hE' h4e => ?_,
    fun s1 s2 h1 h1e h1i h2 => ?_⟩
  · have hv' : nonNull v = true := by cases v <;> simp_all [nonNull]
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hE, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ht, items_look (by rw [call_rule, h4]) hv', items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h4e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hE, items_call_null (by rw [call_tok, h2])]),
      alts_skip (by simp [h2i]), alts_ok (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h3]) hE', items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hE, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ht, items_look_fail (b := true) (by rw [call_rule, h4]) rfl]),
      alts_skip (by simp [h4i]), alts_ok (by rfl) (E s4 h4e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h5]) hE', items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h5e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hE, items_call_null (by rw [call_tok, h2])]),
      alts_fail (by simp [h2i]) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_err (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = true from h3e)]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hE, items_call_null (by rw [call_tok, h2])]),
      alts_fail (by simp [h2i]) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h4]) hE', items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h4e]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_skip (by simp [h1i]), alts_fail (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h2])]), alts_nil]
    rfl

end PyLean.PyGrammar.Peg
