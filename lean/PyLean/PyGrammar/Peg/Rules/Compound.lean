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
    | 'async' 'for' ... (the same with AsyncFor)
    | invalid_for_target
```
With `t` the token under the mark, `for`:
* first pass, the whole alternative matching: `For(t, ex, b, el, type_comment)`;
* first pass, `star_expressions` failing after `in`: the cut ends the rule, `NULL` with the mark
  back and nothing else tried;
* second pass, `invalid_for_stmt` returning `NULL` with no error and the same failure after the
  cut: `NULL` again, and `invalid_for_target` (the last alternative) is not run: the rule ends in
  the state `star_expressions` left. -/
def ForStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 712 → p.callInvalidRules = false →
    ∀ (tg it body orelse tcm : Ast) (ti tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 7) 193 { q with mark := p.mark + 1 } = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 4) 112 s3 = (it, s4) → it ≠ .null →
    expectToken 11 s4 = (.tok tc, s5) → expectToken 57 s5 = (tcm, s6) → s6.errorIndicator = false →
    callRule (f + 1) 33 s6 = (body, s7) → body ≠ .null →
    callRule f 56 s7 = (orelse, s8) → s8.errorIndicator = false →
    callRule (f + 14) 58 p =
      (mkAt .For [tg, it, body, orelse, typeCommentOf tcm] (extraLoc t s8), s8.leave)) ∧
  (t.type = 712 → p.callInvalidRules = false →
    ∀ (tg : Ast) (ti : Token) (s2 s3 s4 : PS),
    callRule (f + 7) 193 { q with mark := p.mark + 1 } = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 4) 112 s3 = (.null, s4) →
    callRule (f + 14) 58 p = (.null, { s4 with mark := p.mark }.leave)) ∧
  (t.type = 712 → p.callInvalidRules = true →
    ∀ (tg : Ast) (ti : Token) (s0 s2 s3 s4 : PS),
    callRule (f + 9) 260 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 7) 193 { s0 with mark := p.mark + 1 } = (tg, s2) → tg ≠ .null →
    expectToken 713 s2 = (.tok ti, s3) → callRule (f + 4) 112 s3 = (.null, s4) →
    callRule (f + 14) 58 p = (.null, { s4 with mark := p.mark }.leave))

theorem forStmt_proven : ForStmt := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 58 = r58 from rfl, r58]
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 712 →
      runCall (g + 1) (.tok 712) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  refine ⟨fun ht hinv tg it body orelse tcm ti tc s2 s3 s4 s5 s6 s7 s8 h1 htg h2 h3 hit h4 h5 h5e
      h6 hb h7 h7e => ?_,
    fun ht hinv tg ti s2 s3 s4 h1 htg h2 h3 => ?_,
    fun ht hinv tg ti s0 s2 s3 s4 h0 h0e h1 htg h2 h3 => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call (by rw [call_rule, h3]) hit, items_call (by rw [call_tok, h4]) (by simp),
        items_opt (by rw [call_tok, h5]) h5e, items_call (by rw [call_rule, h6]) hb,
        items_opt (by rw [call_rule, h7]) h7e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h7e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · rw [alts_skip (by simp [hci, hinv]), alts_cut (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call_null (by rw [call_rule, h3])])]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    have e1 : runCall (f + 9) (.tok 712) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_cut (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) htg,
        items_call (by rw [call_tok, h2]) (by simp), items_cut,
        items_call_null (by rw [call_rule, h3])])]
    rfl

end PyLean.PyGrammar.Peg
