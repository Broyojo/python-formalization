import PyLean.PyGrammar.Peg.Rules.Base

/-! `simple_stmt`, the dispatch of simple statements (`Grammar/python.gram:121-135`). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `simple_stmt (memo)` (`Grammar/python.gram:121-135`):
```
    | assignment
    | &"type" type_alias
    | &('import' | 'from' | "lazy") import_stmt
    | e=star_expressions { _PyAST_Expr(e, EXTRA) }
    | &'return' return_stmt
    | &'raise' raise_stmt
    | &'pass' pass_stmt
    ... (del, yield, assert, break, continue, global, nonlocal, each behind its keyword)
```
At a position not yet memoized for it: `assignment` is tried first and wins when it succeeds (so
`x = 1` is never an expression statement); otherwise, past the `type` and import lookaheads,
`star_expressions` gives `Expr(e)`; only when that fails too does a keyword statement run, here
`return_stmt` behind `&'return'` and `pass_stmt` behind `&'pass'` with the alternatives between
them failing. Every result is memoized at the start mark. -/
def SimpleStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 9) = none →
  let memo (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo p.mark (1000 + 9) v s).2.leave)
  (∀ (v : Ast) (s0 : PS), callRule (f + 7) 11 q = (v, s0) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s0) ∧
  (∀ (e x : Ast) (s0 s1 s2 s3 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (x, s2) → x = .null →
    s2.errorIndicator = false →
    callRule (f + 4) 112 { s2 with mark := p.mark } = (e, s3) → e ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 12) 9 p =
      memo (mkAt .Expr [e] (extraLoc (q.tokenAt p.mark) s3)) s3) ∧
  (∀ (v : Ast) (tr : Token) (s0 s1 s2 s3 s4 s5 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 112 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    expectToken 522 { s3 with mark := p.mark } = (.tok tr, s4) →
    callRule (f + 2) 14 { s4 with mark := p.mark } = (v, s5) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s5) ∧
  (∀ (v : Ast) (tp : Token) (s0 s1 s2 s3 s4 s5 s6 s7 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 112 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    expectToken 522 { s3 with mark := p.mark } = (.null, s4) → s4.errorIndicator = false →
    expectToken 632 { s4 with mark := p.mark } = (.null, s5) → s5.errorIndicator = false →
    expectToken 527 { s5 with mark := p.mark } = (.tok tp, s6) →
    callRule f 16 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s7)

theorem simpleStmt_proven : SimpleStmt := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 9 = r9 from rfl, r9]
  have nn : ∀ v : Ast, v ≠ .null → nonNull v = true := fun v hv => by
    cases v <;> simp_all [nonNull]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun v s0 h0 hv => ?_, fun e x s0 s1 s2 s3 h0 h0e h1 h1e h2 hx h2e h3 he3 h3e => ?_,
    fun v tr s0 s1 s2 s3 s4 s5 h0 h0e h1 h1e h2 h2e h3 h3e h4 h5 hv => ?_,
    fun v tp s0 s1 s2 s3 s4 s5 s6 s7 h0 h0e h1 h1e h2 h2e h3 h3e h4 h4e h5 h5e h6 h7 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h0]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hx
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) he3, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, memoDone]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h4]) rfl, items_call (by rw [call_rule, h5]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h4]) rfl]),
      alts_fail (by rfl) (E s4 h4e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h5]) rfl]),
      alts_ok (by rfl) (E s5 h5e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h6]) rfl, items_call (by rw [call_rule, h7]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl

end PyLean.PyGrammar.Peg
