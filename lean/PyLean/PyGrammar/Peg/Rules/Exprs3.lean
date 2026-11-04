import PyLean.PyGrammar.Peg.Rules.Base

/-! `expression` and `star_expressions` (`Grammar/python.gram:716-737`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `expression` -/

/-- `expression (memo)` (`Grammar/python.gram:716-722`):
```
    | invalid_if_expression
    | invalid_expression
    | invalid_legacy_expression
    | if_expression
    | disjunction
    | lambdef
```
At a position not yet memoized for it. First pass (the three `invalid_` rules skipped):
`if_expression` first, then `disjunction`, then `lambdef`, the first non-`NULL` one being the
result, memoized. Second pass: the `invalid_` rules run first, in that order, and an error from
any of them ends the rule unmemoized; with all three returning `NULL` and no error, the first-pass
order follows. -/
def ExpressionRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 109) = none →
  let memo (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo p.mark (1000 + 109) v s).2.leave)
  (p.callInvalidRules = false → ∀ (v : Ast) (s : PS), callRule (f + 2) 110 q = (v, s) → v ≠ .null →
    callRule (f + 10) 109 p = memo v s) ∧
  (p.callInvalidRules = false → ∀ (v : Ast) (s0 s : PS), callRule (f + 2) 110 q = (.null, s0) →
    s0.errorIndicator = false → callRule (f + 1) 120 { s0 with mark := p.mark } = (v, s) →
    v ≠ .null → callRule (f + 10) 109 p = memo v s) ∧
  (p.callInvalidRules = false → ∀ (v : Ast) (s0 s1 s : PS), callRule (f + 2) 110 q = (.null, s0) →
    s0.errorIndicator = false → callRule (f + 1) 120 { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false → callRule f 149 { s1 with mark := p.mark } = (v, s) → v ≠ .null →
    callRule (f + 10) 109 p = memo v s) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 5) 214 q = (.null, s0) →
    s0.errorIndicator = true → s0.callInvalidRules = true → callRule (f + 10) 109 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 s1 : PS), callRule (f + 5) 214 q = (.null, s0) →
    s0.errorIndicator = false → s0.callInvalidRules = true →
    callRule (f + 4) 213 { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = true → s1.callInvalidRules = true → callRule (f + 10) 109 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 s1 s2 : PS), callRule (f + 5) 214 q = (.null, s0) →
    s0.errorIndicator = false → s0.callInvalidRules = true →
    callRule (f + 4) 213 { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false → s1.callInvalidRules = true → callRule (f + 3) 211 { s1 with mark := p.mark } = (.null, s2) →
    s2.errorIndicator = true → callRule (f + 10) 109 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (v : Ast) (s0 s1 s2 s : PS), callRule (f + 5) 214 q = (.null, s0) →
    s0.errorIndicator = false → s0.callInvalidRules = true →
    callRule (f + 4) 213 { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false → s1.callInvalidRules = true → callRule (f + 3) 211 { s1 with mark := p.mark } = (.null, s2) →
    s2.errorIndicator = false → callRule (f + 2) 110 { s2 with mark := p.mark } = (v, s) →
    v ≠ .null → callRule (f + 10) 109 p = memo v s)

theorem expressionRule_proven : ExpressionRule := by
  intro f p q h hn
  obtain ⟨he, -, hci, -, -, -, -⟩ := h.facts
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 109 = r109 from rfl, r109]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have Et : ∀ s : PS, s.errorIndicator = true → ({ s with mark := p.mark } : PS).errorIndicator = true :=
    fun s hs => hs
  refine ⟨fun hinv v s h1 hv => ?_, fun hinv v s0 s h0 h0e h1 hv => ?_,
    fun hinv v s0 s1 s h0 h0e h1 h1e h2 hv => ?_, fun hinv s0 h0 h0e h0i => ?_,
    fun hinv s0 s1 h0 h0e h0i h1 h1e h1i => ?_, fun hinv s0 s1 s2 h0 h0e h0i h1 h1e h1i h2 h2e => ?_,
    fun hinv v s0 s1 s2 s h0 h0e h0i h1 h1e h1i h2 h2e h3 hv => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_skip (by simp [hci, hinv]), alts_skip (by simp [hci, hinv]),
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_skip (by simp [hci, hinv]), alts_skip (by simp [hci, hinv]),
      alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_skip (by simp [hci, hinv]), alts_skip (by simp [hci, hinv]),
      alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s1 h1e) (by dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by simp [h0i]) (Et s0 h0e)]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by simp [h0i]) (E s0 h0e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_err (by simp [h1i]) (Et s1 h1e)]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by simp [h0i]) (E s0 h0e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by simp [h1i]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_err (by rfl) (Et s2 h2e)]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by simp [h0i]) (E s0 h0e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by simp [h1i]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by dsimp only; rw [items_call (by rw [call_rule, h3]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-! ### `star_expressions` -/

/-- `star_expressions` (`Grammar/python.gram:731-737`):
```
    | a=star_expression b=(',' c=star_expression { c })+ [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Load, EXTRA) }
    | a=star_expression ',' { _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_singleton_seq(p, a)), Load, EXTRA) }
    | star_expression
```
`a, b, c [,]` is a `Load` tuple of all the elements (the artificial loop `_loop1_56` gives the
rest); `a,` with nothing after the comma backs up and gives the one-element tuple; with no comma
at all, it backs up again and the result is the `star_expression` itself, not a tuple. -/
def StarExpressions : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  ∀ (a : Ast) (s1 : PS), callRule (f + 2) 113 q = (a, s1) → a ≠ .null →
  (∀ (b x : Ast) (s2 s3 : PS), callRule (f + 1) 333 s1 = (b, s2) → b ≠ .null →
    expectToken 12 s2 = (x, s3) → s3.errorIndicator = false →
    callRule (f + 7) 112 p =
      (mkAt .Tuple [.seq (a :: seqOf b), opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (∀ (a' : Ast) (tc : Token) (s2 s3 s4 : PS), callRule (f + 1) 333 s1 = (.null, s2) →
    s2.errorIndicator = false → callRule (f + 1) 113 { s2 with mark := p.mark } = (a', s3) →
    a' ≠ .null → expectToken 12 s3 = (.tok tc, s4) → s4.errorIndicator = false →
    callRule (f + 7) 112 p = (mkAt .Tuple [.seq [a'], opNode .Load] (extraLoc t s4), s4.leave)) ∧
  (∀ (a' a'' : Ast) (s2 s3 s4 s5 : PS), callRule (f + 1) 333 s1 = (.null, s2) →
    s2.errorIndicator = false → callRule (f + 1) 113 { s2 with mark := p.mark } = (a', s3) →
    a' ≠ .null → expectToken 12 s3 = (.null, s4) → s4.errorIndicator = false →
    callRule f 113 { s4 with mark := p.mark } = (a'', s5) → a'' ≠ .null →
    callRule (f + 7) 112 p = (a'', s5.leave))

theorem starExpressions_proven : StarExpressions := by
  intro f p q h
  intro t a s1 h1 ha
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 112 = r112 from rfl, r112]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun b x s2 s3 h2 hb h3 h3e => ?_, fun a' tc s2 s3 s4 h2 h2e h3 ha' h4 h4e => ?_,
    fun a' a'' s2 s3 s4 s5 h2 h2e h3 ha' h4 h4e h5 ha'' => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb,
        items_opt (by rw [call_tok, h3]) h3e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h3e, t]
  · rw [alts_fail (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_call (by rw [call_tok, h4]) (by simp),
          items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h4e, t]
  · rw [alts_fail (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) ha', items_call_null (by rw [call_tok, h4])]),
      alts_ok (by rfl) (E s4 h4e) (by
        dsimp only; rw [items_call (by rw [call_rule, h5]) ha'', items_nil]), altResult_none1 rfl rfl]
    rfl

end PyLean.PyGrammar.Peg
