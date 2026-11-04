import PyLean.PyGrammar.Peg.Rules.Base

/-! `if`, `while`, `else` and `block` (`Grammar/python.gram:266-408`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `while_stmt` -/

/-- `while_stmt` (`Grammar/python.gram:403-405`):
```
    | invalid_while_stmt
    | 'while' a=named_expression ':' b=block c=[else_block] { _PyAST_While(a, b, c, EXTRA) }
```
First pass: at any token but `while`, `NULL`; `while a: b [else: c]` gives `While(a, b, c)`. Second
pass: an error from `invalid_while_stmt` ends the rule; its `NULL` with no error leads on to the
`while` alternative from the start mark. -/
def WhileStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ 707 → p.callInvalidRules = false → callRule (f + 10) 57 p = (.null, q.leave)) ∧
  (t.type = 707 → p.callInvalidRules = false → ∀ (a b c : Ast) (tc : Token) (s1 s2 s3 s4 : PS),
    callRule (f + 3) 119 { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 1) 33 s2 = (b, s3) → b ≠ .null →
    callRule f 56 s3 = (c, s4) → s4.errorIndicator = false →
    callRule (f + 10) 57 p = (mkAt .While [a, b, c] (extraLoc t s4), s4.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 5) 259 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 10) 57 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 707 → p.callInvalidRules = true → ∀ (a b c : Ast) (tc : Token) (s0 s1 s2 s3 s4 : PS),
    callRule (f + 5) 259 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 3) 119 { s0 with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 1) 33 s2 = (b, s3) → b ≠ .null →
    callRule f 56 s3 = (c, s4) → s4.errorIndicator = false →
    callRule (f + 10) 57 p = (mkAt .While [a, b, c] (extraLoc t s4), s4.leave))

theorem whileStmt_proven : WhileStmt := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 57 = r57 from rfl, r57]
  refine ⟨fun ht hinv => ?_, fun ht hinv a b c tc s1 s2 s3 s4 h1 ha h2 h3 hb h4 h4e => ?_,
    fun hinv s0 h0 h0e => ?_, fun ht hinv a b c tc s0 s1 s2 s3 s4 h0 h0e h1 ha h2 h3 hb h4 h4e => ?_⟩
  · have e1 : runCall (f + 5) (.tok 707) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null e1), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 5) (.tok 707) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_opt (by rw [call_rule, h4]) h4e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e]
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    have e1 : runCall (f + 5) (.tok 707) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_opt (by rw [call_rule, h4]) h4e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e]

/-! ### `if_stmt` -/

/-- `if_stmt` (`Grammar/python.gram:386-390`):
```
    | invalid_if_stmt
    | 'if' a=named_expression ':' b=block c=elif_stmt {
        _PyAST_If(a, b, CHECK(asdl_stmt_seq*, _PyPegen_singleton_seq(p, c)), EXTRA) }
    | 'if' a=named_expression ':' b=block c=[else_block] { _PyAST_If(a, b, c, EXTRA) }
```
First pass: at any token but `if`, `NULL`; with an `elif_stmt` after the block, `If(a, b, [elif])`
(the `elif` chain is the `orelse`); without one, the mark goes back and the third alternative
parses again and gives `If(a', b', else)`. Second pass: an error from `invalid_if_stmt` ends the
rule; its `NULL` with no error leads on to the `elif` alternative. -/
def IfStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ 700 → p.callInvalidRules = false → callRule (f + 11) 54 p = (.null, q.leave)) ∧
  (t.type = 700 → p.callInvalidRules = false → ∀ (a b e : Ast) (tc : Token) (s1 s2 s3 s4 : PS),
    callRule (f + 4) 119 { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 2) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 1) 55 s3 = (e, s4) → e ≠ .null → s4.errorIndicator = false →
    callRule (f + 11) 54 p = (mkAt .If [a, b, .seq [e]] (extraLoc t s4), s4.leave)) ∧
  (t.type = 700 → p.callInvalidRules = false →
    ∀ (a b a' b' c : Ast) (tc tc' : Token) (s1 s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 4) 119 { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 2) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 1) 55 s3 = (.null, s4) → s4.errorIndicator = false →
    callRule (f + 3) 119 { s4 with mark := p.mark + 1 } = (a', s5) → a' ≠ .null →
    expectToken 11 s5 = (.tok tc', s6) → callRule (f + 1) 33 s6 = (b', s7) → b' ≠ .null →
    callRule f 56 s7 = (c, s8) → s8.errorIndicator = false →
    callRule (f + 11) 54 p = (mkAt .If [a', b', c] (extraLoc t s8), s8.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 6) 256 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 11) 54 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 700 → p.callInvalidRules = true → ∀ (a b e : Ast) (tc : Token) (s0 s1 s2 s3 s4 : PS),
    callRule (f + 6) 256 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 4) 119 { s0 with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 2) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 1) 55 s3 = (e, s4) → e ≠ .null → s4.errorIndicator = false →
    callRule (f + 11) 54 p = (mkAt .If [a, b, .seq [e]] (extraLoc t s4), s4.leave))

theorem ifStmt_proven : IfStmt := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 54 = r54 from rfl, r54]
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 700 →
      runCall (g + 1) (.tok 700) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  refine ⟨fun ht hinv => ?_, fun ht hinv a b e tc s1 s2 s3 s4 h1 ha h2 h3 hb h4 hE h4e => ?_,
    fun ht hinv a b a' b' c tc tc' s1 s2 s3 s4 s5 s6 s7 s8 h1 ha h2 h3 hb h4 h4e h5 ha' h6 h7 hb' h8 h8e => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv a b e tc s0 s1 s2 s3 s4 h0 h0e h1 ha h2 h3 hb h4 hE h4e => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 700) q = (.null, q) := fun g => by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq, alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_call (by rw [call_rule, h4]) hE, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h4e]
  · have g4 : TokGrows q s4 := tg_call h4 |> fun g =>
      (((tg_call h1).trans (tg_expect h2)).trans (tg_call h3)).trans g |> fun g => tg_mark' g _
    have e2 : runCall (f + 5) (.tok 700) { s4 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s4 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g4 hlt, ite_t ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_call_null (by rw [call_rule, h4])]),
      alts_ok (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
      dsimp only
      rw [items_call e2 (by simp), items_call (by rw [call_rule, h5]) ha',
        items_call (by rw [call_tok, h6]) (by simp), items_call (by rw [call_rule, h7]) hb',
        items_opt (by rw [call_rule, h8]) h8e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h8e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h8e]
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    have e1 : runCall (f + 6) (.tok 700) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_call (by rw [call_rule, h4]) hE, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h4e]

/-! ### `else_block` -/

/-- `else_block` (`Grammar/python.gram:396-398`):
```
    | invalid_else_stmt
    | 'else' &&':' b=block { b }
```
First pass: at any token but `else`, `NULL`; `else: b` gives `b`; after `else`, the forced token
`&&':'` (`_PyPegen_expect_forced_token`) either takes the `:` or fails the rule in the state it
left (with its "expected ':'" error), never falling back. Second pass: an error from
`invalid_else_stmt` ends the rule. -/
def ElseBlock : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 704 → p.callInvalidRules = false → callRule (f + 8) 56 p = (.null, q.leave)) ∧
  (t.type = 704 → p.callInvalidRules = false → ∀ (b : Ast) (tc : Token) (s2 s3 : PS),
    forcedToken 11 ":" s1 = (.tok tc, s2) → callRule f 33 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false → callRule (f + 8) 56 p = (b, s3.leave)) ∧
  (t.type = 704 → p.callInvalidRules = false → ∀ (s2 : PS), forcedToken 11 ":" s1 = (.null, s2) →
    callRule (f + 8) 56 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 3) 258 p.enter = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 8) 56 p = (.null, { s0 with mark := p.mark }.leave))

theorem elseBlock_proven : ElseBlock := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hci' : p.enter.callInvalidRules = p.callInvalidRules := rfl
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 56 = r56 from rfl, r56]
  refine ⟨fun ht hinv => ?_, fun ht hinv b tc s2 s3 h2 h3 hb h3e => ?_, fun ht hinv s2 h2 => ?_,
    fun hinv s0 h0 h0e => ?_⟩
  · have e1 : runCall (f + 3) (.tok 704) p.enter = (.null, q) := by
      rw [call_tok, expect_entered h, ite_f ht]
    rw [alts_skip (by simp [hci', hinv]), alts_fail (by rfl) he' (items_call_null e1), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 3) (.tok 704) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    rw [alts_skip (by simp [hci', hinv]), alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have hb' : nonNull b = true := by cases b <;> simp_all [nonNull]
    simp [hb', h3e]
  · have e1 : runCall (f + 3) (.tok 704) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    rw [alts_skip (by simp [hci', hinv]), alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call_null (by rw [call_forcedTok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by simp [hci', hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl

/-! ### `block` -/

/-- `block (memo)` (`Grammar/python.gram:266-269`):
```
    | NEWLINE INDENT a=statements DEDENT { a }
    | simple_stmts
    | invalid_block
```
At a position not yet memoized for it: `NEWLINE INDENT statements DEDENT` gives the statements;
at a token other than `NEWLINE`, `simple_stmts`' result (a one-line body); in the second pass,
`NEWLINE` without `INDENT` and no `simple_stmts` leaves `invalid_block` (which raises "expected an
indented block") to decide. Results are memoized, `NULL` included. -/
def Block : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 33) = none →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  let memo (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo p.mark (1000 + 33) v s).2.leave)
  (t.type = 4 → ∀ (st : Ast) (ti td : Token) (s2 s3 s4 : PS), expectToken 5 s1 = (.tok ti, s2) →
    callRule (f + 1) 4 s2 = (st, s3) → st ≠ .null → expectToken 6 s3 = (.tok td, s4) →
    s4.errorIndicator = false → callRule (f + 8) 33 p = memo st s4) ∧
  (t.type ≠ 4 → ∀ (v : Ast) (s : PS), callRule (f + 2) 8 q = (v, s) → v ≠ .null →
    callRule (f + 8) 33 p = memo v s) ∧
  (t.type = 4 → ∀ (s2 s3 s4 : PS), expectToken 5 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 2) 8 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    s3.callInvalidRules = true → callRule (f + 1) 221 { s3 with mark := p.mark } = (.null, s4) →
    callRule (f + 8) 33 p = memo .null { s4 with mark := p.mark })

theorem block_proven : Block := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 33 = r33 from rfl, r33]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 4 →
      runCall (g + 1) (.tok 4) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  refine ⟨fun ht st ti td s2 s3 s4 h2 h3 hst h4 h4e => ?_, fun ht v s h1 hv => ?_,
    fun ht s2 s3 s4 h2 h2e h3 h3e h3i h4 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hst, items_call (by rw [call_tok, h4]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have hs' : nonNull st = true := by cases st <;> simp_all [nonNull]
    simp [hs', h4e, memoDone]
  · have e1 : runCall (f + 4) (.tok 4) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e1), hq, alts_ok (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by
      dsimp only; rw [items_call (tok_ok _ ht) (by simp), items_call_null (by rw [call_tok, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_fail (by simp [h3i]) (E s3 h3e) (by dsimp only; rw [items_call_null (by rw [call_rule, h4])]),
      alts_nil]
    rfl

end PyLean.PyGrammar.Peg
