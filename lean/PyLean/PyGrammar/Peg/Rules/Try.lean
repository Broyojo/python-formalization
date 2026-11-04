import PyLean.PyGrammar.Peg.Rules.Base2

/-! `elif`, `try`, `except`, `except*` and `finally` (`Grammar/python.gram:391-483`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `elif_stmt` -/

/-- `elif_stmt` (`Grammar/python.gram:391-395`):
```
    | invalid_elif_stmt
    | 'elif' a=named_expression ':' b=block c=elif_stmt {
        _PyAST_If(a, b, CHECK(asdl_stmt_seq*, _PyPegen_singleton_seq(p, c)), EXTRA) }
    | 'elif' a=named_expression ':' b=block c=[else_block] { _PyAST_If(a, b, c, EXTRA) }
```
First pass: at any token but `elif`, `NULL`; with another `elif_stmt` after the block,
`If(a, b, [elif])`, the chain nesting to the right; without one, the mark goes back and the third
alternative parses again and gives `If(a', b', else)`. Second pass: an error from
`invalid_elif_stmt` ends the rule; its `NULL` with no error leads on to the nested alternative. -/
def ElifStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ 705 → p.callInvalidRules = false → callRule (f + 11) 55 p = (.null, q.leave)) ∧
  (t.type = 705 → p.callInvalidRules = false → ∀ (a b e : Ast) (tc : Token) (s1 s2 s3 s4 : PS),
    callRule (f + 4) 119 { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 2) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 1) 55 s3 = (e, s4) → e ≠ .null → s4.errorIndicator = false →
    callRule (f + 11) 55 p = (mkAt .If [a, b, .seq [e]] (extraLoc t s4), s4.leave)) ∧
  (t.type = 705 → p.callInvalidRules = false →
    ∀ (a b a' b' c : Ast) (tc tc' : Token) (s1 s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 4) 119 { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 2) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 1) 55 s3 = (.null, s4) → s4.errorIndicator = false →
    callRule (f + 3) 119 { s4 with mark := p.mark + 1 } = (a', s5) → a' ≠ .null →
    expectToken 11 s5 = (.tok tc', s6) → callRule (f + 1) 33 s6 = (b', s7) → b' ≠ .null →
    callRule f 56 s7 = (c, s8) → s8.errorIndicator = false →
    callRule (f + 11) 55 p = (mkAt .If [a', b', c] (extraLoc t s8), s8.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 6) 257 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 11) 55 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 705 → p.callInvalidRules = true → ∀ (a b e : Ast) (tc : Token) (s0 s1 s2 s3 s4 : PS),
    callRule (f + 6) 257 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 4) 119 { s0 with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok tc, s2) → callRule (f + 2) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 1) 55 s3 = (e, s4) → e ≠ .null → s4.errorIndicator = false →
    callRule (f + 11) 55 p = (mkAt .If [a, b, .seq [e]] (extraLoc t s4), s4.leave))

theorem elifStmt_proven : ElifStmt := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 55 = r55 from rfl, r55]
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 705 →
      runCall (g + 1) (.tok 705) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  refine ⟨fun ht hinv => ?_, fun ht hinv a b e tc s1 s2 s3 s4 h1 ha h2 h3 hb h4 hE h4e => ?_,
    fun ht hinv a b a' b' c tc tc' s1 s2 s3 s4 s5 s6 s7 s8 h1 ha h2 h3 hb h4 h4e h5 ha' h6 h7 hb' h8 h8e => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv a b e tc s0 s1 s2 s3 s4 h0 h0e h1 ha h2 h3 hb h4 hE h4e => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 705) q = (.null, q) := fun g => by
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
    have e2 : runCall (f + 5) (.tok 705) { s4 with mark := p.mark } =
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
    have e1 : runCall (f + 6) (.tok 705) { s0 with mark := p.mark } =
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

/-! ### `finally_block` -/

/-- `finally_block` (`Grammar/python.gram:480-482`):
```
    | invalid_finally_stmt
    | 'finally' &&':' a=block { a }
```
No `EXTRA`. First pass: at any token but `finally`, `NULL`; `finally: a` gives the block `a`; after
`finally` the forced `&&':'` either takes the `:` or ends the rule in the state it left (with its
"expected ':'" error set). Second pass: an error from `invalid_finally_stmt` ends the rule, and its
`NULL` with no error leads on to the plain alternative. -/
def FinallyBlock : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 691 → p.callInvalidRules = false → callRule (f + 8) 64 p = (.null, q.leave)) ∧
  (t.type = 691 → p.callInvalidRules = false → ∀ (b : Ast) (tc : Token) (s2 s3 : PS),
    forcedToken 11 ":" s1 = (.tok tc, s2) → callRule f 33 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false → callRule (f + 8) 64 p = (b, s3.leave)) ∧
  (t.type = 691 → p.callInvalidRules = false → ∀ (s2 : PS), forcedToken 11 ":" s1 = (.null, s2) →
    s2.errorIndicator = true ∧ callRule (f + 8) 64 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 3) 247 p.enter = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 8) 64 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (b : Ast) (tf tc : Token) (s0 s1 s2 s3 : PS),
    callRule (f + 3) 247 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectToken 691 { s0 with mark := p.mark } = (.tok tf, s1) →
    forcedToken 11 ":" s1 = (.tok tc, s2) → callRule f 33 s2 = (b, s3) →
    b ≠ .null → s3.errorIndicator = false → callRule (f + 8) 64 p = (b, s3.leave))

theorem finallyBlock_proven : FinallyBlock := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hci' : p.enter.callInvalidRules = p.callInvalidRules := rfl
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 64 = r64 from rfl, r64]
  refine ⟨fun ht hinv => ?_, fun ht hinv b tc s2 s3 h2 h3 hb h3e => ?_, fun ht hinv s2 h2 => ?_,
    fun hinv s0 h0 h0e => ?_, fun hinv b tf tc s0 s1 s2 s3 h0 h0e h1 h2 h3 hb h3e => ?_⟩
  · have e1 : runCall (f + 3) (.tok 691) p.enter = (.null, q) := by
      rw [call_tok, expect_entered h, ite_f ht]
    rw [alts_skip (by simp [hci', hinv]), alts_fail (by rfl) he' (items_call_null e1), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 3) (.tok 691) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    rw [alts_skip (by simp [hci', hinv]), alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have hb' : nonNull b = true := by cases b <;> simp_all [nonNull]
    simp [hb', h3e]
  · have e1 : runCall (f + 3) (.tok 691) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    refine ⟨forcedToken_null_ei h2, ?_⟩
    rw [alts_skip (by simp [hci', hinv]), alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call_null (by rw [call_forcedTok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by simp [hci', hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have e1 : runCall (f + 3) (.tok 691) { s0 with mark := p.mark } = (.tok tf, s1) := by
      rw [call_tok, h1]
    rw [alts_fail (by simp [hci', hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have hb' : nonNull b = true := by cases b <;> simp_all [nonNull]
    simp [hb', h3e]

/-! ### `try_stmt` -/

/-- `try_stmt` (`Grammar/python.gram:441-447`):
```
    | invalid_try_stmt
    | 'try' &&':' b=block f=finally_block { _PyAST_Try(b, NULL, NULL, f, EXTRA) }
    | 'try' &&':' b=block ex[asdl_excepthandler_seq*]=except_block+ el=[else_block] f=[finally_block] { _PyAST_Try(b, ex, el, f, EXTRA) }
    | 'try' &&':' b=block ex[asdl_excepthandler_seq*]=except_star_block+ el=[else_block] f=[finally_block] {
        CHECK_VERSION(stmt_ty, 11, "Exception groups are",
                      _PyAST_TryStar(b, ex, el, f, EXTRA)) }
```
`except_block+` and `except_star_block+` are the artificial loops `_loop1_36` (rule 313) and
`_loop1_37` (rule 314). First pass:
* at any token but `try`, `NULL`;
* `try: b finally: f` gives `Try(b, [], [], f)`;
* after `try` the forced `&&':'` failing ends the rule with its error set, never falling back to
  the next alternative (which would see `error_indicator`);
* with no `finally_block` right after the block, the mark goes back and the second alternative
  gives `Try(b', handlers, orelse, finalbody)`, `orelse` and `finalbody` possibly `NULL`;
* with no `except_block` either, the third gives `TryStar(...)` when `feature_version` is at
  least 11, and with a lower one `NULL` with "Exception groups are only supported in Python 3.11
  and greater".
Second pass: an error from `invalid_try_stmt` ends the rule; its `NULL` with no error leads on
to the `finally` alternative. -/
def TryStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 674 → p.callInvalidRules = false → callRule (f + 13) 61 p = (.null, q.leave)) ∧
  (t.type = 674 → p.callInvalidRules = false → ∀ (b fb : Ast) (tc : Token) (s2 s3 s4 : PS),
    forcedToken 11 ":" s1 = (.tok tc, s2) → callRule (f + 5) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 4) 64 s3 = (fb, s4) → fb ≠ .null → s4.errorIndicator = false →
    callRule (f + 13) 61 p = (mkAt .Try [b, .null, .null, fb] (extraLoc t s4), s4.leave)) ∧
  (t.type = 674 → p.callInvalidRules = false → ∀ (s2 : PS), forcedToken 11 ":" s1 = (.null, s2) →
    s2.errorIndicator = true ∧ callRule (f + 13) 61 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (t.type = 674 → p.callInvalidRules = false →
    ∀ (b b' ex el fb : Ast) (tc tc' : Token) (s2 s3 s4 s5 s6 s7 s8 s9 : PS),
    forcedToken 11 ":" s1 = (.tok tc, s2) → callRule (f + 5) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 4) 64 s3 = (.null, s4) → s4.errorIndicator = false →
    forcedToken 11 ":" { s4 with mark := p.mark + 1 } = (.tok tc', s5) →
    callRule (f + 4) 33 s5 = (b', s6) → b' ≠ .null →
    callRule (f + 3) 313 s6 = (ex, s7) → ex ≠ .null →
    callRule (f + 2) 56 s7 = (el, s8) → s8.errorIndicator = false →
    callRule (f + 1) 64 s8 = (fb, s9) → s9.errorIndicator = false →
    callRule (f + 13) 61 p = (mkAt .Try [b', ex, el, fb] (extraLoc t s9), s9.leave)) ∧
  (t.type = 674 → p.callInvalidRules = false →
    ∀ (b b' b'' ex el fb : Ast) (tc tc' tc'' : Token) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 : PS),
    forcedToken 11 ":" s1 = (.tok tc, s2) → callRule (f + 5) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 4) 64 s3 = (.null, s4) → s4.errorIndicator = false →
    forcedToken 11 ":" { s4 with mark := p.mark + 1 } = (.tok tc', s5) →
    callRule (f + 4) 33 s5 = (b', s6) → b' ≠ .null →
    callRule (f + 3) 313 s6 = (.null, s7) → s7.errorIndicator = false →
    forcedToken 11 ":" { s7 with mark := p.mark + 1 } = (.tok tc'', s8) →
    callRule (f + 3) 33 s8 = (b'', s9) → b'' ≠ .null →
    callRule (f + 2) 314 s9 = (ex, s10) → ex ≠ .null →
    callRule (f + 1) 56 s10 = (el, s11) → s11.errorIndicator = false →
    callRule f 64 s11 = (fb, s12) → s12.errorIndicator = false →
    (11 ≤ s12.featureVersion → callRule (f + 13) 61 p =
      (mkAt .TryStar [b'', ex, el, fb] (extraLoc t s12), s12.leave)) ∧
    (s12.featureVersion < 11 →
      (callRule (f + 13) 61 p).1 = .null ∧ (callRule (f + 13) 61 p).2.errorIndicator = true ∧
      (callRule (f + 13) 61 p).2.tok = (raiseError0 "SyntaxError"
        "Exception groups are only supported in Python 3.11 and greater"
        { s12 with errorIndicator := true }).2.tok)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 8) 244 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 13) 61 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 674 → p.callInvalidRules = true → ∀ (b fb : Ast) (tc : Token) (s0 s2 s3 s4 : PS),
    callRule (f + 8) 244 q = (.null, s0) → s0.errorIndicator = false →
    forcedToken 11 ":" { s0 with mark := p.mark + 1 } = (.tok tc, s2) →
    callRule (f + 5) 33 s2 = (b, s3) → b ≠ .null →
    callRule (f + 4) 64 s3 = (fb, s4) → fb ≠ .null → s4.errorIndicator = false →
    callRule (f + 13) 61 p = (mkAt .Try [b, .null, .null, fb] (extraLoc t s4), s4.leave))

theorem tryStmt_proven : TryStmt := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 61 = r61 from rfl, r61]
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 674 →
      runCall (g + 1) (.tok 674) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have again : ∀ g (s : PS), TokGrows q s → (q.tokenAt p.mark).type = 674 →
      runCall (g + 1) (.tok 674) { s with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 }) :=
    fun g s gs ht => by rw [call_tok, expect_again gs hlt, ite_t ht]
  refine ⟨fun ht hinv => ?_, fun ht hinv b fb tc s2 s3 s4 h2 h3 hb h4 hfb h4e => ?_,
    fun ht hinv s2 h2 => ?_,
    fun ht hinv b b' ex el fb tc tc' s2 s3 s4 s5 s6 s7 s8 s9 h2 h3 hb h4 h4e h5 h6 hb' h7 hex h8 h8e
      h9 h9e => ?_,
    fun ht hinv b b' b'' ex el fb tc tc' tc'' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 h2 h3 hb h4 h4e h5
      h6 hb' h7 h7e h8 h9 hb'' h10 hex h11 h11e h12 h12e => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv b fb tc s0 s2 s3 s4 h0 h0e h2 h3 hb h4 hfb h4e => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 674) q = (.null, q) := fun g => by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq, alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_call (by rw [call_rule, h4]) hfb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e]
  · have h2e := forcedToken_null_ei h2
    refine ⟨h2e, ?_⟩
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call_null (by rw [call_forcedTok, h2])]),
      alts_err (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = true from h2e)]
    rfl
  · have g4 : TokGrows q s4 :=
      tg_mark' ((((tg_forced h2).trans (tg_call h3)).trans (tg_call h4))) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_call_null (by rw [call_rule, h4])]),
      alts_ok (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
      dsimp only
      rw [items_call (again _ _ g4 ht) (by simp), items_call (by rw [call_forcedTok, h5]) (by simp),
        items_call (by rw [call_rule, h6]) hb', items_call (by rw [call_rule, h7]) hex,
        items_opt (by rw [call_rule, h8]) h8e, items_opt (by rw [call_rule, h9]) h9e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h9e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h9e]
  · have g4 : TokGrows q s4 :=
      tg_mark' ((((tg_forced h2).trans (tg_call h3)).trans (tg_call h4))) _
    have g7 : TokGrows q s7 :=
      g4.trans (tg_mark' ((((tg_forced h5).trans (tg_call h6)).trans (tg_call h7))) _)
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_call_null (by rw [call_rule, h4])]),
      alts_fail (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
      dsimp only
      rw [items_call (again _ _ g4 ht) (by simp), items_call (by rw [call_forcedTok, h5]) (by simp),
        items_call (by rw [call_rule, h6]) hb', items_call_null (by rw [call_rule, h7])]),
      alts_ok (by rfl) (show ({ s7 with mark := p.mark } : PS).errorIndicator = false from h7e) (by
      dsimp only
      rw [items_call (again _ _ g7 ht) (by simp), items_call (by rw [call_forcedTok, h8]) (by simp),
        items_call (by rw [call_rule, h9]) hb'', items_call (by rw [call_rule, h10]) hex,
        items_opt (by rw [call_rule, h11]) h11e, items_opt (by rw [call_rule, h12]) h12e, items_nil]),
      altResult_extra rfl rfl]
    have hn : evalA (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok tc'')).push
          b'').push ex).push el).push fb)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s12))
        (.mk .TryStar [(.var 2), (.var 3), (.var 4), (.var 5), .extra0, .extra1, .extra2, .extra3]) s12 =
        (mkAt .TryStar [b'', ex, el, fb] (extraLoc (q.tokenAt p.mark) s12), s12) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs]
      rfl
    have hnn : mkAt .TryStar [b'', ex, el, fb] (extraLoc (q.tokenAt p.mark) s12) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 11) (m := "Exception groups are") hn hnn (by omega)]
      simp [mkAst, mkAt, nonNull, h12e]
    · rw [evalA_cv_low (v := 11) (m := "Exception groups are") hn hnn (by omega)]
      have hmsg : toString (cpsStr ("Exception groups are".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (11 : Int) ++ toString " and greater" =
          "Exception groups are only supported in Python 3.11 and greater" := by decide +kernel
      simp only [hmsg]
      exact cv_low_result _ rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call (again _ _ g0 ht) (by simp), items_call (by rw [call_forcedTok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_call (by rw [call_rule, h4]) hfb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e]

end PyLean.PyGrammar.Peg
