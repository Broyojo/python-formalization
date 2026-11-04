import PyLean.PyGrammar.Peg.Rules.Base2

/-! `except_block` and `except_star_block` (`Grammar/python.gram:453-479`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `except_block` -/

/-- `except_block` (`Grammar/python.gram:453-466`):
```
    | invalid_except_stmt_indent
    | 'except' e=expression ':' b=block {
        _PyAST_ExceptHandler(e, NULL, b, EXTRA) }
    | 'except' e=expression 'as' t=NAME ':' b=block {
        _PyAST_ExceptHandler(e, ((expr_ty) t)->v.Name.id, b, EXTRA) }
    | 'except' e=expressions ':' b=block {
        CHECK_VERSION(
            excepthandler_ty,
            14,
            "except expressions without parentheses are",
            _PyAST_ExceptHandler(e, NULL, b, EXTRA)) }
    | 'except' ':' b=block { _PyAST_ExceptHandler(NULL, NULL, b, EXTRA) }
    | invalid_except_stmt
```
First pass:
* at any token but `except`, `NULL`;
* `except e: b` gives `ExceptHandler(e, NULL, b)`;
* with no `:` after the expression, the mark goes back and `except e as n: b` gives
  `ExceptHandler(e, n.id, b)`;
* with no `as` either, the third alternative reparses with `expressions` (`except A, B:`):
  `ExceptHandler(Tuple, NULL, b)` when `feature_version` is at least 14, and otherwise `NULL`
  with "except expressions without parentheses are only supported in Python 3.14 and greater";
* with no expression at all, `except: b` gives `ExceptHandler(NULL, NULL, b)`.
Second pass: an error from `invalid_except_stmt_indent` ends the rule, its `NULL` with no error
leads to the first plain alternative, and when every plain alternative fails, the last one,
`invalid_except_stmt`, decides. -/
def ExceptBlock : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 695 → p.callInvalidRules = false → callRule (f + 12) 62 p = (.null, q.leave)) ∧
  (t.type = 695 → p.callInvalidRules = false → ∀ (e b : Ast) (tc : Token) (s2 s3 s4 : PS),
    callRule (f + 5) 109 s1 = (e, s2) → e ≠ .null → expectToken 11 s2 = (.tok tc, s3) →
    callRule (f + 3) 33 s3 = (b, s4) → b ≠ .null → s4.errorIndicator = false →
    callRule (f + 12) 62 p = (mkAt .ExceptHandler [e, .null, b] (extraLoc t s4), s4.leave)) ∧
  (t.type = 695 → p.callInvalidRules = false →
    ∀ (e e' n b : Ast) (ta tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 5) 109 s1 = (e, s2) → e ≠ .null → expectToken 11 s2 = (.null, s3) →
    s3.errorIndicator = false →
    callRule (f + 4) 109 { s3 with mark := p.mark + 1 } = (e', s4) → e' ≠ .null →
    expectToken 698 s4 = (.tok ta, s5) → nameToken s5 = (n, s6) → n ≠ .null →
    expectToken 11 s6 = (.tok tc, s7) → callRule f 33 s7 = (b, s8) → b ≠ .null →
    s8.errorIndicator = false →
    callRule (f + 12) 62 p =
      (mkAt .ExceptHandler [e', fieldOf n "id", b] (extraLoc t s8), s8.leave)) ∧
  (t.type = 695 → p.callInvalidRules = false →
    ∀ (e e' e'' b : Ast) (tc : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 5) 109 s1 = (e, s2) → e ≠ .null → expectToken 11 s2 = (.null, s3) →
    s3.errorIndicator = false →
    callRule (f + 4) 109 { s3 with mark := p.mark + 1 } = (e', s4) → e' ≠ .null →
    expectToken 698 s4 = (.null, s5) → s5.errorIndicator = false →
    callRule (f + 3) 108 { s5 with mark := p.mark + 1 } = (e'', s6) → e'' ≠ .null →
    expectToken 11 s6 = (.tok tc, s7) → callRule (f + 1) 33 s7 = (b, s8) → b ≠ .null →
    s8.errorIndicator = false →
    (14 ≤ s8.featureVersion → callRule (f + 12) 62 p =
      (mkAt .ExceptHandler [e'', .null, b] (extraLoc t s8), s8.leave)) ∧
    (s8.featureVersion < 14 →
      (callRule (f + 12) 62 p).1 = .null ∧ (callRule (f + 12) 62 p).2.errorIndicator = true ∧
      (callRule (f + 12) 62 p).2.tok = (raiseError0 "SyntaxError"
        "except expressions without parentheses are only supported in Python 3.14 and greater"
        { s8 with errorIndicator := true }).2.tok)) ∧
  (t.type = 695 → p.callInvalidRules = false → ∀ (b : Ast) (tc : Token) (s2 s3 s4 s5 s6 : PS),
    callRule (f + 5) 109 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 109 { s2 with mark := p.mark + 1 } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 108 { s3 with mark := p.mark + 1 } = (.null, s4) → s4.errorIndicator = false →
    expectToken 11 { s4 with mark := p.mark + 1 } = (.tok tc, s5) →
    callRule (f + 1) 33 s5 = (b, s6) → b ≠ .null → s6.errorIndicator = false →
    callRule (f + 12) 62 p = (mkAt .ExceptHandler [.null, .null, b] (extraLoc t s6), s6.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 7) 248 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 12) 62 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 695 → p.callInvalidRules = true → ∀ (e b : Ast) (tc : Token) (s0 s2 s3 s4 : PS),
    callRule (f + 7) 248 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 5) 109 { s0 with mark := p.mark + 1 } = (e, s2) → e ≠ .null →
    expectToken 11 s2 = (.tok tc, s3) →
    callRule (f + 3) 33 s3 = (b, s4) → b ≠ .null → s4.errorIndicator = false →
    callRule (f + 12) 62 p = (mkAt .ExceptHandler [e, .null, b] (extraLoc t s4), s4.leave)) ∧
  (t.type = 695 → p.callInvalidRules = true → ∀ (v : Ast) (s0 s2 s3 s4 s5 s6 : PS),
    callRule (f + 7) 248 q = (.null, s0) → s0.errorIndicator = false →
    callRule (f + 5) 109 { s0 with mark := p.mark + 1 } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 109 { s2 with mark := p.mark + 1 } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 3) 108 { s3 with mark := p.mark + 1 } = (.null, s4) → s4.errorIndicator = false →
    expectToken 11 { s4 with mark := p.mark + 1 } = (.null, s5) → s5.errorIndicator = false →
    s5.callInvalidRules = true → callRule (f + 2) 245 { s5 with mark := p.mark } = (v, s6) →
    v = .null → callRule (f + 12) 62 p = (.null, { s6 with mark := p.mark }.leave))

theorem exceptBlock_proven : ExceptBlock := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 62 = r62 from rfl, r62]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 695 →
      runCall (g + 1) (.tok 695) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have again : ∀ g (s : PS), TokGrows q s → (q.tokenAt p.mark).type = 695 →
      runCall (g + 1) (.tok 695) { s with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 }) :=
    fun g s gs ht => by rw [call_tok, expect_again gs hlt, ite_t ht]
  refine ⟨fun ht hinv => ?_, fun ht hinv e b tc s2 s3 s4 h2 hE h3 h4 hb h4e => ?_,
    fun ht hinv e e' n b ta tc s2 s3 s4 s5 s6 s7 s8 h2 hE h3 h3e h4 hE' h5 h6 hn h7 h8 hb h8e => ?_,
    fun ht hinv e e' e'' b tc s2 s3 s4 s5 s6 s7 s8 h2 hE h3 h3e h4 hE' h5 h5e h6 hE'' h7 h8 hb h8e => ?_,
    fun ht hinv b tc s2 s3 s4 s5 s6 h2 h2e h3 h3e h4 h4e h5 h6 hb h6e => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv e b tc s0 s2 s3 s4 h0 h0e h2 hE h3 h4 hb h4e => ?_,
    fun ht hinv v s0 s2 s3 s4 s5 s6 h0 h0e h2 h2e h3 h3e h4 h4e h5 h5e h5i h6 hv => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 695) q = (.null, q) := fun g => by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq, alts_skip (by simp [hci, hinv]), alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h2]) hE,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have g3 : TokGrows q s3 := tg_mark' ((tg_call h2).trans (tg_expect h3)) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h2]) hE,
        items_call_null (by rw [call_tok, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call (by rw [call_rule, h4]) hE',
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_name, h6]) hn,
        items_call (by rw [call_tok, h7]) (by simp), items_call (by rw [call_rule, h8]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h8e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have g3 : TokGrows q s3 := tg_mark' ((tg_call h2).trans (tg_expect h3)) _
    have g5 : TokGrows q s5 := g3.trans (tg_mark' ((tg_call h4).trans (tg_expect h5)) _)
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_rule, h2]) hE,
        items_call_null (by rw [call_tok, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call (by rw [call_rule, h4]) hE',
        items_call_null (by rw [call_tok, h5])]),
      alts_ok (by rfl) (E s5 h5e) (by
      dsimp only
      rw [items_call (again _ _ g5 ht) (by simp), items_call (by rw [call_rule, h6]) hE'',
        items_call (by rw [call_tok, h7]) (by simp), items_call (by rw [call_rule, h8]) hb,
        items_nil]), altResult_extra rfl rfl]
    have hn : evalA (((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push e'').push
          (.tok tc)).push b)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s8))
        (.mk .ExceptHandler [(.var 1), .null, (.var 3), .extra0, .extra1, .extra2, .extra3]) s8 =
        (mkAt .ExceptHandler [e'', .null, b] (extraLoc (q.tokenAt p.mark) s8), s8) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs]
      rfl
    have hnn : mkAt .ExceptHandler [e'', .null, b] (extraLoc (q.tokenAt p.mark) s8) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 14) (m := "except expressions without parentheses are") hn hnn
        (by omega)]
      simp [mkAst, mkAt, nonNull, h8e]
    · rw [evalA_cv_low (v := 14) (m := "except expressions without parentheses are") hn hnn
        (by omega)]
      have hmsg : toString (cpsStr ("except expressions without parentheses are".toList.map
          Char.toNat)) ++ toString " only supported in Python 3." ++ toString (14 : Int) ++
          toString " and greater" =
          "except expressions without parentheses are only supported in Python 3.14 and greater" := by
        decide +kernel
      simp only [hmsg]
      exact cv_low_result _ rfl
  · have g2 : TokGrows q s2 := tg_mark' (tg_call h2) _
    have g3 : TokGrows q s3 := g2.trans (tg_mark' (tg_call h3) _)
    have g4 : TokGrows q s4 := g3.trans (tg_mark' (tg_call h4) _)
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (again _ _ g2 ht) (by simp), items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call_null (by rw [call_rule, h4])]),
      alts_ok (by rfl) (E s4 h4e) (by
      dsimp only
      rw [items_call (again _ _ g4 ht) (by simp), items_call (by rw [call_tok, h5]) (by simp),
        items_call (by rw [call_rule, h6]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h6e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (again _ _ g0 ht) (by simp), items_call (by rw [call_rule, h2]) hE,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · subst hv
    have g0 : TokGrows q s0 := tg_call h0
    have g2 : TokGrows q s2 := g0.trans (tg_mark' (tg_call h2) _)
    have g3 : TokGrows q s3 := g2.trans (tg_mark' (tg_call h3) _)
    have g4 : TokGrows q s4 := g3.trans (tg_mark' (tg_call h4) _)
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (again _ _ g0 ht) (by simp), items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (again _ _ g2 ht) (by simp), items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call_null (by rw [call_rule, h4])]),
      alts_fail (by rfl) (E s4 h4e) (by
      dsimp only
      rw [items_call (again _ _ g4 ht) (by simp), items_call_null (by rw [call_tok, h5])]),
      alts_fail (by simp [h5i]) (E s5 h5e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h6])]), alts_nil]
    rfl

/-! ### `except_star_block` -/

/-- `except_star_block` (`Grammar/python.gram:467-479`):
```
    | invalid_except_star_stmt_indent
    | 'except' '*' e=expression ':' b=block {
        _PyAST_ExceptHandler(e, NULL, b, EXTRA) }
    | 'except' '*' e=expression 'as' t=NAME ':' b=block {
        _PyAST_ExceptHandler(e, ((expr_ty) t)->v.Name.id, b, EXTRA) }
    | 'except' '*' e=expressions ':' b=block {
        CHECK_VERSION(
            excepthandler_ty,
            14,
            "except expressions without parentheses are",
            _PyAST_ExceptHandler(e,  NULL, b, EXTRA)) }
    | invalid_except_star_stmt
```
As `except_block` with `'*'` after `except` and no bare alternative. First pass: at any token but
`except`, `NULL`; `except* e: b` gives `ExceptHandler(e, NULL, b)`; with no `:` after `e`,
`except* e as n: b` gives `ExceptHandler(e, n.id, b)`; with no `as` either, `except* A, B: b`
under the version check 14; `except` not followed by `*` fails every alternative, so `NULL` in the
first pass. Second pass: an error from `invalid_except_star_stmt_indent` ends the rule, its `NULL`
leads to the first plain alternative, and with no `*` the last alternative,
`invalid_except_star_stmt`, decides. -/
def ExceptStarBlock : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 695 → p.callInvalidRules = false → callRule (f + 13) 63 p = (.null, q.leave)) ∧
  (t.type = 695 → p.callInvalidRules = false → ∀ (e b : Ast) (ts tc : Token) (s2 s3 s4 s5 : PS),
    expectToken 16 s1 = (.tok ts, s2) → callRule (f + 5) 109 s2 = (e, s3) → e ≠ .null →
    expectToken 11 s3 = (.tok tc, s4) →
    callRule (f + 3) 33 s4 = (b, s5) → b ≠ .null → s5.errorIndicator = false →
    callRule (f + 13) 63 p = (mkAt .ExceptHandler [e, .null, b] (extraLoc t s5), s5.leave)) ∧
  (t.type = 695 → p.callInvalidRules = false →
    ∀ (e e' n b : Ast) (ts ts' ta tc : Token) (s2 s3 s4 s5 s6 s7 s8 s9 s10 : PS),
    expectToken 16 s1 = (.tok ts, s2) → callRule (f + 5) 109 s2 = (e, s3) → e ≠ .null →
    expectToken 11 s3 = (.null, s4) → s4.errorIndicator = false →
    expectToken 16 { s4 with mark := p.mark + 1 } = (.tok ts', s5) →
    callRule (f + 4) 109 s5 = (e', s6) → e' ≠ .null →
    expectToken 698 s6 = (.tok ta, s7) → nameToken s7 = (n, s8) → n ≠ .null →
    expectToken 11 s8 = (.tok tc, s9) → callRule f 33 s9 = (b, s10) → b ≠ .null →
    s10.errorIndicator = false →
    callRule (f + 13) 63 p =
      (mkAt .ExceptHandler [e', fieldOf n "id", b] (extraLoc t s10), s10.leave)) ∧
  (t.type = 695 → p.callInvalidRules = false →
    ∀ (e e' e'' b : Ast) (ts ts' ts'' tc : Token) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : PS),
    expectToken 16 s1 = (.tok ts, s2) → callRule (f + 5) 109 s2 = (e, s3) → e ≠ .null →
    expectToken 11 s3 = (.null, s4) → s4.errorIndicator = false →
    expectToken 16 { s4 with mark := p.mark + 1 } = (.tok ts', s5) →
    callRule (f + 4) 109 s5 = (e', s6) → e' ≠ .null →
    expectToken 698 s6 = (.null, s7) → s7.errorIndicator = false →
    expectToken 16 { s7 with mark := p.mark + 1 } = (.tok ts'', s8) →
    callRule (f + 3) 108 s8 = (e'', s9) → e'' ≠ .null →
    expectToken 11 s9 = (.tok tc, s10) → callRule (f + 1) 33 s10 = (b, s11) → b ≠ .null →
    s11.errorIndicator = false →
    (14 ≤ s11.featureVersion → callRule (f + 13) 63 p =
      (mkAt .ExceptHandler [e'', .null, b] (extraLoc t s11), s11.leave)) ∧
    (s11.featureVersion < 14 →
      (callRule (f + 13) 63 p).1 = .null ∧ (callRule (f + 13) 63 p).2.errorIndicator = true ∧
      (callRule (f + 13) 63 p).2.tok = (raiseError0 "SyntaxError"
        "except expressions without parentheses are only supported in Python 3.14 and greater"
        { s11 with errorIndicator := true }).2.tok)) ∧
  (t.type = 695 → p.callInvalidRules = false → ∀ (s2 s3 s4 : PS),
    expectToken 16 s1 = (.null, s2) → s2.errorIndicator = false →
    expectToken 16 { s2 with mark := p.mark + 1 } = (.null, s3) → s3.errorIndicator = false →
    expectToken 16 { s3 with mark := p.mark + 1 } = (.null, s4) → s4.callInvalidRules = false →
    callRule (f + 13) 63 p = (.null, { s4 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 8) 249 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 13) 63 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 695 → p.callInvalidRules = true → ∀ (e b : Ast) (ts tc : Token) (s0 s2 s3 s4 s5 : PS),
    callRule (f + 8) 249 q = (.null, s0) → s0.errorIndicator = false →
    expectToken 16 { s0 with mark := p.mark + 1 } = (.tok ts, s2) →
    callRule (f + 5) 109 s2 = (e, s3) → e ≠ .null →
    expectToken 11 s3 = (.tok tc, s4) →
    callRule (f + 3) 33 s4 = (b, s5) → b ≠ .null → s5.errorIndicator = false →
    callRule (f + 13) 63 p = (mkAt .ExceptHandler [e, .null, b] (extraLoc t s5), s5.leave)) ∧
  (t.type = 695 → p.callInvalidRules = true → ∀ (v : Ast) (s0 s2 s3 s4 s5 : PS),
    callRule (f + 8) 249 q = (.null, s0) → s0.errorIndicator = false →
    expectToken 16 { s0 with mark := p.mark + 1 } = (.null, s2) → s2.errorIndicator = false →
    expectToken 16 { s2 with mark := p.mark + 1 } = (.null, s3) → s3.errorIndicator = false →
    expectToken 16 { s3 with mark := p.mark + 1 } = (.null, s4) → s4.errorIndicator = false →
    s4.callInvalidRules = true → callRule (f + 4) 246 { s4 with mark := p.mark } = (v, s5) →
    v = .null → callRule (f + 13) 63 p = (.null, { s5 with mark := p.mark }.leave))

theorem exceptStarBlock_proven : ExceptStarBlock := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 63 = r63 from rfl, r63]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have tok_ok : ∀ g, (q.tokenAt p.mark).type = 695 →
      runCall (g + 1) (.tok 695) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have again : ∀ g (s : PS), TokGrows q s → (q.tokenAt p.mark).type = 695 →
      runCall (g + 1) (.tok 695) { s with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 }) :=
    fun g s gs ht => by rw [call_tok, expect_again gs hlt, ite_t ht]
  refine ⟨fun ht hinv => ?_, fun ht hinv e b ts tc s2 s3 s4 s5 h1 h2 hE h3 h4 hb h4e => ?_,
    fun ht hinv e e' n b ts ts' ta tc s2 s3 s4 s5 s6 s7 s8 s9 s10 h1 h2 hE h3 h3e h4 h5 hE' h6 h7 hn
      h8 h9 hb h9e => ?_,
    fun ht hinv e e' e'' b ts ts' ts'' tc s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h1 h2 hE h3 h3e h4 h5 hE'
      h6 h6e h7 h8 hE'' h9 h10 hb h10e => ?_,
    fun ht hinv s2 s3 s4 h1 h1e h2 h2e h3 h3i => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv e b ts tc s0 s2 s3 s4 s5 h0 h0e h1 h2 hE h3 h4 hb h4e => ?_,
    fun ht hinv v s0 s2 s3 s4 s5 h0 h0e h1 h1e h2 h2e h3 h3e h3i h4 hv => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 695) q = (.null, q) := fun g => by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq, alts_skip (by simp [hci, hinv]), alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) hE,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have g4 : TokGrows q s4 := tg_mark' (((tg_expect h1).trans (tg_call h2)).trans (tg_expect h3)) _
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) hE, items_call_null (by rw [call_tok, h3])]),
      alts_ok (by rfl) (E s4 h3e) (by
      dsimp only
      rw [items_call (again _ _ g4 ht) (by simp), items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) hE',
        items_call (by rw [call_tok, h6]) (by simp), items_call (by rw [call_name, h7]) hn,
        items_call (by rw [call_tok, h8]) (by simp), items_call (by rw [call_rule, h9]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h9e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have g4 : TokGrows q s4 := tg_mark' (((tg_expect h1).trans (tg_call h2)).trans (tg_expect h3)) _
    have g7 : TokGrows q s7 :=
      g4.trans (tg_mark' (((tg_expect h4).trans (tg_call h5)).trans (tg_expect h6)) _)
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) hE, items_call_null (by rw [call_tok, h3])]),
      alts_fail (by rfl) (E s4 h3e) (by
      dsimp only
      rw [items_call (again _ _ g4 ht) (by simp), items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) hE', items_call_null (by rw [call_tok, h6])]),
      alts_ok (by rfl) (E s7 h6e) (by
      dsimp only
      rw [items_call (again _ _ g7 ht) (by simp), items_call (by rw [call_tok, h7]) (by simp),
        items_call (by rw [call_rule, h8]) hE'',
        items_call (by rw [call_tok, h9]) (by simp), items_call (by rw [call_rule, h10]) hb,
        items_nil]), altResult_extra rfl rfl]
    have hn : evalA ((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok ts'')).push
          e'').push (.tok tc)).push b)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s11))
        (.mk .ExceptHandler [(.var 2), .null, (.var 4), .extra0, .extra1, .extra2, .extra3]) s11 =
        (mkAt .ExceptHandler [e'', .null, b] (extraLoc (q.tokenAt p.mark) s11), s11) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs]
      rfl
    have hnn : mkAt .ExceptHandler [e'', .null, b] (extraLoc (q.tokenAt p.mark) s11) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 14) (m := "except expressions without parentheses are") hn hnn
        (by omega)]
      simp [mkAst, mkAt, nonNull, h10e]
    · rw [evalA_cv_low (v := 14) (m := "except expressions without parentheses are") hn hnn
        (by omega)]
      have hmsg : toString (cpsStr ("except expressions without parentheses are".toList.map
          Char.toNat)) ++ toString " only supported in Python 3." ++ toString (14 : Int) ++
          toString " and greater" =
          "except expressions without parentheses are only supported in Python 3.14 and greater" := by
        decide +kernel
      simp only [hmsg]
      exact cv_low_result _ rfl
  · have g2 : TokGrows q s2 := tg_mark' (tg_expect h1) _
    have g3 : TokGrows q s3 := g2.trans (tg_mark' (tg_expect h2) _)
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ ht) (by simp), items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (E s2 h1e) (by
      dsimp only
      rw [items_call (again _ _ g2 ht) (by simp), items_call_null (by rw [call_tok, h2])]),
      alts_fail (by rfl) (E s3 h2e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call_null (by rw [call_tok, h3])]),
      alts_skip (by simp [h3i]), alts_nil]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (again _ _ g0 ht) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) hE,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · subst hv
    have g0 : TokGrows q s0 := tg_call h0
    have g2 : TokGrows q s2 := g0.trans (tg_mark' (tg_expect h1) _)
    have g3 : TokGrows q s3 := g2.trans (tg_mark' (tg_expect h2) _)
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (again _ _ g0 ht) (by simp), items_call_null (by rw [call_tok, h1])]),
      alts_fail (by rfl) (E s2 h1e) (by
      dsimp only
      rw [items_call (again _ _ g2 ht) (by simp), items_call_null (by rw [call_tok, h2])]),
      alts_fail (by rfl) (E s3 h2e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call_null (by rw [call_tok, h3])]),
      alts_fail (by simp [h3i]) (E s4 h3e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h4])]), alts_nil]
    rfl

end PyLean.PyGrammar.Peg
