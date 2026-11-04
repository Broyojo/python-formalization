import PyLean.PyGrammar.Peg.Rules.Base2

/-! `match_stmt` (`Grammar/python.gram:487-490`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `match_stmt` (`Grammar/python.gram:487-490`):
```
    | "match" subject=subject_expr ':' NEWLINE INDENT cases[asdl_match_case_seq*]=case_block+ DEDENT {
        CHECK_VERSION(stmt_ty, 10, "Pattern matching is", _PyAST_Match(subject, cases, EXTRA)) }
    | invalid_match_stmt
```
`"match"` is the soft keyword (`_PyPegen_expect_soft_keyword` with the bytes of `match`,
`[109, 97, 116, 99, 104]`), and `case_block+` the loop `_loop1_38` (rule 315). `match s:` NEWLINE
INDENT cases DEDENT gives `Match(s, cases)` when `feature_version` is at least 10, and with a lower
one `NULL` with "Pattern matching is only supported in Python 3.10 and greater". In the first
pass, a `NAME` that is not `match` (or no `NAME`) fails the rule; in the second, when the first
alternative fails (no soft keyword, or no `:` after the subject), `invalid_match_stmt` runs from
the start mark and decides. -/
def MatchStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (m subj cases : Ast) (tc tn ti td : Token) (s1 s2 s3 s4 s5 s6 s7 : PS),
    expectSoftKeyword [109, 97, 116, 99, 104] q = (m, s1) → m ≠ .null →
    callRule (f + 5) 66 s1 = (subj, s2) → subj ≠ .null → expectToken 11 s2 = (.tok tc, s3) →
    expectToken 4 s3 = (.tok tn, s4) → expectToken 5 s4 = (.tok ti, s5) →
    callRule (f + 1) 315 s5 = (cases, s6) → cases ≠ .null → expectToken 6 s6 = (.tok td, s7) →
    s7.errorIndicator = false →
    (10 ≤ s7.featureVersion →
      callRule (f + 11) 65 p = (mkAt .Match [subj, cases] (extraLoc t s7), s7.leave)) ∧
    (s7.featureVersion < 10 →
      (callRule (f + 11) 65 p).1 = .null ∧ (callRule (f + 11) 65 p).2.errorIndicator = true ∧
      (callRule (f + 11) 65 p).2.tok = (raiseError0 "SyntaxError"
        "Pattern matching is only supported in Python 3.10 and greater"
        { s7 with errorIndicator := true }).2.tok)) ∧
  (∀ (s1 : PS), expectSoftKeyword [109, 97, 116, 99, 104] q = (.null, s1) →
    s1.errorIndicator = false → s1.callInvalidRules = false →
    callRule (f + 11) 65 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (v : Ast) (s1 s2 : PS), expectSoftKeyword [109, 97, 116, 99, 104] q = (.null, s1) →
    s1.errorIndicator = false → s1.callInvalidRules = true →
    callRule (f + 5) 250 { s1 with mark := p.mark } = (v, s2) → v = .null →
    callRule (f + 11) 65 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (m subj v : Ast) (s1 s2 s3 s4 : PS),
    expectSoftKeyword [109, 97, 116, 99, 104] q = (m, s1) → m ≠ .null →
    callRule (f + 5) 66 s1 = (subj, s2) → subj ≠ .null → expectToken 11 s2 = (.null, s3) →
    s3.errorIndicator = false → s3.callInvalidRules = true →
    callRule (f + 5) 250 { s3 with mark := p.mark } = (v, s4) → v = .null →
    callRule (f + 11) 65 p = (.null, { s4 with mark := p.mark }.leave))

theorem matchStmt_proven : MatchStmt := by
  intro f p q h
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 65 = r65 from rfl, r65]
  refine ⟨fun m subj cases tc tn ti td s1 s2 s3 s4 s5 s6 s7 h1 hm h2 hs h3 h4 h5 h6 hc h7 h7e => ?_,
    fun s1 h1 h1e h1i => ?_, fun v s1 s2 h1 h1e h1i h2 hv => ?_,
    fun m subj v s1 s2 s3 s4 h1 hm h2 hs h3 h3e h3i h4 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_softKw, h1]) hm, items_call (by rw [call_rule, h2]) hs,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_rule, h6]) hc,
        items_call (by rw [call_tok, h7]) (by simp), items_nil]), altResult_extra rfl rfl]
    have hn : evalA ((((((((#[] : Array Ast).push m).push subj).push (.tok tc)).push (.tok tn)).push
          (.tok ti)).push cases).push (.tok td))
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s7))
        (.mk .Match [(.var 1), (.var 5), .extra0, .extra1, .extra2, .extra3]) s7 =
        (mkAt .Match [subj, cases] (extraLoc (q.tokenAt p.mark) s7), s7) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs]
      rfl
    have hnn : mkAt .Match [subj, cases] (extraLoc (q.tokenAt p.mark) s7) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 10) (m := "Pattern matching is") hn hnn (by omega)]
      simp [mkAst, mkAt, nonNull, h7e]
    · rw [evalA_cv_low (v := 10) (m := "Pattern matching is") hn hnn (by omega)]
      have hmsg : toString (cpsStr ("Pattern matching is".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (10 : Int) ++ toString " and greater" =
          "Pattern matching is only supported in Python 3.10 and greater" := by decide +kernel
      simp only [hmsg]
      exact cv_low_result _ rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_softKw, h1])]),
      alts_skip (by simp [h1i]), alts_nil]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_softKw, h1])]),
      alts_fail (by simp [h1i]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_softKw, h1]) hm, items_call (by rw [call_rule, h2]) hs,
        items_call_null (by rw [call_tok, h3])]),
      alts_fail (by simp [h3i]) (E s3 h3e) (by dsimp only; rw [items_call_null (by rw [call_rule, h4])]),
      alts_nil]
    rfl

end PyLean.PyGrammar.Peg
