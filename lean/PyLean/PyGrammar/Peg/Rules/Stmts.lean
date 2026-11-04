import PyLean.PyGrammar.Peg.Rules.Base

/-! Simple statements of `Grammar/python.gram:185-217`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `pass_stmt`, `break_stmt`, `continue_stmt` -/

/-- `kw_stmt: 'kw' { _PyAST_C(EXTRA) }` (`Grammar/python.gram:194-201`): at a `kw` token the rule
function takes exactly that token and returns the node `C` located at it; at any other token it
returns `NULL` with the mark where it was. -/
def KeywordStmt (id kw : Nat) (c : Ctor) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  callRule (f + 5) id p =
    if (q.tokenAt p.mark).type = kw then
      (.node c [] (some (tokLoc (q.tokenAt p.mark))), { q with mark := p.mark + 1 }.leave)
    else (.null, q.leave)

/-- The shape of the three rules, for the proof. -/
def kwRule (name : String) (kw : Nat) (c : Ctor) : Rule where
  name := name
  kind := .normal
  memo := false
  leftRec := false
  leader := false
  extra := true
  withoutInvalid := false
  alts := [{ items := [.call (.tok kw)], action := some (.mk c [.extra0, .extra1, .extra2, .extra3]),
             nvars := 1, guardInvalid := false, extra := true }]

theorem keywordStmt_of {id kw : Nat} {c : Ctor} {name : String} (hr : ruleOf id = kwRule name kw c)
    (hk : 6 < kw) (hc : c.fields = []) : KeywordStmt id kw c := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  rw [callRule_extra (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
    (by rw [hr]; rfl) h, hr]
  simp only [kwRule]
  by_cases ht : (q.tokenAt p.mark).type = kw
  · have e1 : runCall (f + 1) (.tok kw) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_ok (by rfl) he (by dsimp only; rw [items_call e1 (by simp), items_nil]), ite_t ht]
    rw [altResult_extra rfl rfl]
    rw [lastNonWhitespaceToken_at { q with mark := p.mark + 1 } p.mark rfl
      (by show (q.tokenAt p.mark).type ≠ 0 ∧ ((q.tokenAt p.mark).type < 4 ∨ 6 < (q.tokenAt p.mark).type)
          omega)]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAst, hc,
      List.length_nil, List.drop_zero, normFields, nonNull, Bool.not_true, Bool.false_or, he,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte, Option.getD_some]
    rfl
  · have e1 : runCall (f + 1) (.tok kw) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e1), alts_nil, ite_f ht]
    rw [← hm]
    rfl

theorem passStmt_proven : KeywordStmt 16 527 .Pass := keywordStmt_of (name := _) rfl (by decide) rfl
theorem breakStmt_proven : KeywordStmt 17 528 .Break := keywordStmt_of (name := _) rfl (by decide) rfl
theorem continueStmt_proven : KeywordStmt 18 529 .Continue := keywordStmt_of (name := _) rfl (by decide) rfl

/-! ### `return_stmt` -/

/-- `return_stmt: 'return' a=[star_expressions] { _PyAST_Return(a, EXTRA) }`
(`Grammar/python.gram:185-186`). At a `return` token, `star_expressions` runs right after it; if it
ends with an error the rule fails with the mark back, otherwise the rule returns `Return(a)` with
`a` whatever `star_expressions` returned (`NULL` for a bare `return`), located from `return` to the
last token taken. At any other token, `NULL`. -/
def ReturnStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  ((q.tokenAt p.mark).type ≠ 522 → callRule (f + 6) 14 p = (.null, q.leave)) ∧
  ((q.tokenAt p.mark).type = 522 → ∀ (a : Ast) (s : PS),
    callRule f 112 { q with mark := p.mark + 1 } = (a, s) →
    callRule (f + 6) 14 p =
      if s.errorIndicator then (.null, { s with mark := p.mark }.leave)
      else (mkAt .Return [a] (extraLoc (q.tokenAt p.mark) s), s.leave))

theorem returnStmt_proven : ReturnStmt := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 14 = r14 from rfl, r14]
  refine ⟨fun ht => ?_, fun ht a s hs => ?_⟩
  · have e1 : runCall (f + 2) (.tok 522) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e1), alts_nil, ← hm]
    rfl
  · have e1 : runCall (f + 2) (.tok 522) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    have e2 : runCall (f + 1) (.rule 112) { q with mark := p.mark + 1 } = (a, s) := by
      rw [call_rule, hs]
    by_cases hse : s.errorIndicator = true
    · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call e1 (by simp), items_opt_err e2 hse]), alts_nil,
        ite_t hse]
      rfl
    · have hse' : s.errorIndicator = false := by simpa using hse
      rw [alts_ok (by rfl) he (by dsimp only; rw [items_call e1 (by simp), items_opt e2 hse', items_nil]),
        ite_f hse, altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hse',
        Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.getD_some, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull]

/-! ### `raise_stmt` -/

/-- `raise_stmt` (`Grammar/python.gram:188-192`), in the first pass, where `invalid_raise_stmt`
is skipped:
```
    | 'raise' a=expression 'from' b=expression { _PyAST_Raise(a, b, EXTRA) }
    | invalid_raise_stmt
    | 'raise' a=expression { _PyAST_Raise(a, NULL, EXTRA) }
    | 'raise' { _PyAST_Raise(NULL, NULL, EXTRA) }
```
With `t` the token under the mark:
* not `raise`: `NULL`, mark unmoved;
* `raise a from b` (both `expression` calls succeed, `from` between): `Raise(a, b)`;
* `raise a` with no `from` after `a`: the first alternative fails, the mark goes back, and the
  third alternative parses `expression` again and returns `Raise(a', NULL)`;
* `raise` with no expression after it (both `expression` calls fail): `Raise(NULL, NULL)` located
  at the `raise` token alone.
The order is what decides `raise a from b`: the third alternative also matches its prefix. -/
def RaiseStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q → p.callInvalidRules = false →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 632 → callRule (f + 8) 15 p = (.null, q.leave)) ∧
  (t.type = 632 → ∀ (a b : Ast) (tf : Token) (s2 s3 s4 : PS),
    callRule (f + 2) 109 s1 = (a, s2) → a ≠ .null →
    expectToken 650 s2 = (.tok tf, s3) →
    callRule f 109 s3 = (b, s4) → b ≠ .null → s4.errorIndicator = false →
    callRule (f + 8) 15 p = (mkAt .Raise [a, b] (extraLoc t s4), s4.leave)) ∧
  (t.type = 632 → ∀ (a a' : Ast) (s2 s3 s4 : PS),
    callRule (f + 2) 109 s1 = (a, s2) → a ≠ .null →
    expectToken 650 s2 = (.null, s3) → s3.errorIndicator = false → s3.callInvalidRules = false →
    callRule f 109 { s3 with mark := p.mark + 1 } = (a', s4) → a' ≠ .null →
    s4.errorIndicator = false →
    callRule (f + 8) 15 p = (mkAt .Raise [a', .null] (extraLoc t s4), s4.leave)) ∧
  (t.type = 632 → ∀ (s2 s3 : PS),
    callRule (f + 2) 109 s1 = (.null, s2) → s2.errorIndicator = false →
    s2.callInvalidRules = false →
    callRule f 109 { s2 with mark := p.mark + 1 } = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 8) 15 p =
      (mkAt .Raise [.null, .null] (tokLoc t), { s3 with mark := p.mark + 1 }.leave))

/-- The token under the mark is not one of `NEWLINE`, `INDENT`, `DEDENT`, `ENDMARKER`. -/
theorem kwNotWs {s : PS} {m ty : Nat} (h : (s.tokenAt m).type = ty) (hk : 6 < ty) :
    (s.tokenAt m).type ≠ 0 ∧ ((s.tokenAt m).type < 4 ∨ 6 < (s.tokenAt m).type) := by
  omega

theorem raiseStmt_proven : RaiseStmt := by
  intro f p q h hinv
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 15 = r15 from rfl, r15]
  have hg : ∀ s : PS, s.callInvalidRules = false →
      ((true && !s.callInvalidRules) = true) := fun s hs => by simp [hs]
  refine ⟨fun ht => ?_, fun ht a b tf s2 s3 s4 h1 ha h2 h3 hb h4e => ?_,
    fun ht a a' s2 s3 s4 h1 ha h2 h2e h2i h3 ha' h4e => ?_,
    fun ht s2 s3 h1 h1e h1i h2 h2e => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 632) q = (.null, q) := fun g => by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null (e1 _)), hq, alts_skip (hg q (hci.trans hinv)),
      alts_fail (by rfl) he (items_call_null (e1 _)), hq,
      alts_fail (by rfl) he (items_call_null (e1 _)), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 4) (.tok 632) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, Bool.false_eq_true, ↓reduceIte, Option.getD_some, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have e1 : runCall (f + 4) (.tok 632) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    have g3 : TokGrows q s3 := (tg_mark' (tg_call h1) _).trans (tg_expect h2)
    have e3 : runCall (f + 2) (.tok 632) { s3 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s3 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g3 hlt, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call_null (by rw [call_tok, h2])]),
      alts_skip (hg { s3 with mark := p.mark } h2i),
      alts_ok (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call e3 (by simp), items_call (by rw [call_rule, h3]) ha', items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have e1 : runCall (f + 4) (.tok 632) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    have g2 : TokGrows q s2 := tg_mark' (tg_call h1) _
    have g3 : TokGrows q s3 := (tg_mark (g2.trans (tg_mark' (tg_call h2) _)) _)
    have e2 : runCall (f + 2) (.tok 632) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    have e3 : runCall (f + 1) (.tok 632) { s3 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s3 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g3 hlt, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_skip (hg { s2 with mark := p.mark } h1i),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only
        rw [items_call e2 (by simp), items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h2e)
        (by dsimp only; rw [items_call e3 (by simp), items_nil]),
      altResult_extra rfl rfl]
    have hl : lastNonWhitespaceToken { s3 with mark := p.mark + 1 } = q.tokenAt p.mark := by
      rw [lastNonWhitespaceToken_at _ p.mark rfl (by
        show (s3.tokenAt p.mark).type ≠ 0 ∧ ((s3.tokenAt p.mark).type < 4 ∨ 6 < (s3.tokenAt p.mark).type)
        rw [g3.same p.mark hlt]; omega)]
      exact g3.same p.mark hlt
    rw [hl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, tokLoc, locArgs]
    simp [mkAst, nonNull]

/-- `raise_stmt` in the second pass (`Grammar/python.gram:188-192`): when the first alternative
fails (no `expression` after `raise`), `invalid_raise_stmt` runs before the plain alternatives, and
if it raises, `raise_stmt` fails with that error and no later alternative runs. -/
def RaiseStmtInvalid : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.tokenAt p.mark).type = 632 → ∀ (s2 s3 : PS),
  callRule (f + 2) 109 { q with mark := p.mark + 1 } = (.null, s2) → s2.errorIndicator = false →
  s2.callInvalidRules = true →
  callRule (f + 2) 218 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = true →
  callRule (f + 8) 15 p = (.null, { s3 with mark := p.mark }.leave)

theorem raiseStmtInvalid_proven : RaiseStmtInvalid := by
  intro f p q h ht s2 s3 h1 h1e h1i h2 h2e
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 15 = r15 from rfl, r15]
  have e1 : runCall (f + 4) (.tok 632) q =
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
    rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call_null (by rw [call_rule, h1])]),
    alts_fail (by simp [h1i]) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h1e)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
    alts_err (by rfl) (show ({ s3 with mark := p.mark } : PS).errorIndicator = true from h2e)]
  rfl

/-- `invalid_raise_stmt` (`Grammar/python.gram:1321-1325`), new in 3.15, run in the second pass:
```
    | a='raise' b='from' {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "did you forget an expression between 'raise' and 'from'?") }
    | 'raise' expression a='from' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "did you forget an expression after 'from'?") }
```
`raise from` raises the first message over the range from `raise` to `from`; `raise a from` (an
`expression` between) raises the second at the `from` token. Both end the rule with `NULL` and
`error_indicator` set. At any token but `raise`, `NULL` and no error. -/
def InvalidRaiseStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 632 → callRule (f + 8) 218 p = (.null, q.leave)) ∧
  (t.type = 632 → ∀ (tf : Token) (s2 : PS),
    expectToken 650 s1 = (.tok tf, s2) → s2.errorIndicator = false →
    callRule (f + 8) 218 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" t.lineno t.colOffset tf.endLineno
          tf.endColOffset "did you forget an expression between 'raise' and 'from'?" s2).2 with
        errorIndicator := true }.leave)) ∧
  (t.type = 632 → ∀ (a : Ast) (tf : Token) (s2 s3 s4 : PS),
    expectToken 650 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 1) 109 { s2 with mark := p.mark + 1 } = (a, s3) → a ≠ .null →
    expectToken 650 s3 = (.tok tf, s4) → s4.errorIndicator = false →
    callRule (f + 8) 218 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" tf.lineno tf.colOffset tf.endLineno
          tf.endColOffset "did you forget an expression after 'from'?" s4).2 with
        errorIndicator := true }.leave))

theorem invalidRaiseStmt_proven : InvalidRaiseStmt := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 218 = r218 from rfl, r218]
  refine ⟨fun ht => ?_, fun ht tf s2 h2 h2e => ?_, fun ht a tf s2 s3 s4 h2 h2e h3 ha h4 h4e => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 632) p.enter = (.null, q) := fun g => by
      rw [call_tok, expect_entered h, ite_f ht]
    have e2 : ∀ g, runCall (g + 1) (.tok 632) { q with mark := p.mark } = (.null, q) := fun g => by
      rw [hq, call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he' (items_call_null (e1 _)),
      alts_fail (by rfl) (show ({ q with mark := p.mark } : PS).errorIndicator = false from he)
        (items_call_null (e2 _)), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 4) (.tok 632) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_tok, h2]) (by simp), items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
      locOf, tokLoc]
    have hmsg : msgOf [.str ("did you forget an expression between 'raise' and 'from'?".toList.map
        Char.toNat)] = "did you forget an expression between 'raise' and 'from'?" := by
      decide +kernel
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [hmsg]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
      Array.size_empty, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte, Option.getD_some]
    have herr := raiseEKL_errOcc "SyntaxError"
      "did you forget an expression between 'raise' and 'from'?" (q.tokenAt p.mark).lineno
      (q.tokenAt p.mark).colOffset tf.endLineno tf.endColOffset s2 h2e
    generalize raiseErrorKnownLocation "SyntaxError" (q.tokenAt p.mark).lineno
      (q.tokenAt p.mark).colOffset tf.endLineno tf.endColOffset
      "did you forget an expression between 'raise' and 'from'?" s2 = r at herr ⊢
    obtain ⟨u, s'⟩ := r
    simp only at herr
    simp [nonNull, herr]
  · have e1 : runCall (f + 4) (.tok 632) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    have g2 : TokGrows q s2 := tg_mark' (tg_expect h2) _
    have e2 : runCall (f + 3) (.tok 632) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call e2 (by simp), items_call (by rw [call_rule, h3]) ha,
          items_call (by rw [call_tok, h4]) (by simp), items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
      locOf, tokLoc]
    have hmsg : msgOf [.str ("did you forget an expression after 'from'?".toList.map
        Char.toNat)] = "did you forget an expression after 'from'?" := by
      decide +kernel
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [hmsg]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
      Array.size_empty, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte, Option.getD_some]
    have herr := raiseEKL_errOcc "SyntaxError" "did you forget an expression after 'from'?"
      tf.lineno tf.colOffset tf.endLineno tf.endColOffset s4 h4e
    generalize raiseErrorKnownLocation "SyntaxError" tf.lineno tf.colOffset tf.endLineno
      tf.endColOffset "did you forget an expression after 'from'?" s4 = r at herr ⊢
    obtain ⟨u, s'⟩ := r
    simp only at herr
    simp [nonNull, herr]

end PyLean.PyGrammar.Peg
