import PyLean.PyGrammar.Peg.Rules.Base

/-! `yield`, `assert` and `import` statements of `Grammar/python.gram`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The token under the mark is not one of `NEWLINE`, `INDENT`, `DEDENT`, `ENDMARKER`. -/
theorem notWs {s : PS} {m ty : Nat} (h : (s.tokenAt m).type = ty) (hk : 6 < ty) :
    (s.tokenAt m).type ≠ 0 ∧ ((s.tokenAt m).type < 4 ∨ 6 < (s.tokenAt m).type) := by
  omega

/-! ### `yield_expr`, `yield_stmt` -/

/-- `yield_expr` (`Grammar/python.gram:727-729`):
```
    | 'yield' 'from' a=expression { _PyAST_YieldFrom(a, EXTRA) }
    | 'yield' a=[star_expressions] { _PyAST_Yield(a, EXTRA) }
```
`yield from a` is `YieldFrom(a)`; `yield` not followed by `from` backs up and parses
`star_expressions`, giving `Yield(a)` (`a` is `NULL` for a bare `yield`). The order matters:
the second alternative also matches `yield` alone and would leave `from a` unparsed. -/
def YieldExpr : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 588 → callRule (f + 7) 111 p = (.null, q.leave)) ∧
  (t.type = 588 → ∀ (a : Ast) (tf : Token) (s2 s3 : PS), expectToken 650 s1 = (.tok tf, s2) →
    callRule f 109 s2 = (a, s3) → a ≠ .null → s3.errorIndicator = false →
    callRule (f + 7) 111 p = (mkAt .YieldFrom [a] (extraLoc t s3), s3.leave)) ∧
  (t.type = 588 → ∀ (a : Ast) (s2 s3 : PS), expectToken 650 s1 = (.null, s2) →
    s2.errorIndicator = false → callRule f 112 { s2 with mark := p.mark + 1 } = (a, s3) →
    s3.errorIndicator = false →
    callRule (f + 7) 111 p = (mkAt .Yield [a] (extraLoc t s3), s3.leave))

theorem yieldExpr_proven : YieldExpr := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 111 = r111 from rfl, r111]
  have tok_ok : ∀ (g ty : Nat), (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ (g ty : Nat), (q.tokenAt p.mark).type ≠ ty →
      runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  refine ⟨fun ht => ?_, fun ht a tf s2 s3 h1 h2 ha h3e => ?_, fun ht a s2 s3 h1 h1e h2 h2e => ?_⟩
  · rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ ht)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ ht)), hq, alts_nil]
    rfl
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_rule, h2]) ha, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have g2 : TokGrows q s2 := tg_mark' (tg_expect h1) _
    have e2 : runCall (f + 2) (.tok 588) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call_null (by rw [call_tok, h1])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only
        rw [items_call e2 (by simp), items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]

/-- `yield_stmt: y=yield_expr { _PyAST_Expr(y, EXTRA) }` (`Grammar/python.gram:213`): a
`yield_expr` wrapped in an expression statement; if `yield_expr` fails, `NULL` with the mark
back. -/
def YieldStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q → ∀ (y : Ast) (s : PS),
  callRule f 111 q = (y, s) →
  (y ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 22 p = (mkAt .Expr [y] (extraLoc (q.tokenAt p.mark) s), s.leave)) ∧
  (y = .null → callRule (f + 5) 22 p = (.null, { s with mark := p.mark }.leave))

theorem yieldStmt_proven : YieldStmt := by
  intro f p q h y s h1
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 22 = r22 from rfl, r22]
  refine ⟨fun hy hse => ?_, fun hy => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hy, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hse,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · subst hy
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl

/-! ### `del_stmt` -/

/-- `del_stmt` (`Grammar/python.gram:209-211`) in the first pass:
```
    | 'del' a=del_targets &(';' | NEWLINE) { _PyAST_Delete(a, EXTRA) }
    | invalid_del_stmt
```
The positive lookahead (the artificial rule `_tmp_15` for `';' | NEWLINE`) consumes nothing: when
it matches, the result is `Delete(a)` ending at the targets; when it does not (`del x y`), the rule
fails with the mark back, although `del_targets` matched. -/
def DelStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q → p.callInvalidRules = false →
  let t := q.tokenAt p.mark
  (t.type ≠ 634 → callRule (f + 7) 21 p = (.null, q.leave)) ∧
  (t.type = 634 → ∀ (a v : Ast) (s2 s3 : PS),
    callRule (f + 1) 203 { q with mark := p.mark + 1 } = (a, s2) → a ≠ .null →
    callRule f 292 s2 = (v, s3) → s3.errorIndicator = false →
    (v ≠ .null → callRule (f + 7) 21 p =
      (mkAt .Delete [a] (extraLoc t { s3 with mark := s2.mark }), { s3 with mark := s2.mark }.leave)) ∧
    (v = .null → s3.callInvalidRules = false →
      callRule (f + 7) 21 p = (.null, { s3 with mark := p.mark }.leave)))

theorem delStmt_proven : DelStmt := by
  intro f p q h hinv
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 21 = r21 from rfl, r21]
  refine ⟨fun ht => ?_, fun ht a v s2 s3 h1 ha h2 h2e => ⟨fun hv => ?_, fun hv h3i => ?_⟩⟩
  · have e1 : runCall (f + 3) (.tok 634) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e1), hq,
      alts_skip (by simp [hci, hinv]), alts_nil]
    rfl
  · have e1 : runCall (f + 3) (.tok 634) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    have hv' : nonNull v = true := by cases v <;> simp_all [nonNull]
    rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_look (by rw [call_rule, h2]) hv', items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · subst hv
    have e1 : runCall (f + 3) (.tok 634) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_skip (by simp [h3i]), alts_nil]
    rfl

/-- `del_stmt` in the second pass (`Grammar/python.gram:209-211`): when the first alternative
fails at its lookahead (`del x y`), `invalid_del_stmt` runs from the start mark, and its outcome is
the rule's: the error it raises (or its `NULL`) with the mark back. -/
def DelStmtInvalid : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.tokenAt p.mark).type = 634 → ∀ (a : Ast) (s2 s3 s4 : PS),
  callRule (f + 1) 203 { q with mark := p.mark + 1 } = (a, s2) → a ≠ .null →
  callRule f 292 s2 = (.null, s3) → s3.errorIndicator = false → s3.callInvalidRules = true →
  callRule (f + 1) 219 { s3 with mark := p.mark } = (.null, s4) →
  callRule (f + 7) 21 p = (.null, { s4 with mark := p.mark }.leave)

theorem delStmtInvalid_proven : DelStmtInvalid := by
  intro f p q h ht a s2 s3 s4 h1 ha h2 h2e h2i h3
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 21 = r21 from rfl, r21]
  have e1 : runCall (f + 3) (.tok 634) q =
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
    rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
    alts_fail (by simp [h2i]) (show ({ s3 with mark := p.mark } : PS).errorIndicator = false from h2e)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]), alts_nil]
  rfl

/-! ### `assert_stmt` -/

/-- `assert_stmt` (`Grammar/python.gram:215-217`) in the first pass:
```
    | invalid_assert_stmt
    | 'assert' a=expression b=[',' z=expression { z }] { _PyAST_Assert(a, b, EXTRA) }
```
`invalid_assert_stmt` comes first in 3.15 but is skipped in the first pass. At `assert`, with an
`expression` after it and the optional `, msg` part (the artificial rule `_tmp_16`) ending with no
error, the rule returns `Assert(a, b)`. At any other token, `NULL`. -/
def AssertStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q → p.callInvalidRules = false →
  let t := q.tokenAt p.mark
  (t.type ≠ 638 → callRule (f + 8) 23 p = (.null, q.leave)) ∧
  (t.type = 638 → ∀ (a b : Ast) (s2 s3 : PS),
    callRule (f + 1) 109 { q with mark := p.mark + 1 } = (a, s2) → a ≠ .null →
    callRule f 293 s2 = (b, s3) → s3.errorIndicator = false →
    callRule (f + 8) 23 p = (mkAt .Assert [a, b] (extraLoc t s3), s3.leave))

theorem assertStmt_proven : AssertStmt := by
  intro f p q h hinv
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hg : (true && !q.callInvalidRules) = true := by simp [hci, hinv]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 23 = r23 from rfl, r23]
  refine ⟨fun ht => ?_, fun ht a b s2 s3 h1 ha h2 h3e => ?_⟩
  · have e1 : runCall (f + 3) (.tok 638) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip hg, alts_fail (by rfl) he (items_call_null e1), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 3) (.tok 638) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_skip hg, alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
        items_opt (by rw [call_rule, h2]) h3e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]

/-- `assert_stmt` in the second pass (`Grammar/python.gram:215-217`): in 3.15 `invalid_assert_stmt`
is the first alternative, so it runs before anything else. If it raises, the rule fails with its
error and the `assert` alternative is not tried; if it returns `NULL` with no error, the `assert`
alternative runs from the start mark as in the first pass. -/
def AssertStmtInvalid : Prop := ∀ (f : Nat) (p q : PS), Entered p q → p.callInvalidRules = true →
  ∀ (s1 : PS), callRule (f + 3) 220 q = (.null, s1) →
  (s1.errorIndicator = true → callRule (f + 8) 23 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (s1.errorIndicator = false → (q.tokenAt p.mark).type = 638 → ∀ (a b : Ast) (s2 s3 : PS),
    callRule (f + 1) 109 { s1 with mark := p.mark + 1 } = (a, s2) → a ≠ .null →
    callRule f 293 s2 = (b, s3) → s3.errorIndicator = false →
    callRule (f + 8) 23 p = (mkAt .Assert [a, b] (extraLoc (q.tokenAt p.mark) s3), s3.leave))

theorem assertStmtInvalid_proven : AssertStmtInvalid := by
  intro f p q h hinv s1 h0
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 23 = r23 from rfl, r23]
  refine ⟨fun h0e => ?_, fun h0e ht a b s2 s3 h1 ha h2 h3e => ?_⟩
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g1 : TokGrows q s1 := tg_call h0
    have e1 : runCall (f + 3) (.tok 638) { s1 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s1 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g1 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h0e)
      (by
        dsimp only
        rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha,
          items_opt (by rw [call_rule, h2]) h3e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]

/-! ### `import_stmt` -/

/-- `import_stmt (memo)` (`Grammar/python.gram:219-222`):
```
    | invalid_import
    | import_name
    | import_from
```
At a position not yet memoized for it: in the first pass `invalid_import` is skipped,
`import_name` is tried first and `import_from` only when it fails; in the second pass
`invalid_import` runs first, and an error from it ends the rule (no later alternative, nothing
memoized), while a `NULL` without error from it leads on to `import_name`. Results are memoized
at the start mark. -/
def ImportStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 24) = none →
  let memo (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo p.mark (1000 + 24) v s).2.leave)
  (p.callInvalidRules = false → ∀ (v : Ast) (s : PS), callRule (f + 1) 25 q = (v, s) → v ≠ .null →
    callRule (f + 7) 24 p = memo v s) ∧
  (p.callInvalidRules = false → ∀ (v : Ast) (s0 s : PS), callRule (f + 1) 25 q = (.null, s0) →
    s0.errorIndicator = false → callRule f 26 { s0 with mark := p.mark } = (v, s) → v ≠ .null →
    callRule (f + 7) 24 p = memo v s) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 2) 237 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 7) 24 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (v : Ast) (s0 s : PS), callRule (f + 2) 237 q = (.null, s0) →
    s0.errorIndicator = false → callRule (f + 1) 25 { s0 with mark := p.mark } = (v, s) →
    v ≠ .null → callRule (f + 7) 24 p = memo v s)

theorem importStmt_proven : ImportStmt := by
  intro f p q h hn
  obtain ⟨he, -, hci, -, -, -, -⟩ := h.facts
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 24 = r24 from rfl, r24]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun hinv v s h1 hv => ?_, fun hinv v s0 s h1 h1e h2 hv => ?_,
    fun hinv s0 h0 h0e => ?_, fun hinv v s0 s h0 h0e h1 hv => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_skip (by simp [hci, hinv]),
      alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s0 h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl

/-! ### `import_name` -/

/-- `import_name` (`Grammar/python.gram:227-228`), with the 3.15 soft keyword:
```
    | lazy="lazy"? 'import' a=dotted_as_names { _PyAST_Import(a, lazy ? 1 : 0, EXTRA) }
```
Whatever the optional `"lazy"` read gave (a `Name` for the soft keyword, `NULL` otherwise): if it
ended with an error, the rule fails; if `import` does not follow, or `dotted_as_names` fails, the
rule fails with the mark back; otherwise the result is `Import(a, is_lazy)`, `is_lazy` 1 exactly
when `"lazy"` was there. -/
def ImportName : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  ∀ (lz : Ast) (s1 : PS), expectSoftKeyword [108, 97, 122, 121] q = (lz, s1) →
  (s1.errorIndicator = true → callRule (f + 7) 25 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (s1.errorIndicator = false → ∀ (s2 : PS), expectToken 651 s1 = (.null, s2) →
    callRule (f + 7) 25 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (s1.errorIndicator = false → ∀ (ti : Token) (s2 s3 : PS), expectToken 651 s1 = (.tok ti, s2) →
    callRule f 30 s2 = (.null, s3) →
    callRule (f + 7) 25 p = (.null, { s3 with mark := p.mark }.leave)) ∧
  (s1.errorIndicator = false → ∀ (a : Ast) (ti : Token) (s2 s3 : PS),
    expectToken 651 s1 = (.tok ti, s2) → callRule f 30 s2 = (a, s3) → a ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 7) 25 p =
      (mkAt .Import [a, .int (if truth lz then 1 else 0)] (extraLoc (q.tokenAt p.mark) s3), s3.leave))

theorem importName_proven : ImportName := by
  intro f p q h lz s1 h1
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 25 = r25 from rfl, r25]
  refine ⟨fun h1e => ?_, fun h1e s2 h2 => ?_, fun h1e ti s2 s3 h2 h3 => ?_,
    fun h1e a ti s2 s3 h2 h3 ha h3e => ?_⟩
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_opt_err (by rw [call_softKw, h1]) h1e]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_softKw, h1]) h1e, items_call_null (by rw [call_tok, h2])]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_softKw, h1]) h1e, items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_rule, h3])]), alts_nil]
    rfl
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_softKw, h1]) h1e, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ha, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    cases ht : truth lz <;> simp [mkAst, nonNull, ht, StateT.pure, pure, h3e]

/-! ### `import_from` -/

/-- `import_from` (`Grammar/python.gram:231-236`), with the 3.15 `lazy` prefix:
```
    | invalid_import_from
    | lazy="lazy"? 'from' a=('.' | '...')* b=dotted_name 'import' c=import_from_targets {
        _PyPegen_checked_from_import(p, a, b, c, lazy, EXTRA) }
    | lazy="lazy"? 'from' a=('.' | '...')+ 'import' b=import_from_targets {
        _PyAST_ImportFrom(NULL, b, _PyPegen_seq_count_dots(a), lazy ? 1 : 0, EXTRA) }
```
First pass (`invalid_import_from` skipped): `[lazy] from [dots] mod import targets` is what
`_PyPegen_checked_from_import` makes of the dots (the artificial loop `_loop0_17`), module, targets
and `lazy` result; `[lazy] from dots import targets` with no module name backs up, reads `lazy`
again, and gives `ImportFrom(NULL, targets, level, is_lazy)` with `level` the dots counted. Second
pass: an error from `invalid_import_from` ends the rule. -/
def ImportFrom : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let lazyKw : List Nat := [108, 97, 122, 121]
  (p.callInvalidRules = false → ∀ (lz dots md tg r : Ast) (tf ti : Token)
    (s1 s2 s3 s4 s5 s6 s7 : PS),
    expectSoftKeyword lazyKw q = (lz, s1) → s1.errorIndicator = false →
    expectToken 650 s1 = (.tok tf, s2) → callRule (f + 3) 294 s2 = (dots, s3) → dots ≠ .null →
    callRule (f + 2) 32 s3 = (md, s4) → md ≠ .null → expectToken 651 s4 = (.tok ti, s5) →
    callRule f 27 s5 = (tg, s6) → tg ≠ .null →
    checkedFromImport dots md tg lz t.lineno t.colOffset (lastNonWhitespaceToken s6).endLineno
      (lastNonWhitespaceToken s6).endColOffset s6 = (r, s7) → r ≠ .null → s7.errorIndicator = false →
    callRule (f + 11) 26 p = (r, s7.leave)) ∧
  (p.callInvalidRules = false → ∀ (lz lz' dots dots' tg : Ast) (tf tf' ti : Token)
    (s1 s2 s3 s4 s5 s6 s7 s8 s9 : PS),
    expectSoftKeyword lazyKw q = (lz, s1) → s1.errorIndicator = false →
    expectToken 650 s1 = (.tok tf, s2) → callRule (f + 3) 294 s2 = (dots, s3) → dots ≠ .null →
    callRule (f + 2) 32 s3 = (.null, s4) → s4.errorIndicator = false →
    expectSoftKeyword lazyKw { s4 with mark := p.mark } = (lz', s5) → s5.errorIndicator = false →
    expectToken 650 s5 = (.tok tf', s6) → callRule (f + 2) 295 s6 = (dots', s7) → dots' ≠ .null →
    expectToken 651 s7 = (.tok ti, s8) → callRule f 27 s8 = (tg, s9) → tg ≠ .null →
    s9.errorIndicator = false →
    callRule (f + 11) 26 p =
      (mkAt .ImportFrom [.null, tg, .int (countDots dots'), .int (if truth lz' then 1 else 0)]
        (extraLoc t s9), s9.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 6) 240 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 11) 26 p = (.null, { s0 with mark := p.mark }.leave))

theorem importFrom_proven : ImportFrom := by
  intro f p q h
  obtain ⟨he, -, hci, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 26 = r26 from rfl, r26]
  refine ⟨fun hinv lz dots md tg r tf ti s1 s2 s3 s4 s5 s6 s7 h1 h1e h2 h3 hd h4 hm h5 h6 ht h7 hr
      h7e => ?_,
    fun hinv lz lz' dots dots' tg tf tf' ti s1 s2 s3 s4 s5 s6 s7 s8 s9 h1 h1e h2 h3 hd h4 h4e h5 h5e
      h6 h7 hd' h8 h9 ht h9e => ?_,
    fun hinv s0 h0 h0e => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_softKw, h1]) h1e, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hd, items_call (by rw [call_rule, h4]) hm,
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_rule, h6]) ht,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
      Array.size_empty, List.getD, Option.getD_some, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Nat.reduceEqDiff, ↓reduceIte]
    rw [h7]
    have hr' : nonNull r = true := by cases r <;> simp_all [nonNull]
    simp [hr', h7e]
  · have e5 : runCall (f + 5) (.softKw [108, 97, 122, 121]) { s4 with mark := p.mark } = (lz', s5) := by
      rw [call_softKw, h5]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_softKw, h1]) h1e, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hd, items_call_null (by rw [call_rule, h4])]),
      alts_ok (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
        dsimp only
        rw [items_opt e5 h5e, items_call (by rw [call_tok, h6]) (by simp),
          items_call (by rw [call_rule, h7]) hd', items_call (by rw [call_tok, h8]) (by simp),
          items_call (by rw [call_rule, h9]) ht, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h9e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    cases hz : truth lz' <;> simp [mkAst, nonNull, hz, StateT.pure, pure, h9e]
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl

/-! ### `invalid_import` -/

/-- `invalid_import` (`Grammar/python.gram:1433-1437`), second pass:
```
    | a='import' ','.dotted_name+ 'from' dotted_name {
        RAISE_SYNTAX_ERROR_STARTING_FROM(a, "Did you mean to use 'from ... import ...' instead?") }
    | 'import' token=NEWLINE {
        RAISE_SYNTAX_ERROR_STARTING_FROM(token, "Expected one or more names after 'import'") }
```
`import a.b from c` raises the first message from the `import` token on; `import` followed by
`NEWLINE` raises the second at the `NEWLINE`. At any token but `import` the rule returns `NULL`
with no error: in particular at the soft keyword `lazy` of `lazy import`. -/
def InvalidImport : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type ≠ 651 → callRule (f + 8) 237 p = (.null, q.leave)) ∧
  (t.type = 651 → ∀ (ns d : Ast) (tf : Token) (s2 s3 s4 : PS),
    callRule (f + 2) 415 s1 = (ns, s2) → ns ≠ .null → expectToken 650 s2 = (.tok tf, s3) →
    callRule f 32 s3 = (d, s4) → d ≠ .null → s4.errorIndicator = false →
    callRule (f + 8) 237 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" t.lineno t.colOffset (-5) (-5)
          "Did you mean to use 'from ... import ...' instead?" s4).2 with
        errorIndicator := true }.leave)) ∧
  (t.type = 651 → ∀ (tn : Token) (s2 s3 : PS),
    callRule (f + 2) 415 s1 = (.null, s2) → s2.errorIndicator = false →
    expectToken 4 { s2 with mark := p.mark + 1 } = (.tok tn, s3) → s3.errorIndicator = false →
    callRule (f + 8) 237 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" tn.lineno tn.colOffset (-5) (-5)
          "Expected one or more names after 'import'" s3).2 with errorIndicator := true }.leave))

theorem invalidImport_proven : InvalidImport := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 237 = r237 from rfl, r237]
  refine ⟨fun ht => ?_, fun ht ns d tf s2 s3 s4 h1 hns h2 h3 hd h4e => ?_,
    fun ht tn s2 s3 h1 h1e h2 h2e => ?_⟩
  · have e1 : runCall (f + 4) (.tok 651) p.enter = (.null, q) := by
      rw [call_tok, expect_entered h, ite_f ht]
    have e2 : runCall (f + 3) (.tok 651) { q with mark := p.mark } = (.null, q) := by
      rw [hq, call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he' (items_call_null e1),
      alts_fail (by rfl) (show ({ q with mark := p.mark } : PS).errorIndicator = false from he)
        (items_call_null e2), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 4) (.tok 651) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) hns,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hd,
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, locOf,
      tokLoc]
    have hmsg : msgOf [.str ("Did you mean to use 'from ... import ...' instead?".toList.map
        Char.toNat)] = "Did you mean to use 'from ... import ...' instead?" := by
      decide +kernel
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [hmsg]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
      Array.size_empty, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte, Option.getD_some]
    generalize hr : raiseErrorKnownLocation "SyntaxError" (q.tokenAt p.mark).lineno
      (q.tokenAt p.mark).colOffset (-5) (-5)
      "Did you mean to use 'from ... import ...' instead?" s4 = r
    have herr := raised_result _ _ _ _ _ _ hr h4e
    obtain ⟨u, s'⟩ := r
    simp only at herr
    simp [nonNull, herr]
  · have e1 : runCall (f + 4) (.tok 651) p.enter =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expect_entered h, ite_t ht]
    have g2 : TokGrows q s2 := tg_mark' (tg_call h1) _
    have e2 : runCall (f + 3) (.tok 651) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call e1 (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only
        rw [items_call e2 (by simp), items_call (by rw [call_tok, h2]) (by simp), items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, locOf,
      tokLoc]
    have hmsg : msgOf [.str ("Expected one or more names after 'import'".toList.map
        Char.toNat)] = "Expected one or more names after 'import'" := by
      decide +kernel
    simp only [List.drop_succ_cons, List.drop_zero]
    rw [hmsg]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
      Array.size_empty, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ]
    simp only [Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte, Option.getD_some]
    generalize hr : raiseErrorKnownLocation "SyntaxError" tn.lineno tn.colOffset (-5) (-5)
      "Expected one or more names after 'import'" s3 = r
    have herr := raised_result _ _ _ _ _ _ hr h2e
    obtain ⟨u, s'⟩ := r
    simp only at herr
    simp [nonNull, herr]

end PyLean.PyGrammar.Peg
