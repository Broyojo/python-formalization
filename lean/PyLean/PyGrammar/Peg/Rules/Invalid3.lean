import PyLean.PyGrammar.Peg.Rules.Cmp

/-! `invalid_` rules with their exact messages and locations, rule by rule:
`invalid_starred_expression_unpacking`, `invalid_starred_expression_unpacking_sequence`,
`invalid_default`, `invalid_kwds`, `invalid_lambda_kwds`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `invalid_starred_expression_unpacking`, `..._sequence` -/

def condStarMsg : String :=
  "invalid starred expression. Did you forget to wrap the conditional expression in parentheses?"
def assignUnpackMsg : String := "cannot assign to iterable argument unpacking"

/-- `invalid_starred_expression_unpacking` (`Grammar/python.gram:1577-1580`), new in 3.15:
```
    | a='*' b=if_expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "invalid starred expression. Did you forget to wrap the conditional expression in parentheses?") }
    | a='*' expression '=' b=expression { RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, "cannot assign to iterable argument unpacking") }
```
No `EXTRA`. `*` (16) and an `if_expression` (110) raise the first message over `*` .. the
conditional; once that fails, from the start mark, `*`, an `expression` (109), `=` (22) and an
`expression` raise the second over `*` .. the right-hand side. Both end the rule with `NULL` and
`error_indicator` set; otherwise `NULL` with the mark back. -/
def InvalidStarredExpressionUnpacking : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (b : Ast) (c : Token) (s1 s2 : PS), expectToken 16 p.enter = (.tok c, s1) →
    callRule (f + 3) 110 s1 = (b, s2) → b ≠ .null → s2.errorIndicator = false →
    callRule (f + 9) 266 p = (.null, (raisedAt (.tok c) b condStarMsg s2).leave)) ∧
  (∀ (s0 : PS), (expectToken 16 p.enter = (.null, s0) ∨
      ∃ c s1, expectToken 16 p.enter = (.tok c, s1) ∧ callRule (f + 3) 110 s1 = (.null, s0)) →
    s0.errorIndicator = false →
    (∀ (a b : Ast) (c d : Token) (s1 s2 s3 s4 : PS), expectToken 16 { s0 with mark := p.mark } = (.tok c, s1) →
      callRule (f + 2) 109 s1 = (a, s2) → a ≠ .null → expectToken 22 s2 = (.tok d, s3) →
      callRule f 109 s3 = (b, s4) → b ≠ .null → s4.errorIndicator = false →
      callRule (f + 9) 266 p = (.null, (raisedAt (.tok c) b assignUnpackMsg s4).leave)) ∧
    (∀ (s : PS), (expectToken 16 { s0 with mark := p.mark } = (.null, s) ∨
        (∃ c s1, expectToken 16 { s0 with mark := p.mark } = (.tok c, s1) ∧ callRule (f + 2) 109 s1 = (.null, s)) ∨
        (∃ c a s1 s2, expectToken 16 { s0 with mark := p.mark } = (.tok c, s1) ∧
          callRule (f + 2) 109 s1 = (a, s2) ∧ a ≠ .null ∧ expectToken 22 s2 = (.null, s)) ∨
        (∃ c d a s1 s2 s3, expectToken 16 { s0 with mark := p.mark } = (.tok c, s1) ∧
          callRule (f + 2) 109 s1 = (a, s2) ∧ a ≠ .null ∧ expectToken 22 s2 = (.tok d, s3) ∧
          callRule f 109 s3 = (.null, s))) →
      callRule (f + 9) 266 p = (.null, { s with mark := p.mark }.leave)))

theorem invalidStarredExpressionUnpacking_proven : InvalidStarredExpressionUnpacking := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 266 = r266 from rfl, r266]
  refine ⟨fun b c s1 s2 h1 h2 hb h2e => ?_, fun s0 h0 h0e =>
    ⟨fun a b c d s1 s2 s3 s4 h1 h2 ha h3 h4 hb h4e => ?_, fun s hs => ?_⟩⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_raiseKR rfl rfl h2e (by decide +kernel)]
    rfl
  all_goals
    have hA : runItems (f + 6) [.call (.tok 16), .call (.rule 110)] #[] false p.enter = ((none, false), s0) := by
      rcases h0 with h0 | ⟨c, s1, h0, h0'⟩
      · rw [items_call_null (by rw [call_tok, h0])]
      · rw [items_call (by rw [call_tok, h0]) (by simp), items_call_null (by rw [call_rule, h0'])]
  · rw [alts_fail (by rfl) he' hA, alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hb, items_nil]),
      altResult_raiseKR rfl rfl h4e (by decide +kernel)]
    rfl
  · have hB : runItems (f + 5) [.call (.tok 16), .call (.rule 109), .call (.tok 22), .call (.rule 109)] #[]
        false { s0 with mark := p.mark } = ((none, false), s) := by
      rcases hs with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, a, s1, s2, h1, h2, ha, h3⟩ |
          ⟨c, d, a, s1, s2, s3, h1, h2, ha, h3, h4⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
          items_call_null (by rw [call_tok, h3])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
          items_call (by rw [call_tok, h3]) (by simp), items_call_null (by rw [call_rule, h4])]
    rw [alts_fail (by rfl) he' hA, alts_fail (by rfl) (E s0 h0e) hB, alts_nil]
    rfl

/-- `invalid_starred_expression_unpacking_sequence` (`Grammar/python.gram:1581-1584`), new in
3.15:
```
    | a='**' bitwise_or { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use dict unpacking here") }
    | invalid_starred_expression_unpacking
```
No `EXTRA`. `**` (35) and a `bitwise_or` (135) raise "cannot use dict unpacking here" located at
the `**` token (so `[**a]`, `(**a,)` and `{**a, *b}` get it); once that fails, in the second pass
`invalid_starred_expression_unpacking` (266) from the start mark; otherwise `NULL` with the mark
back. -/
def InvalidStarredExpressionUnpackingSequence : Prop := ∀ (f : Nat) (p : PS),
  p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (b : Ast) (c : Token) (s1 s2 : PS), expectToken 35 p.enter = (.tok c, s1) →
    callRule (f + 1) 135 s1 = (b, s2) → b ≠ .null → s2.errorIndicator = false →
    callRule (f + 7) 267 p = (.null, (raisedAt (.tok c) (.tok c) "cannot use dict unpacking here" s2).leave)) ∧
  (∀ (s0 : PS), (expectToken 35 p.enter = (.null, s0) ∨
      ∃ c s1, expectToken 35 p.enter = (.tok c, s1) ∧ callRule (f + 1) 135 s1 = (.null, s0)) →
    s0.errorIndicator = false →
    (s0.callInvalidRules = false → callRule (f + 7) 267 p = (.null, { s0 with mark := p.mark }.leave)) ∧
    (s0.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 1) 266 { s0 with mark := p.mark } = (v, s) →
      v ≠ .null → callRule (f + 7) 267 p = (v, s.leave)) ∧
    (s0.callInvalidRules = true → ∀ (s : PS), callRule (f + 1) 266 { s0 with mark := p.mark } = (.null, s) →
      callRule (f + 7) 267 p = (.null, { s with mark := p.mark }.leave)))

theorem invalidStarredExpressionUnpackingSequence_proven : InvalidStarredExpressionUnpackingSequence := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 267 = r267 from rfl, r267]
  refine ⟨fun b c s1 s2 h1 h2 hb h2e => ?_, fun s0 h0 h0e => ⟨fun hi => ?_, fun hi v s h1 hv => ?_,
    fun hi s h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_raiseKL rfl rfl h2e (by decide +kernel)]
    rfl
  all_goals
    have hA : runItems (f + 4) [.call (.tok 35), .call (.rule 135)] #[] false p.enter = ((none, false), s0) := by
      rcases h0 with h0 | ⟨c, s1, h0, h0'⟩
      · rw [items_call_null (by rw [call_tok, h0])]
      · rw [items_call (by rw [call_tok, h0]) (by simp), items_call_null (by rw [call_rule, h0'])]
  · rw [alts_fail (by rfl) he' hA, alts_skip (by simp [hi]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' hA, alts_ok (by simp [hi]) (E s0 h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' hA, alts_fail (by simp [hi]) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-! ### `invalid_default` -/

/-- `invalid_default: a='=' &(')'|',') { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "expected default
value expression") }` (`Grammar/python.gram:1373-1374`): `=` (22) followed by `)` or `,` (the
group `_tmp_126`, 403, not consumed) raises "expected default value expression" at the `=`
(`def f(a=): ...`); otherwise `NULL` with the mark back. -/
def InvalidDefault : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (x : Ast) (c : Token) (s1 s2 : PS), expectToken 22 p.enter = (.tok c, s1) →
    callRule f 403 s1 = (x, s2) → nonNull x = true → s2.errorIndicator = false →
    callRule (f + 6) 224 p = (.null, (raisedAt (.tok c) (.tok c) "expected default value expression"
      { s2 with mark := s1.mark }).leave)) ∧
  (∀ (x : Ast) (c : Token) (s1 s2 : PS), expectToken 22 p.enter = (.tok c, s1) →
    callRule f 403 s1 = (x, s2) → nonNull x = false →
    callRule (f + 6) 224 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (s1 : PS), expectToken 22 p.enter = (.null, s1) →
    callRule (f + 6) 224 p = (.null, { s1 with mark := p.mark }.leave))

theorem invalidDefault_proven : InvalidDefault := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 224 = r224 from rfl, r224]
  refine ⟨fun x c s1 s2 h1 h2 hx h2e => ?_, fun x c s1 s2 h1 h2 hx => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_look (by rw [call_rule, h2]) hx, items_nil]),
      altResult_raiseKL rfl rfl (show ({ s2 with mark := s1.mark } : PS).errorIndicator = false from h2e)
        (by decide +kernel)]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_look_fail (by rw [call_rule, h2]) (by simpa using hx)]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, h1])]), alts_nil]
    rfl

end PyLean.PyGrammar.Peg
