import PyLean.PyGrammar.Peg.Rules.Params3

/-! `invalid_` rules with their exact messages, rule by rule: `invalid_group`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `'(' a=starred_expression ')'` failing from `X`, ending in `s`. -/
def IGA0Fails (f : Nat) (X s : PS) : Prop :=
  expectToken 7 X = (.null, s) ∨
  (∃ (c : Token) (s1 : PS), expectToken 7 X = (.tok c, s1) ∧ callRule (f + 3) 190 s1 = (.null, s)) ∨
  (∃ (c : Token) (a : Ast) (s1 s2 : PS), expectToken 7 X = (.tok c, s1) ∧
    callRule (f + 3) 190 s1 = (a, s2) ∧ a ≠ .null ∧ expectToken 8 s2 = (.null, s))

/-- `'(' a='**' expression ')'` failing from `X`, ending in `s`. -/
def IGA1Fails (f : Nat) (X s : PS) : Prop :=
  expectToken 7 X = (.null, s) ∨
  (∃ (c : Token) (s1 : PS), expectToken 7 X = (.tok c, s1) ∧ expectToken 35 s1 = (.null, s)) ∨
  (∃ (c d : Token) (s1 s2 : PS), expectToken 7 X = (.tok c, s1) ∧ expectToken 35 s1 = (.tok d, s2) ∧
    callRule (f + 1) 109 s2 = (.null, s)) ∨
  (∃ (c d : Token) (e : Ast) (s1 s2 s3 : PS), expectToken 7 X = (.tok c, s1) ∧
    expectToken 35 s1 = (.tok d, s2) ∧ callRule (f + 1) 109 s2 = (e, s3) ∧ e ≠ .null ∧
    expectToken 8 s3 = (.null, s))

/-- `invalid_group` (`Grammar/python.gram:1428-1432`), run in the second pass from `group`:
```
    | '(' a=starred_expression ')' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use starred expression here") }
    | '(' a='**' expression ')' {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "cannot use double starred expression here") }
```
No `EXTRA`. `(` (7), a `starred_expression` (190) and `)` (8) raise "cannot use starred expression
here" located at the starred expression (`(*a)`); once that fails, from the start mark, `(`, `**`
(35), an `expression` (109) and `)` raise "cannot use double starred expression here" located at
the `**` token (`(**a)`). Both end the rule with `NULL` and `error_indicator` set (`raisedAt`);
when neither matches, `NULL` with the mark back and no error. -/
def InvalidGroup : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a : Ast) (c c' : Token) (s1 s2 s3 : PS), expectToken 7 p.enter = (.tok c, s1) →
    callRule (f + 3) 190 s1 = (a, s2) → a ≠ .null → expectToken 8 s2 = (.tok c', s3) →
    s3.errorIndicator = false →
    callRule (f + 9) 236 p = (.null, (raisedAt a a "cannot use starred expression here" s3).leave)) ∧
  (∀ (s0 : PS), IGA0Fails f p.enter s0 → s0.errorIndicator = false →
    (∀ (e : Ast) (c d c' : Token) (s1 s2 s3 s4 : PS), expectToken 7 { s0 with mark := p.mark } = (.tok c, s1) →
      expectToken 35 s1 = (.tok d, s2) → callRule (f + 1) 109 s2 = (e, s3) → e ≠ .null →
      expectToken 8 s3 = (.tok c', s4) → s4.errorIndicator = false →
      callRule (f + 9) 236 p =
        (.null, (raisedAt (.tok d) (.tok d) "cannot use double starred expression here" s4).leave)) ∧
    (∀ (s1 : PS), IGA1Fails f { s0 with mark := p.mark } s1 →
      callRule (f + 9) 236 p = (.null, { s1 with mark := p.mark }.leave)))

theorem invalidGroup_proven : InvalidGroup := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 236 = r236 from rfl, r236]
  have hA : ∀ s0, IGA0Fails f p.enter s0 →
      runItems (f + 6) [.call (.tok 7), .call (.rule 190), .call (.tok 8)] #[] false p.enter =
        ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, a, s1, s2, h1, h2, ha, h3⟩
    · rw [items_call_null (by rw [call_tok, h1])]
    · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
    · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call_null (by rw [call_tok, h3])]
  refine ⟨fun a c c' s1 s2 s3 h1 h2 ha h3 h3e => ?_, fun s0 h0 h0e =>
    ⟨fun e c d c' s1 s2 s3 s4 h1 h2 h3 hE h4 h4e => ?_, fun s1 h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_tok, h3]) (by simp), items_nil]),
      altResult_raiseKL rfl rfl h3e (by decide +kernel)]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hE, items_call (by rw [call_tok, h4]) (by simp),
        items_nil]),
      altResult_raiseKL rfl rfl h4e (by decide +kernel)]
    rfl
  · have hB : runItems (f + 5) [.call (.tok 7), .call (.tok 35), .call (.rule 109), .call (.tok 8)] #[]
        false { s0 with mark := p.mark } = ((none, false), s1) := by
      rcases h1 with h1 | ⟨c, t1, h1, h2⟩ | ⟨c, d, t1, t2, h1, h2, h3⟩ |
          ⟨c, d, e, t1, t2, t3, h1, h2, h3, hE, h4⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_tok, h2])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
          items_call_null (by rw [call_rule, h3])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
          items_call (by rw [call_rule, h3]) hE, items_call_null (by rw [call_tok, h4])]
    rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) hB, alts_nil]
    rfl

end PyLean.PyGrammar.Peg
