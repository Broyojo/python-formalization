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
the `**` token. Both end the rule with `NULL` and `error_indicator` set (`raisedAt`); when neither
matches, `NULL` with the mark back and no error. Through `atom` (`tuple | group | genexp`), 3.15
reaches the second alternative only for an operand that is not a `bitwise_or` (`(**not a)`,
`(**lambda: 0)`): `(**a)` raises "cannot use dict unpacking here" first, in `tuple`'s
`star_named_expression_sequence` (`invalid_starred_expression_unpacking_sequence`). -/
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


/-! ### The parameter rules with the loops they call -/

def SlashNoDefaultRule : Prop := SlashNoDefault 41 306 8 ∧ Loop1Over 306 45
theorem slashNoDefaultRule_proven : SlashNoDefaultRule := ⟨slashNoDefault_proven, loop1_29_proven⟩
def LambdaSlashNoDefaultRule : Prop := SlashNoDefault 152 351 11 ∧ Loop1Over 351 156
theorem lambdaSlashNoDefaultRule_proven : LambdaSlashNoDefaultRule :=
  ⟨lambdaSlashNoDefault_proven, loop1_74_proven⟩
def KwdsRule : Prop := Kwds 44 226 45
theorem kwdsRule_proven : KwdsRule := kwds_proven
def LambdaKwdsRule : Prop := Kwds 155 231 156
theorem lambdaKwdsRule_proven : LambdaKwdsRule := lambdaKwds_proven
def ParamsRule : Prop := InvOr 39 223 40
theorem paramsRule_proven : ParamsRule := params_proven
def LambdaParamsRule : Prop := InvOr 150 228 151
theorem lambdaParamsRule_proven : LambdaParamsRule := lambdaParams_proven
def StarNamedExpressionSequenceRule : Prop := InvOr 117 267 116
theorem starNamedExpressionSequenceRule_proven : StarNamedExpressionSequenceRule :=
  starNamedExpressionSequence_proven
def ParamNoDefaultRule : Prop := ParamNoDefault 45 49
theorem paramNoDefaultRule_proven : ParamNoDefaultRule := paramNoDefault_proven
def ParamNoDefaultStarAnnotationRule : Prop := ParamNoDefault 46 50
theorem paramNoDefaultStarAnnotationRule_proven : ParamNoDefaultStarAnnotationRule :=
  paramNoDefaultStarAnnotation_proven
def SlashWithDefaultRule : Prop := SlashWithDefault 42 304 307 8 ∧ Loop0Over 304 45 ∧ Loop1Over 307 47
theorem slashWithDefaultRule_proven : SlashWithDefaultRule :=
  ⟨slashWithDefault_proven, loop0_27_proven, loop1_30_proven⟩
def LambdaSlashWithDefaultRule : Prop :=
  SlashWithDefault 153 349 352 11 ∧ Loop0Over 349 156 ∧ Loop1Over 352 157
theorem lambdaSlashWithDefaultRule_proven : LambdaSlashWithDefaultRule :=
  ⟨lambdaSlashWithDefault_proven, loop0_72_proven, loop1_75_proven⟩
def StarEtcRule : Prop := StarEtc ∧ Loop0Over 308 48 ∧ Loop1Over 309 48
theorem starEtcRule_proven : StarEtcRule := ⟨starEtc_proven, loop0_31_proven, loop1_32_proven⟩
def LambdaStarEtcRule : Prop := LambdaStarEtc ∧ Loop0Over 353 158 ∧ Loop1Over 354 158
theorem lambdaStarEtcRule_proven : LambdaStarEtcRule :=
  ⟨lambdaStarEtc_proven, loop0_76_proven, loop1_77_proven⟩
def ParametersRule : Prop := Parameters 40 41 42 304 305 306 307 43 ∧ Loop0Over 304 45 ∧
  Loop0Over 305 47 ∧ Loop1Over 306 45 ∧ Loop1Over 307 47
theorem parametersRule_proven : ParametersRule :=
  ⟨parameters_proven, loop0_27_proven, loop0_28_proven, loop1_29_proven, loop1_30_proven⟩
def LambdaParametersRule : Prop := Parameters 151 152 153 349 350 351 352 154 ∧ Loop0Over 349 156 ∧
  Loop0Over 350 157 ∧ Loop1Over 351 156 ∧ Loop1Over 352 157
theorem lambdaParametersRule_proven : LambdaParametersRule :=
  ⟨lambdaParameters_proven, loop0_72_proven, loop0_73_proven, loop1_74_proven, loop1_75_proven⟩

end PyLean.PyGrammar.Peg
