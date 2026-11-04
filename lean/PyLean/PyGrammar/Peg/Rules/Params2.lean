import PyLean.PyGrammar.Peg.Rules.Params

/-! Function and lambda parameters, continued (`Grammar/python.gram:318-376`, `925-962`):
`param_no_default` (and its `star_annotation` twin), the `*_with_default` and `*_maybe_default`
rules, `slash_with_default`, `star_etc` and `parameters`, with their lambda twins, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem addTypeComment_nonNull (a tc : Ast) (h : a ≠ .null) : nonNull (addTypeComment a tc) = true := by
  unfold addTypeComment
  split
  · cases a <;> simp_all [nonNull]
  · simp [nonNull]
  · cases a <;> simp_all [nonNull]

theorem addTypeComment_null (a : Ast) : addTypeComment a .null = a := by
  simp [addTypeComment]

/-! ### `param_no_default`, `param_no_default_star_annotation` -/

/-- `a=pr ','` failing from `X`, ending in `s`. -/
def PNDFails (f pr : Nat) (X s : PS) : Prop :=
  callRule (f + 3) pr X = (.null, s) ∨
  ∃ (a : Ast) (s1 : PS), callRule (f + 3) pr X = (a, s1) ∧ a ≠ .null ∧ expectToken 12 s1 = (.null, s)

/-- `param_no_default` (`Grammar/python.gram:365-367`) and `param_no_default_star_annotation`
(`Grammar/python.gram:368-370`):
```
    | a=param ',' tc=TYPE_COMMENT? { _PyPegen_add_type_comment_to_arg(p, a, tc) }
    | a=param tc=TYPE_COMMENT? &')' { _PyPegen_add_type_comment_to_arg(p, a, tc) }
```
(the twin with `param_star_annotation`). No `EXTRA`. A parameter (`pr`), `,` (12) and an optional
`TYPE_COMMENT` (57) give the parameter with that type comment; once that fails, from the start
mark, a parameter, an optional `TYPE_COMMENT` and `)` (8, not consumed) give it; otherwise `NULL`
with the mark back. -/
def ParamNoDefault (id pr : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a tc : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 3) pr p.enter = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.tok c, s2) → expectToken 57 s2 = (tc, s3) → s3.errorIndicator = false →
    callRule (f + 8) id p = (addTypeComment a tc, s3.leave)) ∧
  (∀ (s0 s1 s2 s3 : PS) (a tc x : Ast), PNDFails f pr p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) pr { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    expectToken 57 s1 = (tc, s2) → s2.errorIndicator = false → expectToken 8 s2 = (x, s3) →
    (nonNull x = true → s3.errorIndicator = false →
      callRule (f + 8) id p = (addTypeComment a tc, { s3 with mark := s2.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 8) id p = (.null, { s3 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), PNDFails f pr p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) pr { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 8) id p = (.null, { s1 with mark := p.mark }.leave))

theorem paramNoDefault_of {id pr : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule pr), .call (.tok 12), .opt (.tok 57)]
        (some (.call .add_type_comment_to_arg [.var 0, .var 2])) 3 false false,
       Alt.mk [.call (.rule pr), .opt (.tok 57), .look true (.tok 8)]
        (some (.call .add_type_comment_to_arg [.var 0, .var 1])) 2 false false]) :
    ParamNoDefault id pr := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  have hA : ∀ s0, PNDFails f pr p.enter s0 →
      runItems (f + 5) [.call (.rule pr), .call (.tok 12), .opt (.tok 57)] #[] false p.enter =
        ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, s1, h1, ha, h2⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]
  refine ⟨fun a tc c s1 s2 s3 h1 ha h2 h3 h3e => ?_,
    fun s0 s1 s2 s3 a tc x h0 h0e h1 ha h2 h2e h3 => ⟨fun hx h3e => ?_, fun hx => ?_⟩,
    fun s0 s1 h0 h0e h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_opt (by rw [call_tok, h3]) h3e, items_nil]), altResult_plain rfl rfl]
    have hn := addTypeComment_nonNull a tc ha
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [hn, h3e]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_tok, h2]) h2e,
        items_look (by rw [call_tok, h3]) hx, items_nil]), altResult_plain rfl rfl]
    have hn := addTypeComment_nonNull a tc ha
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [hn, h3e]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_tok, h2]) h2e,
        items_look_fail (by rw [call_tok, h3]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

theorem paramNoDefault_proven : ParamNoDefault 45 49 := paramNoDefault_of rfl
theorem paramNoDefaultStarAnnotation_proven : ParamNoDefault 46 50 := paramNoDefault_of rfl

/-! ### `param_with_default`, `param_maybe_default` -/

/-- `a=param c=default ','` failing from `X`, ending in `s`. -/
def PWDFails (f : Nat) (X s : PS) : Prop :=
  callRule (f + 4) 49 X = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (f + 4) 49 X = (a, s1) ∧ a ≠ .null ∧ callRule (f + 3) 53 s1 = (.null, s)) ∨
  (∃ (a d : Ast) (s1 s2 : PS), callRule (f + 4) 49 X = (a, s1) ∧ a ≠ .null ∧
    callRule (f + 3) 53 s1 = (d, s2) ∧ d ≠ .null ∧ expectToken 12 s2 = (.null, s))

/-- `param_with_default` (`Grammar/python.gram:371-373`):
```
    | a=param c=default ',' tc=TYPE_COMMENT? { _PyPegen_name_default_pair(p, a, c, tc) }
    | a=param c=default tc=TYPE_COMMENT? &')' { _PyPegen_name_default_pair(p, a, c, tc) }
```
No `EXTRA`. A `param` (49), a `default` (53), `,` (12) and an optional `TYPE_COMMENT` (57) give the
pair (the parameter with that type comment, its default); once that fails, from the start mark,
`param`, `default`, an optional `TYPE_COMMENT` and `)` (8, not consumed) give it; otherwise `NULL`
with the mark back. -/
def ParamWithDefault : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a d tc : Ast) (c : Token) (s1 s2 s3 s4 : PS), callRule (f + 4) 49 p.enter = (a, s1) →
    a ≠ .null → callRule (f + 3) 53 s1 = (d, s2) → d ≠ .null → expectToken 12 s2 = (.tok c, s3) →
    expectToken 57 s3 = (tc, s4) → s4.errorIndicator = false →
    callRule (f + 9) 47 p = (rec_ .PNameDefaultPair [addTypeComment a tc, d], s4.leave)) ∧
  (∀ (s0 s1 s2 s3 s4 : PS) (a d tc x : Ast), PWDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 3) 49 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    callRule (f + 2) 53 s1 = (d, s2) → d ≠ .null → expectToken 57 s2 = (tc, s3) →
    s3.errorIndicator = false → expectToken 8 s3 = (x, s4) →
    (nonNull x = true → s4.errorIndicator = false →
      callRule (f + 9) 47 p = (rec_ .PNameDefaultPair [addTypeComment a tc, d],
        { s4 with mark := s3.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 9) 47 p = (.null, { s4 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), PWDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 3) 49 { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 9) 47 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (s0 s1 s2 : PS) (a : Ast), PWDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 3) 49 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    callRule (f + 2) 53 s1 = (.null, s2) →
    callRule (f + 9) 47 p = (.null, { s2 with mark := p.mark }.leave))

theorem paramWithDefault_proven : ParamWithDefault := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 47 = r47 from rfl, r47]
  have hA : ∀ s0, PWDFails f p.enter s0 →
      runItems (f + 6) [.call (.rule 49), .call (.rule 53), .call (.tok 12), .opt (.tok 57)] #[] false
        p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, s1, h1, ha, h2⟩ | ⟨a, d, s1, s2, h1, ha, h2, hd, h3⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_call_null (by rw [call_tok, h3])]
  refine ⟨fun a d tc c s1 s2 s3 s4 h1 ha h2 hd h3 h4 h4e => ?_,
    fun s0 s1 s2 s3 s4 a d tc x h0 h0e h1 ha h2 hd h3 h3e h4 => ⟨fun hx h4e => ?_, fun hx => ?_⟩,
    fun s0 s1 h0 h0e h1 => ?_, fun s0 s1 s2 a h0 h0e h1 ha h2 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_call (by rw [call_tok, h3]) (by simp), items_opt (by rw [call_tok, h4]) h4e,
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_opt (by rw [call_tok, h3]) h3e, items_look (by rw [call_tok, h4]) hx, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_opt (by rw [call_tok, h3]) h3e,
        items_look_fail (by rw [call_tok, h4]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl

/-- `a=param c=default? ','` failing from `X`, ending in `s`. -/
def PMDFails (f : Nat) (X s : PS) : Prop :=
  callRule (f + 4) 49 X = (.null, s) ∨
  (∃ (a d : Ast) (s1 s2 : PS), callRule (f + 4) 49 X = (a, s1) ∧ a ≠ .null ∧
    callRule (f + 3) 53 s1 = (d, s2) ∧ s2.errorIndicator = false ∧ expectToken 12 s2 = (.null, s))

/-- `param_maybe_default` (`Grammar/python.gram:374-376`):
```
    | a=param c=default? ',' tc=TYPE_COMMENT? { _PyPegen_name_default_pair(p, a, c, tc) }
    | a=param c=default? tc=TYPE_COMMENT? &')' { _PyPegen_name_default_pair(p, a, c, tc) }
```
As `param_with_default` with the `default` optional (`NULL` in the pair without one). -/
def ParamMaybeDefault : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a d tc : Ast) (c : Token) (s1 s2 s3 s4 : PS), callRule (f + 4) 49 p.enter = (a, s1) →
    a ≠ .null → callRule (f + 3) 53 s1 = (d, s2) → s2.errorIndicator = false →
    expectToken 12 s2 = (.tok c, s3) → expectToken 57 s3 = (tc, s4) → s4.errorIndicator = false →
    callRule (f + 9) 48 p = (rec_ .PNameDefaultPair [addTypeComment a tc, d], s4.leave)) ∧
  (∀ (s0 s1 s2 s3 s4 : PS) (a d tc x : Ast), PMDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 3) 49 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    callRule (f + 2) 53 s1 = (d, s2) → s2.errorIndicator = false → expectToken 57 s2 = (tc, s3) →
    s3.errorIndicator = false → expectToken 8 s3 = (x, s4) →
    (nonNull x = true → s4.errorIndicator = false →
      callRule (f + 9) 48 p = (rec_ .PNameDefaultPair [addTypeComment a tc, d],
        { s4 with mark := s3.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 9) 48 p = (.null, { s4 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), PMDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 3) 49 { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 9) 48 p = (.null, { s1 with mark := p.mark }.leave))

theorem paramMaybeDefault_proven : ParamMaybeDefault := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 48 = r48 from rfl, r48]
  have hA : ∀ s0, PMDFails f p.enter s0 →
      runItems (f + 6) [.call (.rule 49), .opt (.rule 53), .call (.tok 12), .opt (.tok 57)] #[] false
        p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, d, s1, s2, h1, ha, h2, h2e, h3⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_call_null (by rw [call_tok, h3])]
  refine ⟨fun a d tc c s1 s2 s3 s4 h1 ha h2 h2e h3 h4 h4e => ?_,
    fun s0 s1 s2 s3 s4 a d tc x h0 h0e h1 ha h2 h2e h3 h3e h4 => ⟨fun hx h4e => ?_, fun hx => ?_⟩,
    fun s0 s1 h0 h0e h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_call (by rw [call_tok, h3]) (by simp), items_opt (by rw [call_tok, h4]) h4e,
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_opt (by rw [call_tok, h3]) h3e, items_look (by rw [call_tok, h4]) hx, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_opt (by rw [call_tok, h3]) h3e,
        items_look_fail (by rw [call_tok, h4]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-! ### `lambda_param_with_default`, `lambda_param_maybe_default` -/

/-- `a=lambda_param c=default ','` failing from `X`, ending in `s`. -/
def LPWDFails (f : Nat) (X s : PS) : Prop :=
  callRule (f + 3) 159 X = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (f + 3) 159 X = (a, s1) ∧ a ≠ .null ∧ callRule (f + 2) 53 s1 = (.null, s)) ∨
  (∃ (a d : Ast) (s1 s2 : PS), callRule (f + 3) 159 X = (a, s1) ∧ a ≠ .null ∧
    callRule (f + 2) 53 s1 = (d, s2) ∧ d ≠ .null ∧ expectToken 12 s2 = (.null, s))

/-- `lambda_param_with_default` (`Grammar/python.gram:958-960`):
```
    | a=lambda_param c=default ',' { _PyPegen_name_default_pair(p, a, c, NULL) }
    | a=lambda_param c=default &':' { _PyPegen_name_default_pair(p, a, c, NULL) }
```
No `EXTRA`. A `lambda_param` (159), a `default` (53) and `,` (12) give the pair (no type comment);
once that fails, from the start mark, `lambda_param`, `default` and `:` (11, not consumed) give
it; otherwise `NULL` with the mark back. -/
def LambdaParamWithDefault : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a d : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 3) 159 p.enter = (a, s1) → a ≠ .null →
    callRule (f + 2) 53 s1 = (d, s2) → d ≠ .null → expectToken 12 s2 = (.tok c, s3) →
    s3.errorIndicator = false → callRule (f + 8) 157 p = (rec_ .PNameDefaultPair [a, d], s3.leave)) ∧
  (∀ (s0 s1 s2 s3 : PS) (a d x : Ast), LPWDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) 159 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    callRule (f + 1) 53 s1 = (d, s2) → d ≠ .null → expectToken 11 s2 = (x, s3) →
    (nonNull x = true → s3.errorIndicator = false →
      callRule (f + 8) 157 p = (rec_ .PNameDefaultPair [a, d], { s3 with mark := s2.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 8) 157 p = (.null, { s3 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), LPWDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) 159 { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 8) 157 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (s0 s1 s2 : PS) (a : Ast), LPWDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) 159 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    callRule (f + 1) 53 s1 = (.null, s2) →
    callRule (f + 8) 157 p = (.null, { s2 with mark := p.mark }.leave))

theorem lambdaParamWithDefault_proven : LambdaParamWithDefault := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 157 = r157 from rfl, r157]
  have hA : ∀ s0, LPWDFails f p.enter s0 →
      runItems (f + 5) [.call (.rule 159), .call (.rule 53), .call (.tok 12)] #[] false
        p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, s1, h1, ha, h2⟩ | ⟨a, d, s1, s2, h1, ha, h2, hd, h3⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_call_null (by rw [call_tok, h3])]
  refine ⟨fun a d c s1 s2 s3 h1 ha h2 hd h3 h3e => ?_,
    fun s0 s1 s2 s3 a d x h0 h0e h1 ha h2 hd h3 => ⟨fun hx h3e => ?_, fun hx => ?_⟩,
    fun s0 s1 h0 h0e h1 => ?_, fun s0 s1 s2 a h0 h0e h1 ha h2 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_call (by rw [call_tok, h3]) (by simp), items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_, addTypeComment_null]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_look (by rw [call_tok, h3]) hx, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_, addTypeComment_null]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hd,
        items_look_fail (by rw [call_tok, h3]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl

/-- `a=lambda_param c=default? ','` failing from `X`, ending in `s`. -/
def LPMDFails (f : Nat) (X s : PS) : Prop :=
  callRule (f + 3) 159 X = (.null, s) ∨
  (∃ (a d : Ast) (s1 s2 : PS), callRule (f + 3) 159 X = (a, s1) ∧ a ≠ .null ∧
    callRule (f + 2) 53 s1 = (d, s2) ∧ s2.errorIndicator = false ∧ expectToken 12 s2 = (.null, s))

/-- `lambda_param_maybe_default` (`Grammar/python.gram:961-963`):
```
    | a=lambda_param c=default? ',' { _PyPegen_name_default_pair(p, a, c, NULL) }
    | a=lambda_param c=default? &':' { _PyPegen_name_default_pair(p, a, c, NULL) }
```
As `lambda_param_with_default` with the `default` optional. -/
def LambdaParamMaybeDefault : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a d : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 3) 159 p.enter = (a, s1) → a ≠ .null →
    callRule (f + 2) 53 s1 = (d, s2) → s2.errorIndicator = false → expectToken 12 s2 = (.tok c, s3) →
    s3.errorIndicator = false → callRule (f + 8) 158 p = (rec_ .PNameDefaultPair [a, d], s3.leave)) ∧
  (∀ (s0 s1 s2 s3 : PS) (a d x : Ast), LPMDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) 159 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    callRule (f + 1) 53 s1 = (d, s2) → s2.errorIndicator = false → expectToken 11 s2 = (x, s3) →
    (nonNull x = true → s3.errorIndicator = false →
      callRule (f + 8) 158 p = (rec_ .PNameDefaultPair [a, d], { s3 with mark := s2.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 8) 158 p = (.null, { s3 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), LPMDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) 159 { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 8) 158 p = (.null, { s1 with mark := p.mark }.leave))

theorem lambdaParamMaybeDefault_proven : LambdaParamMaybeDefault := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 158 = r158 from rfl, r158]
  have hA : ∀ s0, LPMDFails f p.enter s0 →
      runItems (f + 5) [.call (.rule 159), .opt (.rule 53), .call (.tok 12)] #[] false
        p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, d, s1, s2, h1, ha, h2, h2e, h3⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_call_null (by rw [call_tok, h3])]
  refine ⟨fun a d c s1 s2 s3 h1 ha h2 h2e h3 h3e => ?_,
    fun s0 s1 s2 s3 a d x h0 h0e h1 ha h2 h2e h3 => ⟨fun hx h3e => ?_, fun hx => ?_⟩,
    fun s0 s1 h0 h0e h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_call (by rw [call_tok, h3]) (by simp), items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_, addTypeComment_null]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_look (by rw [call_tok, h3]) hx, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_, addTypeComment_null]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e,
        items_look_fail (by rw [call_tok, h3]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-! ### `slash_with_default`, `lambda_slash_with_default` -/

/-- `a=l0 b=l1 '/'` failing from `X` (`l0` called with fuel `g + 1`), ending in `s`. -/
def SlashWDHeadFails (g l0 l1 : Nat) (X s : PS) : Prop :=
  callRule (g + 1) l0 X = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (g + 1) l0 X = (a, s1) ∧ a ≠ .null ∧ callRule g l1 s1 = (.null, s)) ∨
  (∃ (a b : Ast) (s1 s2 : PS), callRule (g + 1) l0 X = (a, s1) ∧ a ≠ .null ∧
    callRule g l1 s1 = (b, s2) ∧ b ≠ .null ∧ expectToken 17 s2 = (.null, s))

/-- `a=l0 b=l1 '/'` matching from `X`, ending in `s3`. -/
def SlashWDHead (g l0 l1 : Nat) (X : PS) (a b : Ast) (s3 : PS) : Prop :=
  ∃ (c : Token) (s1 s2 : PS), callRule (g + 1) l0 X = (a, s1) ∧ a ≠ .null ∧
    callRule g l1 s1 = (b, s2) ∧ b ≠ .null ∧ expectToken 17 s2 = (.tok c, s3)

/-- `slash_with_default` (`Grammar/python.gram:334-336`) and `lambda_slash_with_default`
(`Grammar/python.gram:939-941`):
```
    | a=param_no_default* b=param_with_default+ '/' ',' { _PyPegen_slash_with_default(p, (asdl_arg_seq *)a, b) }
    | a=param_no_default* b=param_with_default+ '/' &')' { _PyPegen_slash_with_default(p, (asdl_arg_seq *)a, b) }
```
(the lambda rule with the lambda parameters and `&':'`). No `EXTRA`. The `*` loop (`l0`), the `+`
loop (`l1`), `/` (17) and `,` (12) give the `SlashWithDefault` record of the two sequences; once
that fails, from the start mark, the loops and `/` followed by `lk` (not consumed) give it;
otherwise `NULL` with the mark back. -/
def SlashWithDefault (id l0 l1 lk : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a b : Ast) (c : Token) (s3 s4 : PS), SlashWDHead (f + 3) l0 l1 p.enter a b s3 →
    expectToken 12 s3 = (.tok c, s4) → s4.errorIndicator = false →
    callRule (f + 9) id p = (rec_ .PSlashWithDefault [a, b], s4.leave)) ∧
  (∀ (s0 : PS), (SlashWDHeadFails (f + 3) l0 l1 p.enter s0 ∨
      ∃ a b s3, SlashWDHead (f + 3) l0 l1 p.enter a b s3 ∧ expectToken 12 s3 = (.null, s0)) →
    s0.errorIndicator = false →
    (∀ (a b x : Ast) (s3 s4 : PS), SlashWDHead (f + 2) l0 l1 { s0 with mark := p.mark } a b s3 →
      expectToken lk s3 = (x, s4) →
      (nonNull x = true → s4.errorIndicator = false →
        callRule (f + 9) id p = (rec_ .PSlashWithDefault [a, b], { s4 with mark := s3.mark }.leave)) ∧
      (nonNull x = false → callRule (f + 9) id p = (.null, { s4 with mark := p.mark }.leave))) ∧
    (∀ (s1 : PS), SlashWDHeadFails (f + 2) l0 l1 { s0 with mark := p.mark } s1 →
      callRule (f + 9) id p = (.null, { s1 with mark := p.mark }.leave)))

theorem slashWDHead_items {g l0 l1 : Nat} {X s : PS} {rest : List Item}
    (h : SlashWDHeadFails (g + 1) l0 l1 X s) :
    runItems (g + 4) (.call (.rule l0) :: .call (.rule l1) :: .call (.tok 17) :: rest) #[] false X =
      ((none, false), s) := by
  rcases h with h1 | ⟨a, s1, h1, ha, h2⟩ | ⟨a, b, s1, s2, h1, ha, h2, hb, h3⟩
  · rw [items_call_null (by rw [call_rule, h1])]
  · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]
  · rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb,
      items_call_null (by rw [call_tok, h3])]

theorem slashWDHead_ok {g l0 l1 : Nat} {X s3 : PS} {a b : Ast} {rest : List Item}
    (h : SlashWDHead (g + 1) l0 l1 X a b s3) :
    ∃ c, runItems (g + 4) (.call (.rule l0) :: .call (.rule l1) :: .call (.tok 17) :: rest) #[] false X =
      runItems (g + 1) rest (((#[] : Array Ast).push a |>.push b).push (.tok c)) false s3 := by
  obtain ⟨c, s1, s2, h1, ha, h2, hb, h3⟩ := h
  exact ⟨c, by rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb,
    items_call (by rw [call_tok, h3]) (by simp)]⟩

theorem slashWithDefault_of {id l0 l1 lk : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule l0), .call (.rule l1), .call (.tok 17), .call (.tok 12)]
        (some (.call .slash_with_default [.var 0, .var 1])) 4 false false,
       Alt.mk [.call (.rule l0), .call (.rule l1), .call (.tok 17), .look true (.tok lk)]
        (some (.call .slash_with_default [.var 0, .var 1])) 3 false false]) :
    SlashWithDefault id l0 l1 lk := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  have hA : ∀ s0, (SlashWDHeadFails (f + 3) l0 l1 p.enter s0 ∨
      ∃ a b s3, SlashWDHead (f + 3) l0 l1 p.enter a b s3 ∧ expectToken 12 s3 = (.null, s0)) →
      runItems (f + 6) [.call (.rule l0), .call (.rule l1), .call (.tok 17), .call (.tok 12)] #[]
        false p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h0 | ⟨a, b, s3, hh, h4⟩
    · exact slashWDHead_items (g := f + 2) h0
    · obtain ⟨c, hc⟩ := slashWDHead_ok (g := f + 2) (rest := [.call (.tok 12)]) hh
      rw [hc, items_call_null (by rw [call_tok, h4])]
  refine ⟨fun a b c s3 s4 hh h4 h4e => ?_, fun s0 h0 h0e => ⟨fun a b x s3 s4 hh h4 =>
    ⟨fun hx h4e => ?_, fun hx => ?_⟩, fun s1 h1 => ?_⟩⟩
  · obtain ⟨c', hc⟩ := slashWDHead_ok (g := f + 2) (rest := [.call (.tok 12)]) hh
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [hc, items_call (by rw [call_tok, h4]) (by simp), items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · obtain ⟨c', hc⟩ := slashWDHead_ok (g := f + 1) (rest := [.look true (.tok lk)]) hh
    rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [hc, items_look (by rw [call_tok, h4]) hx, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · obtain ⟨c', hc⟩ := slashWDHead_ok (g := f + 1) (rest := [.look true (.tok lk)]) hh
    rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [hc, items_look_fail (by rw [call_tok, h4]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e)
      (slashWDHead_items (g := f + 1) h1), alts_nil]
    rfl

/-- `slash_with_default` (42): `param_no_default*` is `_loop0_27` (304), `param_with_default+`
`_loop1_30` (307), `&')'` 8. -/
theorem slashWithDefault_proven : SlashWithDefault 42 304 307 8 := slashWithDefault_of rfl
/-- `lambda_slash_with_default` (153): `_loop0_72` (349), `_loop1_75` (352), `&':'` 11. -/
theorem lambdaSlashWithDefault_proven : SlashWithDefault 153 349 352 11 := slashWithDefault_of rfl

/-! ### The loops -/

theorem loop0_27_proven : Loop0Over 304 45 := loop0Over_of rfl
theorem loop0_28_proven : Loop0Over 305 47 := loop0Over_of rfl
theorem loop1_30_proven : Loop1Over 307 47 := loop1Over_of rfl
theorem loop0_31_proven : Loop0Over 308 48 := loop0Over_of rfl
theorem loop1_32_proven : Loop1Over 309 48 := loop1Over_of rfl
theorem loop0_72_proven : Loop0Over 349 156 := loop0Over_of rfl
theorem loop0_73_proven : Loop0Over 350 157 := loop0Over_of rfl
theorem loop1_75_proven : Loop1Over 352 157 := loop1Over_of rfl
theorem loop0_76_proven : Loop0Over 353 158 := loop0Over_of rfl
theorem loop1_77_proven : Loop1Over 354 158 := loop1Over_of rfl

end PyLean.PyGrammar.Peg
