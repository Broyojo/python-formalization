import PyLean.PyGrammar.Peg.Rules.Base3

/-! Function and lambda parameters (`Grammar/python.gram:314-380` and `917-966`), rule by rule:
`param`, `param_star_annotation`, `lambda_param`, the `*_no_default` rules, `slash_no_default`,
`kwds`, `params` and their lambda twins. The lambda rules repeat the function rules without
annotations or type comments, and with `&':'` for `&')'`; where the two have the same shape one
statement, over the rule numbers, covers both. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Reaching the alternatives after a leading `invalid_` one -/

/-- The alternatives after a leading `invalid_x` alternative (rule `inv`) start from `X`: in the
first pass the entry state (the `invalid_` alternative is not tried), in the second the state
`invalid_x` left with the mark back, when it gave `NULL` without an error. -/
def InvPass (g inv : Nat) (p X : PS) : Prop :=
  (p.callInvalidRules = false ∧ X = p.enter) ∨
  (p.callInvalidRules = true ∧ ∃ s, callRule g inv p.enter = (.null, s) ∧ s.errorIndicator = false ∧
    X = { s with mark := p.mark })

/-- The leading `invalid_` alternative of a rule without `EXTRA`. -/
def invAlt (inv : Nat) : Alt := Alt.mk [.call (.rule inv)] none 1 true false

theorem invPass_alts {g inv : Nat} {p X : PS} {rest : List Alt} {st : Int × Int}
    (he : p.errorIndicator = false) (h : InvPass g inv p X) :
    runAlts (g + 3) (invAlt inv :: rest) false p.mark st p.enter =
      runAlts (g + 2) rest false p.mark st X := by
  have he' : p.enter.errorIndicator = false := he
  rcases h with ⟨hi, rfl⟩ | ⟨hi, s, h1, h1e, rfl⟩
  · have hi' : p.enter.callInvalidRules = false := hi
    rw [alts_skip (by simp [invAlt, hi'])]
  · have hi' : p.enter.callInvalidRules = true := hi
    rw [alts_fail (by simp [invAlt, hi']) he' (by
      show runItems (g + 2) [.call (.rule inv)] #[] false p.enter = _
      rw [items_call_null (by rw [call_rule, h1])])]

/-- The second pass of a leading `invalid_` alternative giving a non-`NULL` result. -/
theorem invAlt_ok {g inv : Nat} {p s : PS} {v : Ast} {rest : List Alt} {st : Int × Int}
    (he : p.errorIndicator = false) (hi : p.callInvalidRules = true)
    (h1 : callRule g inv p.enter = (v, s)) (hv : v ≠ .null) :
    runAlts (g + 3) (invAlt inv :: rest) false p.mark st p.enter = (some v, s) := by
  have he' : p.enter.errorIndicator = false := he
  have hi' : p.enter.callInvalidRules = true := hi
  rw [alts_ok (by simp [invAlt, hi']) he' (by
    show runItems (g + 2) [.call (.rule inv)] #[] false p.enter = _
    rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
  rfl

/-- The second pass of a leading `invalid_` alternative raising: the next alternative (not an
`invalid_` one) sees `error_indicator` and the rule gives `NULL`. -/
theorem invAlt_err {g inv : Nat} {p s : PS} {a : Alt} {rest : List Alt} {st : Int × Int}
    (he : p.errorIndicator = false) (hi : p.callInvalidRules = true) (hg : a.guardInvalid = false)
    (h1 : callRule g inv p.enter = (.null, s)) (h1e : s.errorIndicator = true) :
    runAlts (g + 3) (invAlt inv :: a :: rest) false p.mark st p.enter =
      (none, { s with mark := p.mark }) := by
  have he' : p.enter.errorIndicator = false := he
  have hi' : p.enter.callInvalidRules = true := hi
  rw [alts_fail (by simp [invAlt, hi']) he' (by
      show runItems (g + 2) [.call (.rule inv)] #[] false p.enter = _
      rw [items_call_null (by rw [call_rule, h1])]),
    alts_err (by simp [hg]) (show ({ s with mark := p.mark } : PS).errorIndicator = true from h1e)]

/-! ### One parameter: `param`, `param_star_annotation`, `lambda_param` -/

/-- `lambda_param[arg_ty]: a=NAME { _PyAST_arg(a->v.Name.id, NULL, NULL, EXTRA) }`
(`Grammar/python.gram:964`): a `NAME` gives `arg(name, annotation = NULL, type_comment = NULL)`
spanning it; no `NAME` gives `NULL` with the mark back. -/
def LambdaParam : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (n : Ast) (s : PS), nameToken q = (n, s) → n ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 159 p = (mkAt .arg_ [fieldOf n "id", .null, .null] (extraLoc t s), s.leave)) ∧
  (∀ (s : PS), nameToken q = (.null, s) →
    callRule (f + 5) 159 p = (.null, { s with mark := p.mark }.leave))

theorem lambdaParam_proven : LambdaParam := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 159 = r159 from rfl, r159]
  refine ⟨fun n s h1 hn h1e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_name, h1]) hn, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h1e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl

/-- `param[arg_ty]: a=NAME b=annotation? { _PyAST_arg(a->v.Name.id, b, NULL, EXTRA) }`
(`Grammar/python.gram:377`): a `NAME` and the optional `annotation` (51) give `arg(name, b,
NULL)` spanning them (`b` `NULL` without one); no `NAME` gives `NULL` with the mark back. -/
def ParamRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (n b : Ast) (s1 s2 : PS), nameToken q = (n, s1) → n ≠ .null → callRule f 51 s1 = (b, s2) →
    s2.errorIndicator = false →
    callRule (f + 6) 49 p = (mkAt .arg_ [fieldOf n "id", b, .null] (extraLoc t s2), s2.leave)) ∧
  (∀ (s : PS), nameToken q = (.null, s) →
    callRule (f + 6) 49 p = (.null, { s with mark := p.mark }.leave))

theorem paramRule_proven : ParamRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 49 = r49 from rfl, r49]
  refine ⟨fun n b s1 s2 h1 hn h2 h2e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl

/-- `param_star_annotation[arg_ty]: a=NAME b=star_annotation { _PyAST_arg(a->v.Name.id, b, NULL,
EXTRA) }` (`Grammar/python.gram:378`): a `NAME` and a `star_annotation` (52, mandatory) give
`arg(name, b, NULL)`; no `NAME`, or no `star_annotation` after it, `NULL` with the mark back. -/
def ParamStarAnnotation : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (n b : Ast) (s1 s2 : PS), nameToken q = (n, s1) → n ≠ .null → callRule f 52 s1 = (b, s2) →
    b ≠ .null → s2.errorIndicator = false →
    callRule (f + 6) 50 p = (mkAt .arg_ [fieldOf n "id", b, .null] (extraLoc t s2), s2.leave)) ∧
  (∀ (n : Ast) (s1 s2 : PS), nameToken q = (n, s1) → n ≠ .null → callRule f 52 s1 = (.null, s2) →
    callRule (f + 6) 50 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (s : PS), nameToken q = (.null, s) →
    callRule (f + 6) 50 p = (.null, { s with mark := p.mark }.leave))

theorem paramStarAnnotation_proven : ParamStarAnnotation := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 50 = r50 from rfl, r50]
  refine ⟨fun n b s1 s2 h1 hn h2 hb h2e => ?_, fun n s1 s2 h1 hn h2 => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_name, h1]) hn, items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl

/-! ### `lambda_param_no_default` -/

/-- `a=lambda_param ','` failing from `X`, ending in `s`. -/
def LPNDFails (f : Nat) (X s : PS) : Prop :=
  callRule (f + 2) 159 X = (.null, s) ∨
  ∃ (a : Ast) (s1 : PS), callRule (f + 2) 159 X = (a, s1) ∧ a ≠ .null ∧ expectToken 12 s1 = (.null, s)

/-- `lambda_param_no_default` (`Grammar/python.gram:955-957`):
```
    | a=lambda_param ',' { a }
    | a=lambda_param &':' { a }
```
No `EXTRA`. A `lambda_param` (159) and `,` (12) give the parameter; once that fails, from the start
mark, a `lambda_param` followed by `:` (11), which is not consumed, gives it; otherwise `NULL` with
the mark back (so `lambda a b: 0` has no parameter `a`). -/
def LambdaParamNoDefault : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a : Ast) (c : Token) (s1 s2 : PS), callRule (f + 2) 159 p.enter = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 7) 156 p = (a, s2.leave)) ∧
  (∀ (s0 s1 s2 : PS) (a x : Ast), LPNDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 1) 159 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (x, s2) →
    (nonNull x = true → s2.errorIndicator = false →
      callRule (f + 7) 156 p = (a, { s2 with mark := s1.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 7) 156 p = (.null, { s2 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), LPNDFails f p.enter s0 → s0.errorIndicator = false →
    callRule (f + 1) 159 { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 7) 156 p = (.null, { s1 with mark := p.mark }.leave))

theorem lambdaParamNoDefault_proven : LambdaParamNoDefault := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 156 = r156 from rfl, r156]
  have hA : ∀ s0, LPNDFails f p.enter s0 →
      runItems (f + 4) [.call (.rule 159), .call (.tok 12)] #[] false p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, s1, h1, ha, h2⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]
  refine ⟨fun a c s1 s2 h1 ha h2 h2e => ?_, fun s0 s1 s2 a x h0 h0e h1 ha h2 => ⟨fun hx h2e => ?_,
    fun hx => ?_⟩, fun s0 s1 h0 h0e h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look (by rw [call_tok, h2]) hx, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look_fail (by rw [call_tok, h2]) (by simpa using hx)]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-! ### `slash_no_default`, `lambda_slash_no_default` -/

/-- `a=l1 '/' ','` failing from `X`, ending in `s`. -/
def SlashNDFails (f l1 : Nat) (X s : PS) : Prop :=
  callRule (f + 3) l1 X = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (f + 3) l1 X = (a, s1) ∧ a ≠ .null ∧ expectToken 17 s1 = (.null, s)) ∨
  (∃ (a : Ast) (c : Token) (s1 s2 : PS), callRule (f + 3) l1 X = (a, s1) ∧ a ≠ .null ∧
    expectToken 17 s1 = (.tok c, s2) ∧ expectToken 12 s2 = (.null, s))

/-- `slash_no_default` (`Grammar/python.gram:331-333`) and `lambda_slash_no_default`
(`Grammar/python.gram:935-937`):
```
    | a[asdl_arg_seq*]=param_no_default+ '/' ',' { a }
    | a[asdl_arg_seq*]=param_no_default+ '/' &')' { a }
```
(the lambda rule with `lambda_param_no_default+` and `&':'`). No `EXTRA`. The `+` loop (`l1`), `/`
(17) and `,` (12) give the loop's sequence; once that fails, from the start mark, the loop and `/`
followed by `lk` (`)` 8 or `:` 11, not consumed) give it; otherwise `NULL` with the mark back. -/
def SlashNoDefault (id l1 lk : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a : Ast) (c c' : Token) (s1 s2 s3 : PS), callRule (f + 3) l1 p.enter = (a, s1) → a ≠ .null →
    expectToken 17 s1 = (.tok c, s2) → expectToken 12 s2 = (.tok c', s3) →
    s3.errorIndicator = false → callRule (f + 8) id p = (a, s3.leave)) ∧
  (∀ (s0 s1 s2 s3 : PS) (a x : Ast) (c : Token), SlashNDFails f l1 p.enter s0 →
    s0.errorIndicator = false → callRule (f + 2) l1 { s0 with mark := p.mark } = (a, s1) →
    a ≠ .null → expectToken 17 s1 = (.tok c, s2) → expectToken lk s2 = (x, s3) →
    (nonNull x = true → s3.errorIndicator = false →
      callRule (f + 8) id p = (a, { s3 with mark := s2.mark }.leave)) ∧
    (nonNull x = false → callRule (f + 8) id p = (.null, { s3 with mark := p.mark }.leave))) ∧
  (∀ (s0 s1 : PS), SlashNDFails f l1 p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) l1 { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 8) id p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (s0 s1 s2 : PS) (a : Ast), SlashNDFails f l1 p.enter s0 → s0.errorIndicator = false →
    callRule (f + 2) l1 { s0 with mark := p.mark } = (a, s1) → a ≠ .null →
    expectToken 17 s1 = (.null, s2) →
    callRule (f + 8) id p = (.null, { s2 with mark := p.mark }.leave))

theorem slashNoDefault_of {id l1 lk : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule l1), .call (.tok 17), .call (.tok 12)] (some (.var 0)) 3 false false,
       Alt.mk [.call (.rule l1), .call (.tok 17), .look true (.tok lk)] (some (.var 0)) 2 false false]) :
    SlashNoDefault id l1 lk := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  have hA : ∀ s0, SlashNDFails f l1 p.enter s0 →
      runItems (f + 5) [.call (.rule l1), .call (.tok 17), .call (.tok 12)] #[] false p.enter =
        ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, s1, h1, ha, h2⟩ | ⟨a, c, s1, s2, h1, ha, h2, h3⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_tok, h3])]
  refine ⟨fun a c c' s1 s2 s3 h1 ha h2 h3 h3e => ?_,
    fun s0 s1 s2 s3 a x c h0 h0e h1 ha h2 h3 => ⟨fun hx h3e => ?_, fun hx => ?_⟩,
    fun s0 s1 h0 h0e h1 => ?_, fun s0 s1 s2 a h0 h0e h1 ha h2 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_tok, h3]) (by simp), items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h3e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_look (by rw [call_tok, h3]) hx, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_look_fail (by rw [call_tok, h3]) (by simpa using hx)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s0 h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl

/-! ### `kwds`, `lambda_kwds` -/

/-- `kwds` (`Grammar/python.gram:348-350`) and `lambda_kwds` (`Grammar/python.gram:951-953`):
```
    | invalid_kwds
    | '**' a=param_no_default { a }
```
(the lambda rule with `invalid_lambda_kwds` and `lambda_param_no_default`). No `EXTRA`. In the
second pass `invalid_kwds` (`inv`) runs first: a non-`NULL` result is the rule's, an error ends the
rule with `NULL`. Then (`InvPass`), from `X`: `**` (35) and a `param_no_default` (`pnd`) give the
parameter; no `**`, or no parameter after it, `NULL` with the mark back. -/
def Kwds (id inv pnd : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (p.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 3) inv p.enter = (v, s) →
    v ≠ .null → callRule (f + 8) id p = (v, s.leave)) ∧
  (p.callInvalidRules = true → ∀ (s : PS), callRule (f + 3) inv p.enter = (.null, s) →
    s.errorIndicator = true → callRule (f + 8) id p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPass (f + 3) inv p X →
    (∀ (a : Ast) (c : Token) (s1 s2 : PS), expectToken 35 X = (.tok c, s1) →
      callRule (f + 1) pnd s1 = (a, s2) → a ≠ .null → s2.errorIndicator = false →
      callRule (f + 8) id p = (a, s2.leave)) ∧
    (∀ (c : Token) (s1 s2 : PS), expectToken 35 X = (.tok c, s1) →
      callRule (f + 1) pnd s1 = (.null, s2) →
      callRule (f + 8) id p = (.null, { s2 with mark := p.mark }.leave)) ∧
    (∀ (s1 : PS), expectToken 35 X = (.null, s1) →
      callRule (f + 8) id p = (.null, { s1 with mark := p.mark }.leave)))

theorem kwds_of {id inv pnd : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [invAlt inv, Alt.mk [.call (.tok 35), .call (.rule pnd)] (some (.var 1)) 2 false false]) :
    Kwds id inv pnd := by
  intro f p he hl
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 6 = (f + 3) + 3 from rfl, invAlt_ok he hi h1 hv]
    rfl
  · rw [show f + 6 = (f + 3) + 3 from rfl, invAlt_err he hi rfl h1 h1e]
    rfl
  have hXe : X.errorIndicator = false := by
    rcases hX with ⟨-, rfl⟩ | ⟨-, s, -, hs, rfl⟩
    · exact he
    · exact hs
  have hXm : X.mark = p.mark := by
    rcases hX with ⟨-, rfl⟩ | ⟨-, s, -, -, rfl⟩ <;> rfl
  rw [show f + 6 = (f + 3) + 3 from rfl, invPass_alts he hX]
  refine ⟨fun a c s1 s2 h1 h2 ha h2e => ?_, fun c s1 s2 h1 h2 => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) hXe (by dsimp only; rw [items_call_null (by rw [call_tok, h1])]), alts_nil]
    rfl

/-! ### Instances -/

/-- `slash_no_default` (41): `param_no_default+` is `_loop1_29` (306), `&')'` is 8. -/
theorem slashNoDefault_proven : SlashNoDefault 41 306 8 := slashNoDefault_of rfl
/-- `lambda_slash_no_default` (152): `lambda_param_no_default+` is `_loop1_74` (351), `&':'` 11. -/
theorem lambdaSlashNoDefault_proven : SlashNoDefault 152 351 11 := slashNoDefault_of rfl
/-- `kwds` (44): `invalid_kwds` (226), `param_no_default` (45). -/
theorem kwds_proven : Kwds 44 226 45 := kwds_of rfl
/-- `lambda_kwds` (155): `invalid_lambda_kwds` (231), `lambda_param_no_default` (156). -/
theorem lambdaKwds_proven : Kwds 155 231 156 := kwds_of rfl
/-- `params: invalid_parameters | parameters` (`Grammar/python.gram:314-316`): 39, 223, 40. -/
theorem params_proven : InvOr 39 223 40 := invOr_of rfl
/-- `lambda_params: invalid_lambda_parameters | lambda_parameters`
(`Grammar/python.gram:917-919`): 150, 228, 151. -/
theorem lambdaParams_proven : InvOr 150 228 151 := invOr_of rfl
/-- `star_named_expression_sequence: invalid_starred_expression_unpacking_sequence |
star_named_expression` (`Grammar/python.gram:749-751`, new in 3.15): 117, 267, 116. -/
theorem starNamedExpressionSequence_proven : InvOr 117 267 116 := invOr_of rfl

/-- `_loop1_29` (306): `param_no_default+`. -/
theorem loop1_29_proven : Loop1Over 306 45 := loop1Over_of rfl
/-- `_loop1_74` (351): `lambda_param_no_default+`. -/
theorem loop1_74_proven : Loop1Over 351 156 := loop1Over_of rfl

end PyLean.PyGrammar.Peg
