import PyLean.PyGrammar.Peg.Rules.Patterns6

/-! Expression rules (`Grammar/python.gram:724-1150`), rule by rule: `named_expression`,
`star_expression`, `star_named_expression`, `if_expression`, `group`, `lambdef`, `list`, `tuple`,
`set`, `starred_expression`, `single_target`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `named_expression` (`Grammar/python.gram:758-761`):
```
    | assignment_expression
    | invalid_named_expression
    | a=expression !':=' { a }
```
An `assignment_expression` (118) is the result; without one (no error), in the first pass (the
pass flag of the state it left), an `expression` (109) from the start mark not followed by `:=`
(53) is the result, and followed by `:=` the rule gives `NULL` with the mark back. In the second
pass `invalid_named_expression` (215) runs first: its error ends the rule, its `NULL` leads to the
same last alternative. -/
def NamedExpression : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a : Ast) (s : PS), callRule (f + 3) 118 p.enter = (a, s) → a ≠ .null →
    callRule (f + 8) 119 p = (a, s.leave)) ∧
  (∀ (e x : Ast) (s1 s2 s3 : PS), callRule (f + 3) 118 p.enter = (.null, s1) →
    s1.errorIndicator = false → s1.callInvalidRules = false →
    callRule (f + 1) 109 { s1 with mark := p.mark } = (e, s2) → e ≠ .null →
    expectToken 53 s2 = (x, s3) →
    (nonNull x = false → callRule (f + 8) 119 p = (e, { s3 with mark := s2.mark }.leave)) ∧
    (nonNull x = true → callRule (f + 8) 119 p = (.null, { s3 with mark := p.mark }.leave))) ∧
  (∀ (s1 s2 : PS), callRule (f + 3) 118 p.enter = (.null, s1) → s1.errorIndicator = false →
    s1.callInvalidRules = true → callRule (f + 2) 215 { s1 with mark := p.mark } = (.null, s2) →
    s2.errorIndicator = true → callRule (f + 8) 119 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (e x : Ast) (s1 s1' s2 s3 : PS), callRule (f + 3) 118 p.enter = (.null, s1) →
    s1.errorIndicator = false → s1.callInvalidRules = true →
    callRule (f + 2) 215 { s1 with mark := p.mark } = (.null, s1') → s1'.errorIndicator = false →
    callRule (f + 1) 109 { s1' with mark := p.mark } = (e, s2) → e ≠ .null →
    expectToken 53 s2 = (x, s3) → nonNull x = false →
    callRule (f + 8) 119 p = (e, { s3 with mark := s2.mark }.leave))

theorem namedExpression_proven : NamedExpression := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 119 = r119 from rfl, r119]
  refine ⟨fun a s h1 ha => ?_, fun e x s1 s2 s3 h1 h1e hi h2 he2 h3 => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun s1 s2 h1 h1e hi h2 h2e => ?_, fun e x s1 s1' s2 s3 h1 h1e hi h2 h2e h3 he3 h4 hx => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_skip (by simp [hi]), alts_ok (by rfl) (E s1 h1e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) he2, items_look (by rw [call_tok, h3]) hx, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_skip (by simp [hi]), alts_fail (by rfl) (E s1 h1e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) he2, items_look_fail (by rw [call_tok, h3]) (by simpa using hx)]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by simp [hi]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_err (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = true from h2e)]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by simp [hi]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s1' h2e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h3]) he3, items_look (by rw [call_tok, h4]) hx, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- `star_named_expression` (`Grammar/python.gram:745-747`):
```
    | '*' a=bitwise_or { _PyAST_Starred(a, Load, EXTRA) }
    | named_expression
```
At `*` (16), a `bitwise_or` (135) after it gives `Starred(a, Load)`; otherwise (no error), the
`named_expression` (119) from the start mark. -/
def StarNamedExpression : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 16 → ∀ (b : Ast) (s : PS), callRule (f + 1) 135 { q with mark := p.mark + 1 } = (b, s) →
    b ≠ .null → s.errorIndicator = false →
    callRule (f + 7) 116 p = (mkAt .Starred [b, opNode .Load] (extraLoc t s), s.leave)) ∧
  (t.type = 16 → ∀ (v : Ast) (s s' : PS), callRule (f + 1) 135 { q with mark := p.mark + 1 } = (.null, s) →
    s.errorIndicator = false → callRule (f + 1) 119 { s with mark := p.mark } = (v, s') → v ≠ .null →
    callRule (f + 7) 116 p = (v, s'.leave)) ∧
  (t.type ≠ 16 → ∀ (v : Ast) (s' : PS), callRule (f + 1) 119 q = (v, s') → v ≠ .null →
    callRule (f + 7) 116 p = (v, s'.leave)) ∧
  (t.type ≠ 16 → ∀ (s' : PS), callRule (f + 1) 119 q = (.null, s') →
    callRule (f + 7) 116 p = (.null, { s' with mark := p.mark }.leave))

theorem starNamedExpression_proven : StarNamedExpression := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 116 = r116 from rfl, r116]
  refine ⟨fun ht b s h1 hb h1e => ?_, fun ht v s s' h1 h1e h2 hv => ?_, fun ht v s' h1 hv => ?_,
    fun ht s' h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h1e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
      dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq,
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq,
      alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `star_expression (memo)` (`Grammar/python.gram:737-739`): as `star_named_expression`, with
`expression` (109) for `named_expression`, memoized at the start mark. -/
def StarExpression : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 113) = none →
  let t := q.tokenAt p.mark
  (t.type = 16 → ∀ (b : Ast) (s : PS), callRule (f + 1) 135 { q with mark := p.mark + 1 } = (b, s) →
    b ≠ .null → s.errorIndicator = false →
    callRule (f + 7) 113 p = memoDone p.mark 113 (some (mkAt .Starred [b, opNode .Load] (extraLoc t s)), s)) ∧
  (t.type = 16 → ∀ (v : Ast) (s s' : PS), callRule (f + 1) 135 { q with mark := p.mark + 1 } = (.null, s) →
    s.errorIndicator = false → callRule (f + 1) 109 { s with mark := p.mark } = (v, s') → v ≠ .null →
    callRule (f + 7) 113 p = memoDone p.mark 113 (some v, s')) ∧
  (t.type ≠ 16 → ∀ (v : Ast) (s' : PS), callRule (f + 1) 109 q = (v, s') → v ≠ .null →
    callRule (f + 7) 113 p = memoDone p.mark 113 (some v, s')) ∧
  (t.type ≠ 16 → ∀ (s' : PS), callRule (f + 1) 109 q = (.null, s') →
    callRule (f + 7) 113 p = memoDone p.mark 113 (some .null, { s' with mark := p.mark }))

theorem starExpression_proven : StarExpression := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 113 = r113 from rfl, r113]
  refine ⟨fun ht b s h1 hb h1e => ?_, fun ht v s s' h1 h1e h2 hv => ?_, fun ht v s' h1 hv => ?_,
    fun ht s' h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h1e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
      dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq,
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq,
      alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]

/-- `if_expression: a=disjunction 'if' b=disjunction 'else' c=expression { _PyAST_IfExp(b, a, c,
EXTRA) }` (`Grammar/python.gram:724-726`): the condition is the middle `disjunction` (120), the
first is the body, the `expression` (109) after `else` (704) the orelse; without the first
`disjunction`, the `if` (700) or the `else`, `NULL` with the mark back. -/
def IfExpression : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a b c : Ast) (ti te : Token) (s1 s2 s3 s4 s5 : PS), callRule (f + 4) 120 q = (a, s1) →
    a ≠ .null → expectToken 700 s1 = (.tok ti, s2) → callRule (f + 2) 120 s2 = (b, s3) → b ≠ .null →
    expectToken 704 s3 = (.tok te, s4) → callRule f 109 s4 = (c, s5) → c ≠ .null →
    s5.errorIndicator = false →
    callRule (f + 9) 110 p = (mkAt .IfExp [b, a, c] (extraLoc t s5), s5.leave)) ∧
  (∀ (s1 : PS), callRule (f + 4) 120 q = (.null, s1) →
    callRule (f + 9) 110 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (a : Ast) (s1 s2 : PS), callRule (f + 4) 120 q = (a, s1) → a ≠ .null →
    expectToken 700 s1 = (.null, s2) → callRule (f + 9) 110 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (a b : Ast) (ti : Token) (s1 s2 s3 s4 : PS), callRule (f + 4) 120 q = (a, s1) → a ≠ .null →
    expectToken 700 s1 = (.tok ti, s2) → callRule (f + 2) 120 s2 = (b, s3) → b ≠ .null →
    expectToken 704 s3 = (.null, s4) → callRule (f + 9) 110 p = (.null, { s4 with mark := p.mark }.leave))

theorem ifExpression_proven : IfExpression := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 110 = r110 from rfl, r110]
  refine ⟨fun a b c ti te s1 s2 s3 s4 s5 h1 ha h2 h3 hb h4 h5 hc h5e => ?_, fun s1 h1 => ?_,
    fun a s1 s2 h1 ha h2 => ?_, fun a b ti s1 s2 s3 s4 h1 ha h2 h3 hb h4 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) hc, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h5e]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_call_null (by rw [call_tok, h4])]), alts_nil]
    rfl

/-- `_tmp_71: yield_expr | named_expression`, the inside of a `group`. -/
def Tmp71 : Prop := ∀ (g : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (g + 6) 348 p =
    let a := choiceRes g p.mark [111, 119] p.enter
    (a.1.getD .null, a.2.leave)

theorem tmp71_proven : Tmp71 := by
  intro g p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  have := choice_run g p.mark (0, 0) [111, 119] p.enter
  simp only [List.length, List.map, choiceAlt] at this
  simp only [show ruleOf 348 = r348 from rfl, r348]
  rw [← this]

/-- The first alternative `'(' a=(yield_expr | named_expression) ')'` of `group` fails, ending in
`s`: at a token other than `(` (7) (then `s = q`), with `_tmp_71` (348) `NULL` after `(`, or with
no `)` (8) after it. -/
def GroupA1Fails (f : Nat) (p q s : PS) : Prop :=
  ((q.tokenAt p.mark).type ≠ 7 ∧ s = q) ∨
  ((q.tokenAt p.mark).type = 7 ∧ callRule (f + 1) 348 { q with mark := p.mark + 1 } = (.null, s)) ∨
  ((q.tokenAt p.mark).type = 7 ∧ ∃ (v : Ast) (s1 : PS),
    callRule (f + 1) 348 { q with mark := p.mark + 1 } = (v, s1) ∧ v ≠ .null ∧
    expectToken 8 s1 = (.null, s))

/-- `group` (`Grammar/python.gram:906-909`):
```
    | '(' a=(yield_expr | named_expression) ')' { a }
    | invalid_group
```
No `EXTRA`. At `(` (7), the inner `yield_expr | named_expression` (`_tmp_71`, 348) and `)` (8) give
the inner expression itself (parentheses leave no node). Once that alternative fails
(`GroupA1Fails`, ending in `s`): in the first pass (`s.callInvalidRules = false`) `NULL` with the
mark back; in the second, an error already set ends the rule with `NULL`, and otherwise
`invalid_group` (236) runs from the start mark and its result is the rule's (`NULL` with the mark
back when it gives `NULL`, which is what it gives after raising for `(*a)` and `(**not a)`; in
3.15 `(**a)` raises earlier, in `tuple`'s `star_named_expression_sequence`). -/
def Group : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 7 → ∀ (v : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 1) 348 { q with mark := p.mark + 1 } = (v, s1) → v ≠ .null →
    expectToken 8 s1 = (.tok c, s2) → s2.errorIndicator = false → callRule (f + 7) 148 p = (v, s2.leave)) ∧
  (∀ (s : PS), GroupA1Fails f p q s → s.callInvalidRules = false →
    callRule (f + 7) 148 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (s : PS), GroupA1Fails f p q s → s.callInvalidRules = true → s.errorIndicator = true →
    callRule (f + 7) 148 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (s s' : PS) (v : Ast), GroupA1Fails f p q s → s.callInvalidRules = true →
    s.errorIndicator = false → callRule (f + 1) 236 { s with mark := p.mark } = (v, s') → v ≠ .null →
    callRule (f + 7) 148 p = (v, s'.leave)) ∧
  (∀ (s s' : PS), GroupA1Fails f p q s → s.callInvalidRules = true →
    s.errorIndicator = false → callRule (f + 1) 236 { s with mark := p.mark } = (.null, s') →
    callRule (f + 7) 148 p = (.null, { s' with mark := p.mark }.leave))

theorem group_proven : Group := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 148 = r148 from rfl, r148]
  have hA : ∀ s, GroupA1Fails f p q s →
      runItems (f + 4) [.call (.tok 7), .call (.rule 348), .call (.tok 8)] #[] false p.enter =
        ((none, false), s) := by
    intro s hs
    rcases hs with ⟨ht, rfl⟩ | ⟨ht, h1⟩ | ⟨ht, v, s1, h1, hv, h2⟩
    · rw [items_call_null (by rw [call_tok, expect_entered h, ite_f ht])]
    · rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) hv, items_call_null (by rw [call_tok, h2])]
  refine ⟨fun ht v c s1 s2 h1 hv h2 h2e => ?_, fun s hs hi => ?_, fun s hs hi hse => ?_,
    fun s s' v hs hi hse h1 hv => ?_, fun s s' hs hi hse h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases v <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (hA s hs), alts_skip (by simp [hi]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA s hs),
      alts_err (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = true from hse)]
    rfl
  · rw [alts_fail (by rfl) he' (hA s hs),
      alts_ok (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
        (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (hA s hs),
      alts_fail (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `lambdef` (`Grammar/python.gram:913-915`):
```
    | 'lambda' a=[lambda_params] ':' b=expression {
        _PyAST_Lambda((a) ? a : CHECK(arguments_ty, _PyPegen_empty_arguments(p)), b, EXTRA) }
```
At `lambda` (622), the optional `lambda_params` (150), `:` (11) and an `expression` (109) give
`Lambda(params, body)`, the parameters `_PyPegen_empty_arguments` when there are none
(`lambda: 0`); at another token, or without `:` or the body, `NULL` with the mark back. -/
def Lambdef : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 622 → ∀ (a b : Ast) (c : Token) (s1 s2 s3 : PS),
    callRule (f + 2) 150 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 11 s1 = (.tok c, s2) → callRule f 109 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 8) 149 p =
      (mkAt .Lambda [if truth a then a else makeArguments .null .null .null .null .null, b]
        (extraLoc t s3), s3.leave)) ∧
  (t.type = 622 → ∀ (a : Ast) (s1 s2 : PS), callRule (f + 2) 150 { q with mark := p.mark + 1 } = (a, s1) →
    s1.errorIndicator = false → expectToken 11 s1 = (.null, s2) →
    callRule (f + 8) 149 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (t.type ≠ 622 → callRule (f + 8) 149 p = (.null, q.leave))

theorem lambdef_proven : Lambdef := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 149 = r149 from rfl, r149]
  refine ⟨fun ht a b c s1 s2 s3 h1 h1e h2 h3 hb h3e => ?_, fun ht a s1 s2 h1 h1e h2 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) hb,
        items_nil]), altResult_extra rfl rfl]
    cases hta : truth a <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hta,
        mkAt, extraLoc, locArgs, callHelper, ↓reduceIte, Bool.false_eq_true] <;>
      simp [mkAst, nonNull, hta, h3e, StateT.pure, StateT.bind, pure, bind, makeArguments]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq, alts_nil]
    rfl

/-- `list: '[' a=[star_named_expressions_sequence] ']' { _PyAST_List(a, Load, EXTRA) }`
(`Grammar/python.gram:1016-1017`, 3.15): at `[` (9) the optional `star_named_expressions_sequence`
(115) and `]` (10) give `List(a, Load)` (`[]` empty); at another token, or without `]`, `NULL` with
the mark back. -/
def ListRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 9 → ∀ (a : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 1) 115 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 10 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 7) 174 p = (mkAt .List [a, opNode .Load] (extraLoc t s2), s2.leave)) ∧
  (t.type = 9 → ∀ (a : Ast) (s1 s2 : PS),
    callRule (f + 1) 115 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 10 s1 = (.null, s2) → callRule (f + 7) 174 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (t.type ≠ 9 → callRule (f + 7) 174 p = (.null, q.leave))

/-- `tuple: '(' a=[y=star_named_expression_sequence ',' z=[star_named_expressions_sequence] {
_PyPegen_seq_insert_in_front(p, y, z) } ] ')' { _PyAST_Tuple(a, Load, EXTRA) }`
(`Grammar/python.gram:1019-1021`, 3.15): at `(` the optional group (`_tmp_84`, 361) and `)` give
`Tuple(a, Load)` (so `()` is empty and `(a,)` has one element); at another token, or without `)`,
`NULL` with the mark back. -/
def TupleRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 7 → ∀ (a : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 1) 361 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 8 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 7) 175 p = (mkAt .Tuple [a, opNode .Load] (extraLoc t s2), s2.leave)) ∧
  (t.type = 7 → ∀ (a : Ast) (s1 s2 : PS),
    callRule (f + 1) 361 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 8 s1 = (.null, s2) → callRule (f + 7) 175 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (t.type ≠ 7 → callRule (f + 7) 175 p = (.null, q.leave))

/-- `set: '{' a=star_named_expressions_sequence '}' { _PyAST_Set(a, EXTRA) }`
(`Grammar/python.gram:1023`, 3.15): at `{` (25) the (mandatory) `star_named_expressions_sequence`
(115) and `}`
(26) give `Set(a)` (so `{}` is not a set); at another token, without elements or without `}`,
`NULL` with the mark back. -/
def SetRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 25 → ∀ (a : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 1) 115 { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    expectToken 26 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 7) 176 p = (mkAt .Set [a] (extraLoc t s2), s2.leave)) ∧
  (t.type = 25 → ∀ (s1 : PS), callRule (f + 1) 115 { q with mark := p.mark + 1 } = (.null, s1) →
    callRule (f + 7) 176 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (t.type ≠ 25 → callRule (f + 7) 176 p = (.null, q.leave))

theorem listRule_proven : ListRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 174 = r174 from rfl, r174]
  refine ⟨fun ht a c s1 s2 h1 h1e h2 h2e => ?_, fun ht a s1 s2 h1 h1e h2 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call (by rw [call_tok, h2]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq, alts_nil]
    rfl

theorem tupleRule_proven : TupleRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 175 = r175 from rfl, r175]
  refine ⟨fun ht a c s1 s2 h1 h1e h2 h2e => ?_, fun ht a s1 s2 h1 h1e h2 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call (by rw [call_tok, h2]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq, alts_nil]
    rfl

theorem setRule_proven : SetRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 176 = r176 from rfl, r176]
  refine ⟨fun ht a c s1 s2 h1 ha h2 h2e => ?_, fun ht s1 h1 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_tok, h2]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq, alts_nil]
    rfl

/-- `_tmp_84: y=star_named_expression_sequence ',' z=[star_named_expressions_sequence] {
_PyPegen_seq_insert_in_front(p, y, z) }`, the inside of a `tuple`: a first element
(`star_named_expression_sequence`, 117) and `,` (12), then the optional rest
(`star_named_expressions_sequence`, 115), as one sequence; without the first element or the `,`,
`NULL` with the mark back. -/
def Tmp84 : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (y z : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 117 p.enter = (y, s1) → y ≠ .null →
    expectToken 12 s1 = (.tok c, s2) → callRule f 115 s2 = (z, s3) → s3.errorIndicator = false →
    callRule (f + 7) 361 p = (.seq (y :: seqOf z), s3.leave)) ∧
  (∀ (s1 : PS), callRule (f + 2) 117 p.enter = (.null, s1) →
    callRule (f + 7) 361 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (y : Ast) (s1 s2 : PS), callRule (f + 2) 117 p.enter = (y, s1) → y ≠ .null →
    expectToken 12 s1 = (.null, s2) → callRule (f + 7) 361 p = (.null, { s2 with mark := p.mark }.leave))

theorem tmp84_proven : Tmp84 := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 361 = r361 from rfl, r361]
  refine ⟨fun y z c s1 s2 s3 h1 hy h2 h3 h3e => ?_, fun s1 h1 => ?_, fun y s1 s2 h1 hy h2 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hy, items_call (by rw [call_tok, h2]) (by simp),
        items_opt (by rw [call_rule, h3]) h3e, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hy, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl

def TupleRuleFull : Prop := TupleRule ∧ Tmp84
theorem tupleRuleFull_proven : TupleRuleFull := ⟨tupleRule_proven, tmp84_proven⟩

def GroupRule : Prop := Group ∧ Tmp71
theorem groupRule_proven : GroupRule := ⟨group_proven, tmp71_proven⟩

/-- `assignment_expression` (`Grammar/python.gram:753-756`):
```
    | a=NAME ':=' ~ b=expression {
        CHECK_VERSION(expr_ty, 8, "Assignment expressions are",
        _PyAST_NamedExpr(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), b, EXTRA)) }
```
A `NAME`, `:=` (53), the cut, and an `expression` (109) give `NamedExpr(a in Store context, b)`
with `feature_version >= 8`, and below 8 raise "Assignment expressions are only supported in
Python 3.8 and greater"; past the cut, a missing `expression` ends the rule with `NULL` (no other
alternative is tried); without the `NAME` or the `:=`, `NULL` with the mark back. -/
def AssignmentExpression : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (n b : Ast) (c : Token) (s1 s2 s3 : PS), nameToken q = (n, s1) → n ≠ .null →
    expectToken 53 s1 = (.tok c, s2) → callRule f 109 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false →
    (8 ≤ s3.featureVersion → callRule (f + 8) 118 p =
      (mkAt .NamedExpr [setExprContext (opNode .Store) 100000 n, b] (extraLoc t s3), s3.leave)) ∧
    (s3.featureVersion < 8 →
      (callRule (f + 8) 118 p).1 = .null ∧ (callRule (f + 8) 118 p).2.errorIndicator = true ∧
      (callRule (f + 8) 118 p).2.tok = (raiseError0 "SyntaxError"
        "Assignment expressions are only supported in Python 3.8 and greater"
        { s3 with errorIndicator := true }).2.tok)) ∧
  (∀ (n : Ast) (c : Token) (s1 s2 s3 : PS), nameToken q = (n, s1) → n ≠ .null →
    expectToken 53 s1 = (.tok c, s2) → callRule f 109 s2 = (.null, s3) →
    callRule (f + 8) 118 p = (.null, { s3 with mark := p.mark }.leave)) ∧
  (∀ (n : Ast) (s1 s2 : PS), nameToken q = (n, s1) → n ≠ .null → expectToken 53 s1 = (.null, s2) →
    callRule (f + 8) 118 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (s1 : PS), nameToken q = (.null, s1) →
    callRule (f + 8) 118 p = (.null, { s1 with mark := p.mark }.leave))

theorem assignmentExpression_proven : AssignmentExpression := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 118 = r118 from rfl, r118]
  refine ⟨fun n b c s1 s2 s3 h1 hn h2 h3 hb h3e => ?_, fun n c s1 s2 s3 h1 hn h2 h3 => ?_,
    fun n s1 s2 h1 hn h2 => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
        items_cut, items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    have hne : setExprContext (Ast.node .Store [] none) 100000 n ≠ .null := by
      intro h0
      have := setExprContext_nonNull (Ast.node .Store [] none) 100000 n hn
      rw [h0] at this
      simp [nonNull] at this
    have g0 : ((((#[] : Array Ast).push n).push (.tok c)).push (.int 1) |>.push b).getD 0 .null = n := rfl
    have g3 : ((((#[] : Array Ast).push n).push (.tok c)).push (.int 1) |>.push b).getD 3 .null = b := rfl
    have l0 : [n, Ast.node Ctor.Store [] none].getD 0 Ast.null = n := rfl
    have l1 : [n, Ast.node Ctor.Store [] none].getD 1 Ast.null = Ast.node Ctor.Store [] none := rfl
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · have h8 : ¬ ((s3.featureVersion : Int) < 8) := by omega
      have hE : evalA (((((#[] : Array Ast).push n).push (.tok c)).push (.int 1)).push b)
          (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s3))
          (.checkVersion (.int 8) (.str "Assignment expressions are")
            (.mk .NamedExpr [.check (.call .set_expr_context [.var 0, .ctor .Store]), .var 3, .extra0,
              .extra1, .extra2, .extra3])) s3 =
          (mkAt .NamedExpr [setExprContext (opNode .Store) 100000 n, b]
            (extraLoc (q.tokenAt p.mark) s3), s3) := by
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
          MonadStateOf.get, mkAst, callHelper, g0, g3, l0, l1, opNode]
        revert hne
        generalize setExprContext (Ast.node .Store [] none) 100000 n = X
        intro hne
        cases X with
        | null => exact absurd rfl hne
        | _ => simp [h8, StateT.get, mkAst, mkAt, extraLoc, locArgs, mkExtra, StateT.pure, pure]
      rw [hE]
      simp [mkAst, mkAt, nonNull, h3e]
    · have h8 : (s3.featureVersion : Int) < 8 := by omega
      have hE : evalA (((((#[] : Array Ast).push n).push (.tok c)).push (.int 1)).push b)
          (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s3))
          (.checkVersion (.int 8) (.str "Assignment expressions are")
            (.mk .NamedExpr [.check (.call .set_expr_context [.var 0, .ctor .Store]), .var 3, .extra0,
              .extra1, .extra2, .extra3])) s3 =
          (.null, (raiseError0 "SyntaxError"
            "Assignment expressions are only supported in Python 3.8 and greater"
            { s3 with errorIndicator := true }).2) := by
        have hmsg : toString (cpsStr ("Assignment expressions are".toList.map Char.toNat)) ++
            toString " only supported in Python 3." ++ toString (8 : Int) ++ toString " and greater" =
            "Assignment expressions are only supported in Python 3.8 and greater" := by decide +kernel
        simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
          MonadStateOf.get, mkAst, callHelper, g0, g3, l0, l1]
        revert hne
        generalize setExprContext (Ast.node .Store [] none) 100000 n = X
        intro hne
        cases X with
        | null => exact absurd rfl hne
        | _ =>
          simp only [StateT.get, pure]
          simp only [h8, ↓reduceIte, hmsg]
          rfl
      rw [hE]
      have hei := (frame_raiseError0 "SyntaxError"
        "Assignment expressions are only supported in Python 3.8 and greater"
        { s3 with errorIndicator := true }).grows.err rfl
      generalize raiseError0 "SyntaxError" "Assignment expressions are only supported in Python 3.8 and greater"
        { s3 with errorIndicator := true } = r at hei ⊢
      dsimp only
      split <;> simp [hei, PS.leave]
  · rw [alts_cut (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
        items_cut, items_call_null (by rw [call_rule, h3])])]
    rfl
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl

/-- `single_target` (`Grammar/python.gram:1145-1148`):
```
    | single_subscript_attribute_target
    | a=NAME { _PyPegen_set_expr_context(p, a, Store) }
    | '(' a=single_target ')' { a }
```
No `EXTRA`. A `single_subscript_attribute_target` (200) is the result; without one (no error), a
`NAME` from the start mark in `Store` context; without that, `(` (7), an inner `single_target` and
`)` (8) give the inner target (so `(x) += 1` assigns to `x`); otherwise `NULL` with the mark back. -/
def SingleTarget : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule (f + 4) 200 p.enter = (v, s) → v ≠ .null →
    callRule (f + 9) 199 p = (v, s.leave)) ∧
  (∀ (n : Ast) (s s' : PS), callRule (f + 4) 200 p.enter = (.null, s) → s.errorIndicator = false →
    nameToken { s with mark := p.mark } = (n, s') → n ≠ .null → s'.errorIndicator = false →
    callRule (f + 9) 199 p = (setExprContext (opNode .Store) 100000 n, s'.leave)) ∧
  (∀ (v : Ast) (o c : Token) (s s' s2 s3 s4 : PS), callRule (f + 4) 200 p.enter = (.null, s) →
    s.errorIndicator = false → nameToken { s with mark := p.mark } = (.null, s') →
    s'.errorIndicator = false → expectToken 7 { s' with mark := p.mark } = (.tok o, s2) →
    callRule (f + 1) 199 s2 = (v, s3) → v ≠ .null → expectToken 8 s3 = (.tok c, s4) →
    s4.errorIndicator = false → callRule (f + 9) 199 p = (v, s4.leave)) ∧
  (∀ (s s' s2 : PS), callRule (f + 4) 200 p.enter = (.null, s) →
    s.errorIndicator = false → nameToken { s with mark := p.mark } = (.null, s') →
    s'.errorIndicator = false → expectToken 7 { s' with mark := p.mark } = (.null, s2) →
    callRule (f + 9) 199 p = (.null, { s2 with mark := p.mark }.leave))

theorem singleTarget_proven : SingleTarget := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 199 = r199 from rfl, r199]
  refine ⟨fun v s h1 hv => ?_, fun n s s' h1 h1e h2 hn h2e => ?_,
    fun v o c s s' s2 s3 s4 h1 h1e h2 h2e h3 h4 hv h5 h5e => ?_, fun s s' s2 h1 h1e h2 h2e h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s h1e) (by dsimp only; rw [items_call (by rw [call_name, h2]) hn, items_nil]),
      altResult_plain rfl rfl]
    have hnn := setExprContext_nonNull (opNode .Store) 100000 n hn
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [hnn, h2e, opNode]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (E s h1e) (by dsimp only; rw [items_call_null (by rw [call_name, h2])]),
      alts_ok (by rfl) (E s' h2e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hv,
        items_call (by rw [call_tok, h5]) (by simp), items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h5e, Bool.or_false]
    cases v <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (E s h1e) (by dsimp only; rw [items_call_null (by rw [call_name, h2])]),
      alts_fail (by rfl) (E s' h2e) (by dsimp only; rw [items_call_null (by rw [call_tok, h3])]),
      alts_nil]
    rfl

end PyLean.PyGrammar.Peg
