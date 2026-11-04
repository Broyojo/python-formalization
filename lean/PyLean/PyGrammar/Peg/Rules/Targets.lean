import PyLean.PyGrammar.Peg.Rules.Atom

/-! `slices`, `slice` (`Grammar/python.gram:886-892`) and the assignment and `del` targets
(`Grammar/python.gram:1118-1183`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `slices`, `slice` -/

/-- `slices` (`Grammar/python.gram:886-888`):
```
    | a=slice !',' { a }
    | a[asdl_expr_seq*]=','.(slice | starred_expression)+ [','] { _PyAST_Tuple(a, Load, EXTRA) }
```
A `slice` not followed by `,` is the result; a `slice` followed by `,`, or no `slice` (and no
error), gives `Tuple(elements, Load)` of the `','.(slice | starred_expression)+` gather
(`_gather_66`) from the start mark, an optional trailing `,` included; an error in `slice` gives
`NULL`. So `a[1, 2]` and `a[1,]` subscript with a tuple, `a[1]` with the slice itself, and
`a[*b]` with a one-element tuple. -/
def Slices : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a : Ast) (s s' : PS), callRule (f + 2) 146 q = (a, s) → a ≠ .null →
    expectToken 12 s = (.null, s') → s'.errorIndicator = false →
    callRule (f + 7) 145 p = (a, { s' with mark := s.mark }.leave)) ∧
  (∀ (a xs o : Ast) (c : Token) (s s' s2 s3 : PS), callRule (f + 2) 146 q = (a, s) → a ≠ .null →
    expectToken 12 s = (.tok c, s') → callRule (f + 1) 343 { s' with mark := p.mark } = (xs, s2) →
    xs ≠ .null → expectToken 12 s2 = (o, s3) → s3.errorIndicator = false →
    callRule (f + 7) 145 p = (mkAt .Tuple [xs, opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (∀ (xs o : Ast) (s s2 s3 : PS), callRule (f + 2) 146 q = (.null, s) → s.errorIndicator = false →
    callRule (f + 1) 343 { s with mark := p.mark } = (xs, s2) →
    xs ≠ .null → expectToken 12 s2 = (o, s3) → s3.errorIndicator = false →
    callRule (f + 7) 145 p = (mkAt .Tuple [xs, opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (∀ (s : PS), callRule (f + 2) 146 q = (.null, s) → s.errorIndicator = true →
    callRule (f + 7) 145 p = (.null, { s with mark := p.mark }.leave))

theorem slices_proven : Slices := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 145 = r145 from rfl, r145]
  refine ⟨fun a s s' h1 ha h2 h2e => ?_, fun a xs o c s s' s2 s3 h1 ha h2 h3 hxs h4 h4e => ?_,
    fun xs o s s2 s3 h1 h1e h3 hxs h4 h4e => ?_, fun s h1 h1e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look (b := false) (by rw [call_tok, h2]) rfl,
        items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · have g1 := callRule_grows (f + 1) 343 { s' with mark := p.mark }
    rw [h3] at g1
    have g2 := expectToken_grows 12 s2
    rw [h4] at g2
    have hse : ({ s' with mark := p.mark } : PS).errorIndicator = false := (g1.trans g2).err_false h4e
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look_fail (b := false) (by rw [call_tok, h2]) rfl]),
      alts_ok (by rfl) hse (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) hxs, items_opt (by rw [call_tok, h4]) h4e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) hxs, items_opt (by rw [call_tok, h4]) h4e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_err (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = true from h1e)]
    rfl

theorem ei_back_call {g r : Nat} {s s' : PS} {v : Ast} (h : callRule g r s = (v, s'))
    (he : s'.errorIndicator = false) : s.errorIndicator = false := by
  have := callRule_grows g r s
  rw [h] at this
  exact this.err_false he

theorem ei_back_expect {ty : Nat} {s s' : PS} {v : Ast} (h : expectToken ty s = (v, s'))
    (he : s'.errorIndicator = false) : s.errorIndicator = false := by
  have := expectToken_grows ty s
  rw [h] at this
  exact this.err_false he

/-- `_PyPegen_set_expr_context` never turns a node into `NULL`. -/
theorem setExprContext_ne {c : Ast} : ∀ (f : Nat) (e : Ast), e ≠ .null → setExprContext c f e ≠ .null
  | 0, _, h => h
  | _ + 1, e, h => by
    unfold setExprContext
    split <;> first | exact h | simp

/-- `slice` (`Grammar/python.gram:890-892`):
```
    | a=[expression] ':' b=[expression] c=[':' d=[expression] { d }] { _PyAST_Slice(a, b, c, EXTRA) }
    | a=named_expression { a }
```
An optional `expression`, then `:`, gives `Slice(lower, upper, step)` from the two optional
`expression`s around it and the optional `':' [expression]` (`_tmp_67`) after, each possibly
`NULL`; with no `:` after the first optional `expression`, the mark goes back and the result is
`named_expression` from the start mark; an error in the first optional `expression` gives `NULL`
(`(_opt_var = expression_rule(p), !p->error_indicator)`). -/
def Slice : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a b c : Ast) (to : Token) (s1 s2 s3 s4 : PS), callRule (f + 3) 109 q = (a, s1) →
    s1.errorIndicator = false → expectToken 11 s1 = (.tok to, s2) → callRule (f + 1) 109 s2 = (b, s3) →
    s3.errorIndicator = false → callRule f 344 s3 = (c, s4) → s4.errorIndicator = false →
    callRule (f + 8) 146 p = (mkAt .Slice [a, b, c] (extraLoc t s4), s4.leave)) ∧
  (∀ (a n : Ast) (s1 s2 s3 : PS), callRule (f + 3) 109 q = (a, s1) → s1.errorIndicator = false →
    expectToken 11 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 2) 119 { s2 with mark := p.mark } = (n, s3) → n ≠ .null → s3.errorIndicator = false →
    callRule (f + 8) 146 p = (n, s3.leave)) ∧
  (∀ (a : Ast) (s1 : PS), callRule (f + 3) 109 q = (a, s1) → s1.errorIndicator = true →
    callRule (f + 8) 146 p = (.null, { s1 with mark := p.mark }.leave))

theorem slice_proven : Slice := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 146 = r146 from rfl, r146]
  refine ⟨fun a b c to s1 s2 s3 s4 h1 h1e h2 h3 h3e h4 h4e => ?_,
    fun a n s1 s2 s3 h1 h1e h2 h2e h3 hn h3e => ?_, fun a s1 h1 h1e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_rule, h1]) h1e, items_call (by rw [call_tok, h2]) (by simp),
        items_opt (by rw [call_rule, h3]) h3e, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_opt (by rw [call_rule, h1]) h1e, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hn, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h3e, Bool.or_false]
    cases n <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_opt_err (by rw [call_rule, h1]) h1e]),
      alts_err (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = true from h1e)]
    rfl

/-! ### `star_targets`, `star_target`, `target_with_star_atom` -/

/-- `star_targets` (`Grammar/python.gram:1118-1121`):
```
    | a=star_target !',' { a }
    | a=star_target b=(',' c=star_target { c })* [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Store, EXTRA) }
```
A `star_target` not followed by `,` is the result; followed by `,`, the second alternative calls
`star_target` again from the start mark, then the `(',' star_target)*` loop (`_loop0_97`) and an
optional `,`, and gives `Tuple([a] + rest, Store)`, so `a, = x` and `a, b = x` assign to tuples;
with no `star_target`, `NULL` with the mark back. -/
def StarTargets : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a : Ast) (s s' : PS), callRule (f + 3) 196 q = (a, s) → a ≠ .null →
    expectToken 12 s = (.null, s') → s'.errorIndicator = false →
    callRule (f + 8) 193 p = (a, { s' with mark := s.mark }.leave)) ∧
  (∀ (a a' b o : Ast) (c : Token) (s s' s2 s3 s4 : PS), callRule (f + 3) 196 q = (a, s) → a ≠ .null →
    expectToken 12 s = (.tok c, s') → callRule (f + 2) 196 { s' with mark := p.mark } = (a', s2) →
    a' ≠ .null → callRule (f + 1) 374 s2 = (b, s3) → b ≠ .null → expectToken 12 s3 = (o, s4) →
    s4.errorIndicator = false →
    callRule (f + 8) 193 p = (mkAt .Tuple [.seq (a' :: seqOf b), opNode .Store] (extraLoc t s4), s4.leave)) ∧
  (∀ (s s2 : PS), callRule (f + 3) 196 q = (.null, s) → s.errorIndicator = false →
    callRule (f + 2) 196 { s with mark := p.mark } = (.null, s2) →
    callRule (f + 8) 193 p = (.null, { s2 with mark := p.mark }.leave))

theorem starTargets_proven : StarTargets := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 193 = r193 from rfl, r193]
  refine ⟨fun a s s' h1 ha h2 h2e => ?_,
    fun a a' b o c s s' s2 s3 s4 h1 ha h2 h3 ha' h4 hb h5 h5e => ?_, fun s s2 h1 h1e h2 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look (b := false) (by rw [call_tok, h2]) rfl,
        items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · have hse : ({ s' with mark := p.mark } : PS).errorIndicator = false :=
      ei_back_call h3 (ei_back_call h4 (ei_back_expect h5 h5e))
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look_fail (b := false) (by rw [call_tok, h2]) rfl]),
      alts_ok (by rfl) hse (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_call (by rw [call_rule, h4]) hb,
          items_opt (by rw [call_tok, h5]) h5e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h5e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h5e]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl

end PyLean.PyGrammar.Peg
