import PyLean.PyGrammar.Peg.Rules.Targets

/-! `star_target`, `target_with_star_atom`, `del_targets`, `del_target`
(`Grammar/python.gram:1129-1176`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The end of a `(memo)` rule function whose alternatives returned `v` in state `s`. -/
abbrev memoRet (m id : Nat) (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo m (1000 + id) v s).2.leave)

/-- `star_target (memo)` (`Grammar/python.gram:1129-1132`):
```
    | '*' a=(!'*' star_target) {
        _PyAST_Starred(CHECK(expr_ty, _PyPegen_set_expr_context(p, a, Store)), Store, EXTRA) }
    | target_with_star_atom
```
At `*` (16) followed by `(!'*' star_target)` (`_tmp_101`): `Starred(a, Store)` with `a` put in the
`Store` context (`_PyPegen_set_expr_context`); without that, and at any other token,
`target_with_star_atom` from the start mark. Memoized at the start mark. -/
def StarTarget : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 196) = none →
  let t := q.tokenAt p.mark
  (t.type = 16 → ∀ (a : Ast) (s : PS), callRule (f + 1) 378 { q with mark := p.mark + 1 } = (a, s) →
    a ≠ .null → s.errorIndicator = false →
    callRule (f + 7) 196 p = memoRet p.mark 196
      (mkAt .Starred [setExprContext (opNode .Store) 100000 a, opNode .Store] (extraLoc t s)) s) ∧
  (t.type = 16 → ∀ (v : Ast) (s s2 : PS), callRule (f + 1) 378 { q with mark := p.mark + 1 } = (.null, s) →
    s.errorIndicator = false → callRule (f + 1) 197 { s with mark := p.mark } = (v, s2) → v ≠ .null →
    callRule (f + 7) 196 p = memoRet p.mark 196 v s2) ∧
  (t.type ≠ 16 → ∀ (v : Ast) (s : PS), callRule (f + 1) 197 q = (v, s) → v ≠ .null →
    callRule (f + 7) 196 p = memoRet p.mark 196 v s)

theorem starTarget_proven : StarTarget := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 196 = r196 from rfl, r196]
  have e16 : ∀ g, runCall (g + 1) (.tok 16) q = if (q.tokenAt p.mark).type = 16 then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  refine ⟨fun ht a s h1 ha hse => ?_, fun ht v s s2 h1 hse h2 hv => ?_, fun ht v s h1 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [e16, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    have hne := setExprContext_ne (c := Ast.node Ctor.Store [] none) 100000 a ha
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hse,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, Array.size_push,
      Array.size_empty, List.getD, Option.getD_some, Nat.reduceEqDiff, ↓reduceIte,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
    simp [mkAst, nonNull, hse, memoDone, memoRet, StateT.pure, pure, StateT.bind, bind, hne]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [e16, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (by rw [e16, ite_f ht])), hq,
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- `target_with_star_atom (memo)` (`Grammar/python.gram:1134-1137`):
```
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Store, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Store, EXTRA) }
    | star_atom
```
`t_primary` `.` NAME with no trailer after it (`!t_lookahead` holds) gives `Attribute(a, NAME.id,
Store)`; with a trailer after it the alternative fails, and with `t_primary` again and no `[` the
result is `star_atom` from the start mark. With no `.` after `t_primary`, `t_primary` `[` slices
`]` with no trailer after it gives `Subscript(a, slices, Store)`, and with a trailer after it again
`star_atom`. With no `t_primary`, `star_atom`. Memoized at the start mark. -/
def TargetWithStarAtom : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 197) = none →
  let t := q.tokenAt p.mark
  (∀ (a b x : Ast) (to : Token) (s1 s2 s3 s4 : PS), callRule (f + 5) 201 q = (a, s1) → a ≠ .null →
    expectToken 23 s1 = (.tok to, s2) → nameToken s2 = (b, s3) → b ≠ .null →
    callRule (f + 2) 202 s3 = (x, s4) → nonNull x = false → s4.errorIndicator = false →
    callRule (f + 10) 197 p = memoRet p.mark 197
      (mkAt .Attribute [a, fieldOf b "id", opNode .Store] (extraLoc t { s4 with mark := s3.mark }))
      { s4 with mark := s3.mark }) ∧
  (∀ (a b x a' v : Ast) (to : Token) (s1 s2 s3 s4 s5 s6 s7 : PS), callRule (f + 5) 201 q = (a, s1) →
    a ≠ .null → expectToken 23 s1 = (.tok to, s2) → nameToken s2 = (b, s3) → b ≠ .null →
    callRule (f + 2) 202 s3 = (x, s4) → nonNull x = true → s4.errorIndicator = false →
    callRule (f + 4) 201 { s4 with mark := p.mark } = (a', s5) → a' ≠ .null →
    expectToken 9 s5 = (.null, s6) → s6.errorIndicator = false →
    callRule (f + 3) 198 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 10) 197 p = memoRet p.mark 197 v s7) ∧
  (∀ (a a' sl x : Ast) (to tc : Token) (s1 s2 s3 s4 s5 s6 s7 : PS), callRule (f + 5) 201 q = (a, s1) →
    a ≠ .null → expectToken 23 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 201 { s2 with mark := p.mark } = (a', s3) → a' ≠ .null →
    expectToken 9 s3 = (.tok to, s4) → callRule (f + 2) 145 s4 = (sl, s5) → sl ≠ .null →
    expectToken 10 s5 = (.tok tc, s6) → callRule f 202 s6 = (x, s7) → s7.errorIndicator = false →
    (nonNull x = false → callRule (f + 10) 197 p = memoRet p.mark 197
      (mkAt .Subscript [a', sl, opNode .Store] (extraLoc t { s7 with mark := s6.mark }))
      { s7 with mark := s6.mark }) ∧
    (nonNull x = true → ∀ (v : Ast) (s8 : PS), callRule (f + 3) 198 { s7 with mark := p.mark } = (v, s8) →
      v ≠ .null → callRule (f + 10) 197 p = memoRet p.mark 197 v s8)) ∧
  (∀ (v : Ast) (s1 s2 s3 : PS), callRule (f + 5) 201 q = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 4) 201 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 3) 198 { s2 with mark := p.mark } = (v, s3) → v ≠ .null →
    callRule (f + 10) 197 p = memoRet p.mark 197 v s3)

theorem targetWithStarAtom_proven : TargetWithStarAtom := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 197 = r197 from rfl, r197]
  refine ⟨fun a b x to s1 s2 s3 s4 h1 ha h2 h3 hb h4 hx h4e => ?_,
    fun a b x a' v to s1 s2 s3 s4 s5 s6 s7 h1 ha h2 h3 hb h4 hx h4e h5 ha' h6 h6e h7 hv => ?_,
    fun a a' sl x to tc s1 s2 s3 s4 s5 s6 s7 h1 ha h2 h2e h3 ha' h4 h5 hsl h6 h7 h7e => ?_,
    fun v s1 s2 s3 h1 h1e h2 h2e h3 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_look (b := false) (by rw [call_rule, h4]) hx,
        items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e, memoDone, memoRet]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_look_fail (b := false) (by rw [call_rule, h4]) hx]),
      alts_fail (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h5]) ha', items_call_null (by rw [call_tok, h6])]),
      alts_ok (by rfl) (show ({ s6 with mark := p.mark } : PS).errorIndicator = false from h6e) (by
        dsimp only; rw [items_call (by rw [call_rule, h7]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · refine ⟨fun hx => ?_, fun hx v s8 h8 hv => ?_⟩
    · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
        alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_call (by rw [call_tok, h4]) (by simp),
          items_call (by rw [call_rule, h5]) hsl, items_call (by rw [call_tok, h6]) (by simp),
          items_look (b := false) (by rw [call_rule, h7]) hx, items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        Bool.or_false, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h7e, memoDone, memoRet]
    · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
        alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_call (by rw [call_tok, h4]) (by simp),
          items_call (by rw [call_rule, h5]) hsl, items_call (by rw [call_tok, h6]) (by simp),
          items_look_fail (b := false) (by rw [call_rule, h7]) hx]),
        alts_ok (by rfl) (show ({ s7 with mark := p.mark } : PS).errorIndicator = false from h7e) (by
          dsimp only; rw [items_call (by rw [call_rule, h8]) hv, items_nil]),
        altResult_none1 rfl rfl]
      rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-! ### `del_targets`, `del_target` -/

/-- `del_targets: a[asdl_expr_seq*]=','.del_target+ [','] { a }` (`Grammar/python.gram:1171`):
the `','.del_target+` gather (`_gather_103`) and an optional trailing `,`; `NULL` with the mark
back when the gather fails. -/
def DelTargets : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a o : Ast) (s s' : PS), callRule (f + 1) 380 p.enter = (a, s) → a ≠ .null →
    expectToken 12 s = (o, s') → s'.errorIndicator = false → callRule (f + 6) 203 p = (a, s'.leave)) ∧
  (∀ (s : PS), callRule (f + 1) 380 p.enter = (.null, s) →
    callRule (f + 6) 203 p = (.null, { s with mark := p.mark }.leave))

theorem delTargets_proven : DelTargets := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 203 = r203 from rfl, r203]
  refine ⟨fun a o s s' h1 ha h2 h2e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_tok, h2]) h2e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `del_target (memo)` (`Grammar/python.gram:1173-1176`):
```
    | a=t_primary '.' b=NAME !t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Del, EXTRA) }
    | a=t_primary '[' b=slices ']' !t_lookahead { _PyAST_Subscript(a, b, Del, EXTRA) }
    | del_t_atom
```
As `TargetWithStarAtom`, with `Del` for `Store` and `del_t_atom` for `star_atom`. -/
def DelTarget : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 204) = none →
  let t := q.tokenAt p.mark
  (∀ (a b x : Ast) (to : Token) (s1 s2 s3 s4 : PS), callRule (f + 5) 201 q = (a, s1) → a ≠ .null →
    expectToken 23 s1 = (.tok to, s2) → nameToken s2 = (b, s3) → b ≠ .null →
    callRule (f + 2) 202 s3 = (x, s4) → nonNull x = false → s4.errorIndicator = false →
    callRule (f + 10) 204 p = memoRet p.mark 204
      (mkAt .Attribute [a, fieldOf b "id", opNode .Del] (extraLoc t { s4 with mark := s3.mark }))
      { s4 with mark := s3.mark }) ∧
  (∀ (a b x a' v : Ast) (to : Token) (s1 s2 s3 s4 s5 s6 s7 : PS), callRule (f + 5) 201 q = (a, s1) →
    a ≠ .null → expectToken 23 s1 = (.tok to, s2) → nameToken s2 = (b, s3) → b ≠ .null →
    callRule (f + 2) 202 s3 = (x, s4) → nonNull x = true → s4.errorIndicator = false →
    callRule (f + 4) 201 { s4 with mark := p.mark } = (a', s5) → a' ≠ .null →
    expectToken 9 s5 = (.null, s6) → s6.errorIndicator = false →
    callRule (f + 3) 205 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 10) 204 p = memoRet p.mark 204 v s7) ∧
  (∀ (a a' sl x : Ast) (to tc : Token) (s1 s2 s3 s4 s5 s6 s7 : PS), callRule (f + 5) 201 q = (a, s1) →
    a ≠ .null → expectToken 23 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 201 { s2 with mark := p.mark } = (a', s3) → a' ≠ .null →
    expectToken 9 s3 = (.tok to, s4) → callRule (f + 2) 145 s4 = (sl, s5) → sl ≠ .null →
    expectToken 10 s5 = (.tok tc, s6) → callRule f 202 s6 = (x, s7) → s7.errorIndicator = false →
    (nonNull x = false → callRule (f + 10) 204 p = memoRet p.mark 204
      (mkAt .Subscript [a', sl, opNode .Del] (extraLoc t { s7 with mark := s6.mark }))
      { s7 with mark := s6.mark }) ∧
    (nonNull x = true → ∀ (v : Ast) (s8 : PS), callRule (f + 3) 205 { s7 with mark := p.mark } = (v, s8) →
      v ≠ .null → callRule (f + 10) 204 p = memoRet p.mark 204 v s8)) ∧
  (∀ (v : Ast) (s1 s2 s3 : PS), callRule (f + 5) 201 q = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 4) 201 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 3) 205 { s2 with mark := p.mark } = (v, s3) → v ≠ .null →
    callRule (f + 10) 204 p = memoRet p.mark 204 v s3)

theorem delTarget_proven : DelTarget := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 204 = r204 from rfl, r204]
  refine ⟨fun a b x to s1 s2 s3 s4 h1 ha h2 h3 hb h4 hx h4e => ?_,
    fun a b x a' v to s1 s2 s3 s4 s5 s6 s7 h1 ha h2 h3 hb h4 hx h4e h5 ha' h6 h6e h7 hv => ?_,
    fun a a' sl x to tc s1 s2 s3 s4 s5 s6 s7 h1 ha h2 h2e h3 ha' h4 h5 hsl h6 h7 h7e => ?_,
    fun v s1 s2 s3 h1 h1e h2 h2e h3 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_look (b := false) (by rw [call_rule, h4]) hx,
        items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e, memoDone, memoRet]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_look_fail (b := false) (by rw [call_rule, h4]) hx]),
      alts_fail (by rfl) (show ({ s4 with mark := p.mark } : PS).errorIndicator = false from h4e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h5]) ha', items_call_null (by rw [call_tok, h6])]),
      alts_ok (by rfl) (show ({ s6 with mark := p.mark } : PS).errorIndicator = false from h6e) (by
        dsimp only; rw [items_call (by rw [call_rule, h7]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · refine ⟨fun hx => ?_, fun hx v s8 h8 hv => ?_⟩
    · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
        alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_call (by rw [call_tok, h4]) (by simp),
          items_call (by rw [call_rule, h5]) hsl, items_call (by rw [call_tok, h6]) (by simp),
          items_look (b := false) (by rw [call_rule, h7]) hx, items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        Bool.or_false, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h7e, memoDone, memoRet]
    · rw [alts_fail (by rfl) he (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
        alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_call (by rw [call_tok, h4]) (by simp),
          items_call (by rw [call_rule, h5]) hsl, items_call (by rw [call_tok, h6]) (by simp),
          items_look_fail (b := false) (by rw [call_rule, h7]) hx]),
        alts_ok (by rfl) (show ({ s7 with mark := p.mark } : PS).errorIndicator = false from h7e) (by
          dsimp only; rw [items_call (by rw [call_rule, h8]) hv, items_nil]),
        altResult_none1 rfl rfl]
      rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl

end PyLean.PyGrammar.Peg
