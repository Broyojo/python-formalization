import PyLean.PyGrammar.Peg.Rules.Base

/-! `global`/`nonlocal`, `inversion`, `comparison` and `await_primary`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `global_stmt`, `nonlocal_stmt` -/

/-- `kw_stmt: 'kw' a=','.NAME+ { _PyAST_C(CHECK(..., _PyPegen_map_names_to_ids(p, a)), EXTRA) }`
(`Grammar/python.gram:203-207`): at the keyword, the comma-separated names (the artificial gather
rule `_gather_23`) become the node's identifier list, the `id` of each `Name`; if the names fail,
`NULL` with the mark back; at any other token, `NULL`. -/
def NamesStmt (id kw : Nat) (c : Ctor) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ kw → callRule (f + 6) id p = (.null, q.leave)) ∧
  (t.type = kw → ∀ (a : Ast) (s : PS), callRule f 291 { q with mark := p.mark + 1 } = (a, s) →
    (a = .null → callRule (f + 6) id p = (.null, { s with mark := p.mark }.leave)) ∧
    (a ≠ .null → s.errorIndicator = false →
      callRule (f + 6) id p =
        (mkAt c [.seq ((seqOf a).map (fieldOf · "id"))] (extraLoc t s), s.leave)))

/-- The shape of the two rules, for the proof. -/
def namesRule (name : String) (kw : Nat) (c : Ctor) : Rule where
  name := name
  kind := .normal
  memo := false
  leftRec := false
  leader := false
  extra := true
  withoutInvalid := false
  alts := [{ items := [.call (.tok kw), .call (.rule 291)],
             action := some (.mk c [.check (.call .map_names_to_ids [.var 1]), .extra0, .extra1,
               .extra2, .extra3]),
             nvars := 2, guardInvalid := false, extra := true }]

theorem namesStmt_of {id kw : Nat} {c : Ctor} {name : String} (hr : ruleOf id = namesRule name kw c)
    (hc : c.fields.length = 1) : NamesStmt id kw c := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl) (by rw [hr]; rfl)
    (by rw [hr]; rfl) h, hr]
  simp only [namesRule]
  refine ⟨fun ht => ?_, fun ht a s h1 => ⟨fun ha => ?_, fun ha hse => ?_⟩⟩
  · have e1 : runCall (f + 2) (.tok kw) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e1), hq, alts_nil]
    rfl
  · subst ha
    have e1 : runCall (f + 2) (.tok kw) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only; rw [items_call e1 (by simp), items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · have e1 : runCall (f + 2) (.tok kw) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hse,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, hc]

/-- `global_stmt` (530) builds `Global`, `nonlocal_stmt` (531) `Nonlocal`. -/
def GlobalNonlocal : Prop := NamesStmt 19 530 .Global ∧ NamesStmt 20 531 .Nonlocal

theorem globalNonlocal_proven : GlobalNonlocal :=
  ⟨namesStmt_of (name := _) rfl rfl, namesStmt_of (name := _) rfl rfl⟩

/-! ### `inversion` -/

/-- `inversion (memo)` (`Grammar/python.gram:777-779`):
```
    | 'not' a=inversion { _PyAST_UnaryOp(Not, a, EXTRA) }
    | comparison
```
At a position not yet memoized for it: at `not`, `UnaryOp(Not, a)` over `inversion` one token on
(so `not` nests and binds looser than comparisons: `not a == b` is `not (a == b)`); at any other
token `comparison`'s result. Memoized at the start mark. -/
def Inversion : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 122) = none →
  let t := q.tokenAt p.mark
  (t.type = 721 → ∀ (a : Ast) (s : PS), callRule f 122 { q with mark := p.mark + 1 } = (a, s) →
    a ≠ .null → s.errorIndicator = false →
    callRule (f + 6) 122 p =
      (mkAt .UnaryOp [opNode .Not, a] (extraLoc t s),
        (insertMemo p.mark (1000 + 122) (mkAt .UnaryOp [opNode .Not, a] (extraLoc t s)) s).2.leave)) ∧
  (t.type ≠ 721 → ∀ (v : Ast) (s : PS), callRule f 123 q = (v, s) → v ≠ .null →
    callRule (f + 6) 122 p = (v, (insertMemo p.mark (1000 + 122) v s).2.leave))

theorem inversion_proven : Inversion := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 122 = r122 from rfl, r122]
  refine ⟨fun ht a s h1 ha hse => ?_, fun ht v s h1 hv => ?_⟩
  · have e1 : runCall (f + 2) (.tok 721) q =
        (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hse,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, memoDone]
  · have e1 : runCall (f + 2) (.tok 721) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e1), hq, alts_ok (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl

/-! ### `comparison` -/

/-- `comparison` (`Grammar/python.gram:784-791`):
```
    | a=bitwise_or b=compare_op_bitwise_or_pair+ {
        _PyAST_Compare(a, CHECK(..., _PyPegen_get_cmpops(p, b)), CHECK(..., _PyPegen_get_exprs(p, b)), EXTRA) }
    | bitwise_or
```
`a op1 b1 op2 b2 ...` is one `Compare` node: the left operand, the operators of the pairs and their
right operands, in order (chained comparison, not nested); with no comparison operator after the
`bitwise_or`, the mark goes back and `bitwise_or` parsed again is the result. -/
def Comparison : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  ∀ (a : Ast) (s1 : PS), callRule (f + 1) 135 q = (a, s1) → a ≠ .null →
  (∀ (b : Ast) (s2 : PS), callRule f 340 s1 = (b, s2) → b ≠ .null → s2.errorIndicator = false →
    callRule (f + 6) 123 p =
      (mkAt .Compare [a, .seq ((seqOf b).map (recField · 0)), .seq ((seqOf b).map (recField · 1))]
        (extraLoc (q.tokenAt p.mark) s2), s2.leave)) ∧
  (∀ (a' : Ast) (s2 s3 : PS), callRule f 340 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule f 135 { s2 with mark := p.mark } = (a', s3) → a' ≠ .null →
    callRule (f + 6) 123 p = (a', s3.leave))

theorem comparison_proven : Comparison := by
  intro f p q h a s1 h1 ha
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 123 = r123 from rfl, r123]
  refine ⟨fun b s2 h2 hb h2e => ?_, fun a' s2 s3 h2 h2e h3 ha' => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h2e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) ha', items_nil]), altResult_none1 rfl rfl]
    rfl

/-! ### `await_primary` -/

/-- `await_primary (memo)` (`Grammar/python.gram:871-873`):
```
    | 'await' a=primary { CHECK_VERSION(expr_ty, 5, "Await expressions are", _PyAST_Await(a, EXTRA)) }
    | primary
```
At `await` followed by a `primary`: `Await(a)` when `feature_version` is at least 5, and with a
lower one `NULL` with `error_indicator` set; at any other token `primary`'s result. Memoized at the
start mark. The operand is a `primary`, so `await x ** 2` is `(await x) ** 2` (`power` sees
`await_primary` on the left of `**`). -/
def AwaitPrimary : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 143) = none →
  let t := q.tokenAt p.mark
  (t.type = 598 → ∀ (a : Ast) (s : PS), callRule f 144 { q with mark := p.mark + 1 } = (a, s) →
    a ≠ .null → s.errorIndicator = false → 5 ≤ s.featureVersion →
    callRule (f + 6) 143 p =
      (mkAt .Await [a] (extraLoc t s),
        (insertMemo p.mark (1000 + 143) (mkAt .Await [a] (extraLoc t s)) s).2.leave)) ∧
  (t.type = 598 → ∀ (a : Ast) (s : PS), callRule f 144 { q with mark := p.mark + 1 } = (a, s) →
    a ≠ .null → s.errorIndicator = false → s.featureVersion < 5 →
    (callRule (f + 6) 143 p).1 = .null ∧ (callRule (f + 6) 143 p).2.errorIndicator = true) ∧
  (t.type ≠ 598 → ∀ (v : Ast) (s : PS), callRule f 144 q = (v, s) → v ≠ .null →
    callRule (f + 6) 143 p = (v, (insertMemo p.mark (1000 + 143) v s).2.leave))

theorem awaitPrimary_proven : AwaitPrimary := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 143 = r143 from rfl, r143]
  have e1 : (q.tokenAt p.mark).type = 598 → runCall (f + 2) (.tok 598) q =
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := fun ht => by
    rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  refine ⟨fun ht a s h1 ha hse hv => ?_, fun ht a s h1 ha hse hv => ?_, fun ht v s h1 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (e1 ht) (by simp), items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    have h5 : ¬ ((s.featureVersion : Int) < 5) := by omega
    have hE : evalA ((#[] : Array Ast).push (.tok (q.tokenAt p.mark)) |>.push a)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s))
        (.checkVersion (.int 5) (.str "Await expressions are")
          (.mk .Await [.var 1, .extra0, .extra1, .extra2, .extra3])) s =
        (mkAt .Await [a] (extraLoc (q.tokenAt p.mark) s), s) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, mkAst]
      rw [ite_f h5]
      simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, StateT.pure, pure]
    rw [hE]
    simp [mkAst, mkAt, nonNull, memoDone, hse]
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (e1 ht) (by simp), items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    have h5 : (s.featureVersion : Int) < 5 := by omega
    have hE : evalA ((#[] : Array Ast).push (.tok (q.tokenAt p.mark)) |>.push a)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s))
        (.checkVersion (.int 5) (.str "Await expressions are")
          (.mk .Await [.var 1, .extra0, .extra1, .extra2, .extra3])) s =
        (.null, (raiseError0 "SyntaxError"
          "Await expressions are only supported in Python 3.5 and greater"
          { s with errorIndicator := true }).2) := by
      have hmsg : toString (cpsStr ("Await expressions are".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (5 : Int) ++ toString " and greater" =
          "Await expressions are only supported in Python 3.5 and greater" := by decide +kernel
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, get, getThe,
        MonadStateOf.get, StateT.get, mkAst]
      rw [ite_t h5]
      simp only [hmsg]
      rfl
    rw [hE]
    have hei := (frame_raiseError0 "SyntaxError"
      "Await expressions are only supported in Python 3.5 and greater"
      { s with errorIndicator := true }).grows.err rfl
    generalize raiseError0 "SyntaxError"
      "Await expressions are only supported in Python 3.5 and greater"
      { s with errorIndicator := true } = r at hei ⊢
    dsimp only
    split <;> simp [hei, PS.leave, memoDone, insertMemo, modify, modifyGet, MonadStateOf.modifyGet,
      StateT.modifyGet, MonadState.modifyGet] <;> rfl
  · have e0 : runCall (f + 2) (.tok 598) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null e0), hq, alts_ok (by rfl) he (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl

end PyLean.PyGrammar.Peg
