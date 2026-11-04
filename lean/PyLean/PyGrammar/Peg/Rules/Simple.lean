import PyLean.PyGrammar.Peg.Rules.Base

/-! `simple_stmt`, the dispatch of simple statements (`Grammar/python.gram:121-135`). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `simple_stmt (memo)` (`Grammar/python.gram:121-135`):
```
    | assignment
    | &"type" type_alias
    | &('import' | 'from' | "lazy") import_stmt
    | e=star_expressions { _PyAST_Expr(e, EXTRA) }
    | &'return' return_stmt
    | &'raise' raise_stmt
    | &'pass' pass_stmt
    ... (del, yield, assert, break, continue, global, nonlocal, each behind its keyword)
```
At a position not yet memoized for it: `assignment` is tried first and wins when it succeeds (so
`x = 1` is never an expression statement); otherwise, past the `type` and import lookaheads,
`star_expressions` gives `Expr(e)`; only when that fails too does a keyword statement run, here
`return_stmt` behind `&'return'` and `pass_stmt` behind `&'pass'` with the alternatives between
them failing. Every result is memoized at the start mark. -/
def SimpleStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 9) = none →
  let memo (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo p.mark (1000 + 9) v s).2.leave)
  (∀ (v : Ast) (s0 : PS), callRule (f + 7) 11 q = (v, s0) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s0) ∧
  (∀ (e x : Ast) (s0 s1 s2 s3 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (x, s2) → x = .null →
    s2.errorIndicator = false →
    callRule (f + 4) 112 { s2 with mark := p.mark } = (e, s3) → e ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 12) 9 p =
      memo (mkAt .Expr [e] (extraLoc (q.tokenAt p.mark) s3)) s3) ∧
  (∀ (v : Ast) (tr : Token) (s0 s1 s2 s3 s4 s5 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 112 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    expectToken 522 { s3 with mark := p.mark } = (.tok tr, s4) →
    callRule (f + 2) 14 { s4 with mark := p.mark } = (v, s5) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s5) ∧
  (∀ (v : Ast) (tp : Token) (s0 s1 s2 s3 s4 s5 s6 s7 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 4) 112 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    expectToken 522 { s3 with mark := p.mark } = (.null, s4) → s4.errorIndicator = false →
    expectToken 632 { s4 with mark := p.mark } = (.null, s5) → s5.errorIndicator = false →
    expectToken 527 { s5 with mark := p.mark } = (.tok tp, s6) →
    callRule f 16 { s6 with mark := p.mark } = (v, s7) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s7)

theorem simpleStmt_proven : SimpleStmt := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 9 = r9 from rfl, r9]
  have nn : ∀ v : Ast, v ≠ .null → nonNull v = true := fun v hv => by
    cases v <;> simp_all [nonNull]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun v s0 h0 hv => ?_, fun e x s0 s1 s2 s3 h0 h0e h1 h1e h2 hx h2e h3 he3 h3e => ?_,
    fun v tr s0 s1 s2 s3 s4 s5 h0 h0e h1 h1e h2 h2e h3 h3e h4 h5 hv => ?_,
    fun v tp s0 s1 s2 s3 s4 s5 s6 s7 h0 h0e h1 h1e h2 h2e h3 h3e h4 h4e h5 h5e h6 h7 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h0]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hx
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) he3, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, memoDone]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h4]) rfl, items_call (by rw [call_rule, h5]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_rule, h2]) rfl]),
      alts_fail (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h4]) rfl]),
      alts_fail (by rfl) (E s4 h4e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_tok, h5]) rfl]),
      alts_ok (by rfl) (E s5 h5e) (by
        dsimp only
        rw [items_look (b := true) (by rw [call_tok, h6]) rfl, items_call (by rw [call_rule, h7]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl

/-- The keyword alternatives of `simple_stmt`, in the grammar's order (`Grammar/python.gram:125-135`):
the keyword token's type and the rule it guards: `return`, `raise`, `pass`, `del`, `yield`,
`assert`, `break`, `continue`, `global`, `nonlocal`. -/
def kwStmts : List (Nat × Nat) :=
  [(522, 14), (632, 15), (527, 16), (634, 21), (588, 22), (638, 23), (528, 17), (529, 18),
   (530, 19), (531, 20)]

/-- The positive lookaheads `&'kw'` for the keywords `tys` all fail, one after the other, each read
at mark `m` of the state the previous one left, with no error. -/
def LookFails (m : Nat) : List Nat → PS → PS → Prop
  | [], s, s' => s' = s
  | ty :: tys, s, s' => ∃ s1, expectToken ty { s with mark := m } = (.null, s1) ∧
      s1.errorIndicator = false ∧ LookFails m tys s1 s'

/-- A `&'kw' kw_stmt` alternative. -/
def kwAlt (x : Nat × Nat) : Alt :=
  { items := [.look true (.tok x.1), .call (.rule x.2)], action := none, nvars := 1,
    guardInvalid := false, extra := false }

theorem kwAlts_run (m : Nat) (st : Int × Int) : ∀ (pre : List (Nat × Nat)) (kw rid c : Nat)
    (post : List (Nat × Nat)) (s sP s4 s5 : PS) (v : Ast) (tk : Token),
    s.errorIndicator = false → LookFails m (pre.map Prod.fst) s sP →
    expectToken kw { sP with mark := m } = (.tok tk, s4) →
    callRule c rid { s4 with mark := m } = (v, s5) → v ≠ .null →
    runAlts (c + 4 + pre.length) ((pre ++ (kw, rid) :: post).map kwAlt) false m st
      { s with mark := m } = (some v, s5)
  | [], kw, rid, c, post, s, sP, s4, s5, v, tk, he, hl, h1, h2, hv => by
    simp only [LookFails, List.map_nil] at hl
    subst hl
    simp only [List.nil_append, List.map_cons, List.length_nil, Nat.add_zero]
    rw [alts_ok (by rfl) (show ({ sP with mark := m } : PS).errorIndicator = false from he) (by
      show runItems (c + 3) [.look true (.tok kw), .call (.rule rid)] #[] false _ = _
      rw [items_look (b := true) (by rw [call_tok, h1]) rfl,
        items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  | (k, r) :: pre, kw, rid, c, post, s, sP, s4, s5, v, tk, he, hl, h1, h2, hv => by
    obtain ⟨s1, hk, hk1, hl'⟩ := hl
    simp only [List.cons_append, List.map_cons, List.length_cons]
    rw [show c + 4 + (pre.length + 1) = (c + 4 + pre.length) + 1 by omega]
    rw [alts_fail (by rfl) (show ({ s with mark := m } : PS).errorIndicator = false from he) (by
      show runItems (c + 4 + pre.length) [.look true (.tok k), .call (.rule r)] #[] false _ = _
      rw [show c + 4 + pre.length = (c + 3 + pre.length) + 1 by omega,
        items_look_fail (b := true) (by
          rw [show c + 3 + pre.length = (c + 2 + pre.length) + 1 by omega, call_tok]; exact hk) rfl])]
    exact kwAlts_run m st pre kw rid c post s1 sP s4 s5 v tk hk1 hl' h1 h2 hv

/-- The rest of `simple_stmt` (`Grammar/python.gram:121-135`), at a position not yet memoized for
it: with `assignment` failing, `"type"` holding gives `type_alias`'s result; with the `type`
lookahead failing too, `&('import' | 'from' | "lazy")` (the artificial `_tmp_5`) holding gives
`import_stmt`'s, before `star_expressions` is tried (so `lazy import x` is an import); and with
`star_expressions` failing as well, the keyword alternatives are tried in the order of
`kwStmts`: for every keyword, when the lookaheads of the keywords before it fail and its own
holds, the result is the rule it guards. Every result is memoized. -/
def SimpleStmtMore : Prop := ∀ (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 9) = none →
  let memo (v : Ast) (s : PS) : Ast × PS := (v, (insertMemo p.mark (1000 + 9) v s).2.leave)
  (∀ (f : Nat) (x v : Ast) (s0 s1 s2 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (x, s1) → x ≠ .null →
    callRule (f + 5) 101 { s1 with mark := p.mark } = (v, s2) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s2) ∧
  (∀ (f : Nat) (x v : Ast) (s0 s1 s2 s3 : PS), callRule (f + 7) 11 q = (.null, s0) →
    s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (f + 5) 282 { s1 with mark := p.mark } = (x, s2) → x ≠ .null →
    callRule (f + 4) 24 { s2 with mark := p.mark } = (v, s3) → v ≠ .null →
    callRule (f + 12) 9 p = memo v s3) ∧
  (∀ (pre post : List (Nat × Nat)) (kw rid : Nat), pre ++ (kw, rid) :: post = kwStmts →
    ∀ (c : Nat) (v : Ast) (tk : Token) (s0 s1 s2 s3 sP s4 s5 : PS),
    callRule (c + pre.length + 5) 11 q = (.null, s0) → s0.errorIndicator = false →
    expectSoftKeyword [116, 121, 112, 101] { s0 with mark := p.mark } = (.null, s1) →
    s1.errorIndicator = false →
    callRule (c + pre.length + 3) 282 { s1 with mark := p.mark } = (.null, s2) →
    s2.errorIndicator = false →
    callRule (c + pre.length + 2) 112 { s2 with mark := p.mark } = (.null, s3) →
    s3.errorIndicator = false →
    LookFails p.mark (pre.map Prod.fst) s3 sP →
    expectToken kw { sP with mark := p.mark } = (.tok tk, s4) →
    callRule c rid { s4 with mark := p.mark } = (v, s5) → v ≠ .null →
    callRule (c + pre.length + 10) 9 p = memo v s5)

theorem r9_alts : r9.alts = r9.alts.take 4 ++ kwStmts.map kwAlt := rfl

theorem simpleStmtMore_proven : SimpleStmtMore := by
  intro p q h hn
  obtain ⟨he, -, -, -, -, -, -⟩ := h.facts
  have nn : ∀ v : Ast, v ≠ .null → nonNull v = true := fun v hv => by
    cases v <;> simp_all [nonNull]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  refine ⟨fun f x v s0 s1 s2 h0 h0e h1 hx h2 hv => ?_, fun f x v s0 s1 s2 s3 h0 h0e h1 h1e h2 hx h3 hv => ?_,
    fun pre post kw rid hpre c v tk s0 s1 s2 s3 sP s4 s5 h0 h0e h1 h1e h2 h2e h3 h3e hl h4 h5 hv => ?_⟩
  · rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
    simp only [show ruleOf 9 = r9 from rfl, r9]
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
        dsimp only
        rw [items_look (by rw [call_softKw, h1]) (nn x hx), items_call (by rw [call_rule, h2]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
    simp only [show ruleOf 9 = r9 from rfl, r9]
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only; rw [items_look_fail (b := true) (by rw [call_softKw, h1]) rfl]),
      alts_ok (by rfl) (E s1 h1e) (by
        dsimp only
        rw [items_look (by rw [call_rule, h2]) (nn x hx), items_call (by rw [call_rule, h3]) hv,
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [show c + pre.length + 10 = (c + pre.length + 8) + 2 by omega,
      callRule_memo_extra rfl rfl rfl rfl rfl h hn]
    simp only [show ruleOf 9 = r9 from rfl]
    rw [r9_alts, ← hpre]
    simp only [show r9.alts.take 4 = [r9.alts[0]!, r9.alts[1]!, r9.alts[2]!, r9.alts[3]!] from rfl,
      List.cons_append, List.nil_append]
    rw [show c + pre.length + 8 = (c + pre.length + 7) + 1 by omega,
      alts_fail (by rfl) he (by
        show runItems (c + pre.length + 7) [.call (.rule 11)] #[] false q = _
        rw [show c + pre.length + 7 = (c + pre.length + 6) + 1 by omega,
          items_call_null (by rw [show c + pre.length + 6 = (c + pre.length + 5) + 1 by omega,
            call_rule, h0])]),
      show c + pre.length + 7 = (c + pre.length + 6) + 1 by omega,
      alts_fail (by rfl) (E s0 h0e) (by
        show runItems (c + pre.length + 6) [.look true (.softKw [116, 121, 112, 101]), .call (.rule 101)]
          #[] false _ = _
        rw [show c + pre.length + 6 = (c + pre.length + 5) + 1 by omega,
          items_look_fail (b := true) (by
            rw [show c + pre.length + 5 = (c + pre.length + 4) + 1 by omega, call_softKw, h1]) rfl]),
      show c + pre.length + 6 = (c + pre.length + 5) + 1 by omega,
      alts_fail (by rfl) (E s1 h1e) (by
        show runItems (c + pre.length + 5) [.look true (.rule 282), .call (.rule 24)] #[] false _ = _
        rw [show c + pre.length + 5 = (c + pre.length + 4) + 1 by omega,
          items_look_fail (b := true) (by
            rw [show c + pre.length + 4 = (c + pre.length + 3) + 1 by omega, call_rule, h2]) rfl]),
      show c + pre.length + 5 = (c + pre.length + 4) + 1 by omega,
      alts_fail (by rfl) (E s2 h2e) (by
        show runItems (c + pre.length + 4) [.call (.rule 112)] #[] false _ = _
        rw [show c + pre.length + 4 = (c + pre.length + 3) + 1 by omega,
          items_call_null (by rw [show c + pre.length + 3 = (c + pre.length + 2) + 1 by omega,
            call_rule, h3])]),
      show c + pre.length + 4 = c + 4 + pre.length by omega,
      kwAlts_run p.mark _ pre kw rid c post s3 sP s4 s5 v tk h3e hl h4 h5 hv]
    rfl

end PyLean.PyGrammar.Peg
