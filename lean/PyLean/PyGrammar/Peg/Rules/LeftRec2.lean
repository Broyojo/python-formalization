import PyLean.PyGrammar.Peg.Rules.LeftRec

/-! `term` and `shift_expr` (`Grammar/python.gram:833-854`): left-recursive binary-operator rules
with an `invalid_` alternative before the operand, rule by rule (see `LeftRec.lean`). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `term`, `shift_expr` -/

/-- One round of `term_raw` (`Grammar/python.gram:847-854`):
```
    | a=term '*' b=factor { _PyAST_BinOp(a, Mult, b, EXTRA) }
    | a=term '/' b=factor { _PyAST_BinOp(a, Div, b, EXTRA) }
    | a=term '//' b=factor { _PyAST_BinOp(a, FloorDiv, b, EXTRA) }
    | a=term '%' b=factor { _PyAST_BinOp(a, Mod, b, EXTRA) }
    | a=term '@' b=factor { CHECK_VERSION(expr_ty, 5, "The '@' operator is", _PyAST_BinOp(a, MatMult, b, EXTRA)) }
    | invalid_factor
    | factor
```
As `SumStep`, with five operators tried in this order, each after the ones before it fail at
their token (the mark going back and the seed found again each time); `@` under
`CHECK_VERSION(5)`, with "The '@' operator is only supported in Python 3.5 and greater" below 5.
With no seed, or no operator after it, the round is `factor` from the start mark, in the second
pass after `invalid_factor`, whose error ends the round. -/
def TermStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1140) = some (1140, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → σ.callInvalidRules = false → ∀ (b : Ast) (s2 : PS),
    callRule f 141 σ.enter = (b, s2) → b ≠ .null → ruleBody (f + 10) 140 (ruleOf 140) σ = (b, s2.leave)) ∧
  (v = .null → σ.callInvalidRules = true → ∀ (s2 : PS), callRule (f + 1) 275 σ.enter = (.null, s2) →
    s2.errorIndicator = true → ruleBody (f + 10) 140 (ruleOf 140) σ = (.null, { s2 with mark := σ.mark }.leave)) ∧
  (v = .null → σ.callInvalidRules = true → ∀ (b : Ast) (s2 s3 : PS),
    callRule (f + 1) 275 σ.enter = (.null, s2) → s2.errorIndicator = false →
    callRule f 141 { s2 with mark := σ.mark } = (b, s3) → b ≠ .null → ruleBody (f + 10) 140 (ruleOf 140) σ = (b, s3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (y z : PS),
    expectToken 16 u = (.tok to, y) → callRule (f + 4) 141 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    ruleBody (f + 10) 140 (ruleOf 140) σ = (mkAt .BinOp [v, opNode .Mult, b] (extraLoc t z), z.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (x0 y z : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.tok to, y) → callRule (f + 3) 141 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    ruleBody (f + 10) 140 (ruleOf 140) σ = (mkAt .BinOp [v, opNode .Div, b] (extraLoc t z), z.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (x0 x1 y z : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    expectToken 47 { x1 with mark := e } = (.tok to, y) → callRule (f + 2) 141 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    ruleBody (f + 10) 140 (ruleOf 140) σ = (mkAt .BinOp [v, opNode .FloorDiv, b] (extraLoc t z), z.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (x0 x1 x2 y z : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    expectToken 47 { x1 with mark := e } = (.null, x2) → x2.errorIndicator = false →
    expectToken 24 { x2 with mark := e } = (.tok to, y) → callRule (f + 1) 141 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    ruleBody (f + 10) 140 (ruleOf 140) σ = (mkAt .BinOp [v, opNode .Mod, b] (extraLoc t z), z.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (x0 x1 x2 x3 y z : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    expectToken 47 { x1 with mark := e } = (.null, x2) → x2.errorIndicator = false →
    expectToken 24 { x2 with mark := e } = (.null, x3) → x3.errorIndicator = false →
    expectToken 49 { x3 with mark := e } = (.tok to, y) → callRule f 141 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    (5 ≤ z.featureVersion → ruleBody (f + 10) 140 (ruleOf 140) σ = (mkAt .BinOp [v, opNode .MatMult, b] (extraLoc t z), z.leave)) ∧
    (z.featureVersion < 5 → (ruleBody (f + 10) 140 (ruleOf 140) σ).1 = .null ∧ (ruleBody (f + 10) 140 (ruleOf 140) σ).2.errorIndicator = true ∧
      (ruleBody (f + 10) 140 (ruleOf 140) σ).2.tok = (raiseError0 "SyntaxError"
        "The '@' operator is only supported in Python 3.5 and greater"
        { z with errorIndicator := true }).2.tok)) ∧
  (v ≠ .null → ∀ (b : Ast) (x0 x1 x2 x3 x4 z : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    expectToken 47 { x1 with mark := e } = (.null, x2) → x2.errorIndicator = false →
    expectToken 24 { x2 with mark := e } = (.null, x3) → x3.errorIndicator = false →
    expectToken 49 { x3 with mark := e } = (.null, x4) → x4.errorIndicator = false →
    x4.callInvalidRules = false → callRule f 141 { x4 with mark := σ.mark } = (b, z) →
    b ≠ .null → ruleBody (f + 10) 140 (ruleOf 140) σ = (b, z.leave)) ∧
  (v ≠ .null → ∀ (x0 x1 x2 x3 x4 g : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    expectToken 47 { x1 with mark := e } = (.null, x2) → x2.errorIndicator = false →
    expectToken 24 { x2 with mark := e } = (.null, x3) → x3.errorIndicator = false →
    expectToken 49 { x3 with mark := e } = (.null, x4) → x4.errorIndicator = false →
    x4.callInvalidRules = true → callRule (f + 1) 275 { x4 with mark := σ.mark } = (.null, g) →
    g.errorIndicator = true → ruleBody (f + 10) 140 (ruleOf 140) σ = (.null, { g with mark := σ.mark }.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (x0 x1 x2 x3 x4 g z : PS),
    expectToken 16 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 17 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    expectToken 47 { x1 with mark := e } = (.null, x2) → x2.errorIndicator = false →
    expectToken 24 { x2 with mark := e } = (.null, x3) → x3.errorIndicator = false →
    expectToken 49 { x3 with mark := e } = (.null, x4) → x4.errorIndicator = false →
    x4.callInvalidRules = true → callRule (f + 1) 275 { x4 with mark := σ.mark } = (.null, g) →
    g.errorIndicator = false → callRule f 141 { g with mark := σ.mark } = (b, z) → b ≠ .null →
    ruleBody (f + 10) 140 (ruleOf 140) σ = (b, z.leave))

theorem termStep_proven : TermStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hci : σ.enter.callInvalidRules = σ.callInvalidRules := rfl
  have hS : Seeded 140 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 140 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 140) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  have fill : ∀ {x y : PS} {ty : Nat} {a : Ast}, expectToken ty x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_expect hx).le
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 140 = r140 from rfl, r140]
  refine ⟨fun hv hinv b s2 h2 hb => ?_,
    fun hv hinv s2 h2 h2e => ?_,
    fun hv hinv b s2 s3 h2 h2e h3 hb => ?_,
    fun hv b to y z hy hz hb hze => ?_,
    fun hv b to x0 y z k0 k0e hy hz hb hze => ?_,
    fun hv b to x0 x1 y z k0 k0e k1 k1e hy hz hb hze => ?_,
    fun hv b to x0 x1 x2 y z k0 k0e k1 k1e k2 k2e hy hz hb hze => ?_,
    fun hv b to x0 x1 x2 x3 y z k0 k0e k1 k1e k2 k2e k3 k3e hy hz hb hze => ?_,
    fun hv b x0 x1 x2 x3 x4 z k0 k0e k1 k1e k2 k2e k3 k3e k4 k4e hi hz hb => ?_,
    fun hv x0 x1 x2 x3 x4 g k0 k0e k1 k1e k2 k2e k3 k3e k4 k4e hi hg hge => ?_,
    fun hv b x0 x1 x2 x3 x4 g z k0 k0e k1 k1e k2 k2e k3 k3e k4 k4e hi hg hge hz hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by simp [hci, hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_err (by rfl) (show ({ s2 with mark := σ.mark } : PS).errorIndicator = true from h2e)]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by simp [hci, hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hze,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_ok (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hze,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    have hS1 : Seeded 140 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect k1 k1e
        (show e ≤ x0.fill from f0)
    have f1 : e ≤ x1.fill :=
      Nat.le_trans (show e ≤ ({ x0 with mark := e } : PS).fill from f0) (fill k1)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_ok (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hze,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    have hS1 : Seeded 140 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect k1 k1e
        (show e ≤ x0.fill from f0)
    have f1 : e ≤ x1.fill :=
      Nat.le_trans (show e ≤ ({ x0 with mark := e } : PS).fill from f0) (fill k1)
    have hS2 : Seeded 140 σ.mark v e { x2 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x1 with mark := e } from ⟨hS1.find, hS1.lt, hS1.level⟩).after_expect k2 k2e
        (show e ≤ x1.fill from f1)
    have f2 : e ≤ x2.fill :=
      Nat.le_trans (show e ≤ ({ x1 with mark := e } : PS).fill from f1) (fill k2)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_ok (by rfl) (E x2 k2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hze,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    have hS1 : Seeded 140 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect k1 k1e
        (show e ≤ x0.fill from f0)
    have f1 : e ≤ x1.fill :=
      Nat.le_trans (show e ≤ ({ x0 with mark := e } : PS).fill from f0) (fill k1)
    have hS2 : Seeded 140 σ.mark v e { x2 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x1 with mark := e } from ⟨hS1.find, hS1.lt, hS1.level⟩).after_expect k2 k2e
        (show e ≤ x1.fill from f1)
    have f2 : e ≤ x2.fill :=
      Nat.le_trans (show e ≤ ({ x1 with mark := e } : PS).fill from f1) (fill k2)
    have hS3 : Seeded 140 σ.mark v e { x3 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x2 with mark := e } from ⟨hS2.find, hS2.lt, hS2.level⟩).after_expect k3 k3e
        (show e ≤ x2.fill from f2)
    have f3 : e ≤ x3.fill :=
      Nat.le_trans (show e ≤ ({ x2 with mark := e } : PS).fill from f2) (fill k3)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_fail (by rfl) (E x2 k2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call_null (by rw [call_tok, k3])]),
      alts_ok (by rfl) (E x3 k3e) (by
      dsimp only
      rw [items_call (hit _ _ hS3 rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    have hn : evalA ((((#[] : Array Ast).push v).push (.tok to)).push b)
        (mkExtra ((σ.tokenAt σ.mark).lineno, (σ.tokenAt σ.mark).colOffset) (lastNonWhitespaceToken z))
        (.mk .BinOp [(.var 0), (.ctor .MatMult), (.var 2), .extra0, .extra1, .extra2, .extra3]) z =
        (mkAt .BinOp [v, opNode .MatMult, b] (extraLoc (σ.tokenAt σ.mark) z), z) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs]
      rfl
    have hnn : mkAt .BinOp [v, opNode .MatMult, b] (extraLoc (σ.tokenAt σ.mark) z) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv' => ?_, fun hv' => ?_⟩
    · rw [evalA_cv_ok (v := 5) (m := "The '@' operator is") hn hnn (by omega)]
      simp [mkAst, mkAt, nonNull, hze]
    · rw [evalA_cv_low (v := 5) (m := "The '@' operator is") hn hnn (by omega)]
      have hmsg : toString (cpsStr ("The '@' operator is".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (5 : Int) ++ toString " and greater" =
          "The '@' operator is only supported in Python 3.5 and greater" := by decide +kernel
      simp only [hmsg]
      exact cv_low_result _ rfl
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    have hS1 : Seeded 140 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect k1 k1e
        (show e ≤ x0.fill from f0)
    have f1 : e ≤ x1.fill :=
      Nat.le_trans (show e ≤ ({ x0 with mark := e } : PS).fill from f0) (fill k1)
    have hS2 : Seeded 140 σ.mark v e { x2 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x1 with mark := e } from ⟨hS1.find, hS1.lt, hS1.level⟩).after_expect k2 k2e
        (show e ≤ x1.fill from f1)
    have f2 : e ≤ x2.fill :=
      Nat.le_trans (show e ≤ ({ x1 with mark := e } : PS).fill from f1) (fill k2)
    have hS3 : Seeded 140 σ.mark v e { x3 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x2 with mark := e } from ⟨hS2.find, hS2.lt, hS2.level⟩).after_expect k3 k3e
        (show e ≤ x2.fill from f2)
    have f3 : e ≤ x3.fill :=
      Nat.le_trans (show e ≤ ({ x2 with mark := e } : PS).fill from f2) (fill k3)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_fail (by rfl) (E x2 k2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call_null (by rw [call_tok, k3])]),
      alts_fail (by rfl) (E x3 k3e) (by
      dsimp only
      rw [items_call (hit _ _ hS3 rfl) hv, items_call_null (by rw [call_tok, k4])]),
      alts_skip (by simp [hi]), alts_ok (by rfl) (E x4 k4e) (by
        dsimp only; rw [items_call (by rw [call_rule, hz]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    have hS1 : Seeded 140 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect k1 k1e
        (show e ≤ x0.fill from f0)
    have f1 : e ≤ x1.fill :=
      Nat.le_trans (show e ≤ ({ x0 with mark := e } : PS).fill from f0) (fill k1)
    have hS2 : Seeded 140 σ.mark v e { x2 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x1 with mark := e } from ⟨hS1.find, hS1.lt, hS1.level⟩).after_expect k2 k2e
        (show e ≤ x1.fill from f1)
    have f2 : e ≤ x2.fill :=
      Nat.le_trans (show e ≤ ({ x1 with mark := e } : PS).fill from f1) (fill k2)
    have hS3 : Seeded 140 σ.mark v e { x3 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x2 with mark := e } from ⟨hS2.find, hS2.lt, hS2.level⟩).after_expect k3 k3e
        (show e ≤ x2.fill from f2)
    have f3 : e ≤ x3.fill :=
      Nat.le_trans (show e ≤ ({ x2 with mark := e } : PS).fill from f2) (fill k3)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_fail (by rfl) (E x2 k2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call_null (by rw [call_tok, k3])]),
      alts_fail (by rfl) (E x3 k3e) (by
      dsimp only
      rw [items_call (hit _ _ hS3 rfl) hv, items_call_null (by rw [call_tok, k4])]),
      alts_fail (by simp [hi]) (E x4 k4e) (by dsimp only; rw [items_call_null (by rw [call_rule, hg])]),
      alts_err (by rfl) (show ({ g with mark := σ.mark } : PS).errorIndicator = true from hge)]
    rfl
  · have hSu : Seeded 140 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 140 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    have hS1 : Seeded 140 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect k1 k1e
        (show e ≤ x0.fill from f0)
    have f1 : e ≤ x1.fill :=
      Nat.le_trans (show e ≤ ({ x0 with mark := e } : PS).fill from f0) (fill k1)
    have hS2 : Seeded 140 σ.mark v e { x2 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x1 with mark := e } from ⟨hS1.find, hS1.lt, hS1.level⟩).after_expect k2 k2e
        (show e ≤ x1.fill from f1)
    have f2 : e ≤ x2.fill :=
      Nat.le_trans (show e ≤ ({ x1 with mark := e } : PS).fill from f1) (fill k2)
    have hS3 : Seeded 140 σ.mark v e { x3 with mark := σ.mark } :=
      (show Seeded 140 σ.mark v e { x2 with mark := e } from ⟨hS2.find, hS2.lt, hS2.level⟩).after_expect k3 k3e
        (show e ≤ x2.fill from f2)
    have f3 : e ≤ x3.fill :=
      Nat.le_trans (show e ≤ ({ x2 with mark := e } : PS).fill from f2) (fill k3)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_fail (by rfl) (E x2 k2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call_null (by rw [call_tok, k3])]),
      alts_fail (by rfl) (E x3 k3e) (by
      dsimp only
      rw [items_call (hit _ _ hS3 rfl) hv, items_call_null (by rw [call_tok, k4])]),
      alts_fail (by simp [hi]) (E x4 k4e) (by dsimp only; rw [items_call_null (by rw [call_rule, hg])]),
      alts_ok (by rfl) (E g hge) (by
        dsimp only; rw [items_call (by rw [call_rule, hz]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- One round of `shift_expr_raw` (`Grammar/python.gram:833-837`):
```
    | a=shift_expr '<<' b=sum { _PyAST_BinOp(a, LShift, b, EXTRA) }
    | a=shift_expr '>>' b=sum { _PyAST_BinOp(a, RShift, b, EXTRA) }
    | invalid_arithmetic
    | sum
```
As `SumStep` with `<<` then `>>` over `sum`; with no seed, or no operator after it, the round is
`sum` from the start mark, in the second pass after `invalid_arithmetic`, whose error ends the
round. -/
def ShiftExprStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1138) = some (1138, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → σ.callInvalidRules = false → ∀ (b : Ast) (s2 : PS),
    callRule f 139 σ.enter = (b, s2) → b ≠ .null → ruleBody (f + 7) 138 (ruleOf 138) σ = (b, s2.leave)) ∧
  (v = .null → σ.callInvalidRules = true → ∀ (s2 : PS), callRule (f + 1) 274 σ.enter = (.null, s2) →
    s2.errorIndicator = true → ruleBody (f + 7) 138 (ruleOf 138) σ = (.null, { s2 with mark := σ.mark }.leave)) ∧
  (v = .null → σ.callInvalidRules = true → ∀ (b : Ast) (s2 s3 : PS),
    callRule (f + 1) 274 σ.enter = (.null, s2) → s2.errorIndicator = false →
    callRule f 139 { s2 with mark := σ.mark } = (b, s3) → b ≠ .null → ruleBody (f + 7) 138 (ruleOf 138) σ = (b, s3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (y z : PS),
    expectToken 33 u = (.tok to, y) → callRule (f + 1) 139 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    ruleBody (f + 7) 138 (ruleOf 138) σ = (mkAt .BinOp [v, opNode .LShift, b] (extraLoc t z), z.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (x0 y z : PS),
    expectToken 33 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 34 { x0 with mark := e } = (.tok to, y) → callRule f 139 y = (b, z) → b ≠ .null →
    z.errorIndicator = false →
    ruleBody (f + 7) 138 (ruleOf 138) σ = (mkAt .BinOp [v, opNode .RShift, b] (extraLoc t z), z.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (x0 x1 z : PS),
    expectToken 33 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 34 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    x1.callInvalidRules = false → callRule f 139 { x1 with mark := σ.mark } = (b, z) →
    b ≠ .null → ruleBody (f + 7) 138 (ruleOf 138) σ = (b, z.leave)) ∧
  (v ≠ .null → ∀ (x0 x1 g : PS),
    expectToken 33 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 34 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    x1.callInvalidRules = true → callRule (f + 1) 274 { x1 with mark := σ.mark } = (.null, g) →
    g.errorIndicator = true → ruleBody (f + 7) 138 (ruleOf 138) σ = (.null, { g with mark := σ.mark }.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (x0 x1 g z : PS),
    expectToken 33 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 34 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    x1.callInvalidRules = true → callRule (f + 1) 274 { x1 with mark := σ.mark } = (.null, g) →
    g.errorIndicator = false → callRule f 139 { g with mark := σ.mark } = (b, z) → b ≠ .null →
    ruleBody (f + 7) 138 (ruleOf 138) σ = (b, z.leave))

theorem shiftExprStep_proven : ShiftExprStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hci : σ.enter.callInvalidRules = σ.callInvalidRules := rfl
  have hS : Seeded 138 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 138 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 138) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  have fill : ∀ {x y : PS} {ty : Nat} {a : Ast}, expectToken ty x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_expect hx).le
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 138 = r138 from rfl, r138]
  refine ⟨fun hv hinv b s2 h2 hb => ?_,
    fun hv hinv s2 h2 h2e => ?_,
    fun hv hinv b s2 s3 h2 h2e h3 hb => ?_,
    fun hv b to y z hy hz hb hze => ?_,
    fun hv b to x0 y z k0 k0e hy hz hb hze => ?_,
    fun hv b x0 x1 z k0 k0e k1 k1e hi hz hb => ?_,
    fun hv x0 x1 g k0 k0e k1 k1e hi hg hge => ?_,
    fun hv b x0 x1 g z k0 k0e k1 k1e hi hg hge hz hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by simp [hci, hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_err (by rfl) (show ({ s2 with mark := σ.mark } : PS).errorIndicator = true from h2e)]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by simp [hci, hinv]) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have hSu : Seeded 138 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hze,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hSu : Seeded 138 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 138 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_ok (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call (by rw [call_tok, hy]) (by simp),
        items_call (by rw [call_rule, hz]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hze,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hSu : Seeded 138 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 138 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_skip (by simp [hi]), alts_ok (by rfl) (E x1 k1e) (by
        dsimp only; rw [items_call (by rw [call_rule, hz]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have hSu : Seeded 138 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 138 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by simp [hi]) (E x1 k1e) (by dsimp only; rw [items_call_null (by rw [call_rule, hg])]),
      alts_err (by rfl) (show ({ g with mark := σ.mark } : PS).errorIndicator = true from hge)]
    rfl
  · have hSu : Seeded 138 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS0 : Seeded 138 σ.mark v e { x0 with mark := σ.mark } :=
      hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fill k0)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by simp [hi]) (E x1 k1e) (by dsimp only; rw [items_call_null (by rw [call_rule, hg])]),
      alts_ok (by rfl) (E g hge) (by
        dsimp only; rw [items_call (by rw [call_rule, hz]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- `term`: one round and the loop. -/
def TermRule : Prop := TermStep ∧ LeaderLoop 140
theorem termRule_proven : TermRule := ⟨termStep_proven, leaderLoop_of rfl rfl⟩

/-- `shift_expr`: one round and the loop. -/
def ShiftExprRule : Prop := ShiftExprStep ∧ LeaderLoop 138
theorem shiftExprRule_proven : ShiftExprRule := ⟨shiftExprStep_proven, leaderLoop_of rfl rfl⟩

end PyLean.PyGrammar.Peg
