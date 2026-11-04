import PyLean.PyGrammar.Peg.Rules.Primary

/-! `t_primary` and `t_lookahead` (`Grammar/python.gram:1154-1166`): the primaries in front of an
assignment, `del` or `for` target's last `.name` or `[slice]`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem tg_name {s s' : PS} {v : Ast} (h : nameToken s = (v, s')) : TokGrows s s' := by
  have := (spec_name (fun _ => default) s).grows.toks
  rwa [h] at this

theorem PS.enter_leave (p : PS) : p.enter.leave = p := by
  cases p
  simp [PS.enter, PS.leave]

/-! ### `t_lookahead` -/

/-- `t_lookahead: '(' | '[' | '.'` (`Grammar/python.gram:1166`), from a state whose token under the
mark is read: that token when it is `(`, `[` or `.` (7, 9, 23), with the mark past it; `NULL` with
the state unchanged at any other token. -/
def TLookahead : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  p.mark < p.fill →
  let t := p.tokenAt p.mark
  ((t.type = 7 ∨ t.type = 9 ∨ t.type = 23) →
    callRule (f + 7) 202 p = (.tok t, { p with mark := p.mark + 1 })) ∧
  (t.type ≠ 7 → t.type ≠ 9 → t.type ≠ 23 → callRule (f + 7) 202 p = (.null, p))

theorem tLookahead_proven : TLookahead := by
  intro f p he hl hlt
  have he' : p.enter.errorIndicator = false := he
  have hlt' : p.enter.mark < p.enter.fill := hlt
  have ex : ∀ ty, expectToken ty p.enter = if (p.tokenAt p.mark).type = ty then
      (.tok (p.tokenAt p.mark), { p.enter with mark := p.mark + 1 }) else (.null, p.enter) := by
    intro ty
    rw [expectToken_at ty p.enter hlt']
    rfl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 202 = r202 from rfl, r202]
  have hp : ({ p.enter with mark := p.mark } : PS) = p.enter := rfl
  refine ⟨fun ht => ?_, fun h7 h9 h23 => ?_⟩
  · rcases ht with h | h | h
    · rw [alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_tok, ex, ite_t h]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      exact congrArg _ (enter_leave_mark p _)
    · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, ex, ite_f (by omega)])]), hp,
        alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_tok, ex, ite_t h]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      exact congrArg _ (enter_leave_mark p _)
    · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, ex, ite_f (by omega)])]), hp,
        alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, ex, ite_f (by omega)])]), hp,
        alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_tok, ex, ite_t h]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      exact congrArg _ (enter_leave_mark p _)
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, ex, ite_f h7])]), hp,
      alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, ex, ite_f h9])]), hp,
      alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_tok, ex, ite_f h23])]), hp,
      alts_nil]
    exact congrArg _ (PS.enter_leave p)

/-! ### `t_primary` -/

/-- One round of `t_primary_raw` (`Grammar/python.gram:1154-1164`):
```
    | a=t_primary '.' b=NAME &t_lookahead { _PyAST_Attribute(a, b->v.Name.id, Load, EXTRA) }
    | a=t_primary '[' b=slices ']' &t_lookahead { _PyAST_Subscript(a, b, Load, EXTRA) }
    | a=t_primary b=genexp &t_lookahead {
        _PyAST_Call(a, CHECK(asdl_expr_seq*, (asdl_expr_seq*)_PyPegen_singleton_seq(p, b)), NULL, EXTRA) }
    | a=t_primary '(' b=[arguments] ')' &t_lookahead {
        _PyAST_Call(a, (b) ? ((expr_ty) b)->v.Call.args : NULL, (b) ? ((expr_ty) b)->v.Call.keywords : NULL, EXTRA) }
    | a=atom &t_lookahead { a }
```
As `PrimaryStep`, but every alternative ends with the positive lookahead `&t_lookahead`, so a
trailer is taken only when another trailer (`(`, `[` or `.`) follows it, and the order is `.`,
`[`, `genexp`, `(` (not `primary`'s `.`, `genexp`, `(`, `[`):
* no seed: `atom` followed by a lookahead that holds is the round, and with the lookahead failing
  the round is `NULL` with the mark back;
* a seed and `.` NAME, `[` slices `]`, `genexp` or `(` [arguments] `)` with the lookahead holding
  after it: `Attribute`, `Subscript`, `Call` with one generator, `Call` with the arguments, all
  `Load`;
* a seed and `.` NAME with the lookahead failing (`a.b = 1`: `=` after `b`): that alternative fails,
  the later trailers fail at their first token, and the round is `atom` from the start mark again
  (which does not grow, so the loop keeps the seed `a` and `target_with_star_atom` takes `.b`);
* a seed and no trailer: `atom &t_lookahead` from the start mark, `NULL` when the lookahead fails.
Hypotheses: as `PrimaryStep`; the state a lookahead or `genexp` call leaves keeps the seed
(`SeedKept`) where a later alternative calls `t_primary` again; no error after the lookahead where a
node is built. -/
def TPrimaryStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1201) = some (1201, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → ∀ (b x : Ast) (s2 s3 : PS), callRule (f + 3) 147 σ.enter = (b, s2) → b ≠ .null →
    callRule (f + 2) 202 s2 = (x, s3) → nonNull x = true → s3.errorIndicator = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ = (b, { s3 with mark := s2.mark }.leave)) ∧
  (v = .null → ∀ (b x : Ast) (s2 s3 : PS), callRule (f + 3) 147 σ.enter = (b, s2) → b ≠ .null →
    callRule (f + 2) 202 s2 = (x, s3) → nonNull x = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ = (.null, { s3 with mark := σ.mark }.leave)) ∧
  (v ≠ .null → ∀ (b x : Ast) (to : Token) (s2 s3 s4 : PS), expectToken 23 u = (.tok to, s2) →
    nameToken s2 = (b, s3) → b ≠ .null → callRule (f + 4) 202 s3 = (x, s4) → nonNull x = true →
    s4.errorIndicator = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ =
      (mkAt .Attribute [v, fieldOf b "id", opNode .Load] (extraLoc t { s4 with mark := s3.mark }),
        { s4 with mark := s3.mark }.leave)) ∧
  (v ≠ .null → ∀ (b n x x' : Ast) (to : Token) (s2 s3 s4 x1 y z1 w w' : PS),
    expectToken 23 u = (.tok to, s2) → nameToken s2 = (n, s3) → n ≠ .null →
    callRule (f + 4) 202 s3 = (x, s4) → nonNull x = false → s4.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) s4 →
    expectToken 9 { s4 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    callRule (f + 4) 185 { x1 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) y →
    expectToken 7 { y with mark := e } = (.null, z1) → z1.errorIndicator = false →
    callRule (f + 3) 147 { z1 with mark := σ.mark } = (b, w) → b ≠ .null →
    callRule (f + 2) 202 w = (x', w') → nonNull x' = true → w'.errorIndicator = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ = (b, { w' with mark := w.mark }.leave)) ∧
  (v ≠ .null → ∀ (sl x : Ast) (to tc : Token) (x0 x1 x2 x3 x4 : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.tok to, x1) → callRule (f + 4) 145 x1 = (sl, x2) →
    sl ≠ .null → expectToken 10 x2 = (.tok tc, x3) → callRule (f + 2) 202 x3 = (x, x4) →
    nonNull x = true → x4.errorIndicator = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ =
      (mkAt .Subscript [v, sl, opNode .Load] (extraLoc t { x4 with mark := x3.mark }),
        { x4 with mark := x3.mark }.leave)) ∧
  (v ≠ .null → ∀ (g x : Ast) (x0 x1 y y2 : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    callRule (f + 4) 185 { x1 with mark := e } = (g, y) → g ≠ .null →
    callRule (f + 3) 202 y = (x, y2) → nonNull x = true → y2.errorIndicator = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ =
      (mkAt .Call [v, .seq [g], .null] (extraLoc t { y2 with mark := y.mark }),
        { y2 with mark := y.mark }.leave)) ∧
  (v ≠ .null → ∀ (a x : Ast) (to tc : Token) (x0 x1 y z1 z2 z3 z4 : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    callRule (f + 4) 185 { x1 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) y →
    expectToken 7 { y with mark := e } = (.tok to, z1) → callRule (f + 2) 187 z1 = (a, z2) →
    z2.errorIndicator = false → expectToken 8 z2 = (.tok tc, z3) → callRule f 202 z3 = (x, z4) →
    nonNull x = true → z4.errorIndicator = false →
    ruleBody (f + 11) 201 (ruleOf 201) σ =
      (mkAt .Call [v, if truth a then fieldOf a "args" else .null,
        if truth a then fieldOf a "keywords" else .null] (extraLoc t { z4 with mark := z3.mark }),
        { z4 with mark := z3.mark }.leave)) ∧
  (v ≠ .null → ∀ (b x : Ast) (x0 x1 y z1 w w' : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    callRule (f + 4) 185 { x1 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) y →
    expectToken 7 { y with mark := e } = (.null, z1) → z1.errorIndicator = false →
    callRule (f + 3) 147 { z1 with mark := σ.mark } = (b, w) → b ≠ .null →
    callRule (f + 2) 202 w = (x, w') →
    (nonNull x = true → w'.errorIndicator = false →
      ruleBody (f + 11) 201 (ruleOf 201) σ = (b, { w' with mark := w.mark }.leave)) ∧
    (nonNull x = false →
      ruleBody (f + 11) 201 (ruleOf 201) σ = (.null, { w' with mark := σ.mark }.leave)))

theorem tPrimaryStep_proven : TPrimaryStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have hl1 : σ.level + 1 ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 201 σ.mark v e σ.enter := ⟨hf, hlt, hl1⟩
  have hit : ∀ g (S : PS), Seeded 201 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 201) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  have fillE : ∀ {x y : PS} {ty : Nat} {a : Ast}, expectToken ty x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_expect hx).le
  have fillC : ∀ {x y : PS} {g r : Nat} {a : Ast}, callRule g r x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_call hx).le
  have fillN : ∀ {x y : PS} {a : Ast}, nameToken x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_name hx).le
  have hSu : Seeded 201 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 201 = r201 from rfl, r201]
  refine ⟨fun hv b x s2 s3 h2 hb h3 hx h3e => ?_, fun hv b x s2 s3 h2 hb h3 hx => ?_,
    fun hv b x to s2 s3 s4 h2 h3 hb h4 hx h4e => ?_,
    fun hv b n x x' to s2 s3 s4 x1 y z1 w w' h2 h3 hn h4 hx h4e hk4 k1 k1e hg hye hky k2 k2e hat hb
      hla hx' hw'e => ?_,
    fun hv sl x to tc x0 x1 x2 x3 x4 k0 k0e k1 hsl hsln k2 hla hx h4e => ?_,
    fun hv g x x0 x1 y y2 k0 k0e k1 k1e hg hgn hla hx h2e => ?_,
    fun hv a x to tc x0 x1 y z1 z2 z3 z4 k0 k0e k1 k1e hg hye hky k2 ha hae k3 hla hx h4e => ?_,
    fun hv b x x0 x1 y z1 w w' k0 k0e k1 k1e hg hye hky k2 k2e hat hb hla => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by
        dsimp only
        rw [items_call (by rw [call_rule, h2]) hb, items_look (by rw [call_rule, h3]) hx, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h3e, Bool.or_false]
    simp [nonNull]
    try (cases b <;> simp_all)
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (by
        dsimp only
        rw [items_call (by rw [call_rule, h2]) hb, items_look_fail (by rw [call_rule, h3]) hx]),
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_look (by rw [call_rule, h4]) hx, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e]
  · have f4 : σ.fill ≤ s4.fill :=
      Nat.le_trans (show σ.fill ≤ ({ σ.enter with mark := e } : PS).fill from Nat.le_refl _)
        (Nat.le_trans (fillE h2) (Nat.le_trans (fillN h3) (fillC h4)))
    have hS4 : Seeded 201 σ.mark v e { s4 with mark := σ.mark } :=
      hk4.seeded hl1 (Nat.lt_of_lt_of_le hlt f4) σ.mark
    have hS4' : Seeded 201 σ.mark v e { s4 with mark := e } :=
      hk4.seeded hl1 (Nat.lt_of_lt_of_le hlt f4) e
    have hS1 : Seeded 201 σ.mark v e { x1 with mark := σ.mark } :=
      hS4'.after_expect k1 k1e (Nat.le_trans hef f4)
    have a1 : ({ s4 with mark := e } : PS).fill ≤ x1.fill := fillE k1
    have a2 : ({ x1 with mark := e } : PS).fill ≤ y.fill := fillC hg
    have fy : σ.fill ≤ y.fill := Nat.le_trans f4 (Nat.le_trans a1 a2)
    have hSy : Seeded 201 σ.mark v e { y with mark := σ.mark } :=
      hky.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hn, items_look_fail (by rw [call_rule, h4]) hx]),
      alts_fail (by rfl) (E s4 h4e) (by
      dsimp only
      rw [items_call (hit _ _ hS4 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_fail (by rfl) (E y hye) (by
      dsimp only
      rw [items_call (hit _ _ hSy rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_ok (by rfl) (E z1 k2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, hat]) hb, items_look (by rw [call_rule, hla]) hx', items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, hw'e, Bool.or_false]
    simp [nonNull]
    try (cases b <;> simp_all)
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_ok (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ (hSu.after_expect k0 k0e hef) rfl) hv,
        items_call (by rw [call_tok, k1]) (by simp), items_call (by rw [call_rule, hsl]) hsln,
        items_call (by rw [call_tok, k2]) (by simp), items_look (by rw [call_rule, hla]) hx,
        items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h4e]
  · have hS0 : Seeded 201 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fillE k0)
    have hS1 : Seeded 201 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 201 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect
        k1 k1e f0
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_ok (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call (by rw [call_rule, hg]) hgn,
        items_look (by rw [call_rule, hla]) hx, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h2e]
  · have hS0 : Seeded 201 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fillE k0)
    have hS1 : Seeded 201 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 201 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect
        k1 k1e f0
    have a0 : ({ σ.enter with mark := e } : PS).fill ≤ x0.fill := fillE k0
    have a1 : ({ x0 with mark := e } : PS).fill ≤ x1.fill := fillE k1
    have a2 : ({ x1 with mark := e } : PS).fill ≤ y.fill := fillC hg
    have fy : σ.fill ≤ y.fill := Nat.le_trans a0 (Nat.le_trans a1 a2)
    have hSy : Seeded 201 σ.mark v e { y with mark := σ.mark } :=
      hky.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_ok (by rfl) (E y hye) (by
      dsimp only
      rw [items_call (hit _ _ hSy rfl) hv, items_call (by rw [call_tok, k2]) (by simp),
        items_opt (by rw [call_rule, ha]) hae, items_call (by rw [call_tok, k3]) (by simp),
        items_look (by rw [call_rule, hla]) hx, items_nil]),
      altResult_extra rfl rfl]
    cases hta : truth a <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hta,
        Bool.or_false, mkAt, extraLoc, locArgs, ↓reduceIte, Bool.false_eq_true] <;>
      simp [mkAst, nonNull, hta, StateT.pure, StateT.bind, h4e, pure, bind]
  · have hS0 : Seeded 201 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fillE k0)
    have hS1 : Seeded 201 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 201 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect
        k1 k1e f0
    have a0 : ({ σ.enter with mark := e } : PS).fill ≤ x0.fill := fillE k0
    have a1 : ({ x0 with mark := e } : PS).fill ≤ x1.fill := fillE k1
    have a2 : ({ x1 with mark := e } : PS).fill ≤ y.fill := fillC hg
    have fy : σ.fill ≤ y.fill := Nat.le_trans a0 (Nat.le_trans a1 a2)
    have hSy : Seeded 201 σ.mark v e { y with mark := σ.mark } :=
      hky.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    refine ⟨fun hx hw'e => ?_, fun hx => ?_⟩
    · rw [alts_fail (by rfl) he' (by
        dsimp only
        rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
        alts_fail (by rfl) (E x0 k0e) (by
        dsimp only
        rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
        alts_fail (by rfl) (E x1 k1e) (by
        dsimp only
        rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_rule, hg])]),
        alts_fail (by rfl) (E y hye) (by
        dsimp only
        rw [items_call (hit _ _ hSy rfl) hv, items_call_null (by rw [call_tok, k2])])]
      rw [alts_ok (by rfl) (E z1 k2e) (by
          dsimp only
          rw [items_call (by rw [call_rule, hat]) hb, items_look (by rw [call_rule, hla]) hx, items_nil]),
        altResult_plain rfl rfl]
      simp only [evalA, pure, StateT.pure, hw'e, Bool.or_false]
      simp [nonNull]
      try (cases b <;> simp_all)
    · rw [alts_fail (by rfl) he' (by
        dsimp only
        rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
        alts_fail (by rfl) (E x0 k0e) (by
        dsimp only
        rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
        alts_fail (by rfl) (E x1 k1e) (by
        dsimp only
        rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_rule, hg])]),
        alts_fail (by rfl) (E y hye) (by
        dsimp only
        rw [items_call (hit _ _ hSy rfl) hv, items_call_null (by rw [call_tok, k2])])]
      rw [alts_fail (by rfl) (E z1 k2e) (by
          dsimp only
          rw [items_call (by rw [call_rule, hat]) hb, items_look_fail (by rw [call_rule, hla]) hx]),
        alts_nil]
      rfl

/-! ### `t_primary` when the lookahead after a trailer fails -/

/-- The fourth alternative of `t_primary_raw`, `a=t_primary '(' b=[arguments] ')' &t_lookahead`,
run after the seed (ending at `e`) from state `y`, fails with no error and leaves `z`: no `(` (7);
or `(`, `arguments` (187, an optional, no error) and no `)` (8); or `(` `arguments` `)` and the
lookahead `t_lookahead` (202) failing, as in `f(x) = 1`, where the state is the lookahead's with
the mark after the `)`. -/
def TPCallFails (f e : Nat) (y z : PS) : Prop :=
  (expectToken 7 { y with mark := e } = (.null, z) ∧ z.errorIndicator = false) ∨
  (∃ (to : Token) (a : Ast) (z1 z2 : PS), expectToken 7 { y with mark := e } = (.tok to, z1) ∧
    callRule (f + 2) 187 z1 = (a, z2) ∧ z2.errorIndicator = false ∧ expectToken 8 z2 = (.null, z) ∧
    z.errorIndicator = false) ∨
  (∃ (to tc : Token) (a x : Ast) (z1 z2 z3 z4 : PS), expectToken 7 { y with mark := e } = (.tok to, z1) ∧
    callRule (f + 2) 187 z1 = (a, z2) ∧ z2.errorIndicator = false ∧ expectToken 8 z2 = (.tok tc, z3) ∧
    callRule f 202 z3 = (x, z4) ∧ nonNull x = false ∧ z = { z4 with mark := z3.mark } ∧
    z.errorIndicator = false)

theorem TPCallFails.ei {f e : Nat} {y z : PS} (h : TPCallFails f e y z) : z.errorIndicator = false := by
  rcases h with ⟨-, h⟩ | ⟨-, -, -, -, -, -, -, -, h⟩ | ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ <;>
    exact h

/-- The last alternative of `t_primary_raw`, `a=atom &t_lookahead { a }`, as the round's result
`r`, from the state `z` the alternatives before it left (mark back at the start): `atom` (147)
with the lookahead holding gives the atom; with it failing, or without an atom, `NULL` with the
mark back at the start. -/
def TPAtomTail (f : Nat) (σ z : PS) (r : Ast × PS) : Prop :=
  (∀ (b x : Ast) (w w' : PS), callRule (f + 3) 147 { z with mark := σ.mark } = (b, w) → b ≠ .null →
    callRule (f + 2) 202 w = (x, w') →
    (nonNull x = true → w'.errorIndicator = false → r = (b, { w' with mark := w.mark }.leave)) ∧
    (nonNull x = false → r = (.null, { w' with mark := σ.mark }.leave))) ∧
  (∀ (w : PS), callRule (f + 3) 147 { z with mark := σ.mark } = (.null, w) →
    r = (.null, { w with mark := σ.mark }.leave))

/-- `a=atom &t_lookahead { a }`, the last alternative of `t_primary_raw`. -/
def tpAtomAlt : Alt :=
  { items := [(.call (.rule 147)), (.look true (.rule 202))], action := some (.var 0), nvars := 1,
    guardInvalid := false, extra := false }

theorem tpAtomTail_of {f : Nat} {σ z : PS} {st : Int × Int} (hze : z.errorIndicator = false) :
    TPAtomTail f σ z ((runAlts (f + 6) [tpAtomAlt] false σ.mark st { z with mark := σ.mark }).1.getD .null,
      (runAlts (f + 6) [tpAtomAlt] false σ.mark st { z with mark := σ.mark }).2.leave) := by
  have E : ({ z with mark := σ.mark } : PS).errorIndicator = false := hze
  simp only [tpAtomAlt]
  refine ⟨fun b x w w' hat hb hla => ⟨fun hx hw'e => ?_, fun hx => ?_⟩, fun w hat => ?_⟩
  · rw [alts_ok (by rfl) E (by
        dsimp only
        rw [items_call (by rw [call_rule, hat]) hb, items_look (by rw [call_rule, hla]) hx, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, hw'e, Bool.or_false]
    simp [nonNull]
    try (cases b <;> simp_all)
  · rw [alts_fail (by rfl) E (by
        dsimp only
        rw [items_call (by rw [call_rule, hat]) hb, items_look_fail (by rw [call_rule, hla]) hx]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) E (by dsimp only; rw [items_call_null (by rw [call_rule, hat])]), alts_nil]
    rfl

/-- The `'(' [arguments] ')' &t_lookahead` alternative failing as `TPCallFails` says, from the
start mark with the seed found. -/
theorem tpCall_items {f e : Nat} {σ y z : PS} {v : Ast} (hv : v ≠ .null)
    (hS : Seeded 201 σ.mark v e { y with mark := σ.mark }) (h : TPCallFails f e y z) :
    runItems (f + 6) [(.call (.rule 201)), (.call (.tok 7)), (.opt (.rule 187)), (.call (.tok 8)),
      (.look true (.rule 202))] #[] false { y with mark := σ.mark } = ((none, false), z) := by
  have hit : runCall (f + 5) (.rule 201) { y with mark := σ.mark } = (v, { y with mark := e }) := by
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS.level hS.lt hS.find
  rcases h with ⟨h1, -⟩ | ⟨to, a, z1, z2, h1, h2, h2e, h3, -⟩ |
      ⟨to, tc, a, x, z1, z2, z3, z4, h1, h2, h2e, h3, h4, hx, rfl, -⟩
  · rw [items_call hit hv, items_call_null (by rw [call_tok, h1])]
  · rw [items_call hit hv, items_call (by rw [call_tok, h1]) (by simp),
      items_opt (by rw [call_rule, h2]) h2e, items_call_null (by rw [call_tok, h3])]
  · rw [items_call hit hv, items_call (by rw [call_tok, h1]) (by simp),
      items_opt (by rw [call_rule, h2]) h2e, items_call (by rw [call_tok, h3]) (by simp),
      items_look_fail (by rw [call_rule, h4]) hx]

/-- A round of `t_primary_raw` with a seed `v` where a trailer matched but `&t_lookahead` after
it failed (no further `(`, `[` or `.`: the trailer is the assignment's own last target):
* `[` slices `]` with the lookahead failing (`a[0] = 1`): the subscript alternative fails, the
  mark goes back, `genexp` (which needs `(`) gives `NULL`, the call alternative fails
  (`TPCallFails`), and the round is `atom &t_lookahead` from the start mark (`TPAtomTail`);
* a `genexp` with the lookahead failing (`f(x for x in y) = 1`): likewise, through the call
  alternative to `atom`;
* `(` [arguments] `)` with the lookahead failing (`f(x) = 1`, inside `TPCallFails`): to `atom`.
So a trailer never ends a `t_primary`: `target_with_star_atom` takes the last one. Hypotheses: as
`TPrimaryStep`; the outcome states keep the seed (`SeedKept`) where a later alternative calls
`t_primary` again. -/
def TPrimaryFallback : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1201) = some (1201, v, e) → e ≤ σ.fill → v ≠ .null →
  let u : PS := { σ.enter with mark := e }
  (∀ (sl x : Ast) (to tc : Token) (x0 x1 x2 x3 x4 y z : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.tok to, x1) → callRule (f + 4) 145 x1 = (sl, x2) →
    sl ≠ .null → expectToken 10 x2 = (.tok tc, x3) → callRule (f + 2) 202 x3 = (x, x4) →
    nonNull x = false → x4.errorIndicator = false → SeedKept 201 σ.mark v e (σ.level + 1) x4 →
    callRule (f + 4) 185 { x4 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) y → TPCallFails f e y z →
    TPAtomTail f σ z (ruleBody (f + 11) 201 (ruleOf 201) σ)) ∧
  (∀ (g x : Ast) (x0 x1 y y2 z : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    callRule (f + 4) 185 { x1 with mark := e } = (g, y) → g ≠ .null →
    callRule (f + 3) 202 y = (x, y2) → nonNull x = false → y2.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) y2 → TPCallFails f e y2 z →
    TPAtomTail f σ z (ruleBody (f + 11) 201 (ruleOf 201) σ)) ∧
  (∀ (x0 x1 y z : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    expectToken 9 { x0 with mark := e } = (.null, x1) → x1.errorIndicator = false →
    callRule (f + 4) 185 { x1 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 201 σ.mark v e (σ.level + 1) y → TPCallFails f e y z →
    TPAtomTail f σ z (ruleBody (f + 11) 201 (ruleOf 201) σ))

theorem tPrimaryFallback_proven : TPrimaryFallback := by
  intro f σ v e he hlv hlt hf hef hv
  have hσl : σ.level ≠ MAXSTACK := by omega
  have hl1 : σ.level + 1 ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 201 σ.mark v e σ.enter := ⟨hf, hlt, hl1⟩
  have hit : ∀ g (S : PS), Seeded 201 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 201) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have fillE : ∀ {x y : PS} {ty : Nat} {a : Ast}, expectToken ty x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_expect hx).le
  have fillC : ∀ {x y : PS} {g r : Nat} {a : Ast}, callRule g r x = (a, y) → x.fill ≤ y.fill :=
    fun hx => (tg_call hx).le
  have hSu : Seeded 201 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 201 = r201 from rfl, r201]
  refine ⟨fun sl x to tc x0 x1 x2 x3 x4 y z k0 k0e k1 hsl hsln k2 hla hx h4e hk4 hg hye hky hz => ?_,
    fun g x x0 x1 y y2 z k0 k0e k1 k1e hg hgn hla hx h2e hk2 hz => ?_,
    fun x0 x1 y z k0 k0e k1 k1e hg hye hky hz => ?_⟩
  · have a0 : ({ σ.enter with mark := e } : PS).fill ≤ x0.fill := fillE k0
    have a1 : ({ x0 with mark := e } : PS).fill ≤ x1.fill := fillE k1
    have f4 : σ.fill ≤ x4.fill := Nat.le_trans a0 (Nat.le_trans a1 (Nat.le_trans (fillC hsl)
      (Nat.le_trans (fillE k2) (fillC hla))))
    have hS4 : Seeded 201 σ.mark v e { x4 with mark := σ.mark } :=
      hk4.seeded hl1 (Nat.lt_of_lt_of_le hlt f4) σ.mark
    have fy : σ.fill ≤ y.fill :=
      Nat.le_trans f4 (show ({ x4 with mark := e } : PS).fill ≤ y.fill from fillC hg)
    have hSy : Seeded 201 σ.mark v e { y with mark := σ.mark } :=
      hky.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ (hSu.after_expect k0 k0e hef) rfl) hv,
        items_call (by rw [call_tok, k1]) (by simp), items_call (by rw [call_rule, hsl]) hsln,
        items_call (by rw [call_tok, k2]) (by simp), items_look_fail (by rw [call_rule, hla]) hx]),
      alts_fail (by rfl) (E x4 h4e) (by
      dsimp only
      rw [items_call (hit _ _ hS4 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_fail (by rfl) (E y hye) (by exact tpCall_items hv hSy hz)]
    exact tpAtomTail_of hz.ei
  · have hS0 : Seeded 201 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fillE k0)
    have hS1 : Seeded 201 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 201 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect
        k1 k1e f0
    have a0 : ({ σ.enter with mark := e } : PS).fill ≤ x0.fill := fillE k0
    have a1 : ({ x0 with mark := e } : PS).fill ≤ x1.fill := fillE k1
    have a2 : ({ x1 with mark := e } : PS).fill ≤ y.fill := fillC hg
    have fy2 : σ.fill ≤ y2.fill := Nat.le_trans a0 (Nat.le_trans a1 (Nat.le_trans a2 (fillC hla)))
    have hSy2 : Seeded 201 σ.mark v e { y2 with mark := σ.mark } :=
      hk2.seeded hl1 (Nat.lt_of_lt_of_le hlt fy2) σ.mark
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call (by rw [call_rule, hg]) hgn,
        items_look_fail (by rw [call_rule, hla]) hx]),
      alts_fail (by rfl) (E y2 h2e) (by exact tpCall_items hv hSy2 hz)]
    exact tpAtomTail_of hz.ei
  · have hS0 : Seeded 201 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have f0 : e ≤ x0.fill :=
      Nat.le_trans (show e ≤ ({ σ.enter with mark := e } : PS).fill from hef) (fillE k0)
    have hS1 : Seeded 201 σ.mark v e { x1 with mark := σ.mark } :=
      (show Seeded 201 σ.mark v e { x0 with mark := e } from ⟨hS0.find, hS0.lt, hS0.level⟩).after_expect
        k1 k1e f0
    have a0 : ({ σ.enter with mark := e } : PS).fill ≤ x0.fill := fillE k0
    have a1 : ({ x0 with mark := e } : PS).fill ≤ x1.fill := fillE k1
    have a2 : ({ x1 with mark := e } : PS).fill ≤ y.fill := fillC hg
    have fy : σ.fill ≤ y.fill := Nat.le_trans a0 (Nat.le_trans a1 a2)
    have hSy : Seeded 201 σ.mark v e { y with mark := σ.mark } :=
      hky.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E x1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_fail (by rfl) (E y hye) (by exact tpCall_items hv hSy hz)]
    exact tpAtomTail_of hz.ei

/-- `t_primary`: one round (`TPrimaryStep`), the rounds where the lookahead after a trailer fails
(`TPrimaryFallback`), and the loop (`LeaderLoop`). -/
def TPrimaryRule : Prop := TPrimaryStep ∧ TPrimaryFallback ∧ LeaderLoop 201
theorem tPrimaryRule_proven : TPrimaryRule :=
  ⟨tPrimaryStep_proven, tPrimaryFallback_proven, leaderLoop_of rfl rfl⟩

end PyLean.PyGrammar.Peg
