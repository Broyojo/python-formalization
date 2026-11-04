import PyLean.PyGrammar.Peg.Rules.LeftRec

/-! `primary` (`Grammar/python.gram:875-884`), the left-recursive leader of calls, attributes and
subscripts, rule by rule (see `LeftRec.lean`). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- What a sub-rule call that returned (with no error) leaves of the round's seed: the memo entry
of the leader at the start mark, and `p->level` as it was when the call started. Every rule
function of `Parser/parser.c` writes memo entries only at marks at or after the one it started
from (`_PyPegen_insert_memo(p, _mark, ...)`, `_PyPegen_update_memo(p, _mark, ...)`), and restores
`p->level` on every return; a call that starts after the seed's start therefore leaves both. -/
structure SeedKept (id m : Nat) (v : Ast) (e : Nat) (lvl : Nat) (y : PS) : Prop where
  find : (y.memo.getD m []).find? (fun x => x.1 == 1000 + id) = some (1000 + id, v, e)
  level : y.level = lvl

theorem SeedKept.seeded {id m e lvl : Nat} {v : Ast} {y : PS} (k : SeedKept id m v e lvl y)
    (hl : lvl ≠ MAXSTACK) (hlt : m < y.fill) (m' : Nat) : Seeded id m v e { y with mark := m' } :=
  ⟨k.find, hlt, by rw [show ({ y with mark := m' } : PS).level = y.level from rfl, k.level]; exact hl⟩

/-! ### `primary` -/

/-- One round of `primary_raw` (`Grammar/python.gram:875-884`):
```
    | a=primary '.' b=NAME { _PyAST_Attribute(a, b->v.Name.id, Load, EXTRA) }
    | a=primary b=genexp { _PyAST_Call(a, CHECK(asdl_expr_seq*, (asdl_expr_seq*)_PyPegen_singleton_seq(p, b)), NULL, EXTRA) }
    | a=primary '(' b=[arguments] ')' {
        _PyAST_Call(a,
                 (b) ? ((expr_ty) b)->v.Call.args : NULL,
                 (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                 EXTRA) }
    | a=primary '[' b=slices ']' { _PyAST_Subscript(a, b, Load, EXTRA) }
    | atom
```
run from a state `σ` at the start mark whose memo holds seed `v` for `primary`, ending at `e`
(as in `SumStep`):
* with no seed (the first round), the four trailer alternatives fail at the recursive call and the
  round is `atom` from the start mark, `NULL` with the mark back when `atom` fails;
* with a seed and `.` NAME after it, `Attribute(v, NAME.id, Load)`;
* with no `.`, a `genexp` after the seed gives `Call(v, [genexp], NULL)`, and an error in `genexp`
  ends the round with `NULL`;
* with no `.` and no `genexp` (and no error), `(` [arguments] `)` gives
  `Call(v, b ? b.args : NULL, b ? b.keywords : NULL)`: `genexp` is tried before the call with
  arguments, so `f(x for x in y)` is a call with one generator argument;
* with none of `.`, `genexp`, `(`, `[` slices `]` gives `Subscript(v, slices, Load)`;
* with none of the four, the round is `atom` from the start mark (which does not grow, and ends
  the loop).
Each later alternative finds the seed again through `_PyPegen_is_memoized`. Hypotheses: as
`SumStep`; and after the `genexp` call returned `NULL` without an error, the state keeps the seed
(`SeedKept`: the memo entry at the start mark and `p->level`), as every real outcome does. -/
def PrimaryStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1144) = some (1144, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → ∀ (b : Ast) (s2 : PS), callRule (f + 2) 147 σ.enter = (b, s2) → b ≠ .null →
    ruleBody (f + 10) 144 (ruleOf 144) σ = (b, s2.leave)) ∧
  (v = .null → ∀ (s2 : PS), callRule (f + 2) 147 σ.enter = (.null, s2) →
    ruleBody (f + 10) 144 (ruleOf 144) σ = (.null, { s2 with mark := σ.mark }.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 : PS), expectToken 23 u = (.tok to, s2) →
    nameToken s2 = (b, s3) → b ≠ .null → s3.errorIndicator = false →
    ruleBody (f + 10) 144 (ruleOf 144) σ =
      (mkAt .Attribute [v, fieldOf b "id", opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (v ≠ .null → ∀ (g : Ast) (x0 y : PS), expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    callRule (f + 4) 185 { x0 with mark := e } = (g, y) → g ≠ .null → y.errorIndicator = false →
    ruleBody (f + 10) 144 (ruleOf 144) σ = (mkAt .Call [v, .seq [g], .null] (extraLoc t y), y.leave)) ∧
  (v ≠ .null → ∀ (x0 y : PS), expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    callRule (f + 4) 185 { x0 with mark := e } = (.null, y) → y.errorIndicator = true →
    ruleBody (f + 10) 144 (ruleOf 144) σ = (.null, { y with mark := σ.mark }.leave)) ∧
  (v ≠ .null → ∀ (a : Ast) (to tc : Token) (x0 y z1 z2 z3 : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    callRule (f + 4) 185 { x0 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 144 σ.mark v e (σ.level + 1) y →
    expectToken 7 { y with mark := e } = (.tok to, z1) → callRule (f + 2) 187 z1 = (a, z2) →
    z2.errorIndicator = false → expectToken 8 z2 = (.tok tc, z3) → z3.errorIndicator = false →
    ruleBody (f + 10) 144 (ruleOf 144) σ =
      (mkAt .Call [v, if truth a then fieldOf a "args" else .null,
        if truth a then fieldOf a "keywords" else .null] (extraLoc t z3), z3.leave)) ∧
  (v ≠ .null → ∀ (sl : Ast) (to tc : Token) (x0 y z1 w1 w2 w3 : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    callRule (f + 4) 185 { x0 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 144 σ.mark v e (σ.level + 1) y →
    expectToken 7 { y with mark := e } = (.null, z1) → z1.errorIndicator = false →
    expectToken 9 { z1 with mark := e } = (.tok to, w1) → callRule (f + 1) 145 w1 = (sl, w2) →
    sl ≠ .null → expectToken 10 w2 = (.tok tc, w3) → w3.errorIndicator = false →
    ruleBody (f + 10) 144 (ruleOf 144) σ =
      (mkAt .Subscript [v, sl, opNode .Load] (extraLoc t w3), w3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (x0 y z1 w1 w2 : PS),
    expectToken 23 u = (.null, x0) → x0.errorIndicator = false →
    callRule (f + 4) 185 { x0 with mark := e } = (.null, y) → y.errorIndicator = false →
    SeedKept 144 σ.mark v e (σ.level + 1) y →
    expectToken 7 { y with mark := e } = (.null, z1) → z1.errorIndicator = false →
    expectToken 9 { z1 with mark := e } = (.null, w1) → w1.errorIndicator = false →
    callRule (f + 2) 147 { w1 with mark := σ.mark } = (b, w2) → b ≠ .null →
    ruleBody (f + 10) 144 (ruleOf 144) σ = (b, w2.leave))

theorem primaryStep_proven : PrimaryStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have hl1 : σ.level + 1 ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 144 σ.mark v e σ.enter := ⟨hf, hlt, hl1⟩
  have hit : ∀ g (S : PS), Seeded 144 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 144) S = (v, { S with mark := e }) := by
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
  have hSu : Seeded 144 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 144 = r144 from rfl, r144]
  refine ⟨fun hv b s2 h2 hb => ?_, fun hv s2 h2 => ?_,
    fun hv b to s2 s3 h2 h3 hb h3e => ?_,
    fun hv g x0 y k0 k0e hg hgn hye => ?_,
    fun hv x0 y k0 k0e hg hye => ?_,
    fun hv a to tc x0 y z1 z2 z3 k0 k0e hg hye hk k1 ha hae k2 k2e => ?_,
    fun hv sl to tc x0 y z1 w1 w2 w3 k0 k0e hg hye hk k1 k1e k2 hsl hsln k3 k3e => ?_,
    fun hv b x0 y z1 w1 w2 k0 k0e hg hye hk k1 k1e k2 k2e hat hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hS0 : Seeded 144 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_ok (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call (by rw [call_rule, hg]) hgn, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hye,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull]
  · have hS0 : Seeded 144 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_err (by rfl) (show ({ y with mark := σ.mark } : PS).errorIndicator = true from hye)]
    rfl
  · have hS0 : Seeded 144 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have fy : σ.fill ≤ y.fill :=
      Nat.le_trans (show σ.fill ≤ ({ σ.enter with mark := e } : PS).fill from Nat.le_refl _)
        (Nat.le_trans (fillE k0) (show ({ x0 with mark := e } : PS).fill ≤ y.fill from fillC hg))
    have hSy : Seeded 144 σ.mark v e { y with mark := σ.mark } :=
      hk.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_ok (by rfl) (E y hye) (by
      dsimp only
      rw [items_call (hit _ _ hSy rfl) hv, items_call (by rw [call_tok, k1]) (by simp),
        items_opt (by rw [call_rule, ha]) hae, items_call (by rw [call_tok, k2]) (by simp),
        items_nil]),
      altResult_extra rfl rfl]
    cases hta : truth a <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, k2e, hta,
        Bool.or_false, mkAt, extraLoc, locArgs, ↓reduceIte, Bool.false_eq_true] <;>
      simp [mkAst, nonNull, hta, StateT.pure, StateT.bind, k2e, pure, bind]
  · have hS0 : Seeded 144 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have fy : σ.fill ≤ y.fill :=
      Nat.le_trans (show σ.fill ≤ ({ σ.enter with mark := e } : PS).fill from Nat.le_refl _)
        (Nat.le_trans (fillE k0) (show ({ x0 with mark := e } : PS).fill ≤ y.fill from fillC hg))
    have hSy : Seeded 144 σ.mark v e { y with mark := σ.mark } :=
      hk.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    have hSy' : Seeded 144 σ.mark v e { y with mark := e } :=
      hk.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) e
    have hS1 : Seeded 144 σ.mark v e { z1 with mark := σ.mark } :=
      hSy'.after_expect k1 k1e (Nat.le_trans hef fy)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_fail (by rfl) (E y hye) (by
      dsimp only
      rw [items_call (hit _ _ hSy rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_ok (by rfl) (E z1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call (by rw [call_tok, k2]) (by simp),
        items_call (by rw [call_rule, hsl]) hsln, items_call (by rw [call_tok, k3]) (by simp),
        items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, k3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have hS0 : Seeded 144 σ.mark v e { x0 with mark := σ.mark } := hSu.after_expect k0 k0e hef
    have fy : σ.fill ≤ y.fill :=
      Nat.le_trans (show σ.fill ≤ ({ σ.enter with mark := e } : PS).fill from Nat.le_refl _)
        (Nat.le_trans (fillE k0) (show ({ x0 with mark := e } : PS).fill ≤ y.fill from fillC hg))
    have hSy : Seeded 144 σ.mark v e { y with mark := σ.mark } :=
      hk.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) σ.mark
    have hSy' : Seeded 144 σ.mark v e { y with mark := e } :=
      hk.seeded hl1 (Nat.lt_of_lt_of_le hlt fy) e
    have hS1 : Seeded 144 σ.mark v e { z1 with mark := σ.mark } :=
      hSy'.after_expect k1 k1e (Nat.le_trans hef fy)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, k0])]),
      alts_fail (by rfl) (E x0 k0e) (by
      dsimp only
      rw [items_call (hit _ _ hS0 rfl) hv, items_call_null (by rw [call_rule, hg])]),
      alts_fail (by rfl) (E y hye) (by
      dsimp only
      rw [items_call (hit _ _ hSy rfl) hv, items_call_null (by rw [call_tok, k1])]),
      alts_fail (by rfl) (E z1 k1e) (by
      dsimp only
      rw [items_call (hit _ _ hS1 rfl) hv, items_call_null (by rw [call_tok, k2])]),
      alts_ok (by rfl) (E w1 k2e) (by
        dsimp only; rw [items_call (by rw [call_rule, hat]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- `primary`: one round (`PrimaryStep`) and the loop (`LeaderLoop`), so trailers group to the left:
`a.b(c)[d]` is `Subscript(Call(Attribute(a, b), [c]), d)`. -/
def PrimaryRule : Prop := PrimaryStep ∧ LeaderLoop 144
theorem primaryRule_proven : PrimaryRule := ⟨primaryStep_proven, leaderLoop_of rfl rfl⟩

end PyLean.PyGrammar.Peg
