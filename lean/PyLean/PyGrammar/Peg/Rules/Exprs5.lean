import PyLean.PyGrammar.Peg.Rules.Exprs4

/-! `disjunction` and `conjunction` (`Grammar/python.gram:763-771`), with their `+` loops of
`'or' conjunction` and `'and' inversion`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- A `_loop1_` rule over one rule `rr` (default action): rounds `i < n` call `rr` from `ss i`
(`ss 0` the state after entry), the first `NULL` ends the loop; with at least one round (and no
error) the sequence of the values in order, ending after the last; with none, `NULL`. -/
def Loop1Over (lp rr : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  ∀ (n : Nat) (vs : Nat → Ast) (ss : Nat → PS) (s' : PS), ss 0 = p.enter →
  (∀ i, i < n → callRule (f + (n - i)) rr (ss i) = (vs i, ss (i + 1)) ∧ vs i ≠ .null) →
  callRule f rr (ss n) = (.null, s') →
  (0 < n → s'.errorIndicator = false →
    callRule (f + n + 5) lp p = (.seq ((List.range n).map vs), { s' with mark := (ss n).mark }.leave)) ∧
  (n = 0 → callRule (f + n + 5) lp p = (.null, { s' with mark := (ss n).mark }.leave))

theorem loop1Over_of {lp rr : Nat}
    (hl : ruleOf lp = Rule.mk (ruleOf lp).name .loop1 false false false false false
      [Alt.mk [.call (.rule rr)] none 1 false false]) : Loop1Over lp rr := by
  intro f p he hlv n vs ss s' hs0 hstep hlast
  have he' : p.enter.errorIndicator = false := he
  have hloop := runLoop_chain rr ((ruleOf lp).alts.headD default) (by rw [hl]; rfl) (by rw [hl]; rfl)
    (by rw [hl]; rfl) (0, 0) n f vs ss s' [] hstep hlast
  rw [hs0] at hloop
  have hloop' : runLoop (f + n + 3) ((ruleOf lp).alts.headD default) p.mark (0, 0) [] p.enter =
      ((((List.range n).map vs).reverse ++ [], (ss n).mark, false, true), s') := hloop
  have hp : rulePrologue lp (ruleOf lp) p = (.inr (p.mark, (0, 0)), p.enter) := by
    simp only [rulePrologue, addLevel_ok p hlv, he', show (ruleOf lp).memo = false by rw [hl],
      Bool.false_eq_true, ↓reduceIte, ruleStart, show (ruleOf lp).extra = false by rw [hl]]
    rfl
  have hk : (ruleOf lp).kind = RuleKind.loop1 := by rw [hl]
  have hb : callRule (f + n + 5) lp p = loopFinish (ruleOf lp)
      (((List.range n).map vs).reverse ++ [], (ss n).mark, false, true) s' := by
    have e1 : callRule (f + n + 5) lp p = ruleBody (f + n + 4) lp (ruleOf lp) p := by
      rw [show f + n + 5 = (f + n + 4) + 1 from rfl]
      simp only [callRule, show (ruleOf lp).leftRec = false by rw [hl],
        show (ruleOf lp).withoutInvalid = false by rw [hl], Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
    rw [e1, show f + n + 4 = (f + n + 3) + 1 from rfl]
    simp only [ruleBody, hp, hk, he', Bool.false_eq_true, ↓reduceIte]
    rw [hloop']
  refine ⟨fun hpos hse => ?_, fun hz => ?_⟩
  · have hne : (((List.range n).map vs).reverse ++ []).isEmpty = false := by
      cases n with
      | zero => omega
      | succ k => simp [List.range_succ]
    rw [hb]
    simp only [loopFinish, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, hne, hse,
      Bool.or_false, Bool.and_false, retLevel_eq, subLevel]
    simp
  · subst hz
    rw [hb]
    simp only [loopFinish, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, retLevel_eq]
    simp

/-- A rule `x: tok e=rr { e }` (no `EXTRA`): at the token `tk`, the `rr` after it is the result;
at another token, or without `rr`, `NULL` with the mark back. -/
def TokThen (id tk rr : Nat) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ tk → callRule (f + 6) id p = (.null, q.leave)) ∧
  (t.type = tk → ∀ (e : Ast) (s : PS), callRule f rr { q with mark := p.mark + 1 } = (e, s) →
    e ≠ .null → s.errorIndicator = false → callRule (f + 6) id p = (e, s.leave)) ∧
  (t.type = tk → ∀ (s : PS), callRule f rr { q with mark := p.mark + 1 } = (.null, s) →
    callRule (f + 6) id p = (.null, { s with mark := p.mark }.leave))

theorem tokThen_of {id tk rr : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.tok tk), .call (.rule rr)] (some (.var 1)) 2 false false]) :
    TokThen id tk rr := by
  intro f p q h
  obtain ⟨-, -, -, -, hm, -, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) h.ei h.level, hr]
  refine ⟨fun ht => ?_, fun ht e s h1 hE h1e => ?_, fun ht s h1 => ?_⟩
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [call_tok, expect_entered h, ite_f ht])), hq,
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) hE, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases e <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- The first alternative `a=sub b=loop+` of a `BoolOp` rule fails, ending in `s`. -/
def BoolA1Fails (f sub lp : Nat) (q s : PS) : Prop :=
  callRule (f + 3) sub q = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (f + 3) sub q = (a, s1) ∧ a ≠ .null ∧ callRule (f + 2) lp s1 = (.null, s))

/-- `disjunction (memo)` / `conjunction (memo)` (`Grammar/python.gram:763-771`):
```
    | a=sub b=('op' c=sub { c })+ { _PyAST_BoolOp(Op, CHECK(..., _PyPegen_seq_insert_in_front(p, a, b)), EXTRA) }
    | sub
```
A `sub` followed by the `+` loop (`lp`) gives one flat `BoolOp(op, [a] + b)` (so `a or b or c` is
one `BoolOp` with three values); once that fails, `sub` from the start mark; memoized at the start
mark. -/
def BoolOpRule (id sub lp : Nat) (op : Ctor) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + id) = none →
  let t := q.tokenAt p.mark
  (∀ (a b : Ast) (s1 s2 : PS), callRule (f + 3) sub q = (a, s1) → a ≠ .null →
    callRule (f + 2) lp s1 = (b, s2) → b ≠ .null → s2.errorIndicator = false →
    callRule (f + 8) id p =
      memoDone p.mark id (some (mkAt .BoolOp [opNode op, .seq (a :: seqOf b)] (extraLoc t s2)), s2)) ∧
  (∀ (v : Ast) (s s3 : PS), BoolA1Fails f sub lp q s → s.errorIndicator = false →
    callRule (f + 2) sub { s with mark := p.mark } = (v, s3) → v ≠ .null →
    callRule (f + 8) id p = memoDone p.mark id (some v, s3)) ∧
  (∀ (s s3 : PS), BoolA1Fails f sub lp q s → s.errorIndicator = false →
    callRule (f + 2) sub { s with mark := p.mark } = (.null, s3) →
    callRule (f + 8) id p = memoDone p.mark id (some .null, { s3 with mark := p.mark }))

theorem boolOpRule_of {id sub lp : Nat} {op : Ctor}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal true false false true false
      [Alt.mk [.call (.rule sub), .call (.rule lp)]
        (some (.mk .BoolOp [.ctor op, .check (.call .seq_insert_in_front [.var 0, .var 1]), .extra0,
          .extra1, .extra2, .extra3])) 2 false true,
       Alt.mk [.call (.rule sub)] none 1 false false]) : BoolOpRule id sub lp op := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_memo_extra (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) h hn, hr]
  have hA1 : ∀ {s : PS}, BoolA1Fails f sub lp q s →
      runItems (f + 5) [.call (.rule sub), .call (.rule lp)] #[] false q = ((none, false), s) := by
    intro s hf
    rcases hf with h1 | ⟨a, s1, h1, ha, h2⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]
  refine ⟨fun a b s1 s2 h1 ha h2 hb h2e => ?_, fun v s s3 h0 h0e h1 hv => ?_,
    fun s s3 h0 h0e h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h2e, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) he (by exact hA1 h0), alts_ok (by rfl) (E s h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by exact hA1 h0), alts_fail (by rfl) (E s h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]

/-- `disjunction`: the rule, its loop `_loop1_61` (338) and the group `'or' c=conjunction { c }`
(`_tmp_163`, 440; `or` is 589). -/
def DisjunctionRule : Prop := BoolOpRule 120 121 338 .Or ∧ Loop1Over 338 440 ∧ TokThen 440 589 121
theorem disjunctionRule_proven : DisjunctionRule :=
  ⟨boolOpRule_of rfl, loop1Over_of rfl, tokThen_of rfl⟩

/-- `conjunction`: the rule, its loop `_loop1_62` (339) and the group `'and' c=inversion { c }`
(`_tmp_164`, 441; `and` is 590). -/
def ConjunctionRule : Prop := BoolOpRule 121 122 339 .And ∧ Loop1Over 339 441 ∧ TokThen 441 590 122
theorem conjunctionRule_proven : ConjunctionRule :=
  ⟨boolOpRule_of rfl, loop1Over_of rfl, tokThen_of rfl⟩

end PyLean.PyGrammar.Peg
