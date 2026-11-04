import PyLean.PyGrammar.Peg.Rules.Base2

/-! `decorators` (`Grammar/python.gram:271`) and the `+` loop it is built on, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### A `+`/`*` loop over one sub-rule -/

/-- `handle_alt_loop` for an alternative that is one call of rule `rr` with the default action
(`_loop1_24` and its kind, `Parser/parser.c`): `while ((_res = rr_rule(p))) { _children[_n++] = _res;
_mark = p->mark; }`. Round `i` calls `rr` from `ss i`, which returns `vs i` and ends in `ss (i + 1)`;
the loop stops at the first `NULL` (round `n`), with the children in order and `_mark` the end of
the last child. -/
theorem runLoop_chain (rr : Nat) (a : Alt) (ha : a.items = [.call (.rule rr)])
    (hact : a.action = none) (hn : a.nvars = 1) (st : Int × Int) :
    ∀ (n f : Nat) (vs : Nat → Ast) (ss : Nat → PS) (s' : PS) (acc : List Ast),
    (∀ i, i < n → callRule (f + (n - i)) rr (ss i) = (vs i, ss (i + 1)) ∧ vs i ≠ .null) →
    callRule f rr (ss n) = (.null, s') →
    runLoop (f + n + 3) a (ss 0).mark st acc (ss 0) =
      ((((List.range n).map vs).reverse ++ acc, (ss n).mark, false, true), s') := by
  intro n
  induction n with
  | zero =>
    intro f vs ss s' acc _ hlast
    simp only [runLoop, ha, Nat.add_zero, List.range_zero, List.map_nil, List.reverse_nil,
      List.nil_append]
    rw [items_call_null (by rw [call_rule, hlast])]
  | succ n ih =>
    intro f vs ss s' acc hstep hlast
    obtain ⟨h0, h0n⟩ := hstep 0 (Nat.zero_lt_succ n)
    rw [show f + (n + 1 - 0) = f + n + 1 from by omega] at h0
    have hih := ih f (fun i => vs (i + 1)) (fun i => ss (i + 1)) s' (vs 0 :: acc) (fun i hi => by
      have := hstep (i + 1) (by omega)
      rw [show f + (n + 1 - (i + 1)) = f + (n - i) from by omega] at this
      exact this) hlast
    have hr : runItems (f + n + 3) a.items #[] false (ss 0) = ((some #[vs 0], false), ss 1) := by
      rw [ha, items_call (by rw [call_rule, h0]) h0n, items_nil]
      rfl
    have halt : altResult a false #[vs 0] st (ss 1) = (some (vs 0), ss 1) := by
      rw [altResult_none1 hact hn]
      rfl
    rw [show f + (n + 1) + 3 = (f + n + 3) + 1 from by omega, runLoop]
    simp only [hr, halt]
    simp only [Nat.zero_add] at hih
    rw [hih]
    simp [List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
    rfl

/-! ### `decorators` -/

/-- `decorators: a[asdl_expr_seq*]=('@' f=named_expression NEWLINE { f })+ { a }`
(`Grammar/python.gram:271`). The group `'@' f=named_expression NEWLINE { f }` is `_tmp_161`
(rule 438), the `+` loop `_loop1_24` (rule 301), and `decorators` itself (rule 34) has no
`EXTRA`.
* one decorator line: at `@`, `named_expression` then `NEWLINE` gives the expression; `@` with no
  `NEWLINE` after the expression, or any other token, gives `NULL`;
* the whole rule: the decorator lines one after another, in source order, as one sequence ending
  after the last `NEWLINE`; no decorator line at all gives `NULL` (`+`). -/
def DecoratorsRule : Prop :=
  (∀ (f : Nat) (p q : PS), Entered p q →
    let t := q.tokenAt p.mark
    (t.type ≠ 49 → callRule (f + 7) 438 p = (.null, q.leave)) ∧
    (t.type = 49 → ∀ (e : Ast) (tn : Token) (s2 s3 : PS),
      callRule (f + 1) 119 { q with mark := p.mark + 1 } = (e, s2) → e ≠ .null →
      expectToken 4 s2 = (.tok tn, s3) → s3.errorIndicator = false →
      callRule (f + 7) 438 p = (e, s3.leave)) ∧
    (t.type = 49 → ∀ (e : Ast) (s2 s3 : PS),
      callRule (f + 1) 119 { q with mark := p.mark + 1 } = (e, s2) → e ≠ .null →
      expectToken 4 s2 = (.null, s3) →
      callRule (f + 7) 438 p = (.null, { s3 with mark := p.mark }.leave))) ∧
  (∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level + 1 < MAXSTACK →
    ∀ (n : Nat) (vs : Nat → Ast) (ss : Nat → PS) (s' : PS), ss 0 = p.enter.enter →
    (∀ i, i < n → callRule (f + (n - i)) 438 (ss i) = (vs i, ss (i + 1)) ∧ vs i ≠ .null) →
    callRule f 438 (ss n) = (.null, s') →
    (0 < n → s'.errorIndicator = false →
      callRule (f + n + 10) 34 p =
        (.seq ((List.range n).map vs), { s' with mark := (ss n).mark }.leave.leave)) ∧
    (n = 0 → callRule (f + n + 10) 34 p =
      (.null, { { s' with mark := (ss n).mark }.leave with mark := p.mark }.leave)))

theorem decoratorsRule_proven : DecoratorsRule := by
  refine ⟨fun f p q h => ?_, fun f p he hl n vs ss s' hs0 hstep hlast => ?_⟩
  · obtain ⟨-, -, -, -, hm, -, -⟩ := h.facts
    have he' : p.enter.errorIndicator = false := h.ei
    have hq : { q with mark := p.mark } = q := by rw [← hm]
    rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 438 = r438 from rfl, r438]
    refine ⟨fun ht => ?_, fun ht e tn s2 s3 h2 hE h3 h3e => ?_, fun ht e s2 s3 h2 hE h3 => ?_⟩
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [call_tok, expect_entered h, ite_f ht])), hq,
        alts_nil]
      rfl
    · rw [alts_ok (by rfl) he' (by
        dsimp only
        rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
          items_call (by rw [call_rule, h2]) hE, items_call (by rw [call_tok, h3]) (by simp),
          items_nil]), altResult_plain rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
      have hE' : nonNull e = true := by cases e <;> simp_all [nonNull]
      simp [hE', h3e]
    · rw [alts_fail (by rfl) he' (by
        dsimp only
        rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
          items_call (by rw [call_rule, h2]) hE, items_call_null (by rw [call_tok, h3])]), alts_nil]
      rfl
  · have hl1 : p.level ≠ MAXSTACK := by omega
    have hl2 : p.enter.level ≠ MAXSTACK := by show p.level + 1 ≠ MAXSTACK; omega
    have he' : p.enter.errorIndicator = false := he
    have he'' : p.enter.enter.errorIndicator = false := he
    -- `_loop1_24`, rule 301: the prologue (no memo, no `EXTRA`), then the loop
    have hloop := runLoop_chain 438 (r301.alts.headD default) rfl rfl rfl (0, 0) n f vs ss s' [] hstep hlast
    rw [hs0] at hloop
    have hloop' : runLoop (f + n + 3) (r301.alts.headD default) p.mark (0, 0) [] p.enter.enter =
        ((((List.range n).map vs).reverse ++ [], (ss n).mark, false, true), s') := hloop
    have hp : rulePrologue 301 r301 p.enter = (.inr (p.mark, (0, 0)), p.enter.enter) := by
      simp only [rulePrologue, addLevel_ok p.enter hl2, he'', show r301.memo = false from rfl,
        Bool.false_eq_true, ↓reduceIte, ruleStart, show r301.extra = false from rfl]
      rfl
    have hk : r301.kind = RuleKind.loop1 := rfl
    have hb : callRule (f + n + 5) 301 p.enter = loopFinish r301
        (((List.range n).map vs).reverse ++ [], (ss n).mark, false, true) s' := by
      have e1 : callRule (f + n + 5) 301 p.enter = ruleBody (f + n + 4) 301 r301 p.enter := by
        rw [show f + n + 5 = (f + n + 4) + 1 from rfl]
        simp only [callRule, show ruleOf 301 = r301 from rfl, show r301.leftRec = false from rfl,
          show r301.withoutInvalid = false from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      rw [e1, show f + n + 4 = (f + n + 3) + 1 from rfl]
      simp only [ruleBody, hp, hk, he'', Bool.false_eq_true, ↓reduceIte]
      rw [hloop']
    have hr34 := callRule_plain (f := f + n + 8) (id := 34) (p := p) rfl rfl rfl rfl rfl he hl1
    rw [show f + n + 8 + 2 = f + n + 10 from rfl] at hr34
    rw [hr34]
    simp only [show ruleOf 34 = r34 from rfl, r34]
    refine ⟨fun hpos hse => ?_, fun hz => ?_⟩
    · have hne : (((List.range n).map vs).reverse ++ []).isEmpty = false := by
        cases n with
        | zero => omega
        | succ k => simp [List.range_succ]
      have hfin : loopFinish r301 (((List.range n).map vs).reverse ++ [], (ss n).mark, false, true) s' =
          (.seq ((List.range n).map vs), { s' with mark := (ss n).mark }.leave) := by
        simp only [loopFinish, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, hne, hse,
          Bool.or_false, Bool.and_false, retLevel_eq, subLevel]
        simp
      rw [alts_ok (by rfl) he' (by
        dsimp only
        rw [items_call (by rw [call_rule, hb, hfin]) (by simp), items_nil]), altResult_plain rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
      simp [nonNull, hse, PS.leave]
    · subst hz
      have hfin : loopFinish r301 (((List.range 0).map vs).reverse ++ [], (ss 0).mark, false, true) s' =
          (.null, { s' with mark := (ss 0).mark }.leave) := by
        simp only [loopFinish, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, retLevel_eq]
        simp
      rw [alts_fail (by rfl) he' (by
        dsimp only
        rw [items_call_null (by rw [call_rule, hb, hfin])]), alts_nil]
      rfl

end PyLean.PyGrammar.Peg
