import PyLean.PyGrammar.Peg.Rules.Patterns2
import PyLean.PyGrammar.Peg.Rules.Decorators

/-! The `','.x+` gathers of the pattern rules and the rules built on them
(`Grammar/python.gram:600-678`): `maybe_sequence_pattern`, `open_sequence_pattern`,
`items_pattern`, `positional_patterns`, `keyword_patterns`, and the one-item rules
`key_value_pattern`, `double_star_pattern`, `keyword_pattern`, `star_pattern`,
`pattern_capture_target`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `','.rr+`: the `_loop0_` of `',' rr` and the `_gather_` around it -/

/-- `handle_alt_loop` for the alternative `sep elem=rr { elem }` of a `_loop0_` (the tail of a
`sep.rr+` gather; `sep` is `,` (12) or, for `simple_stmts`, `;` (13)): round `i` reads the
separator token `sep` from `ss i`, then `rr` gives `vs i` and ends in `ss (i + 1)`; the loop stops
at the first round where `sep` or `rr` fails (round `n`), with the children in order and `_mark`
the end of the last child (so a trailing separator is left unread). -/
theorem runLoop_sep (sep rr : Nat) (a : Alt) (ha : a.items = [.call (.tok sep), .call (.rule rr)])
    (hact : a.action = some (.var 1)) (hex : a.extra = false) (st : Int × Int) :
    ∀ (n f : Nat) (vs : Nat → Ast) (ss ts : Nat → PS) (s' : PS) (acc : List Ast),
    (∀ i, i < n → (∃ c, expectToken sep (ss i) = (.tok c, ts i)) ∧
      callRule (f + (n - i)) rr (ts i) = (vs i, ss (i + 1)) ∧ vs i ≠ .null ∧
      (ss (i + 1)).errorIndicator = false) →
    (expectToken sep (ss n) = (.null, s') ∨
      ∃ (c : Token) (t : PS), expectToken sep (ss n) = (.tok c, t) ∧ callRule f rr t = (.null, s')) →
    runLoop (f + n + 4) a (ss 0).mark st acc (ss 0) =
      ((((List.range n).map vs).reverse ++ acc, (ss n).mark, false, true), s') := by
  intro n
  induction n with
  | zero =>
    intro f vs ss ts s' acc _ hlast
    simp only [runLoop, ha, Nat.add_zero, List.range_zero, List.map_nil, List.reverse_nil,
      List.nil_append]
    rcases hlast with h | ⟨c, t, h1, h2⟩
    · rw [items_call_null (by rw [call_tok, h])]
    · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
  | succ n ih =>
    intro f vs ss ts s' acc hstep hlast
    obtain ⟨⟨c, h0t⟩, h0, h0n, h0e⟩ := hstep 0 (Nat.zero_lt_succ n)
    rw [show f + (n + 1 - 0) = f + n + 1 from by omega] at h0
    have hih := ih f (fun i => vs (i + 1)) (fun i => ss (i + 1)) (fun i => ts (i + 1)) s'
      (vs 0 :: acc) (fun i hi => by
        have := hstep (i + 1) (by omega)
        rw [show f + (n + 1 - (i + 1)) = f + (n - i) from by omega] at this
        exact this) hlast
    have hr : runItems (f + n + 4) a.items #[] false (ss 0) =
        ((some #[.tok c, vs 0], false), ss 1) := by
      rw [ha, items_call (by rw [call_tok, h0t]) (by simp), items_call (by rw [call_rule, h0]) h0n,
        items_nil]
      rfl
    have hv : nonNull (vs 0) = true := by cases h : vs 0 <;> simp_all [nonNull]
    have halt : altResult a false #[.tok c, vs 0] st (ss 1) = (some (vs 0), ss 1) := by
      rw [altResult_plain hact hex]
      simp only [evalA, pure, StateT.pure, hv, h0e]
      simp [nonNull]
    rw [show f + (n + 1) + 4 = (f + n + 4) + 1 from by omega, runLoop]
    simp only [hr, halt]
    simp only [Nat.zero_add] at hih
    rw [hih]
    simp [List.range_succ_eq_map, List.map_cons, List.map_map, List.reverse_cons]
    rfl

/-- Entry of a `_gather_` rule function (no memo, no `EXTRA`): as `callRule_plain`, with the
gather default action. -/
theorem callRule_gather {f id : Nat} {p : PS}
    (h1 : (ruleOf id).leftRec = false) (h2 : (ruleOf id).withoutInvalid = false)
    (h3 : (ruleOf id).memo = false) (h4 : (ruleOf id).kind = .gather) (h5 : (ruleOf id).extra = false)
    (he : p.errorIndicator = false) (hl : p.level ≠ MAXSTACK) :
    callRule (f + 2) id p =
      let a := runAlts f (ruleOf id).alts true p.mark (0, 0) p.enter
      (a.1.getD .null, a.2.leave) := by
  have he' : p.enter.errorIndicator = false := he
  have hp : rulePrologue id (ruleOf id) p = (.inr (p.mark, (0, 0)), p.enter) := by
    simp only [rulePrologue, addLevel_ok p hl, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5]
    rfl
  simp only [callRule, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, h4, retLevel_eq]
  have hg : (RuleKind.gather == RuleKind.gather) = true := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all

/-- A `sep.rr+` gather (`_gather_g`: `rr _loop0_lp`, `_loop0_lp`: `(sep rr)*`, `sep` a token
type), from `p`: the
first `rr` at the entry state, then the loop's rounds (`runLoop_sep`) from the state after it; the
result is the sequence of all the `rr` values in source order, ending after the last one; no first
`rr` gives `NULL` with the mark back. -/
def GatherSepTok (sep g lp rr : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level + 1 < MAXSTACK →
  (∀ (k0 : Ast) (s1 : PS) (n : Nat) (vs : Nat → Ast) (ss ts : Nat → PS) (s' : PS),
    callRule (f + n + 7) rr p.enter = (k0, s1) → k0 ≠ .null → s1.errorIndicator = false →
    s1.level = p.level + 1 →
    ss 0 = s1.enter →
    (∀ i, i < n → (∃ c, expectToken sep (ss i) = (.tok c, ts i)) ∧
      callRule (f + (n - i)) rr (ts i) = (vs i, ss (i + 1)) ∧ vs i ≠ .null ∧
      (ss (i + 1)).errorIndicator = false) →
    (expectToken sep (ss n) = (.null, s') ∨
      ∃ (c : Token) (t : PS), expectToken sep (ss n) = (.tok c, t) ∧ callRule f rr t = (.null, s')) →
    callRule (f + n + 12) g p =
      (.seq (k0 :: (List.range n).map vs), { s' with mark := (ss n).mark }.leave.leave)) ∧
  (∀ (n : Nat) (s1 : PS), callRule (f + n + 7) rr p.enter = (.null, s1) →
    callRule (f + n + 12) g p = (.null, { s1 with mark := p.mark }.leave))

theorem gatherSepTok_of {sep g lp rr : Nat}
    (hg : ruleOf g = Rule.mk (ruleOf g).name .gather false false false false false
      [Alt.mk [.call (.rule rr), .call (.rule lp)] none 2 false false])
    (hl : ruleOf lp = Rule.mk (ruleOf lp).name .loop0 false false false false false
      [Alt.mk [.call (.tok sep), .call (.rule rr)] (some (.var 1)) 2 false false]) :
    GatherSepTok sep g lp rr := by
  intro f p he hlv
  have hl1 : p.level ≠ MAXSTACK := by omega
  have he' : p.enter.errorIndicator = false := he
  have hG : ∀ k, callRule (k + 2) g p =
      let a := runAlts k [Alt.mk [.call (.rule rr), .call (.rule lp)] none 2 false false] true
        p.mark (0, 0) p.enter
      (a.1.getD .null, a.2.leave) := by
    intro k
    rw [callRule_gather (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg]) (by rw [hg]) he hl1, hg]
  refine ⟨fun k0 s1 n vs ss ts s' h1 hk h1e h1l hs0 hstep hlast => ?_, fun n s1 h1 => ?_⟩
  · rw [show f + n + 12 = (f + n + 10) + 2 from rfl, hG]
    have hloop := runLoop_sep sep rr ((ruleOf lp).alts.headD default) (by rw [hl]; rfl) (by rw [hl]; rfl)
      (by rw [hl]; rfl) (0, 0) n f vs ss ts s' [] hstep hlast
    rw [hs0] at hloop
    have hle : s1.level ≠ MAXSTACK := by omega
    have hlp : callRule (f + n + 6) lp s1 =
        (.seq ((List.range n).map vs), { s' with mark := (ss n).mark }.leave) := by
      have e1 : callRule (f + n + 6) lp s1 = ruleBody (f + n + 5) lp (ruleOf lp) s1 := by
        rw [show f + n + 6 = (f + n + 5) + 1 from rfl]
        simp only [callRule, show (ruleOf lp).leftRec = false by rw [hl],
          show (ruleOf lp).withoutInvalid = false by rw [hl], Bool.false_and, Bool.false_eq_true,
          ↓reduceIte]
      have hp : rulePrologue lp (ruleOf lp) s1 = (.inr (s1.mark, (0, 0)), s1.enter) := by
        simp only [rulePrologue, addLevel_ok s1 hle, show s1.enter.errorIndicator = false from h1e,
          show (ruleOf lp).memo = false by rw [hl], Bool.false_eq_true, ↓reduceIte, ruleStart,
          show (ruleOf lp).extra = false by rw [hl]]
        rfl
      rw [e1, show f + n + 5 = (f + n + 4) + 1 from rfl]
      simp only [ruleBody, hp, show (ruleOf lp).kind = .loop0 by rw [hl],
        show s1.enter.errorIndicator = false from h1e, Bool.false_eq_true, ↓reduceIte]
      rw [show s1.mark = s1.enter.mark from rfl, hloop]
      simp only [loopFinish, Bool.not_true, Bool.false_eq_true, ↓reduceIte, retLevel_eq,
        show (ruleOf lp).kind = .loop0 by rw [hl]]
      simp
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hk, items_call (by rw [call_rule, hlp]) (by simp),
        items_nil])]
    simp only [altResult]
    rfl
  · rw [show f + n + 12 = (f + n + 10) + 2 from rfl, hG]
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `GatherSepTok` with the separator `,` (12), the separator of every gather but `simple_stmts`'
`';'.simple_stmt+`. -/
def GatherSep (g lp rr : Nat) : Prop := GatherSepTok 12 g lp rr

theorem gatherSep_of {g lp rr : Nat}
    (hg : ruleOf g = Rule.mk (ruleOf g).name .gather false false false false false
      [Alt.mk [.call (.rule rr), .call (.rule lp)] none 2 false false])
    (hl : ruleOf lp = Rule.mk (ruleOf lp).name .loop0 false false false false false
      [Alt.mk [.call (.tok 12), .call (.rule rr)] (some (.var 1)) 2 false false]) :
    GatherSep g lp rr := gatherSepTok_of hg hl

end PyLean.PyGrammar.Peg
