import PyLean.PyGrammar.Peg.Rules.Patterns4

/-! `attr` and `name_or_attr` (the left-recursive dotted names of value and class patterns),
`as_pattern` and `case_block` (`Grammar/python.gram:497-591`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- Entry of a rule function that is in a left-recursive group but not its leader (no memo, no
`EXTRA`): no seed loop of its own, so as `callRule_plain`. -/
theorem callRule_lrPlain {f id : Nat} {p : PS}
    (h1 : (ruleOf id).leftRec = true) (h1' : (ruleOf id).leader = false)
    (h2 : (ruleOf id).withoutInvalid = false)
    (h3 : (ruleOf id).memo = false) (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = false)
    (he : p.errorIndicator = false) (hl : p.level ≠ MAXSTACK) :
    callRule (f + 2) id p =
      let a := runAlts f (ruleOf id).alts false p.mark (0, 0) p.enter
      (a.1.getD .null, a.2.leave) := by
  have he' : p.enter.errorIndicator = false := he
  have hp : rulePrologue id (ruleOf id) p = (.inr (p.mark, (0, 0)), p.enter) := by
    simp only [rulePrologue, addLevel_ok p hl, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5]
    rfl
  simp only [callRule, h1, h1', h2, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, h4, retLevel_eq]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all

/-- `name_or_attr: attr | NAME` (`Grammar/python.gram:589-591`), called inside a round of `attr`
whose seed `v` (ending at `e`) is in the memo at the mark: the call of `attr` returns the seed
(`_PyPegen_is_memoized`), so with a seed the result is the seed, resuming at its end; with none
(the first round), the `NAME` under the mark, `NULL` with the mark back without one. -/
def NameOrAttr : Prop := ∀ (g : Nat) (S : PS) (v : Ast) (e : Nat),
  S.errorIndicator = false → S.level + 1 < MAXSTACK → S.mark < S.fill →
  (S.memo.getD S.mark []).find? (fun x => x.1 == 1085) = some (1085, v, e) →
  (v ≠ .null → callRule (g + 6) 86 S = (v, { S with mark := e })) ∧
  (v = .null → ∀ (n : Ast) (s1 : PS), nameToken S.enter = (n, s1) → n ≠ .null →
    callRule (g + 6) 86 S = (n, s1.leave)) ∧
  (v = .null → ∀ (s1 : PS), nameToken S.enter = (.null, s1) →
    callRule (g + 6) 86 S = (.null, { s1 with mark := S.mark }.leave))

theorem nameOrAttr_proven : NameOrAttr := by
  intro g S v e he hlv hlt hf
  have hl : S.level ≠ MAXSTACK := by omega
  have he' : S.enter.errorIndicator = false := he
  have hit : runCall (g + 2) (.rule 85) S.enter = (v, { S.enter with mark := e }) := by
    rw [call_rule]
    exact callRule_leader_hit rfl rfl (show S.level + 1 ≠ MAXSTACK by omega) hlt hf
  rw [callRule_lrPlain rfl rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 86 = r86 from rfl, r86]
  refine ⟨fun hv => ?_, fun hv n s1 h1 hn => ?_, fun hv s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call hit hv, items_nil]),
      altResult_none1 rfl rfl]
    exact congrArg _ (enter_leave_mark S e)
  · subst hv
    have hS : ({ ({ S.enter with mark := e } : PS) with mark := S.mark } : PS) = S.enter := rfl
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null hit]), hS,
      alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_name, h1]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hv
    have hS : ({ ({ S.enter with mark := e } : PS) with mark := S.mark } : PS) = S.enter := rfl
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null hit]), hS,
      alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl

/-- One round of `attr_raw` (`Grammar/python.gram:585-587`):
```
    | value=name_or_attr '.' attr=NAME {
        _PyAST_Attribute(value, attr->v.Name.id, Load, EXTRA) }
```
run from a state `σ` at the start mark whose memo holds seed `v` for `attr`, ending at `e`: with a
seed, `name_or_attr` gives it back (`NameOrAttr`) and `.` NAME after it give
`Attribute(v, NAME.id, Load)`, so `a.b.c` groups as `(a.b).c`; in the first round (no seed) the
`NAME` under the mark takes the seed's place; without the `.` (or the first `NAME`), `NULL` with
the mark back, which ends the seed loop. -/
def AttrStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 2 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1085) = some (1085, v, e) →
  let t := σ.tokenAt σ.mark
  (v ≠ .null → ∀ (b : Ast) (c : Token) (s2 s3 : PS),
    expectToken 23 { σ.enter with mark := e } = (.tok c, s2) → nameToken s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false →
    ruleBody (f + 10) 85 (ruleOf 85) σ =
      (mkAt .Attribute [v, fieldOf b "id", opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (v ≠ .null → ∀ (s2 : PS), expectToken 23 { σ.enter with mark := e } = (.null, s2) →
    ruleBody (f + 10) 85 (ruleOf 85) σ = (.null, { s2 with mark := σ.mark }.leave)) ∧
  (v = .null → ∀ (n b : Ast) (c : Token) (s1 s2 s3 : PS), nameToken σ.enter.enter = (n, s1) →
    n ≠ .null → expectToken 23 s1.leave = (.tok c, s2) → nameToken s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false →
    ruleBody (f + 10) 85 (ruleOf 85) σ =
      (mkAt .Attribute [n, fieldOf b "id", opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (v = .null → ∀ (n : Ast) (s1 s2 : PS), nameToken σ.enter.enter = (n, s1) → n ≠ .null →
    expectToken 23 s1.leave = (.null, s2) →
    ruleBody (f + 10) 85 (ruleOf 85) σ = (.null, { s2 with mark := σ.mark }.leave))

theorem attrStep_proven : AttrStep := by
  intro f σ v e he hlv hlt hf
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hN := nameOrAttr_proven f σ.enter v e he (show σ.level + 1 + 1 < MAXSTACK by omega) hlt hf
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 85 = r85 from rfl, r85]
  refine ⟨fun hv b c s2 s3 h2 h3 hb h3e => ?_, fun hv s2 h2 => ?_,
    fun hv n b c s1 s2 s3 h1 hn h2 h3 hb h3e => ?_, fun hv n s1 s2 h1 hn h2 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, hN.1 hv]) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, hN.1 hv]) hv, items_call_null (by rw [call_tok, h2])]),
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, hN.2.1 hv n s1 h1 hn]) hn,
        items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_name, h3]) hb,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, hN.2.1 hv n s1 h1 hn]) hn,
        items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl

/-- `attr`: one round (`AttrStep`, with `name_or_attr` inside it) and the seed loop. -/
def AttrRule : Prop := AttrStep ∧ NameOrAttr ∧ LeaderLoop 85
theorem attrRule_proven : AttrRule := ⟨attrStep_proven, nameOrAttr_proven, leaderLoop_of rfl rfl⟩

/-! ### `as_pattern` -/

/-- The first alternative of `as_pattern`, `or_pattern 'as' pattern_capture_target`, fails from
`q`, ending in `s`. -/
def AsAltFails (f : Nat) (q s : PS) : Prop :=
  callRule (f + 3) 72 q = (.null, s) ∨
  (∃ (pt : Ast) (s1 : PS), callRule (f + 3) 72 q = (pt, s1) ∧ pt ≠ .null ∧
    expectToken 698 s1 = (.null, s)) ∨
  (∃ (pt : Ast) (c : Token) (s1 s2 : PS), callRule (f + 3) 72 q = (pt, s1) ∧ pt ≠ .null ∧
    expectToken 698 s1 = (.tok c, s2) ∧ callRule (f + 1) 82 s2 = (.null, s))

theorem asAlt_items {f : Nat} {q s : PS} (h : AsAltFails f q s) :
    runItems (f + 5) [(.call (.rule 72)), (.call (.tok 698)), (.call (.rule 82))] #[] false q =
      ((none, false), s) := by
  rcases h with h | ⟨pt, s1, h1, hp, h2⟩ | ⟨pt, c, s1, s2, h1, hp, h2, h3⟩
  · rw [items_call_null (by rw [call_rule, h])]
  · rw [items_call (by rw [call_rule, h1]) hp, items_call_null (by rw [call_tok, h2])]
  · rw [items_call (by rw [call_rule, h1]) hp, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]

/-- `as_pattern` (`Grammar/python.gram:513-516`):
```
    | pattern=or_pattern 'as' target=pattern_capture_target {
        _PyAST_MatchAs(pattern, target->v.Name.id, EXTRA) }
    | invalid_as_pattern
```
An `or_pattern` (72), `as` (698) and a `pattern_capture_target` (82) give `MatchAs(pattern,
name)`; once that fails, in the first pass `NULL` with the mark back, in the second pass the
result of `invalid_as_pattern` (252) from the start mark (which raises for `case 1 as _:` and
`case 1 as y.z:`). -/
def AsPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (pt tg : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 3) 72 q = (pt, s1) → pt ≠ .null →
    expectToken 698 s1 = (.tok c, s2) → callRule (f + 1) 82 s2 = (tg, s3) → tg ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 8) 71 p = (mkAt .MatchAs [pt, fieldOf tg "id"] (extraLoc t s3), s3.leave)) ∧
  (∀ (s : PS), AsAltFails f q s → s.callInvalidRules = false →
    callRule (f + 8) 71 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (v : Ast) (s s' : PS), AsAltFails f q s → s.errorIndicator = false →
    s.callInvalidRules = true → callRule (f + 2) 252 { s with mark := p.mark } = (v, s') →
    v ≠ .null → callRule (f + 8) 71 p = (v, s'.leave)) ∧
  (∀ (s s' : PS), AsAltFails f q s → s.errorIndicator = false →
    s.callInvalidRules = true → callRule (f + 2) 252 { s with mark := p.mark } = (.null, s') →
    callRule (f + 8) 71 p = (.null, { s' with mark := p.mark }.leave))

theorem asPattern_proven : AsPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 71 = r71 from rfl, r71]
  refine ⟨fun pt tg c s1 s2 s3 h1 hp h2 h3 ht h3e => ?_, fun s h0 hi => ?_,
    fun v s s' h0 h0e hi h1 hv => ?_, fun s s' h0 h0e hi h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hp, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ht, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (by exact asAlt_items h0), alts_skip (by simp [hi]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by exact asAlt_items h0),
      alts_ok (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h0e)
        (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by exact asAlt_items h0),
      alts_fail (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h0e)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-! ### `case_block` -/

/-- `case_block` (`Grammar/python.gram:497-500`):
```
    | invalid_case_block
    | "case" pattern=patterns guard=guard? ':' body=block {
        _PyAST_match_case(pattern, guard, body, p->arena) }
```
No `EXTRA`. In the first pass, the soft keyword `case`, `patterns` (69), the optional `guard` (68),
`:` (11) and `block` (33) give `match_case(pattern, guard, body)` (`guard` `NULL` without one);
without `case`, `NULL` with the mark back. In the second pass `invalid_case_block` (251) runs
first: its error ends the rule; its `NULL` with no error leads to the same alternative from the
start mark. -/
def CaseBlock : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (p.callInvalidRules = false → ∀ (k pt g b : Ast) (c : Token) (s1 s2 s3 s4 s5 : PS),
    expectSoftKeyword [99, 97, 115, 101] p.enter = (k, s1) → k ≠ .null → callRule (f + 3) 69 s1 = (pt, s2) →
    pt ≠ .null → callRule (f + 2) 68 s2 = (g, s3) → s3.errorIndicator = false →
    expectToken 11 s3 = (.tok c, s4) → callRule f 33 s4 = (b, s5) → b ≠ .null →
    s5.errorIndicator = false →
    callRule (f + 10) 67 p = (mkAst .match_case_ [pt, g, b], s5.leave)) ∧
  (p.callInvalidRules = false → ∀ (s1 : PS), expectSoftKeyword [99, 97, 115, 101] p.enter = (.null, s1) →
    callRule (f + 10) 67 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 5) 251 p.enter = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 10) 67 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (k pt g b : Ast) (c : Token) (s0 s1 s2 s3 s4 s5 : PS),
    callRule (f + 5) 251 p.enter = (.null, s0) → s0.errorIndicator = false →
    expectSoftKeyword [99, 97, 115, 101] { s0 with mark := p.mark } = (k, s1) → k ≠ .null →
    callRule (f + 3) 69 s1 = (pt, s2) → pt ≠ .null → callRule (f + 2) 68 s2 = (g, s3) →
    s3.errorIndicator = false → expectToken 11 s3 = (.tok c, s4) → callRule f 33 s4 = (b, s5) →
    b ≠ .null → s5.errorIndicator = false →
    callRule (f + 10) 67 p = (mkAst .match_case_ [pt, g, b], s5.leave))

theorem caseBlock_proven : CaseBlock := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 67 = r67 from rfl, r67]
  have fin : ∀ (pt g b c k : Ast) (s5 : PS), s5.errorIndicator = false → pt ≠ .null → b ≠ .null →
      (altResult (Alt.mk [(.call (.softKw [99, 97, 115, 101])), (.call (.rule 69)),
        (.opt (.rule 68)), (.call (.tok 11)), (.call (.rule 33))]
        (some (.mk .match_case_ [(.var 1), (.var 2), (.var 4)])) 5 false false) false
        (((((#[] : Array Ast).push k).push pt).push g).push c |>.push b) (0, 0) s5) =
        (some (mkAst .match_case_ [pt, g, b]), s5) := by
    intro pt g b c k s5 h5e hp hb
    rw [altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h5e]
  refine ⟨fun hi k pt g b c s1 s2 s3 s4 s5 h1 hk h2 hp h3 h3e h4 h5 hb h5e => ?_,
    fun hi s1 h1 => ?_, fun hi s0 h0 h0e => ?_,
    fun hi k pt g b c s0 s1 s2 s3 s4 s5 h0 h0e h1 hk h2 hp h3 h3e h4 h5 hb h5e => ?_⟩
  · rw [alts_skip (by simp [hi, PS.enter]), alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_softKw, h1]) hk, items_call (by rw [call_rule, h2]) hp,
        items_opt (by rw [call_rule, h3]) h3e, items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) hb, items_nil]), fin pt g b (.tok c) k s5 h5e hp hb]
    rfl
  · rw [alts_skip (by simp [hi, PS.enter]), alts_fail (by rfl) he' (by
      dsimp only; rw [items_call_null (by rw [call_softKw, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by simp [hi, PS.enter]) he' (by
      dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · rw [alts_fail (by simp [hi, PS.enter]) he' (by
      dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call (by rw [call_softKw, h1]) hk, items_call (by rw [call_rule, h2]) hp,
        items_opt (by rw [call_rule, h3]) h3e, items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) hb, items_nil]), fin pt g b (.tok c) k s5 h5e hp hb]
    rfl

end PyLean.PyGrammar.Peg
