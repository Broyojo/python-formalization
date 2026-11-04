import PyLean.PyGrammar.Peg.Rules.Args2

/-! The comparison operators (`Grammar/python.gram:793-816`), rule by rule:
`compare_op_bitwise_or_pair` and the ten `*_bitwise_or` rules, with the `!=` / `<>` check of
`from __future__ import barry_as_FLUFL`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Ordered choice with `invalid_` alternatives -/

/-- An alternative that is one rule call with the default action, guarded by
`call_invalid_rules` when `gi`. -/
def choiceAltG (x : Nat × Bool) : Alt :=
  { items := [.call (.rule x.1)], action := none, nvars := 1, guardInvalid := x.2, extra := false }

/-- `choiceRes` where an alternative flagged `true` is an `invalid_` one: skipped in the first pass
(the pass flag of the state reached), tried in the second. -/
def choiceResG (g m : Nat) : List (Nat × Bool) → PS → Option Ast × PS
  | [], s => (some .null, s)
  | (r, gi) :: rest, s =>
    if gi && !s.callInvalidRules then choiceResG g m rest s else
    if s.errorIndicator then (none, s) else
    let c := callRule (g + rest.length) r s
    if nonNull c.1 then (some c.1, c.2) else choiceResG g m rest { c.2 with mark := m }

theorem choiceG_run (g m : Nat) (st : Int × Int) :
    ∀ (rs : List (Nat × Bool)) (s : PS), runAlts (g + rs.length + 2) (rs.map choiceAltG) false m st s =
      choiceResG g m rs s
  | [], s => by simp only [List.map, List.length, Nat.add_zero]; rw [alts_nil]; rfl
  | (r, gi) :: rest, s => by
    have ih := choiceG_run g m st rest
    simp only [List.map, List.length]
    rw [show g + (rest.length + 1) + 2 = (g + rest.length + 2) + 1 from by omega]
    by_cases hg : (gi && !s.callInvalidRules) = true
    · rw [alts_skip (by simpa [choiceAltG] using hg), ih]
      simp [choiceResG, hg]
    · have hg' : (gi && !s.callInvalidRules) = false := by simpa using hg
      cases he : s.errorIndicator with
      | true =>
        rw [alts_err (by simpa [choiceAltG] using hg') he]
        simp [choiceResG, hg', he]
      | false =>
        generalize hc : callRule (g + rest.length) r s = c
        obtain ⟨v, s'⟩ := c
        cases v with
        | null =>
          rw [alts_fail (by simpa [choiceAltG] using hg') he (by
            show runItems (g + rest.length + 1 + 1) [.call (.rule r)] #[] false s = _
            rw [items_call_null (by rw [call_rule, hc])]), ih]
          simp [choiceResG, hg', he, hc, nonNull]
        | _ =>
          rw [alts_ok (by simpa [choiceAltG] using hg') he (by
            show runItems (g + rest.length + 1 + 1) [.call (.rule r)] #[] false s = _
            rw [items_call (by rw [call_rule, hc]) (by simp), items_nil]), altResult_none1 rfl rfl]
          simp [choiceResG, hg', he, hc, nonNull]

/-- `compare_op_bitwise_or_pair` (`Grammar/python.gram:793-804`):
```
    | eq_bitwise_or | noteq_bitwise_or | lte_bitwise_or | invalid_noteq | lt_bitwise_or
    | gte_bitwise_or | gt_bitwise_or | notin_bitwise_or | in_bitwise_or | isnot_bitwise_or
    | is_bitwise_or
```
The ordered choice (`choiceResG`) of those rules (125, 126, 127, 277, 128, 129, 130, 131, 132,
133, 134), from the start mark, `invalid_noteq` (277) only in the second pass and before
`lt_bitwise_or` (so `1 <> 2` is diagnosed before `<` is tried). -/
def CompareOpPair : Prop := ∀ (g : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (g + 15) 124 p =
    let a := choiceResG g p.mark [(125, false), (126, false), (127, false), (277, true), (128, false),
      (129, false), (130, false), (131, false), (132, false), (133, false), (134, false)] p.enter
    (a.1.getD .null, a.2.leave)

theorem compareOpPair_proven : CompareOpPair := by
  intro g p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  have := choiceG_run g p.mark (0, 0) [(125, false), (126, false), (127, false), (277, true),
    (128, false), (129, false), (130, false), (131, false), (132, false), (133, false), (134, false)]
    p.enter
  simp only [List.length, List.map, choiceAltG] at this
  simp only [show ruleOf 124 = r124 from rfl, r124]
  rw [← this]

/-! ### `op bitwise_or` -/

/-- `x: tok a=bitwise_or { _PyPegen_cmpop_expr_pair(p, Op, a) }` (no `EXTRA`): at `tk`, a
`bitwise_or` (135) gives the `CmpopExprPair` record `(Op, a)`; at another token, or without a
`bitwise_or`, `NULL` with the mark back. -/
def CmpPair (id tk : Nat) (op : Ctor) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ tk → callRule (f + 6) id p = (.null, q.leave)) ∧
  (t.type = tk → ∀ (b : Ast) (s : PS), callRule f 135 { q with mark := p.mark + 1 } = (b, s) →
    b ≠ .null → s.errorIndicator = false →
    callRule (f + 6) id p = (rec_ .PCmpopExprPair [opNode op, b], s.leave)) ∧
  (t.type = tk → ∀ (s : PS), callRule f 135 { q with mark := p.mark + 1 } = (.null, s) →
    callRule (f + 6) id p = (.null, { s with mark := p.mark }.leave))

theorem cmpPair_of {id tk : Nat} {op : Ctor}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.tok tk), .call (.rule 135)] (some (.call .cmpop_expr_pair [.ctor op, .var 1]))
        2 false false]) :
    CmpPair id tk op := by
  intro f p q h
  obtain ⟨-, -, -, -, hm, -, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) h.ei h.level, hr]
  refine ⟨fun ht => ?_, fun ht b s h1 hb h1e => ?_, fun ht s h1 => ?_⟩
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [call_tok, expect_entered h, ite_f ht])), hq,
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h1e, rec_, opNode]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `x: tk1 tk2 a=bitwise_or { _PyPegen_cmpop_expr_pair(p, Op, a) }` (`not in`, `is not`): the two
tokens and a `bitwise_or` give `(Op, a)`; otherwise `NULL` with the mark back. -/
def CmpPair2 (id tk1 tk2 : Nat) (op : Ctor) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (b : Ast) (c d : Token) (s1 s2 s3 : PS), expectToken tk1 p.enter = (.tok c, s1) →
    expectToken tk2 s1 = (.tok d, s2) → callRule f 135 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 7) id p = (rec_ .PCmpopExprPair [opNode op, b], s3.leave)) ∧
  (∀ (s : PS), (expectToken tk1 p.enter = (.null, s) ∨
      (∃ c s1, expectToken tk1 p.enter = (.tok c, s1) ∧ expectToken tk2 s1 = (.null, s)) ∨
      (∃ c d s1 s2, expectToken tk1 p.enter = (.tok c, s1) ∧ expectToken tk2 s1 = (.tok d, s2) ∧
        callRule f 135 s2 = (.null, s))) →
    callRule (f + 7) id p = (.null, { s with mark := p.mark }.leave))

theorem cmpPair2_of {id tk1 tk2 : Nat} {op : Ctor}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.tok tk1), .call (.tok tk2), .call (.rule 135)]
        (some (.call .cmpop_expr_pair [.ctor op, .var 2])) 3 false false]) :
    CmpPair2 id tk1 tk2 op := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  refine ⟨fun b c d s1 s2 s3 h1 h2 h3 hb h3e => ?_, fun s hs => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_, opNode]
  · have hA : runItems (f + 4) [.call (.tok tk1), .call (.tok tk2), .call (.rule 135)] #[] false p.enter =
        ((none, false), s) := by
      rcases hs with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, d, s1, s2, h1, h2, h3⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_tok, h2])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
          items_call_null (by rw [call_rule, h3])]
    rw [alts_fail (by rfl) he' hA, alts_nil]
    rfl

def EqBitwiseOr : Prop := CmpPair 125 27 .Eq
theorem eqBitwiseOr_proven : EqBitwiseOr := cmpPair_of rfl
def LteBitwiseOr : Prop := CmpPair 127 29 .LtE
theorem lteBitwiseOr_proven : LteBitwiseOr := cmpPair_of rfl
def LtBitwiseOr : Prop := CmpPair 128 20 .Lt
theorem ltBitwiseOr_proven : LtBitwiseOr := cmpPair_of rfl
def GteBitwiseOr : Prop := CmpPair 129 30 .GtE
theorem gteBitwiseOr_proven : GteBitwiseOr := cmpPair_of rfl
def GtBitwiseOr : Prop := CmpPair 130 21 .Gt
theorem gtBitwiseOr_proven : GtBitwiseOr := cmpPair_of rfl
def InBitwiseOr : Prop := CmpPair 132 713 .In
theorem inBitwiseOr_proven : InBitwiseOr := cmpPair_of rfl
def IsBitwiseOr : Prop := CmpPair 134 597 .Is
theorem isBitwiseOr_proven : IsBitwiseOr := cmpPair_of rfl
/-- `not` (721) `in` (713). -/
def NotinBitwiseOr : Prop := CmpPair2 131 721 713 .NotIn
theorem notinBitwiseOr_proven : NotinBitwiseOr := cmpPair2_of rfl
/-- `is` (597) `not` (721). -/
def IsnotBitwiseOr : Prop := CmpPair2 133 597 721 .IsNot
theorem isnotBitwiseOr_proven : IsnotBitwiseOr := cmpPair2_of rfl

/-! ### `noteq_bitwise_or` and the `!=` / `<>` check -/

/-- The message `_PyPegen_check_barry_as_flufl` raises (`Parser/action_helpers.c:940`). -/
abbrev barryMsg : String := "with Barry as BDFL, use '<>' instead of '!='"

/-- `_tmp_64: tok='!=' { _PyPegen_check_barry_as_flufl(p, tok) ? NULL : tok }`, the operator of
`noteq_bitwise_or` (`Grammar/python.gram:807-808`). The tokenizer gives `NOTEQUAL` (28) for both
`!=` and `<>`. Without `barry_as_FLUFL`, `!=` is the result and `<>` gives `NULL` (no error);
with it, `<>` is the result and `!=` raises "with Barry as BDFL, use '<>' instead of '!='" and
gives `NULL` with `error_indicator` set (`_PyPegen_check_barry_as_flufl`,
`Parser/action_helpers.c:934-948`, returns -1 after `RAISE_SYNTAX_ERROR`, so the action's `NULL`
is an error return and `compare_op_bitwise_or_pair` tries no further operator); at another token
`NULL` with the mark back. -/
def Tmp64 : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 : PS := { q with mark := p.mark + 1 }
  (t.type ≠ 28 → callRule (f + 5) 341 p = (.null, q.leave)) ∧
  (t.type = 28 → q.flagBarry = false → t.bytes = [33, 61] →
    callRule (f + 5) 341 p = (.tok t, s1.leave)) ∧
  (t.type = 28 → q.flagBarry = false → t.bytes ≠ [33, 61] → q.errOccurred = false →
    callRule (f + 5) 341 p = (.null, s1.leave)) ∧
  (t.type = 28 → q.flagBarry = true → t.bytes = [60, 62] →
    callRule (f + 5) 341 p = (.tok t, s1.leave)) ∧
  (t.type = 28 → q.flagBarry = true → t.bytes ≠ [60, 62] →
    (callRule (f + 5) 341 p).1 = .null ∧
    (callRule (f + 5) 341 p).2.errorIndicator = true ∧
    (callRule (f + 5) 341 p).2.tok = (raiseError0 "SyntaxError" barryMsg s1).2.tok)

theorem tmp64_proven : Tmp64 := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have he1 : ({ q with mark := p.mark + 1 } : PS).errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 341 = r341 from rfl, r341]
  refine ⟨fun ht => ?_, fun ht hb hs => ?_, fun ht hb hs ho => ?_, fun ht hb hs => ?_,
    fun ht hb hs => ?_⟩
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [call_tok, expect_entered h, ite_f ht])), hq,
      alts_nil]
    rfl
  all_goals
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp), items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, checkBarry,
      get, getThe, MonadStateOf.get, StateT.get]
  · simp [hb, hs, truth, nonNull, he1, StateT.pure, pure, StateT.bind, bind]
  · have ho' : q.tok.err.isSome = false := ho
    simp [hb, hs, truth, nonNull, he1, ho', PS.errOccurred, StateT.pure, pure, StateT.bind, bind]
  · simp [hb, hs, truth, nonNull, he1, StateT.pure, pure, StateT.bind, bind]
  · have hs2 : ((q.tokenAt p.mark).bytes != [60, 62]) = true := by simpa using hs
    simp [hb, hs, hs2, StateT.pure, pure, StateT.bind, bind]
    have hr := (raises_raiseError0 "SyntaxError" barryMsg).2
      { q with mark := p.mark + 1, flagBarry := true }
    generalize raiseError0 "SyntaxError" "with Barry as BDFL, use '<>' instead of '!='"
      { q with mark := p.mark + 1, flagBarry := true } = r at hr
    obtain ⟨u, s'⟩ := r
    simp only at hr
    simp only [truth, nonNull]
    split <;> simp [PS.leave, StateT.pure, pure, hr] <;> split <;> simp_all [StateT.pure] <;> (rename_i hx _; exact hx rfl)

/-- `noteq_bitwise_or: (tok='!=' { ... }) a=bitwise_or { _PyPegen_cmpop_expr_pair(p, NotEq, a) }`
(`Grammar/python.gram:807-808`): the operator group (`_tmp_64`, 341) and a `bitwise_or` (135) give
`(NotEq, a)`; without either `NULL` with the mark back. -/
def NoteqBitwiseOr : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (o b : Ast) (s1 s2 : PS), callRule (f + 2) 341 p.enter = (o, s1) → o ≠ .null →
    callRule (f + 1) 135 s1 = (b, s2) → b ≠ .null → s2.errorIndicator = false →
    callRule (f + 7) 126 p = (rec_ .PCmpopExprPair [opNode .NotEq, b], s2.leave)) ∧
  (∀ (s : PS), (callRule (f + 2) 341 p.enter = (.null, s) ∨
      ∃ o s1, callRule (f + 2) 341 p.enter = (o, s1) ∧ o ≠ .null ∧ callRule (f + 1) 135 s1 = (.null, s)) →
    callRule (f + 7) 126 p = (.null, { s with mark := p.mark }.leave))

theorem noteqBitwiseOr_proven : NoteqBitwiseOr := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 126 = r126 from rfl, r126]
  refine ⟨fun o b s1 s2 h1 ho h2 hb h2e => ?_, fun s hs => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ho, items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h2e, rec_, opNode]
  · have hA : runItems (f + 4) [.call (.rule 341), .call (.rule 135)] #[] false p.enter =
        ((none, false), s) := by
      rcases hs with h1 | ⟨o, s1, h1, ho, h2⟩
      · rw [items_call_null (by rw [call_rule, h1])]
      · rw [items_call (by rw [call_rule, h1]) ho, items_call_null (by rw [call_rule, h2])]
    rw [alts_fail (by rfl) he' hA, alts_nil]
    rfl

def NoteqBitwiseOrRule : Prop := NoteqBitwiseOr ∧ Tmp64
theorem noteqBitwiseOrRule_proven : NoteqBitwiseOrRule := ⟨noteqBitwiseOr_proven, tmp64_proven⟩

end PyLean.PyGrammar.Peg
