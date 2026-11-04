import PyLean.PyGrammar.Peg.Rules.AsTarget2

/-! The literal pattern rules under `closed_pattern` (`Grammar/python.gram:532-570`), rule by rule:
`literal_pattern`, `literal_expr`, `complex_number`, `signed_real_number`, `real_number`,
`imaginary_number`, with the lookahead group `('+' | '-')` (`_tmp_41`). -/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem PS.mark_mark (s : PS) (a b : Nat) :
    ({ ({ s with mark := a } : PS) with mark := b } : PS) = { s with mark := b } := rfl

/-- `_tmp_41: '+' | '-'` (14, 15): that token with the mark past it; at any other token `NULL`
with the state the entry read left. -/
def Tmp41 : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  ((t.type = 14 ∨ t.type = 15) → callRule (f + 6) 318 p = (.tok t, { q with mark := p.mark + 1 }.leave)) ∧
  (t.type ≠ 14 → t.type ≠ 15 → callRule (f + 6) 318 p = (.null, q.leave))

theorem tmp41_proven : Tmp41 := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  have e1 : ∀ ty g, runCall (g + 1) (.tok ty) p.enter = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expect_entered h]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 318 = r318 from rfl, r318]
  refine ⟨fun ht => ?_, fun h14 h15 => ?_⟩
  · rcases ht with ht | ht
    · rw [alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [e1, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f (by omega)])), hq,
        alts_ok (by rfl) he (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f h14])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f h15])), hq, alts_nil]
    rfl

/-- The first alternative of `literal_pattern` and `literal_expr`, `signed_number !('+' | '-')`,
fails with no cut, ending in `s`: no `signed_number` (77), or one followed by `+` or `-`
(`_tmp_41`, 318, matching), as in `1 + 2j`. -/
def SignedNumAltFails (f : Nat) (q s : PS) : Prop :=
  callRule (f + 5) 77 q = (.null, s) ∨
  (∃ (v x : Ast) (s1 : PS), callRule (f + 5) 77 q = (v, s1) ∧ v ≠ .null ∧
    callRule (f + 4) 318 s1 = (x, s) ∧ nonNull x = true)

theorem SignedNumAltFails.tg {f : Nat} {q s : PS} (h : SignedNumAltFails f q s) : TokGrows q s := by
  rcases h with h | ⟨v, x, s1, h1, -, h2, -⟩
  · exact tg_call h
  · exact (tg_call h1).trans (tg_call h2)

theorem signedNumAlt_items {f : Nat} {q s : PS} (m : Nat) (h : SignedNumAltFails f q s) :
    ∃ s' : PS, runItems (f + 7) [(.call (.rule 77)), (.look false (.rule 318))] #[] false q =
      ((none, false), s') ∧ ({ s' with mark := m } : PS) = { s with mark := m } := by
  rcases h with h | ⟨v, x, s1, h1, hv, h2, hx⟩
  · exact ⟨s, items_call_null (by rw [call_rule, h]), rfl⟩
  · refine ⟨{ s with mark := s1.mark }, ?_, rfl⟩
    rw [items_call (by rw [call_rule, h1]) hv, items_look_fail (by rw [call_rule, h2]) hx]

/-- `literal_pattern` (`Grammar/python.gram:533-540`):
```
    | value=signed_number !('+' | '-') { _PyAST_MatchValue(value, EXTRA) }
    | value=complex_number { _PyAST_MatchValue(value, EXTRA) }
    | value=strings { _PyAST_MatchValue(value, EXTRA) }
    | 'None' { _PyAST_MatchSingleton(Py_None, EXTRA) }
    | 'True' { _PyAST_MatchSingleton(Py_True, EXTRA) }
    | 'False' { _PyAST_MatchSingleton(Py_False, EXTRA) }
```
A `signed_number` not followed by `+`/`-` gives `MatchValue(value)` (so `case -1:` is a value
pattern); once that fails (`SignedNumAltFails`), `complex_number` from the start mark gives
`MatchValue` of the `BinOp` (`case 1 + 2j:`); then `strings`; then, at `None` (628), `True` (627)
or `False` (629), `MatchSingleton` of that constant spanning the keyword; any other token `NULL`
with the mark back. -/
def LiteralPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (v x : Ast) (s1 s2 : PS), callRule (f + 5) 77 q = (v, s1) → v ≠ .null →
    callRule (f + 4) 318 s1 = (x, s2) → nonNull x = false → s2.errorIndicator = false →
    callRule (f + 10) 74 p =
      (mkAt .MatchValue [v] (extraLoc t { s2 with mark := s1.mark }), { s2 with mark := s1.mark }.leave)) ∧
  (∀ (c : Ast) (s1 s2 : PS), SignedNumAltFails f q s1 → s1.errorIndicator = false →
    callRule (f + 4) 76 { s1 with mark := p.mark } = (c, s2) → c ≠ .null → s2.errorIndicator = false →
    callRule (f + 10) 74 p = (mkAt .MatchValue [c] (extraLoc t s2), s2.leave)) ∧
  (∀ (sv : Ast) (s1 s2 s3 : PS), SignedNumAltFails f q s1 → s1.errorIndicator = false →
    callRule (f + 4) 76 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 3) 173 { s2 with mark := p.mark } = (sv, s3) → sv ≠ .null → s3.errorIndicator = false →
    callRule (f + 10) 74 p = (mkAt .MatchValue [sv] (extraLoc t s3), s3.leave)) ∧
  (∀ (s1 s2 s3 : PS), SignedNumAltFails f q s1 → s1.errorIndicator = false →
    callRule (f + 4) 76 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 3) 173 { s2 with mark := p.mark } = (.null, s3) → s3.errorIndicator = false →
    let s : PS := { s3 with mark := p.mark + 1 }
    (t.type = 628 → callRule (f + 10) 74 p =
      (mkAt .MatchSingleton [.const .none] (extraLoc t s), s.leave)) ∧
    (t.type = 627 → callRule (f + 10) 74 p =
      (mkAt .MatchSingleton [.const .true_] (extraLoc t s), s.leave)) ∧
    (t.type = 629 → callRule (f + 10) 74 p =
      (mkAt .MatchSingleton [.const .false_] (extraLoc t s), s.leave)) ∧
    (t.type ≠ 628 → t.type ≠ 627 → t.type ≠ 629 →
      callRule (f + 10) 74 p = (.null, { s3 with mark := p.mark }.leave)))

theorem literalPattern_proven : LiteralPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 74 = r74 from rfl, r74]
  refine ⟨fun v x s1 s2 h1 hv h2 hx h2e => ?_, fun c s1 s2 h1 h1e h2 hc h2e => ?_,
    fun sv s1 s2 s3 h1 h1e h2 h2e h3 hsv h3e => ?_, fun s1 s2 s3 h1 h1e h2 h2e h3 h3e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hv, items_look (by rw [call_rule, h2]) hx, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · obtain ⟨s1', hi1, hs1⟩ := signedNumAlt_items p.mark h1
    rw [alts_fail (by rfl) he (by exact hi1), hs1, alts_ok (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call (by rw [call_rule, h2]) hc, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · obtain ⟨s1', hi1, hs1⟩ := signedNumAlt_items p.mark h1
    rw [alts_fail (by rfl) he (by exact hi1), hs1,
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
      dsimp only; rw [items_call (by rw [call_rule, h3]) hsv, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · have g3 : TokGrows q s3 :=
      h1.tg.trans ((tg_mark (TokGrows.refl _) p.mark).trans (tg_call h2) |>.trans
        ((tg_mark (TokGrows.refl _) p.mark).trans (tg_call h3)))
    have ek : ∀ ty g, runCall (g + 1) (.tok ty) { s3 with mark := p.mark } =
        if (q.tokenAt p.mark).type = ty then
          (.tok (q.tokenAt p.mark), { s3 with mark := p.mark + 1 })
        else (.null, { s3 with mark := p.mark }) := by
      intro ty g
      rw [call_tok, expect_again g3 hlt]
    obtain ⟨s1', hi1, hs1⟩ := signedNumAlt_items p.mark h1
    rw [alts_fail (by rfl) he (by exact hi1), hs1,
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])])]
    refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun h628 h627 h629 => ?_⟩
    · rw [alts_ok (by rfl) (E s3 h3e) (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        Bool.or_false, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h3e]
    · rw [alts_fail (by rfl) (E s3 h3e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark, alts_ok (by rfl) (E s3 h3e) (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        Bool.or_false, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h3e]
    · rw [alts_fail (by rfl) (E s3 h3e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark,
        alts_fail (by rfl) (E s3 h3e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark, alts_ok (by rfl) (E s3 h3e) (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        Bool.or_false, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h3e]
    · rw [alts_fail (by rfl) (E s3 h3e) (items_call_null (by rw [ek, ite_f h628])), PS.mark_mark,
        alts_fail (by rfl) (E s3 h3e) (items_call_null (by rw [ek, ite_f h627])), PS.mark_mark,
        alts_fail (by rfl) (E s3 h3e) (items_call_null (by rw [ek, ite_f h629])), PS.mark_mark,
        alts_nil]
      rfl

/-! ### `literal_expr` -/

/-- The third alternative of `literal_expr`, `&(STRING|FSTRING_START|TSTRING_START) strings`, run
from `s0` (mark `m`), fails with no cut, ending in `s`: the lookahead `_tmp_42` (319) fails, or it
holds and `strings` (173) from the mark gives `NULL`. -/
def StrAltFails (f m : Nat) (s0 s : PS) : Prop :=
  (∃ x : Ast, callRule (f + 3) 319 s0 = (x, s) ∧ nonNull x = false) ∨
  (∃ (x : Ast) (s' : PS), callRule (f + 3) 319 s0 = (x, s') ∧ nonNull x = true ∧
    callRule (f + 2) 173 { s' with mark := m } = (.null, s))

theorem StrAltFails.tg {f m : Nat} {s0 s : PS} (h : StrAltFails f m s0 s) : TokGrows s0 s := by
  rcases h with ⟨x, h, -⟩ | ⟨x, s', h1, -, h2⟩
  · exact tg_call h
  · exact (tg_call h1).trans ((tg_mark (TokGrows.refl _) m).trans (tg_call h2))

theorem strAlt_items {f m : Nat} {s0 s : PS} (hm : s0.mark = m) (h : StrAltFails f m s0 s) :
    ∃ s' : PS, runItems (f + 5) [(.look true (.rule 319)), (.call (.rule 173))] #[] false s0 =
      ((none, false), s') ∧ ({ s' with mark := m } : PS) = { s with mark := m } := by
  rcases h with ⟨x, h, hx⟩ | ⟨x, s', h1, hx, h2⟩
  · refine ⟨{ s with mark := s0.mark }, ?_, rfl⟩
    rw [items_look_fail (by rw [call_rule, h]) (by simpa using hx)]
  · refine ⟨s, ?_, rfl⟩
    rw [items_look (by rw [call_rule, h1]) hx, items_call_null (by rw [call_rule, hm, h2])]

/-- `literal_expr` (`Grammar/python.gram:542-548`):
```
    | signed_number !('+' | '-')
    | complex_number
    | &(STRING|FSTRING_START|TSTRING_START) strings
    | 'None' { _PyAST_Constant(Py_None, NULL, EXTRA) }
    | 'True' { _PyAST_Constant(Py_True, NULL, EXTRA) }
    | 'False' { _PyAST_Constant(Py_False, NULL, EXTRA) }
```
The mapping-key form of `literal_pattern`: the same order, but the first three alternatives give
the expression itself (default action), `strings` only behind the string lookahead, and the
keywords `Constant(None/True/False, NULL)` spanning the keyword; any other token `NULL` with the
mark back. -/
def LiteralExpr : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (v x : Ast) (s1 s2 : PS), callRule (f + 5) 77 q = (v, s1) → v ≠ .null →
    callRule (f + 4) 318 s1 = (x, s2) → nonNull x = false →
    callRule (f + 10) 75 p = (v, { s2 with mark := s1.mark }.leave)) ∧
  (∀ (c : Ast) (s1 s2 : PS), SignedNumAltFails f q s1 → s1.errorIndicator = false →
    callRule (f + 4) 76 { s1 with mark := p.mark } = (c, s2) → c ≠ .null →
    callRule (f + 10) 75 p = (c, s2.leave)) ∧
  (∀ (x sv : Ast) (s1 s2 s3 s4 : PS), SignedNumAltFails f q s1 → s1.errorIndicator = false →
    callRule (f + 4) 76 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 3) 319 { s2 with mark := p.mark } = (x, s3) → nonNull x = true →
    callRule (f + 2) 173 { s3 with mark := p.mark } = (sv, s4) → sv ≠ .null →
    callRule (f + 10) 75 p = (sv, s4.leave)) ∧
  (∀ (s1 s2 s4 : PS), SignedNumAltFails f q s1 → s1.errorIndicator = false →
    callRule (f + 4) 76 { s1 with mark := p.mark } = (.null, s2) → s2.errorIndicator = false →
    StrAltFails f p.mark { s2 with mark := p.mark } s4 → s4.errorIndicator = false →
    let s : PS := { s4 with mark := p.mark + 1 }
    (t.type = 628 → callRule (f + 10) 75 p =
      (mkAt .Constant [.const .none, .null] (extraLoc t s), s.leave)) ∧
    (t.type = 627 → callRule (f + 10) 75 p =
      (mkAt .Constant [.const .true_, .null] (extraLoc t s), s.leave)) ∧
    (t.type = 629 → callRule (f + 10) 75 p =
      (mkAt .Constant [.const .false_, .null] (extraLoc t s), s.leave)) ∧
    (t.type ≠ 628 → t.type ≠ 627 → t.type ≠ 629 →
      callRule (f + 10) 75 p = (.null, { s4 with mark := p.mark }.leave)))

theorem literalExpr_proven : LiteralExpr := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 75 = r75 from rfl, r75]
  refine ⟨fun v x s1 s2 h1 hv h2 hx => ?_, fun c s1 s2 h1 h1e h2 hc => ?_,
    fun x sv s1 s2 s3 s4 h1 h1e h2 h2e h3 hx h4 hsv => ?_, fun s1 s2 s4 h1 h1e h2 h2e h3 h4e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hv, items_look (by rw [call_rule, h2]) hx, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · obtain ⟨s1', hi1, hs1⟩ := signedNumAlt_items p.mark h1
    rw [alts_fail (by rfl) he (by exact hi1), hs1, alts_ok (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call (by rw [call_rule, h2]) hc, items_nil]), altResult_none1 rfl rfl]
    rfl
  · obtain ⟨s1', hi1, hs1⟩ := signedNumAlt_items p.mark h1
    rw [alts_fail (by rfl) he (by exact hi1), hs1,
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_look (by rw [call_rule, h3]) hx, items_call (by rw [call_rule, h4]) hsv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have g4 : TokGrows q s4 :=
      h1.tg.trans ((tg_mark (TokGrows.refl _) p.mark).trans (tg_call h2) |>.trans
        ((tg_mark (TokGrows.refl _) p.mark).trans h3.tg))
    have ek : ∀ ty g, runCall (g + 1) (.tok ty) { s4 with mark := p.mark } =
        if (q.tokenAt p.mark).type = ty then
          (.tok (q.tokenAt p.mark), { s4 with mark := p.mark + 1 })
        else (.null, { s4 with mark := p.mark }) := by
      intro ty g
      rw [call_tok, expect_again g4 hlt]
    obtain ⟨s1', hi1, hs1⟩ := signedNumAlt_items p.mark h1
    obtain ⟨s4', hi4, hs4⟩ := strAlt_items (f := f) rfl h3
    rw [alts_fail (by rfl) he (by exact hi1), hs1,
      alts_fail (by rfl) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by exact hi4), hs4]
    refine ⟨fun ht => ?_, fun ht => ?_, fun ht => ?_, fun h628 h627 h629 => ?_⟩
    · rw [alts_ok (by rfl) (E s4 h4e) (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h4e]
    · rw [alts_fail (by rfl) (E s4 h4e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark, alts_ok (by rfl) (E s4 h4e) (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h4e]
    · rw [alts_fail (by rfl) (E s4 h4e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark,
        alts_fail (by rfl) (E s4 h4e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark, alts_ok (by rfl) (E s4 h4e) (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h4e]
    · rw [alts_fail (by rfl) (E s4 h4e) (items_call_null (by rw [ek, ite_f h628])), PS.mark_mark,
        alts_fail (by rfl) (E s4 h4e) (items_call_null (by rw [ek, ite_f h627])), PS.mark_mark,
        alts_fail (by rfl) (E s4 h4e) (items_call_null (by rw [ek, ite_f h629])), PS.mark_mark,
        alts_nil]
      rfl

/-! ### `complex_number` -/

/-- One alternative `real=signed_real_number op imag=imaginary_number` of `complex_number`, run
from `s0`, fails with no cut, ending in `s`: no `signed_real_number` (78); or no `op`; or no
`imaginary_number` (80), which includes `_PyPegen_ensure_imaginary` raising. -/
def CplxAltFails (g op : Nat) (s0 s : PS) : Prop :=
  callRule (g + 2) 78 s0 = (.null, s) ∨
  (∃ (r : Ast) (s1 : PS), callRule (g + 2) 78 s0 = (r, s1) ∧ r ≠ .null ∧ expectToken op s1 = (.null, s)) ∨
  (∃ (r : Ast) (c : Token) (s1 s2 : PS), callRule (g + 2) 78 s0 = (r, s1) ∧ r ≠ .null ∧
    expectToken op s1 = (.tok c, s2) ∧ callRule g 80 s2 = (.null, s))

theorem cplxAlt_items {g op : Nat} {s0 s : PS} (h : CplxAltFails g op s0 s) :
    runItems (g + 4) [(.call (.rule 78)), (.call (.tok op)), (.call (.rule 80))] #[] false s0 =
      ((none, false), s) := by
  rcases h with h | ⟨r, s1, h1, hr, h2⟩ | ⟨r, c, s1, s2, h1, hr, h2, h3⟩
  · rw [items_call_null (by rw [call_rule, h])]
  · rw [items_call (by rw [call_rule, h1]) hr, items_call_null (by rw [call_tok, h2])]
  · rw [items_call (by rw [call_rule, h1]) hr, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]

/-- `complex_number` (`Grammar/python.gram:550-554`):
```
    | real=signed_real_number '+' imag=imaginary_number {
        _PyAST_BinOp(real, Add, imag, EXTRA) }
    | real=signed_real_number '-' imag=imaginary_number  {
        _PyAST_BinOp(real, Sub, imag, EXTRA) }
```
`signed_real_number` (78), `+` (14) and `imaginary_number` (80) give `BinOp(real, Add, imag)`; once
that alternative fails (`CplxAltFails`) with no error, the same with `-` (15) from the start mark
gives `BinOp(real, Sub, imag)`; an error in the first (as `_PyPegen_ensure_imaginary` raising
for `1 + 2`) ends the rule with `NULL`; both failing gives `NULL` with the mark back. -/
def ComplexNumber : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (r i : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 3) 78 q = (r, s1) → r ≠ .null →
    expectToken 14 s1 = (.tok c, s2) → callRule (f + 1) 80 s2 = (i, s3) → i ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 8) 76 p = (mkAt .BinOp [r, opNode .Add, i] (extraLoc t s3), s3.leave)) ∧
  (∀ (r i : Ast) (c : Token) (s0 s1 s2 s3 : PS), CplxAltFails (f + 1) 14 q s0 →
    s0.errorIndicator = false → callRule (f + 2) 78 { s0 with mark := p.mark } = (r, s1) →
    r ≠ .null → expectToken 15 s1 = (.tok c, s2) → callRule f 80 s2 = (i, s3) → i ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 8) 76 p = (mkAt .BinOp [r, opNode .Sub, i] (extraLoc t s3), s3.leave)) ∧
  (∀ (s0 : PS), CplxAltFails (f + 1) 14 q s0 → s0.errorIndicator = true →
    callRule (f + 8) 76 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (∀ (s0 s : PS), CplxAltFails (f + 1) 14 q s0 → s0.errorIndicator = false →
    CplxAltFails f 15 { s0 with mark := p.mark } s →
    callRule (f + 8) 76 p = (.null, { s with mark := p.mark }.leave))

theorem complexNumber_proven : ComplexNumber := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 76 = r76 from rfl, r76]
  refine ⟨fun r i c s1 s2 s3 h1 hr h2 h3 hi h3e => ?_,
    fun r i c s0 s1 s2 s3 h0 h0e h1 hr h2 h3 hi h3e => ?_, fun s0 h0 h0e => ?_,
    fun s0 s h0 h0e h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hr, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hi, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (by exact cplxAlt_items h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hr, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hi, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (by exact cplxAlt_items h0),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · rw [alts_fail (by rfl) he (by exact cplxAlt_items h0),
      alts_fail (by rfl) (E s0 h0e) (by exact cplxAlt_items h1), alts_nil]
    rfl

/-! ### `signed_real_number`, `real_number`, `imaginary_number` -/

/-- `signed_real_number` (`Grammar/python.gram:561-564`):
```
    | real_number
    | '+' real=real_number { _PyAST_UnaryOp(UAdd, real, EXTRA) }
    | '-' real=real_number { _PyAST_UnaryOp(USub, real, EXTRA) }
```
`real_number` (79) is the result; without it (no error), at `+` (14) a `real_number` after it gives
`UnaryOp(UAdd, real)`, at `-` (15) `UnaryOp(USub, real)`; at any other token `NULL` with the mark
back. -/
def SignedRealNumber : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (v : Ast) (s : PS), callRule (f + 3) 79 q = (v, s) → v ≠ .null →
    callRule (f + 8) 78 p = (v, s.leave)) ∧
  (∀ (s : PS), callRule (f + 3) 79 q = (.null, s) → s.errorIndicator = false →
    (t.type = 14 → ∀ (r : Ast) (s2 : PS), callRule (f + 1) 79 { s with mark := p.mark + 1 } = (r, s2) →
      r ≠ .null → s2.errorIndicator = false →
      callRule (f + 8) 78 p = (mkAt .UnaryOp [opNode .UAdd, r] (extraLoc t s2), s2.leave)) ∧
    (t.type = 15 → ∀ (r : Ast) (s2 : PS), callRule f 79 { s with mark := p.mark + 1 } = (r, s2) →
      r ≠ .null → s2.errorIndicator = false →
      callRule (f + 8) 78 p = (mkAt .UnaryOp [opNode .USub, r] (extraLoc t s2), s2.leave)) ∧
    (t.type ≠ 14 → t.type ≠ 15 → callRule (f + 8) 78 p = (.null, { s with mark := p.mark }.leave)))

theorem signedRealNumber_proven : SignedRealNumber := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 78 = r78 from rfl, r78]
  refine ⟨fun v s h1 hv => ?_, fun s h1 h1e => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have ek : ∀ ty g, runCall (g + 1) (.tok ty) { s with mark := p.mark } =
        if (q.tokenAt p.mark).type = ty then
          (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 })
        else (.null, { s with mark := p.mark }) := by
      intro ty g
      rw [call_tok, expect_again (tg_call h1) hlt]
    rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])])]
    refine ⟨fun ht r s2 h2 hr h2e => ?_, fun ht r s2 h2 hr h2e => ?_, fun h14 h15 => ?_⟩
    · rw [alts_ok (by rfl) (E s h1e) (by
        dsimp only
        rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h2]) hr,
          items_nil]), altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h2e]
    · rw [alts_fail (by rfl) (E s h1e) (items_call_null (by rw [ek, ite_f (by omega)])),
        PS.mark_mark, alts_ok (by rfl) (E s h1e) (by
        dsimp only
        rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h2]) hr,
          items_nil]), altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
        mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, h2e]
    · rw [alts_fail (by rfl) (E s h1e) (items_call_null (by rw [ek, ite_f h14])), PS.mark_mark,
        alts_fail (by rfl) (E s h1e) (items_call_null (by rw [ek, ite_f h15])), PS.mark_mark,
        alts_nil]
      rfl

/-- The raise of `_PyPegen_ensure_real`/`_PyPegen_ensure_imaginary` over `n`, as the rule
function returns it. -/
def ensureRaised (n : Ast) (m : String) (s : PS) : Ast × PS :=
  (.null, { (raiseErrorKnownLocation "SyntaxError" (locOf n).lineno (locOf n).colOffset
    (locOf n).endLineno (locOf n).endColOffset m s).2 with errorIndicator := true }.leave)

/-- `real_number: real=NUMBER { _PyPegen_ensure_real(p, real) }` (`Grammar/python.gram:566-567`,
`Parser/action_helpers.c:863-871`): a `NUMBER` that is a `Constant` and not complex is the result;
a complex one (`2j`) raises "real number required in complex literal" over it; no `NUMBER` gives
`NULL` with the mark back. -/
def RealNumber : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (n : Ast) (s : PS), numberToken p.enter = (n, s) → n ≠ .null → s.errorIndicator = false →
    isConstant n = true → isComplexConst n = false → callRule (f + 5) 79 p = (n, s.leave)) ∧
  (∀ (n : Ast) (s : PS), numberToken p.enter = (n, s) → n ≠ .null → s.errorIndicator = false →
    (isConstant n = false ∨ isComplexConst n = true) →
    callRule (f + 5) 79 p = ensureRaised n "real number required in complex literal" s) ∧
  (∀ (s : PS), numberToken p.enter = (.null, s) →
    callRule (f + 5) 79 p = (.null, { s with mark := p.mark }.leave))

/-- `imaginary_number: imag=NUMBER { _PyPegen_ensure_imaginary(p, imag) }`
(`Grammar/python.gram:569-570`, `Parser/action_helpers.c:853-861`): a complex `Constant` is the
result; any other `NUMBER` (`1`) raises "imaginary number required in complex literal" over it;
no `NUMBER` gives `NULL` with the mark back. -/
def ImaginaryNumber : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (n : Ast) (s : PS), numberToken p.enter = (n, s) → n ≠ .null → s.errorIndicator = false →
    isConstant n = true → isComplexConst n = true → callRule (f + 5) 80 p = (n, s.leave)) ∧
  (∀ (n : Ast) (s : PS), numberToken p.enter = (n, s) → n ≠ .null → s.errorIndicator = false →
    (isConstant n = false ∨ isComplexConst n = false) →
    callRule (f + 5) 80 p = ensureRaised n "imaginary number required in complex literal" s) ∧
  (∀ (s : PS), numberToken p.enter = (.null, s) →
    callRule (f + 5) 80 p = (.null, { s with mark := p.mark }.leave))

theorem realNumber_proven : RealNumber := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 79 = r79 from rfl, r79]
  refine ⟨fun n s h1 hn h1e hc hx => ?_, fun n s h1 hn h1e hc => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_number, h1]) hn, items_nil]),
      altResult_plain rfl rfl]
    have g0 : ((#[] : Array Ast).push n).getD 0 .null = n := rfl
    have l0 : [n].getD 0 Ast.null = n := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, g0, l0,
      ensureReal, hc, hx]
    simp [nonNull, h1e, StateT.pure, pure]
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_number, h1]) hn, items_nil]),
      altResult_plain rfl rfl]
    have g0 : ((#[] : Array Ast).push n).getD 0 .null = n := rfl
    have l0 : [n].getD 0 Ast.null = n := rfl
    have hb : (!isConstant n || isComplexConst n) = true := by
      rcases hc with hc | hc <;> simp [hc]
    have herr := raiseEKL_errOcc "SyntaxError" "real number required in complex literal"
      (locOf n).lineno (locOf n).colOffset (locOf n).endLineno (locOf n).endColOffset s h1e
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, g0, l0,
      ensureReal, hb, ↓reduceIte]
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq, ensureRaised]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_number, h1])]),
      alts_nil]
    rfl

theorem imaginaryNumber_proven : ImaginaryNumber := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 80 = r80 from rfl, r80]
  refine ⟨fun n s h1 hn h1e hc hx => ?_, fun n s h1 hn h1e hc => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_number, h1]) hn, items_nil]),
      altResult_plain rfl rfl]
    have g0 : ((#[] : Array Ast).push n).getD 0 .null = n := rfl
    have l0 : [n].getD 0 Ast.null = n := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, g0, l0,
      ensureImaginary, hc, hx]
    simp [nonNull, h1e, StateT.pure, pure]
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_number, h1]) hn, items_nil]),
      altResult_plain rfl rfl]
    have g0 : ((#[] : Array Ast).push n).getD 0 .null = n := rfl
    have l0 : [n].getD 0 Ast.null = n := rfl
    have hb : (!(isConstant n && isComplexConst n)) = true := by
      rcases hc with hc | hc <;> simp [hc]
    have herr := raiseEKL_errOcc "SyntaxError" "imaginary number required in complex literal"
      (locOf n).lineno (locOf n).colOffset (locOf n).endLineno (locOf n).endColOffset s h1e
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, g0, l0,
      ensureImaginary, hb, ↓reduceIte]
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq, ensureRaised]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_number, h1])]),
      alts_nil]
    rfl

/-- `literal_pattern` with its lookahead group `('+' | '-')`. -/
def LiteralPatternRule : Prop := LiteralPattern ∧ Tmp41
theorem literalPatternRule_proven : LiteralPatternRule := ⟨literalPattern_proven, tmp41_proven⟩

/-- `real_number` and `imaginary_number`. -/
def RealImaginaryNumber : Prop := RealNumber ∧ ImaginaryNumber
theorem realImaginaryNumber_proven : RealImaginaryNumber := ⟨realNumber_proven, imaginaryNumber_proven⟩

end PyLean.PyGrammar.Peg
