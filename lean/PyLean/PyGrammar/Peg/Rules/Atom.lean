import PyLean.PyGrammar.Peg.Rules.TPrimary

/-! `atom` (`Grammar/python.gram:894-904`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `_PyPegen_name_token` at a token that is not a `NAME`. -/
theorem nameToken_other {q : PS} (hlt : q.mark < q.fill) (ht : (q.tokenAt q.mark).type ≠ 1) :
    nameToken q = (.null, q) := by
  have : expectToken TokKind.NAME.num q = (.null, q) := by
    rw [expectToken_at _ _ hlt]
    exact ite_f ht
  simp only [nameToken, bind, StateT.bind, this]
  rfl

/-- `atom` (`Grammar/python.gram:894-904`):
```
    | NAME
    | 'True' { _PyAST_Constant(Py_True, NULL, EXTRA) }
    | 'False' { _PyAST_Constant(Py_False, NULL, EXTRA) }
    | 'None' { _PyAST_Constant(Py_None, NULL, EXTRA) }
    | &(STRING|FSTRING_START|TSTRING_START) strings
    | NUMBER
    | &'(' (genexp | tuple | group)
    | &'[' (listcomp | list)
    | &'{' (dictcomp | setcomp | dict | set)
    | '...' { _PyAST_Constant(Py_Ellipsis, NULL, EXTRA) }
```
By the token `t` under the mark (`NAME` 1, `True` 627, `False` 629, `None` 628, `NUMBER` 2, `(` 7,
`[` 9, `{` 25, `...` 52): a `NAME` is the result of `_PyPegen_name_token`; the three keywords and
`...` give their `Constant` with no `kind`, spanning the token; past those, the
`&(STRING|FSTRING_START|TSTRING_START)` lookahead (`_tmp_42`, given by its outcome) holding gives
`strings` from the start mark; with it failing, a `NUMBER` is `_PyPegen_number_token`'s result, and
`(`, `[`, `{` give the result of their group (`_tmp_68`, `_tmp_69`, `_tmp_70`) after the lookahead
on that token; any other token, with the string lookahead failing, gives `NULL` with the mark back.
-/
def Atom : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let kw : Prop := t.type ≠ 1 ∧ t.type ≠ 627 ∧ t.type ≠ 629 ∧ t.type ≠ 628
  (t.type = 1 → ∀ (n : Ast) (s : PS), nameToken q = (n, s) → n ≠ .null →
    callRule (f + 14) 147 p = (n, s.leave)) ∧
  (t.type = 627 → callRule (f + 14) 147 p =
    (mkAt .Constant [.const .true_, .null] (extraLoc t { q with mark := p.mark + 1 }),
      { q with mark := p.mark + 1 }.leave)) ∧
  (t.type = 629 → callRule (f + 14) 147 p =
    (mkAt .Constant [.const .false_, .null] (extraLoc t { q with mark := p.mark + 1 }),
      { q with mark := p.mark + 1 }.leave)) ∧
  (t.type = 628 → callRule (f + 14) 147 p =
    (mkAt .Constant [.const .none, .null] (extraLoc t { q with mark := p.mark + 1 }),
      { q with mark := p.mark + 1 }.leave)) ∧
  (kw → ∀ (x v : Ast) (s s' : PS), callRule (f + 5) 319 q = (x, s) → nonNull x = true →
    callRule (f + 4) 173 { s with mark := p.mark } = (v, s') → v ≠ .null →
    callRule (f + 14) 147 p = (v, s'.leave)) ∧
  (kw → ∀ (x : Ast) (s : PS), callRule (f + 5) 319 q = (x, s) → nonNull x = false →
    s.errorIndicator = false →
    (t.type = 2 → ∀ (n : Ast) (s' : PS), numberToken { s with mark := p.mark } = (n, s') → n ≠ .null →
      callRule (f + 14) 147 p = (n, s'.leave)) ∧
    (t.type = 7 → ∀ (v : Ast) (s' : PS), callRule (f + 2) 345 { s with mark := p.mark } = (v, s') →
      v ≠ .null → callRule (f + 14) 147 p = (v, s'.leave)) ∧
    (t.type = 9 → ∀ (v : Ast) (s' : PS), callRule (f + 1) 346 { s with mark := p.mark } = (v, s') →
      v ≠ .null → callRule (f + 14) 147 p = (v, s'.leave)) ∧
    (t.type = 25 → ∀ (v : Ast) (s' : PS), callRule f 347 { s with mark := p.mark } = (v, s') →
      v ≠ .null → callRule (f + 14) 147 p = (v, s'.leave)) ∧
    (t.type = 52 → callRule (f + 14) 147 p =
      (mkAt .Constant [.const .ellipsis, .null] (extraLoc t { s with mark := p.mark + 1 }),
        { s with mark := p.mark + 1 }.leave)) ∧
    (t.type ≠ 2 → t.type ≠ 7 → t.type ≠ 9 → t.type ≠ 25 → t.type ≠ 52 →
      callRule (f + 14) 147 p = (.null, { s with mark := p.mark }.leave)))

theorem atom_proven : Atom := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 147 = r147 from rfl, r147]
  have eqk : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  have nm : (q.tokenAt p.mark).type ≠ 1 → runCall (f + 10) .name q = (.null, q) := by
    intro ht
    rw [call_name, nameToken_other hlt' (hm ▸ ht)]
  refine ⟨fun ht n s h1 hn => ?_, fun ht => ?_, fun ht => ?_, fun ht => ?_,
    fun hk x v s s' h1 hx h2 hv => ?_, fun hk x s h1 hx hse => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_name, h1]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (nm (by omega))), hq,
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [eqk, ite_t ht]) (by simp), items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, he,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, he]
  · rw [alts_fail (by rfl) he (items_call_null (nm (by omega))), hq,
      alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f (by omega)])), hq,
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [eqk, ite_t ht]) (by simp), items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, he,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, he]
  · rw [alts_fail (by rfl) he (items_call_null (nm (by omega))), hq,
      alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f (by omega)])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f (by omega)])), hq,
      alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [eqk, ite_t ht]) (by simp), items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, he,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, he]
  · obtain ⟨k1, k2, k3, k4⟩ := hk
    have h2' : callRule (f + 4) 173 { s with mark := q.mark } = (v, s') := by rw [hm]; exact h2
    rw [alts_fail (by rfl) he (items_call_null (nm k1)), hq,
      alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f k2])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f k3])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f k4])), hq,
      alts_ok (by rfl) he (by
        dsimp only
        rw [items_look (by rw [call_rule, h1]) hx, items_call (by rw [call_rule, h2']) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · obtain ⟨k1, k2, k3, k4⟩ := hk
    have g := tg_call h1
    have hS : ∀ ty, expectToken ty { s with mark := p.mark } =
        if (q.tokenAt p.mark).type = ty then (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 })
        else (.null, { s with mark := p.mark }) := fun ty => expect_again g hlt
    have hSe : ({ s with mark := p.mark } : PS).errorIndicator = false := hse
    have hnum : (q.tokenAt p.mark).type ≠ 2 → numberToken { s with mark := p.mark } = (.null, { s with mark := p.mark }) := by
      intro ht
      refine numberToken_other (Nat.lt_of_lt_of_le hlt g.le) ?_
      show (({ s with mark := p.mark } : PS).tokenAt p.mark).type ≠ 2
      rw [show ({ s with mark := p.mark } : PS).tokenAt p.mark = q.tokenAt p.mark from g.same p.mark hlt]
      exact ht
    have pre : ∀ g', runAlts (f + 12) r147.alts false p.mark
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q =
        runAlts (f + 7) (r147.alts.drop 5) false p.mark
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) { s with mark := p.mark } ∨ g' := by
      intro g'
      left
      simp only [r147]
      rw [alts_fail (by rfl) he (items_call_null (nm k1)), hq,
        alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f k2])), hq,
        alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f k3])), hq,
        alts_fail (by rfl) he (items_call_null (by rw [eqk, ite_f k4])), hq,
        alts_fail (by rfl) he (by dsimp only; rw [items_look_fail (by rw [call_rule, h1]) hx]),
        hm]
      rfl
    have pre' := (pre False).resolve_right id
    simp only [r147] at pre'
    rw [pre']
    simp only [List.drop]
    refine ⟨fun ht n s' h3 hn => ?_, fun ht v s' h3 hv => ?_, fun ht v s' h3 hv => ?_,
      fun ht v s' h3 hv => ?_, fun ht => ?_, fun t2 t7 t9 t25 t52 => ?_⟩
    · rw [alts_ok (by rfl) hSe (by dsimp only; rw [items_call (by rw [call_number, h3]) hn, items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) hSe (items_call_null (by rw [call_number, hnum (by omega)])),
        alts_ok (by rfl) hSe (by
          dsimp only
          rw [items_look (b := true) (by rw [call_tok, hS, ite_t ht]) rfl, items_call (by rw [call_rule, h3]) hv,
            items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) hSe (items_call_null (by rw [call_number, hnum (by omega)])),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f (by omega)]) rfl]),
        alts_ok (by rfl) hSe (by
          dsimp only
          rw [items_look (b := true) (by rw [call_tok, hS, ite_t ht]) rfl, items_call (by rw [call_rule, h3]) hv,
            items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) hSe (items_call_null (by rw [call_number, hnum (by omega)])),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f (by omega)]) rfl]),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f (by omega)]) rfl]),
        alts_ok (by rfl) hSe (by
          dsimp only
          rw [items_look (b := true) (by rw [call_tok, hS, ite_t ht]) rfl, items_call (by rw [call_rule, h3]) hv,
            items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) hSe (items_call_null (by rw [call_number, hnum (by omega)])),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f (by omega)]) rfl]),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f (by omega)]) rfl]),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f (by omega)]) rfl]),
        alts_ok (by rfl) hSe (by
          dsimp only; rw [items_call (by rw [call_tok, hS, ite_t ht]) (by simp), items_nil]),
        altResult_extra rfl rfl]
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, hse,
        Bool.or_false, mkAt, extraLoc, locArgs]
      simp [mkAst, nonNull, hse]
    · rw [alts_fail (by rfl) hSe (items_call_null (by rw [call_number, hnum t2])),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f t7]) rfl]),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f t9]) rfl]),
        alts_fail (by rfl) hSe (by dsimp only; rw [items_look_fail (by rw [call_tok, hS, ite_f t25]) rfl]),
        alts_fail (by rfl) hSe (items_call_null (by rw [call_tok, hS, ite_f t52])),
        alts_nil]
      rfl

end PyLean.PyGrammar.Peg
