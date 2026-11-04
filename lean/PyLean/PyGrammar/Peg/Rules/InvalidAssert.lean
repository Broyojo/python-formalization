import PyLean.PyGrammar.Peg.Rules.Base2

/-! `invalid_assert_stmt` (`Grammar/python.gram:1329-1347`) and the names
`_PyPegen_get_expr_name` puts in its message, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- Every name `_PyPegen_get_expr_name` (`Parser/action_helpers.c:1084-1159`) returns. -/
def exprNames : List String :=
  ["attribute", "subscript", "starred", "name", "list", "tuple", "lambda", "function call",
   "expression", "generator expression", "yield expression", "await expression",
   "list comprehension", "set comprehension", "dict comprehension", "dict literal", "set display",
   "f-string expression", "t-string expression", "None", "False", "True", "ellipsis", "literal",
   "comparison", "conditional expression", "named expression"]

theorem exprName_mem {e : Ast} {nm : String} (h : exprName e = some nm) : nm ∈ exprNames := by
  unfold exprName at h
  split at h
  · rename_i c fs l
    cases c <;> simp at h <;> (try subst h) <;> (try simp [exprNames]) <;>
      (split at h <;> (cases h; simp [exprNames]))
  · cases h

/-- The `%s` of the assignment message, for every name. -/
theorem assignMsg (nm : String) (h : nm ∈ exprNames) :
    msgOf [.str ("cannot assign to %s here. Maybe you meant '==' instead of '='?".toList.map
      Char.toNat), .str (nm.toList.map Char.toNat)] =
    "cannot assign to " ++ nm ++ " here. Maybe you meant '==' instead of '='?" := by
  revert nm
  decide +kernel

/-- `invalid_assert_stmt` (`Grammar/python.gram:1329-1347`):
```
    | 'assert' a=expression '=' b=expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b,
            "cannot assign to %s here. Maybe you meant '==' instead of '='?",
            _PyPegen_get_expr_name(a)) }
    | 'assert' expression ',' a=expression '=' b=expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b,
            "cannot assign to %s here. Maybe you meant '==' instead of '='?",
            _PyPegen_get_expr_name(a)) }
    | 'assert' a=expression ':=' b=expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b,
            "cannot use named expression without parentheses here") }
    | 'assert' expression ',' a=expression ':=' b=expression {
        RAISE_SYNTAX_ERROR_KNOWN_RANGE(
            a, b,
            "cannot use named expression without parentheses here") }
```
No `EXTRA`. At any token but `assert`, `NULL` and no error. `assert a = b` raises "cannot assign to
<name of a> here. Maybe you meant '==' instead of '='?" over `a`..`b`, the name from
`_PyPegen_get_expr_name(a)` (`nm`, one of `exprNames`; every node `expression` returns has one,
`Slice` being the only kind without, and only a subscript holds a `Slice`); with no `=` after the
test, the mark goes back and `assert t, a = b` raises the same about the message `a`; with no
`,` either, `assert a := b` raises "cannot use named expression without parentheses here" over
`a`..`b`; and with no `:=` after the test, `assert t, a := b` raises it over the message. Every
raise ends the rule with `NULL` and `error_indicator` set (`RAISE_ERROR_KNOWN_LOCATION`,
`Parser/pegen.h`). -/
def InvalidAssertStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  let raised (a b : Ast) (m : String) (s : PS) : Ast × PS :=
    (.null, { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset
      (locOf b).endLineno (locOf b).endColOffset m s).2 with errorIndicator := true }.leave)
  let assign (nm : String) : String :=
    "cannot assign to " ++ nm ++ " here. Maybe you meant '==' instead of '='?"
  let named : String := "cannot use named expression without parentheses here"
  (t.type ≠ 638 → callRule (f + 13) 220 p = (.null, q.leave)) ∧
  (t.type = 638 → ∀ (a b : Ast) (nm : String) (te : Token) (s2 s3 s4 : PS),
    callRule (f + 7) 109 s1 = (a, s2) → a ≠ .null → expectToken 22 s2 = (.tok te, s3) →
    callRule (f + 5) 109 s3 = (b, s4) → b ≠ .null → s4.errorIndicator = false →
    exprName a = some nm → callRule (f + 13) 220 p = raised a b (assign nm) s4) ∧
  (t.type = 638 → ∀ (a0 a a' b : Ast) (nm : String) (tc te : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 7) 109 s1 = (a0, s2) → a0 ≠ .null → expectToken 22 s2 = (.null, s3) →
    s3.errorIndicator = false →
    callRule (f + 6) 109 { s3 with mark := p.mark + 1 } = (a', s4) → a' ≠ .null →
    expectToken 12 s4 = (.tok tc, s5) → callRule (f + 4) 109 s5 = (a, s6) → a ≠ .null →
    expectToken 22 s6 = (.tok te, s7) → callRule (f + 2) 109 s7 = (b, s8) → b ≠ .null →
    s8.errorIndicator = false →
    exprName a = some nm → callRule (f + 13) 220 p = raised a b (assign nm) s8) ∧
  (t.type = 638 → ∀ (a0 a1 a b : Ast) (tw : Token) (s2 s3 s4 s5 s6 s7 s8 : PS),
    callRule (f + 7) 109 s1 = (a0, s2) → a0 ≠ .null → expectToken 22 s2 = (.null, s3) →
    s3.errorIndicator = false →
    callRule (f + 6) 109 { s3 with mark := p.mark + 1 } = (a1, s4) → a1 ≠ .null →
    expectToken 12 s4 = (.null, s5) → s5.errorIndicator = false →
    callRule (f + 5) 109 { s5 with mark := p.mark + 1 } = (a, s6) → a ≠ .null →
    expectToken 53 s6 = (.tok tw, s7) → callRule (f + 3) 109 s7 = (b, s8) → b ≠ .null →
    s8.errorIndicator = false → callRule (f + 13) 220 p = raised a b named s8) ∧
  (t.type = 638 → ∀ (a0 a1 a2 a3 a4 a b : Ast) (tc tc' tw : Token)
    (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 : PS),
    callRule (f + 7) 109 s1 = (a0, s2) → a0 ≠ .null → expectToken 22 s2 = (.null, s3) →
    s3.errorIndicator = false →
    callRule (f + 6) 109 { s3 with mark := p.mark + 1 } = (a1, s4) → a1 ≠ .null →
    expectToken 12 s4 = (.tok tc, s5) → callRule (f + 4) 109 s5 = (a2, s6) → a2 ≠ .null →
    expectToken 22 s6 = (.null, s7) → s7.errorIndicator = false →
    callRule (f + 5) 109 { s7 with mark := p.mark + 1 } = (a3, s8) → a3 ≠ .null →
    expectToken 53 s8 = (.null, s9) → s9.errorIndicator = false →
    callRule (f + 4) 109 { s9 with mark := p.mark + 1 } = (a4, s10) → a4 ≠ .null →
    expectToken 12 s10 = (.tok tc', s11) → callRule (f + 2) 109 s11 = (a, s12) → a ≠ .null →
    expectToken 53 s12 = (.tok tw, s13) → callRule f 109 s13 = (b, s14) → b ≠ .null →
    s14.errorIndicator = false → callRule (f + 13) 220 p = raised a b named s14)

/-- The tail every raising alternative of `invalid_assert_stmt` shares: the action raises with no
error before it, so `emit_action` turns its `NULL` into an error return. -/
theorem raised_tail (cls m : String) (a b c d : Int) (s : PS) (he : s.errorIndicator = false) :
    (let r := (Ast.null, (raiseErrorKnownLocation cls a b c d m s).2)
     if ((!nonNull r.1 || r.2.errorIndicator) && r.2.errOccurred) = true then
       ((none : Option Ast), { r.2 with errorIndicator := true })
     else (some r.1, r.2)) =
    (none, { (raiseErrorKnownLocation cls a b c d m s).2 with errorIndicator := true }) := by
  have herr := raiseEKL_errOcc cls m a b c d s he
  generalize raiseErrorKnownLocation cls a b c d m s = r at herr ⊢
  obtain ⟨u, s'⟩ := r
  simp only at herr
  simp [nonNull, herr]

theorem invalidAssertStmt_proven : InvalidAssertStmt := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have again : ∀ g (s : PS), TokGrows q s → (q.tokenAt p.mark).type = 638 →
      runCall (g + 1) (.tok 638) { s with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 }) :=
    fun g s gs ht => by rw [call_tok, expect_again gs hlt, ite_t ht]
  have first : ∀ g, (q.tokenAt p.mark).type = 638 →
      runCall (g + 1) (.tok 638) p.enter = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ht => by rw [call_tok, expect_entered h, ite_t ht]
  have hn : (msgOf [.str ("cannot use named expression without parentheses here".toList.map
      Char.toNat)]) = "cannot use named expression without parentheses here" := by decide +kernel
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 220 = r220 from rfl, r220]
  refine ⟨fun ht => ?_,
    fun ht a b nm te s2 s3 s4 h2 ha h3 h4 hb h4e hnm => ?_,
    fun ht a0 a a' b nm tc te s2 s3 s4 s5 s6 s7 s8 h2 ha0 h3 h3e h4 ha' h5 h6 ha h7 h8 hb h8e hnm => ?_,
    fun ht a0 a1 a b tw s2 s3 s4 s5 s6 s7 s8 h2 ha0 h3 h3e h4 ha1 h5 h5e h6 ha h7 h8 hb h8e => ?_,
    fun ht a0 a1 a2 a3 a4 a b tc tc' tw s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 h2 ha0 h3 h3e
      h4 ha1 h5 h6 ha2 h7 h7e h8 ha3 h9 h9e h10 ha4 h11 h12 ha h13 h14 hb h14e => ?_⟩
  · have e1 : ∀ g, runCall (g + 1) (.tok 638) p.enter = (.null, q) := fun g => by
      rw [call_tok, expect_entered h, ite_f ht]
    have e2 : ∀ g, runCall (g + 1) (.tok 638) { q with mark := p.mark } = (.null, q) := fun g => by
      rw [hq, call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_fail (by rfl) he' (items_call_null (e1 _)),
      alts_fail (by rfl) (E q he) (items_call_null (e2 _)),
      alts_fail (by rfl) (E q he) (items_call_null (e2 _)),
      alts_fail (by rfl) (E q he) (items_call_null (e2 _)), hq, alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (first _ ht) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hb,
        items_nil]), altResult_plain rfl rfl]
    have g1 : (((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a).push (.tok te)).push b).getD 1 .null = a := rfl
    have g3 : (((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a).push (.tok te)).push b).getD 3 .null = b := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g1, g3, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, hnm]
    rw [assignMsg nm (exprName_mem hnm)]
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot assign to " ++ nm ++ " here. Maybe you meant '==' instead of '='?") (locOf a).lineno (locOf a).colOffset
      (locOf b).endLineno (locOf b).endColOffset s4 h4e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · have g3 : TokGrows q s3 := tg_mark' ((tg_call h2).trans (tg_expect h3)) _
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (first _ ht) (by simp), items_call (by rw [call_rule, h2]) ha0,
        items_call_null (by rw [call_tok, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call (by rw [call_rule, h4]) ha',
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_rule, h6]) ha,
        items_call (by rw [call_tok, h7]) (by simp), items_call (by rw [call_rule, h8]) hb,
        items_nil]), altResult_plain rfl rfl]
    have g1 : (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a').push (.tok tc)).push a).push (.tok te)).push b).getD 3 .null = a := rfl
    have g3 : (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a').push (.tok tc)).push a).push (.tok te)).push b).getD 5 .null = b := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g1, g3, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some, hnm]
    rw [assignMsg nm (exprName_mem hnm)]
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot assign to " ++ nm ++ " here. Maybe you meant '==' instead of '='?") (locOf a).lineno (locOf a).colOffset
      (locOf b).endLineno (locOf b).endColOffset s8 h8e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · have g3 : TokGrows q s3 := tg_mark' ((tg_call h2).trans (tg_expect h3)) _
    have g5 : TokGrows q s5 := g3.trans (tg_mark' ((tg_call h4).trans (tg_expect h5)) _)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (first _ ht) (by simp), items_call (by rw [call_rule, h2]) ha0,
        items_call_null (by rw [call_tok, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call (by rw [call_rule, h4]) ha1,
        items_call_null (by rw [call_tok, h5])]),
      alts_ok (by rfl) (E s5 h5e) (by
      dsimp only
      rw [items_call (again _ _ g5 ht) (by simp), items_call (by rw [call_rule, h6]) ha,
        items_call (by rw [call_tok, h7]) (by simp), items_call (by rw [call_rule, h8]) hb,
        items_nil]), altResult_plain rfl rfl]
    have g1 : (((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a).push (.tok tw)).push b).getD 1 .null = a := rfl
    have g3 : (((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a).push (.tok tw)).push b).getD 3 .null = b := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g1, g3, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    rw [hn]
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot use named expression without parentheses here") (locOf a).lineno (locOf a).colOffset
      (locOf b).endLineno (locOf b).endColOffset s8 h8e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · have g3 : TokGrows q s3 := tg_mark' ((tg_call h2).trans (tg_expect h3)) _
    have g7 : TokGrows q s7 := g3.trans (tg_mark' ((((tg_call h4).trans (tg_expect h5)).trans
      (tg_call h6)).trans (tg_expect h7)) _)
    have g9 : TokGrows q s9 := g7.trans (tg_mark' ((tg_call h8).trans (tg_expect h9)) _)
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (first _ ht) (by simp), items_call (by rw [call_rule, h2]) ha0,
        items_call_null (by rw [call_tok, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (again _ _ g3 ht) (by simp), items_call (by rw [call_rule, h4]) ha1,
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_rule, h6]) ha2,
        items_call_null (by rw [call_tok, h7])]),
      alts_fail (by rfl) (E s7 h7e) (by
      dsimp only
      rw [items_call (again _ _ g7 ht) (by simp), items_call (by rw [call_rule, h8]) ha3,
        items_call_null (by rw [call_tok, h9])]),
      alts_ok (by rfl) (E s9 h9e) (by
      dsimp only
      rw [items_call (again _ _ g9 ht) (by simp), items_call (by rw [call_rule, h10]) ha4,
        items_call (by rw [call_tok, h11]) (by simp), items_call (by rw [call_rule, h12]) ha,
        items_call (by rw [call_tok, h13]) (by simp), items_call (by rw [call_rule, h14]) hb,
        items_nil]), altResult_plain rfl rfl]
    have g1 : (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a4).push (.tok tc')).push a).push (.tok tw)).push b).getD 3 .null = a := rfl
    have g3 : (((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a4).push (.tok tc')).push a).push (.tok tw)).push b).getD 5 .null = b := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g1, g3, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
      Option.getD_some]
    rw [hn]
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot use named expression without parentheses here") (locOf a).lineno (locOf a).colOffset
      (locOf b).endLineno (locOf b).endColOffset s14 h14e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]

end PyLean.PyGrammar.Peg
