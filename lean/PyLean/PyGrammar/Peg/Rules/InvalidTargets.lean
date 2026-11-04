import PyLean.PyGrammar.Peg.Rules.Patterns
import PyLean.PyGrammar.Peg.Rules.InvalidAssert

/-! `invalid_del_stmt` and `invalid_ann_assign_target` (`Grammar/python.gram:1317-1328`), rule by
rule: the `RAISE_SYNTAX_ERROR_INVALID_TARGET` users and the names `_PyPegen_get_expr_name` puts in
their messages. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `invalid_del_stmt` (`Grammar/python.gram:1326-1328`):
```
    | 'del' a=star_expressions {
        RAISE_SYNTAX_ERROR_INVALID_TARGET(DEL_TARGETS, a) }
```
No `EXTRA`. At any token but `del` (634), `NULL` and no error. After `del` and `star_expressions`,
`_RAISE_SYNTAX_ERROR_INVALID_TARGET` (`Parser/pegen.h:244-264`) asks
`_PyPegen_get_invalid_target(a, DEL_TARGETS)` (`invalidTarget 1`) for the first node that cannot
be deleted: with none, the action returns `NULL` without an exception and the rule gives `NULL`
with no error; with one, `t`, it raises "cannot delete <name of t>" over `t`
(`RAISE_SYNTAX_ERROR_KNOWN_LOCATION`), the name from `_PyPegen_get_expr_name(t)` (`nm`), and the
rule ends with `NULL` and `error_indicator` set. Without `star_expressions`, `NULL` with the mark
back. -/
def InvalidDelStmt : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ 634 → callRule (f + 6) 219 p = (.null, q.leave)) ∧
  (t.type = 634 → ∀ (a : Ast) (s : PS), callRule f 112 { q with mark := p.mark + 1 } = (a, s) →
    a ≠ .null → s.errorIndicator = false → s.errOccurred = false → invalidTarget 1 100000 a = .null →
    callRule (f + 6) 219 p = (.null, s.leave)) ∧
  (t.type = 634 → ∀ (a tg : Ast) (nm : String) (s : PS),
    callRule f 112 { q with mark := p.mark + 1 } = (a, s) → a ≠ .null → s.errorIndicator = false →
    invalidTarget 1 100000 a = tg → tg ≠ .null → exprName tg = some nm →
    callRule (f + 6) 219 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" (locOf tg).lineno (locOf tg).colOffset
        (locOf tg).endLineno (locOf tg).endColOffset ("cannot delete " ++ nm) s).2 with
          errorIndicator := true }.leave)) ∧
  (t.type = 634 → ∀ (s : PS), callRule f 112 { q with mark := p.mark + 1 } = (.null, s) →
    callRule (f + 6) 219 p = (.null, { s with mark := p.mark }.leave))

theorem invalidDelStmt_proven : InvalidDelStmt := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 219 = r219 from rfl, r219]
  refine ⟨fun ht => ?_, fun ht a s h1 ha h1e h1o hnt => ?_,
    fun ht a tg nm s h1 ha h1e hnt htg hnm => ?_, fun ht s h1 => ?_⟩
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [call_tok, expect_entered h, ite_f ht])), hq,
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) ha, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [hnt, h1o, StateT.pure, pure]
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) ha, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    have hmsg : toString "cannot delete " ++ toString ((exprName tg).getD "") = "cannot delete " ++ nm := by
      rw [hnm]
      rfl
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot delete " ++ nm) (locOf tg).lineno
      (locOf tg).colOffset (locOf tg).endLineno (locOf tg).endColOffset s h1e
    have g1 : (((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push a).getD 1 .null = a := rfl
    have i1 : Int.toNat 1 = 1 := rfl
    have l0 : [Ast.int 1, a].getD 0 Ast.null = .int 1 := rfl
    have l1 : [Ast.int 1, a].getD 1 Ast.null = a := rfl
    have hb : ((1 : Int) == 0 || (1 : Int) == 2) = false := rfl
    simp only [g1, l0, i1, l1, hb, Bool.false_eq_true, ↓reduceIte]
    simp only [hnt]
    simp only [hmsg, raiseRange, bind, StateT.bind, pure, StateT.pure]
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `invalid_ann_assign_target` (`Grammar/python.gram:1317-1320`):
```
    | list
    | tuple
    | '(' a=invalid_ann_assign_target ')' { a }
```
No `EXTRA`. A `list` is the result; without one (and no error), a `tuple` from the start mark;
without either, `(` (7) `invalid_ann_assign_target` `)` gives the inner target, so `((a, b))` gives
the tuple; otherwise `NULL` with the mark back. -/
def InvalidAnnAssignTarget : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule (f + 4) 174 p.enter = (v, s) → v ≠ .null →
    callRule (f + 9) 217 p = (v, s.leave)) ∧
  (∀ (v : Ast) (s s2 : PS), callRule (f + 4) 174 p.enter = (.null, s) → s.errorIndicator = false →
    callRule (f + 3) 175 { s with mark := p.mark } = (v, s2) → v ≠ .null →
    callRule (f + 9) 217 p = (v, s2.leave)) ∧
  (∀ (v : Ast) (o c : Token) (s s2 s3 s4 s5 : PS), callRule (f + 4) 174 p.enter = (.null, s) →
    s.errorIndicator = false → callRule (f + 3) 175 { s with mark := p.mark } = (.null, s2) →
    s2.errorIndicator = false → expectToken 7 { s2 with mark := p.mark } = (.tok o, s3) →
    callRule (f + 1) 217 s3 = (v, s4) → v ≠ .null → expectToken 8 s4 = (.tok c, s5) →
    s5.errorIndicator = false → callRule (f + 9) 217 p = (v, s5.leave)) ∧
  (∀ (s s2 s3 : PS), callRule (f + 4) 174 p.enter = (.null, s) →
    s.errorIndicator = false → callRule (f + 3) 175 { s with mark := p.mark } = (.null, s2) →
    s2.errorIndicator = false → expectToken 7 { s2 with mark := p.mark } = (.null, s3) →
    callRule (f + 9) 217 p = (.null, { s3 with mark := p.mark }.leave))

theorem invalidAnnAssignTarget_proven : InvalidAnnAssignTarget := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 217 = r217 from rfl, r217]
  refine ⟨fun v s h1 hv => ?_, fun v s s2 h1 h1e h2 hv => ?_,
    fun v o c s s2 s3 s4 s5 h1 h1e h2 h2e h3 h4 hv h5 h5e => ?_, fun s s2 s3 h1 h1e h2 h2e h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_tok, h3]) (by simp), items_call (by rw [call_rule, h4]) hv,
          items_call (by rw [call_tok, h5]) (by simp), items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h5e, Bool.or_false]
    cases v <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call_null (by rw [call_tok, h3])]),
      alts_nil]
    rfl

/-- The `%s` of the annotation message, for every name `_PyPegen_get_expr_name` returns. -/
theorem annMsg (nm : String) (h : nm ∈ exprNames) :
    msgOf [.str ("only single target (not %s) can be annotated".toList.map Char.toNat),
      .str (nm.toList.map Char.toNat)] = "only single target (not " ++ nm ++ ") can be annotated" := by
  revert nm
  decide +kernel

/-- The `%s` of the augmented-assignment message, for every name. -/
theorem augMsg (nm : String) (h : nm ∈ exprNames) :
    msgOf [.str ("'%s' is an illegal expression for augmented assignment".toList.map Char.toNat),
      .str (nm.toList.map Char.toNat)] = "'" ++ nm ++ "' is an illegal expression for augmented assignment" := by
  revert nm
  decide +kernel

/-- `invalid_assignment` (`Grammar/python.gram:1297-1316`), the annotation alternatives and the
augmented-assignment one:
```
    | a=invalid_ann_assign_target ':' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "only single target (not %s) can be annotated",
            _PyPegen_get_expr_name(a)) }
    | a=star_named_expression ',' star_named_expressions* ':' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "only single target (not tuple) can be annotated") }
    | a=expression ':' expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "illegal target for annotation") }
    | (star_targets '=')* a=star_expressions '=' { RAISE_SYNTAX_ERROR_INVALID_TARGET(STAR_TARGETS, a) }
    | (star_targets '=')* a=yield_expr '=' { RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "assignment to yield expression not possible") }
    | a=star_expressions augassign annotated_rhs {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, "'%s' is an illegal expression for augmented assignment",
            _PyPegen_get_expr_name(a)) }
```
No `EXTRA`; every raise is over `a` alone and ends the rule with `NULL` and `error_indicator`
set. A list or tuple target (`invalid_ann_assign_target`) followed by `:` and an annotation raises
"only single target (not <name>) can be annotated"; without it, a `star_named_expression` and `,`
before `:` raise "... (not tuple) ..." at the first element; without the `,`, an `expression`
followed by `:` raises "illegal target for annotation". And when nothing before is an
annotation, no `=` follows the `star_expressions` after the `(star_targets '=')*` loop, and no
`yield_expr` after the loop either, `star_expressions` `augassign` `annotated_rhs` raises
"'<name>' is an illegal expression for augmented assignment" (so `f() += 1` names a "function
call"). The names are `_PyPegen_get_expr_name`'s (`nm`, one of `exprNames`), as in
`InvalidAssertStmt`. -/
def InvalidAssignment : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  let raised (a : Ast) (m : String) (s : PS) : Ast × PS :=
    (.null, { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset
      (locOf a).endLineno (locOf a).endColOffset m s).2 with errorIndicator := true }.leave)
  (∀ (a b : Ast) (nm : String) (c : Token) (s1 s2 s3 : PS), callRule (f + 7) 217 p.enter = (a, s1) →
    a ≠ .null → expectToken 11 s1 = (.tok c, s2) → callRule (f + 5) 109 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false → exprName a = some nm →
    callRule (f + 12) 216 p = raised a ("only single target (not " ++ nm ++ ") can be annotated") s3) ∧
  (∀ (a xs b : Ast) (c c' : Token) (s1 s2 s3 s4 s5 s6 : PS), callRule (f + 7) 217 p.enter = (.null, s1) →
    s1.errorIndicator = false → callRule (f + 6) 116 { s1 with mark := p.mark } = (a, s2) → a ≠ .null →
    expectToken 12 s2 = (.tok c, s3) → callRule (f + 4) 398 s3 = (xs, s4) → xs ≠ .null →
    expectToken 11 s4 = (.tok c', s5) → callRule (f + 2) 109 s5 = (b, s6) → b ≠ .null →
    s6.errorIndicator = false →
    callRule (f + 12) 216 p = raised a "only single target (not tuple) can be annotated" s6) ∧
  (∀ (a' a b : Ast) (c : Token) (s1 s2 s3 s4 s5 s6 : PS), callRule (f + 7) 217 p.enter = (.null, s1) →
    s1.errorIndicator = false → callRule (f + 6) 116 { s1 with mark := p.mark } = (a', s2) → a' ≠ .null →
    expectToken 12 s2 = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 5) 109 { s3 with mark := p.mark } = (a, s4) → a ≠ .null →
    expectToken 11 s4 = (.tok c, s5) → callRule (f + 3) 109 s5 = (b, s6) → b ≠ .null →
    s6.errorIndicator = false → callRule (f + 12) 216 p = raised a "illegal target for annotation" s6) ∧
  (∀ (a' a0 l a1 l' a o b : Ast) (nm : String) (s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 : PS),
    callRule (f + 7) 217 p.enter = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 6) 116 { s1 with mark := p.mark } = (a', s2) → a' ≠ .null →
    expectToken 12 s2 = (.null, s3) → s3.errorIndicator = false →
    callRule (f + 5) 109 { s3 with mark := p.mark } = (a0, s4) → a0 ≠ .null →
    expectToken 11 s4 = (.null, s5) → s5.errorIndicator = false →
    callRule (f + 4) 399 { s5 with mark := p.mark } = (l, s6) → l ≠ .null →
    callRule (f + 3) 112 s6 = (a1, s7) → a1 ≠ .null → expectToken 22 s7 = (.null, s8) →
    s8.errorIndicator = false →
    callRule (f + 3) 399 { s8 with mark := p.mark } = (l', s9) → l' ≠ .null →
    callRule (f + 2) 111 s9 = (.null, s10) → s10.errorIndicator = false →
    callRule (f + 2) 112 { s10 with mark := p.mark } = (a, s11) → a ≠ .null →
    callRule (f + 1) 13 s11 = (o, s12) → o ≠ .null → callRule f 12 s12 = (b, s13) → b ≠ .null →
    s13.errorIndicator = false → exprName a = some nm →
    callRule (f + 12) 216 p =
      raised a ("'" ++ nm ++ "' is an illegal expression for augmented assignment") s13)

theorem invalidAssignment_proven : InvalidAssignment := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 216 = r216 from rfl, r216]
  refine ⟨fun a b nm c s1 s2 s3 h1 ha h2 h3 hb h3e hnm => ?_,
    fun a xs b c c' s1 s2 s3 s4 s5 s6 h1 h1e h2 ha h3 h4 hxs h5 h6 hb h6e => ?_,
    fun a' a b c s1 s2 s3 s4 s5 s6 h1 h1e h2 ha' h3 h3e h4 ha h5 h6 hb h6e => ?_,
    fun a' a0 l a1 l' a o b nm s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 h1 h1e h2 ha' h3 h3e h4 ha0
      h5 h5e h6 hl6 h7 ha1 h8 h8e h9 hl9 h10 h10e h11 ha h12 ho h13 hb h13e hnm => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    have g0 : ((((#[] : Array Ast).push a).push (.tok c)).push b).getD 0 .null = a := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g0, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, hnm]
    rw [annMsg nm (exprName_mem hnm)]
    have herr := raiseEKL_errOcc "SyntaxError" ("only single target (not " ++ nm ++ ") can be annotated")
      (locOf a).lineno (locOf a).colOffset (locOf a).endLineno (locOf a).endColOffset s3 h3e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s1 h1e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) ha, items_call (by rw [call_tok, h3]) (by simp),
        items_call (by rw [call_rule, h4]) hxs, items_call (by rw [call_tok, h5]) (by simp),
        items_call (by rw [call_rule, h6]) hb, items_nil]), altResult_plain rfl rfl]
    have g0 : ((((((#[] : Array Ast).push a).push (.tok c)).push xs).push (.tok c')).push b).getD 0 .null = a := rfl
    have hm : msgOf [.str ("only single target (not tuple) can be annotated".toList.map Char.toNat)] =
        "only single target (not tuple) can be annotated" := by decide +kernel
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g0, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rw [hm]
    have herr := raiseEKL_errOcc "SyntaxError" "only single target (not tuple) can be annotated"
      (locOf a).lineno (locOf a).colOffset (locOf a).endLineno (locOf a).endColOffset s6 h6e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (E s1 h1e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) ha', items_call_null (by rw [call_tok, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h4]) ha, items_call (by rw [call_tok, h5]) (by simp),
        items_call (by rw [call_rule, h6]) hb, items_nil]), altResult_plain rfl rfl]
    have g0 : ((((#[] : Array Ast).push a).push (.tok c)).push b).getD 0 .null = a := rfl
    have hm : msgOf [.str ("illegal target for annotation".toList.map Char.toNat)] =
        "illegal target for annotation" := by decide +kernel
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g0, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some]
    rw [hm]
    have herr := raiseEKL_errOcc "SyntaxError" "illegal target for annotation"
      (locOf a).lineno (locOf a).colOffset (locOf a).endLineno (locOf a).endColOffset s6 h6e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (E s1 h1e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) ha', items_call_null (by rw [call_tok, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h4]) ha0, items_call_null (by rw [call_tok, h5])]),
      alts_fail (by rfl) (E s5 h5e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h6]) hl6, items_call (by rw [call_rule, h7]) ha1,
        items_call_null (by rw [call_tok, h8])]),
      alts_fail (by rfl) (E s8 h8e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h9]) hl9, items_call_null (by rw [call_rule, h10])]),
      alts_ok (by rfl) (E s10 h10e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h11]) ha, items_call (by rw [call_rule, h12]) ho,
        items_call (by rw [call_rule, h13]) hb, items_nil]), altResult_plain rfl rfl]
    have g0 : ((((#[] : Array Ast).push a).push o).push b).getD 0 .null = a := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g0, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, hnm]
    rw [augMsg nm (exprName_mem hnm)]
    have herr := raiseEKL_errOcc "SyntaxError" ("'" ++ nm ++ "' is an illegal expression for augmented assignment")
      (locOf a).lineno (locOf a).colOffset (locOf a).endLineno (locOf a).endColOffset s13 h13e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]

end PyLean.PyGrammar.Peg
