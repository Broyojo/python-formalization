import PyLean.PyGrammar.Peg.Rules.InvalidTargets
import PyLean.PyGrammar.Peg.Rules.AsTarget

/-! `invalid_dotted_as_name` and `invalid_import_from_as_name` (`Grammar/python.gram:1438-1445`)
rule by rule, with the lookahead group `NAME (',' | ')' | ';' | NEWLINE)` (`_tmp_139`, `_tmp_175`). -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `_tmp_175: ',' | ')' | ';' | NEWLINE` (the group inside the lookahead): at `,` `)` `;` or
`NEWLINE` (12, 8, 13, 4) that token with the mark past it; at any other token `NULL` with the mark
back. -/
def Tmp175 : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  ((t.type = 12 ∨ t.type = 8 ∨ t.type = 13 ∨ t.type = 4) →
    callRule (f + 8) 452 p = (.tok t, { q with mark := p.mark + 1 }.leave)) ∧
  (t.type ≠ 12 → t.type ≠ 8 → t.type ≠ 13 → t.type ≠ 4 → callRule (f + 8) 452 p = (.null, q.leave))

theorem tmp175_proven : Tmp175 := by
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
  have qe : q.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 452 = r452 from rfl, r452]
  refine ⟨fun ht => ?_, fun h12 h8 h13 h4 => ?_⟩
  · rcases ht with ht | ht | ht | ht
    · rw [alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [e1, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f (by omega)])), hq,
        alts_ok (by rfl) qe (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f (by omega)])), hq,
        alts_fail (by rfl) qe (items_call_null (by rw [ek, ite_f (by omega)])), hq,
        alts_ok (by rfl) qe (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f (by omega)])), hq,
        alts_fail (by rfl) qe (items_call_null (by rw [ek, ite_f (by omega)])), hq,
        alts_fail (by rfl) qe (items_call_null (by rw [ek, ite_f (by omega)])), hq,
        alts_ok (by rfl) qe (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f h12])), hq,
      alts_fail (by rfl) qe (items_call_null (by rw [ek, ite_f h8])), hq,
      alts_fail (by rfl) qe (items_call_null (by rw [ek, ite_f h13])), hq,
      alts_fail (by rfl) qe (items_call_null (by rw [ek, ite_f h4])), hq, alts_nil]
    rfl

/-- `_tmp_139: NAME (',' | ')' | ';' | NEWLINE)` (the group of the negative lookahead in both
rules): a `NAME` (`_PyPegen_name_token`) and then `_tmp_175` give a non-`NULL` value (the default
action of a two-item alternative, `_PyPegen_dummy_name`); no `NAME`, or a `NAME` followed by none
of the four tokens, gives `NULL` with the mark back. -/
def Tmp139 : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (s : PS), nameToken p.enter = (.null, s) →
    callRule (f + 6) 416 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (n x : Ast) (s s' : PS), nameToken p.enter = (n, s) → n ≠ .null → callRule f 452 s = (x, s') →
    x ≠ .null → callRule (f + 6) 416 p = (rec_ .PDummy [], s'.leave)) ∧
  (∀ (n : Ast) (s s' : PS), nameToken p.enter = (n, s) → n ≠ .null → callRule f 452 s = (.null, s') →
    callRule (f + 6) 416 p = (.null, { s' with mark := p.mark }.leave))

theorem tmp139_proven : Tmp139 := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 416 = r416 from rfl, r416]
  refine ⟨fun s h1 => ?_, fun n x s s' h1 hn h2 hx => ?_, fun n s s' h1 hn h2 => ?_⟩
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_rule, h2]) hx, items_nil]),
      altResult]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call_null (by rw [call_rule, h2])]), alts_nil]
    rfl

/-- The `%s` of the import-target message, for every name `_PyPegen_get_expr_name` returns. -/
theorem importTargetMsg (nm : String) (h : nm ∈ exprNames) :
    msgOf [.str ("cannot use %s as import target".toList.map Char.toNat),
      .str (nm.toList.map Char.toNat)] = "cannot use " ++ nm ++ " as import target" := by
  revert nm
  decide +kernel

/-- `_PyPegen_get_expr_name` of a number constant (`import a as 1`) is "literal". -/
theorem exprName_number (v : PyConst) (l : Option Loc)
    (hv : v ≠ .none ∧ v ≠ .false_ ∧ v ≠ .true_ ∧ v ≠ .ellipsis) (rest : List Ast) :
    exprName (.node .Constant (.const v :: rest) l) = some "literal" := by
  obtain ⟨h1, h2, h3, h4⟩ := hv
  cases v <;> simp_all [exprName]

/-- `invalid_dotted_as_name` (`Grammar/python.gram:1438-1441`):
```
    | dotted_name 'as' !(NAME (',' | ')' | ';' | NEWLINE)) a=expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a,
            "cannot use %s as import target", _PyPegen_get_expr_name(a)) }
```
No `EXTRA`. `dotted_name` (32), `as` (698), the negative lookahead on `_tmp_139` (416) and
`expression` (109) from the mark after `as` raise "cannot use <name of a> as import target" over
`a` (`import a as 1` says "literal", at the `1`), the rule ending `NULL` with `error_indicator` set.
When `_tmp_139` matches (the target is a `NAME` followed by `,` `)` `;` or `NEWLINE`, as in a valid
`import a as b`) the rule gives `NULL` with the mark back and no error; so does a missing
`dotted_name`, `as` or `expression`. Note that the lookahead looks only one token past the name:
`import a as b c` passes it and names "name" (`dottedAsNameNameTarget_refuted`). -/
def InvalidDottedAsName : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (d n a : Ast) (c : Token) (nm : String) (s1 s2 s3 s4 : PS),
    callRule (f + 3) 32 p.enter = (d, s1) → d ≠ .null → expectToken 698 s1 = (.tok c, s2) →
    callRule (f + 1) 416 s2 = (n, s3) → nonNull n = false →
    callRule f 109 { s3 with mark := s2.mark } = (a, s4) → a ≠ .null → s4.errorIndicator = false →
    exprName a = some nm →
    callRule (f + 8) 238 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset
        (locOf a).endLineno (locOf a).endColOffset ("cannot use " ++ nm ++ " as import target")
          s4).2 with errorIndicator := true }.leave)) ∧
  (∀ (d n : Ast) (c : Token) (s1 s2 s3 : PS),
    callRule (f + 3) 32 p.enter = (d, s1) → d ≠ .null → expectToken 698 s1 = (.tok c, s2) →
    callRule (f + 1) 416 s2 = (n, s3) → nonNull n = true →
    callRule (f + 8) 238 p = (.null, { s3 with mark := p.mark }.leave)) ∧
  (∀ (d n : Ast) (c : Token) (s1 s2 s3 s4 : PS),
    callRule (f + 3) 32 p.enter = (d, s1) → d ≠ .null → expectToken 698 s1 = (.tok c, s2) →
    callRule (f + 1) 416 s2 = (n, s3) → nonNull n = false →
    callRule f 109 { s3 with mark := s2.mark } = (.null, s4) →
    callRule (f + 8) 238 p = (.null, { s4 with mark := p.mark }.leave)) ∧
  (∀ (d : Ast) (s1 s2 : PS), callRule (f + 3) 32 p.enter = (d, s1) → d ≠ .null →
    expectToken 698 s1 = (.null, s2) →
    callRule (f + 8) 238 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (s1 : PS), callRule (f + 3) 32 p.enter = (.null, s1) →
    callRule (f + 8) 238 p = (.null, { s1 with mark := p.mark }.leave))

theorem invalidDottedAsName_proven : InvalidDottedAsName := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 238 = r238 from rfl, r238]
  refine ⟨fun d n a c nm s1 s2 s3 s4 h1 hd h2 h3 hn h4 ha h4e hnm => ?_,
    fun d n c s1 s2 s3 h1 hd h2 h3 hn => ?_, fun d n c s1 s2 s3 s4 h1 hd h2 h3 hn h4 => ?_,
    fun d s1 s2 h1 hd h2 => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hd, items_call (by rw [call_tok, h2]) (by simp),
        items_look (by rw [call_rule, h3]) hn, items_call (by rw [call_rule, h4]) ha, items_nil]),
      altResult_plain rfl rfl]
    have g2 : ((((#[] : Array Ast).push d).push (.tok c)).push a).getD 2 .null = a := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g2, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, hnm]
    rw [importTargetMsg nm (exprName_mem hnm)]
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot use " ++ nm ++ " as import target")
      (locOf a).lineno (locOf a).colOffset (locOf a).endLineno (locOf a).endColOffset s4 h4e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hd, items_call (by rw [call_tok, h2]) (by simp),
        items_look_fail (by rw [call_rule, h3]) (by simpa using hn)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hd, items_call (by rw [call_tok, h2]) (by simp),
        items_look (by rw [call_rule, h3]) hn, items_call_null (by rw [call_rule, h4])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hd, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `invalid_import_from_as_name` (`Grammar/python.gram:1442-1445`):
```
    | NAME 'as' !(NAME (',' | ')' | ';' | NEWLINE)) a=expression {
        RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a,
            "cannot use %s as import target", _PyPegen_get_expr_name(a)) }
```
As `InvalidDottedAsName`, with `NAME` (`_PyPegen_name_token`) in place of `dotted_name`
(`from x import a as 1` says "literal" at the `1`). -/
def InvalidImportFromAsName : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (d n a : Ast) (c : Token) (nm : String) (s1 s2 s3 s4 : PS),
    nameToken p.enter = (d, s1) → d ≠ .null → expectToken 698 s1 = (.tok c, s2) →
    callRule (f + 1) 416 s2 = (n, s3) → nonNull n = false →
    callRule f 109 { s3 with mark := s2.mark } = (a, s4) → a ≠ .null → s4.errorIndicator = false →
    exprName a = some nm →
    callRule (f + 8) 239 p =
      (.null, { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset
        (locOf a).endLineno (locOf a).endColOffset ("cannot use " ++ nm ++ " as import target")
          s4).2 with errorIndicator := true }.leave)) ∧
  (∀ (d n : Ast) (c : Token) (s1 s2 s3 : PS),
    nameToken p.enter = (d, s1) → d ≠ .null → expectToken 698 s1 = (.tok c, s2) →
    callRule (f + 1) 416 s2 = (n, s3) → nonNull n = true →
    callRule (f + 8) 239 p = (.null, { s3 with mark := p.mark }.leave)) ∧
  (∀ (d n : Ast) (c : Token) (s1 s2 s3 s4 : PS),
    nameToken p.enter = (d, s1) → d ≠ .null → expectToken 698 s1 = (.tok c, s2) →
    callRule (f + 1) 416 s2 = (n, s3) → nonNull n = false →
    callRule f 109 { s3 with mark := s2.mark } = (.null, s4) →
    callRule (f + 8) 239 p = (.null, { s4 with mark := p.mark }.leave)) ∧
  (∀ (d : Ast) (s1 s2 : PS), nameToken p.enter = (d, s1) → d ≠ .null →
    expectToken 698 s1 = (.null, s2) →
    callRule (f + 8) 239 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (s1 : PS), nameToken p.enter = (.null, s1) →
    callRule (f + 8) 239 p = (.null, { s1 with mark := p.mark }.leave))

theorem invalidImportFromAsName_proven : InvalidImportFromAsName := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 239 = r239 from rfl, r239]
  refine ⟨fun d n a c nm s1 s2 s3 s4 h1 hd h2 h3 hn h4 ha h4e hnm => ?_,
    fun d n c s1 s2 s3 h1 hd h2 h3 hn => ?_, fun d n c s1 s2 s3 s4 h1 hd h2 h3 hn h4 => ?_,
    fun d s1 s2 h1 hd h2 => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hd, items_call (by rw [call_tok, h2]) (by simp),
        items_look (by rw [call_rule, h3]) hn, items_call (by rw [call_rule, h4]) ha, items_nil]),
      altResult_plain rfl rfl]
    have g2 : ((((#[] : Array Ast).push d).push (.tok c)).push a).getD 2 .null = a := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper,
      raiseRange, List.drop_succ_cons, List.drop_zero, g2, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, hnm]
    rw [importTargetMsg nm (exprName_mem hnm)]
    have herr := raiseEKL_errOcc "SyntaxError" ("cannot use " ++ nm ++ " as import target")
      (locOf a).lineno (locOf a).colOffset (locOf a).endLineno (locOf a).endColOffset s4 h4e
    split
    rename_i u s' heq
    rw [heq] at herr
    simp only at herr
    simp [nonNull, herr, heq]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hd, items_call (by rw [call_tok, h2]) (by simp),
        items_look_fail (by rw [call_rule, h3]) (by simpa using hn)]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hd, items_call (by rw [call_tok, h2]) (by simp),
        items_look (by rw [call_rule, h3]) hn, items_call_null (by rw [call_rule, h4])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hd, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl

/-- The two error rules with the lookahead group they guard on. -/
def InvalidAsNameRules : Prop := InvalidDottedAsName ∧ InvalidImportFromAsName ∧ Tmp139 ∧ Tmp175
theorem invalidAsNameRules_proven : InvalidAsNameRules :=
  ⟨invalidDottedAsName_proven, invalidImportFromAsName_proven, tmp139_proven, tmp175_proven⟩

end PyLean.PyGrammar.Peg
