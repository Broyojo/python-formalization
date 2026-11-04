import PyLean.PyGrammar.Peg.Rules.Base

/-! The start rules and `statement` of `Grammar/python.gram:89-103`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The `TypeIgnore` nodes `_PyPegen_make_module` builds from the `# type: ignore` comments the
tokenizer recorded. -/
def typeIgnoreNodes (s : PS) : List Ast :=
  s.typeIgnores.map fun (line, tag) => mkAst .TypeIgnore [.int line, .str (utf8Decode tag)]

/-! ### `file` -/

/-- `file: a=[statements] ENDMARKER { _PyPegen_make_module(p, a) }` (`Grammar/python.gram:89`).
After the optional `statements`, the next token must be `ENDMARKER`: then the result is
`Module(a, type_ignores)`; any other token makes the rule fail, so a parse of `file` consumes all
the input. An error from `statements` fails the rule. -/
def FileRule : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  ∀ (a : Ast) (s1 : PS), callRule (f + 1) 4 p.enter = (a, s1) →
  (s1.errorIndicator = true → callRule (f + 6) 0 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (s1.errorIndicator = false → ∀ (te : Token) (s2 : PS), expectToken 0 s1 = (.tok te, s2) →
    s2.errorIndicator = false →
    callRule (f + 6) 0 p = (mkAst .Module [a, .seq (typeIgnoreNodes s2)], s2.leave)) ∧
  (s1.errorIndicator = false → ∀ (s2 : PS), expectToken 0 s1 = (.null, s2) →
    callRule (f + 6) 0 p = (.null, { s2 with mark := p.mark }.leave))

theorem fileRule_proven : FileRule := by
  intro f p he hl a s1 h1
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 0 = r0 from rfl, r0]
  refine ⟨fun h1e => ?_, fun h1e te s2 h2 h2e => ?_, fun h1e s2 h2 => ?_⟩
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_opt_err (by rw [call_rule, h1]) h1e]),
      alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_opt (by rw [call_rule, h1]) h1e, items_call (by rw [call_tok, h2]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, get,
      getThe, MonadStateOf.get, StateT.get, h2e, typeIgnoreNodes]
    simp [mkAst, nonNull, h2e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_opt (by rw [call_rule, h1]) h1e, items_call_null (by rw [call_tok, h2])]),
      alts_nil]
    rfl

/-! ### `eval` -/

/-- `eval: a=expressions NEWLINE* ENDMARKER { _PyAST_Expression(a, p->arena) }`
(`Grammar/python.gram:91`): `expressions`, any newlines (the artificial loop `_loop0_1`), then
`ENDMARKER`, giving `Expression(a)`; without `ENDMARKER` there the rule fails. -/
def EvalRule : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  ∀ (a nl : Ast) (s1 s2 : PS), callRule (f + 2) 108 p.enter = (a, s1) → a ≠ .null →
  callRule (f + 1) 278 s1 = (nl, s2) → nl ≠ .null →
  (∀ (te : Token) (s3 : PS), expectToken 0 s2 = (.tok te, s3) → s3.errorIndicator = false →
    callRule (f + 7) 2 p = (mkAst .Expression [a], s3.leave)) ∧
  (∀ (s3 : PS), expectToken 0 s2 = (.null, s3) →
    callRule (f + 7) 2 p = (.null, { s3 with mark := p.mark }.leave))

theorem evalRule_proven : EvalRule := by
  intro f p he hl a nl s1 s2 h1 ha h2 hn
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 2 = r2 from rfl, r2]
  refine ⟨fun te s3 h3 h3e => ?_, fun s3 h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hn,
        items_call (by rw [call_tok, h3]) (by simp), items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hn,
        items_call_null (by rw [call_tok, h3])]), alts_nil]
    rfl

/-! ### `interactive` -/

/-- `interactive: a=statement_newline { _PyAST_Interactive(a, p->arena) }`
(`Grammar/python.gram:90`): `Interactive(a)` around `statement_newline`, `NULL` if it fails. -/
def InteractiveRule : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK → ∀ (a : Ast) (s1 : PS), callRule f 7 p.enter = (a, s1) →
  (a ≠ .null → s1.errorIndicator = false →
    callRule (f + 5) 1 p = (mkAst .Interactive [a], s1.leave)) ∧
  (a = .null → callRule (f + 5) 1 p = (.null, { s1 with mark := p.mark }.leave))

theorem interactiveRule_proven : InteractiveRule := by
  intro f p he hl a s1 h1
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 1 = r1 from rfl, r1]
  refine ⟨fun ha h1e => ?_, fun ha => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h1e]
  · subst ha
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl

/-! ### `statement` -/

theorem registerStmts_val (a : Ast) (s : PS) :
    (registerStmts a s).1 = a ∧ (registerStmts a s).2.errorIndicator = s.errorIndicator ∧
      (registerStmts a s).2.tok = s.tok := by
  unfold registerStmts
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · cases (seqOf a).getLast? with
    | none => exact ⟨rfl, rfl, rfl⟩
    | some last =>
      dsimp only
      split
      · exact ⟨rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl⟩

/-- `statement` (`Grammar/python.gram:99-101`):
```
    | a=compound_stmt { (asdl_stmt_seq*)_PyPegen_register_stmts(p, (asdl_stmt_seq*)_PyPegen_singleton_seq(p, a)) }
    | a[asdl_stmt_seq*]=simple_stmts { a }
```
`compound_stmt` is tried first: if it succeeds the result is the one-statement sequence, passed
through `_PyPegen_register_stmts` (which records its location in the second pass); only if it
fails does `simple_stmts` run, from the same mark, and its sequence is the result. -/
def StatementRule : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK → ∀ (c : Ast) (s1 : PS), callRule (f + 1) 10 p.enter = (c, s1) →
  (c ≠ .null → s1.errorIndicator = false →
    callRule (f + 6) 5 p = (.seq [c], (registerStmts (.seq [c]) s1).2.leave)) ∧
  (c = .null → s1.errorIndicator = false → ∀ (v : Ast) (s2 : PS),
    callRule f 8 { s1 with mark := p.mark } = (v, s2) → v ≠ .null → s2.errorIndicator = false →
    callRule (f + 6) 5 p = (v, s2.leave))

theorem statementRule_proven : StatementRule := by
  intro f p he hl c s1 h1
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 5 = r5 from rfl, r5]
  refine ⟨fun hc h1e => ?_, fun hc h1e v s2 h2 hv h2e => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hc, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp only [List.getD_cons_zero, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      Array.size_empty, Option.getD_some, Nat.zero_add, Nat.reduceEqDiff, ↓reduceIte]
    obtain ⟨r1, r2, -⟩ := registerStmts_val (.seq [c]) s1
    simp only [r1, r2, h1e, nonNull]
    simp
  · subst hc
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have hv' : nonNull v = true := by cases v <;> simp_all [nonNull]
    simp [hv', h2e]

end PyLean.PyGrammar.Peg
