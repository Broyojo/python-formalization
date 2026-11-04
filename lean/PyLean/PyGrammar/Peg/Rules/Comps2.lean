import PyLean.PyGrammar.Peg.Rules.Comps

/-! `dictcomp`, `for_if_clause` and `expressions` (`Grammar/python.gram:710-714`, `1050-1075`),
rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `dictcomp` -/

/-- `'{' a=kvpair b=for_if_clauses '}'` failing from the entry state `q`, ending in `s`. -/
def DCA0Fails (f : Nat) (m : Nat) (q s : PS) : Prop :=
  ((q.tokenAt m).type ≠ 25 ∧ s = q) ∨
  ((q.tokenAt m).type = 25 ∧ callRule (f + 4) 180 { q with mark := m + 1 } = (.null, s)) ∨
  ((q.tokenAt m).type = 25 ∧ ∃ (a : Ast) (s1 : PS), callRule (f + 4) 180 { q with mark := m + 1 } = (a, s1) ∧
    a ≠ .null ∧ callRule (f + 3) 181 s1 = (.null, s)) ∨
  ((q.tokenAt m).type = 25 ∧ ∃ (a b : Ast) (s1 s2 : PS), callRule (f + 4) 180 { q with mark := m + 1 } = (a, s1) ∧
    a ≠ .null ∧ callRule (f + 3) 181 s1 = (b, s2) ∧ b ≠ .null ∧ expectToken 26 s2 = (.null, s))

/-- `'{' '**' a=expression b=for_if_clauses '}'` failing from `Y`, ending in `s`. -/
def DCA1Fails (f : Nat) (Y s : PS) : Prop :=
  expectToken 25 Y = (.null, s) ∨
  (∃ (c : Token) (s1 : PS), expectToken 25 Y = (.tok c, s1) ∧ expectToken 35 s1 = (.null, s)) ∨
  (∃ (c d : Token) (s1 s2 : PS), expectToken 25 Y = (.tok c, s1) ∧ expectToken 35 s1 = (.tok d, s2) ∧
    callRule (f + 2) 109 s2 = (.null, s)) ∨
  (∃ (c d : Token) (a : Ast) (s1 s2 s3 : PS), expectToken 25 Y = (.tok c, s1) ∧
    expectToken 35 s1 = (.tok d, s2) ∧ callRule (f + 2) 109 s2 = (a, s3) ∧ a ≠ .null ∧
    callRule (f + 1) 181 s3 = (.null, s)) ∨
  (∃ (c d : Token) (a b : Ast) (s1 s2 s3 s4 : PS), expectToken 25 Y = (.tok c, s1) ∧
    expectToken 35 s1 = (.tok d, s2) ∧ callRule (f + 2) 109 s2 = (a, s3) ∧ a ≠ .null ∧
    callRule (f + 1) 181 s3 = (b, s4) ∧ b ≠ .null ∧ expectToken 26 s4 = (.null, s))

/-- `dictcomp` (`Grammar/python.gram:1070-1072`):
```
    | '{' a=kvpair b=for_if_clauses '}' { _PyAST_DictComp(a->key, a->value, b, EXTRA) }
    | '{' '**' a=expression b=for_if_clauses '}' { _PyAST_DictComp(a, NULL, b, EXTRA) }
```
At `{` (25), a `kvpair` (180), `for_if_clauses` (181) and `}` (26) give `DictComp(key, value,
generators)` from the pair's fields; once that fails, from the start mark, `{`, `**` (35), an
`expression` (109), `for_if_clauses` and `}` give `DictComp(a, NULL, generators)` (PEP 798, new
in 3.15: the element is any `expression`, not only a `bitwise_or`); otherwise `NULL` with the mark
back. -/
def Dictcomp : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 25 → ∀ (kv b : Ast) (c : Token) (s1 s2 s3 : PS),
    callRule (f + 4) 180 { q with mark := p.mark + 1 } = (kv, s1) → kv ≠ .null →
    callRule (f + 3) 181 s1 = (b, s2) → b ≠ .null → expectToken 26 s2 = (.tok c, s3) →
    s3.errorIndicator = false →
    callRule (f + 10) 186 p =
      (mkAt .DictComp [attrOf kv "key", attrOf kv "value", b] (extraLoc t s3), s3.leave)) ∧
  (∀ (s0 : PS), DCA0Fails f p.mark q s0 → s0.errorIndicator = false →
    (∀ (a b : Ast) (c d c' : Token) (s1 s2 s3 s4 s5 : PS),
      expectToken 25 { s0 with mark := p.mark } = (.tok c, s1) → expectToken 35 s1 = (.tok d, s2) →
      callRule (f + 2) 109 s2 = (a, s3) → a ≠ .null → callRule (f + 1) 181 s3 = (b, s4) → b ≠ .null →
      expectToken 26 s4 = (.tok c', s5) → s5.errorIndicator = false →
      callRule (f + 10) 186 p = (mkAt .DictComp [a, .null, b] (extraLoc t s5), s5.leave)) ∧
    (∀ (s : PS), DCA1Fails f { s0 with mark := p.mark } s →
      callRule (f + 10) 186 p = (.null, { s with mark := p.mark }.leave)))

theorem dictcomp_proven : Dictcomp := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 186 = r186 from rfl, r186]
  have hA : ∀ s, DCA0Fails f p.mark q s →
      runItems (f + 7) [.call (.tok 25), .call (.rule 180), .call (.rule 181), .call (.tok 26)] #[]
        false q = ((none, false), s) := by
    intro s hs
    rcases hs with ⟨ht, rfl⟩ | ⟨ht, h1⟩ | ⟨ht, a, s1, h1, ha, h2⟩ | ⟨ht, a, b, s1, s2, h1, ha, h2, hb, h3⟩
    · rw [items_call_null (by rw [ek, ite_f ht])]
    · rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call_null (by rw [call_rule, h2])]
    · rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_rule, h2]) hb, items_call_null (by rw [call_tok, h3])]
  refine ⟨fun ht kv b c s1 s2 s3 h1 hk h2 hb h3 h3e => ?_, fun s0 h0 h0e =>
    ⟨fun a b c d c' s1 s2 s3 s4 s5 h1 h2 h3 ha h4 hb h5 h5e => ?_, fun s h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) hk,
        items_call (by rw [call_rule, h2]) hb, items_call (by rw [call_tok, h3]) (by simp),
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (hA s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ha, items_call (by rw [call_rule, h4]) hb,
        items_call (by rw [call_tok, h5]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h5e]
  · have hB : runItems (f + 6) [.call (.tok 25), .call (.tok 35), .call (.rule 109), .call (.rule 181),
        .call (.tok 26)] #[] false { s0 with mark := p.mark } = ((none, false), s) := by
      rcases h1 with h1 | ⟨c, t1, h1, h2⟩ | ⟨c, d, t1, t2, h1, h2, h3⟩ |
          ⟨c, d, a, t1, t2, t3, h1, h2, h3, ha, h4⟩ | ⟨c, d, a, b, t1, t2, t3, t4, h1, h2, h3, ha, h4, hb, h5⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_tok, h2])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
          items_call_null (by rw [call_rule, h3])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
          items_call (by rw [call_rule, h3]) ha, items_call_null (by rw [call_rule, h4])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
          items_call (by rw [call_rule, h3]) ha, items_call (by rw [call_rule, h4]) hb,
          items_call_null (by rw [call_tok, h5])]
    rw [alts_fail (by rfl) he (hA s0 h0), alts_fail (by rfl) (E s0 h0e) hB, alts_nil]
    rfl

/-! ### `for_if_clause` -/

/-- The message of `CHECK_VERSION(comprehension_ty, 6, "Async comprehensions are", ...)`. -/
def asyncCompMsg : String := "Async comprehensions are only supported in Python 3.6 and greater"

/-- `'async' 'for' a=star_targets 'in'` failing (before the cut) from `X`, ending in `s`. -/
def FIA0Fails (f : Nat) (X s : PS) : Prop :=
  expectToken 716 X = (.null, s) ∨
  (∃ (c : Token) (s1 : PS), expectToken 716 X = (.tok c, s1) ∧ expectToken 712 s1 = (.null, s)) ∨
  (∃ (c d : Token) (s1 s2 : PS), expectToken 716 X = (.tok c, s1) ∧ expectToken 712 s1 = (.tok d, s2) ∧
    callRule (f + 4) 193 s2 = (.null, s)) ∨
  (∃ (c d : Token) (t : Ast) (s1 s2 s3 : PS), expectToken 716 X = (.tok c, s1) ∧
    expectToken 712 s1 = (.tok d, s2) ∧ callRule (f + 4) 193 s2 = (t, s3) ∧ t ≠ .null ∧
    expectToken 713 s3 = (.null, s))

/-- `'for' a=star_targets 'in'` failing (before the cut) from `Y`, ending in `s`. -/
def FIA1Fails (f : Nat) (Y s : PS) : Prop :=
  expectToken 712 Y = (.null, s) ∨
  (∃ (d : Token) (s2 : PS), expectToken 712 Y = (.tok d, s2) ∧ callRule (f + 4) 193 s2 = (.null, s)) ∨
  (∃ (d : Token) (t : Ast) (s2 s3 : PS), expectToken 712 Y = (.tok d, s2) ∧
    callRule (f + 4) 193 s2 = (t, s3) ∧ t ≠ .null ∧ expectToken 713 s3 = (.null, s))

/-- After the cut, `b=disjunction c=('if' z=disjunction { z })*` failing from `S`, ending in `s`. -/
def FICutFails (f : Nat) (S s : PS) : Prop :=
  callRule (f + 1) 120 S = (.null, s) ∨
  (∃ (b : Ast) (s1 : PS), callRule (f + 1) 120 S = (b, s1) ∧ b ≠ .null ∧ callRule f 365 s1 = (.null, s))

/-- `for_if_clause` (`Grammar/python.gram:1050-1056`):
```
    | 'async' 'for' a=star_targets 'in' ~ b=disjunction c[asdl_expr_seq*]=('if' z=disjunction { z })* {
        CHECK_VERSION(comprehension_ty, 6, "Async comprehensions are", _PyAST_comprehension(a, b, c, 1, p->arena)) }
    | 'for' a=star_targets 'in' ~ b=disjunction c[asdl_expr_seq*]=('if' z=disjunction { z })* {
        _PyAST_comprehension(a, b, c, 0, p->arena) }
    | invalid_for_if_clause
    | invalid_for_target
```
No `EXTRA`. `async` (716) `for` (712), `star_targets` (193), `in` (713), the cut, a `disjunction`
(120) and the `if` loop (`_loop0_88`, 365) give `comprehension(target, iter, ifs, is_async = 1)`
behind `CHECK_VERSION` 6 (`CVRes`); a failure after the cut (`FICutFails`) ends the rule with
`NULL`, no other alternative tried. Once the first fails before its cut, from the start mark, the
same without `async` gives `comprehension(..., 0)`, with the same cut. Once both fail before their
cuts, the first pass gives `NULL` with the mark back; the second `invalid_for_if_clause` (234),
then `invalid_for_target` (235), each from the start mark. -/
def ForIfClause : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (t b cs : Ast) (c d e : Token) (s1 s2 s3 s4 s5 s6 : PS), expectToken 716 p.enter = (.tok c, s1) →
    expectToken 712 s1 = (.tok d, s2) → callRule (f + 4) 193 s2 = (t, s3) → t ≠ .null →
    expectToken 713 s3 = (.tok e, s4) → callRule (f + 1) 120 s4 = (b, s5) → b ≠ .null →
    callRule f 365 s5 = (cs, s6) → cs ≠ .null → s6.errorIndicator = false →
    CVRes 6 asyncCompMsg (callRule (f + 11) 182 p) (mkAst .comprehension_ [t, b, cs, .int 1]) s6) ∧
  (∀ (t : Ast) (c d e : Token) (s1 s2 s3 s4 s : PS), expectToken 716 p.enter = (.tok c, s1) →
    expectToken 712 s1 = (.tok d, s2) → callRule (f + 4) 193 s2 = (t, s3) → t ≠ .null →
    expectToken 713 s3 = (.tok e, s4) → FICutFails f s4 s →
    callRule (f + 11) 182 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (s0 : PS), FIA0Fails f p.enter s0 → s0.errorIndicator = false →
    (∀ (t b cs : Ast) (d e : Token) (s2 s3 s4 s5 s6 : PS),
      expectToken 712 { s0 with mark := p.mark } = (.tok d, s2) → callRule (f + 4) 193 s2 = (t, s3) →
      t ≠ .null → expectToken 713 s3 = (.tok e, s4) → callRule (f + 1) 120 s4 = (b, s5) → b ≠ .null →
      callRule f 365 s5 = (cs, s6) → cs ≠ .null → s6.errorIndicator = false →
      callRule (f + 11) 182 p = (mkAst .comprehension_ [t, b, cs, .int 0], s6.leave)) ∧
    (∀ (t : Ast) (d e : Token) (s2 s3 s4 s : PS),
      expectToken 712 { s0 with mark := p.mark } = (.tok d, s2) → callRule (f + 4) 193 s2 = (t, s3) →
      t ≠ .null → expectToken 713 s3 = (.tok e, s4) → FICutFails f s4 s →
      callRule (f + 11) 182 p = (.null, { s with mark := p.mark }.leave)) ∧
    (∀ (s1 : PS), FIA1Fails f { s0 with mark := p.mark } s1 → s1.errorIndicator = false →
      (s1.callInvalidRules = false →
        callRule (f + 11) 182 p = (.null, { s1 with mark := p.mark }.leave)) ∧
      (s1.callInvalidRules = true → ∀ (v : Ast) (s : PS),
        callRule (f + 4) 234 { s1 with mark := p.mark } = (v, s) → v ≠ .null →
        callRule (f + 11) 182 p = (v, s.leave)) ∧
      (s1.callInvalidRules = true → ∀ (s : PS),
        callRule (f + 4) 234 { s1 with mark := p.mark } = (.null, s) → s.errorIndicator = false → s.callInvalidRules = true →
        (∀ (v : Ast) (s' : PS), callRule (f + 3) 235 { s with mark := p.mark } = (v, s') →
          v ≠ .null → callRule (f + 11) 182 p = (v, s'.leave)) ∧
        (∀ (s' : PS), callRule (f + 3) 235 { s with mark := p.mark } = (.null, s') →
          callRule (f + 11) 182 p = (.null, { s' with mark := p.mark }.leave)))))

theorem forIfClause_proven : ForIfClause := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 182 = r182 from rfl, r182]
  have hA0 : ∀ s0, FIA0Fails f p.enter s0 →
      runItems (f + 8) [.call (.tok 716), .call (.tok 712), .call (.rule 193), .call (.tok 713), .cut,
        .call (.rule 120), .call (.rule 365)] #[] false p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, d, s1, s2, h1, h2, h3⟩ | ⟨c, d, t, s1, s2, s3, h1, h2, h3, ht, h4⟩
    · rw [items_call_null (by rw [call_tok, h1])]
    · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_tok, h2])]
    · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_rule, h3])]
    · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ht, items_call_null (by rw [call_tok, h4])]
  have hA1 : ∀ Y s1, FIA1Fails f Y s1 →
      runItems (f + 7) [.call (.tok 712), .call (.rule 193), .call (.tok 713), .cut,
        .call (.rule 120), .call (.rule 365)] #[] false Y = ((none, false), s1) := by
    intro Y s1 h0
    rcases h0 with h2 | ⟨d, s2, h2, h3⟩ | ⟨d, t, s2, s3, h2, h3, ht, h4⟩
    · rw [items_call_null (by rw [call_tok, h2])]
    · rw [items_call (by rw [call_tok, h2]) (by simp), items_call_null (by rw [call_rule, h3])]
    · rw [items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) ht,
        items_call_null (by rw [call_tok, h4])]
  have hC : ∀ {env : Array Ast} {S s : PS}, FICutFails f S s →
      runItems (f + 3) [.call (.rule 120), .call (.rule 365)] env true S = ((none, true), s) := by
    intro env S s hs
    rcases hs with h5 | ⟨b, s5, h5, hb, h6⟩
    · rw [items_call_null (by rw [call_rule, h5])]
    · rw [items_call (by rw [call_rule, h5]) hb, items_call_null (by rw [call_rule, h6])]
  refine ⟨fun t b cs c d e s1 s2 s3 s4 s5 s6 h1 h2 h3 ht h4 h5 hb h6 hcs h6e => ?_,
    fun t c d e s1 s2 s3 s4 s h1 h2 h3 ht h4 hs => ?_, fun s0 h0 h0e =>
    ⟨fun t b cs d e s2 s3 s4 s5 s6 h2 h3 ht h4 h5 hb h6 hcs h6e => ?_,
      fun t d e s2 s3 s4 s h2 h3 ht h4 hs => ?_, fun s1 h1 h1e =>
      ⟨fun hi => ?_, fun hi v s h7 hv => ?_, fun hi s h7 h7e hsi => ⟨fun v s' h8 hv => ?_, fun s' h8 => ?_⟩⟩⟩⟩
  · try dsimp only
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ht, items_call (by rw [call_tok, h4]) (by simp), items_cut,
        items_call (by rw [call_rule, h5]) hb, items_call (by rw [call_rule, h6]) hcs, items_nil])]
    exact altResult_cvg rfl rfl (by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
      rfl) (by simp [mkAst]) h6e (by decide +kernel)
  · rw [alts_cut (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) ht, items_call (by rw [call_tok, h4]) (by simp), items_cut,
        hC hs])]
    rfl
  · rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) ht,
        items_call (by rw [call_tok, h4]) (by simp), items_cut,
        items_call (by rw [call_rule, h5]) hb, items_call (by rw [call_rule, h6]) hcs, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    simp [mkAst, nonNull, h6e]
  · rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_cut (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h2]) (by simp), items_call (by rw [call_rule, h3]) ht,
        items_call (by rw [call_tok, h4]) (by simp), items_cut, hC hs])]
    rfl
  · rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_fail (by rfl) (E s0 h0e) (hA1 _ s1 h1),
      alts_skip (by simp [hi]), alts_skip (by simp [hi]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_fail (by rfl) (E s0 h0e) (hA1 _ s1 h1),
      alts_ok (by simp [hi]) (E s1 h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h7]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_fail (by rfl) (E s0 h0e) (hA1 _ s1 h1),
      alts_fail (by simp [hi]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h7])]),
      alts_ok (by simp [hsi]) (E s h7e) (by
        dsimp only; rw [items_call (by rw [call_rule, h8]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_fail (by rfl) (E s0 h0e) (hA1 _ s1 h1),
      alts_fail (by simp [hi]) (E s1 h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h7])]),
      alts_fail (by simp [hsi]) (E s h7e) (by dsimp only; rw [items_call_null (by rw [call_rule, h8])]),
      alts_nil]
    rfl

/-- `for_if_clause` with its `if` loop `_loop0_88` (365) and the group `'if' z=disjunction { z }`
(`_tmp_166`, 443; `if` is 700). -/
def ForIfClauseRule : Prop := ForIfClause ∧ Loop0Over 365 443 ∧ TokThen 443 700 120
theorem forIfClauseRule_proven : ForIfClauseRule :=
  ⟨forIfClause_proven, loop0Over_of rfl, tokThen_of rfl⟩

/-! ### `expressions` -/

/-- `expressions` (`Grammar/python.gram:710-714`):
```
    | a=expression b=(',' c=expression { c })+ [','] {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, a, b)), Load, EXTRA) }
    | a=expression ',' { _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_singleton_seq(p, a)), Load, EXTRA) }
    | expression
```
An `expression` (109), the `+` loop of `, expression` (`_loop1_55`, 332) and an optional `,` give
`Tuple([a] + rest, Load)`; once that fails, from the start mark, an `expression` and `,` give the
one-element `Tuple([a], Load)`; then an `expression` alone is the result; otherwise `NULL` with the
mark back. -/
def ExpressionsRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a b x : Ast) (s1 s2 s3 : PS), callRule (f + 2) 109 q = (a, s1) → a ≠ .null →
    callRule (f + 1) 332 s1 = (b, s2) → b ≠ .null → expectToken 12 s2 = (x, s3) →
    s3.errorIndicator = false →
    callRule (f + 7) 108 p = (mkAt .Tuple [.seq (a :: seqOf b), opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (∀ (s0 : PS), (callRule (f + 2) 109 q = (.null, s0) ∨
      ∃ a s1, callRule (f + 2) 109 q = (a, s1) ∧ a ≠ .null ∧ callRule (f + 1) 332 s1 = (.null, s0)) →
    s0.errorIndicator = false →
    (∀ (a : Ast) (c : Token) (s1 s2 : PS), callRule (f + 1) 109 { s0 with mark := p.mark } = (a, s1) →
      a ≠ .null → expectToken 12 s1 = (.tok c, s2) → s2.errorIndicator = false →
      callRule (f + 7) 108 p = (mkAt .Tuple [.seq [a], opNode .Load] (extraLoc t s2), s2.leave)) ∧
    (∀ (s1 : PS), (callRule (f + 1) 109 { s0 with mark := p.mark } = (.null, s1) ∨
        ∃ a s1', callRule (f + 1) 109 { s0 with mark := p.mark } = (a, s1') ∧ a ≠ .null ∧
          expectToken 12 s1' = (.null, s1)) →
      s1.errorIndicator = false →
      (∀ (v : Ast) (s : PS), callRule f 109 { s1 with mark := p.mark } = (v, s) → v ≠ .null →
        callRule (f + 7) 108 p = (v, s.leave)) ∧
      (∀ (s : PS), callRule f 109 { s1 with mark := p.mark } = (.null, s) →
        callRule (f + 7) 108 p = (.null, { s with mark := p.mark }.leave))))

theorem expressionsRule_proven : ExpressionsRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 108 = r108 from rfl, r108]
  refine ⟨fun a b x s1 s2 s3 h1 ha h2 hb h3 h3e => ?_, fun s0 h0 h0e =>
    ⟨fun a c s1 s2 h1 ha h2 h2e => ?_, fun s1 h1 h1e => ⟨fun v s h2 hv => ?_, fun s h2 => ?_⟩⟩⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb,
        items_opt (by rw [call_tok, h3]) h3e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e, opNode, StateT.pure, StateT.bind, pure, bind]
  all_goals
    have hA : runItems (f + 4) [.call (.rule 109), .call (.rule 332), .opt (.tok 12)] #[] false q =
        ((none, false), s0) := by
      rcases h0 with h0 | ⟨a, t1, h0, ha, h0'⟩
      · rw [items_call_null (by rw [call_rule, h0])]
      · rw [items_call (by rw [call_rule, h0]) ha, items_call_null (by rw [call_rule, h0'])]
  · rw [alts_fail (by rfl) he hA, alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e, opNode, StateT.pure, StateT.bind, pure, bind]
  all_goals
    have hB : runItems (f + 3) [.call (.rule 109), .call (.tok 12)] #[] false { s0 with mark := p.mark } =
        ((none, false), s1) := by
      rcases h1 with h1 | ⟨a, t1, h1, ha, h1'⟩
      · rw [items_call_null (by rw [call_rule, h1])]
      · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h1'])]
  · rw [alts_fail (by rfl) he hA, alts_fail (by rfl) (E s0 h0e) hB, alts_ok (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he hA, alts_fail (by rfl) (E s0 h0e) hB, alts_fail (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h2])]), alts_nil]
    rfl

/-- `expressions` with its loop `_loop1_55` (332) and the group `',' c=expression { c }`
(`_tmp_16`, 293). -/
def ExpressionsRuleFull : Prop := ExpressionsRule ∧ Loop1Over 332 293 ∧ TokThen 293 12 109
theorem expressionsRuleFull_proven : ExpressionsRuleFull :=
  ⟨expressionsRule_proven, loop1Over_of rfl, tokThen_of rfl⟩


def ListcompRule : Prop := CompRule 183 9 116 10 .ListComp
theorem listcompRule_proven : ListcompRule := listcomp_proven
def SetcompRule : Prop := CompRule 184 25 116 26 .SetComp
theorem setcompRule_proven : SetcompRule := setcomp_proven

end PyLean.PyGrammar.Peg
