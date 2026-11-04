import PyLean.PyGrammar.Peg.Rules.Invalid2

/-! Displays and comprehensions (`Grammar/python.gram:710-714`, `741-743`, `1028-1075`), rule by
rule: `expressions`, `star_named_expressions(_sequence)`, `dict`, `double_starred_kvpairs`,
`double_starred_kvpair`, `kvpair`, `for_if_clauses`, `for_if_clause`, `listcomp`, `setcomp`,
`genexp`, `dictcomp`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `CHECK_VERSION` with any version and message -/

/-- What a rule function returns (`r`) when its alternative's action is
`CHECK_VERSION(t, ver, pre, v)` reached in state `s`, `msg` being
`"<pre> only supported in Python 3.<ver> and greater"`. -/
def CVRes (ver : Nat) (msg : String) (r : Ast × PS) (v : Ast) (s : PS) : Prop :=
  (ver ≤ s.featureVersion → r = (v, s.leave)) ∧
  (s.featureVersion < ver → r.1 = .null ∧ r.2.errorIndicator = true ∧
    r.2.tok = (raiseError0 "SyntaxError" msg { s with errorIndicator := true }).2.tok)

theorem altResult_cvg {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {node : AE}
    {v : Ast} {ver : Nat} {pre msg : String}
    (h1 : a.action = some (.checkVersion (.int ver) (.str pre) node))
    (h2 : a.extra = false) (hn : evalA env {} node s = (v, s)) (hnn : v ≠ .null)
    (he : s.errorIndicator = false)
    (hmsg : toString (cpsStr (pre.toList.map Char.toNat)) ++ toString " only supported in Python 3." ++
      toString (ver : Int) ++ toString " and greater" = msg) :
    CVRes ver msg (((altResult a g env st s).1.getD .null), (altResult a g env st s).2.leave) v s := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · rw [altResult_plain h1 h2]
    dsimp only
    rw [evalA_cv_ok hn hnn (by omega)]
    have : nonNull v = true := by cases v <;> simp_all [nonNull]
    simp [this, he]
  · have hlow := evalA_cv_low (m := pre) hn hnn (by omega : (s.featureVersion : Int) < ver)
    rw [hmsg] at hlow
    apply cv_low_result msg
    rw [altResult_plain h1 h2]
    dsimp only
    rw [hlow]

/-! ### `x=gather [','] { x }` -/

/-- `star_named_expressions`, `star_named_expressions_sequence`, `double_starred_kvpairs`
(`Grammar/python.gram:741`, `743`, `1036`): `a=','.x+ [','] { a }`. No `EXTRA`. The gather (`g`)
and an optional trailing `,` (12) give the gather's sequence; no gather gives `NULL` with the mark
back. -/
def GatherOptComma (id g : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a x : Ast) (s1 s2 : PS), callRule (f + 1) g p.enter = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (x, s2) → s2.errorIndicator = false → callRule (f + 6) id p = (a, s2.leave)) ∧
  (∀ (s1 : PS), callRule (f + 1) g p.enter = (.null, s1) →
    callRule (f + 6) id p = (.null, { s1 with mark := p.mark }.leave))

theorem gatherOptComma_of {id g : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule g), .opt (.tok 12)] (some (.var 0)) 2 false false]) :
    GatherOptComma id g := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  refine ⟨fun a x s1 s2 h1 ha h2 h2e => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_tok, h2]) h2e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `star_named_expressions` (114) with `_gather_58` (335) of `star_named_expression`. -/
def StarNamedExpressionsRule : Prop := GatherOptComma 114 335 ∧ GatherSep 335 334 116
theorem starNamedExpressionsRule_proven : StarNamedExpressionsRule :=
  ⟨gatherOptComma_of rfl, gatherSep_of rfl rfl⟩
/-- `star_named_expressions_sequence` (115, new in 3.15) with `_gather_60` (337) of
`star_named_expression_sequence` (117). -/
def StarNamedExpressionsSequenceRule : Prop := GatherOptComma 115 337 ∧ GatherSep 337 336 117
theorem starNamedExpressionsSequenceRule_proven : StarNamedExpressionsSequenceRule :=
  ⟨gatherOptComma_of rfl, gatherSep_of rfl rfl⟩
/-- `double_starred_kvpairs` (178) with `_gather_86` (363) of `double_starred_kvpair` (179). -/
def DoubleStarredKvpairsRule : Prop := GatherOptComma 178 363 ∧ GatherSep 363 362 179
theorem doubleStarredKvpairsRule_proven : DoubleStarredKvpairsRule :=
  ⟨gatherOptComma_of rfl, gatherSep_of rfl rfl⟩

/-! ### `kvpair`, `double_starred_kvpair`, `dict` -/

/-- `kvpair[KeyValuePair*]: a=expression ':' b=expression { _PyPegen_key_value_pair(p, a, b) }`
(`Grammar/python.gram:1042`): an `expression` (109), `:` (11) and an `expression` give the
`KeyValuePair` record `(key, value)`; without any of them `NULL` with the mark back. -/
def Kvpair : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a b : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 109 p.enter = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok c, s2) → callRule f 109 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false → callRule (f + 7) 180 p = (rec_ .PKeyValuePair [a, b], s3.leave)) ∧
  (∀ (s1 : PS), callRule (f + 2) 109 p.enter = (.null, s1) →
    callRule (f + 7) 180 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (a : Ast) (s1 s2 : PS), callRule (f + 2) 109 p.enter = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.null, s2) → callRule (f + 7) 180 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (a : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 109 p.enter = (a, s1) → a ≠ .null →
    expectToken 11 s1 = (.tok c, s2) → callRule f 109 s2 = (.null, s3) →
    callRule (f + 7) 180 p = (.null, { s3 with mark := p.mark }.leave))

theorem kvpair_proven : Kvpair := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 180 = r180 from rfl, r180]
  refine ⟨fun a b c s1 s2 s3 h1 ha h2 h3 hb h3e => ?_, fun s1 h1 => ?_, fun a s1 s2 h1 ha h2 => ?_,
    fun a c s1 s2 s3 h1 ha h2 h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_rule, h3])]), alts_nil]
    rfl

/-- `double_starred_kvpair` (`Grammar/python.gram:1038-1040`):
```
    | '**' a=bitwise_or { _PyPegen_key_value_pair(p, NULL, a) }
    | kvpair
```
No `EXTRA`. `**` (35) and a `bitwise_or` (135) give the record `(NULL, a)` (a `**` item: no key);
once that fails, `kvpair` (180) from the start mark is the result, `NULL` with the mark back
without one. -/
def DoubleStarredKvpair : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a : Ast) (c : Token) (s1 s2 : PS), expectToken 35 p.enter = (.tok c, s1) →
    callRule (f + 1) 135 s1 = (a, s2) → a ≠ .null → s2.errorIndicator = false →
    callRule (f + 7) 179 p = (rec_ .PKeyValuePair [.null, a], s2.leave)) ∧
  (∀ (s0 : PS), (expectToken 35 p.enter = (.null, s0) ∨
      ∃ c s1, expectToken 35 p.enter = (.tok c, s1) ∧ callRule (f + 1) 135 s1 = (.null, s0)) →
    s0.errorIndicator = false →
    (∀ (v : Ast) (s : PS), callRule (f + 1) 180 { s0 with mark := p.mark } = (v, s) → v ≠ .null →
      callRule (f + 7) 179 p = (v, s.leave)) ∧
    (∀ (s : PS), callRule (f + 1) 180 { s0 with mark := p.mark } = (.null, s) →
      callRule (f + 7) 179 p = (.null, { s with mark := p.mark }.leave)))

theorem doubleStarredKvpair_proven : DoubleStarredKvpair := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 179 = r179 from rfl, r179]
  refine ⟨fun a c s1 s2 h1 h2 ha h2e => ?_, fun s0 h0 h0e => ⟨fun v s h1 hv => ?_, fun s h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h2e, rec_]
  all_goals
    have hA : runItems (f + 4) [.call (.tok 35), .call (.rule 135)] #[] false p.enter =
        ((none, false), s0) := by
      rcases h0 with h0 | ⟨c, s1, h0, h0'⟩
      · rw [items_call_null (by rw [call_tok, h0])]
      · rw [items_call (by rw [call_tok, h0]) (by simp), items_call_null (by rw [call_rule, h0'])]
  · rw [alts_fail (by rfl) he' hA, alts_ok (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' hA, alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `_PyPegen_get_keys(p, a)` / `_PyPegen_get_values(p, a)`: the keys and values of the pairs
(`NULL` keys for `**` items). -/
def keysOfPairs (a : Ast) : Ast := .seq ((seqOf a).map (recField · 0))
def valuesOfPairs (a : Ast) : Ast := .seq ((seqOf a).map (recField · 1))

/-- `dict` (`Grammar/python.gram:1028-1034`):
```
    | '{' a=[double_starred_kvpairs] '}' {
        _PyAST_Dict(
            CHECK(asdl_expr_seq*, _PyPegen_get_keys(p, a)),
            CHECK(asdl_expr_seq*, _PyPegen_get_values(p, a)),
            EXTRA) }
    | '{' invalid_double_starred_kvpairs '}'
```
At `{` (25), the optional `double_starred_kvpairs` (178) and `}` (26) give `Dict(keys, values)`
(`{}` both empty); once that fails, from the start mark, `{`, `invalid_double_starred_kvpairs`
(263) and `}` give `_PyPegen_dummy_name` (that alternative is not guarded by
`call_invalid_rules`: it runs in the first pass too); otherwise `NULL` with the mark back. -/
def DictRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 25 → ∀ (a : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 2) 178 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 26 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 8) 177 p =
      (mkAt .Dict [keysOfPairs a, valuesOfPairs a] (extraLoc t s2), s2.leave)) ∧
  (t.type ≠ 25 → callRule (f + 8) 177 p = (.null, q.leave)) ∧
  (t.type = 25 → ∀ (a : Ast) (s1 s2 : PS),
    callRule (f + 2) 178 { q with mark := p.mark + 1 } = (a, s1) → s1.errorIndicator = false →
    expectToken 26 s1 = (.null, s2) → s2.errorIndicator = false →
    (∀ (v : Ast) (c : Token) (s3 s4 : PS), callRule (f + 1) 263 { s2 with mark := p.mark + 1 } = (v, s3) →
      v ≠ .null → expectToken 26 s3 = (.tok c, s4) → s4.errorIndicator = false →
      callRule (f + 8) 177 p = (rec_ .PDummy [], s4.leave)) ∧
    (∀ (s3 : PS), callRule (f + 1) 263 { s2 with mark := p.mark + 1 } = (.null, s3) →
      callRule (f + 8) 177 p = (.null, { s3 with mark := p.mark }.leave)))

theorem dictRule_proven : DictRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 177 = r177 from rfl, r177]
  refine ⟨fun ht a c s1 s2 h1 h1e h2 h2e => ?_, fun ht => ?_,
    fun ht a s1 s2 h1 h1e h2 h2e => ⟨fun v c s3 s4 h3 hv h4 h4e => ?_, fun s3 h3 => ?_⟩⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call (by rw [call_tok, h2]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e, keysOfPairs, valuesOfPairs, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq, alts_nil]
    rfl
  · have g2 : TokGrows q s2 := TokGrows.trans (tg_mark' (tg_call h1) _) (tg_expect h2)
    have e2 : runCall (f + 3) (.tok 25) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call e2 (by simp), items_call (by rw [call_rule, h3]) hv,
          items_call (by rw [call_tok, h4]) (by simp), items_nil])]
    simp only [altResult, Bool.false_eq_true, ↓reduceIte, show (3 : Nat) > 1 from by decide]
    rfl
  · have g2 : TokGrows q s2 := TokGrows.trans (tg_mark' (tg_call h1) _) (tg_expect h2)
    have e2 : runCall (f + 3) (.tok 25) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call_null (by rw [call_tok, h2])]),
      alts_fail (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call e2 (by simp), items_call_null (by rw [call_rule, h3])]), alts_nil]
    rfl

/-! ### Comprehensions -/

/-- `'open' elt for_if_clauses 'close'` failing from the entry state `q` (start mark `m`, token
`t` under it), ending in `s`. -/
def CompA0Fails (f op elt cl : Nat) (m : Nat) (q s : PS) : Prop :=
  ((q.tokenAt m).type ≠ op ∧ s = q) ∨
  ((q.tokenAt m).type = op ∧ callRule (f + 2) elt { q with mark := m + 1 } = (.null, s)) ∨
  ((q.tokenAt m).type = op ∧ ∃ (a : Ast) (s1 : PS), callRule (f + 2) elt { q with mark := m + 1 } = (a, s1) ∧
    a ≠ .null ∧ callRule (f + 1) 181 s1 = (.null, s)) ∨
  ((q.tokenAt m).type = op ∧ ∃ (a b : Ast) (s1 s2 : PS), callRule (f + 2) elt { q with mark := m + 1 } = (a, s1) ∧
    a ≠ .null ∧ callRule (f + 1) 181 s1 = (b, s2) ∧ b ≠ .null ∧ expectToken cl s2 = (.null, s))

/-- `listcomp`, `setcomp`, `genexp` (`Grammar/python.gram:1058-1068`):
```
    | '[' a=star_named_expression b=for_if_clauses ']' { _PyAST_ListComp(a, b, EXTRA) }
    | invalid_comprehension
```
(`setcomp` with `{` `}` and `SetComp`; `genexp` with `(` `)`, the element
`( assignment_expression | expression !':=' | starred_expression )` (`_tmp_89`, 366) and
`GeneratorExp`). At the opening token (`op`), the element (`elt`), `for_if_clauses` (181) and the
closing token (`cl`) give `ctor(elt, generators)`; once that fails (`CompA0Fails`), in the first
pass `NULL` with the mark back, in the second an error already set gives `NULL`, and otherwise
`invalid_comprehension` (222) from the start mark gives the result (`NULL` with the mark back when
it gives `NULL`). -/
def CompRule (id op elt cl : Nat) (ctor : Ctor) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = op → ∀ (a b : Ast) (c : Token) (s1 s2 s3 : PS),
    callRule (f + 2) elt { q with mark := p.mark + 1 } = (a, s1) → a ≠ .null →
    callRule (f + 1) 181 s1 = (b, s2) → b ≠ .null → expectToken cl s2 = (.tok c, s3) →
    s3.errorIndicator = false →
    callRule (f + 8) id p = (mkAt ctor [a, b] (extraLoc t s3), s3.leave)) ∧
  (∀ (s : PS), CompA0Fails f op elt cl p.mark q s →
    (s.callInvalidRules = false → callRule (f + 8) id p = (.null, { s with mark := p.mark }.leave)) ∧
    (s.callInvalidRules = true → s.errorIndicator = true →
      callRule (f + 8) id p = (.null, { s with mark := p.mark }.leave)) ∧
    (s.callInvalidRules = true → s.errorIndicator = false → ∀ (v : Ast) (s' : PS),
      callRule (f + 2) 222 { s with mark := p.mark } = (v, s') → v ≠ .null →
      callRule (f + 8) id p = (v, s'.leave)) ∧
    (s.callInvalidRules = true → s.errorIndicator = false → ∀ (s' : PS),
      callRule (f + 2) 222 { s with mark := p.mark } = (.null, s') →
      callRule (f + 8) id p = (.null, { s' with mark := p.mark }.leave)))

theorem compRule_of {id op elt cl : Nat} {ctor : Ctor}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false true false
      [Alt.mk [.call (.tok op), .call (.rule elt), .call (.rule 181), .call (.tok cl)]
        (some (.mk ctor [.var 1, .var 2, .extra0, .extra1, .extra2, .extra3])) 4 false true,
       Alt.mk [.call (.rule 222)] none 1 true false]) :
    CompRule id op elt cl ctor := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) h, hr]
  have hA : ∀ s, CompA0Fails f op elt cl p.mark q s →
      runItems (f + 5) [.call (.tok op), .call (.rule elt), .call (.rule 181), .call (.tok cl)] #[]
        false q = ((none, false), s) := by
    intro s hs
    rcases hs with ⟨ht, rfl⟩ | ⟨ht, h1⟩ | ⟨ht, a, s1, h1, ha, h2⟩ | ⟨ht, a, b, s1, s2, h1, ha, h2, hb, h3⟩
    · rw [items_call_null (by rw [ek, ite_f ht])]
    · rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call_null (by rw [call_rule, h2])]
    · rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_rule, h2]) hb, items_call_null (by rw [call_tok, h3])]
  have hmk : ∀ s : PS, { s with mark := q.mark } = { s with mark := p.mark } := fun s => by rw [hm]
  refine ⟨fun ht a b c s1 s2 s3 h1 ha h2 hb h3 h3e => ?_, fun s hs =>
    ⟨fun hi => ?_, fun hi hse => ?_, fun hi hse v s' h1 hv => ?_, fun hi hse s' h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_call (by rw [call_rule, h2]) hb, items_call (by rw [call_tok, h3]) (by simp),
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (hA s hs), alts_skip (by simp [hi]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (hA s hs),
      alts_err (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = true from hse)]
    rfl
  · rw [alts_fail (by rfl) he (hA s hs),
      alts_ok (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
        (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (hA s hs),
      alts_fail (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `listcomp` (183): `[` 9, `star_named_expression` 116, `]` 10. -/
theorem listcomp_proven : CompRule 183 9 116 10 .ListComp := compRule_of rfl
/-- `setcomp` (184): `{` 25, `star_named_expression` 116, `}` 26. -/
theorem setcomp_proven : CompRule 184 25 116 26 .SetComp := compRule_of rfl

/-- `_tmp_89: assignment_expression | expression !':=' | starred_expression`, the element of a
`genexp` (`Grammar/python.gram:1067`): `assignment_expression` (118); once that fails, an
`expression` (109) not followed by `:=` (53); then `starred_expression` (190, `*` and any
`expression`); each from the start mark. -/
def Tmp89 : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule (f + 3) 118 p.enter = (v, s) → v ≠ .null →
    callRule (f + 8) 366 p = (v, s.leave)) ∧
  (∀ (s0 : PS), callRule (f + 3) 118 p.enter = (.null, s0) → s0.errorIndicator = false →
    (∀ (e x : Ast) (s1 s2 : PS), callRule (f + 2) 109 { s0 with mark := p.mark } = (e, s1) → e ≠ .null →
      expectToken 53 s1 = (x, s2) → nonNull x = false →
      callRule (f + 8) 366 p = (e, { s2 with mark := s1.mark }.leave)) ∧
    (∀ (s1 : PS), (callRule (f + 2) 109 { s0 with mark := p.mark } = (.null, s1) ∨
        ∃ e x s1' s1'', callRule (f + 2) 109 { s0 with mark := p.mark } = (e, s1') ∧ e ≠ .null ∧
          expectToken 53 s1' = (x, s1'') ∧ nonNull x = true ∧ s1 = { s1'' with mark := s1'.mark }) →
      s1.errorIndicator = false →
      (∀ (v : Ast) (s : PS), callRule (f + 1) 190 { s1 with mark := p.mark } = (v, s) → v ≠ .null →
        callRule (f + 8) 366 p = (v, s.leave)) ∧
      (∀ (s : PS), callRule (f + 1) 190 { s1 with mark := p.mark } = (.null, s) →
        callRule (f + 8) 366 p = (.null, { s with mark := p.mark }.leave))))

theorem tmp89_proven : Tmp89 := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 366 = r366 from rfl, r366]
  refine ⟨fun v s h1 hv => ?_, fun s0 h0 h0e => ⟨fun e x s1 s2 h1 hE h2 hx => ?_, fun s1 h1 h1e =>
    ⟨fun v s h2 hv => ?_, fun s h2 => ?_⟩⟩⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) hE, items_look (by rw [call_tok, h2]) (by simpa using hx),
          items_nil]), altResult_none1 rfl rfl]
    rfl
  all_goals
    have hB : runItems (f + 4) [.call (.rule 109), .look false (.tok 53)] #[] false
        { s0 with mark := p.mark } = ((none, false), s1) := by
      rcases h1 with h1 | ⟨e, x, s1', s1'', h1, hE, hk2, hx, rfl⟩
      · rw [items_call_null (by rw [call_rule, h1])]
      · rw [items_call (by rw [call_rule, h1]) hE, items_look_fail (by rw [call_tok, hk2]) (by simpa using hx)]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) hB, alts_ok (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) hB, alts_fail (by rfl) (E s1 h1e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h2])]), alts_nil]
    rfl

/-- `genexp` (185): `(` 7, `_tmp_89` 366, `)` 8, with its element group. -/
def GenexpRule : Prop := CompRule 185 7 366 8 .GeneratorExp ∧ Tmp89
theorem genexpRule_proven : GenexpRule := ⟨compRule_of rfl, tmp89_proven⟩

/-- `for_if_clauses: a[asdl_comprehension_seq*]=for_if_clause+ { a }`
(`Grammar/python.gram:1047-1048`): the `+` loop `_loop1_87` (364) of `for_if_clause` (182) is the
result (a non-`NULL` loop comes with no error); no clause gives `NULL` with the mark back. -/
def ForIfClauses : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule f 364 p.enter = (v, s) → v ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 181 p = (v, s.leave)) ∧
  (∀ (s : PS), callRule f 364 p.enter = (.null, s) →
    callRule (f + 5) 181 p = (.null, { s with mark := p.mark }.leave))

theorem forIfClauses_proven : ForIfClauses := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 181 = r181 from rfl, r181]
  refine ⟨fun v s h1 hv h1e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases v <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

def ForIfClausesRule : Prop := ForIfClauses ∧ Loop1Over 364 182
theorem forIfClausesRule_proven : ForIfClausesRule := ⟨forIfClauses_proven, loop1Over_of rfl⟩

end PyLean.PyGrammar.Peg
