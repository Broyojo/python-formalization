import PyLean.PyGrammar.Peg.Rules.Patterns5

/-! `mapping_pattern` and `class_pattern` (`Grammar/python.gram:617-666`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- `_PyPegen_get_pattern_keys(p, items)` and `_PyPegen_get_patterns(p, items)`: the first and
second fields of the `KeyPatternPair`s. -/
def keysOf (it : Ast) : Ast := .seq ((seqOf it).map (recField · 0))
def patsOf (it : Ast) : Ast := .seq ((seqOf it).map (recField · 1))

/-! ### `mapping_pattern` -/

/-- `'{' '}'` failing after the `{`, from `B` (the state after it), ending in `s`. -/
def MapA1Fails (B s : PS) : Prop := expectToken 26 B = (.null, s)

/-- `'{' rest=double_star_pattern ','? '}'` failing after the `{`. -/
def MapA2Fails (f : Nat) (B s : PS) : Prop :=
  callRule (f + 5) 96 B = (.null, s) ∨
  (∃ (r x : Ast) (s1 s2 : PS), callRule (f + 5) 96 B = (r, s1) ∧ r ≠ .null ∧
    expectToken 12 s1 = (x, s2) ∧ s2.errorIndicator = false ∧ expectToken 26 s2 = (.null, s))

/-- `'{' items=items_pattern ',' rest=double_star_pattern ','? '}'` failing after the `{`. -/
def MapA3Fails (f : Nat) (B s : PS) : Prop :=
  callRule (f + 4) 94 B = (.null, s) ∨
  (∃ (it : Ast) (s1 : PS), callRule (f + 4) 94 B = (it, s1) ∧ it ≠ .null ∧ expectToken 12 s1 = (.null, s)) ∨
  (∃ (it : Ast) (c : Token) (s1 s2 : PS), callRule (f + 4) 94 B = (it, s1) ∧ it ≠ .null ∧
    expectToken 12 s1 = (.tok c, s2) ∧ callRule (f + 2) 96 s2 = (.null, s)) ∨
  (∃ (it r x : Ast) (c : Token) (s1 s2 s3 s4 : PS), callRule (f + 4) 94 B = (it, s1) ∧ it ≠ .null ∧
    expectToken 12 s1 = (.tok c, s2) ∧ callRule (f + 2) 96 s2 = (r, s3) ∧ r ≠ .null ∧
    expectToken 12 s3 = (x, s4) ∧ s4.errorIndicator = false ∧ expectToken 26 s4 = (.null, s))

/-- `'{' items=items_pattern ','? '}'` failing after the `{`. -/
def MapA4Fails (f : Nat) (B s : PS) : Prop :=
  callRule (f + 3) 94 B = (.null, s) ∨
  (∃ (it x : Ast) (s1 s2 : PS), callRule (f + 3) 94 B = (it, s1) ∧ it ≠ .null ∧
    expectToken 12 s1 = (x, s2) ∧ s2.errorIndicator = false ∧ expectToken 26 s2 = (.null, s))

theorem MapA1Fails.tg {B s : PS} (h : MapA1Fails B s) : TokGrows B s := tg_expect h

theorem MapA2Fails.tg {f : Nat} {B s : PS} (h : MapA2Fails f B s) : TokGrows B s := by
  rcases h with h | ⟨r, x, s1, s2, h1, -, h2, -, h3⟩
  · exact tg_call h
  · exact (tg_call h1).trans ((tg_expect h2).trans (tg_expect h3))

theorem MapA3Fails.tg {f : Nat} {B s : PS} (h : MapA3Fails f B s) : TokGrows B s := by
  rcases h with h | ⟨it, s1, h1, -, h2⟩ | ⟨it, c, s1, s2, h1, -, h2, h3⟩ |
      ⟨it, r, x, c, s1, s2, s3, s4, h1, -, h2, h3, -, h4, -, h5⟩
  · exact tg_call h
  · exact (tg_call h1).trans (tg_expect h2)
  · exact (tg_call h1).trans ((tg_expect h2).trans (tg_call h3))
  · exact (tg_call h1).trans ((tg_expect h2).trans ((tg_call h3).trans
      ((tg_expect h4).trans (tg_expect h5))))

theorem MapA4Fails.tg {f : Nat} {B s : PS} (h : MapA4Fails f B s) : TokGrows B s := by
  rcases h with h | ⟨it, x, s1, s2, h1, -, h2, -, h3⟩
  · exact tg_call h
  · exact (tg_call h1).trans ((tg_expect h2).trans (tg_expect h3))

theorem mapA1_items {f : Nat} {X B s : PS} {c : Token} (hb : expectToken 25 X = (.tok c, B))
    (h : MapA1Fails B s) :
    runItems (f + 9) [(.call (.tok 25)), (.call (.tok 26))] #[] false X = ((none, false), s) := by
  rw [items_call (by rw [call_tok, hb]) (by simp), items_call_null (by rw [call_tok, h])]

theorem mapA2_items {f : Nat} {X B s : PS} {c : Token} (hb : expectToken 25 X = (.tok c, B))
    (h : MapA2Fails f B s) :
    runItems (f + 8) [(.call (.tok 25)), (.call (.rule 96)), (.opt (.tok 12)), (.call (.tok 26))]
      #[] false X = ((none, false), s) := by
  rw [items_call (by rw [call_tok, hb]) (by simp)]
  rcases h with h | ⟨r, x, s1, s2, h1, hr, h2, h2e, h3⟩
  · rw [items_call_null (by rw [call_rule, h])]
  · rw [items_call (by rw [call_rule, h1]) hr, items_opt (by rw [call_tok, h2]) h2e,
      items_call_null (by rw [call_tok, h3])]

theorem mapA3_items {f : Nat} {X B s : PS} {c0 : Token} (hb : expectToken 25 X = (.tok c0, B))
    (h : MapA3Fails f B s) :
    runItems (f + 7) [(.call (.tok 25)), (.call (.rule 94)), (.call (.tok 12)), (.call (.rule 96)),
      (.opt (.tok 12)), (.call (.tok 26))] #[] false X = ((none, false), s) := by
  rw [items_call (by rw [call_tok, hb]) (by simp)]
  rcases h with h | ⟨it, s1, h1, hi, h2⟩ | ⟨it, c, s1, s2, h1, hi, h2, h3⟩ |
      ⟨it, r, x, c, s1, s2, s3, s4, h1, hi, h2, h3, hr, h4, h4e, h5⟩
  · rw [items_call_null (by rw [call_rule, h])]
  · rw [items_call (by rw [call_rule, h1]) hi, items_call_null (by rw [call_tok, h2])]
  · rw [items_call (by rw [call_rule, h1]) hi, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]
  · rw [items_call (by rw [call_rule, h1]) hi, items_call (by rw [call_tok, h2]) (by simp),
      items_call (by rw [call_rule, h3]) hr, items_opt (by rw [call_tok, h4]) h4e,
      items_call_null (by rw [call_tok, h5])]

theorem mapA4_items {f : Nat} {X B s : PS} {c0 : Token} (hb : expectToken 25 X = (.tok c0, B))
    (h : MapA4Fails f B s) :
    runItems (f + 6) [(.call (.tok 25)), (.call (.rule 94)), (.opt (.tok 12)), (.call (.tok 26))]
      #[] false X = ((none, false), s) := by
  rw [items_call (by rw [call_tok, hb]) (by simp)]
  rcases h with h | ⟨it, x, s1, s2, h1, hi, h2, h2e, h3⟩
  · rw [items_call_null (by rw [call_rule, h])]
  · rw [items_call (by rw [call_rule, h1]) hi, items_opt (by rw [call_tok, h2]) h2e,
      items_call_null (by rw [call_tok, h3])]

/-- `mapping_pattern` (`Grammar/python.gram:617-634`):
```
    | '{' '}' { _PyAST_MatchMapping(NULL, NULL, NULL, EXTRA) }
    | '{' rest=double_star_pattern ','? '}' { _PyAST_MatchMapping(NULL, NULL, rest->v.Name.id, EXTRA) }
    | '{' items=items_pattern ',' rest=double_star_pattern ','? '}' {
        _PyAST_MatchMapping(CHECK(..., _PyPegen_get_pattern_keys(p, items)),
            CHECK(..., _PyPegen_get_patterns(p, items)), rest->v.Name.id, EXTRA) }
    | '{' items=items_pattern ','? '}' {
        _PyAST_MatchMapping(CHECK(..., _PyPegen_get_pattern_keys(p, items)),
            CHECK(..., _PyPegen_get_patterns(p, items)), NULL, EXTRA) }
    | invalid_mapping_pattern
```
At `{` (25): `}` (26) right after gives the empty mapping; once that fails, a
`double_star_pattern` (96), an optional `,` and `}` give `MatchMapping(rest=name)`; then
`items_pattern` (94), `,`, a `double_star_pattern`, an optional `,` and `}` give
`MatchMapping(keys, patterns, rest)`; then `items_pattern`, an optional `,` and `}` give
`MatchMapping(keys, patterns)`; each later alternative starts again at the `{`. When all four fail
(and at any other token), the first pass gives `NULL` with the mark back and the second pass the
result of `invalid_mapping_pattern` (254) from the start mark (which raises for `{**r, 1: a}`). -/
def MappingPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let q1 : PS := { q with mark := p.mark + 1 }
  (t.type = 25 → ∀ (c : Token) (s : PS), expectToken 26 q1 = (.tok c, s) → s.errorIndicator = false →
    callRule (f + 12) 93 p = (mkAt .MatchMapping [.null, .null, .null] (extraLoc t s), s.leave)) ∧
  (t.type = 25 → ∀ (r x : Ast) (c : Token) (s0 s1 s2 s3 : PS), MapA1Fails q1 s0 →
    s0.errorIndicator = false → callRule (f + 5) 96 { s0 with mark := p.mark + 1 } = (r, s1) →
    r ≠ .null → expectToken 12 s1 = (x, s2) → s2.errorIndicator = false →
    expectToken 26 s2 = (.tok c, s3) → s3.errorIndicator = false →
    callRule (f + 12) 93 p =
      (mkAt .MatchMapping [.null, .null, fieldOf r "id"] (extraLoc t s3), s3.leave)) ∧
  (t.type = 25 → ∀ (it r x : Ast) (c c' : Token) (s0 s1 s2 s3 s4 s5 s6 : PS), MapA1Fails q1 s0 →
    s0.errorIndicator = false → MapA2Fails f { s0 with mark := p.mark + 1 } s1 →
    s1.errorIndicator = false → callRule (f + 4) 94 { s1 with mark := p.mark + 1 } = (it, s2) →
    it ≠ .null → expectToken 12 s2 = (.tok c, s3) → callRule (f + 2) 96 s3 = (r, s4) → r ≠ .null →
    expectToken 12 s4 = (x, s5) → s5.errorIndicator = false → expectToken 26 s5 = (.tok c', s6) →
    s6.errorIndicator = false →
    callRule (f + 12) 93 p =
      (mkAt .MatchMapping [keysOf it, patsOf it, fieldOf r "id"] (extraLoc t s6), s6.leave)) ∧
  (t.type = 25 → ∀ (it x : Ast) (c : Token) (s0 s1 s2 s3 s4 s5 : PS), MapA1Fails q1 s0 →
    s0.errorIndicator = false → MapA2Fails f { s0 with mark := p.mark + 1 } s1 →
    s1.errorIndicator = false → MapA3Fails f { s1 with mark := p.mark + 1 } s2 →
    s2.errorIndicator = false → callRule (f + 3) 94 { s2 with mark := p.mark + 1 } = (it, s3) →
    it ≠ .null → expectToken 12 s3 = (x, s4) → s4.errorIndicator = false →
    expectToken 26 s4 = (.tok c, s5) → s5.errorIndicator = false →
    callRule (f + 12) 93 p =
      (mkAt .MatchMapping [keysOf it, patsOf it, .null] (extraLoc t s5), s5.leave)) ∧
  (t.type = 25 → ∀ (s0 s1 s2 s3 : PS), MapA1Fails q1 s0 → s0.errorIndicator = false →
    MapA2Fails f { s0 with mark := p.mark + 1 } s1 → s1.errorIndicator = false →
    MapA3Fails f { s1 with mark := p.mark + 1 } s2 → s2.errorIndicator = false →
    MapA4Fails f { s2 with mark := p.mark + 1 } s3 → s3.errorIndicator = false →
    (s3.callInvalidRules = false → callRule (f + 12) 93 p = (.null, { s3 with mark := p.mark }.leave)) ∧
    (s3.callInvalidRules = true → ∀ (v : Ast) (s' : PS),
      callRule (f + 3) 254 { s3 with mark := p.mark } = (v, s') → v ≠ .null →
      callRule (f + 12) 93 p = (v, s'.leave)) ∧
    (s3.callInvalidRules = true → ∀ (s' : PS),
      callRule (f + 3) 254 { s3 with mark := p.mark } = (.null, s') →
      callRule (f + 12) 93 p = (.null, { s' with mark := p.mark }.leave))) ∧
  (t.type ≠ 25 →
    (q.callInvalidRules = false → callRule (f + 12) 93 p = (.null, q.leave)) ∧
    (q.callInvalidRules = true → ∀ (v : Ast) (s' : PS), callRule (f + 3) 254 q = (v, s') →
      v ≠ .null → callRule (f + 12) 93 p = (v, s'.leave)) ∧
    (q.callInvalidRules = true → ∀ (s' : PS), callRule (f + 3) 254 q = (.null, s') →
      callRule (f + 12) 93 p = (.null, { s' with mark := p.mark }.leave)))

theorem mappingPattern_proven : MappingPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have e0 : ∀ ty, expectToken ty q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty
    rw [expectToken_at _ _ hlt', hm]
  -- `{` again at the start mark, after a failed alternative
  have ob : ∀ (s : PS), TokGrows q s → (q.tokenAt p.mark).type = 25 →
      expectToken 25 { s with mark := p.mark } = (.tok (q.tokenAt p.mark), { s with mark := p.mark + 1 }) := by
    intro s g ht
    rw [expect_again g hlt, ite_t ht]
  have gq1 : TokGrows q { q with mark := p.mark + 1 } := tg_mark (TokGrows.refl _) _
  have gm : ∀ {s s' : PS}, TokGrows q s → TokGrows { s with mark := p.mark + 1 } s' → TokGrows q s' :=
    fun g g' => (tg_mark g _).trans g'
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 93 = r93 from rfl, r93]
  refine ⟨fun ht c s h1 h1e => ?_, fun ht r x c s0 s1 s2 s3 h0 h0e h1 hr h2 h2e h3 h3e => ?_,
    fun ht it r x c c' s0 s1 s2 s3 s4 s5 s6 h0 h0e h1 h1e h2 hi h3 h4 hr h5 h5e h6 h6e => ?_,
    fun ht it x c s0 s1 s2 s3 s4 s5 h0 h0e h1 h1e h2' h2e h3 hi h4 h4e h5 h5e => ?_,
    fun ht s0 s1 s2 s3 h0 h0e h1 h1e h2 h2e h3' h3e => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_tok, e0, ite_t ht]) (by simp),
        items_call (by rw [call_tok, h1]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h1e]
  · have g0 : TokGrows q s0 := gq1.trans h0.tg
    rw [alts_fail (by rfl) he (by exact mapA1_items (by rw [e0, ite_t ht]) h0),
      alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, ob s0 g0 ht]) (by simp),
        items_call (by rw [call_rule, h1]) hr, items_opt (by rw [call_tok, h2]) h2e,
        items_call (by rw [call_tok, h3]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · have g0 : TokGrows q s0 := gq1.trans h0.tg
    have g1 : TokGrows q s1 := gm g0 h1.tg
    rw [alts_fail (by rfl) he (by exact mapA1_items (by rw [e0, ite_t ht]) h0),
      alts_fail (by rfl) (E s0 h0e) (by exact mapA2_items (ob s0 g0 ht) h1),
      alts_ok (by rfl) (E s1 h1e) (by
      dsimp only
      rw [items_call (by rw [call_tok, ob s1 g1 ht]) (by simp),
        items_call (by rw [call_rule, h2]) hi, items_call (by rw [call_tok, h3]) (by simp),
        items_call (by rw [call_rule, h4]) hr, items_opt (by rw [call_tok, h5]) h5e,
        items_call (by rw [call_tok, h6]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h6e, keysOf, patsOf, StateT.pure, StateT.bind, pure, bind]
  · have g0 : TokGrows q s0 := gq1.trans h0.tg
    have g1 : TokGrows q s1 := gm g0 h1.tg
    have g2 : TokGrows q s2 := gm g1 h2'.tg
    rw [alts_fail (by rfl) he (by exact mapA1_items (by rw [e0, ite_t ht]) h0),
      alts_fail (by rfl) (E s0 h0e) (by exact mapA2_items (ob s0 g0 ht) h1),
      alts_fail (by rfl) (E s1 h1e) (by exact mapA3_items (ob s1 g1 ht) h2'),
      alts_ok (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (by rw [call_tok, ob s2 g2 ht]) (by simp),
        items_call (by rw [call_rule, h3]) hi, items_opt (by rw [call_tok, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h5e, keysOf, patsOf, StateT.pure, StateT.bind, pure, bind]
  · have g0 : TokGrows q s0 := gq1.trans h0.tg
    have g1 : TokGrows q s1 := gm g0 h1.tg
    have g2 : TokGrows q s2 := gm g1 h2.tg
    rw [alts_fail (by rfl) he (by exact mapA1_items (by rw [e0, ite_t ht]) h0),
      alts_fail (by rfl) (E s0 h0e) (by exact mapA2_items (ob s0 g0 ht) h1),
      alts_fail (by rfl) (E s1 h1e) (by exact mapA3_items (ob s1 g1 ht) h2),
      alts_fail (by rfl) (E s2 h2e) (by exact mapA4_items (ob s2 g2 ht) h3')]
    refine ⟨fun hi => ?_, fun hi v s' h4 hv => ?_, fun hi s' h4 => ?_⟩
    · rw [alts_skip (by simp [hi]), alts_nil]
      rfl
    · rw [alts_ok (by simp [hi]) (E s3 h3e) (by
        dsimp only; rw [items_call (by rw [call_rule, h4]) hv, items_nil]), altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by simp [hi]) (E s3 h3e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h4])]), alts_nil]
      rfl
  · have k0 : ∀ g, runCall (g + 1) (.tok 25) q = (.null, q) := fun g => by
      rw [call_tok, e0, ite_f ht]
    rw [alts_fail (by rfl) he (items_call_null (k0 _)), hq,
      alts_fail (by rfl) he (items_call_null (k0 _)), hq,
      alts_fail (by rfl) he (items_call_null (k0 _)), hq,
      alts_fail (by rfl) he (items_call_null (k0 _)), hq]
    refine ⟨fun hi => ?_, fun hi v s' h4 hv => ?_, fun hi s' h4 => ?_⟩
    · rw [alts_skip (by simp [hi]), alts_nil]
      rfl
    · rw [alts_ok (by simp [hi]) he (by
        dsimp only; rw [items_call (by rw [call_rule, h4]) hv, items_nil]), altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by simp [hi]) he (by
        dsimp only; rw [items_call_null (by rw [call_rule, h4])]), alts_nil]
      rfl

/-! ### `class_pattern` -/

/-- `_PyPegen_map_names_to_ids(p, _PyPegen_get_pattern_keys(p, keywords))`. -/
def idsOf (kw : Ast) : Ast := .seq ((seqOf (keysOf kw)).map (fieldOf · "id"))

/-- `cls=name_or_attr '('` failing from `X`, ending in `s`. -/
def ClsHeadFails (g : Nat) (X s : PS) : Prop :=
  callRule g 86 X = (.null, s) ∨
  (∃ (c : Ast) (s1 : PS), callRule g 86 X = (c, s1) ∧ c ≠ .null ∧ expectToken 7 s1 = (.null, s))

/-- `cls=name_or_attr '('` matching from `X`, ending in `s2`. -/
def ClsHead (g : Nat) (X s2 : PS) : Prop :=
  ∃ (c : Ast) (to : Token) (s1 : PS), callRule g 86 X = (c, s1) ∧ c ≠ .null ∧
    expectToken 7 s1 = (.tok to, s2)

/-- `name_or_attr '(' ')'` failing. -/
def ClsA1Fails (f : Nat) (X s : PS) : Prop :=
  ClsHeadFails (f + 9) X s ∨ (∃ s2, ClsHead (f + 9) X s2 ∧ expectToken 8 s2 = (.null, s))

/-- `name_or_attr '(' rr ','? ')'` (`rr` = 98 or 99) failing. -/
def ClsA23Fails (g rr : Nat) (X s : PS) : Prop :=
  ClsHeadFails (g + 2) X s ∨
  (∃ s2, ClsHead (g + 2) X s2 ∧ (callRule g rr s2 = (.null, s) ∨
    ∃ (ps x : Ast) (s3 s4 : PS), callRule g rr s2 = (ps, s3) ∧ ps ≠ .null ∧
      expectToken 12 s3 = (x, s4) ∧ s4.errorIndicator = false ∧ expectToken 8 s4 = (.null, s)))

/-- `name_or_attr '(' positional_patterns ',' keyword_patterns ','? ')'` failing. -/
def ClsA4Fails (f : Nat) (X s : PS) : Prop :=
  ClsHeadFails (f + 6) X s ∨
  (∃ s2, ClsHead (f + 6) X s2 ∧ (callRule (f + 4) 98 s2 = (.null, s) ∨
    (∃ (ps : Ast) (s3 : PS), callRule (f + 4) 98 s2 = (ps, s3) ∧ ps ≠ .null ∧
      expectToken 12 s3 = (.null, s)) ∨
    (∃ (ps : Ast) (c : Token) (s3 s4 : PS), callRule (f + 4) 98 s2 = (ps, s3) ∧ ps ≠ .null ∧
      expectToken 12 s3 = (.tok c, s4) ∧ callRule (f + 2) 99 s4 = (.null, s)) ∨
    (∃ (ps kw x : Ast) (c : Token) (s3 s4 s5 s6 : PS), callRule (f + 4) 98 s2 = (ps, s3) ∧
      ps ≠ .null ∧ expectToken 12 s3 = (.tok c, s4) ∧ callRule (f + 2) 99 s4 = (kw, s5) ∧
      kw ≠ .null ∧ expectToken 12 s5 = (x, s6) ∧ s6.errorIndicator = false ∧
      expectToken 8 s6 = (.null, s))))

theorem clsHead_items {g : Nat} {X s : PS} {rest : List Item} (h : ClsHeadFails (g + 1) X s) :
    runItems (g + 3) ((.call (.rule 86)) :: (.call (.tok 7)) :: rest) #[] false X = ((none, false), s) := by
  rcases h with h | ⟨c, s1, h1, hc, h2⟩
  · rw [items_call_null (by rw [call_rule, h])]
  · rw [items_call (by rw [call_rule, h1]) hc, items_call_null (by rw [call_tok, h2])]

theorem clsA1_items {f : Nat} {X s : PS} (h : ClsA1Fails f X s) :
    runItems (f + 11) [(.call (.rule 86)), (.call (.tok 7)), (.call (.tok 8))] #[] false X =
      ((none, false), s) := by
  rcases h with h | ⟨s2, ⟨c, to, s1, h1, hc, h2⟩, h3⟩
  · exact clsHead_items (g := f + 8) h
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_tok, h3])]

theorem clsA23_items {g rr : Nat} {X s : PS} (h : ClsA23Fails (g + 2) rr X s) :
    runItems (g + 6) [(.call (.rule 86)), (.call (.tok 7)), (.call (.rule rr)), (.opt (.tok 12)),
      (.call (.tok 8))] #[] false X = ((none, false), s) := by
  rcases h with h | ⟨s2, ⟨c, to, s1, h1, hc, h2⟩, h3 | ⟨ps, x, s3, s4, h3, hp, h4, h4e, h5⟩⟩
  · exact clsHead_items (g := g + 3) h
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call (by rw [call_rule, h3]) hp, items_opt (by rw [call_tok, h4]) h4e,
      items_call_null (by rw [call_tok, h5])]

theorem clsA4_items {f : Nat} {X s : PS} (h : ClsA4Fails f X s) :
    runItems (f + 8) [(.call (.rule 86)), (.call (.tok 7)), (.call (.rule 98)), (.call (.tok 12)),
      (.call (.rule 99)), (.opt (.tok 12)), (.call (.tok 8))] #[] false X = ((none, false), s) := by
  rcases h with h | ⟨s2, ⟨c, to, s1, h1, hc, h2⟩, h3 | ⟨ps, s3, h3, hp, h4⟩ |
      ⟨ps, c', s3, s4, h3, hp, h4, h5⟩ | ⟨ps, kw, x, c', s3, s4, s5, s6, h3, hp, h4, h5, hk, h6, h6e, h7⟩⟩
  · exact clsHead_items (g := f + 5) h
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call (by rw [call_rule, h3]) hp, items_call_null (by rw [call_tok, h4])]
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call (by rw [call_rule, h3]) hp, items_call (by rw [call_tok, h4]) (by simp),
      items_call_null (by rw [call_rule, h5])]
  · rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
      items_call (by rw [call_rule, h3]) hp, items_call (by rw [call_tok, h4]) (by simp),
      items_call (by rw [call_rule, h5]) hk, items_opt (by rw [call_tok, h6]) h6e,
      items_call_null (by rw [call_tok, h7])]

/-- `class_pattern` (`Grammar/python.gram:646-666`):
```
    | cls=name_or_attr '(' ')' { _PyAST_MatchClass(cls, NULL, NULL, NULL, EXTRA) }
    | cls=name_or_attr '(' patterns=positional_patterns ','? ')' {
        _PyAST_MatchClass(cls, patterns, NULL, NULL, EXTRA) }
    | cls=name_or_attr '(' keywords=keyword_patterns ','? ')' {
        _PyAST_MatchClass(cls, NULL,
            CHECK(..., _PyPegen_map_names_to_ids(p, CHECK(..., _PyPegen_get_pattern_keys(p, keywords)))),
            CHECK(..., _PyPegen_get_patterns(p, keywords)), EXTRA) }
    | cls=name_or_attr '(' patterns=positional_patterns ',' keywords=keyword_patterns ','? ')' {
        _PyAST_MatchClass(cls, patterns, ..., ..., EXTRA) }
    | invalid_class_pattern
```
`name_or_attr` (86) and `(` (7) then: `)` (8) gives `MatchClass(cls)`; once that fails,
`positional_patterns` (98), an optional `,` and `)` give `MatchClass(cls, patterns)`; then
`keyword_patterns` (99), an optional `,` and `)` give `MatchClass(cls, [], kwd_attrs, kwd_patterns)`
(the names of the keyword pairs and their patterns); then positional, `,`, keyword, an optional `,`
and `)` give all four. Each alternative starts again from the start mark. When all four fail, the
first pass gives `NULL` with the mark back and the second pass the result of
`invalid_class_pattern` (253) from the start mark (which raises for `C(a=1, 1)`). -/
def ClassPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (c : Ast) (to tc : Token) (s1 s2 s3 : PS), callRule (f + 9) 86 q = (c, s1) → c ≠ .null →
    expectToken 7 s1 = (.tok to, s2) → expectToken 8 s2 = (.tok tc, s3) → s3.errorIndicator = false →
    callRule (f + 14) 97 p = (mkAt .MatchClass [c, .null, .null, .null] (extraLoc t s3), s3.leave)) ∧
  (∀ (c ps x : Ast) (to tc : Token) (s0 s1 s2 s3 s4 s5 : PS), ClsA1Fails f q s0 →
    s0.errorIndicator = false → callRule (f + 8) 86 { s0 with mark := p.mark } = (c, s1) →
    c ≠ .null → expectToken 7 s1 = (.tok to, s2) → callRule (f + 6) 98 s2 = (ps, s3) → ps ≠ .null →
    expectToken 12 s3 = (x, s4) → s4.errorIndicator = false → expectToken 8 s4 = (.tok tc, s5) →
    s5.errorIndicator = false →
    callRule (f + 14) 97 p = (mkAt .MatchClass [c, ps, .null, .null] (extraLoc t s5), s5.leave)) ∧
  (∀ (c kw x : Ast) (to tc : Token) (s0 s0' s1 s2 s3 s4 s5 : PS), ClsA1Fails f q s0 →
    s0.errorIndicator = false → ClsA23Fails (f + 6) 98 { s0 with mark := p.mark } s0' →
    s0'.errorIndicator = false → callRule (f + 7) 86 { s0' with mark := p.mark } = (c, s1) →
    c ≠ .null → expectToken 7 s1 = (.tok to, s2) → callRule (f + 5) 99 s2 = (kw, s3) → kw ≠ .null →
    expectToken 12 s3 = (x, s4) → s4.errorIndicator = false → expectToken 8 s4 = (.tok tc, s5) →
    s5.errorIndicator = false →
    callRule (f + 14) 97 p =
      (mkAt .MatchClass [c, .null, idsOf kw, patsOf kw] (extraLoc t s5), s5.leave)) ∧
  (∀ (c ps kw x : Ast) (to tm tc : Token) (s0 s0' s0'' s1 s2 s3 s4 s5 s6 s7 : PS),
    ClsA1Fails f q s0 → s0.errorIndicator = false →
    ClsA23Fails (f + 6) 98 { s0 with mark := p.mark } s0' → s0'.errorIndicator = false →
    ClsA23Fails (f + 5) 99 { s0' with mark := p.mark } s0'' → s0''.errorIndicator = false →
    callRule (f + 6) 86 { s0'' with mark := p.mark } = (c, s1) → c ≠ .null →
    expectToken 7 s1 = (.tok to, s2) → callRule (f + 4) 98 s2 = (ps, s3) → ps ≠ .null →
    expectToken 12 s3 = (.tok tm, s4) → callRule (f + 2) 99 s4 = (kw, s5) → kw ≠ .null →
    expectToken 12 s5 = (x, s6) → s6.errorIndicator = false → expectToken 8 s6 = (.tok tc, s7) →
    s7.errorIndicator = false →
    callRule (f + 14) 97 p =
      (mkAt .MatchClass [c, ps, idsOf kw, patsOf kw] (extraLoc t s7), s7.leave)) ∧
  (∀ (s0 s0' s0'' s4 : PS), ClsA1Fails f q s0 → s0.errorIndicator = false →
    ClsA23Fails (f + 6) 98 { s0 with mark := p.mark } s0' → s0'.errorIndicator = false →
    ClsA23Fails (f + 5) 99 { s0' with mark := p.mark } s0'' → s0''.errorIndicator = false →
    ClsA4Fails f { s0'' with mark := p.mark } s4 → s4.errorIndicator = false →
    (s4.callInvalidRules = false → callRule (f + 14) 97 p = (.null, { s4 with mark := p.mark }.leave)) ∧
    (s4.callInvalidRules = true → ∀ (v : Ast) (s' : PS),
      callRule (f + 5) 253 { s4 with mark := p.mark } = (v, s') → v ≠ .null →
      callRule (f + 14) 97 p = (v, s'.leave)) ∧
    (s4.callInvalidRules = true → ∀ (s' : PS),
      callRule (f + 5) 253 { s4 with mark := p.mark } = (.null, s') →
      callRule (f + 14) 97 p = (.null, { s' with mark := p.mark }.leave)))

theorem classPattern_proven : ClassPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 97 = r97 from rfl, r97]
  refine ⟨fun c to tc s1 s2 s3 h1 hc h2 h3 h3e => ?_,
    fun c ps x to tc s0 s1 s2 s3 s4 s5 h0 h0e h1 hc h2 h3 hp h4 h4e h5 h5e => ?_,
    fun c kw x to tc s0 s0' s1 s2 s3 s4 s5 h0 h0e h0' h0'e h1 hc h2 h3 hk h4 h4e h5 h5e => ?_,
    fun c ps kw x to tm tc s0 s0' s0'' s1 s2 s3 s4 s5 s6 s7 h0 h0e h0' h0'e h0'' h0''e h1 hc h2 h3
      hp h4 h5 hk h6 h6e h7 h7e => ?_,
    fun s0 s0' s0'' s4 h0 h0e h0' h0'e h0'' h0''e h4' h4e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_tok, h3]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (by exact clsA1_items h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hp, items_opt (by rw [call_tok, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h5e]
  · rw [alts_fail (by rfl) he (by exact clsA1_items h0),
      alts_fail (by rfl) (E s0 h0e) (by exact clsA23_items h0'),
      alts_ok (by rfl) (E s0' h0'e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hk, items_opt (by rw [call_tok, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h5e, idsOf, keysOf, patsOf, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) he (by exact clsA1_items h0),
      alts_fail (by rfl) (E s0 h0e) (by exact clsA23_items h0'),
      alts_fail (by rfl) (E s0' h0'e) (by exact clsA23_items h0''),
      alts_ok (by rfl) (E s0'' h0''e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hc, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hp, items_call (by rw [call_tok, h4]) (by simp),
        items_call (by rw [call_rule, h5]) hk, items_opt (by rw [call_tok, h6]) h6e,
        items_call (by rw [call_tok, h7]) (by simp), items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h7e, idsOf, keysOf, patsOf, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) he (by exact clsA1_items h0),
      alts_fail (by rfl) (E s0 h0e) (by exact clsA23_items h0'),
      alts_fail (by rfl) (E s0' h0'e) (by exact clsA23_items h0''),
      alts_fail (by rfl) (E s0'' h0''e) (by exact clsA4_items h4')]
    refine ⟨fun hi => ?_, fun hi v s' h5 hv => ?_, fun hi s' h5 => ?_⟩
    · rw [alts_skip (by simp [hi]), alts_nil]
      rfl
    · rw [alts_ok (by simp [hi]) (E s4 h4e) (by
        dsimp only; rw [items_call (by rw [call_rule, h5]) hv, items_nil]), altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by simp [hi]) (E s4 h4e) (by
        dsimp only; rw [items_call_null (by rw [call_rule, h5])]), alts_nil]
      rfl

end PyLean.PyGrammar.Peg
