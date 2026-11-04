import PyLean.PyGrammar.Peg.Rules.Patterns3

/-! The one-item pattern rules and the rules on the `','.x+` gathers (`Grammar/python.gram:
502-678`), rule by rule: `pattern_capture_target`, `value_pattern`, `star_pattern`,
`double_star_pattern`, `key_value_pattern`, `keyword_pattern`, `open_sequence_pattern`,
`maybe_sequence_pattern`, `items_pattern`, `positional_patterns`, `keyword_patterns`, `guard`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem setExprContext_nonNull (c : Ast) (k : Nat) (n : Ast) (h : n ≠ .null) :
    nonNull (setExprContext c k n) = true := by
  cases k with
  | zero => cases n <;> simp_all [setExprContext, nonNull]
  | succ k =>
    unfold setExprContext
    split <;> simp_all [nonNull]

/-- `_tmp_43: '.' | '(' | '='` (23, 7, 22): that token with the mark past it; at any other token
`NULL` with the state the entry read left. -/
def Tmp43 : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  ((t.type = 23 ∨ t.type = 7 ∨ t.type = 22) →
    callRule (f + 7) 320 p = (.tok t, { q with mark := p.mark + 1 }.leave)) ∧
  (t.type ≠ 23 → t.type ≠ 7 → t.type ≠ 22 → callRule (f + 7) 320 p = (.null, q.leave))

theorem tmp43_proven : Tmp43 := by
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
  simp only [show ruleOf 320 = r320 from rfl, r320]
  refine ⟨fun ht => ?_, fun h23 h7 h22 => ?_⟩
  · rcases ht with ht | ht | ht
    · rw [alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [e1, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f (by omega)])), hq,
        alts_ok (by rfl) he (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
    · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f (by omega)])), hq,
        alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f (by omega)])), hq,
        alts_ok (by rfl) he (by
        dsimp only; rw [items_call (by rw [ek, ite_t ht]) (by simp), items_nil]),
        altResult_none1 rfl rfl]
      rfl
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [e1, ite_f h23])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f h7])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f h22])), hq, alts_nil]
    rfl

/-- `pattern_capture_target` (`Grammar/python.gram:575-577`):
```
    | !"_" name=NAME !('.' | '(' | '=') {
        _PyPegen_set_expr_context(p, name, Store) }
```
No `EXTRA`. With the soft keyword `_` not under the mark, a `NAME` not followed by `.` `(` or `=`
(`_tmp_43`) is the name in `Store` context (so `case x:` binds `x`, while `case x.y:` and
`case x(...)` go to `value_pattern` and `class_pattern`); `_` itself, a missing `NAME`, or the
lookahead holding gives `NULL` with the mark back. -/
def PatternCaptureTarget : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (x n y : Ast) (s0 s1 s2 : PS), expectSoftKeyword [95] p.enter = (x, s0) → nonNull x = false →
    nameToken { s0 with mark := p.mark } = (n, s1) → n ≠ .null → callRule f 320 s1 = (y, s2) →
    nonNull y = false → s2.errorIndicator = false →
    callRule (f + 7) 82 p =
      (setExprContext (opNode .Store) 100000 n, { s2 with mark := s1.mark }.leave)) ∧
  (∀ (x : Ast) (s0 : PS), expectSoftKeyword [95] p.enter = (x, s0) → nonNull x = true →
    callRule (f + 7) 82 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (∀ (x : Ast) (s0 s1 : PS), expectSoftKeyword [95] p.enter = (x, s0) → nonNull x = false →
    nameToken { s0 with mark := p.mark } = (.null, s1) →
    callRule (f + 7) 82 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (x n y : Ast) (s0 s1 s2 : PS), expectSoftKeyword [95] p.enter = (x, s0) → nonNull x = false →
    nameToken { s0 with mark := p.mark } = (n, s1) → n ≠ .null → callRule f 320 s1 = (y, s2) →
    nonNull y = true → callRule (f + 7) 82 p = (.null, { s2 with mark := p.mark }.leave))

theorem patternCaptureTarget_proven : PatternCaptureTarget := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 82 = r82 from rfl, r82]
  refine ⟨fun x n y s0 s1 s2 h0 hx h1 hn h2 hy h2e => ?_, fun x s0 h0 hx => ?_,
    fun x s0 s1 h0 hx h1 => ?_, fun x n y s0 s1 s2 h0 hx h1 hn h2 hy => ?_⟩
  · have h1' : nameToken { s0 with mark := p.enter.mark } = (n, s1) := h1
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_look (by rw [call_softKw, h0]) hx, items_call (by rw [call_name, h1']) hn,
        items_look (by rw [call_rule, h2]) hy, items_nil]), altResult_plain rfl rfl]
    have g0 : ((#[] : Array Ast).push n).getD 0 .null = n := rfl
    have l0 : [n, opNode .Store].getD 0 Ast.null = n := rfl
    have l1 : [n, opNode .Store].getD 1 Ast.null = opNode .Store := rfl
    have hnn := setExprContext_nonNull (opNode .Store) 100000 n hn
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, g0]
    simp [hnn, h2e, opNode]
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_look_fail (by rw [call_softKw, h0]) (by simpa using hx)]), alts_nil]
    rfl
  · have h1' : nameToken { s0 with mark := p.enter.mark } = (.null, s1) := h1
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_look (by rw [call_softKw, h0]) hx, items_call_null (by rw [call_name, h1'])]),
      alts_nil]
    rfl
  · have h1' : nameToken { s0 with mark := p.enter.mark } = (n, s1) := h1
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_look (by rw [call_softKw, h0]) hx, items_call (by rw [call_name, h1']) hn,
        items_look_fail (by rw [call_rule, h2]) (by simpa using hy)]), alts_nil]
    rfl

/-- `value_pattern: attr=attr !('.' | '(' | '=') { _PyAST_MatchValue(attr, EXTRA) }`
(`Grammar/python.gram:582-583`): an `attr` (85) not followed by `.` `(` or `=` (`_tmp_43`) gives
`MatchValue(attr)` (so `case a.b:` compares with `a.b`); followed by one of them (as
`case a.b(...)`, a class pattern), or with no `attr`, `NULL` with the mark back. -/
def ValuePattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a x : Ast) (s1 s2 : PS), callRule (f + 1) 85 q = (a, s1) → a ≠ .null →
    callRule f 320 s1 = (x, s2) → nonNull x = false → s2.errorIndicator = false →
    callRule (f + 6) 84 p =
      (mkAt .MatchValue [a] (extraLoc t { s2 with mark := s1.mark }), { s2 with mark := s1.mark }.leave)) ∧
  (∀ (a x : Ast) (s1 s2 : PS), callRule (f + 1) 85 q = (a, s1) → a ≠ .null →
    callRule f 320 s1 = (x, s2) → nonNull x = true →
    callRule (f + 6) 84 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (s1 : PS), callRule (f + 1) 85 q = (.null, s1) →
    callRule (f + 6) 84 p = (.null, { s1 with mark := p.mark }.leave))

theorem valuePattern_proven : ValuePattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 84 = r84 from rfl, r84]
  refine ⟨fun a x s1 s2 h1 ha h2 hx h2e => ?_, fun a x s1 s2 h1 ha h2 hx => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look (by rw [call_rule, h2]) hx, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_look_fail (by rw [call_rule, h2]) (by simpa using hx)]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `star_pattern (memo)` (`Grammar/python.gram:611-615`):
```
    | '*' target=pattern_capture_target {
        _PyAST_MatchStar(target->v.Name.id, EXTRA) }
    | '*' wildcard_pattern {
        _PyAST_MatchStar(NULL, EXTRA) }
```
At `*` (16), a `pattern_capture_target` (82) gives `MatchStar(name)`; without one (no error), a
`wildcard_pattern` (83) after the `*` gives `MatchStar(NULL)` (`case [*_]:`); at another token, or
neither, `NULL` with the mark back; the result is memoized at the start mark. -/
def StarPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 92) = none →
  let t := q.tokenAt p.mark
  let q1 : PS := { q with mark := p.mark + 1 }
  (t.type = 16 → ∀ (a : Ast) (s : PS), callRule (f + 1) 82 q1 = (a, s) → a ≠ .null →
    s.errorIndicator = false →
    callRule (f + 7) 92 p = memoDone p.mark 92 (some (mkAt .MatchStar [fieldOf a "id"] (extraLoc t s)), s)) ∧
  (t.type = 16 → ∀ (w : Ast) (s s' : PS), callRule (f + 1) 82 q1 = (.null, s) →
    s.errorIndicator = false → callRule f 83 { s with mark := p.mark + 1 } = (w, s') → w ≠ .null →
    s'.errorIndicator = false →
    callRule (f + 7) 92 p = memoDone p.mark 92 (some (mkAt .MatchStar [.null] (extraLoc t s')), s')) ∧
  (t.type = 16 → ∀ (s s' : PS), callRule (f + 1) 82 q1 = (.null, s) →
    s.errorIndicator = false → callRule f 83 { s with mark := p.mark + 1 } = (.null, s') →
    callRule (f + 7) 92 p = memoDone p.mark 92 (some .null, { s' with mark := p.mark })) ∧
  (t.type ≠ 16 → callRule (f + 7) 92 p = memoDone p.mark 92 (some .null, q))

theorem starPattern_proven : StarPattern := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 92 = r92 from rfl, r92]
  refine ⟨fun ht a s h1 ha h1e => ?_, fun ht w s s' h1 h1e h2 hw h2e => ?_,
    fun ht s s' h1 h1e h2 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call (by rw [call_rule, h1]) ha,
        items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h1e]
  · have g1 : TokGrows q s := (tg_mark (TokGrows.refl _) (p.mark + 1)).trans (tg_call h1)
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_again g1 hlt, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h2]) hw, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  · have g1 : TokGrows q s := (tg_mark (TokGrows.refl _) (p.mark + 1)).trans (tg_call h1)
    rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_again g1 hlt, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h2])]), alts_nil]
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f ht])), hq, alts_nil]

/-- `double_star_pattern: '**' target=pattern_capture_target { target }`
(`Grammar/python.gram:643-644`): at `**` (35) the `pattern_capture_target` after it is the result
(`case {**rest}:`); at another token, or without a target, `NULL` with the mark back. -/
def DoubleStarPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 35 → ∀ (a : Ast) (s : PS), callRule f 82 { q with mark := p.mark + 1 } = (a, s) →
    a ≠ .null → s.errorIndicator = false → callRule (f + 6) 96 p = (a, s.leave)) ∧
  (t.type = 35 → ∀ (s : PS), callRule f 82 { q with mark := p.mark + 1 } = (.null, s) →
    callRule (f + 6) 96 p = (.null, { s with mark := p.mark }.leave)) ∧
  (t.type ≠ 35 → callRule (f + 6) 96 p = (.null, q.leave))

theorem doubleStarPattern_proven : DoubleStarPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 96 = r96 from rfl, r96]
  refine ⟨fun ht a s h1 ha h1e => ?_, fun ht s h1 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) ha, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call_null (by rw [call_tok, expect_entered h, ite_f ht])]), hq, alts_nil]
    rfl

/-- `key_value_pattern: key=(literal_expr | attr) ':' pattern=pattern { _PyPegen_key_pattern_pair(p,
key, pattern) }` (`Grammar/python.gram:639-641`): the key group (`_tmp_48`, 325: `literal_expr`
then `attr`, `Tmp48`), `:` (11) and `pattern` (70) give the pair (key, pattern); no key, no `:` or
no pattern gives `NULL` with the mark back. -/
def KeyValuePattern : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (k pt : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 325 p.enter = (k, s1) → k ≠ .null →
    expectToken 11 s1 = (.tok c, s2) → callRule f 70 s2 = (pt, s3) → pt ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 7) 95 p = (rec_ .PKeyPatternPair [k, pt], s3.leave)) ∧
  (∀ (s1 : PS), callRule (f + 2) 325 p.enter = (.null, s1) →
    callRule (f + 7) 95 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (k : Ast) (s1 s2 : PS), callRule (f + 2) 325 p.enter = (k, s1) → k ≠ .null →
    expectToken 11 s1 = (.null, s2) → callRule (f + 7) 95 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (k : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 325 p.enter = (k, s1) → k ≠ .null →
    expectToken 11 s1 = (.tok c, s2) → callRule f 70 s2 = (.null, s3) →
    callRule (f + 7) 95 p = (.null, { s3 with mark := p.mark }.leave))

theorem keyValuePattern_proven : KeyValuePattern := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 95 = r95 from rfl, r95]
  refine ⟨fun k pt c s1 s2 s3 h1 hk h2 h3 hp h3e => ?_, fun s1 h1 => ?_, fun k s1 s2 h1 hk h2 => ?_,
    fun k c s1 s2 s3 h1 hk h2 h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hk, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hp, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hk, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hk, items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_rule, h3])]), alts_nil]
    rfl

/-- `_tmp_48: literal_expr | attr`, the key of a mapping item: the ordered choice of
`literal_expr` (75) then `attr` (85). -/
def Tmp48 : Prop := ∀ (g : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (g + 6) 325 p =
    let a := choiceRes g p.mark [75, 85] p.enter
    (a.1.getD .null, a.2.leave)

theorem tmp48_proven : Tmp48 := by
  intro g p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  have := choice_run g p.mark (0, 0) [75, 85] p.enter
  simp only [List.length, List.map, choiceAlt] at this
  simp only [show ruleOf 325 = r325 from rfl, r325]
  rw [← this]

/-- `keyword_pattern: arg=NAME '=' value=pattern { _PyPegen_key_pattern_pair(p, arg, value) }`
(`Grammar/python.gram:674-675`): a `NAME`, `=` (22) and a `pattern` (70) give the pair (name,
pattern) (`C(x=1)`); without any of them `NULL` with the mark back. -/
def KeywordPattern : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (n pt : Ast) (c : Token) (s1 s2 s3 : PS), nameToken p.enter = (n, s1) → n ≠ .null →
    expectToken 22 s1 = (.tok c, s2) → callRule f 70 s2 = (pt, s3) → pt ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 7) 100 p = (rec_ .PKeyPatternPair [n, pt], s3.leave)) ∧
  (∀ (s1 : PS), nameToken p.enter = (.null, s1) →
    callRule (f + 7) 100 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (n : Ast) (s1 s2 : PS), nameToken p.enter = (n, s1) → n ≠ .null →
    expectToken 22 s1 = (.null, s2) → callRule (f + 7) 100 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (∀ (n : Ast) (c : Token) (s1 s2 s3 : PS), nameToken p.enter = (n, s1) → n ≠ .null →
    expectToken 22 s1 = (.tok c, s2) → callRule f 70 s2 = (.null, s3) →
    callRule (f + 7) 100 p = (.null, { s3 with mark := p.mark }.leave))

theorem keywordPattern_proven : KeywordPattern := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 100 = r100 from rfl, r100]
  refine ⟨fun n pt c s1 s2 s3 h1 hn h2 h3 hp h3e => ?_, fun s1 h1 => ?_, fun n s1 s2 h1 hn h2 => ?_,
    fun n c s1 s2 s3 h1 hn h2 h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hp, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, rec_]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_rule, h3])]), alts_nil]
    rfl

/-- `open_sequence_pattern: pattern=maybe_star_pattern ',' patterns=maybe_sequence_pattern? {
_PyPegen_seq_insert_in_front(p, pattern, patterns) }` (`Grammar/python.gram:600-602`): a
`maybe_star_pattern` (91), `,` (12) and the optional `maybe_sequence_pattern` (90) give the first
pattern in front of the rest (so `case a,:` is a one-element sequence); without the first pattern
or the `,`, `NULL` with the mark back. -/
def OpenSequencePattern : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (a b : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 91 p.enter = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.tok c, s2) → callRule f 90 s2 = (b, s3) → s3.errorIndicator = false →
    callRule (f + 7) 89 p = (.seq (a :: seqOf b), s3.leave)) ∧
  (∀ (s1 : PS), callRule (f + 2) 91 p.enter = (.null, s1) →
    callRule (f + 7) 89 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (∀ (a : Ast) (s1 s2 : PS), callRule (f + 2) 91 p.enter = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.null, s2) → callRule (f + 7) 89 p = (.null, { s2 with mark := p.mark }.leave))

theorem openSequencePattern_proven : OpenSequencePattern := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 89 = r89 from rfl, r89]
  refine ⟨fun a b c s1 s2 s3 h1 ha h2 h3 h3e => ?_, fun s1 h1 => ?_, fun a s1 s2 h1 ha h2 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_opt (by rw [call_rule, h3]) h3e, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]), alts_nil]
    rfl

/-- `maybe_sequence_pattern: patterns=','.maybe_star_pattern+ ','? { patterns }`
(`Grammar/python.gram:604-605`): the gather (`_gather_45`, 322; `GatherSep 322 321 91`) and an
optional trailing `,` give the gather's sequence; no gather gives `NULL` with the mark back. -/
def MaybeSequencePattern : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (v x : Ast) (s1 s2 : PS), callRule (f + 1) 322 p.enter = (v, s1) → v ≠ .null →
    expectToken 12 s1 = (x, s2) → s2.errorIndicator = false →
    callRule (f + 6) 90 p = (v, s2.leave)) ∧
  (∀ (s1 : PS), callRule (f + 1) 322 p.enter = (.null, s1) →
    callRule (f + 6) 90 p = (.null, { s1 with mark := p.mark }.leave))

theorem maybeSequencePattern_proven : MaybeSequencePattern := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 90 = r90 from rfl, r90]
  refine ⟨fun v x s1 s2 h1 hv h2 h2e => ?_, fun s1 h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hv, items_opt (by rw [call_tok, h2]) h2e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases v <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- A rule `x: g` whose one alternative is a call of rule `g` with the default action: `g`'s
value, `NULL` with the mark back without it. -/
def PassThrough (id g : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule f g p.enter = (v, s) → v ≠ .null → callRule (f + 5) id p = (v, s.leave)) ∧
  (∀ (s : PS), callRule f g p.enter = (.null, s) →
    callRule (f + 5) id p = (.null, { s with mark := p.mark }.leave))

/-- `items_pattern: ','.key_value_pattern+` (`Grammar/python.gram:636-637`): the gather
`_gather_47` (324) of `key_value_pattern` (95) separated by `,`. -/
theorem itemsPattern_proven : PassThrough 94 324 ∧ GatherSep 324 323 95 := by
  refine ⟨fun f p he hl => ?_, gatherSep_of rfl rfl⟩
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 94 = r94 from rfl, r94]
  refine ⟨fun v s h1 hv => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `keyword_patterns: ','.keyword_pattern+` (`Grammar/python.gram:671-672`): the gather
`_gather_52` (329) of `keyword_pattern` (100) separated by `,`. -/
theorem keywordPatterns_proven : PassThrough 99 329 ∧ GatherSep 329 328 100 := by
  refine ⟨fun f p he hl => ?_, gatherSep_of rfl rfl⟩
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 99 = r99 from rfl, r99]
  refine ⟨fun v s h1 hv => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `positional_patterns: args[asdl_pattern_seq*]=','.pattern+ { args }`
(`Grammar/python.gram:668-669`): the gather `_gather_50` (327) of `pattern` (70) separated by
`,`, as the result. -/
def PositionalPatterns : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule f 327 p.enter = (v, s) → v ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 98 p = (v, s.leave)) ∧
  (∀ (s : PS), callRule f 327 p.enter = (.null, s) →
    callRule (f + 5) 98 p = (.null, { s with mark := p.mark }.leave))

theorem positionalPatterns_proven : PositionalPatterns ∧ GatherSep 327 326 70 := by
  refine ⟨fun f p he hl => ?_, gatherSep_of rfl rfl⟩
  have he' : p.enter.errorIndicator = false := he
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 98 = r98 from rfl, r98]
  refine ⟨fun v s h1 hv h1e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases v <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `guard: 'if' guard=named_expression { guard }` (`Grammar/python.gram:502`): at `if` (700) the
`named_expression` (119) after it is the result; at another token, or without the expression,
`NULL` with the mark back. -/
def Guard : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 700 → ∀ (g : Ast) (s : PS), callRule f 119 { q with mark := p.mark + 1 } = (g, s) →
    g ≠ .null → s.errorIndicator = false → callRule (f + 6) 68 p = (g, s.leave)) ∧
  (t.type = 700 → ∀ (s : PS), callRule f 119 { q with mark := p.mark + 1 } = (.null, s) →
    callRule (f + 6) 68 p = (.null, { s with mark := p.mark }.leave)) ∧
  (t.type ≠ 700 → callRule (f + 6) 68 p = (.null, q.leave))

theorem guard_proven : Guard := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 68 = r68 from rfl, r68]
  refine ⟨fun ht g s h1 hg h1e => ?_, fun ht s h1 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) hg, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases g <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call_null (by rw [call_tok, expect_entered h, ite_f ht])]), hq, alts_nil]
    rfl

/-! ### The rules with the helper rules they are made of -/

def PatternCaptureTargetRule : Prop := PatternCaptureTarget ∧ Tmp43
theorem patternCaptureTargetRule_proven : PatternCaptureTargetRule :=
  ⟨patternCaptureTarget_proven, tmp43_proven⟩

def ValuePatternRule : Prop := ValuePattern ∧ Tmp43
theorem valuePatternRule_proven : ValuePatternRule := ⟨valuePattern_proven, tmp43_proven⟩

def KeyValuePatternRule : Prop := KeyValuePattern ∧ Tmp48
theorem keyValuePatternRule_proven : KeyValuePatternRule := ⟨keyValuePattern_proven, tmp48_proven⟩

def MaybeSequencePatternRule : Prop := MaybeSequencePattern ∧ GatherSep 322 321 91
theorem maybeSequencePatternRule_proven : MaybeSequencePatternRule :=
  ⟨maybeSequencePattern_proven, gatherSep_of rfl rfl⟩

def ItemsPatternRule : Prop := PassThrough 94 324 ∧ GatherSep 324 323 95
theorem itemsPatternRule_proven : ItemsPatternRule := itemsPattern_proven

def KeywordPatternsRule : Prop := PassThrough 99 329 ∧ GatherSep 329 328 100
theorem keywordPatternsRule_proven : KeywordPatternsRule := keywordPatterns_proven

def PositionalPatternsRule : Prop := PositionalPatterns ∧ GatherSep 327 326 70
theorem positionalPatternsRule_proven : PositionalPatternsRule := positionalPatterns_proven

end PyLean.PyGrammar.Peg
