import PyLean.PyGrammar.Peg.Rules.Comps2

/-! Call arguments (`Grammar/python.gram:1077-1110`) and type parameters
(`Grammar/python.gram:688-708`), rule by rule: `starred_expression`, `kwarg_or_starred`,
`kwarg_or_double_starred`, `kwargs`, `args`, `arguments`, `type_params`, `type_param_seq`,
`type_param`, `type_param_bound`, `type_param_default`, `type_param_starred_default`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### A leading `invalid_` alternative, from any state -/

/-- As `InvPass`, for the state `S` the alternatives start from (`q` for a rule with `EXTRA`)
and the rule's start mark `m`. -/
def InvPassAt (g inv : Nat) (S : PS) (m : Nat) (X : PS) : Prop :=
  (S.callInvalidRules = false ∧ X = S) ∨
  (S.callInvalidRules = true ∧ ∃ s, callRule g inv S = (.null, s) ∧ s.errorIndicator = false ∧
    X = { s with mark := m })

theorem invPassAt_alts {g inv m : Nat} {S X : PS} {rest : List Alt} {st : Int × Int}
    (he : S.errorIndicator = false) (h : InvPassAt g inv S m X) :
    runAlts (g + 3) (invAlt inv :: rest) false m st S = runAlts (g + 2) rest false m st X := by
  rcases h with ⟨hi, rfl⟩ | ⟨hi, s, h1, h1e, rfl⟩
  · rw [alts_skip (by simp [invAlt, hi])]
  · rw [alts_fail (by simp [invAlt, hi]) he (by
      show runItems (g + 2) [.call (.rule inv)] #[] false S = _
      rw [items_call_null (by rw [call_rule, h1])])]

theorem invAltAt_ok {g inv m : Nat} {S s : PS} {v : Ast} {rest : List Alt} {st : Int × Int}
    (he : S.errorIndicator = false) (hi : S.callInvalidRules = true)
    (h1 : callRule g inv S = (v, s)) (hv : v ≠ .null) :
    runAlts (g + 3) (invAlt inv :: rest) false m st S = (some v, s) := by
  rw [alts_ok (by simp [invAlt, hi]) he (by
    show runItems (g + 2) [.call (.rule inv)] #[] false S = _
    rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
  rfl

theorem invAltAt_err {g inv m : Nat} {S s : PS} {a : Alt} {rest : List Alt} {st : Int × Int}
    (he : S.errorIndicator = false) (hi : S.callInvalidRules = true) (hg : a.guardInvalid = false)
    (h1 : callRule g inv S = (.null, s)) (h1e : s.errorIndicator = true) :
    runAlts (g + 3) (invAlt inv :: a :: rest) false m st S = (none, { s with mark := m }) := by
  rw [alts_fail (by simp [invAlt, hi]) he (by
      show runItems (g + 2) [.call (.rule inv)] #[] false S = _
      rw [items_call_null (by rw [call_rule, h1])]),
    alts_err (by simp [hg]) (show ({ s with mark := m } : PS).errorIndicator = true from h1e)]

theorem invPassAt_ei {g inv m : Nat} {S X : PS} (he : S.errorIndicator = false)
    (h : InvPassAt g inv S m X) : X.errorIndicator = false := by
  rcases h with ⟨-, rfl⟩ | ⟨-, s, -, hs, rfl⟩
  · exact he
  · exact hs

/-! ### `r1 | r2 !lk` -/

/-- A rule `r1 | r2 !lk` (default actions, no `EXTRA`): `_tmp_167` (444, the element of `args`:
`starred_expression | (assignment_expression | expression !':=') !'='`) and `_tmp_178` (455,
`assignment_expression | expression !':='`). `r1` from the entry state is the result; once it gives
`NULL`, `r2` from the start mark, kept only when `lk` does not follow (not consumed). -/
def OrNotLook (id r1 r2 lk : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (∀ (v : Ast) (s : PS), callRule (f + 2) r1 p.enter = (v, s) → v ≠ .null →
    callRule (f + 7) id p = (v, s.leave)) ∧
  (∀ (s0 : PS), callRule (f + 2) r1 p.enter = (.null, s0) → s0.errorIndicator = false →
    (∀ (e x : Ast) (s1 s2 : PS), callRule (f + 1) r2 { s0 with mark := p.mark } = (e, s1) → e ≠ .null →
      expectToken lk s1 = (x, s2) →
      (nonNull x = false → callRule (f + 7) id p = (e, { s2 with mark := s1.mark }.leave)) ∧
      (nonNull x = true → callRule (f + 7) id p = (.null, { s2 with mark := p.mark }.leave))) ∧
    (∀ (s1 : PS), callRule (f + 1) r2 { s0 with mark := p.mark } = (.null, s1) →
      callRule (f + 7) id p = (.null, { s1 with mark := p.mark }.leave)))

theorem orNotLook_of {id r1 r2 lk : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule r1)] none 1 false false,
       Alt.mk [.call (.rule r2), .look false (.tok lk)] none 1 false false]) :
    OrNotLook id r1 r2 lk := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  refine ⟨fun v s h1 hv => ?_, fun s0 h0 h0e => ⟨fun e x s1 s2 h1 hE h2 => ⟨fun hx => ?_, fun hx => ?_⟩,
    fun s1 h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) hE, items_look (by rw [call_tok, h2]) (by simpa using hx),
          items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h1]) hE, items_look_fail (by rw [call_tok, h2]) (by simpa using hx)]),
      alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl

/-! ### `starred_expression` -/

/-- `starred_expression` (`Grammar/python.gram:1094-1097`):
```
    | invalid_starred_expression_unpacking
    | '*' a=expression { _PyAST_Starred(a, Load, EXTRA) }
    | invalid_starred_expression
```
In the second pass `invalid_starred_expression_unpacking` (266) first. Then (`InvPassAt`), from
`X`: `*` (16) and an `expression` (109) give `Starred(a, Load)`; once that fails, ending in `s`,
the first pass gives `NULL` with the mark back and the second `invalid_starred_expression` (268)
from the start mark. -/
def StarredExpression : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (q.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 2) 266 q = (v, s) → v ≠ .null →
    callRule (f + 7) 190 p = (v, s.leave)) ∧
  (q.callInvalidRules = true → ∀ (s : PS), callRule (f + 2) 266 q = (.null, s) →
    s.errorIndicator = true → callRule (f + 7) 190 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPassAt (f + 2) 266 q p.mark X →
    (∀ (a : Ast) (c : Token) (s1 s2 : PS), expectToken 16 X = (.tok c, s1) → callRule f 109 s1 = (a, s2) →
      a ≠ .null → s2.errorIndicator = false →
      callRule (f + 7) 190 p = (mkAt .Starred [a, opNode .Load] (extraLoc t s2), s2.leave)) ∧
    (∀ (s : PS), (expectToken 16 X = (.null, s) ∨
        ∃ c s1, expectToken 16 X = (.tok c, s1) ∧ callRule f 109 s1 = (.null, s)) →
      (s.callInvalidRules = false → callRule (f + 7) 190 p = (.null, { s with mark := p.mark }.leave)) ∧
      (s.callInvalidRules = true → s.errorIndicator = false → ∀ (v : Ast) (s' : PS),
        callRule f 268 { s with mark := p.mark } = (v, s') → v ≠ .null →
        callRule (f + 7) 190 p = (v, s'.leave)) ∧
      (s.callInvalidRules = true → s.errorIndicator = false → ∀ (s' : PS),
        callRule f 268 { s with mark := p.mark } = (.null, s') →
        callRule (f + 7) 190 p = (.null, { s' with mark := p.mark }.leave))))

theorem starredExpression_proven : StarredExpression := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 190 = r190 from rfl, r190]
  have hI : Alt.mk [.call (.rule 266)] none 1 true false = invAlt 266 := rfl
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 5 = (f + 2) + 3 from rfl, hI, invAltAt_ok he hi h1 hv]
    rfl
  · rw [show f + 5 = (f + 2) + 3 from rfl, hI, invAltAt_err he hi rfl h1 h1e]
    rfl
  have hXe := invPassAt_ei he hX
  rw [show f + 5 = (f + 2) + 3 from rfl, hI, invPassAt_alts he hX]
  refine ⟨fun a c s1 s2 h1 h2 ha h2e => ?_, fun s hs => ⟨fun hi => ?_, fun hi hse v s' h1 hv => ?_,
    fun hi hse s' h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e]
  all_goals
    have hA : runItems (f + 3) [.call (.tok 16), .call (.rule 109)] #[] false X = ((none, false), s) := by
      rcases hs with h1 | ⟨c, s1, h1, h2⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
  · rw [alts_fail (by rfl) hXe hA, alts_skip (by simp [hi]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) hXe hA, alts_ok (by simp [hi])
      (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
      (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) hXe hA, alts_fail (by simp [hi])
      (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
      (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-! ### `kwarg_or_starred`, `kwarg_or_double_starred` -/

/-- `a=NAME '=' b=expression` failing from `X`, ending in `s`. -/
def KwA1Fails (f : Nat) (X s : PS) : Prop :=
  nameToken X = (.null, s) ∨
  (∃ (n : Ast) (s1 : PS), nameToken X = (n, s1) ∧ n ≠ .null ∧ expectToken 22 s1 = (.null, s)) ∨
  (∃ (n : Ast) (c : Token) (s1 s2 : PS), nameToken X = (n, s1) ∧ n ≠ .null ∧
    expectToken 22 s1 = (.tok c, s2) ∧ callRule f 109 s2 = (.null, s))

theorem kwA1_items {f : Nat} {X s : PS} (h : KwA1Fails f X s) :
    runItems (f + 4) [.call .name, .call (.tok 22), .call (.rule 109)] #[] false X = ((none, false), s) := by
  rcases h with h1 | ⟨n, s1, h1, hn, h2⟩ | ⟨n, c, s1, s2, h1, hn, h2, h3⟩
  · rw [items_call_null (by rw [call_name, h1])]
  · rw [items_call (by rw [call_name, h1]) hn, items_call_null (by rw [call_tok, h2])]
  · rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]

/-- `_PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(arg, value, EXTRA)), 1)`. -/
def kwRec (arg value : Ast) (l : Loc) : Ast := rec_ .PKeywordOrStarred [mkAt .keyword_ [arg, value] l, .int 1]

/-- `kwarg_or_starred` (`Grammar/python.gram:1099-1103`):
```
    | invalid_kwarg
    | a=NAME '=' b=expression {
        _PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(a->v.Name.id, b, EXTRA)), 1) }
    | a=starred_expression { _PyPegen_keyword_or_starred(p, a, 0) }
```
In the second pass `invalid_kwarg` (209) first. Then, from `X`: `NAME` `=` (22) `expression` (109)
gives the `KeywordOrStarred` record of `keyword(name, value)` with flag 1; once that fails, a
`starred_expression` (190) from the start mark gives the record of it with flag 0; otherwise `NULL`
with the mark back. -/
def KwargOrStarred : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (q.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 3) 209 q = (v, s) → v ≠ .null →
    callRule (f + 8) 191 p = (v, s.leave)) ∧
  (q.callInvalidRules = true → ∀ (s : PS), callRule (f + 3) 209 q = (.null, s) →
    s.errorIndicator = true → callRule (f + 8) 191 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPassAt (f + 3) 209 q p.mark X →
    (∀ (n b : Ast) (c : Token) (s1 s2 s3 : PS), nameToken X = (n, s1) → n ≠ .null →
      expectToken 22 s1 = (.tok c, s2) → callRule f 109 s2 = (b, s3) → b ≠ .null →
      s3.errorIndicator = false →
      callRule (f + 8) 191 p = (kwRec (fieldOf n "id") b (extraLoc t s3), s3.leave)) ∧
    (∀ (s0 : PS), KwA1Fails f X s0 → s0.errorIndicator = false →
      (∀ (a : Ast) (s : PS), callRule (f + 1) 190 { s0 with mark := p.mark } = (a, s) → a ≠ .null →
        s.errorIndicator = false →
        callRule (f + 8) 191 p = (rec_ .PKeywordOrStarred [a, .int 0], s.leave)) ∧
      (∀ (s : PS), callRule (f + 1) 190 { s0 with mark := p.mark } = (.null, s) →
        callRule (f + 8) 191 p = (.null, { s with mark := p.mark }.leave))))

theorem kwargOrStarred_proven : KwargOrStarred := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 191 = r191 from rfl, r191]
  have hI : Alt.mk [.call (.rule 209)] none 1 true false = invAlt 209 := rfl
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 6 = (f + 3) + 3 from rfl, hI, invAltAt_ok he hi h1 hv]
    rfl
  · rw [show f + 6 = (f + 3) + 3 from rfl, hI, invAltAt_err he hi rfl h1 h1e]
    rfl
  have hXe := invPassAt_ei he hX
  rw [show f + 6 = (f + 3) + 3 from rfl, hI, invPassAt_alts he hX]
  refine ⟨fun n b c s1 s2 s3 h1 hn h2 h3 hb h3e => ?_, fun s0 h0 h0e =>
    ⟨fun a s h1 ha h1e => ?_, fun s h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e, kwRec, rec_, mkAt, extraLoc, locArgs, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) hXe (kwA1_items h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h1e, rec_]
  · rw [alts_fail (by rfl) hXe (kwA1_items h0), alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `kwarg_or_double_starred` (`Grammar/python.gram:1105-1110`):
```
    | invalid_kwarg
    | a=NAME '=' b=expression {
        _PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(a->v.Name.id, b, EXTRA)), 1) }
    | '**' a=expression { _PyPegen_keyword_or_starred(p, CHECK(keyword_ty, _PyAST_keyword(NULL, a, EXTRA)), 1) }
```
As `kwarg_or_starred`, with `**` (35) `expression` giving `keyword(NULL, value)` for the last
alternative. -/
def KwargOrDoubleStarred : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (q.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 3) 209 q = (v, s) → v ≠ .null →
    callRule (f + 8) 192 p = (v, s.leave)) ∧
  (q.callInvalidRules = true → ∀ (s : PS), callRule (f + 3) 209 q = (.null, s) →
    s.errorIndicator = true → callRule (f + 8) 192 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPassAt (f + 3) 209 q p.mark X →
    (∀ (n b : Ast) (c : Token) (s1 s2 s3 : PS), nameToken X = (n, s1) → n ≠ .null →
      expectToken 22 s1 = (.tok c, s2) → callRule f 109 s2 = (b, s3) → b ≠ .null →
      s3.errorIndicator = false →
      callRule (f + 8) 192 p = (kwRec (fieldOf n "id") b (extraLoc t s3), s3.leave)) ∧
    (∀ (s0 : PS), KwA1Fails f X s0 → s0.errorIndicator = false →
      (∀ (a : Ast) (c : Token) (s1 s2 : PS), expectToken 35 { s0 with mark := p.mark } = (.tok c, s1) →
        callRule f 109 s1 = (a, s2) → a ≠ .null → s2.errorIndicator = false →
        callRule (f + 8) 192 p = (kwRec .null a (extraLoc t s2), s2.leave)) ∧
      (∀ (s : PS), (expectToken 35 { s0 with mark := p.mark } = (.null, s) ∨
          ∃ c s1, expectToken 35 { s0 with mark := p.mark } = (.tok c, s1) ∧ callRule f 109 s1 = (.null, s)) →
        callRule (f + 8) 192 p = (.null, { s with mark := p.mark }.leave))))

theorem kwargOrDoubleStarred_proven : KwargOrDoubleStarred := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 192 = r192 from rfl, r192]
  have hI : Alt.mk [.call (.rule 209)] none 1 true false = invAlt 209 := rfl
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 6 = (f + 3) + 3 from rfl, hI, invAltAt_ok he hi h1 hv]
    rfl
  · rw [show f + 6 = (f + 3) + 3 from rfl, hI, invAltAt_err he hi rfl h1 h1e]
    rfl
  have hXe := invPassAt_ei he hX
  rw [show f + 6 = (f + 3) + 3 from rfl, hI, invPassAt_alts he hX]
  refine ⟨fun n b c s1 s2 s3 h1 hn h2 h3 hb h3e => ?_, fun s0 h0 h0e =>
    ⟨fun a c s1 s2 h1 h2 ha h2e => ?_, fun s hs => ?_⟩⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hn, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e, kwRec, rec_, mkAt, extraLoc, locArgs, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) hXe (kwA1_items h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h2e, kwRec, rec_, mkAt, extraLoc, locArgs, StateT.pure, StateT.bind, pure, bind]
  · have hB : runItems (f + 3) [.call (.tok 35), .call (.rule 109)] #[] false { s0 with mark := p.mark } =
        ((none, false), s) := by
      rcases hs with h1 | ⟨c, s1, h1, h2⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
    rw [alts_fail (by rfl) hXe (kwA1_items h0), alts_fail (by rfl) (E s0 h0e) hB, alts_nil]
    rfl

/-! ### `kwargs` -/

/-- `kwargs` (`Grammar/python.gram:1089-1092`):
```
    | a=','.kwarg_or_starred+ ',' b=','.kwarg_or_double_starred+ { _PyPegen_join_sequences(p, a, b) }
    | ','.kwarg_or_starred+
    | ','.kwarg_or_double_starred+
```
No `EXTRA`. The gather of `kwarg_or_starred` (`_gather_94`, 371), `,` (12) and the gather of
`kwarg_or_double_starred` (`_gather_96`, 373) give the two sequences joined; once that fails, the
first gather alone from the start mark; then the second alone; otherwise `NULL` with the mark
back. -/
def Kwargs : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a b : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 371 p.enter = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.tok c, s2) → callRule f 373 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false → callRule (f + 7) 189 p = (joinSeq a b, s3.leave)) ∧
  (∀ (s0 : PS), (callRule (f + 2) 371 p.enter = (.null, s0) ∨
      (∃ a s1, callRule (f + 2) 371 p.enter = (a, s1) ∧ a ≠ .null ∧ expectToken 12 s1 = (.null, s0)) ∨
      (∃ a c s1 s2, callRule (f + 2) 371 p.enter = (a, s1) ∧ a ≠ .null ∧
        expectToken 12 s1 = (.tok c, s2) ∧ callRule f 373 s2 = (.null, s0))) →
    s0.errorIndicator = false →
    (∀ (v : Ast) (s : PS), callRule (f + 1) 371 { s0 with mark := p.mark } = (v, s) → v ≠ .null →
      callRule (f + 7) 189 p = (v, s.leave)) ∧
    (∀ (s1 : PS), callRule (f + 1) 371 { s0 with mark := p.mark } = (.null, s1) →
      s1.errorIndicator = false →
      (∀ (v : Ast) (s : PS), callRule f 373 { s1 with mark := p.mark } = (v, s) → v ≠ .null →
        callRule (f + 7) 189 p = (v, s.leave)) ∧
      (∀ (s : PS), callRule f 373 { s1 with mark := p.mark } = (.null, s) →
        callRule (f + 7) 189 p = (.null, { s with mark := p.mark }.leave))))

theorem kwargs_proven : Kwargs := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 189 = r189 from rfl, r189]
  refine ⟨fun a b c s1 s2 s3 h1 ha h2 h3 hb h3e => ?_, fun s0 h0 h0e =>
    ⟨fun v s h1 hv => ?_, fun s1 h1 h1e => ⟨fun v s h2 hv => ?_, fun s h2 => ?_⟩⟩⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h3e, joinSeq]
  all_goals
    have hA : runItems (f + 4) [.call (.rule 371), .call (.tok 12), .call (.rule 373)] #[] false p.enter =
        ((none, false), s0) := by
      rcases h0 with h0 | ⟨a, s1, h0, ha, h0'⟩ | ⟨a, c, s1, s2, h0, ha, h0', h0''⟩
      · rw [items_call_null (by rw [call_rule, h0])]
      · rw [items_call (by rw [call_rule, h0]) ha, items_call_null (by rw [call_tok, h0'])]
      · rw [items_call (by rw [call_rule, h0]) ha, items_call (by rw [call_tok, h0']) (by simp),
          items_call_null (by rw [call_rule, h0''])]
  · rw [alts_fail (by rfl) he' hA, alts_ok (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' hA, alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_ok (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' hA, alts_fail (by rfl) (E s0 h0e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_fail (by rfl) (E s1 h1e) (by
      dsimp only; rw [items_call_null (by rw [call_rule, h2])]), alts_nil]
    rfl

/-! ### `type_param_bound`, `type_param_default`, `type_param_starred_default` -/

/-- `type_param_bound: ':' e=expression { e }` (`Grammar/python.gram:701`): `TokThen 105 11 109`. -/
theorem typeParamBound_proven : TokThen 105 11 109 := tokThen_of rfl

/-- A rule `x: tok e=rr { CHECK_VERSION(t, ver, pre, e) }` (no `EXTRA`): at the token `tk`, the
`rr` after it behind `CHECK_VERSION`; at another token, or without `rr`, `NULL` with the mark
back. -/
def TokThenCV (id tk rr ver : Nat) (msg : String) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type ≠ tk → callRule (f + 6) id p = (.null, q.leave)) ∧
  (t.type = tk → ∀ (e : Ast) (s : PS), callRule f rr { q with mark := p.mark + 1 } = (e, s) →
    e ≠ .null → s.errorIndicator = false → CVRes ver msg (callRule (f + 6) id p) e s) ∧
  (t.type = tk → ∀ (s : PS), callRule f rr { q with mark := p.mark + 1 } = (.null, s) →
    callRule (f + 6) id p = (.null, { s with mark := p.mark }.leave))

theorem tokThenCV_of {id tk rr ver : Nat} {pre msg : String}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.tok tk), .call (.rule rr)] (some (.checkVersion (.int ver) (.str pre) (.var 1)))
        2 false false])
    (hmsg : toString (cpsStr (pre.toList.map Char.toNat)) ++ toString " only supported in Python 3." ++
      toString (ver : Int) ++ toString " and greater" = msg) :
    TokThenCV id tk rr ver msg := by
  intro f p q h
  obtain ⟨-, -, -, -, hm, -, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) h.ei h.level, hr]
  refine ⟨fun ht => ?_, fun ht e s h1 hE h1e => ?_, fun ht s h1 => ?_⟩
  · rw [alts_fail (by rfl) he' (items_call_null (by rw [call_tok, expect_entered h, ite_f ht])), hq,
      alts_nil]
    rfl
  · dsimp only
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) hE, items_nil])]
    exact altResult_cvg rfl rfl (by simp only [evalA, pure, StateT.pure]; rfl) hE h1e hmsg
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

def typeParamDefaultMsg : String := "Type parameter defaults are only supported in Python 3.13 and greater"

/-- `type_param_default: '=' e=expression { CHECK_VERSION(expr_ty, 13, "Type parameter defaults
are", e) }` (`Grammar/python.gram:702`). -/
theorem typeParamDefault_proven : TokThenCV 106 22 109 13 typeParamDefaultMsg :=
  tokThenCV_of rfl (by decide +kernel)
/-- `type_param_starred_default: '=' e=star_expression { CHECK_VERSION(expr_ty, 13, "Type
parameter defaults are", e) }` (`Grammar/python.gram:704`). -/
theorem typeParamStarredDefault_proven : TokThenCV 107 22 113 13 typeParamDefaultMsg :=
  tokThenCV_of rfl (by decide +kernel)

/-! ### `type_params`, `type_param_seq` -/

def typeParamsMsg : String := "Type parameter lists are only supported in Python 3.12 and greater"

/-- `type_params` (`Grammar/python.gram:688-691`):
```
    | invalid_type_params
    | '[' t=type_param_seq ']' {
        CHECK_VERSION(asdl_type_param_seq *, 12, "Type parameter lists are", t) }
```
No `EXTRA`. In the second pass `invalid_type_params` (276) first. Then, from `X`: `[` (9), a
`type_param_seq` (103) and `]` (10) give the sequence behind `CHECK_VERSION` 12; otherwise `NULL`
with the mark back. -/
def TypeParams : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (p.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 3) 276 p.enter = (v, s) →
    v ≠ .null → callRule (f + 8) 102 p = (v, s.leave)) ∧
  (p.callInvalidRules = true → ∀ (s : PS), callRule (f + 3) 276 p.enter = (.null, s) →
    s.errorIndicator = true → callRule (f + 8) 102 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPass (f + 3) 276 p X →
    (∀ (a : Ast) (c c' : Token) (s1 s2 s3 : PS), expectToken 9 X = (.tok c, s1) →
      callRule (f + 1) 103 s1 = (a, s2) → a ≠ .null → expectToken 10 s2 = (.tok c', s3) →
      s3.errorIndicator = false → CVRes 12 typeParamsMsg (callRule (f + 8) 102 p) a s3) ∧
    (∀ (s : PS), (expectToken 9 X = (.null, s) ∨
        (∃ c s1, expectToken 9 X = (.tok c, s1) ∧ callRule (f + 1) 103 s1 = (.null, s)) ∨
        (∃ c a s1 s2, expectToken 9 X = (.tok c, s1) ∧ callRule (f + 1) 103 s1 = (a, s2) ∧ a ≠ .null ∧
          expectToken 10 s2 = (.null, s))) →
      callRule (f + 8) 102 p = (.null, { s with mark := p.mark }.leave)))

theorem typeParams_proven : TypeParams := by
  intro f p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 102 = r102 from rfl, r102]
  have hI : Alt.mk [.call (.rule 276)] none 1 true false = invAlt 276 := rfl
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 6 = (f + 3) + 3 from rfl, hI, invAlt_ok he hi h1 hv]
    rfl
  · rw [show f + 6 = (f + 3) + 3 from rfl, hI, invAlt_err he hi rfl h1 h1e]
    rfl
  have hXe := invPass_ei he hX
  rw [show f + 6 = (f + 3) + 3 from rfl, hI, invPass_alts he hX]
  refine ⟨fun a c c' s1 s2 s3 h1 h2 ha h3 h3e => ?_, fun s hs => ?_⟩
  · try dsimp only
    rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_tok, h3]) (by simp), items_nil])]
    exact altResult_cvg rfl rfl (by simp only [evalA, pure, StateT.pure]; rfl) ha h3e (by decide +kernel)
  · have hA : runItems (f + 4) [.call (.tok 9), .call (.rule 103), .call (.tok 10)] #[] false X =
        ((none, false), s) := by
      rcases hs with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, a, s1, s2, h1, h2, ha, h3⟩
      · rw [items_call_null (by rw [call_tok, h1])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
      · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
          items_call_null (by rw [call_tok, h3])]
    rw [alts_fail (by rfl) hXe hA, alts_nil]
    have hXm : X.mark = p.mark := by
      rcases hX with ⟨-, rfl⟩ | ⟨-, s', -, -, rfl⟩ <;> rfl
    rfl

/-- `type_param_seq[asdl_type_param_seq*]: a[asdl_type_param_seq*]=','.type_param+ [','] { a }`
(`Grammar/python.gram:693`): `GatherOptComma 103 331` with `_gather_54` (331) of `type_param`
(104). -/
def TypeParamSeqRule : Prop := GatherOptComma 103 331 ∧ GatherSep 331 330 104
theorem typeParamSeqRule_proven : TypeParamSeqRule := ⟨gatherOptComma_of rfl, gatherSep_of rfl rfl⟩

end PyLean.PyGrammar.Peg
