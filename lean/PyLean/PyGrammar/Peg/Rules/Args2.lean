import PyLean.PyGrammar.Peg.Rules.Args

/-! `args`, `arguments` (`Grammar/python.gram:1077-1087`) and `type_param`
(`Grammar/python.gram:695-699`), rule by rule, with the gathers and groups they call. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `args` -/

/-- `_PyPegen_seq_extract_starred_exprs` / `_PyPegen_seq_delete_starred_exprs`
(`Parser/action_helpers.c`): the starred (flag 0) and the keyword (flag 1) items of a
`KeywordOrStarred` sequence, `NULL` when there is none. -/
def starredOf (a : Ast) : Ast :=
  let xs := (seqOf a).filter (fun k => !isKeywordRec k)
  if xs.isEmpty then .null else .seq (xs.map (recField · 0))
def keywordsOf (a : Ast) : Ast :=
  let xs := (seqOf a).filter isKeywordRec
  if xs.isEmpty then .null else .seq (xs.map (recField · 0))

/-- `args` (`Grammar/python.gram:1081-1087`):
```
    | a[asdl_expr_seq*]=','.(starred_expression | ( assignment_expression | expression !':=') !'=')+ b=[',' k=kwargs {k}] {
        _PyPegen_collect_call_seqs(p, a, b, EXTRA) }
    | a=kwargs { _PyAST_Call(_PyPegen_dummy_name(p),
                          CHECK_NULL_ALLOWED(asdl_expr_seq*, _PyPegen_seq_extract_starred_exprs(p, a)),
                          CHECK_NULL_ALLOWED(asdl_keyword_seq*, _PyPegen_seq_delete_starred_exprs(p, a)),
                          EXTRA) }
```
The positional gather (`_gather_91`, 368) and the optional `, kwargs` group (`_tmp_92`, 369) give
`_PyPegen_collect_call_seqs` (a dummy `Call` with the positional and starred items as `args` and
the keywords as `keywords`); once that fails, `kwargs` (189) from the start mark gives the dummy
`Call` with the starred items as `args` and the keyword items as `keywords`; otherwise `NULL`
with the mark back. The `CHECK_NULL_ALLOWED` of an empty part raises nothing when no exception is
pending (`errOccurred = false`). -/
def ArgsRule : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a b : Ast) (s1 s2 : PS), callRule (f + 1) 368 q = (a, s1) → a ≠ .null →
    callRule f 369 s1 = (b, s2) → s2.errorIndicator = false →
    callRule (f + 6) 188 p =
      (collectCallSeqs a b (extraLoc t s2).lineno (extraLoc t s2).colOffset (extraLoc t s2).endLineno
        (extraLoc t s2).endColOffset, s2.leave)) ∧
  (∀ (s0 : PS), callRule (f + 1) 368 q = (.null, s0) → s0.errorIndicator = false →
    (∀ (a : Ast) (s : PS), callRule f 189 { s0 with mark := p.mark } = (a, s) → a ≠ .null →
      s.errorIndicator = false → s.errOccurred = false →
      callRule (f + 6) 188 p =
        (mkAt .Call [rec_ .PDummy [], starredOf a, keywordsOf a] (extraLoc t s), s.leave)) ∧
    (∀ (s : PS), callRule f 189 { s0 with mark := p.mark } = (.null, s) →
      callRule (f + 6) 188 p = (.null, { s with mark := p.mark }.leave)))

theorem collectCallSeqs_nonNull (a b : Ast) (l c el ec : Int) :
    nonNull (collectCallSeqs a b l c el ec) = true := by
  unfold collectCallSeqs
  split <;> simp [mkAt, mkAst, nonNull]

theorem argsRule_proven : ArgsRule := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 188 = r188 from rfl, r188]
  refine ⟨fun a b s1 s2 h1 ha h2 h2e => ?_, fun s0 h0 h0e => ⟨fun a s h1 ha h1e h1o => ?_, fun s h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      extraLoc]
    simp [collectCallSeqs_nonNull, h2e, StateT.pure, StateT.bind, pure, bind]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (E s0 h0e) (by dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
      mkAt, extraLoc, locArgs, get, getThe, MonadStateOf.get, StateT.get]
    by_cases hx : ((seqOf a).filter (fun k => !isKeywordRec k)).isEmpty <;>
    by_cases hy : ((seqOf a).filter isKeywordRec).isEmpty <;>
      simp [hx, hy, starredOf, keywordsOf, mkAst, nonNull, StateT.pure, StateT.bind, pure, bind,
        h1o, h1e, StateT.get, get, getThe, MonadStateOf.get]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_fail (by rfl) (E s0 h0e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl

/-- `args` with the gathers and groups it calls: `_gather_91` (368) of `_tmp_167` (444:
`starred_expression | _tmp_178 !'='`), `_tmp_178` (455: `assignment_expression | expression
!':='`), `_tmp_92` (369: `',' k=kwargs { k }`), and `kwargs`' gathers `_gather_94` (371) of
`kwarg_or_starred` and `_gather_96` (373) of `kwarg_or_double_starred`. -/
def ArgsRuleFull : Prop := ArgsRule ∧ GatherSep 368 367 444 ∧ OrNotLook 444 190 455 22 ∧
  OrNotLook 455 118 109 53 ∧ TokThen 369 12 189
theorem argsRuleFull_proven : ArgsRuleFull :=
  ⟨argsRule_proven, gatherSep_of rfl rfl, orNotLook_of rfl, orNotLook_of rfl, tokThen_of rfl⟩

def KwargsRule : Prop := Kwargs ∧ GatherSep 371 370 191 ∧ GatherSep 373 372 192
theorem kwargsRule_proven : KwargsRule := ⟨kwargs_proven, gatherSep_of rfl rfl, gatherSep_of rfl rfl⟩

/-! ### `arguments` -/

/-- `a=args [','] &')'` failing from the entry state `q`, ending in `s`. -/
def ArgumentsA0Fails (f : Nat) (q s : PS) : Prop :=
  callRule (f + 2) 188 q = (.null, s) ∨
  ∃ (a x y : Ast) (s1 s2 s3 : PS), callRule (f + 2) 188 q = (a, s1) ∧ a ≠ .null ∧
    expectToken 12 s1 = (x, s2) ∧ s2.errorIndicator = false ∧ expectToken 8 s2 = (y, s3) ∧
    nonNull y = false ∧ s = { s3 with mark := s2.mark }

/-- `arguments (memo)` (`Grammar/python.gram:1077-1079`):
```
    | a=args [','] &')' { a }
    | invalid_arguments
```
No `EXTRA`. `args` (188), an optional `,` (12), and `)` (8) next (not consumed) give `args`'s
`Call`; once that fails, in the first pass `NULL` with the mark back; in the second an error
already set gives `NULL`, otherwise `invalid_arguments` (208) from the start mark. Every result is
memoized at the start mark (an error return is not). -/
def Arguments : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 187) = none →
  (∀ (a x y : Ast) (s1 s2 s3 : PS), callRule (f + 2) 188 q = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (x, s2) → s2.errorIndicator = false → expectToken 8 s2 = (y, s3) →
    nonNull y = true → s3.errorIndicator = false →
    callRule (f + 7) 187 p = memoDone p.mark 187 (some a, { s3 with mark := s2.mark })) ∧
  (∀ (s : PS), ArgumentsA0Fails f q s →
    (s.callInvalidRules = false →
      callRule (f + 7) 187 p = memoDone p.mark 187 (some .null, { s with mark := p.mark })) ∧
    (s.callInvalidRules = true → s.errorIndicator = true →
      callRule (f + 7) 187 p = memoDone p.mark 187 (none, { s with mark := p.mark })) ∧
    (s.callInvalidRules = true → s.errorIndicator = false → ∀ (v : Ast) (s' : PS),
      callRule (f + 1) 208 { s with mark := p.mark } = (v, s') → v ≠ .null →
      callRule (f + 7) 187 p = memoDone p.mark 187 (some v, s')) ∧
    (s.callInvalidRules = true → s.errorIndicator = false → ∀ (s' : PS),
      callRule (f + 1) 208 { s with mark := p.mark } = (.null, s') →
      callRule (f + 7) 187 p = memoDone p.mark 187 (some .null, { s' with mark := p.mark })))

theorem arguments_proven : Arguments := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 187 = r187 from rfl, r187]
  have hA : ∀ s, ArgumentsA0Fails f q s →
      runItems (f + 4) [.call (.rule 188), .opt (.tok 12), .look true (.tok 8)] #[] false q =
        ((none, false), s) := by
    intro s hs
    rcases hs with h1 | ⟨a, x, y, s1, s2, s3, h1, ha, h2, h2e, h3, hy, rfl⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_tok, h2]) h2e,
        items_look_fail (by rw [call_tok, h3]) (by simpa using hy)]
  refine ⟨fun a x y s1 s2 s3 h1 ha h2 h2e h3 hy h3e => ?_, fun s hs =>
    ⟨fun hi => ?_, fun hi hse => ?_, fun hi hse v s' h1 hv => ?_, fun hi hse s' h1 => ?_⟩⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_tok, h2]) h2e,
        items_look (by rw [call_tok, h3]) hy, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, Bool.or_false, show ({ s3 with mark := s2.mark } : PS).errorIndicator = false from h3e]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he (hA s hs), alts_skip (by simp [hi]), alts_nil]
  · rw [alts_fail (by rfl) he (hA s hs),
      alts_err (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = true from hse)]
  · rw [alts_fail (by rfl) he (hA s hs),
      alts_ok (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
        (by dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (hA s hs),
      alts_fail (by simp [hi]) (show ({ s with mark := p.mark } : PS).errorIndicator = false from hse)
        (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]

/-! ### `type_param` -/

/-- `type_param (memo)` (`Grammar/python.gram:695-699`):
```
    | a=NAME b=[type_param_bound] c=[type_param_default] { _PyAST_TypeVar(a->v.Name.id, b, c, EXTRA) }
    | invalid_type_param
    | '*' a=NAME b=[type_param_starred_default] { _PyAST_TypeVarTuple(a->v.Name.id, b, EXTRA) }
    | '**' a=NAME b=[type_param_default] { _PyAST_ParamSpec(a->v.Name.id, b, EXTRA) }
```
A `NAME`, the optional `type_param_bound` (105) and `type_param_default` (106) give
`TypeVar(name, bound, default)`; with no `NAME`, in the second pass `invalid_type_param` (212)
first; then (`InvPassAt`), from `X`: `*` (16), `NAME` and the optional
`type_param_starred_default` (107) give `TypeVarTuple(name, default)`; once that fails, `**` (35),
`NAME` and the optional `type_param_default` give `ParamSpec(name, default)`; otherwise `NULL`
with the mark back. Every result is memoized at the start mark. -/
def TypeParam : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 104) = none →
  let t := q.tokenAt p.mark
  (∀ (n b d : Ast) (s1 s2 s3 : PS), nameToken q = (n, s1) → n ≠ .null →
    callRule (f + 4) 105 s1 = (b, s2) → s2.errorIndicator = false →
    callRule (f + 3) 106 s2 = (d, s3) → s3.errorIndicator = false →
    callRule (f + 10) 104 p =
      memoDone p.mark 104 (some (mkAt .TypeVar [fieldOf n "id", b, d] (extraLoc t s3)), s3)) ∧
  (∀ (s0 : PS), nameToken q = (.null, s0) → s0.errorIndicator = false →
    let S := { s0 with mark := p.mark }
    (S.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 4) 212 S = (v, s) → v ≠ .null →
      callRule (f + 10) 104 p = memoDone p.mark 104 (some v, s)) ∧
    (S.callInvalidRules = true → ∀ (s : PS), callRule (f + 4) 212 S = (.null, s) →
      s.errorIndicator = true →
      callRule (f + 10) 104 p = memoDone p.mark 104 (none, { s with mark := p.mark })) ∧
    (∀ (X : PS), InvPassAt (f + 4) 212 S p.mark X →
      (∀ (n d : Ast) (c : Token) (s1 s2 s3 : PS), expectToken 16 X = (.tok c, s1) →
        nameToken s1 = (n, s2) → n ≠ .null → callRule (f + 1) 107 s2 = (d, s3) →
        s3.errorIndicator = false →
        callRule (f + 10) 104 p =
          memoDone p.mark 104 (some (mkAt .TypeVarTuple [fieldOf n "id", d] (extraLoc t s3)), s3)) ∧
      (∀ (s4 : PS), (expectToken 16 X = (.null, s4) ∨
          ∃ c s1, expectToken 16 X = (.tok c, s1) ∧ nameToken s1 = (.null, s4)) →
        s4.errorIndicator = false →
        (∀ (n d : Ast) (c : Token) (s5 s6 s7 : PS), expectToken 35 { s4 with mark := p.mark } = (.tok c, s5) →
          nameToken s5 = (n, s6) → n ≠ .null → callRule f 106 s6 = (d, s7) →
          s7.errorIndicator = false →
          callRule (f + 10) 104 p =
            memoDone p.mark 104 (some (mkAt .ParamSpec [fieldOf n "id", d] (extraLoc t s7)), s7)) ∧
        (∀ (s : PS), (expectToken 35 { s4 with mark := p.mark } = (.null, s) ∨
            ∃ c s5, expectToken 35 { s4 with mark := p.mark } = (.tok c, s5) ∧ nameToken s5 = (.null, s)) →
          callRule (f + 10) 104 p = memoDone p.mark 104 (some .null, { s with mark := p.mark })))))

theorem typeParam_proven : TypeParam := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 104 = r104 from rfl, r104]
  have hI : Alt.mk [.call (.rule 212)] none 1 true false = invAlt 212 := rfl
  refine ⟨fun n b d s1 s2 s3 h1 hN h2 h2e h3 h3e => ?_, fun s0 h0 h0e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) hN, items_opt (by rw [call_rule, h2]) h2e,
        items_opt (by rw [call_rule, h3]) h3e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  have hA0 : runItems (f + 7) [.call .name, .opt (.rule 105), .opt (.rule 106)] #[] false q =
      ((none, false), s0) := by
    rw [items_call_null (by rw [call_name, h0])]
  try dsimp only
  rw [alts_fail (by rfl) he hA0, show f + 7 = (f + 4) + 3 from rfl, hI]
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [invAltAt_ok (E s0 h0e) hi h1 hv]
  · rw [invAltAt_err (E s0 h0e) hi rfl h1 h1e]
  have hXe := invPassAt_ei (E s0 h0e) hX
  rw [invPassAt_alts (E s0 h0e) hX]
  refine ⟨fun n d c s1 s2 s3 h1 h2 hN h3 h3e => ?_, fun s4 h4 h4e =>
    ⟨fun n d c s5 s6 s7 h5 h6 hN h7 h7e => ?_, fun s hs => ?_⟩⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_name, h2]) hN,
        items_opt (by rw [call_rule, h3]) h3e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h3e]
  all_goals
    have hA2 : runItems (f + 5) [.call (.tok 16), .call .name, .opt (.rule 107)] #[] false X =
        ((none, false), s4) := by
      rcases h4 with h4 | ⟨c, s1, h4, h4'⟩
      · rw [items_call_null (by rw [call_tok, h4])]
      · rw [items_call (by rw [call_tok, h4]) (by simp), items_call_null (by rw [call_name, h4'])]
  · rw [alts_fail (by rfl) hXe hA2, alts_ok (by rfl) (E s4 h4e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_name, h6]) hN,
        items_opt (by rw [call_rule, h7]) h7e, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra,
      mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, h7e]
  · have hA3 : runItems (f + 4) [.call (.tok 35), .call .name, .opt (.rule 106)] #[] false
        { s4 with mark := p.mark } = ((none, false), s) := by
      rcases hs with h5 | ⟨c, s5, h5, h5'⟩
      · rw [items_call_null (by rw [call_tok, h5])]
      · rw [items_call (by rw [call_tok, h5]) (by simp), items_call_null (by rw [call_name, h5'])]
    rw [alts_fail (by rfl) hXe hA2, alts_fail (by rfl) (E s4 h4e) hA3, alts_nil]


def TypeParamBoundRule : Prop := TokThen 105 11 109
theorem typeParamBoundRule_proven : TypeParamBoundRule := typeParamBound_proven
def TypeParamDefaultRule : Prop := TokThenCV 106 22 109 13 typeParamDefaultMsg
theorem typeParamDefaultRule_proven : TypeParamDefaultRule := typeParamDefault_proven
def TypeParamStarredDefaultRule : Prop := TokThenCV 107 22 113 13 typeParamDefaultMsg
theorem typeParamStarredDefaultRule_proven : TypeParamStarredDefaultRule := typeParamStarredDefault_proven

end PyLean.PyGrammar.Peg
