import PyLean.PyGrammar.Peg.Rules.Targets2

/-! The names of import statements (`Grammar/python.gram:242-258`): `import_from_as_names`,
`import_from_as_name`, `dotted_as_names`, `dotted_as_name` and the left-recursive `dotted_name`,
rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- Entry of the `_raw` function of a left-recursive leader that does not read `EXTRA`. -/
theorem ruleBody_noextra {f id : Nat} {σ : PS} (h3 : (ruleOf id).memo = false)
    (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = false)
    (he : σ.errorIndicator = false) (hl : σ.level ≠ MAXSTACK) :
    ruleBody (f + 1) id (ruleOf id) σ =
      let a := runAlts f (ruleOf id).alts false σ.mark (0, 0) σ.enter
      (a.1.getD .null, a.2.leave) := by
  have he' : σ.enter.errorIndicator = false := he
  have hp : rulePrologue id (ruleOf id) σ = (.inr (σ.mark, (0, 0)), σ.enter) := by
    simp only [rulePrologue, addLevel_ok σ hl, he', h3, Bool.false_eq_true, ↓reduceIte, ruleStart, h5]
    rfl
  simp only [ruleBody, hp, h4]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all [retLevel_eq]

/-- `e->v.Name.id`, as `%U` reads it. -/
def nameIdOf (e : Ast) : List Nat :=
  match fieldOf e "id" with
  | .ident s => s
  | _ => []

/-- `_PyPegen_join_names_with_dot(p, a, b)` (`Parser/action_helpers.c:123-139`): the `Name`
`"%U.%U"` of the two ids, `Load`, from the start of `a` to the end of `b` (`EXTRA_EXPR`). -/
def dotJoin (a b : Ast) : Ast :=
  mkAt .Name [.ident (nameIdOf a ++ [46] ++ nameIdOf b), opNode .Load]
    ⟨(locOf a).lineno, (locOf a).colOffset, (locOf b).endLineno, (locOf b).endColOffset⟩

/-! ### `dotted_name` -/

/-- One round of `dotted_name_raw` (`Grammar/python.gram:256-258`):
```
    | a=dotted_name '.' b=NAME { _PyPegen_join_names_with_dot(p, a, b) }
    | NAME
```
As `SumStep`, with no `EXTRA`: with no seed, the round is `NAME` (`NULL` with the mark back when
there is none); with a seed `v` and `.` NAME after it, the `Name` `v.id + "." + NAME.id` spanning
both (`_PyPegen_join_names_with_dot`); with a seed and no `.`, or `.` and no NAME, `NAME` from the
start mark. So `a.b.c` is one `Name` `"a.b.c"`. -/
def DottedNameStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1032) = some (1032, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  (v = .null → ∀ (n : Ast) (s : PS), nameToken σ.enter = (n, s) → n ≠ .null →
    ruleBody (f + 6) 32 (ruleOf 32) σ = (n, s.leave)) ∧
  (v = .null → ∀ (s : PS), nameToken σ.enter = (.null, s) →
    ruleBody (f + 6) 32 (ruleOf 32) σ = (.null, { s with mark := σ.mark }.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 : PS), expectToken 23 u = (.tok to, s2) →
    nameToken s2 = (b, s3) → b ≠ .null → s3.errorIndicator = false →
    ruleBody (f + 6) 32 (ruleOf 32) σ = (dotJoin v b, s3.leave)) ∧
  (v ≠ .null → ∀ (n : Ast) (to : Token) (s2 s3 s4 : PS), expectToken 23 u = (.tok to, s2) →
    nameToken s2 = (.null, s3) → s3.errorIndicator = false →
    nameToken { s3 with mark := σ.mark } = (n, s4) → n ≠ .null →
    ruleBody (f + 6) 32 (ruleOf 32) σ = (n, s4.leave)) ∧
  (v ≠ .null → ∀ (n : Ast) (s2 s3 : PS), expectToken 23 u = (.null, s2) → s2.errorIndicator = false →
    nameToken { s2 with mark := σ.mark } = (n, s3) → n ≠ .null →
    ruleBody (f + 6) 32 (ruleOf 32) σ = (n, s3.leave))

theorem dottedNameStep_proven : DottedNameStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 32 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 32 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 32) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  rw [ruleBody_noextra rfl rfl rfl he hσl]
  simp only [show ruleOf 32 = r32 from rfl, r32]
  refine ⟨fun hv n s h1 hn => ?_, fun hv s h1 => ?_, fun hv b to s2 s3 h2 h3 hb h3e => ?_,
    fun hv n to s2 s3 s4 h2 h3 h3e h4 hn => ?_, fun hv n s2 s3 h2 h2e h3 hn => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_name, h1]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_name, h3]) hb, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, h3e,
      Bool.or_false]
    simp only [mkAst, nonNull, dotJoin, mkAt, locArgs, rec_, Bool.not_true, Bool.false_or, h3e,
      Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call_null (by rw [call_name, h3])]),
      alts_ok (by rfl) (show ({ s3 with mark := σ.mark } : PS).errorIndicator = false from h3e) (by
        dsimp only; rw [items_call (by rw [call_name, h4]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := σ.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call (by rw [call_name, h3]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- `dotted_name`: one round and the loop. -/
def DottedNameRule : Prop := DottedNameStep ∧ LeaderLoop 32
theorem dottedNameRule_proven : DottedNameRule := ⟨dottedNameStep_proven, leaderLoop_of rfl rfl⟩

/-! ### `dotted_as_name`, `import_from_as_name` -/

/-- The `alias` an `as`-name alternative builds: `_PyAST_alias(a->v.Name.id, (b) ? b->v.Name.id :
NULL, EXTRA)`. -/
def aliasOf (a b : Ast) (l : Loc) : Ast :=
  mkAt .alias_ [fieldOf a "id", if truth b then fieldOf b "id" else .null] l

/-- `dotted_as_name` (`Grammar/python.gram:251-254`):
```
    | invalid_dotted_as_name
    | a=dotted_name b=['as' z=NAME { z }] { _PyAST_alias(
        a->v.Name.id, (b) ? ((expr_ty) b)->v.Name.id : NULL, EXTRA) }
```
`dotted_name` and an optional `'as' NAME` (`_tmp_21`) give `alias(name, asname)`, `asname`
`NULL` without `as`; no `dotted_name` gives `NULL`. In the second pass `invalid_dotted_as_name`
runs first, and its error ends the rule. -/
def DottedAsName : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (q.callInvalidRules = false → ∀ (a b : Ast) (s1 s2 : PS), callRule (f + 1) 32 q = (a, s1) →
    a ≠ .null → callRule f 298 s1 = (b, s2) → s2.errorIndicator = false →
    callRule (f + 7) 31 p = (aliasOf a b (extraLoc t s2), s2.leave)) ∧
  (q.callInvalidRules = false → ∀ (s1 : PS), callRule (f + 1) 32 q = (.null, s1) →
    callRule (f + 7) 31 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (q.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 2) 238 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 7) 31 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (q.callInvalidRules = true → ∀ (a b : Ast) (s0 s1 s2 : PS), callRule (f + 2) 238 q = (.null, s0) →
    s0.errorIndicator = false → callRule (f + 1) 32 { s0 with mark := p.mark } = (a, s1) →
    a ≠ .null → callRule f 298 s1 = (b, s2) → s2.errorIndicator = false →
    callRule (f + 7) 31 p = (aliasOf a b (extraLoc t s2), s2.leave))

theorem dottedAsName_proven : DottedAsName := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 31 = r31 from rfl, r31]
  refine ⟨fun hi a b s1 s2 h1 ha h2 h2e => ?_, fun hi s1 h1 => ?_, fun hi s0 h0 h0e => ?_,
    fun hi a b s0 s1 s2 h0 h0e h1 ha h2 h2e => ?_⟩
  · rw [alts_skip (by simp [hi]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    cases hb : truth b <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e, hb,
        Bool.or_false, mkAt, extraLoc, locArgs, ↓reduceIte, Bool.false_eq_true, aliasOf] <;>
      simp [mkAst, nonNull, hb, StateT.pure, StateT.bind, h2e, pure, bind, mkAt, locArgs]
  · rw [alts_skip (by simp [hi]), alts_fail (by rfl) he (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by simp [hi]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · rw [alts_fail (by simp [hi]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    cases hb : truth b <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e, hb,
        Bool.or_false, mkAt, extraLoc, locArgs, ↓reduceIte, Bool.false_eq_true, aliasOf] <;>
      simp [mkAst, nonNull, hb, StateT.pure, StateT.bind, h2e, pure, bind, mkAt, locArgs]

/-- `import_from_as_name` (`Grammar/python.gram:244-247`):
```
    | invalid_import_from_as_name
    | a=NAME b=['as' z=NAME { z }] { _PyAST_alias(
        a->v.Name.id, (b) ? ((expr_ty) b)->v.Name.id : NULL, EXTRA) }
```
As `DottedAsName`, with `NAME` for `dotted_name` and `invalid_import_from_as_name` for
`invalid_dotted_as_name`. -/
def ImportFromAsName : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (q.callInvalidRules = false → ∀ (a b : Ast) (s1 s2 : PS), nameToken q = (a, s1) →
    a ≠ .null → callRule f 298 s1 = (b, s2) → s2.errorIndicator = false →
    callRule (f + 7) 29 p = (aliasOf a b (extraLoc t s2), s2.leave)) ∧
  (q.callInvalidRules = false → ∀ (s1 : PS), nameToken q = (.null, s1) →
    callRule (f + 7) 29 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (q.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 2) 239 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 7) 29 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (q.callInvalidRules = true → ∀ (a b : Ast) (s0 s1 s2 : PS), callRule (f + 2) 239 q = (.null, s0) →
    s0.errorIndicator = false → nameToken { s0 with mark := p.mark } = (a, s1) →
    a ≠ .null → callRule f 298 s1 = (b, s2) → s2.errorIndicator = false →
    callRule (f + 7) 29 p = (aliasOf a b (extraLoc t s2), s2.leave))

theorem importFromAsName_proven : ImportFromAsName := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 29 = r29 from rfl, r29]
  refine ⟨fun hi a b s1 s2 h1 ha h2 h2e => ?_, fun hi s1 h1 => ?_, fun hi s0 h0 h0e => ?_,
    fun hi a b s0 s1 s2 h0 h0e h1 ha h2 h2e => ?_⟩
  · rw [alts_skip (by simp [hi]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) ha, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    cases hb : truth b <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e, hb,
        Bool.or_false, mkAt, extraLoc, locArgs, ↓reduceIte, Bool.false_eq_true, aliasOf] <;>
      simp [mkAst, nonNull, hb, StateT.pure, StateT.bind, h2e, pure, bind, mkAt, locArgs]
  · rw [alts_skip (by simp [hi]), alts_fail (by rfl) he (by
      dsimp only; rw [items_call_null (by rw [call_name, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by simp [hi]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · rw [alts_fail (by simp [hi]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call (by rw [call_name, h1]) ha, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_extra rfl rfl]
    cases hb : truth b <;>
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e, hb,
        Bool.or_false, mkAt, extraLoc, locArgs, ↓reduceIte, Bool.false_eq_true, aliasOf] <;>
      simp [mkAst, nonNull, hb, StateT.pure, StateT.bind, h2e, pure, bind, mkAt, locArgs]

/-! ### `import_from_as_names`, `dotted_as_names` -/

/-- `import_from_as_names: a[asdl_alias_seq*]=','.import_from_as_name+ { a }` and
`dotted_as_names: a[asdl_alias_seq*]=','.dotted_as_name+ { a }` (`Grammar/python.gram:242-250`):
the gather (`_gather_20`, `_gather_23`) is the result; `NULL` with the mark back without it. No
trailing `,` is taken. -/
def AsNames : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a : Ast) (s : PS), callRule f 297 p.enter = (a, s) → a ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 28 p = (a, s.leave)) ∧
  (∀ (s : PS), callRule f 297 p.enter = (.null, s) →
    callRule (f + 5) 28 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (a : Ast) (s : PS), callRule f 300 p.enter = (a, s) → a ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 30 p = (a, s.leave)) ∧
  (∀ (s : PS), callRule f 300 p.enter = (.null, s) →
    callRule (f + 5) 30 p = (.null, { s with mark := p.mark }.leave))

theorem asNames_proven : AsNames := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  refine ⟨fun a s h1 ha h1e => ?_, fun s h1 => ?_, fun a s h1 ha h1e => ?_, fun s h1 => ?_⟩
  · rw [callRule_plain rfl rfl rfl rfl rfl he hl]
    simp only [show ruleOf 28 = r28 from rfl, r28]
    rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [callRule_plain rfl rfl rfl rfl rfl he hl]
    simp only [show ruleOf 28 = r28 from rfl, r28]
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [callRule_plain rfl rfl rfl rfl rfl he hl]
    simp only [show ruleOf 30 = r30 from rfl, r30]
    rw [alts_ok (by rfl) he' (by dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h1e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [callRule_plain rfl rfl rfl rfl rfl he hl]
    simp only [show ruleOf 30 = r30 from rfl, r30]
    rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

end PyLean.PyGrammar.Peg
