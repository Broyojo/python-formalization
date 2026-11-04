import PyLean.PyGrammar.Peg.Rules.Base2

/-! `import_from_targets`, class and function definitions, `annotation`, `star_annotation` and
`default` (`Grammar/python.gram:237-381`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `import_from_targets` -/

/-- `import_from_targets` (`Grammar/python.gram:237-241`):
```
    | '(' a=import_from_as_names [','] ')' { a }
    | import_from_as_names !','
    | '*' { (asdl_alias_seq*)_PyPegen_singleton_seq(p, CHECK(alias_ty, _PyPegen_alias_for_star(p, EXTRA))) }
    | invalid_import_from_targets
```
* `(names ,?)` gives the names;
* names with no `(`, not followed by `,`, give the names, the negative lookahead consuming
  nothing;
* names followed by `,` (`from x import a,`) fail the second alternative; the third needs `*`, so
  in the first pass the rule gives `NULL`, and in the second `invalid_import_from_targets` decides;
* `*` gives `[alias('*', NULL)]` located at the `*`. -/
def ImportFromTargets : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type = 7 → ∀ (a c : Ast) (tr : Token) (s2 s3 s4 : PS),
    callRule (f + 2) 28 s1 = (a, s2) → a ≠ .null → expectToken 12 s2 = (c, s3) →
    s3.errorIndicator = false → expectToken 8 s3 = (.tok tr, s4) → s4.errorIndicator = false →
    callRule (f + 8) 27 p = (a, s4.leave)) ∧
  (t.type ≠ 7 → ∀ (a : Ast) (s2 s3 : PS),
    callRule (f + 2) 28 q = (a, s2) → a ≠ .null → expectToken 12 s2 = (.null, s3) →
    callRule (f + 8) 27 p = (a, { s3 with mark := s2.mark }.leave)) ∧
  (t.type ≠ 7 → t.type ≠ 16 → ∀ (a : Ast) (tc : Token) (s2 s3 : PS),
    callRule (f + 2) 28 q = (a, s2) → a ≠ .null → expectToken 12 s2 = (.tok tc, s3) →
    s3.errorIndicator = false →
    (s3.callInvalidRules = false →
      callRule (f + 8) 27 p = (.null, { s3 with mark := p.mark }.leave)) ∧
    (s3.callInvalidRules = true → ∀ (v : Ast) (s4 : PS),
      callRule f 241 { s3 with mark := p.mark } = (v, s4) → v = .null →
      callRule (f + 8) 27 p = (.null, { s4 with mark := p.mark }.leave))) ∧
  (t.type = 16 → ∀ (s2 : PS), callRule (f + 2) 28 q = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 8) 27 p =
      (.seq [mkAt .alias_ [.ident [42], .null] (extraLoc t { s2 with mark := p.mark + 1 })],
        { s2 with mark := p.mark + 1 }.leave))

theorem importFromTargets_proven : ImportFromTargets := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 27 = r27 from rfl, r27]
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have tok_ok : ∀ g ty, (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ g ty, (q.tokenAt p.mark).type ≠ ty → runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  refine ⟨fun ht a c tr s2 s3 s4 h2 ha h3 h3e h4 h4e => ?_, fun ht a s2 s3 h2 ha h3 => ?_,
    fun ht ht' a tc s2 s3 h2 ha h3 h3e => ⟨fun hinv => ?_, fun hinv v s4 h4 hv => ?_⟩,
    fun ht s2 h2 h2e => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_opt (by rw [call_tok, h3]) h3e, items_call (by rw [call_tok, h4]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have ha' : nonNull a = true := by cases a <;> simp_all [nonNull]
    simp [ha', h4e]
  · rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ ht)), hq,
      alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) ha, items_look (b := false) (by rw [call_tok, h3]) rfl, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · have g3 : TokGrows q s3 := (tg_call h2).trans (tg_expect h3)
    have e16 : runCall (f + 2) (.tok 16) { s3 with mark := p.mark } = (.null, { s3 with mark := p.mark }) := by
      rw [call_tok, expect_again g3 hlt, ite_f ht']
    rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ ht)), hq,
      alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) ha, items_look_fail (b := false) (by rw [call_tok, h3]) rfl]),
      alts_fail (by rfl) (E s3 h3e) (items_call_null e16), alts_skip (by simp [hinv]), alts_nil]
    rfl
  · subst hv
    have g3 : TokGrows q s3 := (tg_call h2).trans (tg_expect h3)
    have e16 : runCall (f + 2) (.tok 16) { s3 with mark := p.mark } = (.null, { s3 with mark := p.mark }) := by
      rw [call_tok, expect_again g3 hlt, ite_f ht']
    rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ ht)), hq,
      alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h2]) ha, items_look_fail (b := false) (by rw [call_tok, h3]) rfl]),
      alts_fail (by rfl) (E s3 h3e) (items_call_null e16),
      alts_fail (by simp [hinv]) (E s3 h3e) (by dsimp only; rw [items_call_null (by rw [call_rule, h4])]),
      alts_nil]
    rfl
  · have g2 : TokGrows q s2 := tg_call h2
    have e16 : runCall (f + 2) (.tok 16) { s2 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s2 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g2 hlt, ite_t ht]
    rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by dsimp only; rw [items_call e16 (by simp), items_nil]),
      altResult_extra rfl rfl]
    have hn : evalA ((#[] : Array Ast).push (.tok (q.tokenAt p.mark)))
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset)
          (lastNonWhitespaceToken { s2 with mark := p.mark + 1 }))
        (.call .singleton_seq [(.check (.call .alias_for_star [.extra0, .extra1, .extra2, .extra3]))])
        { s2 with mark := p.mark + 1 } =
        (.seq [mkAt .alias_ [.ident [42], .null] (extraLoc (q.tokenAt p.mark) { s2 with mark := p.mark + 1 })],
          { s2 with mark := p.mark + 1 }) := by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, callHelper,
        mkAt, extraLoc, locArgs]
      rfl
    rw [hn]
    simp [nonNull, h2e]

/-! ### `class_def`, `function_def` -/

/-- `class_def` (`Grammar/python.gram:276-278`):
```
    | a=decorators b=class_def_raw { _PyPegen_class_def_decorators(p, a, b) }
    | class_def_raw
```
No `EXTRA`. With decorators, `_PyPegen_class_def_decorators` rebuilds the `ClassDef` with the
decorator list and keeps every other field and the location of the `class` statement, so a
decorated class starts at `class`, not at `@`. Without decorators, `class_def_raw`'s result; with
decorators and no class after them (`@d` then `def`), both alternatives fail. -/
def ClassDef : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (d n ba kw b x tp : Ast) (l : Option Loc) (s1 s2 : PS),
    callRule (f + 1) 34 p.enter = (d, s1) → d ≠ .null →
    callRule f 36 s1 = (.node .ClassDef [n, ba, kw, b, x, tp] l, s2) → s2.errorIndicator = false →
    callRule (f + 6) 35 p = (.node .ClassDef [n, ba, kw, b, d, tp] l, s2.leave)) ∧
  (∀ (c : Ast) (s1 s2 : PS), callRule (f + 1) 34 p.enter = (.null, s1) → s1.errorIndicator = false →
    callRule f 36 { s1 with mark := p.mark } = (c, s2) → c ≠ .null →
    callRule (f + 6) 35 p = (c, s2.leave)) ∧
  (∀ (d : Ast) (s1 s2 s3 : PS),
    callRule (f + 1) 34 p.enter = (d, s1) → d ≠ .null → callRule f 36 s1 = (.null, s2) →
    s2.errorIndicator = false → callRule f 36 { s2 with mark := p.mark } = (.null, s3) →
    callRule (f + 6) 35 p = (.null, { s3 with mark := p.mark }.leave))

theorem classDef_proven : ClassDef := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 35 = r35 from rfl, r35]
  refine ⟨fun d n ba kw b x tp l s1 s2 h1 hd h2 h2e => ?_, fun c s1 s2 h1 h1e h2 hc => ?_,
    fun d s1 s2 s3 h1 hd h2 h2e h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hd, items_call (by rw [call_rule, h2]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h2e, StateT.pure, pure]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s1 h1e) (by dsimp only; rw [items_call (by rw [call_rule, h2]) hc, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hd, items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_nil]
    rfl

/-- `function_def` (`Grammar/python.gram:291-293`):
```
    | d=decorators f=function_def_raw { _PyPegen_function_def_decorators(p, d, f) }
    | function_def_raw
```
As `class_def`: `_PyPegen_function_def_decorators` (`Parser/action_helpers.c:739-765`) rebuilds the
`FunctionDef` or `AsyncFunctionDef`, whichever it was, with the decorators and every other field,
location included, unchanged. -/
def FunctionDef : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (k : Ctor) (d n ar b x r tc tp : Ast) (l : Option Loc) (s1 s2 : PS),
    callRule (f + 1) 34 p.enter = (d, s1) → d ≠ .null →
    callRule f 38 s1 = (.node k [n, ar, b, x, r, tc, tp] l, s2) → s2.errorIndicator = false →
    callRule (f + 6) 37 p = (.node k [n, ar, b, d, r, tc, tp] l, s2.leave)) ∧
  (∀ (c : Ast) (s1 s2 : PS), callRule (f + 1) 34 p.enter = (.null, s1) → s1.errorIndicator = false →
    callRule f 38 { s1 with mark := p.mark } = (c, s2) → c ≠ .null →
    callRule (f + 6) 37 p = (c, s2.leave)) ∧
  (∀ (d : Ast) (s1 s2 s3 : PS),
    callRule (f + 1) 34 p.enter = (d, s1) → d ≠ .null → callRule f 38 s1 = (.null, s2) →
    s2.errorIndicator = false → callRule f 38 { s2 with mark := p.mark } = (.null, s3) →
    callRule (f + 6) 37 p = (.null, { s3 with mark := p.mark }.leave))

theorem functionDef_proven : FunctionDef := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 37 = r37 from rfl, r37]
  refine ⟨fun k d n ar b x r tc tp l s1 s2 h1 hd h2 h2e => ?_, fun c s1 s2 h1 h1e h2 hc => ?_,
    fun d s1 s2 s3 h1 hd h2 h2e h3 => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hd, items_call (by rw [call_rule, h2]) (by simp),
        items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h2e, StateT.pure, pure]
  · rw [alts_fail (by rfl) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s1 h1e) (by dsimp only; rw [items_call (by rw [call_rule, h2]) hc, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hd, items_call_null (by rw [call_rule, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_nil]
    rfl

/-! ### `class_def_raw` -/

/-- `class_def_raw` (`Grammar/python.gram:280-286`):
```
    | invalid_class_def_raw
    | 'class' a=NAME t=[type_params] b=['(' z=[arguments] ')' { z }] ':' c=block {
        _PyAST_ClassDef(a->v.Name.id,
                     (b) ? ((expr_ty) b)->v.Call.args : NULL,
                     (b) ? ((expr_ty) b)->v.Call.keywords : NULL,
                     c, NULL, t, EXTRA) }
```
`['(' z=[arguments] ')']` is `_tmp_25` (rule 302). First pass: at any token but `class`, `NULL`;
`class n[tp](args): c` gives `ClassDef(n.id, args.args, args.keywords, c, [], tp)`, the bases and
keywords `NULL` (empty) when there is no argument list or it is `()`. Second pass: an error from
`invalid_class_def_raw` ends the rule; its `NULL` leads to the plain alternative. -/
def ClassDefRaw : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  let res (n tp z c : Ast) (s : PS) : Ast × PS :=
    (mkAt .ClassDef [fieldOf n "id", if truth z then fieldOf z "args" else .null,
      if truth z then fieldOf z "keywords" else .null, c, .null, tp] (extraLoc t s), s.leave)
  (t.type ≠ 719 → p.callInvalidRules = false → callRule (f + 11) 36 p = (.null, q.leave)) ∧
  (t.type = 719 → p.callInvalidRules = false →
    ∀ (n tp z c : Ast) (tc : Token) (s2 s3 s4 s5 s6 : PS),
    nameToken s1 = (n, s2) → n ≠ .null → callRule (f + 3) 102 s2 = (tp, s3) →
    s3.errorIndicator = false → callRule (f + 2) 302 s3 = (z, s4) → s4.errorIndicator = false →
    expectToken 11 s4 = (.tok tc, s5) → callRule f 33 s5 = (c, s6) → c ≠ .null →
    s6.errorIndicator = false → callRule (f + 11) 36 p = res n tp z c s6) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 6) 262 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 11) 36 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 719 → p.callInvalidRules = true →
    ∀ (n tp z c : Ast) (tc : Token) (s0 s2 s3 s4 s5 s6 : PS),
    callRule (f + 6) 262 q = (.null, s0) → s0.errorIndicator = false →
    nameToken { s0 with mark := p.mark + 1 } = (n, s2) → n ≠ .null →
    callRule (f + 3) 102 s2 = (tp, s3) →
    s3.errorIndicator = false → callRule (f + 2) 302 s3 = (z, s4) → s4.errorIndicator = false →
    expectToken 11 s4 = (.tok tc, s5) → callRule f 33 s5 = (c, s6) → c ≠ .null →
    s6.errorIndicator = false → callRule (f + 11) 36 p = res n tp z c s6)

theorem classDefRaw_proven : ClassDefRaw := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 36 = r36 from rfl, r36]
  have act : ∀ (t0 : Token) (n tp z tc c : Ast) (ex : Extra) (s : PS),
      evalA (((((((#[] : Array Ast).push (.tok t0)).push n).push tp).push z).push tc).push c) ex
        (.mk .ClassDef [(.field (.var 1) "id"), (.ite (.var 3) (.field (.var 3) "args") .null),
          (.ite (.var 3) (.field (.var 3) "keywords") .null), (.var 5), .null, (.var 2), .extra0,
          .extra1, .extra2, .extra3]) s =
      (mkAst .ClassDef [fieldOf n "id", if truth z then fieldOf z "args" else .null,
        if truth z then fieldOf z "keywords" else .null, c, .null, tp, .int ex.startLine,
        .int ex.startCol, .int ex.endLine, .int ex.endCol], s) := by
    intro t0 n tp z tc c ex s
    have e3 : (((((((#[] : Array Ast).push (.tok t0)).push n).push tp).push z).push tc).push c).getD 3
        .null = z := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, e3]
    cases truth z <;> rfl
  refine ⟨fun ht hinv => ?_, fun ht hinv n tp z c tc s2 s3 s4 s5 s6 h2 hn h3 h3e h4 h4e h5 h6 hc h6e => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv n tp z c tc s0 s2 s3 s4 s5 s6 h0 h0e h2 hn h3 h3e h4 h4e h5 h6 hc h6e => ?_⟩
  · have e1 : runCall (f + 6) (.tok 719) q = (.null, q) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
    rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null e1), hq, alts_nil]
    rfl
  · have e1 : runCall (f + 6) (.tok 719) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) := by
      rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
    rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_name, h2]) hn,
        items_opt (by rw [call_rule, h3]) h3e, items_opt (by rw [call_rule, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_rule, h6]) hc,
        items_nil]), altResult_extra rfl rfl]
    rw [act]
    simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, nonNull, h6e]
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    have e1 : runCall (f + 6) (.tok 719) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_name, h2]) hn,
        items_opt (by rw [call_rule, h3]) h3e, items_opt (by rw [call_rule, h4]) h4e,
        items_call (by rw [call_tok, h5]) (by simp), items_call (by rw [call_rule, h6]) hc,
        items_nil]), altResult_extra rfl rfl]
    rw [act]
    simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, nonNull, h6e]

/-! ### `function_def_raw` -/

/-- `function_def_raw` (`Grammar/python.gram:295-309`):
```
    | invalid_def_raw
    | 'def' n=NAME t=[type_params] '(' params=[params] ')' a=['->' z=expression { z }] ':' tc=[func_type_comment] b=block {
        _PyAST_FunctionDef(n->v.Name.id,
                        (params) ? params : CHECK(arguments_ty, _PyPegen_empty_arguments(p)),
                        b, NULL, a, NEW_TYPE_COMMENT(p, tc), t, EXTRA) }
    | 'async' 'def' n=NAME t=[type_params] '(' params=[params] ')' a=['->' z=expression { z }] ':' tc=[func_type_comment] b=block {
        CHECK_VERSION(
            stmt_ty,
            5,
            "Async functions are",
            _PyAST_AsyncFunctionDef(n->v.Name.id,
                            (params) ? params : CHECK(arguments_ty, _PyPegen_empty_arguments(p)),
                            b, NULL, a, NEW_TYPE_COMMENT(p, tc), t, EXTRA)
        ) }
```
`['->' expression]` is `_tmp_26` (rule 303). First pass: at any token but `def` or `async`,
`NULL`; `def n[tp](params) -> r: tc b` gives `FunctionDef(n.id, params, b, [], r, tc, tp)`, with
empty `arguments` (`_PyPegen_empty_arguments`) for `()`; `async def ...` gives
`AsyncFunctionDef(...)` when `feature_version` is at least 5, and otherwise `NULL` with "Async
functions are only supported in Python 3.5 and greater". Second pass: an error from
`invalid_def_raw` ends the rule; its `NULL` leads to the `def` alternative. -/
def FunctionDefRaw : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  let args (ar : Ast) : Ast := if truth ar then ar else makeArguments .null .null .null .null .null
  (t.type ≠ 717 → t.type ≠ 716 → p.callInvalidRules = false →
    callRule (f + 17) 38 p = (.null, q.leave)) ∧
  (t.type = 717 → p.callInvalidRules = false →
    ∀ (n tp ar r tc b : Ast) (to tr tk : Token) (s2 s3 s4 s5 s6 s7 s8 s9 s10 : PS),
    nameToken s1 = (n, s2) → n ≠ .null → callRule (f + 9) 102 s2 = (tp, s3) →
    s3.errorIndicator = false → expectToken 7 s3 = (.tok to, s4) →
    callRule (f + 7) 39 s4 = (ar, s5) → s5.errorIndicator = false →
    expectToken 8 s5 = (.tok tr, s6) → callRule (f + 5) 303 s6 = (r, s7) →
    s7.errorIndicator = false → expectToken 11 s7 = (.tok tk, s8) →
    callRule (f + 3) 207 s8 = (tc, s9) → s9.errorIndicator = false →
    callRule (f + 2) 33 s9 = (b, s10) → b ≠ .null → s10.errorIndicator = false →
    callRule (f + 17) 38 p = (mkAt .FunctionDef [fieldOf n "id", args ar, b, .null, r,
      typeCommentOf tc, tp] (extraLoc t s10), s10.leave)) ∧
  (t.type = 716 → p.callInvalidRules = false →
    ∀ (n tp ar r tc b : Ast) (td to tr tk : Token) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : PS),
    expectToken 717 s1 = (.tok td, s2) →
    nameToken s2 = (n, s3) → n ≠ .null → callRule (f + 7) 102 s3 = (tp, s4) →
    s4.errorIndicator = false → expectToken 7 s4 = (.tok to, s5) →
    callRule (f + 5) 39 s5 = (ar, s6) → s6.errorIndicator = false →
    expectToken 8 s6 = (.tok tr, s7) → callRule (f + 3) 303 s7 = (r, s8) →
    s8.errorIndicator = false → expectToken 11 s8 = (.tok tk, s9) →
    callRule (f + 1) 207 s9 = (tc, s10) → s10.errorIndicator = false →
    callRule f 33 s10 = (b, s11) → b ≠ .null → s11.errorIndicator = false →
    (5 ≤ s11.featureVersion → callRule (f + 17) 38 p = (mkAt .AsyncFunctionDef
      [fieldOf n "id", args ar, b, .null, r, typeCommentOf tc, tp] (extraLoc t s11), s11.leave)) ∧
    (s11.featureVersion < 5 →
      (callRule (f + 17) 38 p).1 = .null ∧ (callRule (f + 17) 38 p).2.errorIndicator = true ∧
      (callRule (f + 17) 38 p).2.tok = (raiseError0 "SyntaxError"
        "Async functions are only supported in Python 3.5 and greater"
        { s11 with errorIndicator := true }).2.tok)) ∧
  (p.callInvalidRules = true → ∀ (s0 : PS), callRule (f + 12) 261 q = (.null, s0) →
    s0.errorIndicator = true → callRule (f + 17) 38 p = (.null, { s0 with mark := p.mark }.leave)) ∧
  (t.type = 717 → p.callInvalidRules = true →
    ∀ (n tp ar r tc b : Ast) (to tr tk : Token) (s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 : PS),
    callRule (f + 12) 261 q = (.null, s0) → s0.errorIndicator = false →
    nameToken { s0 with mark := p.mark + 1 } = (n, s2) → n ≠ .null →
    callRule (f + 9) 102 s2 = (tp, s3) →
    s3.errorIndicator = false → expectToken 7 s3 = (.tok to, s4) →
    callRule (f + 7) 39 s4 = (ar, s5) → s5.errorIndicator = false →
    expectToken 8 s5 = (.tok tr, s6) → callRule (f + 5) 303 s6 = (r, s7) →
    s7.errorIndicator = false → expectToken 11 s7 = (.tok tk, s8) →
    callRule (f + 3) 207 s8 = (tc, s9) → s9.errorIndicator = false →
    callRule (f + 2) 33 s9 = (b, s10) → b ≠ .null → s10.errorIndicator = false →
    callRule (f + 17) 38 p = (mkAt .FunctionDef [fieldOf n "id", args ar, b, .null, r,
      typeCommentOf tc, tp] (extraLoc t s10), s10.leave))

theorem functionDefRaw_proven : FunctionDefRaw := by
  intro f p q h
  obtain ⟨he, -, hci, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 38 = r38 from rfl, r38]
  have tok_ok : ∀ g ty, (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ g ty, (q.tokenAt p.mark).type ≠ ty → runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  have act : ∀ (t0 : Token) (n tp to ar tr r tk tc b : Ast) (ex : Extra) (s : PS),
      evalA (((((((((((#[] : Array Ast).push (.tok t0)).push n).push tp).push to).push ar).push
          tr).push r).push tk).push tc).push b) ex
        (.mk .FunctionDef [(.field (.var 1) "id"), (.ite (.var 4) (.var 4)
          (.check (.call .empty_arguments []))), (.var 9), .null, (.var 6),
          (.call .NEW_TYPE_COMMENT [(.var 8)]), (.var 2), .extra0, .extra1, .extra2, .extra3]) s =
      (mkAst .FunctionDef [fieldOf n "id",
        (if truth ar then ar else makeArguments .null .null .null .null .null), b, .null, r,
        typeCommentOf tc, tp, .int ex.startLine, .int ex.startCol, .int ex.endLine,
        .int ex.endCol], s) := by
    intro t0 n tp to ar tr r tk tc b ex s
    have e4 : (((((((((((#[] : Array Ast).push (.tok t0)).push n).push tp).push to).push ar).push
        tr).push r).push tk).push tc).push b).getD 4 .null = ar := rfl
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, e4]
    cases truth ar <;> rfl
  refine ⟨fun h1 h2 hinv => ?_,
    fun ht hinv n tp ar r tc b to tr tk s2 s3 s4 s5 s6 s7 s8 s9 s10 h2 hn h3 h3e h4 h5 h5e h6 h7 h7e
      h8 h9 h9e h10 hb h10e => ?_,
    fun ht hinv n tp ar r tc b td to tr tk s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h1 h2 hn h3 h3e h4 h5 h5e
      h6 h7 h7e h8 h9 h9e h10 hb h10e => ?_,
    fun hinv s0 h0 h0e => ?_,
    fun ht hinv n tp ar r tc b to tr tk s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 h0 h0e h2 hn h3 h3e h4 h5 h5e
      h6 h7 h7e h8 h9 h9e h10 hb h10e => ?_⟩
  · rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ h1)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h2)), hq, alts_nil]
    rfl
  · rw [alts_skip (by simp [hci, hinv]), alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_name, h2]) hn,
        items_opt (by rw [call_rule, h3]) h3e, items_call (by rw [call_tok, h4]) (by simp),
        items_opt (by rw [call_rule, h5]) h5e, items_call (by rw [call_tok, h6]) (by simp),
        items_opt (by rw [call_rule, h7]) h7e, items_call (by rw [call_tok, h8]) (by simp),
        items_opt (by rw [call_rule, h9]) h9e, items_call (by rw [call_rule, h10]) hb, items_nil]),
      altResult_extra rfl rfl]
    rw [act]
    simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, nonNull, h10e]
  · rw [alts_skip (by simp [hci, hinv]), alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))),
      hq, alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_tok, h1]) (by simp),
        items_call (by rw [call_name, h2]) hn,
        items_opt (by rw [call_rule, h3]) h3e, items_call (by rw [call_tok, h4]) (by simp),
        items_opt (by rw [call_rule, h5]) h5e, items_call (by rw [call_tok, h6]) (by simp),
        items_opt (by rw [call_rule, h7]) h7e, items_call (by rw [call_tok, h8]) (by simp),
        items_opt (by rw [call_rule, h9]) h9e, items_call (by rw [call_rule, h10]) hb, items_nil]),
      altResult_extra rfl rfl]
    have hn' : evalA ((((((((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok td)).push
          n).push tp).push (.tok to)).push ar).push (.tok tr)).push r).push (.tok tk)).push tc).push b)
        (mkExtra ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) (lastNonWhitespaceToken s11))
        (.mk .AsyncFunctionDef [(.field (.var 2) "id"), (.ite (.var 5) (.var 5)
          (.check (.call .empty_arguments []))), (.var 10), .null, (.var 7),
          (.call .NEW_TYPE_COMMENT [(.var 9)]), (.var 3), .extra0, .extra1, .extra2, .extra3]) s11 =
        (mkAt .AsyncFunctionDef [fieldOf n "id",
          (if truth ar then ar else makeArguments .null .null .null .null .null), b, .null, r,
          typeCommentOf tc, tp] (extraLoc (q.tokenAt p.mark) s11), s11) := by
      have e5 : ((((((((((((#[] : Array Ast).push (.tok (q.tokenAt p.mark))).push (.tok td)).push
          n).push tp).push (.tok to)).push ar).push (.tok tr)).push r).push (.tok tk)).push tc).push
          b).getD 5 .null = ar := rfl
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, mkAt,
        extraLoc, locArgs, callHelper, e5]
      cases truth ar <;> rfl
    have hnn : mkAt .AsyncFunctionDef [fieldOf n "id",
        (if truth ar then ar else makeArguments .null .null .null .null .null), b, .null, r,
        typeCommentOf tc, tp] (extraLoc (q.tokenAt p.mark) s11) ≠ .null := by
      simp [mkAt, mkAst]
    refine ⟨fun hv => ?_, fun hv => ?_⟩
    · rw [evalA_cv_ok (v := 5) (m := "Async functions are") hn' hnn (by omega)]
      simp [mkAst, mkAt, nonNull, h10e]
    · rw [evalA_cv_low (v := 5) (m := "Async functions are") hn' hnn (by omega)]
      have hmsg : toString (cpsStr ("Async functions are".toList.map Char.toNat)) ++
          toString " only supported in Python 3." ++ toString (5 : Int) ++ toString " and greater" =
          "Async functions are only supported in Python 3.5 and greater" := by decide +kernel
      simp only [hmsg]
      exact cv_low_result _ rfl
  · rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_err (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = true from h0e)]
    rfl
  · have g0 : TokGrows q s0 := tg_call h0
    have e1 : runCall (f + 12) (.tok 717) { s0 with mark := p.mark } =
        (.tok (q.tokenAt p.mark), { s0 with mark := p.mark + 1 }) := by
      rw [call_tok, expect_again g0 hlt, ite_t ht]
    rw [alts_fail (by simp [hci, hinv]) he (by dsimp only; rw [items_call_null (by rw [call_rule, h0])]),
      alts_ok (by rfl) (show ({ s0 with mark := p.mark } : PS).errorIndicator = false from h0e) (by
      dsimp only
      rw [items_call e1 (by simp), items_call (by rw [call_name, h2]) hn,
        items_opt (by rw [call_rule, h3]) h3e, items_call (by rw [call_tok, h4]) (by simp),
        items_opt (by rw [call_rule, h5]) h5e, items_call (by rw [call_tok, h6]) (by simp),
        items_opt (by rw [call_rule, h7]) h7e, items_call (by rw [call_tok, h8]) (by simp),
        items_opt (by rw [call_rule, h9]) h9e, items_call (by rw [call_rule, h10]) hb, items_nil]),
      altResult_extra rfl rfl]
    rw [act]
    simp [mkAst, mkAt, extraLoc, locArgs, mkExtra, nonNull, h10e]

/-! ### `annotation`, `star_annotation`, `default` -/

/-- `annotation: ':' a=expression { a }`, `star_annotation: ':' a=star_expression { a }` and
`default: '=' a=expression { a } | invalid_default` (`Grammar/python.gram:379-381`), no `EXTRA`:
at the separator, the expression after it (`expression` for `annotation` and `default`,
`star_expression` for `star_annotation`, so that only `*args: *Ts` takes a starred annotation);
at any other token, `NULL` with the mark back. `default`, second pass: with no expression after
`=`, `invalid_default` runs from the start mark and decides. -/
def AnnotationDefault : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type = 11 → ∀ (a : Ast) (s2 : PS), callRule f 109 s1 = (a, s2) → a ≠ .null →
    s2.errorIndicator = false → callRule (f + 6) 51 p = (a, s2.leave)) ∧
  (t.type ≠ 11 → callRule (f + 6) 51 p = (.null, q.leave)) ∧
  (t.type = 11 → ∀ (a : Ast) (s2 : PS), callRule f 113 s1 = (a, s2) → a ≠ .null →
    s2.errorIndicator = false → callRule (f + 6) 52 p = (a, s2.leave)) ∧
  (t.type ≠ 11 → callRule (f + 6) 52 p = (.null, q.leave)) ∧
  (t.type = 22 → ∀ (a : Ast) (s2 : PS), callRule f 109 s1 = (a, s2) → a ≠ .null →
    s2.errorIndicator = false → callRule (f + 6) 53 p = (a, s2.leave)) ∧
  (t.type ≠ 22 → p.callInvalidRules = false → callRule (f + 6) 53 p = (.null, q.leave)) ∧
  (t.type = 22 → p.callInvalidRules = false → ∀ (s2 : PS), callRule f 109 s1 = (.null, s2) →
    s2.errorIndicator = false → s2.callInvalidRules = false →
    callRule (f + 6) 53 p = (.null, { s2 with mark := p.mark }.leave)) ∧
  (t.type = 22 → ∀ (v : Ast) (s2 s3 : PS), callRule f 109 s1 = (.null, s2) →
    s2.errorIndicator = false → s2.callInvalidRules = true →
    callRule f 224 { s2 with mark := p.mark } = (v, s3) → v = .null →
    callRule (f + 6) 53 p = (.null, { s3 with mark := p.mark }.leave))

theorem annotationDefault_proven : AnnotationDefault := by
  intro f p q h
  obtain ⟨-, -, hci, -, hm, -, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hci' : p.enter.callInvalidRules = p.callInvalidRules := rfl
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  have tok_ok : ∀ g ty, (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) p.enter = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expect_entered h, ite_t ht]
  have tok_no : ∀ g ty, (q.tokenAt p.mark).type ≠ ty → runCall (g + 1) (.tok ty) p.enter = (.null, q) :=
    fun g ty ht => by rw [call_tok, expect_entered h, ite_f ht]
  refine ⟨fun ht a s2 h2 ha h2e => ?_, fun ht => ?_, fun ht a s2 h2 ha h2e => ?_, fun ht => ?_,
    fun ht a s2 h2 ha h2e => ?_, fun ht hinv => ?_, fun ht hinv s2 h2 h2e h2i => ?_,
    fun ht v s2 s3 h2 h2e h2i h3 hv => ?_⟩
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 51 = r51 from rfl, r51]
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h2]) ha, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have ha' : nonNull a = true := by cases a <;> simp_all [nonNull]
    simp [ha', h2e]
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 51 = r51 from rfl, r51]
    rw [alts_fail (by rfl) he' (items_call_null (tok_no _ _ ht)), hq, alts_nil]
    rfl
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 52 = r52 from rfl, r52]
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h2]) ha, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have ha' : nonNull a = true := by cases a <;> simp_all [nonNull]
    simp [ha', h2e]
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 52 = r52 from rfl, r52]
    rw [alts_fail (by rfl) he' (items_call_null (tok_no _ _ ht)), hq, alts_nil]
    rfl
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 53 = r53 from rfl, r53]
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h2]) ha, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure]
    have ha' : nonNull a = true := by cases a <;> simp_all [nonNull]
    simp [ha', h2e]
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 53 = r53 from rfl, r53]
    rw [alts_fail (by rfl) he' (items_call_null (tok_no _ _ ht)), hq,
      alts_skip (by simp [show q.callInvalidRules = p.callInvalidRules from hci, hinv]), alts_nil]
    rfl
  · rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 53 = r53 from rfl, r53]
    rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call (tok_ok _ _ ht) (by simp), items_call_null (by rw [call_rule, h2])]),
      alts_skip (by simp [h2i]), alts_nil]
    rfl
  · subst hv
    rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
    simp only [show ruleOf 53 = r53 from rfl, r53]
    rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call (tok_ok _ _ ht) (by simp), items_call_null (by rw [call_rule, h2])]),
      alts_fail (by simp [h2i]) (E s2 h2e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_nil]
    rfl

end PyLean.PyGrammar.Peg
