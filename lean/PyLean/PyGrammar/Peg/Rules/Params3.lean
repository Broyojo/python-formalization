import PyLean.PyGrammar.Peg.Rules.Params2

/-! `star_etc`, `lambda_star_etc` (`Grammar/python.gram:338-346`, `943-949`) and `parameters`,
`lambda_parameters` (`Grammar/python.gram:318-327`, `925-933`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `star_etc`, `lambda_star_etc` -/

/-- `'*' a=pr b=lp* ...` failing before the optional `kwds` from `X` (`pr` called with fuel
`g + 1`, the loop `lp` with `g`), ending in `s`. -/
def StarPFails (g pr lp : Nat) (X s : PS) : Prop :=
  expectToken 16 X = (.null, s) ∨
  (∃ (c : Token) (s1 : PS), expectToken 16 X = (.tok c, s1) ∧ callRule (g + 1) pr s1 = (.null, s)) ∨
  (∃ (c : Token) (a : Ast) (s1 s2 : PS), expectToken 16 X = (.tok c, s1) ∧
    callRule (g + 1) pr s1 = (a, s2) ∧ a ≠ .null ∧ callRule g lp s2 = (.null, s))

/-- `'*' ',' b=lp+ ...` failing before the optional `kwds` from `X`, ending in `s`. -/
def StarCommaFails (g lp : Nat) (X s : PS) : Prop :=
  expectToken 16 X = (.null, s) ∨
  (∃ (c : Token) (s1 : PS), expectToken 16 X = (.tok c, s1) ∧ expectToken 12 s1 = (.null, s)) ∨
  (∃ (c c' : Token) (s1 s2 : PS), expectToken 16 X = (.tok c, s1) ∧ expectToken 12 s1 = (.tok c', s2) ∧
    callRule g lp s2 = (.null, s))

theorem starPFails_items {g pr lp : Nat} {X s : PS} {rest : List Item} (h : StarPFails g pr lp X s) :
    runItems (g + 4) (.call (.tok 16) :: .call (.rule pr) :: .call (.rule lp) :: rest) #[] false X =
      ((none, false), s) := by
  rcases h with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, a, s1, s2, h1, h2, ha, h3⟩
  · rw [items_call_null (by rw [call_tok, h1])]
  · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_rule, h2])]
  · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
      items_call_null (by rw [call_rule, h3])]

theorem starCommaFails_items {g lp : Nat} {X s : PS} {rest : List Item} (h : StarCommaFails g lp X s) :
    runItems (g + 4) (.call (.tok 16) :: .call (.tok 12) :: .call (.rule lp) :: rest) #[] false X =
      ((none, false), s) := by
  rcases h with h1 | ⟨c, s1, h1, h2⟩ | ⟨c, c', s1, s2, h1, h2, h3⟩
  · rw [items_call_null (by rw [call_tok, h1])]
  · rw [items_call (by rw [call_tok, h1]) (by simp), items_call_null (by rw [call_tok, h2])]
  · rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
      items_call_null (by rw [call_rule, h3])]

theorem invPass_ei {g inv : Nat} {p X : PS} (he : p.errorIndicator = false) (h : InvPass g inv p X) :
    X.errorIndicator = false := by
  rcases h with ⟨-, rfl⟩ | ⟨-, s, -, hs, rfl⟩
  · exact he
  · exact hs

/-- `star_etc` (`Grammar/python.gram:338-346`):
```
    | invalid_star_etc
    | '*' a=param_no_default b=param_maybe_default* c=[kwds] { _PyPegen_star_etc(p, a, b, c) }
    | '*' a=param_no_default_star_annotation b=param_maybe_default* c=[kwds] { _PyPegen_star_etc(p, a, b, c) }
    | '*' ',' b=param_maybe_default+ c=[kwds] { _PyPegen_star_etc(p, NULL, b, c) }
    | a=kwds { _PyPegen_star_etc(p, NULL, NULL, a) }
```
No `EXTRA`. In the second pass `invalid_star_etc` (225) first (its result, or `NULL` on its
error). Then (`InvPass`), each alternative from the start mark: `*` (16), `param_no_default` (45),
`param_maybe_default*` (`_loop0_31`, 308) and the optional `kwds` (44) give the `StarEtc` record
`(vararg, kwonlyargs, kwarg)`; then the same with `param_no_default_star_annotation` (46, `*args:
*Ts`); then `*` `,` (12) `param_maybe_default+` (`_loop1_32`, 309) and the optional `kwds` give
`(NULL, kwonlyargs, kwarg)`; then `kwds` alone `(NULL, NULL, kwarg)`; otherwise `NULL` with the
mark back. -/
def StarEtc : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (p.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 6) 225 p.enter = (v, s) →
    v ≠ .null → callRule (f + 11) 43 p = (v, s.leave)) ∧
  (p.callInvalidRules = true → ∀ (s : PS), callRule (f + 6) 225 p.enter = (.null, s) →
    s.errorIndicator = true → callRule (f + 11) 43 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPass (f + 6) 225 p X →
    (∀ (a b k : Ast) (c : Token) (s1 s2 s3 s4 : PS), expectToken 16 X = (.tok c, s1) →
      callRule (f + 4) 45 s1 = (a, s2) → a ≠ .null → callRule (f + 3) 308 s2 = (b, s3) → b ≠ .null →
      callRule (f + 2) 44 s3 = (k, s4) → s4.errorIndicator = false →
      callRule (f + 11) 43 p = (rec_ .PStarEtc [a, b, k], s4.leave)) ∧
    (∀ (s0 : PS), StarPFails (f + 3) 45 308 X s0 → s0.errorIndicator = false →
      (∀ (a b k : Ast) (c : Token) (s1 s2 s3 s4 : PS), expectToken 16 { s0 with mark := p.mark } = (.tok c, s1) →
        callRule (f + 3) 46 s1 = (a, s2) → a ≠ .null → callRule (f + 2) 308 s2 = (b, s3) → b ≠ .null →
        callRule (f + 1) 44 s3 = (k, s4) → s4.errorIndicator = false →
        callRule (f + 11) 43 p = (rec_ .PStarEtc [a, b, k], s4.leave)) ∧
      (∀ (s0' : PS), StarPFails (f + 2) 46 308 { s0 with mark := p.mark } s0' → s0'.errorIndicator = false →
        (∀ (b k : Ast) (c c' : Token) (s1 s2 s3 s4 : PS),
          expectToken 16 { s0' with mark := p.mark } = (.tok c, s1) → expectToken 12 s1 = (.tok c', s2) →
          callRule (f + 1) 309 s2 = (b, s3) → b ≠ .null → callRule f 44 s3 = (k, s4) →
          s4.errorIndicator = false →
          callRule (f + 11) 43 p = (rec_ .PStarEtc [.null, b, k], s4.leave)) ∧
        (∀ (s0'' : PS), StarCommaFails (f + 1) 309 { s0' with mark := p.mark } s0'' →
          s0''.errorIndicator = false →
          (∀ (k : Ast) (s4 : PS), callRule (f + 2) 44 { s0'' with mark := p.mark } = (k, s4) →
            k ≠ .null → s4.errorIndicator = false →
            callRule (f + 11) 43 p = (rec_ .PStarEtc [.null, .null, k], s4.leave)) ∧
          (∀ (s4 : PS), callRule (f + 2) 44 { s0'' with mark := p.mark } = (.null, s4) →
            callRule (f + 11) 43 p = (.null, { s4 with mark := p.mark }.leave))))))

theorem starEtc_proven : StarEtc := by
  intro f p he hl
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 43 = r43 from rfl, r43]
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 9 = (f + 6) + 3 from rfl, show Alt.mk [.call (.rule 225)] none 1 true false = invAlt 225 from rfl,
      invAlt_ok he hi h1 hv]
    rfl
  · rw [show f + 9 = (f + 6) + 3 from rfl, show Alt.mk [.call (.rule 225)] none 1 true false = invAlt 225 from rfl,
      invAlt_err he hi rfl h1 h1e]
    rfl
  have hXe := invPass_ei he hX
  rw [show f + 9 = (f + 6) + 3 from rfl, show Alt.mk [.call (.rule 225)] none 1 true false = invAlt 225 from rfl,
    invPass_alts he hX]
  refine ⟨fun a b k c s1 s2 s3 s4 h1 h2 ha h3 hb h4 h4e => ?_, fun s0 h0 h0e =>
    ⟨fun a b k c s1 s2 s3 s4 h1 h2 ha h3 hb h4 h4e => ?_, fun s0' h0' h0'e =>
      ⟨fun b k c c' s1 s2 s3 s4 h1 h2 h3 hb h4 h4e => ?_, fun s0'' h0'' h0''e =>
        ⟨fun k s4 h1 hk h1e => ?_, fun s4 h1 => ?_⟩⟩⟩⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 3) h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 3) h0),
      alts_fail (by rfl) (E s0 h0e) (starPFails_items (g := f + 2) h0'),
      alts_ok (by rfl) (E s0' h0'e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 3) h0),
      alts_fail (by rfl) (E s0 h0e) (starPFails_items (g := f + 2) h0'),
      alts_fail (by rfl) (E s0' h0'e) (starCommaFails_items (g := f + 1) h0''),
      alts_ok (by rfl) (E s0'' h0''e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hk, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h1e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 3) h0),
      alts_fail (by rfl) (E s0 h0e) (starPFails_items (g := f + 2) h0'),
      alts_fail (by rfl) (E s0' h0'e) (starCommaFails_items (g := f + 1) h0''),
      alts_fail (by rfl) (E s0'' h0''e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl

/-- `lambda_star_etc` (`Grammar/python.gram:943-949`):
```
    | invalid_lambda_star_etc
    | '*' a=lambda_param_no_default b=lambda_param_maybe_default* c=[lambda_kwds] { _PyPegen_star_etc(p, a, b, c) }
    | '*' ',' b=lambda_param_maybe_default+ c=[lambda_kwds] { _PyPegen_star_etc(p, NULL, b, c) }
    | a=lambda_kwds { _PyPegen_star_etc(p, NULL, NULL, a) }
```
As `star_etc` without the `*args: *Ts` alternative: `invalid_lambda_star_etc` (230),
`lambda_param_no_default` (156), `lambda_param_maybe_default*` (`_loop0_76`, 353), `+`
(`_loop1_77`, 354), `lambda_kwds` (155). -/
def LambdaStarEtc : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  (p.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 5) 230 p.enter = (v, s) →
    v ≠ .null → callRule (f + 10) 154 p = (v, s.leave)) ∧
  (p.callInvalidRules = true → ∀ (s : PS), callRule (f + 5) 230 p.enter = (.null, s) →
    s.errorIndicator = true → callRule (f + 10) 154 p = (.null, { s with mark := p.mark }.leave)) ∧
  (∀ (X : PS), InvPass (f + 5) 230 p X →
    (∀ (a b k : Ast) (c : Token) (s1 s2 s3 s4 : PS), expectToken 16 X = (.tok c, s1) →
      callRule (f + 3) 156 s1 = (a, s2) → a ≠ .null → callRule (f + 2) 353 s2 = (b, s3) → b ≠ .null →
      callRule (f + 1) 155 s3 = (k, s4) → s4.errorIndicator = false →
      callRule (f + 10) 154 p = (rec_ .PStarEtc [a, b, k], s4.leave)) ∧
    (∀ (s0 : PS), StarPFails (f + 2) 156 353 X s0 → s0.errorIndicator = false →
      (∀ (b k : Ast) (c c' : Token) (s1 s2 s3 s4 : PS),
        expectToken 16 { s0 with mark := p.mark } = (.tok c, s1) → expectToken 12 s1 = (.tok c', s2) →
        callRule (f + 1) 354 s2 = (b, s3) → b ≠ .null → callRule f 155 s3 = (k, s4) →
        s4.errorIndicator = false →
        callRule (f + 10) 154 p = (rec_ .PStarEtc [.null, b, k], s4.leave)) ∧
      (∀ (s0' : PS), StarCommaFails (f + 1) 354 { s0 with mark := p.mark } s0' →
        s0'.errorIndicator = false →
        (∀ (k : Ast) (s4 : PS), callRule (f + 2) 155 { s0' with mark := p.mark } = (k, s4) →
          k ≠ .null → s4.errorIndicator = false →
          callRule (f + 10) 154 p = (rec_ .PStarEtc [.null, .null, k], s4.leave)) ∧
        (∀ (s4 : PS), callRule (f + 2) 155 { s0' with mark := p.mark } = (.null, s4) →
          callRule (f + 10) 154 p = (.null, { s4 with mark := p.mark }.leave)))))

theorem lambdaStarEtc_proven : LambdaStarEtc := by
  intro f p he hl
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  simp only [show ruleOf 154 = r154 from rfl, r154]
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_, fun X hX => ?_⟩
  · rw [show f + 8 = (f + 5) + 3 from rfl, show Alt.mk [.call (.rule 230)] none 1 true false = invAlt 230 from rfl,
      invAlt_ok he hi h1 hv]
    rfl
  · rw [show f + 8 = (f + 5) + 3 from rfl, show Alt.mk [.call (.rule 230)] none 1 true false = invAlt 230 from rfl,
      invAlt_err he hi rfl h1 h1e]
    rfl
  have hXe := invPass_ei he hX
  rw [show f + 8 = (f + 5) + 3 from rfl, show Alt.mk [.call (.rule 230)] none 1 true false = invAlt 230 from rfl,
    invPass_alts he hX]
  refine ⟨fun a b k c s1 s2 s3 s4 h1 h2 ha h3 hb h4 h4e => ?_, fun s0 h0 h0e =>
    ⟨fun b k c c' s1 s2 s3 s4 h1 h2 h3 hb h4 h4e => ?_, fun s0' h0' h0'e =>
      ⟨fun k s4 h1 hk h1e => ?_, fun s4 h1 => ?_⟩⟩⟩
  · rw [alts_ok (by rfl) hXe (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_rule, h2]) ha,
        items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 2) h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_tok, h1]) (by simp), items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_opt (by rw [call_rule, h4]) h4e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h4e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 2) h0),
      alts_fail (by rfl) (E s0 h0e) (starCommaFails_items (g := f + 1) h0'),
      alts_ok (by rfl) (E s0' h0'e) (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hk, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [nonNull, h1e, rec_]
  · rw [alts_fail (by rfl) hXe (starPFails_items (g := f + 2) h0),
      alts_fail (by rfl) (E s0 h0e) (starCommaFails_items (g := f + 1) h0'),
      alts_fail (by rfl) (E s0' h0'e) (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_nil]
    rfl

/-! ### `parameters`, `lambda_parameters` -/

/-- The message of `CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", ...)`. -/
def posOnlyMsg : String := "Positional-only parameters are only supported in Python 3.8 and greater"

/-- What a rule function returns (`r`) when its alternative's action is
`CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", v)`, reached in state `s`: with
`feature_version >= 8` the node and `s`; below, `NULL` with `error_indicator` set and the version
error raised. -/
def CVResult (r : Ast × PS) (v : Ast) (s : PS) : Prop :=
  (8 ≤ s.featureVersion → r = (v, s.leave)) ∧
  (s.featureVersion < 8 → r.1 = .null ∧ r.2.errorIndicator = true ∧
    r.2.tok = (raiseError0 "SyntaxError" posOnlyMsg { s with errorIndicator := true }).2.tok)

theorem altResult_cv {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS} {node : AE}
    {v : Ast}
    (h1 : a.action = some (.checkVersion (.int 8) (.str "Positional-only parameters are") node))
    (h2 : a.extra = false) (hn : evalA env {} node s = (v, s)) (hnn : v ≠ .null)
    (he : s.errorIndicator = false) :
    CVResult (((altResult a g env st s).1.getD .null), (altResult a g env st s).2.leave) v s := by
  refine ⟨fun hv => ?_, fun hv => ?_⟩
  · rw [altResult_plain h1 h2]
    dsimp only
    rw [evalA_cv_ok hn hnn (by omega)]
    have : nonNull v = true := by cases v <;> simp_all [nonNull]
    simp [this, he]
  · have hlow := evalA_cv_low (m := "Positional-only parameters are") hn hnn
      (by omega : (s.featureVersion : Int) < 8)
    have hmsg : toString (cpsStr ("Positional-only parameters are".toList.map Char.toNat)) ++
        toString " only supported in Python 3." ++ toString (8 : Int) ++ toString " and greater" =
        posOnlyMsg := by decide +kernel
    rw [hmsg] at hlow
    apply cv_low_result posOnlyMsg
    rw [altResult_plain h1 h2]
    dsimp only
    rw [hlow]

theorem makeArguments_nonNull (a b c d e : Ast) : nonNull (makeArguments a b c d e) = true := by
  simp [makeArguments, mkAst, nonNull]

theorem makeArguments_ne (a b c d e : Ast) : makeArguments a b c d e ≠ .null := by
  simp [makeArguments, mkAst]

/-- `a=snd b=pnd0 c=pwd0` failing from `X`, ending in `s`. -/
def ParA0Fails (f snd pnd0 pwd0 : Nat) (X s : PS) : Prop :=
  callRule (f + 4) snd X = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (f + 4) snd X = (a, s1) ∧ a ≠ .null ∧ callRule (f + 3) pnd0 s1 = (.null, s)) ∨
  (∃ (a b : Ast) (s1 s2 : PS), callRule (f + 4) snd X = (a, s1) ∧ a ≠ .null ∧
    callRule (f + 3) pnd0 s1 = (b, s2) ∧ b ≠ .null ∧ callRule (f + 2) pwd0 s2 = (.null, s))

/-- `a=sub b=pwd0` failing from `X` (`sub` with fuel `g + 1`), ending in `s`. -/
def ParA12Fails (g sub pwd0 : Nat) (X s : PS) : Prop :=
  callRule (g + 1) sub X = (.null, s) ∨
  (∃ (a : Ast) (s1 : PS), callRule (g + 1) sub X = (a, s1) ∧ a ≠ .null ∧ callRule g pwd0 s1 = (.null, s))

theorem parA12_items {g sub pwd0 : Nat} {X s : PS} {rest : List Item}
    (h : ParA12Fails (g + 1) sub pwd0 X s) :
    runItems (g + 4) (.call (.rule sub) :: .call (.rule pwd0) :: rest) #[] false X = ((none, false), s) := by
  rcases h with h1 | ⟨a, s1, h1, ha, h2⟩
  · rw [items_call_null (by rw [call_rule, h1])]
  · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]

/-- `parameters` (`Grammar/python.gram:318-327`) and `lambda_parameters`
(`Grammar/python.gram:925-933`):
```
    | a=slash_no_default b[asdl_arg_seq*]=param_no_default* c=param_with_default* d=[star_etc] {
        CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", _PyPegen_make_arguments(p, a, NULL, b, c, d)) }
    | a=slash_with_default b=param_with_default* c=[star_etc] {
        CHECK_VERSION(arguments_ty, 8, "Positional-only parameters are", _PyPegen_make_arguments(p, NULL, a, NULL, b, c)) }
    | a[asdl_arg_seq*]=param_no_default+ b=param_with_default* c=[star_etc] {
        _PyPegen_make_arguments(p, NULL, NULL, a, b, c) }
    | a=param_with_default+ b=[star_etc] { _PyPegen_make_arguments(p, NULL, NULL, NULL, a, b)}
    | a=star_etc { _PyPegen_make_arguments(p, NULL, NULL, NULL, NULL, a) }
```
(the lambda rule with the lambda sub-rules). No `EXTRA`. Each alternative from the start mark, in
this order: `slash_no_default` (`snd`), `param_no_default*` (`pnd0`), `param_with_default*`
(`pwd0`) and the optional `star_etc` (`se`) give `_PyPegen_make_arguments` with the
positional-only names first, behind `CHECK_VERSION` 8 (`CVResult`); then `slash_with_default`
(`swd`), likewise; then `param_no_default+` (`pnd1`), `param_with_default*`, `[star_etc]`; then
`param_with_default+` (`pwd1`), `[star_etc]`; then `star_etc`; otherwise `NULL` with the mark back. -/
def Parameters (id snd swd pnd0 pwd0 pnd1 pwd1 se : Nat) : Prop := ∀ (f : Nat) (p : PS),
  p.errorIndicator = false → p.level ≠ MAXSTACK →
  (∀ (a b c d : Ast) (s1 s2 s3 s4 : PS), callRule (f + 4) snd p.enter = (a, s1) → a ≠ .null →
    callRule (f + 3) pnd0 s1 = (b, s2) → b ≠ .null → callRule (f + 2) pwd0 s2 = (c, s3) → c ≠ .null →
    callRule (f + 1) se s3 = (d, s4) → s4.errorIndicator = false →
    CVResult (callRule (f + 9) id p) (makeArguments a .null b c d) s4) ∧
  (∀ (s0 : PS), ParA0Fails f snd pnd0 pwd0 p.enter s0 → s0.errorIndicator = false →
    (∀ (a c d : Ast) (s1 s2 s3 : PS), callRule (f + 3) swd { s0 with mark := p.mark } = (a, s1) →
      a ≠ .null → callRule (f + 2) pwd0 s1 = (c, s2) → c ≠ .null → callRule (f + 1) se s2 = (d, s3) →
      s3.errorIndicator = false →
      CVResult (callRule (f + 9) id p) (makeArguments .null a .null c d) s3) ∧
    (∀ (s0' : PS), ParA12Fails (f + 2) swd pwd0 { s0 with mark := p.mark } s0' →
      s0'.errorIndicator = false →
      (∀ (a c d : Ast) (s1 s2 s3 : PS), callRule (f + 2) pnd1 { s0' with mark := p.mark } = (a, s1) →
        a ≠ .null → callRule (f + 1) pwd0 s1 = (c, s2) → c ≠ .null → callRule f se s2 = (d, s3) →
        s3.errorIndicator = false →
        callRule (f + 9) id p = (makeArguments .null .null a c d, s3.leave)) ∧
      (∀ (s0'' : PS), ParA12Fails (f + 1) pnd1 pwd0 { s0' with mark := p.mark } s0'' →
        s0''.errorIndicator = false →
        (∀ (a d : Ast) (s1 s2 : PS), callRule (f + 1) pwd1 { s0'' with mark := p.mark } = (a, s1) →
          a ≠ .null → callRule f se s1 = (d, s2) → s2.errorIndicator = false →
          callRule (f + 9) id p = (makeArguments .null .null .null a d, s2.leave)) ∧
        (∀ (s3 : PS), callRule (f + 1) pwd1 { s0'' with mark := p.mark } = (.null, s3) →
          s3.errorIndicator = false →
          (∀ (d : Ast) (s4 : PS), callRule f se { s3 with mark := p.mark } = (d, s4) → d ≠ .null →
            s4.errorIndicator = false →
            callRule (f + 9) id p = (makeArguments .null .null .null .null d, s4.leave)) ∧
          (∀ (s4 : PS), callRule f se { s3 with mark := p.mark } = (.null, s4) →
            callRule (f + 9) id p = (.null, { s4 with mark := p.mark }.leave))))))

theorem parameters_of {id snd swd pnd0 pwd0 pnd1 pwd1 se : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule snd), .call (.rule pnd0), .call (.rule pwd0), .opt (.rule se)]
        (some (.checkVersion (.int 8) (.str "Positional-only parameters are")
          (.call .make_arguments [.var 0, .null, .var 1, .var 2, .var 3]))) 4 false false,
       Alt.mk [.call (.rule swd), .call (.rule pwd0), .opt (.rule se)]
        (some (.checkVersion (.int 8) (.str "Positional-only parameters are")
          (.call .make_arguments [.null, .var 0, .null, .var 1, .var 2]))) 3 false false,
       Alt.mk [.call (.rule pnd1), .call (.rule pwd0), .opt (.rule se)]
        (some (.call .make_arguments [.null, .null, .var 0, .var 1, .var 2])) 3 false false,
       Alt.mk [.call (.rule pwd1), .opt (.rule se)]
        (some (.call .make_arguments [.null, .null, .null, .var 0, .var 1])) 2 false false,
       Alt.mk [.call (.rule se)]
        (some (.call .make_arguments [.null, .null, .null, .null, .var 0])) 1 false false]) :
    Parameters id snd swd pnd0 pwd0 pnd1 pwd1 se := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  have hA0 : ∀ s0, ParA0Fails f snd pnd0 pwd0 p.enter s0 →
      runItems (f + 6) [.call (.rule snd), .call (.rule pnd0), .call (.rule pwd0), .opt (.rule se)] #[]
        false p.enter = ((none, false), s0) := by
    intro s0 h0
    rcases h0 with h1 | ⟨a, s1, h1, ha, h2⟩ | ⟨a, b, s1, s2, h1, ha, h2, hb, h3⟩
    · rw [items_call_null (by rw [call_rule, h1])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_rule, h2])]
    · rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb,
        items_call_null (by rw [call_rule, h3])]
  refine ⟨fun a b c d s1 s2 s3 s4 h1 ha h2 hb h3 hc h4 h4e => ?_, fun s0 h0 h0e =>
    ⟨fun a c d s1 s2 s3 h1 ha h2 hc h3 h3e => ?_, fun s0' h0' h0'e =>
      ⟨fun a c d s1 s2 s3 h1 ha h2 hc h3 h3e => ?_, fun s0'' h0'' h0''e =>
        ⟨fun a d s1 s2 h1 ha h2 h2e => ?_, fun s3 h3 h3e =>
          ⟨fun d s4 h4 hd h4e => ?_, fun s4 h4 => ?_⟩⟩⟩⟩⟩
  · dsimp only
    rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hb,
        items_call (by rw [call_rule, h3]) hc, items_opt (by rw [call_rule, h4]) h4e, items_nil])]
    exact altResult_cv rfl rfl (by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
      rfl) (makeArguments_ne _ _ _ _ _) h4e
  · dsimp only
    rw [alts_fail (by rfl) he' (hA0 s0 h0), alts_ok (by rfl) (E s0 h0e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hc,
        items_opt (by rw [call_rule, h3]) h3e, items_nil])]
    exact altResult_cv rfl rfl (by
      simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
      rfl) (makeArguments_ne _ _ _ _ _) h3e
  · rw [alts_fail (by rfl) he' (hA0 s0 h0),
      alts_fail (by rfl) (E s0 h0e) (parA12_items (g := f + 1) h0'),
      alts_ok (by rfl) (E s0' h0'e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_rule, h2]) hc,
        items_opt (by rw [call_rule, h3]) h3e, items_nil]), altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [makeArguments_nonNull, h3e]
  · rw [alts_fail (by rfl) he' (hA0 s0 h0),
      alts_fail (by rfl) (E s0 h0e) (parA12_items (g := f + 1) h0'),
      alts_fail (by rfl) (E s0' h0'e) (parA12_items (g := f) h0''),
      alts_ok (by rfl) (E s0'' h0''e) (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_opt (by rw [call_rule, h2]) h2e, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [makeArguments_nonNull, h2e]
  · rw [alts_fail (by rfl) he' (hA0 s0 h0),
      alts_fail (by rfl) (E s0 h0e) (parA12_items (g := f + 1) h0'),
      alts_fail (by rfl) (E s0' h0'e) (parA12_items (g := f) h0''),
      alts_fail (by rfl) (E s0'' h0''e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by dsimp only; rw [items_call (by rw [call_rule, h4]) hd, items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper]
    simp [makeArguments_nonNull, h4e]
  · rw [alts_fail (by rfl) he' (hA0 s0 h0),
      alts_fail (by rfl) (E s0 h0e) (parA12_items (g := f + 1) h0'),
      alts_fail (by rfl) (E s0' h0'e) (parA12_items (g := f) h0''),
      alts_fail (by rfl) (E s0'' h0''e) (by dsimp only; rw [items_call_null (by rw [call_rule, h3])]),
      alts_fail (by rfl) (E s3 h3e) (by dsimp only; rw [items_call_null (by rw [call_rule, h4])]),
      alts_nil]
    rfl

/-- `parameters` (40): `slash_no_default` 41, `slash_with_default` 42, `param_no_default*` 304,
`param_with_default*` 305, `param_no_default+` 306, `param_with_default+` 307, `star_etc` 43. -/
theorem parameters_proven : Parameters 40 41 42 304 305 306 307 43 := parameters_of rfl
/-- `lambda_parameters` (151): 152, 153, 349, 350, 351, 352, `lambda_star_etc` 154. -/
theorem lambdaParameters_proven : Parameters 151 152 153 349 350 351 352 154 := parameters_of rfl

end PyLean.PyGrammar.Peg
