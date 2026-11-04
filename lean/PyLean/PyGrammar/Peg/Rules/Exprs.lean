import PyLean.PyGrammar.Peg.Rules.Base

/-! Expression rules of `Grammar/python.gram`, rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### `factor` -/

/-- `factor (memo)` (`Grammar/python.gram:856-860`):
```
    | '+' a=factor { _PyAST_UnaryOp(UAdd, a, EXTRA) }
    | '-' a=factor { _PyAST_UnaryOp(USub, a, EXTRA) }
    | '~' a=factor { _PyAST_UnaryOp(Invert, a, EXTRA) }
    | power
```
At a position not yet memoized for `factor`: at `+`, `-`, `~` the operand is `factor` again, one
token on, and the result is the unary node over it; at any other token the result is `power`'s.
Either way the result is memoized at the starting mark. So a prefix operator binds looser than
`**` (`-x ** y` is `-(x ** y)`, because `power` parses `x ** y`) and prefix operators nest. -/
def Factor : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 141) = none →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  let un (c : Ctor) (b : Ast) (s : PS) : Ast × PS :=
    let v := mkAt .UnaryOp [opNode c, b] (extraLoc t s)
    (v, (insertMemo p.mark (1000 + 141) v s).2.leave)
  (t.type = 14 → ∀ (b : Ast) (s2 : PS), callRule (f + 3) 141 s1 = (b, s2) → b ≠ .null →
    s2.errorIndicator = false → callRule (f + 9) 141 p = un .UAdd b s2) ∧
  (t.type = 15 → ∀ (b : Ast) (s2 : PS), callRule (f + 2) 141 s1 = (b, s2) → b ≠ .null →
    s2.errorIndicator = false → callRule (f + 9) 141 p = un .USub b s2) ∧
  (t.type = 31 → ∀ (b : Ast) (s2 : PS), callRule (f + 1) 141 s1 = (b, s2) → b ≠ .null →
    s2.errorIndicator = false → callRule (f + 9) 141 p = un .Invert b s2) ∧
  (t.type ≠ 14 → t.type ≠ 15 → t.type ≠ 31 → ∀ (v : Ast) (s : PS),
    callRule (f + 1) 142 q = (v, s) → v ≠ .null →
    callRule (f + 9) 141 p = (v, (insertMemo p.mark (1000 + 141) v s).2.leave))

theorem factor_proven : Factor := by
  intro f p q h hn
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_memo_extra rfl rfl rfl rfl rfl h hn]
  simp only [show ruleOf 141 = r141 from rfl, r141]
  have tok_ok : ∀ (g ty : Nat), (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ (g ty : Nat), (q.tokenAt p.mark).type ≠ ty →
      runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  have fin : ∀ (c : Ctor) (b : Ast) (s2 : PS), s2.errorIndicator = false →
      memoDone p.mark 141 (altResult
        { items := [.call (.tok 0), .call (.rule 141)],
          action := some (.mk .UnaryOp [.ctor c, .var 1, .extra0, .extra1, .extra2, .extra3]),
          nvars := 2, guardInvalid := false, extra := true } false
        ((#[] : Array Ast).push (.tok (q.tokenAt p.mark)) |>.push b)
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) s2) =
      (mkAt .UnaryOp [opNode c, b] (extraLoc (q.tokenAt p.mark) s2),
        (insertMemo p.mark (1000 + 141) (mkAt .UnaryOp [opNode c, b]
          (extraLoc (q.tokenAt p.mark) s2)) s2).2.leave) := by
    intro c b s2 h2e
    rw [altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, memoDone]
  refine ⟨fun ht b s2 h1 hb h2e => ?_, fun ht b s2 h1 hb h2e => ?_,
    fun ht b s2 h1 hb h2e => ?_, fun h14 h15 h31 v s h1 hv => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h1]) hb, items_nil])]
    exact fin .UAdd b s2 h2e
  · rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h1]) hb, items_nil])]
    exact fin .USub b s2 h2e
  · rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_rule, h1]) hb, items_nil])]
    exact fin .Invert b s2 h2e
  · rw [alts_fail (by rfl) he (items_call_null (tok_no _ _ h14)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h15)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h31)), hq,
      alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl

/-! ### `power` -/

/-- `power` (`Grammar/python.gram:862-864`):
```
    | a=await_primary '**' b=factor { _PyAST_BinOp(a, Pow, b, EXTRA) }
    | await_primary
```
`a ** b` is `BinOp(a, Pow, b)` with the right operand a `factor`, so `**` groups to the right
(`factor` reaches `power` again) and takes a signed right operand (`2 ** -1`). Without `**` after
`await_primary`, the mark goes back and the second alternative returns `await_primary` parsed
again. -/
def Power : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a b : Ast) (tp : Token) (s1 s2 s3 : PS), callRule (f + 2) 143 q = (a, s1) → a ≠ .null →
    expectToken 35 s1 = (.tok tp, s2) → callRule f 141 s2 = (b, s3) → b ≠ .null →
    s3.errorIndicator = false →
    callRule (f + 7) 142 p = (mkAt .BinOp [a, opNode .Pow, b] (extraLoc t s3), s3.leave)) ∧
  (∀ (a a' : Ast) (s1 s2 s3 : PS), callRule (f + 2) 143 q = (a, s1) → a ≠ .null →
    expectToken 35 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 1) 143 { s2 with mark := p.mark } = (a', s3) → a' ≠ .null →
    callRule (f + 7) 142 p = (a', s3.leave))

theorem power_proven : Power := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 142 = r142 from rfl, r142]
  refine ⟨fun a b tp s1 s2 s3 h1 ha h2 h3 hb h3e => ?_,
    fun a a' s1 s2 s3 h1 ha h2 h2e h3 ha' => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only
        rw [items_call (by rw [call_rule, h3]) ha', items_nil]), altResult_none1 rfl rfl]
    rfl

/-! ### `signed_number` -/

/-- `signed_number` (`Grammar/python.gram:556-559`, the literal patterns of `match`), with the
`'+' NUMBER` alternative that 3.15 added:
```
    | NUMBER
    | '+' number=NUMBER { _PyAST_UnaryOp(UAdd, number, EXTRA) }
    | '-' number=NUMBER { _PyAST_UnaryOp(USub, number, EXTRA) }
```
A `NUMBER` is returned as `_PyPegen_number_token` makes it; `+` and `-` followed by a `NUMBER`
give the unary node; any other token gives `NULL`. -/
def SignedNumber : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  let s1 := { q with mark := p.mark + 1 }
  (t.type = 2 → ∀ (v : Ast) (s : PS), numberToken q = (v, s) → v ≠ .null →
    callRule (f + 8) 77 p = (v, s.leave)) ∧
  (t.type = 14 → ∀ (n : Ast) (s : PS), numberToken s1 = (n, s) → n ≠ .null →
    s.errorIndicator = false →
    callRule (f + 8) 77 p = (mkAt .UnaryOp [opNode .UAdd, n] (extraLoc t s), s.leave)) ∧
  (t.type = 15 → ∀ (n : Ast) (s : PS), numberToken s1 = (n, s) → n ≠ .null →
    s.errorIndicator = false →
    callRule (f + 8) 77 p = (mkAt .UnaryOp [opNode .USub, n] (extraLoc t s), s.leave)) ∧
  (t.type ≠ 2 → t.type ≠ 14 → t.type ≠ 15 → callRule (f + 8) 77 p = (.null, q.leave))

theorem signedNumber_proven : SignedNumber := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 77 = r77 from rfl, r77]
  have tok_ok : ∀ (g ty : Nat), (q.tokenAt p.mark).type = ty →
      runCall (g + 1) (.tok ty) q = (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_t ht]
  have tok_no : ∀ (g ty : Nat), (q.tokenAt p.mark).type ≠ ty →
      runCall (g + 1) (.tok ty) q = (.null, q) :=
    fun g ty ht => by rw [call_tok, expectToken_at _ _ hlt', hm, ite_f ht]
  have num_no : ∀ g, (q.tokenAt p.mark).type ≠ 2 → runCall (g + 1) .number q = (.null, q) :=
    fun g ht => by rw [call_number, numberToken_other hlt' (hm ▸ ht)]
  have fin : ∀ (c : Ctor) (n : Ast) (s : PS), s.errorIndicator = false →
      (altResult
        { items := [.call (.tok 0), .call .number],
          action := some (.mk .UnaryOp [.ctor c, .var 1, .extra0, .extra1, .extra2, .extra3]),
          nvars := 2, guardInvalid := false, extra := true } false
        ((#[] : Array Ast).push (.tok (q.tokenAt p.mark)) |>.push n)
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) s).1.getD .null =
        mkAt .UnaryOp [opNode c, n] (extraLoc (q.tokenAt p.mark) s) ∧
      (altResult
        { items := [.call (.tok 0), .call .number],
          action := some (.mk .UnaryOp [.ctor c, .var 1, .extra0, .extra1, .extra2, .extra3]),
          nvars := 2, guardInvalid := false, extra := true } false
        ((#[] : Array Ast).push (.tok (q.tokenAt p.mark)) |>.push n)
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) s).2 = s := by
    intro c n s h2e
    rw [altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  refine ⟨fun ht v s h1 hv => ?_, fun ht n s h1 hn h1e => ?_, fun ht n s h1 hn h1e => ?_,
    fun h2 h14 h15 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_number, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (items_call_null (num_no _ (by omega))), hq,
      alts_ok (by rfl) he (by
        dsimp only
        rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_number, h1]) hn,
          items_nil])]
    obtain ⟨e1, e2⟩ := fin .UAdd n s h1e
    exact Prod.ext e1 (congrArg PS.leave e2)
  · rw [alts_fail (by rfl) he (items_call_null (num_no _ (by omega))), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ (by omega))), hq,
      alts_ok (by rfl) he (by
        dsimp only
        rw [items_call (tok_ok _ _ ht) (by simp), items_call (by rw [call_number, h1]) hn,
          items_nil])]
    obtain ⟨e1, e2⟩ := fin .USub n s h1e
    exact Prod.ext e1 (congrArg PS.leave e2)
  · rw [alts_fail (by rfl) he (items_call_null (num_no _ h2)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h14)), hq,
      alts_fail (by rfl) he (items_call_null (tok_no _ _ h15)), hq, alts_nil]
    rfl

end PyLean.PyGrammar.Peg
