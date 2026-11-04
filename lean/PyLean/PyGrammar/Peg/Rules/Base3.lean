import PyLean.PyGrammar.Peg.Rules.Exprs5

/-! More tools for `Peg/Rules/`: the raising actions `RAISE_SYNTAX_ERROR_KNOWN_LOCATION` and
`RAISE_SYNTAX_ERROR_KNOWN_RANGE`, `*` loops (`_loop0_`), and rules of the form
`invalid_x | x`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- The state a `RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, msg)` leaves (`Parser/pegen.h`,
`RAISE_ERROR_KNOWN_LOCATION`): the exception from `a`'s start to `b`'s end, and the error return
of the action (`emit_action` turns its `NULL` into `error_indicator`). -/
def raisedAt (a b : Ast) (m : String) (s : PS) : PS :=
  { (raiseErrorKnownLocation "SyntaxError" (locOf a).lineno (locOf a).colOffset (locOf b).endLineno
      (locOf b).endColOffset m s).2 with errorIndicator := true }

/-- `RAISE_SYNTAX_ERROR_KNOWN_LOCATION(a, msg)` as an action without `EXTRA`, `a` the alternative's
variable `i`, with no error before it: an error return located at `a`. -/
theorem altResult_raiseKL {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i : Nat} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_LOCATION [.var i, .str m]))
    (h2 : a.extra = false) (he : s.errorIndicator = false)
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = (none, raisedAt (env.getD i .null) (env.getD i .null) m s) := by
  rw [altResult_plain h1 h2]
  simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
    List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero]
  have herr := raiseEKL_errOcc "SyntaxError" m (locOf (env.getD i .null)).lineno
    (locOf (env.getD i .null)).colOffset (locOf (env.getD i .null)).endLineno
    (locOf (env.getD i .null)).endColOffset s he
  unfold raisedAt
  generalize raiseErrorKnownLocation "SyntaxError" (locOf (env.getD i .null)).lineno
    (locOf (env.getD i .null)).colOffset (locOf (env.getD i .null)).endLineno
    (locOf (env.getD i .null)).endColOffset m s = r at herr ⊢
  obtain ⟨u, s'⟩ := r
  simp only at herr
  simp [nonNull, herr]

/-- `RAISE_SYNTAX_ERROR_KNOWN_RANGE(a, b, msg)` as an action without `EXTRA`, `a` and `b` the
alternative's variables `i` and `j`, with no error before it. -/
theorem altResult_raiseKR {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {i j : Nat} {m : String}
    (h1 : a.action = some (.call .RAISE_SYNTAX_ERROR_KNOWN_RANGE [.var i, .var j, .str m]))
    (h2 : a.extra = false) (he : s.errorIndicator = false)
    (hm : msgOf [.str (m.toList.map Char.toNat)] = m) :
    altResult a g env st s = (none, raisedAt (env.getD i .null) (env.getD j .null) m s) := by
  rw [altResult_plain h1 h2]
  simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, raiseRange,
    List.drop_succ_cons, List.drop_zero, hm, List.getD_cons_zero, List.getD_cons_succ]
  have herr := raiseEKL_errOcc "SyntaxError" m (locOf (env.getD i .null)).lineno
    (locOf (env.getD i .null)).colOffset (locOf (env.getD j .null)).endLineno
    (locOf (env.getD j .null)).endColOffset s he
  unfold raisedAt
  generalize raiseErrorKnownLocation "SyntaxError" (locOf (env.getD i .null)).lineno
    (locOf (env.getD i .null)).colOffset (locOf (env.getD j .null)).endLineno
    (locOf (env.getD j .null)).endColOffset m s = r at herr ⊢
  obtain ⟨u, s'⟩ := r
  simp only at herr
  simp [nonNull, herr]

/-- A `_loop0_` rule over one rule `rr` (default action): rounds `i < n` call `rr` from `ss i`
(`ss 0` the state after entry), the first `NULL` ends the loop; the sequence of the values in
order, ending after the last (the empty sequence when there is none: `*` never fails without an
error). -/
def Loop0Over (lp rr : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  ∀ (n : Nat) (vs : Nat → Ast) (ss : Nat → PS) (s' : PS), ss 0 = p.enter →
  (∀ i, i < n → callRule (f + (n - i)) rr (ss i) = (vs i, ss (i + 1)) ∧ vs i ≠ .null) →
  callRule f rr (ss n) = (.null, s') →
  callRule (f + n + 5) lp p = (.seq ((List.range n).map vs), { s' with mark := (ss n).mark }.leave)

theorem loop0Over_of {lp rr : Nat}
    (hl : ruleOf lp = Rule.mk (ruleOf lp).name .loop0 false false false false false
      [Alt.mk [.call (.rule rr)] none 1 false false]) : Loop0Over lp rr := by
  intro f p he hlv n vs ss s' hs0 hstep hlast
  have he' : p.enter.errorIndicator = false := he
  have hloop := runLoop_chain rr ((ruleOf lp).alts.headD default) (by rw [hl]; rfl) (by rw [hl]; rfl)
    (by rw [hl]; rfl) (0, 0) n f vs ss s' [] hstep hlast
  rw [hs0] at hloop
  have hloop' : runLoop (f + n + 3) ((ruleOf lp).alts.headD default) p.mark (0, 0) [] p.enter =
      ((((List.range n).map vs).reverse ++ [], (ss n).mark, false, true), s') := hloop
  have hp : rulePrologue lp (ruleOf lp) p = (.inr (p.mark, (0, 0)), p.enter) := by
    simp only [rulePrologue, addLevel_ok p hlv, he', show (ruleOf lp).memo = false by rw [hl],
      Bool.false_eq_true, ↓reduceIte, ruleStart, show (ruleOf lp).extra = false by rw [hl]]
    rfl
  have hk : (ruleOf lp).kind = RuleKind.loop0 := by rw [hl]
  have hb : callRule (f + n + 5) lp p = loopFinish (ruleOf lp)
      (((List.range n).map vs).reverse ++ [], (ss n).mark, false, true) s' := by
    have e1 : callRule (f + n + 5) lp p = ruleBody (f + n + 4) lp (ruleOf lp) p := by
      rw [show f + n + 5 = (f + n + 4) + 1 from rfl]
      simp only [callRule, show (ruleOf lp).leftRec = false by rw [hl],
        show (ruleOf lp).withoutInvalid = false by rw [hl], Bool.false_and, Bool.false_eq_true,
        ↓reduceIte]
    rw [e1, show f + n + 4 = (f + n + 3) + 1 from rfl]
    simp only [ruleBody, hp, hk, he', Bool.false_eq_true, ↓reduceIte]
    rw [hloop']
  rw [hb]
  simp only [loopFinish, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hk, retLevel_eq]
  simp

/-- A rule `invalid_x | x` without `EXTRA` (`inv` guarded by `call_invalid_rules`): in the first
pass the result of `rr` from the entry state; in the second, `inv` first: its non-`NULL` result
is the rule's, an error from it ends the rule with `NULL`, and its `NULL` leads to `rr` from the
start mark. A `NULL` from `rr` puts the mark back. -/
def InvOr (id inv rr : Nat) : Prop := ∀ (f : Nat) (p : PS), p.errorIndicator = false →
  p.level ≠ MAXSTACK →
  (p.callInvalidRules = false → ∀ (v : Ast) (s : PS), callRule f rr p.enter = (v, s) → v ≠ .null →
    callRule (f + 6) id p = (v, s.leave)) ∧
  (p.callInvalidRules = false → ∀ (s : PS), callRule f rr p.enter = (.null, s) →
    callRule (f + 6) id p = (.null, { s with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (v : Ast) (s : PS), callRule (f + 1) inv p.enter = (v, s) →
    v ≠ .null → callRule (f + 6) id p = (v, s.leave)) ∧
  (p.callInvalidRules = true → ∀ (s : PS), callRule (f + 1) inv p.enter = (.null, s) →
    s.errorIndicator = true → callRule (f + 6) id p = (.null, { s with mark := p.mark }.leave)) ∧
  (p.callInvalidRules = true → ∀ (v : Ast) (s s' : PS), callRule (f + 1) inv p.enter = (.null, s) →
    s.errorIndicator = false → callRule f rr { s with mark := p.mark } = (v, s') → v ≠ .null →
    callRule (f + 6) id p = (v, s'.leave)) ∧
  (p.callInvalidRules = true → ∀ (s s' : PS), callRule (f + 1) inv p.enter = (.null, s) →
    s.errorIndicator = false → callRule f rr { s with mark := p.mark } = (.null, s') →
    callRule (f + 6) id p = (.null, { s' with mark := p.mark }.leave))

theorem invOr_of {id inv rr : Nat}
    (hr : ruleOf id = Rule.mk (ruleOf id).name .normal false false false false false
      [Alt.mk [.call (.rule inv)] none 1 true false, Alt.mk [.call (.rule rr)] none 1 false false]) :
    InvOr id inv rr := by
  intro f p he hl
  have he' : p.enter.errorIndicator = false := he
  have E : ∀ s : PS, s.errorIndicator = false → ({ s with mark := p.mark } : PS).errorIndicator = false :=
    fun s hs => hs
  rw [callRule_plain (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) (by rw [hr]) he hl, hr]
  refine ⟨fun hi v s h1 hv => ?_, fun hi s h1 => ?_, fun hi v s h1 hv => ?_, fun hi s h1 h1e => ?_,
    fun hi v s s' h1 h1e h2 hv => ?_, fun hi s s' h1 h1e h2 => ?_⟩
  · have hi' : p.enter.callInvalidRules = false := hi
    rw [alts_skip (by simp [hi']), alts_ok (by rfl) he' (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · have hi' : p.enter.callInvalidRules = false := hi
    rw [alts_skip (by simp [hi']), alts_fail (by rfl) he' (by
      dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · have hi' : p.enter.callInvalidRules = true := hi
    rw [alts_ok (by simp [hi']) he' (by
      dsimp only; rw [items_call (by rw [call_rule, h1]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · have hi' : p.enter.callInvalidRules = true := hi
    rw [alts_fail (by simp [hi']) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_err (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = true from h1e)]
    rfl
  · have hi' : p.enter.callInvalidRules = true := hi
    rw [alts_fail (by simp [hi']) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (E s h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]), altResult_none1 rfl rfl]
    rfl
  · have hi' : p.enter.callInvalidRules = true := hi
    rw [alts_fail (by simp [hi']) he' (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_fail (by rfl) (E s h1e) (by dsimp only; rw [items_call_null (by rw [call_rule, h2])]),
      alts_nil]
    rfl

end PyLean.PyGrammar.Peg
