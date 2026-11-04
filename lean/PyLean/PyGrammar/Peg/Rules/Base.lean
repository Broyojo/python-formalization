import PyLean.PyGrammar.Peg.TokenProps
import PyLean.PyGrammar.Peg.Sound
import PyLean.PyGrammar.Peg.ErrorProps

/-!
Tools for the rule-by-rule statements of `Peg/Rules/`. Each statement there is about one rule
function of `Parser/parser.c`, as `callRule` runs it on that rule's data: from any parser state,
given what the token readers and the sub-rule functions it calls return (as equations, so
any outcome of a sub-rule is allowed, including an error), it says what the rule function
returns and in which state. Those statements are written from the rule's text in
`Grammar/python.gram`, never from `GrammarData.lean`, so a rule with its alternatives in another
order, a lookahead or cut dropped, or another action, fails them.

`fuel` is the model's bound (`Interp.lean`). Each interpreter level uses one unit, so a rule
called with `f + k` calls its sub-rules with fuel `f + j` for a fixed `j < k`; the statements
hold for every `f`.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

theorem ite_t {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : c) : (if c then a else b) = a := by
  simp [h]

theorem ite_f {α : Sort _} {c : Prop} [Decidable c] {a b : α} (h : ¬c) : (if c then a else b) = b := by
  simp [h]

/-- `p->level++`, on entry to a rule function. -/
def PS.enter (p : PS) : PS := { p with level := p.level + 1 }

/-- `p->level--`, on the way out. -/
def PS.leave (q : PS) : PS := { q with level := q.level - 1 }

/-- An operator constant, `.ctor` in an action. -/
abbrev opNode (c : Ctor) : Ast := .node c [] none

/-- `EXTRA` of an alternative that started at token `t` and ended with `q.mark`. -/
def extraLoc (t : Token) (q : PS) : Loc :=
  let e := lastNonWhitespaceToken q
  ⟨t.lineno, t.colOffset, e.endLineno, e.endColOffset⟩

/-- What a rule function needs on entry to run its alternatives: no error yet, the stack below
`MAXSTACK`, a mark within the tokens, and the token under the mark read (by `ensureToken`, which
may run the tokenizer) into state `q`. The other outcome of `ensureToken`, a tokenizer error, is
`callRule_extra_fail`. -/
structure Entered (p q : PS) : Prop where
  ei : p.errorIndicator = false
  level : p.level ≠ MAXSTACK
  mark : p.mark ≤ p.fill
  read : ensureToken p.enter = (true, q)

theorem addLevel_ok (p : PS) (h : p.level ≠ MAXSTACK) : addLevel p = ((), p.enter) := by
  have h' : (p.level == MAXSTACK) = false := by simpa using h
  simp only [addLevel, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, modify,
    modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet, h',
    Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, PS.enter]

theorem retLevel_eq (v : Ast) (s : PS) : retLevel v s = (v, s.leave) := rfl

/-- The control fields a token read leaves alone. -/
structure Ctl (p q : PS) : Prop where
  ei : q.errorIndicator = p.errorIndicator
  level : q.level = p.level
  inv : q.callInvalidRules = p.callInvalidRules
  fv : q.featureVersion = p.featureVersion

theorem pushToken_ctl (p : PS) : Ctl p (pushToken p).1 := by
  unfold pushToken
  dsimp only
  generalize getTokSkippingIgnores (p.tok.src.size + 2) p.tok p.typeIgnores = r
  obtain ⟨s, ty, t, ig⟩ := r
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl, rfl, rfl⟩

theorem tokenizerError_fst (q : PS) : (tokenizerError q).1 = -1 := by
  unfold tokenizerError
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure]
  split
  · rfl
  · simp only [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, MonadState.modifyGet,
      StateT.bind, StateT.get, pure, StateT.pure]
    rfl

theorem ensureToken_mark (p : PS) : (ensureToken p).2.mark = p.mark := (frame_ensureToken p).mark

/-- At a token already read, `ensureToken` does nothing. -/
theorem ensureToken_at (q : PS) (h : q.mark < q.fill) : ensureToken q = (true, q) := by
  have h' : (q.mark == q.fill) = false := by simp; omega
  rw [ensureToken_eq]
  simp [h']

theorem expectToken_at (ty : Nat) (p : PS) (h : p.mark < p.fill) :
    expectToken ty p = if (p.tokenAt p.mark).type = ty then
      (.tok (p.tokenAt p.mark), { p with mark := p.mark + 1 }) else (.null, p) := by
  rw [(expectToken_proven p ty).1 (Nat.ne_of_lt h)]
  by_cases ht : (p.tokenAt p.mark).type = ty <;> simp [ht]

theorem callRule_grows (f id : Nat) (p : PS) : Grows p (callRule f id p).2 :=
  ((sound_all f).2.2.2.2.2.2 (fun _ => default) id p).grows

theorem expectToken_grows (ty : Nat) (p : PS) : Grows p (expectToken ty p).2 :=
  (expectToken_step ty p).1

/-- `_PyPegen_get_last_nonnwhitespace_token` right after taking a token that is not `NEWLINE`,
`INDENT`, `DEDENT` or `ENDMARKER`. -/
theorem lastNonWhitespaceToken_at (s : PS) (m : Nat) (h : s.mark = m + 1)
    (ht : (s.tokenAt m).type ≠ 0 ∧ ((s.tokenAt m).type < 4 ∨ 6 < (s.tokenAt m).type)) :
    lastNonWhitespaceToken s = s.tokenAt m := by
  unfold lastNonWhitespaceToken
  rw [h]
  simp only [lastNonWhitespaceToken.go]
  split
  · rfl
  · rename_i hn
    exfalso
    apply hn
    have e0 : TokKind.ENDMARKER.num = 0 := rfl
    have e4 : TokKind.NEWLINE.num = 4 := rfl
    have e6 : TokKind.DEDENT.num = 6 := rfl
    simp only [e0, e4, e6, bne_iff_ne, ne_eq, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
    omega

/-- A successful `ensureToken` moves nothing the rule functions look at, and leaves a token under
the mark. -/
theorem ensureToken_ok {p q : PS} (hm : p.mark ≤ p.fill) (h : ensureToken p = (true, q)) :
    Ctl p q ∧ q.mark = p.mark ∧ q.mark < q.fill ∧ TokGrows p q := by
  have hs := frame_ensureToken p
  rw [h] at hs
  have hlt := ensureToken_lt p hm (by rw [h])
  rw [h] at hlt
  refine ⟨?_, hs.mark, hs.mark ▸ hlt, hs.grows.toks⟩
  rw [ensureToken_eq] at h
  by_cases h1 : (p.mark == p.fill) = true
  · by_cases h2 : (fillToken p).1 < 0
    · simp only [h1, h2, ↓reduceIte] at h
      cases h
    · simp only [h1, h2, ↓reduceIte] at h
      cases h
      have := fillToken_step p
      by_cases h3 : ((pushToken p).2 == TokKind.ERRORTOKEN.num) = true
      · exfalso
        apply h2
        rw [this]
        simp only [h3, ↓reduceIte]
        split
        · rw [raiseDecode_eq]
          show (-1 : Int) < 0
          decide
        · rw [tokenizerError_fst]
          decide
      · rw [this]
        simp only [h3, Bool.false_eq_true, ↓reduceIte]
        exact pushToken_ctl p
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- What `Entered` gives about the state after the entry read. -/
theorem Entered.facts {p q : PS} (h : Entered p q) :
    q.errorIndicator = false ∧ q.level = p.level + 1 ∧ q.callInvalidRules = p.callInvalidRules ∧
      q.featureVersion = p.featureVersion ∧ q.mark = p.mark ∧ p.mark < q.fill ∧
      TokGrows p q := by
  obtain ⟨c, m, l, g⟩ := ensureToken_ok (p := p.enter) (q := q) h.mark h.read
  exact ⟨c.ei.trans h.ei, (c.level : q.level = p.level + 1), c.inv, c.fv, m, m ▸ l, ⟨g.le, fun i hi => g.same i hi⟩⟩

/-- Entry of a rule function that is not left-recursive, not memoized, not `_without_invalid`,
and reads `EXTRA`: `add_level`, the `error_indicator` check, the start location, the alternatives,
and `p->level--`. -/
theorem callRule_extra {f id : Nat} {p q : PS}
    (h1 : (ruleOf id).leftRec = false) (h2 : (ruleOf id).withoutInvalid = false)
    (h3 : (ruleOf id).memo = false) (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = true)
    (h : Entered p q) :
    callRule (f + 2) id p =
      let a := runAlts f (ruleOf id).alts false p.mark
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q
      (a.1.getD .null, a.2.leave) := by
  have he' : p.enter.errorIndicator = false := h.ei
  have hp : rulePrologue id (ruleOf id) p =
      (.inr (p.mark, ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset)), q) := by
    simp only [rulePrologue, addLevel_ok p h.level, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5, startLocation, h.read, Bool.not_true]
    rfl
  simp only [callRule, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, h4, retLevel_eq]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all

/-- The end of a `(memo)` rule function: `_PyPegen_insert_memo(p, _mark, type, _res)` at `done`,
reached with a value (`NULL` included) but not on an error return. -/
def memoDone (m id : Nat) (a : Option Ast × PS) : Ast × PS :=
  match a.1 with
  | none => (.null, a.2.leave)
  | some v => (v, (insertMemo m (1000 + id) v a.2).2.leave)

/-- Entry of a `(memo)` rule function that reads `EXTRA`, at a position with no memo entry for it
yet: as `callRule_extra`, and the result is memoized. -/
theorem callRule_memo_extra {f id : Nat} {p q : PS}
    (h1 : (ruleOf id).leftRec = false) (h2 : (ruleOf id).withoutInvalid = false)
    (h3 : (ruleOf id).memo = true) (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = true)
    (h : Entered p q) (hn : (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + id) = none) :
    callRule (f + 2) id p =
      memoDone p.mark id (runAlts f (ruleOf id).alts false p.mark
        ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset) q) := by
  obtain ⟨-, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : ensureToken q = (true, q) := ensureToken_at q (hm ▸ hlt)
  have hp : rulePrologue id (ruleOf id) p =
      (.inr (p.mark, ((q.tokenAt p.mark).lineno, (q.tokenAt p.mark).colOffset)), q) := by
    simp only [rulePrologue, addLevel_ok p h.level, he', h3, Bool.false_eq_true, ↓reduceIte,
      isMemoized, h.read, memoLookup, hm, hn, ruleStart, h5, startLocation, hq, Bool.not_true]
  simp only [callRule, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, h4, retLevel_eq]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, ↓reduceIte, memoDone]
  split <;> simp_all

/-- Entry of a rule function that reads `EXTRA`, when reading the token under the mark fails (a
tokenizer error): `NULL`, with the state `ensureToken` left and `p->level` back. -/
theorem callRule_extra_fail {f id : Nat} {p q : PS}
    (h1 : (ruleOf id).leftRec = false) (h2 : (ruleOf id).withoutInvalid = false)
    (h3 : (ruleOf id).memo = false) (h5 : (ruleOf id).extra = true)
    (he : p.errorIndicator = false) (hl : p.level ≠ MAXSTACK)
    (hq : ensureToken p.enter = (false, q)) :
    callRule (f + 2) id p = (.null, q.leave) := by
  have he' : p.enter.errorIndicator = false := he
  have hp : rulePrologue id (ruleOf id) p = (.inl .null, q) := by
    simp only [rulePrologue, addLevel_ok p hl, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5, startLocation, hq, Bool.not_false]
  simp only [callRule, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, retLevel_eq]

/-- Entry of a plain rule function that does not read `EXTRA`: no token is read on entry. -/
theorem callRule_plain {f id : Nat} {p : PS}
    (h1 : (ruleOf id).leftRec = false) (h2 : (ruleOf id).withoutInvalid = false)
    (h3 : (ruleOf id).memo = false) (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = false)
    (he : p.errorIndicator = false) (hl : p.level ≠ MAXSTACK) :
    callRule (f + 2) id p =
      let a := runAlts f (ruleOf id).alts false p.mark (0, 0) p.enter
      (a.1.getD .null, a.2.leave) := by
  have he' : p.enter.errorIndicator = false := he
  have hp : rulePrologue id (ruleOf id) p = (.inr (p.mark, (0, 0)), p.enter) := by
    simp only [rulePrologue, addLevel_ok p hl, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5]
    rfl
  simp only [callRule, h1, h2, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  simp only [ruleBody, hp, h4, retLevel_eq]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all

theorem tg_call {f id : Nat} {s s' : PS} {v : Ast} (h : callRule f id s = (v, s')) :
    TokGrows s s' := by
  have := (callRule_grows f id s).toks
  rwa [h] at this

theorem tg_expect {ty : Nat} {s s' : PS} {v : Ast} (h : expectToken ty s = (v, s')) :
    TokGrows s s' := by
  have := (expectToken_grows ty s).toks
  rwa [h] at this

theorem tg_mark {s s' : PS} (h : TokGrows s s') (m : Nat) : TokGrows s { s' with mark := m } :=
  ⟨h.le, h.same⟩

theorem tg_mark' {s s' : PS} (h : TokGrows s s') (m : Nat) : TokGrows { s with mark := m } s' :=
  ⟨h.le, h.same⟩

/-- Back at mark `m` after an alternative failed, the token there is still the one read first. -/
theorem expect_again {ty m : Nat} {q s : PS} (g : TokGrows q s) (hlt : m < q.fill) :
    expectToken ty { s with mark := m } =
      if (q.tokenAt m).type = ty then (.tok (q.tokenAt m), { s with mark := m + 1 })
      else (.null, { s with mark := m }) := by
  rw [expectToken_at ty { s with mark := m } (Nat.lt_of_lt_of_le hlt g.le)]
  have e : ({ s with mark := m } : PS).tokenAt ({ s with mark := m } : PS).mark = q.tokenAt m :=
    g.same m hlt
  rw [e]

/-- The first token read of a rule function without `EXTRA`, after `Entered`. -/
theorem expect_entered {ty : Nat} {p q : PS} (h : Entered p q) :
    expectToken ty p.enter =
      if (q.tokenAt p.mark).type = ty then (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 })
      else (.null, q) := by
  obtain ⟨-, -, -, -, hm, hlt, -⟩ := h.facts
  rw [expectToken_eq, h.read]
  simp only [↓reduceIte, takeToken, hm, bne_iff_ne, ne_eq]
  by_cases ht : (q.tokenAt p.mark).type = ty <;> simp [ht]

/-- A raise with no error yet sets one. -/
theorem raiseEKL_errOcc (cls msg : String) (a b c d : Int) (s : PS) (h : s.errorIndicator = false) :
    (raiseErrorKnownLocation cls a b c d msg s).2.errOccurred = true := by
  unfold raiseErrorKnownLocation
  obtain ⟨e, he, -⟩ := raiseKnownLocation_err s cls msg a (if (b == -5) = true then -5 else b + 1) c
    (if (d == -5) = true then -5 else d + 1) (by simp [h])
  simp only [PS.errOccurred, he, Option.isSome_some]

/-- `_PyPegen_number_token` at a token that is not a `NUMBER`. -/
theorem numberToken_other {q : PS} (hlt : q.mark < q.fill) (ht : (q.tokenAt q.mark).type ≠ 2) :
    numberToken q = (.null, q) := by
  have : expectToken TokKind.NUMBER.num q = (.null, q) := by
    rw [expectToken_at _ _ hlt]
    exact ite_f ht
  simp only [numberToken, bind, StateT.bind, this]
  rfl

/-! ### One step of `runItems` and `runAlts` -/

theorem items_nil (f : Nat) (env : Array Ast) (cut : Bool) (s : PS) :
    runItems (f + 1) [] env cut s = ((some env, cut), s) := by simp [runItems]

theorem items_call {f : Nat} {c : Call} {rest : List Item} {env : Array Ast} {cut : Bool}
    {s s' : PS} {v : Ast} (h : runCall f c s = (v, s')) (hv : v ≠ .null) :
    runItems (f + 1) (.call c :: rest) env cut s = runItems f rest (env.push v) cut s' := by
  have : nonNull v = true := by cases v <;> simp_all [nonNull]
  simp only [runItems, h, this, ↓reduceIte]

theorem items_call_null {f : Nat} {c : Call} {rest : List Item} {env : Array Ast} {cut : Bool}
    {s s' : PS} (h : runCall f c s = (.null, s')) :
    runItems (f + 1) (.call c :: rest) env cut s = ((none, cut), s') := by
  simp only [runItems, h, nonNull, Bool.false_eq_true, ↓reduceIte]

theorem items_opt {f : Nat} {c : Call} {rest : List Item} {env : Array Ast} {cut : Bool}
    {s s' : PS} {v : Ast} (h : runCall f c s = (v, s')) (he : s'.errorIndicator = false) :
    runItems (f + 1) (.opt c :: rest) env cut s = runItems f rest (env.push v) cut s' := by
  simp only [runItems, h, he, Bool.false_eq_true, ↓reduceIte]

theorem items_opt_err {f : Nat} {c : Call} {rest : List Item} {env : Array Ast} {cut : Bool}
    {s s' : PS} {v : Ast} (h : runCall f c s = (v, s')) (he : s'.errorIndicator = true) :
    runItems (f + 1) (.opt c :: rest) env cut s = ((none, cut), s') := by
  simp only [runItems, h, he, ↓reduceIte]

theorem items_look {f : Nat} {b : Bool} {c : Call} {rest : List Item} {env : Array Ast}
    {cut : Bool} {s s' : PS} {v : Ast} (h : runCall f c s = (v, s')) (hv : nonNull v = b) :
    runItems (f + 1) (.look b c :: rest) env cut s =
      runItems f rest env cut { s' with mark := s.mark } := by
  simp only [runItems, h, hv, beq_self_eq_true, ↓reduceIte]

theorem items_look_fail {f : Nat} {b : Bool} {c : Call} {rest : List Item} {env : Array Ast}
    {cut : Bool} {s s' : PS} {v : Ast} (h : runCall f c s = (v, s')) (hv : nonNull v = !b) :
    runItems (f + 1) (.look b c :: rest) env cut s = ((none, cut), { s' with mark := s.mark }) := by
  cases b <;> simp_all [runItems]

theorem items_cut (f : Nat) (rest : List Item) (env : Array Ast) (cut : Bool) (s : PS) :
    runItems (f + 1) (.cut :: rest) env cut s = runItems f rest (env.push (.int 1)) true s := by
  simp [runItems]

theorem call_tok (f t : Nat) (s : PS) : runCall (f + 1) (.tok t) s = expectToken t s := by
  simp [runCall]

theorem call_number (f : Nat) (s : PS) : runCall (f + 1) .number s = numberToken s := by
  simp [runCall]

theorem call_softKw (f : Nat) (kw : List Nat) (s : PS) :
    runCall (f + 1) (.softKw kw) s = expectSoftKeyword kw s := by
  simp [runCall]

/-- The tail of an action that raises: `RAISE_*` returns `NULL` with the exception set, and
`emit_action` turns that into an error return. -/
theorem raised_result {r : Unit × PS} {s : PS} (cls msg : String) (a b c d : Int)
    (hr : raiseErrorKnownLocation cls a b c d msg s = r) (he : s.errorIndicator = false) :
    r.2.errOccurred = true := by
  rw [← hr]
  exact raiseEKL_errOcc cls msg a b c d s he

theorem call_rule (f r : Nat) (s : PS) : runCall (f + 1) (.rule r) s = callRule f r s := by
  simp [runCall]

theorem alts_nil (f : Nat) (g : Bool) (m : Nat) (st : Int × Int) (s : PS) :
    runAlts (f + 1) [] g m st s = (some .null, s) := by simp [runAlts]

/-- An alternative whose items all matched: its action decides. -/
theorem alts_ok {f : Nat} {a : Alt} {rest : List Alt} {g : Bool} {m : Nat} {st : Int × Int}
    {s s' : PS} {env : Array Ast} {c : Bool}
    (hg : (a.guardInvalid && !s.callInvalidRules) = false) (he : s.errorIndicator = false)
    (h : runItems f a.items #[] false s = ((some env, c), s')) :
    runAlts (f + 1) (a :: rest) g m st s = altResult a g env st s' := by
  simp only [runAlts, hg, he, h, Bool.false_eq_true, ↓reduceIte]

/-- An alternative that failed before a cut: back to the mark, on to the next. -/
theorem alts_fail {f : Nat} {a : Alt} {rest : List Alt} {g : Bool} {m : Nat} {st : Int × Int}
    {s s' : PS} (hg : (a.guardInvalid && !s.callInvalidRules) = false)
    (he : s.errorIndicator = false) (h : runItems f a.items #[] false s = ((none, false), s')) :
    runAlts (f + 1) (a :: rest) g m st s = runAlts f rest g m st { s' with mark := m } := by
  simp only [runAlts, hg, he, h, Bool.false_eq_true, ↓reduceIte]

/-- An alternative that failed after its cut: the rule fails. -/
theorem alts_cut {f : Nat} {a : Alt} {rest : List Alt} {g : Bool} {m : Nat} {st : Int × Int}
    {s s' : PS} (hg : (a.guardInvalid && !s.callInvalidRules) = false)
    (he : s.errorIndicator = false) (h : runItems f a.items #[] false s = ((none, true), s')) :
    runAlts (f + 1) (a :: rest) g m st s = (none, { s' with mark := m }) := by
  simp only [runAlts, hg, he, h, Bool.false_eq_true, ↓reduceIte]

/-- An `invalid_` alternative in the first pass is not tried. -/
theorem alts_skip {f : Nat} {a : Alt} {rest : List Alt} {g : Bool} {m : Nat} {st : Int × Int}
    {s : PS} (hg : (a.guardInvalid && !s.callInvalidRules) = true) :
    runAlts (f + 1) (a :: rest) g m st s = runAlts f rest g m st s := by
  simp only [runAlts, hg, ↓reduceIte]

/-- With `error_indicator` set, no further alternative runs. -/
theorem alts_err {f : Nat} {a : Alt} {rest : List Alt} {g : Bool} {m : Nat} {st : Int × Int}
    {s : PS} (hg : (a.guardInvalid && !s.callInvalidRules) = false) (he : s.errorIndicator = true) :
    runAlts (f + 1) (a :: rest) g m st s = (none, s) := by
  simp only [runAlts, hg, he, Bool.false_eq_true, ↓reduceIte]

/-- The `EXTRA` values of an alternative that started at `st` and whose last token is `t`. -/
def mkExtra (st : Int × Int) (t : Token) : Extra := ⟨st.1, st.2, t.endLineno, t.endColOffset⟩

/-- A located action that builds a node from its variables. -/
theorem altResult_extra {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} (h1 : a.action = some act) (h2 : a.extra = true) :
    altResult a g env st s =
      let r := evalA env (mkExtra st (lastNonWhitespaceToken s)) act s
      if ((!nonNull r.1 || r.2.errorIndicator) && r.2.errOccurred) = true then
        (none, { r.2 with errorIndicator := true })
      else (some r.1, r.2) := by
  unfold mkExtra
  simp only [altResult, h1, h2, ↓reduceIte, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure]
  split
  rename_i heq
  rw [heq]
  split <;> rfl

/-- An action with no `EXTRA`. -/
theorem altResult_plain {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    {act : AE} (h1 : a.action = some act) (h2 : a.extra = false) :
    altResult a g env st s =
      let r := evalA env {} act s
      if ((!nonNull r.1 || r.2.errorIndicator) && r.2.errOccurred) = true then
        (none, { r.2 with errorIndicator := true })
      else (some r.1, r.2) := by
  simp only [altResult, h1, h2, Bool.false_eq_true, ↓reduceIte, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, pure, StateT.pure]
  split
  rename_i heq
  rw [heq]
  split <;> rfl

/-- The default action of a one-item alternative: its value. -/
theorem altResult_none1 {a : Alt} {g : Bool} {env : Array Ast} {st : Int × Int} {s : PS}
    (h1 : a.action = none) (h2 : a.nvars = 1) :
    altResult a g env st s = (some (env.getD 0 .null), s) := by
  simp only [altResult, h1, h2]
  rfl

end PyLean.PyGrammar.Peg
