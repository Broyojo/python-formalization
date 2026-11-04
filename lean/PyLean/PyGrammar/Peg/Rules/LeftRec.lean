import PyLean.PyGrammar.Peg.Rules.Base2

/-! Left recursion (`Tools/peg_generator/pegen/c_generator.py`, `_set_up_rule_memoization`), and
the left-recursive binary-operator rules `sum` and `bitwise_or` (`Grammar/python.gram:821-845`),
rule by rule.

A left-recursive leader `name_rule` (`Parser/parser.c`, e.g. `sum_rule`, 13163-13197) is

```
    if (_PyPegen_is_memoized(p, sum_type, &_res)) { p->level--; return _res; }
    int _mark = p->mark;
    int _resmark = p->mark;
    while (1) {
        int tmpvar_8 = _PyPegen_update_memo(p, _mark, sum_type, _res);
        if (tmpvar_8) { p->level--; return _res; }
        p->mark = _mark;
        void *_raw = sum_raw(p);
        if (p->error_indicator) { p->level--; return NULL; }
        if (_raw == NULL || p->mark <= _resmark)
            break;
        _resmark = p->mark;
        _res = _raw;
    }
    p->mark = _resmark;
    _res = _res; p->level--; return _res;
```

`growSeed` (`Interp.lean`) is that loop. Each round stores the last seed in the memo at `_mark`,
so that the recursive call `sum` inside `sum_raw` finds it and the round can extend it on the
right: the seed is always the left operand, which is what makes `a - b - c` group as
`(a - b) - c`. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### The memo entry a round leaves -/

theorem updateMemo_find (s : PS) (m ty : Nat) (v : Ast) (hm : m < s.memo.size) :
    ((updateMemo m ty v s).2.memo.getD m []).find? (fun x => x.1 == ty) = some (ty, v, s.mark) := by
  show ((s.memo.modify m _).getD m []).find? _ = _
  rw [modify_getD_self _ _ hm]
  by_cases ha : (s.memo.getD m []).any (fun x => x.1 == ty) = true
  · simp only [ha, ↓reduceIte]
    exact find_replaced _ ty (ty, v, s.mark) rfl ha
  · have hf : ((s.memo.getD m []).any fun x => x.1 == ty) = false := Bool.eq_false_iff.mpr ha
    simp only [hf, Bool.false_eq_true, ↓reduceIte, List.find?_cons]
    simp

theorem enter_leave_mark (s : PS) (m : Nat) : ({ s.enter with mark := m } : PS).leave = { s with mark := m } := by
  cases s
  simp [PS.enter, PS.leave]

/-- The recursive call of a left-recursive leader inside its own `_raw` function: the memo entry
of the current round is found (`_PyPegen_is_memoized`), and the call returns the seed and resumes
where the seed ended, without parsing anything. -/
theorem callRule_leader_hit {f id : Nat} {s : PS} {v : Ast} {e : Nat}
    (h1 : (ruleOf id).leftRec = true) (h2 : (ruleOf id).leader = true)
    (hl : s.level ≠ MAXSTACK) (hlt : s.mark < s.fill)
    (hf : (s.memo.getD s.mark []).find? (fun x => x.1 == 1000 + id) = some (1000 + id, v, e)) :
    callRule (f + 1) id s = (v, { s with mark := e }) := by
  have hm : isMemoized (1000 + id) s.enter = (some v, { s.enter with mark := e }) := by
    have := isMemoized_hit s.enter s.mark (1000 + id) v e hlt hf
    exact this
  simp only [callRule, h1, h2, Bool.and_self, ↓reduceIte, addLevel_ok s hl, hm, retLevel_eq,
    enter_leave_mark]

/-- The entry of a left-recursive leader, at a position with no memo entry for it: the seed loop
starts with a `NULL` seed at the start mark. -/
theorem callRule_leader {f id : Nat} {p q : PS}
    (h1 : (ruleOf id).leftRec = true) (h2 : (ruleOf id).leader = true) (h : Entered p q)
    (hn : (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + id) = none) :
    callRule (f + 1) id p = growSeed f id (ruleOf id) p.mark p.mark .null q := by
  obtain ⟨-, -, -, -, hm, -, -⟩ := h.facts
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have hiso : isMemoized (1000 + id) p.enter = (none, q) := by
    simp only [isMemoized, h.read, ↓reduceIte, memoLookup, hm, hn]
  simp only [callRule, h1, h2, Bool.and_self, ↓reduceIte, addLevel_ok p h.level, hiso, hm]

/-! ### The seed loop -/

/-- `growSeed`, the `while (1)` above, run for `n` rounds that each grow the seed and a last one
that does not: round `i` stores seed `vs i` (ending at `(ss i).mark`) and runs the `_raw`
function from the start mark, which returns `vs (i + 1)` in state `ss (i + 1)`, further on. The
loop then returns the last seed, at the mark where it ended; an error in the last round returns
`NULL`. Fuel: round `i` runs the `_raw` function with `f + (n - i)`. -/
def GrowSeedChain : Prop := ∀ (id : Nat) (r : Rule) (mark n f : Nat) (vs : Nat → Ast) (ss : Nat → PS)
  (w : Ast) (s' : PS),
  (∀ i, i < n →
    ruleBody (f + (n - i)) id r { (updateMemo mark (1000 + id) (vs i) (ss i)).2 with mark := mark } =
      (vs (i + 1), ss (i + 1)) ∧
    (ss (i + 1)).errorIndicator = false ∧ vs (i + 1) ≠ .null ∧ (ss i).mark < (ss (i + 1)).mark) →
  ruleBody f id r { (updateMemo mark (1000 + id) (vs n) (ss n)).2 with mark := mark } = (w, s') →
  (s'.errorIndicator = false → (w = .null ∨ s'.mark ≤ (ss n).mark) →
    growSeed (f + n + 1) id r mark (ss 0).mark (vs 0) (ss 0) =
      (vs n, { s' with mark := (ss n).mark }.leave)) ∧
  (s'.errorIndicator = true →
    growSeed (f + n + 1) id r mark (ss 0).mark (vs 0) (ss 0) = (.null, s'.leave))

theorem growSeedChain_proven : GrowSeedChain := by
  intro id r mark n
  induction n with
  | zero =>
    intro f vs ss w s' _ hlast
    refine ⟨fun he hw => ?_, fun he => ?_⟩
    · have hc : (!nonNull w || decide (s'.mark ≤ (ss 0).mark)) = true := by
        rcases hw with hw | hw
        · subst hw; rfl
        · simp [hw]
      simp only [growSeed, Nat.add_zero, hlast, he, Bool.false_eq_true, ↓reduceIte, hc, retLevel_eq]
    · simp only [growSeed, Nat.add_zero, hlast, he, ↓reduceIte, retLevel_eq]
  | succ n ih =>
    intro f vs ss w s' hstep hlast
    obtain ⟨h0, h0e, h0n, h0m⟩ := hstep 0 (Nat.zero_lt_succ n)
    have hc : (!nonNull (vs 1) || decide ((ss 1).mark ≤ (ss 0).mark)) = false := by
      have : nonNull (vs 1) = true := by cases h : vs 1 <;> simp_all [nonNull]
      simp [this]
      omega
    have e0 : f + (n + 1 - 0) = f + n + 1 := by omega
    rw [e0] at h0
    have hih := ih f (fun i => vs (i + 1)) (fun i => ss (i + 1)) w s' (fun i hi => by
      have := hstep (i + 1) (by omega)
      rw [show f + (n + 1 - (i + 1)) = f + (n - i) from by omega] at this
      exact this) hlast
    have eg : growSeed (f + (n + 1) + 1) id r mark (ss 0).mark (vs 0) (ss 0) =
        growSeed (f + n + 1) id r mark (ss 1).mark (vs 1) (ss 1) := by
      rw [show f + (n + 1) + 1 = (f + n + 1) + 1 from by omega]
      simp only [growSeed, h0, h0e, Bool.false_eq_true, ↓reduceIte, hc]
    rw [eg]
    exact hih

/-! ### A round of a `_raw` function -/

/-- Entry of the `_raw` function of a left-recursive leader that reads `EXTRA`, at a mark whose
token is already read. -/
theorem ruleBody_extra {f id : Nat} {σ : PS} (h3 : (ruleOf id).memo = false)
    (h4 : (ruleOf id).kind = .normal) (h5 : (ruleOf id).extra = true)
    (he : σ.errorIndicator = false) (hl : σ.level ≠ MAXSTACK) (hlt : σ.mark < σ.fill) :
    ruleBody (f + 1) id (ruleOf id) σ =
      let a := runAlts f (ruleOf id).alts false σ.mark
        ((σ.tokenAt σ.mark).lineno, (σ.tokenAt σ.mark).colOffset) σ.enter
      (a.1.getD .null, a.2.leave) := by
  have he' : σ.enter.errorIndicator = false := he
  have hr : ensureToken σ.enter = (true, σ.enter) := ensureToken_at σ.enter hlt
  have hp : rulePrologue id (ruleOf id) σ =
      (.inr (σ.mark, ((σ.tokenAt σ.mark).lineno, (σ.tokenAt σ.mark).colOffset)), σ.enter) := by
    simp only [rulePrologue, addLevel_ok σ hl, he', h3, Bool.false_eq_true, ↓reduceIte,
      ruleStart, h5, startLocation, hr, Bool.not_true]
    rfl
  simp only [ruleBody, hp, h4]
  have hg : (RuleKind.normal == RuleKind.gather) = false := rfl
  simp only [hg, h3, Bool.false_eq_true, ↓reduceIte]
  split <;> simp_all [retLevel_eq]

/-- What a round needs of the state it runs from: the seed `v`, ending at `e`, is the memo entry
for rule `id` at `mark`; the token at `mark` is read; the recursive call is below `MAXSTACK`. -/
structure Seeded (id mark : Nat) (v : Ast) (e : Nat) (S : PS) : Prop where
  find : (S.memo.getD mark []).find? (fun x => x.1 == 1000 + id) = some (1000 + id, v, e)
  lt : mark < S.fill
  level : S.level ≠ MAXSTACK

/-- The seed survives a token read that did not fail: `_PyPegen_expect_token` touches neither the
memo at an earlier position nor `p->level`. -/
theorem Seeded.after_expect {id mark e ty : Nat} {v x : Ast} {S s2 : PS} (hS : Seeded id mark v e S)
    (h : expectToken ty S = (x, s2)) (he : s2.errorIndicator = false) (hm : S.mark ≤ S.fill) :
    Seeded id mark v e { s2 with mark := mark } := by
  obtain ⟨g, mem, _⟩ := expectToken_step ty S
  rw [h] at g mem
  have hlev : s2.level = S.level := by
    rw [expectToken_eq] at h
    rcases hE : ensureToken S with ⟨b, T⟩
    rw [hE] at h
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases h
      have := ensureToken_ei S (by rw [hE])
      rw [hE] at this
      simp_all
    · obtain ⟨c, -, -, -⟩ := ensureToken_ok hm hE
      simp only [↓reduceIte, takeToken] at h
      split at h <;> (cases h; first | exact c.level | exact c.level)
  exact ⟨by rw [show ({ s2 with mark := mark } : PS).memo = s2.memo from rfl, mem]; exact hS.find,
    Nat.lt_of_lt_of_le hS.lt g.toks.le, by rw [show ({ s2 with mark := mark } : PS).level = s2.level from rfl, hlev]; exact hS.level⟩

/-! ### `sum` -/

/-- One round of `sum_raw` (`Grammar/python.gram:842-845`):
```
    | a=sum '+' b=term { _PyAST_BinOp(a, Add, b, EXTRA) }
    | a=sum '-' b=term { _PyAST_BinOp(a, Sub, b, EXTRA) }
    | term
```
run from a state `σ` at the start mark whose memo holds seed `v` for `sum`, ending at `e`
(what `_PyPegen_update_memo` left; `updateMemo_find`). The recursive `sum` returns the
seed and resumes at its end:
* with no seed yet (the first round), both operator alternatives fail and the round is `term`;
* with a seed and `+` after it, `BinOp(v, Add, b)` with `b` the `term` after the operator, the
  seed on the left;
* with `-` instead, the first alternative fails at `+`, the mark goes back, the second finds the
  seed again and gives `BinOp(v, Sub, b)`;
* with neither, the round is `term` from the start mark again (which does not grow, and ends the
  loop).
Hypotheses: the token at the start mark is read, the seed ends within the tokens read, and the
round and its recursive call are below `MAXSTACK`. -/
def SumStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1139) = some (1139, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → ∀ (b : Ast) (s2 : PS), callRule (f + 1) 140 σ.enter = (b, s2) → b ≠ .null →
    ruleBody (f + 7) 139 (ruleOf 139) σ = (b, s2.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 : PS), expectToken 14 u = (.tok to, s2) →
    callRule (f + 1) 140 s2 = (b, s3) → b ≠ .null → s3.errorIndicator = false →
    ruleBody (f + 7) 139 (ruleOf 139) σ = (mkAt .BinOp [v, opNode .Add, b] (extraLoc t s3), s3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 s4 : PS), expectToken 14 u = (.null, s2) →
    s2.errorIndicator = false → expectToken 15 { s2 with mark := e } = (.tok to, s3) →
    callRule f 140 s3 = (b, s4) → b ≠ .null → s4.errorIndicator = false →
    ruleBody (f + 7) 139 (ruleOf 139) σ = (mkAt .BinOp [v, opNode .Sub, b] (extraLoc t s4), s4.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (s2 s3 s4 : PS), expectToken 14 u = (.null, s2) →
    s2.errorIndicator = false → expectToken 15 { s2 with mark := e } = (.null, s3) →
    s3.errorIndicator = false → callRule (f + 1) 140 { s3 with mark := σ.mark } = (b, s4) →
    b ≠ .null → ruleBody (f + 7) 139 (ruleOf 139) σ = (b, s4.leave))

theorem sumStep_proven : SumStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 139 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 139 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 139) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 139 = r139 from rfl, r139]
  refine ⟨fun hv b s2 h2 hb => ?_, fun hv b to s2 s3 h2 h3 hb h3e => ?_,
    fun hv b to s2 s3 s4 h2 h2e h3 h4 hb h4e => ?_, fun hv b s2 s3 s4 h2 h2e h3 h3e h4 hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, PS.enter]
  · have hSu : Seeded 139 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS2 : Seeded 139 σ.mark v e { s2 with mark := σ.mark } := hSu.after_expect h2 h2e hef
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call (by rw [call_tok, h3]) (by simp),
        items_call (by rw [call_rule, h4]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h4e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, PS.enter]
  · have hSu : Seeded 139 σ.mark v e { σ.enter with mark := e } := ⟨hf, hlt, hS.level⟩
    have hS2 : Seeded 139 σ.mark v e { s2 with mark := σ.mark } := hSu.after_expect h2 h2e hef
    rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, h2])]),
      alts_fail (by rfl) (E s2 h2e) (by
      dsimp only
      rw [items_call (hit _ _ hS2 rfl) hv, items_call_null (by rw [call_tok, h3])]),
      alts_ok (by rfl) (E s3 h3e) (by
        dsimp only; rw [items_call (by rw [call_rule, h4]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-! ### `bitwise_or` -/

/-- One round of `bitwise_or_raw` (`Grammar/python.gram:821-823`):
```
    | a=bitwise_or '|' b=bitwise_xor { _PyAST_BinOp(a, BitOr, b, EXTRA) }
    | bitwise_xor
```
As `SumStep` with one operator: no seed, the round is `bitwise_xor`; a seed and `|` after it,
`BinOp(v, BitOr, b)`; a seed and anything else, `bitwise_xor` from the start mark. -/
def BitwiseOrStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1135) = some (1135, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → ∀ (b : Ast) (s2 : PS), callRule (f + 1) 136 σ.enter = (b, s2) → b ≠ .null →
    ruleBody (f + 6) 135 (ruleOf 135) σ = (b, s2.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 : PS), expectToken 18 u = (.tok to, s2) →
    callRule f 136 s2 = (b, s3) → b ≠ .null → s3.errorIndicator = false →
    ruleBody (f + 6) 135 (ruleOf 135) σ = (mkAt .BinOp [v, opNode .BitOr, b] (extraLoc t s3), s3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (s2 s3 : PS), expectToken 18 u = (.null, s2) →
    s2.errorIndicator = false → callRule (f + 1) 136 { s2 with mark := σ.mark } = (b, s3) →
    b ≠ .null → ruleBody (f + 6) 135 (ruleOf 135) σ = (b, s3.leave))

theorem bitwiseOrStep_proven : BitwiseOrStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 135 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 135 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 135) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 135 = r135 from rfl, r135]
  refine ⟨fun hv b s2 h2 hb => ?_, fun hv b to s2 s3 h2 h3 hb h3e => ?_,
    fun hv b s2 s3 h2 h2e h3 hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, PS.enter]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-! ### `bitwise_xor`, `bitwise_and` -/

/-- One round of `bitwise_xor_raw` (`Grammar/python.gram:825-827`):
```
    | a=bitwise_xor '^' b=bitwise_and { _PyAST_BinOp(a, BitXor, b, EXTRA) }
    | bitwise_and
```
As `BitwiseOrStep`: no seed, the round is the operand rule; a seed and the operator after it,
`BinOp(v, BitXor, b)`, the seed on the left; a seed and anything else, the operand rule from
the start mark. -/
def BitwiseXorStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1136) = some (1136, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → ∀ (b : Ast) (s2 : PS), callRule (f + 1) 137 σ.enter = (b, s2) → b ≠ .null →
    ruleBody (f + 6) 136 (ruleOf 136) σ = (b, s2.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 : PS), expectToken 32 u = (.tok to, s2) →
    callRule f 137 s2 = (b, s3) → b ≠ .null → s3.errorIndicator = false →
    ruleBody (f + 6) 136 (ruleOf 136) σ = (mkAt .BinOp [v, opNode .BitXor, b] (extraLoc t s3), s3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (s2 s3 : PS), expectToken 32 u = (.null, s2) →
    s2.errorIndicator = false → callRule (f + 1) 137 { s2 with mark := σ.mark } = (b, s3) →
    b ≠ .null → ruleBody (f + 6) 136 (ruleOf 136) σ = (b, s3.leave))

theorem bitwiseXorStep_proven : BitwiseXorStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 136 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 136 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 136) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 136 = r136 from rfl, r136]
  refine ⟨fun hv b s2 h2 hb => ?_, fun hv b to s2 s3 h2 h3 hb h3e => ?_,
    fun hv b s2 s3 h2 h2e h3 hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, PS.enter]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-- One round of `bitwise_and_raw` (`Grammar/python.gram:829-831`):
```
    | a=bitwise_and '&' b=shift_expr { _PyAST_BinOp(a, BitAnd, b, EXTRA) }
    | shift_expr
```
As `BitwiseOrStep`: no seed, the round is the operand rule; a seed and the operator after it,
`BinOp(v, BitAnd, b)`, the seed on the left; a seed and anything else, the operand rule from
the start mark. -/
def BitwiseAndStep : Prop := ∀ (f : Nat) (σ : PS) (v : Ast) (e : Nat),
  σ.errorIndicator = false → σ.level + 1 < MAXSTACK → σ.mark < σ.fill →
  (σ.memo.getD σ.mark []).find? (fun x => x.1 == 1137) = some (1137, v, e) → e ≤ σ.fill →
  let u : PS := { σ.enter with mark := e }
  let t := σ.tokenAt σ.mark
  (v = .null → ∀ (b : Ast) (s2 : PS), callRule (f + 1) 138 σ.enter = (b, s2) → b ≠ .null →
    ruleBody (f + 6) 137 (ruleOf 137) σ = (b, s2.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (to : Token) (s2 s3 : PS), expectToken 19 u = (.tok to, s2) →
    callRule f 138 s2 = (b, s3) → b ≠ .null → s3.errorIndicator = false →
    ruleBody (f + 6) 137 (ruleOf 137) σ = (mkAt .BinOp [v, opNode .BitAnd, b] (extraLoc t s3), s3.leave)) ∧
  (v ≠ .null → ∀ (b : Ast) (s2 s3 : PS), expectToken 19 u = (.null, s2) →
    s2.errorIndicator = false → callRule (f + 1) 138 { s2 with mark := σ.mark } = (b, s3) →
    b ≠ .null → ruleBody (f + 6) 137 (ruleOf 137) σ = (b, s3.leave))

theorem bitwiseAndStep_proven : BitwiseAndStep := by
  intro f σ v e he hlv hlt hf hef
  have hσl : σ.level ≠ MAXSTACK := by omega
  have he' : σ.enter.errorIndicator = false := he
  have hS : Seeded 137 σ.mark v e σ.enter := ⟨hf, hlt, by show σ.level + 1 ≠ MAXSTACK; omega⟩
  have hit : ∀ g (S : PS), Seeded 137 σ.mark v e S → S.mark = σ.mark →
      runCall (g + 2) (.rule 137) S = (v, { S with mark := e }) := by
    intro g S hS' hm
    rw [call_rule]
    exact callRule_leader_hit rfl rfl hS'.level (hm ▸ hS'.lt) (hm ▸ hS'.find)
  have E : ∀ x : PS, x.errorIndicator = false → ({ x with mark := σ.mark } : PS).errorIndicator = false :=
    fun x hx => hx
  have hσ : ({ ({ σ.enter with mark := e } : PS) with mark := σ.mark } : PS) = σ.enter := rfl
  rw [ruleBody_extra rfl rfl rfl he hσl hlt]
  simp only [show ruleOf 137 = r137 from rfl, r137]
  refine ⟨fun hv b s2 h2 hb => ?_, fun hv b to s2 s3 h2 h3 hb h3e => ?_,
    fun hv b s2 s3 h2 h2e h3 hb => ?_⟩
  · subst hv
    rw [alts_fail (by rfl) he' (items_call_null (hit _ _ hS rfl)), hσ,
      alts_ok (by rfl) he' (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call (by rw [call_tok, h2]) (by simp),
        items_call (by rw [call_rule, h3]) hb, items_nil]), altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull, PS.enter]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (hit _ _ hS rfl) hv, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (E s2 h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hb, items_nil]),
      altResult_none1 rfl rfl]
    rfl

/-! ### The rules as a whole -/

/-- The whole of a left-recursive leader (`sum`, `bitwise_or`, ...): its entry at a position with
no memo entry for it starts the seed loop with `NULL`, and the loop (`GrowSeedChain`) returns the
last seed that grew, at the mark it ended; with the rule's round theorem, each seed is
`BinOp(previous seed, op, operand)`, so the operators group to the left. -/
def LeaderLoop (id : Nat) : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + id) = none →
  ∀ (n : Nat) (vs : Nat → Ast) (ss : Nat → PS) (w : Ast) (s' : PS), vs 0 = .null → ss 0 = q →
  (∀ i, i < n →
    ruleBody (f + (n - i)) id (ruleOf id)
        { (updateMemo p.mark (1000 + id) (vs i) (ss i)).2 with mark := p.mark } =
      (vs (i + 1), ss (i + 1)) ∧
    (ss (i + 1)).errorIndicator = false ∧ vs (i + 1) ≠ .null ∧ (ss i).mark < (ss (i + 1)).mark) →
  ruleBody f id (ruleOf id) { (updateMemo p.mark (1000 + id) (vs n) (ss n)).2 with mark := p.mark } =
    (w, s') →
  (s'.errorIndicator = false → (w = .null ∨ s'.mark ≤ (ss n).mark) →
    callRule (f + n + 2) id p = (vs n, { s' with mark := (ss n).mark }.leave)) ∧
  (s'.errorIndicator = true → callRule (f + n + 2) id p = (.null, s'.leave))

theorem leaderLoop_of {id : Nat} (h1 : (ruleOf id).leftRec = true) (h2 : (ruleOf id).leader = true) :
    LeaderLoop id := by
  intro f p q h hn n vs ss w s' h0 hs0 hstep hlast
  obtain ⟨-, -, -, -, hm, -, -⟩ := h.facts
  rw [callRule_leader h1 h2 h hn]
  have := growSeedChain_proven id (ruleOf id) p.mark n f vs ss w s' hstep hlast
  rw [h0, hs0, hm] at this
  rw [← h0, ← hs0]
  rw [h0, hs0]
  exact this

/-- `sum`: one round (`SumStep`) and the loop. -/
def SumRule : Prop := SumStep ∧ LeaderLoop 139
theorem sumRule_proven : SumRule := ⟨sumStep_proven, leaderLoop_of rfl rfl⟩

/-- `bitwise_or`: one round and the loop. -/
def BitwiseOrRule : Prop := BitwiseOrStep ∧ LeaderLoop 135
theorem bitwiseOrRule_proven : BitwiseOrRule := ⟨bitwiseOrStep_proven, leaderLoop_of rfl rfl⟩

/-- `bitwise_xor`: one round and the loop. -/
def BitwiseXorRule : Prop := BitwiseXorStep ∧ LeaderLoop 136
theorem bitwiseXorRule_proven : BitwiseXorRule := ⟨bitwiseXorStep_proven, leaderLoop_of rfl rfl⟩

/-- `bitwise_and`: one round and the loop. -/
def BitwiseAndRule : Prop := BitwiseAndStep ∧ LeaderLoop 137
theorem bitwiseAndRule_proven : BitwiseAndRule := ⟨bitwiseAndStep_proven, leaderLoop_of rfl rfl⟩

end PyLean.PyGrammar.Peg
