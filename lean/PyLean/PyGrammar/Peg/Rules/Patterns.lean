import PyLean.PyGrammar.Peg.Rules.Imports

/-! The pattern rules under `match_stmt` (`Grammar/python.gram:492-611`), rule by rule. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Ordered choice of rules -/

/-- PEG ordered choice over rule calls, each from the start mark `m`, as `Parser/parser.c` emits it
for alternatives that are one rule call with the default action: with `error_indicator` set no
further alternative runs (error return); otherwise the first non-`NULL` result is the rule's,
and a `NULL` one puts the mark back and tries the next; past the last, `_res = NULL`. The `i`-th
call gets `g` plus the number of rules after it as fuel. -/
def choiceRes (g m : Nat) : List Nat → PS → Option Ast × PS
  | [], s => (some .null, s)
  | r :: rest, s =>
    if s.errorIndicator then (none, s) else
    let c := callRule (g + rest.length) r s
    if nonNull c.1 then (some c.1, c.2) else choiceRes g m rest { c.2 with mark := m }

/-- An alternative that is one rule call with the default action. -/
def choiceAlt (r : Nat) : Alt :=
  { items := [.call (.rule r)], action := none, nvars := 1, guardInvalid := false, extra := false }

theorem choice_run (g m : Nat) (st : Int × Int) :
    ∀ (rs : List Nat) (s : PS), runAlts (g + rs.length + 2) (rs.map choiceAlt) false m st s =
      choiceRes g m rs s
  | [], s => by simp only [List.map, List.length, Nat.add_zero]; rw [alts_nil]; rfl
  | r :: rest, s => by
    have ih := choice_run g m st rest
    cases he : s.errorIndicator with
    | true =>
      simp only [List.map, List.length]
      rw [show g + (rest.length + 1) + 2 = (g + rest.length + 2) + 1 from by omega,
        alts_err (by rfl) he]
      simp [choiceRes, he]
    | false =>
      simp only [List.map, List.length]
      rw [show g + (rest.length + 1) + 2 = (g + rest.length + 2) + 1 from by omega]
      generalize hc : callRule (g + rest.length) r s = c
      obtain ⟨v, s'⟩ := c
      cases v with
      | null =>
        rw [alts_fail (by rfl) he (by
          show runItems (g + rest.length + 1 + 1) [.call (.rule r)] #[] false s = _
          rw [items_call_null (by rw [call_rule, hc])]), ih]
        simp [choiceRes, he, hc, nonNull]
      | _ =>
        rw [alts_ok (by rfl) he (by
          show runItems (g + rest.length + 1 + 1) [.call (.rule r)] #[] false s = _
          rw [items_call (by rw [call_rule, hc]) (by simp), items_nil]), altResult_none1 rfl rfl]
        simp [choiceRes, he, hc, nonNull]

/-! ### `closed_pattern`, `pattern`, `maybe_star_pattern` -/

/-- `closed_pattern (memo)` (`Grammar/python.gram:522-530`):
```
    | literal_pattern | capture_pattern | wildcard_pattern | value_pattern
    | group_pattern | sequence_pattern | mapping_pattern | class_pattern
```
the ordered choice (`choiceRes`) of those eight rules (74, 81, 83, 84, 87, 88, 93, 97) in this
order, from the start mark, memoized at the start mark (`NULL` included, an error return not). So
`case x:` is a capture (capture before value), `case _:` a wildcard (`capture_pattern` refuses
`_`), `case (a):` a group (group before sequence). -/
def ClosedPattern : Prop := ∀ (g : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1000 + 73) = none →
  callRule (g + 12) 73 p = memoDone p.mark 73 (choiceRes g p.mark [74, 81, 83, 84, 87, 88, 93, 97] q)

theorem closedPattern_proven : ClosedPattern := by
  intro g p q h hn
  rw [callRule_memo_plain rfl rfl rfl rfl rfl h hn]
  have := choice_run g p.mark (0, 0) [74, 81, 83, 84, 87, 88, 93, 97] q
  simp only [List.length, List.map, choiceAlt] at this
  simp only [show ruleOf 73 = r73 from rfl, r73]
  rw [← this]

/-- `pattern: as_pattern | or_pattern` (`Grammar/python.gram:509-511`): the ordered choice of
`as_pattern` (71) then `or_pattern` (72). -/
def PatternRule : Prop := ∀ (g : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (g + 6) 70 p =
    let a := choiceRes g p.mark [71, 72] p.enter
    (a.1.getD .null, a.2.leave)

theorem patternRule_proven : PatternRule := by
  intro g p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  have := choice_run g p.mark (0, 0) [71, 72] p.enter
  simp only [List.length, List.map, choiceAlt] at this
  simp only [show ruleOf 70 = r70 from rfl, r70]
  rw [← this]

/-- `maybe_star_pattern: star_pattern | pattern` (`Grammar/python.gram:607-609`): the ordered
choice of `star_pattern` (92) then `pattern` (70). -/
def MaybeStarPattern : Prop := ∀ (g : Nat) (p : PS), p.errorIndicator = false → p.level ≠ MAXSTACK →
  callRule (g + 6) 91 p =
    let a := choiceRes g p.mark [92, 70] p.enter
    (a.1.getD .null, a.2.leave)

theorem maybeStarPattern_proven : MaybeStarPattern := by
  intro g p he hl
  rw [callRule_plain rfl rfl rfl rfl rfl he hl]
  have := choice_run g p.mark (0, 0) [92, 70] p.enter
  simp only [List.length, List.map, choiceAlt] at this
  simp only [show ruleOf 91 = r91 from rfl, r91]
  rw [← this]

/-! ### `or_pattern`, `capture_pattern`, `wildcard_pattern` -/

theorem ast_beq_int (a b : Int) : (Ast.int a == Ast.int b) = (a == b) := rfl

/-- `or_pattern` (`Grammar/python.gram:518-520`):
```
    | patterns[asdl_pattern_seq*]='|'.closed_pattern+ {
        asdl_seq_LEN(patterns) == 1 ? asdl_seq_GET(patterns, 0) : _PyAST_MatchOr(patterns, EXTRA) }
```
The `'|'.closed_pattern+` gather (`_gather_40`) with one element gives that element itself, with
more `MatchOr(patterns)`; no gather gives `NULL`. -/
def OrPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (xs y : Ast) (s : PS), callRule f 317 q = (xs, s) → xs ≠ .null → s.errorIndicator = false →
    seqOf xs = [y] → y ≠ .null → callRule (f + 5) 72 p = (y, s.leave)) ∧
  (∀ (xs : Ast) (s : PS), callRule f 317 q = (xs, s) → xs ≠ .null → s.errorIndicator = false →
    (seqOf xs).length ≠ 1 → callRule (f + 5) 72 p = (mkAt .MatchOr [xs] (extraLoc t s), s.leave)) ∧
  (∀ (s : PS), callRule f 317 q = (.null, s) →
    callRule (f + 5) 72 p = (.null, { s with mark := p.mark }.leave))

theorem orPattern_proven : OrPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 72 = r72 from rfl, r72]
  refine ⟨fun xs y s h1 hx h1e hy hyn => ?_, fun xs s h1 hx h1e hl => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hx, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, hy, h1e,
      Bool.or_false, List.length, ast_beq_int]
    have hny : nonNull y = true := by cases y <;> simp_all [nonNull]
    simp [nonNull, h1e, truth, StateT.pure, StateT.bind, pure, bind, hny, hy]
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hx, items_nil]),
      altResult_extra rfl rfl]
    have hne : (((seqOf xs).length : Int) == 1) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, callHelper, h1e,
      Bool.or_false, ast_beq_int, hne]
    simp [nonNull, h1e, mkAst, mkAt, extraLoc, locArgs, mkExtra, truth, StateT.pure, StateT.bind,
      pure, bind, hne]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `capture_pattern: target=pattern_capture_target { _PyAST_MatchAs(NULL, target->v.Name.id,
EXTRA) }` (`Grammar/python.gram:572-573`): `MatchAs(NULL, name)` from `pattern_capture_target`'s
`Name`; `NULL` without it. -/
def CapturePattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a : Ast) (s : PS), callRule f 82 q = (a, s) → a ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 81 p = (mkAt .MatchAs [.null, fieldOf a "id"] (extraLoc t s), s.leave)) ∧
  (∀ (s : PS), callRule f 82 q = (.null, s) →
    callRule (f + 5) 81 p = (.null, { s with mark := p.mark }.leave))

theorem capturePattern_proven : CapturePattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 81 = r81 from rfl, r81]
  refine ⟨fun a s h1 ha h1e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) ha, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h1e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl

/-- `wildcard_pattern: "_" { _PyAST_MatchAs(NULL, NULL, EXTRA) }` (`Grammar/python.gram:579-580`):
the soft keyword `_` (`_PyPegen_expect_soft_keyword(p, "_")`) gives `MatchAs(NULL, NULL)`; `NULL`
without it. -/
def WildcardPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (x : Ast) (s : PS), expectSoftKeyword [95] q = (x, s) → x ≠ .null → s.errorIndicator = false →
    callRule (f + 5) 83 p = (mkAt .MatchAs [.null, .null] (extraLoc t s), s.leave)) ∧
  (∀ (s : PS), expectSoftKeyword [95] q = (.null, s) →
    callRule (f + 5) 83 p = (.null, { s with mark := p.mark }.leave))

theorem wildcardPattern_proven : WildcardPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 83 = r83 from rfl, r83]
  refine ⟨fun x s h1 hx h1e => ?_, fun s h1 => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_softKw, h1]) hx, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h1e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_softKw, h1])]), alts_nil]
    rfl

/-! ### `group_pattern`, `sequence_pattern`, `patterns`, `subject_expr` -/

/-- `group_pattern: '(' pattern=pattern ')' { pattern }` (`Grammar/python.gram:593-594`): at `(`
(7), `pattern` and `)` give the inner pattern itself; at any other token, or without the inner
pattern, `NULL` with the mark back. -/
def GroupPattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 7 → ∀ (a : Ast) (c : Token) (s1 s2 : PS), callRule (f + 1) 70 { q with mark := p.mark + 1 } = (a, s1) →
    a ≠ .null → expectToken 8 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 7) 87 p = (a, s2.leave)) ∧
  (t.type = 7 → ∀ (s1 : PS), callRule (f + 1) 70 { q with mark := p.mark + 1 } = (.null, s1) →
    callRule (f + 7) 87 p = (.null, { s1 with mark := p.mark }.leave)) ∧
  (t.type ≠ 7 → callRule (f + 7) 87 p = (.null, q.leave))

theorem groupPattern_proven : GroupPattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have he' : p.enter.errorIndicator = false := h.ei
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  rw [callRule_plain rfl rfl rfl rfl rfl h.ei h.level]
  simp only [show ruleOf 87 = r87 from rfl, r87]
  refine ⟨fun ht a c s1 s2 h1 ha h2 h2e => ?_, fun ht s1 h1 => ?_, fun ht => ?_⟩
  · rw [alts_ok (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp), items_nil]),
      altResult_plain rfl rfl]
    simp only [evalA, pure, StateT.pure, h2e, Bool.or_false]
    cases a <;> simp_all [nonNull]
  · rw [alts_fail (by rfl) he' (by
      dsimp only
      rw [items_call (by rw [call_tok, expect_entered h, ite_t ht]) (by simp),
        items_call_null (by rw [call_rule, h1])]), alts_nil]
    rfl
  · rw [alts_fail (by rfl) he' (by
      dsimp only; rw [items_call_null (by rw [call_tok, expect_entered h, ite_f ht])]), hq, alts_nil]
    rfl

/-- `sequence_pattern` (`Grammar/python.gram:596-598`):
```
    | '[' patterns=maybe_sequence_pattern? ']' { _PyAST_MatchSequence(patterns, EXTRA) }
    | '(' patterns=open_sequence_pattern? ')' { _PyAST_MatchSequence(patterns, EXTRA) }
```
At `[`, the optional `maybe_sequence_pattern` and `]` give `MatchSequence(patterns)`; at `(`, the
first alternative fails at its first token and the optional `open_sequence_pattern` and `)` give
`MatchSequence(patterns)` (so `()` and `[]` are empty sequences, `(a,)` one element); at any other
token `NULL` with the mark back. -/
def SequencePattern : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (t.type = 9 → ∀ (ps : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 2) 90 { q with mark := p.mark + 1 } = (ps, s1) → s1.errorIndicator = false →
    expectToken 10 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 8) 88 p = (mkAt .MatchSequence [ps] (extraLoc t s2), s2.leave)) ∧
  (t.type = 7 → ∀ (ps : Ast) (c : Token) (s1 s2 : PS),
    callRule (f + 1) 89 { q with mark := p.mark + 1 } = (ps, s1) → s1.errorIndicator = false →
    expectToken 8 s1 = (.tok c, s2) → s2.errorIndicator = false →
    callRule (f + 8) 88 p = (mkAt .MatchSequence [ps] (extraLoc t s2), s2.leave)) ∧
  (t.type ≠ 9 → t.type ≠ 7 → callRule (f + 8) 88 p = (.null, q.leave))

theorem sequencePattern_proven : SequencePattern := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  have hlt' : q.mark < q.fill := hm ▸ hlt
  have hq : { q with mark := p.mark } = q := by rw [← hm]
  have ek : ∀ ty g, runCall (g + 1) (.tok ty) q = if (q.tokenAt p.mark).type = ty then
      (.tok (q.tokenAt p.mark), { q with mark := p.mark + 1 }) else (.null, q) := by
    intro ty g
    rw [call_tok, expectToken_at _ _ hlt', hm]
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 88 = r88 from rfl, r88]
  refine ⟨fun ht ps c s1 s2 h1 h1e h2 h2e => ?_, fun ht ps c s1 s2 h1 h1e h2 h2e => ?_,
    fun h9 h7 => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call (by rw [call_tok, h2]) (by simp), items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f (by omega)])), hq,
      alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [ek, ite_t ht]) (by simp), items_opt (by rw [call_rule, h1]) h1e,
        items_call (by rw [call_tok, h2]) (by simp), items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h2e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f h9])), hq,
      alts_fail (by rfl) he (items_call_null (by rw [ek, ite_f h7])), hq, alts_nil]
    rfl

/-- `patterns` (`Grammar/python.gram:504-507`):
```
    | patterns[asdl_pattern_seq*]=open_sequence_pattern { _PyAST_MatchSequence(patterns, EXTRA) }
    | pattern
```
An `open_sequence_pattern` (a pattern and a `,` at least) gives `MatchSequence`, so `case a, b:`
is a sequence; without it (and no error), `pattern` from the start mark; an error in
`open_sequence_pattern` gives `NULL`. -/
def Patterns : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (ps : Ast) (s : PS), callRule (f + 1) 89 q = (ps, s) → ps ≠ .null → s.errorIndicator = false →
    callRule (f + 6) 69 p = (mkAt .MatchSequence [ps] (extraLoc t s), s.leave)) ∧
  (∀ (v : Ast) (s s2 : PS), callRule (f + 1) 89 q = (.null, s) → s.errorIndicator = false →
    callRule f 70 { s with mark := p.mark } = (v, s2) → v ≠ .null →
    callRule (f + 6) 69 p = (v, s2.leave)) ∧
  (∀ (s : PS), callRule (f + 1) 89 q = (.null, s) → s.errorIndicator = true →
    callRule (f + 6) 69 p = (.null, { s with mark := p.mark }.leave))

theorem patterns_proven : Patterns := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 69 = r69 from rfl, r69]
  refine ⟨fun ps s h1 hp h1e => ?_, fun v s s2 h1 h1e h2 hv => ?_, fun s h1 h1e => ?_⟩
  · rw [alts_ok (by rfl) he (by dsimp only; rw [items_call (by rw [call_rule, h1]) hp, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h1e,
      Bool.or_false, mkAt, extraLoc, locArgs]
    simp [mkAst, nonNull]
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hv, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_err (by rfl) (show ({ s with mark := p.mark } : PS).errorIndicator = true from h1e)]
    rfl

/-- `subject_expr` (`Grammar/python.gram:492-495`):
```
    | value=star_named_expression ',' values=star_named_expressions? {
        _PyAST_Tuple(CHECK(asdl_expr_seq*, _PyPegen_seq_insert_in_front(p, value, values)), Load, EXTRA) }
    | named_expression
```
A `star_named_expression` and `,` give `Tuple([value] + values, Load)` with the optional
`star_named_expressions` after (so `match a, *b:` matches a tuple); without the `,`, or without
the first expression (and no error), `named_expression` from the start mark. -/
def SubjectExpr : Prop := ∀ (f : Nat) (p q : PS), Entered p q →
  let t := q.tokenAt p.mark
  (∀ (a b : Ast) (c : Token) (s1 s2 s3 : PS), callRule (f + 2) 116 q = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.tok c, s2) → callRule f 114 s2 = (b, s3) → s3.errorIndicator = false →
    callRule (f + 7) 66 p = (mkAt .Tuple [.seq (a :: seqOf b), opNode .Load] (extraLoc t s3), s3.leave)) ∧
  (∀ (a n : Ast) (s1 s2 s3 : PS), callRule (f + 2) 116 q = (a, s1) → a ≠ .null →
    expectToken 12 s1 = (.null, s2) → s2.errorIndicator = false →
    callRule (f + 1) 119 { s2 with mark := p.mark } = (n, s3) → n ≠ .null →
    callRule (f + 7) 66 p = (n, s3.leave)) ∧
  (∀ (n : Ast) (s1 s2 : PS), callRule (f + 2) 116 q = (.null, s1) → s1.errorIndicator = false →
    callRule (f + 1) 119 { s1 with mark := p.mark } = (n, s2) → n ≠ .null →
    callRule (f + 7) 66 p = (n, s2.leave))

theorem subjectExpr_proven : SubjectExpr := by
  intro f p q h
  obtain ⟨he, -, -, -, hm, hlt, -⟩ := h.facts
  rw [callRule_extra rfl rfl rfl rfl rfl h]
  simp only [show ruleOf 66 = r66 from rfl, r66]
  refine ⟨fun a b c s1 s2 s3 h1 ha h2 h3 h3e => ?_, fun a n s1 s2 s3 h1 ha h2 h2e h3 hn => ?_,
    fun n s1 s2 h1 h1e h2 hn => ?_⟩
  · rw [alts_ok (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call (by rw [call_tok, h2]) (by simp),
        items_opt (by rw [call_rule, h3]) h3e, items_nil]),
      altResult_extra rfl rfl]
    simp only [evalA, evalA.evalList, bind, StateT.bind, pure, StateT.pure, mkExtra, h3e,
      Bool.or_false, mkAt, extraLoc, locArgs, callHelper]
    simp [mkAst, nonNull, h3e]
  · rw [alts_fail (by rfl) he (by
      dsimp only
      rw [items_call (by rw [call_rule, h1]) ha, items_call_null (by rw [call_tok, h2])]),
      alts_ok (by rfl) (show ({ s2 with mark := p.mark } : PS).errorIndicator = false from h2e) (by
        dsimp only; rw [items_call (by rw [call_rule, h3]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl
  · rw [alts_fail (by rfl) he (by dsimp only; rw [items_call_null (by rw [call_rule, h1])]),
      alts_ok (by rfl) (show ({ s1 with mark := p.mark } : PS).errorIndicator = false from h1e) (by
        dsimp only; rw [items_call (by rw [call_rule, h2]) hn, items_nil]),
      altResult_none1 rfl rfl]
    rfl

end PyLean.PyGrammar.Peg
