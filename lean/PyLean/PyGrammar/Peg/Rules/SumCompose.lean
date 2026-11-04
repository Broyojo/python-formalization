import PyLean.PyGrammar.Peg.Rules.LeftRec

/-! `a - b - c` from `sum`'s round theorem and its seed loop (`LeftRec.lean`): the two conjuncts of
`SumRule` composed for three operands. -/

namespace PyLean.PyGrammar.Peg

open Lexer

/-- What the state a round of `sum` ends in leaves for the next round: no error, `p->level` back
to the leader's (each rule function restores it), the start mark within the memo table and the
tokens read (`memo.size = fill`, the type invariant of `FillToken`), and the mark within the
tokens. -/
structure RoundOK (p s : PS) : Prop where
  ei : s.errorIndicator = false
  level : s.level = p.level + 1
  memo : p.mark < s.memo.size
  fill : p.mark < s.fill
  mark : s.mark ≤ s.fill

/-- The state a round of the seed loop runs from: the seed `v` stored at the start mark by
`_PyPegen_update_memo`, the mark back at the start. -/
abbrev seedState (p : PS) (v : Ast) (s : PS) : PS :=
  { (updateMemo p.mark 1139 v s).2 with mark := p.mark }

theorem seedState_pre {p s : PS} (v : Ast) (h : RoundOK p s) (hl : p.level + 2 < MAXSTACK) :
    (seedState p v s).errorIndicator = false ∧ (seedState p v s).level + 1 < MAXSTACK ∧
    (seedState p v s).mark < (seedState p v s).fill ∧
    ((seedState p v s).memo.getD (seedState p v s).mark []).find? (fun x => x.1 == 1139) =
      some (1139, v, s.mark) ∧ s.mark ≤ (seedState p v s).fill := by
  refine ⟨h.ei, ?_, h.fill, ?_, h.mark⟩
  · show s.level + 1 < MAXSTACK
    rw [h.level]
    omega
  · exact updateMemo_find s p.mark 1139 v h.memo

/-- `a - b - c` is `BinOp(BinOp(a, Sub, b), Sub, c)`: `sum` from entry (no memo entry yet at the
mark), with `term` giving `a` in the first round, then in each of two rounds `-` (after the `+`
alternative fails) and `term` giving `b`, then `c`, and in a last round neither operator (so
`term` from the start mark, which does not grow), returns the left-nested tree, at the mark after
`c`. Each round runs from `seedState`, the seed stored at the start mark, and its `term` calls get
what the round theorem (`SumStep`) gives them. Hypotheses: entry invariants; `RoundOK` for the
state each round ends in; each growing round ends further on; no error after the last. -/
def SumSubSub : Prop := ∀ (g : Nat) (p q : PS), Entered p q →
  (q.memo.getD p.mark []).find? (fun m => m.1 == 1139) = none → p.level + 2 < MAXSTACK →
  p.mark < q.memo.size →
  ∀ (a b c d : Ast) (to1 to2 : Token) (s1 x1 y1 z1 x2 y2 z2 x3 y3 w : PS),
  callRule (g + 4) 140 (seedState p .null q).enter = (a, s1) → a ≠ .null → RoundOK p s1.leave →
  q.mark < s1.mark →
  expectToken 14 { (seedState p a s1.leave).enter with mark := s1.mark } = (.null, x1) →
  x1.errorIndicator = false → expectToken 15 { x1 with mark := s1.mark } = (.tok to1, y1) →
  callRule (g + 2) 140 y1 = (b, z1) → b ≠ .null → RoundOK p z1.leave → s1.mark < z1.mark →
  let v2 := mkAt .BinOp [a, opNode .Sub, b] (extraLoc ((seedState p a s1.leave).tokenAt p.mark) z1)
  expectToken 14 { (seedState p v2 z1.leave).enter with mark := z1.mark } = (.null, x2) →
  x2.errorIndicator = false → expectToken 15 { x2 with mark := z1.mark } = (.tok to2, y2) →
  callRule (g + 1) 140 y2 = (c, z2) → c ≠ .null → RoundOK p z2.leave → z1.mark < z2.mark →
  let v3 := mkAt .BinOp [v2, opNode .Sub, c] (extraLoc ((seedState p v2 z1.leave).tokenAt p.mark) z2)
  expectToken 14 { (seedState p v3 z2.leave).enter with mark := z2.mark } = (.null, x3) →
  x3.errorIndicator = false → expectToken 15 { x3 with mark := z2.mark } = (.null, y3) →
  y3.errorIndicator = false → callRule (g + 1) 140 { y3 with mark := p.mark } = (d, w) → d ≠ .null →
  w.errorIndicator = false → w.mark ≤ z2.mark →
  callRule (g + 12) 139 p = (v3, { w.leave with mark := z2.mark }.leave)

theorem sumSubSub_proven : SumSubSub := by
  intro g p q h hn hl hqm a b c d to1 to2 s1 x1 y1 z1 x2 y2 z2 x3 y3 w h1 ha r1 g1 k1 k1e k2 k3 hb r2 g2
    v2 m1 m1e m2 m3 hc r3 g3 v3 n1 n1e n2 n2e n3 hd hwe hwm
  obtain ⟨he, hlev, -, -, hm, hlt, -⟩ := h.facts
  have r0 : RoundOK p q := ⟨he, hlev, hm ▸ hqm, hlt, by omega⟩
  have st := sumStep_proven
  let vs : Nat → Ast := fun i => match i with | 0 => .null | 1 => a | 2 => v2 | _ => v3
  let ss : Nat → PS := fun i => match i with | 0 => q | 1 => s1.leave | 2 => z1.leave | _ => z2.leave
  have loop := leaderLoop_of (id := 139) rfl rfl (g + 7) p q h hn 3 vs ss d w.leave rfl rfl
  have step0 : ruleBody (g + 7 + (3 - 0)) 139 (ruleOf 139) (seedState p .null q) = (a, s1.leave) := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := seedState_pre .null r0 hl
    have := (st (g + 3) (seedState p .null q) .null q.mark e1 e2 e3 e4 e5).1 rfl a s1 h1 ha
    simpa [show g + 7 + (3 - 0) = g + 3 + 7 from by omega] using this
  have step1 : ruleBody (g + 7 + (3 - 1)) 139 (ruleOf 139) (seedState p a s1.leave) = (v2, z1.leave) := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := seedState_pre a r1 hl
    have := (st (g + 2) (seedState p a s1.leave) a s1.leave.mark e1 e2 e3 e4 e5).2.2.1 ha b to1 x1 y1 z1
      k1 k1e k2 k3 hb r2.ei
    simpa [show g + 7 + (3 - 1) = g + 2 + 7 from by omega] using this
  have step2 : ruleBody (g + 7 + (3 - 2)) 139 (ruleOf 139) (seedState p v2 z1.leave) = (v3, z2.leave) := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := seedState_pre v2 r2 hl
    have hv2 : v2 ≠ .null := by simp [v2, mkAt, mkAst]
    have := (st (g + 1) (seedState p v2 z1.leave) v2 z1.leave.mark e1 e2 e3 e4 e5).2.2.1 hv2 c to2 x2 y2 z2
      m1 m1e m2 m3 hc r3.ei
    simpa [show g + 7 + (3 - 2) = g + 1 + 7 from by omega] using this
  have last : ruleBody (g + 7) 139 (ruleOf 139) (seedState p v3 z2.leave) = (d, w.leave) := by
    obtain ⟨e1, e2, e3, e4, e5⟩ := seedState_pre v3 r3 hl
    have hv3 : v3 ≠ .null := by simp [v3, mkAt, mkAst]
    exact (st g (seedState p v3 z2.leave) v3 z2.leave.mark e1 e2 e3 e4 e5).2.2.2 hv3 d x3 y3 w
      n1 n1e n2 n2e n3 hd
  have hv2 : v2 ≠ .null := by simp [v2, mkAt, mkAst]
  have hv3 : v3 ≠ .null := by simp [v3, mkAt, mkAst]
  have hstep : ∀ i, i < 3 →
      ruleBody (g + 7 + (3 - i)) 139 (ruleOf 139)
          { (updateMemo p.mark (1000 + 139) (vs i) (ss i)).2 with mark := p.mark } =
        (vs (i + 1), ss (i + 1)) ∧
      (ss (i + 1)).errorIndicator = false ∧ vs (i + 1) ≠ .null ∧ (ss i).mark < (ss (i + 1)).mark := by
    intro i hi
    match i, hi with
    | 0, _ => exact ⟨step0, r1.ei, ha, g1⟩
    | 1, _ => exact ⟨step1, r2.ei, hv2, g2⟩
    | 2, _ => exact ⟨step2, r3.ei, hv3, g3⟩
  have := (loop hstep last).1 hwe (Or.inr hwm)
  rw [show g + 12 = g + 7 + 3 + 2 from by omega]
  exact this

end PyLean.PyGrammar.Peg
