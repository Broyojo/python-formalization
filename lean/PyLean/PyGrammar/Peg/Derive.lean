import PyLean.PyGrammar.Peg.Frame

/-!
What a successful rule means, stated on the grammar data and nothing else. `RuleM ts id i j` says
that the tokens `ts i`, ..., `ts (j - 1)` are matched by one alternative of `ruleOf id`, item by
item, with sub-rules matched the same way. It is a declarative relation: no marks, no memo, no
fuel, no order of alternatives. A lookahead consumes nothing and is not checked, so this is an
over-approximation of PEG semantics, and `Sound.lean` proves the direction "parser success implies
a match".

Two constructors exist because of what the C does:
* `ItemsM.opt` takes a `CallM` even when the call returned `NULL`: an action returning `NULL` with
  no exception leaves `p->mark` advanced, and `(_opt_var = c(p), !p->error_indicator)` carries on
  from there.
* `ItemsM.optSoft`: `_PyPegen_soft_keyword_token` advances past a `NAME` that is not a soft keyword
  and then returns `NULL`, `Parser/pegen.c:597-612`.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

mutual
  /-- One call of an item consumes tokens `i` to `j`. -/
  inductive CallM (ts : Nat → Token) : Call → Nat → Nat → Prop
    | tok {t i : Nat} : (ts i).type = t → CallM ts (.tok t) i (i + 1)
    | name {i : Nat} : (ts i).type = TokKind.NAME.num → CallM ts .name i (i + 1)
    | number {i : Nat} : (ts i).type = TokKind.NUMBER.num → CallM ts .number i (i + 1)
    | string {i : Nat} : (ts i).type = TokKind.STRING.num → CallM ts .string i (i + 1)
    | softKeywordToken {i : Nat} : (ts i).type = TokKind.NAME.num →
        softKeywords.contains (ts i).bytes = true → CallM ts .softKeywordToken i (i + 1)
    | softKw {s : List Nat} {i : Nat} : (ts i).type = TokKind.NAME.num → (ts i).bytes = s →
        CallM ts (.softKw s) i (i + 1)
    | forcedTok {t : Nat} {s : String} {i : Nat} : (ts i).type = t →
        CallM ts (.forcedTok t s) i (i + 1)
    | forcedRule {r : Nat} {s : String} {i j : Nat} : RuleM ts r i j →
        CallM ts (.forcedRule r s) i j
    | rule {r i j : Nat} : RuleM ts r i j → CallM ts (.rule r) i j

  /-- The items of an alternative, in sequence. -/
  inductive ItemsM (ts : Nat → Token) : List Item → Nat → Nat → Prop
    | nil {i : Nat} : ItemsM ts [] i i
    | call {c : Call} {rest : List Item} {i k j : Nat} : CallM ts c i k → ItemsM ts rest k j →
        ItemsM ts (.call c :: rest) i j
    | opt {c : Call} {rest : List Item} {i k j : Nat} : CallM ts c i k → ItemsM ts rest k j →
        ItemsM ts (.opt c :: rest) i j
    | optSkip {c : Call} {rest : List Item} {i j : Nat} : ItemsM ts rest i j →
        ItemsM ts (.opt c :: rest) i j
    | optSoft {rest : List Item} {i j : Nat} : (ts i).type = TokKind.NAME.num →
        ItemsM ts rest (i + 1) j → ItemsM ts (.opt .softKeywordToken :: rest) i j
    | look {b : Bool} {c : Call} {rest : List Item} {i j : Nat} : ItemsM ts rest i j →
        ItemsM ts (.look b c :: rest) i j
    | cut {rest : List Item} {i j : Nat} : ItemsM ts rest i j → ItemsM ts (.cut :: rest) i j

  /-- Zero or more iterations of a loop rule's alternative. -/
  inductive LoopM (ts : Nat → Token) : Alt → Nat → Nat → Prop
    | done {a : Alt} {i : Nat} : LoopM ts a i i
    | step {a : Alt} {i k j : Nat} : ItemsM ts a.items i k → LoopM ts a k j → LoopM ts a i j

  /-- Rule `id` matches tokens `i` to `j`. -/
  inductive RuleM (ts : Nat → Token) : Nat → Nat → Nat → Prop
    | alt {id : Nat} {a : Alt} {i j : Nat} :
        ((ruleOf id).kind = .normal ∨ (ruleOf id).kind = .gather) → a ∈ (ruleOf id).alts →
        ItemsM ts a.items i j → RuleM ts id i j
    | loop0 {id i j : Nat} : (ruleOf id).kind = .loop0 →
        LoopM ts ((ruleOf id).alts.headD default) i j → RuleM ts id i j
    | loop1 {id i k j : Nat} : (ruleOf id).kind = .loop1 →
        ItemsM ts ((ruleOf id).alts.headD default).items i k →
        LoopM ts ((ruleOf id).alts.headD default) k j → RuleM ts id i j
end

/-- `ts` is the token stream of `q`. -/
def Agree (ts : Nat → Token) (q : PS) : Prop := ∀ i, i < q.fill → q.tokenAt i = ts i

theorem Agree.of_grows {ts : Nat → Token} {p q : PS} (g : Grows p q) (h : Agree ts q) :
    Agree ts p := fun i hi => (g.toks.same i hi).symm.trans (h i (Nat.lt_of_lt_of_le hi g.toks.le))

/-- What a rule function can end on: `NULL` with the mark back at its start, or a match. The match
may come with a `NULL` value, from an action returning `NULL`. -/
def RuleEnd (ts : Nat → Token) (id i m : Nat) (node : Ast) : Prop :=
  (node = .null ∧ m = i) ∨ RuleM ts id i m

/-- Every memo entry records a true fact. -/
def MemoOK (ts : Nat → Token) (p : PS) : Prop :=
  ∀ (i id : Nat) (node : Ast) (m : Nat), (1000 + id, node, m) ∈ p.memo.getD i [] →
    m ≤ p.fill ∧ RuleEnd ts id i m node

/-- The invariant of a parse: the mark is within the tokens read, and the memo is sound. -/
structure Inv (ts : Nat → Token) (p : PS) : Prop where
  mark : p.mark ≤ p.fill
  memo : MemoOK ts p

/-- The shape of every statement below. Tokens grow and `error_indicator` is never cleared,
unconditionally; and if the run ends with no error, on the token stream `ts`, then the invariant
is preserved and `R` holds. -/
structure Spec (ts : Nat → Token) (p q : PS) (R : Prop) : Prop where
  grows : Grows p q
  post : Agree ts q → q.errorIndicator = false → Inv ts p → Inv ts q ∧ R

theorem Spec.seq {ts : Nat → Token} {p p1 q : PS} {R1 R2 R : Prop} (s1 : Spec ts p p1 R1)
    (s2 : Spec ts p1 q R2) (k : R1 → R2 → R) : Spec ts p q R :=
  ⟨s1.grows.trans s2.grows, fun ha he hi =>
    let e1 := s2.grows.err_false he
    let a1 := Agree.of_grows s2.grows ha
    let r1 := s1.post a1 e1 hi
    let r2 := s2.post ha he r1.1
    ⟨r2.1, k r1.2 r2.2⟩⟩

theorem Spec.weaken {ts : Nat → Token} {p q : PS} {R R' : Prop} (s : Spec ts p q R) (k : R → R') :
    Spec ts p q R' :=
  ⟨s.grows, fun ha he hi => let r := s.post ha he hi; ⟨r.1, k r.2⟩⟩

/-- With `error_indicator` set at the end there is nothing to show but growth. -/
theorem Spec.ofError {ts : Nat → Token} {p q : PS} {R : Prop} (g : Grows p q)
    (e : q.errorIndicator = true) : Spec ts p q R :=
  ⟨g, fun _ he _ => by rw [e] at he; exact absurd he (by decide)⟩

theorem Inv.ofStep {ts : Nat → Token} {p q : PS} (s : Step p q) (h : Inv ts p) : Inv ts q := by
  refine ⟨?_, fun i id node m hm => ?_⟩
  · rw [s.mark]
    exact Nat.le_trans h.mark s.grows.toks.le
  · rw [s.memo i] at hm
    have := h.memo i id node m hm
    exact ⟨Nat.le_trans this.1 s.grows.toks.le, this.2⟩

theorem Spec.ofStep {ts : Nat → Token} {p q : PS} (s : Step p q) : Spec ts p q True :=
  ⟨s.grows, fun _ _ hi => ⟨Inv.ofStep s hi, trivial⟩⟩

/-- Putting the mark back. -/
theorem Spec.setMark {ts : Nat → Token} {p p1 : PS} {R : Prop} (s : Spec ts p p1 R) (m : Nat)
    (hm : Inv ts p → Inv ts p1 → m ≤ p1.fill) : Spec ts p { p1 with mark := m } R :=
  ⟨⟨⟨s.grows.toks.le, s.grows.toks.same⟩, s.grows.err⟩, fun ha he hi =>
    let r := s.post ha he hi
    ⟨⟨hm hi r.1, r.1.memo⟩, r.2⟩⟩

theorem spec_frame {α : Type} {ts : Nat → Token} {f : PM α} (h : Frame f) (p : PS) :
    Spec ts p (f p).2 True := Spec.ofStep (h p)

/-! ### Reading tokens -/

theorem ensureToken_ei (p : PS) (h : (ensureToken p).1 = false) :
    (ensureToken p).2.errorIndicator = true := by
  rw [ensureToken_eq] at h ⊢
  split at h
  · split at h
    · simp only [*, ↓reduceIte]
    · simp at h
  · simp at h

theorem ensureToken_lt (p : PS) (hm : p.mark ≤ p.fill) (h : (ensureToken p).1 = true) :
    p.mark < (ensureToken p).2.fill := by
  have hs := frame_ensureToken p
  by_cases he : p.mark = p.fill
  · have hb : (p.mark == p.fill) = true := by simpa using he
    have hg := (fillToken_proven p).2.1
    rw [ensureToken_eq] at h ⊢
    simp only [hb, ↓reduceIte] at h ⊢
    split at h
    · simp at h
    · rename_i hf
      simp only [hf, ↓reduceIte]
      omega
  · exact Nat.lt_of_lt_of_le (by omega) hs.grows.toks.le

/-- What happens at the token under the mark, for any reader that takes at most that token. -/
structure TokRead (ts : Nat → Token) (p q : PS) (v : Ast) (Good : Token → Prop) : Prop where
  spec : Spec ts p q True
  out : q.errorIndicator = false → p.mark ≤ p.fill →
    (v = .null ∧ q.mark = p.mark) ∨
    (nonNull v = true ∧ q.mark = p.mark + 1 ∧ p.mark < q.fill ∧ Good (q.tokenAt p.mark))

/-- `_PyPegen_expect_token`, for the proof: a token of the right type or nothing. -/
theorem expectToken_step (ty : Nat) (p : PS) :
    Grows p (expectToken ty p).2 ∧
    (∀ i, (expectToken ty p).2.memo.getD i [] = p.memo.getD i []) ∧
    ((expectToken ty p).2.errorIndicator = false → p.mark ≤ p.fill →
      ((expectToken ty p).1 = .null ∧ (expectToken ty p).2.mark = p.mark) ∨
      (∃ t : Token, (expectToken ty p).1 = .tok t ∧ (expectToken ty p).2.mark = p.mark + 1 ∧
        p.mark < (expectToken ty p).2.fill ∧ (expectToken ty p).2.tokenAt p.mark = t ∧
        t.type = ty)) := by
  have hs := frame_ensureToken p
  rw [expectToken_eq]
  generalize he : ensureToken p = r at hs
  obtain ⟨ok, s⟩ := r
  dsimp only at hs ⊢
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨hs.grows, hs.memo, fun _ _ => Or.inl ⟨trivial, hs.mark⟩⟩
  | true =>
    simp only [↓reduceIte, takeToken]
    by_cases ht : ((s.tokenAt s.mark).type != ty) = true
    · simp only [ht, ↓reduceIte]
      exact ⟨hs.grows, hs.memo, fun _ _ => Or.inl ⟨trivial, hs.mark⟩⟩
    · simp only [ht, Bool.false_eq_true, ↓reduceIte]
      have hty : (s.tokenAt s.mark).type = ty := by simpa using ht
      refine ⟨⟨⟨hs.grows.toks.le, hs.grows.toks.same⟩, hs.grows.err⟩, hs.memo, fun _ hm => ?_⟩
      have hlt : p.mark < s.fill := by
        have := ensureToken_lt p hm (by rw [he])
        rwa [he] at this
      refine Or.inr ⟨_, rfl, ?_, hlt, ?_, hty⟩
      · show s.mark + 1 = p.mark + 1
        rw [hs.mark]
      · show s.tokenAt p.mark = s.tokenAt s.mark
        rw [hs.mark]

end PyLean.PyGrammar.Peg
