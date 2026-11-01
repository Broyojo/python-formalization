import PyLean.PyGrammar.Peg.Derive

/-!
Soundness of the parser against the grammar data: when `callRule` succeeds on rule `id`, the tokens
it consumed really are a match of `ruleOf id` in the sense of `RuleM`. `callRule` on the data of
`GrammarData.lean` is `Parser/parser.c`, as `gen/gen_grammar.py --check` confirms for the data, so
this ties the behaviour of every generated rule function to its grammar rule.

The proof is one induction on fuel over the seven mutually recursive functions. What makes it go:

* `Frame`: actions do not move the mark, tokens only grow, `error_indicator` is never cleared.
* `MemoOK`: every memo entry records a true match. This is what covers left recursion. A seed
  stored by `growSeed` is a derivation already built, and the next round of `ruleBody` extends it.
* The failure paths: an alternative that fails puts the mark back; a `NULL` from an action leaves
  the mark moved, which `RuleEnd` allows; and any path that sets `error_indicator` is excluded by
  the statement, which is about runs that end with no error.

Only the direction "success implies a match" is claimed. Lookaheads and the order of alternatives
are not reflected in `RuleM`, so this says nothing about which match PEG chooses.
-/

namespace PyLean.PyGrammar.Peg

open Lexer

/-! ### Frames of what the interpreter calls -/

theorem Step.setEI {p q : PS} (s : Step p q) : Step p { q with errorIndicator := true } :=
  ⟨s.mark, ⟨⟨s.grows.toks.le, s.grows.toks.same⟩, fun _ => rfl⟩, s.memo⟩

theorem frame_newIdentifier (b : List Nat) : Frame (newIdentifier b) := by
  unfold newIdentifier
  frame

theorem frame_nameFromToken (x : Ast) : Frame (nameFromToken x) := by
  intro p
  unfold nameFromToken
  dsimp only
  split
  · rename_i t
    have s := frame_newIdentifier t.bytes p
    split
    · exact s.setEI
    · exact s
  · exact Step.refl p

theorem nameFromToken_ei (t : Token) (s : PS) (h : (nameFromToken (.tok t) s).1 = .null) :
    (nameFromToken (.tok t) s).2.errorIndicator = true := by
  revert h
  simp only [nameFromToken]
  split
  · intro _
    rfl
  · intro h
    cases h

theorem frame_numberFromToken (x : Ast) : Frame (numberFromToken x) := by
  intro p
  unfold numberFromToken
  split
  · rename_i t
    split
    · exact (Step.setEI (Step.refl p)).trans (frame_raiseError0 _ _ _)
    · split
      · exact Step.refl p
      · exact (Step.setEI (Step.refl p)).trans (frame_raiseErrorKnownLocation _ _ _ _ _ _ _)
  · exact Step.refl p

theorem numberFromToken_ei (t : Token) (s : PS) (h : (numberFromToken (.tok t) s).1 = .null) :
    (numberFromToken (.tok t) s).2.errorIndicator = true := by
  revert h
  simp only [numberFromToken]
  split
  · intro _
    exact (frame_raiseError0 _ _ _).grows.err rfl
  · split
    · intro h
      cases h
    · intro _
      exact (frame_raiseErrorKnownLocation _ _ _ _ _ _ _).grows.err rfl

theorem frame_addLevel : Frame addLevel := by
  unfold addLevel
  frame

theorem frame_retLevel (v : Ast) : Frame (retLevel v) := by
  unfold retLevel subLevel
  frame

theorem frame_outOfFuel : Frame outOfFuel := by
  unfold outOfFuel
  frame

theorem outOfFuel_ei (p : PS) : (outOfFuel p).2.errorIndicator = true := rfl

macro_rules | `(tactic| frame_leaf) => `(tactic| with_reducible exact frame_evalA _ _ _)

theorem frame_altResult (a : Alt) (g : Bool) (env : Array Ast) (st : Int × Int) :
    Frame (altResult a g env st) := by
  unfold altResult
  frame

/-- A `none` from `g` comes with `error_indicator` set. -/
def NoneErr {α : Type} (g : PM (Option α)) : Prop :=
  ∀ s, (g s).1 = none → (g s).2.errorIndicator = true

theorem altResult_none (a : Alt) (g : Bool) (env : Array Ast) (st : Int × Int) :
    NoneErr (altResult a g env st) := by
  have hb : ∀ {α β : Type} {m : PM α} {k : α → PM (Option β)}, (∀ x, NoneErr (k x)) →
      NoneErr (m >>= k) := fun h s => h _ _
  have hp : ∀ {β : Type} (x : β), NoneErr (pure (some x) : PM (Option β)) := fun _ _ h => by
    cases h
  have hm : NoneErr (do
      modify fun p => { p with errorIndicator := true }
      return (none : Option Ast)) := fun _ _ => rfl
  unfold altResult
  repeat' (first
    | exact hp _
    | exact hm
    | refine hb (fun _ => ?_)
    | split
    | dsimp only)

/-! ### What a call ends on -/

/-- What a `NULL` from a call can leave behind: nothing moved, or a match whose action gave `NULL`,
or the non-soft `NAME` `_PyPegen_soft_keyword_token` steps over. -/
def NullEnd (ts : Nat → Token) (c : Call) (i k : Nat) : Prop :=
  k = i ∨ CallM ts c i k ∨ (c = .softKeywordToken ∧ (ts i).type = TokKind.NAME.num ∧ k = i + 1)

structure CallEnd (ts : Nat → Token) (c : Call) (i k : Nat) (v : Ast) : Prop where
  ok : nonNull v = true → CallM ts c i k
  nul : v = .null → NullEnd ts c i k

/-- A token read and nothing else, for `_PyPegen_name_token` and friends. -/
def TokEnd (ts : Nat → Token) (ty i k : Nat) (v : Ast) : Prop :=
  (v = .null ∧ k = i) ∨ (nonNull v = true ∧ k = i + 1 ∧ (ts i).type = ty)

theorem inv_of {ts : Nat → Token} {p q : PS} (g : Grows p q)
    (m : ∀ i, q.memo.getD i [] = p.memo.getD i []) (hm : q.mark ≤ q.fill) (hi : Inv ts p) :
    Inv ts q := by
  refine ⟨hm, fun i id node x hx => ?_⟩
  rw [m i] at hx
  have := hi.memo i id node x hx
  exact ⟨Nat.le_trans this.1 g.toks.le, this.2⟩

theorem expect_tok {ty : Nat} {p : PS} {t : Token} (h : (expectToken ty p).1 = .tok t)
    (he : (expectToken ty p).2.errorIndicator = false) (hm : p.mark ≤ p.fill) :
    (expectToken ty p).2.mark = p.mark + 1 ∧ p.mark < (expectToken ty p).2.fill ∧
      (expectToken ty p).2.tokenAt p.mark = t ∧ t.type = ty := by
  obtain ⟨_, _, o⟩ := expectToken_step ty p
  rcases o he hm with ⟨h1, _⟩ | ⟨u, h1, h2, h3, h4, h5⟩
  · rw [h] at h1
    cases h1
  · rw [h] at h1
    cases h1
    exact ⟨h2, h3, h4, h5⟩

theorem expect_nontok {ty : Nat} {p : PS} (h : ∀ t, (expectToken ty p).1 = .tok t → False)
    (he : (expectToken ty p).2.errorIndicator = false) (hm : p.mark ≤ p.fill) :
    (expectToken ty p).2.mark = p.mark := by
  obtain ⟨_, _, o⟩ := expectToken_step ty p
  rcases o he hm with ⟨_, h2⟩ | ⟨u, h1, _⟩
  · exact h2
  · exact (h u h1).elim

/-- `_PyPegen_expect_token` followed by a function of what it returned that reads no token: `NULL`
stays `NULL`, and a `NULL` from a token is an error. -/
theorem spec_after_expect (ts : Nat → Token) (ty : Nat) (k : Ast → PM Ast)
    (h0 : ∀ s, k .null s = (.null, s)) (hf : ∀ x, Frame (k x))
    (he : ∀ t s, (k (.tok t) s).1 = .null → (k (.tok t) s).2.errorIndicator = true) (p : PS) :
    Spec ts p (k (expectToken ty p).1 (expectToken ty p).2).2
      (TokEnd ts ty p.mark (k (expectToken ty p).1 (expectToken ty p).2).2.mark
        (k (expectToken ty p).1 (expectToken ty p).2).1) := by
  obtain ⟨g, m, o⟩ := expectToken_step ty p
  generalize expectToken ty p = e at g m o
  obtain ⟨v, st⟩ := e
  dsimp only at g m o ⊢
  have s := hf v st
  refine ⟨g.trans s.grows, fun ha hq hi => ?_⟩
  have he1 := s.grows.err_false hq
  rcases o he1 hi.mark with ⟨h1, h2⟩ | ⟨t, h1, h2, h3, h4, h5⟩
  · subst h1
    rw [h0]
    exact ⟨inv_of g m (by rw [h2]; exact Nat.le_trans hi.mark g.toks.le) hi, Or.inl ⟨rfl, h2⟩⟩
  · subst h1
    have hnn : nonNull (k (.tok t) st).1 = true := by
      cases hx : (k (.tok t) st).1 with
      | null =>
        have := he t st hx
        rw [this] at hq
        cases hq
      | _ => rfl
    have hmk : (k (.tok t) st).2.mark = p.mark + 1 := s.mark.trans h2
    have hfill : p.mark < (k (.tok t) st).2.fill := Nat.lt_of_lt_of_le h3 s.grows.toks.le
    refine ⟨inv_of (g.trans s.grows) (fun i => (s.memo i).trans (m i))
      (by rw [hmk]; exact hfill) hi, Or.inr ⟨hnn, hmk, ?_⟩⟩
    have := ha p.mark hfill
    rw [← this, s.grows.toks.same _ h3, h4]
    exact h5

theorem spec_of_tokEnd {ts : Nat → Token} {p q : PS} {ty : Nat} {c : Call} {v : Ast}
    (s : Spec ts p q (TokEnd ts ty p.mark q.mark v))
    (good : ∀ i, (ts i).type = ty → CallM ts c i (i + 1)) :
    Spec ts p q (CallEnd ts c p.mark q.mark v) :=
  s.weaken fun t => by
    rcases t with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · exact ⟨fun h => (by rw [h1] at h; cases h), fun _ => Or.inl h2⟩
    · refine ⟨fun _ => by rw [h2]; exact good _ h3, fun h => ?_⟩
      rw [h] at h1
      cases h1

theorem spec_expect (ts : Nat → Token) (ty : Nat) (p : PS) :
    Spec ts p (expectToken ty p).2
      (TokEnd ts ty p.mark (expectToken ty p).2.mark (expectToken ty p).1) := by
  obtain ⟨g, m, o⟩ := expectToken_step ty p
  refine ⟨g, fun ha he hi => ?_⟩
  rcases o he hi.mark with ⟨h1, h2⟩ | ⟨t, h1, h2, h3, h4, h5⟩
  · exact ⟨inv_of g m (by rw [h2]; exact Nat.le_trans hi.mark g.toks.le) hi, Or.inl ⟨h1, h2⟩⟩
  · refine ⟨inv_of g m (by rw [h2]; exact h3) hi, Or.inr ⟨by rw [h1]; rfl, h2, ?_⟩⟩
    rw [← ha p.mark h3, h4]
    exact h5

theorem spec_name (ts : Nat → Token) (p : PS) :
    Spec ts p (nameToken p).2 (TokEnd ts TokKind.NAME.num p.mark (nameToken p).2.mark
      (nameToken p).1) :=
  spec_after_expect ts TokKind.NAME.num nameFromToken (fun _ => rfl) frame_nameFromToken
    nameFromToken_ei p

theorem spec_number (ts : Nat → Token) (p : PS) :
    Spec ts p (numberToken p).2 (TokEnd ts TokKind.NUMBER.num p.mark (numberToken p).2.mark
      (numberToken p).1) :=
  spec_after_expect ts TokKind.NUMBER.num numberFromToken (fun _ => rfl) frame_numberFromToken
    numberFromToken_ei p

theorem spec_softKeywordToken (ts : Nat → Token) (p : PS) :
    Spec ts p (softKeywordToken p).2
      (CallEnd ts .softKeywordToken p.mark (softKeywordToken p).2.mark (softKeywordToken p).1) := by
  obtain ⟨g, m, _⟩ := expectToken_step TokKind.NAME.num p
  unfold softKeywordToken
  dsimp only
  split
  · rename_i _ t ht
    split
    · rename_i hc
      have s := frame_nameFromToken (.tok t) (expectToken TokKind.NAME.num p).2
      refine ⟨g.trans s.grows, fun ha hq hi => ?_⟩
      have he1 := s.grows.err_false hq
      obtain ⟨h2, h3, h4, h5⟩ := expect_tok ht he1 hi.mark
      have hnn : nonNull (nameFromToken (.tok t) (expectToken TokKind.NAME.num p).2).1 = true := by
        cases hx : (nameFromToken (.tok t) (expectToken TokKind.NAME.num p).2).1 with
        | null =>
          have := nameFromToken_ei t _ hx
          rw [this] at hq
          cases hq
        | _ => rfl
      have hmk := s.mark.trans h2
      have hfill := Nat.lt_of_lt_of_le h3 s.grows.toks.le
      have hts : ts p.mark = t := by
        rw [← ha p.mark hfill, s.grows.toks.same _ h3, h4]
      refine ⟨inv_of (g.trans s.grows) (fun i => (s.memo i).trans (m i))
        (by rw [hmk]; exact hfill) hi, ⟨fun _ => ?_, fun h => ?_⟩⟩
      · rw [hmk]
        exact CallM.softKeywordToken (by rw [hts]; exact h5) (by rw [hts]; exact hc)
      · rw [h] at hnn
        cases hnn
    · refine ⟨g, fun ha he hi => ?_⟩
      obtain ⟨h2, h3, h4, h5⟩ := expect_tok ht he hi.mark
      refine ⟨inv_of g m (by rw [h2]; exact h3) hi, ⟨fun h => (by cases h), fun _ => ?_⟩⟩
      exact Or.inr (Or.inr ⟨rfl, by rw [← ha p.mark h3, h4]; exact h5, h2⟩)
  · rename_i hn
    refine ⟨g, fun ha he hi => ?_⟩
    have h2 := expect_nontok hn he hi.mark
    exact ⟨inv_of g m (by rw [h2]; exact Nat.le_trans hi.mark g.toks.le) hi,
      ⟨fun h => (by cases h), fun _ => Or.inl h2⟩⟩

theorem spec_softKw (ts : Nat → Token) (kw : List Nat) (p : PS) :
    Spec ts p (expectSoftKeyword kw p).2
      (CallEnd ts (.softKw kw) p.mark (expectSoftKeyword kw p).2.mark
        (expectSoftKeyword kw p).1) := by
  have hs := frame_ensureToken p
  unfold expectSoftKeyword
  dsimp only
  have nullEnd : ∀ {R : Prop}, (Inv ts (ensureToken p).2 → R) →
      Spec ts p (ensureToken p).2 R := fun k =>
    ⟨hs.grows, fun _ _ hi => ⟨Inv.ofStep hs hi, k (Inv.ofStep hs hi)⟩⟩
  have nullR : Spec ts p (ensureToken p).2
      (CallEnd ts (.softKw kw) p.mark (ensureToken p).2.mark .null) :=
    nullEnd fun _ => ⟨fun h => (by cases h), fun _ => Or.inl hs.mark⟩
  split
  · exact nullR
  · rename_i hok
    have hok' : (ensureToken p).1 = true := by simpa using hok
    split
    · exact nullR
    · split
      · exact nullR
      · rename_i ht hb
        have ht' : ((ensureToken p).2.tokenAt (ensureToken p).2.mark).type = TokKind.NAME.num := by
          simpa using ht
        have hb' : ((ensureToken p).2.tokenAt (ensureToken p).2.mark).bytes = kw := by
          simpa using hb
        have sp := spec_name ts (ensureToken p).2
        refine ⟨hs.grows.trans sp.grows, fun ha he hi => ?_⟩
        have hi1 := Inv.ofStep hs hi
        obtain ⟨inv, te⟩ := sp.post ha he hi1
        refine ⟨inv, ?_⟩
        rw [hs.mark] at te
        rcases te with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · exact ⟨fun h => (by rw [h1] at h; cases h), fun _ => Or.inl h2⟩
        · have hlt := ensureToken_lt p hi.mark hok'
          have hfill := Nat.lt_of_lt_of_le hlt sp.grows.toks.le
          have hts : ts p.mark = (ensureToken p).2.tokenAt p.mark := by
            rw [← ha p.mark hfill, sp.grows.toks.same _ hlt]
          refine ⟨fun _ => ?_, fun h => ?_⟩
          · rw [h2]
            refine CallM.softKw h3 ?_
            rw [hts, ← hs.mark]
            exact hb'
          · rw [h] at h1
            cases h1

theorem spec_forcedTok (ts : Nat → Token) (ty : Nat) (x : String) (p : PS) :
    Spec ts p (forcedToken ty x p).2
      (CallEnd ts (.forcedTok ty x) p.mark (forcedToken ty x p).2.mark (forcedToken ty x p).1) := by
  have hs := frame_ensureToken p
  unfold forcedToken
  dsimp only
  split
  · rename_i h
    exact Spec.ofError (Grows.refl p) h
  · split
    · rename_i hok
      have hok' : (ensureToken p).1 = false := by simpa using hok
      exact Spec.ofError hs.grows (ensureToken_ei p hok')
    · rename_i hok
      have hok' : (ensureToken p).1 = true := by simpa using hok
      split
      · exact Spec.ofError (hs.grows.trans (frame_raiseRange _ _ _ _ _).grows)
          (raiseKnownLocation_ei _ _ _ _ _ _ _)
      · rename_i ht
        have ht' : ((ensureToken p).2.tokenAt (ensureToken p).2.mark).type = ty := by
          simpa using ht
        refine ⟨⟨⟨hs.grows.toks.le, hs.grows.toks.same⟩, hs.grows.err⟩, fun ha _ hi => ?_⟩
        have hlt := ensureToken_lt p hi.mark hok'
        have hmk : (ensureToken p).2.mark = p.mark := hs.mark
        refine ⟨⟨?_, fun i id n x hx => ?_⟩, ⟨fun _ => ?_, fun h => by cases h⟩⟩
        · show (ensureToken p).2.mark + 1 ≤ (ensureToken p).2.fill
          omega
        · exact (Inv.ofStep hs hi).memo i id n x hx
        · show CallM ts (.forcedTok ty x) p.mark ((ensureToken p).2.mark + 1)
          rw [hmk]
          refine CallM.forcedTok ?_
          have := ha p.mark hlt
          have e : ({ (ensureToken p).2 with mark := (ensureToken p).2.mark + 1 } : PS).tokenAt p.mark
            = (ensureToken p).2.tokenAt p.mark := rfl
          rw [← this, e, ← hmk]
          exact ht'

theorem raiseError_ei (cls msg : String) (p : PS) :
    (raiseError cls false msg p).2.errorIndicator = true := by
  unfold raiseError
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    exact h.1
  · split
    · exact raiseKnownLocation_ei _ _ _ _ _ _ _
    · exact raiseKnownLocation_ei _ _ _ _ _ _ _

/-! ### The memo -/

theorem mem_modify (a : Array (List (Nat × Ast × Nat))) (m i : Nat)
    (f : List (Nat × Ast × Nat) → List (Nat × Ast × Nat)) (x : Nat × Ast × Nat)
    (h : x ∈ (a.modify m f).getD i []) :
    x ∈ a.getD i [] ∨ (i = m ∧ x ∈ f (a.getD m [])) := by
  by_cases hi : i = m
  · subst hi
    by_cases hs : i < a.size
    · rw [modify_getD_self a i hs f] at h
      exact Or.inr ⟨rfl, h⟩
    · left
      simpa [Array.getD_eq_getD_getElem?, Array.getElem?_modify, hs] using h
  · left
    simpa [Array.getD_eq_getD_getElem?, Array.getElem?_modify, Ne.symm hi] using h

theorem memoOK_insert {ts : Nat → Token} {p : PS} {mark id : Nat} {v : Ast} (h : MemoOK ts p)
    (hm : p.mark ≤ p.fill) (he : RuleEnd ts id mark p.mark v) :
    MemoOK ts (insertMemo mark (1000 + id) v p).2 := by
  intro i id' node m hx
  have hx' : (1000 + id', node, m) ∈ (p.memo.modify mark fun l => (1000 + id, v, p.mark) :: l).getD i [] := hx
  rcases mem_modify _ _ _ _ _ hx' with h1 | ⟨h1, h2⟩
  · exact h i id' node m h1
  · rcases List.mem_cons.mp h2 with h3 | h3
    · simp only [Prod.mk.injEq] at h3
      obtain ⟨h4, h5, h6⟩ := h3
      subst h1 h5 h6
      have e : id' = id := by omega
      subst e
      exact ⟨hm, he⟩
    · rw [h1] at *
      exact h mark id' node m h3

theorem memoOK_update {ts : Nat → Token} {p : PS} {mark id : Nat} {v : Ast} (h : MemoOK ts p)
    (hm : p.mark ≤ p.fill) (he : RuleEnd ts id mark p.mark v) :
    MemoOK ts (updateMemo mark (1000 + id) v p).2 := by
  intro i id' node m hx
  have hx' : (1000 + id', node, m) ∈ (p.memo.modify mark fun l =>
      if l.any (fun m => m.1 == 1000 + id) then
        l.map fun m => if m.1 == 1000 + id then (1000 + id, v, p.mark) else m
      else (1000 + id, v, p.mark) :: l).getD i [] := hx
  have new : (1000 + id', node, m) = (1000 + id, v, p.mark) → m ≤ p.fill ∧ RuleEnd ts id' mark m node := by
    intro e
    simp only [Prod.mk.injEq] at e
    obtain ⟨h4, h5, h6⟩ := e
    subst h5 h6
    have e : id' = id := by omega
    subst e
    exact ⟨hm, he⟩
  rcases mem_modify _ _ _ _ _ hx' with h1 | ⟨h1, h2⟩
  · exact h i id' node m h1
  · rw [h1]
    split at h2
    · obtain ⟨y, hy, hxy⟩ := List.mem_map.mp h2
      split at hxy
      · exact new hxy.symm
      · rw [hxy] at hy
        exact h mark id' node m hy
    · rcases List.mem_cons.mp h2 with h3 | h3
      · exact new h3
      · exact h mark id' node m h3

theorem memoLookup_none {ty : Nat} {s : PS} (h : (memoLookup ty s).1 = none) :
    (memoLookup ty s).2 = s := by
  revert h
  unfold memoLookup
  split
  · intro h
    cases h
  · intro _
    rfl

theorem isMemoized_eq (ty : Nat) (p : PS) :
    isMemoized ty p = if (ensureToken p).1 then memoLookup ty (ensureToken p).2
      else (some .null, (ensureToken p).2) := rfl

/-- `_PyPegen_is_memoized` with no entry: only a token read. -/
theorem isMemoized_none {ty : Nat} {p : PS} (h : (isMemoized ty p).1 = none) :
    Step p (isMemoized ty p).2 := by
  have hs := frame_ensureToken p
  rw [isMemoized_eq] at h ⊢
  split at h
  · rename_i hok
    simp only [hok, ↓reduceIte]
    rw [memoLookup_none h]
    exact hs
  · cases h

theorem isMemoized_spec (ts : Nat → Token) (id : Nat) (p : PS) :
    Spec ts p (isMemoized (1000 + id) p).2
      (∀ v, (isMemoized (1000 + id) p).1 = some v →
        RuleEnd ts id p.mark (isMemoized (1000 + id) p).2.mark v) := by
  have hs := frame_ensureToken p
  rw [isMemoized_eq]
  split
  · generalize hl : memoLookup (1000 + id) (ensureToken p).2 = r
    revert hl
    unfold memoLookup
    split
    · rename_i y node m hf
      intro hl
      subst hl
      obtain ⟨hy, hmem⟩ : (y == 1000 + id) = true ∧ _ :=
        ⟨by simpa using (List.find?_some hf), List.mem_of_find?_eq_some hf⟩
      have hy' : y = 1000 + id := by simpa using hy
      subst hy'
      refine ⟨⟨⟨hs.grows.toks.le, hs.grows.toks.same⟩, hs.grows.err⟩, fun _ _ hi => ?_⟩
      have hx : (1000 + id, node, m) ∈ p.memo.getD p.mark [] := by
        rw [← hs.memo, ← hs.mark]
        exact hmem
      obtain ⟨h1, h2⟩ := hi.memo p.mark id node m hx
      refine ⟨⟨Nat.le_trans h1 hs.grows.toks.le, fun i id' n x hm =>
        (Inv.ofStep hs hi).memo i id' n x hm⟩, fun v hv => ?_⟩
      cases hv
      exact h2
    · intro hl
      subst hl
      refine (Spec.ofStep hs).weaken fun _ v hv => ?_
      cases hv
  · rename_i hok
    have hok' : (ensureToken p).1 = false := by simpa using hok
    exact Spec.ofError hs.grows (ensureToken_ei p hok')

/-! ### The head of a rule function -/

theorem frame_startLocation (m : Nat) : Frame (startLocation m) := by
  intro p
  have hs := frame_ensureToken p
  unfold startLocation
  dsimp only
  split <;> exact hs

theorem ruleStart_step (r : Rule) (p : PS) :
    Step p (ruleStart r p).2 ∧
    (∀ v, (ruleStart r p).1 = .inl v → (ruleStart r p).2.errorIndicator = true) ∧
    (∀ x, (ruleStart r p).1 = .inr x → x.1 = p.mark) := by
  unfold ruleStart
  dsimp only
  split
  · have hs := frame_startLocation p.mark p
    split
    · exact ⟨hs, fun v h => (by cases h), fun x h => by cases h; rfl⟩
    · rename_i hn
      refine ⟨hs, fun _ _ => ?_, fun x h => by cases h⟩
      revert hn
      have he := frame_ensureToken p
      unfold startLocation
      dsimp only
      split
      · rename_i hok
        intro _
        have hok' : (ensureToken p).1 = false := by simpa using hok
        exact ensureToken_ei p hok'
      · intro h
        cases h
  · exact ⟨Step.refl p, fun v h => (by cases h), fun x h => by cases h; rfl⟩

theorem prologue_eq (id : Nat) (r : Rule) (p : PS) :
    rulePrologue id r p =
      if (addLevel p).2.errorIndicator then (.inl .null, (addLevel p).2) else
      match (if r.memo then isMemoized (1000 + id) (addLevel p).2 else (none, (addLevel p).2)).1 with
      | some v => (.inl v, (if r.memo then isMemoized (1000 + id) (addLevel p).2
          else (none, (addLevel p).2)).2)
      | none => ruleStart r (if r.memo then isMemoized (1000 + id) (addLevel p).2
          else (none, (addLevel p).2)).2 := rfl

/-- `.inr`, the rule proceeds: only a token read has happened. -/
theorem prologue_inr (id : Nat) (r : Rule) (p : PS) (x : Nat × (Int × Int))
    (h : (rulePrologue id r p).1 = .inr x) :
    x.1 = p.mark ∧ Step p (rulePrologue id r p).2 := by
  have s1 := frame_addLevel p
  rw [prologue_eq] at h ⊢
  split at h
  · cases h
  · rename_i hei
    simp only [hei, Bool.false_eq_true, ↓reduceIte]
    split at h
    · cases h
    · rename_i hn
      have s2 : Step (addLevel p).2 (if r.memo then isMemoized (1000 + id) (addLevel p).2
          else (none, (addLevel p).2)).2 := by
        split
        · rename_i hm
          simp only [hm, ↓reduceIte] at hn
          exact isMemoized_none hn
        · exact Step.refl _
      obtain ⟨h1, _, h3⟩ := ruleStart_step r (if r.memo then isMemoized (1000 + id) (addLevel p).2
        else (none, (addLevel p).2)).2
      refine ⟨?_, (s1.trans s2).trans h1⟩
      rw [h3 x h, s2.mark, s1.mark]

theorem prologue_spec (ts : Nat → Token) (id : Nat) (p : PS) :
    Spec ts p (rulePrologue id (ruleOf id) p).2
      (∀ v, (rulePrologue id (ruleOf id) p).1 = .inl v →
        RuleEnd ts id p.mark (rulePrologue id (ruleOf id) p).2.mark v) := by
  have s1 := frame_addLevel p
  rw [prologue_eq]
  split
  · rename_i h
    exact Spec.ofError s1.grows h
  · by_cases hm : (ruleOf id).memo = true
    · simp only [hm, ↓reduceIte]
      have sm := isMemoized_spec ts id (addLevel p).2
      have comb := (Spec.ofStep (ts := ts) s1).seq sm (fun _ r => r)
      split
      · rename_i v hv
        refine comb.weaken fun r x hx => ?_
        cases hx
        have := r v hv
        rwa [s1.mark] at this
      · rename_i hv
        obtain ⟨h1, h2, _⟩ := ruleStart_step (ruleOf id) (isMemoized (1000 + id) (addLevel p).2).2
        have sq := Spec.ofStep (ts := ts) h1
        have c2 := comb.seq sq (fun _ _ => True.intro)
        refine ⟨c2.grows, fun ha he hi => ⟨(c2.post ha he hi).1, fun v hx => ?_⟩⟩
        have := h2 v hx
        rw [this] at he
        cases he
    · simp only [hm, Bool.false_eq_true, ↓reduceIte]
      obtain ⟨h1, h2, _⟩ := ruleStart_step (ruleOf id) (addLevel p).2
      have c2 := (Spec.ofStep (ts := ts) s1).seq (Spec.ofStep (ts := ts) h1)
        (fun _ _ => True.intro)
      refine ⟨c2.grows, fun ha he hi => ⟨(c2.post ha he hi).1, fun v hx => ?_⟩⟩
      have := h2 v hx
      rw [this] at he
      cases he

/-! ### The induction -/

/-- `runCall` ends in `CallEnd`. -/
def SCall (f : Nat) : Prop := ∀ (ts : Nat → Token) (c : Call) (p : PS),
  Spec ts p (runCall f c p).2 (CallEnd ts c p.mark (runCall f c p).2.mark (runCall f c p).1)

/-- `runItems`: an alternative that reached its end matched. -/
def SItems (f : Nat) : Prop := ∀ (ts : Nat → Token) (items : List Item) (env : Array Ast)
    (cut : Bool) (p : PS),
  Spec ts p (runItems f items env cut p).2
    (∀ e, (runItems f items env cut p).1.1 = some e →
      ItemsM ts items p.mark (runItems f items env cut p).2.mark)

/-- `runAlts`: back at `mark` with nothing to show, or some alternative of the rule matched. -/
def SAlts (f : Nat) : Prop := ∀ (ts : Nat → Token) (id : Nat) (alts : List Alt) (g : Bool)
    (mark : Nat) (st : Int × Int) (p : PS), p.mark = mark →
  ((ruleOf id).kind = .normal ∨ (ruleOf id).kind = .gather) →
  (∀ a, a ∈ alts → a ∈ (ruleOf id).alts) →
  Spec ts p (runAlts f alts g mark st p).2
    (((runAlts f alts g mark st p).2.mark = mark ∧
        ∀ v, (runAlts f alts g mark st p).1 = some v → v = .null) ∨
      RuleM ts id mark (runAlts f alts g mark st p).2.mark)

/-- What `runLoop` returns: a mark within the tokens, no error, and either nothing new or at least
one iteration. -/
structure LoopEnd (ts : Nat → Token) (a : Alt) (mark : Nat) (acc : List Ast) (fill : Nat)
    (r : List Ast × Nat × Bool × Bool) : Prop where
  le : r.2.1 ≤ fill
  ok : r.2.2.2 = true
  out : (r.1 = acc ∧ r.2.1 = mark) ∨ ∃ k, ItemsM ts a.items mark k ∧ LoopM ts a k r.2.1

def SLoop (f : Nat) : Prop := ∀ (ts : Nat → Token) (a : Alt) (mark : Nat) (st : Int × Int)
    (acc : List Ast) (p : PS), p.mark = mark →
  Spec ts p (runLoop f a mark st acc p).2
    (LoopEnd ts a mark acc (runLoop f a mark st acc p).2.fill (runLoop f a mark st acc p).1)

def SBody (f : Nat) : Prop := ∀ (ts : Nat → Token) (id : Nat) (p : PS),
  Spec ts p (ruleBody f id (ruleOf id) p).2
    (RuleEnd ts id p.mark (ruleBody f id (ruleOf id) p).2.mark (ruleBody f id (ruleOf id) p).1)

/-- `growSeed`: the seed is a true `RuleEnd`, so what it grows into is. -/
def SGrow (f : Nat) : Prop := ∀ (ts : Nat → Token) (id mark resmark : Nat) (res : Ast) (p : PS),
  p.mark = resmark →
  Grows p (growSeed f id (ruleOf id) mark resmark res p).2 ∧
  (Agree ts (growSeed f id (ruleOf id) mark resmark res p).2 →
    (growSeed f id (ruleOf id) mark resmark res p).2.errorIndicator = false →
    Inv ts p → mark ≤ p.fill → RuleEnd ts id mark resmark res →
    Inv ts (growSeed f id (ruleOf id) mark resmark res p).2 ∧
      RuleEnd ts id mark (growSeed f id (ruleOf id) mark resmark res p).2.mark
        (growSeed f id (ruleOf id) mark resmark res p).1)

def SRule (f : Nat) : Prop := ∀ (ts : Nat → Token) (id : Nat) (p : PS),
  Spec ts p (callRule f id p).2
    (RuleEnd ts id p.mark (callRule f id p).2.mark (callRule f id p).1)

theorem retLevel_val (v : Ast) (s : PS) : (retLevel v s).1 = v := rfl

theorem retLevel_err (v : Ast) (s : PS) :
    (retLevel v s).2.errorIndicator = s.errorIndicator := rfl

theorem spec_retLevel (ts : Nat → Token) (v : Ast) (s : PS) : Spec ts s (retLevel v s).2 True :=
  spec_frame (frame_retLevel v) s

theorem call_succ {f : Nat} (hr : SRule f) : SCall (f + 1) := by
  intro ts c p
  cases c with
  | tok t =>
    simp only [runCall]
    exact spec_of_tokEnd (spec_expect ts t p) fun _ h => CallM.tok h
  | name =>
    simp only [runCall]
    exact spec_of_tokEnd (spec_name ts p) fun _ h => CallM.name h
  | number =>
    simp only [runCall]
    exact spec_of_tokEnd (spec_number ts p) fun _ h => CallM.number h
  | string =>
    simp only [runCall]
    exact spec_of_tokEnd (spec_expect ts TokKind.STRING.num p) fun _ h => CallM.string h
  | softKeywordToken =>
    simp only [runCall]
    exact spec_softKeywordToken ts p
  | softKw s =>
    simp only [runCall]
    exact spec_softKw ts s p
  | forcedTok t s =>
    simp only [runCall]
    exact spec_forcedTok ts t s p
  | forcedRule r s =>
    have sr := hr ts r p
    simp only [runCall]
    unfold forcedResult
    split
    · rename_i h
      exact Spec.ofError sr.grows h
    · split
      · exact Spec.ofError (sr.grows.trans (frame_raiseError _ _ _ _).grows) (raiseError_ei _ _ _)
      · rename_i hn
        refine sr.weaken fun e => ⟨fun _ => ?_, fun h => (hn h).elim⟩
        rcases e with ⟨h1, _⟩ | h1
        · exact (hn h1).elim
        · exact CallM.forcedRule h1
  | rule r =>
    simp only [runCall]
    refine (hr ts r p).weaken fun e => ⟨fun h => ?_, fun _ => ?_⟩
    · rcases e with ⟨h1, _⟩ | h1
      · rw [h1] at h
        cases h
      · exact CallM.rule h1
    · rcases e with ⟨_, h1⟩ | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl (CallM.rule h1))

theorem opt_of_null {ts : Nat → Token} {c : Call} {rest : List Item} {i k j : Nat}
    (h : NullEnd ts c i k) (r : ItemsM ts rest k j) : ItemsM ts (.opt c :: rest) i j := by
  rcases h with h | h | ⟨h1, h2, h3⟩
  · subst h
    exact ItemsM.optSkip r
  · exact ItemsM.opt h r
  · subst h1 h3
    exact ItemsM.optSoft h2 r

theorem items_succ {f : Nat} (hc : SCall f) (hi : SItems f) : SItems (f + 1) := by
  intro ts items env cut p
  cases items with
  | nil =>
    simp only [runItems]
    exact ⟨Grows.refl p, fun _ _ h => ⟨h, fun _ _ => ItemsM.nil⟩⟩
  | cons it rest =>
    cases it with
    | call c =>
      simp only [runItems]
      have s1 := hc ts c p
      split
      · rename_i hn
        have s2 := hi ts rest (env.push (runCall f c p).1) cut (runCall f c p).2
        exact s1.seq s2 fun r1 r2 e he => ItemsM.call (r1.ok hn) (r2 e he)
      · exact s1.weaken fun _ e he => by cases he
    | opt c =>
      simp only [runItems]
      have s1 := hc ts c p
      split
      · exact s1.weaken fun _ e he => by cases he
      · have s2 := hi ts rest (env.push (runCall f c p).1) cut (runCall f c p).2
        refine s1.seq s2 fun r1 r2 e he => ?_
        have hr := r2 e he
        cases hv : nonNull (runCall f c p).1 with
        | true => exact ItemsM.opt (r1.ok hv) hr
        | false =>
          have : (runCall f c p).1 = .null := by
            cases hx : (runCall f c p).1 <;> simp_all [nonNull]
          exact opt_of_null (r1.nul this) hr
    | look b c =>
      simp only [runItems]
      have s1 := hc ts c p
      have sm := s1.setMark p.mark fun h _ => Nat.le_trans h.mark s1.grows.toks.le
      split
      · have s2 := hi ts rest env cut { (runCall f c p).2 with mark := p.mark }
        exact sm.seq s2 fun _ r2 e he => ItemsM.look (r2 e he)
      · exact sm.weaken fun _ e he => by cases he
    | cut =>
      simp only [runItems]
      exact (hi ts rest (env.push (.int 1)) true p).weaken fun r e he => ItemsM.cut (r e he)

theorem alts_succ {f : Nat} (hi : SItems f) (ha : SAlts f) : SAlts (f + 1) := by
  intro ts id alts g mark st p hm hk hall
  cases alts with
  | nil =>
    simp only [runAlts]
    exact ⟨Grows.refl p, fun _ _ h => ⟨h, Or.inl ⟨hm, fun v hv => by cases hv; rfl⟩⟩⟩
  | cons a rest =>
    have hrest : ∀ x, x ∈ rest → x ∈ (ruleOf id).alts :=
      fun x h => hall x (List.mem_cons_of_mem _ h)
    simp only [runAlts]
    split
    · exact ha ts id rest g mark st p hm hk hrest
    · split
      · rename_i h
        exact Spec.ofError (Grows.refl p) h
      · have si := hi ts a.items #[] false p
        split
        · rename_i env he
          have hs := frame_altResult a g env st (runItems f a.items #[] false p).2
          refine si.seq (Spec.ofStep hs) fun r _ => Or.inr ?_
          have hit := r env he
          rw [hm] at hit
          rw [hs.mark]
          exact RuleM.alt hk (hall a (List.mem_cons_self ..)) hit
        · have sm := si.setMark mark fun h _ => by
            rw [← hm]
            exact Nat.le_trans h.mark si.grows.toks.le
          split
          · exact sm.weaken fun _ => Or.inl ⟨rfl, fun v hv => by cases hv⟩
          · have s2 := ha ts id rest g mark st
              { (runItems f a.items #[] false p).2 with mark := mark } rfl hk hrest
            exact sm.seq s2 fun _ r => r

theorem loop_succ {f : Nat} (hi : SItems f) (hl : SLoop f) : SLoop (f + 1) := by
  intro ts a mark st acc p hm
  simp only [runLoop]
  have si := hi ts a.items #[] false p
  split
  · rename_i env he
    have hs := frame_altResult a false env st (runItems f a.items #[] false p).2
    split
    · rename_i v hv
      have s2 := hl ts a (altResult a false env st (runItems f a.items #[] false p).2).2.mark st
        (v :: acc) (altResult a false env st (runItems f a.items #[] false p).2).2 rfl
      refine (si.seq (Spec.ofStep hs) fun r _ => r).seq s2 fun r e => ?_
      have hit := r env he
      rw [hm] at hit
      rw [← hs.mark] at hit
      refine ⟨e.le, e.ok, Or.inr ?_⟩
      rcases e.out with ⟨_, h2⟩ | ⟨k, h1, h2⟩
      · rw [h2]
        exact ⟨_, hit, LoopM.done⟩
      · exact ⟨_, hit, LoopM.step h1 h2⟩
    · rename_i hv
      exact Spec.ofError (si.grows.trans hs.grows) (altResult_none a false env st _ hv)
  · refine ⟨si.grows, fun ha he h => ?_⟩
    have r := si.post ha he h
    refine ⟨r.1, ⟨?_, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩
    show mark ≤ _
    rw [← hm]
    exact Nat.le_trans h.mark si.grows.toks.le

theorem loop_ruleEnd {ts : Nat → Token} {id mark mark' : Nat} {acc : List Ast}
    (hk : (ruleOf id).kind = .loop0 ∨ (ruleOf id).kind = .loop1)
    (e : (acc = [] ∧ mark' = mark) ∨ ∃ k, ItemsM ts ((ruleOf id).alts.headD default).items mark k ∧
      LoopM ts ((ruleOf id).alts.headD default) k mark') :
    RuleM ts id mark mark' ∨ ((ruleOf id).kind = .loop1 ∧ acc = [] ∧ mark' = mark) := by
  rcases hk with hk | hk
  · left
    refine RuleM.loop0 hk ?_
    rcases e with ⟨_, h⟩ | ⟨k, h1, h2⟩
    · rw [h]
      exact LoopM.done
    · exact LoopM.step h1 h2
  · rcases e with ⟨h1, h2⟩ | ⟨k, h1, h2⟩
    · exact Or.inr ⟨hk, h1, h2⟩
    · exact Or.inl (RuleM.loop1 hk h1 h2)

theorem loopFinish_spec (ts : Nat → Token) (id x : Nat)
    (hk : (ruleOf id).kind = .loop0 ∨ (ruleOf id).kind = .loop1)
    (res : List Ast × Nat × Bool × Bool) (s : PS) :
    Grows s (loopFinish (ruleOf id) res s).2 ∧
    (Inv ts s → res.2.1 ≤ s.fill → res.2.2.2 = true →
      ((res.1 = [] ∧ res.2.1 = x) ∨ ∃ k, ItemsM ts ((ruleOf id).alts.headD default).items x k ∧
        LoopM ts ((ruleOf id).alts.headD default) k res.2.1) →
      Inv ts (loopFinish (ruleOf id) res s).2 ∧
        RuleEnd ts id x (loopFinish (ruleOf id) res s).2.mark (loopFinish (ruleOf id) res s).1) := by
  have fin : ∀ v, Grows s (retLevel v { s with mark := res.2.1 }).2 ∧
      (Inv ts s → res.2.1 ≤ s.fill →
        ((res.1 = [] ∧ res.2.1 = x) ∨ ∃ k, ItemsM ts ((ruleOf id).alts.headD default).items x k ∧
          LoopM ts ((ruleOf id).alts.headD default) k res.2.1) →
        (v = .null ∨ RuleM ts id x res.2.1) →
        Inv ts (retLevel v { s with mark := res.2.1 }).2 ∧
          RuleEnd ts id x (retLevel v { s with mark := res.2.1 }).2.mark
            (retLevel v { s with mark := res.2.1 }).1) := by
    intro v
    have st := frame_retLevel v { s with mark := res.2.1 }
    have gm : Grows s { s with mark := res.2.1 } := ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩
    refine ⟨gm.trans st.grows, fun hi hle hout hv => ⟨Inv.ofStep st ⟨hle, hi.memo⟩, ?_⟩⟩
    show RuleEnd ts id x res.2.1 v
    rcases hv with h | h
    · rcases hout with ⟨_, h4⟩ | ⟨k, h1, h2⟩
      · exact Or.inl ⟨h, h4⟩
      · rcases loop_ruleEnd (acc := [.null]) hk (Or.inr ⟨k, h1, h2⟩) with h5 | ⟨_, h5, _⟩
        · exact Or.inr h5
        · cases h5
    · exact Or.inr h
  unfold loopFinish
  dsimp only
  split
  · rename_i hok
    refine ⟨(frame_retLevel .null s).grows, fun _ _ h _ => ?_⟩
    rw [h] at hok
    simp at hok
  · split
    · exact ⟨(fin .null).1, fun hi hl _ ho => (fin .null).2 hi hl ho (Or.inl rfl)⟩
    · split
      · exact ⟨(fin .null).1, fun hi hl _ ho => (fin .null).2 hi hl ho (Or.inl rfl)⟩
      · rename_i hc
        refine ⟨(fin _).1, fun hi hl _ ho => (fin _).2 hi hl ho (Or.inr ?_)⟩
        rcases loop_ruleEnd hk ho with h5 | ⟨h5, h6, _⟩
        · exact h5
        · exact (hc (by simp [h5, h6])).elim

theorem body_succ {f : Nat} (ha : SAlts f) (hl : SLoop f) : SBody (f + 1) := by
  intro ts id p
  have sp := prologue_spec ts id p
  have hin := prologue_inr id (ruleOf id) p
  simp only [ruleBody]
  generalize rulePrologue id (ruleOf id) p = E at sp hin ⊢
  obtain ⟨ev, s⟩ := E
  dsimp only at sp hin ⊢
  cases ev with
  | inl v =>
    have sr := spec_retLevel ts v s
    exact sp.seq sr fun r _ => r v rfl
  | inr x =>
    obtain ⟨h1, h2⟩ := hin x rfl
    have hmark : s.mark = x.1 := by rw [h2.mark, h1]
    have sg := Spec.ofStep (ts := ts) h2
    cases hk : (ruleOf id).kind with
    | normal =>
      simp only [hk]
      have sa := ha ts id (ruleOf id).alts (RuleKind.normal == RuleKind.gather) x.1 x.2 s hmark
        (Or.inl hk) (fun _ h => h)
      have sc := sg.seq sa fun _ r => r
      generalize runAlts f (ruleOf id).alts (RuleKind.normal == RuleKind.gather) x.1 x.2 s = A at sc ⊢
      obtain ⟨av, ast⟩ := A
      dsimp only at sc ⊢
      cases av with
      | none =>
        have sr := spec_retLevel ts .null ast
        refine sc.seq sr fun r _ => ?_
        rw [← h1]
        show RuleEnd ts id x.1 ast.mark .null
        rcases r with ⟨h3, _⟩ | h3
        · exact Or.inl ⟨rfl, h3⟩
        · exact Or.inr h3
      | some v =>
        by_cases hmemo : (ruleOf id).memo = true
        · simp only [hmemo, ↓reduceIte]
          have hg : Grows ast (insertMemo x.1 (1000 + id) v ast).2 :=
            ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩
          have sr := spec_retLevel ts v (insertMemo x.1 (1000 + id) v ast).2
          refine ⟨sc.grows.trans (hg.trans sr.grows), fun ha' he hi => ?_⟩
          have a1 := Agree.of_grows sr.grows ha'
          have a2 := Agree.of_grows hg a1
          have e2 := hg.err_false (sr.grows.err_false he)
          obtain ⟨inv, r⟩ := sc.post a2 e2 hi
          have he' : RuleEnd ts id x.1 ast.mark v := by
            rcases r with ⟨h3, h4⟩ | h3
            · exact Or.inl ⟨h4 v rfl, h3⟩
            · exact Or.inr h3
          have minv : Inv ts (insertMemo x.1 (1000 + id) v ast).2 :=
            ⟨inv.mark, memoOK_insert inv.memo inv.mark he'⟩
          refine ⟨(sr.post ha' he minv).1, ?_⟩
          rw [← h1]
          exact he'
        · simp only [hmemo, Bool.false_eq_true, ↓reduceIte]
          have sr := spec_retLevel ts v ast
          refine sc.seq sr fun r _ => ?_
          rw [← h1]
          show RuleEnd ts id x.1 ast.mark v
          rcases r with ⟨h3, h4⟩ | h3
          · exact Or.inl ⟨h4 v rfl, h3⟩
          · exact Or.inr h3
    | gather =>
      simp only [hk]
      have sa := ha ts id (ruleOf id).alts (RuleKind.gather == RuleKind.gather) x.1 x.2 s hmark
        (Or.inr hk) (fun _ h => h)
      have sc := sg.seq sa fun _ r => r
      generalize runAlts f (ruleOf id).alts (RuleKind.gather == RuleKind.gather) x.1 x.2 s = A at sc ⊢
      obtain ⟨av, ast⟩ := A
      dsimp only at sc ⊢
      cases av with
      | none =>
        have sr := spec_retLevel ts .null ast
        refine sc.seq sr fun r _ => ?_
        rw [← h1]
        show RuleEnd ts id x.1 ast.mark .null
        rcases r with ⟨h3, _⟩ | h3
        · exact Or.inl ⟨rfl, h3⟩
        · exact Or.inr h3
      | some v =>
        by_cases hmemo : (ruleOf id).memo = true
        · simp only [hmemo, ↓reduceIte]
          have hg : Grows ast (insertMemo x.1 (1000 + id) v ast).2 :=
            ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩
          have sr := spec_retLevel ts v (insertMemo x.1 (1000 + id) v ast).2
          refine ⟨sc.grows.trans (hg.trans sr.grows), fun ha' he hi => ?_⟩
          have a1 := Agree.of_grows sr.grows ha'
          have a2 := Agree.of_grows hg a1
          have e2 := hg.err_false (sr.grows.err_false he)
          obtain ⟨inv, r⟩ := sc.post a2 e2 hi
          have he' : RuleEnd ts id x.1 ast.mark v := by
            rcases r with ⟨h3, h4⟩ | h3
            · exact Or.inl ⟨h4 v rfl, h3⟩
            · exact Or.inr h3
          have minv : Inv ts (insertMemo x.1 (1000 + id) v ast).2 :=
            ⟨inv.mark, memoOK_insert inv.memo inv.mark he'⟩
          refine ⟨(sr.post ha' he minv).1, ?_⟩
          rw [← h1]
          exact he'
        · simp only [hmemo, Bool.false_eq_true, ↓reduceIte]
          have sr := spec_retLevel ts v ast
          refine sc.seq sr fun r _ => ?_
          rw [← h1]
          show RuleEnd ts id x.1 ast.mark v
          rcases r with ⟨h3, h4⟩ | h3
          · exact Or.inl ⟨h4 v rfl, h3⟩
          · exact Or.inr h3
    | loop0 =>
      simp only [hk]
      split
      · rename_i h
        exact Spec.ofError (h2.grows.trans (frame_retLevel .null s).grows) h
      · have sl := hl ts ((ruleOf id).alts.headD default) x.1 x.2 [] s hmark
        have sc := sg.seq sl fun _ r => r
        obtain ⟨g, post⟩ := loopFinish_spec ts id x.1 (Or.inl hk)
          (runLoop f ((ruleOf id).alts.headD default) x.1 x.2 [] s).1
          (runLoop f ((ruleOf id).alts.headD default) x.1 x.2 [] s).2
        refine ⟨sc.grows.trans g, fun ha' he hi => ?_⟩
        obtain ⟨inv, le⟩ := sc.post (Agree.of_grows g ha') (g.err_false he) hi
        rw [← h1]
        exact post inv le.le le.ok le.out
    | loop1 =>
      simp only [hk]
      split
      · rename_i h
        exact Spec.ofError (h2.grows.trans (frame_retLevel .null s).grows) h
      · have sl := hl ts ((ruleOf id).alts.headD default) x.1 x.2 [] s hmark
        have sc := sg.seq sl fun _ r => r
        obtain ⟨g, post⟩ := loopFinish_spec ts id x.1 (Or.inr hk)
          (runLoop f ((ruleOf id).alts.headD default) x.1 x.2 [] s).1
          (runLoop f ((ruleOf id).alts.headD default) x.1 x.2 [] s).2
        refine ⟨sc.grows.trans g, fun ha' he hi => ?_⟩
        obtain ⟨inv, le⟩ := sc.post (Agree.of_grows g ha') (g.err_false he) hi
        rw [← h1]
        exact post inv le.le le.ok le.out

theorem growSeed_succ (f id : Nat) (r : Rule) (mark resmark : Nat) (res : Ast) (p q0 : PS)
    (hq : q0 = { (updateMemo mark (1000 + id) res p).2 with mark := mark }) :
    growSeed (f + 1) id r mark resmark res p =
      if (ruleBody f id r q0).2.errorIndicator then retLevel .null (ruleBody f id r q0).2
      else if !nonNull (ruleBody f id r q0).1 || decide ((ruleBody f id r q0).2.mark ≤ resmark) then
        retLevel res { (ruleBody f id r q0).2 with mark := resmark }
      else growSeed f id r mark (ruleBody f id r q0).2.mark (ruleBody f id r q0).1
        (ruleBody f id r q0).2 := by
  subst hq
  simp only [growSeed]

theorem grow_succ {f : Nat} (hb : SBody f) (hg : SGrow f) : SGrow (f + 1) := by
  intro ts id mark resmark res p hm
  obtain ⟨q0, hq⟩ : ∃ q, q = { (updateMemo mark (1000 + id) res p).2 with mark := mark } := ⟨_, rfl⟩
  have h2 : Grows p q0 := by
    subst hq
    exact ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩
  have hinv : Inv ts p → mark ≤ p.fill → RuleEnd ts id mark resmark res → Inv ts q0 := by
    intro hi hf he
    subst hq
    exact ⟨hf, memoOK_update hi.memo hi.mark (by rw [hm]; exact he)⟩
  have hmk : q0.mark = mark := by rw [hq]
  have sb := hb ts id q0
  rw [growSeed_succ f id (ruleOf id) mark resmark res p q0 hq]
  generalize ruleBody f id (ruleOf id) q0 = B at sb ⊢
  obtain ⟨bv, bs⟩ := B
  dsimp only at sb ⊢
  rw [hmk] at sb
  split
  · rename_i h
    have gr := h2.trans (sb.grows.trans (frame_retLevel .null bs).grows)
    refine ⟨gr, fun _ he _ _ _ => ?_⟩
    have : (retLevel .null bs).2.errorIndicator = true := h
    rw [this] at he
    cases he
  · split
    · have st := frame_retLevel res { bs with mark := resmark }
      have gm : Grows bs { bs with mark := resmark } := ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩
      refine ⟨h2.trans (sb.grows.trans (gm.trans st.grows)), fun ha he hi hf hr => ?_⟩
      have a1 := Agree.of_grows (gm.trans st.grows) ha
      have e1 := (gm.trans st.grows).err_false he
      obtain ⟨inv, _⟩ := sb.post a1 e1 (hinv hi hf hr)
      have hle : resmark ≤ bs.fill := by
        have := hi.mark
        have g1 := h2.toks.le
        have g2 := sb.grows.toks.le
        omega
      exact ⟨Inv.ofStep st ⟨hle, inv.memo⟩, hr⟩
    · obtain ⟨g3, post⟩ := hg ts id mark bs.mark bv bs rfl
      refine ⟨h2.trans (sb.grows.trans g3), fun ha he hi hf hr => ?_⟩
      have a1 := Agree.of_grows g3 ha
      have e1 := g3.err_false he
      obtain ⟨inv, r⟩ := sb.post a1 e1 (hinv hi hf hr)
      exact post ha he inv (Nat.le_trans (Nat.le_trans hf h2.toks.le) sb.grows.toks.le) r

theorem rule_succ {f : Nat} (hb : SBody f) (hg : SGrow f) : SRule (f + 1) := by
  intro ts id p
  simp only [callRule]
  split
  · have s1 := frame_addLevel p
    have sm := isMemoized_spec ts id (addLevel p).2
    have comb := (Spec.ofStep (ts := ts) s1).seq sm (fun _ r => r)
    have hnone := @isMemoized_none (1000 + id) (addLevel p).2
    generalize isMemoized (1000 + id) (addLevel p).2 = M at comb hnone ⊢
    obtain ⟨mv, ms⟩ := M
    dsimp only at comb hnone ⊢
    cases mv with
    | some v =>
      have sr := spec_retLevel ts v ms
      refine comb.seq sr fun r _ => ?_
      have := r v rfl
      rw [s1.mark] at this
      exact this
    | none =>
      have st := hnone rfl
      obtain ⟨g, post⟩ := hg ts id ms.mark ms.mark .null ms rfl
      refine ⟨comb.grows.trans g, fun ha he hi => ?_⟩
      obtain ⟨inv, _⟩ := comb.post (Agree.of_grows g ha) (g.err_false he) hi
      obtain ⟨i2, r⟩ := post ha he inv inv.mark (Or.inl ⟨rfl, rfl⟩)
      have e : ms.mark = p.mark := (s1.trans st).mark
      refine ⟨i2, ?_⟩
      show RuleEnd ts id p.mark (growSeed f id (ruleOf id) ms.mark ms.mark .null ms).2.mark
        (growSeed f id (ruleOf id) ms.mark ms.mark .null ms).1
      rw [← e]
      exact r
  · split
    · have s0 : Step p { p with callInvalidRules := false } :=
        ⟨rfl, ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩, fun _ => rfl⟩
      have sb := hb ts id { p with callInvalidRules := false }
      have comb := (Spec.ofStep (ts := ts) s0).seq sb (fun _ r => r)
      generalize ruleBody f id (ruleOf id) { p with callInvalidRules := false } = B at comb ⊢
      obtain ⟨bv, bs⟩ := B
      dsimp only at comb ⊢
      have s2 : Step bs { bs with callInvalidRules := p.callInvalidRules } :=
        ⟨rfl, ⟨⟨Nat.le_refl _, fun _ _ => rfl⟩, fun h => h⟩, fun _ => rfl⟩
      exact comb.seq (Spec.ofStep s2) fun r _ => r
    · exact hb ts id p

theorem sound_zero : SCall 0 ∧ SItems 0 ∧ SAlts 0 ∧ SLoop 0 ∧ SBody 0 ∧ SGrow 0 ∧ SRule 0 := by
  have out : ∀ {ts : Nat → Token} {R : Prop} (p : PS), Spec ts p (outOfFuel p).2 R :=
    fun p => Spec.ofError (frame_outOfFuel p).grows (outOfFuel_ei p)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ts c p
    simp only [runCall]
    exact out p
  · intro ts items env cut p
    simp only [runItems]
    exact out p
  · intro ts id alts g mark st p _ _ _
    simp only [runAlts]
    exact out p
  · intro ts a mark st acc p _
    simp only [runLoop]
    exact out p
  · intro ts id p
    simp only [ruleBody]
    exact out p
  · intro ts id mark resmark res p _
    simp only [growSeed]
    exact ⟨(frame_outOfFuel p).grows, fun _ he _ _ _ => by
      rw [outOfFuel_ei p] at he
      cases he⟩
  · intro ts id p
    simp only [callRule]
    exact out p

theorem sound_all (f : Nat) :
    SCall f ∧ SItems f ∧ SAlts f ∧ SLoop f ∧ SBody f ∧ SGrow f ∧ SRule f := by
  induction f with
  | zero => exact sound_zero
  | succ f ih =>
    obtain ⟨hc, hi, ha, hl, hb, hg, hr⟩ := ih
    exact ⟨call_succ hr, items_succ hc hi, alts_succ hi ha, loop_succ hi hl, body_succ ha hl,
      grow_succ hb hg, rule_succ hb hg⟩

/-- The token readers of `Parser/pegen.c` as the generated parser sees them. Each takes exactly the
token its name promises and moves the mark past it, or leaves the mark alone, or ends in an error.
`_PyPegen_soft_keyword_token` is the exception, kept as it is in the C: a `NAME` that is not a soft
keyword stays consumed. -/
def TokenReaders : Prop := ∀ (ts : Nat → Token) (p : PS),
  Spec ts p (nameToken p).2 (TokEnd ts TokKind.NAME.num p.mark (nameToken p).2.mark (nameToken p).1) ∧
  Spec ts p (softKeywordToken p).2
    (CallEnd ts .softKeywordToken p.mark (softKeywordToken p).2.mark (softKeywordToken p).1) ∧
  (∀ kw, Spec ts p (expectSoftKeyword kw p).2
    (CallEnd ts (.softKw kw) p.mark (expectSoftKeyword kw p).2.mark (expectSoftKeyword kw p).1)) ∧
  (∀ ty x, Spec ts p (forcedToken ty x p).2
    (CallEnd ts (.forcedTok ty x) p.mark (forcedToken ty x p).2.mark (forcedToken ty x p).1))

theorem tokenReaders_proven : TokenReaders := fun ts p =>
  ⟨spec_name ts p, spec_softKeywordToken ts p, fun kw => spec_softKw ts kw p,
    fun ty x => spec_forcedTok ts ty x p⟩

/-- Every action in the grammar, whatever it computes, leaves `p->mark` where it was, only appends
tokens, leaves the memo alone and never clears `error_indicator`. -/
def ActionsFrame : Prop := ∀ (env : Array Ast) (ex : Extra) (e : AE), Frame (evalA env ex e)

theorem actionsFrame_proven : ActionsFrame := frame_evalA

/-- Soundness of every generated rule function against the grammar: for any rule `id`, any fuel and
any state with the mark within the tokens read and an empty memo, as at the start of a parse, if
`callRule` returns non-`NULL` with no error, then the tokens it consumed are a match of `ruleOf id`
by `RuleM`, over the tokens read by then. There is no hypothesis on the source, on the rule, or on
the shape of the grammar, and left recursion is included. -/
def CallRuleSound : Prop := ∀ (fuel id : Nat) (p : PS),
  p.mark ≤ p.fill → (∀ i, p.memo.getD i [] = []) →
  (callRule fuel id p).2.errorIndicator = false → nonNull (callRule fuel id p).1 = true →
  RuleM (callRule fuel id p).2.tokenAt id p.mark (callRule fuel id p).2.mark

theorem callRuleSound_proven : CallRuleSound := by
  intro fuel id p hm he' hq hn
  have s := (sound_all fuel).2.2.2.2.2.2 (callRule fuel id p).2.tokenAt id p
  have hi : Inv (callRule fuel id p).2.tokenAt p :=
    ⟨hm, fun i _ _ _ hx => by rw [he' i] at hx; cases hx⟩
  rcases (s.post (fun _ _ => rfl) hq hi).2 with ⟨h1, _⟩ | h1
  · rw [h1] at hn
    cases hn
  · exact h1

end PyLean.PyGrammar.Peg
