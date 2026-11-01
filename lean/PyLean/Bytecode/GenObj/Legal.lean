import PyLean.Bytecode.GenObj.MiscProps

/-!
# State transition invariants across the whole state machine

`Mono w w'` says every frame state moved along `legalEdge`, `ag_closed` only went on,
and every awaitable only moved forward. All the operations of the file preserve it,
for every generator in the world, given `HooksLegal`: the only assumptions on the
interpreter, each a fact about what Python code can do through the model itself.
-/

namespace PyLean.Bytecode.GenObj

def AwaitableState.rank : AwaitableState → Nat
  | .init => 0
  | .iter => 1
  | .closed => 2

variable {V X : Type}

structure Mono (w w' : World V X) : Prop where
  st : ∀ q, legalEdge (w.get q).state (w'.get q).state = true
  closed : ∀ q, (w.get q).agClosed = true → (w'.get q).agClosed = true
  asend : ∀ a, (w.asends a).state.rank ≤ (w'.asends a).state.rank
  athrow : ∀ a, (w.athrows a).state.rank ≤ (w'.athrows a).state.rank

theorem Mono.refl (w : World V X) : Mono w w :=
  ⟨fun _ => legalEdge_refl _, fun _ h => h, fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩

theorem Mono.trans {a b c : World V X} (h1 : Mono a b) (h2 : Mono b c) : Mono a c :=
  ⟨fun q => legalEdge_trans (h1.st q) (h2.st q), fun q h => h2.closed q (h1.closed q h),
   fun q => Nat.le_trans (h1.asend q) (h2.asend q), fun q => Nat.le_trans (h1.athrow q) (h2.athrow q)⟩

/-- No frame that is executing, or suspended in `yield from`, sits at a depth-1
`RESUME`. The compiler guarantees the `yield from` half (the `RESUME` of a delegation
loop is inside its `SETUP_FINALLY`); the executing half fails only in the window of
`GenCloseRejectsExecuting`'s refutation, so assuming it here is on record there. -/
def Inv (w : World V X) : Prop :=
  ∀ q, ((w.get q).state = .executing ∨ (w.get q).state = .suspendedYieldFrom) →
    (w.get q).instr.isResumeDepth1 = false

/-- `Inv` for every frame but `r`, the one being resumed. -/
def InvExcept (r : Ref) (w : World V X) : Prop :=
  ∀ q, q ≠ r → ((w.get q).state = .executing ∨ (w.get q).state = .suspendedYieldFrom) →
    (w.get q).instr.isResumeDepth1 = false

/-- What is assumed of the interpreter. Python code run by a hook acts on these
objects only through the model's own operations, so it preserves `Mono` and `Inv`;
`YIELD_VALUE 1` is followed by a `RESUME` without the depth-1 bit (the compiler's
`SETUP_FINALLY`); and looking up `throw` on a sub-iterator does not touch frame states
(the case excluded here is `GenThrowLookupSeesExecuting`'s refutation). -/
structure HooksLegal (h : Hooks V X) : Prop where
  resume : ∀ w r a e, InvExcept r w →
    Mono w (h.resume w r a e).1 ∧ InvExcept r (h.resume w r a e).1
  resumeYf : ∀ w r a e v d top, (h.resume w r a e).2 = .yielded true v d top → d = false
  getClose : ∀ w o, Inv w → Mono w (h.getClose w o).1 ∧ Inv (h.getClose w o).1
  getThrow : ∀ w o, Inv w → Mono w (h.getThrow w o).1 ∧ Inv (h.getThrow w o).1
  getThrowFrames : ∀ w o q, ((h.getThrow w o).1.get q).state = (w.get q).state
  callNoArgs : ∀ w m, Inv w → Mono w (h.callNoArgs w m).1 ∧ Inv (h.callNoArgs w m).1
  callThrow : ∀ w m a b c, Inv w →
    Mono w (h.callThrow w m a b c).1 ∧ Inv (h.callThrow w m a b c).1
  unraisable : ∀ w m e, Inv w → Mono w (h.unraisable w m e) ∧ Inv (h.unraisable w m e)
  warn : ∀ w m, Inv w → Mono w (h.warn w m).1 ∧ Inv (h.warn w m).1

/-- `HooksLegal` can be met: a frame that re-raises what is thrown and touches nothing. -/
theorem noopHooks_legal : HooksLegal noopHooks where
  resume _ _ _ _ hi := ⟨Mono.refl _, hi⟩
  resumeYf := by intro w r a e v d top h; exact absurd h (by simp [noopHooks])
  getClose _ _ hi := ⟨Mono.refl _, hi⟩
  getThrow _ _ hi := ⟨Mono.refl _, hi⟩
  getThrowFrames _ _ _ := rfl
  callNoArgs _ _ hi := ⟨Mono.refl _, hi⟩
  callThrow _ _ _ _ _ hi := ⟨Mono.refl _, hi⟩
  unraisable _ _ _ hi := ⟨Mono.refl _, hi⟩
  warn _ _ hi := ⟨Mono.refl _, hi⟩

/-- Writing a frame's state, as the model does on every path. -/
theorem mono_write {w w2 w3 : World V X} {r : Ref} {s : FrameState}
    (m : Mono (w.setState r s) w2) (hne : ∀ q, q ≠ r → w3.get q = w2.get q)
    (hr : legalEdge (w.get r).state (w3.get r).state = true)
    (hc : (w3.get r).agClosed = (w2.get r).agClosed)
    (hs : w3.asends = w2.asends) (ht : w3.athrows = w2.athrows) : Mono w w3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    by_cases hq : q = r
    · subst hq; exact hr
    · have := m.st q
      rw [get_setState_ne _ _ hq] at this
      rw [hne q hq]; exact this
  · intro q hq0
    by_cases hq : q = r
    · subst hq
      rw [hc]
      apply m.closed
      simpa [World.setState] using hq0
    · rw [hne q hq]
      apply m.closed
      rw [get_setState_ne _ _ hq]; exact hq0
  · intro a; rw [hs]; exact m.asend a
  · intro a; rw [ht]; exact m.athrow a

theorem Inv.except {w : World V X} (hi : Inv w) (r : Ref) (s : FrameState) :
    InvExcept r (w.setState r s) := by
  intro q hq hst
  rw [get_setState_ne _ _ hq] at hst ⊢
  exact hi q hst

theorem legal_to_cleared (s : FrameState) (h : s ≠ .executing) : legalEdge s .cleared = true := by
  cases s <;> first | rfl | exact absurd rfl h

theorem legal_to_oparg (s : FrameState) (b : Bool)
    (h1 : s ≠ .executing) (h2 : s.finished = false) : legalEdge s (FrameState.ofOparg b) = true := by
  cases s <;> cases b <;> first | rfl | exact absurd rfl h1 | (simp at h2)

theorem genYf_some {g : GenObj V} {yf} (hy : genYf g = some yf) :
    g.state = .suspendedYieldFrom := by
  unfold genYf at hy
  split at hy
  · assumption
  · simp at hy

section Send
variable {h : Hooks V X}

theorem get_clear_ne (w : World V X) {r q : Ref} (hq : q ≠ r) :
    (clearGenFrame w r).get q = w.get q := get_setState_ne _ _ hq

theorem genSendEx2_legal (hh : HooksLegal h) (w : World V X) (r arg exc err closing) (hi : Inv w) :
    Mono w (genSendEx2 h w r arg exc err closing).1 ∧ Inv (genSendEx2 h w r arg exc err closing).1 := by
  by_cases hrej : SendRejected (w.get r) arg
  · rw [(genSendRejectedNoEffect_proven V X h h w r arg exc err closing hrej).1]
    exact ⟨Mono.refl w, hi⟩
  have h1 : ¬ ((w.get r).state = .created ∧ isNonNull arg = true) := fun c => hrej (Or.inl c)
  have h2 : (w.get r).state ≠ .executing := fun c => hrej (Or.inr (Or.inl c))
  have h3 : (w.get r).state.finished = false := by
    cases hf : (w.get r).state.finished with
    | false => rfl
    | true => exact absurd (Or.inr (Or.inr hf)) hrej
  rw [genSendEx2_live h w r arg exc err closing h1 h2 h3]
  have hres := hh.resume (w.setState r .executing) r (arg.getD .none) (if exc then err else none)
    (hi.except r _)
  have hyf := fun v d top => hh.resumeYf (w.setState r .executing) r (arg.getD .none)
    (if exc then err else none) v d top
  simp only
  generalize h.resume (w.setState r .executing) r (arg.getD .none) (if exc then err else none) = res
    at hres hyf
  obtain ⟨w2, o⟩ := res
  obtain ⟨m, ie⟩ := hres
  simp only at m ie hyf ⊢
  cases o with
  | yielded oparg v d top =>
    simp only [finishResume]
    constructor
    · apply mono_write m
      · intro q hq; simp [suspendFrame, hq]
      · simpa [suspendFrame] using legal_to_oparg _ oparg h2 h3
      · simp [suspendFrame]
      · rfl
      · rfl
    · intro q hst
      by_cases hq : q = r
      · subst hq
        cases oparg with
        | false => simp [suspendFrame, FrameState.ofOparg] at hst
        | true =>
          have := hyf v d top rfl
          simp [suspendFrame, InstrPtr.isResumeDepth1, this]
      · simp only [suspendFrame, World.get_set_ne _ _ hq] at hst ⊢
        exact ie q hq hst
  | raised e =>
    simp only [finishResume]
    constructor
    · apply mono_write m
      · intro q hq; exact get_clear_ne _ hq
      · simpa [clearGenFrame] using legal_to_cleared _ h2
      · simp [clearGenFrame, World.setState]
      · rfl
      · rfl
    · intro q hst
      by_cases hq : q = r
      · subst hq; simp [clearGenFrame] at hst
      · rw [get_clear_ne _ hq] at hst ⊢
        exact ie q hq hst
  | returned v =>
    have hgoal : Mono w (clearGenFrame w2 r) ∧ Inv (clearGenFrame w2 r) := by
      constructor
      · apply mono_write m
        · intro q hq; exact get_clear_ne _ hq
        · simpa [clearGenFrame] using legal_to_cleared _ h2
        · simp [clearGenFrame, World.setState]
        · rfl
        · rfl
      · intro q hst
        by_cases hq : q = r
        · subst hq; simp [clearGenFrame] at hst
        · rw [get_clear_ne _ hq] at hst ⊢
          exact ie q hq hst
    simp only [finishResume]
    split <;> exact hgoal

theorem genSendEx_legal (hh : HooksLegal h) (w : World V X) (r arg exc err closing) (hi : Inv w) :
    Mono w (genSendEx h w r arg exc err closing).1 ∧ Inv (genSendEx h w r arg exc err closing).1 :=
  genSendEx2_legal hh w r arg exc err closing hi

theorem genCloseFinish_fst (w : World V X) (r p) :
    (genCloseFinish h w r p).1 = (genSendEx h w r (some .none) true p true).1 := by
  simp only [genCloseFinish]
  generalize (genSendEx h w r (some .none) true p true) = s
  obtain ⟨w', res⟩ := s
  cases res with
  | ok v => rfl
  | err e =>
    cases e with
    | none => rfl
    | some x => simp only; split <;> rfl

/-- `delegating` keeps the invariants when `act` does. -/
theorem delegating_legal {α : Type} (w : World V X) (r : Ref) (act : World V X → World V X × α)
    (hact : ∀ w', Inv w' → Mono w' (act w').1 ∧ Inv (act w').1) (hi : Inv w)
    (hs : (w.get r).state = .suspendedYieldFrom) :
    Mono w (delegating w r act).1 ∧ Inv (delegating w r act).1 := by
  have hi1 : Inv (w.setState r .executing) := by
    intro q hst
    by_cases hq : q = r
    · subst hq
      simpa using hi q (Or.inr hs)
    · rw [get_setState_ne _ _ hq] at hst ⊢
      exact hi q hst
  obtain ⟨m, i2⟩ := hact _ hi1
  simp only [delegating]
  generalize act (w.setState r .executing) = p at m i2
  obtain ⟨w2, a⟩ := p
  simp only at m i2 ⊢
  have hexec : (w2.get r).state = .executing := by
    have := m.st r
    simp only [state_setState] at this
    cases hk : (w2.get r).state <;> rw [hk] at this <;> first | rfl | exact absurd this (by decide)
  constructor
  · apply mono_write m
    · intro q hq; exact get_setState_ne _ _ hq
    · simpa [hs] using legalEdge_refl .suspendedYieldFrom
    · simp [World.setState]
    · rfl
    · rfl
  · intro q hst
    by_cases hq : q = r
    · subst hq
      simpa using i2 q (Or.inl hexec)
    · rw [get_setState_ne _ _ hq] at hst ⊢
      exact i2 q hst

theorem genCloseIter_legal (hh : HooksLegal h) (c : World V X → Ref → World V X × Ret V)
    (hc : ∀ w r, Inv w → Mono w (c w r).1 ∧ Inv (c w r).1) (w : World V X) (yf) (hi : Inv w) :
    Mono w (genCloseIter h c w yf).1 ∧ Inv (genCloseIter h c w yf).1 := by
  simp only [genCloseIter]
  split
  · rename_i r _
    have := hc w r hi
    generalize c w r = p at this
    obtain ⟨w', res⟩ := p
    cases res <;> exact this
  · simp only [genCloseIterForeign]
    obtain ⟨m1, i1⟩ := hh.getClose w yf hi
    generalize h.getClose w yf = a at m1 i1
    obtain ⟨wa, ra⟩ := a
    simp only at m1 i1 ⊢
    have hmeth : Mono wa (closeMeth h wa ra).1 ∧ Inv (closeMeth h wa ra).1 := by
      cases ra with
      | error e => exact hh.unraisable wa _ e i1
      | ok mo => exact ⟨Mono.refl _, i1⟩
    generalize closeMeth h wa ra = m at hmeth
    obtain ⟨wm, mo⟩ := m
    simp only at hmeth ⊢
    cases mo with
    | none => exact ⟨m1.trans hmeth.1, hmeth.2⟩
    | some mt =>
      simp only
      obtain ⟨m3, i3⟩ := hh.callNoArgs wm mt hmeth.2
      generalize h.callNoArgs wm mt = c3 at m3 i3
      obtain ⟨w3, r3⟩ := c3
      cases r3 <;> exact ⟨(m1.trans hmeth.1).trans m3, i3⟩

theorem closeDelegate_legal (hh : HooksLegal h) (c : World V X → Ref → World V X × Ret V)
    (hc : ∀ w r, Inv w → Mono w (c w r).1 ∧ Inv (c w r).1) (w : World V X) (r) (hi : Inv w) :
    Mono w (closeDelegate h c w r).1 ∧ Inv (closeDelegate h c w r).1 := by
  simp only [closeDelegate]
  cases hy : genYf (w.get r) with
  | none => exact ⟨Mono.refl w, hi⟩
  | some yf =>
    dsimp only
    exact delegating_legal w r _ (fun w' i' => genCloseIter_legal hh c hc w' yf i') hi
      (genYf_some hy)

/-- `genClearFrame (setState completed)`, the write of :392-393 and :419-420. -/
theorem clearCompleted_spec (w : World V X) (r : Ref) (hs : (w.get r).state ≠ .executing)
    (hi : Inv w) :
    Mono w (genClearFrame (w.setState r .completed) r) ∧
      Inv (genClearFrame (w.setState r .completed) r) := by
  have hg : genClearFrame (w.setState r .completed) r =
      (w.setState r .completed).setState r .cleared := by
    simp [genClearFrame]
  rw [hg]
  have hne : ∀ q, q ≠ r → ((w.setState r .completed).setState r .cleared).get q = w.get q := by
    intro q hq
    rw [get_setState_ne _ _ hq, get_setState_ne _ _ hq]
  constructor
  · refine ⟨?_, ?_, fun _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
    · intro q
      by_cases hq : q = r
      · subst hq; simpa using legal_to_cleared _ hs
      · rw [hne q hq]; exact legalEdge_refl _
    · intro q hc
      by_cases hq : q = r
      · subst hq; simpa [World.setState] using hc
      · rw [hne q hq]; exact hc
  · intro q hst
    by_cases hq : q = r
    · subst hq; simp at hst
    · rw [hne q hq] at hst ⊢; exact hi q hst

theorem genCloseF_legal (hh : HooksLegal h) (n : Nat) :
    ∀ (w : World V X) (r), Inv w →
      Mono w (genCloseF h n w r).1 ∧ Inv (genCloseF h n w r).1 := by
  induction n with
  | zero => intro w r hi; exact ⟨Mono.refl w, hi⟩
  | succ n ih =>
    intro w r hi
    simp only [genCloseF]
    split
    · rename_i hc
      exact clearCompleted_spec w r (by simp [hc]) hi
    · split
      · exact ⟨Mono.refl w, hi⟩
      · simp only [genCloseBody]
        obtain ⟨m, i⟩ := closeDelegate_legal hh (genCloseF h n) ih w r hi
        generalize closeDelegate h (genCloseF h n) w r = p at m i
        obtain ⟨w1, st⟩ := p
        simp only at m i ⊢
        split
        · rename_i hf
          have hne : (w1.get r).state ≠ .executing := by
            intro e
            have := i r (Or.inl e)
            rw [hf.1] at this
            exact absurd this (by decide)
          obtain ⟨m2, i2⟩ := clearCompleted_spec w1 r hne i
          exact ⟨m.trans m2, i2⟩
        · rw [genCloseFinish_fst]
          obtain ⟨m2, i2⟩ := genSendEx_legal hh w1 r (some .none) true (closePending st) true i
          exact ⟨m.trans m2, i2⟩

theorem throwHere_legal (hh : HooksLegal h) (w : World V X) (r typ val tb) (hi : Inv w) :
    Mono w (throwHere h w r typ val tb).1 ∧ Inv (throwHere h w r typ val tb).1 := by
  simp only [throwHere]
  split
  · exact ⟨Mono.refl w, hi⟩
  · cases typ
    case excClass k c => exact genSendEx_legal hh w r _ _ _ _ hi
    case excInst k c m v =>
      dsimp only
      split
      · exact ⟨Mono.refl w, hi⟩
      · exact genSendEx_legal hh w r _ _ _ _ hi
    all_goals exact ⟨Mono.refl w, hi⟩

theorem afterDelegate_legal (hh : HooksLegal h) (w : World V X) (r) (x : Ret V) (hi : Inv w) :
    Mono w (afterDelegate h w r x).1 ∧ Inv (afterDelegate h w r x).1 := by
  cases x with
  | ok v => exact ⟨Mono.refl w, hi⟩
  | err e => exact genSendEx_legal hh w r _ _ _ _ hi

theorem genThrowF_legal (hh : HooksLegal h) (n : Nat) :
    ∀ (w : World V X) (r c typ val tb), Inv w →
      Mono w (genThrowF h n w r c typ val tb).1 ∧ Inv (genThrowF h n w r c typ val tb).1 := by
  induction n with
  | zero => intro w r c typ val tb hi; exact ⟨Mono.refl w, hi⟩
  | succ n ih =>
    intro w r c typ val tb hi
    simp only [genThrowF]
    cases hy : genYf (w.get r) with
    | none => exact throwHere_legal hh w r typ val tb hi
    | some yf =>
      have hs := genYf_some hy
      simp only
      split
      · have hd := delegating_legal w r (fun w' => genCloseIter h (genCloseF h n) w' yf)
          (fun w' i' => genCloseIter_legal hh _ (genCloseF_legal hh n) w' yf i') hi hs
        generalize delegating w r (fun w' => genCloseIter h (genCloseF h n) w' yf) = p at hd
        obtain ⟨w1, st⟩ := p
        obtain ⟨m, i⟩ := hd
        simp only at m i ⊢
        cases st with
        | fail e =>
          obtain ⟨m2, i2⟩ := genSendEx_legal hh w1 r (some .none) true e false i
          exact ⟨m.trans m2, i2⟩
        | ok =>
          obtain ⟨m2, i2⟩ := throwHere_legal hh w1 r typ val tb i
          exact ⟨m.trans m2, i2⟩
      · split
        · rename_i sub _
          have hd := delegating_legal w r (fun w' => genThrowF h n w' sub c typ val tb)
            (fun w' i' => ih w' sub c typ val tb i') hi hs
          generalize delegating w r (fun w' => genThrowF h n w' sub c typ val tb) = p at hd
          obtain ⟨w1, res⟩ := p
          obtain ⟨m, i⟩ := hd
          obtain ⟨m2, i2⟩ := afterDelegate_legal hh w1 r res i
          exact ⟨m.trans m2, i2⟩
        · obtain ⟨m1, i1⟩ := hh.getThrow w yf hi
          have hfr := hh.getThrowFrames w yf r
          generalize hq : h.getThrow w yf = q at m1 i1 hfr
          obtain ⟨w1, res⟩ := q
          simp only at m1 i1 hfr ⊢
          cases res with
          | error e => exact ⟨m1, i1⟩
          | ok mo =>
            cases mo with
            | none =>
              obtain ⟨m2, i2⟩ := throwHere_legal hh w1 r typ val tb i1
              exact ⟨m1.trans m2, i2⟩
            | some meth =>
              simp only
              have hd := delegating_legal w1 r (fun w' => h.callThrow w' meth typ val tb)
                (fun w' i' => hh.callThrow w' meth typ val tb i') i1 (hfr.trans hs)
              generalize delegating w1 r (fun w' => h.callThrow w' meth typ val tb) = p at hd
              obtain ⟨w2, res⟩ := p
              obtain ⟨m2, i2⟩ := hd
              obtain ⟨m3, i3⟩ := afterDelegate_legal hh w2 r res i2
              exact ⟨(m1.trans m2).trans m3, i3⟩

theorem genThrow_legal (hh : HooksLegal h) (fuel) (w : World V X) (r args) (hi : Inv w) :
    Mono w (genThrow h fuel w r args).1 ∧ Inv (genThrow h fuel w r args).1 := by
  simp only [genThrow]
  cases hc : (checkPositional "throw" args.length 1 3 : Option (Exc V)) with
  | some e => exact ⟨Mono.refl w, hi⟩
  | none =>
    simp only
    have hw : Mono w (if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
        else (w, none)).1 ∧ Inv (if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
        else (w, none)).1 := by
      split
      · exact hh.warn w _ hi
      · exact ⟨Mono.refl w, hi⟩
    generalize (if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
        else (w, none)) = q at hw
    obtain ⟨w1, warned⟩ := q
    obtain ⟨m, i⟩ := hw
    simp only at m i ⊢
    cases warned with
    | some e => exact ⟨m, i⟩
    | none =>
      obtain ⟨m2, i2⟩ := genThrowF_legal hh fuel w1 r true (unpackThrowArgs args).1
        (unpackThrowArgs args).2.1 (unpackThrowArgs args).2.2 i
      exact ⟨m.trans m2, i2⟩

end Send

section Async
variable {h : Hooks V X}

theorem Mono.setRunning {w w' : World V X} (m : Mono w w') (r : Ref) (b : Bool) :
    Mono w (w'.setRunning r b) := by
  refine ⟨?_, ?_, m.asend, m.athrow⟩
  · intro q; simpa using m.st q
  · intro q hc
    by_cases hq : q = r
    · subst hq; simpa [World.setRunning] using m.closed q hc
    · simpa [World.setRunning, hq] using m.closed q hc

theorem Mono.setClosed {w w' : World V X} (m : Mono w w') (r : Ref) :
    Mono w (w'.setClosed r) := by
  refine ⟨?_, ?_, m.asend, m.athrow⟩
  · intro q; simpa using m.st q
  · intro q hc
    by_cases hq : q = r
    · subst hq; simp [World.setClosed]
    · simpa [World.setClosed, hq] using m.closed q hc

theorem Inv.setRunning {w : World V X} (hi : Inv w) (r : Ref) (b : Bool) :
    Inv (w.setRunning r b) := by
  intro q hst
  by_cases hq : q = r
  · subst hq
    simp only [state_setRunning] at hst
    simpa [World.setRunning] using hi q hst
  · simp only [state_setRunning] at hst
    simpa [World.setRunning, hq] using hi q hst

theorem Inv.setClosed {w : World V X} (hi : Inv w) (r : Ref) : Inv (w.setClosed r) := by
  intro q hst
  by_cases hq : q = r
  · subst hq
    simp only [state_setClosed] at hst
    simpa [World.setClosed] using hi q hst
  · simp only [state_setClosed] at hst
    simpa [World.setClosed, hq] using hi q hst

theorem Mono.setAthrowClosed {w w' : World V X} (m : Mono w w') (a : Ref) :
    Mono w (w'.setAthrowState a .closed) := by
  refine ⟨m.st, m.closed, m.asend, ?_⟩
  intro q
  by_cases hq : q = a
  · subst hq
    simp only [World.setAthrowState, if_true]
    cases (w.athrows q).state <;> decide
  · simpa [World.setAthrowState, hq] using m.athrow q

theorem Mono.setAsendClosed {w w' : World V X} (m : Mono w w') (a : Ref) :
    Mono w (w'.setAsendState a .closed) := by
  refine ⟨m.st, m.closed, ?_, m.athrow⟩
  intro q
  by_cases hq : q = a
  · subst hq
    simp only [World.setAsendState, if_true]
    cases (w.asends q).state <;> decide
  · simpa [World.setAsendState, hq] using m.asend q

theorem unwrap_legal (w : World V X) (r) (res : Ret V) (hi : Inv w) :
    Mono w (asyncGenUnwrapValue w r res).1 ∧ Inv (asyncGenUnwrapValue w r res).1 := by
  cases res with
  | err e =>
    simp only [asyncGenUnwrapValue]
    split
    · exact ⟨((Mono.refl w).setClosed r).setRunning r false, (hi.setClosed r).setRunning r false⟩
    · exact ⟨(Mono.refl w).setRunning r false, hi.setRunning r false⟩
  | ok v =>
    cases v
    case wrapped o => exact ⟨(Mono.refl w).setRunning r false, hi.setRunning r false⟩
    all_goals exact ⟨Mono.refl w, hi⟩

theorem Mono.setAsendIter {w : World V X} (a : Ref) (hs : (w.asends a).state = .init) :
    Mono w (w.setAsendState a .iter) := by
  refine ⟨fun _ => legalEdge_refl _, fun _ h => h, ?_, fun _ => Nat.le_refl _⟩
  intro q
  by_cases hq : q = a
  · subst hq; simp [World.setAsendState, hs, AwaitableState.rank]
  · simp [World.setAsendState, hq]

theorem Mono.setAthrowIter {w : World V X} (a : Ref) (hs : (w.athrows a).state = .init) :
    Mono w (w.setAthrowState a .iter) := by
  refine ⟨fun _ => legalEdge_refl _, fun _ h => h, fun _ => Nat.le_refl _, ?_⟩
  intro q
  by_cases hq : q = a
  · subst hq; simp [World.setAthrowState, hs, AwaitableState.rank]
  · simp [World.setAthrowState, hq]

theorem Inv.setAsend {w : World V X} (hi : Inv w) (a s) : Inv (w.setAsendState a s) := hi
theorem Inv.setAthrow {w : World V X} (hi : Inv w) (a s) : Inv (w.setAthrowState a s) := hi

theorem asyncGenAsendSend_legal (hh : HooksLegal h) (w : World V X) (a arg) (hi : Inv w) :
    Mono w (asyncGenAsendSend h w a arg).1 ∧ Inv (asyncGenAsendSend h w a arg).1 := by
  simp only [asyncGenAsendSend]
  split
  · exact ⟨Mono.refl w, hi⟩
  split
  · exact ⟨(Mono.refl w).setAsendClosed a, hi⟩
  have hw1 : Mono w (if (w.asends a).state = .init then w.setAsendState a .iter else w) ∧
      Inv (if (w.asends a).state = .init then w.setAsendState a .iter else w) := by
    split
    · rename_i hs; exact ⟨Mono.setAsendIter a hs, hi⟩
    · exact ⟨Mono.refl w, hi⟩
  generalize (if (w.asends a).state = .init then w.setAsendState a .iter else w) = w1 at hw1 ⊢
  obtain ⟨m1, i1⟩ := hw1
  have m2 := m1.setRunning (w.asends a).gen true
  have i2 := i1.setRunning (w.asends a).gen true
  generalize hg : w1.setRunning (w.asends a).gen true = w2 at m2 i2 ⊢
  obtain ⟨m3, i3⟩ := genSendEx_legal hh w2 (w.asends a).gen
    (if (w.asends a).state = .init ∧ isNullOrNone arg = true then (w.asends a).sendval else arg)
    false none false i2
  simp only [genSend]
  generalize genSendEx h w2 (w.asends a).gen _ false none false = s at m3 i3
  obtain ⟨w3, res⟩ := s
  simp only at m3 i3 ⊢
  simp only [asendFinish]
  obtain ⟨m4, i4⟩ := unwrap_legal w3 (w.asends a).gen res i3
  generalize asyncGenUnwrapValue w3 (w.asends a).gen res = u at m4 i4
  obtain ⟨w4, r4⟩ := u
  simp only at m4 i4 ⊢
  cases r4 with
  | ok v => exact ⟨(m2.trans m3).trans m4, i4⟩
  | err e => exact ⟨((m2.trans m3).trans m4).setAsendClosed a, i4⟩

theorem asyncGenAsendThrow_legal (hh : HooksLegal h) (fuel) (w : World V X) (a args) (hi : Inv w) :
    Mono w (asyncGenAsendThrow h fuel w a args).1 ∧ Inv (asyncGenAsendThrow h fuel w a args).1 := by
  simp only [asyncGenAsendThrow]
  split
  · exact ⟨Mono.refl w, hi⟩
  split
  · exact ⟨(Mono.refl w).setAsendClosed a, hi⟩
  have hw1 : Mono w (if (w.asends a).state = .init then
        (w.setAsendState a .iter).setRunning (w.asends a).gen true else w) ∧
      Inv (if (w.asends a).state = .init then
        (w.setAsendState a .iter).setRunning (w.asends a).gen true else w) := by
    split
    · rename_i hs
      exact ⟨(Mono.setAsendIter a hs).setRunning _ true, (hi.setAsend a _).setRunning _ true⟩
    · exact ⟨Mono.refl w, hi⟩
  generalize (if (w.asends a).state = .init then
        (w.setAsendState a .iter).setRunning (w.asends a).gen true else w) = w1 at hw1 ⊢
  obtain ⟨m1, i1⟩ := hw1
  obtain ⟨m3, i3⟩ := genThrow_legal hh fuel w1 (w.asends a).gen args i1
  generalize genThrow h fuel w1 (w.asends a).gen args = s at m3 i3
  obtain ⟨w3, res⟩ := s
  simp only at m3 i3 ⊢
  simp only [asendThrowFinish]
  obtain ⟨m4, i4⟩ := unwrap_legal w3 (w.asends a).gen res i3
  generalize asyncGenUnwrapValue w3 (w.asends a).gen res = u at m4 i4
  obtain ⟨w4, r4⟩ := u
  simp only at m4 i4 ⊢
  cases r4 with
  | ok v => exact ⟨(m1.trans m3).trans m4, i4⟩
  | err e =>
    exact ⟨(((m1.trans m3).trans m4).setRunning _ false).setAsendClosed a, i4.setRunning _ false⟩

theorem athrowCheckError_legal {w0 w : World V X} (m : Mono w0 w) (hi : Inv w) (a gen acl e) :
    Mono w0 (athrowCheckError w a gen acl e).1 ∧ Inv (athrowCheckError w a gen acl e).1 := by
  simp only [athrowCheckError]
  split <;> exact ⟨(m.setRunning gen false).setAthrowClosed a, hi.setRunning gen false⟩

theorem acloseTail_legal {w0 w : World V X} (m : Mono w0 w) (hi : Inv w) (a gen) (t : Ret V) :
    Mono w0 (acloseTail w a gen t).1 ∧ Inv (acloseTail w a gen t).1 := by
  cases t with
  | err e => exact athrowCheckError_legal m hi a gen true e
  | ok v =>
    cases v
    case wrapped o => exact ⟨(m.setRunning gen false).setAthrowClosed a, hi.setRunning gen false⟩
    all_goals exact ⟨m, hi⟩

theorem athrowStartAclose_legal (hh : HooksLegal h) (fuel) (w : World V X) (a gen) (hi : Inv w) :
    Mono w (athrowStartAclose h fuel w a gen).1 ∧ Inv (athrowStartAclose h fuel w a gen).1 := by
  simp only [athrowStartAclose]
  have m1 := (Mono.refl w).setClosed gen
  have i1 := hi.setClosed gen
  obtain ⟨m2, i2⟩ := genThrowF_legal hh fuel (w.setClosed gen) gen false
    (.excClass .generatorExit "GeneratorExit") none none i1
  exact acloseTail_legal (m1.trans m2) i2 a gen _

theorem athrowStartArgs_legal (hh : HooksLegal h) (fuel) (w : World V X) (a gen args) (hi : Inv w) :
    Mono w (athrowStartArgs h fuel w a gen args).1 ∧ Inv (athrowStartArgs h fuel w a gen args).1 := by
  simp only [athrowStartArgs]
  cases hc : (checkPositional "athrow" args.length 1 3 : Option (Exc V)) with
  | some e => exact ⟨Mono.refl w, hi⟩
  | none =>
    simp only
    obtain ⟨m2, i2⟩ := genThrowF_legal hh fuel w gen false (unpackThrowArgs args).1
      (unpackThrowArgs args).2.1 (unpackThrowArgs args).2.2 hi
    generalize genThrowF h fuel w gen false _ _ _ = t at m2 i2
    obtain ⟨w2, res⟩ := t
    simp only at m2 i2 ⊢
    obtain ⟨m3, i3⟩ := unwrap_legal w2 gen res i2
    generalize asyncGenUnwrapValue w2 gen res = u at m3 i3
    obtain ⟨w3, r3⟩ := u
    simp only at m3 i3 ⊢
    cases r3 with
    | ok v => exact ⟨m2.trans m3, i3⟩
    | err e => exact athrowCheckError_legal (m2.trans m3) i3 a gen false e

theorem athrowIter_legal (hh : HooksLegal h) (w : World V X) (a gen args arg) (hi : Inv w) :
    Mono w (athrowIter h w a gen args arg).1 ∧ Inv (athrowIter h w a gen args arg).1 := by
  simp only [athrowIter]
  obtain ⟨m2, i2⟩ := genSendEx_legal hh w gen (some arg) false none false hi
  simp only [genSend]
  generalize genSendEx h w gen (some arg) false none false = t at m2 i2
  obtain ⟨w2, res⟩ := t
  simp only at m2 i2 ⊢
  cases args with
  | some l =>
    obtain ⟨m3, i3⟩ := unwrap_legal w2 gen res i2
    exact ⟨m2.trans m3, i3⟩
  | none => exact acloseTail_legal m2 i2 a gen res

theorem asyncGenAthrowSend_legal (hh : HooksLegal h) (fuel) (w : World V X) (a arg) (hi : Inv w) :
    Mono w (asyncGenAthrowSend h fuel w a arg).1 ∧ Inv (asyncGenAthrowSend h fuel w a arg).1 := by
  simp only [asyncGenAthrowSend]
  split
  · exact ⟨Mono.refl w, hi⟩
  split
  · exact ⟨(Mono.refl w).setAthrowClosed a, hi⟩
  split
  · rename_i hs
    split
    · exact ⟨(Mono.refl w).setAthrowClosed a, hi⟩
    split
    · exact ⟨(Mono.refl w).setAthrowClosed a, hi⟩
    split
    · exact ⟨Mono.refl w, hi⟩
    have m1 := (Mono.setAthrowIter a hs).setRunning (w.athrows a).gen true
    have i1 := (hi.setAthrow a .iter).setRunning (w.athrows a).gen true
    split
    · rename_i hargs
      obtain ⟨m2, i2⟩ := athrowStartAclose_legal hh fuel _ a (w.athrows a).gen i1
      exact ⟨m1.trans m2, i2⟩
    · rename_i hargs
      obtain ⟨m2, i2⟩ := athrowStartArgs_legal hh fuel _ a (w.athrows a).gen _ i1
      exact ⟨m1.trans m2, i2⟩
  · exact athrowIter_legal hh w a _ _ arg hi

theorem athrowThrowFinish_legal {w0 w : World V X} (m : Mono w0 w) (hi : Inv w) (a gen args)
    (res : Ret V) :
    Mono w0 (athrowThrowFinish w a gen args res).1 ∧ Inv (athrowThrowFinish w a gen args res).1 := by
  cases args with
  | some l =>
    simp only [athrowThrowFinish]
    obtain ⟨m3, i3⟩ := unwrap_legal w gen res hi
    generalize asyncGenUnwrapValue w gen res = u at m3 i3
    obtain ⟨w3, r3⟩ := u
    simp only at m3 i3 ⊢
    cases r3 with
    | ok v => exact ⟨m.trans m3, i3⟩
    | err e =>
      exact ⟨((m.trans m3).setRunning gen false).setAthrowClosed a, i3.setRunning gen false⟩
  | none =>
    cases res with
    | err e =>
      simp only [athrowThrowFinish]
      split <;> exact ⟨(m.setRunning gen false).setAthrowClosed a, hi.setRunning gen false⟩
    | ok v =>
      cases v
      case wrapped o => exact ⟨(m.setRunning gen false).setAthrowClosed a, hi.setRunning gen false⟩
      all_goals exact ⟨m, hi⟩

theorem asyncGenAthrowThrow_legal (hh : HooksLegal h) (fuel) (w : World V X) (a args) (hi : Inv w) :
    Mono w (asyncGenAthrowThrow h fuel w a args).1 ∧ Inv (asyncGenAthrowThrow h fuel w a args).1 := by
  simp only [asyncGenAthrowThrow]
  split
  · exact ⟨Mono.refl w, hi⟩
  split
  · exact ⟨(Mono.refl w).setAthrowClosed a, hi⟩
  have hw1 : Mono w (if (w.athrows a).state = .init then
        (w.setAthrowState a .iter).setRunning (w.athrows a).gen true else w) ∧
      Inv (if (w.athrows a).state = .init then
        (w.setAthrowState a .iter).setRunning (w.athrows a).gen true else w) := by
    split
    · rename_i hs
      exact ⟨(Mono.setAthrowIter a hs).setRunning _ true, (hi.setAthrow a _).setRunning _ true⟩
    · exact ⟨Mono.refl w, hi⟩
  generalize (if (w.athrows a).state = .init then
        (w.setAthrowState a .iter).setRunning (w.athrows a).gen true else w) = w1 at hw1 ⊢
  obtain ⟨m1, i1⟩ := hw1
  obtain ⟨m3, i3⟩ := genThrow_legal hh fuel w1 (w.athrows a).gen args i1
  exact athrowThrowFinish_legal (m1.trans m3) i3 a _ _ _

end Async

/-- `gen_close` and `gen_throw` move every generator in the world only along legal
edges, restore the state they bracket with `FRAME_EXECUTING`, and leave `ag_closed`
and the awaitables monotone, for all arguments, all frame outcomes and every
reentrant use of the model from the hooks. Hypotheses: `HooksLegal` and `Inv`. -/
def GenOpsStateEdges : Prop :=
  ∀ (V X : Type) (h : Hooks V X), HooksLegal h →
  ∀ (fuel : Nat) (w : World V X) (r : Ref) (args : List (Obj V)), Inv w →
    Mono w (genCloseF h fuel w r).1 ∧ Mono w (genThrow h fuel w r args).1

theorem genOpsStateEdges_proven : GenOpsStateEdges :=
  fun _ _ _ hh fuel w r args hi =>
    ⟨(genCloseF_legal hh fuel w r hi).1, (genThrow_legal hh fuel w r args hi).1⟩

/-- The same for the awaitables' `send` and `throw`: `init -> iter -> closed` only,
frame states along legal edges, `ag_closed` only set. -/
def AsyncOpsStateEdges : Prop :=
  ∀ (V X : Type) (h : Hooks V X), HooksLegal h →
  ∀ (fuel : Nat) (w : World V X) (a : Ref) (arg : Option (Obj V)) (arg' : Obj V)
    (args : List (Obj V)), Inv w →
    Mono w (asyncGenAsendSend h w a arg).1 ∧ Mono w (asyncGenAsendThrow h fuel w a args).1 ∧
    Mono w (asyncGenAthrowSend h fuel w a arg').1 ∧ Mono w (asyncGenAthrowThrow h fuel w a args).1

theorem asyncOpsStateEdges_proven : AsyncOpsStateEdges :=
  fun _ _ _ hh fuel w a arg arg' args hi =>
    ⟨(asyncGenAsendSend_legal hh w a arg hi).1, (asyncGenAsendThrow_legal hh fuel w a args hi).1,
     (asyncGenAthrowSend_legal hh fuel w a arg' hi).1, (asyncGenAthrowThrow_legal hh fuel w a args hi).1⟩

end PyLean.Bytecode.GenObj
