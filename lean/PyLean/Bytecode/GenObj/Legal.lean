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

/-- What is assumed of the interpreter. Python code run by a hook acts on these
objects only through the model's own operations, so it preserves `Mono`. That is all: on
3.15 nothing else is needed, because every operation on a `FRAME_EXECUTING` generator is
refused before it touches the frame, and because `_gen_throw` marks the generator before
it looks up `throw`. -/
structure HooksLegal (h : Hooks V X) : Prop where
  resume : ∀ w r a e, Mono w (h.resume w r a e).1
  getClose : ∀ w o, Mono w (h.getClose w o).1
  getThrow : ∀ w o, Mono w (h.getThrow w o).1
  callNoArgs : ∀ w m, Mono w (h.callNoArgs w m).1
  callThrow : ∀ w m a b c, Mono w (h.callThrow w m a b c).1
  unraisable : ∀ w m e, Mono w (h.unraisable w m e)
  warn : ∀ w m, Mono w (h.warn w m).1
  normalize : ∀ w t v, Mono w (h.normalize w t v).1

/-- `HooksLegal` can be met: a frame that re-raises what is thrown and touches nothing. -/
theorem noopHooks_legal : HooksLegal noopHooks where
  resume _ _ _ _ := Mono.refl _
  getClose _ _ := Mono.refl _
  getThrow _ _ := Mono.refl _
  callNoArgs _ _ := Mono.refl _
  callThrow _ _ _ _ _ := Mono.refl _
  unraisable _ _ _ := Mono.refl _
  warn _ _ := Mono.refl _
  normalize _ _ _ := Mono.refl _

/-- A frame marked `FRAME_EXECUTING` stays so across anything that preserves `Mono`. -/
theorem Mono.executing {a b : World V X} (m : Mono a b) {r : Ref}
    (hs : (a.get r).state = .executing) : (b.get r).state = .executing := by
  have := m.st r
  rw [hs] at this
  cases hk : (b.get r).state <;> rw [hk] at this <;> first | rfl | exact absurd this (by decide)

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

theorem legal_to_cleared (s : FrameState) (h : s ≠ .executing) : legalEdge s .cleared = true := by
  cases s <;> first | rfl | exact absurd rfl h

theorem legal_to_oparg (s : FrameState) (b : Bool)
    (h1 : s ≠ .executing) (h2 : s.finished = false) : legalEdge s (FrameState.ofOparg b) = true := by
  cases s <;> cases b <;> first | rfl | exact absurd rfl h1 | (simp at h2)

section Send
variable {h : Hooks V X}

theorem get_clear_ne (w : World V X) {r q : Ref} (hq : q ≠ r) :
    (clearGenFrame w r).get q = w.get q := get_setState_ne _ _ hq

/-- `gen_send_ex2` on a generator that was in state `(w0.get r).state` and has been marked
`FRAME_EXECUTING`, then went through anything legal. -/
theorem genSendEx2_legal (hh : HooksLegal h) {w0 w : World V X} {r : Ref} (arg e)
    (h2 : (w0.get r).state ≠ .executing) (h3 : (w0.get r).state.finished = false)
    (m0 : Mono (w0.setState r .executing) w) : Mono w0 (genSendEx2 h w r arg e).1 := by
  simp only [genSendEx2]
  have m1 := m0.trans (hh.resume w r (arg.getD .none) e)
  generalize h.resume w r (arg.getD .none) e = res at m1
  obtain ⟨w2, o⟩ := res
  simp only at m1 ⊢
  have hcl : Mono w0 (clearGenFrame w2 r) := by
    apply mono_write m1
    · intro q hq; exact get_clear_ne _ hq
    · simpa [clearGenFrame] using legal_to_cleared _ h2
    · simp [clearGenFrame, World.setState]
    · rfl
    · rfl
  cases o with
  | yielded oparg v d top =>
    simp only [finishResume]
    apply mono_write m1
    · intro q hq; simp [suspendFrame, hq]
    · simpa [suspendFrame] using legal_to_oparg _ oparg h2 h3
    · simp [suspendFrame]
    · rfl
    · rfl
  | raised e => simpa only [finishResume] using hcl
  | returned v =>
    simp only [finishResume]
    split <;> exact hcl

theorem genSendEx_legal (hh : HooksLegal h) (w : World V X) (r arg) :
    Mono w (genSendEx h w r arg).1 := by
  by_cases hrej : SendRejected (w.get r) arg
  · rw [(genSendRejectedNoEffect_proven V X h h w r arg hrej).1]
    exact Mono.refl w
  have h1 : ¬ ((w.get r).state = .created ∧ isNonNull arg = true) := fun c => hrej (Or.inl c)
  have h2 : (w.get r).state ≠ .executing := fun c => hrej (Or.inr (Or.inl c))
  have h3 : (w.get r).state.finished = false := by
    cases hf : (w.get r).state.finished with
    | false => rfl
    | true => exact absurd (Or.inr (Or.inr hf)) hrej
  rw [genSendEx_live h w r arg h1 h2 h3]
  exact genSendEx2_legal hh arg none h2 h3 (Mono.refl _)

theorem genCloseFinish_fst (w : World V X) (r p) :
    (genCloseFinish h w r p).1 = (genSendEx2 h w r (some .none) p).1 := by
  simp only [genCloseFinish]
  generalize (genSendEx2 h w r (some .none) p) = s
  obtain ⟨w', res⟩ := s
  cases res with
  | next v => rfl
  | ret v => rfl
  | err e =>
    cases e with
    | none => rfl
    | some x => simp only; split <;> rfl

theorem genThrowCurrent_legal (hh : HooksLegal h) {w0 w : World V X} {r : Ref} (e)
    (h2 : (w0.get r).state ≠ .executing) (h3 : (w0.get r).state.finished = false)
    (m0 : Mono (w0.setState r .executing) w) : Mono w0 (genThrowCurrent h w r e).1 :=
  genSendEx2_legal hh _ e h2 h3 m0

theorem genCloseIter_legal (hh : HooksLegal h) (c : World V X → Ref → World V X × Ret V)
    (hc : ∀ w r, Mono w (c w r).1) (w : World V X) (yf) :
    Mono w (genCloseIter h c w yf).1 := by
  simp only [genCloseIter]
  split
  · rename_i r _
    have := hc w r
    generalize c w r = p at this
    obtain ⟨w', res⟩ := p
    cases res <;> exact this
  · simp only [genCloseIterForeign]
    have m1 := hh.getClose w yf
    generalize h.getClose w yf = a at m1
    obtain ⟨wa, ra⟩ := a
    simp only at m1 ⊢
    have hmeth : Mono wa (closeMeth h wa ra).1 := by
      cases ra with
      | error e => exact hh.unraisable wa _ e
      | ok mo => exact Mono.refl _
    generalize closeMeth h wa ra = m at hmeth
    obtain ⟨wm, mo⟩ := m
    simp only at hmeth ⊢
    cases mo with
    | none => exact m1.trans hmeth
    | some mt =>
      simp only
      have m3 := hh.callNoArgs wm mt
      generalize h.callNoArgs wm mt = c3 at m3
      obtain ⟨w3, r3⟩ := c3
      cases r3 <;> exact (m1.trans hmeth).trans m3

theorem closeDelegate_legal (hh : HooksLegal h) (c : World V X → Ref → World V X × Ret V)
    (hc : ∀ w r, Mono w (c w r).1) (w : World V X) (r s) :
    Mono w (closeDelegate h c w r s).1 := by
  simp only [closeDelegate]
  split
  · exact genCloseIter_legal hh c hc w _
  · exact Mono.refl w

/-- `FRAME_CLEARED` and `gen_clear_frame`, the writes of :472-475 and :508-509. -/
theorem clear_legal {w0 w : World V X} {r : Ref} {s : FrameState} (hs : (w0.get r).state ≠ .executing)
    (m : Mono (w0.setState r s) w) : Mono w0 (genClearFrame (w.setState r .cleared) r) := by
  apply mono_write m
  · intro q hq
    simp only [genClearFrame]
    rw [World.get_set_ne _ _ hq, get_setState_ne _ _ hq]
  · simpa [genClearFrame] using legal_to_cleared _ hs
  · simp [genClearFrame, World.setState]
  · rfl
  · rfl

theorem genCloseF_legal (hh : HooksLegal h) (n : Nat) :
    ∀ (w : World V X) (r), Mono w (genCloseF h n w r).1 := by
  induction n with
  | zero => intro w r; exact Mono.refl w
  | succ n ih =>
    intro w r
    simp only [genCloseF]
    split
    · rename_i hc
      have m0 : Mono (w.setState r (w.get r).state) w := by rw [setState_self]; exact Mono.refl w
      exact clear_legal (by simp [hc]) m0
    · rename_i hc0
      split
      · exact Mono.refl w
      · rename_i hf0
        have h3 : (w.get r).state.finished = false := by simpa using hf0
        split
        · exact Mono.refl w
        · rename_i hx
          simp only [genCloseBody]
          have m := closeDelegate_legal hh (genCloseF h n) ih (w.setState r .executing) r (w.get r).state
          generalize closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state = p at m
          obtain ⟨w1, st⟩ := p
          simp only at m ⊢
          split
          · exact clear_legal hx m
          · rw [genCloseFinish_fst]
            exact genSendEx2_legal hh _ _ hx h3 m

/-- `gen_set_exception` runs Python code only through `normalize`. -/
theorem genSetException_mono (hh : HooksLegal h) (w : World V X) (typ val tb) :
    Mono w (genSetException h w typ val tb).1 := by
  unfold genSetException
  split
  · exact Mono.refl _
  · split
    · exact hh.normalize _ _ _
    · split <;> exact Mono.refl _
    · exact Mono.refl _

theorem throwHere_legal (hh : HooksLegal h) {w0 w : World V X} {r : Ref} (typ val tb)
    (h2 : (w0.get r).state ≠ .executing) (h3 : (w0.get r).state.finished = false)
    (m : Mono (w0.setState r .executing) w) :
    Mono w0 (throwHere h w r (w0.get r).state typ val tb).1 := by
  simp only [throwHere]
  have m2 := m.trans (genSetException_mono hh w typ val tb)
  split
  · exact genThrowCurrent_legal hh _ h2 h3 m2
  · simp only
    apply mono_write m2
    · intro q hq; exact get_setState_ne _ _ hq
    · simpa using legalEdge_refl _
    · simp [World.setState]
    · rfl
    · rfl

theorem afterDelegate_legal (hh : HooksLegal h) {w0 w : World V X} {r : Ref} (x : Ret V)
    (h2 : (w0.get r).state ≠ .executing) (h3 : (w0.get r).state.finished = false)
    (m : Mono (w0.setState r .executing) w) :
    Mono w0 (afterDelegate h w r (w0.get r).state x).1 := by
  cases x with
  | ok v =>
    simp only [afterDelegate]
    apply mono_write m
    · intro q hq; exact get_setState_ne _ _ hq
    · simpa using legalEdge_refl _
    · simp [World.setState]
    · rfl
    · rfl
  | err e => exact genThrowCurrent_legal hh _ h2 h3 m

theorem genThrowF_legal (hh : HooksLegal h) (n : Nat) :
    ∀ (w : World V X) (r c typ val tb), Mono w (genThrowF h n w r c typ val tb).1 := by
  induction n with
  | zero => intro w r c typ val tb; exact Mono.refl w
  | succ n ih =>
    intro w r c typ val tb
    simp only [genThrowF]
    split
    · exact Mono.refl w
    · rename_i h2
      split
      · split
        · exact Mono.refl w
        · split <;> exact genSetException_mono hh w _ _ _
      · rename_i hf0
        have h3 : (w.get r).state.finished = false := by simpa using hf0
        have m0 := Mono.refl (w.setState r .executing)
        split
        · split
          · have m := genCloseIter_legal hh (genCloseF h n) (genCloseF_legal hh n)
              (w.setState r .executing) ((w.setState r .executing).get r).stackTop
            generalize genCloseIter h (genCloseF h n) (w.setState r .executing) _ = p at m
            obtain ⟨w1, st⟩ := p
            simp only at m ⊢
            cases st with
            | fail e => exact genThrowCurrent_legal hh _ h2 h3 m
            | ok => exact throwHere_legal hh typ val tb h2 h3 m
          · split
            · rename_i sub _
              have m := ih (w.setState r .executing) sub c typ val tb
              generalize genThrowF h n (w.setState r .executing) sub c typ val tb = p at m
              obtain ⟨w1, res⟩ := p
              exact afterDelegate_legal hh res h2 h3 m
            · have m1 := hh.getThrow (w.setState r .executing) ((w.setState r .executing).get r).stackTop
              generalize h.getThrow (w.setState r .executing) _ = q at m1
              obtain ⟨w1, res⟩ := q
              simp only at m1 ⊢
              cases res with
              | error e =>
                simp only
                apply mono_write m1
                · intro q hq; exact get_setState_ne _ _ hq
                · simpa using legalEdge_refl _
                · simp [World.setState]
                · rfl
                · rfl
              | ok mo =>
                cases mo with
                | none => exact throwHere_legal hh typ val tb h2 h3 m1
                | some meth =>
                  simp only
                  have m2 := m1.trans (hh.callThrow w1 meth typ val tb)
                  generalize h.callThrow w1 meth typ val tb = p at m2
                  obtain ⟨w2, res⟩ := p
                  exact afterDelegate_legal hh res h2 h3 m2
        · exact throwHere_legal hh typ val tb h2 h3 m0

theorem genThrow_legal (hh : HooksLegal h) (fuel) (w : World V X) (r args) :
    Mono w (genThrow h fuel w r args).1 := by
  simp only [genThrow]
  cases hc : (checkPositional "throw" args.length 1 3 : Option (Exc V)) with
  | some e => exact Mono.refl w
  | none =>
    simp only
    have hw : Mono w (if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
        else (w, none)).1 := by
      split
      · exact hh.warn w _
      · exact Mono.refl w
    generalize (if args.length > 1 then
        h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead."
        else (w, none)) = q at hw
    obtain ⟨w1, warned⟩ := q
    simp only at hw ⊢
    cases warned with
    | some e => exact hw
    | none => exact hw.trans (genThrowF_legal hh fuel w1 r true _ _ _)

/-- `gen_close` with a resume that is `bad` off `FRAME_EXECUTING`. On 3.15 `gen_close` does
not re-check the state after `gen_close_iter` ran Python code, so what keeps a `CLEARED`
frame from being resumed is that this code cannot move a frame out of `FRAME_EXECUTING`:
`HooksLegal`. -/
theorem genCloseF_guard (hh : HooksLegal h) (bad) (n : Nat) :
    ∀ (w : World V X) (r), genCloseF (guardResume h bad) n w r = genCloseF h n w r := by
  induction n with
  | zero => intro w r; rfl
  | succ n ih =>
    intro w r
    have hc : genCloseF (guardResume h bad) n = genCloseF h n := by
      funext w r; exact ih w r
    simp only [genCloseF, hc]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp only [genCloseBody]
          have hd : closeDelegate (guardResume h bad) (genCloseF h n) (w.setState r .executing) r
              (w.get r).state = closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state := rfl
          rw [hd]
          have m := closeDelegate_legal hh (genCloseF h n) (genCloseF_legal hh n)
            (w.setState r .executing) r (w.get r).state
          generalize closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state = p at m
          obtain ⟨w1, st⟩ := p
          simp only at m ⊢
          have hx : (w1.get r).state = .executing := m.executing (by simp)
          split
          · rfl
          · simp only [genCloseFinish, genSendEx2_guard h bad w1 r _ _ hx]

theorem genThrowCurrent_guard (bad) (w : World V X) (r e) (hs : (w.get r).state = .executing) :
    genThrowCurrent (guardResume h bad) w r e = genThrowCurrent h w r e := by
  simp only [genThrowCurrent, genSendEx2_guard h bad w r _ _ hs]

theorem throwHere_guard (hh : HooksLegal h) (bad) (w : World V X) (r s typ val tb)
    (hs : (w.get r).state = .executing) :
    throwHere (guardResume h bad) w r s typ val tb = throwHere h w r s typ val tb := by
  have hse : ∀ w : World V X, genSetException (guardResume h bad) w typ val tb =
      genSetException h w typ val tb := fun _ => rfl
  simp only [throwHere, hse]
  split
  · exact genThrowCurrent_guard bad _ r _ ((genSetException_mono hh w typ val tb).executing hs)
  · rfl

theorem afterDelegate_guard (bad) (w : World V X) (r s) (x : Ret V) (hs : (w.get r).state = .executing) :
    afterDelegate (guardResume h bad) w r s x = afterDelegate h w r s x := by
  cases x with
  | ok v => rfl
  | err e => exact genThrowCurrent_guard bad w r e hs

theorem genThrowF_guard (hh : HooksLegal h) (bad) (n : Nat) :
    ∀ (w : World V X) (r c typ val tb),
      genThrowF (guardResume h bad) n w r c typ val tb = genThrowF h n w r c typ val tb := by
  induction n with
  | zero => intro w r c typ val tb; rfl
  | succ n ih =>
    intro w r c typ val tb
    have hc : genCloseF (guardResume h bad) n = genCloseF h n := by
      funext w r; exact genCloseF_guard hh bad n w r
    have hse : ∀ w : World V X, genSetException (guardResume h bad) w typ val tb =
      genSetException h w typ val tb := fun _ => rfl
    have hx0 : ((w.setState r .executing).get r).state = .executing := by simp
    simp only [genThrowF, hse, hc, ih]
    split
    · rfl
    · split
      · rfl
      · split
        · split
          · have hi : genCloseIter (guardResume h bad) (genCloseF h n) (w.setState r .executing)
                ((w.setState r .executing).get r).stackTop =
                genCloseIter h (genCloseF h n) (w.setState r .executing)
                ((w.setState r .executing).get r).stackTop := rfl
            rw [hi]
            have m := genCloseIter_legal hh (genCloseF h n) (genCloseF_legal hh n)
              (w.setState r .executing) ((w.setState r .executing).get r).stackTop
            generalize genCloseIter h (genCloseF h n) (w.setState r .executing) _ = p at m
            obtain ⟨w1, st⟩ := p
            have hx : (w1.get r).state = .executing := m.executing hx0
            cases st with
            | fail e => exact genThrowCurrent_guard bad w1 r e hx
            | ok => exact throwHere_guard hh bad w1 r _ typ val tb hx
          · split
            · rename_i sub _
              have m := genThrowF_legal hh n (w.setState r .executing) sub c typ val tb
              generalize genThrowF h n (w.setState r .executing) sub c typ val tb = p at m
              obtain ⟨w1, res⟩ := p
              exact afterDelegate_guard bad w1 r _ res (m.executing hx0)
            · have hg : (guardResume h bad).getThrow = h.getThrow := rfl
              rw [hg]
              have m1 := hh.getThrow (w.setState r .executing) ((w.setState r .executing).get r).stackTop
              generalize h.getThrow (w.setState r .executing) _ = q at m1
              obtain ⟨w1, res⟩ := q
              simp only at m1 ⊢
              have hx1 := m1.executing hx0
              cases res with
              | error e => rfl
              | ok mo =>
                cases mo with
                | none => exact throwHere_guard hh bad w1 r _ typ val tb hx1
                | some meth =>
                  simp only
                  have hcl : (guardResume h bad).callThrow = h.callThrow := rfl
                  rw [hcl]
                  have m2 := m1.trans (hh.callThrow w1 meth typ val tb)
                  generalize h.callThrow w1 meth typ val tb = p at m2
                  obtain ⟨w2, res⟩ := p
                  exact afterDelegate_guard bad w2 r _ res (m2.executing hx0)
        · exact throwHere_guard hh bad _ r _ typ val tb hx0

end Send

/-- Every resume, through `gen_send_ex`, `gen_close` or `_gen_throw` at any delegation
depth, sees the frame marked `FRAME_EXECUTING`: replacing `resume` by anything at all on
other states changes nothing, so a `CLEARED` frame is never resumed. Hypothesis:
`HooksLegal`. `gen_send_ex` needs no hypothesis, since it writes the state itself just before
the resume. `gen_close` and `_gen_throw` run Python code between their write and the
resume and do not look again, which is sound because that code cannot change a
`FRAME_EXECUTING` state through the model's operations, each of which refuses it. -/
def GenResumeSeesExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (bad : World V X × ResumeOutcome V), HooksLegal h →
  ∀ (n : Nat) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (c : Bool) (typ : Obj V) (val tb : Option (Obj V)),
    genSendEx (guardResume h bad) w r arg = genSendEx h w r arg ∧
    genCloseF (guardResume h bad) n w r = genCloseF h n w r ∧
    genThrowF (guardResume h bad) n w r c typ val tb = genThrowF h n w r c typ val tb

theorem genResumeSeesExecuting_proven : GenResumeSeesExecuting :=
  fun _ _ h bad hh n w r arg c typ val tb =>
    ⟨genSendEx_guard h bad w r arg, genCloseF_guard hh bad n w r,
     genThrowF_guard hh bad n w r c typ val tb⟩

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

theorem unwrap_legal (w : World V X) (r) (res : Ret V) :
    Mono w (asyncGenUnwrapValue w r res).1 := by
  cases res with
  | err e =>
    simp only [asyncGenUnwrapValue]
    split
    · exact ((Mono.refl w).setClosed r).setRunning r false
    · exact (Mono.refl w).setRunning r false
  | ok v =>
    cases v
    case wrapped o => exact (Mono.refl w).setRunning r false
    all_goals exact Mono.refl w

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

theorem genSend_legal (hh : HooksLegal h) (w : World V X) (r arg) :
    Mono w (genSend h w r arg).1 := genSendEx_legal hh w r arg

theorem asyncGenAsendSend_legal (hh : HooksLegal h) (w : World V X) (a arg) :
    Mono w (asyncGenAsendSend h w a arg).1 := by
  simp only [asyncGenAsendSend]
  split
  · exact Mono.refl w
  split
  · exact (Mono.refl w).setAsendClosed a
  have hw1 : Mono w (if (w.asends a).state = .init then w.setAsendState a .iter else w) := by
    split
    · rename_i hs; exact Mono.setAsendIter a hs
    · exact Mono.refl w
  generalize (if (w.asends a).state = .init then w.setAsendState a .iter else w) = w1 at hw1 ⊢
  have m2 := hw1.setRunning (w.asends a).gen true
  generalize hg : w1.setRunning (w.asends a).gen true = w2 at m2 ⊢
  have m3 := genSend_legal hh w2 (w.asends a).gen
    (if (w.asends a).state = .init ∧ isNullOrNone arg = true then (w.asends a).sendval else arg)
  generalize genSend h w2 (w.asends a).gen _ = s at m3
  obtain ⟨w3, res⟩ := s
  simp only at m3 ⊢
  simp only [asendFinish]
  have m4 := unwrap_legal w3 (w.asends a).gen res
  generalize asyncGenUnwrapValue w3 (w.asends a).gen res = u at m4
  obtain ⟨w4, r4⟩ := u
  simp only at m4 ⊢
  cases r4 with
  | ok v => exact (m2.trans m3).trans m4
  | err e => exact ((m2.trans m3).trans m4).setAsendClosed a

theorem asyncGenAsendThrow_legal (hh : HooksLegal h) (fuel) (w : World V X) (a args) :
    Mono w (asyncGenAsendThrow h fuel w a args).1 := by
  simp only [asyncGenAsendThrow]
  split
  · exact Mono.refl w
  split
  · exact (Mono.refl w).setAsendClosed a
  have hw1 : Mono w (if (w.asends a).state = .init then
        (w.setAsendState a .iter).setRunning (w.asends a).gen true else w) := by
    split
    · rename_i hs
      exact (Mono.setAsendIter a hs).setRunning _ true
    · exact Mono.refl w
  generalize (if (w.asends a).state = .init then
        (w.setAsendState a .iter).setRunning (w.asends a).gen true else w) = w1 at hw1 ⊢
  have m3 := genThrow_legal hh fuel w1 (w.asends a).gen args
  generalize genThrow h fuel w1 (w.asends a).gen args = s at m3
  obtain ⟨w3, res⟩ := s
  simp only at m3 ⊢
  simp only [asendThrowFinish]
  have m4 := unwrap_legal w3 (w.asends a).gen res
  generalize asyncGenUnwrapValue w3 (w.asends a).gen res = u at m4
  obtain ⟨w4, r4⟩ := u
  simp only at m4 ⊢
  cases r4 with
  | ok v => exact (hw1.trans m3).trans m4
  | err e => exact (((hw1.trans m3).trans m4).setRunning _ false).setAsendClosed a

theorem athrowCheckError_legal {w0 w : World V X} (m : Mono w0 w) (a gen acl e) :
    Mono w0 (athrowCheckError w a gen acl e).1 := by
  simp only [athrowCheckError]
  split <;> exact (m.setRunning gen false).setAthrowClosed a

theorem acloseTail_legal {w0 w : World V X} (m : Mono w0 w) (a gen) (t : Ret V) :
    Mono w0 (acloseTail w a gen t).1 := by
  cases t with
  | err e => exact athrowCheckError_legal m a gen true e
  | ok v =>
    cases v
    case wrapped o => exact (m.setRunning gen false).setAthrowClosed a
    all_goals exact m

theorem athrowStartAclose_legal (hh : HooksLegal h) (fuel) (w : World V X) (a gen) :
    Mono w (athrowStartAclose h fuel w a gen).1 := by
  simp only [athrowStartAclose]
  have m1 := (Mono.refl w).setClosed gen
  have m2 := genThrowF_legal hh fuel (w.setClosed gen) gen false
    (.excClass .generatorExit "GeneratorExit") none none
  exact acloseTail_legal (m1.trans m2) a gen _

theorem athrowStartArgs_legal (hh : HooksLegal h) (fuel) (w : World V X) (a gen tv) :
    Mono w (athrowStartArgs h fuel w a gen tv).1 := by
  simp only [athrowStartArgs]
  have m2 := genThrowF_legal hh fuel w gen false tv.1 tv.2.1 tv.2.2
  generalize genThrowF h fuel w gen false _ _ _ = t at m2
  obtain ⟨w2, res⟩ := t
  simp only at m2 ⊢
  have m3 := unwrap_legal w2 gen res
  generalize asyncGenUnwrapValue w2 gen res = u at m3
  obtain ⟨w3, r3⟩ := u
  simp only at m3 ⊢
  cases r3 with
  | ok v => exact m2.trans m3
  | err e => exact athrowCheckError_legal (m2.trans m3) a gen false e

theorem athrowIter_legal (hh : HooksLegal h) (w : World V X) (a gen args arg) :
    Mono w (athrowIter h w a gen args arg).1 := by
  simp only [athrowIter]
  have m2 := genSend_legal hh w gen (some arg)
  generalize genSend h w gen (some arg) = t at m2
  obtain ⟨w2, res⟩ := t
  simp only at m2 ⊢
  cases args with
  | some l => exact m2.trans (unwrap_legal w2 gen res)
  | none => exact acloseTail_legal m2 a gen res

theorem asyncGenAthrowSend_legal (hh : HooksLegal h) (fuel) (w : World V X) (a arg) :
    Mono w (asyncGenAthrowSend h fuel w a arg).1 := by
  simp only [asyncGenAthrowSend]
  split
  · exact Mono.refl w
  split
  · exact (Mono.refl w).setAthrowClosed a
  split
  · rename_i hs
    split
    · exact (Mono.refl w).setAthrowClosed a
    split
    · exact (Mono.refl w).setAthrowClosed a
    split
    · exact Mono.refl w
    have m1 := (Mono.setAthrowIter a hs).setRunning (w.athrows a).gen true
    split
    · exact m1.trans (athrowStartAclose_legal hh fuel _ a (w.athrows a).gen)
    · exact m1.trans (athrowStartArgs_legal hh fuel _ a (w.athrows a).gen _)
  · exact athrowIter_legal hh w a _ _ arg

theorem athrowThrowFinish_legal {w0 w : World V X} (m : Mono w0 w) (a gen args) (res : Ret V) :
    Mono w0 (athrowThrowFinish w a gen args res).1 := by
  cases args with
  | some l =>
    simp only [athrowThrowFinish]
    have m3 := unwrap_legal w gen res
    generalize asyncGenUnwrapValue w gen res = u at m3
    obtain ⟨w3, r3⟩ := u
    simp only at m3 ⊢
    cases r3 with
    | ok v => exact m.trans m3
    | err e => exact ((m.trans m3).setRunning gen false).setAthrowClosed a
  | none =>
    cases res with
    | err e =>
      simp only [athrowThrowFinish]
      split <;> exact (m.setRunning gen false).setAthrowClosed a
    | ok v =>
      cases v
      case wrapped o => exact (m.setRunning gen false).setAthrowClosed a
      all_goals exact m

theorem asyncGenAthrowThrow_legal (hh : HooksLegal h) (fuel) (w : World V X) (a args) :
    Mono w (asyncGenAthrowThrow h fuel w a args).1 := by
  simp only [asyncGenAthrowThrow]
  split
  · exact Mono.refl w
  split
  · exact (Mono.refl w).setAthrowClosed a
  have hw1 : Mono w (if (w.athrows a).state = .init then
        (w.setAthrowState a .iter).setRunning (w.athrows a).gen true else w) := by
    split
    · rename_i hs
      exact (Mono.setAthrowIter a hs).setRunning _ true
    · exact Mono.refl w
  generalize (if (w.athrows a).state = .init then
        (w.setAthrowState a .iter).setRunning (w.athrows a).gen true else w) = w1 at hw1 ⊢
  exact athrowThrowFinish_legal (hw1.trans (genThrow_legal hh fuel w1 (w.athrows a).gen args)) a _ _ _

end Async

/-- `gen_close` and `gen_throw` move every generator in the world only along legal
edges, write back the state they hold `FRAME_EXECUTING` over whenever the frame did not run,
and leave `ag_closed` and the awaitables monotone, for all arguments, all frame outcomes and
every reentrant use of the model from the hooks. Hypothesis: `HooksLegal`. -/
def GenOpsStateEdges : Prop :=
  ∀ (V X : Type) (h : Hooks V X), HooksLegal h →
  ∀ (fuel : Nat) (w : World V X) (r : Ref) (args : List (Obj V)),
    Mono w (genCloseF h fuel w r).1 ∧ Mono w (genThrow h fuel w r args).1

theorem genOpsStateEdges_proven : GenOpsStateEdges :=
  fun _ _ _ hh fuel w r args => ⟨genCloseF_legal hh fuel w r, genThrow_legal hh fuel w r args⟩

/-- The same for the awaitables' `send` and `throw`: `init -> iter -> closed` only,
frame states along legal edges, `ag_closed` only set. -/
def AsyncOpsStateEdges : Prop :=
  ∀ (V X : Type) (h : Hooks V X), HooksLegal h →
  ∀ (fuel : Nat) (w : World V X) (a : Ref) (arg : Option (Obj V)) (arg' : Obj V)
    (args : List (Obj V)),
    Mono w (asyncGenAsendSend h w a arg).1 ∧ Mono w (asyncGenAsendThrow h fuel w a args).1 ∧
    Mono w (asyncGenAthrowSend h fuel w a arg').1 ∧ Mono w (asyncGenAthrowThrow h fuel w a args).1

theorem asyncOpsStateEdges_proven : AsyncOpsStateEdges :=
  fun _ _ _ hh fuel w a arg arg' args =>
    ⟨asyncGenAsendSend_legal hh w a arg, asyncGenAsendThrow_legal hh fuel w a args,
     asyncGenAthrowSend_legal hh fuel w a arg', asyncGenAthrowThrow_legal hh fuel w a args⟩

end PyLean.Bytecode.GenObj
