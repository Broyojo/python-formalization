import PyLean.Bytecode.GenObj.AsyncGen

/-!
# Properties of the generator state machine

Everything here quantifies over the value type `V`, the extension type `X` and the
`Hooks`, so it holds for every frame evaluator. Hypotheses on the hooks are spelled
out in `HooksLegal` and are the only assumptions made about the interpreter.
-/

namespace PyLean.Bytecode.GenObj

section Basic
variable {V X : Type}

theorem finished_iff (s : FrameState) : s.finished = true ↔ s = .cleared := by
  cases s <;> decide

@[simp] theorem finished_cleared : FrameState.cleared.finished = true := by decide
@[simp] theorem finished_created : FrameState.created.finished = false := by decide
@[simp] theorem finished_suspended : FrameState.suspended.finished = false := by decide
@[simp] theorem finished_yf : FrameState.suspendedYieldFrom.finished = false := by decide
@[simp] theorem finished_executing : FrameState.executing.finished = false := by decide

@[simp] theorem state_setState (w : World V X) (r : Ref) (s : FrameState) :
    ((w.setState r s).get r).state = s := by simp [World.setState]

@[simp] theorem instr_setState (w : World V X) (r q : Ref) (s : FrameState) :
    ((w.setState r s).get q).instr = (w.get q).instr := by
  by_cases h : q = r
  · subst h; simp [World.setState]
  · simp [World.setState, h]

@[simp] theorem kind_setState (w : World V X) (r q : Ref) (s : FrameState) :
    ((w.setState r s).get q).kind = (w.get q).kind := by
  by_cases h : q = r
  · subst h; simp [World.setState]
  · simp [World.setState, h]

theorem get_setState_ne (w : World V X) {r q : Ref} (s : FrameState) (h : q ≠ r) :
    (w.setState r s).get q = w.get q := by
  simp [World.setState, h]

/-- Writing back the state a generator already has changes nothing. -/
theorem setState_self (w : World V X) (r : Ref) : w.setState r (w.get r).state = w := by
  cases w with
  | mk gens asends athrows nu od cs fi fh ext =>
    simp only [World.setState, World.set, World.get, World.mk.injEq, true_and, and_true]
    funext q
    by_cases h : q = r
    · subst h; simp
    · simp [h]

/-- The second of two writes of a state wins. -/
theorem setState_setState (w : World V X) (r : Ref) (s t : FrameState) :
    (w.setState r s).setState r t = w.setState r t := by
  simp only [World.setState, World.set, World.get]
  congr 1
  funext q
  by_cases h : q = r
  · subst h; simp
  · simp [h]

@[simp] theorem noUnwind_setState (w : World V X) (r : Ref) (s : FrameState) :
    (w.setState r s).noUnwindTools = w.noUnwindTools := rfl

theorem state_setState_any (w : World V X) (r q : Ref) (s : FrameState) :
    ((w.setState r s).get q).state = if q = r then s else (w.get q).state := by
  by_cases h : q = r
  · subst h; simp
  · simp [get_setState_ne, h]

@[simp] theorem state_setRunning (w : World V X) (r q : Ref) (b : Bool) :
    ((w.setRunning r b).get q).state = (w.get q).state := by
  by_cases h : q = r
  · subst h; simp [World.setRunning]
  · simp [World.setRunning, h]

@[simp] theorem state_setClosed (w : World V X) (r q : Ref) :
    ((w.setClosed r).get q).state = (w.get q).state := by
  by_cases h : q = r
  · subst h; simp [World.setClosed]
  · simp [World.setClosed, h]

@[simp] theorem running_setRunning (w : World V X) (r : Ref) (b : Bool) :
    ((w.setRunning r b).get r).agRunningAsync = b := by
  simp [World.setRunning]

@[simp] theorem running_setState (w : World V X) (r q : Ref) (s : FrameState) :
    ((w.setState r s).get q).agRunningAsync = (w.get q).agRunningAsync := by
  by_cases h : q = r
  · subst h; simp [World.setState]
  · simp [World.setState, h]

@[simp] theorem asends_setRunning (w : World V X) (r : Ref) (b : Bool) :
    (w.setRunning r b).asends = w.asends := rfl
@[simp] theorem athrows_setRunning (w : World V X) (r : Ref) (b : Bool) :
    (w.setRunning r b).athrows = w.athrows := rfl
@[simp] theorem asends_setClosed (w : World V X) (r : Ref) :
    (w.setClosed r).asends = w.asends := rfl
@[simp] theorem athrows_setClosed (w : World V X) (r : Ref) :
    (w.setClosed r).athrows = w.athrows := rfl
@[simp] theorem asends_setAthrow (w : World V X) (a : Ref) (s : AwaitableState) :
    (w.setAthrowState a s).asends = w.asends := rfl
@[simp] theorem athrows_setAsend (w : World V X) (a : Ref) (s : AwaitableState) :
    (w.setAsendState a s).athrows = w.athrows := rfl

@[simp] theorem asendState_set (w : World V X) (a : Ref) (s : AwaitableState) :
    ((w.setAsendState a s).asends a).state = s := by
  simp [World.setAsendState]

@[simp] theorem athrowState_set (w : World V X) (a : Ref) (s : AwaitableState) :
    ((w.setAthrowState a s).athrows a).state = s := by
  simp [World.setAthrowState]

@[simp] theorem setRunning_setAthrow_get (w : World V X) (a r q : Ref) (s : AwaitableState) (b : Bool) :
    (((w.setRunning r b).setAthrowState a s).get q) = (w.setRunning r b).get q := rfl

/-- `gen_send_ex` rejects the call before touching the frame: :335, :349, :353. -/
def SendRejected (g : GenObj V) (arg : Option (Obj V)) : Prop :=
  (g.state = .created ∧ isNonNull arg = true) ∨ g.state = .executing ∨ g.state.finished = true

theorem genSendEx_executing (h : Hooks V X) (w : World V X) (r : Ref) (arg)
    (hs : (w.get r).state = .executing) :
    genSendEx h w r arg =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind)))) := by
  simp [genSendEx, hs]

theorem genSendEx_finished (h : Hooks V X) (w : World V X) (r : Ref) (arg)
    (hs : (w.get r).state.finished = true) (hnc : ¬ ((w.get r).state = .created ∧ isNonNull arg = true)) :
    genSendEx h w r arg =
      if (w.get r).kind = .coro then
        (w, .err (some (Exc.runtimeError "cannot reuse already awaited coroutine")))
      else if arg.isSome = true then (w, .ret .none)
      else (w, .err none) := by
  have h2 : (w.get r).state ≠ .executing := by
    intro e; rw [e] at hs; simp at hs
  simp only [genSendEx]
  rw [if_neg hnc, if_neg h2, if_pos hs]

/-- Reaching the frame. -/
theorem genSendEx_live (h : Hooks V X) (w : World V X) (r : Ref) (arg)
    (h1 : ¬ ((w.get r).state = .created ∧ isNonNull arg = true))
    (h2 : (w.get r).state ≠ .executing) (h3 : (w.get r).state.finished = false) :
    genSendEx h w r arg = genSendEx2 h (w.setState r .executing) r arg none := by
  simp only [genSendEx]
  rw [if_neg h1, if_neg h2, if_neg (by simp [h3])]

theorem finishResume_state (w : World V X) (r : Ref) (k : GenKind) (arg : Option (Obj V))
    (o : ResumeOutcome V) :
    ((finishResume w r k arg o).1.get r).state = .cleared ∨
      ((finishResume w r k arg o).1.get r).state.isSuspended = true := by
  cases o with
  | yielded oparg v d top =>
    right; cases oparg <;> simp [finishResume, suspendFrame, FrameState.ofOparg, FrameState.isSuspended]
  | returned v =>
    left; simp only [finishResume]; split <;> simp [clearGenFrame]
  | raised e => left; simp [finishResume, clearGenFrame]

end Basic

/-! ## `gen_send_ex` -/

/-- A call `gen_send_ex` rejects (non-None to a just-started generator, already
executing, finished) changes nothing and does not depend on the frame evaluator at
all, so a finished or running frame is never resumed and every state check comes
before any effect. -/
def GenSendRejectedNoEffect : Prop :=
  ∀ (V X : Type) (h h' : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)),
    SendRejected (w.get r) arg →
    (genSendEx h w r arg).1 = w ∧ genSendEx h' w r arg = genSendEx h w r arg

theorem genSendRejectedNoEffect_proven : GenSendRejectedNoEffect := by
  intro V X h h' w r arg hr
  rcases hr with ⟨h1, h2⟩ | h1 | h1
  · simp [genSendEx, h1, h2]
  · simp [genSendEx, h1]
  · have hnc : ¬ ((w.get r).state = .created ∧ isNonNull arg = true) := by
      rintro ⟨c, -⟩; rw [c] at h1; simp at h1
    rw [genSendEx_finished h w r arg h1 hnc, genSendEx_finished h' w r arg h1 hnc]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- `gen_send_ex` raises `ValueError` with the type's "already executing" message
whenever `gi_frame_state == FRAME_EXECUTING`, for all arguments. -/
def GenAlreadyExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)),
    (w.get r).state = .executing →
    genSendEx h w r arg =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))

theorem genAlreadyExecuting_proven : GenAlreadyExecuting :=
  fun _ _ h w r arg hs => genSendEx_executing h w r arg hs

/-- A resume that returns `bad` unless the frame is `FRAME_EXECUTING`. -/
def guardResume {V X : Type} (h : Hooks V X) (bad : World V X × ResumeOutcome V) : Hooks V X :=
  { h with resume := fun w q a e => if (w.get q).state = .executing then h.resume w q a e else bad }

section Guard
variable {V X : Type}

theorem genSendEx_guard (h : Hooks V X) (bad) (w : World V X) (r arg) :
    genSendEx (guardResume h bad) w r arg = genSendEx h w r arg := by
  simp [genSendEx, genSendEx2, guardResume]

theorem genSendEx2_guard (h : Hooks V X) (bad) (w : World V X) (r arg e)
    (hs : (w.get r).state = .executing) :
    genSendEx2 (guardResume h bad) w r arg e = genSendEx2 h w r arg e := by
  simp [genSendEx2, guardResume, hs]

end Guard

/-- The legal `gi_frame_state` edges as seen between two model calls. A generator that
is really executing stays so through nested calls. -/
def legalEdge : FrameState → FrameState → Bool
  | .created, .created | .created, .suspended | .created, .suspendedYieldFrom
  | .created, .cleared => true
  | .suspended, .suspended | .suspended, .suspendedYieldFrom | .suspended, .cleared => true
  | .suspendedYieldFrom, .suspended | .suspendedYieldFrom, .suspendedYieldFrom
  | .suspendedYieldFrom, .cleared => true
  | .executing, .executing => true
  | .cleared, .cleared => true
  | _, _ => false

theorem legalEdge_refl (s : FrameState) : legalEdge s s = true := by cases s <;> rfl

theorem legalEdge_trans {a b c : FrameState} (h1 : legalEdge a b = true)
    (h2 : legalEdge b c = true) : legalEdge a c = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | (exact absurd h1 (by decide)) | (exact absurd h2 (by decide))

/-- For every generator, argument, and every outcome of the frame, `gen_send_ex`
moves `gi_frame_state` along a legal edge. -/
def GenSendStateEdges : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)),
    legalEdge (w.get r).state ((genSendEx h w r arg).1.get r).state = true

theorem genSendStateEdges_proven : GenSendStateEdges := by
  intro V X h w r arg
  by_cases h1 : (w.get r).state = .created ∧ isNonNull arg = true
  · have : SendRejected (w.get r) arg := Or.inl h1
    rw [(genSendRejectedNoEffect_proven V X h h w r arg this).1]
    exact legalEdge_refl _
  by_cases h2 : (w.get r).state = .executing
  · have : SendRejected (w.get r) arg := Or.inr (Or.inl h2)
    rw [(genSendRejectedNoEffect_proven V X h h w r arg this).1]
    exact legalEdge_refl _
  cases h3 : (w.get r).state.finished with
  | true =>
    have : SendRejected (w.get r) arg := Or.inr (Or.inr h3)
    rw [(genSendRejectedNoEffect_proven V X h h w r arg this).1]
    exact legalEdge_refl _
  | false =>
    rw [genSendEx_live h w r arg h1 h2 h3]
    simp only [genSendEx2]
    have hst := finishResume_state
      (h.resume (w.setState r .executing) r (arg.getD .none) none).1 r
      ((w.setState r .executing).get r).kind arg
      (h.resume (w.setState r .executing) r (arg.getD .none) none).2
    generalize hs : (w.get r).state = s at *
    generalize ((finishResume _ r _ arg _).1.get r).state = s' at hst ⊢
    cases s <;> simp_all <;> cases s' <;> simp_all [legalEdge, FrameState.isSuspended]

/-- `next(gen)` and `gen.send(None)` are the same operation: same result, same
world, for every state and frame outcome, on the two types with `tp_iternext`
(`gen_iternext` asserts this type at :632). -/
def GenIternextVsSendNone : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref),
    (w.get r).kind ≠ .asyncGen →
    nextCall h w r = genSend h w r (some .none)

theorem genIternextVsSendNone_proven : GenIternextVsSendNone := by
  intro V X h w r hk
  simp only [nextCall, genIternext, genSend]
  by_cases h2 : (w.get r).state = .executing
  · simp [genSendEx_executing, h2, iterResultToRet, sendResultToRet, nullToStop]
  have hnc1 : ¬ ((w.get r).state = .created ∧ isNonNull (none : Option (Obj V)) = true) := by
    simp [isNonNull]
  have hnc2 : ¬ ((w.get r).state = .created ∧ isNonNull (some Obj.none : Option (Obj V)) = true) := by
    simp [isNonNull]
  cases h3 : (w.get r).state.finished with
  | true =>
    rw [genSendEx_finished h w r none h3 hnc1, genSendEx_finished h w r (some .none) h3 hnc2]
    by_cases hc : (w.get r).kind = .coro
    · simp [hc, iterResultToRet, sendResultToRet, nullToStop]
    · simp [hc, iterResultToRet, sendResultToRet, nullToStop, Obj.isNone, hk]
  | false =>
    rw [genSendEx_live h w r none hnc1 h2 h3, genSendEx_live h w r (some .none) hnc2 h2 h3]
    simp only [genSendEx2, Option.getD]
    generalize h.resume (w.setState r .executing) r Obj.none none = res
    obtain ⟨w', o⟩ := res
    cases o with
    | yielded oparg v d top => simp [finishResume, iterResultToRet, sendResultToRet, nullToStop]
    | raised e => simp [finishResume, iterResultToRet, sendResultToRet, nullToStop]
    | returned v =>
      cases v <;> simp [finishResume, iterResultToRet, sendResultToRet, nullToStop, Obj.isNone, hk]

/-- `gen.send(arg)` is `PyGen_am_send` plus `gen_set_stop_iteration`, :384-399: a returned
value `v` becomes `StopIteration` carrying exactly `v`, on generators and coroutines. -/
def GenSendVsAmSend : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Obj V),
    (w.get r).kind ≠ .asyncGen →
    (genSend h w r (some arg)).1 = (pyGenAmSend h w r arg).1 ∧
    (match (pyGenAmSend h w r arg).2 with
     | .next v => (genSend h w r (some arg)).2 = .ok v
     | .ret v => fetchStopIterationValue
        (match (genSend h w r (some arg)).2 with
         | .err e => e
         | .ok _ => none) = .ok v
     | .err e => (genSend h w r (some arg)).2 = .err e)

theorem genSendVsAmSend_proven : GenSendVsAmSend := by
  intro V X h w r arg hk
  simp only [genSend, pyGenAmSend, true_and]
  generalize (genSendEx h w r (some arg)).2 = s
  cases s with
  | next v => rfl
  | err e => rfl
  | ret v =>
    cases v <;> simp [sendResultToRet, hk, Obj.isNone, fetchStopIterationValue,
      Exc.stopIterationNone, Exc.isStopIteration, setStopIterationValue]

/-- `_PyGen_SetStopIterationValue` and `_PyGen_FetchStopIterationValue` round-trip
every value, tuples included (the comment at :655-659), and the fetch leaves any
other exception pending. -/
def StopIterationValueRoundTrip : Prop :=
  ∀ (V : Type) (v : Obj V) (e : Exc V),
    fetchStopIterationValue (some (setStopIterationValue v)) = .ok v ∧
    (e.isStopIteration = false → fetchStopIterationValue (some e) = .err (some e))

theorem stopIterationValueRoundTrip_proven : StopIterationValueRoundTrip := by
  intro V v e
  constructor
  · simp [fetchStopIterationValue, setStopIterationValue, Exc.isStopIteration]
  · intro h; simp [fetchStopIterationValue, h]

/-! ## `gen_close` -/

section Close
variable {V X : Type}

/-- What the throw at :518 leaves: a yield is not `.ok`, and everything else cleared the
frame. -/
theorem genCloseFinish_ok (h : Hooks V X) (w : World V X) (r : Ref) (p : Option (Exc V)) (v : Obj V)
    (hok : (genCloseFinish h w r p).2 = .ok v) :
    ((genCloseFinish h w r p).1.get r).state.finished = true := by
  revert hok
  simp only [genCloseFinish, genSendEx2]
  generalize h.resume w r _ p = res
  obtain ⟨w', o⟩ := res
  cases o with
  | yielded oparg x d top => simp [finishResume]
  | returned x => simp [finishResume, clearGenFrame, Option.isNone]
  | raised e =>
    simp only [finishResume]
    split <;> simp [clearGenFrame]

theorem genClearFrame_state (w : World V X) (r : Ref) :
    ((genClearFrame w r).get r).state = (w.get r).state := by
  simp [genClearFrame]

end Close

/-- `close()` is idempotent: if it returns normally the generator is finished, and
closing again returns `None` without changing anything. This holds for every
frame outcome (a body that ignores `GeneratorExit` makes the first close raise). -/
def GenCloseIdempotent : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n m : Nat) (w w' : World V X) (r : Ref) (v : Obj V),
    genCloseF h (n + 1) w r = (w', .ok v) →
    (w'.get r).state.finished = true ∧ genCloseF h (m + 1) w' r = (w', .ok .none)

theorem genCloseIdempotent_proven : GenCloseIdempotent := by
  intro V X h n m w w' r v hc
  have hf : (w'.get r).state.finished = true := by
    simp only [genCloseF] at hc
    split at hc
    · have := congrArg Prod.fst hc
      simp only at this
      rw [← this, genClearFrame_state]; simp
    · split at hc
      · have := congrArg Prod.fst hc
        simp only at this
        rw [← this]; assumption
      · split at hc
        · simp at hc
        · simp only [genCloseBody] at hc
          split at hc
          · have := congrArg Prod.fst hc
            simp only at this
            rw [← this, genClearFrame_state]; simp
          · have h1 := congrArg Prod.fst hc
            have h2 := congrArg Prod.snd hc
            simp only at h1 h2
            rw [← h1]
            exact genCloseFinish_ok h _ r _ v h2
  refine ⟨hf, ?_⟩
  have hnc : (w'.get r).state ≠ .created := by
    intro e; rw [e] at hf; simp at hf
  simp [genCloseF, hnc, hf]

/-- `gen_close` on a generator that is running raises the "already executing"
`ValueError` and changes nothing. This was false on 3.14.7, where the check sat in
`gen_send_ex2`, behind the fast path that cleared the frame: `bytecode-gen-close-clears-running-frame`.
3.15 moved it to the top of `gen_close`, :483-486. -/
def GenCloseRejectsExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    (w.get r).state = .executing →
    genCloseF h (n + 1) w r =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))

theorem genCloseRejectsExecuting_proven : GenCloseRejectsExecuting := by
  intro V X h n w r hs
  simp [genCloseF, hs]

/-- The same with the instruction pointer anywhere but at a depth-1 `RESUME`, the case
that was all there was on 3.14.7. On 3.15 it follows from the unconditional statement. -/
def GenCloseRejectsExecutingPastResume : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    (w.get r).state = .executing →
    ¬ ((w.get r).instr.isResumeDepth1 = true ∧ w.noUnwindTools = true) →
    genCloseF h (n + 1) w r =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))

theorem genCloseRejectsExecutingPastResume_proven : GenCloseRejectsExecutingPastResume :=
  fun V X h n w r hs _ => genCloseRejectsExecuting_proven V X h n w r hs

def noopHooks : Hooks Unit Unit where
  resume w _ _ e := (w, .raised (e.getD Exc.fuel))
  getClose w _ := (w, .ok none)
  getThrow w _ := (w, .ok none)
  callNoArgs w _ := (w, .ok .none)
  callOneArg w _ _ := (w, .ok .none)
  callThrow w _ _ _ _ := (w, .ok .none)
  unraisable w _ _ := w
  warn w _ := (w, none)
  warnUnawaitedCoro w _ := w
  warnUnawaitedAgen w _ _ := w
  normalize _ _ := Exc.generatorExit
  typeName _ := "x"
  audit _ _ := none
  frameObject _ _ := .none
  isIter _ := false
  amAwait _ _ := none

/-- `gen_close`'s fast path (:499-512) agrees with the slow path on a frame the slow
path would simply unwind: if throwing `GeneratorExit` at the suspended depth-1
`RESUME` makes the frame raise it unchanged, then the world with unwinding tools
(`_PyEval_NoToolsForUnwind` false) takes the slow path to the same result and final
state as the fast path, and the fast path drops the frame's stack (`gen_clear_frame`).
The hypothesis is what a depth-1 frame does: no handler but the outermost, whose
`stopiteration_error` passes `GeneratorExit` through. -/
def GenCloseFastSlowAgree : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    (w.get r).state = .suspended → (w.get r).instr = .resume true → w.noUnwindTools = false →
    (∀ a, (h.resume (w.setState r .executing) r a (some Exc.generatorExit)).2 =
      .raised Exc.generatorExit) →
    let fast := genCloseF h (n + 1) { w with noUnwindTools := true } r
    let slow := genCloseF h (n + 1) w r
    fast.2 = .ok .none ∧ slow.2 = .ok .none ∧
      (fast.1.get r).state = .cleared ∧ (slow.1.get r).state = .cleared ∧
      (fast.1.get r).stackTop = .none

theorem genCloseFastSlowAgree_proven : GenCloseFastSlowAgree := by
  intro V X h n w r hs hi hu hr
  have g1 : ({ w with noUnwindTools := true } : World V X).get r = w.get r := rfl
  have hfast : genCloseF h (n + 1) { w with noUnwindTools := true } r =
      (genClearFrame ((({ w with noUnwindTools := true } : World V X).setState r .executing).setState r .cleared) r,
       .ok .none) := by
    simp [genCloseF, g1, hs, genCloseBody, closeDelegate, hi, InstrPtr.isResumeDepth1]
  have hsl : genCloseF h (n + 1) w r =
      genCloseFinish h (w.setState r .executing) r (some Exc.generatorExit) := by
    simp [genCloseF, hs, genCloseBody, closeDelegate, hi, hu, closePending]
  have hslow : genSendEx2 h (w.setState r .executing) r (some .none) (some Exc.generatorExit) =
      (clearGenFrame (h.resume (w.setState r .executing) r .none (some Exc.generatorExit)).1 r,
       .err (some Exc.generatorExit)) := by
    show finishResume _ r _ _ (h.resume (w.setState r .executing) r .none (some Exc.generatorExit)).2 = _
    rw [hr .none]
    rfl
  dsimp only
  rw [hfast, hsl]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp only [genCloseFinish, hslow]
    simp [Exc.generatorExit, Exc.isGeneratorExit]
  · simp [genClearFrame_state]
  · simp only [genCloseFinish, hslow]
    simp [clearGenFrame, Exc.generatorExit, Exc.isGeneratorExit]
  · simp [genClearFrame]

end PyLean.Bytecode.GenObj
