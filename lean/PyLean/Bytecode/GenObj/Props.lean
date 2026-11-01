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

theorem finished_iff (s : FrameState) : s.finished = true ↔ s = .completed ∨ s = .cleared := by
  cases s <;> decide

@[simp] theorem finished_cleared : FrameState.cleared.finished = true := by decide
@[simp] theorem finished_completed : FrameState.completed.finished = true := by decide
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

/-- `gen_send_ex2` rejects the call before touching the frame: :199, :212, :223. -/
def SendRejected (g : GenObj V) (arg : Option (Obj V)) : Prop :=
  (g.state = .created ∧ isNonNull arg = true) ∨ g.state = .executing ∨ g.state.finished = true

theorem genSendEx2_executing (h : Hooks V X) (w : World V X) (r : Ref) (arg exc err closing)
    (hs : (w.get r).state = .executing) :
    genSendEx2 h w r arg exc err closing =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind)))) := by
  simp [genSendEx2, hs]

theorem genSendEx2_finished (h : Hooks V X) (w : World V X) (r : Ref) (arg exc err closing)
    (hs : (w.get r).state.finished = true) (hnc : ¬ ((w.get r).state = .created ∧ isNonNull arg = true)) :
    genSendEx2 h w r arg exc err closing =
      if (w.get r).kind = .coro ∧ closing = false then
        (w, .err (some (Exc.runtimeError "cannot reuse already awaited coroutine")))
      else if arg.isSome = true ∧ exc = false then (w, .ret .none)
      else (w, .err err) := by
  have h2 : (w.get r).state ≠ .executing := by
    intro e; rw [e] at hs; simp at hs
  simp only [genSendEx2]
  rw [if_neg hnc, if_neg h2, if_pos hs]

/-- Reaching the frame. -/
theorem genSendEx2_live (h : Hooks V X) (w : World V X) (r : Ref) (arg exc err closing)
    (h1 : ¬ ((w.get r).state = .created ∧ isNonNull arg = true))
    (h2 : (w.get r).state ≠ .executing) (h3 : (w.get r).state.finished = false) :
    genSendEx2 h w r arg exc err closing =
      let res := h.resume (w.setState r .executing) r (arg.getD .none) (if exc then err else none)
      finishResume res.1 r (w.get r).kind arg res.2 := by
  simp only [genSendEx2]
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

/-! ## `gen_send_ex2` -/

/-- A call `gen_send_ex2` rejects (non-None to a just-started generator, already
executing, finished) changes nothing and does not depend on the frame evaluator at
all, so a finished or running frame is never resumed and every state check comes
before any effect. -/
def GenSendRejectedNoEffect : Prop :=
  ∀ (V X : Type) (h h' : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (exc : Bool) (err : Option (Exc V)) (closing : Bool),
    SendRejected (w.get r) arg →
    (genSendEx2 h w r arg exc err closing).1 = w ∧
      genSendEx2 h' w r arg exc err closing = genSendEx2 h w r arg exc err closing

theorem genSendRejectedNoEffect_proven : GenSendRejectedNoEffect := by
  intro V X h h' w r arg exc err closing hr
  rcases hr with ⟨h1, h2⟩ | h1 | h1
  · simp [genSendEx2, h1, h2]
  · simp [genSendEx2, h1]
  · have hnc : ¬ ((w.get r).state = .created ∧ isNonNull arg = true) := by
      rintro ⟨c, -⟩; rw [c] at h1; simp at h1
    rw [genSendEx2_finished h w r arg exc err closing h1 hnc,
      genSendEx2_finished h' w r arg exc err closing h1 hnc]
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩

/-- `gen_send_ex2` raises `ValueError` with the type's "already executing" message
whenever `gi_frame_state == FRAME_EXECUTING`, for all arguments. -/
def GenAlreadyExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (exc : Bool) (err : Option (Exc V)) (closing : Bool),
    (w.get r).state = .executing →
    genSendEx2 h w r arg exc err closing =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))

theorem genAlreadyExecuting_proven : GenAlreadyExecuting :=
  fun _ _ h w r arg exc err closing hs => genSendEx2_executing h w r arg exc err closing hs

/-- A resume that returns `bad` unless the frame is `FRAME_EXECUTING`. -/
def guardResume {V X : Type} (h : Hooks V X) (bad : World V X × ResumeOutcome V) : Hooks V X :=
  { h with resume := fun w q a e => if (w.get q).state = .executing then h.resume w q a e else bad }

section Guard
variable {V X : Type}

theorem genSendEx2_guard (h : Hooks V X) (bad) (w : World V X) (r arg exc err closing) :
    genSendEx2 (guardResume h bad) w r arg exc err closing = genSendEx2 h w r arg exc err closing := by
  simp [genSendEx2, guardResume]

theorem genSendEx_guard (h : Hooks V X) (bad) (w : World V X) (r arg exc err closing) :
    genSendEx (guardResume h bad) w r arg exc err closing = genSendEx h w r arg exc err closing := by
  simp [genSendEx, genSendEx2_guard]

theorem genCloseFinish_guard (h : Hooks V X) (bad) (w : World V X) (r p) :
    genCloseFinish (guardResume h bad) w r p = genCloseFinish h w r p := by
  simp [genCloseFinish, genSendEx_guard]

theorem genCloseIter_guard (h : Hooks V X) (bad) (c) (w : World V X) (yf) :
    genCloseIter (guardResume h bad) c w yf = genCloseIter h c w yf := rfl

theorem genCloseBody_guard (h : Hooks V X) (bad) (c) (w : World V X) (r) :
    genCloseBody (guardResume h bad) c w r = genCloseBody h c w r := by
  have hd : closeDelegate (guardResume h bad) c w r = closeDelegate h c w r := rfl
  simp only [genCloseBody, hd, genCloseFinish_guard]

theorem genCloseF_guard (h : Hooks V X) (bad) (n : Nat) :
    ∀ (w : World V X) (r), genCloseF (guardResume h bad) n w r = genCloseF h n w r := by
  induction n with
  | zero => intro w r; rfl
  | succ n ih =>
    intro w r
    have hc : genCloseF (guardResume h bad) n = genCloseF h n := by
      funext w r; exact ih w r
    simp only [genCloseF, hc, genCloseBody_guard]

theorem throwHere_guard (h : Hooks V X) (bad) (w : World V X) (r typ val tb) :
    throwHere (guardResume h bad) w r typ val tb = throwHere h w r typ val tb := by
  unfold throwHere
  simp only [genSendEx_guard]
  rfl

theorem afterDelegate_guard (h : Hooks V X) (bad) (w : World V X) (r) (x : Ret V) :
    afterDelegate (guardResume h bad) w r x = afterDelegate h w r x := by
  cases x <;> simp [afterDelegate, genSendEx_guard]

theorem genThrowF_guard (h : Hooks V X) (bad) (n : Nat) :
    ∀ (w : World V X) (r c typ val tb),
      genThrowF (guardResume h bad) n w r c typ val tb = genThrowF h n w r c typ val tb := by
  induction n with
  | zero => intro w r c typ val tb; rfl
  | succ n ih =>
    intro w r c typ val tb
    have hc : genCloseF (guardResume h bad) n = genCloseF h n := by
      funext w r; exact genCloseF_guard h bad n w r
    have ht : ∀ sub, (fun w' => genThrowF (guardResume h bad) n w' sub c typ val tb)
        = (fun w' => genThrowF h n w' sub c typ val tb) := by
      intro sub; funext w'; exact ih w' sub c typ val tb
    simp only [genThrowF, throwHere_guard, afterDelegate_guard, genSendEx_guard, hc, ht,
      genCloseIter_guard]
    rfl

end Guard

/-- Every resume, through `gen_send_ex2`, `gen_close` or `_gen_throw` at any
delegation depth, sees the frame marked `FRAME_EXECUTING`: replacing `resume` by
anything at all on other states changes nothing, so a `CLEARED` frame is never
resumed. -/
def GenResumeSeesExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (bad : World V X × ResumeOutcome V) (n : Nat) (w : World V X)
    (r : Ref) (arg : Option (Obj V)) (exc : Bool) (err : Option (Exc V)) (closing : Bool)
    (c : Bool) (typ : Obj V) (val tb : Option (Obj V)),
    genSendEx2 (guardResume h bad) w r arg exc err closing = genSendEx2 h w r arg exc err closing ∧
    genCloseF (guardResume h bad) n w r = genCloseF h n w r ∧
    genThrowF (guardResume h bad) n w r c typ val tb = genThrowF h n w r c typ val tb

theorem genResumeSeesExecuting_proven : GenResumeSeesExecuting :=
  fun _ _ h bad n w r arg exc err closing c typ val tb =>
    ⟨genSendEx2_guard h bad w r arg exc err closing, genCloseF_guard h bad n w r,
     genThrowF_guard h bad n w r c typ val tb⟩

/-- The legal `gi_frame_state` edges as seen between two model calls. `completed`
is transient: `gen_close` sets it and `gen_clear_frame` replaces it at once. A
generator that is really executing stays so through nested calls. -/
def legalEdge : FrameState → FrameState → Bool
  | .created, .created | .created, .suspended | .created, .suspendedYieldFrom
  | .created, .cleared => true
  | .suspended, .suspended | .suspended, .suspendedYieldFrom | .suspended, .cleared => true
  | .suspendedYieldFrom, .suspended | .suspendedYieldFrom, .suspendedYieldFrom
  | .suspendedYieldFrom, .cleared => true
  | .executing, .executing => true
  | .completed, .completed | .completed, .cleared => true
  | .cleared, .cleared => true
  | _, _ => false

theorem legalEdge_refl (s : FrameState) : legalEdge s s = true := by cases s <;> rfl

theorem legalEdge_trans {a b c : FrameState} (h1 : legalEdge a b = true)
    (h2 : legalEdge b c = true) : legalEdge a c = true := by
  cases a <;> cases b <;> cases c <;> first | rfl | (exact absurd h1 (by decide)) | (exact absurd h2 (by decide))

/-- For every generator, argument, and every outcome of the frame, `gen_send_ex2`
moves `gi_frame_state` along a legal edge. -/
def GenSendStateEdges : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V))
    (exc : Bool) (err : Option (Exc V)) (closing : Bool),
    legalEdge (w.get r).state ((genSendEx2 h w r arg exc err closing).1.get r).state = true

theorem genSendStateEdges_proven : GenSendStateEdges := by
  intro V X h w r arg exc err closing
  by_cases h1 : (w.get r).state = .created ∧ isNonNull arg = true
  · have : SendRejected (w.get r) arg := Or.inl h1
    rw [(genSendRejectedNoEffect_proven V X h h w r arg exc err closing this).1]
    exact legalEdge_refl _
  by_cases h2 : (w.get r).state = .executing
  · have : SendRejected (w.get r) arg := Or.inr (Or.inl h2)
    rw [(genSendRejectedNoEffect_proven V X h h w r arg exc err closing this).1]
    exact legalEdge_refl _
  cases h3 : (w.get r).state.finished with
  | true =>
    have : SendRejected (w.get r) arg := Or.inr (Or.inr h3)
    rw [(genSendRejectedNoEffect_proven V X h h w r arg exc err closing this).1]
    exact legalEdge_refl _
  | false =>
    rw [genSendEx2_live h w r arg exc err closing h1 h2 h3]
    have hst := finishResume_state
      (h.resume (w.setState r .executing) r (arg.getD .none) (if exc then err else none)).1 r
      (w.get r).kind arg
      (h.resume (w.setState r .executing) r (arg.getD .none) (if exc then err else none)).2
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
  simp only [nextCall, genIternext, genSend, genSendEx]
  by_cases h2 : (w.get r).state = .executing
  · simp [genSendEx2_executing, h2, iterResultToRet, sendResultToRet, nullToStop]
  cases h3 : (w.get r).state.finished with
  | true =>
    have hnc1 : ¬ ((w.get r).state = .created ∧ isNonNull (none : Option (Obj V)) = true) := by simp [isNonNull]
    have hnc2 : ¬ ((w.get r).state = .created ∧ isNonNull (some Obj.none : Option (Obj V)) = true) := by simp [isNonNull]
    rw [genSendEx2_finished h w r none false none false h3 hnc1,
        genSendEx2_finished h w r (some .none) false none false h3 hnc2]
    by_cases hc : (w.get r).kind = .coro
    · simp [hc, iterResultToRet, sendResultToRet, nullToStop]
    · simp [hc, iterResultToRet, sendResultToRet, nullToStop, Obj.isNone, hk]
  | false =>
    have hnc1 : ¬ ((w.get r).state = .created ∧ isNonNull (none : Option (Obj V)) = true) := by simp [isNonNull]
    have hnc2 : ¬ ((w.get r).state = .created ∧ isNonNull (some Obj.none : Option (Obj V)) = true) := by simp [isNonNull]
    rw [genSendEx2_live h w r none false none false hnc1 h2 h3,
        genSendEx2_live h w r (some .none) false none false hnc2 h2 h3]
    simp only [Option.getD, Bool.false_eq_true, if_false]
    generalize h.resume (w.setState r .executing) r Obj.none none = res
    obtain ⟨w', o⟩ := res
    cases o with
    | yielded oparg v d top => simp [finishResume, iterResultToRet, sendResultToRet, nullToStop]
    | raised e => simp [finishResume, iterResultToRet, sendResultToRet, nullToStop]
    | returned v =>
      cases v <;> simp [finishResume, iterResultToRet, sendResultToRet, nullToStop, Obj.isNone, hk]

/-- `gen.send(arg)` is `PyGen_am_send` plus the conversion at :301-313: a returned
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
  simp only [genSend, genSendEx, pyGenAmSend, true_and]
  generalize (genSendEx2 h w r (some arg) false none false).2 = s
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

/-- What the throw at :428 can do: yield, finish the generator, or fail on a running
frame with a plain `ValueError`. -/
theorem genSendEx_close_cases (h : Hooks V X) (w : World V X) (r : Ref) (p : Option (Exc V)) :
    let s := genSendEx h w r (some .none) true p true
    (∃ v, s.2 = .ok v) ∨ (s.1.get r).state.finished = true ∨
      s.2 = .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))) := by
  intro s
  by_cases h2 : (w.get r).state = .executing
  · right; right
    simp [s, genSendEx, genSendEx2_executing, h2, sendResultToRet]
  have hnc : ¬ ((w.get r).state = .created ∧ isNonNull (some Obj.none : Option (Obj V)) = true) := by
    simp [isNonNull]
  cases h3 : (w.get r).state.finished with
  | true =>
    right; left
    simp only [s, genSendEx]
    rw [genSendEx2_finished h w r (some .none) true p true h3 hnc]
    simp [h3]
  | false =>
    simp only [s, genSendEx]
    rw [genSendEx2_live h w r (some .none) true p true hnc h2 h3]
    simp only
    generalize h.resume (w.setState r .executing) r _ _ = res
    obtain ⟨w', o⟩ := res
    cases o with
    | yielded oparg v d top =>
      left; exact ⟨v, by simp [finishResume, sendResultToRet]⟩
    | raised e => right; left; simp [finishResume, clearGenFrame]
    | returned v =>
      right; left
      simp [finishResume, clearGenFrame, Option.isNone]

theorem genCloseFinish_ok (h : Hooks V X) (w : World V X) (r : Ref) (p : Option (Exc V)) (v : Obj V)
    (hok : (genCloseFinish h w r p).2 = .ok v) :
    ((genCloseFinish h w r p).1.get r).state.finished = true := by
  have hc := genSendEx_close_cases h w r p
  simp only at hc
  revert hok
  simp only [genCloseFinish]
  generalize hs : genSendEx h w r (some .none) true p true = s at hc
  obtain ⟨w', res⟩ := s
  rcases hc with ⟨x, hx⟩ | hf | he
  · simp at hx; subst hx; simp
  · simp at hf
    cases res with
    | ok x => simp
    | err e =>
      cases e with
      | none => simp [hf]
      | some x =>
        simp only
        split <;> simp [hf]
  · simp at he; subst he
    simp [Exc.valueError, Exc.isGeneratorExit, fetchStopIterationValue, Exc.isStopIteration]

theorem genClearFrame_state (w : World V X) (r : Ref) :
    ((genClearFrame w r).get r).state = .cleared := by
  unfold genClearFrame
  split
  · assumption
  · simp

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
`ValueError` and changes nothing. -/
def GenCloseRejectsExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    (w.get r).state = .executing →
    genCloseF h (n + 1) w r =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))

/-- The same with the instruction pointer anywhere but at a depth-1 `RESUME`: the
case left over by `GenCloseRejectsExecuting`'s refutation, which is what main's
reordered `gen_close` makes unconditional. -/
def GenCloseRejectsExecutingPastResume : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    (w.get r).state = .executing →
    ¬ ((w.get r).instr.isResumeDepth1 = true ∧ w.noUnwindTools = true) →
    genCloseF h (n + 1) w r =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))

theorem genCloseRejectsExecutingPastResume_proven : GenCloseRejectsExecutingPastResume := by
  intro V X h n w r hs hi
  simp only [genCloseF, genCloseBody, closeDelegate, genYf, hs]
  simp [hi, genCloseFinish, genSendEx, genSendEx2_executing, hs, sendResultToRet,
    Exc.valueError, Exc.isGeneratorExit, fetchStopIterationValue, Exc.isStopIteration]

/-- The window: a frame just resumed, still at a depth-1 `RESUME`. Reached by
`gen_send_ex2`, which hands `resume` the frame in this state. -/
def executingAtResume : World Unit Unit :=
  { gens := fun _ => { kind := .gen, state := .executing, instr := .resume true }
    asends := fun _ => {}
    athrows := fun _ => {}
    ext := () }

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

theorem genCloseRejectsExecuting_refuted : ¬ GenCloseRejectsExecuting := by
  intro hp
  have := hp Unit Unit noopHooks 0 executingAtResume 0 rfl
  have h2 := congrArg Prod.snd this
  simp [genCloseF, genCloseBody, closeDelegate, genYf, executingAtResume, World.get,
    FrameState.finished, FrameState.toInt, InstrPtr.isResumeDepth1, genClearFrame, World.setState,
    World.set] at h2

/-- `gen_close`'s fast path (:410-422) agrees with the slow path on a frame the slow
path would simply unwind: if throwing `GeneratorExit` at the suspended depth-1
`RESUME` makes the frame raise it unchanged, then the world with unwinding tools
(`_PyEval_NoToolsForUnwind` false) takes the slow path to the same result and final
state as the fast path. The hypothesis is what a depth-1 frame does: no handler but
the outermost, whose `stopiteration_error` passes `GeneratorExit` through. -/
def GenCloseFastSlowAgree : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    (w.get r).state = .suspended → (w.get r).instr = .resume true → w.noUnwindTools = false →
    (∀ a, (h.resume (w.setState r .executing) r a (some Exc.generatorExit)).2 =
      .raised Exc.generatorExit) →
    let fast := genCloseF h (n + 1) { w with noUnwindTools := true } r
    let slow := genCloseF h (n + 1) w r
    fast.2 = .ok .none ∧ slow.2 = .ok .none ∧
      (fast.1.get r).state = .cleared ∧ (slow.1.get r).state = .cleared

theorem genCloseFastSlowAgree_proven : GenCloseFastSlowAgree := by
  intro V X h n w r hs hi hu hr
  have g1 : ({ w with noUnwindTools := true } : World V X).get r = w.get r := rfl
  have hnc : ¬ ((w.get r).state = .created ∧ isNonNull (some Obj.none : Option (Obj V)) = true) := by
    simp [isNonNull]
  have hslow : genSendEx2 h w r (some .none) true (some Exc.generatorExit) true =
      (clearGenFrame (h.resume (w.setState r .executing) r .none (some Exc.generatorExit)).1 r,
       .err (some Exc.generatorExit)) := by
    rw [genSendEx2_live h w r (some .none) true (some Exc.generatorExit) true hnc
      (by simp [hs]) (by simp [hs])]
    show finishResume _ r _ _ (h.resume (w.setState r .executing) r .none (some Exc.generatorExit)).2 = _
    rw [hr .none]
    rfl
  have hfast : genCloseF h (n + 1) { w with noUnwindTools := true } r =
      (genClearFrame (({ w with noUnwindTools := true } : World V X).setState r .completed) r, .ok .none) := by
    simp [genCloseF, g1, hs, genCloseBody, closeDelegate, genYf, hi, InstrPtr.isResumeDepth1]
  have hsl : genCloseF h (n + 1) w r = genCloseFinish h w r (some Exc.generatorExit) := by
    simp [genCloseF, hs, genCloseBody, closeDelegate, genYf, hi, hu, closePending]
  dsimp only
  rw [hfast, hsl]
  refine ⟨rfl, ?_, genClearFrame_state _ _, ?_⟩
  · simp only [genCloseFinish, genSendEx, hslow]
    simp [sendResultToRet, Exc.generatorExit, Exc.isGeneratorExit]
  · simp only [genCloseFinish, genSendEx, hslow]
    simp [sendResultToRet, clearGenFrame, Exc.generatorExit, Exc.isGeneratorExit]

end PyLean.Bytecode.GenObj
