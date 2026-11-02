import PyLean.Bytecode.GenObj.Props

/-!
# Properties of the async generator state machine
-/

namespace PyLean.Bytecode.GenObj

section Lemmas
variable {V X : Type}

theorem unwrap_err (w : World V X) (r : Ref) (res : Ret V) (e : Option (Exc V))
    (hu : (asyncGenUnwrapValue w r res).2 = .err e) :
    ((asyncGenUnwrapValue w r res).1.get r).agRunningAsync = false := by
  cases res with
  | err e' => simp [asyncGenUnwrapValue]
  | ok v =>
    cases v <;> simp_all [asyncGenUnwrapValue]

theorem athrows_unwrap (w : World V X) (r : Ref) (res : Ret V) :
    (asyncGenUnwrapValue w r res).1.athrows = w.athrows := by
  cases res with
  | err e' => simp only [asyncGenUnwrapValue]; split <;> rfl
  | ok v => cases v <;> rfl

theorem asends_unwrap (w : World V X) (r : Ref) (res : Ret V) :
    (asyncGenUnwrapValue w r res).1.asends = w.asends := by
  cases res with
  | err e' => simp only [asyncGenUnwrapValue]; split <;> rfl
  | ok v => cases v <;> rfl

theorem asendFinish_err (w : World V X) (a gen : Ref) (res : Ret V) (e)
    (he : (asendFinish w a gen res).2 = .err e) :
    ((asendFinish w a gen res).1.asends a).state = .closed ∧
      ((asendFinish w a gen res).1.get gen).agRunningAsync = false := by
  simp only [asendFinish] at he ⊢
  cases hu : (asyncGenUnwrapValue w gen res).2 with
  | ok v => simp [hu] at he
  | err e' =>
    simp only [hu]
    exact ⟨asendState_set _ _ _, unwrap_err w gen res e' hu⟩

theorem asendThrowFinish_err (w : World V X) (a gen : Ref) (res : Ret V) (e)
    (he : (asendThrowFinish w a gen res).2 = .err e) :
    ((asendThrowFinish w a gen res).1.asends a).state = .closed ∧
      ((asendThrowFinish w a gen res).1.get gen).agRunningAsync = false := by
  simp only [asendThrowFinish] at he ⊢
  cases hu : (asyncGenUnwrapValue w gen res).2 with
  | ok v => simp [hu] at he
  | err e' =>
    simp only [hu]
    exact ⟨asendState_set _ _ _, running_setRunning _ _ _⟩

theorem athrowCheckError_spec (w : World V X) (a gen : Ref) (m : Bool) (e : Option (Exc V)) :
    ((athrowCheckError w a gen m e).1.athrows a).state = .closed ∧
      ((athrowCheckError w a gen m e).1.get gen).agRunningAsync = false := by
  simp only [athrowCheckError]
  split <;> exact ⟨athrowState_set _ _ _, running_setRunning _ _ _⟩

theorem athrowYieldClose_spec (w : World V X) (a gen : Ref) :
    ((athrowYieldClose w a gen).1.athrows a).state = .closed ∧
      ((athrowYieldClose w a gen).1.get gen).agRunningAsync = false :=
  ⟨athrowState_set _ _ _, running_setRunning _ _ _⟩

theorem acloseTail_spec (w : World V X) (a gen : Ref) (t : Ret V) (e)
    (he : (acloseTail w a gen t).2 = .err e) :
    ((acloseTail w a gen t).1.athrows a).state = .closed ∧
      ((acloseTail w a gen t).1.get gen).agRunningAsync = false := by
  cases t with
  | err e' => exact athrowCheckError_spec w a gen true e'
  | ok v =>
    cases v
    case wrapped o => exact athrowYieldClose_spec w a gen
    all_goals simp [acloseTail] at he

theorem athrowStartAclose_err (h : Hooks V X) (fuel) (w : World V X) (a gen : Ref) (e)
    (he : (athrowStartAclose h fuel w a gen).2 = .err e) :
    ((athrowStartAclose h fuel w a gen).1.athrows a).state = .closed ∧
      ((athrowStartAclose h fuel w a gen).1.get gen).agRunningAsync = false :=
  acloseTail_spec _ a gen _ e he

theorem athrowIter_none_err (h : Hooks V X) (w : World V X) (a gen : Ref) (arg : Obj V) (e)
    (he : (athrowIter h w a gen none arg).2 = .err e) :
    ((athrowIter h w a gen none arg).1.athrows a).state = .closed ∧
      ((athrowIter h w a gen none arg).1.get gen).agRunningAsync = false :=
  acloseTail_spec _ a gen _ e he

theorem athrowIter_some_err (h : Hooks V X) (w : World V X) (a gen : Ref) (l) (arg : Obj V) (e)
    (he : (athrowIter h w a gen (some l) arg).2 = .err e) :
    ((athrowIter h w a gen (some l) arg).1.get gen).agRunningAsync = false :=
  unwrap_err _ gen _ e he

theorem athrowStartArgs_err (h : Hooks V X) (fuel) (w : World V X) (a gen : Ref)
    (tv) (e) (he : (athrowStartArgs h fuel w a gen tv).2 = .err e) :
    ((athrowStartArgs h fuel w a gen tv).1.athrows a).state = .closed ∧
      ((athrowStartArgs h fuel w a gen tv).1.get gen).agRunningAsync = false := by
  simp only [athrowStartArgs] at he ⊢
  generalize hu : asyncGenUnwrapValue _ gen _ = u at he ⊢
  obtain ⟨w', res⟩ := u
  cases res with
  | ok v => simp at he
  | err e' => exact athrowCheckError_spec w' a gen false e'

theorem athrowThrowFinish_err (w : World V X) (a gen : Ref) (args) (res : Ret V) (e)
    (he : (athrowThrowFinish w a gen args res).2 = .err e) :
    ((athrowThrowFinish w a gen args res).1.athrows a).state = .closed ∧
      ((athrowThrowFinish w a gen args res).1.get gen).agRunningAsync = false := by
  cases args with
  | some l =>
    simp only [athrowThrowFinish] at he ⊢
    cases hu : (asyncGenUnwrapValue w gen res).2 with
    | ok v => simp [hu] at he
    | err e' =>
      simp only [hu]
      exact ⟨athrowState_set _ _ _, running_setRunning _ _ _⟩
  | none =>
    cases res with
    | err e' =>
      simp only [athrowThrowFinish]
      split <;> exact ⟨athrowState_set _ _ _, running_setRunning _ _ _⟩
    | ok v =>
      cases v
      case wrapped o => exact ⟨athrowState_set _ _ _, running_setRunning _ _ _⟩
      all_goals simp [athrowThrowFinish] at he

end Lemmas

/-- `async_gen_unwrap_value` in full: on `NULL` the running flag is cleared (`NULL`
with no exception becoming `StopAsyncIteration`) and `ag_closed` can only be set; a
wrapped value becomes `StopIteration(value)` with the flag cleared; anything else
is an `await` passing through, with nothing changed. -/
def AsyncGenUnwrapValue : Prop :=
  ∀ (V X : Type) (w : World V X) (r : Ref),
    (∀ e : Option (Exc V),
      let u := asyncGenUnwrapValue w r (.err e)
      u.2 = .err (some (e.getD Exc.stopAsyncIteration)) ∧
      (u.1.get r).agRunningAsync = false ∧
      ((w.get r).agClosed = true → (u.1.get r).agClosed = true)) ∧
    (∀ v : Obj V,
      let u := asyncGenUnwrapValue w r (.ok (.wrapped v))
      u.2 = .err (some (setStopIterationValue v)) ∧ (u.1.get r).agRunningAsync = false) ∧
    (∀ v : Obj V, (∀ x, v ≠ .wrapped x) → asyncGenUnwrapValue w r (.ok v) = (w, .ok v))

theorem asyncGenUnwrapValue_proven : AsyncGenUnwrapValue := by
  intro V X w r
  refine ⟨?_, ?_, ?_⟩
  · intro e u
    refine ⟨rfl, running_setRunning _ _ _, ?_⟩
    intro hc
    simp only [u, asyncGenUnwrapValue]
    split <;> simp_all [World.setRunning, World.setClosed]
  · intro v u
    exact ⟨rfl, running_setRunning _ _ _⟩
  · intro v hv
    cases v
    case wrapped o => exact absurd rfl (hv o)
    all_goals rfl

/-- After `asend`'s `send` or `throw` raises, the awaitable is
`AWAITABLE_STATE_CLOSED`: an awaited `asend()` cannot be reused. -/
def AsendErrorCloses : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Option (Obj V))
    (args : List (Obj V)) (e : Option (Exc V)),
    ((asyncGenAsendSend h w a arg).2 = .err e →
      ((asyncGenAsendSend h w a arg).1.asends a).state = .closed) ∧
    ((asyncGenAsendThrow h fuel w a args).2 = .err e →
      ((asyncGenAsendThrow h fuel w a args).1.asends a).state = .closed)

theorem asendErrorCloses_proven : AsendErrorCloses := by
  intro V X h fuel w a arg args e
  constructor
  · intro he
    simp only [asyncGenAsendSend] at he ⊢
    split
    · assumption
    · split
      · exact asendState_set _ _ _
      · rw [if_neg ‹_›, if_neg ‹_›] at he
        exact (asendFinish_err _ _ _ _ e he).1
  · intro he
    simp only [asyncGenAsendThrow] at he ⊢
    split
    · assumption
    · split
      · exact asendState_set _ _ _
      · rw [if_neg ‹_›, if_neg ‹_›] at he
        exact (asendThrowFinish_err _ _ _ _ e he).1

/-- An `asend` that got past its state checks clears `ag_running_async` whenever
`send` or `throw` raises, on every path: the flag never stays set after the
generator gave up control with an exception. -/
def AsendErrorClearsRunning : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Option (Obj V))
    (args : List (Obj V)) (e : Option (Exc V)),
    (w.asends a).state ≠ .closed →
    ¬ ((w.asends a).state = .init ∧ (w.get (w.asends a).gen).agRunningAsync = true) →
    ((asyncGenAsendSend h w a arg).2 = .err e →
      ((asyncGenAsendSend h w a arg).1.get (w.asends a).gen).agRunningAsync = false) ∧
    ((asyncGenAsendThrow h fuel w a args).2 = .err e →
      ((asyncGenAsendThrow h fuel w a args).1.get (w.asends a).gen).agRunningAsync = false)

theorem asendErrorClearsRunning_proven : AsendErrorClearsRunning := by
  intro V X h fuel w a arg args e h1 h2
  constructor
  · intro he
    simp only [asyncGenAsendSend, if_neg h1, if_neg h2] at he ⊢
    exact (asendFinish_err _ _ _ _ e he).2
  · intro he
    simp only [asyncGenAsendThrow, if_neg h1, if_neg h2] at he ⊢
    exact (asendThrowFinish_err _ _ _ _ e he).2

/-- Every `aclose()` awaitable that raises from `send` with `None` is closed and has
cleared `ag_running_async`, on every path. -/
def AcloseErrorCloses : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V)
    (e : Option (Exc V)),
    (w.athrows a).args = none → arg.isNone = true →
    (asyncGenAthrowSend h fuel w a arg).2 = .err e →
    ((asyncGenAthrowSend h fuel w a arg).1.athrows a).state = .closed

theorem acloseErrorCloses_proven : AcloseErrorCloses := by
  intro V X h fuel w a arg e hargs harg he
  simp only [asyncGenAthrowSend] at he ⊢
  split
  · assumption
  · rename_i h1
    rw [if_neg h1] at he
    split
    · exact athrowState_set _ _ _
    · rename_i h2
      rw [if_neg h2] at he
      split
      · rename_i h3
        rw [if_pos h3] at he
        split
        · exact athrowState_set _ _ _
        · rename_i h4
          rw [if_neg h4] at he
          split
          · exact athrowState_set _ _ _
          · rename_i h5
            rw [if_neg h5, if_neg (by simp [harg])] at he
            rw [if_neg (by simp [harg]), hargs]
            rw [hargs] at he
            have := (athrowStartAclose_err h fuel _ a _ e he).1
            exact this
      · rename_i h3
        rw [if_neg h3, hargs] at he
        rw [hargs]
        exact (athrowIter_none_err h w a _ arg e he).1

/-- The first step of `athrow()`/`aclose()` closes the awaitable and clears
`ag_running_async` whenever it raises. Since 3.15 every `athrow()` awaitable has a
well-formed argument list, so this needs no hypothesis on it. -/
def AThrowStartErrorCloses : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V)
    (e : Option (Exc V)),
    (w.athrows a).state = .init → arg.isNone = true →
    (w.get (w.athrows a).gen).state.finished = false →
    (w.get (w.athrows a).gen).agRunningAsync = false →
    (w.get (w.athrows a).gen).agClosed = false →
    (asyncGenAthrowSend h fuel w a arg).2 = .err e →
    ((asyncGenAthrowSend h fuel w a arg).1.athrows a).state = .closed ∧
    ((asyncGenAthrowSend h fuel w a arg).1.get (w.athrows a).gen).agRunningAsync = false

theorem aThrowStartErrorCloses_proven : AThrowStartErrorCloses := by
  intro V X h fuel w a arg e hs harg hf hr hc he
  simp only [asyncGenAthrowSend, hs, hf, hr, hc, harg] at he ⊢
  simp at he ⊢
  cases hargs : (w.athrows a).args with
  | none =>
    rw [hargs] at he
    exact athrowStartAclose_err h fuel _ a _ e he
  | some l =>
    rw [hargs] at he
    exact athrowStartArgs_err h fuel _ a _ l e he

/-- Stated over every state of the awaitable: an `athrow()` or `aclose()` awaitable
that raises from `send(None)` is closed. False: after the first step, the `athrow()` path
at :2378-2380 returns without setting `AWAITABLE_STATE_CLOSED`. -/
def AThrowErrorCloses : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V)
    (e : Option (Exc V)),
    arg.isNone = true →
    (asyncGenAthrowSend h fuel w a arg).2 = .err e →
    ((asyncGenAthrowSend h fuel w a arg).1.athrows a).state = .closed

/-- An `athrow()` awaitable that already went through one `await`, and a frame that
now yields a value. -/
def athrowIterWorld : World Unit Unit :=
  { gens := fun _ => { kind := .asyncGen, state := .suspendedYieldFrom, agRunningAsync := true }
    asends := fun _ => {}
    athrows := fun _ => { gen := 0, args := some (.none, none, none), state := .iter }
    ext := () }

def yieldWrappedHooks : Hooks Unit Unit :=
  { noopHooks with resume := fun w _ _ _ => (w, .yielded false (.wrapped .none) false .none) }

theorem aThrowErrorCloses_refuted : ¬ AThrowErrorCloses := by
  intro hp
  have := hp Unit Unit yieldWrappedHooks 0 athrowIterWorld 0 .none _ rfl rfl
  exact absurd this (by decide)

/-- An `athrow()`/`aclose()` awaitable that got past its state checks clears
`ag_running_async` when `send(None)` raises. This was false on 3.14.7, where `athrow()` with a
bad argument count failed after the flag was set: `bytecode-gen-athrow-bad-args-stuck-running`.
3.15 moved `PyArg_UnpackTuple` to `async_gen_athrow_new`, :2604-2606, so no such awaitable
exists. -/
def AThrowErrorClearsRunning : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V)
    (e : Option (Exc V)),
    (w.athrows a).state ≠ .closed →
    (w.get (w.athrows a).gen).state.finished = false →
    ((w.athrows a).state = .init → (w.get (w.athrows a).gen).agRunningAsync = false ∧
      (w.get (w.athrows a).gen).agClosed = false) →
    arg.isNone = true →
    (asyncGenAthrowSend h fuel w a arg).2 = .err e →
    ((asyncGenAthrowSend h fuel w a arg).1.get (w.athrows a).gen).agRunningAsync = false

theorem aThrowErrorClearsRunning_proven : AThrowErrorClearsRunning := by
  intro V X h fuel w a arg e h0 hf hi harg he
  by_cases hinit : (w.athrows a).state = .init
  · obtain ⟨hr, hc⟩ := hi hinit
    exact (aThrowStartErrorCloses_proven V X h fuel w a arg e hinit harg hf hr hc he).2
  · simp only [asyncGenAthrowSend, if_neg h0, hf, if_neg hinit] at he ⊢
    simp at he ⊢
    cases hargs : (w.athrows a).args with
    | none =>
      try rw [hargs] at he
      exact (athrowIter_none_err h w a _ arg e he).2
    | some l =>
      try rw [hargs] at he
      exact athrowIter_some_err h w a _ l arg e he

/-- `athrow` with the wrong number of arguments fails where the awaitable would be made,
so no awaitable holds a bad list. This is what makes `AThrowErrorClearsRunning` hold. -/
def AthrowBadArgsRejected : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r a : Ref) (args : List (Obj V)),
    (args.length = 0 ∨ args.length > 3) → (asyncGenAthrow h w r a args).2 matches .fail _

theorem athrowBadArgsRejected_proven : AthrowBadArgsRejected := by
  intro V X h w r a args hb
  simp only [asyncGenAthrow]
  generalize (if args.length > 1 then _ else (w, none)) = q
  obtain ⟨w0, warned⟩ := q
  cases warned with
  | some e => simp
  | none =>
    simp only
    generalize asyncGenInitHooks h w0 r = p
    obtain ⟨w1, st⟩ := p
    cases st with
    | fail e => simp
    | ok =>
      simp only
      have hs : (checkPositional "athrow" args.length 1 3 : Option (Exc V)).isSome = true := by
        rcases hb with h0 | h3
        · simp [checkPositional, h0]
        · have : ¬ args.length < 1 := by omega
          simp [checkPositional, this, h3]
      cases hc : (checkPositional "athrow" args.length 1 3 : Option (Exc V)) with
      | none => simp [hc] at hs
      | some e => simp

/-- After `athrow`'s `throw` raises, the awaitable is closed and, if it got past its
state checks, `ag_running_async` is cleared, in both modes. -/
def AThrowThrowErrorCloses : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (args : List (Obj V))
    (e : Option (Exc V)),
    (asyncGenAthrowThrow h fuel w a args).2 = .err e →
    ((asyncGenAthrowThrow h fuel w a args).1.athrows a).state = .closed ∧
    ((w.athrows a).state ≠ .closed →
      ¬ ((w.athrows a).state = .init ∧ (w.get (w.athrows a).gen).agRunningAsync = true) →
      ((asyncGenAthrowThrow h fuel w a args).1.get (w.athrows a).gen).agRunningAsync = false)

theorem aThrowThrowErrorCloses_proven : AThrowThrowErrorCloses := by
  intro V X h fuel w a args e he
  by_cases h1 : (w.athrows a).state = .closed
  · have : asyncGenAthrowThrow h fuel w a args =
        (w, .err (some (Exc.runtimeError reuseAthrowMsg))) := by
      simp [asyncGenAthrowThrow, h1]
    rw [this]
    exact ⟨h1, fun hn => absurd h1 hn⟩
  by_cases h2 : (w.athrows a).state = .init ∧ (w.get (w.athrows a).gen).agRunningAsync = true
  · simp only [asyncGenAthrowThrow, if_neg h1, if_pos h2]
    exact ⟨athrowState_set _ _ _, fun _ hn => absurd h2 hn⟩
  · simp only [asyncGenAthrowThrow, if_neg h1, if_neg h2] at he ⊢
    have := athrowThrowFinish_err _ a _ _ _ e he
    exact ⟨this.1, fun _ _ => this.2⟩

/-- The `close()` method of an `asend` or `athrow` awaitable: if it returns normally
the awaitable is closed, and closing again returns `None` with no effect. -/
def AwaitableCloseIdempotent : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (v : Obj V),
    ((asyncGenAsendClose h fuel w a).2 = .ok v →
      asyncGenAsendClose h fuel (asyncGenAsendClose h fuel w a).1 a =
        ((asyncGenAsendClose h fuel w a).1, .ok .none)) ∧
    ((asyncGenAthrowClose h fuel w a).2 = .ok v →
      asyncGenAthrowClose h fuel (asyncGenAthrowClose h fuel w a).1 a =
        ((asyncGenAthrowClose h fuel w a).1, .ok .none))

section CloseL
variable {V X : Type}

theorem closeResult_ok (r : Ret V) (v) (h : closeResult r = .ok v) : ∃ e, r = .err e := by
  cases r with
  | err e => exact ⟨e, rfl⟩
  | ok x => simp [closeResult] at h

theorem asendClose_closed (h : Hooks V X) (fuel) (w : World V X) (a) (v)
    (hv : (asyncGenAsendClose h fuel w a).2 = .ok v) :
    ((asyncGenAsendClose h fuel w a).1.asends a).state = .closed := by
  simp only [asyncGenAsendClose] at hv ⊢
  split
  · assumption
  · rename_i hn
    rw [if_neg hn] at hv
    obtain ⟨e, he⟩ := closeResult_ok _ _ hv
    exact (asendErrorCloses_proven V X h fuel w a none _ e).2 he

theorem athrowClose_closed (h : Hooks V X) (fuel) (w : World V X) (a) (v)
    (hv : (asyncGenAthrowClose h fuel w a).2 = .ok v) :
    ((asyncGenAthrowClose h fuel w a).1.athrows a).state = .closed := by
  simp only [asyncGenAthrowClose] at hv ⊢
  split
  · assumption
  · rename_i hn
    rw [if_neg hn] at hv
    obtain ⟨e, he⟩ := closeResult_ok _ _ hv
    exact (aThrowThrowErrorCloses_proven V X h fuel w a _ e he).1

end CloseL

theorem awaitableCloseIdempotent_proven : AwaitableCloseIdempotent := by
  intro V X h fuel w a v
  constructor
  · intro hv
    have := asendClose_closed h fuel w a v hv
    simp [asyncGenAsendClose] at this ⊢
    simp [this]
  · intro hv
    have := athrowClose_closed h fuel w a v hv
    simp [asyncGenAthrowClose] at this ⊢
    simp [this]

/-- A closed awaitable: `send`, `next` and `throw` raise the "cannot reuse" error
and `close` returns `None`, with no effect on anything and no call into the frame. -/
def AwaitableClosedTerminal : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Option (Obj V))
    (arg' : Obj V) (args : List (Obj V)),
    ((w.asends a).state = .closed →
      asyncGenAsendSend h w a arg = (w, .err (some (Exc.runtimeError reuseAsendMsg))) ∧
      asyncGenAsendIternext h w a = (w, .err (some (Exc.runtimeError reuseAsendMsg))) ∧
      asyncGenAsendThrow h fuel w a args = (w, .err (some (Exc.runtimeError reuseAsendMsg))) ∧
      asyncGenAsendClose h fuel w a = (w, .ok .none)) ∧
    ((w.athrows a).state = .closed →
      asyncGenAthrowSend h fuel w a arg' = (w, .err (some (Exc.runtimeError reuseAthrowMsg))) ∧
      asyncGenAthrowIternext h fuel w a = (w, .err (some (Exc.runtimeError reuseAthrowMsg))) ∧
      asyncGenAthrowThrow h fuel w a args = (w, .err (some (Exc.runtimeError reuseAthrowMsg))) ∧
      asyncGenAthrowClose h fuel w a = (w, .ok .none))

theorem awaitableClosedTerminal_proven : AwaitableClosedTerminal := by
  intro V X h fuel w a arg arg' args
  constructor
  · intro hc
    simp [asyncGenAsendSend, asyncGenAsendIternext, asyncGenAsendThrow, asyncGenAsendClose, hc]
  · intro hc
    simp [asyncGenAthrowSend, asyncGenAthrowIternext, asyncGenAthrowThrow, asyncGenAthrowClose, hc]

/-- A fresh awaitable on a generator with `ag_running_async` set fails with the
"already running" `RuntimeError`, closes itself, and leaves the generator alone: one
of `anext`/`asend`/`aclose`/`athrow` cannot interleave with another. -/
def AwaitableRunningExclusion : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Option (Obj V))
    (arg' : Obj V) (args : List (Obj V)),
    ((w.asends a).state = .init → (w.get (w.asends a).gen).agRunningAsync = true →
      asyncGenAsendSend h w a arg =
        (w.setAsendState a .closed, .err (some (Exc.runtimeError anextRunningMsg))) ∧
      asyncGenAsendThrow h fuel w a args =
        (w.setAsendState a .closed, .err (some (Exc.runtimeError anextRunningMsg)))) ∧
    ((w.athrows a).state = .init → (w.get (w.athrows a).gen).agRunningAsync = true →
      (w.get (w.athrows a).gen).state.finished = false →
      asyncGenAthrowSend h fuel w a arg' =
        (w.setAthrowState a .closed,
         .err (some (Exc.runtimeError (athrowRunningMsg (w.athrows a).args)))) ∧
      asyncGenAthrowThrow h fuel w a args =
        (w.setAthrowState a .closed,
         .err (some (Exc.runtimeError (athrowRunningMsg (w.athrows a).args)))))

theorem awaitableRunningExclusion_proven : AwaitableRunningExclusion := by
  intro V X h fuel w a arg arg' args
  constructor
  · intro hi hr
    simp [asyncGenAsendSend, asyncGenAsendThrow, hi, hr]
  · intro hi hr hf
    simp [asyncGenAthrowSend, asyncGenAthrowThrow, hi, hr, hf]

/-- `athrow`/`aclose` on a finished generator ends the awaitable with `StopIteration`
at once, whatever its state and argument: the frame is not touched. -/
def AthrowOnFinished : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V),
    (w.athrows a).state ≠ .closed →
    (w.get (w.athrows a).gen).state.finished = true →
    asyncGenAthrowSend h fuel w a arg =
      (w.setAthrowState a .closed, .err (some Exc.stopIterationNone)) ∧
    asyncGenAthrowIternext h fuel w a =
      (w.setAthrowState a .closed, .err (some Exc.stopIterationNone))

theorem athrowOnFinished_proven : AthrowOnFinished := by
  intro V X h fuel w a arg h1 h2
  simp [asyncGenAthrowSend, asyncGenAthrowIternext, h1, h2]

/-- `athrow`/`aclose` on a generator with `ag_closed` set that is not finished
(`aclose()` was ignored) raises `StopAsyncIteration` without resuming it. -/
def AthrowOnClosed : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (a : Ref) (arg : Obj V),
    (w.athrows a).state = .init →
    (w.get (w.athrows a).gen).state.finished = false →
    (w.get (w.athrows a).gen).agRunningAsync = false →
    (w.get (w.athrows a).gen).agClosed = true →
    asyncGenAthrowSend h fuel w a arg =
      (w.setAthrowState a .closed, .err (some Exc.stopAsyncIteration))

theorem athrowOnClosed_proven : AthrowOnClosed := by
  intro V X h fuel w a arg h1 h2 h3 h4
  simp [asyncGenAthrowSend, h1, h2, h3, h4]

/-- `async_gen_init_hooks` runs at most once per object: once `ag_hooks_inited` is
set nothing happens, and `firstiter` runs with the flag already set, so a raising
hook is not retried and a reentrant call does not run it twice. -/
def AsyncGenHooksOnce : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (bad : World V X × Ret V) (w : World V X) (r : Ref),
    ((w.get r).agHooksInited = true → asyncGenInitHooks h w r = (w, .ok)) ∧
    asyncGenInitHooks
      { h with callOneArg := fun w f a =>
          if (w.get r).agHooksInited = true then h.callOneArg w f a else bad } w r =
      asyncGenInitHooks h w r

theorem asyncGenHooksOnce_proven : AsyncGenHooksOnce := by
  intro V X h bad w r
  constructor
  · intro hi
    simp [asyncGenInitHooks, hi]
  · by_cases hi : (w.get r).agHooksInited = true
    · simp [asyncGenInitHooks, hi]
    · simp only [asyncGenInitHooks, hi]
      cases hf : w.finalizerHook <;> cases hl : w.firstiter <;>
        simp [World.set, World.get, hf, hl]

/-- `anext`, `asend`, `aclose` and `athrow` create a fresh `AWAITABLE_STATE_INIT`
awaitable holding exactly their argument (NULL for `anext` and `aclose`), after the
hooks and, for `athrow`, the deprecation check. And `athrow` with the wrong number of
arguments is refused the same way. -/
def AsyncGenMethodsCreate : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r a : Ref) (arg : Obj V) (args : List (Obj V)),
    ((asyncGenAnext h w r a).2 matches .ok →
      (asyncGenAnext h w r a).1.asends a = { gen := r, sendval := none, state := .init }) ∧
    ((asyncGenAsend h w r a arg).2 matches .ok →
      (asyncGenAsend h w r a arg).1.asends a = { gen := r, sendval := some arg, state := .init }) ∧
    ((asyncGenAclose h w r a).2 matches .ok →
      (asyncGenAclose h w r a).1.athrows a = { gen := r, args := none, state := .init }) ∧
    ((asyncGenAthrow h w r a args).2 matches .ok →
      (asyncGenAthrow h w r a args).1.athrows a =
        { gen := r, args := some (unpackThrowArgs args), state := .init })

theorem asyncGenMethodsCreate_proven : AsyncGenMethodsCreate := by
  intro V X h w r a arg args
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [asyncGenAnext]
    generalize asyncGenInitHooks h w r = p
    obtain ⟨w1, st⟩ := p
    cases st <;> simp [asyncGenAsendNew]
  · simp only [asyncGenAsend]
    generalize asyncGenInitHooks h w r = p
    obtain ⟨w1, st⟩ := p
    cases st <;> simp [asyncGenAsendNew]
  · simp only [asyncGenAclose]
    generalize asyncGenInitHooks h w r = p
    obtain ⟨w1, st⟩ := p
    cases st <;> simp [asyncGenAthrowNew]
  · simp only [asyncGenAthrow]
    generalize (if args.length > 1 then _ else (w, none)) = q
    obtain ⟨w0, warned⟩ := q
    cases warned with
    | some e => simp
    | none =>
      simp only
      generalize asyncGenInitHooks h w0 r = p
      obtain ⟨w1, st⟩ := p
      cases st with
      | fail e => simp
      | ok =>
        simp only
        cases hc : (checkPositional "athrow" args.length 1 3 : Option (Exc V)) <;>
          simp [asyncGenAthrowNew]

/-- The finalizers of the awaitables only ever warn, and only about an awaitable
that was never started. -/
def AwaitableFinalizeWarnsInit : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (a : Ref),
    ((w.asends a).state ≠ .init → asyncGenAsendFinalize h w a = w) ∧
    ((w.asends a).state = .init →
      asyncGenAsendFinalize h w a = h.warnUnawaitedAgen w (w.asends a).gen "asend") ∧
    ((w.athrows a).state ≠ .init → asyncGenAthrowFinalize h w a = w) ∧
    ((w.athrows a).state = .init →
      asyncGenAthrowFinalize h w a = h.warnUnawaitedAgen w (w.athrows a).gen
        (match (w.athrows a).args with | some _ => "athrow" | none => "aclose"))

theorem awaitableFinalizeWarnsInit_proven : AwaitableFinalizeWarnsInit := by
  intro V X h w a
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro hs <;>
    simp [asyncGenAsendFinalize, asyncGenAthrowFinalize, hs] <;> rfl

end PyLean.Bytecode.GenObj
