import PyLean.Bytecode.StackEffect

/-!
Frame switching, exception unwinding and the handled-exception chain, for all
states. These are the invariants the compiler relies on when it lays out
`try`/`except`, `with`, `for` and generators: `exception_unwind` restores the stack
depth recorded in the exception table, `RETURN_VALUE` resumes the caller at
`instr_ptr + return_offset` with the value on top, and
`PUSH_EXC_INFO`/`POP_EXCEPT` nest.
-/

namespace PyLean.Bytecode

open Uop

/-- `RETURN_VALUE` removes the frame, resumes the caller at its return offset and
leaves the value on top of the caller's stack, whatever the caller's stack is.
The frame is not a generator's: `owner = .thread`. -/
def ReturnValue : Prop :=
  ∀ (regs : Regs) (retval : Val) (rest : List Val) (caller : Frame) (prev : List Frame),
    regs.prev = caller :: prev → regs.frame.owner = .thread →
    RETURN_VALUE ⟨regs, retval :: rest⟩ =
      .ok () ⟨{ regs with
        rt := { regs.rt with pyRecursionRemaining := regs.rt.pyRecursionRemaining + 1 }
        frame := caller, prev := prev, next := caller.instrPtr + caller.returnOffset },
        retval :: caller.stack⟩

theorem returnValue_proven : ReturnValue := by
  intro regs retval rest caller prev hp ho
  obtain ⟨rt, frame, pv, next⟩ := regs
  simp only at hp ho
  subst hp
  simp [RETURN_VALUE, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, getFrame, leaveRecursivePy,
    popToPrevious, frameClearAndPop, ho, loadIp, monadLift, liftM, MonadLift.monadLift, pure,
    EStateM.pure]

/-- A handler found by `get_exception_handler` truncates the stack to the recorded
depth, pushes `lasti` if the entry says so, pushes the exception, and jumps. Every
value below `level` survives. -/
def UnwindToHandler : Prop :=
  ∀ (P : Program) (n : Nat) (v : Val) (s : St) (handler level : Nat) (lasti : Bool),
    s.regs.next ≠ 0 →
    getExceptionHandler ((P[s.regs.frame.code]?.map (·.exceptiontable)).getD #[]) (s.regs.next - 1) =
      some (handler, level, lasti) →
    unwind P (n + 1) v s =
      .cont ⟨{ s.regs with next := handler },
        v :: ((if lasti then [Val.tagged s.regs.frame.instrPtr] else []) ++
          s.stack.drop (s.stack.length - level))⟩

theorem unwindToHandler_proven : UnwindToHandler := by
  intro P n v s handler level lasti h0 h
  simp only [unwind, h0, ↓reduceIte, h]
  cases lasti <;> simp

/-- With no handler the frame is popped and the search goes on in the caller at its
`instr_ptr`, after the caller's traceback entry (`goto error` there); the frame's stack is simply
dropped. -/
def UnwindNoHandler : Prop :=
  ∀ (P : Program) (n : Nat) (v : Val) (s : St) (caller : Frame) (rest : List Frame),
    (s.regs.next = 0 ∨ getExceptionHandler ((P[s.regs.frame.code]?.map (·.exceptiontable)).getD #[])
      (s.regs.next - 1) = none) →
    s.regs.prev = caller :: rest → s.regs.frame.owner = .thread → caller.owner ≠ .interpreter →
    unwind P (n + 1) v s =
      unwind P n v ⟨{ rt := tracebackHere P { caller with returnOffset := 0 } v
                              { s.regs.rt with pyRecursionRemaining := s.regs.rt.pyRecursionRemaining + 1 }
                      frame := { caller with returnOffset := 0 }, prev := rest,
                      next := caller.instrPtr }, caller.stack⟩

theorem unwindNoHandler_proven : UnwindNoHandler := by
  intro P n v s caller rest h hp ho hc
  have hn : (if s.regs.next = 0 then none else getExceptionHandler
      ((P[s.regs.frame.code]?.map (·.exceptiontable)).getD #[]) (s.regs.next - 1)) = none := by
    rcases h with h | h
    · simp [h]
    · simp [h]
  simp only [unwind]
  simp only [hn, leaveRecursivePy, hp, frameClearAndPop, ho]
  have : (caller.owner == FrameOwner.interpreter) = false := by simpa using hc
  simp [this, pure, EStateM.pure]

/-- With no handler in the last frame above an entry frame, evaluation stops with
the exception: `return NULL`. -/
def UnwindExit : Prop :=
  ∀ (P : Program) (n : Nat) (v : Val) (s : St) (caller : Frame) (rest : List Frame),
    (s.regs.next = 0 ∨ getExceptionHandler ((P[s.regs.frame.code]?.map (·.exceptiontable)).getD #[])
      (s.regs.next - 1) = none) →
    s.regs.prev = caller :: rest → s.regs.frame.owner = .thread → caller.owner = .interpreter →
    ∃ rt, unwind P (n + 1) v s = .raised v rt ∧ rt.heap = s.regs.rt.heap

theorem unwindExit_proven : UnwindExit := by
  intro P n v s caller rest h hp ho hc
  have hn : (if s.regs.next = 0 then none else getExceptionHandler
      ((P[s.regs.frame.code]?.map (·.exceptiontable)).getD #[]) (s.regs.next - 1)) = none := by
    rcases h with h | h
    · simp [h]
    · simp [h]
  simp only [unwind]
  simp only [hn, leaveRecursivePy, hp, frameClearAndPop, ho]
  simp [hc, pure, EStateM.pure]

/-- `PUSH_EXC_INFO` then `POP_EXCEPT` restores `tstate->exc_info->exc_value`, which is
why `except` blocks nest: the handled exception after the block is the one before
it, whatever that was, including none at all. -/
def ExcInfoNests : Prop :=
  ∀ (regs : Regs) (exc : Val) (rest : List Val) (top : Val) (chain : List Val),
    regs.rt.excInfo = top :: chain → top ≠ .none →
    (do PUSH_EXC_INFO; (popExcKeep : M Unit); POP_EXCEPT) ⟨regs, exc :: rest⟩ =
      .ok () ⟨regs, rest⟩
where
  /-- The handler body takes the exception off the stack. -/
  popExcKeep : M Unit := stk 1 0 fun _ => pure []

theorem excInfoNests_proven : ExcInfoNests := by
  intro regs exc rest top chain h hn
  obtain ⟨rt, frame, pv, next⟩ := regs
  simp only at h
  obtain ⟨heap, out, excInfo, rem, lim, ver, bd, ss, pf⟩ := rt
  simp only at h
  subst h
  by_cases ht : top = .null
  · subst ht
    simp [PUSH_EXC_INFO, POP_EXCEPT, ExcInfoNests.popExcKeep, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, getExcInfoTop, setExcInfoTop, pure, EStateM.pure, monadLift, liftM,
      MonadLift.monadLift]
  · simp [PUSH_EXC_INFO, POP_EXCEPT, ExcInfoNests.popExcKeep, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, getExcInfoTop, setExcInfoTop, pure, EStateM.pure, monadLift, liftM,
      MonadLift.monadLift, ht, hn]

/-- `FOR_ITER` on an exhausted iterator jumps over `END_FOR` with `iter` and `index_or_null`
left on the stack, which is the `(iter, null_or_index -- iter, null_or_index, next)` signature
with the `END_FOR` that would have popped `next` already applied: the `POP_ITER` at the target
takes the two slots. This holds for both forms of the slot, the tagged index and `NULL`, and for
whatever the step did to the heap on the way to the end (a stateful `__next__` that records its
last call, say): the runtime after the instruction is exactly the runtime that one step left. -/
def ForIterExhausted : Prop :=
  ∀ (e : Env) (regs : Regs) (it index : Val) (rest : List Val) (rt : Rt),
    virtualNext e it index regs.rt = .ok none rt →
    FOR_ITER e ⟨regs, index :: it :: rest⟩ =
      .error .dispatch
        ⟨{ regs with rt := rt, next := (regs.next + ((e.oparg : Int) + 1)).toNat }, index :: it :: rest⟩

theorem forIterExhausted_proven : ForIterExhausted := by
  intro e regs it index rest rt h
  simp [FOR_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, peekN, bind, EStateM.bind, BM.lift, RM.lift, h,
    jumpBy, pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw,
    MonadExceptOf.throw, monadLift, liftM, MonadLift.monadLift]

/-- `FOR_ITER` with a next item writes the new `index_or_null` back to its slot and pushes
the item above it, with the runtime the one step left (a `__next__` that changes state, a
`list_iterator` advancing or a generator running to its next `yield`, included). -/
def ForIterNext : Prop :=
  ∀ (e : Env) (regs : Regs) (it index index' v : Val) (rest : List Val) (rt : Rt),
    virtualNext e it index regs.rt = .ok (some (v, index')) rt →
    FOR_ITER e ⟨regs, index :: it :: rest⟩ = .ok () ⟨{ regs with rt := rt }, v :: index' :: it :: rest⟩

theorem forIterNext_proven : ForIterNext := by
  intro e regs it index index' v rest rt h
  simp [FOR_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, peekN, popN, pushAll, bind, EStateM.bind, BM.lift,
    RM.lift, h, pure, EStateM.pure, monadLift, liftM, MonadLift.monadLift]

/-- `YIELD_VALUE` suspends: the generator records `FRAME_SUSPENDED + oparg`, the frame
is stored with `instr_ptr` on the next instruction and the saved stack, the caller
resumes after the `SEND`/`FOR_ITER` that entered it, and the handled exception of
the generator goes back into the generator. -/
def YieldSuspends : Prop :=
  ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val) (a : Addr) (g : GenObj) (ev : Val)
    (chain : List Val) (caller : Frame) (prev : List Frame),
    regs.frame.owner = .generator a → regs.rt.heap[a]? = some (.gen g) →
    regs.rt.excInfo = ev :: chain → regs.prev = caller :: prev →
    ∃ s', YIELD_VALUE e ⟨regs, v :: rest⟩ = .ok () s' ∧
      s'.stack = v :: caller.stack ∧ s'.regs.next = caller.instrPtr + 2 ∧
      s'.regs.rt.excInfo = chain ∧ s'.regs.frame = caller ∧
      s'.regs.rt.heap[a]? = some (.gen { g with
        frameState := 1 + (e.oparg : Int), excValue := ev,
        frame := { regs.frame with instrPtr := regs.frame.instrPtr + 1, stack := rest } })

end PyLean.Bytecode
