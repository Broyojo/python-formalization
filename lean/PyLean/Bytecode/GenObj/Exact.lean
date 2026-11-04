import PyLean.Bytecode.GenObj.Legal

/-!
# Exact outcomes of the generator operations, `Objects/genobject.c`

Each statement gives the result and the resulting world of one operation for every state
and for every outcome of the Python code the body calls (the frame, a sub-iterator's
`close` or `throw`, the hooks). The outcomes of those calls are hypotheses of the form
`h.resume w r arg exc = (w', o)`: the statement pins which call the body makes, with which
arguments and in which world, and what it does with each answer. A body that never resumed
the frame, resumed it with other arguments, or always failed, contradicts some instance.

The spec-side helpers below (`afterYield`, `clearedWorld`, `stopIterationOf`, `FastClose`,
`closeOutcome`) are written out from the C, not taken from the model.
-/

namespace PyLean.Bytecode.GenObj

section Spec
variable {V X : Type}

/-- What `_YIELD_VALUE` leaves (`Python/bytecodes.c:1856-1872`): `FRAME_SUSPENDED + oparg`,
the next instruction, and the stack. -/
def afterYield (w : World V X) (r : Ref) (oparg : Bool) (nxt : InstrPtr) (top : Obj V) :
    World V X :=
  w.set r { w.get r with
    state := if oparg then .suspendedYieldFrom else .suspended, instr := nxt, stackTop := top }

/-- `gi_frame_state = FRAME_CLEARED` and `gen_clear_frame` (:167-175), which drops the
frame's contents (what the model holds of them is the stack). -/
def clearedWorld (w : World V X) (r : Ref) : World V X :=
  w.set r { w.get r with state := .cleared, stackTop := .none }

/-- `gen_set_stop_iteration` (:385-399): `StopAsyncIteration` for an async generator, else
`StopIteration` carrying the value (`StopIteration()` when it is `None`, which the model
does not tell apart from `StopIteration(None)`). -/
def stopIterationOf (kind : GenKind) (v : Obj V) : Exc V :=
  if kind = .asyncGen then ⟨.stopAsyncIteration, "StopAsyncIteration", "", .none⟩
  else ⟨.stopIteration, "StopIteration", "", v⟩

/-- The fast path of `gen_close` (:500-511): `is_resume(frame->instr_ptr)` (`RESUME`,
`RESUME_CHECK`, `RESUME_CHECK_JIT` or `INSTRUMENTED_RESUME`, `Include/opcode_ids.h`), the
`RESUME_OPARG_DEPTH1_MASK` bit (0x8) of its oparg, and `_PyEval_NoToolsForUnwind`. -/
def FastClose (i : InstrPtr) (w : World V X) : Prop :=
  (i.opcode = 128 ∨ i.opcode = 200 ∨ i.opcode = 201 ∨ i.opcode = 244) ∧
    i.oparg &&& 8 ≠ 0 ∧ w.noUnwindTools = true

/-- The end of `gen_close` (:517-540) on what the frame did with the thrown exception: a
returned value is the result, a yield is the "ignored GeneratorExit" `RuntimeError` with
the frame left suspended, `GeneratorExit` (or a subclass) is swallowed, and any other
exception propagates. -/
def closeOutcome (kind : GenKind) (w' : World V X) (r : Ref) :
    ResumeOutcome V → World V X × Ret V
  | .returned v => (w'.setState r .cleared, .ok v)
  | .yielded oparg _ nxt top =>
    (afterYield w' r oparg nxt top, .err (some (Exc.runtimeError
      (match kind with
       | .gen => "generator ignored GeneratorExit"
       | .coro => "coroutine ignored GeneratorExit"
       | .asyncGen => "async generator ignored GeneratorExit"))))
  | .raised e =>
    if e.kind = .generatorExit then (w'.setState r .cleared, .ok .none)
    else (w'.setState r .cleared, .err (some e))

/-- `PyErr_GivenExceptionMatches(typ, PyExc_GeneratorExit)` (:656): a `GeneratorExit` class or
instance, subclasses included. -/
def IsGenExit (typ : Obj V) : Prop :=
  (∃ cl, typ = .excClass .generatorExit cl) ∨ (∃ cl m v, typ = .excInst .generatorExit cl m v)

end Spec

section Lemmas
variable {V X : Type}

theorem World.set_set (w : World V X) (r : Ref) (g g' : GenObj V) :
    (w.set r g).set r g' = w.set r g' := by
  cases w
  simp only [World.set, World.mk.injEq, and_true]
  funext q
  by_cases hq : q = r <;> simp [hq]

theorem suspendFrame_eq (w : World V X) (r : Ref) (oparg : Bool) (nxt : InstrPtr) (top : Obj V) :
    suspendFrame w r oparg nxt top = afterYield w r oparg nxt top := by
  cases oparg <;> rfl

theorem genClearFrame_setState (w : World V X) (r : Ref) (s : FrameState) :
    genClearFrame (w.setState r s) r = w.set r { w.get r with state := s, stackTop := .none } := by
  simp [genClearFrame, World.setState, World.set_set]

theorem clearedWorld_eq (w : World V X) (r : Ref) (s : FrameState) :
    genClearFrame ((w.setState r s).setState r .cleared) r = clearedWorld w r := by
  rw [setState_setState, genClearFrame_setState]; rfl

theorem fast_iff (i : InstrPtr) (w : World V X) :
    (i.isResumeDepth1 = true ∧ w.noUnwindTools = true) ↔ FastClose i w := by
  simp only [InstrPtr.isResumeDepth1, InstrPtr.isResume, InstrPtr.depth1, FastClose, RESUME,
    RESUME_CHECK, RESUME_CHECK_JIT, INSTRUMENTED_RESUME, RESUME_OPARG_DEPTH1_MASK,
    Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨?_, h2, h3⟩
    rcases h1 with ((h | h) | h) | h <;> simp [h]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    rcases h1 with h | h | h | h <;> simp [h]

theorem givenMatches_iff (typ : Obj V) : givenMatchesGeneratorExit typ = true ↔ IsGenExit typ := by
  cases typ <;> simp [givenMatchesGeneratorExit, IsGenExit]
  all_goals first
    | (constructor <;> intro h <;> (try subst h) <;> simp_all)
    | skip

theorem genSendEx2_eq (h : Hooks V X) (w w' : World V X) (r : Ref) (arg exc) (o : ResumeOutcome V)
    (hres : h.resume w r (arg.getD .none) exc = (w', o)) :
    genSendEx2 h w r arg exc = finishResume w' r (w.get r).kind arg o := by
  simp [genSendEx2, hres]

end Lemmas

variable {V X : Type}

/-! ## `gen_send_ex2` and `gen_send_ex` -/

/-- `gen_send_ex` (:330-375) and `gen_send_ex2` (:260-325), for every state, argument and frame
outcome. A just-started object refuses a non-None value with the `TypeError` of its type; a
finished coroutine raises "cannot reuse already awaited coroutine", a finished generator
returns `None` to `send` (`PYGEN_RETURN`) and `NULL` with nothing set to `next`; otherwise the
frame runs marked `FRAME_EXECUTING`, with the sent value (or `None`) pushed and no exception,
and a yield is `PYGEN_NEXT` with its value and the frame suspended, a return is `PYGEN_RETURN`
with the value and the frame cleared (except `None` returned to `next` of a generator or
coroutine, which is `NULL` with nothing set, :310-316), and an exception propagates with the
frame cleared. The running case is `gen-already-executing`. -/
def GenSendExOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)),
    ((w.get r).state = .created → isNonNull arg = true →
      genSendEx h w r arg = (w, .err (some (Exc.typeError (cantSendMsg (w.get r).kind))))) ∧
    ((w.get r).state = .cleared →
      genSendEx h w r arg =
        if (w.get r).kind = .coro then
          (w, .err (some (Exc.runtimeError "cannot reuse already awaited coroutine")))
        else if arg.isSome = true then (w, .ret .none)
        else (w, .err none)) ∧
    ((w.get r).state ≠ .executing → (w.get r).state ≠ .cleared →
      ¬ ((w.get r).state = .created ∧ isNonNull arg = true) →
      ∀ w' o, h.resume (w.setState r .executing) r (arg.getD .none) none = (w', o) →
      genSendEx h w r arg =
        match o with
        | .yielded oparg v nxt top => (afterYield w' r oparg nxt top, .next v)
        | .returned v =>
          if v.isNone = true ∧ (w.get r).kind ≠ .asyncGen ∧ arg.isNone = true then
            (w'.setState r .cleared, .err none)
          else (w'.setState r .cleared, .ret v)
        | .raised e => (w'.setState r .cleared, .err (some e)))

theorem genSendExOutcomes_proven : GenSendExOutcomes := by
  intro V X h w r arg
  refine ⟨fun hc hn => by simp [genSendEx, hc, hn], fun hc => ?_, fun he hc hn w' o hres => ?_⟩
  · have hcr : ¬ ((w.get r).state = .created ∧ isNonNull arg = true) := by
      rw [hc]; simp
    exact genSendEx_finished h w r arg (by rw [hc]; decide) hcr
  · have h3 : (w.get r).state.finished = false := by
      cases hs : (w.get r).state <;> simp_all
    rw [genSendEx_live h w r arg hn he h3, genSendEx2_eq h _ w' r arg none o hres]
    cases o <;> simp [finishResume, suspendFrame_eq, clearGenFrame]

/-- `gen_send` (:406-414) through `gen_set_stop_iteration` (:385-399): a `PYGEN_RETURN` of `v`
becomes `StopAsyncIteration` on an async generator and `StopIteration(v)` otherwise, a yield
is the value, and errors pass through, with the world `gen_send_ex` left. -/
def GenSendSetsStopIteration : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (arg : Option (Obj V)),
    genSend h w r arg =
      ((genSendEx h w r arg).1,
       match (genSendEx h w r arg).2 with
       | .next v => .ok v
       | .ret v => .err (some (stopIterationOf (w.get r).kind v))
       | .err e => .err e)

theorem genSendSetsStopIteration_proven : GenSendSetsStopIteration := by
  intro V X h w r arg
  simp only [genSend]
  congr 1
  cases (genSendEx h w r arg).2 with
  | next v => rfl
  | err e => rfl
  | ret v =>
    by_cases hk : (w.get r).kind = .asyncGen
    · simp [sendResultToRet, stopIterationOf, hk, Exc.stopAsyncIteration]
    · cases v <;> simp [sendResultToRet, stopIterationOf, hk, Obj.isNone, Exc.stopIterationNone,
        setStopIterationValue]

/-- `gen_throw_current_exception` (:604-613) on a generator marked `FRAME_EXECUTING`: the frame
runs with `None` pushed and the pending exception `e` thrown, and its yield is the result, its
return goes through `gen_set_stop_iteration`, and its exception propagates. -/
def GenThrowCurrentOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w w' : World V X) (r : Ref) (e : Option (Exc V))
    (o : ResumeOutcome V),
    h.resume w r .none e = (w', o) →
    genThrowCurrent h w r e =
      match o with
      | .yielded oparg v nxt top => (afterYield w' r oparg nxt top, .ok v)
      | .returned v => (w'.setState r .cleared, .err (some (stopIterationOf (w.get r).kind v)))
      | .raised e' => (w'.setState r .cleared, .err (some e'))

theorem genThrowCurrentOutcomes_proven : GenThrowCurrentOutcomes := by
  intro V X h w w' r e o hres
  have h2 := genSendEx2_eq h w w' r (some .none) e o hres
  simp only [genThrowCurrent, h2]
  cases o with
  | yielded oparg v nxt top => simp [finishResume, suspendFrame_eq, sendResultToRet]
  | raised e' => simp [finishResume, clearGenFrame, sendResultToRet]
  | returned v =>
    by_cases hk : (w.get r).kind = .asyncGen
    · simp [finishResume, clearGenFrame, sendResultToRet, stopIterationOf, hk, Option.isNone,
        Exc.stopAsyncIteration]
    · cases v <;> simp [finishResume, clearGenFrame, sendResultToRet, stopIterationOf, hk,
        Option.isNone, Obj.isNone, Exc.stopIterationNone, setStopIterationValue]

/-! ## `gen_close`, `gen_close_iter`, `is_resume` -/

/-- `gen_close` (:464-541) for every state and frame outcome. A just-created object is cleared
and gives `None`, a finished one gives `None`, a running one the already-executing
`ValueError`. A suspended one is marked `FRAME_EXECUTING`; one in a `yield from` first closes
its sub-iterator (`gen_close_iter`). Then at a depth-1 `RESUME` (the four opcodes of
`is_resume`, mask 0x8) with no unwind tools it is cleared without running and gives `None`;
otherwise `GeneratorExit` (or the sub-iterator's error) is thrown in and `closeOutcome`
reads the result: a returned value, the "ignored GeneratorExit" `RuntimeError` on a yield,
`None` for `GeneratorExit`, and any other exception. -/
def GenCloseOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref),
    ((w.get r).state = .created → genCloseF h (n + 1) w r = (clearedWorld w r, .ok .none)) ∧
    ((w.get r).state = .cleared → genCloseF h (n + 1) w r = (w, .ok .none)) ∧
    ((w.get r).state = .executing →
      genCloseF h (n + 1) w r = (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))) ∧
    ((w.get r).state = .suspended →
      (FastClose (w.get r).instr w → genCloseF h (n + 1) w r = (clearedWorld w r, .ok .none)) ∧
      (¬ FastClose (w.get r).instr w → ∀ w' o,
        h.resume (w.setState r .executing) r .none (some Exc.generatorExit) = (w', o) →
        genCloseF h (n + 1) w r = closeOutcome (w.get r).kind w' r o)) ∧
    ((w.get r).state = .suspendedYieldFrom → ∀ wc st,
      genCloseIter h (genCloseF h n) (w.setState r .executing) (w.get r).stackTop = (wc, st) →
      (FastClose (wc.get r).instr wc → genCloseF h (n + 1) w r = (clearedWorld wc r, .ok .none)) ∧
      (¬ FastClose (wc.get r).instr wc → ∀ w' o,
        h.resume wc r .none (match st with | .ok => some Exc.generatorExit | .fail e => e) = (w', o) →
        genCloseF h (n + 1) w r = closeOutcome (wc.get r).kind w' r o))

theorem genCloseFinish_eq (h : Hooks V X) (w w' : World V X) (r : Ref) (p : Option (Exc V))
    (o : ResumeOutcome V) (hres : h.resume w r .none p = (w', o)) :
    genCloseFinish h w r p = closeOutcome (w.get r).kind w' r o := by
  have h2 := genSendEx2_eq h w w' r (some .none) p o hres
  simp only [genCloseFinish, h2]
  cases o with
  | yielded oparg v nxt top =>
    cases hk : (w.get r).kind <;> simp [finishResume, suspendFrame_eq, closeOutcome, ignoredExitMsg]
  | returned v => simp [finishResume, clearGenFrame, closeOutcome, Option.isNone]
  | raised e =>
    by_cases hg : e.kind = .generatorExit
    · simp [finishResume, clearGenFrame, closeOutcome, Exc.isGeneratorExit, hg]
    · simp [finishResume, clearGenFrame, closeOutcome, Exc.isGeneratorExit, hg]

theorem stackTop_setState (w : World V X) (r q : Ref) (s : FrameState) :
    ((w.setState r s).get q).stackTop = (w.get q).stackTop := by
  by_cases hq : q = r
  · subst hq; simp [World.setState]
  · simp [World.setState, hq]

theorem genCloseF_live (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref)
    (h1 : (w.get r).state ≠ .created) (h2 : (w.get r).state ≠ .cleared)
    (h3 : (w.get r).state ≠ .executing) :
    genCloseF h (n + 1) w r =
      genCloseBody h (genCloseF h n) (w.setState r .executing) r (w.get r).state := by
  have hf : (w.get r).state.finished = false := by
    cases hs : (w.get r).state <;> simp_all
  simp only [genCloseF]
  rw [if_neg h1, if_neg (by simp [hf]), if_neg h3]

theorem genCloseBody_eq (h : Hooks V X) (close : World V X → Ref → World V X × Ret V)
    (w1 : World V X) (r : Ref) (state : FrameState) (wc : World V X) (st : CStatus V)
    (hp : closeDelegate h close w1 r state = (wc, st)) :
    genCloseBody h close w1 r state =
      if (wc.get r).instr.isResumeDepth1 = true ∧ wc.noUnwindTools = true then
        (genClearFrame (wc.setState r .cleared) r, .ok .none)
      else genCloseFinish h wc r (closePending st) := by
  simp only [genCloseBody, hp]

theorem genCloseOutcomes_proven : GenCloseOutcomes := by
  intro V X h n w r
  refine ⟨fun hs => ?_, fun hs => ?_, fun hs => ?_, fun hs => ⟨fun hf => ?_, fun hf w' o hres => ?_⟩,
    fun hs wc st hcl => ⟨fun hf => ?_, fun hf w' o hres => ?_⟩⟩
  · simp [genCloseF, hs, genClearFrame_setState, clearedWorld]
  · simp [genCloseF, hs]
  · simp [genCloseF, hs]
  · have hp : closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state =
        (w.setState r .executing, .ok) := by simp [closeDelegate, hs]
    rw [genCloseF_live h n w r (by rw [hs]; decide) (by rw [hs]; decide) (by rw [hs]; decide),
      genCloseBody_eq h _ _ r _ _ _ hp,
      if_pos (by rw [instr_setState, noUnwind_setState]; exact (fast_iff _ _).2 hf),
      clearedWorld_eq]
  · have hp : closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state =
        (w.setState r .executing, .ok) := by simp [closeDelegate, hs]
    rw [genCloseF_live h n w r (by rw [hs]; decide) (by rw [hs]; decide) (by rw [hs]; decide),
      genCloseBody_eq h _ _ r _ _ _ hp,
      if_neg (by rw [instr_setState, noUnwind_setState]; exact fun c => hf ((fast_iff _ _).1 c))]
    rw [show closePending (CStatus.ok : CStatus V) = some Exc.generatorExit from rfl,
      genCloseFinish_eq h _ w' r _ o hres, kind_setState]
  · have hp : closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state =
        (wc, st) := by simp only [closeDelegate, hs, if_true, stackTop_setState]; exact hcl
    rw [genCloseF_live h n w r (by rw [hs]; decide) (by rw [hs]; decide) (by rw [hs]; decide),
      genCloseBody_eq h _ _ r _ _ _ hp, if_pos ((fast_iff _ _).2 hf), genClearFrame_setState]
    rfl
  · have hp : closeDelegate h (genCloseF h n) (w.setState r .executing) r (w.get r).state =
        (wc, st) := by simp only [closeDelegate, hs, if_true, stackTop_setState]; exact hcl
    rw [genCloseF_live h n w r (by rw [hs]; decide) (by rw [hs]; decide) (by rw [hs]; decide),
      genCloseBody_eq h _ _ r _ _ _ hp, if_neg (fun c => hf ((fast_iff _ _).1 c))]
    exact genCloseFinish_eq h wc w' r _ o (by cases st <;> exact hres)

/-- `gen_close_iter` (:425-449). An exact generator or coroutine is closed with `close` (the
recursive `gen_close`) and its error is the -1 return. Anything else has its `close` looked up:
a failed lookup is reported as unraisable and ignored, no attribute is success, and otherwise
`close()` is called and its error is the -1 return. -/
def GenCloseIterOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (c : World V X → Ref → World V X × Ret V) (w : World V X)
    (yf : Obj V),
    (∀ sub, yf = .gen sub → (w.get sub).kind ≠ .asyncGen → ∀ w' res, c w sub = (w', res) →
      genCloseIter h c w yf = (w', match res with | .ok _ => .ok | .err e => .fail e)) ∧
    ((∀ sub, yf = .gen sub → (w.get sub).kind = .asyncGen) → ∀ w1 a, h.getClose w yf = (w1, a) →
      (a = .ok none → genCloseIter h c w yf = (w1, .ok)) ∧
      (∀ e, a = .error e →
        genCloseIter h c w yf = (h.unraisable w1 "Exception ignored while closing generator" e, .ok)) ∧
      (∀ m w2 res, a = .ok (some m) → h.callNoArgs w1 m = (w2, res) →
        genCloseIter h c w yf = (w2, match res with | .ok _ => .ok | .err e => .fail e)))

theorem genCloseIterOutcomes_proven : GenCloseIterOutcomes := by
  intro V X h c w yf
  refine ⟨fun sub hy hk w' res hc => ?_, fun hy w1 a ha => ⟨fun h0 => ?_, fun e he => ?_,
    fun m w2 res hm hcall => ?_⟩⟩
  · subst hy
    simp only [genCloseIter, genOrCoro?, if_neg hk, hc]
    cases res <;> rfl
  all_goals
    have hg : genOrCoro? w yf = none := by
      cases yf <;> simp [genOrCoro?]
      next sub => simp [hy sub rfl]
    simp only [genCloseIter, hg, genCloseIterForeign, ha]
  · subst h0; rfl
  · subst he; rfl
  · subst hm; simp only [closeMeth, hcall]; cases res <;> rfl

/-- `gen_set_exception` (:546-601). The traceback is checked first: anything but absent,
`None` or a traceback object is the `TypeError` whatever `typ` is. Then a class is normalized
with its value (`PyErr_NormalizeException`), an instance with a value other than `None` is the
"instance exception may not have a separate value" `TypeError`, an instance with none is
raised as it is, and anything else is the "exceptions must be classes or instances" `TypeError`
naming its type (`%s` of `tp_name`, untruncated). Tracebacks themselves are not modelled. -/
def GenSetExceptionCases : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (typ : Obj V) (val : Option (Obj V)),
    (∀ t : Obj V, (match t with | .none | .traceback => False | _ => True) →
      genSetException h typ val (some t) =
        .error (Exc.typeError "throw() third argument must be a traceback object")) ∧
    (∀ tb, (tb = none ∨ tb = some .none ∨ tb = some .traceback) →
      (∀ k cl, typ = .excClass k cl → genSetException h typ val tb = .ok (h.normalize typ val)) ∧
      (∀ k cl m v, typ = .excInst k cl m v → (val = none ∨ val = some .none) →
        genSetException h typ val tb = .ok ⟨k, cl, m, v⟩) ∧
      (∀ k cl m v u, typ = .excInst k cl m v → val = some u → u.isNone = false →
        genSetException h typ val tb =
          .error (Exc.typeError "instance exception may not have a separate value")) ∧
      ((match typ with | .excClass .. | .excInst .. => False | _ => True) →
        genSetException h typ val tb = .error (Exc.typeError
          ("exceptions must be classes or instances deriving from BaseException, not "
            ++ h.typeName typ))))

theorem genSetExceptionCases_proven : GenSetExceptionCases := by
  intro V X h typ val
  refine ⟨fun t ht => ?_, fun tb htb => ?_⟩
  · cases t <;> simp_all [genSetException, badTraceback]
  · have hb : badTraceback tb = false := by
      rcases htb with h0 | h0 | h0 <;> subst h0 <;> rfl
    refine ⟨fun k cl ht => ?_, fun k cl m v ht hv => ?_, fun k cl m v u ht hv hu => ?_, fun ht => ?_⟩
    · subst ht; simp [genSetException, hb]
    · subst ht; rcases hv with hv | hv <;> subst hv <;> simp [genSetException, hb, isNonNull]
    · subst ht; subst hv
      cases u <;> simp_all [genSetException, isNonNull, Obj.isNone]
    · cases typ <;> simp_all [genSetException]

/-! ## `_gen_throw` and `gen_throw` -/

/-- `_gen_throw` (:625-726) for every state and every outcome of the Python code it runs.
States first: running is the already-executing `ValueError`; finished is the cannot-reuse
`RuntimeError` for a coroutine and otherwise whatever `gen_set_exception` sets, with nothing
run. Otherwise the generator is `FRAME_EXECUTING` from :649 on. Not delegating (`throw_here`,
:719-725): a `gen_set_exception` failure writes the old state back and raises, a success is
thrown in by `gen_throw_current_exception`. Delegating, with `GeneratorExit` and
`close_on_genexit` (:656-669): the sub-iterator is closed (`gen_close_iter`), its error is
thrown into the frame, and otherwise `throw_here`. Delegating otherwise: an exact generator or
coroutine gets `_gen_throw` recursively (:672-689); anything else has `throw` looked up (a
failed lookup writes the state back and raises, no attribute is `throw_here`) and called with
`(typ, val, tb)`; a value from the sub-iterator writes the state back and is the result
(:715-716), an error is thrown into the frame (:712-714). -/
def GenThrowFOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (n : Nat) (w : World V X) (r : Ref) (c : Bool) (typ : Obj V)
    (val tb : Option (Obj V)),
    ((w.get r).state = .executing → genThrowF h (n + 1) w r c typ val tb =
      (w, .err (some (Exc.valueError (alreadyExecutingMsg (w.get r).kind))))) ∧
    ((w.get r).state = .cleared → genThrowF h (n + 1) w r c typ val tb =
      (w, .err (some (if (w.get r).kind = .coro then
          Exc.runtimeError "cannot reuse already awaited coroutine"
        else match genSetException h typ val tb with | .ok e | .error e => e)))) ∧
    (((w.get r).state = .created ∨ (w.get r).state = .suspended) →
      (∀ e, genSetException h typ val tb = .error e →
        genThrowF h (n + 1) w r c typ val tb = (w, .err (some e))) ∧
      (∀ e, genSetException h typ val tb = .ok e →
        genThrowF h (n + 1) w r c typ val tb = genThrowCurrent h (w.setState r .executing) r (some e))) ∧
    ((w.get r).state = .suspendedYieldFrom →
      (IsGenExit typ → c = true → ∀ wc st,
        genCloseIter h (genCloseF h n) (w.setState r .executing) (w.get r).stackTop = (wc, st) →
        (∀ e, st = .fail e → genThrowF h (n + 1) w r c typ val tb = genThrowCurrent h wc r e) ∧
        (st = .ok → ∀ e, genSetException h typ val tb = .error e →
          genThrowF h (n + 1) w r c typ val tb = (wc.setState r .suspendedYieldFrom, .err (some e))) ∧
        (st = .ok → ∀ e, genSetException h typ val tb = .ok e →
          genThrowF h (n + 1) w r c typ val tb = genThrowCurrent h wc r (some e))) ∧
      (¬ (IsGenExit typ ∧ c = true) →
        (∀ sub, (w.get r).stackTop = .gen sub → (w.get sub).kind ≠ .asyncGen → ∀ w' res,
          genThrowF h n (w.setState r .executing) sub c typ val tb = (w', res) →
          genThrowF h (n + 1) w r c typ val tb =
            match res with
            | .ok v => (w'.setState r .suspendedYieldFrom, .ok v)
            | .err e => genThrowCurrent h w' r e) ∧
        ((∀ sub, (w.get r).stackTop = .gen sub → (w.get sub).kind = .asyncGen) → ∀ wq q,
          h.getThrow (w.setState r .executing) (w.get r).stackTop = (wq, q) →
          (∀ e, q = .error e →
            genThrowF h (n + 1) w r c typ val tb = (wq.setState r .suspendedYieldFrom, .err (some e))) ∧
          (q = .ok none → ∀ e, genSetException h typ val tb = .error e →
            genThrowF h (n + 1) w r c typ val tb = (wq.setState r .suspendedYieldFrom, .err (some e))) ∧
          (q = .ok none → ∀ e, genSetException h typ val tb = .ok e →
            genThrowF h (n + 1) w r c typ val tb = genThrowCurrent h wq r (some e)) ∧
          (∀ m w' res, q = .ok (some m) → h.callThrow wq m typ val tb = (w', res) →
            genThrowF h (n + 1) w r c typ val tb =
              match res with
              | .ok v => (w'.setState r .suspendedYieldFrom, .ok v)
              | .err e => genThrowCurrent h w' r e))))

theorem genThrowFOutcomes_proven : GenThrowFOutcomes := by
  intro V X h n w r c typ val tb
  refine ⟨fun hs => by simp [genThrowF, hs], fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · by_cases hk : (w.get r).kind = .coro
    · simp [genThrowF, hs, hk]
    · simp only [genThrowF, hs, hk]
      cases genSetException h typ val tb <;> simp
  · have hx : (w.get r).state ≠ .executing := by rcases hs with hs | hs <;> rw [hs] <;> decide
    have hf : (w.get r).state.finished = false := by rcases hs with hs | hs <;> rw [hs] <;> rfl
    have hy : (w.get r).state ≠ .suspendedYieldFrom := by
      rcases hs with hs | hs <;> rw [hs] <;> decide
    refine ⟨fun e he => ?_, fun e he => ?_⟩
    · simp only [genThrowF, if_neg hx, hf, Bool.false_eq_true, if_false, state_setState, if_neg hy,
        throwHere, he, setState_setState, setState_self]
    · simp only [genThrowF, if_neg hx, hf, Bool.false_eq_true, if_false, state_setState, if_neg hy,
        throwHere, he]
  · have hx : (w.get r).state ≠ .executing := by rw [hs]; decide
    have hf : (w.get r).state.finished = false := by rw [hs]; rfl
    refine ⟨fun hg hc wc st hcl => ⟨fun e he => ?_, fun hok e he => ?_, fun hok e he => ?_⟩,
      fun hng => ⟨fun sub hsub hk w' res hrec => ?_, fun hna wq q hq => ⟨fun e he => ?_,
        fun h0 e he => ?_, fun h0 e he => ?_, fun m w' res hm hcall => ?_⟩⟩⟩
    · have hg' := (givenMatches_iff typ).2 hg
      simp only [genThrowF, hs, reduceCtorEq, finished_yf, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
        stackTop_setState, hg', hc, and_self, hcl, he]
    · have hg' := (givenMatches_iff typ).2 hg
      subst hok
      simp only [genThrowF, hs, reduceCtorEq, finished_yf, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
        stackTop_setState, hg', hc, and_self, hcl, throwHere, he]
    · have hg' := (givenMatches_iff typ).2 hg
      subst hok
      simp only [genThrowF, hs, reduceCtorEq, finished_yf, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
        stackTop_setState, hg', hc, and_self, hcl, throwHere, he]
    · have hg' : ¬ (givenMatchesGeneratorExit typ = true ∧ c = true) :=
        fun ⟨a, b⟩ => hng ⟨(givenMatches_iff typ).1 a, b⟩
      have hsub' : genOrCoro? (w.setState r .executing) (w.get r).stackTop = some sub := by
        rw [hsub]; simp [genOrCoro?, kind_setState, hk]
      simp only [genThrowF, hs, reduceCtorEq, finished_yf, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
        stackTop_setState, if_neg hg', hsub', hrec]
      cases res <;> simp [afterDelegate]
    all_goals
      have hg' : ¬ (givenMatchesGeneratorExit typ = true ∧ c = true) :=
        fun ⟨a, b⟩ => hng ⟨(givenMatches_iff typ).1 a, b⟩
      have hnone : genOrCoro? (w.setState r .executing) (w.get r).stackTop = none := by
        cases hst : (w.get r).stackTop <;> simp [genOrCoro?]
        next sub => simp [kind_setState, hna sub hst]
      simp only [genThrowF, hs, reduceCtorEq, finished_yf, Bool.false_eq_true, if_false, if_true, ite_false, ite_true,
        stackTop_setState, if_neg hg', hnone, hq]
    · subst he; rfl
    · subst h0; simp only [throwHere, he, setState_setState]
    · subst h0; simp only [throwHere, he]
    · subst hm; simp only [hcall]; cases res <;> simp [afterDelegate]

/-- `gen_throw` (:730-757): `_PyArg_CheckPositional("throw", nargs, 1, 3)` first, with its
exact messages and nothing else run; for two or three arguments the `DeprecationWarning`,
whose failure (warnings as errors) is the result; then `_gen_throw` with `close_on_genexit`
set and the arguments in the `(typ, val, tb)` slots. -/
def GenThrowArgs : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref),
    genThrow h fuel w r [] = (w, .err (some (Exc.typeError "throw expected at least 1 argument, got 0"))) ∧
    (∀ args : List (Obj V), args.length > 3 → genThrow h fuel w r args =
      (w, .err (some (Exc.typeError s!"throw expected at most 3 arguments, got {args.length}")))) ∧
    (∀ typ, genThrow h fuel w r [typ] = genThrowF h fuel w r true typ none none) ∧
    (∀ typ val w1 e, h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead." = (w1, some e) →
      genThrow h fuel w r [typ, val] = (w1, .err (some e)) ∧
      ∀ tb, genThrow h fuel w r [typ, val, tb] = (w1, .err (some e))) ∧
    (∀ typ val w1, h.warn w "the (type, exc, tb) signature of throw() is deprecated, use the single-arg signature instead." = (w1, none) →
      genThrow h fuel w r [typ, val] = genThrowF h fuel w1 r true typ (some val) none ∧
      ∀ tb, genThrow h fuel w r [typ, val, tb] = genThrowF h fuel w1 r true typ (some val) (some tb))

theorem genThrowArgs_proven : GenThrowArgs := by
  intro V X h fuel w r
  refine ⟨by simp [genThrow, checkPositional]; rfl, fun args ha => ?_, fun typ => ?_,
    fun typ val w1 e hw => ⟨?_, fun tb => ?_⟩, fun typ val w1 hw => ⟨?_, fun tb => ?_⟩⟩
  · have : ¬ args.length < 1 := by omega
    have hm : toString "throw" ++ toString " expected at most " ++ Nat.repr 3 ++
        toString " argument" ++ toString "s" ++ toString ", got " =
        toString "throw expected at most 3 arguments, got " := by rfl
    simp [genThrow, checkPositional, ha, this, hm]
  · simp [genThrow, checkPositional, unpackThrowArgs]
  all_goals simp [genThrow, checkPositional, unpackThrowArgs, hw]

/-! ## `gen_finalize` -/

/-- `gen_finalize` (:108-164). A finished object is left alone. An async generator with a
finalizer and `ag_closed` clear has the finalizer called with it, a failure reported as
"Exception ignored while finalizing generator", and nothing else. Otherwise a `CO_COROUTINE`
code object still `FRAME_CREATED` gets the never-awaited `RuntimeWarning`, and everything else
is closed with `gen_close`, a failure with an exception reported as "Exception ignored while
closing generator". -/
def GenFinalizeOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref),
    ((w.get r).state = .cleared → genFinalize h fuel w r = w) ∧
    ((w.get r).state ≠ .cleared → (w.get r).kind = .asyncGen → (w.get r).agClosed = false →
      ∀ f, (w.get r).finalizer = some f → ∀ w1 res, h.callOneArg w f (.gen r) = (w1, res) →
      genFinalize h fuel w r =
        match res with
        | .err (some e) => h.unraisable w1 "Exception ignored while finalizing generator" e
        | _ => w1) ∧
    ((w.get r).state ≠ .cleared →
      ¬ ((w.get r).kind = .asyncGen ∧ (w.get r).agClosed = false ∧ (w.get r).finalizer.isSome) →
      ((w.get r).code.flags &&& 0x80 ≠ 0 → (w.get r).state = .created →
        genFinalize h fuel w r = h.warnUnawaitedCoro w r) ∧
      (¬ ((w.get r).code.flags &&& 0x80 ≠ 0 ∧ (w.get r).state = .created) →
        ∀ w1 res, genCloseF h fuel w r = (w1, res) →
        genFinalize h fuel w r =
          match res with
          | .err (some e) => h.unraisable w1 "Exception ignored while closing generator" e
          | _ => w1))

theorem genFinalizeOutcomes_proven : GenFinalizeOutcomes := by
  intro V X h fuel w r
  refine ⟨fun hs => by simp [genFinalize, hs], fun hs hk hc f hf w1 res hcall => ?_,
    fun hs hn => ⟨fun hco hcr => ?_, fun hnc w1 res hcl => ?_⟩⟩
  · have hfin : (w.get r).state.finished = false := by
      cases h' : (w.get r).state <;> simp_all
    simp only [genFinalize, hfin, Bool.false_eq_true, if_false, hk, hc, and_self, if_true, hf, hcall]
    cases res with
    | ok v => rfl
    | err e => cases e <;> rfl
  all_goals
    have hfin : (w.get r).state.finished = false := by
      cases h' : (w.get r).state <;> simp_all
    have hv : (if (w.get r).kind = .asyncGen ∧ (w.get r).agClosed = false then (w.get r).finalizer
        else none) = none := by
      split
      · next hh => cases hf : (w.get r).finalizer <;> simp_all
      · rfl
  · simp only [genFinalize, hfin, Bool.false_eq_true, if_false, hv, Code.hasFlag, CO_COROUTINE]
    have hz : ((w.get r).code.flags &&& 128 != 0) = true ∧ (w.get r).state = .created :=
      ⟨by simpa using hco, hcr⟩
    simp only [hz, and_self, ite_true]
  · simp only [genFinalize, hfin, Bool.false_eq_true, if_false, hv, Code.hasFlag, CO_COROUTINE]
    have hz : ¬ (((w.get r).code.flags &&& 128 != 0) = true ∧ (w.get r).state = .created) :=
      fun ⟨a, b⟩ => hnc ⟨by simpa using a, b⟩
    simp only [hz, ite_false, hcl]
    cases res with
    | ok v => rfl
    | err e => cases e <;> rfl

/-! ## `gen_set_name`, `gen_set_qualname` -/

/-- `gen_set_name` (:845-861) and `gen_set_qualname` (:872-888): deletion or a value that is
not a `str` is the `TypeError` with the exact message and changes nothing; a `str` is stored
as it is and only that attribute changes. -/
def GenNameSetterMessages : Prop :=
  ∀ (V X : Type) (w : World V X) (r : Ref),
    genSetName w r none = (w, .fail (some (Exc.typeError "__name__ must be set to a string object"))) ∧
    genSetQualname w r none =
      (w, .fail (some (Exc.typeError "__qualname__ must be set to a string object"))) ∧
    (∀ v : Obj V, (∀ s, v ≠ .str s) →
      genSetName w r (some v) = (w, .fail (some (Exc.typeError "__name__ must be set to a string object"))) ∧
      genSetQualname w r (some v) =
        (w, .fail (some (Exc.typeError "__qualname__ must be set to a string object")))) ∧
    (∀ s, genSetName w r (some (.str s)) = (w.set r { w.get r with name := .str s }, .ok) ∧
      genSetQualname w r (some (.str s)) = (w.set r { w.get r with qualname := .str s }, .ok))

theorem genNameSetterMessages_proven : GenNameSetterMessages := by
  intro V X w r
  refine ⟨rfl, rfl, fun v hv => ?_, fun s => ⟨rfl, rfl⟩⟩
  cases v <;> simp_all [genSetName, genSetQualname]

/-! ## `gen_is_coroutine` and `_PyCoro_GetAwaitableIter` -/

/-- A coroutine (`PyCoro_CheckExact`) or a generator whose code has `CO_ITERABLE_COROUTINE`
(0x100), `gen_is_coroutine` (:1226-1235): an async generator with the flag is not one. -/
def CoroLike (w : World V X) (o : Obj V) : Prop :=
  ∃ r, o = .gen r ∧ ((w.get r).kind = .coro ∨
    ((w.get r).kind = .gen ∧ (w.get r).code.flags &&& 0x100 ≠ 0))

/-- `gen_is_coroutine` (:1226-1235) and `_PyCoro_GetAwaitableIter` (:1246-1284). A coroutine or
`types.coroutine` generator is returned as it is. Otherwise a type with no `am_await` is the
"'%.100s' object can't be awaited" `TypeError` (`tp_name`, cut to 100 bytes), a raising
`__await__` propagates, and its result is refused if it is coroutine-like ("%T.__await__()
must return an iterator, not coroutine") or not an iterator ("... not %T"), with `%T` the fully
qualified type name; an iterator is the result. -/
def AwaitableIterOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (o : Obj V),
    (genIsCoroutine w o = true ↔
      ∃ r, o = .gen r ∧ (w.get r).kind = .gen ∧ (w.get r).code.flags &&& 0x100 ≠ 0) ∧
    (CoroLike w o → pyCoroGetAwaitableIter h w o = (w, .ok o)) ∧
    (¬ CoroLike w o →
      (h.amAwait w o = none → pyCoroGetAwaitableIter h w o =
        (w, .err (some (Exc.typeError
          ("'" ++ String.ofList (cutUtf8 100 (h.typeName o).toList) ++ "' object can't be awaited"))))) ∧
      (∀ w1 e, h.amAwait w o = some (w1, .err e) → pyCoroGetAwaitableIter h w o = (w1, .err e)) ∧
      (∀ w1 res, h.amAwait w o = some (w1, .ok res) →
        (CoroLike w1 res → pyCoroGetAwaitableIter h w o = (w1, .err (some (Exc.typeError
          (h.typeFqName o ++ ".__await__() must return an iterator, not coroutine"))))) ∧
        (¬ CoroLike w1 res → h.isIter res = false → pyCoroGetAwaitableIter h w o =
          (w1, .err (some (Exc.typeError
            (h.typeFqName o ++ ".__await__() must return an iterator, not " ++ h.typeFqName res))))) ∧
        (¬ CoroLike w1 res → h.isIter res = true → pyCoroGetAwaitableIter h w o = (w1, .ok res))))

theorem coroLike_iff (w : World V X) (o : Obj V) :
    (isCoro w o = true ∨ genIsCoroutine w o = true) ↔ CoroLike w o := by
  cases o <;> simp [isCoro, genIsCoroutine, CoroLike, Code.hasFlag, CO_ITERABLE_COROUTINE]

theorem awaitableIterOutcomes_proven : AwaitableIterOutcomes := by
  intro V X h w o
  refine ⟨?_, fun hc => ?_, fun hc => ⟨fun ha => ?_, fun w1 e ha => ?_, fun w1 res ha =>
    ⟨fun hr => ?_, fun hr hi => ?_, fun hr hi => ?_⟩⟩⟩
  · cases o <;> simp [genIsCoroutine, Code.hasFlag, CO_ITERABLE_COROUTINE]
  · simp [pyCoroGetAwaitableIter, (coroLike_iff w o).2 hc]
  all_goals have hc' : ¬ (isCoro w o = true ∨ genIsCoroutine w o = true) :=
    fun x => hc ((coroLike_iff w o).1 x)
  · simp only [pyCoroGetAwaitableIter, if_neg hc', ha, trunc100]
  · simp only [pyCoroGetAwaitableIter, if_neg hc', ha]
  · simp only [pyCoroGetAwaitableIter, if_neg hc', ha, if_pos ((coroLike_iff w1 res).2 hr)]
  · have hr' : ¬ (isCoro w1 res = true ∨ genIsCoroutine w1 res = true) :=
      fun x => hr ((coroLike_iff w1 res).1 x)
    simp only [pyCoroGetAwaitableIter, if_neg hc', ha, if_neg hr', hi, if_true]
  · have hr' : ¬ (isCoro w1 res = true ∨ genIsCoroutine w1 res = true) :=
      fun x => hr ((coroLike_iff w1 res).1 x)
    simp only [pyCoroGetAwaitableIter, if_neg hc', ha, if_neg hr', hi]
    rfl

end PyLean.Bytecode.GenObj
