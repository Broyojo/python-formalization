import PyLean.Bytecode.GenObj.AsyncProps
import PyLean.Bytecode.GenObj.Script

/-!
# Delegation depth, `throw`, getters, setters, construction
-/

namespace PyLean.Bytecode.GenObj

/-! ## The recursion of `gen_close` and `_gen_throw` -/

/-- From `r` on, every generator delegates to the next one. -/
def ChainFrom (w : World Unit Unit) (r : Nat) : Prop :=
  ∀ q : Nat, r ≤ q → (w.get q).kind = .gen ∧ (w.get q).state = .suspendedYieldFrom ∧
    (w.get q).stackTop = .gen (q + 1)

theorem ChainFrom.setState {w : World Unit Unit} {r : Nat} (hc : ChainFrom w r) (s) :
    ChainFrom (w.setState r s) (r + 1) := by
  intro q hq
  have hne : q ≠ r := by omega
  rw [get_setState_ne _ _ hne]
  exact hc q (by omega)

/-- The frame of `noopHooks` re-raises what is thrown into it. -/
theorem noop_throw (w : World Unit Unit) (r : Ref) (hs : (w.get r).state = .suspendedYieldFrom)
    (e : Exc Unit) (c : Bool) :
    genSendEx noopHooks w r (some .none) true (some e) c =
      (clearGenFrame (w.setState r .executing) r, .err (some e)) := by
  have hnc : ¬ ((w.get r).state = .created ∧ isNonNull (some Obj.none : Option (Obj Unit)) = true) := by
    simp [isNonNull]
  simp only [genSendEx]
  rw [genSendEx2_live noopHooks w r (some .none) true (some e) c hnc (by simp [hs]) (by simp [hs])]
  rfl

/-- The `yield from` chain the recursion walks. -/
def chainWorld : World Unit Unit :=
  { gens := fun i => { kind := .gen, state := .suspendedYieldFrom, stackTop := .gen (i + 1) }
    asends := fun _ => {}
    athrows := fun _ => {}
    noUnwindTools := false
    ext := () }

theorem close_chain (K : Nat) : ∀ (w : World Unit Unit) (r : Ref),
    ChainFrom w r → w.noUnwindTools = false →
    (genCloseF noopHooks K w r).2 = .err (some Exc.fuel) ∧
      (genCloseF noopHooks K w r).1.noUnwindTools = false := by
  induction K with
  | zero => intro w r _ hn; exact ⟨rfl, hn⟩
  | succ K ih =>
    intro w r hc hn
    obtain ⟨hk, hs, ht⟩ := hc r (Nat.le_refl r)
    have hsub := hc.setState FrameState.executing
    obtain ⟨hk1, -, -⟩ := hsub (r + 1) (Nat.le_refl _)
    obtain ⟨i1, i2⟩ := ih (w.setState r .executing) (r + 1) hsub (by simpa using hn)
    have hd : closeDelegate noopHooks (genCloseF noopHooks K) w r =
        (((genCloseF noopHooks K (w.setState r .executing) (r + 1)).1.setState r .suspendedYieldFrom),
          .fail (some Exc.fuel)) := by
      simp [closeDelegate, genYf, hs, ht, delegating, genCloseIter, genOrCoro?, hk1, i1]
    have hbody : genCloseF noopHooks (K + 1) w r =
        genCloseFinish noopHooks
          ((genCloseF noopHooks K (w.setState r .executing) (r + 1)).1.setState r .suspendedYieldFrom)
          r (some Exc.fuel) := by
      simp only [genCloseF, hs, genCloseBody, hd]
      simp [i2, closePending]
    rw [hbody]
    generalize hw : (genCloseF noopHooks K (w.setState r .executing) (r + 1)).1.setState r
      .suspendedYieldFrom = w2
    have hs2 : (w2.get r).state = .suspendedYieldFrom := by rw [← hw]; simp
    have hn2 : w2.noUnwindTools = false := by rw [← hw]; simpa using i2
    have hfin : genCloseFinish noopHooks w2 r (some Exc.fuel) =
        (clearGenFrame (w2.setState r .executing) r, .err (some Exc.fuel)) := by
      simp only [genCloseFinish, noop_throw w2 r hs2]
      simp [sendResultToRet, Exc.fuel, Exc.isGeneratorExit, fetchStopIterationValue,
        Exc.isStopIteration]
    rw [hfin]
    exact ⟨rfl, by simpa [clearGenFrame] using hn2⟩

/-- A fixed amount of C stack is enough to close any generator: there is a `K` such
that `gen_close` never needs more than `K` nested C calls. This is what a stack
guard would give; the source has none. -/
def GenCloseStackBounded : Prop :=
  ∃ K : Nat, ∀ (w : World Unit Unit) (r : Ref),
    (genCloseF noopHooks K w r).2 ≠ .err (some Exc.fuel)

theorem genCloseStackBounded_refuted : ¬ GenCloseStackBounded := by
  rintro ⟨K, hK⟩
  have hc : ChainFrom chainWorld 0 := fun q _ => ⟨rfl, rfl, rfl⟩
  exact hK chainWorld 0 (close_chain K chainWorld 0 hc rfl).1

theorem throw_chain (typ : Obj Unit) (K : Nat) (htyp : givenMatchesGeneratorExit typ = false) :
    ∀ (w : World Unit Unit) (r : Nat), ChainFrom w r →
    (genThrowF noopHooks K w r true typ none none).2 = .err (some Exc.fuel) := by
  induction K with
  | zero => intro w r _; rfl
  | succ K ih =>
    intro w r hc
    obtain ⟨hk, hs, ht⟩ := hc r (Nat.le_refl r)
    have hsub := hc.setState FrameState.executing
    obtain ⟨hk1, -, -⟩ := hc (r + 1) (Nat.le_succ r)
    have i1 := ih (w.setState r .executing) (r + 1) hsub
    have hg : genOrCoro? w (Obj.gen (r + 1)) = some (r + 1) := by simp [genOrCoro?, hk1]
    simp only [genThrowF, genYf, hs, ht, htyp]
    simp only [if_true, hg, delegating]
    generalize hq : genThrowF noopHooks K (w.setState r .executing) (r + 1) true typ none none = q at i1
    obtain ⟨w', res⟩ := q
    simp only at i1
    subst i1
    simp only [hs, afterDelegate]
    generalize hw : w'.setState r .suspendedYieldFrom = w2
    have hs2 : (w2.get r).state = .suspendedYieldFrom := by rw [← hw]; simp
    simp [noop_throw w2 r hs2]

/-- The same for `_gen_throw`, which recurses along the chain in the same way. -/
def GenThrowStackBounded : Prop :=
  ∃ K : Nat, ∀ (w : World Unit Unit) (r : Ref),
    (genThrowF noopHooks K w r true (.excClass .plain "ValueError") none none).2 ≠
      .err (some Exc.fuel)

theorem genThrowStackBounded_refuted : ¬ GenThrowStackBounded := by
  rintro ⟨K, hK⟩
  have hc : ChainFrom chainWorld 0 := fun q _ => ⟨rfl, rfl, rfl⟩
  exact hK chainWorld 0 (throw_chain _ K rfl chainWorld 0 hc)

/-! ## `gen_throw` argument handling -/

/-- `PyExceptionClass_Check(typ)` or `PyExceptionInstance_Check(typ)`. -/
def isThrowable {V : Type} : Obj V → Bool
  | .excClass .. | .excInst .. => true
  | _ => false

/-- A wrong argument count for `throw()` is rejected before anything else. -/
def GenThrowArity : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (args : List (Obj V)),
    (args.length = 0 ∨ args.length > 3) →
    (genThrow h fuel w r args).1 = w ∧ ∃ e, (genThrow h fuel w r args).2 = .err (some e) ∧
      e.cls = "TypeError"

theorem genThrowArity_proven : GenThrowArity := by
  intro V X h fuel w r args ha
  rcases ha with h0 | h3
  · simp [genThrow, checkPositional, h0, Exc.typeError]
  · have : ¬ args.length < 1 := by omega
    simp [genThrow, checkPositional, h3, this, Exc.typeError]

/-- Without a sub-iterator, `throw()` with something that cannot be raised is a
`TypeError` and nothing changes. -/
def GenThrowBadArgUndelegated : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (typ : Obj V),
    genYf (w.get r) = none → isThrowable typ = false →
    genThrow h (fuel + 1) w r [typ] =
      (w, .err (some (Exc.typeError
        ("exceptions must be classes or instances deriving from BaseException, not "
          ++ h.typeName typ))))

theorem genThrowBadArgUndelegated_proven : GenThrowBadArgUndelegated := by
  intro V X h fuel w r typ hy ht
  cases typ <;> simp_all [genThrow, checkPositional, unpackThrowArgs, genThrowF, throwHere,
    isThrowable, badTraceback]

/-- With or without a sub-iterator, `throw()` with something that cannot be raised
leaves the generator's state alone. False: a delegating generator gets the
`TypeError` from its sub-generator raised at its `yield from`. -/
def GenThrowBadArgNoEffect : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (typ : Obj V),
    isThrowable typ = false →
    ((genThrow h (fuel + 1) w r [typ]).1.get r).state = (w.get r).state

/-- Generator 0 delegates to suspended generator 1. -/
def delegatingWorld : World Unit Unit :=
  { gens := fun i => if i = 0 then
      { kind := .gen, state := .suspendedYieldFrom, stackTop := .gen 1 }
      else { kind := .gen, state := .suspended }
    asends := fun _ => {}
    athrows := fun _ => {}
    ext := () }

theorem genThrowBadArgNoEffect_refuted : ¬ GenThrowBadArgNoEffect := by
  intro hp
  have := hp Unit Unit noopHooks 1 delegatingWorld 0 .none rfl
  exact absurd this (by decide)

/-- `gen_throw` with no sub-iterator and a throwable class raises it into the frame:
it is `gen_send_ex` with the normalized exception. -/
def GenThrowNoDelegation : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (c : Bool)
    (k : ExcKind) (cls : String),
    genYf (w.get r) = none →
    genThrowF h (fuel + 1) w r c (.excClass k cls) none none =
      genSendEx h w r (some .none) true (some (h.normalize (.excClass k cls) none)) false

theorem genThrowNoDelegation_proven : GenThrowNoDelegation := by
  intro V X h fuel w r c k cls hy
  simp [genThrowF, hy, throwHere, badTraceback]

/-- `_PyGen_yf` is the stack top exactly while suspended in `yield from`. -/
def GenYfState : Prop :=
  ∀ (V : Type) (g : GenObj V),
    (g.state = .suspendedYieldFrom → genYf g = some g.stackTop ∧
      genGetYieldFrom g = g.stackTop) ∧
    (g.state ≠ .suspendedYieldFrom → genYf g = none ∧ genGetYieldFrom g = .none)

theorem genYfState_proven : GenYfState := by
  intro V g
  constructor <;> intro h <;> simp [genYf, genGetYieldFrom, h]

/-- `gen_close_iter` on a generator or coroutine is `gen_close` on it; on anything
else a failed attribute lookup is reported and ignored, and no `close` attribute
means success. -/
def GenCloseIterForeign : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (c : World V X → Ref → World V X × Ret V) (w : World V X)
    (yf : Obj V),
    genOrCoro? w yf = none →
    (h.getClose w yf).2 = .ok none ∨ (∃ e, (h.getClose w yf).2 = .error e) →
    (genCloseIter h c w yf).2 matches .ok

theorem genCloseIterForeign_proven : GenCloseIterForeign := by
  intro V X h c w yf hg hc
  simp only [genCloseIter, hg, genCloseIterForeign]
  rcases hc with hc | ⟨e, hc⟩ <;> simp [hc, closeMeth]

/-- A `getThrow` that returns `bad` unless `r` is marked `FRAME_EXECUTING`. -/
def guardThrowLookup {V X : Type} (h : Hooks V X) (r : Ref)
    (bad : World V X × Except (Exc V) (Option (Obj V))) : Hooks V X :=
  { h with getThrow := fun w o => if (w.get r).state = .executing then h.getThrow w o else bad }

/-- All Python code `_gen_throw` runs for a sub-iterator runs with the delegating
generator marked `FRAME_EXECUTING`, like every other delegation bracket in the file.
False on 3.14.7: `PyObject_GetOptionalAttr(yf, throw)` at :514 comes before the
bracket at :526-529, so a `throw` property can resume or close the generator, and
:523-531 then links the cleared frame into the thread's frame stack. -/
def GenThrowLookupSeesExecuting : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (bad : World V X × Except (Exc V) (Option (Obj V))) (n : Nat)
    (w : World V X) (r : Ref) (c : Bool) (typ : Obj V) (val tb : Option (Obj V)),
    genThrowF (guardThrowLookup h r bad) n w r c typ val tb = genThrowF h n w r c typ val tb

/-- Generator 0 delegates to an object that is not a generator. -/
def foreignDelegateWorld : World Unit Unit :=
  { gens := fun _ => { kind := .gen, state := .suspendedYieldFrom, stackTop := .other () }
    asends := fun _ => {}
    athrows := fun _ => {}
    ext := () }

theorem genThrowLookupSeesExecuting_refuted : ¬ GenThrowLookupSeesExecuting := by
  intro hp
  have := hp Unit Unit noopHooks (foreignDelegateWorld, .error Exc.fuel) 1 foreignDelegateWorld 0
    false (.excClass .plain "ValueError") none none
  have h2 := congrArg (fun p => match p.2 with
    | Ret.err (some e) => e.kind
    | _ => ExcKind.stopIteration) this
  exact absurd h2 (by decide)

/-! ## PEP 479 -/

/-- `stopiteration_error` leaves no `StopIteration` (in an async generator, no
`StopAsyncIteration`) and passes every other exception through unchanged. This is
what the asserts at :279-281 rely on. -/
def Pep479Conversion : Prop :=
  ∀ (V : Type) (k : GenKind) (e : Exc V),
    (stopIterationError k e).isStopIteration = false ∧
    (k = .asyncGen → (stopIterationError k e).isStopAsyncIteration = false) ∧
    (e.isStopIteration = false → (k = .asyncGen → e.isStopAsyncIteration = false) →
      stopIterationError k e = e)

theorem pep479Conversion_proven : Pep479Conversion := by
  intro V k e
  have kinds : ∀ (b : Bool) (m : String), (Exc.runtimeError m : Exc V).isStopIteration = false ∧
      (Exc.runtimeError m : Exc V).isStopAsyncIteration = false := by
    intro _ m; exact ⟨rfl, rfl⟩
  unfold stopIterationError
  cases hk : k <;> cases hs : e.isStopIteration <;> simp [hs, Exc.runtimeError, Exc.isStopIteration,
    Exc.isStopAsyncIteration] <;> (try (intro h; simp_all [Exc.isStopIteration, Exc.isStopAsyncIteration]))
  all_goals first
    | (split <;> simp_all [Exc.isStopIteration, Exc.isStopAsyncIteration])
    | skip

/-- The asserts at :279-281 applied to the frames the difftest validated: a frame
never ends by raising `StopIteration`. False: an exception thrown into a
`FRAME_CREATED` frame is raised at the first `RESUME`, outside the handler that
performs PEP 479's conversion. -/
def FrameNeverRaisesStopIteration : Prop :=
  ∀ (w : Script.W) (r : Ref) (arg : Script.O) (thrown : Option (Exc Script.SV)) (e : Exc Script.SV),
    (Script.runFrame (Script.hooksAt 1) 1 w r arg thrown).2 = .raised e →
    e.isStopIteration = false

theorem frameNeverRaisesStopIteration_refuted : ¬ FrameNeverRaisesStopIteration := by
  intro hp
  have := hp (Script.initialWorld .gen [] false 0 0) 0 .none (some Exc.stopIterationNone)
    Exc.stopIterationNone rfl
  exact absurd this (by decide)

/-- The same past the first `RESUME`: an exception unwinding off the bottom of a
script frame, the only way `runK` raises, has been through `stopiteration_error`. -/
def StartedFrameNeverRaisesStopIteration : Prop :=
  ∀ (k : GenKind) (e : Exc Script.SV) (w : Script.W) (r : Ref) (fuel : Nat),
    (w.get r).kind = k →
    ∀ e', (Script.runK (Script.hooksAt 1) 1 fuel w r (.unwind e) []).2 = .raised e' →
    e'.isStopIteration = false

theorem startedFrameNeverRaisesStopIteration_proven : StartedFrameNeverRaisesStopIteration := by
  intro k e w r fuel hk e' hr
  cases fuel with
  | zero =>
    simp [Script.runK] at hr
    subst hr; rfl
  | succ s =>
    simp [Script.runK] at hr
    subst hr
    exact (pep479Conversion_proven Script.SV _ e).1

/-! ## Getters and setters -/

/-- `gi_running`, `gi_suspended`, `gi_frame` (and the `cr_`/`ag_` ones) read off the
frame state: running iff `FRAME_EXECUTING`, suspended iff one of the two suspended
states, and no frame iff finished. -/
def GenFlagGetters : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (n : String),
    (genGetRunning (w.get r) = true ↔ (w.get r).state = .executing) ∧
    (genGetSuspended (w.get r) = true ↔
      (w.get r).state = .suspended ∨ (w.get r).state = .suspendedYieldFrom) ∧
    (h.audit w n = none →
      ((w.get r).state.finished = true → genGetFrame h w r n = .ok .none) ∧
      ((w.get r).state.finished = false → genGetFrame h w r n = .ok (h.frameObject w r)))

theorem genFlagGetters_proven : GenFlagGetters := by
  intro V X h w r n
  refine ⟨by simp [genGetRunning], ?_, ?_⟩
  · simp only [genGetSuspended]
    cases (w.get r).state <;> simp [FrameState.isSuspended]
  · intro ha
    constructor <;> intro hf <;> simp [genGetFrame, ha, hf]

/-- `gi_code` does not depend on the frame state: it is still there after the frame
is cleared (:76-79), so the code is the one the object was made with. -/
def GenCodeStable : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref) (n : String) (s : FrameState),
    h.audit (w.setState r s) n = h.audit w n →
    genGetCode h (w.setState r s) r n = genGetCode h w r n

theorem genCodeStable_proven : GenCodeStable := by
  intro V X h w r n s ha
  unfold genGetCode
  rw [ha]
  cases h.audit w n <;> simp [World.setState]

/-- `__name__` and `__qualname__`: anything but a `str`, or deletion, is a `TypeError`
and nothing changes; a `str` reads back, and only that attribute changes. -/
def GenNameSetters : Prop :=
  ∀ (V X : Type) (w : World V X) (r : Ref) (s : String) (v : Option (Obj V)),
    genGetName ((genSetName w r (some (.str s))).1.get r) = .str s ∧
    genGetQualname ((genSetName w r (some (.str s))).1.get r) = genGetQualname (w.get r) ∧
    genGetQualname ((genSetQualname w r (some (.str s))).1.get r) = .str s ∧
    genGetName ((genSetQualname w r (some (.str s))).1.get r) = genGetName (w.get r) ∧
    ((∀ t, v ≠ some (.str t)) →
      (genSetName w r v).1 = w ∧ (genSetQualname w r v).1 = w ∧
      (genSetName w r v).2 matches .fail _ ∧ (genSetQualname w r v).2 matches .fail _)

theorem genNameSetters_proven : GenNameSetters := by
  intro V X w r s v
  refine ⟨by simp [genSetName, genGetName], by simp [genSetName, genGetQualname],
    by simp [genSetQualname, genGetQualname], by simp [genSetQualname, genGetName], ?_⟩
  intro hv
  cases v with
  | none => simp [genSetName, genSetQualname]
  | some o =>
    cases o
    case str t => exact absurd rfl (hv t)
    all_goals simp [genSetName, genSetQualname]

/-- `__sizeof__` depends only on the code object, not on the frame state. -/
def GenSizeofStateless : Prop :=
  ∀ (V X : Type) (base : Nat) (w : World V X) (r : Ref) (s : FrameState),
    genSizeof base ((w.setState r s).get r) = genSizeof base (w.get r) ∧
    genSizeof base (w.get r) =
      base + ((w.get r).code.nlocalsplus + (w.get r).code.stacksize) * 8

theorem genSizeofStateless_proven : GenSizeofStateless := by
  intro V X base w r s
  simp [genSizeof, World.setState]

/-- `repr()` is `<tp_name object qualname at address>` with the type's `tp_name`. -/
def GenReprNames : Prop :=
  ∀ (V : Type) (g : GenObj V) (addr q : String),
    genRepr g addr q =
      "<" ++ (match g.kind with
        | .gen => "generator" | .coro => "coroutine" | .asyncGen => "async_generator")
        ++ " object " ++ q ++ " at " ++ addr ++ ">"

theorem genReprNames_proven : GenReprNames := by
  intro V g addr q
  cases hk : g.kind <;> simp [genRepr, hk, reprPrefix] <;> rfl

/-! ## Construction -/

/-- `make_gen` and `_Py_MakeCoro` pick the type from the code flags, start with a
cleared frame and the function's names, and an async generator starts with its
flags off. -/
def PyMakeCoroKinds : Prop :=
  ∀ (V X : Type) (w : World V X) (code : Code) (n q : Obj V) (g : GenObj V),
    pyMakeCoro w code n q = some g →
    g.state = .cleared ∧ g.name = n ∧ g.qualname = q ∧ g.code.flags = code.flags ∧
    (let cf := code.flags &&& (CO_GENERATOR ||| CO_COROUTINE ||| CO_ASYNC_GENERATOR)
     (cf = CO_GENERATOR → g.kind = .gen) ∧
     (cf = CO_ASYNC_GENERATOR → g.kind = .asyncGen ∧ g.agClosed = false ∧
        g.agHooksInited = false ∧ g.agRunningAsync = false) ∧
     (cf = CO_COROUTINE → g.kind = .coro ∧
       g.origin = if w.originDepth = 0 then none else some (computeCrOrigin w.originDepth w.callStack)))

theorem pyMakeCoroKinds_proven : PyMakeCoroKinds := by
  intro V X w code n q g hm
  simp only [pyMakeCoro] at hm
  split at hm
  · rename_i h1
    simp at hm; subst hm
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    simp only [h1]
    refine ⟨fun _ => rfl, ?_, ?_⟩ <;> intro h <;> exact absurd h (by decide)
  · rename_i h1
    split at hm
    · rename_i h2
      simp at hm; subst hm
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      simp only [h2]
      refine ⟨?_, fun _ => by simp [makeGen], ?_⟩ <;> intro h <;> exact absurd h (by decide)
    · rename_i h2
      split at hm
      · rename_i h3
        split at hm
        · rename_i h4
          simp at hm; subst hm
          refine ⟨rfl, rfl, rfl, rfl, ?_⟩
          simp only [h3, h4]
          refine ⟨?_, ?_, fun _ => ⟨rfl, by simp⟩⟩ <;> intro h <;> exact absurd h (by decide)
        · rename_i h4
          simp at hm; subst hm
          refine ⟨rfl, rfl, rfl, rfl, ?_⟩
          simp only [h3]
          refine ⟨?_, ?_, fun _ => ⟨rfl, by simp [h4]⟩⟩ <;> intro h <;> exact absurd h (by decide)
      · simp at hm

/-- The frame-copying constructors start in `FRAME_CREATED`, and a NULL name or
qualname falls back to the code object's. -/
def GenNewFallbacks : Prop :=
  ∀ (V X : Type) (w : World V X) (code : Code) (n q : Obj V),
    (pyGenNew code : GenObj V).state = .created ∧
    (pyGenNew code : GenObj V).name = .str code.name ∧
    (pyGenNew code : GenObj V).qualname = .str code.qualname ∧
    (pyGenNewWithQualName code (some n) (some q)).name = n ∧
    (pyGenNewWithQualName code (some n) (some q)).qualname = q ∧
    (pyGenNewWithQualName code (some n) none).qualname = .str code.qualname ∧
    (pyCoroNew w code (some n) (some q)).kind = .coro ∧
    (pyCoroNew w code (some n) (some q)).state = .created ∧
    (pyAsyncGenNew code (some n) (some q)).kind = .asyncGen ∧
    (pyAsyncGenNew code (some n) (some q)).state = .created ∧
    (pyAsyncGenNew code (some n) (some q)).agRunningAsync = false ∧
    (w.originDepth = 0 → (pyCoroNew w code (some n) (some q)).origin = none)

theorem genNewFallbacks_proven : GenNewFallbacks := by
  intro V X w code n q
  by_cases hd : w.originDepth = 0 <;>
    simp [pyGenNew, pyGenNewWithQualName, pyCoroNew, pyAsyncGenNew, genNewWithQualname, hd]

section Origin
theorem crOriginCount_eq (d : Nat) : ∀ (l : List (String × Nat × String)) (c : Nat), c ≤ d →
    crOriginCount d l c = min d (c + l.length) := by
  intro l
  induction l with
  | nil => intro c hc; simp [crOriginCount]; omega
  | cons f rest ih =>
    intro c hc
    simp only [crOriginCount]
    split
    · rw [ih (c + 1) (by omega)]
      simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega

theorem crOriginCollect_eq (n : Nat) : ∀ (l : List (String × Nat × String)) (i : Nat),
    crOriginCollect n l i = l.take (n - i) := by
  intro l
  induction l with
  | nil => intro i; simp [crOriginCollect]
  | cons f rest ih =>
    intro i
    simp only [crOriginCollect]
    split
    · rename_i hi
      rw [ih (i + 1)]
      have : n - i = (n - (i + 1)) + 1 := by omega
      rw [this]
      simp
    · rename_i hi
      have : n - i = 0 := by omega
      simp [this]
end Origin

/-- `cr_origin` is the innermost `origin_depth` frames, innermost first, and no more
than the stack has. -/
def CrOriginTake : Prop :=
  ∀ (d : Nat) (frames : List (String × Nat × String)),
    computeCrOrigin d frames = frames.take d

theorem crOriginTake_proven : CrOriginTake := by
  intro d frames
  simp only [computeCrOrigin]
  rw [crOriginCount_eq d frames 0 (Nat.zero_le _), crOriginCollect_eq]
  simp only [Nat.zero_add, Nat.sub_zero]
  by_cases h : d ≤ frames.length
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right (by omega), List.take_length, List.take_of_length_le (by omega)]

/-! ## Coroutines -/

/-- `coro.__await__()` is a view of the coroutine: its methods are the coroutine's. -/
def CoroWrapperPassThrough : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref) (arg : Obj V)
    (args : List (Obj V)),
    coroWrapperIternext h w r = genIternext h w r ∧
    coroWrapperSend h w r arg = genSend h w r (some arg) ∧
    coroWrapperThrow h fuel w r args = genThrow h fuel w r args ∧
    coroWrapperClose h fuel w r = genCloseF h fuel w r

theorem coroWrapperPassThrough_proven : CoroWrapperPassThrough :=
  fun _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- `_PyCoro_GetAwaitableIter` returns a coroutine (or `types.coroutine` generator)
as it is, and otherwise only an iterator that is not a coroutine, so `await` never
gets a second coroutine out of `__await__`. -/
def AwaitableIterResult : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (o v : Obj V),
    (pyCoroGetAwaitableIter h w o).2 = .ok v →
    (isCoro w o = true ∨ genIsCoroutine w o = true) ∧ (pyCoroGetAwaitableIter h w o).1 = w ∨
    (h.isIter v = true ∧ isCoro (pyCoroGetAwaitableIter h w o).1 v = false ∧
      genIsCoroutine (pyCoroGetAwaitableIter h w o).1 v = false)

theorem awaitableIterResult_proven : AwaitableIterResult := by
  intro V X h w o v he
  by_cases hc : isCoro w o = true ∨ genIsCoroutine w o = true
  · left
    exact ⟨hc, by simp [pyCoroGetAwaitableIter, hc]⟩
  · right
    cases ha : h.amAwait w o with
    | none => simp [pyCoroGetAwaitableIter, hc, ha] at he
    | some p =>
      obtain ⟨w1, res⟩ := p
      cases res with
      | err e => simp [pyCoroGetAwaitableIter, hc, ha] at he
      | ok x =>
        simp only [pyCoroGetAwaitableIter, if_neg hc, ha] at he ⊢
        by_cases c1 : isCoro w1 x = true ∨ genIsCoroutine w1 x = true
        · simp [c1] at he
        · by_cases c2 : h.isIter x = false
          · simp [c1, c2] at he
          · rw [if_neg c1, if_neg c2] at he ⊢
            simp at he; subst he
            simp at c1 c2
            exact ⟨c2, c1.1, c1.2⟩

/-! ## `_PyGen_Finalize` -/

/-- `_PyGen_Finalize` does nothing to a finished generator; an unstarted coroutine
only warns and an async generator with a finalizer only gets it called, in both cases
without ever resuming the frame. -/
def GenFinalizeBranches : Prop :=
  ∀ (V X : Type) (h h' : Hooks V X) (fuel : Nat) (w : World V X) (r : Ref),
    ((w.get r).state.finished = true → genFinalize h fuel w r = w) ∧
    ((w.get r).kind = .coro → (w.get r).state = .created →
      (w.get r).code.hasFlag CO_COROUTINE = true →
      genFinalize h fuel w r = h.warnUnawaitedCoro w r) ∧
    ((w.get r).kind = .asyncGen → (w.get r).agClosed = false → (w.get r).finalizer.isSome = true →
      (w.get r).state.finished = false → h'.callOneArg = h.callOneArg → h'.unraisable = h.unraisable →
      genFinalize h' fuel w r = genFinalize h fuel w r)

theorem genFinalizeBranches_proven : GenFinalizeBranches := by
  intro V X h h' fuel w r
  refine ⟨?_, ?_, ?_⟩
  · intro hf; simp [genFinalize, hf]
  · intro hk hs hc
    simp [genFinalize, hk, hs, hc]
  · intro hk hc hfin hf h1 h2
    cases hg : (w.get r).finalizer with
    | none => simp [hg] at hfin
    | some f => simp [genFinalize, hf, hk, hc, hg, h1, h2]

end PyLean.Bytecode.GenObj
