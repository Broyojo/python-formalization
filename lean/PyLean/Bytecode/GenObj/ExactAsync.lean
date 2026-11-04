import PyLean.Bytecode.GenObj.Exact

/-!
# Exact outcomes of the async generator operations, `Objects/genobject.c:1666-2621`

As in `Exact.lean`: each statement gives the result and the world for every state of the
awaitable and the generator and every outcome of the call into the generator (`gen_send`,
`gen_throw`, `_gen_throw`) or the hooks, with that call's arguments and world pinned. The
callees' own outcomes are `Exact.lean`'s statements and `AsyncGenUnwrapValueOutcomes`.
-/

namespace PyLean.Bytecode.GenObj

variable {V X : Type}

section Spec

/-- `async_gen_unwrap_value` (:1912-1938) followed by `close`ing the awaitable when it returned
`NULL`, as every caller does: an async yield (`_PyAsyncGenWrappedValue`) is `StopIteration`
carrying the value with `ag_running_async` cleared; a bare value (an `await` inside the body
suspending) passes through untouched; `NULL` is the pending exception, `StopAsyncIteration` if
none, with `ag_closed` set for `StopAsyncIteration` or `GeneratorExit` and `ag_running_async`
cleared. -/
def awaitTail (close : World V X → World V X) (w' : World V X) (g : Ref) : Ret V → World V X × Ret V
  | .ok (.wrapped v) => (close (w'.setRunning g false), .err (some ⟨.stopIteration, "StopIteration", "", v⟩))
  | .ok v => (w', .ok v)
  | .err none =>
    (close ((w'.setClosed g).setRunning g false),
     .err (some ⟨.stopAsyncIteration, "StopAsyncIteration", "", .none⟩))
  | .err (some x) =>
    (close ((if x.kind = .stopAsyncIteration ∨ x.kind = .generatorExit then w'.setClosed g else w').setRunning g false),
     .err (some x))

/-- `aclose()` mode on a result of the generator (:2356-2361, :2384-2394, :2397-2420,
:2466-2489): an async yield is the "async generator ignored GeneratorExit" `RuntimeError`, a
bare value passes through, and an exception closes the awaitable, with `StopAsyncIteration`
and `GeneratorExit` turned into `StopIteration`; each ending clears `ag_running_async`. -/
def acloseOutcome (w' : World V X) (a g : Ref) : Ret V → World V X × Ret V
  | .ok (.wrapped _) =>
    ((w'.setRunning g false).setAthrowState a .closed,
     .err (some (Exc.runtimeError "async generator ignored GeneratorExit")))
  | .ok v => (w', .ok v)
  | .err e =>
    ((w'.setRunning g false).setAthrowState a .closed,
     .err (match e with
       | some x => if x.kind = .stopAsyncIteration ∨ x.kind = .generatorExit then
           some ⟨.stopIteration, "StopIteration", "", .none⟩ else some x
       | none => none))

/-- `close()` of an `asend`/`athrow` awaitable on the result of throwing `GeneratorExit`
(:2076-2090, :2509-2523): `StopIteration`, `StopAsyncIteration` and `GeneratorExit` are
swallowed, another exception propagates, and a value is the "coroutine ignored GeneratorExit"
`RuntimeError`. -/
def closeAwaitableOutcome : Ret V → Ret V
  | .ok _ => .err (some (Exc.runtimeError "coroutine ignored GeneratorExit"))
  | .err (some x) =>
    if x.kind = .stopIteration ∨ x.kind = .stopAsyncIteration ∨ x.kind = .generatorExit then
      .ok .none else .err (some x)
  | .err none => .err none

end Spec

section Lemmas

theorem setRunning_setRunning (w : World V X) (r : Ref) (b b' : Bool) :
    (w.setRunning r b).setRunning r b' = w.setRunning r b' := by
  simp [World.setRunning, World.set_set]

theorem unwrap_tail (close : World V X → World V X) (w' : World V X) (g : Ref) (res : Ret V) :
    (match asyncGenUnwrapValue w' g res with
     | (u1, .err e) => (close u1, Ret.err e)
     | (u1, .ok v) => (u1, .ok v)) = awaitTail close w' g res := by
  cases res with
  | ok v => cases v <;> simp [asyncGenUnwrapValue, awaitTail, setStopIterationValue]
  | err e =>
    cases e with
    | none => simp [asyncGenUnwrapValue, awaitTail, Exc.stopAsyncIteration, Exc.isStopAsyncIteration]
    | some x =>
      by_cases h1 : x.kind = .stopAsyncIteration
      · simp [asyncGenUnwrapValue, awaitTail, Exc.isStopAsyncIteration, Exc.isGeneratorExit, h1]
      · by_cases h2 : x.kind = .generatorExit
        · simp [asyncGenUnwrapValue, awaitTail, Exc.isStopAsyncIteration, Exc.isGeneratorExit, h2]
        · simp [asyncGenUnwrapValue, awaitTail, Exc.isStopAsyncIteration, Exc.isGeneratorExit, h1, h2]

theorem asendFinish_eq (w' : World V X) (a g : Ref) (res : Ret V) :
    asendFinish w' a g res = awaitTail (fun w => w.setAsendState a .closed) w' g res := by
  rw [← unwrap_tail]; simp only [asendFinish]; cases asyncGenUnwrapValue w' g res with
  | mk u1 u2 => cases u2 <;> rfl

end Lemmas

/-! ## `async_gen_unwrap_value`, `_PyAsyncGenValueWrapperNew` -/

/-- `async_gen_unwrap_value` (:1912-1938) on every input, the async yield built by
`_PyAsyncGenValueWrapperNew` (:2246-2262, what `_INTRINSIC_ASYNC_GEN_WRAP` makes of a
`yield` value) included: `NULL` with no exception becomes `StopAsyncIteration` and sets
`ag_closed`, `NULL` with `StopAsyncIteration` or `GeneratorExit` sets `ag_closed`, any other
`NULL` leaves it, and all three clear `ag_running_async`; a wrapped value is
`StopIteration(value)` with `ag_running_async` cleared; any other value is returned with no
change. -/
def AsyncGenUnwrapValueOutcomes : Prop :=
  ∀ (V X : Type) (w : World V X) (r : Ref),
    asyncGenUnwrapValue w r (.err none) =
      ((w.setClosed r).setRunning r false, .err (some ⟨.stopAsyncIteration, "StopAsyncIteration", "", .none⟩)) ∧
    (∀ e : Exc V, (e.kind = .stopAsyncIteration ∨ e.kind = .generatorExit) →
      asyncGenUnwrapValue w r (.err (some e)) = ((w.setClosed r).setRunning r false, .err (some e))) ∧
    (∀ e : Exc V, e.kind ≠ .stopAsyncIteration → e.kind ≠ .generatorExit →
      asyncGenUnwrapValue w r (.err (some e)) = (w.setRunning r false, .err (some e))) ∧
    (∀ v : Obj V, asyncGenUnwrapValue w r (.ok (asyncGenValueWrapperNew v)) =
      (w.setRunning r false, .err (some ⟨.stopIteration, "StopIteration", "", v⟩))) ∧
    (∀ v : Obj V, (∀ u, v ≠ .wrapped u) → asyncGenUnwrapValue w r (.ok v) = (w, .ok v))

theorem asyncGenUnwrapValueOutcomes_proven : AsyncGenUnwrapValueOutcomes := by
  intro V X w r
  refine ⟨by simp [asyncGenUnwrapValue, Exc.stopAsyncIteration, Exc.isStopAsyncIteration], fun e he => ?_,
    fun e h1 h2 => ?_, fun v => rfl, fun v hv => ?_⟩
  · rcases he with he | he <;>
      simp [asyncGenUnwrapValue, Exc.isStopAsyncIteration, Exc.isGeneratorExit, he]
  · simp [asyncGenUnwrapValue, Exc.isStopAsyncIteration, Exc.isGeneratorExit, h1, h2]
  · cases v <;> simp_all [asyncGenUnwrapValue]

/-! ## `async_gen_init_hooks` and the four methods -/

/-- `async_gen_init_hooks` (:1669-1702). Once `ag_hooks_inited` is set it does nothing.
Otherwise it sets the flag, stores `tstate->async_gen_finalizer` if there is one, and then
calls `firstiter` with the generator, in the world where both are already done; that call's
failure is the 1 return, so a raising hook is not retried. -/
def AsyncGenInitHooksOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r : Ref),
    ((w.get r).agHooksInited = true → asyncGenInitHooks h w r = (w, .ok)) ∧
    ((w.get r).agHooksInited = false →
      (w.firstiter = none → asyncGenInitHooks h w r =
        (w.set r { w.get r with agHooksInited := true, finalizer := w.finalizerHook.or (w.get r).finalizer }, .ok)) ∧
      (∀ fi w3 res, w.firstiter = some fi →
        h.callOneArg (w.set r { w.get r with agHooksInited := true, finalizer := w.finalizerHook.or (w.get r).finalizer }) fi (.gen r) = (w3, res) →
        asyncGenInitHooks h w r = (w3, match res with | .ok _ => .ok | .err e => .fail e)))

@[simp] theorem finalizerHook_set (w : World V X) (r : Ref) (g : GenObj V) :
    (w.set r g).finalizerHook = w.finalizerHook := rfl

@[simp] theorem firstiter_set (w : World V X) (r : Ref) (g : GenObj V) :
    (w.set r g).firstiter = w.firstiter := rfl

theorem asyncGenInitHooksOutcomes_proven : AsyncGenInitHooksOutcomes := by
  intro V X h w r
  refine ⟨fun hi => by simp [asyncGenInitHooks, hi], fun hi => ⟨fun hn => ?_, fun fi w3 res hfi hc => ?_⟩⟩
  · unfold asyncGenInitHooks
    rw [if_neg (by simp [hi])]
    cases hf : w.finalizerHook <;> simp [hf, hn, World.set_set]
  · unfold asyncGenInitHooks
    rw [if_neg (by simp [hi])]
    cases hf : w.finalizerHook <;> simp [hf, hfi, World.set_set] at hc ⊢ <;> rw [hc] <;> cases res <;> rfl

/-- `async_gen_anext` (:1706-1713), `async_gen_asend` (:1717-1724), `async_gen_aclose`
(:1728-1735), `async_gen_athrow` (:1738-1753) with `async_gen_athrow_new` (:2599-2621). A
failure of the hooks is the result; otherwise a fresh `AWAITABLE_STATE_INIT` awaitable holds
the generator and `NULL` (anext), the argument (asend), no exception (aclose). `athrow` first
warns for more than one argument (a failing warning is the result, before the hooks), then runs
the hooks, then `PyArg_UnpackTuple("athrow", 1, 3)` with its exact messages, and stores the one
to three arguments in the `(typ, val, tb)` slots. -/
def AsyncGenMethodsOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (r a : Ref),
    (∀ w1 e, asyncGenInitHooks h w r = (w1, .fail e) →
      asyncGenAnext h w r a = (w1, .fail e) ∧ (∀ v, asyncGenAsend h w r a v = (w1, .fail e)) ∧
      asyncGenAclose h w r a = (w1, .fail e)) ∧
    (∀ w1, asyncGenInitHooks h w r = (w1, .ok) →
      asyncGenAnext h w r a =
        ({ w1 with asends := fun q => if q = a then { gen := r, sendval := none, state := .init } else w1.asends q }, .ok) ∧
      (∀ v, asyncGenAsend h w r a v =
        ({ w1 with asends := fun q => if q = a then { gen := r, sendval := some v, state := .init } else w1.asends q }, .ok)) ∧
      asyncGenAclose h w r a =
        ({ w1 with athrows := fun q => if q = a then { gen := r, args := none, state := .init } else w1.athrows q }, .ok)) ∧
    (∀ args : List (Obj V), args.length > 1 → ∀ w1 e,
      h.warn w "the (type, exc, tb) signature of athrow() is deprecated, use the single-arg signature instead." = (w1, some e) →
      asyncGenAthrow h w r a args = (w1, .fail (some e))) ∧
    (∀ (args : List (Obj V)) w1,
      (args.length ≤ 1 ∧ w1 = w ∨ args.length > 1 ∧
        h.warn w "the (type, exc, tb) signature of athrow() is deprecated, use the single-arg signature instead." = (w1, none)) →
      (∀ w2 e, asyncGenInitHooks h w1 r = (w2, .fail e) → asyncGenAthrow h w r a args = (w2, .fail e)) ∧
      (∀ w2, asyncGenInitHooks h w1 r = (w2, .ok) →
        let mk := fun (t : Obj V × Option (Obj V) × Option (Obj V)) =>
          ({ w2 with athrows := fun q => if q = a then { gen := r, args := some t, state := .init } else w2.athrows q },
           (CStatus.ok : CStatus V))
        (args = [] → asyncGenAthrow h w r a args =
          (w2, .fail (some (Exc.typeError "athrow expected at least 1 argument, got 0")))) ∧
        (args.length > 3 → asyncGenAthrow h w r a args =
          (w2, .fail (some (Exc.typeError s!"athrow expected at most 3 arguments, got {args.length}")))) ∧
        (∀ t, args = [t] → asyncGenAthrow h w r a args = mk (t, none, none)) ∧
        (∀ t v, args = [t, v] → asyncGenAthrow h w r a args = mk (t, some v, none)) ∧
        (∀ t v tb, args = [t, v, tb] → asyncGenAthrow h w r a args = mk (t, some v, some tb))))

theorem asyncGenMethodsOutcomes_proven : AsyncGenMethodsOutcomes := by
  intro V X h w r a
  refine ⟨fun w1 e hi => ⟨by simp [asyncGenAnext, hi], fun v => by simp [asyncGenAsend, hi],
      by simp [asyncGenAclose, hi]⟩,
    fun w1 hi => ⟨by simp [asyncGenAnext, hi, asyncGenAsendNew], fun v => by simp [asyncGenAsend, hi, asyncGenAsendNew],
      by simp [asyncGenAclose, hi, asyncGenAthrowNew]⟩,
    fun args hl w1 e hw => by simp [asyncGenAthrow, hl, hw],
    fun args w1 hw => ⟨fun w2 e hi => ?_, fun w2 hi => ?_⟩⟩
  · rcases hw with ⟨hl, rfl⟩ | ⟨hl, hw⟩
    · have : ¬ args.length > 1 := by omega
      simp [asyncGenAthrow, this, hi]
    · simp [asyncGenAthrow, hl, hw, hi]
  · have hpre : asyncGenAthrow h w r a args =
        match checkPositional "athrow" args.length 1 3 with
        | some e => (w2, .fail (some e))
        | none => (asyncGenAthrowNew w2 a r (some (unpackThrowArgs args)), .ok) := by
      rcases hw with ⟨hl, rfl⟩ | ⟨hl, hw⟩
      · have : ¬ args.length > 1 := by omega
        simp only [asyncGenAthrow, this, if_false, hi]; rfl
      · simp only [asyncGenAthrow, hl, if_true, hw, hi]; rfl
    refine ⟨fun h0 => ?_, fun h3 => ?_, fun t ht => ?_, fun t v ht => ?_, fun t v tb ht => ?_⟩
    · subst h0; rw [hpre]; simp [checkPositional]; rfl
    · have : ¬ args.length < 1 := by omega
      have hm : toString "athrow" ++ toString " expected at most " ++ Nat.repr 3 ++
          toString " argument" ++ toString "s" ++ toString ", got " =
          toString "athrow expected at most 3 arguments, got " := by rfl
      rw [hpre]; simp [checkPositional, h3, this, hm]
    all_goals subst ht; rw [hpre]; simp [checkPositional, unpackThrowArgs, asyncGenAthrowNew]

/-! ## The `asend` awaitable -/

/-- `async_gen_asend_send` (:1974-2008) and `async_gen_asend_iternext` (:2025-2028). Closed is
the cannot-reuse `RuntimeError`. At `AWAITABLE_STATE_INIT` a generator with
`ag_running_async` set closes the awaitable with the already-running `RuntimeError`; otherwise
the awaitable moves to `AWAITABLE_STATE_ITER`, `None` or `NULL` is replaced by `ags_sendval`
(:1993-1995), and with `ag_running_async` set the generator gets `gen_send`; at
`AWAITABLE_STATE_ITER` the argument goes as it is. `awaitTail` reads the result and closes the
awaitable on `NULL`. `__next__` is `send(NULL)`. -/
def AsendSendOutcomes : Prop :=
  ∀ (V X : Type) (h : Hooks V X) (w : World V X) (a : Ref) (arg : Option (Obj V)),
    ((w.asends a).state = .closed → asyncGenAsendSend h w a arg =
      (w, .err (some (Exc.runtimeError "cannot reuse already awaited __anext__()/asend()")))) ∧
    ((w.asends a).state = .init → (w.get (w.asends a).gen).agRunningAsync = true →
      asyncGenAsendSend h w a arg = (w.setAsendState a .closed,
        .err (some (Exc.runtimeError "anext(): asynchronous generator is already running")))) ∧
    ((w.asends a).state = .init → (w.get (w.asends a).gen).agRunningAsync = false → ∀ w' res,
      genSend h ((w.setAsendState a .iter).setRunning (w.asends a).gen true) (w.asends a).gen
        (match arg with | none | some .none => (w.asends a).sendval | some v => some v) = (w', res) →
      asyncGenAsendSend h w a arg = awaitTail (fun w => w.setAsendState a .closed) w' (w.asends a).gen res) ∧
    ((w.asends a).state = .init → (w.get (w.asends a).gen).agRunningAsync = false → ∀ w' res,
      genSend h ((w.setAsendState a .iter).setRunning (w.asends a).gen true) (w.asends a).gen
        (w.asends a).sendval = (w', res) →
      asyncGenAsendIternext h w a = awaitTail (fun w => w.setAsendState a .closed) w' (w.asends a).gen res) ∧
    ((w.asends a).state = .iter → ∀ w' res,
      genSend h (w.setRunning (w.asends a).gen true) (w.asends a).gen arg = (w', res) →
      asyncGenAsendSend h w a arg = awaitTail (fun w => w.setAsendState a .closed) w' (w.asends a).gen res) ∧
    ((w.asends a).state = .iter → ∀ w' res,
      genSend h (w.setRunning (w.asends a).gen true) (w.asends a).gen none = (w', res) →
      asyncGenAsendIternext h w a = awaitTail (fun w => w.setAsendState a .closed) w' (w.asends a).gen res)

theorem asendArg (arg : Option (Obj V)) (sv : Option (Obj V)) :
    (if isNullOrNone arg = true then sv else arg) =
      (match arg with | none | some .none => sv | some v => some v) := by
  cases arg with
  | none => rfl
  | some v => cases v <;> rfl

theorem asyncGenAsendSendOutcomes_proven : AsendSendOutcomes := by
  intro V X h w a arg
  refine ⟨fun hs => by simp [asyncGenAsendSend, hs, reuseAsendMsg],
    fun hs hr => by simp [asyncGenAsendSend, hs, hr, anextRunningMsg],
    fun hs hr w' res hg => ?_, fun hs hr w' res hg => ?_, fun hs w' res hg => ?_, fun hs w' res hg => ?_⟩
  · simp only [asyncGenAsendSend, hs, hr, reduceCtorEq, if_false, Bool.false_eq_true, and_false,
      if_true, true_and]
    rw [asendArg, hg, asendFinish_eq]
  · simp only [asyncGenAsendIternext, asyncGenAsendSend, hs, hr, reduceCtorEq, if_false,
      Bool.false_eq_true, and_false, if_true, true_and, isNullOrNone]
    rw [hg, asendFinish_eq]
  · simp only [asyncGenAsendSend, hs, reduceCtorEq, if_false, false_and, ite_false, if_false]
    rw [hg, asendFinish_eq]
  · simp only [asyncGenAsendIternext, asyncGenAsendSend, hs, reduceCtorEq, if_false, false_and,
      ite_false]
    rw [hg, asendFinish_eq]

end PyLean.Bytecode.GenObj
