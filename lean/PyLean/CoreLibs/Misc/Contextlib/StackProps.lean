import PyLean.CoreLibs.Misc.Contextlib.Model

/-!
Properties of `ExitStack` and `AsyncExitStack`.

`nested` is what the class promises to imitate, "Callbacks are invoked in LIFO order to match the
behaviour of nested context managers" (Lib/contextlib.py:592): each level of a nested `with` calls
its `__exit__` with the exception leaving the level inside it, and passes on nothing if the result
is true, the same exception if false, or the exception `__exit__` raised. It carries no flags. The
loop of `ExitStack.__exit__` works with `suppressed_exc` and `pending_raise` instead, and
`exit_matches_nested` shows that the two agree on what leaves the outermost level.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

variable {σ F O A : Type}

/-- Nested `with` statements, innermost first: `exc` is the exception in flight. -/
def nested (c : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat) :
    Nat → Xs σ F O A → Option ExcId → Py (Xs σ F O A × Option ExcId)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, x, exc =>
    match x.2 with
    | [] => .ok (x, exc)
    | (isSync, cb) :: rest =>
      if !isSync then .error (.assertionError "") else
      match cb.call c (x.1, rest) exc with
      | (x, .ok true) => nested c frameExc fixFuel fuel x none
      | (x, .ok false) => nested c frameExc fixFuel fuel x exc
      | (x, .error newExc) =>
        match fixExceptionContext frameExc exc fixFuel x.1.h newExc with
        | none => .error .modelFuel
        | some h => nested c frameExc fixFuel fuel ({ x.1 with h := h }, x.2) (some newExc)

/-- What leaves a `with` block whose `__exit__` gave `r`, when `received` was passed in. -/
def outcome (received : Option ExcId) : Res Bool → Option ExcId
  | .ok true => none
  | .ok false => received
  | .error e => some e

/-- The flags of the loop against the exception in flight. -/
def FlagInv (received exc : Option ExcId) (suppressed pending : Bool) : Prop :=
  (pending = false → exc = if suppressed then none else received) ∧
  (pending = true → exc.isSome = true)

theorem exitLoop_nested (c : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat)
    (received : Option ExcId) :
    ∀ (fuel : Nat) (x : Xs σ F O A) (exc : Option ExcId) (sup pend : Bool),
      FlagInv received exc sup pend →
      match nested c frameExc fixFuel fuel x exc with
      | .error e => exitLoop c frameExc fixFuel fuel x exc sup pend = .error e
      | .ok (x', o) => ∃ sup' pend',
          exitLoop c frameExc fixFuel fuel x exc sup pend = .ok (x', o, sup', pend') ∧
          FlagInv received o sup' pend' := by
  intro fuel
  induction fuel with
  | zero => intro x exc sup pend _; rfl
  | succ f ih =>
    intro x exc sup pend hinv
    obtain ⟨s, st⟩ := x
    cases st with
    | nil =>
      simp only [nested, exitLoop]
      exact ⟨sup, pend, rfl, hinv⟩
    | cons p rest =>
      obtain ⟨isSync, cb⟩ := p
      cases isSync with
      | false => simp [nested, exitLoop]
      | true =>
        simp only [nested, exitLoop, Bool.not_true, Bool.false_eq_true, if_false]
        cases hc : cb.call c (s, rest) exc with
        | mk x' r =>
          cases r with
          | ok b =>
            cases b with
            | true => exact ih x' none true false ⟨fun _ => (by simp), fun h => (by cases h)⟩
            | false => exact ih x' exc sup pend hinv
          | error n =>
            simp only
            cases hf : fixExceptionContext frameExc exc fixFuel x'.1.h n with
            | none => simp
            | some h =>
              exact ih _ (some n) sup true ⟨fun h => (by cases h), fun _ => rfl⟩

/-- `ExitStack.__exit__` "behaves as though we were actually nesting multiple with statements": for
every stack, every behaviour of the callbacks and every exception passed in, the exception that
leaves the `with ExitStack()` block is the one that leaves the nested `with` statements, and the
callbacks run with the same arguments in the same order, ending with the same stack. A fuel or
`__context__` failure is shared by the two sides. -/
def ExitMatchesNested : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A)
    (exc frameExc : Option ExcId),
    match nested c frameExc fixFuel fuel x exc, exit c fuel fixFuel x exc frameExc with
    | .error e, r => r = .error e
    | .ok (x1, o), .ok (x2, r) => outcome exc r = o ∧ x2.2 = x1.2
    | .ok _, .error _ => False

theorem exitMatchesNested_proven : ExitMatchesNested := by
  intro σ F O A c fuel fixFuel x exc frameExc
  have hinv : FlagInv exc exc false false := ⟨fun _ => (by simp), fun h => (by cases h)⟩
  have h := exitLoop_nested c frameExc fixFuel exc fuel x exc false false hinv
  cases hn : nested c frameExc fixFuel fuel x exc with
  | error e =>
    rw [hn] at h
    simp only at h
    simp [exit, h, bind, Except.bind]
  | ok p =>
    obtain ⟨x1, o⟩ := p
    rw [hn] at h
    simp only at h
    obtain ⟨sup, pend, h1, h2, h3⟩ := h
    simp only [exit, h1, bind, Except.bind, pure, Except.pure]
    cases pend with
    | true =>
      cases o with
      | none => simpa using h3 rfl
      | some e => simp [outcome, raiseKeepingContext]
    | false =>
      have ho := h2 rfl
      simp only [Bool.false_eq_true, if_false]
      refine ⟨?_, trivial⟩
      cases sup with
      | true =>
        cases exc with
        | none => simp [outcome] at ho ⊢; exact ho.symm
        | some e => simp [outcome] at ho ⊢; exact ho.symm
      | false =>
        cases exc with
        | none => simp [outcome] at ho ⊢; exact ho.symm
        | some e => simp [outcome] at ho ⊢; exact ho.symm

/-- Callbacks that record themselves and leave the stack alone. -/
structure Recording (c : Calls σ F O A) (lg : St σ → List (Cb F O A)) : Prop where
  same : ∀ (cb : Cb F O A) (x : Xs σ F O A) (d : Option ExcId), (cb.call c x d).1.2 = x.2
  log : ∀ (cb : Cb F O A) (x : Xs σ F O A) (d : Option ExcId),
    lg (cb.call c x d).1.1 = lg x.1 ++ [cb]
  heap : ∀ (s : St σ) h, lg { s with h := h } = lg s

/-- "Callbacks are invoked in LIFO order": the entries run from the last pushed to the first, each
exactly once, and the stack is empty afterwards. The hypothesis on `__context__` is `FixDefined`: the
walk of `_fix_exception_context` ends, which the refutation of `ExitStackTerminates` shows can fail. -/
def ExitLifo : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (lg : St σ → List (Cb F O A)), Recording c lg →
    ∀ (fixFuel : Nat) (x : Xs σ F O A) (exc frameExc : Option ExcId),
      (∀ e h n, (fixExceptionContext frameExc e fixFuel h n).isSome = true) →
      (∀ p ∈ x.2, p.1 = true) →
      ∃ x' o, nested c frameExc fixFuel (x.2.length + 1) x exc = .ok (x', o) ∧
        x'.2 = [] ∧ lg x'.1 = lg x.1 ++ x.2.map (·.2)

theorem exitLifo_proven : ExitLifo := by
  intro σ F O A c lg hr fixFuel x exc frameExc hfix hs
  obtain ⟨s, st⟩ := x
  induction st generalizing s exc with
  | nil => exact ⟨(s, []), exc, rfl, rfl, by simp⟩
  | cons p rest ih =>
    obtain ⟨isSync, cb⟩ := p
    have hsy : isSync = true := hs (isSync, cb) (by simp)
    subst hsy
    have hrest : ∀ p ∈ rest, p.1 = true := fun p hp => hs p (by simp [hp])
    simp only [List.length_cons]
    rw [nested]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    have hst : (cb.call c (s, rest) exc).1.2 = rest := hr.same cb (s, rest) exc
    have hlg : lg (cb.call c (s, rest) exc).1.1 = lg s ++ [cb] := hr.log cb (s, rest) exc
    cases hc : cb.call c (s, rest) exc with
    | mk x1 r =>
      rw [hc] at hst hlg
      simp only at hst hlg
      obtain ⟨s1, st1⟩ := x1
      simp only at hst hlg
      subst hst
      cases r with
      | ok b =>
        cases b with
        | true =>
          obtain ⟨x', o, a, b', d⟩ := ih none s1 hrest
          exact ⟨x', o, a, b', by simp [d, hlg]⟩
        | false =>
          obtain ⟨x', o, a, b', d⟩ := ih exc s1 hrest
          exact ⟨x', o, a, b', by simp [d, hlg]⟩
      | error n =>
        obtain ⟨h, hh⟩ := Option.isSome_iff_exists.1 (hfix exc s1.h n)
        simp only [hh]
        obtain ⟨x', o, a, b', d⟩ := ih (some n) { s1 with h := h } hrest
        refine ⟨x', o, a, b', ?_⟩
        rw [d, hr.heap, hlg]
        simp

/-- The walk of `_fix_exception_context`, `while 1:` at Lib/contextlib.py:580, ends. Refuted: an
exception raised by a callback whose `__context__` chain is a cycle meets neither `None`, `old_exc`
nor `frame_exc`, so `ExitStack.__exit__` never returns. -/
def ExitStackTerminates : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (x : Xs σ F O A) (exc frameExc : Option ExcId),
    ∃ fuel fixFuel, exit c fuel fixFuel x exc frameExc ≠ .error .modelFuel

/-- Two exceptions, each the `__context__` of the other. -/
def cycleHeap : Heap :=
  [{ cls := clsExc, context := some 1 }, { cls := clsExc, context := some 0 }]

theorem fix_cycle : ∀ (fuel e : Nat), e = 0 ∨ e = 1 →
    fixExceptionContext none none fuel cycleHeap e = none := by
  intro fuel
  induction fuel with
  | zero => intro e _; rfl
  | succ f ih =>
    intro e he
    rcases he with rfl | rfl
    · exact ih 1 (.inr rfl)
    · exact ih 0 (.inl rfl)

/-- The callback raises the first exception of `cycleHeap`. -/
def cycleCalls : Calls Unit Unit Unit Unit where
  raw := fun _ x _ => (x, .error 0)
  bound := fun _ _ x _ => (x, .error 0)
  wrapped := fun _ _ x => (x, .error 0)

theorem exitStackTerminates_refuted : ¬ExitStackTerminates := by
  intro h
  obtain ⟨fuel, fixFuel, hne⟩ := h Unit Unit Unit Unit cycleCalls
    ({ h := cycleHeap, g := () }, [(true, .raw ())]) none none
  apply hne
  cases fuel with
  | zero => rfl
  | succ f =>
    have hf := fix_cycle fixFuel 0 (.inl rfl)
    simp [exit, exitLoop, Cb.call, cycleCalls, hf, bind, Except.bind]

/-- Following `__context__` from `e` reaches `None` within `n` steps. -/
def chainEnds (h : Heap) : Nat → ExcId → Bool
  | 0, _ => false
  | n + 1, e =>
    match (h.get e).context with
    | none => true
    | some c => chainEnds h n c

/-- No `__context__` chain of the heap is a cycle. -/
def Acyclic (h : Heap) : Prop := ∀ e, ∃ n, chainEnds h n e = true

/-- `__exit__` does not create a `__context__` cycle, as the interpreter's own chaining does not
(Python/errors.c:203-208). Refuted: `_fix_exception_context` sets `new_exc.__context__ = old_exc`
without looking for `new_exc` in the chain of `old_exc`. Here `F` is received and handled, `A` was
raised while `B` was being handled, a first callback raises `A`, and a second re-raises `B`. Nested
`with` statements give `B -> A`, `ExitStack` gives `B -> A -> B`. -/
def ExitKeepsContextAcyclic : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (fuel fixFuel : Nat) (x x' : Xs σ F O A)
    (exc frameExc : Option ExcId) (r : Res Bool),
    (∀ (cb : Cb F O A) (y : Xs σ F O A) (d : Option ExcId), (cb.call c y d).1.1.h = y.1.h) →
    Acyclic x.1.h → exit c fuel fixFuel x exc frameExc = .ok (x', r) → Acyclic x'.1.h

/-- `F`, `B` with context `F`, `A` with context `B`. -/
def fbaHeap : Heap :=
  [{ cls := clsExc }, { cls := clsExc, context := some 0 }, { cls := clsExc, context := some 1 }]

/-- Callback 0 raises `A`, callback 1 raises `B`. -/
def fbaCalls : Calls Unit Nat Unit Unit where
  raw := fun f x _ => (x, .error (if f = 0 then 2 else 1))
  bound := fun f _ x _ => (x, .error (if f = 0 then 2 else 1))
  wrapped := fun f _ x => (x, .error (if f = 0 then 2 else 1))

theorem chainEnds_set (e : ExcId) : ∀ (n : Nat), e = 1 ∨ e = 2 →
    chainEnds
      [{ cls := clsExc }, { cls := clsExc, context := some 2 }, { cls := clsExc, context := some 1 }]
      n e = false := by
  intro n
  induction n generalizing e with
  | zero => intro _; rfl
  | succ f ih =>
    intro he
    rcases he with rfl | rfl
    · exact ih 2 (.inr rfl)
    · exact ih 1 (.inl rfl)

theorem exitKeepsContextAcyclic_refuted : ¬ExitKeepsContextAcyclic := by
  intro h
  have hacy : Acyclic fbaHeap := by
    intro e
    refine ⟨4, ?_⟩
    match e with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | _ + 3 => rfl
  have hrun : exit fbaCalls 3 5 ({ h := fbaHeap, g := () }, [(true, .raw 0), (true, .raw 1)])
      (some 0) (some 0) =
      .ok (({ h := [{ cls := clsExc }, { cls := clsExc, context := some 2 },
        { cls := clsExc, context := some 1 }], g := () }, []), .error 1) := by
    rfl
  have := h Unit Nat Unit Unit fbaCalls 3 5 _ _ (some 0) (some 0) _
    (by
      intro cb y d
      cases cb <;> rfl)
    hacy hrun
  obtain ⟨n, hn⟩ := this 1
  rw [chainEnds_set 1 n (.inl rfl)] at hn
  cases hn

/-! ### Registering callbacks -/

/-- What `push`, `callback`, `enter_context`, `pop_all` do to `_exit_callbacks`, in the sync and the
async class. `push` registers the `__exit__` found on the type, bound to the object, or else the
object as a plain callable. `callback` registers a wrapper around the callable. `enter_context` calls
`__enter__`, and the exit is pushed only if that succeeded; an object without the protocol gives the
`TypeError` and pushes nothing. `pop_all` moves everything to a new stack. -/
def StackRegistration : Prop :=
  ∀ (σ F O A V : Type) (st : Stack F O A) (lookup : ExitLookup F O) (asF : O → F) (o : O) (m f : F)
    (a : A) (x : Xs σ F O A) (msg attrMsg : String) (en : Xs σ F O A → Xs σ F O A × Res V) (x1 : Xs σ F O A)
    (v : V) (e : ExcId) (b : Bool),
    (lookup o = some m → push lookup asF st o = (true, .bound m o) :: st) ∧
    (lookup o = none → push lookup asF st o = (true, .raw (asF o)) :: st) ∧
    (lookup o = some m → pushAsyncExit lookup asF st o = (false, .bound m o) :: st) ∧
    (lookup o = none → pushAsyncExit lookup asF st o = (false, .raw (asF o)) :: st) ∧
    callback st f a = (true, .wrapped f a) :: st ∧
    pushAsyncCallback st f a = (false, .wrapped f a) :: st ∧
    pushCmExit st o m = (true, .bound m o) :: st ∧
    pushAsyncCmExit st o m = (false, .bound m o) :: st ∧
    (Stack.init : Stack F O A) = [] ∧
    popAll st = (st, []) ∧
    stackEnter o = o ∧
    ((enterContext (fun _ => some (en, f)) msg attrMsg b x o).1.2 =
      if (en x).2.toBool then (b, .bound f o) :: (en x).1.2 else (en x).1.2) ∧
    (en x = (x1, .error e) → enterContext (fun _ => some (en, f)) msg attrMsg b x o = (x1, .error e)) ∧
    (en x = (x1, .ok v) →
      enterContext (fun _ => some (en, f)) msg attrMsg b x o = ((x1.1, (b, .bound f o) :: x1.2), .ok v)) ∧
    (enterContext (V := V) (fun _ => none) msg attrMsg b x o).1.2 = x.2

theorem stackRegistration_proven : StackRegistration := by
  intro σ F O A V st lookup asF o m f a x msg attrMsg en x1 v e b
  refine ⟨?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · intro h; simp [push, h, pushCmExit, pushExitCallback]
  · intro h; simp [push, h, pushExitCallback]
  · intro h; simp [pushAsyncExit, h, pushAsyncCmExit, pushExitCallback]
  · intro h; simp [pushAsyncExit, h, pushExitCallback]
  · simp only [enterContext]
    cases h : en x with
    | mk y r =>
      cases r <;> simp [Except.toBool, pushExitCallback]
  · intro h; simp [enterContext, h]
  · intro h; simp [enterContext, h, pushExitCallback]

/-- `callback` "Cannot suppress exceptions": the wrapper of `_create_cb_wrapper` calls the callback
with its own arguments, drops the result, and ignores the exception details. The wrapper of
`_create_exit_wrapper` is `cm_exit` bound to `cm`, so it can suppress. -/
def CallbackCannotSuppress : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (f m : F) (a : A) (o : O) (x : Xs σ F O A) (d d' : Option ExcId),
    (Cb.wrapped f a : Cb F O A).call c x d = (Cb.wrapped f a : Cb F O A).call c x d' ∧
    (∀ x', c.wrapped f a x = (x', .ok ()) → (Cb.wrapped f a : Cb F O A).call c x d = (x', .ok false)) ∧
    (∀ x' e, c.wrapped f a x = (x', .error e) →
      (Cb.wrapped f a : Cb F O A).call c x d = (x', .error e)) ∧
    (Cb.bound m o : Cb F O A).call c x d = c.bound m o x d

theorem callbackCannotSuppress_proven : CallbackCannotSuppress := by
  intro σ F O A c f m a o x d d'
  refine ⟨rfl, ?_, ?_, rfl⟩
  · intro x' h; simp [Cb.call, h]
  · intro x' e h; simp [Cb.call, h]

/-! ### `AsyncExitStack` against `ExitStack` -/

/-- No entry of the stack is async. -/
def AllSync (st : Stack F O A) : Prop := ∀ p ∈ st, p.1 = true

theorem aexitLoop_sync (c ac : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat)
    (hk : ∀ (cb : Cb F O A) (x : Xs σ F O A) (d : Option ExcId), AllSync x.2 →
      AllSync (cb.call c x d).1.2) :
    ∀ (fuel : Nat) (x : Xs σ F O A) (exc : Option ExcId) (sup pend : Bool), AllSync x.2 →
      aexitLoop c ac frameExc fixFuel fuel x exc sup pend =
        exitLoop c frameExc fixFuel fuel x exc sup pend := by
  intro fuel
  induction fuel with
  | zero => intro x exc sup pend _; rfl
  | succ f ih =>
    intro x exc sup pend hs
    obtain ⟨s, st⟩ := x
    simp only [aexitLoop, exitLoop]
    cases st with
    | nil => rfl
    | cons p rest =>
      obtain ⟨isSync, cb⟩ := p
      have hy : isSync = true := hs (isSync, cb) (by simp)
      subst hy
      have hr : AllSync rest := fun p hp => hs p (by simp [hp])
      simp only [Bool.not_true, Bool.false_eq_true, if_false, if_true]
      have hk' := hk cb (s, rest) exc hr
      cases hc : cb.call c (s, rest) exc with
      | mk x1 r =>
        rw [hc] at hk'
        simp only at hk'
        cases r with
        | ok b =>
          cases b with
          | true => exact ih _ _ _ _ hk'
          | false => exact ih _ _ _ _ hk'
        | error n =>
          simp only
          cases fixExceptionContext frameExc exc fixFuel x1.1.h n with
          | none => rfl
          | some h => exact ih _ _ _ _ hk'

/-- `AsyncExitStack.__aexit__` is `ExitStack.__exit__` over sync entries, except that an exception
leaving an `async def` turns from `StopIteration` into `RuntimeError`. The `_exit_wrapper` of
`_create_async_cb_wrapper` and `_create_async_exit_wrapper` build the same entries with
`is_sync=False`. `close()` and `aclose()` are the exit with no exception and drop the result. -/
def AsyncExitMatches : Prop :=
  ∀ (σ F O A : Type) (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A)
    (exc frameExc : Option ExcId),
    (∀ (cb : Cb F O A) (x : Xs σ F O A) (d : Option ExcId), AllSync x.2 → AllSync (cb.call c x d).1.2) →
    AllSync x.2 →
    aexit c ac fuel fixFuel x exc frameExc =
      (match exit c fuel fixFuel x exc frameExc with
       | .error e => .error e
       | .ok (x', r) =>
         let (s, r') := coBoundary x'.1 r
         .ok ((s, x'.2), r')) ∧
    (∀ (x' : Xs σ F O A) r, exit c fuel fixFuel x none frameExc = .ok (x', r) →
      close c fuel fixFuel x frameExc =
        .ok (x', match r with
          | .ok _ => .ok ()
          | .error e => .error e))

theorem asyncExitMatches_proven : AsyncExitMatches := by
  intro σ F O A c ac fuel fixFuel x exc frameExc hk hs
  constructor
  · simp only [aexit, exit, aexitLoop_sync c ac frameExc fixFuel hk fuel x exc false false hs,
      bind, Except.bind, pure, Except.pure]
    cases exitLoop c frameExc fixFuel fuel x exc false false with
    | error e => rfl
    | ok p =>
      obtain ⟨x', o, sup, pend⟩ := p
      simp only
      cases pend with
      | true =>
        cases o with
        | none => rfl
        | some e => rfl
      | false => simp [coBoundary]
  · intro x' r h
    simp only [close, h, bind, Except.bind, pure, Except.pure]
    cases r <;> rfl

end PyLean.CoreLibs.Misc.Contextlib
