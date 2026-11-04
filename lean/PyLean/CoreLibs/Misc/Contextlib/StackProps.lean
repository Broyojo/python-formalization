import PyLean.CoreLibs.Misc.Contextlib.AsyncProps

/-!
Properties of `ExitStack` and `AsyncExitStack`.

`nested` is what the class promises to imitate, "Callbacks are invoked in LIFO order to match the
behaviour of nested context managers" (Lib/contextlib.py:651): each level of a nested `with` calls
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

/-- The walk of `_fix_exception_context`, `while 1:` at Lib/contextlib.py:639, ends. Refuted: an
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

/-- `_lookup_special` looks on the type and follows `_descriptor_get`: a class or an object with no `__get__` comes back as
itself, anything else is what its `__get__` gave, including an exception, and nothing on the type gives the default. -/
def LookupSpecialFollowsDescriptor : Prop :=
  ∀ (T : Type) (v dflt : T) (r : Res T),
    lookupSpecial none dflt = .ok dflt ∧
    lookupSpecial (some (.isClass v)) dflt = .ok v ∧
    lookupSpecial (some (.noGet v)) dflt = .ok v ∧
    lookupSpecial (some (.get r)) dflt = r ∧
    lookupSentinel (none : Option (Descr T)) = .ok none ∧
    lookupSentinel (some (.isClass v)) = .ok (some v) ∧
    lookupSentinel (some (.noGet v)) = .ok (some v) ∧
    lookupSentinel (some (.get r)) = (match r with | .ok v => .ok (some v) | .error e => .error e)

theorem lookupSpecialFollowsDescriptor_proven : LookupSpecialFollowsDescriptor := by
  intro T v dflt r
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  cases r <;> rfl

/-- What `push`, `callback`, `enter_context` do to `_exit_callbacks`, in the sync and the async class. `push` registers
what `_lookup_special` gives, or else the object as a plain callable, and returns the object it was given, "for use as a
decorator"; a failing `__get__` raises and registers nothing. `callback` registers a wrapper whose `__wrapped__` is the
callable, and returns the callable. `enter_context` looks up `__enter__` and then `__exit__`, either one missing or failing
stops it before the enter method runs; it then runs the enter method, and the exit is pushed only if that succeeded. Every
registration puts its entry on top, where `__exit__` takes it first. -/
def StackRegistration : Prop :=
  ∀ (σ F O A V : Type) (st : Stack F O A) (lookup : ExitLookup F O A) (asF : O → F) (o : O) (f : F) (cb : Cb F O A)
    (a : A) (x : Xs σ F O A) (msg : String) (en : Xs σ F O A → Xs σ F O A × Res V) (x1 : Xs σ F O A)
    (v : V) (e : ExcId) (b : Bool) (dn : Descr (Xs σ F O A → Xs σ F O A × Res V)) (dx : Descr (Cb F O A)),
    (lookupSpecial (lookup o) (.raw (asF o)) = .ok cb → push lookup asF st o = ((true, cb) :: st, .ok o)) ∧
    (lookup o = none → push lookup asF st o = ((true, .raw (asF o)) :: st, .ok o)) ∧
    (lookup o = some (.get (.error e)) → push lookup asF st o = (st, .error e)) ∧
    (lookupSpecial (lookup o) (.raw (asF o)) = .ok cb → pushAsyncExit lookup asF st o = ((false, cb) :: st, .ok o)) ∧
    (lookup o = none → pushAsyncExit lookup asF st o = ((false, .raw (asF o)) :: st, .ok o)) ∧
    (lookup o = some (.get (.error e)) → pushAsyncExit lookup asF st o = (st, .error e)) ∧
    (callback st f a = ((true, .wrapped f a) :: st, f) ∧ (Cb.wrapped f a : Cb F O A).wrappedAttr = some f) ∧
    pushAsyncCallback st f a = ((false, .wrapped f a) :: st, f) ∧
    (descriptorGet dn = .ok en → descriptorGet dx = .ok cb → en x = (x1, .error e) →
      enterContext (fun _ => some dn) (fun _ => some dx) msg b x o = (x1, .error e)) ∧
    (descriptorGet dn = .ok en → descriptorGet dx = .ok cb → en x = (x1, .ok v) →
      enterContext (fun _ => some dn) (fun _ => some dx) msg b x o = ((x1.1, (b, cb) :: x1.2), .ok v)) ∧
    (enterContext (V := V) (fun _ => none) lookup msg b x o).1.2 = x.2 ∧
    (descriptorGet dn = .ok en → (enterContext (fun _ => some dn) (fun _ => none) msg b x o).1.2 = x.2) ∧
    enterContext (V := V) (fun _ => some (.get (.error e))) lookup msg b x o = (x, .error e) ∧
    (descriptorGet dn = .ok en →
      enterContext (fun _ => some dn) (fun _ => some (.get (.error e))) msg b x o = (x, .error e))

theorem stackRegistration_proven : StackRegistration := by
  intro σ F O A V st lookup asF o f cb a x msg en x1 v e b dn dx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ⟨rfl, rfl⟩, rfl, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro h; simp [push, h, pushExitCallback]
  · intro h; simp [push, lookupSpecial, h, pushExitCallback]
  · intro h; simp [push, lookupSpecial, descriptorGet, h]
  · intro h; simp [pushAsyncExit, h, pushExitCallback]
  · intro h; simp [pushAsyncExit, lookupSpecial, h, pushExitCallback]
  · intro h; simp [pushAsyncExit, lookupSpecial, descriptorGet, h]
  · intro h1 h2 h3; simp [enterContext, lookupSentinel, h1, h2, h3]
  · intro h1 h2 h3; simp [enterContext, lookupSentinel, h1, h2, h3, pushExitCallback]
  · rfl
  · intro h1; simp [enterContext, lookupSentinel, h1]
  · intro h1
    simp only [enterContext, lookupSentinel, h1]
    rfl

/-- `pop_all` "transfers the context stack to a new instance": the instance is made first, by
`type(self)()`, and when that raises, `self` keeps every callback; otherwise the new instance gets
the deque in its order and `self` is left empty. -/
def PopAllMoves : Prop :=
  ∀ (σ F O A N : Type) (mk : St σ → St σ × Res N) (s s' : St σ) (st : Stack F O A) (n : N) (e : ExcId),
    (mk s = (s', .error e) → popAll mk s st = (s', st, .error e)) ∧
    (mk s = (s', .ok n) → popAll mk s st = (s', [], .ok (n, st)))

theorem popAllMoves_proven : PopAllMoves := by
  intro σ F O A N mk s s' st n e
  constructor
  · intro h; simp [popAll, h]
  · intro h; simp [popAll, h]

/-- The deque after registering `cbs` in order with `_push_exit_callback`. -/
def registerAll (st : Stack F O A) : List (Cb F O A) → Stack F O A
  | [] => st
  | cb :: cbs => registerAll (pushExitCallback st cb) cbs

theorem registerAll_eq (st : Stack F O A) (cbs : List (Cb F O A)) :
    registerAll st cbs = (cbs.map (fun cb => (true, cb))).reverse ++ st := by
  induction cbs generalizing st with
  | nil => rfl
  | cons cb rest ih => simp [registerAll, ih, pushExitCallback]

/-- "Callbacks are invoked in LIFO order": after any sequence of registrations, which put their
entries on top (`StackRegistration`), `ExitStack.__exit__` calls the entries from the last
registered to the first, each once, and leaves the stack empty, when the walk of
`_fix_exception_context` ends (`FixDefined`, which `ExitStackTerminates` shows can fail). -/
def ExitRunsLifo : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (lg : St σ → List (Cb F O A)), Recording c lg →
    ∀ (fixFuel : Nat) (s : St σ) (cbs : List (Cb F O A)) (exc frameExc : Option ExcId),
      (∀ e h n, (fixExceptionContext frameExc e fixFuel h n).isSome = true) →
      ∃ x' r, exit c (cbs.length + 1) fixFuel (s, registerAll [] cbs) exc frameExc = .ok (x', r) ∧
        x'.2 = [] ∧ lg x'.1 = lg s ++ cbs.reverse

theorem exitRunsLifo_proven : ExitRunsLifo := by
  intro σ F O A c lg hr fixFuel s cbs exc frameExc hfix
  have hall : ∀ p ∈ (s, registerAll [] cbs).2, p.1 = true := by
    intro p hp
    rw [registerAll_eq] at hp
    simp at hp
    obtain ⟨cb, _, rfl⟩ := hp
    rfl
  have hlen : (s, registerAll ([] : Stack F O A) cbs).2.length = cbs.length := by
    simp [registerAll_eq]
  obtain ⟨x', o, hn, hx, hl⟩ := exitLifo_proven σ F O A c lg hr fixFuel (s, registerAll [] cbs) exc
    frameExc hfix hall
  rw [hlen] at hn
  have hinv : FlagInv exc exc false false := ⟨fun _ => (by simp), fun h => (by cases h)⟩
  have h := exitLoop_nested c frameExc fixFuel exc (cbs.length + 1) (s, registerAll [] cbs) exc false
    false hinv
  rw [hn] at h
  obtain ⟨sup, pend, h1, _, h3⟩ := h
  have hmap : (registerAll ([] : Stack F O A) cbs).map (·.2) = cbs.reverse := by
    simp [registerAll_eq, List.map_reverse, Function.comp_def]
  cases pend with
  | true =>
    cases o with
    | none => simpa using h3 rfl
    | some e =>
      refine ⟨raiseKeepingContext x' e frameExc, .error e, ?_, ?_, ?_⟩
      · simp [exit, h1, bind, Except.bind, pure, Except.pure]
      · simpa [raiseKeepingContext] using hx
      · simp only [raiseKeepingContext]
        rw [hr.heap, hl]
        try simp only at hmap
        rw [hmap]
  | false =>
    refine ⟨x', .ok (exc.isSome && sup), ?_, hx, ?_⟩
    · simp [exit, h1, bind, Except.bind, pure, Except.pure]
    · rw [hl]
      try simp only at hmap
      rw [hmap]

/-- `close()` "immediately unwinds the context stack": it is the exit with no exception, so the
exception that leaves it is the one leaving nested `with` statements with no exception, and a
callback's true result does not make it return anything but `None`. -/
def CloseMatchesNested : Prop :=
  ∀ (σ F O A : Type) (c : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (frameExc : Option ExcId),
    match nested c frameExc fixFuel fuel x none, close c fuel fixFuel x frameExc with
    | .error e, r => r = .error e
    | .ok (x1, o), .ok (x2, r) => x2.2 = x1.2 ∧ (match o with | none => r = .ok () | some e => r = .error e)
    | .ok _, .error _ => False

theorem closeMatchesNested_proven : CloseMatchesNested := by
  intro σ F O A c fuel fixFuel x frameExc
  have h := exitMatchesNested_proven σ F O A c fuel fixFuel x none frameExc
  cases hn : nested c frameExc fixFuel fuel x none with
  | error e =>
    rw [hn] at h
    try simp only at h
    simp [close, h, bind, Except.bind]
  | ok p =>
    obtain ⟨x1, o⟩ := p
    rw [hn] at h
    try simp only at h
    cases he : exit c fuel fixFuel x none frameExc with
    | error e => rw [he] at h; simp at h
    | ok q =>
      obtain ⟨x2, r⟩ := q
      rw [he] at h
      obtain ⟨ho, hs⟩ := h
      cases r with
      | ok b =>
        have hc : close c fuel fixFuel x frameExc = .ok (x2, .ok ()) := by
          simp [close, he, bind, Except.bind, pure, Except.pure]
        rw [hc]
        refine ⟨hs, ?_⟩
        cases b <;> simp [outcome] at ho <;> subst ho <;> rfl
      | error e =>
        have hc : close c fuel fixFuel x frameExc = .ok (x2, .error e) := by
          simp [close, he, bind, Except.bind, pure, Except.pure]
        rw [hc]
        refine ⟨hs, ?_⟩
        simp [outcome] at ho; subst ho; rfl

/-- `callback` "Cannot suppress exceptions": the wrapper of `_create_cb_wrapper` calls the callback
with its own arguments, drops the result, and ignores the exception details. An exit method bound to `cm`, which is
what `_lookup_special` gives for a function, passes the details on, so it can suppress. -/
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

/-! ### `AsyncExitStack` -/

/-- `push_async_callback`'s entry "Cannot suppress exceptions" either: the `async def` wrapper of
`_create_async_cb_wrapper` awaits the callback with its own arguments, ignores the details and gives
`None`; an exception comes through, except that a `StopIteration`, which a callable that is no
coroutine function can raise from the call, leaves the wrapper as the coroutine's `RuntimeError`. -/
def AsyncCallbackCannotSuppress : Prop :=
  ∀ (σ F O A : Type) (ac : Calls σ F O A) (f : F) (a : A) (x x' : Xs σ F O A) (d d' : Option ExcId)
    (e : ExcId),
    (Cb.wrapped f a : Cb F O A).acall ac x d = (Cb.wrapped f a : Cb F O A).acall ac x d' ∧
    (ac.wrapped f a x = (x', .ok ()) → (Cb.wrapped f a : Cb F O A).acall ac x d = (x', .ok false)) ∧
    (ac.wrapped f a x = (x', .error e) → x'.1.h.isInst e "StopIteration" = false →
      (Cb.wrapped f a : Cb F O A).acall ac x d = (x', .error e)) ∧
    (ac.wrapped f a x = (x', .error e) → x'.1.h.isInst e "StopIteration" = true →
      (Cb.wrapped f a : Cb F O A).acall ac x d =
        let r : St σ × Res Bool := coroutineStop x'.1 e
        ((r.1, x'.2), r.2))

theorem asyncCallbackCannotSuppress_proven : AsyncCallbackCannotSuppress := by
  intro σ F O A ac f a x x' d d' e
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h; simp [Cb.acall, h, coBoundary]
  · intro h1 h2; simp [Cb.acall, h1, h2, coBoundary]
  · intro h1 h2; simp [Cb.acall, h1, h2, coBoundary, coroutineStop]

/-- `enter_async_context` is `enter_context` with `__aenter__`, `__aexit__` and `is_sync=False`, in
an `async def`: the result of `await _enter()` is returned and the exit pushed after it; a failure
of a lookup or of `_enter` pushes nothing and comes through, a `StopIteration` as the coroutine's
`RuntimeError`; a missing method is the `TypeError` with the source's message. -/
def AEnterContextCases : Prop :=
  ∀ (σ F O A V : Type) (x x1 : Xs σ F O A) (o : O) (msg : String) (cb : Cb F O A) (v : V) (e : ExcId)
    (en : Xs σ F O A → Xs σ F O A × Res V) (dn : Descr (Xs σ F O A → Xs σ F O A × Res V))
    (dx : Descr (Cb F O A)) (lookup : ExitLookup F O A),
    let wrap : Xs σ F O A → ExcId → Xs σ F O A × Res V := fun y e =>
      if y.1.h.isInst e "StopIteration" then
        let r : St σ × Res V := coroutineStop y.1 e
        ((r.1, y.2), r.2)
      else (y, .error e)
    (descriptorGet dn = .ok en → descriptorGet dx = .ok cb → en x = (x1, .ok v) →
      aenterContext (fun _ => some dn) (fun _ => some dx) msg x o = ((x1.1, (false, cb) :: x1.2), .ok v)) ∧
    (descriptorGet dn = .ok en → descriptorGet dx = .ok cb → en x = (x1, .error e) →
      aenterContext (fun _ => some dn) (fun _ => some dx) msg x o = wrap x1 e) ∧
    aenterContext (V := V) (fun _ => some (.get (.error e))) lookup msg x o = wrap x e ∧
    (descriptorGet dn = .ok en →
      aenterContext (fun _ => some dn) (fun _ => some (.get (.error e))) msg x o = wrap x e) ∧
    (∃ t, aenterContext (V := V) (fun _ => none) lookup msg x o =
      (((x.1.raiseNew clsType msg).1, x.2), .error t) ∧ ((x.1.raiseNew clsType msg).1.h.get t).msg = msg ∧
      ((x.1.raiseNew clsType msg).1.h.get t).cls = clsType)

theorem aEnterContextCases_proven : AEnterContextCases := by
  intro σ F O A V x x1 o msg cb v e en dn dx lookup wrap
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 h3
    simp [aenterContext, enterContext, lookupSentinel, h1, h2, h3, pushExitCallback, coBoundary]
  · intro h1 h2 h3
    cases hs : x1.1.h.isInst e "StopIteration" <;>
      simp [aenterContext, enterContext, lookupSentinel, h1, h2, h3, coBoundary, wrap, hs, coroutineStop]
  · cases hs : x.1.h.isInst e "StopIteration" <;>
      simp [aenterContext, enterContext, lookupSentinel, descriptorGet, coBoundary, wrap, hs, coroutineStop]
  · intro h1
    simp only [aenterContext, enterContext, lookupSentinel, h1]
    cases hs : x.1.h.isInst e "StopIteration" <;>
      simp [descriptorGet, coBoundary, wrap, hs, coroutineStop]
  · have hr := raiseNew_not_stop x.1 clsType msg none (by decide)
    have ho := raiseNew_obj x.1 clsType msg none
    refine ⟨(x.1.raiseNew clsType msg).2, ?_, ho.2.1, ho.2.2.2.2⟩
    simp only [aenterContext, enterContext, lookupSentinel]
    rw [coBoundary_of_not_stop _ _ hr]

/-- Nested `async with` statements, innermost first: a sync entry is called, an async one awaited. -/
def anested (c ac : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat) :
    Nat → Xs σ F O A → Option ExcId → Py (Xs σ F O A × Option ExcId)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, x, exc =>
    match x.2 with
    | [] => .ok (x, exc)
    | (isSync, cb) :: rest =>
      match (if isSync then cb.call c (x.1, rest) exc else cb.acall ac (x.1, rest) exc) with
      | (x, .ok true) => anested c ac frameExc fixFuel fuel x none
      | (x, .ok false) => anested c ac frameExc fixFuel fuel x exc
      | (x, .error newExc) =>
        match fixExceptionContext frameExc exc fixFuel x.1.h newExc with
        | none => .error .modelFuel
        | some h => anested c ac frameExc fixFuel fuel ({ x.1 with h := h }, x.2) (some newExc)

theorem aexitLoop_anested (c ac : Calls σ F O A) (frameExc : Option ExcId) (fixFuel : Nat)
    (received : Option ExcId) :
    ∀ (fuel : Nat) (x : Xs σ F O A) (exc : Option ExcId) (sup pend : Bool),
      FlagInv received exc sup pend →
      match anested c ac frameExc fixFuel fuel x exc with
      | .error e => aexitLoop c ac frameExc fixFuel fuel x exc sup pend = .error e
      | .ok (x', o) => ∃ sup' pend',
          aexitLoop c ac frameExc fixFuel fuel x exc sup pend = .ok (x', o, sup', pend') ∧
          FlagInv received o sup' pend' := by
  intro fuel
  induction fuel with
  | zero => intro x exc sup pend _; rfl
  | succ f ih =>
    intro x exc sup pend hinv
    obtain ⟨s, st⟩ := x
    cases st with
    | nil =>
      simp only [anested, aexitLoop]
      exact ⟨sup, pend, rfl, hinv⟩
    | cons p rest =>
      obtain ⟨isSync, cb⟩ := p
      simp only [anested, aexitLoop]
      generalize (if isSync = true then cb.call c (s, rest) exc else cb.acall ac (s, rest) exc) = res
      obtain ⟨x', r⟩ := res
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

/-- The exception `AsyncExitStack.__aexit__` raises, `e`, against the exception `p` leaving the
nested `async with` levels: `p` itself, or for a `StopIteration` `p` the coroutine's
`RuntimeError` for it. -/
def ALeaves (h : Heap) (p e : ExcId) : Prop :=
  (e = p ∧ h.isInst p "StopIteration" = false) ∨
  (h.isInst p "StopIteration" = true ∧ e ≠ p ∧ (h.get e).cls = clsRuntime ∧
    (h.get e).msg = "coroutine raised StopIteration" ∧ (h.get e).cause = some p ∧
    (h.get e).context = some p)

theorem coBoundary_leaves {σ : Type} (s : St σ) (p : ExcId) :
    ∃ e, coBoundary s (.error p : Res Bool) = ((coBoundary s (.error p : Res Bool)).1, .error e) ∧
      ALeaves (coBoundary s (.error p : Res Bool)).1.h p e := by
  cases hs : s.h.isInst p "StopIteration" with
  | false =>
    refine ⟨p, by simp [coBoundary, hs], ?_⟩
    left
    simp [coBoundary, hs]
  | true =>
    have hl := isInst_lt hs
    refine ⟨s.h.length, by simp [coBoundary, hs, Heap.alloc], ?_⟩
    right
    simp only [coBoundary, hs, if_true]
    have hg := get_alloc_last s.h
      { cls := clsRuntime, msg := "coroutine raised StopIteration", context := some p, cause := some p }
    have hp := get_alloc_lt s.h
      { cls := clsRuntime, msg := "coroutine raised StopIteration", context := some p, cause := some p } p hl
    simp only [Heap.alloc] at hg hp ⊢
    refine ⟨?_, Nat.ne_of_gt hl, ?_, ?_, ?_, ?_⟩
    · simp only [Heap.isInst] at hs ⊢; rw [hp]; exact hs
    all_goals simp [hg]

/-- `AsyncExitStack.__aexit__` "behaves as though we were actually nesting multiple with
statements", here `async with` and `with` statements: for every stack, sync and async entries
mixed, every behaviour of the callbacks and every exception passed in, the callbacks run in the
same order with the same arguments, ending with the same stack, and what `__aexit__` gives is what
leaves the nested statements: true for nothing, false for the exception passed in, or the
exception raised, after the coroutine boundary of `__aexit__`. -/
def AExitMatchesNested : Prop :=
  ∀ (σ F O A : Type) (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A)
    (exc frameExc : Option ExcId),
    match anested c ac frameExc fixFuel fuel x exc, aexit c ac fuel fixFuel x exc frameExc with
    | .error e, r => r = .error e
    | .ok (x1, o), .ok (x2, r) => x2.2 = x1.2 ∧
        (match r with
         | .ok true => o = none
         | .ok false => o = exc
         | .error e => ∃ p, o = some p ∧ ALeaves x2.1.h p e)
    | .ok _, .error _ => False

theorem aexit_shape (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A)
    (exc frameExc : Option ExcId) :
    match anested c ac frameExc fixFuel fuel x exc, aexit c ac fuel fixFuel x exc frameExc with
    | .error e, r => r = .error e
    | .ok (x1, o), .ok (x2, r) => x2.2 = x1.2 ∧
        (match r with
         | .ok true => o = none
         | .ok false => o = exc
         | .error e => ∃ p, o = some p ∧ ALeaves x2.1.h p e)
    | .ok _, .error _ => False := by
  have hinv : FlagInv exc exc false false := ⟨fun _ => (by simp), fun h => (by cases h)⟩
  have h := aexitLoop_anested c ac frameExc fixFuel exc fuel x exc false false hinv
  cases hn : anested c ac frameExc fixFuel fuel x exc with
  | error e =>
    rw [hn] at h
    simp only at h
    simp [aexit, h, bind, Except.bind]
  | ok p =>
    obtain ⟨x1, o⟩ := p
    rw [hn] at h
    simp only at h
    obtain ⟨sup, pend, h1, h2, h3⟩ := h
    cases pend with
    | true =>
      cases o with
      | none => simpa using h3 rfl
      | some p =>
        obtain ⟨e, he, hl⟩ := coBoundary_leaves (raiseKeepingContext x1 p frameExc).1 p
        simp only [aexit, h1, bind, Except.bind, pure, Except.pure, if_true]
        rw [he]
        refine ⟨by simp [raiseKeepingContext], p, by simp, hl⟩
    | false =>
      have ho := h2 rfl
      simp only [aexit, h1, bind, Except.bind, pure, Except.pure, Bool.false_eq_true, if_false]
      refine ⟨by simp, ?_⟩
      cases sup <;> cases exc <;> simp at ho ⊢ <;> exact ho

theorem aExitMatchesNested_proven : AExitMatchesNested := by
  intro σ F O A c ac fuel fixFuel x exc frameExc
  exact aexit_shape c ac fuel fixFuel x exc frameExc

/-- `aclose()` is `__aexit__(None, None, None)` with the result dropped: what leaves it is the
exception leaving nested `async with` statements with no exception, after the coroutine boundary,
and a callback's true result does not make it return anything but `None`. -/
def ACloseMatchesNested : Prop :=
  ∀ (σ F O A : Type) (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x : Xs σ F O A) (frameExc : Option ExcId),
    match anested c ac frameExc fixFuel fuel x none, aclose c ac fuel fixFuel x frameExc with
    | .error e, r => r = .error e
    | .ok (x1, o), .ok (x2, r) => x2.2 = x1.2 ∧
        (match r with
         | .ok () => o = none
         | .error e => ∃ p, o = some p ∧ ALeaves x2.1.h p e)
    | .ok _, .error _ => False

theorem aCloseMatchesNested_proven : ACloseMatchesNested := by
  intro σ F O A c ac fuel fixFuel x frameExc
  have h := aexit_shape c ac fuel fixFuel x none frameExc
  cases hn : anested c ac frameExc fixFuel fuel x none with
  | error e =>
    rw [hn] at h
    try simp only at h
    simp [aclose, h, bind, Except.bind]
  | ok p =>
    obtain ⟨x1, o⟩ := p
    rw [hn] at h
    try simp only at h
    cases he : aexit c ac fuel fixFuel x none frameExc with
    | error e => rw [he] at h; simp at h
    | ok q =>
      obtain ⟨x2, r⟩ := q
      rw [he] at h
      obtain ⟨hs, ho⟩ := h
      cases r with
      | ok b =>
        have hc : aclose c ac fuel fixFuel x frameExc = .ok (x2, .ok ()) := by
          simp [aclose, he, bind, Except.bind, pure, Except.pure, coBoundary]
        rw [hc]
        refine ⟨hs, ?_⟩
        cases b <;> simpa using ho
      | error e =>
        obtain ⟨p, hp, hl⟩ := ho
        have hne : x2.1.h.isInst e "StopIteration" = false := by
          rcases hl with ⟨rfl, h2⟩ | ⟨_, _, h3, _⟩
          · exact h2
          · simp [Heap.isInst, h3, clsRuntime]
        have hc : aclose c ac fuel fixFuel x frameExc = .ok (x2, .error e) := by
          simp [aclose, he, bind, Except.bind, pure, Except.pure, coBoundary, hne]
        rw [hc]
        exact ⟨hs, p, hp, hl⟩

/-- `AsyncExitStack.__aexit__` terminates for every exception a callback raises. Refuted like
`ExitStackTerminates`: the copy of `_fix_exception_context` at Lib/contextlib.py:768-780 has the
same `while 1`, and an awaited callback raising an exception whose `__context__` chain is a cycle
keeps it running. -/
def AExitTerminates : Prop :=
  ∀ (σ F O A : Type) (c ac : Calls σ F O A) (x : Xs σ F O A) (exc frameExc : Option ExcId),
    ∃ fuel fixFuel, aexit c ac fuel fixFuel x exc frameExc ≠ .error .modelFuel

theorem aExitTerminates_refuted : ¬AExitTerminates := by
  intro h
  obtain ⟨fuel, fixFuel, hne⟩ := h Unit Unit Unit Unit cycleCalls cycleCalls
    ({ h := cycleHeap, g := () }, [(false, .raw ())]) none none
  apply hne
  cases fuel with
  | zero => rfl
  | succ f =>
    have hf := fix_cycle fixFuel 0 (.inl rfl)
    simp [aexit, aexitLoop, Cb.acall, Cb.call, cycleCalls, hf, bind, Except.bind]

/-- `AsyncExitStack.__aexit__` does not create a `__context__` cycle when the callbacks do not.
Refuted by the counterexample of `ExitKeepsContextAcyclic` with both callbacks awaited. -/
def AExitKeepsContextAcyclic : Prop :=
  ∀ (σ F O A : Type) (c ac : Calls σ F O A) (fuel fixFuel : Nat) (x x' : Xs σ F O A)
    (exc frameExc : Option ExcId) (r : Res Bool),
    (∀ k : Calls σ F O A, k = c ∨ k = ac →
      (∀ f (y : Xs σ F O A) d, (k.raw f y d).1.1.h = y.1.h) ∧
      (∀ m o (y : Xs σ F O A) d, (k.bound m o y d).1.1.h = y.1.h) ∧
      (∀ f a (y : Xs σ F O A), (k.wrapped f a y).1.1.h = y.1.h)) →
    Acyclic x.1.h → aexit c ac fuel fixFuel x exc frameExc = .ok (x', r) → Acyclic x'.1.h

theorem aExitKeepsContextAcyclic_refuted : ¬AExitKeepsContextAcyclic := by
  intro h
  have hacy : Acyclic fbaHeap := by
    intro e
    refine ⟨4, ?_⟩
    match e with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | _ + 3 => rfl
  have hrun : aexit fbaCalls fbaCalls 3 5
      ({ h := fbaHeap, g := () }, [(false, .raw 0), (false, .raw 1)]) (some 0) (some 0) =
      .ok (({ h := [{ cls := clsExc }, { cls := clsExc, context := some 2 },
        { cls := clsExc, context := some 1 }], g := () }, []), .error 1) := by
    rfl
  have := h Unit Nat Unit Unit fbaCalls fbaCalls 3 5 _ _ (some 0) (some 0) _
    (by
      intro k hk
      rcases hk with rfl | rfl <;> exact ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩)
    hacy hrun
  obtain ⟨n, hn⟩ := this 1
  rw [chainEnds_set 1 n (.inl rfl)] at hn
  cases hn

end PyLean.CoreLibs.Misc.Contextlib
