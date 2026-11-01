import PyLean.CoreLibs.Misc.Contextlib.Model

/-!
Properties of `Lib/contextlib.py`. A generator is any `GenOps`, so the case analysis of `__exit__`
is proved for every generator, not for one script. `cfg` ranges over `syncCfg` and `asyncCfg`.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

variable {σ V : Type}

/-! ### Abstract base classes -/

/-- `AbstractContextManager`: `__enter__` returns `self`, `__exit__` returns `None` so an exception
propagates, and `__subclasshook__` on the class itself is `True` exactly when both methods are found
along the MRO and the nearest definition is not `None`; on a subclass it is `NotImplemented`.
`AbstractAsyncContextManager` is the same with its method names. -/
def AbstractBases : Prop :=
  ∀ (O : Type) (self : O) (e : Option ExcId) (ms : List String) (mro : MroDicts),
    absEnter self = self ∧ absExit self e = none ∧
    (subclasshook true ms mro = some true ↔ ∀ m ∈ ms, checkMethod mro m = true) ∧
    (¬(∀ m ∈ ms, checkMethod mro m = true) → subclasshook true ms mro = none) ∧
    subclasshook false ms mro = none

theorem abstractBases_proven : AbstractBases := by
  intro O self e ms mro
  refine ⟨rfl, rfl, ?_, ?_, rfl⟩
  · simp [subclasshook]
  · intro h
    have : ¬ (ms.all (checkMethod mro) = true) := by simpa using h
    simp [subclasshook, this]

/-- `None` in the class body hides an inherited method: a class that sets `__exit__ = None` is no
context manager even if a base defines it. -/
def SubclassHookNone : Prop :=
  ∀ (d : List (String × Bool)) (rest : MroDicts) (m : String),
    d.lookup m = some true → checkMethod (d :: rest) m = false

theorem subclassHookNone_proven : SubclassHookNone := by
  intro d rest m h
  simp [checkMethod, List.findSome?, h]

/-! ### `ContextDecorator` -/

/-- A `ContextDecorator` "enables context managers to work as decorators": `_recreate_cm` returns
`self`, and calling the decorated function is the function's body inside `with self._recreate_cm():`.
When creating the context manager fails, the function does not run. -/
def DecoratorIsWith : Prop :=
  ∀ (σ V R C : Type) (c : C) (toCM : C → CM σ V) (func : St σ → St σ × Res R) (s : St σ) (e : ExcId),
    ContextDecorator.recreateCm c = c ∧
    ContextDecorator.call (fun s => (s, .ok (ContextDecorator.recreateCm c))) toCM func s =
      withStmt (toCM c) (fun _ s => func s) s ∧
    ContextDecorator.call (C := C) (fun s => (s, .error e)) toCM func s = (s, .error e)

theorem decoratorIsWith_proven : DecoratorIsWith := fun _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl⟩

/-! ### `@contextmanager` -/

/-- `_recreate_cm` of a generator context manager: while `func`, `args`, `kwds` are there it makes a
fresh one, which is what lets the decorated function run many times. After `__enter__` deleted them
it is `AttributeError`, not a second use of an exhausted generator. `__init__` takes `__doc__` from
`func` when it has one and from the class otherwise. `contextmanager` starts live. -/
def RecreateFresh : Prop :=
  ∀ (σ : Type) (name : String) (fresh : St σ → St σ × Res Unit) (s s' : St σ)
    (doc cdoc : Option String) (d : String),
    (fresh s = (s', .ok ()) → gcmRecreate name contextmanager fresh s = (s', .ok contextmanager)) ∧
    (∀ e, fresh s = (s', .error e) → gcmRecreate name contextmanager fresh s = (s', .error e)) ∧
    ((gcmRecreate name { live := false } fresh s).2 =
      .error (s.raiseNew clsAttr s!"'{name}' object has no attribute 'func'").2) ∧
    gcmDoc (some d) cdoc = some d ∧ gcmDoc none cdoc = cdoc ∧
    contextmanager.live = true

theorem recreateFresh_proven : RecreateFresh := by
  intro σ name fresh s s' doc cdoc d
  refine ⟨?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro h; simp [gcmRecreate, contextmanager, h]
  · intro e h; simp [gcmRecreate, contextmanager, h]

/-- `__enter__`: the value the generator yields is the value of the `with` target; a generator that
stops at once gives `RuntimeError("generator didn't yield")` with the `StopIteration` as context; any
other exception comes through; a second `__enter__` raises `AttributeError`, because the instance is
one-shot. -/
def EnterCases : Prop :=
  ∀ (σ V : Type) (cfg : Cfg) (ops : GenOps σ V) (name : String) (s s' : St σ) (v : V) (e : ExcId),
    (ops.next s = (s', .ok v) → gcmEnter cfg ops name contextmanager s = ({ live := false }, s', .ok v)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e cfg.stop = true →
      gcmEnter cfg ops name contextmanager s =
        let (s2, x) := s'.raiseNew clsRuntime "generator didn't yield" (some e)
        ({ live := false }, s2, .error x)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e cfg.stop = false →
      gcmEnter cfg ops name contextmanager s = ({ live := false }, s', .error e)) ∧
    (gcmEnter cfg ops name { live := false } s).1 = { live := false } ∧
    (gcmEnter cfg ops name { live := false } s).2.1.g = s.g

theorem enterCases_proven : EnterCases := by
  intro σ V cfg ops name s s' v e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [gcmEnter, contextmanager, h]
  · intro h1 h2; simp [gcmEnter, contextmanager, h1, h2]
  · intro h1 h2; simp [gcmEnter, contextmanager, h1, h2]
  · simp [gcmEnter]
  · simp [gcmEnter, St.raiseNew]

/-- `__exit__(None, None, None)`: a generator that finishes gives `False`; one that yields again is
closed and gives `RuntimeError("generator didn't stop")`, chained to whatever is being handled; any
other exception from the generator comes through. -/
def ExitNoException : Prop :=
  ∀ (σ V : Type) (cfg : Cfg) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (v : V) (e : ExcId),
    (ops.next s = (s', .error e) → s'.h.isInst e cfg.stop = true →
      gcmExit cfg ops inst s none none none = (s', .ok false)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e cfg.stop = false →
      gcmExit cfg ops inst s none none none = (s', .error e)) ∧
    (ops.next s = (s', .ok v) →
      gcmExit cfg ops inst s none none none = raiseThenClose ops s' "generator didn't stop")

theorem exitNoException_proven : ExitNoException := by
  intro σ V cfg ops inst s s' v e
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2; simp [gcmExit, h1, h2]
  · intro h1 h2; simp [gcmExit, h1, h2]
  · intro h; simp [gcmExit, h]

/-- `__exit__(type, value, tb)` on every generator, branch by branch.
A generator that yields after `throw` is the `RuntimeError` of the source, after `close`.
A stop exception means the generator ended: it swallows `value`, unless the stop exception is `value`
itself, which `with` must then re-raise.
`value` coming back means "not suppressed": `__exit__` returns `False` and restores the traceback.
A `RuntimeError` caused by a `value` of the stop classes is PEP 479 wrapping `value`, which counts as
`value` coming back. Anything else is a new failure and is raised. -/
def ExitThrowCases : Prop :=
  ∀ (σ V : Type) (cfg : Cfg) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (c : Cls)
    (value : ExcId) (tb : Option Nat) (v : V) (exc : ExcId),
    let run := gcmExit cfg ops inst s (some c) (some value) tb
    (ops.throw s value = (s', .ok v) → run = raiseThenClose ops s' cfg.afterThrow) ∧
    (ops.throw s value = (s', .error exc) → s'.h.isInst exc cfg.stop = true →
      run = (s', .ok (decide (exc ≠ value)))) ∧
    (ops.throw s value = (s', .error value) → s'.h.isInst value cfg.stop = false →
      run = ({ s' with h := s'.h.setTb value tb }, .ok false)) ∧
    (ops.throw s value = (s', .error exc) → exc ≠ value → s'.h.isInst exc cfg.stop = false →
      s'.h.isInst exc "RuntimeError" = true → s'.h.isInstAny value cfg.wrapped = true →
      (s'.h.get exc).cause = some value →
      run = ({ s' with h := s'.h.setTb value tb }, .ok false)) ∧
    (ops.throw s value = (s', .error exc) → exc ≠ value → s'.h.isInst exc cfg.stop = false →
      (s'.h.isInst exc "RuntimeError" = false ∨ s'.h.isInstAny value cfg.wrapped = false ∨
        (s'.h.get exc).cause ≠ some value) →
      run = (s', .error exc))

theorem exitThrowCases_proven : ExitThrowCases := by
  intro σ V cfg ops inst s s' c value tb v exc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [gcmExit, h]
  · intro h1 h2; simp [gcmExit, h1, h2]
  · intro h1 h2
    simp only [gcmExit, h1, h2]
    cases h3 : s'.h.isInst value "RuntimeError" <;> simp
  · intro h1 h2 h3 h4 h5 h6
    simp [gcmExit, h1, h2, h3, h4, h5, h6]
  · intro h1 h2 h3 h4
    simp only [gcmExit, h1, h2, Bool.false_eq_true, if_false, h3, decide_true, ne_eq,
      if_true, not_false_eq_true]
    rcases h4 with h4 | h4 | h4
    · simp [h4]
    · simp [h4, h3]
    · cases hr : s'.h.isInst exc "RuntimeError" <;> simp [h3, h4]

/-- "`__exit__()` must not raise an exception unless `__exit__()` itself failed" (Lib/contextlib.py
:188-189): on every generator whose `close()` does not itself raise `value`, `__exit__` never
raises the exception passed in. A `with` statement then re-raises it with the original traceback. -/
def ExitNeverRaisesValue : Prop :=
  ∀ (σ V : Type) (cfg : Cfg) (ops : GenOps σ V) (inst : Instantiate σ) (s : St σ) (c : Cls)
    (value : ExcId) (tb : Option Nat),
    (∀ s0 h, ∀ s1, ops.close s0 h = (s1, .error value) → False) →
    (∀ s0, value < s0.h.length → value < (ops.throw s0 value).1.h.length) →
    value < s.h.length →
    ∀ r, gcmExit cfg ops inst s (some c) (some value) tb = r → r.2 ≠ .error value

theorem exitNeverRaisesValue_proven : ExitNeverRaisesValue := by
  intro σ V cfg ops inst s c value tb hclose hlen hv r hr
  subst hr
  have hl := hlen s hv
  generalize hth : ops.throw s value = th at hl
  obtain ⟨s', tr⟩ := th
  simp only at hl
  simp only [gcmExit, hth]
  cases tr with
  | ok v =>
    simp only [raiseThenClose]
    generalize hn : s'.raiseNew clsRuntime cfg.afterThrow (ops.handled s') = n
    obtain ⟨s2, rt⟩ := n
    have hrt : rt ≠ value := by
      have h2 : rt = s'.h.length := by
        have := congrArg Prod.snd hn
        simpa [St.raiseNew, Heap.alloc] using this.symm
      rw [h2]
      exact Nat.ne_of_gt hl
    cases hc : ops.close s2 (some rt) with
    | mk s3 cr =>
      cases cr with
      | ok u => simp; exact hrt
      | error e =>
        simp only
        intro heq
        have : e = value := by simpa using heq
        subst this
        exact hclose s2 (some rt) s3 hc
  | error exc =>
    simp only
    by_cases hev : exc = value
    · subst hev
      simp only [ne_eq, not_true_eq_false, if_true, if_false]
      split
      · simp
      · split <;> simp
    · simp only [hev, if_false, ne_eq, not_false_eq_true, if_true]
      split
      · simp
      · split
        · split
          · simp
          · simpa using hev
        · simpa using hev

/-- The docstring of `contextmanager`: with a generator that yields once and then finishes,
`with g(): body` behaves as `<setup>; try: body finally: <cleanup>`: a normal body gives its result,
and a body that raises `e` lets the generator re-raise it after cleanup, and the `with` statement
raises the same object `e`. -/
def ContextmanagerTryFinally : Prop :=
  ∀ (σ V R : Type) (cfg : Cfg) (ops : GenOps σ V) (inst : Instantiate σ) (name : String)
    (body : V → St σ → St σ × Res R) (s s1 s2 s3 : St σ) (v : V) (r : R) (e stop : ExcId),
    let cm : CM σ V :=
      { enter := fun s => (gcmEnter cfg ops name contextmanager s).2
        exit := fun s x => match x with
          | none => gcmExit cfg ops inst s none none none
          | some ex => gcmExit cfg ops inst s (some (s.h.get ex).cls) (some ex) (s.h.get ex).tb }
    ops.next s = (s1, .ok v) →
    (body v s1 = (s2, .ok r) → ops.next s2 = (s3, .error stop) → s3.h.isInst stop cfg.stop = true →
      withStmt cm body s = (s3, .ok (some r))) ∧
    (body v s1 = (s2, .error e) → ops.throw s2 e = (s3, .error e) →
      s3.h.isInst e cfg.stop = false →
      (withStmt cm body s).2 = .error e)

theorem contextmanagerTryFinally_proven : ContextmanagerTryFinally := by
  intro σ V R cfg ops inst name body s s1 s2 s3 v r e stop cm h1
  constructor
  · intro h2 h3 h4
    simp [withStmt, cm, gcmEnter, contextmanager, h1, h2, gcmExit, h3, h4]
  · intro h2 h3 h4
    simp only [withStmt, cm, gcmEnter, contextmanager, h1, Bool.not_true, Bool.false_eq_true,
      if_false, h2, gcmExit, h3, h4]
    cases hr : s3.h.isInst e "RuntimeError" <;> simp

/-- The async twin. For the same generator behaviour, `__aexit__` and `__exit__` differ only by
`Cfg`: when neither `value` nor what the generator raises is a stop exception, they do the same, and
`__aenter__` is `__enter__` when what comes out is not `StopIteration`. A `throw` that yields gives
the message with `athrow`. -/
def AsyncTwinExit : Prop :=
  ∀ (σ V : Type) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (c : Cls) (value exc : ExcId)
    (tb : Option Nat),
    ops.throw s value = (s', .error exc) →
    s'.h.isInst exc "StopIteration" = false → s'.h.isInst exc "StopAsyncIteration" = false →
    s'.h.isInst value "StopIteration" = false → s'.h.isInst value "StopAsyncIteration" = false →
    agcmExit ops inst s (some c) (some value) tb = gcmExit syncCfg ops inst s (some c) (some value) tb

theorem asyncTwinExit_proven : AsyncTwinExit := by
  intro σ V ops inst s s' c value exc tb h1 h2 h3 h4 h5
  have hwa : s'.h.isInstAny value asyncCfg.wrapped = false := by
    simp [Heap.isInstAny, asyncCfg, h4, h5]
  have hws : s'.h.isInstAny value syncCfg.wrapped = false := by
    simp [Heap.isInstAny, syncCfg, h4]
  have hstopA : asyncCfg.stop = "StopAsyncIteration" := rfl
  have hstopS : syncCfg.stop = "StopIteration" := rfl
  simp only [agcmExit, gcmExit, h1, hstopA, hstopS, h2, h3, hwa, hws]
  by_cases hrt : s'.h.isInst exc "RuntimeError" = true
  · by_cases hev : exc = value
    · subst hev
      simp [hrt, coBoundary]
    · simp [hrt, hev, coBoundary, h2]
  · by_cases hev : exc = value
    · subst hev
      simp [hrt, coBoundary]
    · simp [hrt, hev, coBoundary, h2]

/-! ### `closing`, `nullcontext`, `_RedirectStream`, `chdir` -/

/-- `closing`, `aclosing`: `with closing(x) as y` binds `x` itself, calls `close()` exactly once
whatever the body does, and suppresses nothing: "`f = ...; try: <block> finally: f.close()`". -/
def ClosingOnce : Prop :=
  ∀ (R T : Type) (thing : T) (body : T → St Nat → St Nat × Res R) (s s1 : St Nat) (e : ExcId) (r : R),
    let closeF : St Nat → St Nat × Res Unit := fun s => ({ s with g := s.g + 1 }, .ok ())
    let cm : CM Nat T :=
      { enter := fun s => (s, .ok (closingEnter thing)), exit := fun s _ => closingExit closeF s }
    (body thing s = (s1, .ok r) → withStmt cm body s = ({ s1 with g := s1.g + 1 }, .ok (some r))) ∧
    (body thing s = (s1, .error e) → withStmt cm body s = ({ s1 with g := s1.g + 1 }, .error e))

theorem closingOnce_proven : ClosingOnce := by
  intro R T thing body s s1 e r closeF cm
  constructor
  · intro h; simp [withStmt, cm, closingEnter, closeF, closingExit, h]
  · intro h; simp [withStmt, cm, closingEnter, closeF, closingExit, h]

/-- `nullcontext` "does no additional processing": `with nullcontext(v) as x: body` is `body` with
`x = v`, value or exception, in the sync and the async form. -/
def NullcontextTransparent : Prop :=
  ∀ (σ T R : Type) (v : T) (body : T → St σ → St σ × Res R) (s : St σ),
    let cm : CM σ T :=
      { enter := fun s => (s, .ok (nullEnter v)), exit := fun s e => (s, .ok (nullExit e)) }
    withStmt cm body s =
      (match body v s with
       | (s, .ok r) => (s, .ok (some r))
       | (s, .error e) => (s, .error e))

theorem nullcontextTransparent_proven : NullcontextTransparent := by
  intro σ T R v body s cm
  simp only [withStmt, cm, nullEnter, nullExit]
  generalize body v s = r
  obtain ⟨s', x⟩ := r
  cases x <;> rfl

/-- `redirect_stdout` and `redirect_stderr` are re-entrant: `__enter__` installs the new target and
returns it, and the matching `__exit__` restores exactly the stream that was current and the state of
the object. `__exit__` without `__enter__` is `IndexError` from the empty list. -/
def RedirectRestores : Prop :=
  ∀ (S : Type) (r : Redirect S) (cur : S),
    (r.enter cur).2.1 = r.newTarget ∧ (r.enter cur).2.2 = r.newTarget ∧
    (r.enter cur).1.exit = some (r, cur) ∧
    ((Redirect.init cur).exit = none) ∧ (Redirect.init cur).oldTargets = []

theorem redirectRestores_proven : RedirectRestores := by
  intro S r cur
  refine ⟨rfl, rfl, ?_, rfl, rfl⟩
  simp [Redirect.enter, Redirect.exit]

/-- `chdir`: the matching `__exit__` goes back to the directory `__enter__` found, also when several
`__enter__` calls on one object nest, as long as that directory still works. When `os.chdir` fails in
`__enter__`, the exception propagates, the cwd stays, and the saved directory stays on the stack,
because it was pushed first. -/
def ChdirRestores : Prop :=
  ∀ (P E : Type) (f : P → P → Except E P) (c : Chdir P) (cwd new : P) (e : E),
    (f c.path cwd = .ok new → f cwd new = .ok cwd →
      (c.enter f cwd).1.exit f (c.enter f cwd).2.1 = some (c, cwd, .ok ())) ∧
    (f c.path cwd = .error e →
      c.enter f cwd = ({ c with oldCwd := c.oldCwd ++ [cwd] }, cwd, .error e)) ∧
    (Chdir.init c.path).oldCwd = []

theorem chdirRestores_proven : ChdirRestores := by
  intro P E f c cwd new e
  refine ⟨?_, ?_, rfl⟩
  · intro h1 h2
    simp [Chdir.enter, Chdir.exit, h1, h2]
  · intro h
    simp [Chdir.enter, h]

/-! ### `suppress` -/

/-- `suppress.__exit__` on a plain exception, or no exception: nothing to do for `None`, `True` for a
listed class, `False` otherwise. `__enter__` returns `None`. -/
def SuppressPlain : Prop :=
  ∀ (σ : Type) (cs : List String) (s : St σ) (handled : Option ExcId) (e : ExcId),
    suppressExit cs s handled none = (s, .ok none) ∧
    (s.h.isInstAny e cs = true → suppressExit cs s handled (some e) = (s, .ok (some true))) ∧
    (s.h.isInstAny e cs = false → s.h.isInst e "BaseExceptionGroup" = false →
      suppressExit cs s handled (some e) = (s, .ok (some false))) ∧
    suppressEnter = ()

theorem suppressPlain_proven : SuppressPlain := by
  intro σ cs s handled e
  refine ⟨rfl, ?_, ?_, rfl⟩
  · intro h; simp [suppressExit, h]
  · intro h1 h2; simp [suppressExit, h1, h2]

/-- A group's members being leaves: no nested group. -/
def Flat (h : Heap) (excs : List ExcId) : Prop := ∀ e ∈ excs, (h.get e).children = none

theorem split_fold_flat (cs : List String) (fuel : Nat) (h : Heap) (excs : List ExcId)
    (hf : Flat h excs) : ∀ (ms rs : List ExcId),
    excs.foldl
      (fun (st : Heap × List ExcId × List ExcId) e =>
        let x := splitRec cs fuel st.1 e
        (x.1, st.2.1 ++ x.2.1.toList, st.2.2 ++ x.2.2.toList)) (h, ms, rs) =
    (h, ms ++ excs.filter (fun e => h.isInstAny e cs),
      rs ++ excs.filter (fun e => !h.isInstAny e cs)) ∨ fuel = 0 := by
  intro ms rs
  cases fuel with
  | zero => exact .inr rfl
  | succ f =>
    left
    induction excs generalizing ms rs with
    | nil => simp
    | cons e rest ih =>
      have hc : (h.get e).children = none := hf e (by simp)
      have hr : Flat h rest := fun x hx => hf x (by simp [hx])
      simp only [List.foldl_cons]
      by_cases hm : h.isInstAny e cs = true
      · have : splitRec cs (f + 1) h e = (h, some e, none) := by
          simp [splitRec, matches', hm]
        simp only [this, Option.toList_some, Option.toList_none, List.append_nil]
        rw [ih hr (ms ++ [e]) rs]
        simp [hm]
      · have hm' : h.isInstAny e cs = false := by simpa using hm
        have : splitRec cs (f + 1) h e = (h, none, some e) := by
          simp [splitRec, matches', hm', hc]
        simp only [this, Option.toList_some, Option.toList_none, List.append_nil]
        rw [ih hr ms (rs ++ [e])]
        simp [hm']

/-- `suppress` on a flat exception group, as documented ("suppressed exceptions are removed from the
group. Any exceptions of the group which are not suppressed are re-raised in a new group which is
created using the original group's derive() method"). When every member matches, the group is
suppressed. Otherwise a new group object is raised, whose members are the unsuppressed ones in order
and whose message, cause and traceback are the original's. That holds when no member matches: the
exception that leaves the `with` is then a new object, not the original. -/
def SuppressGroup : Prop :=
  ∀ (σ : Type) (cs : List String) (s : St σ) (e : ExcId) (excs : List ExcId) (handled : Option ExcId),
    e < s.h.length → s.h.isInstAny e cs = false → s.h.isInst e "BaseExceptionGroup" = true →
    (s.h.get e).children = some excs → Flat s.h excs →
    (excs.all (fun x => s.h.isInstAny x cs) = true →
      (suppressExit cs s handled (some e)).2 = .ok (some true)) ∧
    (excs.all (fun x => s.h.isInstAny x cs) = false →
      ∃ r, (suppressExit cs s handled (some e)).2 = .error r ∧ r ≠ e ∧
        ((suppressExit cs s handled (some e)).1.h.get r).children =
          some (excs.filter (fun x => !s.h.isInstAny x cs)) ∧
        ((suppressExit cs s handled (some e)).1.h.get r).msg = (s.h.get e).msg ∧
        ((suppressExit cs s handled (some e)).1.h.get r).cause = (s.h.get e).cause ∧
        ((suppressExit cs s handled (some e)).1.h.get r).tb = (s.h.get e).tb)

/-- Two exception objects with the same class data; only `__context__` may differ. -/
def SameData (a b : ExcObj) : Prop :=
  a.children = b.children ∧ a.msg = b.msg ∧ a.cause = b.cause ∧ a.tb = b.tb

theorem SameData.refl (a : ExcObj) : SameData a a := ⟨rfl, rfl, rfl, rfl⟩

theorem SameData.trans {a b c : ExcObj} (h1 : SameData a b) (h2 : SameData b c) : SameData a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.trans h2.2.2.2⟩

theorem setContext_same (h : Heap) (a : ExcId) (c : Option ExcId) (r : ExcId) :
    SameData ((h.setContext a c).get r) (h.get r) := by
  simp only [Heap.setContext, Heap.modify, Heap.get]
  by_cases har : a = r
  · subst har
    by_cases hl : a < h.length
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hl)]
      exact SameData.refl _
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne har, ← List.getD_eq_getElem?_getD]
    exact SameData.refl _

theorem breakCycle_same (value : ExcId) (r : ExcId) :
    ∀ (fuel : Nat) (h : Heap) (o slow : ExcId) (t : Bool),
      SameData ((Heap.breakCycle value fuel h o slow t).get r) (h.get r) := by
  intro fuel
  induction fuel with
  | zero => intro h o slow t; exact SameData.refl _
  | succ f ih =>
    intro h o slow t
    simp only [Heap.breakCycle]
    split
    · exact SameData.refl _
    · split
      · exact setContext_same _ _ _ _
      · split
        · exact SameData.refl _
        · exact ih _ _ _ _

theorem raiseCtx_same (h : Heap) (value : ExcId) (handled : Option ExcId) (r : ExcId) :
    SameData ((h.raiseCtx value handled).get r) (h.get r) := by
  unfold Heap.raiseCtx
  split
  · exact SameData.refl _
  · split
    · exact SameData.refl _
    · exact (setContext_same _ _ _ _).trans (breakCycle_same _ _ _ _ _ _ _)

theorem get_alloc_lt (h : Heap) (o : ExcObj) (r : ExcId) (hr : r < h.length) :
    (h.alloc o).1.get r = h.get r := by
  simp [Heap.alloc, Heap.get, List.getD_eq_getElem?_getD, List.getElem?_append_left hr]

theorem get_alloc_last (h : Heap) (o : ExcObj) : (h.alloc o).1.get (h.alloc o).2 = o := by
  simp [Heap.alloc, Heap.get, List.getD_eq_getElem?_getD]

theorem subset_get (h : Heap) (orig : ExcId) (excs : List ExcId) (r : ExcId) (hr : r < h.length) :
    (subset h orig excs).1.get r = h.get r ∧ h.length ≤ (subset h orig excs).1.length := by
  unfold subset
  split
  · exact ⟨rfl, Nat.le_refl _⟩
  · refine ⟨get_alloc_lt _ _ _ hr, ?_⟩
    simp [Heap.alloc]

theorem suppressGroup_proven : SuppressGroup := by
  intro σ cs s e excs handled hl hm hg hc hf
  have hfold := split_fold_flat cs (2 * s.h.length + 1) s.h excs hf [] []
  have hfold' := hfold.resolve_right (by omega)
  simp only [List.nil_append] at hfold'
  let ms := excs.filter (fun x => s.h.isInstAny x cs)
  let rs := excs.filter (fun x => !s.h.isInstAny x cs)
  have hsplit : split cs s.h e =
      (let (h1, m) := subset s.h e ms
       let (h2, r) := subset h1 e rs
       (h2, m, r)) := by
    show splitRec cs ((2 * s.h.length + 1) + 1) s.h e = _
    rw [splitRec]
    have hm' : matches' s.h e cs = false := hm
    simp only [hm', Bool.false_eq_true, if_false, hc]
    rw [hfold']
  have hrun : suppressExit cs s handled (some e) =
      (match (subset (subset s.h e ms).1 e rs).2 with
       | none => ({ s with h := (subset (subset s.h e ms).1 e rs).1 }, .ok (some true))
       | some r =>
        ({ s with h := (subset (subset s.h e ms).1 e rs).1.raiseCtx r handled }, .error r)) := by
    simp only [suppressExit, hm, Bool.false_eq_true, if_false, hg, if_true, hsplit]
    cases (subset (subset s.h e ms).1 e rs).2 <;> rfl
  constructor
  · intro hall
    have hrs : rs = [] := by
      apply List.filter_eq_nil_iff.2
      intro x hx
      have := List.all_eq_true.1 hall x hx
      simp [this]
    rw [hrun, hrs]
    simp [subset]
  · intro hnot
    have hrs : rs ≠ [] := by
      intro hrs
      have h0 := List.filter_eq_nil_iff.1 hrs
      have : excs.all (fun x => s.h.isInstAny x cs) = true := by
        apply List.all_eq_true.2
        intro x hx
        simpa using h0 x hx
      rw [this] at hnot
      cases hnot
    let h1 := (subset s.h e ms).1
    have hg1 : h1.get e = s.h.get e := (subset_get s.h e ms e hl).1
    have hlen1 : s.h.length ≤ h1.length := (subset_get s.h e ms e hl).2
    have hne : rs.isEmpty = false := by
      cases hr : rs with
      | nil => exact absurd hr hrs
      | cons a b => rfl
    let o : ExcObj :=
      { cls := deriveCls h1 rs, msg := (h1.get e).msg, context := (h1.get e).context,
        cause := (h1.get e).cause, tb := (h1.get e).tb, children := some rs }
    have hr2 : (subset h1 e rs).2 = some h1.length := by
      simp [subset, hne, Heap.alloc]
    have hh2 : (subset h1 e rs).1 = (h1.alloc o).1 := by
      simp [subset, hne, Heap.alloc, o]
    have hres : suppressExit cs s handled (some e) =
        ({ s with h := (h1.alloc o).1.raiseCtx h1.length handled }, .error h1.length) := by
      rw [hrun]
      simp only [show (subset s.h e ms).1 = h1 from rfl, hr2, hh2]
    rw [hres]
    have hs := raiseCtx_same (h1.alloc o).1 h1.length handled h1.length
    have hlast : (h1.alloc o).1.get h1.length = o := get_alloc_last h1 o
    rw [hlast] at hs
    obtain ⟨a1, a2, a3, a4⟩ := hs
    have hne' : h1.length ≠ e := Nat.ne_of_gt (Nat.lt_of_lt_of_le hl hlen1)
    refine ⟨h1.length, rfl, hne', a1, ?_, ?_, ?_⟩
    · simp only
      rw [a2]
      simp [o, hg1]
    · simp only
      rw [a3]
      simp [o, hg1]
    · simp only
      rw [a4]
      simp [o, hg1]

end PyLean.CoreLibs.Misc.Contextlib
