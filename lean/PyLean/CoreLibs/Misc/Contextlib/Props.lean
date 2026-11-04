import PyLean.CoreLibs.Misc.Contextlib.Model

/-!
Properties of `Lib/contextlib.py`. A generator is any `GenOps`, so the case analysis of `__exit__`
is proved for every generator, not for one script. `cfg` ranges over `syncCfg` and `asyncCfg`.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

variable {σ V : Type}

/-! ### Abstract base classes -/

/-- `AbstractContextManager.__subclasshook__` on the class itself is `True` exactly when both
methods are found along the MRO and the nearest definition is not `None`; otherwise, and on a
subclass, it is `NotImplemented`. `AbstractAsyncContextManager` is the same with its method names. -/
def AbstractBases : Prop :=
  ∀ (ms : List String) (mro : MroDicts),
    (subclasshook true ms mro = some true ↔ ∀ m ∈ ms, checkMethod mro m = true) ∧
    (¬(∀ m ∈ ms, checkMethod mro m = true) → subclasshook true ms mro = none) ∧
    subclasshook false ms mro = none

theorem abstractBases_proven : AbstractBases := by
  intro ms mro
  refine ⟨?_, ?_, rfl⟩
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

/-- A `ContextDecorator` "enables context managers to work as decorators": the decorated plain
function behaves as its body in `with self._recreate_cm():`. Its value comes
back after `__exit__`; an exception comes back when `__exit__` is false and gives `None` when it is
true; `__exit__` failing replaces the result; and when `__enter__` or creating the manager fails, the
function does not run. -/
def DecoratorIsWith : Prop :=
  ∀ (σ V R C : Type) (c : C) (toCM : C → CM σ V) (func : St σ → St σ × Res R)
    (s s1 s2 s3 : St σ) (v : V) (r : R) (e e2 : ExcId),
    let rec_ : St σ → St σ × Res C := fun s => (s, .ok c)
    (ContextDecorator.call (C := C) (R := R) (fun s => (s, .error e)) toCM func s = (s, .error e)) ∧
    ((toCM c).enter s = (s1, .error e) →
      ContextDecorator.call rec_ toCM func s = (s1, .error e)) ∧
    ((toCM c).enter s = (s1, .ok v) → func s1 = (s2, .ok r) → ∀ b, (toCM c).exit s2 none = (s3, .ok b) →
      ContextDecorator.call rec_ toCM func s = (s3, .ok (some r))) ∧
    ((toCM c).enter s = (s1, .ok v) → func s1 = (s2, .error e) →
      (toCM c).exit s2 (some e) = (s3, .ok false) →
      ContextDecorator.call rec_ toCM func s = (s3, .error e)) ∧
    ((toCM c).enter s = (s1, .ok v) → func s1 = (s2, .error e) →
      (toCM c).exit s2 (some e) = (s3, .ok true) →
      ContextDecorator.call rec_ toCM func s = (s3, .ok none)) ∧
    ((toCM c).enter s = (s1, .ok v) → func s1 = (s2, .error e) →
      (toCM c).exit s2 (some e) = (s3, .error e2) →
      ContextDecorator.call rec_ toCM func s = (s3, .error e2))

theorem decoratorIsWith_proven : DecoratorIsWith := by
  intro σ V R C c toCM func s s1 s2 s3 v r e e2 rec_
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [ContextDecorator.call, rec_, withStmt, h]
  · intro h1 h2 b h3
    cases b <;> simp [ContextDecorator.call, rec_, withStmt, h1, h2, h3]
  · intro h1 h2 h3
    simp [ContextDecorator.call, rec_, withStmt, h1, h2, h3]
  · intro h1 h2 h3
    simp [ContextDecorator.call, rec_, withStmt, h1, h2, h3]
  · intro h1 h2 h3
    simp [ContextDecorator.call, rec_, withStmt, h1, h2, h3]

/-! ### `@contextmanager` -/

/-- `__init__` of a generator context manager: `func(*args, **kwds)` runs first and its failure is
the result; then `__doc__` is `func.__doc__` unless that is `None` or missing (`AttributeError`),
when it is the class's; any other exception from the lookup propagates. The object starts live:
`func`, `args` and `kwds` are stored. -/
def GcmInitCases : Prop :=
  ∀ (σ D : Type) (call : St σ → St σ × Res Unit) (getDoc : St σ → St σ × Res (Option D))
    (cdoc : Option D) (s s1 s2 : St σ) (e : ExcId) (d : D),
    (call s = (s1, .error e) → gcmInit call getDoc cdoc s = (s1, .error e)) ∧
    (call s = (s1, .ok ()) → getDoc s1 = (s2, .ok (some d)) →
      gcmInit call getDoc cdoc s = (s2, .ok ({ live := true }, some d))) ∧
    (call s = (s1, .ok ()) → getDoc s1 = (s2, .ok none) →
      gcmInit call getDoc cdoc s = (s2, .ok ({ live := true }, cdoc))) ∧
    (call s = (s1, .ok ()) → getDoc s1 = (s2, .error e) → s2.h.isInst e "AttributeError" = true →
      gcmInit call getDoc cdoc s = (s2, .ok ({ live := true }, cdoc))) ∧
    (call s = (s1, .ok ()) → getDoc s1 = (s2, .error e) → s2.h.isInst e "AttributeError" = false →
      gcmInit call getDoc cdoc s = (s2, .error e))

theorem gcmInitCases_proven : GcmInitCases := by
  intro σ D call getDoc cdoc s s1 s2 e d
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [gcmInit, h]
  · intro h1 h2; simp [gcmInit, getattrDefault, h1, h2]
  · intro h1 h2; simp [gcmInit, getattrDefault, h1, h2]
  · intro h1 h2 h3; simp [gcmInit, getattrDefault, h1, h2, h3]
  · intro h1 h2 h3; simp [gcmInit, getattrDefault, h1, h2, h3]

/-- `_recreate_cm` of a generator context manager: while `func`, `args` and `kwds` are there it is
the class's `__init__` with them, which is what lets the decorated function run many times. After
`__enter__` deleted them, whatever `__enter__` did, it is `AttributeError` for `func`, raised while
`handled` is handled, and nothing else runs. -/
def RecreateFresh : Prop :=
  ∀ (σ V D : Type) (cfg : Cfg) (ops : GenOps σ V) (name ename : String)
    (init : St σ → St σ × Res (GCM × Option D)) (handled : Option ExcId) (self : GCM) (s s0 : St σ),
    gcmRecreate name { live := true } init handled s = init s ∧
    gcmRecreate name (gcmEnter cfg ops ename self s0).1 init handled s =
      (let (s', e) := s.raiseNew clsAttr s!"'{name}' object has no attribute 'func'" handled
       (s', .error e))

theorem recreateFresh_proven : RecreateFresh := by
  intro σ V D cfg ops name ename init handled self s s0
  refine ⟨rfl, ?_⟩
  have : (gcmEnter cfg ops ename self s0).1.live = false := by
    unfold gcmEnter
    split
    · rename_i h; simpa using h
    · split <;> (try split) <;> rfl
  simp only [gcmRecreate, this, Bool.false_eq_true, if_false]

/-- `__enter__`: the value the generator yields is the value of the `with` target; a generator that
stops at once gives `RuntimeError("generator didn't yield")` with the `StopIteration` as context; any
other exception comes through; a second `__enter__` raises `AttributeError`, because the instance is
one-shot. -/
def EnterCases : Prop :=
  ∀ (σ V : Type) (cfg : Cfg) (ops : GenOps σ V) (name : String) (s s' : St σ) (v : V) (e : ExcId),
    (ops.next s = (s', .ok v) → gcmEnter cfg ops name { live := true } s = ({ live := false }, s', .ok v)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e cfg.stop = true →
      gcmEnter cfg ops name { live := true } s =
        let (s2, x) := s'.raiseNew clsRuntime "generator didn't yield" (some e)
        ({ live := false }, s2, .error x)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e cfg.stop = false →
      gcmEnter cfg ops name { live := true } s = ({ live := false }, s', .error e)) ∧
    (gcmEnter cfg ops name { live := false } s).1 = { live := false } ∧
    (gcmEnter cfg ops name { live := false } s).2.1.g = s.g

theorem enterCases_proven : EnterCases := by
  intro σ V cfg ops name s s' v e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [gcmEnter, h]
  · intro h1 h2; simp [gcmEnter, h1, h2]
  · intro h1 h2; simp [gcmEnter, h1, h2]
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
:250-251): on every generator whose `close()` does not itself raise `value`, `__exit__` never
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

theorem gcmInit_live {σ D : Type} {call : St σ → St σ × Res Unit}
    {getDoc : St σ → St σ × Res (Option D)} {cdoc : Option D} {s0 s : St σ} {g : GCM}
    {doc : Option D} (h : gcmInit call getDoc cdoc s0 = (s, .ok (g, doc))) : g = { live := true } := by
  unfold gcmInit at h
  split at h
  · simp at h
  · split at h
    split at h
    · simp at h
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h; exact h.2.1.symm
    · simp only [Prod.mk.injEq, Except.ok.injEq] at h; exact h.2.1.symm

/-- The docstring of `contextmanager`: calling the decorated function calls `func` at once, and its
failure is the call's; the manager it returns behaves, with a generator that yields once and then
finishes, as `<setup>; try: body finally: <cleanup>`: a normal body gives its result, and a body
that raises `e` lets the generator re-raise it after cleanup, and the `with` statement raises the
same object `e`. -/
def ContextmanagerTryFinally : Prop :=
  ∀ (σ V R D : Type) (ops : GenOps σ V) (inst : Instantiate σ) (call : St σ → St σ × Res Unit)
    (getDoc : St σ → St σ × Res (Option D)) (cdoc : Option D) (body : V → St σ → St σ × Res R)
    (s0 s s1 s2 s3 : St σ) (v : V) (r : R) (e stop : ExcId),
    (call s0 = (s, .error e) → contextmanagerCall call getDoc cdoc s0 = (s, .error e)) ∧
    ∀ (g : GCM) (doc : Option D), contextmanagerCall call getDoc cdoc s0 = (s, .ok (g, doc)) →
    let cm : CM σ V :=
      { enter := fun s => (gcmEnter syncCfg ops "_GeneratorContextManager" g s).2
        exit := fun s x => match x with
          | none => gcmExit syncCfg ops inst s none none none
          | some ex => gcmExit syncCfg ops inst s (some (s.h.get ex).cls) (some ex) (s.h.get ex).tb }
    ops.next s = (s1, .ok v) →
    (body v s1 = (s2, .ok r) → ops.next s2 = (s3, .error stop) →
      s3.h.isInst stop "StopIteration" = true →
      withStmt cm body s = (s3, .ok (some r))) ∧
    (body v s1 = (s2, .error e) → ops.throw s2 e = (s3, .error e) →
      s3.h.isInst e "StopIteration" = false →
      (withStmt cm body s).2 = .error e)

theorem contextmanagerTryFinally_proven : ContextmanagerTryFinally := by
  intro σ V R D ops inst call getDoc cdoc body s0 s s1 s2 s3 v r e stop
  refine ⟨?_, ?_⟩
  · intro h; simp [contextmanagerCall, gcmInit, h]
  intro g doc hg cm h1
  have hl : g = { live := true } := gcmInit_live hg
  subst hl
  constructor
  · intro h2 h3 h4
    simp [withStmt, cm, gcmEnter, h1, h2, gcmExit, h3, h4, syncCfg]
  · intro h2 h3 h4
    simp only [withStmt, cm, gcmEnter, h1, Bool.not_true, Bool.false_eq_true,
      if_false, h2, gcmExit, h3, syncCfg, h4]
    cases hr : s3.h.isInst e "RuntimeError" <;> simp

/-- `__exit__(typ, None, tb)`: `value = typ()` runs first (Lib/contextlib.py:219-222). When the
instantiation raises, that exception is the result and the generator is not touched; otherwise
`__exit__` is what it is with the new instance as `value`, so the cases of `ExitThrowCases` apply
to it. -/
def ExitValueNone : Prop :=
  ∀ (σ V : Type) (cfg : Cfg) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (c : Cls)
    (tb : Option Nat) (e : ExcId),
    (inst s c = (s', .error e) → gcmExit cfg ops inst s (some c) none tb = (s', .error e)) ∧
    (inst s c = (s', .ok e) →
      gcmExit cfg ops inst s (some c) none tb = gcmExit cfg ops inst s' (some c) (some e) tb)

theorem exitValueNone_proven : ExitValueNone := by
  intro σ V cfg ops inst s s' c tb e
  constructor
  · intro h; simp [gcmExit, h]
  · intro h; simp [gcmExit, h]

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

/-! ### `closing`, `_RedirectStream`, `chdir` -/

/-- `closing`: "`with closing(f) as x: <block>` is equivalent to `f = ...; try: <block> finally:
f.close()`", for every behaviour of `close()`, which gets the exception in flight as the one being
handled. The target is `f` itself; `close` runs once, after the block; its exception replaces the
block's outcome; otherwise the block's value or exception (the same object) comes out, so nothing
is suppressed. -/
def ClosingTryFinally : Prop :=
  ∀ (σ R T : Type) (thing : T) (close : Option ExcId → St σ → St σ × Res Unit)
    (body : T → St σ → St σ × Res R) (s s1 s2 : St σ) (e e2 : ExcId) (r : R),
    let cm : CM σ T :=
      { enter := fun s => (s, .ok (closingEnter thing)), exit := fun s x => closingExit (close x) s }
    (body thing s = (s1, .ok r) → close none s1 = (s2, .ok ()) →
      withStmt cm body s = (s2, .ok (some r))) ∧
    (body thing s = (s1, .ok r) → close none s1 = (s2, .error e2) →
      withStmt cm body s = (s2, .error e2)) ∧
    (body thing s = (s1, .error e) → close (some e) s1 = (s2, .ok ()) →
      withStmt cm body s = (s2, .error e)) ∧
    (body thing s = (s1, .error e) → close (some e) s1 = (s2, .error e2) →
      withStmt cm body s = (s2, .error e2))

theorem closingTryFinally_proven : ClosingTryFinally := by
  intro σ R T thing close body s s1 s2 e e2 r cm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; simp [withStmt, cm, closingEnter, closingExit, h1, h2]
  · intro h1 h2; simp [withStmt, cm, closingEnter, closingExit, h1, h2]
  · intro h1 h2; simp [withStmt, cm, closingEnter, closingExit, h1, h2]
  · intro h1 h2; simp [withStmt, cm, closingEnter, closingExit, h1, h2]

/-- `redirect_stdout` and `redirect_stderr` are re-entrant: `__enter__` installs the new target and
returns it, and the matching `__exit__` restores exactly the stream that was current and the state of
the object. When `getattr(sys, stream)` fails, `__enter__` raises that, appends nothing and sets
nothing. A new object, `redirect_stdout(t)`, starts with no saved stream, so `__exit__` without
`__enter__` is `IndexError` from the empty list, and its first `__enter__` installs `t` and saves
only the current stream, which the matching `__exit__` gives back with the object as new. -/
def RedirectRestores : Prop :=
  ∀ (S E : Type) (r : Redirect S) (cur : S) (e : E) (t : S),
    (r.enter (.ok cur : Except E S)).2 = .ok (r.newTarget, r.newTarget) ∧
    ((r.enter (.ok cur : Except E S)).1.exit = some (r, cur)) ∧
    r.enter (.error e : Except E S) = (r, .error e) ∧
    ((Redirect.init t).exit = none) ∧
    (Redirect.init t).enter (.ok cur : Except E S) = ({ newTarget := t, oldTargets := [cur] }, .ok (t, t)) ∧
    ({ newTarget := t, oldTargets := [cur] } : Redirect S).exit = some (Redirect.init t, cur)

theorem redirectRestores_proven : RedirectRestores := by
  intro S E r cur e t
  refine ⟨rfl, ?_, rfl, rfl, rfl, rfl⟩
  simp [Redirect.enter, Redirect.exit]

/-- `chdir`: the matching `__exit__` goes back to the directory `__enter__` found, also when several
`__enter__` calls on one object nest, as long as that directory still works. When `os.getcwd()`
fails, `__enter__` raises that and pushes nothing. When `os.chdir` fails in `__enter__`, the
exception propagates, the cwd stays, and the saved directory stays on the stack, because it was
pushed first. `__exit__` pops before it calls `os.chdir`, so a failing `os.chdir` there leaves the
cwd and drops the entry; with an empty stack it is `IndexError`. A new object, `chdir(p)`, starts
with an empty stack, so `__exit__` alone is `IndexError`, and its first `__enter__` saves only the
current directory and goes to `p`, after which `__exit__` comes back with the object as new. -/
def ChdirRestores : Prop :=
  ∀ (P E : Type) (f : P → P → Except E P) (c : Chdir P) (cwd new old p : P) (e : E),
    (Chdir.init p).exit f cwd = none ∧
    (f p cwd = .ok new → (Chdir.init p).enter f (.ok cwd) cwd = ({ path := p, oldCwd := [cwd] }, new, .ok ())) ∧
    (f cwd new = .ok cwd →
      ({ path := p, oldCwd := [cwd] } : Chdir P).exit f new = some (Chdir.init p, cwd, .ok ())) ∧
    (f c.path cwd = .ok new → f cwd new = .ok cwd →
      (c.enter f (.ok cwd) cwd).1.exit f (c.enter f (.ok cwd) cwd).2.1 = some (c, cwd, .ok ())) ∧
    (c.enter f (.error e) cwd = (c, cwd, .error e)) ∧
    (f c.path cwd = .error e →
      c.enter f (.ok old) cwd = ({ c with oldCwd := c.oldCwd ++ [old] }, cwd, .error e)) ∧
    (c.oldCwd = [] → c.exit f cwd = none) ∧
    (c.oldCwd.getLast? = some old → f old cwd = .error e →
      c.exit f cwd = some ({ c with oldCwd := c.oldCwd.dropLast }, cwd, .error e))

theorem chdirRestores_proven : ChdirRestores := by
  intro P E f c cwd new old p e
  refine ⟨rfl, ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro h; simp [Chdir.init, Chdir.enter, h]
  · intro h; simp [Chdir.init, Chdir.exit, h]
  · intro h1 h2
    simp [Chdir.enter, Chdir.exit, h1, h2]
  · intro h
    simp [Chdir.enter, h]
  · intro h
    simp [Chdir.exit, h]
  · intro h1 h2
    simp [Chdir.exit, h1, h2]

end PyLean.CoreLibs.Misc.Contextlib
