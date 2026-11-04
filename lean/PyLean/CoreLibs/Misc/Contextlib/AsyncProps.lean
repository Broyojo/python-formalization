import PyLean.CoreLibs.Misc.Contextlib.Props
import PyLean.CoreLibs.Misc.Contextlib.HeapLemmas

/-!
Properties of the `async def` methods of `Lib/contextlib.py`: `_AsyncGeneratorContextManager`,
`asynccontextmanager`, `aclosing`. Each is the algorithm of its sync twin with the async object's
operations, run inside a coroutine, so a `StopIteration` that leaves it becomes the `RuntimeError`
of `coroutineStop` (Python/intrinsics.c:141-182). The statements spell that `RuntimeError` out
instead of naming `coBoundary`.
-/

namespace PyLean.CoreLibs.Misc.Contextlib

open PyLean

/-- What a `StopIteration` `e` leaving an `async def` becomes: a new
`RuntimeError("coroutine raised StopIteration")` with `e` as `__cause__` and `__context__`. -/
def coroutineStop {σ α : Type} (s : St σ) (e : ExcId) : St σ × Res α :=
  let (h, x) := s.h.alloc
    { cls := clsRuntime, msg := "coroutine raised StopIteration", context := some e, cause := some e }
  ({ s with h := h }, .error x)

/-- `__aenter__`: the value the generator gives is the value of the `async with` target. A
`StopAsyncIteration` is `RuntimeError("generator didn't yield")` with it as context; a
`StopIteration`, which an object that is no async generator can raise from `anext`, leaves the
coroutine as `RuntimeError("coroutine raised StopIteration")`; anything else comes through. A second
`__aenter__` is `AttributeError` for `args`, deleted by the first. -/
def AEnterCases : Prop :=
  ∀ (σ V : Type) (ops : GenOps σ V) (s s' : St σ) (v : V) (e : ExcId),
    (ops.next s = (s', .ok v) → agcmEnter ops { live := true } s = ({ live := false }, s', .ok v)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e "StopAsyncIteration" = true →
      agcmEnter ops { live := true } s =
        let (s2, x) := s'.raiseNew clsRuntime "generator didn't yield" (some e)
        ({ live := false }, s2, .error x)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e "StopAsyncIteration" = false →
      s'.h.isInst e "StopIteration" = true →
      agcmEnter ops { live := true } s =
        let r : St σ × Res V := coroutineStop s' e
        ({ live := false }, r.1, r.2)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e "StopAsyncIteration" = false →
      s'.h.isInst e "StopIteration" = false →
      agcmEnter ops { live := true } s = ({ live := false }, s', .error e)) ∧
    agcmEnter ops { live := false } s =
      let (s2, x) := s.raiseNew clsAttr "'_AsyncGeneratorContextManager' object has no attribute 'args'"
      ({ live := false }, s2, .error x)

theorem aEnterCases_proven : AEnterCases := by
  intro σ V ops s s' v e
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [agcmEnter, gcmEnter, coBoundary, h]
  · intro h1 h2
    have hr := raiseNew_isInst s' clsRuntime "generator didn't yield" (some e) "StopIteration"
    simp only [agcmEnter, gcmEnter, asyncCfg, h1, h2, coBoundary, Bool.not_true, Bool.false_eq_true,
      if_false, if_true]
    simp [hr, clsRuntime]
  · intro h1 h2 h3
    simp [agcmEnter, gcmEnter, asyncCfg, h1, h2, h3, coBoundary, coroutineStop]
  · intro h1 h2 h3
    simp [agcmEnter, gcmEnter, asyncCfg, h1, h2, h3, coBoundary]
  · have hr := raiseNew_isInst s clsAttr
      "'_AsyncGeneratorContextManager' object has no attribute 'args'" none "StopIteration"
    simp only [agcmEnter, gcmEnter, Bool.not_false, if_true, coBoundary]
    simp [hr, clsAttr]

/-- The way out of `try: raise RuntimeError(msg) finally: await self.gen.aclose()` in `__aexit__`:
the `RuntimeError` when `aclose` succeeds, else what `aclose` raised, a `StopIteration` turned into
the coroutine's `RuntimeError`. -/
def AfterYield {σ V : Type} (ops : GenOps σ V) (s : St σ) (msg : String) (run : St σ × Res Bool) :
    Prop :=
  let (s2, rt) := s.raiseNew clsRuntime msg (ops.handled s)
  (∀ s3, ops.close s2 (some rt) = (s3, .ok ()) → run = (s3, .error rt)) ∧
  (∀ s3 x, ops.close s2 (some rt) = (s3, .error x) → s3.h.isInst x "StopIteration" = true →
    run = coroutineStop s3 x) ∧
  (∀ s3 x, ops.close s2 (some rt) = (s3, .error x) → s3.h.isInst x "StopIteration" = false →
    run = (s3, .error x))

theorem afterYield_of {σ V : Type} (ops : GenOps σ V) (s : St σ) (msg : String) :
    AfterYield ops s msg (coBoundary (raiseThenClose ops s msg).1 (raiseThenClose ops s msg).2) := by
  have hr := raiseNew_isInst s clsRuntime msg (ops.handled s) "StopIteration"
  refine ⟨?_, ?_, ?_⟩
  · intro s3 h
    simp only [raiseThenClose, h, coBoundary]
    simp only [St.raiseNew] at hr h ⊢
    simp [hr, clsRuntime]
  · intro s3 x h hx
    simp [raiseThenClose, h, coBoundary, hx, coroutineStop]
  · intro s3 x h hx
    simp [raiseThenClose, h, coBoundary, hx]

/-- `__aexit__(None, None, None)`: an async generator that finishes gives `False`; one that yields
again is closed, and the result is `AfterYield` with "generator didn't stop"; a `StopIteration`
from `anext` leaves as the coroutine's `RuntimeError`; any other exception comes through. -/
def AExitNoException : Prop :=
  ∀ (σ V : Type) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (v : V) (e : ExcId),
    (ops.next s = (s', .error e) → s'.h.isInst e "StopAsyncIteration" = true →
      agcmExit ops inst s none none none = (s', .ok false)) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e "StopAsyncIteration" = false →
      s'.h.isInst e "StopIteration" = true →
      agcmExit ops inst s none none none = coroutineStop s' e) ∧
    (ops.next s = (s', .error e) → s'.h.isInst e "StopAsyncIteration" = false →
      s'.h.isInst e "StopIteration" = false →
      agcmExit ops inst s none none none = (s', .error e)) ∧
    (ops.next s = (s', .ok v) →
      AfterYield ops s' "generator didn't stop" (agcmExit ops inst s none none none))

theorem aExitNoException_proven : AExitNoException := by
  intro σ V ops inst s s' v e
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2; simp [agcmExit, gcmExit, asyncCfg, h1, h2, coBoundary]
  · intro h1 h2 h3; simp [agcmExit, gcmExit, asyncCfg, h1, h2, h3, coBoundary, coroutineStop]
  · intro h1 h2 h3; simp [agcmExit, gcmExit, asyncCfg, h1, h2, h3, coBoundary]
  · intro h
    have : agcmExit ops inst s none none none =
        coBoundary (raiseThenClose ops s' "generator didn't stop").1
          (raiseThenClose ops s' "generator didn't stop").2 := by
      simp [agcmExit, gcmExit, h]
    rw [this]
    exact afterYield_of ops s' _

/-- `__aexit__(type, value, tb)` on every async generator, branch by branch, as the comments of
Lib/contextlib.py:298-331 say: yielding after `athrow` is `AfterYield` with "generator didn't stop
after athrow()"; a `StopAsyncIteration` swallows `value` unless it is `value`; `value` coming back,
or a `RuntimeError` whose `__cause__` is a `value` of the stop classes, gives `False` and restores
the traceback; anything else is raised, a `StopIteration` as the coroutine's `RuntimeError`. -/
def AExitThrowCases : Prop :=
  ∀ (σ V : Type) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (c : Cls)
    (value : ExcId) (tb : Option Nat) (v : V) (exc : ExcId),
    let run := agcmExit ops inst s (some c) (some value) tb
    (ops.throw s value = (s', .ok v) → AfterYield ops s' "generator didn't stop after athrow()" run) ∧
    (ops.throw s value = (s', .error exc) → s'.h.isInst exc "StopAsyncIteration" = true →
      run = (s', .ok (decide (exc ≠ value)))) ∧
    (ops.throw s value = (s', .error value) → s'.h.isInst value "StopAsyncIteration" = false →
      run = ({ s' with h := s'.h.setTb value tb }, .ok false)) ∧
    (ops.throw s value = (s', .error exc) → exc ≠ value → s'.h.isInst exc "StopAsyncIteration" = false →
      s'.h.isInst exc "RuntimeError" = true →
      (s'.h.isInst value "StopIteration" = true ∨ s'.h.isInst value "StopAsyncIteration" = true) →
      (s'.h.get exc).cause = some value →
      run = ({ s' with h := s'.h.setTb value tb }, .ok false)) ∧
    (ops.throw s value = (s', .error exc) → exc ≠ value → s'.h.isInst exc "StopAsyncIteration" = false →
      (s'.h.isInst exc "RuntimeError" = false ∨
        (s'.h.isInst value "StopIteration" = false ∧ s'.h.isInst value "StopAsyncIteration" = false) ∨
        (s'.h.get exc).cause ≠ some value) →
      run = if s'.h.isInst exc "StopIteration" then coroutineStop s' exc else (s', .error exc))

theorem aExitThrowCases_proven : AExitThrowCases := by
  intro σ V ops inst s s' c value tb v exc run
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have : run = coBoundary (raiseThenClose ops s' "generator didn't stop after athrow()").1
        (raiseThenClose ops s' "generator didn't stop after athrow()").2 := by
      simp [run, agcmExit, gcmExit, h, asyncCfg]
    rw [this]
    exact afterYield_of ops s' _
  · intro h1 h2; simp [run, agcmExit, gcmExit, asyncCfg, h1, h2, coBoundary]
  · intro h1 h2
    simp only [run, agcmExit, gcmExit, asyncCfg, h1, h2]
    cases h3 : s'.h.isInst value "RuntimeError" <;> simp [coBoundary]
  · intro h1 h2 h3 h4 h5 h6
    have hw : s'.h.isInstAny value asyncCfg.wrapped = true := by
      rcases h5 with h5 | h5 <;> simp [Heap.isInstAny, asyncCfg, h5]
    simp only [run, agcmExit, gcmExit, h1, asyncCfg] at hw ⊢
    simp [h2, h3, h4, hw, h6, coBoundary]
  · intro h1 h2 h3 h4
    have hcase : (if s'.h.isInst exc "RuntimeError" = true then
        (if exc = value then ({ s' with h := s'.h.setTb exc tb }, (.ok false : Res Bool))
         else if s'.h.isInstAny value ["StopIteration", "StopAsyncIteration"] = true ∧
            (s'.h.get exc).cause = some value then ({ s' with h := s'.h.setTb value tb }, .ok false)
          else (s', .error exc))
        else if exc ≠ value then (s', .error exc) else ({ s' with h := s'.h.setTb exc tb }, .ok false))
        = (s', .error exc) := by
      rcases h4 with h4 | ⟨h4a, h4b⟩ | h4
      · simp [h4, h2]
      · simp [Heap.isInstAny, h4a, h4b, h2]
      · cases hr : s'.h.isInst exc "RuntimeError" <;> simp [h2, h4]
    simp only [run, agcmExit, gcmExit, h1, asyncCfg, h3, Bool.false_eq_true, if_false]
    rw [hcase]
    cases hs : s'.h.isInst exc "StopIteration" <;> simp [coBoundary, hs, coroutineStop]

/-- `__aexit__(typ, None, tb)`: `value = typ()` runs first. Its exception is the result, a
`StopIteration` turned into the coroutine's `RuntimeError`, and the generator is not touched;
otherwise `__aexit__` is what it is with the new instance as `value`. -/
def AExitValueNone : Prop :=
  ∀ (σ V : Type) (ops : GenOps σ V) (inst : Instantiate σ) (s s' : St σ) (c : Cls)
    (tb : Option Nat) (e : ExcId),
    (inst s c = (s', .error e) →
      agcmExit ops inst s (some c) none tb =
        if s'.h.isInst e "StopIteration" then coroutineStop s' e else (s', .error e)) ∧
    (inst s c = (s', .ok e) →
      agcmExit ops inst s (some c) none tb = agcmExit ops inst s' (some c) (some e) tb)

theorem aExitValueNone_proven : AExitValueNone := by
  intro σ V ops inst s s' c tb e
  constructor
  · intro h
    cases hs : s'.h.isInst e "StopIteration" <;> simp [agcmExit, gcmExit, h, coBoundary, hs, coroutineStop]
  · intro h; simp [agcmExit, gcmExit, h]

/-- The docstring of `asynccontextmanager`: calling the decorated function calls `func` at once,
and its failure is the call's; with an async generator that yields once and then finishes, the
manager it returns behaves as `<setup>; try: body finally: <cleanup>` in `async with`: a normal
body gives its result, and a body that raises `e` lets the generator re-raise it after cleanup, and
the `async with` statement raises the same object `e`. -/
def AContextmanagerTryFinally : Prop :=
  ∀ (σ V R D : Type) (ops : GenOps σ V) (inst : Instantiate σ) (call : St σ → St σ × Res Unit)
    (getDoc : St σ → St σ × Res (Option D)) (cdoc : Option D) (body : V → St σ → St σ × Res R)
    (s0 s s1 s2 s3 : St σ) (v : V) (r : R) (e stop : ExcId),
    (call s0 = (s, .error e) → contextmanagerCall call getDoc cdoc s0 = (s, .error e)) ∧
    ∀ (g : GCM) (doc : Option D), contextmanagerCall call getDoc cdoc s0 = (s, .ok (g, doc)) →
    let cm : CM σ V :=
      { enter := fun s => (agcmEnter ops g s).2
        exit := fun s x => match x with
          | none => agcmExit ops inst s none none none
          | some ex => agcmExit ops inst s (some (s.h.get ex).cls) (some ex) (s.h.get ex).tb }
    ops.next s = (s1, .ok v) →
    (body v s1 = (s2, .ok r) → ops.next s2 = (s3, .error stop) →
      s3.h.isInst stop "StopAsyncIteration" = true →
      withStmt cm body s = (s3, .ok (some r))) ∧
    (body v s1 = (s2, .error e) → ops.throw s2 e = (s3, .error e) →
      s3.h.isInst e "StopAsyncIteration" = false →
      (withStmt cm body s).2 = .error e)

theorem aContextmanagerTryFinally_proven : AContextmanagerTryFinally := by
  intro σ V R D ops inst call getDoc cdoc body s0 s s1 s2 s3 v r e stop
  refine ⟨?_, ?_⟩
  · intro h; simp [contextmanagerCall, gcmInit, h]
  intro g doc hg cm h1
  have hl : g = { live := true } := gcmInit_live hg
  subst hl
  constructor
  · intro h2 h3 h4
    simp [withStmt, cm, agcmEnter, gcmEnter, h1, h2, agcmExit, gcmExit, h3, h4, asyncCfg, coBoundary]
  · intro h2 h3 h4
    simp only [withStmt, cm, agcmEnter, gcmEnter, h1, Bool.not_true, Bool.false_eq_true,
      if_false, coBoundary, h2, agcmExit, gcmExit, h3, asyncCfg, h4]
    cases hr : s3.h.isInst e "RuntimeError" <;> simp

/-- `aclosing`: "`async with aclosing(f) as x: <block>` is equivalent to `try: <block> finally:
await f.aclose()`", for every behaviour of `aclose()`: the target is `f`; `aclose` runs once, after
the block; its exception replaces the block's outcome, a `StopIteration` from it leaving
`__aexit__` as the coroutine's `RuntimeError`; otherwise the block's value or exception (the same
object) comes out, so nothing is suppressed. -/
def AClosingTryFinally : Prop :=
  ∀ (σ R T : Type) (thing : T) (aclose : Option ExcId → St σ → St σ × Res Unit)
    (body : T → St σ → St σ × Res R) (s s1 s2 : St σ) (e e2 : ExcId) (r : R),
    let cm : CM σ T :=
      { enter := fun s => (s, .ok (closingEnter thing)), exit := fun s x => aclosingExit (aclose x) s }
    (body thing s = (s1, .ok r) → aclose none s1 = (s2, .ok ()) →
      withStmt cm body s = (s2, .ok (some r))) ∧
    (body thing s = (s1, .error e) → aclose (some e) s1 = (s2, .ok ()) →
      withStmt cm body s = (s2, .error e)) ∧
    (∀ x, (body thing s = (s1, .ok r) ∧ x = none ∨ body thing s = (s1, .error e) ∧ x = some e) →
      aclose x s1 = (s2, .error e2) →
      withStmt cm body s =
        if s2.h.isInst e2 "StopIteration" then coroutineStop s2 e2 else (s2, .error e2))

theorem aClosingTryFinally_proven : AClosingTryFinally := by
  intro σ R T thing aclose body s s1 s2 e e2 r cm
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2; simp [withStmt, cm, closingEnter, aclosingExit, closingExit, coBoundary, h1, h2]
  · intro h1 h2; simp [withStmt, cm, closingEnter, aclosingExit, closingExit, coBoundary, h1, h2]
  · intro x hx h2
    rcases hx with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · cases hs : s2.h.isInst e2 "StopIteration" <;>
        simp [withStmt, cm, closingEnter, aclosingExit, closingExit, coBoundary, h1, h2, hs,
          coroutineStop]
    · cases hs : s2.h.isInst e2 "StopIteration" <;>
        simp [withStmt, cm, closingEnter, aclosingExit, closingExit, coBoundary, h1, h2, hs,
          coroutineStop]

end PyLean.CoreLibs.Misc.Contextlib
