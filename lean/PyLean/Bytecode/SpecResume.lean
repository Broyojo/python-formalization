import PyLean.Bytecode.SpecFast

/-!
`RESUME` and its specialized forms, `Python/bytecodes.c:168-245` (CPython 3.15.2), with no
monitoring tool active (`_MAYBE_INSTRUMENT` finds the code's instrumentation version equal to the
global one) and on the default build (`_LOAD_BYTECODE` is free-threaded only).
-/

namespace PyLean.Bytecode

open Uop

/-- **`RESUME`** (`:220-224`): at a function start, after a `yield` or anywhere else whose location
bits (`oparg & RESUME_OPARG_LOCATION_MASK`) are below `RESUME_AFTER_YIELD_FROM` (2), the eval
breaker is checked (`_CHECK_PERIODIC_IF_NOT_YIELD_FROM`, `:168-173`): with nothing pending, or
handlers that succeed, the state is unchanged; a pending exception is raised with nothing popped and
the event consumed. After a `yield from` or `await` (location 2 or 3, or the generator-expression
start, 4) nothing is checked, whatever is pending. **`RESUME_CHECK`** (`:226-243`) and
`RESUME_CHECK_JIT` (`:245-248`) do nothing when no event is pending and otherwise deopt to
`RESUME`, which runs the check. A `RESUME` that always or never checked, or a `RESUME_CHECK` that
ignored the breaker, fails one of these. -/
def ResumeRules : Prop :=
  ∀ (e : Env) (regs : Regs) (S : List Val),
    (e.oparg &&& 7 < 2 → regs.rt.pendingExc = .null → execOp e .RESUME ⟨regs, S⟩ = .ok () ⟨regs, S⟩) ∧
    (∀ x rt, e.oparg &&& 7 < 2 → regs.rt.pendingExc ≠ .null →
      raiseVal (α := Unit) regs.rt.pendingExc { regs.rt with pendingExc := .null } = .error x rt →
      execOp e .RESUME ⟨regs, S⟩ = .error x ⟨{ regs with rt := rt }, S⟩) ∧
    (2 ≤ e.oparg &&& 7 → execOp e .RESUME ⟨regs, S⟩ = .ok () ⟨regs, S⟩) ∧
    (regs.rt.pendingExc = .null → execOp e .RESUME_CHECK ⟨regs, S⟩ = .ok () ⟨regs, S⟩) ∧
    (regs.rt.pendingExc ≠ .null → execOp e .RESUME_CHECK ⟨regs, S⟩ = execOp e .RESUME ⟨regs, S⟩) ∧
    (regs.rt.pendingExc = .null → execOp e .RESUME_CHECK_JIT ⟨regs, S⟩ = .ok () ⟨regs, S⟩) ∧
    (regs.rt.pendingExc ≠ .null → execOp e .RESUME_CHECK_JIT ⟨regs, S⟩ = execOp e .RESUME ⟨regs, S⟩)

theorem resumeRules_proven : ResumeRules := by
  intro e regs S
  refine ⟨fun h hp => ?_, fun x rt h hp hr => ?_, fun h => ?_, fun hp => ?_, fun hp => ?_, fun hp => ?_,
    fun hp => ?_⟩
  · bc_simp [execOp, RESUME, _LOAD_BYTECODE, _MAYBE_INSTRUMENT, _QUICKEN_RESUME,
      _CHECK_PERIODIC_IF_NOT_YIELD_FROM, h, _CHECK_PERIODIC, checkPeriodics, hp]
  · have hb : (regs.rt.pendingExc == .null) = false := by simpa using hp
    bc_simp [execOp, RESUME, _LOAD_BYTECODE, _MAYBE_INSTRUMENT, _QUICKEN_RESUME,
      _CHECK_PERIODIC_IF_NOT_YIELD_FROM, h, _CHECK_PERIODIC, checkPeriodics, hb, hr]
  · have h' : ¬ e.oparg &&& 7 < 2 := by omega
    bc_simp [execOp, RESUME, _LOAD_BYTECODE, _MAYBE_INSTRUMENT, _QUICKEN_RESUME,
      _CHECK_PERIODIC_IF_NOT_YIELD_FROM, h']
  · bc_simp [execOp, withDeopt, RESUME_CHECK, _RESUME_CHECK, hp]
  · have hb : (regs.rt.pendingExc != .null) = true := by simpa using hp
    bc_simp [execOp, withDeopt, RESUME_CHECK, _RESUME_CHECK, hb]
  · bc_simp [execOp, withDeopt, RESUME_CHECK_JIT, RESUME_CHECK, _RESUME_CHECK, hp]
  · have hb : (regs.rt.pendingExc != .null) = true := by simpa using hp
    bc_simp [execOp, withDeopt, RESUME_CHECK_JIT, RESUME_CHECK, _RESUME_CHECK, hb]

end PyLean.Bytecode
