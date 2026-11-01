import PyLean.Bytecode.Exec

namespace PyLean.Bytecode
open Uop

theorem withDeopt_of_deopt {m g : M Unit} {s s' : St} (h : m s = .error .deopt s') :
    withDeopt m g s = g s := by simp [withDeopt, h]

theorem withDeopt_of_eq {m g : M Unit} {s : St} (h : m s = g s) (hg : ∀ s', g s ≠ .error .deopt s') :
    withDeopt m g s = g s := by
  simp only [withDeopt, h]
  split
  · rename_i h'; exact absurd h' (hg _)
  · rfl

/-- `BINARY_OP_ADD_INT` is `BINARY_OP` for `+`. -/
example (e : Env) (a b : Int) (regs : Regs) (rest : List Val)
    (h : ∀ rt, e.om.binaryOp e.ctx e.oparg (.int a) (.int b) rt = .ok (.int (a + b)) rt) :
    BINARY_OP_ADD_INT ⟨regs, .int b :: .int a :: rest⟩ = BINARY_OP e ⟨regs, .int b :: .int a :: rest⟩ := by
  simp [BINARY_OP_ADD_INT, BINARY_OP, _BINARY_OP, _SPECIALIZE_BINARY_OP, _GUARD_TOS_INT, _GUARD_NOS_INT,
    _BINARY_OP_ADD_INT, guardTop, stk, stkK, peekN, popN, pushAll, deoptIf, notInt, BM.lift, RM.lift,
    bind, EStateM.bind, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]

end PyLean.Bytecode
