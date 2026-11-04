import PyLean.Bytecode.Ceval

/-!
Stack-effect combinators. `stk p q f` is the DSL signature
`(inputs[p] -- outputs[q])` of `Python/bytecodes.c`: it is the only way an
instruction body touches the evaluation stack, and the body `f` lives in `BM`,
which has no access to the stack. So every step rule has its declared effect by
construction, and `Eff` below only has to compare the declared numbers against
`_PyOpcode_num_popped`/`_pushed`.
-/

namespace PyLean.Bytecode

/-- What a step rule may depend on besides the machine state. -/
structure Env where
  P : Program
  om : ObjModel
  ctx : Ctx
  /-- The opcode being executed (`opcode`). -/
  opcode : Op
  oparg : Nat
  /-- `this_instr`. -/
  this : Nat
  /-- The decoded inline cache of `this_instr`. -/
  cache : List Val := []

/-- The top `n` values in stack order (bottom first), as C sees `args[0..n)`. -/
def peekN (n : Nat) : M (List Val) := fun s =>
  if n ≤ s.stack.length then .ok (s.stack.take n).reverse s
  else .error (.fault "stack underflow") s

/-- Pop the top `n` values, returning them in stack order. -/
def popN (n : Nat) : M (List Val) := fun s =>
  if n ≤ s.stack.length then .ok (s.stack.take n).reverse { s with stack := s.stack.drop n }
  else .error (.fault "stack underflow") s

/-- Push values given in stack order. -/
def pushAll (vs : List Val) : M Unit := fun s => .ok () { s with stack := vs.reverse ++ s.stack }

/-- `(inputs[p] -- outputs[q])` where failure pops the inputs (`ERROR_IF`). -/
def stk (p q : Nat) (f : List Val → BM (List Val)) : M Unit := do
  let ins ← popN p
  let outs ← BM.lift (f ins)
  if outs.length = q then pushAll outs else fault "wrong number of outputs"

/-- `(inputs[p] -- outputs[q])` where failure keeps the inputs (`ERROR_NO_POP`). -/
def stkK (p q : Nat) (f : List Val → BM (List Val)) : M Unit := do
  let ins ← peekN p
  let outs ← BM.lift (f ins)
  if outs.length = q then do
    let _ ← popN p
    pushAll outs
  else fault "wrong number of outputs"

/-- `(inputs[p] -- outputs[q])` where failure pops only the top `k` inputs. `ERROR_IF` pops the
inputs that are not also outputs in the same slot (`pop_k_error`, `Python/generated_cases.c.h`):
`SET_ADD`'s `(set, unused[oparg-1], v -- set, unused[oparg-1])` pops `v` alone and leaves the set
and the items below it for the comprehension's cleanup handler. -/
def stkE (p q k : Nat) (f : List Val → BM (List Val)) : M Unit := fun s =>
  match stkK p q f s with
  | .error x s' => .error x { s' with stack := s'.stack.drop k }
  | r => r

/-- `DEOPT_IF(c)` / `EXIT_IF(c)`. -/
def deoptIf (c : Bool) : BM Unit := if c then throw .deopt else pure ()

/-- A guard on the top `n` values: `(x[n] -- x[n])`. -/
def guardTop (n : Nat) (bad : List Val → BM Bool) : M Unit := do
  let ins ← peekN n
  BM.lift do deoptIf (← bad ins)

/-- `stack_pointer` is saved to the frame; the frame stops being current. -/
def saveStack : M Unit := fun s =>
  .ok () { s with regs := { s.regs with frame := { s.regs.frame with stack := s.stack } } }

/-- The successful effect of a program on the stack: exactly the top `p` values
were consumed and `q` values were put in their place; everything below is
untouched. -/
def Eff {α : Type} (p q : Nat) (m : M α) : Prop :=
  ∀ s a s', m s = .ok a s' →
    p ≤ s.stack.length ∧ s'.stack.length = s.stack.length - p + q ∧ s'.stack.drop q = s.stack.drop p

theorem eff_peekN (n : Nat) : Eff 0 0 (peekN n) := by
  intro s a s' h
  simp only [peekN] at h
  split at h
  · cases h; simp
  · cases h

theorem popN_ok {n : Nat} {s : St} {a : List Val} {s' : St} (h : popN n s = .ok a s') :
    n ≤ s.stack.length ∧ s' = { s with stack := s.stack.drop n } := by
  simp only [popN] at h
  split at h
  · cases h; simp_all
  · cases h

theorem peekN_ok {n : Nat} {s : St} {a : List Val} {s' : St} (h : peekN n s = .ok a s') :
    n ≤ s.stack.length ∧ s' = s := by
  simp only [peekN] at h
  split at h
  · cases h; simp_all
  · cases h

theorem liftB_stack {α : Type} {m : BM α} {s : St} {a : α} {s' : St}
    (h : BM.lift m s = .ok a s') : s'.stack = s.stack := by
  simp only [BM.lift] at h
  split at h
  · cases h; rfl
  · cases h

/-- The effect of `stk p q f` is `(p, q)`, whatever `f` does. -/
theorem eff_stk (p q : Nat) (f : List Val → BM (List Val)) : Eff p q (stk p q f) := by
  intro s a s' h
  simp only [stk, bind, EStateM.bind] at h
  split at h
  · rename_i ins s1 hpop
    obtain ⟨hle, rfl⟩ := popN_ok hpop
    split at h
    · rename_i outs s2 hl
      have hs2 := liftB_stack hl
      split at h
      · rename_i hlen
        simp only [pushAll, pure, EStateM.pure] at h
        cases h
        simp only [] at hs2 ⊢
        rw [hs2]
        refine ⟨hle, ?_, ?_⟩
        · simp [hlen]; omega
        · simp [← hlen]
      · cases h
    · cases h
  · cases h

theorem eff_stkK (p q : Nat) (f : List Val → BM (List Val)) : Eff p q (stkK p q f) := by
  intro s a s' h
  simp only [stkK, bind, EStateM.bind] at h
  split at h
  · rename_i ins s1 hpeek
    obtain ⟨hle, rfl⟩ := peekN_ok hpeek
    split at h
    · rename_i outs s2 hl
      have hs2 := liftB_stack hl
      split at h
      · rename_i hlen
        simp only [EStateM.bind] at h
        split at h
        · rename_i s3 hpop
          obtain ⟨_, rfl⟩ := popN_ok hpop
          simp only [pushAll, pure, EStateM.pure] at h
          cases h
          simp only [] at hs2 ⊢
          rw [hs2]
          refine ⟨hle, ?_, ?_⟩
          · simp [hlen]; omega
          · simp [← hlen]
        · cases h
      · cases h
    · cases h
  · cases h

theorem eff_stkE (p q k : Nat) (f : List Val → BM (List Val)) : Eff p q (stkE p q k f) := by
  intro s a s' h
  simp only [stkE] at h
  split at h
  · cases h
  · rename_i hne
    generalize hr : stkK p q f s = r at h hne
    cases r with
    | ok a' s'' => exact eff_stkK p q f s a s' (hr.trans h)
    | error x s'' => exact absurd rfl (hne x s'')

/-- Sequencing a stack-neutral program (a guard) before an effect. -/
theorem Eff.seq0 {β : Type} {m : M Unit} {k : M β} {p q : Nat}
    (h₁ : Eff 0 0 m) (h₂ : Eff p q k) : Eff p q (m *> k) := by
  intro s a s' h
  simp only [SeqRight.seqRight, bind, EStateM.seqRight] at h
  split at h
  · rename_i s1 hm
    obtain ⟨_, h3, h4⟩ := h₁ s _ s1 hm
    obtain ⟨h5, h6, h7⟩ := h₂ s1 a s' h
    simp only [List.drop_zero] at h4
    rw [h4] at h5 h6 h7
    exact ⟨h5, h6, h7⟩
  · cases h

theorem eff_guardTop (n : Nat) (bad : List Val → BM Bool) : Eff 0 0 (guardTop n bad) := by
  intro s a s' h
  simp only [guardTop, bind, EStateM.bind] at h
  split at h
  · rename_i ins s1 hpeek
    obtain ⟨_, rfl⟩ := peekN_ok hpeek
    have := liftB_stack h
    simp [this]
  · cases h

end PyLean.Bytecode
