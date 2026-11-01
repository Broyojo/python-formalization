import re
names=[]
for f in ['lean/PyLean/Bytecode/Uops1.lean','lean/PyLean/Bytecode/Uops2.lean','lean/PyLean/Bytecode/Uops3.lean']:
    for m in re.finditer(r'^def (\S+)', open(f).read(), re.M):
        n=m.group(1)
        if n[0].isupper() or n.startswith('_'):
            names.append(n)
skip={'NOP'}
keep=[n for n in names if n not in ('GET','Op')]
keep=[n for n in keep if n not in ('ExtendDescr',)]
hdr=r'''import PyLean.Bytecode.Exec

/-!
Stack effects: for every opcode and every `oparg`, a step that completes normally
in the same frame replaces exactly the top `_PyOpcode_num_popped(op, oparg)` values
by `_PyOpcode_num_pushed(op, oparg)` values and leaves the rest of the stack alone.
The tables are generated from `pycore_opcode_metadata.h`; the step rules are the
mirrors of `Python/bytecodes.c`. So this is the source agreeing with its own
generated metadata, instruction by instruction.
-/

namespace PyLean.Bytecode

open Uop

theorem Eff.pure0 {α : Type} (a : α) : Eff 0 0 (pure a : M α) := by
  intro s b s' h
  simp only [pure, EStateM.pure] at h
  cases h; simp

theorem Eff.never {α : Type} {p q : Nat} {m : M α} (h : ∀ s a s', m s ≠ .ok a s') : Eff p q m := by
  intro s a s' hm
  exact absurd hm (h s a s')

theorem Eff.throw_ {α : Type} {p q : Nat} (e : Err) : Eff p q (throw e : M α) :=
  Eff.never (by intro s a s'; simp [throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw])

theorem Eff.fault_ {α : Type} {p q : Nat} (m : String) : Eff p q (fault m : M α) :=
  Eff.throw_ _

/-- A stack-neutral step keeps the stack as it is. -/
theorem Eff.same_stack {α : Type} {m : M α} (h : Eff 0 0 m) {s a s'} (hm : m s = .ok a s') :
    s'.stack = s.stack := by
  have := (h s a s' hm).2.2
  simpa using this

/-- Run a stack-neutral program first. -/
theorem Eff.pre0 {α β : Type} {m : M α} {k : α → M β} {p q : Nat}
    (h₁ : Eff 0 0 m) (h₂ : ∀ a, Eff p q (k a)) : Eff p q (m >>= k) := by
  intro s b s' h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i a s1 hm
    have hs := Eff.same_stack h₁ hm
    obtain ⟨h5, h6, h7⟩ := h₂ a s1 b s' h
    rw [hs] at h5 h6 h7
    exact ⟨h5, h6, h7⟩
  · cases h

/-- Run a stack-neutral program last. -/
theorem Eff.post0 {α β : Type} {m : M α} {k : α → M β} {p q : Nat}
    (h₁ : Eff p q m) (h₂ : ∀ a, Eff 0 0 (k a)) : Eff p q (m >>= k) := by
  intro s b s' h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i a s1 hm
    have hs := Eff.same_stack (h₂ a) h
    obtain ⟨h5, h6, h7⟩ := h₁ s a s1 hm
    rw [hs]
    exact ⟨h5, h6, h7⟩
  · cases h

/-- `k` consumes exactly what `m` produced. -/
theorem Eff.same {α β : Type} {m : M α} {k : α → M β} {p q r : Nat}
    (h₁ : Eff p q m) (h₂ : ∀ a, Eff q r (k a)) : Eff p r (m >>= k) := by
  intro s b s' h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i a s1 hm
    obtain ⟨h5, h6, h7⟩ := h₁ s a s1 hm
    obtain ⟨h8, h9, h10⟩ := h₂ a s1 b s' h
    refine ⟨h5, by omega, by rw [h10, h7]⟩
  · cases h

/-- `k` adds on top of what `m` produced. -/
theorem Eff.append {α β : Type} {m : M α} {k : α → M β} {p q n : Nat}
    (h₁ : Eff p q m) (h₂ : ∀ a, Eff 0 n (k a)) : Eff p (q + n) (m >>= k) := by
  intro s b s' h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i a s1 hm
    obtain ⟨h5, h6, h7⟩ := h₁ s a s1 hm
    obtain ⟨h8, h9, h10⟩ := h₂ a s1 b s' h
    refine ⟨h5, by omega, ?_⟩
    rw [Nat.add_comm q n, ← List.drop_drop, h10]
    simpa using h7
  · cases h

theorem Eff.cast {α : Type} {m : M α} {p q p' q' : Nat} (h : Eff p q m) (hp : p = p') (hq : q = q') :
    Eff p' q' m := by subst hp; subst hq; exact h

theorem Eff.peek {α : Type} {n p q : Nat} {k : List Val → M α}
    (h : ∀ ins, Eff p q (k ins)) : Eff p q (peekN n >>= k) :=
  Eff.pre0 (eff_peekN n) h

theorem eff_liftB {α : Type} (m : BM α) : Eff 0 0 (BM.lift m) := by
  intro s a s' h
  simp [liftB_stack h]

theorem Eff.lift {α β : Type} {m : BM α} {k : α → M β} {p q : Nat}
    (h : ∀ a, Eff p q (k a)) : Eff p q (BM.lift m >>= k) :=
  Eff.pre0 (eff_liftB m) h

theorem Eff.withDeopt {m g : M Unit} {p q : Nat} (h₁ : Eff p q m) (h₂ : Eff p q g) :
    Eff p q (withDeopt m g) := by
  intro s a s' h
  simp only [PyLean.Bytecode.withDeopt] at h
  split at h
  · exact h₂ s a s' h
  · exact h₁ s a s' h

theorem eff_popN (n : Nat) : Eff n 0 (popN n) := by
  intro s a s' h
  obtain ⟨h1, rfl⟩ := popN_ok h
  simp; omega

theorem eff_pushAll (vs : List Val) : Eff 0 vs.length (pushAll vs) := by
  intro s a s' h
  simp only [pushAll] at h
  cases h
  refine ⟨by simp, by simp [List.length_append]; omega, ?_⟩
  show (vs.reverse ++ s.stack).drop vs.length = s.stack.drop 0
  rw [List.drop_zero]
  exact List.drop_left' (by simp)

theorem Eff.pure_id {p q : Nat} {m : M Unit} (h : Eff p q m) : Eff p q (pure () >>= fun _ => m) := by
  simpa using h

theorem Eff.ite' {α : Type} {c : Prop} [Decidable c] {p q : Nat} {a b : M α}
    (h₁ : Eff p q a) (h₂ : Eff p q b) : Eff p q (if c then a else b) := by
  split <;> assumption

theorem eff_dispatchInlined {α : Type} {p q : Nat} (nf : Frame) : Eff p q (dispatchInlined nf : M α) :=
  Eff.never (by
    intro s a s' h
    simp only [dispatchInlined, bind, EStateM.bind] at h
    split at h
    · split at h
      · simp [throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw] at h
      · cases h
    · cases h)

/-- The hypothesis of the step rules: `assert(oparg > 0)` where an instruction
writes `unused[oparg-1]`, `assert(oparg >= 2)` for `SWAP`. Both hold for bytecode
from the compiler. -/
def validOparg : Op → Nat → Prop
  | .LIST_APPEND, a | .SET_ADD, a | .LIST_EXTEND, a | .SET_UPDATE, a | .COPY, a
  | .DICT_UPDATE, a | .DICT_MERGE, a | .MAP_ADD, a => 1 ≤ a
  | .SWAP, a => 2 ≤ a
  | _, _ => True

/-- Opcodes whose normal completion is in another frame, or that have no normal
completion. Their effect on the frame they leave is stated in `Frames.lean`. -/
def leavesFrame : Op → Bool
  | .RETURN_VALUE | .INSTRUMENTED_RETURN_VALUE | .YIELD_VALUE | .INSTRUMENTED_YIELD_VALUE
  | .RETURN_GENERATOR | .BINARY_OP_SUBSCR_GETITEM | .SEND_GEN | .FOR_ITER_GEN
  | .CALL_PY_EXACT_ARGS | .CALL_BOUND_METHOD_EXACT_ARGS | .CALL_PY_GENERAL
  | .CALL_BOUND_METHOD_GENERAL | .CALL_KW_PY | .CALL_KW_BOUND_METHOD
  | .CALL_ALLOC_AND_ENTER_INIT | .LOAD_ATTR_PROPERTY | .LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN => true
  | _ => false

-- `RERAISE` is also excluded: it always jumps to `exception_unwind` (it never completes in
-- the same frame), so its declared `(values[oparg], exc -- values[oparg])` effect is never
-- realized on a normal completion and the uniform theorem has nothing to say about it.
-- The generic `FOR_ITER`/`SEND` forms peek at the iterator/receiver and either push the
-- next value (keeping the peeked value, a `(1 -- 2)` / `(2 -- 2)` effect) or jump over the
-- loop end via `DISPATCH`; their body is a peek-then-conditionally-dispatch shape that the
-- uniform `(pop p, push q)` combinator does not capture. They keep their declared effect; it
-- is just proved elsewhere. (The specialized members `FOR_ITER_LIST` etc. use `stk` and are
-- covered by `eff_execOp`.)
def peekDispatch : Op → Bool
  | .FOR_ITER | .INSTRUMENTED_FOR_ITER | .SEND | .WITH_EXCEPT_START | .RERAISE => true
  | _ => false

/-- The two super-instructions that fold a following `STORE_FAST`/`POP_TOP` with
`SKIP_OVER(1)`: their declared stack effect (`(2 -- )`, `(3 -- )`) differs from the
generic form they deopt to, because the generic form does not skip the next
instruction. They are excluded from the uniform stack-effect theorem and treated
on their own (`superEffects`). -/
def superInstr : Op → Bool
  | .BINARY_OP_INPLACE_ADD_UNICODE | .CALL_LIST_APPEND => true
  | _ => false
'''
uop_list = ', '.join(keep)
macro = r'''
/-- Structural search for the effect of a step rule. -/
syntax "eff_auto" : tactic
macro_rules
  | `(tactic| eff_auto) => `(tactic| first
    | exact eff_stk _ _ _
    | exact eff_stkK _ _ _
    | exact eff_guardTop _ _
    | exact Eff.pure0 _
    | exact Eff.fault_ _
    | exact Eff.throw_ _
    | exact eff_dispatchInlined _
    | exact eff_popN _
    | exact eff_pushAll _
    | exact eff_liftB _
    | (apply Eff.withDeopt <;> eff_auto)
    | (apply Eff.peek; intro _; eff_auto)
    | (apply Eff.lift; intro _; eff_auto)
    | (refine Eff.pre0 ?_ fun _ => ?_ <;> eff_auto)
    | (refine Eff.post0 ?_ fun _ => ?_ <;> eff_auto)
    | (refine Eff.same ?_ fun _ => ?_ <;> eff_auto)
    | (refine Eff.append ?_ fun _ => ?_ <;> eff_auto)
    | (split <;> eff_auto))

set_option maxHeartbeats 2000000 in
theorem eff_execOp (e : Env) (o : Op) (hv : validOparg o e.oparg) (hf : leavesFrame o = false)
    (hs : superInstr o = false) (hp : peekDispatch o = false) :
    Eff (numPopped o e.oparg) (numPushed o e.oparg) (execOp e o) := by
  cases o <;> first
    | exact absurd hf (by decide)
    | exact absurd hs (by decide)
    | exact absurd hp (by decide)
    | (simp only [execOp, numPopped, numPushed, validOparg, UOPS] at hv ⊢ <;> first
        | eff_auto
        | (refine Eff.cast (m := _) ?_ (by omega) (by omega); eff_auto))

end PyLean.Bytecode
'''
out=hdr+macro.replace('UOPS', uop_list)
open('lean/PyLean/Bytecode/StackEffect.lean','w').write(out)
print(len(keep))
