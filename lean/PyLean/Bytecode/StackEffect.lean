import PyLean.Bytecode.Exec

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
    | (simp only [execOp, numPopped, numPushed, validOparg, NOP, NOT_TAKEN, _CHECK_PERIODIC, _CHECK_PERIODIC_IF_NOT_YIELD_FROM, _QUICKEN_RESUME, _MAYBE_INSTRUMENT, _LOAD_BYTECODE, RESUME, RESUME_CHECK, _MONITOR_RESUME, INSTRUMENTED_RESUME, LOAD_FAST_CHECK, LOAD_FAST, LOAD_FAST_BORROW, LOAD_FAST_AND_CLEAR, LOAD_FAST_LOAD_FAST, LOAD_FAST_BORROW_LOAD_FAST_BORROW, LOAD_CONST, LOAD_CONST_MORTAL, LOAD_CONST_IMMORTAL, LOAD_SMALL_INT, STORE_FAST, STORE_FAST_LOAD_FAST, STORE_FAST_STORE_FAST, POP_TOP, PUSH_NULL, END_FOR, POP_ITER, INSTRUMENTED_END_FOR, INSTRUMENTED_POP_ITER, END_SEND, INSTRUMENTED_END_SEND, UNARY_NEGATIVE, UNARY_NOT, _SPECIALIZE_TO_BOOL, _TO_BOOL, TO_BOOL, TO_BOOL_BOOL, TO_BOOL_INT, _GUARD_NOS_LIST, _GUARD_TOS_LIST, _GUARD_TOS_SLICE, _TO_BOOL_LIST, TO_BOOL_LIST, TO_BOOL_NONE, _GUARD_NOS_UNICODE, _GUARD_TOS_UNICODE, _TO_BOOL_STR, TO_BOOL_STR, _REPLACE_WITH_TRUE, _GUARD_TYPE_VERSION, TO_BOOL_ALWAYS_TRUE, UNARY_INVERT, _GUARD_NOS_INT, _GUARD_TOS_INT, _BINARY_OP_MULTIPLY_INT, _BINARY_OP_ADD_INT, _BINARY_OP_SUBTRACT_INT, BINARY_OP_MULTIPLY_INT, BINARY_OP_ADD_INT, BINARY_OP_SUBTRACT_INT, _GUARD_NOS_FLOAT, _GUARD_TOS_FLOAT, _BINARY_OP_MULTIPLY_FLOAT, _BINARY_OP_ADD_FLOAT, _BINARY_OP_SUBTRACT_FLOAT, BINARY_OP_MULTIPLY_FLOAT, BINARY_OP_ADD_FLOAT, BINARY_OP_SUBTRACT_FLOAT, _BINARY_OP_ADD_UNICODE, BINARY_OP_ADD_UNICODE, _BINARY_OP_INPLACE_ADD_UNICODE, BINARY_OP_INPLACE_ADD_UNICODE, _GUARD_BINARY_OP_EXTEND, _BINARY_OP_EXTEND, BINARY_OP_EXTEND, _SPECIALIZE_BINARY_SLICE, _BINARY_SLICE, BINARY_SLICE, _SPECIALIZE_STORE_SLICE, _STORE_SLICE, STORE_SLICE, _BINARY_OP_SUBSCR_LIST_INT, BINARY_OP_SUBSCR_LIST_INT, _BINARY_OP_SUBSCR_LIST_SLICE, BINARY_OP_SUBSCR_LIST_SLICE, _BINARY_OP_SUBSCR_STR_INT, BINARY_OP_SUBSCR_STR_INT, _GUARD_NOS_TUPLE, _GUARD_TOS_TUPLE, _BINARY_OP_SUBSCR_TUPLE_INT, BINARY_OP_SUBSCR_TUPLE_INT, _GUARD_NOS_DICT, _GUARD_TOS_DICT, _BINARY_OP_SUBSCR_DICT, BINARY_OP_SUBSCR_DICT, _PUSH_FRAME, _SAVE_RETURN_OFFSET, _CHECK_PEP_523, _BINARY_OP_SUBSCR_CHECK_FUNC, _BINARY_OP_SUBSCR_INIT_CALL, BINARY_OP_SUBSCR_GETITEM, LIST_APPEND, SET_ADD, _SPECIALIZE_STORE_SUBSCR, _STORE_SUBSCR, STORE_SUBSCR, _STORE_SUBSCR_LIST_INT, STORE_SUBSCR_LIST_INT, _STORE_SUBSCR_DICT, STORE_SUBSCR_DICT, DELETE_SUBSCR, CALL_INTRINSIC_1, CALL_INTRINSIC_2, RAISE_VARARGS, INTERPRETER_EXIT, RETURN_VALUE, _RETURN_VALUE_EVENT, INSTRUMENTED_RETURN_VALUE, GET_AITER, GET_ANEXT, GET_AWAITABLE, _SPECIALIZE_SEND, _SEND, SEND, _SEND_GEN_FRAME, SEND_GEN, YIELD_VALUE, _YIELD_VALUE_EVENT, INSTRUMENTED_YIELD_VALUE, POP_EXCEPT, RERAISE, _END_ASYNC_FOR, _MONITOR_END_ASYNC_FOR, INSTRUMENTED_END_ASYNC_FOR, END_ASYNC_FOR, CLEANUP_THROW, LOAD_COMMON_CONSTANT, LOAD_BUILD_CLASS, STORE_NAME, DELETE_NAME, _SPECIALIZE_UNPACK_SEQUENCE, _UNPACK_SEQUENCE, UNPACK_SEQUENCE, _UNPACK_SEQUENCE_TWO_TUPLE, UNPACK_SEQUENCE_TWO_TUPLE, _UNPACK_SEQUENCE_TUPLE, UNPACK_SEQUENCE_TUPLE, _UNPACK_SEQUENCE_LIST, UNPACK_SEQUENCE_LIST, UNPACK_EX, _SPECIALIZE_STORE_ATTR, _STORE_ATTR, STORE_ATTR, DELETE_ATTR, STORE_GLOBAL, DELETE_GLOBAL, LOAD_LOCALS, LOAD_FROM_DICT_OR_GLOBALS, LOAD_NAME, _SPECIALIZE_LOAD_GLOBAL, _LOAD_GLOBAL, _PUSH_NULL_CONDITIONAL, LOAD_GLOBAL, _GUARD_GLOBALS_VERSION, _LOAD_GLOBAL_MODULE, _LOAD_GLOBAL_BUILTINS, LOAD_GLOBAL_MODULE, LOAD_GLOBAL_BUILTIN, DELETE_FAST, MAKE_CELL, DELETE_DEREF, LOAD_FROM_DICT_OR_DEREF, LOAD_DEREF, STORE_DEREF, COPY_FREE_VARS, BUILD_STRING, BUILD_INTERPOLATION, BUILD_TEMPLATE, BUILD_TUPLE, BUILD_LIST, LIST_EXTEND, SET_UPDATE, BUILD_SET, BUILD_MAP, SETUP_ANNOTATIONS, DICT_UPDATE, DICT_MERGE, MAP_ADD, _SPECIALIZE_LOAD_SUPER_ATTR, _LOAD_SUPER_ATTR, LOAD_SUPER_ATTR, INSTRUMENTED_LOAD_SUPER_ATTR, LOAD_SUPER_ATTR_ATTR, LOAD_SUPER_ATTR_METHOD, _SPECIALIZE_LOAD_ATTR, _LOAD_ATTR, LOAD_ATTR, _GUARD_TYPE_VERSION_AND_LOCK, _CHECK_MANAGED_OBJECT_HAS_VALUES, _LOAD_ATTR_INSTANCE_VALUE, LOAD_ATTR_INSTANCE_VALUE, _LOAD_ATTR_MODULE, LOAD_ATTR_MODULE, _LOAD_ATTR_WITH_HINT, LOAD_ATTR_WITH_HINT, _LOAD_ATTR_SLOT, LOAD_ATTR_SLOT, _CHECK_ATTR_CLASS, _LOAD_ATTR_CLASS, LOAD_ATTR_CLASS, LOAD_ATTR_CLASS_WITH_METACLASS_CHECK, _LOAD_ATTR_PROPERTY_FRAME, LOAD_ATTR_PROPERTY, LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN, _GUARD_DORV_NO_DICT, _STORE_ATTR_INSTANCE_VALUE, STORE_ATTR_INSTANCE_VALUE, _STORE_ATTR_WITH_HINT, STORE_ATTR_WITH_HINT, _STORE_ATTR_SLOT, STORE_ATTR_SLOT, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, COMPARE_OP, _COMPARE_OP_FLOAT, _COMPARE_OP_INT, _COMPARE_OP_STR, COMPARE_OP_FLOAT, COMPARE_OP_INT, COMPARE_OP_STR, IS_OP, _CONTAINS_OP, _SPECIALIZE_CONTAINS_OP, CONTAINS_OP, _GUARD_TOS_ANY_SET, _CONTAINS_OP_SET, CONTAINS_OP_SET, _CONTAINS_OP_DICT, CONTAINS_OP_DICT, CHECK_EG_MATCH, CHECK_EXC_MATCH, IMPORT_NAME, IMPORT_FROM, JUMP_FORWARD, JUMP_BACKWARD_NO_INTERRUPT, _SPECIALIZE_JUMP_BACKWARD, _JIT, JUMP_BACKWARD, JUMP_BACKWARD_NO_JIT, JUMP_BACKWARD_JIT, ENTER_EXECUTOR, _POP_JUMP_IF_FALSE, _POP_JUMP_IF_TRUE, _IS_NONE, POP_JUMP_IF_TRUE, POP_JUMP_IF_FALSE, POP_JUMP_IF_NONE, POP_JUMP_IF_NOT_NONE, GET_LEN, MATCH_CLASS, MATCH_MAPPING, MATCH_SEQUENCE, MATCH_KEYS, GET_ITER, GET_YIELD_FROM_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, FOR_ITER, INSTRUMENTED_FOR_ITER, _ITER_CHECK_LIST, _ITER_JUMP_LIST, _ITER_NEXT_LIST, FOR_ITER_LIST, _ITER_CHECK_TUPLE, _ITER_JUMP_TUPLE, _ITER_NEXT_TUPLE, FOR_ITER_TUPLE, _ITER_CHECK_RANGE, _ITER_JUMP_RANGE, _ITER_NEXT_RANGE, FOR_ITER_RANGE, _FOR_ITER_GEN_FRAME, FOR_ITER_GEN, LOAD_SPECIAL, WITH_EXCEPT_START, PUSH_EXC_INFO, _GUARD_DORV_VALUES_INST_ATTR_FROM_DICT, _GUARD_KEYS_VERSION, _LOAD_ATTR_METHOD_WITH_VALUES, LOAD_ATTR_METHOD_WITH_VALUES, _LOAD_ATTR_METHOD_NO_DICT, LOAD_ATTR_METHOD_NO_DICT, _LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES, LOAD_ATTR_NONDESCRIPTOR_WITH_VALUES, _LOAD_ATTR_NONDESCRIPTOR_NO_DICT, LOAD_ATTR_NONDESCRIPTOR_NO_DICT, _CHECK_ATTR_METHOD_LAZY_DICT, _LOAD_ATTR_METHOD_LAZY_DICT, LOAD_ATTR_METHOD_LAZY_DICT, _SPECIALIZE_CALL, _MAYBE_EXPAND_METHOD, _DO_CALL, _MONITOR_CALL, CALL, INSTRUMENTED_CALL, _PY_FRAME_GENERAL, _CHECK_FUNCTION_VERSION, _CHECK_FUNCTION_VERSION_INLINE, _CHECK_RECURSION_REMAINING, CALL_PY_GENERAL, _CHECK_METHOD_VERSION, _EXPAND_METHOD, CALL_BOUND_METHOD_GENERAL, _CHECK_IS_NOT_PY_CALLABLE, _CALL_NON_PY_GENERAL, CALL_NON_PY_GENERAL, _CHECK_CALL_BOUND_METHOD_EXACT_ARGS, _INIT_CALL_BOUND_METHOD_EXACT_ARGS, _CHECK_FUNCTION_EXACT_ARGS, _CHECK_STACK_SPACE, _INIT_CALL_PY_EXACT_ARGS, CALL_BOUND_METHOD_EXACT_ARGS, CALL_PY_EXACT_ARGS, _GUARD_NOS_NULL, _GUARD_CALLABLE_TYPE_1, _CALL_TYPE_1, CALL_TYPE_1, _GUARD_CALLABLE_STR_1, _CALL_STR_1, CALL_STR_1, _GUARD_CALLABLE_TUPLE_1, _CALL_TUPLE_1, CALL_TUPLE_1, _CHECK_AND_ALLOCATE_OBJECT, _CREATE_INIT_FRAME, CALL_ALLOC_AND_ENTER_INIT, EXIT_INIT_CHECK, _CALL_BUILTIN_CLASS, CALL_BUILTIN_CLASS, _CALL_BUILTIN_O, CALL_BUILTIN_O, _CALL_BUILTIN_FAST, CALL_BUILTIN_FAST, _CALL_BUILTIN_FAST_WITH_KEYWORDS, CALL_BUILTIN_FAST_WITH_KEYWORDS, _GUARD_CALLABLE_LEN, _CALL_LEN, CALL_LEN, CALL_ISINSTANCE, CALL_LIST_APPEND, _CALL_METHOD_DESCRIPTOR_O, CALL_METHOD_DESCRIPTOR_O, _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS, CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS, _CALL_METHOD_DESCRIPTOR_NOARGS, CALL_METHOD_DESCRIPTOR_NOARGS, _CALL_METHOD_DESCRIPTOR_FAST, CALL_METHOD_DESCRIPTOR_FAST, _MONITOR_CALL_KW, _MAYBE_EXPAND_METHOD_KW, _DO_CALL_KW, _PY_FRAME_KW, _CHECK_FUNCTION_VERSION_KW, CALL_KW_PY, _CHECK_METHOD_VERSION_KW, _EXPAND_METHOD_KW, CALL_KW_BOUND_METHOD, _SPECIALIZE_CALL_KW, CALL_KW, INSTRUMENTED_CALL_KW, _CHECK_IS_NOT_PY_CALLABLE_KW, _CALL_KW_NON_PY, CALL_KW_NON_PY, _MAKE_CALLARGS_A_TUPLE, _DO_CALL_FUNCTION_EX, CALL_FUNCTION_EX, INSTRUMENTED_CALL_FUNCTION_EX, MAKE_FUNCTION, SET_FUNCTION_ATTRIBUTE, RETURN_GENERATOR, BUILD_SLICE, CONVERT_VALUE, FORMAT_SIMPLE, FORMAT_WITH_SPEC, COPY, _SPECIALIZE_BINARY_OP, _BINARY_OP, BINARY_OP, SWAP, INSTRUMENTED_JUMP_FORWARD, _MONITOR_JUMP_BACKWARD, INSTRUMENTED_NOT_TAKEN, INSTRUMENTED_JUMP_BACKWARD, INSTRUMENTED_POP_JUMP_IF_TRUE, INSTRUMENTED_POP_JUMP_IF_FALSE, INSTRUMENTED_POP_JUMP_IF_NONE, INSTRUMENTED_POP_JUMP_IF_NOT_NONE] at hv ⊢ <;> first
        | eff_auto
        | (refine Eff.cast (m := _) ?_ (by omega) (by omega); eff_auto))

end PyLean.Bytecode
