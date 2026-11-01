import PyLean.Bytecode.SpecHeap
import PyLean.Bytecode.Frames
import PyLean.Bytecode.FrameProps
import PyLean.Bytecode.Builtins

/-!
The registry-facing statements: closed propositions over the theorems in
`SpecBasic.lean`, `SpecHeap.lean`, `StackEffect.lean` and `Frames.lean`, and the
refutations.
-/

namespace PyLean.Bytecode

open Uop

/-- Stack depth on entry, the invariant the compiler's `stackdepth` establishes. -/
abbrev Deep (s : St) (n : Nat) : Prop := n ≤ s.stack.length

/-- `BINARY_OP_ADD_INT` is `BINARY_OP` for `+` and `+=` on every stack. -/
def BinaryAddInt : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 0 ∨ e.oparg = 13) →
  execOp e .BINARY_OP_ADD_INT s = execOp e .BINARY_OP s
theorem binaryAddInt_proven : BinaryAddInt := fun e h s d o => binaryAddInt_spec e h s d o

def BinarySubInt : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 10 ∨ e.oparg = 23) →
  execOp e .BINARY_OP_SUBTRACT_INT s = execOp e .BINARY_OP s
theorem binarySubInt_proven : BinarySubInt := fun e h s d o => binarySubInt_spec e h s d o

def BinaryMulInt : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 5 ∨ e.oparg = 18) →
  execOp e .BINARY_OP_MULTIPLY_INT s = execOp e .BINARY_OP s
theorem binaryMulInt_proven : BinaryMulInt := fun e h s d o => binaryMulInt_spec e h s d o

def BinaryAddFloat : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 0 ∨ e.oparg = 13) →
  execOp e .BINARY_OP_ADD_FLOAT s = execOp e .BINARY_OP s
theorem binaryAddFloat_proven : BinaryAddFloat := fun e h s d o => binaryAddFloat_spec e h s d o

def BinarySubFloat : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 10 ∨ e.oparg = 23) →
  execOp e .BINARY_OP_SUBTRACT_FLOAT s = execOp e .BINARY_OP s
theorem binarySubFloat_proven : BinarySubFloat := fun e h s d o => binarySubFloat_spec e h s d o

def BinaryMulFloat : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 5 ∨ e.oparg = 18) →
  execOp e .BINARY_OP_MULTIPLY_FLOAT s = execOp e .BINARY_OP s
theorem binaryMulFloat_proven : BinaryMulFloat := fun e h s d o => binaryMulFloat_spec e h s d o

def BinaryAddUnicode : Prop := ∀ (e : Env), Lawful e.om → ∀ s, Deep s 2 → (e.oparg = 0 ∨ e.oparg = 13) →
  execOp e .BINARY_OP_ADD_UNICODE s = execOp e .BINARY_OP s
theorem binaryAddUnicode_proven : BinaryAddUnicode := fun e h s d o => binaryAddUnicode_spec e h s d o

/-- `list[int]`: all stacks, all indices, including negative, too large and huge. -/
def SubscrListInt : Prop := ∀ (e : Env), Lawful e.om → e.oparg = 26 → ∀ s, Deep s 2 →
  (∀ v ∈ s.stack, Live s.regs.rt v) →
  execOp e .BINARY_OP_SUBSCR_LIST_INT s = execOp e .BINARY_OP s
theorem subscrListInt_proven : SubscrListInt := fun e h o s d l => subscrListInt_spec e h o s d l

/-- Stack effects, against `_PyOpcode_num_popped`/`_pushed`, for a representative set
of opcodes, over all stacks and args. -/
def StackEffects : Prop := ∀ (e : Env),
  Eff (numPopped .POP_TOP e.oparg) (numPushed .POP_TOP e.oparg) (execOp e .POP_TOP) ∧
  Eff (numPopped .BUILD_TUPLE e.oparg) (numPushed .BUILD_TUPLE e.oparg) (execOp e .BUILD_TUPLE) ∧
  Eff (numPopped .BUILD_MAP e.oparg) (numPushed .BUILD_MAP e.oparg) (execOp e .BUILD_MAP) ∧
  Eff (numPopped .GET_ITER e.oparg) (numPushed .GET_ITER e.oparg) (execOp e .GET_ITER) ∧
  Eff (numPopped .IS_OP e.oparg) (numPushed .IS_OP e.oparg) (execOp e .IS_OP) ∧
  Eff (numPopped .GET_LEN e.oparg) (numPushed .GET_LEN e.oparg) (execOp e .GET_LEN) ∧
  Eff (numPopped .MATCH_KEYS e.oparg) (numPushed .MATCH_KEYS e.oparg) (execOp e .MATCH_KEYS) ∧
  Eff (numPopped .IMPORT_FROM e.oparg) (numPushed .IMPORT_FROM e.oparg) (execOp e .IMPORT_FROM) ∧
  Eff (numPopped .STORE_FAST e.oparg) (numPushed .STORE_FAST e.oparg) (execOp e .STORE_FAST) ∧
  Eff (numPopped .BUILD_SLICE e.oparg) (numPushed .BUILD_SLICE e.oparg) (execOp e .BUILD_SLICE)
theorem stackEffects_proven : StackEffects := fun e =>
  ⟨eff_pop_top e, eff_build_tuple e, eff_build_map e, eff_get_iter e, eff_is_op e, eff_get_len e,
   eff_match_keys e, eff_import_from e, eff_store_fast e, eff_build_slice e⟩

/-! ## The recursion check -/

/-- Whether an instruction raised, or completed. -/
def completed {σ : Type} : EStateM.Result Err σ Unit → Bool
  | .ok _ _ => true
  | .error .dispatch _ => true
  | _ => false

/-- A suspended generator at address 0. -/
def susp : GenObj := { frameState := -2, frame := { code := 2 } }

/-- `yield from` on it with the recursion budget spent. -/
def recSt : St :=
  { regs := { rt := { heap := #[.gen susp], pyRecursionRemaining := 0 } },
    stack := [.none, .ref 0] }

def recEnv : Env :=
  { P := #[{}, {}, {}], om := Proto.mkOM #[] 0, ctx := ⟨fun _ _ => throw .fuel⟩,
    opcode := .SEND_GEN, oparg := 0, this := 0 }

/-- `SEND_GEN` is `SEND`, the same as every other specialization is its generic form.
False: the generic path goes through `start_frame`, which enforces the recursion
limit, and `_PUSH_FRAME` does not check it. -/
def SendGenAgrees : Prop := ∀ (e : Env) (s : St),
  completed (execOp e .SEND_GEN s) = completed (execOp e .SEND s)

theorem sendGenAgrees_refuted : ¬SendGenAgrees := by
  intro h
  exact absurd (h recEnv recSt) (by decide)

/-! ## `__abstractmethods__` -/

/-- A class with an abstract method, `__init__` a simple function, specialized. -/
def absSt : St :=
  { regs := { rt := { heap := #[.dict {}, .cls { name := "C", dict := 0, version := 7,
                                                 abstractMethods := ["f"] },
                                .func { code := 2 }] },
              frame := { code := 2 } },
    stack := [.null, .ref 1] }

def absEnv : Env :=
  { P := #[{}, {}, { argcount := 1, nlocalsplus := 1 }], om := Proto.mkOM #[] 0,
    ctx := ⟨fun _ _ => throw .fuel⟩, opcode := .CALL_ALLOC_AND_ENTER_INIT, oparg := 0, this := 0,
    cache := [.tagged 7, .ref 2] }

/-- Instantiating a class with abstract methods never allocates: `object_new` refuses
(`Objects/typeobject.c:7477`). False for `CALL_ALLOC_AND_ENTER_INIT`, which skips
`object_new` and which `specialize_class_call` does not withhold from such a class. -/
def AbstractNeverAllocates : Prop := ∀ (e : Env) (s : St) (k : ClassObj),
  s.stack.getD 1 .null = .ref 1 → s.regs.rt.heap[1]? = some (.cls k) → k.abstractMethods ≠ [] →
  completed (CALL_ALLOC_AND_ENTER_INIT e s) = false

theorem abstractNeverAllocates_refuted : ¬AbstractNeverAllocates := by
  intro h
  have := h absEnv absSt { name := "C", dict := 0, version := 7, abstractMethods := ["f"] }
    rfl rfl (by decide)
  exact absurd this (by decide)

/-- The laws the specialization theorems assume hold of the object model the difftest
runs. Not proven, so those theorems are conditional on it. It may need restating:
`binaryOpImpl` calls the `getItem` of the next fuel level down, so the law `subscr`
compares two fuel depths, and they can differ at the fuel limit. -/
def LawfulBuiltin : Prop := ∀ P : Program, Lawful (Proto.builtinOM P)

/-! ## Named gaps

Each is an `.open` entry and a named exclusion of `difftest/bytecode_diff.py`. -/

/-- A template applied to `None` does not reach the model's `fault`. False today: a
template with a `%` in it does. -/
def FormatRuns : Prop :=
  ∀ (om : ObjModel) (ctx : Ctx) (a : String) (b : List UInt8) (rt rt' : Rt) (m : String),
    Proto.seqBinary om ctx 6 (.str a) .none rt ≠ .error (.fault m) rt' ∧
    Proto.seqBinary om ctx 6 (.bytes b) .none rt ≠ .error (.fault m) rt'

/-- `float ** float` does not reach the model's `fault`. False today: a complex result does. -/
def FloatPowRuns : Prop :=
  ∀ (a b : UInt64) (rt rt' : Rt) (m : String), Proto.floatBinary 8 a b rt ≠ .error (.fault m) rt'

/-- `int << int` does not reach the model's `fault`. False today: a huge shift does. -/
def HugeShiftRuns : Prop :=
  ∀ (a b : Int) (rt rt' : Rt) (m : String), Proto.intBinary 3 a b rt ≠ .error (.fault m) rt'

/-- An `.open` entry whose property cannot be written until the model has what the
entry's notes name. No theorem claims it. -/
def NotYetStated : Prop := True

end PyLean.Bytecode
