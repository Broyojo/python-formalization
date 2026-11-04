import PyLean.Bytecode.Props
import PyLean.Bytecode.SpecLoadAttr

/-!
The recursion budget in the frame-pushing `LOAD_ATTR` specializations, `Python/bytecodes.c`.

`CALL_PY_GENERAL`, `CALL_PY_EXACT_ARGS`, `CALL_BOUND_METHOD_*` and `CALL_KW_PY` push the callee's
frame with `_PUSH_FRAME` only after `_CHECK_RECURSION_REMAINING` (`:4611-4613`,
`DEOPT_IF(tstate->py_recursion_remaining <= 1)`), because `_PUSH_FRAME` (`:4628-4642`) decrements the
counter and tests nothing; the generic `LOAD_ATTR` reaches the same callee through the C call of
`property.__get__` or `slot_tp_getattr_hook`, which enforces the limit (`_Py_EnterRecursivePy`).
`LOAD_ATTR_PROPERTY` (`:3070-3077`) and `LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN` (`:3098-3105`) are
`_GUARD_TYPE_VERSION + _CHECK_PEP_523 + frame op + _SAVE_RETURN_OFFSET + _PUSH_FRAME`, with no such
check, so with the budget spent they enter the getter anyway.
-/

namespace PyLean.Bytecode

open Uop

/-- A class `C` (version 7) with an empty dict at 0 and the class at 1; the getter at 2, a function
(version 9) of code 2; an instance of `C` at 3. Code 3 is the running code, with the name `p`. -/
def attrRecHeap : Array Obj :=
  #[.dict {}, .cls { name := "C", dict := 0, version := 7 }, .func { code := 2, version := 9 }, .inst { cls := .ref 1 }]

/-- `o.p` with `py_recursion_remaining = 0`. -/
def attrRecSt : St :=
  { regs := { rt := { heap := attrRecHeap, pyRecursionRemaining := 0 }, frame := { code := 3 } },
    stack := [.ref 3] }

def attrRecProgram (argc : Nat) : Program :=
  #[{}, {}, { argcount := argc, nlocalsplus := argc }, { names := #["p"] }]

/-- `LOAD_ATTR_PROPERTY` specialized for `C.p` with the getter at 2: cache
`[type version, fget, func version]`. -/
def propRecEnv : Env :=
  { P := attrRecProgram 1, om := Proto.mkOM #[] 0, ctx := ⟨fun _ _ => throw .fuel⟩,
    opcode := .LOAD_ATTR_PROPERTY, oparg := 0, this := 0, cache := [.tagged 7, .ref 2, .tagged 9] }

/-- `LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN` with `C.__getattribute__` the function at 2: cache
`[type version, func version, getattribute]`. -/
def gaRecEnv : Env :=
  { P := attrRecProgram 2, om := Proto.mkOM #[] 0, ctx := ⟨fun _ _ => throw .fuel⟩,
    opcode := .LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN, oparg := 0, this := 0, cache := [.tagged 7, .tagged 9, .ref 2] }

/-- With the recursion budget spent (`py_recursion_remaining <= 1`), `LOAD_ATTR_PROPERTY` does not
enter the getter's frame: it exits to the generic `LOAD_ATTR` or raises, as every `CALL` form that
pushes a Python frame does through `_CHECK_RECURSION_REMAINING`, so that the specialized form keeps
the generic form's `RecursionError`. False: it pushes the frame and completes. -/
def PropertyFrameChecksRecursion : Prop := ∀ (e : Env) (s : St), s.regs.rt.pyRecursionRemaining ≤ 1 →
  completed (LOAD_ATTR_PROPERTY e s) = false

theorem propertyFrameChecksRecursion_refuted : ¬PropertyFrameChecksRecursion := by
  intro h
  exact absurd (h propRecEnv attrRecSt (by decide)) (by decide)

/-- The same for `LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN` and the overriding `__getattribute__`. False: it
pushes the frame and completes. -/
def GetattributeFrameChecksRecursion : Prop := ∀ (e : Env) (s : St), s.regs.rt.pyRecursionRemaining ≤ 1 →
  completed (LOAD_ATTR_GETATTRIBUTE_OVERRIDDEN e s) = false

theorem getattributeFrameChecksRecursion_refuted : ¬GetattributeFrameChecksRecursion := by
  intro h
  exact absurd (h gaRecEnv attrRecSt (by decide)) (by decide)

end PyLean.Bytecode
