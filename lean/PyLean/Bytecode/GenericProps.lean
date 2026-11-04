import PyLean.Bytecode.FastProps

/-!
The generic forms and failure paths of `Python/bytecodes.c`, stated over every object model:
which slot is called on which operands with which oparg, and what is left on the stack when the
slot raises. A body that swapped the operands, ignored the oparg, popped where C keeps
(`ERROR_NO_POP`), or turned an exception into a normal result fails these.
-/

namespace PyLean.Bytecode

open Uop

/-- `BINARY_OP` (`Python/bytecodes.c:5940`: `_SPECIALIZE_BINARY_OP + _RECORD_TOS_TYPE +
_RECORD_NOS_TYPE + _BINARY_OP + POP_TOP + POP_TOP`): `_BINARY_OP` (`:5924-5938`) calls
`_PyEval_BinaryOps[oparg](lhs, rhs)`, `lhs` being the second value, and replaces both operands with
the result; when the slot raises it leaves through `ERROR_NO_POP` with both operands still on the
stack. For every object model, every oparg and every pair of operands. -/
def BinaryOpRules : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val) (l r : Val),
  (∀ res rt, e.om.binaryOp e.ctx e.oparg l r regs.rt = .ok res rt →
    execOp e .BINARY_OP ⟨regs, r :: l :: rest⟩ = .ok () ⟨{ regs with rt := rt }, res :: rest⟩) ∧
  (∀ x rt, e.om.binaryOp e.ctx e.oparg l r regs.rt = .error x rt →
    execOp e .BINARY_OP ⟨regs, r :: l :: rest⟩ = .error x ⟨{ regs with rt := rt }, r :: l :: rest⟩)

theorem binaryOpRules_proven : BinaryOpRules := by
  intro e regs rest l r
  constructor
  · intro res rt h
    bc_simp [execOp, BINARY_OP, _SPECIALIZE_BINARY_OP, _BINARY_OP, h]
  · intro x rt h
    bc_simp [execOp, BINARY_OP, _SPECIALIZE_BINARY_OP, _BINARY_OP, h]

/-- `COMPARE_OP` (`Python/bytecodes.c:3251`, `_COMPARE_OP` `:3232-3249`): it calls
`PyObject_RichCompare(left, right, oparg >> 5)`, `left` being the second value; without bit 16 it
pushes that result as it is, with bit 16 it pushes `PyObject_IsTrue` of it as a bool; either call
raising pops both operands (`DECREF_INPUTS(); ERROR_IF`) and propagates. For every object model. -/
def CompareOpRules : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val) (l r : Val),
  (∀ res rt, e.om.richCompare e.ctx l r (e.oparg >>> 5) regs.rt = .ok res rt →
    e.oparg &&& 16 = 0 →
    execOp e .COMPARE_OP ⟨regs, r :: l :: rest⟩ = .ok () ⟨{ regs with rt := rt }, res :: rest⟩) ∧
  (∀ res rt b rt', e.om.richCompare e.ctx l r (e.oparg >>> 5) regs.rt = .ok res rt →
    e.oparg &&& 16 ≠ 0 → e.om.isTrue e.ctx res rt = .ok b rt' →
    execOp e .COMPARE_OP ⟨regs, r :: l :: rest⟩ = .ok () ⟨{ regs with rt := rt' }, .bool b :: rest⟩) ∧
  (∀ res rt x rt', e.om.richCompare e.ctx l r (e.oparg >>> 5) regs.rt = .ok res rt →
    e.oparg &&& 16 ≠ 0 → e.om.isTrue e.ctx res rt = .error x rt' →
    execOp e .COMPARE_OP ⟨regs, r :: l :: rest⟩ = .error x ⟨{ regs with rt := rt' }, rest⟩) ∧
  (∀ x rt, e.om.richCompare e.ctx l r (e.oparg >>> 5) regs.rt = .error x rt →
    execOp e .COMPARE_OP ⟨regs, r :: l :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)

theorem compareOpRules_proven : CompareOpRules := by
  intro e regs rest l r
  refine ⟨fun res rt h h16 => ?_, fun res rt b rt' h h16 hb => ?_, fun res rt x rt' h h16 hb => ?_,
    fun x rt h => ?_⟩
  · have : (e.oparg &&& 16 != 0) = false := by simp [h16]
    bc_simp [execOp, COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h, this]
  · have : (e.oparg &&& 16 != 0) = true := by simpa using h16
    bc_simp [execOp, COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h, this, hb]
  · have : (e.oparg &&& 16 != 0) = true := by simpa using h16
    bc_simp [execOp, COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h, this, hb]
  · bc_simp [execOp, COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h]

/-- `FOR_ITER` over an iterator object (`NULL` in the index slot), `_FOR_ITER`
(`Python/bytecodes.c:3810-3821`) with `_PyForIter_VirtualIteratorNext` (`Python/ceval.c:3709-3739`):
when `tp_iternext` raises something other than `StopIteration` the instruction leaves through
`ERROR_NO_POP` with the exception and both slots kept; when it raises `StopIteration` that is
cleared and the loop ends, jumping over `END_FOR` with both slots kept. -/
def ForIterRaises : Prop := ∀ (e : Env) (regs : Regs) (it : Val) (rest : List Val) (x : Val) (rt : Rt)
    (b : Bool) (rt' : Rt),
  e.om.iterNext e.ctx it regs.rt = .error (.exc x) rt →
  givenMatches x 8 (.cls "StopIteration") rt = .ok b rt' →
  (b = false → execOp e .FOR_ITER ⟨regs, .null :: it :: rest⟩ =
    .error (.exc x) ⟨{ regs with rt := rt' }, .null :: it :: rest⟩) ∧
  (b = true → execOp e .FOR_ITER ⟨regs, .null :: it :: rest⟩ =
    .error .dispatch ⟨{ regs with rt := rt', next := regs.next + e.oparg + 1 }, .null :: it :: rest⟩)

theorem forIterRaises_proven : ForIterRaises := by
  intro e regs it rest x rt b rt' h hm
  constructor
  · rintro rfl
    bc_simp [execOp, FOR_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, virtualNext, iterStep, tryExc, h, hm]
  · rintro rfl
    have hj : ∀ (r : Regs), jumpBy ((e.oparg : Int) + 1) r = .ok () { r with next := r.next + e.oparg + 1 } :=
      fun r => jumpBy_succ r e.oparg
    bc_simp [execOp, FOR_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, virtualNext, iterStep, tryExc, h, hm, hj]

/-- `PUSH_EXC_INFO` (`Python/bytecodes.c:4213-4226`): the handled exception becomes the one on top
of the stack (`exc_info->exc_value = exc`), and below it goes the previous handled exception, or
`None` when there was none, for `POP_EXCEPT` to restore. -/
def PushExcInfoRules : Prop := ∀ (regs : Regs) (exc : Val) (rest : List Val) (top : Val) (chain : List Val),
  regs.rt.excInfo = top :: chain →
  PUSH_EXC_INFO ⟨regs, exc :: rest⟩ =
    .ok () ⟨{ regs with rt := { regs.rt with excInfo := exc :: chain } },
      exc :: (if top = .null then .none else top) :: rest⟩

theorem pushExcInfoRules_proven : PushExcInfoRules := by
  intro regs exc rest top chain h
  by_cases ht : top = .null
  · subst ht
    bc_simp [PUSH_EXC_INFO, getExcInfoTop, setExcInfoTop, h]
  · bc_simp [PUSH_EXC_INFO, getExcInfoTop, setExcInfoTop, h, ht]

/-- `RAISE_VARARGS` (`Python/bytecodes.c:1531-1542`): with `oparg` 1 it raises the top of the stack
and with `oparg` 2 it raises the second value with the top as its cause (`cause = args[1]`,
`exc = args[0]`), as `do_raise` does, popping the operands; with `oparg` 0 and a handled exception
it re-raises that exception through `exception_unwind` (`do_raise` returning 1), and with none it
raises `RuntimeError`. -/
def RaiseVarargsRules : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val),
  (e.oparg = 1 → ∀ x err rt, doRaise e.om e.ctx x .null regs.rt = .error err rt →
    execOp e .RAISE_VARARGS ⟨regs, x :: rest⟩ = .error err ⟨{ regs with rt := rt }, rest⟩) ∧
  (e.oparg = 2 → ∀ x c err rt, doRaise e.om e.ctx x c regs.rt = .error err rt →
    execOp e .RAISE_VARARGS ⟨regs, c :: x :: rest⟩ = .error err ⟨{ regs with rt := rt }, rest⟩) ∧
  (e.oparg = 0 → ∀ ev, topmostExc regs.rt = .ok ev regs.rt → ev ≠ .none → ev ≠ .null →
    execOp e .RAISE_VARARGS ⟨regs, rest⟩ = .error (.unwind ev) ⟨regs, rest⟩) ∧
  (e.oparg = 0 → ∀ err rt, runtimeError (α := Unit) "No active exception to reraise" regs.rt = .error err rt →
    (topmostExc regs.rt = .ok .none regs.rt ∨ topmostExc regs.rt = .ok .null regs.rt) →
    execOp e .RAISE_VARARGS ⟨regs, rest⟩ = .error err ⟨{ regs with rt := rt }, rest⟩)

theorem raiseVarargsRules_proven : RaiseVarargsRules := by
  intro e regs rest
  refine ⟨fun h1 x err rt h => ?_, fun h2 x c err rt h => ?_, fun h0 ev hev h1 h2 => ?_,
    fun h0 err rt h ht => ?_⟩
  · bc_simp [execOp, RAISE_VARARGS, h1, h]
  · bc_simp [execOp, RAISE_VARARGS, h2, h]
  · have hb1 : (ev == .none) = false := by simpa using h1
    have hb2 : (ev == .null) = false := by simpa using h2
    bc_simp [execOp, RAISE_VARARGS, h0, doRaise, hev, hb1, hb2, h1, h2]
  · rcases ht with ht | ht
    · bc_simp [execOp, RAISE_VARARGS, h0, doRaise, ht, h]
    · bc_simp [execOp, RAISE_VARARGS, h0, doRaise, ht, h]

/-- `not x` compiles to `TO_BOOL` then `UNARY_NOT` (`Python/bytecodes.c:477-482`): for every
object model it pushes the negation of what `PyObject_IsTrue` answers, and propagates its
exception with the operand popped. -/
def NotRules : Prop := ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val),
  (∀ b rt, e.om.isTrue e.ctx v regs.rt = .ok b rt →
    (execOp e .TO_BOOL *> execOp e .UNARY_NOT) ⟨regs, v :: rest⟩ =
      .ok () ⟨{ regs with rt := rt }, .bool (!b) :: rest⟩) ∧
  (∀ x rt, e.om.isTrue e.ctx v regs.rt = .error x rt →
    (execOp e .TO_BOOL *> execOp e .UNARY_NOT) ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)

theorem notRules_proven : NotRules := by
  intro e regs v rest
  constructor
  · intro b rt h
    bc_simp [execOp, TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, UNARY_NOT, h, SeqRight.seqRight,
      EStateM.seqRight]
  · intro x rt h
    bc_simp [execOp, TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, h, SeqRight.seqRight, EStateM.seqRight]

/-- `END_FOR` is `no_save_ip` (`Python/bytecodes.c:393-398`): dispatching it leaves
`frame->instr_ptr` where it was, where an instruction without the annotation (`POP_TOP`, the same
`(value --)` body) records its own address there; then it pops its operand. -/
def EndForRules : Prop := ∀ (e : Env) (s : St) (regs : Regs) (v : Val) (rest : List Val),
  (beginInstr .END_FOR s).regs.frame.instrPtr = s.regs.frame.instrPtr ∧
  (beginInstr .POP_TOP s).regs.frame.instrPtr = s.regs.next ∧
  execOp e .END_FOR ⟨regs, v :: rest⟩ = .ok () ⟨regs, rest⟩

theorem endForRules_proven : EndForRules := by
  intro e s regs v rest
  refine ⟨by simp [beginInstr], by simp [beginInstr], ?_⟩
  bc_simp [execOp, END_FOR]

/-- `RETURN_VALUE` from a generator's frame (`_RETURN_VALUE`, `Python/bytecodes.c:1573-1589`, with
`_PyEval_FrameClearAndPop`'s `clear_gen_frame`, `Python/ceval.c:2001-2016`): besides what it does
for a thread's frame (`ReturnValue`), the generator is marked `FRAME_CLEARED`, `tstate->exc_info`
goes back to the item below the generator's own, the generator's handled exception is cleared
(`_PyErr_ClearExcState`), and its frame's locals and stack are dropped. The hypotheses are the
asserts of `clear_gen_frame`: a generator's frame belongs to a live generator, and its
`gi_exc_state` is the top of the `exc_info` chain. A frame owned by the interpreter never runs
`RETURN_VALUE` (`assert(frame->owner != FRAME_OWNED_BY_INTERPRETER)`, `:1574`). -/
def ReturnValueGen : Prop :=
  ∀ (regs : Regs) (retval : Val) (rest : List Val) (caller : Frame) (prev : List Frame) (g : Addr)
    (o : GenObj) (top : Val) (chain : List Val),
    regs.prev = caller :: prev → regs.frame.owner = .generator g →
    regs.rt.heap[g]? = some (.gen o) → regs.rt.excInfo = top :: chain →
    RETURN_VALUE ⟨regs, retval :: rest⟩ =
      .ok () ⟨{ regs with
        rt := { regs.rt with
          pyRecursionRemaining := regs.rt.pyRecursionRemaining + 1
          excInfo := chain
          heap := (regs.rt.heap.setIfInBounds g
            (.gen { o with frameState := 5, excValue := .null, frame := { o.frame with fast := #[], stack := [] } })) }
        frame := caller, prev := prev, next := caller.instrPtr + caller.returnOffset },
        retval :: caller.stack⟩

theorem returnValueGen_proven : ReturnValueGen := by
  intro regs retval rest caller prev g o top chain hp ho hg he
  obtain ⟨rt, frame, pv, next⟩ := regs
  simp only at hp ho hg he
  subst hp
  bc_simp [RETURN_VALUE, getFrame, leaveRecursivePy, popToPrevious, frameClearAndPop, ho, clearGenFrame,
    getGen, hg, popExcState, he, setObj, loadIp]

/-- `_CREATE_INIT_FRAME` (`Python/bytecodes.c:4790-4813`): when `_PyEvalFramePushAndInit` cannot
build `__init__`'s frame (a bad argument count, say) the error is raised in the caller with
`init`, `self` and the arguments consumed, no shim frame on the chain, the caller's
`return_offset` untouched and the recursion counter unchanged; when it can, the `_Py_InitCleanup`
shim holding `self` becomes the frame `__init__` returns to, the caller records
`return_offset = 1 + INLINE_CACHE_ENTRIES_CALL`, and one recursion unit is taken for the shim. -/
def CreateInitFrameRules : Prop := ∀ (e : Env) (regs : Regs) (init self : Val) (args rest : List Val),
  args.length = e.oparg →
  (∀ x rt, framePushAndInit e.P init .null (self :: args) [] regs.rt = .error x rt →
    _CREATE_INIT_FRAME e ⟨regs, args.reverse ++ self :: init :: rest⟩ =
      .error x ⟨{ regs with rt := rt }, rest⟩) ∧
  (∀ nf rt, framePushAndInit e.P init .null (self :: args) [] regs.rt = .ok nf rt →
    _CREATE_INIT_FRAME e ⟨regs, args.reverse ++ self :: init :: rest⟩ = .ok nf
      ⟨{ regs with
          rt := { rt with pyRecursionRemaining := rt.pyRecursionRemaining - 1 }
          frame := { code := initCleanupIdx, stack := [self], owner := .thread }
          prev := { regs.frame with returnOffset := 1 + 3, stack := rest } :: regs.prev }, [self]⟩)

theorem createInitFrameRules_proven : CreateInitFrameRules := by
  intro e regs init self args rest hlen
  have hn : e.oparg + 2 = args.reverse.length + 2 := by simp [hlen]
  have ht : (args.reverse ++ self :: init :: rest).take (e.oparg + 2) = args.reverse ++ [self, init] := by
    rw [hn, List.take_append, List.take_of_length_le (by simp)]; simp
  have hd : (args.reverse ++ self :: init :: rest).drop (e.oparg + 2) = rest := by
    rw [hn, List.drop_append]; simp
  have hle : e.oparg + 2 ≤ (args.reverse ++ self :: init :: rest).length := by simp [hlen]
  have hle' : e.oparg + 2 ≤ args.length + (rest.length + 1 + 1) := by omega
  constructor
  · intro x rt h
    bc_simp [_CREATE_INIT_FRAME, ht, hd, hle, hle', h]
  · intro nf rt h
    bc_simp [_CREATE_INIT_FRAME, ht, hd, hle, hle', h, setReturnOffset, modifyFrame, enterFrame,
      decRecursionRemaining]

/-! ## Registry forms -/


def ReturnValueRules : Prop := ReturnValue ∧ ReturnValueGen
theorem returnValueRules_proven : ReturnValueRules := ⟨returnValue_proven, returnValueGen_proven⟩

def ForIterRules : Prop := ForIterExhausted ∧ ForIterNext ∧ ForIterRaises
theorem forIterRules_proven : ForIterRules :=
  ⟨forIterExhausted_proven, forIterNext_proven, forIterRaises_proven⟩

def CompareOpFull : Prop := CompareFused ∧ CompareOpRules
theorem compareOpFull_proven : CompareOpFull := ⟨compareFused_proven, compareOpRules_proven⟩

def PushExcInfoFull : Prop := ExcInfoNests ∧ PushExcInfoRules
theorem pushExcInfoFull_proven : PushExcInfoFull := ⟨excInfoNests_proven, pushExcInfoRules_proven⟩

def UnaryNotFull : Prop := UnaryNotRules ∧ NotRules
theorem unaryNotFull_proven : UnaryNotFull := ⟨unaryNotRules_proven, notRules_proven⟩

end PyLean.Bytecode
