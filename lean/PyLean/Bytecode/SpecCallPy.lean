import PyLean.Bytecode.SpecCallGeneric
import PyLean.Bytecode.Props

/-!
The specialized Python calls of `Python/bytecodes.c` against their generic forms:
`CALL_PY_GENERAL` (`:4498-4506`), `CALL_BOUND_METHOD_GENERAL` (`:4529-4539`),
`CALL_PY_EXACT_ARGS` (`:4659-4669`), `CALL_BOUND_METHOD_EXACT_ARGS` (`:4644-4657`),
`CALL_KW_PY` (`:5511-5519`), `CALL_KW_BOUND_METHOD` (`:5542-5551`) and `CALL_EX_PY`
(`:5763-5771`), with their uops.

The generic `CALL` (`CALL_KW`, `CALL_FUNCTION_EX`) builds the callee's frame with
`_PyEvalFramePushAndInit` and enters it with `DISPATCH_INLINED`, whose `start_frame` runs
`_Py_EnterRecursivePy` (`Python/ceval_macros.h`): with `py_recursion_remaining <= 0` it raises
`RecursionError` and the new frame is dropped (`exit_unwind`). A specialized form ends in
`_PUSH_FRAME` (`:4628-4642`), which decrements the counter and checks nothing, so it must carry
`_CHECK_RECURSION_REMAINING` (`:4611-4613`, `DEOPT_IF(py_recursion_remaining <= 1)`) to stay a
refinement of its generic form.

Each statement compares what the machine does after the instruction (`afterInstr`: carry on in a
state, return, raise, stop), for every stack of the instruction's shape (the compiler's stack-depth
invariant) whose callable is live, every object model and every runtime, given that the
instruction starts with `next_instr = this_instr + INSTRUCTION_SIZE` (what `beginInstr` sets up),
so that `_SAVE_RETURN_OFFSET` and `frame->return_offset = INSTRUCTION_SIZE` agree. The
`EXACT_ARGS` forms copy the arguments into the frame without `initialize_locals`; they refine
`CALL` only for the code `specialize_py_call` installs them for (`Python/specialize.c:1472-1481,
:1754-1792`: `function_kind == SIMPLE_FUNCTION`, no `*args`, `**kwargs` or keyword-only
parameters and `CO_OPTIMIZED`), which is the stated precondition `SimpleCode` on the function the
`func_version` guard lets through; a function's version is that of its code and is cleared when
`__code__`, `__defaults__` or `__kwdefaults__` change.
-/

namespace PyLean.Bytecode

open Uop

/-! ## The frame builder leaves the recursion counter alone -/

/-- An `RM` computation that, when it succeeds, leaves `py_recursion_remaining` as it was. -/
def KeepsRec {α : Type} (m : RM α) : Prop :=
  ∀ rt a rt', m rt = .ok a rt' → rt'.pyRecursionRemaining = rt.pyRecursionRemaining

theorem kr_pure {α : Type} (a : α) : KeepsRec (pure a : RM α) := by
  intro rt b rt' h
  simp only [pure, EStateM.pure, EStateM.Result.ok.injEq] at h
  rw [← h.2]

theorem kr_bind {α β : Type} {m : RM α} {f : α → RM β} (hm : KeepsRec m) (hf : ∀ a, KeepsRec (f a)) :
    KeepsRec (m >>= f) := by
  intro rt b rt' h
  simp only [bind, EStateM.bind] at h
  split at h
  · rename_i a rt1 h1
    exact (hf a rt1 b rt' h).trans (hm rt a rt1 h1)
  · cases h

theorem kr_never {α : Type} {m : RM α} (h : ∀ rt a rt', m rt ≠ .ok a rt') : KeepsRec m :=
  fun rt a rt' h' => absurd h' (h rt a rt')

theorem kr_throw {α : Type} (x : Err) : KeepsRec (throw x : RM α) :=
  kr_never fun rt a rt' => by simp [throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

theorem kr_ite {α : Type} {c : Prop} [Decidable c] {m1 m2 : RM α} (h1 : KeepsRec m1) (h2 : KeepsRec m2) :
    KeepsRec (if c then m1 else m2) := by
  split <;> assumption

theorem kr_getObj (a : Addr) : KeepsRec (getObj a) := by
  intro rt o rt' h
  simp only [getObj] at h
  split at h
  · cases h; rfl
  · cases h

theorem kr_alloc (o : Obj) : KeepsRec (alloc o) := by
  intro rt v rt' h
  simp only [alloc, EStateM.Result.ok.injEq] at h
  rw [← h.2]

theorem kr_setObj (a : Addr) (o : Obj) : KeepsRec (setObj a o) := by
  intro rt v rt' h
  simp only [setObj, EStateM.Result.ok.injEq] at h
  rw [← h.2]

theorem kr_freshVersion : KeepsRec freshVersion := by
  intro rt v rt' h
  simp only [freshVersion, EStateM.Result.ok.injEq] at h
  rw [← h.2]

theorem raiseVal_ne_ok {α : Type} (v : Val) (rt : Rt) (a : α) (rt' : Rt) : (raiseVal v : RM α) rt ≠ .ok a rt' := by
  simp only [raiseVal, bind, EStateM.bind]
  split <;> simp [throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

theorem typeError_ne_ok {α : Type} (msg : String) (rt : Rt) (a : α) (rt' : Rt) :
    (typeError msg : RM α) rt ≠ .ok a rt' := by
  simp only [typeError, raiseS, bind, EStateM.bind]
  split
  · exact raiseVal_ne_ok _ _ _ _
  · simp

theorem kr_typeError {α : Type} (msg : String) : KeepsRec (typeError msg : RM α) :=
  kr_never (typeError_ne_ok msg)

theorem kr_fault {α : Type} (msg : String) : KeepsRec (fault msg : RM α) := kr_throw _

theorem kr_getDict (v : Val) : KeepsRec (getDict v) := by
  cases v <;> simp only [getDict] <;> first
    | exact kr_fault _
    | exact kr_bind (kr_getObj _) fun o => by cases o <;> first | exact kr_pure _ | exact kr_fault _

theorem kr_putDict (v : Val) (d : DictObj) : KeepsRec (putDict v d) := by
  cases v <;> simp only [putDict] <;> first | exact kr_fault _ | exact kr_setObj _ _

theorem kr_getFunc (v : Val) : KeepsRec (getFunc v) := by
  cases v <;> simp only [getFunc] <;> first
    | exact kr_fault _
    | exact kr_bind (kr_getObj _) fun o => by cases o <;> first | exact kr_pure _ | exact kr_fault _

theorem kr_getCodeR (P : Program) (i : Nat) : KeepsRec (getCodeR P i) := by
  intro rt c rt' h
  simp only [getCodeR] at h
  split at h
  · cases h; rfl
  · cases h

theorem kr_tupleItems (v : Val) : KeepsRec (tupleItems v) := by
  cases v <;> simp only [tupleItems] <;> first
    | exact kr_pure _
    | exact kr_fault _
    | exact kr_bind (kr_getObj _) fun o => by cases o <;> first | exact kr_pure _ | exact kr_fault _

theorem kr_mkDict : KeepsRec mkDict := kr_bind kr_freshVersion fun _ => kr_alloc _

theorem kr_mkTuple (items : List Val) : KeepsRec (mkTuple items) := kr_alloc _

theorem kr_dictFind_go (name : String) (d : DictObj) (h : Int) :
    ∀ n i, KeepsRec (dictFind.go (strKeyEq name) d h n i) := by
  intro n
  induction n with
  | zero => intro i; exact kr_pure _
  | succ n ih =>
    intro i
    simp only [dictFind.go]
    split
    · exact kr_pure _
    · apply kr_ite
      · exact kr_bind (by simp only [strKeyEq]; exact kr_pure _) fun b => by
          split
          · exact kr_pure _
          · exact ih _
      · exact ih _

theorem kr_dictFind (name : String) (d : DictObj) (h : Int) : KeepsRec (dictFind (strKeyEq name) d h) :=
  kr_dictFind_go name d h _ _

theorem kr_dictInsertAt (dv : Val) (d : DictObj) (idx : Option Nat) (h : Int) (k v : Val) :
    KeepsRec (dictInsertAt dv d idx h k v) := by
  unfold dictInsertAt
  split
  · exact kr_putDict _ _
  · exact kr_bind kr_freshVersion fun _ => kr_putDict _ _

theorem kr_dictSetStr (dv : Val) (name : String) (v : Val) : KeepsRec (dictSetStr dv name v) := by
  unfold dictSetStr
  exact kr_bind (kr_getDict _) fun d => kr_bind (kr_dictFind _ _ _) fun _ => kr_dictInsertAt _ _ _ _ _ _

theorem kr_dictGetStr (dv : Val) (name : String) : KeepsRec (dictGetStr dv name) := by
  unfold dictGetStr
  exact kr_bind (kr_getDict _) fun d => kr_bind (kr_dictFind _ _ _) fun o => by
    split <;> exact kr_pure _

theorem kr_bindKeywords (co : Code) (func : FuncObj) (kwdict : Val) :
    ∀ (kws : List (String × Val)) (fast : Array Val), KeepsRec (bindKeywords co func kwdict kws fast) := by
  intro kws
  induction kws with
  | nil => intro fast; exact kr_pure _
  | cons kv rest ih =>
    intro fast
    obtain ⟨k, v⟩ := kv
    simp only [bindKeywords]
    split
    · apply kr_ite
      · exact kr_bind (kr_typeError _) fun _ => ih _
      · exact ih _
    · apply kr_ite
      · exact kr_bind (kr_typeError _) fun _ => kr_bind (kr_dictSetStr _ _ _) fun _ => ih _
      · exact kr_bind (kr_dictSetStr _ _ _) fun _ => ih _

theorem kr_forIn {β σ : Type} (l : List β) (f : β → σ → RM (ForInStep σ)) (hf : ∀ x b, KeepsRec (f x b)) :
    ∀ init, KeepsRec (forIn l init f) := by
  induction l with
  | nil => intro init; simp only [List.forIn_nil]; exact kr_pure _
  | cons x xs ih =>
    intro init
    simp only [List.forIn_cons]
    exact kr_bind (hf x init) fun r => by
      split
      · exact kr_pure _
      · exact ih _

theorem kr_posonly (co : Code) (kwnames : List String) (q : String) :
    KeepsRec (posonlyPassedAsKeyword co kwnames q) := by
  unfold posonlyPassedAsKeyword
  dsimp only
  exact kr_ite (kr_typeError _) (kr_pure _)

theorem kr_tooManyPositional {α : Type} (co : Code) (gvn : Nat) (defaults : Val) (fast : Array Val) (q : String) :
    KeepsRec (tooManyPositional (α := α) co gvn defaults fast q) := by
  unfold tooManyPositional
  exact kr_bind (kr_tupleItems _) fun _ => by dsimp only; split <;> exact kr_typeError _

theorem kr_missingArguments {α : Type} (co : Code) (d : Option Nat) (fast : Array Val) (q : String) :
    KeepsRec (missingArguments (α := α) co d fast q) := by
  unfold missingArguments formatMissing
  dsimp only
  split <;> exact kr_typeError _

/-- Walk a monadic body made of the primitives above, matching only up to reducible unfolding. -/
syntax "kr_auto" : tactic
macro_rules
  | `(tactic| kr_auto) => `(tactic| repeat (first
      | with_reducible exact kr_pure _
      | with_reducible exact kr_typeError _
      | with_reducible exact kr_fault _
      | with_reducible exact kr_mkDict
      | with_reducible exact kr_mkTuple _
      | with_reducible exact kr_tupleItems _
      | with_reducible exact kr_dictGetStr _ _
      | with_reducible exact kr_posonly _ _ _
      | with_reducible exact kr_bindKeywords _ _ _ _ _
      | with_reducible exact kr_tooManyPositional _ _ _ _ _
      | with_reducible exact kr_missingArguments _ _ _ _
      | with_reducible refine kr_bind ?_ (fun _ => ?_)
      | with_reducible refine kr_forIn _ _ (fun _ _ => ?_) _
      | with_reducible refine kr_ite ?_ ?_
      | split))

set_option maxHeartbeats 2000000 in
theorem kr_initializeLocals (co : Code) (func : FuncObj) (fast0 : Array Val) (args : List Val)
    (kwargs : List (String × Val)) : KeepsRec (initializeLocals co func fast0 args kwargs) := by
  unfold initializeLocals
  dsimp only
  kr_auto

theorem kr_framePushAndInit (P : Program) (funcv locals : Val) (args : List Val) (kw : List String) :
    KeepsRec (framePushAndInit P funcv locals args kw) := by
  unfold framePushAndInit
  exact kr_bind (kr_getFunc _) fun func => kr_bind (kr_getCodeR _ _) fun co => by
    dsimp only
    exact kr_bind (kr_initializeLocals _ _ _ _ _) fun _ => kr_pure _

/-- `pushInit` (`_PyEvalFramePushAndInit` from a call site) changes nothing but the runtime, and
leaves its recursion counter as it was. -/
theorem pushInit_ok (e : Env) (c : Val) (args : List Val) (kw : List String) (regs : Regs) (nf : Frame) (r : Regs)
    (h : pushInit e c args kw regs = .ok nf r) :
    r = { regs with rt := r.rt } ∧ r.rt.pyRecursionRemaining = regs.rt.pyRecursionRemaining := by
  simp only [pushInit, bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift] at h
  split at h
  · rename_i func r1 h1
    split at h1
    · rename_i func' rt1 hg
      cases h1
      split at h
      · rename_i co r2 h2
        split at h2
        · rename_i co' rt2 hc
          cases h2
          split at h
          · rename_i nf' rt3 hf
            cases h
            refine ⟨rfl, ?_⟩
            exact ((kr_framePushAndInit _ _ _ _ _ _ _ _ hf).trans (kr_getCodeR _ _ _ _ _ hc)).trans
              (kr_getFunc _ _ _ _ hg)
          · cases h
        · cases h2
      · cases h
    · cases h1
  · cases h

/-! ## Entering the callee: `_PUSH_FRAME` and `DISPATCH_INLINED` -/

theorem wd_deopt {m g : M Unit} {s s' : St} (h : m s = .error .deopt s') : withDeopt m g s = g s := by
  simp [withDeopt, h]

theorem wd_ok {m g : M Unit} {s s' : St} (h : m s = .ok () s') : withDeopt m g s = .ok () s' := by
  simp [withDeopt, h]

theorem wd_err {m g : M Unit} {s s' : St} {x : Err} (h : m s = .error x s') (hx : x ≠ .deopt) :
    withDeopt m g s = .error x s' := by
  simp only [withDeopt, h]
  split
  · rename_i heq; cases heq; exact absurd rfl hx
  · rfl

/-- The state both ways of entering a callee frame `nf` leave, from registers `r` with the
caller's operands gone (`rest`): the caller's frame saved with `return_offset =
INSTRUCTION_SIZE` and its stack, `nf` current, the recursion counter decremented once, and
`next_instr` at `nf`'s first instruction. -/
def enteredSt (e : Env) (nf : Frame) (r : Regs) (rest : List Val) : St :=
  { regs := { rt := { r.rt with pyRecursionRemaining := r.rt.pyRecursionRemaining - 1 }, frame := nf,
              prev := ({ r.frame with returnOffset := instrSize e.opcode, stack := rest } :: r.prev),
              next := nf.instrPtr },
    stack := nf.stack }

/-- `_SAVE_RETURN_OFFSET + _PUSH_FRAME` (`:6136-6140`, `:4628-4642`). -/
theorem pushFrame_entered (e : Env) (nf : Frame) (r : Regs) (rest : List Val)
    (hn : r.next = e.this + instrSize e.opcode) :
    (do BM.lift (_SAVE_RETURN_OFFSET e); _PUSH_FRAME nf : M Unit) ⟨r, rest⟩ = .ok () (enteredSt e nf r rest) := by
  simp [bind, EStateM.bind, BM.lift, _SAVE_RETURN_OFFSET, setReturnOffset, modifyFrame, getNext, hn,
    _PUSH_FRAME, enterFrame, loadIp, RM.lift, enteredSt, pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift]

/-- `frame->return_offset = INSTRUCTION_SIZE; DISPATCH_INLINED(new_frame)` with budget left: `start_frame`'s
`_Py_EnterRecursivePy` decrements the counter and passes. -/
theorem dispatch_entered (e : Env) (nf : Frame) (r : Regs) (rest : List Val)
    (h : 0 < r.rt.pyRecursionRemaining) :
    (dispatchInlined nf : M Unit) ⟨{ r with frame := { r.frame with returnOffset := instrSize e.opcode } }, rest⟩ =
      .error .dispatch (enteredSt e nf r rest) := by
  have h' : ¬ r.rt.pyRecursionRemaining ≤ 0 := by omega
  simp [dispatchInlined, enterFrame, startFrame, bind, EStateM.bind, BM.lift, RM.lift, tryExc, enterRecursivePy, h',
    getFrame, setNext, enteredSt, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw, pure,
    EStateM.pure, liftM, monadLift, MonadLift.monadLift]

/-! ## The guards -/

section
variable (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)

theorem fnVersion_pass (hlen : args.length = e.oparg) (a : Addr) (fo : FuncObj)
    (ho : regs.rt.heap[a]? = some (.func fo)) (hv : fo.version = cacheNat e 0) :
    _CHECK_FUNCTION_VERSION e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ := by
  simp only [_CHECK_FUNCTION_VERSION, funcVersionAt, guardTop, bind, EStateM.bind,
    callStack_peek regs (.ref a) self args rest e.oparg hlen]
  simp [BM.lift, RM.lift, isFunction, getFunc, getObj, ho, hv, deoptIf, bind, EStateM.bind, pure, EStateM.pure,
    liftM, monadLift, MonadLift.monadLift]

theorem fnVersion_fail (hlen : args.length = e.oparg) (hc : Live regs.rt c)
    (hb : ∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat e 0) :
    _CHECK_FUNCTION_VERSION e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
  simp only [_CHECK_FUNCTION_VERSION, funcVersionAt, guardTop, bind, EStateM.bind,
    callStack_peek regs c self args rest e.oparg hlen]
  cases c with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hc
    cases o with
    | func fo =>
      have hv := hb a fo rfl ho
      simp [BM.lift, RM.lift, isFunction, getFunc, getObj, ho, hv, deoptIf, bind, EStateM.bind, pure, EStateM.pure,
        liftM, monadLift, MonadLift.monadLift, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
    | _ =>
      simp [BM.lift, RM.lift, isFunction, getObj, ho, deoptIf, bind, EStateM.bind, pure, EStateM.pure,
        liftM, monadLift, MonadLift.monadLift, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  | _ =>
    simp [BM.lift, RM.lift, isFunction, deoptIf, bind, EStateM.bind, pure, EStateM.pure,
      liftM, monadLift, MonadLift.monadLift, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

end

theorem recRemaining_pass (s : St) (h : 1 < s.regs.rt.pyRecursionRemaining) :
    _CHECK_RECURSION_REMAINING s = .ok () s := by
  have h' : ¬ s.regs.rt.pyRecursionRemaining ≤ 1 := by omega
  simp [_CHECK_RECURSION_REMAINING, guardTop, peekN, BM.lift, RM.lift, getRecursionRemaining, deoptIf, h',
    bind, EStateM.bind, pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift]

theorem recRemaining_fail (s : St) (h : s.regs.rt.pyRecursionRemaining ≤ 1) :
    _CHECK_RECURSION_REMAINING s = .error .deopt s := by
  simp [_CHECK_RECURSION_REMAINING, guardTop, peekN, BM.lift, RM.lift, getRecursionRemaining, deoptIf, h,
    bind, EStateM.bind, pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift, throw, throwThe,
    MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]


/-- `afterInstr` treats an instruction that ended normally and one that ended in `DISPATCH_INLINED`
alike: the machine carries on in the state left. -/
theorem afterInstr_entered (P : Program) (s : St) :
    afterInstr P (.ok () s) = afterInstr P (.error .dispatch s) := rfl

theorem pyFrameGeneral_ok (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)
    (hlen : args.length = e.oparg) (nf : Frame) (r : Regs)
    (hp : pushInit e c (withSelf self args) [] regs = .ok nf r) :
    _PY_FRAME_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ = .ok nf ⟨r, rest⟩ := by
  simp [_PY_FRAME_GENERAL, bind, EStateM.bind, callStack_pop regs c self args rest e.oparg hlen, BM.lift, hp]

theorem pyFrameGeneral_err (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)
    (hlen : args.length = e.oparg) (x : Err) (r : Regs)
    (hp : pushInit e c (withSelf self args) [] regs = .error x r) :
    _PY_FRAME_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ = .error x ⟨r, rest⟩ := by
  simp [_PY_FRAME_GENERAL, bind, EStateM.bind, callStack_pop regs c self args rest e.oparg hlen, BM.lift, hp]

/-- `CALL_PY_GENERAL` (`:4498-4506`: `_CHECK_PEP_523 + _CHECK_FUNCTION_VERSION +
_CHECK_RECURSION_REMAINING + _PY_FRAME_GENERAL + _SAVE_RETURN_OFFSET + _PUSH_FRAME`) on
`(callable, self_or_null, args[oparg])` does what the generic `CALL` does, for every live callable,
every `self_or_null`, every runtime and every object model: when the callable is not a function, or
is one whose `func_version` is not the cached one (`:4485-4490`), or the recursion budget is down to
1 (`:4611-4613`), it exits to `CALL`; otherwise it builds the same frame with
`_PyEvalFramePushAndInit` (or fails the same way, operands consumed) and enters it in the state
`CALL`'s `DISPATCH_INLINED` reaches. Not hypotheses on the function: any code, defaults or
keyword-only parameters, since both paths run `initialize_locals`. A form that skipped the version
guard, the recursion check, `self`, or the return offset would differ in one of the cases. -/
def CallPyGeneralRefines : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → regs.next = e.this + instrSize e.opcode →
  afterInstr e.P (execOp e .CALL_PY_GENERAL ⟨regs, args.reverse ++ self :: c :: rest⟩) =
    afterInstr e.P (execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩)

theorem callPyGeneralRefines_proven : CallPyGeneralRefines := by
  intro e regs c self args rest hlen hc hn
  simp only [execOp]
  by_cases hf : ∃ a fo, c = .ref a ∧ regs.rt.heap[a]? = some (.func fo) ∧ fo.version = cacheNat e 0
  · obtain ⟨a, fo, rfl, ho, hv⟩ := hf
    have hgen := (callGenericRules_proven e regs (.ref a) self args rest hlen hc).2.1 a fo rfl ho
    simp only [execOp] at hgen
    by_cases hr : 1 < regs.rt.pyRecursionRemaining
    · have hrs := recRemaining_pass ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ hr
      cases hp : pushInit e (.ref a) (withSelf self args) [] regs with
      | ok nf r =>
        obtain ⟨hr1, hr2⟩ := pushInit_ok e _ _ _ regs nf r hp
        have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
        have hspec : CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
            .ok () (enteredSt e nf r rest) := by
          simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [fnVersion_pass e regs self args rest hlen a fo ho hv]
          simp only
          rw [hrs]
          simp only
          rw [pyFrameGeneral_ok e regs _ self args rest hlen nf r hp]
          simp only
          have := pushFrame_entered e nf r rest hnext
          simp only [bind, EStateM.bind] at this
          exact this
        rw [wd_ok hspec, hgen.1 nf r hp, dispatch_entered e nf r rest (by omega)]
        rfl
      | error x r =>
        have hspec : CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ = .error x ⟨r, rest⟩ := by
          simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [fnVersion_pass e regs self args rest hlen a fo ho hv]
          simp only
          rw [hrs]
          simp only
          rw [pyFrameGeneral_err e regs _ self args rest hlen x r hp]
        by_cases hx : x = .deopt
        · subst hx; rw [wd_deopt hspec]
        · rw [wd_err hspec hx, hgen.2 x r hp]
    · have hspec : CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
          .error .deopt ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ := by
        simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
        rw [fnVersion_pass e regs self args rest hlen a fo ho hv]
        simp only
        rw [recRemaining_fail _ (by simpa using hr)]
      rw [wd_deopt hspec]
  · have hb : ∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat e 0 :=
      fun a fo h1 h2 h3 => hf ⟨a, fo, h1, h2, h3⟩
    have hspec : CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
      simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [fnVersion_fail e regs c self args rest hlen hc hb]
    rw [wd_deopt hspec]


/-! ## `CALL_BOUND_METHOD_GENERAL` -/

/-- The well-formedness of a bound method object the call forms rely on: `PyMethod_New` refuses a
`NULL` `im_self` (`Objects/classobject.c`), and `im_func` is a live object it holds a reference to. -/
def MethodsWF (rt : Rt) (c : Val) : Prop :=
  ∀ a f s, c = .ref a → rt.heap[a]? = some (.method f s) → s ≠ .null ∧ Live rt f

/-- The bound-method guard passes: `c` is a method object whose `im_func` is a function with the
cached version, and `self_or_null` is `NULL`. -/
def MethodPass (e : Env) (rt : Rt) (c self : Val) (b : Addr) (f s : Val) (fo : FuncObj) : Prop :=
  ∃ a, c = .ref a ∧ rt.heap[a]? = some (.method f s) ∧ f = .ref b ∧ rt.heap[b]? = some (.func fo) ∧
    fo.version = cacheNat e 0 ∧ self = .null

section
variable (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)

theorem methodVersion_pass (hlen : args.length = e.oparg) (b : Addr) (f s : Val) (fo : FuncObj)
    (hp : MethodPass e regs.rt c self b f s fo) :
    _CHECK_METHOD_VERSION e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
  simp only [_CHECK_METHOD_VERSION, guardTop, bind, EStateM.bind, callStack_peek regs c self args rest e.oparg hlen]
  obtain ⟨a, rfl, ho, rfl, hb, hv, rfl⟩ := hp
  simp [methodParts, isFunction, getFunc, getObj, ho, hb, hv, bind, EStateM.bind, RM.lift, BM.lift, pure,
    EStateM.pure, liftM, monadLift, MonadLift.monadLift, deoptIf]

theorem methodVersion_fail (hlen : args.length = e.oparg) (hc : Live regs.rt c) (hwf : MethodsWF regs.rt c)
    (hn : ∀ b f s fo, ¬ MethodPass e regs.rt c self b f s fo) :
    _CHECK_METHOD_VERSION e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
  simp only [_CHECK_METHOD_VERSION, guardTop, bind, EStateM.bind, callStack_peek regs c self args rest e.oparg hlen]
  cases c with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hc
    cases o with
    | method f s =>
      obtain ⟨_, hf⟩ := hwf a f s rfl ho
      cases f with
      | ref b =>
        obtain ⟨o2, ho2⟩ := live_obj hf
        cases o2 with
        | func fo =>
          have hx : ¬ (fo.version = cacheNat e 0 ∧ self = .null) := fun ⟨h1, h2⟩ =>
            hn b (.ref b) s fo ⟨a, rfl, ho, rfl, ho2, h1, h2⟩
          by_cases h1 : fo.version = cacheNat e 0
          · have h2 : self ≠ .null := fun h2 => hx ⟨h1, h2⟩
            simp [methodParts, isFunction, getFunc, getObj, ho, ho2, h1, h2, bind, EStateM.bind, RM.lift, BM.lift,
              pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift, deoptIf, throw, throwThe,
              MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
          · simp [methodParts, isFunction, getFunc, getObj, ho, ho2, h1, bind, EStateM.bind, RM.lift, BM.lift,
              pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift, deoptIf, throw, throwThe,
              MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
        | _ =>
          simp [methodParts, isFunction, getObj, ho, ho2, bind, EStateM.bind, RM.lift, BM.lift, pure, EStateM.pure,
            liftM, monadLift, MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw,
            MonadExceptOf.throw]
      | _ =>
        simp [methodParts, isFunction, getObj, ho, bind, EStateM.bind, RM.lift, BM.lift, pure, EStateM.pure, liftM,
          monadLift, MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw,
          MonadExceptOf.throw]
    | _ =>
      simp [methodParts, getObj, ho, bind, EStateM.bind, RM.lift, BM.lift, pure, EStateM.pure, liftM, monadLift,
        MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  | _ =>
    simp [methodParts, bind, EStateM.bind, RM.lift, BM.lift, pure, EStateM.pure, liftM, monadLift,
      MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

theorem expandMethod_eq (hlen : args.length = e.oparg) (a : Addr) (f s : Val)
    (ho : regs.rt.heap[a]? = some (.method f s)) :
    _EXPAND_METHOD e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ s :: f :: rest⟩ := by
  have hrev : (args.reverse ++ [self, .ref a]).reverse = .ref a :: self :: args := by simp
  rw [callStack_split]
  refine (stk_split_ok (outs := f :: s :: args) (r := regs) (by simp [hlen]) ?_ (by simp [hlen])).trans
    (by simp)
  rw [hrev]
  bc_simp [methodParts, getObj, ho]

end

/-- `CALL_BOUND_METHOD_GENERAL` (`:4529-4539`: `_CHECK_PEP_523 + _CHECK_METHOD_VERSION + _EXPAND_METHOD +
flush + _CHECK_RECURSION_REMAINING + _PY_FRAME_GENERAL + _SAVE_RETURN_OFFSET + _PUSH_FRAME`) does what
`CALL` does, for every live callable with well-formed method objects, every runtime and object model:
unless the callable is a method object whose `im_func` is a function with the cached version and
`self_or_null` is `NULL` (`:4508-4516`), it exits to `CALL`; it exits too with the recursion budget
down to 1; otherwise it splits the method into `im_func` and `im_self` (`:4518-4527`, what `CALL`'s
`_MAYBE_EXPAND_METHOD` does) and builds and enters the same frame as `CALL`, or fails as it does. -/
def CallBoundMethodGeneralRefines : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → MethodsWF regs.rt c → regs.next = e.this + instrSize e.opcode →
  afterInstr e.P (execOp e .CALL_BOUND_METHOD_GENERAL ⟨regs, args.reverse ++ self :: c :: rest⟩) =
    afterInstr e.P (execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩)

theorem callBoundMethodGeneralRefines_proven : CallBoundMethodGeneralRefines := by
  intro e regs c self args rest hlen hc hwf hn
  simp only [execOp]
  by_cases hp : ∃ b f s fo, MethodPass e regs.rt c self b f s fo
  · obtain ⟨b, f, s, fo, hp⟩ := hp
    have hp' := hp
    obtain ⟨a, rfl, ho, rfl, hb, hv, rfl⟩ := hp'
    obtain ⟨hs, hfl⟩ := hwf a (.ref b) s rfl ho
    -- the generic side: expansion, then the inlined call of `im_func`
    have hexp := (callGenericRules_proven e regs (.ref a) .null args rest hlen hc).1 a (.ref b) s rfl ho hs rfl hfl
    have hgen := (callGenericRules_proven e regs (.ref b) s args rest hlen hfl).2.1 b fo rfl hb
    simp only [execOp] at hexp hgen
    rw [hexp]
    have hlen' := hlen
    by_cases hr : 1 < regs.rt.pyRecursionRemaining
    · have hrs := recRemaining_pass ⟨regs, args.reverse ++ s :: .ref b :: rest⟩ hr
      cases hpi : pushInit e (.ref b) (withSelf s args) [] regs with
      | ok nf r =>
        obtain ⟨hr1, hr2⟩ := pushInit_ok e _ _ _ regs nf r hpi
        have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
        have hspec : CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ =
            .ok () (enteredSt e nf r rest) := by
          simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [methodVersion_pass e regs (.ref a) .null args rest hlen b (.ref b) s fo hp]
          simp only
          rw [expandMethod_eq e regs .null args rest hlen a (.ref b) s ho]
          simp only
          rw [hrs]
          simp only
          rw [pyFrameGeneral_ok e regs _ s args rest hlen nf r hpi]
          simp only
          have := pushFrame_entered e nf r rest hnext
          simp only [bind, EStateM.bind] at this
          exact this
        rw [wd_ok hspec, hgen.1 nf r hpi, dispatch_entered e nf r rest (by omega)]
        rfl
      | error x r =>
        have hspec : CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ =
            .error x ⟨r, rest⟩ := by
          simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [methodVersion_pass e regs (.ref a) .null args rest hlen b (.ref b) s fo hp]
          simp only
          rw [expandMethod_eq e regs .null args rest hlen a (.ref b) s ho]
          simp only
          rw [hrs]
          simp only
          rw [pyFrameGeneral_err e regs _ s args rest hlen x r hpi]
        by_cases hx : x = .deopt
        · subst hx; rw [wd_deopt hspec, hexp]
        · rw [wd_err hspec hx, hgen.2 x r hpi]
    · have hspec : CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ =
          .error .deopt ⟨regs, args.reverse ++ s :: .ref b :: rest⟩ := by
        simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
        rw [methodVersion_pass e regs (.ref a) .null args rest hlen b (.ref b) s fo hp]
        simp only
        rw [expandMethod_eq e regs .null args rest hlen a (.ref b) s ho]
        simp only
        rw [recRemaining_fail _ (by simpa using hr)]
      rw [wd_deopt hspec, hexp]
  · have hn' : ∀ b f s fo, ¬ MethodPass e regs.rt c self b f s fo := fun b f s fo h => hp ⟨b, f, s, fo, h⟩
    have hspec : CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
      simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [methodVersion_fail e regs c self args rest hlen hc hwf hn']
    rw [wd_deopt hspec]


end PyLean.Bytecode
