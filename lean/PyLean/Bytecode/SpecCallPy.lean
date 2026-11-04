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

end PyLean.Bytecode
