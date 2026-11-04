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

theorem kr_tooManyPositional {α : Type} (co : Code) (gvn : Nat) (defaults : Val) (fast : Array Val) (q : String) :
    KeepsRec (tooManyPositional (α := α) co gvn defaults fast q) := by
  unfold tooManyPositional
  exact kr_bind (kr_tupleItems _) fun _ => by dsimp only; split <;> exact kr_typeError _

theorem kr_missingArguments {α : Type} (co : Code) (d : Option Nat) (fast : Array Val) (q : String) :
    KeepsRec (missingArguments (α := α) co d fast q) := by
  unfold missingArguments formatMissing
  dsimp only
  split <;> exact kr_typeError _

theorem kr_keepRecursion {α : Type} (m : RM α) : KeepsRec (keepRecursion m) := by
  intro rt a rt' h
  simp only [keepRecursion] at h
  split at h
  · cases h; rfl
  · cases h

/-- The keyword hooks give the recursion counter back, as every call into Python code does. -/
def HooksKeepRec (hk : KwHooks) : Prop :=
  (∀ a b, KeepsRec (hk.eq a b)) ∧ (∀ o, KeepsRec (hk.str o)) ∧ (∀ d k v, KeepsRec (hk.setItem d k v))

theorem kwHooksOf_keepRec (om : ObjModel) (ctx : Ctx) : HooksKeepRec (kwHooksOf om ctx) :=
  ⟨fun _ _ => kr_keepRecursion _, fun _ => kr_keepRecursion _, fun _ _ _ => kr_keepRecursion _⟩

theorem kr_get : KeepsRec (get : RM Rt) := by
  intro rt a rt' h
  simp only [get, getThe, MonadStateOf.get, EStateM.get, EStateM.Result.ok.injEq] at h
  rw [← h.2]

section
variable {hk : KwHooks} (hh : HooksKeepRec hk)
include hh

theorem kr_posonlyHits (n : String) : ∀ l : List Val, KeepsRec (posonlyHits hk n l) := by
  intro l
  induction l with
  | nil => exact kr_pure _
  | cons kw rest ih =>
    simp only [posonlyHits]
    split
    · exact kr_bind (kr_pure _) fun _ => kr_bind ih fun _ => kr_pure _
    · exact kr_bind (hh.1 _ _) fun _ => kr_bind ih fun _ => kr_pure _

theorem kr_posonlyConflicts (kwnames : List Val) :
    ∀ names : List String, KeepsRec (posonlyConflicts hk kwnames names) := by
  intro names
  induction names with
  | nil => exact kr_pure _
  | cons n ns ih =>
    simp only [posonlyConflicts]
    exact kr_bind (kr_posonlyHits hh _ _) fun _ => kr_bind ih fun _ => kr_pure _

theorem kr_posonly (co : Code) (kwnames : List Val) (q : String) :
    KeepsRec (posonlyPassedAsKeyword hk co kwnames q) := by
  unfold posonlyPassedAsKeyword
  exact kr_bind (kr_posonlyConflicts hh _ _) fun _ =>
    kr_ite (kr_bind kr_get fun _ => kr_typeError _) (kr_pure _)

theorem kr_kwSlotSlow (co : Code) (k : Val) : ∀ l : List Nat, KeepsRec (kwSlotSlow hk co k l) := by
  intro l
  induction l with
  | nil => exact kr_pure _
  | cons j js ih =>
    simp only [kwSlotSlow]
    exact kr_bind (hh.1 _ _) fun _ => kr_ite (kr_pure _) ih

theorem kr_findKwSlot (co : Code) (k : Val) : KeepsRec (findKwSlot hk co k) := by
  unfold findKwSlot
  split
  · exact kr_pure _
  · exact kr_kwSlotSlow hh _ _ _

theorem kr_fmtKw (k : Val) : KeepsRec (fmtKw hk k) := by
  unfold fmtKw
  split
  · exact kr_pure _
  · exact hh.2.1 _

theorem kr_unexpectedKeyword {α : Type} (co : Code) (q : String) (k : Val) :
    KeepsRec (unexpectedKeyword (α := α) hk co q k) := by
  unfold unexpectedKeyword
  exact kr_bind kr_get fun _ => kr_bind (kr_fmtKw hh _) fun _ => by
    split <;> exact kr_typeError _

theorem kr_bindKeywords (co : Code) (funcv : Val) (kwdict : Val) (kwnames : List Val) :
    ∀ (kws : List (Val × Val)) (fast : Array Val),
      KeepsRec (bindKeywords hk co funcv kwdict kwnames kws fast) := by
  intro kws
  induction kws with
  | nil => intro fast; exact kr_pure _
  | cons kv rest ih =>
    intro fast
    obtain ⟨k, v⟩ := kv
    simp only [bindKeywords]
    refine kr_bind kr_get fun _ => ?_
    repeat (first
      | exact kr_pure _
      | exact kr_typeError _
      | exact ih _
      | exact kr_findKwSlot hh _ _
      | exact kr_getFunc _
      | exact kr_fmtKw hh _
      | exact kr_posonly hh _ _ _
      | exact kr_unexpectedKeyword hh _ _ _
      | exact kr_dictSetStr _ _ _
      | exact hh.2.2 _ _ _
      | refine kr_bind ?_ (fun _ => ?_)
      | refine kr_ite ?_ ?_
      | split)

end

/-- Walk a monadic body made of the primitives above, matching only up to reducible unfolding. -/
syntax "kr_auto" term : tactic
macro_rules
  | `(tactic| kr_auto $hh) => `(tactic| repeat (first
      | with_reducible exact kr_pure _
      | with_reducible exact kr_typeError _
      | with_reducible exact kr_fault _
      | with_reducible exact kr_mkDict
      | with_reducible exact kr_mkTuple _
      | with_reducible exact kr_tupleItems _
      | with_reducible exact kr_dictGetStr _ _
      | with_reducible exact kr_bindKeywords $hh _ _ _ _ _ _
      | with_reducible exact kr_getFunc _
      | with_reducible exact kr_tooManyPositional _ _ _ _ _
      | with_reducible exact kr_missingArguments _ _ _ _
      | with_reducible refine kr_bind ?_ (fun _ => ?_)
      | with_reducible refine kr_forIn _ _ (fun _ _ => ?_) _
      | with_reducible refine kr_ite ?_ ?_
      | split))

set_option maxHeartbeats 2000000 in
theorem kr_initializeLocals {hk : KwHooks} (hh : HooksKeepRec hk) (co : Code) (funcv : Val)
    (fast0 : Array Val) (args : List Val) (kwargs : List (Val × Val)) :
    KeepsRec (initializeLocals hk co funcv fast0 args kwargs) := by
  unfold initializeLocals
  dsimp only
  kr_auto hh

theorem kr_framePushAndInit {hk : KwHooks} (hh : HooksKeepRec hk) (P : Program) (funcv locals : Val)
    (args : List Val) (kw : List Val) : KeepsRec (framePushAndInit P hk funcv locals args kw) := by
  unfold framePushAndInit
  exact kr_bind (kr_getFunc _) fun func => kr_bind (kr_getCodeR _ _) fun co => by
    dsimp only
    exact kr_bind (kr_initializeLocals hh _ _ _ _ _) fun _ => kr_pure _

/-- `pushInitV` (`_PyEvalFramePushAndInit` from a call site) changes nothing but the runtime, and
leaves its recursion counter as it was. -/
theorem pushInitV_ok (e : Env) (c : Val) (args : List Val) (kw : List Val) (regs : Regs) (nf : Frame) (r : Regs)
    (h : pushInitV e c args kw regs = .ok nf r) :
    r = { regs with rt := r.rt } ∧ r.rt.pyRecursionRemaining = regs.rt.pyRecursionRemaining := by
  simp only [pushInitV, bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift] at h
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
            exact ((kr_framePushAndInit (kwHooksOf_keepRec _ _) _ _ _ _ _ _ _ _ hf).trans
              (kr_getCodeR _ _ _ _ _ hc)).trans (kr_getFunc _ _ _ _ hg)
          · cases h
        · cases h2
      · cases h
    · cases h1
  · cases h

/-- `pushInit` changes nothing but the runtime, and leaves its recursion counter as it was. -/
theorem pushInit_ok (e : Env) (c : Val) (args : List Val) (kw : List String) (regs : Regs) (nf : Frame) (r : Regs)
    (h : pushInit e c args kw regs = .ok nf r) :
    r = { regs with rt := r.rt } ∧ r.rt.pyRecursionRemaining = regs.rt.pyRecursionRemaining :=
  pushInitV_ok e c args _ regs nf r h

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


/-! ## `CALL_KW_PY`, `CALL_KW_BOUND_METHOD` -/

/-- The `_KW` guards are the plain ones one stack slot deeper (`kwnames` on top). -/
def kwEnv (e : Env) : Env := { e with oparg := e.oparg + 1 }

theorem fvKw_eq (e : Env) : _CHECK_FUNCTION_VERSION_KW e = _CHECK_FUNCTION_VERSION (kwEnv e) := rfl
theorem mvKw_eq (e : Env) : _CHECK_METHOD_VERSION_KW e = _CHECK_METHOD_VERSION (kwEnv e) := rfl
theorem expKw_eq (e : Env) : _EXPAND_METHOD_KW e = _EXPAND_METHOD (kwEnv e) := rfl
theorem cacheNat_kwEnv (e : Env) (i : Nat) : cacheNat (kwEnv e) i = cacheNat e i := rfl
theorem methodPass_kwEnv (e : Env) (rt : Rt) (c self : Val) (b : Addr) (f s : Val) (fo : FuncObj) :
    MethodPass (kwEnv e) rt c self b f s fo ↔ MethodPass e rt c self b f s fo := Iff.rfl

theorem kwStack_eq (kwv self c : Val) (args rest : List Val) :
    kwv :: (args.reverse ++ self :: c :: rest) = (args ++ [kwv]).reverse ++ self :: c :: rest := by simp

theorem pyFrameKw_ok (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val) (kw : List String)
    (hlen : args.length = e.oparg) (hkw : kwNames kwv regs.rt = .ok kw regs.rt) (nf : Frame) (r : Regs)
    (hp : pushInit e c (withSelf self args) kw regs = .ok nf r) :
    _PY_FRAME_KW e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .ok nf ⟨r, rest⟩ := by
  simp only [_PY_FRAME_KW, bind, EStateM.bind, kwStack_pop e regs c self kwv args rest hlen, dropLast_snoc,
    getLastD_snoc]
  simp [BM.lift, RM.lift, hkw, hp, bind, EStateM.bind, liftM, monadLift, MonadLift.monadLift]

theorem pyFrameKw_err (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val) (kw : List String)
    (hlen : args.length = e.oparg) (hkw : kwNames kwv regs.rt = .ok kw regs.rt) (x : Err) (r : Regs)
    (hp : pushInit e c (withSelf self args) kw regs = .error x r) :
    _PY_FRAME_KW e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .error x ⟨r, rest⟩ := by
  simp only [_PY_FRAME_KW, bind, EStateM.bind, kwStack_pop e regs c self kwv args rest hlen, dropLast_snoc,
    getLastD_snoc]
  simp [BM.lift, RM.lift, hkw, hp, bind, EStateM.bind, liftM, monadLift, MonadLift.monadLift]

/-- `CALL_KW_PY` (`:5511-5519`: `_CHECK_PEP_523 + _CHECK_FUNCTION_VERSION_KW +
_CHECK_RECURSION_REMAINING + _PY_FRAME_KW + _SAVE_RETURN_OFFSET + _PUSH_FRAME`) on
`(callable, self_or_null, args[oparg], kwnames)` does what the generic `CALL_KW` does, for every live
callable, every runtime and object model, `kwnames` being the compiler's tuple of names: it exits on
a non-function, a stale `func_version` (`:5504-5509`) or a spent recursion budget, and otherwise
builds the frame with `_PyEvalFramePushAndInit` and the keyword names (`:5474-5502`) and enters it as
`CALL_KW`'s `DISPATCH_INLINED` does, or fails as it does. The check was added by
python/cpython#137887. -/
def CallKwPyRefines : Prop := ∀ (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val) (kw : List String),
  args.length = e.oparg → Live regs.rt c → kwNames kwv regs.rt = .ok kw regs.rt →
  regs.next = e.this + instrSize e.opcode →
  afterInstr e.P (execOp e .CALL_KW_PY ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩) =
    afterInstr e.P (execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩)

theorem callKwPyRefines_proven : CallKwPyRefines := by
  intro e regs c self kwv args rest kw hlen hc hkw hn
  have hlen1 : (args ++ [kwv]).length = (kwEnv e).oparg := by simp [kwEnv, hlen]
  simp only [execOp]
  by_cases hf : ∃ a fo, c = .ref a ∧ regs.rt.heap[a]? = some (.func fo) ∧ fo.version = cacheNat e 0
  · obtain ⟨a, fo, rfl, ho, hv⟩ := hf
    have hgen := (callKwGenericRules_proven e regs (.ref a) self kwv args rest kw hlen hc hkw).2.1 a fo rfl ho
    simp only [execOp] at hgen
    have hfv : _CHECK_FUNCTION_VERSION_KW e ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ =
        .ok () ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ := by
      rw [fvKw_eq, kwStack_eq]
      exact fnVersion_pass (kwEnv e) regs self (args ++ [kwv]) rest hlen1 a fo ho hv
    by_cases hr : 1 < regs.rt.pyRecursionRemaining
    · have hrs := recRemaining_pass ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ hr
      cases hp : pushInit e (.ref a) (withSelf self args) kw regs with
      | ok nf r =>
        obtain ⟨hr1, hr2⟩ := pushInit_ok e _ _ _ regs nf r hp
        have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
        have hspec : CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ =
            .ok () (enteredSt e nf r rest) := by
          simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [hfv]; simp only; rw [hrs]; simp only
          rw [pyFrameKw_ok e regs _ self kwv args rest kw hlen hkw nf r hp]
          simp only
          have := pushFrame_entered e nf r rest hnext
          simp only [bind, EStateM.bind] at this
          exact this
        rw [wd_ok hspec, hgen.1 nf r hp, dispatch_entered e nf r rest (by omega)]
        rfl
      | error x r =>
        have hspec : CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ = .error x ⟨r, rest⟩ := by
          simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [hfv]; simp only; rw [hrs]; simp only
          rw [pyFrameKw_err e regs _ self kwv args rest kw hlen hkw x r hp]
        by_cases hx : x = .deopt
        · subst hx; rw [wd_deopt hspec]
        · rw [wd_err hspec hx, hgen.2 x r hp]
    · have hspec : CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ =
          .error .deopt ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ := by
        simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
        rw [hfv]; simp only
        rw [recRemaining_fail _ (by simpa using hr)]
      rw [wd_deopt hspec]
  · have hb : ∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat (kwEnv e) 0 :=
      fun a fo h1 h2 h3 => hf ⟨a, fo, h1, h2, h3⟩
    have hspec : CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
        .error .deopt ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ := by
      simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [fvKw_eq, kwStack_eq, fnVersion_fail (kwEnv e) regs c self (args ++ [kwv]) rest hlen1 hc hb]
    rw [wd_deopt hspec]

/-- `CALL_KW_BOUND_METHOD` (`:5542-5551`: `_CHECK_PEP_523 + _CHECK_METHOD_VERSION_KW + _EXPAND_METHOD_KW +
flush + _PY_FRAME_KW + _SAVE_RETURN_OFFSET + _PUSH_FRAME`) does what `CALL_KW` does, as
`CALL_BOUND_METHOD_GENERAL` does what `CALL` does. False: the macro has no
`_CHECK_RECURSION_REMAINING`, so with the budget spent it pushes the frame where `CALL_KW`'s
`start_frame` raises `RecursionError` (python/cpython#155151). -/
def CallKwBoundMethodRefines : Prop := ∀ (e : Env) (s : St),
  completed (execOp e .CALL_KW_BOUND_METHOD s) = completed (execOp e .CALL_KW s)

/-- `m(a=5)` with `m` bound to the function at 0 (version 9, `def f(self, a)`), `im_self` the int 1,
from code 3, with `py_recursion_remaining = 0`. -/
def kwBoundSt : St :=
  { regs := { rt := { heap := #[.func { code := 2, version := 9 }, .method (.ref 0) (.int 1), .tuple #[.str "a"]],
                      pyRecursionRemaining := 0 },
              frame := { code := 3 }, next := 4 },
    stack := [.ref 2, .int 5, .null, .ref 1] }

def kwBoundEnv : Env :=
  { P := #[{}, {}, { argcount := 2, nlocalsplus := 2, localsplusnames := #["self", "a"], flags := 1 }, {}],
    om := Proto.mkOM #[] 0, ctx := ⟨fun _ _ => throw .fuel⟩,
    opcode := .CALL_KW_BOUND_METHOD, oparg := 1, this := 0, cache := [.tagged 9] }

theorem callKwBoundMethodRefines_refuted : ¬CallKwBoundMethodRefines := by
  intro h
  exact absurd (h kwBoundEnv kwBoundSt) (by decide)


/-- With recursion budget left (`py_recursion_remaining > 0`, so that `CALL_KW`'s `start_frame`
passes), `CALL_KW_BOUND_METHOD` does what `CALL_KW` does, for every live callable with well-formed
method objects, every runtime and object model: unless the callable is a method object whose
`im_func` is a function with the cached version and `self_or_null` is `NULL` (`:5521-5529`) it exits;
otherwise it splits the method (`:5531-5540`) and builds and enters the frame `CALL_KW` builds, or
fails as it does. The narrowing of `CallKwBoundMethodRefines` to what is true. -/
def CallKwBoundMethodRefinesWithBudget : Prop := ∀ (e : Env) (regs : Regs) (c self kwv : Val)
    (args rest : List Val) (kw : List String),
  args.length = e.oparg → Live regs.rt c → MethodsWF regs.rt c → kwNames kwv regs.rt = .ok kw regs.rt →
  regs.next = e.this + instrSize e.opcode → 0 < regs.rt.pyRecursionRemaining →
  afterInstr e.P (execOp e .CALL_KW_BOUND_METHOD ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩) =
    afterInstr e.P (execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩)

theorem callKwBoundMethodRefinesWithBudget_proven : CallKwBoundMethodRefinesWithBudget := by
  intro e regs c self kwv args rest kw hlen hc hwf hkw hn hr
  have hlen1 : (args ++ [kwv]).length = (kwEnv e).oparg := by simp [kwEnv, hlen]
  simp only [execOp]
  by_cases hp : ∃ b f s fo, MethodPass e regs.rt c self b f s fo
  · obtain ⟨b, f, s, fo, hp⟩ := hp
    have hp' := hp
    obtain ⟨a, rfl, ho, rfl, hb, hv, rfl⟩ := hp'
    obtain ⟨hs, hfl⟩ := hwf a (.ref b) s rfl ho
    have hexp := (callKwGenericRules_proven e regs (.ref a) .null kwv args rest kw hlen hc hkw).1
      a (.ref b) s rfl ho hs rfl hfl
    have hgen := (callKwGenericRules_proven e regs (.ref b) s kwv args rest kw hlen hfl hkw).2.1 b fo rfl hb
    simp only [execOp] at hexp hgen
    rw [hexp]
    have hmv : _CHECK_METHOD_VERSION_KW e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
        .ok () ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ := by
      rw [mvKw_eq, kwStack_eq]
      exact methodVersion_pass (kwEnv e) regs (.ref a) .null (args ++ [kwv]) rest hlen1 b (.ref b) s fo hp
    have hex : _EXPAND_METHOD_KW e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
        .ok () ⟨regs, kwv :: (args.reverse ++ s :: .ref b :: rest)⟩ := by
      rw [expKw_eq, kwStack_eq, kwStack_eq]
      exact expandMethod_eq (kwEnv e) regs .null (args ++ [kwv]) rest hlen1 a (.ref b) s ho
    cases hpi : pushInit e (.ref b) (withSelf s args) kw regs with
    | ok nf r =>
      obtain ⟨hr1, hr2⟩ := pushInit_ok e _ _ _ regs nf r hpi
      have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
      have hspec : CALL_KW_BOUND_METHOD e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
          .ok () (enteredSt e nf r rest) := by
        simp only [CALL_KW_BOUND_METHOD, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
        rw [hmv]; simp only; rw [hex]; simp only
        rw [pyFrameKw_ok e regs _ s kwv args rest kw hlen hkw nf r hpi]
        simp only
        have := pushFrame_entered e nf r rest hnext
        simp only [bind, EStateM.bind] at this
        exact this
      rw [wd_ok hspec, hgen.1 nf r hpi, dispatch_entered e nf r rest (by omega)]
      rfl
    | error x r =>
      have hspec : CALL_KW_BOUND_METHOD e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
          .error x ⟨r, rest⟩ := by
        simp only [CALL_KW_BOUND_METHOD, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
        rw [hmv]; simp only; rw [hex]; simp only
        rw [pyFrameKw_err e regs _ s kwv args rest kw hlen hkw x r hpi]
      by_cases hx : x = .deopt
      · subst hx; rw [wd_deopt hspec, hexp]
      · rw [wd_err hspec hx, hgen.2 x r hpi]
  · have hn' : ∀ b f s fo, ¬ MethodPass (kwEnv e) regs.rt c self b f s fo := fun b f s fo h => hp ⟨b, f, s, fo, h⟩
    have hspec : CALL_KW_BOUND_METHOD e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
        .error .deopt ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ := by
      simp only [CALL_KW_BOUND_METHOD, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [mvKw_eq, kwStack_eq, methodVersion_fail (kwEnv e) regs c self (args ++ [kwv]) rest hlen1 hc hwf hn']
    rw [wd_deopt hspec]

/-! ## `CALL_EX_PY` -/

theorem getDict_rt (v : Val) (rt : Rt) (d : DictObj) (rt' : Rt) (h : getDict v rt = .ok d rt') : rt' = rt := by
  cases v with
  | ref a =>
    simp only [getDict, getObj, bind, EStateM.bind] at h
    cases ho : rt.heap[a]? with
    | none => simp [ho] at h
    | some o =>
      cases o <;> simp [ho, pure, EStateM.pure, fault, throw, throwThe, MonadExcept.throw, EStateM.throw,
        MonadExceptOf.throw] at h
      exact h.2.symm
  | _ => simp [getDict, fault, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw] at h

theorem unpackKwargs_rt (kw : Val) (rt : Rt) (p : List Val × List Val) (rt' : Rt)
    (h : unpackKwargs kw rt = .ok p rt') : rt' = rt := by
  cases kw with
  | null => simp [unpackKwargs, pure, EStateM.pure] at h; exact h.2.symm
  | _ =>
    simp only [unpackKwargs, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at h
    split at h
    · rename_i d rt1 hd
      have h2 := getDict_rt _ _ _ _ hd
      subst h2
      split at h
      · simp [pure, EStateM.pure] at h; exact h.2.symm
      · exact absurd h (typeError_ne_ok _ _ _ _)
    · cases h

theorem isPyCallableEx_pass (regs : Regs) (f n ca kw : Val) (rest : List Val) (a : Addr) (fo : FuncObj)
    (ho : regs.rt.heap[a]? = some (.func fo)) (hf : f = .ref a) :
    _CHECK_IS_PY_CALLABLE_EX ⟨regs, kw :: ca :: n :: f :: rest⟩ = .ok () ⟨regs, kw :: ca :: n :: f :: rest⟩ := by
  subst hf
  simp [_CHECK_IS_PY_CALLABLE_EX, guardTop, exStack_peek, bind, EStateM.bind, BM.lift, RM.lift, isFunction, getObj, ho,
    deoptIf, pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift]

theorem isPyCallableEx_fail (regs : Regs) (f n ca kw : Val) (rest : List Val) (hl : Live regs.rt f)
    (hnf : ¬ ∃ a fo, f = .ref a ∧ regs.rt.heap[a]? = some (.func fo)) :
    _CHECK_IS_PY_CALLABLE_EX ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error .deopt ⟨regs, kw :: ca :: n :: f :: rest⟩ := by
  have hff := isFunction_false regs f hl hnf
  simp [_CHECK_IS_PY_CALLABLE_EX, guardTop, exStack_peek, bind, EStateM.bind, BM.lift, RM.lift, hff,
    deoptIf, pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift, throw, throwThe, MonadExcept.throw,
    EStateM.throw, MonadExceptOf.throw]

/-- `CALL_EX_PY` (`:5763-5771`: `_CHECK_PEP_523 + _MAKE_CALLARGS_A_TUPLE + _CHECK_IS_PY_CALLABLE_EX +
_PY_FRAME_EX + _SAVE_RETURN_OFFSET + _PUSH_FRAME`, new in 3.15) does what `CALL_FUNCTION_EX` does.
False: there is no `_CHECK_RECURSION_REMAINING`, so with the budget spent it pushes the frame where
`CALL_FUNCTION_EX`'s `start_frame` raises `RecursionError` (python/cpython#155151). -/
def CallExPyRefines : Prop := ∀ (e : Env) (s : St),
  completed (execOp e .CALL_EX_PY s) = completed (execOp e .CALL_FUNCTION_EX s)

/-- `f(*())` with `f` the function at 0 (`def f()`), from code 3, with `py_recursion_remaining = 0`. -/
def exPySt : St :=
  { regs := { rt := { heap := #[.func { code := 2, version := 9 }, .tuple #[]], pyRecursionRemaining := 0 },
              frame := { code := 3 }, next := 2 },
    stack := [.null, .ref 1, .null, .ref 0] }

def exPyEnv : Env :=
  { P := #[{}, {}, { flags := 1 }, {}], om := Proto.mkOM #[] 0, ctx := ⟨fun _ _ => throw .fuel⟩,
    opcode := .CALL_EX_PY, oparg := 0, this := 0, cache := [] }

theorem callExPyRefines_refuted : ¬CallExPyRefines := by
  intro h
  exact absurd (h exPyEnv exPySt) (by decide)

theorem pyFrameEx_kwerr (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val) (x : Err) (rt : Rt)
    (hu : unpackKwargs kw regs.rt = .error x rt) :
    _PY_FRAME_EX e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩ := by
  simp [_PY_FRAME_EX, exStack_pop, bind, EStateM.bind, BM.lift, RM.lift, hu, liftM, monadLift, MonadLift.monadLift]

theorem pyFrameEx_ok (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val) (t : Addr) (items : Array Val)
    (hct : ca = .ref t) (ht : regs.rt.heap[t]? = some (.tuple items)) (names : List Val) (vals : List Val)
    (hu : unpackKwargs kw regs.rt = .ok (names, vals) regs.rt) (nf : Frame) (r : Regs)
    (hp : pushInitV e f (items.toList ++ vals) names regs = .ok nf r) :
    _PY_FRAME_EX e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .ok nf ⟨r, rest⟩ := by
  subst hct
  have hreg : ({ rt := regs.rt, frame := regs.frame, prev := regs.prev, next := regs.next } : Regs) = regs := rfl
  simp only [_PY_FRAME_EX, exStack_pop, bind, EStateM.bind, BM.lift, RM.lift, hu, liftM, monadLift,
    MonadLift.monadLift, tupleItems, getObj, ht, pure, EStateM.pure, hreg, hp]

theorem pyFrameEx_err (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val) (t : Addr) (items : Array Val)
    (hct : ca = .ref t) (ht : regs.rt.heap[t]? = some (.tuple items)) (names : List Val) (vals : List Val)
    (hu : unpackKwargs kw regs.rt = .ok (names, vals) regs.rt) (x : Err) (r : Regs)
    (hp : pushInitV e f (items.toList ++ vals) names regs = .error x r) :
    _PY_FRAME_EX e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error x ⟨r, rest⟩ := by
  subst hct
  have hreg : ({ rt := regs.rt, frame := regs.frame, prev := regs.prev, next := regs.next } : Regs) = regs := rfl
  simp only [_PY_FRAME_EX, exStack_pop, bind, EStateM.bind, BM.lift, RM.lift, hu, liftM, monadLift,
    MonadLift.monadLift, tupleItems, getObj, ht, pure, EStateM.pure, hreg, hp]

/-- With an exact tuple as `callargs` and recursion budget left (`py_recursion_remaining > 0`),
`CALL_EX_PY` does what `CALL_FUNCTION_EX` does, for every live function or other callable, every
`kwargs` (`NULL` or a dict), runtime and object model: on anything but a Python function it exits
(`:5734-5738`); on a function it unpacks the dict with `_PyStack_UnpackDict` (refusing non-str keys
as `CALL_FUNCTION_EX` does) and builds and enters the frame `CALL_FUNCTION_EX` builds
(`_PY_FRAME_EX`, `:5740-5761`, `_PyEvalFramePushAndInit_Ex`), or fails as it does. The narrowing of
`CallExPyRefines`. A non-tuple `callargs` is first made a tuple by `CALL_EX_PY`'s own
`_MAKE_CALLARGS_A_TUPLE`, after which dispatch is exactly itself on the tuple stack (`CallExPyFast`,
`SpecCallPyFast.lean`), as `CALL_FUNCTION_EX` is (`CallFunctionExRules`). -/
def CallExPyRefinesWithBudget : Prop := ∀ (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val)
    (t : Addr) (items : Array Val),
  ca = .ref t → regs.rt.heap[t]? = some (.tuple items) → Live regs.rt f →
  regs.next = e.this + instrSize e.opcode → 0 < regs.rt.pyRecursionRemaining →
  afterInstr e.P (execOp e .CALL_EX_PY ⟨regs, kw :: ca :: n :: f :: rest⟩) =
    afterInstr e.P (execOp e .CALL_FUNCTION_EX ⟨regs, kw :: ca :: n :: f :: rest⟩)

/-- With an exact tuple as `callargs`, `CALL_EX_PY`'s `_MAKE_CALLARGS_A_TUPLE` has nothing to do and
dispatch is the tail under `withDeopt`. -/
theorem execCallExPy_tuple (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val) (h : IsTuple regs.rt ca) :
    execCallExPy e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
      withDeopt (CALL_EX_PY_TAIL e) (CALL_FUNCTION_EX e) ⟨regs, kw :: ca :: n :: f :: rest⟩ := by
  have hmk := makeCallargs_keep e regs f n ca kw rest h
  simp only [execCallExPy, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
  rw [hmk]

theorem callExPyRefinesWithBudget_proven : CallExPyRefinesWithBudget := by
  intro e regs f n ca kw rest t items hct ht hfl hn hr
  have htup : IsTuple regs.rt ca := ⟨t, items, hct, ht⟩
  have hca : Live regs.rt ca := by
    intro a ha; rw [hct] at ha; cases ha
    exact (Array.getElem?_eq_some_iff.mp ht).1
  have hgen := (callFunctionExRules_proven e regs f n ca kw rest hca).2.2 t items hct ht
  simp only [execOp] at hgen ⊢
  rw [execCallExPy_tuple e regs f n ca kw rest htup]
  by_cases hf : ∃ a fo, f = .ref a ∧ regs.rt.heap[a]? = some (.func fo)
  · obtain ⟨a, fo, hfa, ho⟩ := hf
    have hg := hgen.1 a fo hfa ho
    have hpc := isPyCallableEx_pass regs f n ca kw rest a fo ho hfa
    cases hu : unpackKwargs kw regs.rt with
    | error x rt =>
      have hspec : CALL_EX_PY_TAIL e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩ := by
        simp only [CALL_EX_PY_TAIL, bind, EStateM.bind, pure, EStateM.pure]
        rw [hpc]; simp only
        rw [pyFrameEx_kwerr e regs f n ca kw rest x rt hu]
      by_cases hx : x = .deopt
      · subst hx; rw [wd_deopt hspec]
      · rw [wd_err hspec hx, hg.1 x rt hu]
    | ok p rt =>
      obtain ⟨names, vals⟩ := p
      have hrt := unpackKwargs_rt kw regs.rt _ rt hu
      subst hrt
      have hg2 := hg.2 names vals hu
      cases hpi : pushInitV e f (items.toList ++ vals) names regs with
      | ok nf r =>
        obtain ⟨hr1, hr2⟩ := pushInitV_ok e _ _ _ regs nf r hpi
        have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
        have hspec : CALL_EX_PY_TAIL e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .ok () (enteredSt e nf r rest) := by
          simp only [CALL_EX_PY_TAIL, bind, EStateM.bind, pure, EStateM.pure]
          rw [hpc]; simp only
          rw [pyFrameEx_ok e regs f n ca kw rest t items hct ht names vals hu nf r hpi]
          simp only
          have := pushFrame_entered e nf r rest hnext
          simp only [bind, EStateM.bind] at this
          exact this
        rw [wd_ok hspec, hg2.1 nf r hpi, dispatch_entered e nf r rest (by omega)]
        rfl
      | error x r =>
        have hspec : CALL_EX_PY_TAIL e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error x ⟨r, rest⟩ := by
          simp only [CALL_EX_PY_TAIL, bind, EStateM.bind, pure, EStateM.pure]
          rw [hpc]; simp only
          rw [pyFrameEx_err e regs f n ca kw rest t items hct ht names vals hu x r hpi]
        by_cases hx : x = .deopt
        · subst hx; rw [wd_deopt hspec]
        · rw [wd_err hspec hx, hg2.2 x r hpi]
  · have hspec : CALL_EX_PY_TAIL e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
        .error .deopt ⟨regs, kw :: ca :: n :: f :: rest⟩ := by
      simp only [CALL_EX_PY_TAIL, bind, EStateM.bind, pure, EStateM.pure]
      rw [isPyCallableEx_fail regs f n ca kw rest hfl hf]
    rw [wd_deopt hspec]


/-! ## `CALL_PY_EXACT_ARGS`, `CALL_BOUND_METHOD_EXACT_ARGS` -/

/-- `function_kind(code) == SIMPLE_FUNCTION` (`Python/specialize.c:1472-1481`): no `*args`, no
`**kwargs`, no keyword-only parameters, and `CO_OPTIMIZED`. -/
def SimpleCode (co : Code) : Prop :=
  co.kwonlyargcount = 0 ∧ flagSet co.flags coVarargs = false ∧ flagSet co.flags coVarkeywords = false ∧
    flagSet co.flags coOptimized = true

/-- The specializer's invariant for the `EXACT_ARGS` forms, on the function a call site holds: its
code object is in the program, and when its `func_version` is the one in the cache, that code is a
simple function (`specialize_py_call` installs `CALL_PY_EXACT_ARGS` or
`CALL_BOUND_METHOD_EXACT_ARGS` only for `SIMPLE_FUNCTION` code, `:1754-1792`, and a function's version
changes with its code). -/
def SimpleAtVersion (e : Env) (rt : Rt) (c : Val) : Prop :=
  ∀ a fo, c = .ref a → rt.heap[a]? = some (.func fo) →
    ∃ co, e.P[fo.code]? = some co ∧ (fo.version = cacheNat e 0 → SimpleCode co)

theorem foldl_congr_mem {α β : Type} (f g : β → α → β) :
    ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ acc, f acc x = g acc x) → l.foldl f b = l.foldl g b := by
  intro l
  induction l with
  | nil => intro b _; rfl
  | cons x xs ih =>
    intro b h
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih _ (fun y hy acc => h y (by simp [hy]) acc)

theorem zipIdx_fold (L : List Val) :
    ∀ (k : Nat) (a : Array Val), (L.zipIdx k).foldl (fun f p => f.setIfInBounds p.2 p.1) a =
      (List.range' k L.length).foldl (fun f j => f.setIfInBounds j (L.getD (j - k) .null)) a := by
  induction L with
  | nil => intro k a; rfl
  | cons x xs ih =>
    intro k a
    simp only [List.zipIdx_cons, List.foldl_cons, List.length_cons, List.range'_succ, Nat.sub_self,
      List.getD_cons_zero]
    rw [ih (k + 1)]
    apply foldl_congr_mem
    intro j hj acc
    have hk : k + 1 ≤ j := (List.mem_range'_1.mp hj).1
    have : j - k = (j - (k + 1)) + 1 := by omega
    rw [this, List.getD_cons_succ]

theorem initializeLocals_simple (hk : KwHooks) (co : Code) (funcv : Val) (func : FuncObj) (fast0 : Array Val)
    (L : List Val) (rt : Rt) (hg : getFunc funcv rt = .ok func rt)
    (hs : SimpleCode co) (hl : L.length = co.argcount) :
    initializeLocals hk co funcv fast0 L [] rt =
      .ok ((List.range L.length).foldl (fun f j => f.setIfInBounds j (L.getD j .null)) fast0) rt := by
  obtain ⟨hk, hva, hvk, _⟩ := hs
  simp [initializeLocals, hk, hva, hvk, hl, bindKeywords, pure, EStateM.pure, bind, EStateM.bind, hg]

/-- The frame `_INIT_CALL_PY_EXACT_ARGS` builds (`:4615-4626`): `_PyFrame_PushUnchecked` with `NULL`
locals and the arguments (`self` first when not `NULL`) copied into the first locals. -/
def exactFrame (co : Code) (fo : FuncObj) (c : Val) (L : List Val) : Frame :=
  let nf := frameInitialize co fo.code fo c .null
  { nf with fast := L.zipIdx.foldl (fun f p => f.setIfInBounds p.2 p.1) nf.fast }

theorem pushInit_simple (e : Env) (regs : Regs) (a : Addr) (fo : FuncObj) (co : Code) (L : List Val)
    (ho : regs.rt.heap[a]? = some (.func fo)) (hco : e.P[fo.code]? = some co) (hs : SimpleCode co)
    (hl : L.length = co.argcount) :
    pushInit e (.ref a) L [] regs = .ok (exactFrame co fo (.ref a) L) regs := by
  have hg : getFunc (.ref a) regs.rt = .ok fo regs.rt := by
    simp [getFunc, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
  have hli := initializeLocals_simple (kwHooksOf e.om e.ctx) co (.ref a) fo
    (frameInitialize co fo.code fo (.ref a) (localsFor co fo)).fast L regs.rt hg hs hl
  have hloc : localsFor co fo = .null := by simp [localsFor, hs.2.2.2]
  simp only [pushInit, pushInitV, List.map_nil, framePushAndInit, getFunc, getObj, ho, getCodeR, hco, bind, EStateM.bind, RM.lift, liftM,
    monadLift, MonadLift.monadLift, pure, EStateM.pure, List.length_nil, Nat.sub_zero, List.take_length,
    List.zip_nil_left]
  rw [hli]
  simp only [exactFrame, zipIdx_fold L 0, List.range_eq_range', Nat.sub_zero, hloc]

section
variable (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)

theorem exactArgs_pass (hlen : args.length = e.oparg) (a : Addr) (fo : FuncObj) (co : Code)
    (ho : regs.rt.heap[a]? = some (.func fo)) (hco : e.P[fo.code]? = some co)
    (hx : co.argcount = (withSelf self args).length) :
    _CHECK_FUNCTION_EXACT_ARGS e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ := by
  simp only [_CHECK_FUNCTION_EXACT_ARGS, guardTop, bind, EStateM.bind,
    callStack_peek regs (.ref a) self args rest e.oparg hlen]
  by_cases hs : self = .null
  · subst hs
    simp [withSelf] at hx
    simp [BM.lift, RM.lift, getFunc, getObj, ho, getCodeR, hco, bind, EStateM.bind, pure, EStateM.pure, liftM,
      monadLift, MonadLift.monadLift, hx, hlen, deoptIf]
  · simp [withSelf, hs] at hx
    simp [BM.lift, RM.lift, getFunc, getObj, ho, getCodeR, hco, bind, EStateM.bind, pure, EStateM.pure, liftM,
      monadLift, MonadLift.monadLift, hx, hlen, hs, deoptIf]

theorem exactArgs_fail (hlen : args.length = e.oparg) (a : Addr) (fo : FuncObj) (co : Code)
    (ho : regs.rt.heap[a]? = some (.func fo)) (hco : e.P[fo.code]? = some co)
    (hx : co.argcount ≠ (withSelf self args).length) :
    _CHECK_FUNCTION_EXACT_ARGS e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ := by
  simp only [_CHECK_FUNCTION_EXACT_ARGS, guardTop, bind, EStateM.bind,
    callStack_peek regs (.ref a) self args rest e.oparg hlen]
  by_cases hs : self = .null
  · subst hs
    simp [withSelf] at hx
    rw [hlen] at hx
    simp [BM.lift, RM.lift, getFunc, getObj, ho, getCodeR, hco, bind, EStateM.bind, pure, EStateM.pure, liftM,
      monadLift, MonadLift.monadLift, hx, hlen, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw]
  · simp [withSelf, hs] at hx
    rw [hlen] at hx
    simp [BM.lift, RM.lift, getFunc, getObj, ho, getCodeR, hco, bind, EStateM.bind, pure, EStateM.pure, liftM,
      monadLift, MonadLift.monadLift, hx, hlen, hs, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw]

theorem stackSpace_eval (s : St) :
    _CHECK_STACK_SPACE s = if s.regs.rt.stackSpace then .ok () s else .error .deopt s := by
  cases h : s.regs.rt.stackSpace <;>
    simp [_CHECK_STACK_SPACE, guardTop, peekN, BM.lift, hasStackSpace, h, deoptIf, bind, EStateM.bind, pure,
      EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

theorem initExact_eq (hlen : args.length = e.oparg) (a : Addr) (fo : FuncObj) (co : Code)
    (ho : regs.rt.heap[a]? = some (.func fo)) (hco : e.P[fo.code]? = some co) :
    _INIT_CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
      .ok (exactFrame co fo (.ref a) (withSelf self args)) ⟨regs, rest⟩ := by
  simp only [_INIT_CALL_PY_EXACT_ARGS, bind, EStateM.bind, callStack_pop regs (.ref a) self args rest e.oparg hlen]
  simp [BM.lift, RM.lift, getFunc, getObj, ho, getCodeR, hco, bind, EStateM.bind, pure, EStateM.pure, liftM,
    monadLift, MonadLift.monadLift, exactFrame]

end

theorem withSelf_length (self : Val) (args : List Val) :
    (withSelf self args).length = args.length + (if self != .null then 1 else 0) := by
  unfold withSelf; split <;> simp_all <;> omega

/-- `CALL_PY_EXACT_ARGS` (`:4659-4669`: `_CHECK_PEP_523 + _CHECK_FUNCTION_VERSION +
_CHECK_FUNCTION_EXACT_ARGS + _CHECK_STACK_SPACE + _CHECK_RECURSION_REMAINING + _INIT_CALL_PY_EXACT_ARGS
+ _SAVE_RETURN_OFFSET + _PUSH_FRAME`) does what `CALL` does, for every live callable, every runtime and
object model, under the specializer's invariant `SimpleAtVersion`: it exits on a non-function or a
stale version, when `co_argcount` is not the number of arguments with `self` (`:4596-4602`), when the
data stack has no room (`:4604-4609`) and when the recursion budget is down to 1; otherwise the frame
it fills by copying the arguments is the one `_PyEvalFramePushAndInit` builds, and it is entered as
`CALL` enters it. Without `SimpleAtVersion` it is false: for a function with `*args` or a keyword-only
parameter, the copy leaves those locals `NULL` where `initialize_locals` fills them. -/
def CallPyExactArgsRefines : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → SimpleAtVersion e regs.rt c →
  regs.next = e.this + instrSize e.opcode →
  afterInstr e.P (execOp e .CALL_PY_EXACT_ARGS ⟨regs, args.reverse ++ self :: c :: rest⟩) =
    afterInstr e.P (execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩)

theorem callPyExactArgsRefines_proven : CallPyExactArgsRefines := by
  intro e regs c self args rest hlen hc hsv hn
  simp only [execOp]
  by_cases hf : ∃ a fo, c = .ref a ∧ regs.rt.heap[a]? = some (.func fo) ∧ fo.version = cacheNat e 0
  · obtain ⟨a, fo, rfl, ho, hv⟩ := hf
    obtain ⟨co, hco, hsimp⟩ := hsv a fo rfl ho
    have hgen := (callGenericRules_proven e regs (.ref a) self args rest hlen hc).2.1 a fo rfl ho
    simp only [execOp] at hgen
    have hfv := fnVersion_pass e regs self args rest hlen a fo ho hv
    let S : St := ⟨regs, args.reverse ++ self :: .ref a :: rest⟩
    by_cases hx : co.argcount = (withSelf self args).length
    · have hea' : _CHECK_FUNCTION_EXACT_ARGS e S = .ok () S :=
        exactArgs_pass e regs self args rest hlen a fo co ho hco hx
      by_cases hsp : regs.rt.stackSpace = true
      · have hss : _CHECK_STACK_SPACE S = .ok () S := by rw [stackSpace_eval]; simp [S, hsp]
        by_cases hr : 1 < regs.rt.pyRecursionRemaining
        · have hrs := recRemaining_pass S hr
          have hl : (withSelf self args).length = co.argcount := hx.symm
          have hpi := pushInit_simple e regs a fo co (withSelf self args) ho hco (hsimp hv) hl
          have hspec : CALL_PY_EXACT_ARGS e S = .ok () (enteredSt e (exactFrame co fo (.ref a) (withSelf self args)) regs rest) := by
            simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
            rw [hfv]; simp only; rw [hea']; simp only; rw [hss]; simp only; rw [hrs]; simp only
            rw [initExact_eq e regs self args rest hlen a fo co ho hco]
            simp only
            have := pushFrame_entered e (exactFrame co fo (.ref a) (withSelf self args)) regs rest hn
            simp only [bind, EStateM.bind] at this
            exact this
          rw [wd_ok hspec, hgen.1 _ _ hpi, dispatch_entered e _ regs rest (by omega)]
          rfl
        · have hspec : CALL_PY_EXACT_ARGS e S = .error .deopt S := by
            simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
            rw [hfv]; simp only; rw [hea']; simp only; rw [hss]; simp only
            rw [recRemaining_fail _ (by simpa [S] using hr)]
          rw [wd_deopt hspec]
      · have hspec : CALL_PY_EXACT_ARGS e S = .error .deopt S := by
          simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
          rw [hfv]; simp only; rw [hea']; simp only
          rw [stackSpace_eval]; simp [S, hsp]
        rw [wd_deopt hspec]
    · have hspec : CALL_PY_EXACT_ARGS e S = .error .deopt S := by
        simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
        rw [hfv]; simp only
        rw [exactArgs_fail e regs self args rest hlen a fo co ho hco hx]
      rw [wd_deopt hspec]
  · have hb : ∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat e 0 :=
      fun a fo h1 h2 h3 => hf ⟨a, fo, h1, h2, h3⟩
    have hspec : CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
      simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [fnVersion_fail e regs c self args rest hlen hc hb]
    rw [wd_deopt hspec]


section
variable (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)

theorem boundExact_pass (hlen : args.length = e.oparg) (a : Addr) (f s : Val)
    (ho : regs.rt.heap[a]? = some (.method f s)) :
    _CHECK_CALL_BOUND_METHOD_EXACT_ARGS e ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ := by
  simp only [_CHECK_CALL_BOUND_METHOD_EXACT_ARGS, guardTop, bind, EStateM.bind,
    callStack_peek regs (.ref a) .null args rest e.oparg hlen]
  simp [BM.lift, RM.lift, methodParts, getObj, ho, bind, EStateM.bind, pure, EStateM.pure, liftM, monadLift,
    MonadLift.monadLift, deoptIf]

theorem boundExact_fail (hlen : args.length = e.oparg) (hc : Live regs.rt c)
    (hn : ¬ ∃ a f s, c = .ref a ∧ regs.rt.heap[a]? = some (.method f s) ∧ self = .null) :
    _CHECK_CALL_BOUND_METHOD_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
  simp only [_CHECK_CALL_BOUND_METHOD_EXACT_ARGS, guardTop, bind, EStateM.bind,
    callStack_peek regs c self args rest e.oparg hlen]
  by_cases hs : self = .null
  · subst hs
    cases c with
    | ref a =>
      obtain ⟨o, ho⟩ := live_obj hc
      cases o with
      | method f s => exact absurd ⟨a, f, s, rfl, ho, rfl⟩ hn
      | _ =>
        simp [BM.lift, RM.lift, methodParts, getObj, ho, bind, EStateM.bind, pure, EStateM.pure, liftM, monadLift,
          MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
    | _ =>
      simp [BM.lift, RM.lift, methodParts, bind, EStateM.bind, pure, EStateM.pure, liftM, monadLift,
        MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  · simp [BM.lift, RM.lift, hs, bind, EStateM.bind, pure, EStateM.pure, liftM, monadLift,
      MonadLift.monadLift, deoptIf, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

end

/-- Once its own guard has passed and the method is split, `CALL_BOUND_METHOD_EXACT_ARGS` is
`CALL_PY_EXACT_ARGS` on the split stack (`_CHECK_PEP_523` has nothing to do). -/
theorem boundExact_split (e : Env) (regs : Regs) (args rest : List Val) (hlen : args.length = e.oparg) (a : Addr)
    (f s : Val) (ho : regs.rt.heap[a]? = some (.method f s)) :
    CALL_BOUND_METHOD_EXACT_ARGS e ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ =
      CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ s :: f :: rest⟩ := by
  simp only [CALL_BOUND_METHOD_EXACT_ARGS, CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure,
    EStateM.pure]
  rw [boundExact_pass e regs args rest hlen a f s ho]
  simp only [_INIT_CALL_BOUND_METHOD_EXACT_ARGS]
  rw [expandMethod_eq e regs .null args rest hlen a f s ho]

/-- `CALL_BOUND_METHOD_EXACT_ARGS` (`:4644-4657`: `_CHECK_PEP_523 + _CHECK_CALL_BOUND_METHOD_EXACT_ARGS
+ _INIT_CALL_BOUND_METHOD_EXACT_ARGS + flush + _CHECK_FUNCTION_VERSION + _CHECK_FUNCTION_EXACT_ARGS +
_CHECK_STACK_SPACE + _CHECK_RECURSION_REMAINING + _INIT_CALL_PY_EXACT_ARGS + _SAVE_RETURN_OFFSET +
_PUSH_FRAME`) does what `CALL` does, for every live callable with well-formed method objects, every
runtime and object model, under the specializer's invariant on `im_func`: unless the callable is a
method object with `self_or_null` `NULL` (`:4577-4580`) it exits; otherwise it splits the method
(`:4582-4590`) and is then `CALL_PY_EXACT_ARGS` on `im_func` and `im_self`, whose guards' exits restart
`CALL` (after the `flush`, on the split stack, which `CALL` itself would have made). -/
def CallBoundMethodExactArgsRefines : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → MethodsWF regs.rt c →
  (∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → SimpleAtVersion e regs.rt f) →
  regs.next = e.this + instrSize e.opcode →
  afterInstr e.P (execOp e .CALL_BOUND_METHOD_EXACT_ARGS ⟨regs, args.reverse ++ self :: c :: rest⟩) =
    afterInstr e.P (execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩)

theorem callBoundMethodExactArgsRefines_proven : CallBoundMethodExactArgsRefines := by
  intro e regs c self args rest hlen hc hwf hsv hn
  by_cases hp : ∃ a f s, c = .ref a ∧ regs.rt.heap[a]? = some (.method f s) ∧ self = .null
  · obtain ⟨a, f, s, rfl, ho, rfl⟩ := hp
    obtain ⟨hs, hfl⟩ := hwf a f s rfl ho
    have hexp := (callGenericRules_proven e regs (.ref a) .null args rest hlen hc).1 a f s rfl ho hs rfl hfl
    have hpy := callPyExactArgsRefines_proven e regs f s args rest hlen hfl (hsv a f s rfl ho) hn
    rw [hexp, ← hpy]
    simp only [execOp]
    have hsplit := boundExact_split e regs args rest hlen a f s ho
    simp only [execOp] at hexp
    unfold withDeopt
    rw [hsplit]
    split
    · rw [hexp]
    · rfl
  · have hspec : CALL_BOUND_METHOD_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
      simp only [CALL_BOUND_METHOD_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [boundExact_fail e regs c self args rest hlen hc hp]
    simp only [execOp]
    rw [wd_deopt hspec]


end PyLean.Bytecode
