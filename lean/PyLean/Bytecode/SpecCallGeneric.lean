import PyLean.Bytecode.SpecCall

/-!
The generic calls of `Python/bytecodes.c`: `CALL` (`:4373-4457`), `CALL_KW` (`:5405-5569`) and
`CALL_FUNCTION_EX` (`:5620-5732`), for every object model.

`CALL` and `CALL_KW` take `(callable, self_or_null, args[oparg])` (and `kwnames` on top for
`CALL_KW`). Each is stated as three clauses that between them cover every stack whose callable is
live: a bound method with a `NULL` `self_or_null` is first split into `im_func` and `im_self`
(`_MAYBE_EXPAND_METHOD`), and the instruction is then exactly the instruction on the split stack;
a Python function is inlined (the operands popped, `_PyEvalFramePushAndInit` on `self` and the
arguments, `return_offset` set, `DISPATCH_INLINED`), its frame-building error raised with the
operands consumed; anything else is `PyObject_Vectorcall`, whose result replaces the operands and
is followed by `_CHECK_PERIODIC_AT_END` for `CALL` only, and whose error pops them. A body that
called with the wrong arguments, kept `self` out, inlined a non-function, skipped the expansion,
or kept operands on failure fails one clause.

`im_self` of a method object is never `NULL` (`PyMethod_New` refuses it), which is the hypothesis
`s ≠ .null` of the expansion clauses.
-/

namespace PyLean.Bytecode

open Uop

section
variable (e : Env) (regs : Regs) (c self : Val) (args rest : List Val)

/-- Stack layout of `(callable, self_or_null, args[n])` with `args` in call order. -/
theorem callStack_split : args.reverse ++ self :: c :: rest = (args.reverse ++ [self, c]) ++ rest := by simp

theorem callStack_take (n : Nat) (hlen : args.length = n) :
    (args.reverse ++ self :: c :: rest).take (n + 2) = args.reverse ++ [self, c] := by
  rw [callStack_split]; exact List.take_left' (by simp [hlen])

theorem callStack_drop (n : Nat) (hlen : args.length = n) :
    (args.reverse ++ self :: c :: rest).drop (n + 2) = rest := by
  rw [callStack_split]; exact List.drop_left' (by simp [hlen])

theorem callStack_len (n : Nat) (hlen : args.length = n) :
    n + 2 ≤ (args.reverse ++ self :: c :: rest).length := by simp [hlen]

theorem callStack_peek (n : Nat) (hlen : args.length = n) :
    peekN (n + 2) ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .ok (c :: self :: args) ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
  simp only [peekN, callStack_len c self args rest n hlen, ↓reduceIte, callStack_take c self args rest n hlen]
  simp

theorem callStack_pop (n : Nat) (hlen : args.length = n) :
    popN (n + 2) ⟨regs, args.reverse ++ self :: c :: rest⟩ = .ok (c :: self :: args) ⟨regs, rest⟩ := by
  simp only [popN, callStack_len c self args rest n hlen, ↓reduceIte, callStack_take c self args rest n hlen,
    callStack_drop c self args rest n hlen]
  simp

/-- A callable that is not a method object, or one with `self_or_null` already set, is left as it
is by `_MAYBE_EXPAND_METHOD` (`:4373-4383`). -/
theorem maybeExpand_keep (hlen : args.length = e.oparg) (hc : Live regs.rt c)
    (hk : ∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → self ≠ .null) :
    _MAYBE_EXPAND_METHOD e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ self :: c :: rest⟩ := by
  have hrev : (args.reverse ++ [self, c]).reverse = c :: self :: args := by simp
  rw [callStack_split]
  refine (stk_split_ok (outs := c :: self :: args) (r := regs) (by simp [hlen]) ?_ (by simp [hlen])).trans
    (by simp)
  rw [hrev]
  cases c with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hc
    cases o with
    | method f s =>
      have hs : (self == .null) = false := by simpa using hk a f s rfl ho
      bc_simp [methodParts, getObj, ho, hs]
    | _ => bc_simp [methodParts, getObj, ho]
  | _ => bc_simp [methodParts]

/-- A method object with a `NULL` `self_or_null` becomes `im_func` with `im_self` as `self`. -/
theorem maybeExpand_expand (hlen : args.length = e.oparg) (a : Addr) (f s : Val)
    (ho : regs.rt.heap[a]? = some (.method f s)) :
    _MAYBE_EXPAND_METHOD e ⟨regs, args.reverse ++ .null :: .ref a :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ s :: f :: rest⟩ := by
  have hrev : (args.reverse ++ [Val.null, .ref a]).reverse = .ref a :: .null :: args := by simp
  rw [callStack_split]
  refine (stk_split_ok (outs := f :: s :: args) (r := regs) (by simp [hlen]) ?_ (by simp [hlen])).trans
    (by simp)
  rw [hrev]
  bc_simp [methodParts, getObj, ho]

theorem isFunction_false (hc : Live regs.rt c) (hn : ¬ ∃ a fo, c = .ref a ∧ regs.rt.heap[a]? = some (.func fo)) :
    isFunction c regs.rt = .ok false regs.rt := by
  cases c with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hc
    cases o with
    | func fo => exact absurd ⟨a, fo, rfl, ho⟩ hn
    | _ => simp [isFunction, getObj, ho, bind, EStateM.bind, pure, EStateM.pure]
  | _ => simp [isFunction, pure, EStateM.pure]

/-- `DISPATCH_INLINED` never falls through to the rest of the macro. -/
theorem dispatchInlined_ne_ok (nf : Frame) (s : St) (a : Unit) (s' : St) :
    (dispatchInlined nf : M Unit) s ≠ .ok a s' := by
  intro h
  simp only [dispatchInlined, bind, EStateM.bind] at h
  split at h
  · split at h
    · simp [throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw] at h
    · cases h
  · cases h

end

/-- `CALL oparg` (`:4457`: `_SPECIALIZE_CALL + _MAYBE_EXPAND_METHOD + _DO_CALL +
_CHECK_PERIODIC_AT_END`) on `(callable, self_or_null, args)`, `args` in call order with
`len(args) = oparg`, for every object model. The expansion of a method object (`:4373-4383`); the
inlined call of a function object (`:4398-4419`: `Py_TYPE(callable) == &PyFunction_Type` with the
model's `vectorcall == _PyFunction_Vectorcall` and no PEP 523 hook, `_PyEvalFramePushAndInit` on
`self` (when not `NULL`) then the arguments, no keyword names, `frame->return_offset =
INSTRUCTION_SIZE`, `DISPATCH_INLINED`, and `ERROR_NO_POP` after `SYNC_SP` when the frame cannot be
built, so the operands are consumed either way); and `PyObject_Vectorcall` (`:4420-4433`) for every
other live callable, its result replacing the operands before `_CHECK_PERIODIC_AT_END`, its error
popping them (`ERROR_IF`). -/
def CallGenericRules : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c →
  (∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → s ≠ .null → self = .null → Live regs.rt f →
    execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      execOp e .CALL ⟨regs, args.reverse ++ s :: f :: rest⟩) ∧
  (∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) →
    (∀ nf r, pushInit e c (withSelf self args) [] regs = .ok nf r →
      execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        (dispatchInlined nf : M Unit) ⟨{ r with frame := { r.frame with returnOffset := instrSize e.opcode } }, rest⟩) ∧
    (∀ x r, pushInit e c (withSelf self args) [] regs = .error x r →
      execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩ = .error x ⟨r, rest⟩)) ∧
  ((¬ ∃ a fo, c = .ref a ∧ regs.rt.heap[a]? = some (.func fo)) →
    (∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → self ≠ .null) →
    (∀ v rt, e.om.call e.ctx c (withSelf self args) [] regs.rt = .ok v rt →
      execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, v :: rest⟩) ∧
    (∀ x rt, e.om.call e.ctx c (withSelf self args) [] regs.rt = .error x rt →
      execOp e .CALL ⟨regs, args.reverse ++ self :: c :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩))

theorem callGenericRules_proven : CallGenericRules := by
  intro e regs c self args rest hlen hc
  have hT := callStack_take c self args rest e.oparg hlen
  have hD := callStack_drop c self args rest e.oparg hlen
  have hN := callStack_len c self args rest e.oparg hlen
  refine ⟨fun a f s hca ho hs hself hf => ?_, fun a fo hca ho => ⟨fun nf r hp => ?_, fun x r hp => ?_⟩,
    fun hnf hk => ⟨fun v rt hv => ?_, fun x rt hx => ?_⟩⟩
  · subst hca hself
    have h1 := maybeExpand_expand e regs args rest hlen a f s ho
    have h2 := maybeExpand_keep e regs f s args rest hlen hf (fun _ _ _ _ _ => hs)
    simp only [execOp, CALL, _SPECIALIZE_CALL, bind, EStateM.bind, pure, EStateM.pure]
    rw [h1, h2]
  · subst hca
    have hk := maybeExpand_keep e regs (.ref a) self args rest hlen hc (by intro _ _ _ h; cases h; simp [ho])
    simp only [execOp, CALL, _SPECIALIZE_CALL, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk]
    simp only [_DO_CALL, bind, EStateM.bind, callStack_peek regs (.ref a) self args rest e.oparg hlen]
    simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, isFunction, getObj, ho,
      pure, EStateM.pure, callStack_pop regs (.ref a) self args rest e.oparg hlen, hp, setReturnOffset, modifyFrame]
    split
    · rename_i heq; exact absurd heq (dispatchInlined_ne_ok _ _ _ _)
    · rename_i heq; exact heq.symm
  · subst hca
    have hk := maybeExpand_keep e regs (.ref a) self args rest hlen hc (by intro _ _ _ h; cases h; simp [ho])
    simp only [execOp, CALL, _SPECIALIZE_CALL, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk]
    simp only [_DO_CALL, bind, EStateM.bind, callStack_peek regs (.ref a) self args rest e.oparg hlen]
    simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, isFunction, getObj, ho,
      pure, EStateM.pure, callStack_pop regs (.ref a) self args rest e.oparg hlen, hp]
  · have hk' := maybeExpand_keep e regs c self args rest hlen hc hk
    have hf := isFunction_false regs c hc hnf
    simp only [execOp, CALL, _SPECIALIZE_CALL, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk']
    simp only [_DO_CALL, bind, EStateM.bind, callStack_peek regs c self args rest e.oparg hlen]
    simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, hf,
      pure, EStateM.pure, stk, callStack_pop regs c self args rest e.oparg hlen, hv, pushAll]
  · have hk' := maybeExpand_keep e regs c self args rest hlen hc hk
    have hf := isFunction_false regs c hc hnf
    simp only [execOp, CALL, _SPECIALIZE_CALL, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk']
    simp only [_DO_CALL, bind, EStateM.bind, callStack_peek regs c self args rest e.oparg hlen]
    simp [bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, hf,
      pure, EStateM.pure, stk, callStack_pop regs c self args rest e.oparg hlen, hx]

/-! ## `CALL_KW` -/

section
variable (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val)

theorem kwStack (hlen : args.length = e.oparg) :
    kwv :: (args.reverse ++ self :: c :: rest) = (args ++ [kwv]).reverse ++ self :: c :: rest ∧
      (args ++ [kwv]).length = e.oparg + 1 := by
  simp [hlen]

theorem maybeExpandKw_keep (hlen : args.length = e.oparg) (hc : Live regs.rt c)
    (hk : ∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → self ≠ .null) :
    _MAYBE_EXPAND_METHOD_KW e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
      .ok () ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ := by
  obtain ⟨hs, hl⟩ := kwStack e c self kwv args rest hlen
  rw [hs, callStack_split]
  have hrev : ((args ++ [kwv]).reverse ++ [self, c]).reverse = c :: self :: (args ++ [kwv]) := by simp
  refine (stk_split_ok (outs := c :: self :: (args ++ [kwv])) (r := regs) (by simp [hlen]) ?_
    (by simp [hlen])).trans (by simp)
  rw [hrev]
  cases c with
  | ref a =>
    obtain ⟨o, ho⟩ := live_obj hc
    cases o with
    | method f s =>
      have hs : (self == .null) = false := by simpa using hk a f s rfl ho
      bc_simp [methodParts, getObj, ho, hs]
    | _ => bc_simp [methodParts, getObj, ho]
  | _ => bc_simp [methodParts]

theorem maybeExpandKw_expand (hlen : args.length = e.oparg) (a : Addr) (f s : Val)
    (ho : regs.rt.heap[a]? = some (.method f s)) :
    _MAYBE_EXPAND_METHOD_KW e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
      .ok () ⟨regs, kwv :: (args.reverse ++ s :: f :: rest)⟩ := by
  obtain ⟨hs, hl⟩ := kwStack e (.ref a) .null kwv args rest hlen
  obtain ⟨hs2, _⟩ := kwStack e f s kwv args rest hlen
  rw [hs, hs2, callStack_split]
  have hrev : ((args ++ [kwv]).reverse ++ [Val.null, .ref a]).reverse = .ref a :: .null :: (args ++ [kwv]) := by
    simp
  refine (stk_split_ok (outs := f :: s :: (args ++ [kwv])) (r := regs) (by simp [hlen]) ?_
    (by simp [hlen])).trans (by simp)
  rw [hrev]
  bc_simp [methodParts, getObj, ho]

theorem kwStack_peek (hlen : args.length = e.oparg) :
    peekN (e.oparg + 3) ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
      .ok (c :: self :: (args ++ [kwv])) ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ := by
  obtain ⟨hs, hl⟩ := kwStack e c self kwv args rest hlen
  rw [hs]
  exact callStack_peek regs c self (args ++ [kwv]) rest (e.oparg + 1) hl

theorem kwStack_pop (hlen : args.length = e.oparg) :
    popN (e.oparg + 3) ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
      .ok (c :: self :: (args ++ [kwv])) ⟨regs, rest⟩ := by
  obtain ⟨hs, hl⟩ := kwStack e c self kwv args rest hlen
  rw [hs]
  exact callStack_pop regs c self (args ++ [kwv]) rest (e.oparg + 1) hl

end

/-- `CALL_KW oparg` (`:5565`: `_SPECIALIZE_CALL_KW + _MAYBE_EXPAND_METHOD_KW + _DO_CALL_KW`) on
`(callable, self_or_null, args, kwnames)`, `args` in call order with `len(args) = oparg`, the last
`len(kwnames)` of them the keyword values, for every object model. As `CALL`, with the names of the
`kwnames` tuple passed on: the expansion (`:5407-5417`); the inlined call of a function object
(`:5430-5451`, `_PyEvalFramePushAndInit` with `kwnames`, `return_offset` set, `DISPATCH_INLINED`,
operands consumed on failure); and `PyObject_Vectorcall` with `kwnames` for every other live callable
(`:5452-5466`), whose result replaces the operands and whose error pops them. Unlike `CALL`, the
macro has no `_CHECK_PERIODIC_AT_END`. -/
def CallKwGenericRules : Prop := ∀ (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val)
    (kw : List String),
  args.length = e.oparg → Live regs.rt c → kwNames kwv regs.rt = .ok kw regs.rt →
  (∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → s ≠ .null → self = .null → Live regs.rt f →
    execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
      execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ s :: f :: rest)⟩) ∧
  (∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) →
    (∀ nf r, pushInit e c (withSelf self args) kw regs = .ok nf r →
      execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
        (dispatchInlined nf : M Unit) ⟨{ r with frame := { r.frame with returnOffset := instrSize e.opcode } }, rest⟩) ∧
    (∀ x r, pushInit e c (withSelf self args) kw regs = .error x r →
      execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .error x ⟨r, rest⟩)) ∧
  ((¬ ∃ a fo, c = .ref a ∧ regs.rt.heap[a]? = some (.func fo)) →
    (∀ a f s, c = .ref a → regs.rt.heap[a]? = some (.method f s) → self ≠ .null) →
    (∀ v rt, e.om.call e.ctx c (withSelf self args) kw regs.rt = .ok v rt →
      execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .ok () ⟨{ regs with rt := rt }, v :: rest⟩) ∧
    (∀ x rt, e.om.call e.ctx c (withSelf self args) kw regs.rt = .error x rt →
      execOp e .CALL_KW ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .error x ⟨{ regs with rt := rt }, rest⟩))

theorem dropLast_snoc (xs : List Val) (k : Val) : (xs ++ [k]).dropLast = xs := List.dropLast_concat
theorem getLastD_snoc (xs : List Val) (k : Val) : (xs ++ [k]).getLastD .null = k := by
  rw [List.getLastD_eq_getLast?, List.getLast?_concat]; rfl

theorem callKwGenericRules_proven : CallKwGenericRules := by
  intro e regs c self kwv args rest kw hlen hc hkw

  refine ⟨fun a f s hca ho hs hself hf => ?_, fun a fo hca ho => ⟨fun nf r hp => ?_, fun x r hp => ?_⟩,
    fun hnf hk => ⟨fun v rt hv => ?_, fun x rt hx => ?_⟩⟩
  · subst hca hself
    have h1 := maybeExpandKw_expand e regs kwv args rest hlen a f s ho
    have h2 := maybeExpandKw_keep e regs f s kwv args rest hlen hf (fun _ _ _ _ _ => hs)
    simp only [execOp, CALL_KW, _SPECIALIZE_CALL_KW, bind, EStateM.bind, pure, EStateM.pure]
    rw [h1, h2]
  · subst hca
    have hk := maybeExpandKw_keep e regs (.ref a) self kwv args rest hlen hc (by intro _ _ _ h; cases h; simp [ho])
    simp only [execOp, CALL_KW, _SPECIALIZE_CALL_KW, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk]
    simp only [_DO_CALL_KW, bind, EStateM.bind, kwStack_peek e regs (.ref a) self kwv args rest hlen,
      dropLast_snoc, getLastD_snoc]
    simp [bind, EStateM.bind, BM.lift, hkw, isFunction, getObj, ho, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure, kwStack_pop e regs (.ref a) self kwv args rest hlen, hp,
      setReturnOffset, modifyFrame]
  · subst hca
    have hk := maybeExpandKw_keep e regs (.ref a) self kwv args rest hlen hc (by intro _ _ _ h; cases h; simp [ho])
    simp only [execOp, CALL_KW, _SPECIALIZE_CALL_KW, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk]
    simp only [_DO_CALL_KW, bind, EStateM.bind, kwStack_peek e regs (.ref a) self kwv args rest hlen,
      dropLast_snoc, getLastD_snoc]
    simp [bind, EStateM.bind, BM.lift, hkw, isFunction, getObj, ho, RM.lift, liftM, monadLift,
      MonadLift.monadLift, pure, EStateM.pure, kwStack_pop e regs (.ref a) self kwv args rest hlen, hp]
  · have hk' := maybeExpandKw_keep e regs c self kwv args rest hlen hc hk
    have hf := isFunction_false regs c hc hnf
    simp only [execOp, CALL_KW, _SPECIALIZE_CALL_KW, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk']
    simp only [_DO_CALL_KW, bind, EStateM.bind, kwStack_peek e regs c self kwv args rest hlen,
      dropLast_snoc, getLastD_snoc]
    simp [bind, EStateM.bind, BM.lift, hkw, hf, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, stk, kwStack_pop e regs c self kwv args rest hlen, hv, pushAll]
  · have hk' := maybeExpandKw_keep e regs c self kwv args rest hlen hc hk
    have hf := isFunction_false regs c hc hnf
    simp only [execOp, CALL_KW, _SPECIALIZE_CALL_KW, bind, EStateM.bind, pure, EStateM.pure]
    rw [hk']
    simp only [_DO_CALL_KW, bind, EStateM.bind, kwStack_peek e regs c self kwv args rest hlen,
      dropLast_snoc, getLastD_snoc]
    simp [bind, EStateM.bind, BM.lift, hkw, hf, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
      EStateM.pure, stk, kwStack_pop e regs c self kwv args rest hlen, hx]

end PyLean.Bytecode
