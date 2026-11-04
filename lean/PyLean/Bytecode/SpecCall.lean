import PyLean.Bytecode.SpecMisc

/-!
The `CALL` specializations for known builtins (`Python/bytecodes.c:4671-4756`, `:4988-5090`) and
`_CHECK_PERIODIC_AT_END` (`:163-166`), for every object model.

Each specialized form is stated twice, in the pattern of `SpecFast.lean`: on the stack its guards
accept it runs its own body (which builtin slot it calls, what it pushes, what it keeps when the slot
raises), and on every stack a guard rejects it is the generic `CALL` on the same state. A guard that
rejected a valid stack, accepted an invalid one, or a body that called the wrong slot or popped
where C keeps, fails one conjunct.
-/

namespace PyLean.Bytecode

open Uop

/-- `_CHECK_PERIODIC_AT_END` (`:163-166`, `check_periodics_at_end`, `Python/ceval_macros.h:550-563`):
with no event pending nothing happens; with one pending it is handled as by `_CHECK_PERIODIC`
(the handler's exception is raised with the stack unchanged), except right after a `LOAD_SPECIAL`
code unit, where the event is left pending for a later check. -/
def CheckPeriodicAtEndRules : Prop := ∀ (e : Env) (regs : Regs) (stack : List Val),
  (regs.rt.pendingExc = .null → _CHECK_PERIODIC_AT_END e ⟨regs, stack⟩ = .ok () ⟨regs, stack⟩) ∧
  (∀ c ins, regs.rt.pendingExc ≠ .null → regs.frame.instrPtr ≠ 0 → e.P[regs.frame.code]? = some c →
    c.instrs[regs.frame.instrPtr - 1]? = some ins → ins.op = .LOAD_SPECIAL →
    _CHECK_PERIODIC_AT_END e ⟨regs, stack⟩ = .ok () ⟨regs, stack⟩) ∧
  (regs.rt.pendingExc ≠ .null →
    (regs.frame.instrPtr = 0 ∨ ∀ c ins, e.P[regs.frame.code]? = some c →
      c.instrs[regs.frame.instrPtr - 1]? = some ins → ins.op ≠ .LOAD_SPECIAL) →
    _CHECK_PERIODIC_AT_END e ⟨regs, stack⟩ = _CHECK_PERIODIC ⟨regs, stack⟩)

theorem checkPeriodicAtEndRules_proven : CheckPeriodicAtEndRules := by
  intro e regs stack
  refine ⟨fun h => ?_, fun c ins hp hz hc hi ho => ?_, fun hp hn => ?_⟩
  · simp [_CHECK_PERIODIC_AT_END, checkPeriodicsAtEnd, BM.lift, h]
  · have hb : (regs.rt.pendingExc == .null) = false := by simpa using hp
    have hz' : (regs.frame.instrPtr != 0) = true := by simpa using hz
    simp [_CHECK_PERIODIC_AT_END, checkPeriodicsAtEnd, BM.lift, hb, hc, hi, ho, hz']
  · have hb : (regs.rt.pendingExc == .null) = false := by simpa using hp
    simp only [_CHECK_PERIODIC_AT_END, _CHECK_PERIODIC, checkPeriodicsAtEnd, BM.lift, hb, liftM, monadLift,
      MonadLift.monadLift]
    rcases hn with h0 | hn
    · simp [h0]
    · cases hc : e.P[regs.frame.code]? with
      | none => simp
      | some c =>
        cases hi : c.instrs[regs.frame.instrPtr - 1]? with
        | none => simp [hi]
        | some ins =>
          have := hn c ins hc hi
          simp [hi, this]

/-- `CALL_TYPE_1`, `CALL_STR_1`, `CALL_TUPLE_1` (`:4679-4756`) and `CALL_LEN` (`:4988-5020`) on
`(callable, null, arg)`, and `CALL_ISINSTANCE` (`:5022-5051`) on `(callable, null, instance, cls)`:
when the `self_or_null` slot is `NULL` and the callable is the builtin `type`, `str`, `tuple`, `len`
or `isinstance` itself, the instruction pushes `Py_TYPE(arg)`, `PyObject_Str(arg)`,
`PySequence_Tuple(arg)` (the call `tuple(arg)`), `PyObject_Length(arg)` as an int, or the bool of
`PyObject_IsInstance(instance, cls)` in place of its operands; when that slot raises, the operands
all stay (`ERROR_NO_POP`); `CALL_STR_1` and `CALL_TUPLE_1` then run `_CHECK_PERIODIC_AT_END` with
the result on the stack, and end as it does. On every other stack they are the generic `CALL`. -/
def CallBuiltin1Rules : Prop := ∀ (e : Env) (regs : Regs) (c s a b : Val) (rest : List Val),
  let S := a :: s :: c :: rest
  (s = .null → c = .cls "type" → ∀ t rt, typeOf a regs.rt = .ok t rt →
    execOp e .CALL_TYPE_1 ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, t :: rest⟩) ∧
  ((s ≠ .null ∨ c ≠ .cls "type") → execOp e .CALL_TYPE_1 ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (s = .null → c = .cls "str" →
    (∀ r rt s', e.om.str e.ctx a regs.rt = .ok r rt →
      _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, r :: rest⟩ = .ok () s' →
      execOp e .CALL_STR_1 ⟨regs, S⟩ = .ok () s') ∧
    (∀ r rt x s', e.om.str e.ctx a regs.rt = .ok r rt →
      _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, r :: rest⟩ = .error (.exc x) s' →
      execOp e .CALL_STR_1 ⟨regs, S⟩ = .error (.exc x) s') ∧
    (∀ x rt, e.om.str e.ctx a regs.rt = .error (.exc x) rt →
      execOp e .CALL_STR_1 ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, S⟩)) ∧
  ((s ≠ .null ∨ c ≠ .cls "str") → execOp e .CALL_STR_1 ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (s = .null → c = .cls "tuple" →
    (∀ r rt s', e.om.call e.ctx c [a] [] regs.rt = .ok r rt →
      _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, r :: rest⟩ = .ok () s' →
      execOp e .CALL_TUPLE_1 ⟨regs, S⟩ = .ok () s') ∧
    (∀ r rt x s', e.om.call e.ctx c [a] [] regs.rt = .ok r rt →
      _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, r :: rest⟩ = .error (.exc x) s' →
      execOp e .CALL_TUPLE_1 ⟨regs, S⟩ = .error (.exc x) s') ∧
    (∀ x rt, e.om.call e.ctx c [a] [] regs.rt = .error (.exc x) rt →
      execOp e .CALL_TUPLE_1 ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, S⟩)) ∧
  ((s ≠ .null ∨ c ≠ .cls "tuple") → execOp e .CALL_TUPLE_1 ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (s = .null → c = .builtin "len" →
    (∀ n rt, e.om.length e.ctx a regs.rt = .ok n rt →
      execOp e .CALL_LEN ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, .int n :: rest⟩) ∧
    (∀ x rt, e.om.length e.ctx a regs.rt = .error (.exc x) rt →
      execOp e .CALL_LEN ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, S⟩)) ∧
  ((s ≠ .null ∨ c ≠ .builtin "len") → execOp e .CALL_LEN ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (s = .null → c = .builtin "isinstance" →
    (∀ r rt, e.om.isInstance e.ctx a b regs.rt = .ok r rt →
      execOp e .CALL_ISINSTANCE ⟨regs, b :: S⟩ = .ok () ⟨{ regs with rt := rt }, .bool r :: rest⟩) ∧
    (∀ x rt, e.om.isInstance e.ctx a b regs.rt = .error (.exc x) rt →
      execOp e .CALL_ISINSTANCE ⟨regs, b :: S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, b :: S⟩)) ∧
  ((s ≠ .null ∨ c ≠ .builtin "isinstance") →
    execOp e .CALL_ISINSTANCE ⟨regs, b :: S⟩ = execOp e .CALL ⟨regs, b :: S⟩)

theorem deopt_nosnull (w : Val) (body : M Unit) (regs : Regs) (a s c : Val) (rest : List Val)
    (hn : s ≠ .null ∨ c ≠ w) :
    (do _GUARD_NOS_NULL; guardCallable w; body) ⟨regs, a :: s :: c :: rest⟩ =
      .error .deopt ⟨regs, a :: s :: c :: rest⟩ := by
  by_cases hs : s = .null
  · subst hs
    have hc : c ≠ w := by simpa using hn
    have hb : (c != w) = true := by simpa using hc
    bc_simp [_GUARD_NOS_NULL, guardCallable, hb]
  · have hb : (s != .null) = true := by simpa using hs
    bc_simp [_GUARD_NOS_NULL, hb]

theorem deopt_thirdnull (body : M Unit) (regs : Regs) (b a s c : Val) (rest : List Val)
    (hn : s ≠ .null ∨ c ≠ .builtin "isinstance") :
    (do _GUARD_THIRD_NULL; _GUARD_CALLABLE_ISINSTANCE; body) ⟨regs, b :: a :: s :: c :: rest⟩ =
      .error .deopt ⟨regs, b :: a :: s :: c :: rest⟩ := by
  by_cases hs : s = .null
  · subst hs
    have hc : c ≠ .builtin "isinstance" := by simpa using hn
    have hb : (c != .builtin "isinstance") = true := by simpa using hc
    bc_simp [_GUARD_THIRD_NULL, _GUARD_CALLABLE_ISINSTANCE, hb]
  · have hb : (s != .null) = true := by simpa using hs
    bc_simp [_GUARD_THIRD_NULL, hb]

theorem callBuiltin1Rules_proven : CallBuiltin1Rules := by
  intro e regs c s a b rest
  refine ⟨fun hs hc t rt h => ?_, fun hn => ?_,
    fun hs hc => ⟨fun r rt s' h hp => ?_, fun r rt x s' h hp => ?_, fun x rt h => ?_⟩, fun hn => ?_,
    fun hs hc => ⟨fun r rt s' h hp => ?_, fun r rt x s' h hp => ?_, fun x rt h => ?_⟩, fun hn => ?_,
    fun hs hc => ⟨fun n rt h => ?_, fun x rt h => ?_⟩, fun hn => ?_,
    fun hs hc => ⟨fun r rt h => ?_, fun x rt h => ?_⟩, fun hn => ?_⟩
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_TYPE_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_TYPE_1, _CALL_TYPE_1, h]
  · exact withDeopt_of (deopt_nosnull (.cls "type") _ regs a s c rest hn)
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_STR_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_STR_1, _CALL_STR_1, h, hp]
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_STR_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_STR_1, _CALL_STR_1, h, hp]
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_STR_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_STR_1, _CALL_STR_1, h]
  · exact withDeopt_of (deopt_nosnull (.cls "str") _ regs a s c rest hn)
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_TUPLE_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_TUPLE_1, _CALL_TUPLE_1, h, hp]
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_TUPLE_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_TUPLE_1, _CALL_TUPLE_1, h, hp]
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_TUPLE_1, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_TUPLE_1, _CALL_TUPLE_1, h]
  · exact withDeopt_of (deopt_nosnull (.cls "tuple") _ regs a s c rest hn)
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_LEN, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_LEN, _CALL_LEN, h]
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_LEN, _GUARD_NOS_NULL, guardCallable, _GUARD_CALLABLE_LEN, _CALL_LEN, h]
  · exact withDeopt_of (deopt_nosnull (.builtin "len") _ regs a s c rest hn)
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_ISINSTANCE, _GUARD_THIRD_NULL, _GUARD_CALLABLE_ISINSTANCE, _CALL_ISINSTANCE, h]
  · subst hs hc
    bc_simp [execOp, withDeopt, CALL_ISINSTANCE, _GUARD_THIRD_NULL, _GUARD_CALLABLE_ISINSTANCE, _CALL_ISINSTANCE, h]
  · exact withDeopt_of (deopt_thirdnull _ regs b a s c rest hn)

/-- `CALL_LIST_APPEND` (`:5053-5090`), the specialization of `l.append(x)` on `(callable, self,
arg)`: when the callable is `list.append` itself (`callable_cache.list_append`), `self` is present
and an exact list, `arg` is appended to it and `None` replaces the three operands (for the
`POP_TOP` the compiler puts after the call). On every other stack it is the generic `CALL`. -/
def CallListAppendRules : Prop := ∀ (e : Env) (regs : Regs) (c s a : Val) (rest : List Val),
  Live regs.rt s →
  (c = .methDescr "list" "append" → ∀ l items, s = .ref l → regs.rt.heap[l]? = some (.list items) →
    execOp e .CALL_LIST_APPEND ⟨regs, a :: s :: c :: rest⟩ =
      .ok () ⟨{ regs with rt := { regs.rt with heap := regs.rt.heap.setIfInBounds l (.list (items.push a)) } },
        .none :: rest⟩) ∧
  ((c ≠ .methDescr "list" "append" ∨ ¬ IsList regs.rt s) →
    execOp e .CALL_LIST_APPEND ⟨regs, a :: s :: c :: rest⟩ = execOp e .CALL ⟨regs, a :: s :: c :: rest⟩)

theorem callListAppendRules_proven : CallListAppendRules := by
  intro e regs c s a rest hl
  have gL := guardRules_proven.2.2.2.2.2.2.2.2.1 regs (c :: rest) s a hl
  constructor
  · rintro rfl l items rfl ho
    have g1 := gL.1 ⟨l, items, rfl, ho⟩
    simp only [execOp]
    apply withDeopt_ok
    simp only [CALL_LIST_APPEND, bind, EStateM.bind]
    have h1 : _GUARD_CALLABLE_LIST_APPEND ⟨regs, a :: .ref l :: .methDescr "list" "append" :: rest⟩ =
        .ok () ⟨regs, a :: .ref l :: .methDescr "list" "append" :: rest⟩ := by
      bc_simp [_GUARD_CALLABLE_LIST_APPEND, guardCallable]
    have h2 : _GUARD_NOS_NOT_NULL ⟨regs, a :: .ref l :: .methDescr "list" "append" :: rest⟩ =
        .ok () ⟨regs, a :: .ref l :: .methDescr "list" "append" :: rest⟩ := by
      bc_simp [_GUARD_NOS_NOT_NULL]
    rw [h1]; simp only; rw [h2]; simp only; rw [g1]; simp only
    bc_simp [_CALL_LIST_APPEND, listAppend, ho, setObj]
  · intro hn
    simp only [execOp]
    by_cases hc : c = .methDescr "list" "append"
    · subst hc
      have hn' : ¬ IsList regs.rt s := by simpa using hn
      have h1 : _GUARD_CALLABLE_LIST_APPEND ⟨regs, a :: s :: .methDescr "list" "append" :: rest⟩ =
          .ok () ⟨regs, a :: s :: .methDescr "list" "append" :: rest⟩ := by
        bc_simp [_GUARD_CALLABLE_LIST_APPEND, guardCallable]
      by_cases hs : s = .null
      · subst hs
        refine withDeopt_of (s' := ⟨regs, a :: .null :: .methDescr "list" "append" :: rest⟩) ?_
        simp only [CALL_LIST_APPEND, bind, EStateM.bind]
        rw [h1]; simp only
        bc_simp [_GUARD_NOS_NOT_NULL]
      · have h2 : _GUARD_NOS_NOT_NULL ⟨regs, a :: s :: .methDescr "list" "append" :: rest⟩ =
            .ok () ⟨regs, a :: s :: .methDescr "list" "append" :: rest⟩ := by
          bc_simp [_GUARD_NOS_NOT_NULL, hs]
        refine withDeopt_of (s' := ⟨regs, a :: s :: .methDescr "list" "append" :: rest⟩) ?_
        simp only [CALL_LIST_APPEND, bind, EStateM.bind]
        rw [h1]; simp only; rw [h2]; simp only
        rw [gL.2 hn']
    · have hb : (c != .methDescr "list" "append") = true := by simpa using hc
      refine withDeopt_of (s' := ⟨regs, a :: s :: c :: rest⟩) ?_
      bc_simp [CALL_LIST_APPEND, _GUARD_CALLABLE_LIST_APPEND, guardCallable, hb]

/-- The NULL guards, `Python/bytecodes.c`, on their own: `_GUARD_NOS_NOT_NULL` (`:1753-1755`, in
`CALL_LIST_APPEND` before `_GUARD_NOS_LIST` and in `SEND_VIRTUAL`) exits exactly when the second
value is `NULL` and `_GUARD_TOS_NOT_NULL` (`:3868-3870`, in `FOR_ITER_VIRTUAL`) exactly when the top
is, each leaving the stack as it was; `_GUARD_NOS_NULL` (`:4671-4673`) and `_GUARD_THIRD_NULL`
(`:4675-4677`) exit exactly when the slot is not `NULL`. For every value in the slot and every
stack. In `CALL_LIST_APPEND` the NULL `self` is the one value C's `PyList_CheckExact` in
`_GUARD_NOS_LIST` must never see (it dereferences its argument), so the exit here is what keeps it
away. -/
def NullGuardRules : Prop := ∀ (regs : Regs) (x y z : Val) (rest : List Val),
  _GUARD_NOS_NOT_NULL ⟨regs, y :: x :: rest⟩ =
    (if x = .null then .error .deopt ⟨regs, y :: x :: rest⟩ else .ok () ⟨regs, y :: x :: rest⟩) ∧
  _GUARD_TOS_NOT_NULL ⟨regs, x :: rest⟩ =
    (if x = .null then .error .deopt ⟨regs, x :: rest⟩ else .ok () ⟨regs, x :: rest⟩) ∧
  _GUARD_NOS_NULL ⟨regs, y :: x :: rest⟩ =
    (if x = .null then .ok () ⟨regs, y :: x :: rest⟩ else .error .deopt ⟨regs, y :: x :: rest⟩) ∧
  _GUARD_THIRD_NULL ⟨regs, z :: y :: x :: rest⟩ =
    (if x = .null then .ok () ⟨regs, z :: y :: x :: rest⟩ else .error .deopt ⟨regs, z :: y :: x :: rest⟩)

theorem nullGuardRules_proven : NullGuardRules := by
  intro regs x y z rest
  refine ⟨?_, ?_, ?_, ?_⟩ <;> by_cases hx : x = .null <;>
    simp [hx, _GUARD_NOS_NOT_NULL, _GUARD_TOS_NOT_NULL, _GUARD_NOS_NULL, _GUARD_THIRD_NULL, guardTop, peekN,
      bind, EStateM.bind, BM.lift, deoptIf, pure, EStateM.pure, throw, throwThe, MonadExcept.throw,
      EStateM.throw, MonadExceptOf.throw]

def CallSpecRules : Prop := CheckPeriodicAtEndRules ∧ CallBuiltin1Rules ∧ CallListAppendRules
theorem callSpecRules_proven : CallSpecRules :=
  ⟨checkPeriodicAtEndRules_proven, callBuiltin1Rules_proven, callListAppendRules_proven⟩

end PyLean.Bytecode
