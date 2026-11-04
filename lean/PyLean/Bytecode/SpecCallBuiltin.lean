import PyLean.Bytecode.SpecAsync

/-!
The `CALL` specializations for C functions (`Python/bytecodes.c:4835-4986`, `:5090-5379`), for every
object model.

`CALL_BUILTIN_O`, `_FAST` and `_FAST_WITH_KEYWORDS` test the callable with `PyCFunction_CheckExact`
and its `ml_flags`; `CALL_METHOD_DESCRIPTOR_O`, `_NOARGS`, `_FAST` and `_FAST_WITH_KEYWORDS` test that
its type is `PyMethodDescr_Type`, its `ml_flags`, the argument count and that `self` has exactly the
descriptor's `d_type` (`Py_IS_TYPE`, the type object itself); `CALL_BUILTIN_CLASS` tests `PyType_Check`
and `tp_vectorcall`. The forms of `METH_O` and `METH_NOARGS` also exit when the C stack is past its soft
limit (`_CHECK_RECURSION_LIMIT`, `Rt.cRecursionReached`); the others do not. `ml_meth` is
`ObjModel.mlMeth`, an arbitrary fallible callable.

Each form is stated in the pattern of `SpecCall.lean`: on a stack its guards accept, it calls
`ml_meth` (or `tp_vectorcall`) on exactly `self` and the arguments of its calling convention, the
result replaces the operands and `_CHECK_PERIODIC_AT_END` follows, and an error keeps every operand
(`ERROR_NO_POP`); on every stack a guard rejects it is the generic `CALL` on the same state. A guard
that tested the wrong flags, the type by name, or no recursion limit, or a body that passed `self` in
the wrong place or popped on failure, fails one conjunct.
-/

namespace PyLean.Bytecode

open Uop

section
variable (e : Env) (regs : Regs) (c s : Val) (args rest : List Val)

theorem builtinGuard_pass (hlen : args.length = e.oparg) (bad : Val → List Val → BM Bool)
    (h : bad c (withSelf s args) regs = .ok false regs) :
    builtinGuard e bad ⟨regs, args.reverse ++ s :: c :: rest⟩ = .ok () ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
  simp only [builtinGuard, guardTop, bind, EStateM.bind, callStack_peek regs c s args rest e.oparg hlen]
  bc_simp [h]

theorem builtinGuard_fail (hlen : args.length = e.oparg) (bad : Val → List Val → BM Bool)
    (h : bad c (withSelf s args) regs = .ok true regs) :
    builtinGuard e bad ⟨regs, args.reverse ++ s :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
  simp only [builtinGuard, guardTop, bind, EStateM.bind, callStack_peek regs c s args rest e.oparg hlen]
  bc_simp [h]

theorem stkK_call_ok (hlen : args.length = e.oparg) (f : List Val → BM (List Val)) (r : Val) (regs' : Regs)
    (h : f (c :: s :: args) regs = .ok [r] regs') :
    stkK (e.oparg + 2) 1 f ⟨regs, args.reverse ++ s :: c :: rest⟩ = .ok () ⟨regs', r :: rest⟩ := by
  have hp := callStack_peek regs' c s args rest e.oparg hlen
  have hq := callStack_pop regs' c s args rest e.oparg hlen
  simp only [stkK, bind, EStateM.bind, callStack_peek regs c s args rest e.oparg hlen, BM.lift, h]
  simp only [List.length_singleton, ↓reduceIte]
  simp only [peekN, popN] at hp hq
  simp only [popN, bind, EStateM.bind]
  split at hq <;> simp_all [pushAll]

theorem stkK_call_err (hlen : args.length = e.oparg) (f : List Val → BM (List Val)) (x : Err) (regs' : Regs)
    (h : f (c :: s :: args) regs = .error x regs') :
    stkK (e.oparg + 2) 1 f ⟨regs, args.reverse ++ s :: c :: rest⟩ = .error x ⟨regs', args.reverse ++ s :: c :: rest⟩ := by
  simp only [stkK, bind, EStateM.bind, callStack_peek regs c s args rest e.oparg hlen, BM.lift, h]

end

/-- `m` is what the instruction runs: its result replaces the operands and `_CHECK_PERIODIC_AT_END`
follows, and its exception is raised with every operand kept. -/
def RunsAs (e : Env) (regs : Regs) (S rest : List Val) (op : Op) (m : RM Val) : Prop :=
  (∀ r rt s', m regs.rt = .ok r rt → _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, r :: rest⟩ = .ok () s' →
    execOp e op ⟨regs, S⟩ = .ok () s') ∧
  (∀ r rt x s', m regs.rt = .ok r rt →
    _CHECK_PERIODIC_AT_END e ⟨{ regs with rt := rt }, r :: rest⟩ = .error (.exc x) s' →
    execOp e op ⟨regs, S⟩ = .error (.exc x) s') ∧
  (∀ x rt, m regs.rt = .error (.exc x) rt → execOp e op ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, S⟩)

/-- `CALL_BUILTIN_O` (`:4872-4914`), `CALL_BUILTIN_FAST` (`:4916-4952`), `CALL_BUILTIN_FAST_WITH_KEYWORDS`
(`:4954-4986`) and `CALL_BUILTIN_CLASS` (`:4835-4870`) on `(callable, self_or_null, args[oparg])`, with
`A` the arguments with `self` in front when it is set (`withSelf`): when `PyCFunction_CheckExact` holds
with `ml_flags` exactly `METH_O` and one argument, and the C stack is not past its limit, `CALL_BUILTIN_O`
runs `ml_meth(m_self, A[0])`; with exactly `METH_FASTCALL`, and with exactly `METH_FASTCALL | METH_KEYWORDS`,
the other two run `ml_meth(m_self, A)` whatever the C stack; `CALL_BUILTIN_CLASS` on a type with
`tp_vectorcall` runs it on `A`. On every other stack, and for `CALL_BUILTIN_O` past the C stack limit, each
is the generic `CALL`. -/
def CallBuiltinFnRules : Prop := ∀ (e : Env) (regs : Regs) (c s : Val) (args rest : List Val),
  args.length = e.oparg →
  let S := args.reverse ++ s :: c :: rest
  let A := withSelf s args
  (∀ m, e.om.cfuncOf regs.rt c = some (methO, m) → A.length = 1 → regs.rt.cRecursionReached = false →
    RunsAs e regs S rest .CALL_BUILTIN_O (e.om.mlMeth e.ctx c m A)) ∧
  (∀ m, e.om.cfuncOf regs.rt c = some (methO, m) → A.length = 1 → regs.rt.cRecursionReached = true →
    execOp e .CALL_BUILTIN_O ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  ((∀ fl m, e.om.cfuncOf regs.rt c = some (fl, m) → fl ≠ methO ∨ A.length ≠ 1) →
    execOp e .CALL_BUILTIN_O ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (∀ m, e.om.cfuncOf regs.rt c = some (methFastcall, m) →
    RunsAs e regs S rest .CALL_BUILTIN_FAST (e.om.mlMeth e.ctx c m A)) ∧
  ((∀ fl m, e.om.cfuncOf regs.rt c = some (fl, m) → fl ≠ methFastcall) →
    execOp e .CALL_BUILTIN_FAST ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (∀ m, e.om.cfuncOf regs.rt c = some (methFastcall ||| methKeywords, m) →
    RunsAs e regs S rest .CALL_BUILTIN_FAST_WITH_KEYWORDS (e.om.mlMeth e.ctx c m A)) ∧
  ((∀ fl m, e.om.cfuncOf regs.rt c = some (fl, m) → fl ≠ methFastcall ||| methKeywords) →
    execOp e .CALL_BUILTIN_FAST_WITH_KEYWORDS ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (isType c regs.rt = .ok true regs.rt → e.om.hasTypeVectorcall regs.rt c = true →
    RunsAs e regs S rest .CALL_BUILTIN_CLASS (e.om.typeVectorcall e.ctx c A)) ∧
  ((isType c regs.rt = .ok false regs.rt ∨
      (isType c regs.rt = .ok true regs.rt ∧ e.om.hasTypeVectorcall regs.rt c = false)) →
    execOp e .CALL_BUILTIN_CLASS ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩)

/-- The descriptor guard passes: `PyMethodDescr_Type` with `ml_flags = flags`, the count of `A` accepted,
and `self = A[0]` of exactly the type `d_type`. -/
def DescrPass (e : Env) (rt : Rt) (c : Val) (A : List Val) (flags : Nat) (arity : Nat → Bool)
    (dt self : Val) (tl : List Val) : Prop :=
  e.om.methDescrOf rt c = some (flags, dt) ∧ arity A.length = true ∧ A = self :: tl ∧ typeOf self rt = .ok dt rt

/-- The descriptor guard rejects: not a method descriptor, other flags, a count it refuses, or a `self`
of another type (a subclass included). -/
def DescrReject (e : Env) (rt : Rt) (c : Val) (A : List Val) (flags : Nat) (arity : Nat → Bool) : Prop :=
  e.om.methDescrOf rt c = none ∨
  ∃ fl dt, e.om.methDescrOf rt c = some (fl, dt) ∧
    (fl ≠ flags ∨ (fl = flags ∧ arity A.length = false) ∨
     (fl = flags ∧ arity A.length = true ∧ ∃ self tl T, A = self :: tl ∧ typeOf self rt = .ok T rt ∧ T ≠ dt))

/-- One `CALL_METHOD_DESCRIPTOR_*` form `op`: on a stack the guard accepts it runs `ml_meth(self, tl)`
(unless `rec` and the C stack is past its limit, where it is the generic `CALL`), and it is the
generic `CALL` on every stack the guard rejects. -/
def DescrForm (e : Env) (regs : Regs) (c : Val) (A S rest : List Val) (op : Op) (flags : Nat)
    (arity : Nat → Bool) (rec : Bool) : Prop :=
  (∀ dt self tl, DescrPass e regs.rt c A flags arity dt self tl → (rec = false ∨ regs.rt.cRecursionReached = false) →
    RunsAs e regs S rest op (e.om.mlMeth e.ctx c self tl)) ∧
  (∀ dt self tl, DescrPass e regs.rt c A flags arity dt self tl → rec = true → regs.rt.cRecursionReached = true →
    execOp e op ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩) ∧
  (DescrReject e regs.rt c A flags arity → execOp e op ⟨regs, S⟩ = execOp e .CALL ⟨regs, S⟩)

/-- `CALL_METHOD_DESCRIPTOR_O` (`METH_O`, two arguments with `self`, `:5090-5163`), `_NOARGS`
(`METH_NOARGS`, one, `:5239-5305`), `_FAST` (`METH_FASTCALL`, at least one, `:5307-5379`) and
`_FAST_WITH_KEYWORDS` (`METH_FASTCALL | METH_KEYWORDS`, at least one, `:5165-5237`) on
`(callable, self_or_null, args[oparg])`: each is `DescrForm` with the C stack check for `METH_O` and
`METH_NOARGS` only. `ml_meth` gets `self = A[0]` and the rest: `[arg]`, `[]` (the `NULL`), or the
array. -/
def CallMethodDescrRules : Prop := ∀ (e : Env) (regs : Regs) (c s : Val) (args rest : List Val),
  args.length = e.oparg →
  let S := args.reverse ++ s :: c :: rest
  let A := withSelf s args
  DescrForm e regs c A S rest .CALL_METHOD_DESCRIPTOR_O methO (· == 2) true ∧
  DescrForm e regs c A S rest .CALL_METHOD_DESCRIPTOR_NOARGS methNoArgs (· == 1) true ∧
  DescrForm e regs c A S rest .CALL_METHOD_DESCRIPTOR_FAST methFastcall (· != 0) false ∧
  DescrForm e regs c A S rest .CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS (methFastcall ||| methKeywords) (· != 0) false

section
variable (e : Env) (regs : Regs) (c s : Val) (args rest : List Val)

theorem checkRecursionLimit_eq (S : List Val) :
    _CHECK_RECURSION_LIMIT ⟨regs, S⟩ =
      (if regs.rt.cRecursionReached then .error .deopt ⟨regs, S⟩ else .ok () ⟨regs, S⟩) := by
  cases h : regs.rt.cRecursionReached <;> bc_simp [_CHECK_RECURSION_LIMIT, readRt, h]

theorem cfuncGuard_pass (hlen : args.length = e.oparg) (flags : Nat) (ar : Option Nat) (m : Val)
    (hc : e.om.cfuncOf regs.rt c = some (flags, m))
    (har : ∀ n, ar = some n → (withSelf s args).length = n) :
    cfuncGuard e flags ar ⟨regs, args.reverse ++ s :: c :: rest⟩ = .ok () ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
  unfold cfuncGuard
  apply builtinGuard_pass e regs c s args rest hlen
  cases ar with
  | none => bc_simp [readRt, hc]
  | some n => bc_simp [readRt, hc, har n rfl]

theorem cfuncGuard_fail (hlen : args.length = e.oparg) (flags : Nat) (ar : Option Nat)
    (h : ∀ fl m, e.om.cfuncOf regs.rt c = some (fl, m) → fl ≠ flags ∨ ∃ n, ar = some n ∧ (withSelf s args).length ≠ n) :
    cfuncGuard e flags ar ⟨regs, args.reverse ++ s :: c :: rest⟩ = .error .deopt ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
  unfold cfuncGuard
  apply builtinGuard_fail e regs c s args rest hlen
  cases hc : e.om.cfuncOf regs.rt c with
  | none => bc_simp [readRt, hc]
  | some p =>
    obtain ⟨fl, m⟩ := p
    rcases h fl m hc with hf | ⟨n, hn, hl⟩
    · have hb : (fl != flags) = true := by simpa using hf
      bc_simp [readRt, hc, hb]
    · subst hn
      by_cases hf : fl = flags
      · subst hf; bc_simp [readRt, hc, hl]
      · have hb : (fl != flags) = true := by simpa using hf
        bc_simp [readRt, hc, hb]

theorem cfuncSelf_eq (m : Val) (fl : Nat) (h : e.om.cfuncOf regs.rt c = some (fl, m)) :
    cfuncSelf e c regs = .ok m regs := by
  bc_simp [cfuncSelf, readRt, h]

end

/-- The shared tail: `pre` passes, then `body` runs `m`, then `_CHECK_PERIODIC_AT_END`. -/
theorem runsAs_of (e : Env) (regs : Regs) (S rest : List Val) (op : Op) (pre body : M Unit) (m : RM Val)
    (hop : ∀ st, execOp e op st = withDeopt (do pre; body; _CHECK_PERIODIC_AT_END e) (CALL e) st)
    (hpre : pre ⟨regs, S⟩ = .ok () ⟨regs, S⟩)
    (hok : ∀ r rt, m regs.rt = .ok r rt → body ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩)
    (herr : ∀ x rt, m regs.rt = .error (.exc x) rt → body ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, S⟩) :
    RunsAs e regs S rest op m := by
  refine ⟨fun r rt s' h hp => ?_, fun r rt x s' h hp => ?_, fun x rt h => ?_⟩
  · rw [hop]; simp only [withDeopt, bind, EStateM.bind, hpre, hok r rt h, hp]
  · rw [hop]; simp only [withDeopt, bind, EStateM.bind, hpre, hok r rt h, hp]
  · rw [hop]; simp only [withDeopt, bind, EStateM.bind, hpre, herr x rt h]

/-- The body of the `ml_meth` calls on `A = withSelf s args`. -/
theorem cfuncBody_ok (e : Env) (regs : Regs) (c s : Val) (args rest : List Val) (hlen : args.length = e.oparg)
    (g : Val → List Val → BM Val) (r : Val) (regs' : Regs) (h : g c (withSelf s args) regs = .ok r regs') :
    stkK (e.oparg + 2) 1 (fun
      | c :: s :: args => do pure [← g c (withSelf s args)]
      | _ => fault "arity") ⟨regs, args.reverse ++ s :: c :: rest⟩ = .ok () ⟨regs', r :: rest⟩ := by
  apply stkK_call_ok e regs c s args rest hlen
  bc_simp [h]

theorem cfuncBody_err (e : Env) (regs : Regs) (c s : Val) (args rest : List Val) (hlen : args.length = e.oparg)
    (g : Val → List Val → BM Val) (x : Err) (regs' : Regs) (h : g c (withSelf s args) regs = .error x regs') :
    stkK (e.oparg + 2) 1 (fun
      | c :: s :: args => do pure [← g c (withSelf s args)]
      | _ => fault "arity") ⟨regs, args.reverse ++ s :: c :: rest⟩ = .error x ⟨regs', args.reverse ++ s :: c :: rest⟩ := by
  apply stkK_call_err e regs c s args rest hlen
  bc_simp [h]

theorem callBuiltinFnRules_proven : CallBuiltinFnRules := by
  intro e regs c s args rest hlen
  dsimp only
  have fast : ∀ (op : Op) (flags : Nat) (guard body : M Unit),
      (∀ st, execOp e op st = withDeopt (do guard; body; _CHECK_PERIODIC_AT_END e) (CALL e) st) →
      guard = cfuncGuard e flags none →
      body = stkK (e.oparg + 2) 1 (fun
        | c :: s :: args => do pure [← e.om.mlMeth e.ctx c (← cfuncSelf e c) (withSelf s args)]
        | _ => fault "arity") →
      (∀ m, e.om.cfuncOf regs.rt c = some (flags, m) →
        RunsAs e regs (args.reverse ++ s :: c :: rest) rest op (e.om.mlMeth e.ctx c m (withSelf s args))) ∧
      ((∀ fl m, e.om.cfuncOf regs.rt c = some (fl, m) → fl ≠ flags) →
        execOp e op ⟨regs, args.reverse ++ s :: c :: rest⟩ = execOp e .CALL ⟨regs, args.reverse ++ s :: c :: rest⟩) := by
    intro op flags guard body hop hg hb
    subst hg hb
    refine ⟨fun m hc => ?_, fun hn => ?_⟩
    · refine runsAs_of e regs _ rest op _ _ _ hop
        (cfuncGuard_pass e regs c s args rest hlen flags none m hc (fun n hn => by cases hn))
        (fun r rt h => ?_) (fun x rt h => ?_)
      · apply stkK_call_ok e regs c s args rest hlen
        bc_simp [cfuncSelf_eq e regs c m flags hc, h]
      · apply stkK_call_err e regs c s args rest hlen
        bc_simp [cfuncSelf_eq e regs c m flags hc, h]
    · rw [hop]
      refine withDeopt_of (s' := ⟨regs, args.reverse ++ s :: c :: rest⟩) ?_
      simp only [bind, EStateM.bind]
      rw [cfuncGuard_fail e regs c s args rest hlen flags none (fun fl m h => .inl (hn fl m h))]
  obtain ⟨f1, f2⟩ := fast .CALL_BUILTIN_FAST methFastcall (_GUARD_CALLABLE_BUILTIN_FAST e) (_CALL_BUILTIN_FAST e)
    (fun st => by simp only [execOp, CALL_BUILTIN_FAST]) rfl rfl
  obtain ⟨k1, k2⟩ := fast .CALL_BUILTIN_FAST_WITH_KEYWORDS (methFastcall ||| methKeywords)
    (_GUARD_CALLABLE_BUILTIN_FAST_WITH_KEYWORDS e) (_CALL_BUILTIN_FAST_WITH_KEYWORDS e)
    (fun st => by simp only [execOp, CALL_BUILTIN_FAST_WITH_KEYWORDS, bind_assoc]) rfl rfl
  refine ⟨fun m hc hA hr => ?_, fun m hc hA hr => ?_, fun hn => ?_, f1, f2, k1, k2, fun ht hv => ?_, fun hn => ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, withSelf s args = [a] := List.length_eq_one_iff.mp hA
    refine runsAs_of e regs _ rest _ (do _GUARD_CALLABLE_BUILTIN_O e; _CHECK_RECURSION_LIMIT) (_CALL_BUILTIN_O e) _
      (fun st => by simp only [execOp, CALL_BUILTIN_O, bind_assoc]) ?_ (fun r rt h => ?_) (fun x rt h => ?_)
    · simp only [bind, EStateM.bind, _GUARD_CALLABLE_BUILTIN_O,
        cfuncGuard_pass e regs c s args rest hlen methO (some 1) m hc (fun n hn => by cases hn; exact hA),
        checkRecursionLimit_eq, hr]
      rfl
    · apply stkK_call_ok e regs c s args rest hlen
      rw [ha] at h
      bc_simp [ha, cfuncSelf_eq e regs c m methO hc, h]
    · apply stkK_call_err e regs c s args rest hlen
      rw [ha] at h
      bc_simp [ha, cfuncSelf_eq e regs c m methO hc, h]
  · refine withDeopt_of (s' := ⟨regs, args.reverse ++ s :: c :: rest⟩) ?_
    simp only [CALL_BUILTIN_O, bind, EStateM.bind, _GUARD_CALLABLE_BUILTIN_O,
      cfuncGuard_pass e regs c s args rest hlen methO (some 1) m hc (fun n hn => by cases hn; exact hA),
      checkRecursionLimit_eq, hr]
    rfl
  · refine withDeopt_of (s' := ⟨regs, args.reverse ++ s :: c :: rest⟩) ?_
    simp only [CALL_BUILTIN_O, bind, EStateM.bind, _GUARD_CALLABLE_BUILTIN_O]
    rw [cfuncGuard_fail e regs c s args rest hlen methO (some 1) (fun fl m h => by
      rcases hn fl m h with h | h
      · exact .inl h
      · exact .inr ⟨1, rfl, h⟩)]
  · have hg : _GUARD_CALLABLE_BUILTIN_CLASS e ⟨regs, args.reverse ++ s :: c :: rest⟩ =
        .ok () ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
      unfold _GUARD_CALLABLE_BUILTIN_CLASS
      apply builtinGuard_pass e regs c s args rest hlen
      bc_simp [RM.lift, ht, hv, readRt]
    refine runsAs_of e regs _ rest _ _ (_CALL_BUILTIN_CLASS e) _
      (fun st => by simp only [execOp, CALL_BUILTIN_CLASS]) hg (fun r rt h => ?_) (fun x rt h => ?_)
    · apply stkK_call_ok e regs c s args rest hlen
      bc_simp [h]
    · apply stkK_call_err e regs c s args rest hlen
      bc_simp [h]
  · refine withDeopt_of (s' := ⟨regs, args.reverse ++ s :: c :: rest⟩) ?_
    simp only [CALL_BUILTIN_CLASS, bind, EStateM.bind, _GUARD_CALLABLE_BUILTIN_CLASS]
    rcases hn with ht | ⟨ht, hv⟩
    · rw [builtinGuard_fail e regs c s args rest hlen]
      bc_simp [RM.lift, ht]
    · rw [builtinGuard_fail e regs c s args rest hlen]
      bc_simp [RM.lift, ht, hv, readRt]

section
variable (e : Env) (regs : Regs) (c s : Val) (args rest : List Val)

theorem descrGuard_pass (hlen : args.length = e.oparg) (flags : Nat) (arity : Nat → Bool) (dt self : Val)
    (tl : List Val) (h : DescrPass e regs.rt c (withSelf s args) flags arity dt self tl) :
    methDescrGuard e flags arity ⟨regs, args.reverse ++ s :: c :: rest⟩ =
      .ok () ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
  obtain ⟨hm, ha, hA, ht⟩ := h
  unfold methDescrGuard
  apply builtinGuard_pass e regs c s args rest hlen
  rw [hA] at ha ⊢
  simp only [List.length_cons] at ha
  bc_simp [readRt, hm, ha, ht]

theorem descrGuard_fail (hlen : args.length = e.oparg) (flags : Nat) (arity : Nat → Bool)
    (h : DescrReject e regs.rt c (withSelf s args) flags arity) :
    methDescrGuard e flags arity ⟨regs, args.reverse ++ s :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ s :: c :: rest⟩ := by
  unfold methDescrGuard
  apply builtinGuard_fail e regs c s args rest hlen
  rcases h with hm | ⟨fl, dt, hm, hf | ⟨hf, ha⟩ | ⟨hf, ha, self, tl, T, hA, ht, hT⟩⟩
  · bc_simp [readRt, hm]
  · have hb : (fl != flags) = true := by simpa using hf
    bc_simp [readRt, hm, hb]
  · subst hf
    bc_simp [readRt, hm, ha]
  · subst hf
    rw [hA] at ha ⊢
    simp only [List.length_cons] at ha
    have hb : (T != dt) = true := by simpa using hT
    bc_simp [readRt, hm, ha, ht, hb]

end

theorem descrForm_of (e : Env) (regs : Regs) (c : Val) (A S rest : List Val) (op : Op) (flags : Nat)
    (arity : Nat → Bool) (rec : Bool) (pre body : M Unit)
    (hop : ∀ st, execOp e op st = withDeopt (do pre; body; _CHECK_PERIODIC_AT_END e) (CALL e) st)
    (hpass : ∀ dt self tl, DescrPass e regs.rt c A flags arity dt self tl →
      (rec = false ∨ regs.rt.cRecursionReached = false) → pre ⟨regs, S⟩ = .ok () ⟨regs, S⟩)
    (hrec : ∀ dt self tl, DescrPass e regs.rt c A flags arity dt self tl → rec = true →
      regs.rt.cRecursionReached = true → pre ⟨regs, S⟩ = .error .deopt ⟨regs, S⟩)
    (hrej : DescrReject e regs.rt c A flags arity → pre ⟨regs, S⟩ = .error .deopt ⟨regs, S⟩)
    (hok : ∀ dt self tl r rt, DescrPass e regs.rt c A flags arity dt self tl →
      e.om.mlMeth e.ctx c self tl regs.rt = .ok r rt → body ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, r :: rest⟩)
    (herr : ∀ dt self tl x rt, DescrPass e regs.rt c A flags arity dt self tl →
      e.om.mlMeth e.ctx c self tl regs.rt = .error (.exc x) rt →
      body ⟨regs, S⟩ = .error (.exc x) ⟨{ regs with rt := rt }, S⟩) :
    DescrForm e regs c A S rest op flags arity rec := by
  refine ⟨fun dt self tl hp hr => ?_, fun dt self tl hp hr hc => ?_, fun hj => ?_⟩
  · exact runsAs_of e regs S rest op pre body _ hop (hpass dt self tl hp hr)
      (fun r rt h => hok dt self tl r rt hp h) (fun x rt h => herr dt self tl x rt hp h)
  · rw [hop]; exact withDeopt_of (s' := ⟨regs, S⟩) (by simp only [bind, EStateM.bind, hrec dt self tl hp hr hc])
  · rw [hop]; exact withDeopt_of (s' := ⟨regs, S⟩) (by simp only [bind, EStateM.bind, hrej hj])

theorem callMethodDescrRules_proven : CallMethodDescrRules := by
  intro e regs c s args rest hlen
  dsimp only
  have recPre : ∀ (flags : Nat) (arity : Nat → Bool) (rec : Bool) (pre : M Unit),
      pre = (do methDescrGuard e flags arity; _CHECK_RECURSION_LIMIT) → rec = true →
      (∀ dt self tl, DescrPass e regs.rt c (withSelf s args) flags arity dt self tl →
        (rec = false ∨ regs.rt.cRecursionReached = false) →
        pre ⟨regs, args.reverse ++ s :: c :: rest⟩ = .ok () ⟨regs, args.reverse ++ s :: c :: rest⟩) ∧
      (∀ dt self tl, DescrPass e regs.rt c (withSelf s args) flags arity dt self tl → rec = true →
        regs.rt.cRecursionReached = true →
        pre ⟨regs, args.reverse ++ s :: c :: rest⟩ = .error .deopt ⟨regs, args.reverse ++ s :: c :: rest⟩) ∧
      (DescrReject e regs.rt c (withSelf s args) flags arity →
        pre ⟨regs, args.reverse ++ s :: c :: rest⟩ = .error .deopt ⟨regs, args.reverse ++ s :: c :: rest⟩) := by
    intro flags arity rec pre hp hrec
    subst hp hrec
    refine ⟨fun dt self tl h hr => ?_, fun dt self tl h _ hr => ?_, fun h => ?_⟩
    · have hr' : regs.rt.cRecursionReached = false := by simpa using hr
      simp only [bind, EStateM.bind, descrGuard_pass e regs c s args rest hlen flags arity dt self tl h,
        checkRecursionLimit_eq, hr']
      rfl
    · simp only [bind, EStateM.bind, descrGuard_pass e regs c s args rest hlen flags arity dt self tl h,
        checkRecursionLimit_eq, hr]
      rfl
    · simp only [bind, EStateM.bind, descrGuard_fail e regs c s args rest hlen flags arity h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨p1, p2, p3⟩ := recPre methO (· == 2) true _ rfl rfl
    refine descrForm_of e regs c _ _ rest _ methO _ true _ (_CALL_METHOD_DESCRIPTOR_O e)
      (fun st => by simp only [execOp, CALL_METHOD_DESCRIPTOR_O, _GUARD_CALLABLE_METHOD_DESCRIPTOR_O, bind_assoc])
      p1 p2 p3 (fun dt self tl r rt hp h => ?_) (fun dt self tl x rt hp h => ?_)
    all_goals
      obtain ⟨_, ha, hA, _⟩ := hp
      rw [hA] at ha
      obtain ⟨a, rfl⟩ : ∃ a, tl = [a] := List.length_eq_one_iff.mp (by simpa using ha)
    · apply stkK_call_ok e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_O, hA, h]
    · apply stkK_call_err e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_O, hA, h]
  · obtain ⟨p1, p2, p3⟩ := recPre methNoArgs (· == 1) true _ rfl rfl
    refine descrForm_of e regs c _ _ rest _ methNoArgs _ true _ (_CALL_METHOD_DESCRIPTOR_NOARGS e)
      (fun st => by simp only [execOp, CALL_METHOD_DESCRIPTOR_NOARGS, _GUARD_CALLABLE_METHOD_DESCRIPTOR_NOARGS,
        bind_assoc])
      p1 p2 p3 (fun dt self tl r rt hp h => ?_) (fun dt self tl x rt hp h => ?_)
    all_goals
      obtain ⟨_, ha, hA, _⟩ := hp
      rw [hA] at ha
      obtain rfl : tl = [] := List.length_eq_zero_iff.mp (by simpa using ha)
    · apply stkK_call_ok e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_NOARGS, hA, h]
    · apply stkK_call_err e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_NOARGS, hA, h]
  · refine descrForm_of e regs c _ _ rest _ methFastcall _ false (methDescrGuard e methFastcall (· != 0))
      (_CALL_METHOD_DESCRIPTOR_FAST e)
      (fun st => by simp only [execOp, CALL_METHOD_DESCRIPTOR_FAST, _GUARD_CALLABLE_METHOD_DESCRIPTOR_FAST])
      (fun dt self tl h _ => descrGuard_pass e regs c s args rest hlen _ _ dt self tl h)
      (fun _ _ _ _ h _ => by cases h)
      (fun h => descrGuard_fail e regs c s args rest hlen _ _ h)
      (fun dt self tl r rt hp h => ?_) (fun dt self tl x rt hp h => ?_)
    all_goals obtain ⟨_, _, hA, _⟩ := hp
    · apply stkK_call_ok e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_FAST, hA, h]
    · apply stkK_call_err e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_FAST, hA, h]
  · refine descrForm_of e regs c _ _ rest _ (methFastcall ||| methKeywords) _ false
      (methDescrGuard e (methFastcall ||| methKeywords) (· != 0)) (_CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS e)
      (fun st => by simp only [execOp, CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS,
        _GUARD_CALLABLE_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS, bind_assoc])
      (fun dt self tl h _ => descrGuard_pass e regs c s args rest hlen _ _ dt self tl h)
      (fun _ _ _ _ h _ => by cases h)
      (fun h => descrGuard_fail e regs c s args rest hlen _ _ h)
      (fun dt self tl r rt hp h => ?_) (fun dt self tl x rt hp h => ?_)
    all_goals obtain ⟨_, _, hA, _⟩ := hp
    · apply stkK_call_ok e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS, hA, h]
    · apply stkK_call_err e regs c s args rest hlen
      bc_simp [_CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS, hA, h]

/-- The tier-2 forms (`_CALL_METHOD_DESCRIPTOR_O_INLINE`, `:5134-5151`; `_NOARGS_INLINE`, `:5278-5294`;
`_FAST_INLINE`, `:5352-5370`; `_FAST_WITH_KEYWORDS_INLINE`, `:5210-5227`) take the `ml_meth` read at
trace time as an operand. With that operand read from the callable itself, as the trace guarantees,
and `self` in the `self_or_null` slot (counted in `oparg` by the `O` and `NOARGS` forms, `assert(oparg
== 2)` and `== 1`), each is exactly its tier-1 body on the same stack, in result and in what an error
keeps. -/
def CallDescrInlineRules : Prop := ∀ (e : Env) (regs : Regs) (c self a : Val) (args rest : List Val),
  self ≠ .null →
  _CALL_METHOD_DESCRIPTOR_O_INLINE { e with oparg := 2 } c ⟨regs, a :: self :: c :: rest⟩ =
    _CALL_METHOD_DESCRIPTOR_O { e with oparg := 1 } ⟨regs, a :: self :: c :: rest⟩ ∧
  _CALL_METHOD_DESCRIPTOR_NOARGS_INLINE { e with oparg := 1 } c ⟨regs, self :: c :: rest⟩ =
    _CALL_METHOD_DESCRIPTOR_NOARGS { e with oparg := 0 } ⟨regs, self :: c :: rest⟩ ∧
  (args.length = e.oparg →
    _CALL_METHOD_DESCRIPTOR_FAST_INLINE e c ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      _CALL_METHOD_DESCRIPTOR_FAST e ⟨regs, args.reverse ++ self :: c :: rest⟩ ∧
    _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS_INLINE e c ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS e ⟨regs, args.reverse ++ self :: c :: rest⟩)

theorem callDescrInlineRules_proven : CallDescrInlineRules := by
  intro e regs c self a args rest hs
  have hw : ∀ l, withSelf self l = self :: l := fun l => by simp [withSelf, hs]
  refine ⟨?_, ?_, fun hlen => ⟨?_, ?_⟩⟩
  · simp [_CALL_METHOD_DESCRIPTOR_O_INLINE, _CALL_METHOD_DESCRIPTOR_O, stkK, peekN, hw, bind, EStateM.bind]
  · simp [_CALL_METHOD_DESCRIPTOR_NOARGS_INLINE, _CALL_METHOD_DESCRIPTOR_NOARGS, stkK, peekN, hw, bind, EStateM.bind]
  · simp only [_CALL_METHOD_DESCRIPTOR_FAST_INLINE, _CALL_METHOD_DESCRIPTOR_FAST, stkK, bind, EStateM.bind,
      callStack_peek regs c self args rest e.oparg hlen, hw]
  · simp only [_CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS_INLINE, _CALL_METHOD_DESCRIPTOR_FAST_WITH_KEYWORDS, stkK,
      bind, EStateM.bind, callStack_peek regs c self args rest e.oparg hlen, hw]

def CallBuiltinSpecRules : Prop := CallBuiltinFnRules ∧ CallMethodDescrRules ∧ CallDescrInlineRules
theorem callBuiltinSpecRules_proven : CallBuiltinSpecRules :=
  ⟨callBuiltinFnRules_proven, callMethodDescrRules_proven, callDescrInlineRules_proven⟩

/-! ## `SEND_ASYNC_GEN` -/

/-- `SEND_ASYNC_GEN` (`:1801-1830`) on `(iter, null_or_index, v)`, for every object model: when `iter` is
exactly an `async_generator_asend` it runs `am_send(iter, v)`: `PYGEN_NEXT` replaces `v` by the value,
`PYGEN_RETURN` does too and jumps by `oparg`, an exception keeps all three (`ERROR_NO_POP`); on every
other live receiver it is the generic `SEND`. In the difftest object model, `am_send` of an `asend`
is `_PyAsyncGenASend_Send` (`Objects/genobject.c:2013-2023`): `async_gen_asend_send(iter, v)`'s value is
`PYGEN_NEXT`, and its exception goes to `_PyGen_FetchStopIterationValue`, a `StopIteration`'s value being
`PYGEN_RETURN` and anything else re-raised. -/
def SendAsyncGenRules : Prop :=
  (∀ (e : Env) (regs : Regs) (it n v : Val) (rest : List Val),
    (∀ a g sv st, it = .ref a → regs.rt.heap[a]? = some (.asend g sv st) →
      (∀ r rt, e.om.amSend e.ctx it v regs.rt = .ok (r, false) rt →
        execOp e .SEND_ASYNC_GEN ⟨regs, v :: n :: it :: rest⟩ = .ok () ⟨{ regs with rt := rt }, r :: n :: it :: rest⟩) ∧
      (∀ r rt, e.om.amSend e.ctx it v regs.rt = .ok (r, true) rt →
        execOp e .SEND_ASYNC_GEN ⟨regs, v :: n :: it :: rest⟩ =
          .ok () ⟨{ regs with rt := rt, next := regs.next + e.oparg }, r :: n :: it :: rest⟩) ∧
      (∀ x rt, e.om.amSend e.ctx it v regs.rt = .error (.exc x) rt →
        execOp e .SEND_ASYNC_GEN ⟨regs, v :: n :: it :: rest⟩ = .error (.exc x) ⟨{ regs with rt := rt }, v :: n :: it :: rest⟩)) ∧
    ((∀ a, it = .ref a → ∃ o, regs.rt.heap[a]? = some o ∧ ∀ g sv st, o ≠ .asend g sv st) →
      execOp e .SEND_ASYNC_GEN ⟨regs, v :: n :: it :: rest⟩ = execOp e .SEND ⟨regs, v :: n :: it :: rest⟩)) ∧
  (∀ (ctx : Ctx) (a : Addr) (arg : Val) (rt : Rt),
    (∀ r rt', Proto.asendSend ctx a (some arg) rt = .ok r rt' → Proto.asendAmSend ctx a arg rt = .ok (r, false) rt') ∧
    (∀ x rt', Proto.asendSend ctx a (some arg) rt = .error (.exc x) rt' →
      Proto.asendAmSend ctx a arg rt = (do pure (← fetchStopIterationValue x, true) : RM (Val × Bool)) rt'))

theorem sendAsyncGenRules_proven : SendAsyncGenRules := by
  refine ⟨fun e regs it n v rest => ⟨fun a g sv st hi ho => ?_, fun hn => ?_⟩, fun ctx a arg rt => ⟨fun r rt' h => ?_,
    fun x rt' h => ?_⟩⟩
  · subst hi
    have hg : _GUARD_3OS_ASYNC_GEN_ASEND ⟨regs, v :: n :: .ref a :: rest⟩ = .ok () ⟨regs, v :: n :: .ref a :: rest⟩ := by
      bc_simp [_GUARD_3OS_ASYNC_GEN_ASEND, RM.lift, ho]
    refine ⟨fun r rt h => ?_, fun r rt h => ?_, fun x rt h => ?_⟩
    · simp only [execOp, withDeopt, SEND_ASYNC_GEN, bind, EStateM.bind, hg]
      bc_simp [_SEND_ASYNC_GEN, h]
    · simp only [execOp, withDeopt, SEND_ASYNC_GEN, bind, EStateM.bind, hg]
      bc_simp [_SEND_ASYNC_GEN, h, jumpBy]
      omega
    · simp only [execOp, withDeopt, SEND_ASYNC_GEN, bind, EStateM.bind, hg]
      bc_simp [_SEND_ASYNC_GEN, h]
  · refine withDeopt_of (s' := ⟨regs, v :: n :: it :: rest⟩) ?_
    simp only [SEND_ASYNC_GEN, bind, EStateM.bind]
    cases it with
    | ref a =>
      obtain ⟨o, ho, hne⟩ := hn a rfl
      cases o with
      | asend g sv st => exact absurd rfl (hne g sv st)
      | _ => bc_simp [_GUARD_3OS_ASYNC_GEN_ASEND, RM.lift, ho]
    | _ => bc_simp [_GUARD_3OS_ASYNC_GEN_ASEND, RM.lift]
  · simp [Proto.asendAmSend, tryExc, h, bind, EStateM.bind, pure, EStateM.pure]
  · simp [Proto.asendAmSend, tryExc, h, bind, EStateM.bind, pure, EStateM.pure]

end PyLean.Bytecode
