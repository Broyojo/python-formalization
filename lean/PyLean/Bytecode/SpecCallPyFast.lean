import PyLean.Bytecode.SpecCallPy

/-!
The specialized Python calls of `Python/bytecodes.c` on their own, before `execOp`'s restart.

`execOp` runs each specialized form as `withDeopt SPEC GENERIC` (`Exec.lean`; `execCallExPy` for
`CALL_EX_PY`), so a refinement statement `afterInstr (execOp SPEC) = afterInstr (execOp GENERIC)`
also holds for a body that always exits. The statements here are about the bodies themselves:
on every stack a guard rejects (a stale `func_version` or `im_func` version included) the body
exits with the state unchanged (or, after a method split, on the split stack); on every stack the
guards let through it completes in the state `enteredSt` describes (caller frame saved with
`return_offset = INSTRUCTION_SIZE`, the new frame current, the recursion counter decremented once),
or fails exactly as `_PyEvalFramePushAndInit` fails, operands consumed. A body that always exits,
never exits, skips the version comparison or the recursion check, or builds another frame fails
one of the clauses. The registry entries pair each with its refinement statement.
-/

namespace PyLean.Bytecode

open Uop

/-! ## `CALL_PY_GENERAL` -/

/-- The body of `CALL_PY_GENERAL` (`:4498-4506`) on `(callable, self_or_null, args[oparg])`, for
every live callable, every runtime and object model, with `next_instr = this_instr +
INSTRUCTION_SIZE`: when the callable is not a function, or is one whose `func_version` differs from
the cached one, `_CHECK_FUNCTION_VERSION` (`:4485-4490`) exits with the stack unchanged; when it
matches and `py_recursion_remaining <= 1`, `_CHECK_RECURSION_REMAINING` (`:4611-4613`) exits; with
both passing, `_PY_FRAME_GENERAL` (`:4460-4483`) builds the frame `_PyEvalFramePushAndInit` builds on
`self` and the arguments, and `_SAVE_RETURN_OFFSET + _PUSH_FRAME` (`:6136-6140`, `:4628-4642`) enter
it (`enteredSt`), or the instruction fails with the frame builder's error and the operands gone. -/
def CallPyGeneralFast : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → regs.next = e.this + instrSize e.opcode →
  ((∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat e 0) →
    CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
  (∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version = cacheNat e 0 →
    (regs.rt.pyRecursionRemaining ≤ 1 →
      CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
    (1 < regs.rt.pyRecursionRemaining →
      (∀ nf r, pushInit e c (withSelf self args) [] regs = .ok nf r →
        CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ = .ok () (enteredSt e nf r rest)) ∧
      (∀ x r, pushInit e c (withSelf self args) [] regs = .error x r →
        CALL_PY_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ = .error x ⟨r, rest⟩)))

theorem callPyGeneralFast_proven : CallPyGeneralFast := by
  intro e regs c self args rest hlen hc hn
  refine ⟨fun hb => ?_, fun a fo hca ho hv => ?_⟩
  · simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [fnVersion_fail e regs c self args rest hlen hc hb]
  · subst hca
    have hfv := fnVersion_pass e regs self args rest hlen a fo ho hv
    refine ⟨fun hr => ?_, fun hr => ⟨fun nf r hp => ?_, fun x r hp => ?_⟩⟩
    · simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]
      simp only
      rw [recRemaining_fail ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ hr]
    · have hrs := recRemaining_pass ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ hr
      obtain ⟨hr1, _⟩ := pushInit_ok e _ _ _ regs nf r hp
      have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
      simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hrs]; simp only
      rw [pyFrameGeneral_ok e regs _ self args rest hlen nf r hp]
      simp only
      have := pushFrame_entered e nf r rest hnext
      simp only [bind, EStateM.bind] at this
      exact this
    · have hrs := recRemaining_pass ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ hr
      simp only [CALL_PY_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hrs]; simp only
      rw [pyFrameGeneral_err e regs _ self args rest hlen x r hp]

/-- `bytecode-call-py-general`: the refinement and the body. -/
def CallPyGeneralSpec : Prop := CallPyGeneralRefines ∧ CallPyGeneralFast

theorem callPyGeneralSpec_proven : CallPyGeneralSpec := ⟨callPyGeneralRefines_proven, callPyGeneralFast_proven⟩

/-! ## `CALL_BOUND_METHOD_GENERAL` -/

/-- The body of `CALL_BOUND_METHOD_GENERAL` (`:4529-4539`), for every live callable with well-formed
method objects, every runtime and object model: unless the callable is a method object whose
`im_func` is a function with the cached version and `self_or_null` is `NULL`,
`_CHECK_METHOD_VERSION` (`:4508-4516`) exits with the stack unchanged (a method whose `im_func` has
another version among them); when it passes, `_EXPAND_METHOD` (`:4518-4527`) puts `im_func` and
`im_self` in the two slots, and on that split stack (`flush`) `_CHECK_RECURSION_REMAINING` exits when
`py_recursion_remaining <= 1`; otherwise the frame `_PyEvalFramePushAndInit` builds on `im_func`,
`im_self` and the arguments is entered, or its error raised with the operands gone. -/
def CallBoundMethodGeneralFast : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → MethodsWF regs.rt c → regs.next = e.this + instrSize e.opcode →
  ((∀ b f s fo, ¬ MethodPass e regs.rt c self b f s fo) →
    CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
  (∀ a b s fo, c = .ref a → self = .null → regs.rt.heap[a]? = some (.method (.ref b) s) →
    regs.rt.heap[b]? = some (.func fo) → fo.version = cacheNat e 0 →
    (regs.rt.pyRecursionRemaining ≤ 1 →
      CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ s :: .ref b :: rest⟩) ∧
    (1 < regs.rt.pyRecursionRemaining →
      (∀ nf r, pushInit e (.ref b) (withSelf s args) [] regs = .ok nf r →
        CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ = .ok () (enteredSt e nf r rest)) ∧
      (∀ x r, pushInit e (.ref b) (withSelf s args) [] regs = .error x r →
        CALL_BOUND_METHOD_GENERAL e ⟨regs, args.reverse ++ self :: c :: rest⟩ = .error x ⟨r, rest⟩)))

theorem callBoundMethodGeneralFast_proven : CallBoundMethodGeneralFast := by
  intro e regs c self args rest hlen hc hwf hn
  refine ⟨fun hn' => ?_, fun a b s fo hca hs ho hb hv => ?_⟩
  · simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [methodVersion_fail e regs c self args rest hlen hc hwf hn']
  · subst hca hs
    have hp : MethodPass e regs.rt (.ref a) .null b (.ref b) s fo := ⟨a, rfl, ho, rfl, hb, hv, rfl⟩
    have hmv := methodVersion_pass e regs (.ref a) .null args rest hlen b (.ref b) s fo hp
    have hex := expandMethod_eq e regs .null args rest hlen a (.ref b) s ho
    refine ⟨fun hr => ?_, fun hr => ⟨fun nf r hpi => ?_, fun x r hpi => ?_⟩⟩
    · simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hmv]; simp only; rw [hex]; simp only
      rw [recRemaining_fail ⟨regs, args.reverse ++ s :: .ref b :: rest⟩ hr]
    · have hrs := recRemaining_pass ⟨regs, args.reverse ++ s :: .ref b :: rest⟩ hr
      obtain ⟨hr1, _⟩ := pushInit_ok e _ _ _ regs nf r hpi
      have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
      simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hmv]; simp only; rw [hex]; simp only; rw [hrs]; simp only
      rw [pyFrameGeneral_ok e regs _ s args rest hlen nf r hpi]
      simp only
      have := pushFrame_entered e nf r rest hnext
      simp only [bind, EStateM.bind] at this
      exact this
    · have hrs := recRemaining_pass ⟨regs, args.reverse ++ s :: .ref b :: rest⟩ hr
      simp only [CALL_BOUND_METHOD_GENERAL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hmv]; simp only; rw [hex]; simp only; rw [hrs]; simp only
      rw [pyFrameGeneral_err e regs _ s args rest hlen x r hpi]

/-- `bytecode-call-bound-method-general`: the refinement and the body. -/
def CallBoundMethodGeneralSpec : Prop := CallBoundMethodGeneralRefines ∧ CallBoundMethodGeneralFast

theorem callBoundMethodGeneralSpec_proven : CallBoundMethodGeneralSpec :=
  ⟨callBoundMethodGeneralRefines_proven, callBoundMethodGeneralFast_proven⟩

/-! ## `CALL_KW_PY` -/

/-- The body of `CALL_KW_PY` (`:5511-5519`) on `(callable, self_or_null, args[oparg], kwnames)`,
`kwnames` the compiler's tuple of names: `_CHECK_FUNCTION_VERSION_KW` (`:5504-5509`) exits with the
stack unchanged on a non-function or a function whose `func_version` is not the cached one;
`_CHECK_RECURSION_REMAINING` exits when `py_recursion_remaining <= 1`; otherwise `_PY_FRAME_KW`
(`:5474-5502`) builds the frame with the keyword names and it is entered, or its error raised with
the operands gone. -/
def CallKwPyFast : Prop := ∀ (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val) (kw : List String),
  args.length = e.oparg → Live regs.rt c → kwNames kwv regs.rt = .ok kw regs.rt →
  regs.next = e.this + instrSize e.opcode →
  ((∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat e 0) →
    CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
      .error .deopt ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩) ∧
  (∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version = cacheNat e 0 →
    (regs.rt.pyRecursionRemaining ≤ 1 →
      CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
        .error .deopt ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩) ∧
    (1 < regs.rt.pyRecursionRemaining →
      (∀ nf r, pushInit e c (withSelf self args) kw regs = .ok nf r →
        CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .ok () (enteredSt e nf r rest)) ∧
      (∀ x r, pushInit e c (withSelf self args) kw regs = .error x r →
        CALL_KW_PY e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .error x ⟨r, rest⟩)))

theorem callKwPyFast_proven : CallKwPyFast := by
  intro e regs c self kwv args rest kw hlen hc hkw hn
  have hlen1 : (args ++ [kwv]).length = (kwEnv e).oparg := by simp [kwEnv, hlen]
  refine ⟨fun hb => ?_, fun a fo hca ho hv => ?_⟩
  · simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [fvKw_eq, kwStack_eq, fnVersion_fail (kwEnv e) regs c self (args ++ [kwv]) rest hlen1 hc hb]
  · subst hca
    have hfv : _CHECK_FUNCTION_VERSION_KW e ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ =
        .ok () ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ := by
      rw [fvKw_eq, kwStack_eq]
      exact fnVersion_pass (kwEnv e) regs self (args ++ [kwv]) rest hlen1 a fo ho hv
    refine ⟨fun hr => ?_, fun hr => ⟨fun nf r hp => ?_, fun x r hp => ?_⟩⟩
    · simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only
      rw [recRemaining_fail ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ hr]
    · have hrs := recRemaining_pass ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ hr
      obtain ⟨hr1, _⟩ := pushInit_ok e _ _ _ regs nf r hp
      have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
      simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hrs]; simp only
      rw [pyFrameKw_ok e regs _ self kwv args rest kw hlen hkw nf r hp]
      simp only
      have := pushFrame_entered e nf r rest hnext
      simp only [bind, EStateM.bind] at this
      exact this
    · have hrs := recRemaining_pass ⟨regs, kwv :: (args.reverse ++ self :: .ref a :: rest)⟩ hr
      simp only [CALL_KW_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hrs]; simp only
      rw [pyFrameKw_err e regs _ self kwv args rest kw hlen hkw x r hp]

/-- `bytecode-call-kw-py`: the refinement and the body. -/
def CallKwPySpec : Prop := CallKwPyRefines ∧ CallKwPyFast

theorem callKwPySpec_proven : CallKwPySpec := ⟨callKwPyRefines_proven, callKwPyFast_proven⟩

/-! ## `CALL_KW_BOUND_METHOD` -/

/-- The body of `CALL_KW_BOUND_METHOD` (`:5542-5551`): unless the callable is a method object whose
`im_func` is a function with the cached version and `self_or_null` is `NULL`,
`_CHECK_METHOD_VERSION_KW` (`:5521-5529`) exits with the stack unchanged; otherwise
`_EXPAND_METHOD_KW` (`:5531-5540`) splits the method and, whatever `py_recursion_remaining` is (there
is no `_CHECK_RECURSION_REMAINING`, python/cpython#155151), the frame `_PyEvalFramePushAndInit`
builds on `im_func`, `im_self`, the arguments and the keyword names is entered with the counter
decremented, or its error raised with the operands gone. -/
def CallKwBoundMethodFast : Prop := ∀ (e : Env) (regs : Regs) (c self kwv : Val) (args rest : List Val)
    (kw : List String),
  args.length = e.oparg → Live regs.rt c → MethodsWF regs.rt c → kwNames kwv regs.rt = .ok kw regs.rt →
  regs.next = e.this + instrSize e.opcode →
  ((∀ b f s fo, ¬ MethodPass e regs.rt c self b f s fo) →
    CALL_KW_BOUND_METHOD e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ =
      .error .deopt ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩) ∧
  (∀ a b s fo, c = .ref a → self = .null → regs.rt.heap[a]? = some (.method (.ref b) s) →
    regs.rt.heap[b]? = some (.func fo) → fo.version = cacheNat e 0 →
    (∀ nf r, pushInit e (.ref b) (withSelf s args) kw regs = .ok nf r →
      CALL_KW_BOUND_METHOD e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .ok () (enteredSt e nf r rest)) ∧
    (∀ x r, pushInit e (.ref b) (withSelf s args) kw regs = .error x r →
      CALL_KW_BOUND_METHOD e ⟨regs, kwv :: (args.reverse ++ self :: c :: rest)⟩ = .error x ⟨r, rest⟩))

theorem callKwBoundMethodFast_proven : CallKwBoundMethodFast := by
  intro e regs c self kwv args rest kw hlen hc hwf hkw hn
  have hlen1 : (args ++ [kwv]).length = (kwEnv e).oparg := by simp [kwEnv, hlen]
  refine ⟨fun hn' => ?_, fun a b s fo hca hs ho hb hv => ?_⟩
  · have hn'' : ∀ b f s fo, ¬ MethodPass (kwEnv e) regs.rt c self b f s fo := hn'
    simp only [CALL_KW_BOUND_METHOD, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [mvKw_eq, kwStack_eq, methodVersion_fail (kwEnv e) regs c self (args ++ [kwv]) rest hlen1 hc hwf hn'']
  · subst hca hs
    have hp : MethodPass e regs.rt (.ref a) .null b (.ref b) s fo := ⟨a, rfl, ho, rfl, hb, hv, rfl⟩
    have hmv : _CHECK_METHOD_VERSION_KW e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
        .ok () ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ := by
      rw [mvKw_eq, kwStack_eq]
      exact methodVersion_pass (kwEnv e) regs (.ref a) .null (args ++ [kwv]) rest hlen1 b (.ref b) s fo hp
    have hex : _EXPAND_METHOD_KW e ⟨regs, kwv :: (args.reverse ++ .null :: .ref a :: rest)⟩ =
        .ok () ⟨regs, kwv :: (args.reverse ++ s :: .ref b :: rest)⟩ := by
      rw [expKw_eq, kwStack_eq, kwStack_eq]
      exact expandMethod_eq (kwEnv e) regs .null (args ++ [kwv]) rest hlen1 a (.ref b) s ho
    refine ⟨fun nf r hpi => ?_, fun x r hpi => ?_⟩
    · obtain ⟨hr1, _⟩ := pushInit_ok e _ _ _ regs nf r hpi
      have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
      simp only [CALL_KW_BOUND_METHOD, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hmv]; simp only; rw [hex]; simp only
      rw [pyFrameKw_ok e regs _ s kwv args rest kw hlen hkw nf r hpi]
      simp only
      have := pushFrame_entered e nf r rest hnext
      simp only [bind, EStateM.bind] at this
      exact this
    · simp only [CALL_KW_BOUND_METHOD, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hmv]; simp only; rw [hex]; simp only
      rw [pyFrameKw_err e regs _ s kwv args rest kw hlen hkw x r hpi]

/-- `bytecode-call-kw-bound-budget`: the refinement with budget left and the body. -/
def CallKwBoundMethodSpec : Prop := CallKwBoundMethodRefinesWithBudget ∧ CallKwBoundMethodFast

theorem callKwBoundMethodSpec_proven : CallKwBoundMethodSpec :=
  ⟨callKwBoundMethodRefinesWithBudget_proven, callKwBoundMethodFast_proven⟩

/-! ## `CALL_PY_EXACT_ARGS`, `CALL_BOUND_METHOD_EXACT_ARGS` -/

/-- The body of `CALL_PY_EXACT_ARGS` (`:4659-4669`), for every live callable, every runtime and
object model (no `SIMPLE_FUNCTION` hypothesis: this is the body, not the refinement): a non-function
or a stale `func_version` exits with the stack unchanged; for a function with the cached version and
its code object, `_CHECK_FUNCTION_EXACT_ARGS` (`:4596-4602`) exits when `co_argcount` is not `oparg`
plus one for a non-`NULL` `self_or_null`, `_CHECK_STACK_SPACE` (`:4604-4609`) exits when the data
stack has no room, `_CHECK_RECURSION_REMAINING` when `py_recursion_remaining <= 1`; with all four
passing, `_INIT_CALL_PY_EXACT_ARGS` (`:4615-4626`) fills `exactFrame` (`_PyFrame_PushUnchecked`,
`NULL` locals, `self` then the arguments copied into the first locals) and it is entered. -/
def CallPyExactArgsFast : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c → regs.next = e.this + instrSize e.opcode →
  ((∀ a fo, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version ≠ cacheNat e 0) →
    CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
  (∀ a fo co, c = .ref a → regs.rt.heap[a]? = some (.func fo) → fo.version = cacheNat e 0 →
    e.P[fo.code]? = some co →
    (co.argcount ≠ (withSelf self args).length →
      CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
        .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
    (co.argcount = (withSelf self args).length →
      (regs.rt.stackSpace = false →
        CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
          .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
      (regs.rt.stackSpace = true → regs.rt.pyRecursionRemaining ≤ 1 →
        CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
          .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
      (regs.rt.stackSpace = true → 1 < regs.rt.pyRecursionRemaining →
        CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
          .ok () (enteredSt e (exactFrame co fo c (withSelf self args)) regs rest))))

theorem callPyExactArgsFast_proven : CallPyExactArgsFast := by
  intro e regs c self args rest hlen hc hn
  refine ⟨fun hb => ?_, fun a fo co hca ho hv hco => ?_⟩
  · simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [fnVersion_fail e regs c self args rest hlen hc hb]
  · subst hca
    have hfv := fnVersion_pass e regs self args rest hlen a fo ho hv
    refine ⟨fun hx => ?_, fun hx => ⟨fun hsp => ?_, fun hsp hr => ?_, fun hsp hr => ?_⟩⟩
    · simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only
      rw [exactArgs_fail e regs self args rest hlen a fo co ho hco hx]
    · have hea := exactArgs_pass e regs self args rest hlen a fo co ho hco hx
      simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hea]; simp only
      rw [stackSpace_eval]; simp [hsp]
    · have hea := exactArgs_pass e regs self args rest hlen a fo co ho hco hx
      have hss : _CHECK_STACK_SPACE ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
          .ok () ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ := by
        rw [stackSpace_eval]; simp [hsp]
      simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hea]; simp only; rw [hss]; simp only
      rw [recRemaining_fail ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ hr]
    · have hea := exactArgs_pass e regs self args rest hlen a fo co ho hco hx
      have hss : _CHECK_STACK_SPACE ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ =
          .ok () ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ := by
        rw [stackSpace_eval]; simp [hsp]
      have hrs := recRemaining_pass ⟨regs, args.reverse ++ self :: .ref a :: rest⟩ hr
      simp only [CALL_PY_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hfv]; simp only; rw [hea]; simp only; rw [hss]; simp only; rw [hrs]; simp only
      rw [initExact_eq e regs self args rest hlen a fo co ho hco]
      simp only
      have := pushFrame_entered e (exactFrame co fo (.ref a) (withSelf self args)) regs rest hn
      simp only [bind, EStateM.bind] at this
      exact this

/-- `bytecode-call-py-exact-args`: the refinement under the specializer's invariant and the body. -/
def CallPyExactArgsSpec : Prop := CallPyExactArgsRefines ∧ CallPyExactArgsFast

theorem callPyExactArgsSpec_proven : CallPyExactArgsSpec := ⟨callPyExactArgsRefines_proven, callPyExactArgsFast_proven⟩

/-- The body of `CALL_BOUND_METHOD_EXACT_ARGS` (`:4644-4657`): unless the callable is a method object
and `self_or_null` is `NULL`, `_CHECK_CALL_BOUND_METHOD_EXACT_ARGS` (`:4577-4580`) exits with the stack
unchanged; otherwise `_INIT_CALL_BOUND_METHOD_EXACT_ARGS` (`:4582-4590`) splits it, and the rest is the
body of `CALL_PY_EXACT_ARGS` on `im_func`, `im_self` (whose clauses `CallPyExactArgsFast` states). -/
def CallBoundMethodExactArgsFast : Prop := ∀ (e : Env) (regs : Regs) (c self : Val) (args rest : List Val),
  args.length = e.oparg → Live regs.rt c →
  ((¬ ∃ a f s, c = .ref a ∧ regs.rt.heap[a]? = some (.method f s) ∧ self = .null) →
    CALL_BOUND_METHOD_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      .error .deopt ⟨regs, args.reverse ++ self :: c :: rest⟩) ∧
  (∀ a f s, c = .ref a → self = .null → regs.rt.heap[a]? = some (.method f s) →
    CALL_BOUND_METHOD_EXACT_ARGS e ⟨regs, args.reverse ++ self :: c :: rest⟩ =
      CALL_PY_EXACT_ARGS e ⟨regs, args.reverse ++ s :: f :: rest⟩)

theorem callBoundMethodExactArgsFast_proven : CallBoundMethodExactArgsFast := by
  intro e regs c self args rest hlen hc
  refine ⟨fun hp => ?_, fun a f s hca hs ho => ?_⟩
  · simp only [CALL_BOUND_METHOD_EXACT_ARGS, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [boundExact_fail e regs c self args rest hlen hc hp]
  · subst hca hs
    exact boundExact_split e regs args rest hlen a f s ho

/-- `bytecode-call-bound-method-exact-args`: the refinement, the body, and the body of the
`CALL_PY_EXACT_ARGS` it continues as. -/
def CallBoundMethodExactArgsSpec : Prop :=
  CallBoundMethodExactArgsRefines ∧ CallBoundMethodExactArgsFast ∧ CallPyExactArgsFast

theorem callBoundMethodExactArgsSpec_proven : CallBoundMethodExactArgsSpec :=
  ⟨callBoundMethodExactArgsRefines_proven, callBoundMethodExactArgsFast_proven, callPyExactArgsFast_proven⟩

/-! ## `CALL_EX_PY` -/

theorem makeCallargs_notIter (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val)
    (hca : Live regs.rt ca) (hnt : ¬ IsTuple regs.rt ca) (rt0 : Rt) (tn : String) (rt1 : Rt) (y : Err) (rt2 : Rt)
    (hi : e.om.isIterable ca regs.rt = .ok false rt0) (htn : tpName ca rt0 = .ok tn rt1)
    (hy : typeError (α := Unit) s!"Value after * must be an iterable, not {trunc200 tn}" rt1 = .error y rt2) :
    _MAKE_CALLARGS_A_TUPLE e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
      .error y ⟨{ regs with rt := rt2 }, kw :: ca :: n :: f :: rest⟩ := by
  have hn := isExactTuple_not hca hnt
  simp [_MAKE_CALLARGS_A_TUPLE, stkK, peekN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
    MonadLift.monadLift, hn, checkArgsIterable, hi, htn, hy, pure, EStateM.pure]

theorem makeCallargs_tupleErr (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val)
    (hca : Live regs.rt ca) (hnt : ¬ IsTuple regs.rt ca) (rt0 : Rt) (hi : e.om.isIterable ca regs.rt = .ok true rt0)
    (x : Err) (rt1 : Rt) (hx : e.om.call e.ctx (.cls "tuple") [ca] [] rt0 = .error x rt1) :
    _MAKE_CALLARGS_A_TUPLE e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
      .error x ⟨{ regs with rt := rt1 }, kw :: ca :: n :: f :: rest⟩ := by
  have hn := isExactTuple_not hca hnt
  simp [_MAKE_CALLARGS_A_TUPLE, stkK, peekN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
    MonadLift.monadLift, hn, checkArgsIterable, hi, hx, pure, EStateM.pure]

theorem makeCallargs_conv (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val)
    (hca : Live regs.rt ca) (hnt : ¬ IsTuple regs.rt ca) (rt0 : Rt) (hi : e.om.isIterable ca regs.rt = .ok true rt0)
    (t : Val) (rt1 : Rt) (ht : e.om.call e.ctx (.cls "tuple") [ca] [] rt0 = .ok t rt1) :
    _MAKE_CALLARGS_A_TUPLE e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
      .ok () ⟨{ regs with rt := rt1 }, kw :: t :: n :: f :: rest⟩ := by
  have hn := isExactTuple_not hca hnt
  simp [_MAKE_CALLARGS_A_TUPLE, stkK, peekN, popN, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift,
    MonadLift.monadLift, hn, checkArgsIterable, hi, ht, pure, EStateM.pure, pushAll]

/-- An error of `CALL_EX_PY`'s own `_MAKE_CALLARGS_A_TUPLE` that `CALL_FUNCTION_EX` raises the same
way is what dispatch of `CALL_EX_PY` gives too. -/
theorem execCallExPy_prefixErr (e : Env) (s : St) (y : Err) (s' : St)
    (hm : _MAKE_CALLARGS_A_TUPLE e s = .error y s') (hg : CALL_FUNCTION_EX e s = .error y s') :
    execCallExPy e s = CALL_FUNCTION_EX e s := by
  simp only [execCallExPy, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
  rw [hm]
  cases y <;> first | rfl | exact hg.symm

/-- The body of `CALL_EX_PY` (`:5763-5771`: `_CHECK_PEP_523 + _MAKE_CALLARGS_A_TUPLE +
_CHECK_IS_PY_CALLABLE_EX + _PY_FRAME_EX + _SAVE_RETURN_OFFSET + _PUSH_FRAME`) on `(func, NULL,
callargs, kwargs)`, for every live callable and `callargs`, every runtime and object model.
Its own `_MAKE_CALLARGS_A_TUPLE` (`:5620-5635`) comes first: a `callargs` that is not an exact tuple
(`f(*lst)`) and has no `tp_iter` and is not a sequence raises `TypeError("Value after * must be an
iterable, not T")`, and a failing `PySequence_Tuple` raises its error, both keeping every operand,
and dispatch then raises what `CALL_FUNCTION_EX` raises; a successful conversion leaves the
instruction (the body, and dispatch with its restart) exactly as it is on the stack with that tuple,
so `tuple(callargs)` runs once, also when `_CHECK_IS_PY_CALLABLE_EX` then exits. With an exact tuple:
anything but a Python function exits with the stack unchanged (`:5734-5738`); on a function
`_PY_FRAME_EX` (`:5740-5761`) raises `_PyStack_UnpackDict`'s error with the operands gone, and
otherwise the frame `_PyEvalFramePushAndInit_Ex` builds on the tuple's items, then the dict's values,
with its keys as names, is entered whatever `py_recursion_remaining` is (no
`_CHECK_RECURSION_REMAINING`, python/cpython#155151), or its error raised with the operands gone. -/
def CallExPyFast : Prop := ∀ (e : Env) (regs : Regs) (f n ca kw : Val) (rest : List Val),
  Live regs.rt ca → Live regs.rt f → regs.next = e.this + instrSize e.opcode →
  (¬ IsTuple regs.rt ca → ∀ rt0 tn rt1 y rt2, e.om.isIterable ca regs.rt = .ok false rt0 →
    tpName ca rt0 = .ok tn rt1 →
    typeError (α := Unit) s!"Value after * must be an iterable, not {trunc200 tn}" rt1 = .error y rt2 →
    CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
      .error y ⟨{ regs with rt := rt2 }, kw :: ca :: n :: f :: rest⟩ ∧
    execOp e .CALL_EX_PY ⟨regs, kw :: ca :: n :: f :: rest⟩ =
      execOp e .CALL_FUNCTION_EX ⟨regs, kw :: ca :: n :: f :: rest⟩) ∧
  (¬ IsTuple regs.rt ca → ∀ rt0, e.om.isIterable ca regs.rt = .ok true rt0 →
    (∀ x rt1, e.om.call e.ctx (.cls "tuple") [ca] [] rt0 = .error x rt1 →
      CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
        .error x ⟨{ regs with rt := rt1 }, kw :: ca :: n :: f :: rest⟩ ∧
      execOp e .CALL_EX_PY ⟨regs, kw :: ca :: n :: f :: rest⟩ =
        execOp e .CALL_FUNCTION_EX ⟨regs, kw :: ca :: n :: f :: rest⟩) ∧
    (∀ t rt1, e.om.call e.ctx (.cls "tuple") [ca] [] rt0 = .ok t rt1 → IsTuple rt1 t →
      CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ =
        CALL_EX_PY e ⟨{ regs with rt := rt1 }, kw :: t :: n :: f :: rest⟩ ∧
      execOp e .CALL_EX_PY ⟨regs, kw :: ca :: n :: f :: rest⟩ =
        execOp e .CALL_EX_PY ⟨{ regs with rt := rt1 }, kw :: t :: n :: f :: rest⟩)) ∧
  (∀ t items, ca = .ref t → regs.rt.heap[t]? = some (.tuple items) →
    ((¬ ∃ a fo, f = .ref a ∧ regs.rt.heap[a]? = some (.func fo)) →
      CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error .deopt ⟨regs, kw :: ca :: n :: f :: rest⟩) ∧
    (∀ a fo, f = .ref a → regs.rt.heap[a]? = some (.func fo) →
      (∀ x rt, unpackKwargs kw regs.rt = .error x rt →
        CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩) ∧
      (∀ names vals, unpackKwargs kw regs.rt = .ok (names, vals) regs.rt →
        (∀ nf r, pushInit e f (items.toList ++ vals) names regs = .ok nf r →
          CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .ok () (enteredSt e nf r rest)) ∧
        (∀ x r, pushInit e f (items.toList ++ vals) names regs = .error x r →
          CALL_EX_PY e ⟨regs, kw :: ca :: n :: f :: rest⟩ = .error x ⟨r, rest⟩))))

theorem callExPyFast_proven : CallExPyFast := by
  intro e regs f n ca kw rest hca hfl hn
  have hgen := callFunctionExRules_proven e regs f n ca kw rest hca
  refine ⟨fun hnt rt0 tn rt1 y rt2 hi htn hy => ?_, fun hnt rt0 hi => ⟨fun x rt1 hx => ?_, fun t rt1 ht htt => ?_⟩,
    fun t items hct ht => ⟨fun hnf => ?_, fun a fo hfa ho => ⟨fun x rt hu => ?_, fun names vals hu =>
      ⟨fun nf r hpi => ?_, fun x r hpi => ?_⟩⟩⟩⟩
  · have hm := makeCallargs_notIter e regs f n ca kw rest hca hnt rt0 tn rt1 y rt2 hi htn hy
    have hg := hgen.1 hnt rt0 tn rt1 y rt2 hi htn hy
    simp only [execOp] at hg ⊢
    refine ⟨?_, execCallExPy_prefixErr e _ y _ hm hg⟩
    simp only [CALL_EX_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [hm]
  · have hm := makeCallargs_tupleErr e regs f n ca kw rest hca hnt rt0 hi x rt1 hx
    have hg := (hgen.2.1 hnt rt0 hi).1 x rt1 hx
    simp only [execOp] at hg ⊢
    refine ⟨?_, execCallExPy_prefixErr e _ x _ hm hg⟩
    simp only [CALL_EX_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [hm]
  · have hm1 := makeCallargs_conv e regs f n ca kw rest hca hnt rt0 hi t rt1 ht
    have hm2 := makeCallargs_keep e { regs with rt := rt1 } f n t kw rest htt
    refine ⟨?_, ?_⟩
    · simp only [CALL_EX_PY, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hm1, hm2]
    · simp only [execOp, execCallExPy, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
      rw [hm1, hm2]
  · have hmk := makeCallargs_keep e regs f n ca kw rest ⟨t, items, hct, ht⟩
    simp only [CALL_EX_PY, CALL_EX_PY_TAIL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [hmk]; simp only
    rw [isPyCallableEx_fail regs f n ca kw rest hfl hnf]
  · have hmk := makeCallargs_keep e regs f n ca kw rest ⟨t, items, hct, ht⟩
    have hpc := isPyCallableEx_pass regs f n ca kw rest a fo ho hfa
    simp only [CALL_EX_PY, CALL_EX_PY_TAIL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [hmk]; simp only; rw [hpc]; simp only
    rw [pyFrameEx_kwerr e regs f n ca kw rest x rt hu]
  · have hmk := makeCallargs_keep e regs f n ca kw rest ⟨t, items, hct, ht⟩
    have hpc := isPyCallableEx_pass regs f n ca kw rest a fo ho hfa
    obtain ⟨hr1, _⟩ := pushInit_ok e _ _ _ regs nf r hpi
    have hnext : r.next = e.this + instrSize e.opcode := by rw [hr1]; exact hn
    simp only [CALL_EX_PY, CALL_EX_PY_TAIL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [hmk]; simp only; rw [hpc]; simp only
    rw [pyFrameEx_ok e regs f n ca kw rest t items hct ht names vals hu nf r hpi]
    simp only
    have := pushFrame_entered e nf r rest hnext
    simp only [bind, EStateM.bind] at this
    exact this
  · have hmk := makeCallargs_keep e regs f n ca kw rest ⟨t, items, hct, ht⟩
    have hpc := isPyCallableEx_pass regs f n ca kw rest a fo ho hfa
    simp only [CALL_EX_PY, CALL_EX_PY_TAIL, _CHECK_PEP_523, bind, EStateM.bind, pure, EStateM.pure]
    rw [hmk]; simp only; rw [hpc]; simp only
    rw [pyFrameEx_err e regs f n ca kw rest t items hct ht names vals hu x r hpi]

/-- `bytecode-call-ex-py-budget`: the refinement on an exact tuple with budget left, and the body,
whose first clauses reduce every other `callargs` to that case. -/
def CallExPySpec : Prop := CallExPyRefinesWithBudget ∧ CallExPyFast

theorem callExPySpec_proven : CallExPySpec := ⟨callExPyRefinesWithBudget_proven, callExPyFast_proven⟩

end PyLean.Bytecode
