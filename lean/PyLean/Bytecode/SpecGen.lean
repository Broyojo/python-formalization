import PyLean.Bytecode.SpecCallBuiltin

/-!
Generator frames and exception tracebacks in `Python/bytecodes.c`, for every object model:
`RETURN_GENERATOR` (`:5839-5861`), `YIELD_VALUE` (`:1851-1891`), the generic `SEND` (`:1676-1722`),
`RERAISE` (`:1918-1929`) and `WITH_EXCEPT_START` (`:4153-4187`), with `PyTraceBack_Here` at
`label(error)` (`:6460-6482`).
-/

namespace PyLean.Bytecode

open Uop

/-! ## `RETURN_GENERATOR` -/

/-- The frame `_PyFrame_Copy` puts in the generator: `instr_ptr` past `RETURN_GENERATOR`, owned by it. -/
def movedFrame (f : Frame) (a : Addr) (stack : List Val) : Frame :=
  { f with instrPtr := f.instrPtr + 1, owner := FrameOwner.generator a, stack := stack }

/-- `cr_origin` as `RETURN_GENERATOR` leaves it, stated without the machine's loops: `None` unless the
object is a coroutine and `coroutine_origin_tracking_depth` is not 0, else the first `depth` complete
frames of the caller chain (`_PyFrame_IsIncomplete` frames skipped), innermost first, each as the
`(code, lasti)` its `(co_filename, lineno, co_name)` is read from. -/
def expectedOrigin (P : Program) (kind : GenKind) (depth : Nat) (callers : List Frame) :
    Option (List (Nat × Nat)) :=
  if kind = .coro ∧ depth ≠ 0 then
    some (((callers.filter fun f => !frameIncomplete P f).take depth).map fun f => (f.code, f.instrPtr))
  else none

/-- What `_Py_MakeCoro` and `RETURN_GENERATOR` leave in the heap. -/
def madeGen (co : Code) (func : FuncObj) (gf : Frame) (origin : Option (List (Nat × Nat))) : GenObj :=
  { kind := genKindOfFlags co.flags, name := func.name, qualname := func.qualname, frameState := 0, frame := gf,
    origin := origin }

/-- The object `_Py_MakeCoro` allocates, before the frame is copied in. -/
def bareGen (co : Code) (func : FuncObj) (origin : Option (List (Nat × Nat))) : GenObj :=
  { kind := genKindOfFlags co.flags, name := func.name, qualname := func.qualname, origin := origin }

/-- `_Py_MakeCoro`'s choice of type (`Objects/genobject.c:1120-1140`), for every `co_flags`: the
masked flags `co_flags & (CO_GENERATOR | CO_COROUTINE | CO_ASYNC_GENERATOR)` (`0x20 | 0x80 | 0x200`)
equal to `CO_GENERATOR` make a generator, equal to `CO_ASYNC_GENERATOR` an async generator, and every
other value a coroutine, including 0 and two or three flags at once (the asserts are compiled out of
a release build; checked on 3.15.2 with `code.replace(co_flags=...)`). -/
def GenKindRules : Prop :=
  ∀ flags : Nat,
    (genKindOfFlags flags = .gen ↔ flags &&& 0x2a0 = 0x20) ∧
    (genKindOfFlags flags = .asyncGen ↔ flags &&& 0x2a0 = 0x200) ∧
    (genKindOfFlags flags = .coro ↔ flags &&& 0x2a0 ≠ 0x20 ∧ flags &&& 0x2a0 ≠ 0x200)

/-- `RETURN_GENERATOR` (`:5839-5861`) in the frame of a function `func` (`f_funcobj`) whose code is
`co`, called from `caller`: `_Py_MakeCoro` makes a generator, coroutine or async generator by
`co_flags` (`GenKindRules`) with the function's `__name__` and `__qualname__` and, for a coroutine
while `sys.set_coroutine_origin_tracking_depth` is not 0, `cr_origin` from the first `depth` complete
frames of the caller chain (`expectedOrigin`, `Objects/genobject.c:1143-1160`, `:1540-1570`); the
frame is copied into it with `instr_ptr` past this instruction, its stack as it is (3.15 allows up to
two values, `assert(STACK_LEVEL() <= 2)`), `owner = FRAME_OWNED_BY_GENERATOR` and
`gi_frame_state = FRAME_CREATED` (0), with the async generator flags clear; the frame is popped without
being cleared (its references moved), the recursion counter given back, and the caller resumes at its
`return_offset` with the new object on top. The allocation failures of `_Py_MakeCoro` (`ERROR_IF`) and
of `_PyCoro_ComputeOrigin` are not modelled. -/
def ReturnGeneratorRules : Prop :=
  GenKindRules ∧
  ∀ (e : Env) (regs : Regs) (stack : List Val) (fa : Addr) (func : FuncObj) (co : Code) (caller : Frame)
    (prev : List Frame),
    regs.frame.funcobj = .ref fa → regs.rt.heap[fa]? = some (.func func) → e.P[regs.frame.code]? = some co →
    regs.prev = caller :: prev →
    let a := regs.rt.heap.size
    let origin := expectedOrigin e.P (genKindOfFlags co.flags) regs.rt.coroOriginDepth (caller :: prev)
    let g := madeGen co func (movedFrame regs.frame a stack) origin
    execOp e .RETURN_GENERATOR ⟨regs, stack⟩ =
      .ok () ⟨{ rt := { regs.rt with
                  heap := (regs.rt.heap.push (.gen (bareGen co func origin))).setIfInBounds a (.gen g)
                  pyRecursionRemaining := regs.rt.pyRecursionRemaining + 1 }
                frame := caller, prev := prev, next := caller.instrPtr + caller.returnOffset },
              .ref a :: caller.stack⟩

theorem genKindRules_proven : GenKindRules := by
  intro flags
  have hm : genKindOfFlags flags =
      if flags &&& 0x2a0 = 0x20 then .gen else if flags &&& 0x2a0 = 0x200 then .asyncGen else .coro := by
    have h672 : (32 ||| 128 ||| 512 : Nat) = 0x2a0 := by decide
    simp only [genKindOfFlags, coGenerator, coCoroutine, coAsyncGenerator, h672, beq_iff_eq]
  rw [hm]
  by_cases h1 : flags &&& 0x2a0 = 0x20 <;> by_cases h2 : flags &&& 0x2a0 = 0x200 <;> simp_all

theorem crOriginCount_eq (d : Nat) : ∀ (l : List Frame) (n : Nat), n ≤ d →
    crOriginCount d l n = min d (n + l.length)
  | [], n, h => by simp [crOriginCount]; omega
  | _ :: rest, n, h => by
    unfold crOriginCount
    by_cases hn : n < d
    · rw [if_pos hn, crOriginCount_eq d rest (n + 1) hn]; simp; omega
    · rw [if_neg hn]; simp; omega

theorem crOriginCollect_eq (c : Nat) : ∀ (l : List Frame) (i : Nat),
    crOriginCollect c l i = (l.take (c - i)).map fun f => (f.code, f.instrPtr)
  | [], i => by simp [crOriginCollect]
  | f :: rest, i => by
    unfold crOriginCollect
    by_cases hi : i < c
    · rw [if_pos hi, crOriginCollect_eq c rest (i + 1)]
      have : c - i = (c - (i + 1)) + 1 := by omega
      rw [this]; simp
    · rw [if_neg hi]; have : c - i = 0 := by omega
      rw [this]; simp

theorem makeCoroOrigin_eq (P : Program) (kind : GenKind) (d : Nat) (prev : List Frame) :
    makeCoroOrigin P kind d prev = expectedOrigin P kind d prev := by
  cases kind <;> simp [makeCoroOrigin, expectedOrigin]
  by_cases hd : d = 0
  · simp [hd]
  · simp [hd, computeCrOrigin, completeFrames, crOriginCount_eq d _ 0 (Nat.zero_le _), crOriginCollect_eq]

theorem returnGeneratorRules_proven : ReturnGeneratorRules := by
  refine ⟨genKindRules_proven, ?_⟩
  intro e regs stack fa func co caller prev hf hfo hco hp a origin g
  obtain ⟨rt, frame, pv, next⟩ := regs
  simp only at hf hfo hco hp
  subst hp
  simp [execOp, RETURN_GENERATOR, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, getFunc, getObj, hf, hfo, getCode, hco,
    alloc, setObj, leaveRecursivePy, popToPrevious, loadIp, getFrame, pushAll, a, g, madeGen, movedFrame, bareGen,
    origin, makeCoroOrigin_eq]

/-! ## `YIELD_VALUE` -/

/-- `YIELD_VALUE` (`:1889`, `_MAKE_HEAP_SAFE + _YIELD_VALUE`, `:1851-1887`) in the frame of generator
`a`, called from `caller`, with the generator's handled-exception item on top of `exc_info`: the
generator's frame is saved with `instr_ptr` advanced and its stack below the value, `gi_frame_state`
becomes `FRAME_SUSPENDED + oparg`, `tstate->exc_info` goes back to the previous item with the
generator's `exc_value` kept in the generator, the recursion counter is given back, and the caller
resumes after the `SEND` or `FOR_ITER` with its cache (`LOAD_IP(1 + INLINE_CACHE_ENTRIES_SEND)`) with
the value on top. Nothing raises: the compiler counts on that (`:1852-1854`). -/
def YieldSuspends : Prop :=
  ∀ (e : Env) (regs : Regs) (v : Val) (rest : List Val) (a : Addr) (g : GenObj) (ev : Val)
    (chain : List Val) (caller : Frame) (prev : List Frame),
    regs.frame.owner = .generator a → regs.rt.heap[a]? = some (.gen g) →
    regs.rt.excInfo = ev :: chain → regs.prev = caller :: prev →
    execOp e .YIELD_VALUE ⟨regs, v :: rest⟩ =
      .ok () ⟨{ rt := { regs.rt with
                  heap := regs.rt.heap.setIfInBounds a (.gen { g with
                    frameState := 1 + (e.oparg : Int), excValue := ev,
                    frame := { regs.frame with instrPtr := regs.frame.instrPtr + 1, stack := rest } })
                  excInfo := chain
                  pyRecursionRemaining := regs.rt.pyRecursionRemaining + 1 }
                frame := caller, prev := prev, next := caller.instrPtr + 2 },
              v :: caller.stack⟩

theorem yieldSuspends_proven : YieldSuspends := by
  intro e regs v rest a g ev chain caller prev ho hg hx hp
  obtain ⟨rt, frame, pv, next⟩ := regs
  simp only at ho hg hx hp
  subst hp
  simp [execOp, YIELD_VALUE, bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift,
    pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, frameGen, getFrame, ho, getGen, getObj, hg,
    popExcState, hx, setObj, leaveRecursivePy, popToPrevious, loadIp, pushAll, popN]

/-! ## `label(error)` and `WITH_EXCEPT_START` -/

/-- The error label (`label(error)`, `:6460-6482`), which every raising instruction but `RERAISE`
reaches, first adds the frame's traceback entry (`PyTraceBack_Here`) and then unwinds; `RERAISE` goes to
`exception_unwind` directly (`Err.unwind`, `ReraiseRules`), so a re-raised exception keeps its traceback
and a raised one gets one more entry. `PyTraceBack_Here` on an exception instance: a complete frame gets a
new traceback object, `tb_next` the old traceback, the frame's code and `instr_ptr`, as the exception's
`__traceback__`; an incomplete frame (`instr_ptr` before `_co_firsttraceable`, not a generator's) gets
none. -/
def TracebackRules : Prop :=
  (∀ (P : Program) (v : Val) (s : St),
    afterInstr P (.error (.unwind v) s) = unwind P (s.regs.prev.length + 2) v s ∧
    afterInstr P (.error (.exc v) s) =
      unwind P (s.regs.prev.length + 2) v { s with regs := { s.regs with rt := tracebackHere P s.regs.frame v s.regs.rt } }) ∧
  (∀ (P : Program) (f : Frame) (rt : Rt) (a : Addr) (i : InstObj) (d : ExcData), rt.heap[a]? = some (.inst i) →
    i.exc = some d →
    (frameIncomplete P f = false → tracebackHere P f (.ref a) rt =
      { rt with
        heap := (rt.heap.push (.traceback d.traceback f.code f.instrPtr)).setIfInBounds a
                  (.inst { i with exc := some { d with traceback := .ref rt.heap.size } }) }) ∧
    (frameIncomplete P f = true → tracebackHere P f (.ref a) rt = rt))

theorem tracebackRules_proven : TracebackRules := by
  refine ⟨fun P v s => ⟨rfl, rfl⟩, fun P f rt a i d hi hd => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · simp [tracebackHere, hc, hi, hd]
  · simp [tracebackHere, hc]

/-- `WITH_EXCEPT_START` (`:4153-4187`) on `(exit_func, exit_self, lasti, prev_exc, val)` with `val` an
exception instance: `exit_func` is called with `exit_self` first when it is not `NULL`, then
`type(val)`, `val`, and `val.__traceback__` (`PyException_GetTraceback`, `None` for `NULL`); the
result goes on top of the five, which stay, and an error leaves the stack as it was (no input is
consumed, `ERROR_IF`). -/
def WithExceptStartRules : Prop :=
  ∀ (e : Env) (regs : Regs) (ef es la pe : Val) (rest : List Val) (a : Addr) (i : InstObj) (d : ExcData),
    regs.rt.heap[a]? = some (.inst i) → i.exc = some d →
    let S := Val.ref a :: pe :: la :: es :: ef :: rest
    let tb := if d.traceback = .null then Val.none else d.traceback
    let args := if es = .null then [i.cls, .ref a, tb] else [es, i.cls, .ref a, tb]
    (∀ r rt, e.om.call e.ctx ef args [] regs.rt = .ok r rt →
      execOp e .WITH_EXCEPT_START ⟨regs, S⟩ = .ok () ⟨{ regs with rt := rt }, r :: S⟩) ∧
    (∀ x rt, e.om.call e.ctx ef args [] regs.rt = .error x rt →
      execOp e .WITH_EXCEPT_START ⟨regs, S⟩ = .error x ⟨{ regs with rt := rt }, S⟩)

theorem withExceptStartRules_proven : WithExceptStartRules := by
  intro e regs ef es la pe rest a i d hi hd S tb args
  have ht : typeOf (.ref a) regs.rt = .ok i.cls regs.rt := by
    simp [typeOf, getObj, hi, bind, EStateM.bind, pure, EStateM.pure]
  have hx : excData (.ref a) regs.rt = .ok d regs.rt := by
    cases i with
    | mk cls dict slots base exc =>
      simp only at hd; subst hd
      simp [excData, getObj, hi, bind, EStateM.bind, pure, EStateM.pure]
  refine ⟨fun r rt h => ?_, fun x rt h => ?_⟩
  · simp only [args, tb] at h
    bc_simp [execOp, WITH_EXCEPT_START, S, ht, hx, h]
  · simp only [args, tb] at h
    bc_simp [execOp, WITH_EXCEPT_START, S, ht, hx, h]

/-! ## `SEND` -/

/-- The generic `SEND` (`:1722`, `_SPECIALIZE_SEND + _SEND`, `:1676-1720`) on
`(receiver, null_or_index, v)`, for every object model. An exact generator or coroutine that is not
running (`gen_try_set_executing`) gets `v` pushed on its frame, is marked `FRAME_EXECUTING`, its
handled-exception item goes on top of `exc_info`, `return_offset` is `INSTRUCTION_SIZE + oparg`, and
its frame runs inline (`DISPATCH_INLINED`) with the receiver and `null_or_index` left. Otherwise, with
an index and `v` `None` (a virtual iterator, `_PyForIter_VirtualIteratorNext`), the next item replaces
`v` and the index is updated, the end jumps by `oparg` with the stack as it was, and an error keeps the
stack (`ERROR_NO_POP`); else `_PyIter_Send(receiver, v)`: its value replaces `v`, `PYGEN_RETURN` also
jumps by `oparg`, and an error keeps the stack. -/
def SendRules : Prop := ∀ (e : Env) (regs : Regs) (r n v : Val) (rest : List Val),
  (∀ a g, r = .ref a → regs.rt.heap[a]? = some (.gen g) → (g.kind = .gen ∨ g.kind = .coro) → g.frameState < 4 →
    execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ = (dispatchInlined { g.frame with stack := v :: g.frame.stack } : M Unit)
      ⟨{ regs with
          rt := { regs.rt with
                  heap := regs.rt.heap.setIfInBounds a
                            (.gen { g with frameState := 4, frame := { g.frame with stack := v :: g.frame.stack } })
                  excInfo := g.excValue :: regs.rt.excInfo }
          frame := { regs.frame with returnOffset := instrSize e.opcode + e.oparg } }, n :: r :: rest⟩) ∧
  (resumableGen true r regs.rt = .ok none regs.rt → n ≠ .null → v = .none →
    (∀ rt, virtualNext e r n regs.rt = .ok none rt →
      execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ =
        .error .dispatch ⟨{ regs with rt := rt, next := (regs.next + e.oparg : Int).toNat }, v :: n :: r :: rest⟩) ∧
    (∀ item idx rt, virtualNext e r n regs.rt = .ok (some (item, idx)) rt →
      execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ = .ok () ⟨{ regs with rt := rt }, item :: idx :: r :: rest⟩) ∧
    (∀ x rt, virtualNext e r n regs.rt = .error (.exc x) rt →
      execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ = .error (.exc x) ⟨{ regs with rt := rt }, v :: n :: r :: rest⟩)) ∧
  (resumableGen true r regs.rt = .ok none regs.rt → (n = .null ∨ v ≠ .none) →
    (∀ x rt, iterSend e r v regs.rt = .ok (x, false) rt →
      execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ = .ok () ⟨{ regs with rt := rt }, x :: n :: r :: rest⟩) ∧
    (∀ x rt, iterSend e r v regs.rt = .ok (x, true) rt →
      execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ =
        .ok () ⟨{ regs with rt := rt, next := (regs.next + e.oparg : Int).toNat }, x :: n :: r :: rest⟩) ∧
    (∀ x rt, iterSend e r v regs.rt = .error (.exc x) rt →
      execOp e .SEND ⟨regs, v :: n :: r :: rest⟩ = .error (.exc x) ⟨{ regs with rt := rt }, v :: n :: r :: rest⟩))

theorem sendRules_proven : SendRules := by
  intro e regs r n v rest
  refine ⟨fun a g hr hg hk hs => ?_, fun hn hnn hv => ⟨fun rt h => ?_, fun item idx rt h => ?_, fun x rt h => ?_⟩,
    fun hn hnv => ⟨fun x rt h => ?_, fun x rt h => ?_, fun x rt h => ?_⟩⟩
  · subst hr
    have hres : resumableGen true (.ref a) regs.rt = .ok (some (a, g)) regs.rt := by
      have hs' : decide (g.frameState < 4) = true := by simpa using hs
      rcases hk with hk | hk <;> simp [resumableGen, getObj, hg, hk, hs', bind, EStateM.bind, pure, EStateM.pure]
    simp only [execOp, SEND, _SPECIALIZE_SEND, _SEND, bind, EStateM.bind, pure, EStateM.pure, peekN]
    simp [BM.lift, RM.lift, hres, popN, genEnter, setObj, pushExcState, setReturnOffset, modifyFrame, bind,
      EStateM.bind, pure, EStateM.pure, liftM, monadLift, MonadLift.monadLift]
  · subst hv
    have hb : (n != .null) = true := by simpa using hnn
    bc_simp [execOp, SEND, _SPECIALIZE_SEND, _SEND, hn, hb, h, jumpBy]
  · subst hv
    have hb : (n != .null) = true := by simpa using hnn
    bc_simp [execOp, SEND, _SPECIALIZE_SEND, _SEND, hn, hb, h]
  · subst hv
    have hb : (n != .null) = true := by simpa using hnn
    bc_simp [execOp, SEND, _SPECIALIZE_SEND, _SEND, hn, hb, h]
  · have hb : (n != .null && v == .none) = false := by rcases hnv with h | h <;> simp [h]
    bc_simp [execOp, SEND, _SPECIALIZE_SEND, _SEND, hn, hb, h]
  · have hb : (n != .null && v == .none) = false := by rcases hnv with h | h <;> simp [h]
    bc_simp [execOp, SEND, _SPECIALIZE_SEND, _SEND, hn, hb, h, jumpBy]
  · have hb : (n != .null && v == .none) = false := by rcases hnv with h | h <;> simp [h]
    bc_simp [execOp, SEND, _SPECIALIZE_SEND, _SEND, hn, hb, h]

/-- `PyIter_Send` (`Objects/abstract.c:2930-2953`), as `_SEND` uses it through `iterSend`, for every
object model: a type with `am_send` answers through it; otherwise `None` to an iterator is
`tp_iternext` and anything else `receiver.send(v)` (`PyObject_CallMethodOneArg`); a value is
`PYGEN_NEXT`, a `NULL` with nothing set or a `StopIteration` (a subclass included) is `PYGEN_RETURN`
with its value (`_PyGen_FetchStopIterationValue`), and any other exception, the lookup's included, is
`PYGEN_ERROR`. -/
def IterSendRules : Prop := ∀ (e : Env) (r v : Val) (rt rt1 : Rt),
  (e.om.hasAmSend r rt = .ok true rt1 → iterSend e r v rt = e.om.amSend e.ctx r v rt1) ∧
  (e.om.hasAmSend r rt = .ok false rt1 → ∀ b rt2, e.om.isIterator r rt1 = .ok b rt2 →
    let finish (m : RM (Option Val)) : RM (Val × Bool) :=
      tryExc (do match ← m with | some x => pure (x, false) | none => pure (.none, true))
        fun exc => do pure (← fetchStopIterationValue exc, true)
    (v = .none → b = true → iterSend e r v rt = finish (e.om.iterNext e.ctx r) rt2) ∧
    ((v ≠ .none ∨ b = false) → iterSend e r v rt = finish (do
        let (m, slf) ← e.om.getMethod e.ctx r "send"
        some <$> e.om.call e.ctx m (if slf = .null then [v] else [slf, v]) []) rt2)) ∧
  (∀ x rt2, givenMatches x 8 (.cls "StopIteration") rt = .ok true rt2 →
    fetchStopIterationValue x rt = (do return (← excData x).value : RM Val) rt2) ∧
  (∀ x rt2, givenMatches x 8 (.cls "StopIteration") rt = .ok false rt2 →
    fetchStopIterationValue x rt = .error (.exc x) rt2)

theorem iterSendRules_proven : IterSendRules := by
  intro e r v rt rt1
  refine ⟨fun h => ?_, fun h b rt2 hb => ?_, fun x rt2 h => ?_, fun x rt2 h => ?_⟩
  · simp [iterSend, h, bind, EStateM.bind]
  · intro finish
    refine ⟨fun hv ht => ?_, fun hvb => ?_⟩
    · subst hv ht
      simp [iterSend, h, hb, bind, EStateM.bind, finish]
      rfl
    · have hc : (v == .none && b) = false := by rcases hvb with h | h <;> simp [h]
      simp [iterSend, h, hb, hc, bind, EStateM.bind, finish]
      rfl
  · simp [fetchStopIterationValue, h, bind, EStateM.bind]
  · simp [fetchStopIterationValue, h, bind, EStateM.bind, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw]

/-! ## `END_ASYNC_FOR` -/

/-- `END_ASYNC_FOR` (`:1958`, `_END_ASYNC_FOR`, `:1931-1947`) on `(awaitable, exc)`, for every object
model: when `PyErr_GivenExceptionMatches(exc, StopAsyncIteration)` (a subclass included) both are
dropped and the loop ends; otherwise `exc` is re-raised through `exception_unwind` (no traceback entry),
the two dropped by the unwinding (the model drops them first, as for `CLEANUP_THROW`). -/
def EndAsyncForRules : Prop := ∀ (e : Env) (regs : Regs) (aw exc : Val) (rest : List Val) (rt : Rt),
  (givenMatches exc 8 (.cls "StopAsyncIteration") regs.rt = .ok true rt →
    execOp e .END_ASYNC_FOR ⟨regs, exc :: aw :: rest⟩ = .ok () ⟨{ regs with rt := rt }, rest⟩) ∧
  (givenMatches exc 8 (.cls "StopAsyncIteration") regs.rt = .ok false rt →
    execOp e .END_ASYNC_FOR ⟨regs, exc :: aw :: rest⟩ = .error (.unwind exc) ⟨{ regs with rt := rt }, rest⟩)

theorem endAsyncForRules_proven : EndAsyncForRules := by
  intro e regs aw exc rest rt
  refine ⟨fun h => ?_, fun h => ?_⟩
  · bc_simp [execOp, END_ASYNC_FOR, _END_ASYNC_FOR, h]
  · bc_simp [execOp, END_ASYNC_FOR, _END_ASYNC_FOR, h]

def GenFrameRules : Prop := ReturnGeneratorRules ∧ YieldSuspends ∧ TracebackRules ∧ WithExceptStartRules

end PyLean.Bytecode
