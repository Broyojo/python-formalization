import PyLean.Bytecode.SpecCallPyFast

/-!
The exception-handling instructions of `Python/bytecodes.c`: `CHECK_EXC_MATCH` (`:3441-3453`),
`CHECK_EG_MATCH` (`:3415-3439`) with `_PyEval_ExceptionGroupMatch` (`Python/ceval.c:2263-2348`) and
the `except` type checks (`Python/ceval.c:3340-3400`), `RERAISE` (`:1918-1929`) and
`CLEANUP_THROW` (`:1960-1978`).
-/

namespace PyLean.Bytecode

open Uop

/-! ## `CHECK_EXC_MATCH` -/

/-- `CHECK_EXC_MATCH` (`:3441-3453`) on `(left, right)`, for every object model: when
`_PyEval_CheckExceptTypeValid(right)` fails it raises that error and keeps both operands
(`ERROR_NO_POP`); otherwise it replaces `right` by the bool of `PyErr_GivenExceptionMatches(left,
right)` and keeps `left`. The check comes first: a `right` that is not a class is refused even when
it would not have been compared. -/
def CheckExcMatchRules : Prop := ∀ (e : Env) (regs : Regs) (l r : Val) (rest : List Val),
  (∀ x rt, checkExceptTypeValid r regs.rt = .error x rt →
    execOp e .CHECK_EXC_MATCH ⟨regs, r :: l :: rest⟩ = .error x ⟨{ regs with rt := rt }, r :: l :: rest⟩) ∧
  (∀ rt b rt', checkExceptTypeValid r regs.rt = .ok () rt → givenMatches l 8 r rt = .ok b rt' →
    execOp e .CHECK_EXC_MATCH ⟨regs, r :: l :: rest⟩ = .ok () ⟨{ regs with rt := rt' }, .bool b :: l :: rest⟩)

theorem checkExcMatchRules_proven : CheckExcMatchRules := by
  intro e regs l r rest
  refine ⟨fun x rt h => ?_, fun rt b rt' h1 h2 => ?_⟩
  · bc_simp [execOp, CHECK_EXC_MATCH, h]
  · bc_simp [execOp, CHECK_EXC_MATCH, h1, h2]

/-- `PyTuple_Check` in `_PyEval_CheckExceptTypeValid` (`Python/ceval.c:3343`),
and `PyErr_GivenExceptionMatches` (`Python/errors.c:338`): an instance of a `tuple` subclass is
checked and matched item by item,
exactly as the exact tuple of its items is, so `except T((KeyError, ValueError))` with
`class T(tuple)` catches a `ValueError`, and `except T((KeyError, 1))` is refused. -/
def ExceptTupleSubclassRules : Prop := ∀ (rt : Rt) (a t : Addr) (i : InstObj) (items : Array Val),
  rt.heap[a]? = some (.inst i) → i.base = .ref t → rt.heap[t]? = some (.tuple items) →
  checkExceptTypeValid (.ref a) rt = checkExceptTypeValid (.ref t) rt ∧
  ∀ err n, givenMatches err n (.ref a) rt = givenMatches err n (.ref t) rt

theorem tupleCheckItems_sub (rt : Rt) (a t : Addr) (i : InstObj) (items : Array Val)
    (ha : rt.heap[a]? = some (.inst i)) (hb : i.base = .ref t) (ht : rt.heap[t]? = some (.tuple items)) :
    tupleCheckItems? (.ref a) rt = .ok (some items) rt ∧ tupleCheckItems? (.ref t) rt = .ok (some items) rt := by
  constructor <;> simp [tupleCheckItems?, getObj, ha, hb, ht, bind, EStateM.bind, pure, EStateM.pure]

theorem exceptTupleSubclassRules_proven : ExceptTupleSubclassRules := by
  intro rt a t i items ha hb ht
  obtain ⟨h1, h2⟩ := tupleCheckItems_sub rt a t i items ha hb ht
  refine ⟨?_, fun err n => ?_⟩
  · simp only [checkExceptTypeValid, bind, EStateM.bind]
    rw [h1, h2]
  · cases n with
    | zero => rfl
    | succ n =>
      simp only [givenMatches, bind, EStateM.bind]
      rw [h1, h2]

/-- `bytecode-check-exc-match`. -/
def CheckExcMatchSpec : Prop := CheckExcMatchRules ∧ ExceptTupleSubclassRules

theorem checkExcMatchSpec_proven : CheckExcMatchSpec := ⟨checkExcMatchRules_proven, exceptTupleSubclassRules_proven⟩

/-! ## `CHECK_EG_MATCH` -/

/-- `_PyErr_SetHandledException(tstate, m)` for `m` not `None` (`Python/errors.c:619-622`):
`tstate->exc_info->exc_value = m`. -/
def withHandled (m : Val) (rt : Rt) : Rt :=
  match rt.excInfo with
  | _ :: rest => { rt with excInfo := m :: rest }
  | [] => { rt with excInfo := [m] }

theorem setExcInfoTop_eq (m : Val) (rt : Rt) : setExcInfoTop m rt = .ok () (withHandled m rt) := by
  cases h : rt.excInfo <;> simp [setExcInfoTop, withHandled, h]

/-- `CHECK_EG_MATCH` (`:3415-3439`) on `(exc_value, match_type)`, for every object model: a
`match_type` that `_PyEval_CheckExceptStarTypeValid` refuses raises with both operands popped
(`DECREF_INPUTS` then `ERROR_IF`); otherwise `_PyEval_ExceptionGroupMatch` runs, and its error is
raised with both popped; its `(match, rest)` replaces the operands, `match` on top, and when `match`
is not `None` it becomes the handled exception (`PyErr_SetHandledException`, `:3434-3436`), whatever
object it is. -/
def CheckEgMatchRules : Prop := ∀ (e : Env) (regs : Regs) (ev mt : Val) (rest : List Val),
  (∀ x rt, checkExceptStarTypeValid mt regs.rt = .error x rt →
    execOp e .CHECK_EG_MATCH ⟨regs, mt :: ev :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩) ∧
  (∀ rt, checkExceptStarTypeValid mt regs.rt = .ok () rt →
    (∀ x rt', exceptionGroupMatch e.om e.ctx ev mt rt = .error x rt' →
      execOp e .CHECK_EG_MATCH ⟨regs, mt :: ev :: rest⟩ = .error x ⟨{ regs with rt := rt' }, rest⟩) ∧
    (∀ m r rt', exceptionGroupMatch e.om e.ctx ev mt rt = .ok (m, r) rt' →
      execOp e .CHECK_EG_MATCH ⟨regs, mt :: ev :: rest⟩ =
        .ok () ⟨{ regs with rt := if m = .none then rt' else withHandled m rt' }, m :: r :: rest⟩))

theorem checkEgMatchRules_proven : CheckEgMatchRules := by
  intro e regs ev mt rest
  refine ⟨fun x rt h => ?_, fun rt h => ⟨fun x rt' h2 => ?_, fun m r rt' h2 => ?_⟩⟩
  · bc_simp [execOp, CHECK_EG_MATCH, h]
  · bc_simp [execOp, CHECK_EG_MATCH, h, h2]
  · by_cases hm : m = .none
    · subst hm
      bc_simp [execOp, CHECK_EG_MATCH, h, h2]
    · bc_simp [execOp, CHECK_EG_MATCH, h, h2, hm, setExcInfoTop_eq]

/-- `_PyEval_ExceptionGroupMatch` (`Python/ceval.c:2263-2348`), for every object model: `None` gives
`(None, None)` with nothing run; a value that `PyErr_GivenExceptionMatches` matches is the match
itself when it is a group (`_PyBaseExceptionGroup_Check`) and otherwise the group
`_PyExc_CreateExceptionGroup` wraps it in (`egWrap`), with `rest` `None`; a group that does not match
`match_type` gets its `split` attribute called with `match_type` (`PyObject_CallMethod`, which runs
whatever a subclass defines), and the result must be an exact tuple, else `TypeError("T.split must
return a tuple, not U")`, of at least two items, else `TypeError("T.split must return a 2-tuple, got
tuple of size n")`, the first two items being `(match, rest)` as they are, with no check of what they
are; the attribute's or the call's error is raised as it is; a value that matches nothing and is not
a group gives `(None, exc_value)`. -/
def ExceptionGroupMatchRules : Prop := ∀ (om : ObjModel) (ctx : Ctx) (ev mt : Val) (rt : Rt),
  exceptionGroupMatch om ctx .none mt rt = .ok (.none, .none) rt ∧
  (ev ≠ .none → ∀ rt1 T rt2, givenMatches ev 8 mt rt = .ok true rt1 → typeOf ev rt1 = .ok T rt2 →
    (∀ rt3, isSubtype T (.cls "BaseExceptionGroup") rt2 = .ok true rt3 →
      exceptionGroupMatch om ctx ev mt rt = .ok (ev, .none) rt3) ∧
    (∀ rt3, isSubtype T (.cls "BaseExceptionGroup") rt2 = .ok false rt3 → ∀ w rt4, om.egWrap ctx ev rt3 = .ok w rt4 →
      exceptionGroupMatch om ctx ev mt rt = .ok (w, .none) rt4)) ∧
  (ev ≠ .none → ∀ rt1 T rt2, givenMatches ev 8 mt rt = .ok false rt1 → typeOf ev rt1 = .ok T rt2 →
    (∀ rt3, isSubtype T (.cls "BaseExceptionGroup") rt2 = .ok false rt3 →
      exceptionGroupMatch om ctx ev mt rt = .ok (.none, ev) rt3) ∧
    (∀ rt3, isSubtype T (.cls "BaseExceptionGroup") rt2 = .ok true rt3 →
      (∀ x rt4, om.getAttr ctx ev "split" rt3 = .error x rt4 →
        exceptionGroupMatch om ctx ev mt rt = .error x rt4) ∧
      ∀ f rt4, om.getAttr ctx ev "split" rt3 = .ok f rt4 →
        (∀ x rt5, om.call ctx f [mt] [] rt4 = .error x rt5 → exceptionGroupMatch om ctx ev mt rt = .error x rt5) ∧
        ∀ pair rt5, om.call ctx f [mt] [] rt4 = .ok pair rt5 →
          (∀ items, exactTupleItems? pair rt5 = .ok (some items) rt5 →
            (∀ m r tl, items.toList = m :: r :: tl → exceptionGroupMatch om ctx ev mt rt = .ok (m, r) rt5) ∧
            (items.size < 2 → ∀ n1 rt6, tpName ev rt5 = .ok n1 rt6 →
              exceptionGroupMatch om ctx ev mt rt =
                typeError s!"{trunc200 n1}.split must return a 2-tuple, got tuple of size {items.size}" rt6)) ∧
          (exactTupleItems? pair rt5 = .ok none rt5 → ∀ n1 rt6 n2 rt7, tpName ev rt5 = .ok n1 rt6 →
            tpName pair rt6 = .ok n2 rt7 →
            exceptionGroupMatch om ctx ev mt rt =
              typeError s!"{trunc200 n1}.split must return a tuple, not {trunc200 n2}" rt7)))

theorem exceptionGroupMatchRules_proven : ExceptionGroupMatchRules := by
  intro om ctx ev mt rt
  refine ⟨by simp [exceptionGroupMatch, pure, EStateM.pure], fun hne rt1 T rt2 hg ht => ?_,
    fun hne rt1 T rt2 hg ht => ?_⟩
  · have hne' : (ev == Val.none) = false := by simpa using hne
    refine ⟨fun rt3 hs => ?_, fun rt3 hs w rt4 hw => ?_⟩
    · simp [exceptionGroupMatch, hne', hg, ht, hs, bind, EStateM.bind, pure, EStateM.pure]
    · simp [exceptionGroupMatch, hne', hg, ht, hs, hw, bind, EStateM.bind, pure, EStateM.pure]
  have hne' : (ev == Val.none) = false := by simpa using hne
  refine ⟨fun rt3 hs => ?_, fun rt3 hs => ⟨fun x rt4 ha => ?_, fun f rt4 ha => ⟨fun x rt5 hc => ?_,
    fun pair rt5 hc => ⟨fun items hi => ⟨fun m r tl hl => ?_, fun hsz n1 rt6 hn => ?_⟩,
      fun hi n1 rt6 n2 rt7 hn1 hn2 => ?_⟩⟩⟩⟩
  · simp [exceptionGroupMatch, hne', hg, ht, hs, bind, EStateM.bind, pure, EStateM.pure]
  · simp [exceptionGroupMatch, hne', hg, ht, hs, ha, bind, EStateM.bind, pure, EStateM.pure]
  · simp [exceptionGroupMatch, hne', hg, ht, hs, ha, hc, bind, EStateM.bind, pure, EStateM.pure]
  · simp [exceptionGroupMatch, hne', hg, ht, hs, ha, hc, hi, hl, bind, EStateM.bind, pure, EStateM.pure]
  · have h01 : items.toList = [] ∨ ∃ x, items.toList = [x] := by
      rcases h : items.toList with _ | ⟨x, _ | ⟨y, tl⟩⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨x, rfl⟩
      · have := congrArg List.length h
        simp at this
        omega
    rcases h01 with h0 | ⟨x, h0⟩ <;>
      simp [exceptionGroupMatch, hne', hg, ht, hs, ha, hc, hi, h0, hn, bind, EStateM.bind, pure, EStateM.pure]
  · simp [exceptionGroupMatch, hne', hg, ht, hs, ha, hc, hi, hn1, hn2, bind, EStateM.bind, pure, EStateM.pure]

/-- `bytecode-check-eg-match`. -/
def CheckEgMatchSpec : Prop := CheckEgMatchRules ∧ ExceptionGroupMatchRules

theorem checkEgMatchSpec_proven : CheckEgMatchSpec := ⟨checkEgMatchRules_proven, exceptionGroupMatchRules_proven⟩

/-- The handled exception is `NULL` or an exception instance. -/
def handledOk (rt : Rt) : Bool :=
  match rt.excInfo with
  | v :: _ => v == .null || (match isExcInstance v rt with | .ok b _ => b | .error _ _ => false)
  | [] => true

/-- Whether `CHECK_EG_MATCH` from `s` leaves the handled exception an exception instance (a raising
instruction is not asked). -/
def egMatchKeepsHandled (e : Env) (s : St) : Bool :=
  match execOp e .CHECK_EG_MATCH s with
  | .ok _ s' => handledOk s'.regs.rt
  | .error _ _ => true

/-- `CHECK_EG_MATCH` keeps `tstate->exc_info->exc_value` an exception instance (or `NULL`), the
invariant `sys.exception()` documents ("the exception instance that is currently being handled")
and the C code relies on: `_PyErr_SetObject` reads it as a `PyBaseExceptionObject` to chain
`__context__` (`PyException_GetContext`, `Objects/exceptions.c`). False: the `match` it installs is
the first item of whatever tuple the group's `split` returned, and nothing checks it is an exception,
so `split` returning `(1, None)` makes `1` the handled exception. -/
def EgMatchHandledIsException : Prop := ∀ (e : Env) (s : St),
  handledOk s.regs.rt = true → egMatchKeepsHandled e s = true

/-- `class EG(ExceptionGroup)` at 0 whose `split` returns `(1, None)`, an `EG` instance at 2 being
handled by `except* TypeError`. -/
def egSplitSt : St :=
  { regs := { rt := { heap := #[.cls { name := "EG", mro := [.ref 0, .cls "ExceptionGroup", .cls "BaseExceptionGroup",
                                        .cls "Exception", .cls "BaseException", .cls "object"] },
                               .tuple #[],
                               .inst { cls := .ref 0, exc := some { args := .ref 1 } }] },
              frame := { code := 0 } },
    stack := [.cls "TypeError", .ref 2] }

def egSplitEnv : Env :=
  { P := #[{}, {}], om := { Proto.mkOM #[] 0 with
      getAttr := fun _ _ _ => pure (.builtin "split"),
      call := fun _ _ _ _ => mkTuple [.int 1, .none] },
    ctx := ⟨fun _ _ => throw .fuel⟩, opcode := .CHECK_EG_MATCH, oparg := 0, this := 0, cache := [] }

theorem egMatchHandledIsException_refuted : ¬EgMatchHandledIsException := by
  intro h
  exact absurd (h egSplitEnv egSplitSt (by decide)) (by decide)

/-! ## `RERAISE`, `CLEANUP_THROW` -/

/-- `RERAISE` (`:1918-1929`) on `(values[oparg], exc)`: it re-raises `exc` through
`exception_unwind` (`Err.unwind`, so no traceback entry is added for this instruction), with the
`oparg` values left in place; with `oparg != 0`, `frame->instr_ptr` is first set to the offset
tagged in `values[0]` (`lasti`), so the handler search and the line number use the instruction that
originally raised. -/
def ReraiseRules : Prop := ∀ (e : Env) (regs : Regs) (exc : Val) (vals rest : List Val),
  vals.length = e.oparg →
  (e.oparg = 0 → execOp e .RERAISE ⟨regs, exc :: (vals.reverse ++ rest)⟩ =
    .error (.unwind exc) ⟨regs, vals.reverse ++ rest⟩) ∧
  (∀ n tl, vals = .tagged n :: tl → execOp e .RERAISE ⟨regs, exc :: (vals.reverse ++ rest)⟩ =
    .error (.unwind exc) ⟨{ regs with frame := { regs.frame with instrPtr := n } }, vals.reverse ++ rest⟩)

theorem peekN_rev (regs : Regs) (vals rest : List Val) :
    peekN vals.length ⟨regs, vals.reverse ++ rest⟩ = .ok vals ⟨regs, vals.reverse ++ rest⟩ := by
  simp [peekN]

theorem reraiseRules_proven : ReraiseRules := by
  intro e regs exc vals rest hlen
  have hpop : popN 1 ⟨regs, exc :: (vals.reverse ++ rest)⟩ = .ok [exc] ⟨regs, vals.reverse ++ rest⟩ := by
    simp [popN]
  refine ⟨fun h0 => ?_, fun n tl hv => ?_⟩
  · simp only [execOp, RERAISE, bind, EStateM.bind]
    rw [hpop]
    simp [h0, pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
  · have hne : e.oparg ≠ 0 := by rw [← hlen, hv]; simp
    have hpk := peekN_rev regs vals rest
    rw [hlen] at hpk
    subst hv
    generalize (Val.tagged n :: tl).reverse ++ rest = S at hpop hpk ⊢
    simp only [execOp, RERAISE, bind, EStateM.bind]
    rw [hpop]
    simp [hne, hpk, EStateM.bind, BM.lift, modifyFrame, pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw]

/-- `CLEANUP_THROW` (`:1960-1978`) on `(sub_iter, null_in, last_sent_val, exc_value)`: when
`exc_value` matches `StopIteration` (`PyErr_GivenExceptionMatches`, so a subclass too) the four are
replaced by `(None, null_in, exc_value.value)`, the value the delegated-to iterator returned;
otherwise `exc_value` is re-raised through `exception_unwind` (`goto exception_unwind` leaves the
operands, and unwinding to the handler's depth, below them, pops them; the model pops them first). -/
def CleanupThrowRules : Prop := ∀ (e : Env) (regs : Regs) (sub nullIn last exc : Val) (rest : List Val),
  (∀ rt d rt', givenMatches exc 8 (.cls "StopIteration") regs.rt = .ok true rt → excData exc rt = .ok d rt' →
    execOp e .CLEANUP_THROW ⟨regs, exc :: last :: nullIn :: sub :: rest⟩ =
      .ok () ⟨{ regs with rt := rt' }, d.value :: nullIn :: .none :: rest⟩) ∧
  (∀ rt, givenMatches exc 8 (.cls "StopIteration") regs.rt = .ok false rt →
    execOp e .CLEANUP_THROW ⟨regs, exc :: last :: nullIn :: sub :: rest⟩ =
      .error (.unwind exc) ⟨{ regs with rt := rt }, rest⟩)

theorem cleanupThrowRules_proven : CleanupThrowRules := by
  intro e regs sub nullIn last exc rest
  refine ⟨fun rt d rt' h1 h2 => ?_, fun rt h => ?_⟩
  · bc_simp [execOp, CLEANUP_THROW, h1, h2]
  · bc_simp [execOp, CLEANUP_THROW, h]

end PyLean.Bytecode
