import PyLean.Bytecode.SpecBasic
import PyLean.Bytecode.SpecLocals

/-!
`TO_BOOL` and its specializations, `Python/bytecodes.c:486-588`.

The generic form pushes `PyObject_IsTrue(value)` and, when that raises, pops the value and
propagates the exception (`ERROR_IF(err < 0)` after `PyStackRef_CLOSE`). Each specialized
form is the generic one for every value: on the type it was specialized for it gives the
same answer without the call, and on any other value its guard sends it back to `TO_BOOL`.
That is the adaptive interpreter's contract, and a specialization that answered differently
for some value of its own type would fail it.

`TO_BOOL_STR` tests `value_o == &_Py_STR(empty)` (`:578`), pointer identity with the empty
string singleton, where the model tests `s != ""`. The two agree because every route to an
empty exact `str` returns that singleton (`unicode_get_empty`); a probe of the constructors on
3.15.2 is recorded with the registry entry. `TO_BOOL_ALWAYS_TRUE` is not stated here: its
answer rests on what the specializer put in the cache, not on the value.
-/

namespace PyLean.Bytecode

open Uop

theorem toBool_generic (e : Env) (regs : Regs) (rest : List Val) (v : Val) (b : Bool)
    (h : e.om.isTrue e.ctx v regs.rt = .ok b regs.rt) :
    TO_BOOL e ⟨regs, v :: rest⟩ = .ok () ⟨regs, .bool b :: rest⟩ := by
  simp [TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, stk, popN, pushAll, bind, EStateM.bind, BM.lift,
    RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]

/-- Generic `TO_BOOL` pushes the truth value `__bool__` or `__len__` gives, and when either
raises it pops the value and propagates the exception, whatever the object model. -/
def ToBoolGeneric : Prop := ∀ (e : Env) (regs : Regs) (rest : List Val) (v : Val),
    (∀ b rt, e.om.isTrue e.ctx v regs.rt = .ok b rt →
      execOp e .TO_BOOL ⟨regs, v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, .bool b :: rest⟩) ∧
    (∀ x rt, e.om.isTrue e.ctx v regs.rt = .error x rt →
      execOp e .TO_BOOL ⟨regs, v :: rest⟩ = .error x ⟨{ regs with rt := rt }, rest⟩)

theorem toBoolGeneric_proven : ToBoolGeneric := by
  intro e regs rest v
  constructor
  · intro b rt h
    simp [execOp, TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]
  · intro x rt h
    simp [execOp, TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, stk, popN, bind, EStateM.bind,
      BM.lift, RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]

/-- The heap holds every address on the stack: a type invariant of the machine state. -/
def HeapHolds (s : St) : Prop := ∀ a, .ref a ∈ s.stack → ∃ o, s.regs.rt.heap[a]? = some o

/-- `TO_BOOL_BOOL`, `TO_BOOL_INT`, `TO_BOOL_NONE`, `TO_BOOL_STR` and `TO_BOOL_LIST` are
`TO_BOOL` for every value on top of every stack, given the builtin `bool_slot`s
(`Lawful`). -/
def ToBoolSpecialized : Prop := ∀ (e : Env), Lawful e.om → ∀ (s : St), 1 ≤ s.stack.length →
  HeapHolds s →
    execOp e .TO_BOOL_BOOL s = execOp e .TO_BOOL s ∧
    execOp e .TO_BOOL_INT s = execOp e .TO_BOOL s ∧
    execOp e .TO_BOOL_NONE s = execOp e .TO_BOOL s ∧
    execOp e .TO_BOOL_STR s = execOp e .TO_BOOL s ∧
    execOp e .TO_BOOL_LIST s = execOp e .TO_BOOL s

theorem stk11_deopt (f : List Val → BM (List Val)) (regs : Regs) (v : Val) (rest : List Val)
    (h : f [v] regs = .error .deopt regs) :
    ∃ s', stk 1 1 f ⟨regs, v :: rest⟩ = .error .deopt s' :=
  stk_deopt 1 1 f _ (by simp) ⟨regs, by simpa using h⟩

theorem toBoolSpecialized_proven : ToBoolSpecialized := by
  intro e hom s hs hheap
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | v :: rest, _ =>
  have hdeopt : (Err.deopt : Err) = .deopt := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- TO_BOOL_BOOL: a guard; on a bool the value stays, which is what `bool_slot` gives.
    apply withDeopt_eq
    cases v with
    | bool b =>
      right
      rw [toBool_generic e regs rest _ b (hom.true_bool _ _ _)]
      show guardTop 1 _ _ = _
      exact guardTop_one regs rest _ (.bool b) false rfl
    | _ =>
      left
      exact ⟨_, by show guardTop 1 _ _ = _; rw [guardTop_one regs rest _ _ true rfl]; rfl⟩
  · apply withDeopt_eq
    cases v with
    | int i =>
      right
      rw [toBool_generic e regs rest _ _ (hom.true_int _ _ _)]
      exact stk_ok (outs := [.bool (i != 0)]) (r := regs) (by simp) rfl rfl
    | _ => left; exact stk11_deopt _ regs _ rest rfl
  · apply withDeopt_eq
    cases v with
    | none =>
      right
      rw [toBool_generic e regs rest _ _ (hom.true_none _ _)]
      exact stk_ok (outs := [.bool false]) (r := regs) (by simp) rfl rfl
    | _ => left; exact stk11_deopt _ regs _ rest rfl
  · apply withDeopt_eq
    cases v with
    | str t =>
      right
      rw [toBool_generic e regs rest _ _ (hom.true_str _ _ _)]
      show (do _GUARD_TOS_UNICODE; _TO_BOOL_STR) _ = _
      have hg : _GUARD_TOS_UNICODE ⟨regs, .str t :: rest⟩ = .ok () ⟨regs, .str t :: rest⟩ :=
        strKind.tos_eval regs rest (.str t)
      simp only [bind, EStateM.bind, hg]
      exact stk_ok (outs := [.bool (t != "")]) (r := regs) (by simp) rfl rfl
    | _ => left; exact ⟨_, rfl⟩
  · apply withDeopt_eq
    have hguard : ∀ isL, notList v regs = .ok isL regs →
        _GUARD_TOS_LIST ⟨regs, v :: rest⟩ =
          if isL then .error .deopt ⟨regs, v :: rest⟩ else .ok () ⟨regs, v :: rest⟩ :=
      fun isL h => guardTop_one regs rest _ v isL (by simpa using h)
    cases v with
    | ref a =>
      obtain ⟨o, ho⟩ := hheap a (by simp)
      cases o with
      | list items =>
        right
        rw [toBool_generic e regs rest _ _ (hom.true_list _ a items _ ho)]
        have hn : notList (.ref a) regs = .ok false regs := by
          simp [notList, isExactList, getObj, ho, bind, EStateM.bind, RM.lift, pure, EStateM.pure,
            monadLift, liftM, MonadLift.monadLift]
        show (do _GUARD_TOS_LIST; _TO_BOOL_LIST) _ = _
        simp only [bind, EStateM.bind, hguard false hn, Bool.false_eq_true, ite_false]
        exact stk_ok (outs := [.bool (items.size != 0)]) (r := regs) (by simp)
          (by simp [getObj, ho, bind, EStateM.bind, RM.lift, pure, EStateM.pure, monadLift, liftM,
            MonadLift.monadLift]) rfl
      | _ =>
        left
        have hn : notList (.ref a) regs = .ok true regs := by
          simp [notList, isExactList, getObj, ho, bind, EStateM.bind, RM.lift, pure, EStateM.pure,
            monadLift, liftM, MonadLift.monadLift]
        refine ⟨⟨regs, .ref a :: rest⟩, ?_⟩
        show (do _GUARD_TOS_LIST; _TO_BOOL_LIST) _ = _
        simp [bind, EStateM.bind, hguard true hn]
    | _ => left; exact ⟨_, rfl⟩

end PyLean.Bytecode
