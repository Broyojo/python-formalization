import PyLean.Bytecode.SpecFast

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
  have hv : Live regs.rt v := fun a ha => by
    subst ha
    obtain ⟨o, ho⟩ := hheap a (by simp)
    exact (Array.getElem?_eq_some_iff.1 ho).1
  obtain ⟨_, fi1, fi2, fn1, fn2, fs1, fs2, fl1, fl2, fb1, fb2⟩ := toBoolFast_proven regs rest v hv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply withDeopt_eq
    by_cases hb : IsBool v
    · right
      obtain ⟨b, rfl⟩ := hb
      rw [fb1 ⟨b, rfl⟩, toBool_generic e regs rest _ b (hom.true_bool _ _ _)]
    · exact Or.inl ⟨_, fb2 hb⟩
  · apply withDeopt_eq
    by_cases hc : CompactInt v
    · right
      obtain ⟨i, rfl, hc⟩ := hc
      rw [fi1 i rfl hc, toBool_generic e regs rest _ _ (hom.true_int _ _ _)]
    · exact Or.inl ⟨_, fi2 hc⟩
  · apply withDeopt_eq
    by_cases hn : v = .none
    · right
      subst hn
      rw [fn1 rfl, toBool_generic e regs rest _ _ (hom.true_none _ _)]
    · exact Or.inl (fn2 hn)
  · apply withDeopt_eq
    by_cases ht : IsStr v
    · right
      obtain ⟨t, rfl⟩ := ht
      rw [fs1 t rfl, toBool_generic e regs rest _ _ (hom.true_str _ _ _)]
    · exact Or.inl ⟨_, fs2 ht⟩
  · apply withDeopt_eq
    by_cases hl : IsList regs.rt v
    · right
      obtain ⟨a, items, rfl, ho⟩ := hl
      rw [fl1 a items rfl ho, toBool_generic e regs rest _ _ (hom.true_list _ a items _ ho)]
    · exact Or.inl ⟨_, fl2 hl⟩

end PyLean.Bytecode
