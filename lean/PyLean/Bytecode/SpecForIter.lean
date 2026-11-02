import PyLean.Bytecode.SpecSubscr

/-!
`FOR_ITER_LIST` and `FOR_ITER_TUPLE`, `Python/bytecodes.c` `_ITER_CHECK_LIST` .. `_ITER_NEXT_TUPLE`.

Since 3.15 an exact list or tuple is iterated without an iterator object: `GET_ITER` leaves the
sequence on the stack with a tagged index above it (`PyStackRef_TagInt(0)`), and `FOR_ITER` reads
item `index` and bumps the tag (`_PyForIter_VirtualIteratorNext`, `Python/ceval.c`). The
specialized forms do the same read and the same bounds test without the call. Each equals
`FOR_ITER` on every stack whose sequence slot carries a tag, which is what `GET_ITER` leaves:
on a list or tuple they agree item by item and at the end of the sequence, and on anything else
the type guard sends them back to `FOR_ITER`.

At the end C also writes `PyStackRef_TagInt(-1)` into the slot; only the `POP_ITER` at the jump
target reads it, and it discards it, so the model does not.
-/

namespace PyLean.Bytecode

open Uop

/-- What `GET_ITER` leaves: a list or tuple being iterated has a tagged index above it. -/
def TaggedSeq (s : St) : Prop := ∀ index a rest o, s.stack = index :: .ref a :: rest →
  s.regs.rt.heap[a]? = some o → (∃ items, o = .list items ∨ o = .tuple items) → ∃ i, index = .tagged i

theorem seqItems_ok {regs : Regs} {a : Addr} {o : Obj} {items : Array Val} (h : regs.rt.heap[a]? = some o)
    (ho : o = .list items ∨ o = .tuple items) : seqItems (.ref a) regs = .ok items regs := by
  rcases ho with rfl | rfl <;>
  simp [seqItems, getObj, h, bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, pure,
    EStateM.pure]

theorem iterItem_ok {rt : Rt} {a : Addr} {o : Obj} {items : Array Val} (i : Nat) (h : rt.heap[a]? = some o)
    (ho : o = .list items ∨ o = .tuple items) :
    iterItem (.ref a) i rt = .ok (items[i]?.map fun v => (v, i + 1)) rt := by
  rcases ho with rfl | rfl <;>
  simp [iterItem, getObj, h, bind, EStateM.bind, pure, EStateM.pure]

/-- On a list or tuple with a tagged index, the jump-and-next body is generic `FOR_ITER`. -/
theorem seq_body (e : Env) (regs : Regs) (a : Addr) (o : Obj) (items : Array Val) (i : Nat)
    (rest : List Val) (h : regs.rt.heap[a]? = some o) (ho : o = .list items ∨ o = .tuple items) :
    (do iterJumpSeq e; iterNextSeq) ⟨regs, .tagged i :: .ref a :: rest⟩ =
      FOR_ITER e ⟨regs, .tagged i :: .ref a :: rest⟩ := by
  have hsi := seqItems_ok (regs := regs) h ho
  have hit := iterItem_ok (rt := regs.rt) i h ho
  by_cases hend : items.size ≤ i
  · have hnone : items[i]? = none := by simp [hend]
    simp [iterJumpSeq, iterNextSeq, FOR_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, virtualNext, peekN, popN,
      bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, hsi, hit, hnone, hend,
      taggedIndex, pure, EStateM.pure, jumpBy, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw]
  · have hlt : i < items.size := by omega
    have hsome : items[i]? = some items[i] := by simp [hlt]
    simp [iterJumpSeq, iterNextSeq, FOR_ITER, _SPECIALIZE_FOR_ITER, _FOR_ITER, virtualNext, peekN, popN,
      bind, EStateM.bind, BM.lift, RM.lift, liftM, monadLift, MonadLift.monadLift, hsi, hit, hsome, hend,
      taggedIndex, pure, EStateM.pure, stk, pushAll, Array.getD_eq_getD_getElem?]

/-- `FOR_ITER_LIST` and `FOR_ITER_TUPLE` are `FOR_ITER` on every live stack that `GET_ITER` could
have left. -/
def ForIterSeq : Prop := ∀ (e : Env) (s : St), 2 ≤ s.stack.length → (∀ v ∈ s.stack, Live s.regs.rt v) →
  TaggedSeq s →
    execOp e .FOR_ITER_LIST s = execOp e .FOR_ITER s ∧ execOp e .FOR_ITER_TUPLE s = execOp e .FOR_ITER s

theorem forIterSeq_proven : ForIterSeq := by
  intro e s hs hlive htag
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | index :: iter :: rest, _ =>
    have hl : Live regs.rt iter := hlive iter (by simp)
    constructor
    · refine guard1_spec _ _ (FOR_ITER e) _ ?_
      by_cases hir : ∃ a, iter = .ref a
      · obtain ⟨a, rfl⟩ := hir
        obtain ⟨o, ho⟩ := live_obj hl
        by_cases hlist : ∃ items, o = .list items
        · obtain ⟨items, rfl⟩ := hlist
          obtain ⟨i, rfl⟩ := htag index a rest _ rfl ho ⟨items, Or.inl rfl⟩
          right
          refine ⟨guardTop_two regs rest _ _ _ false (notList_list regs ho), Or.inr ?_⟩
          exact seq_body e regs a _ items i rest ho (Or.inl rfl)
        · left
          have hn : ∀ i, o ≠ .list i := fun i hi => hlist ⟨i, hi⟩
          exact guardTop_two regs rest _ _ _ true (notList_other regs ho hn)
      · left
        have hn : ∀ a, iter ≠ .ref a := fun a ha => hir ⟨a, ha⟩
        exact guardTop_two regs rest _ _ _ true (notList_nonref regs iter hn)
    · refine guard1_spec _ _ (FOR_ITER e) _ ?_
      by_cases hir : ∃ a, iter = .ref a
      · obtain ⟨a, rfl⟩ := hir
        obtain ⟨o, ho⟩ := live_obj hl
        by_cases htup : ∃ items, o = .tuple items
        · obtain ⟨items, rfl⟩ := htup
          obtain ⟨i, rfl⟩ := htag index a rest _ rfl ho ⟨items, Or.inr rfl⟩
          right
          refine ⟨guardTop_two regs rest _ _ _ false (notTuple_tuple regs ho), Or.inr ?_⟩
          exact seq_body e regs a _ items i rest ho (Or.inr rfl)
        · left
          have hn : ∀ i, o ≠ .tuple i := fun i hi => htup ⟨i, hi⟩
          exact guardTop_two regs rest _ _ _ true (notTuple_other regs ho hn)
      · left
        have hn : ∀ a, iter ≠ .ref a := fun a ha => hir ⟨a, ha⟩
        exact guardTop_two regs rest _ _ _ true (notTuple_nonref regs iter hn)

end PyLean.Bytecode
