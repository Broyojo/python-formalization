import PyLean.Bytecode.SpecHeap
import PyLean.Bytecode.LawfulBuiltin

/-!
`BINARY_OP_SUBSCR_TUPLE_INT`, `BINARY_OP_SUBSCR_STR_INT` and `BINARY_OP_SUBSCR_USTR_INT`,
`Python/bytecodes.c`, the macros after `_BINARY_OP_SUBSCR_LIST_SLICE`.

Each is `BINARY_OP` for `[]` on every stack whose values are live: on the operands it was
specialized for it reads the item without calling `__getitem__`, and on any other operand one
of its guards sends it back to `BINARY_OP`. 3.15 split the tuple bounds check into its own guard
(`_GUARD_BINARY_OP_SUBSCR_TUPLE_INT_BOUNDS`); the model folds it into the fast path, which deopts
in the same cases. `USTR_INT`, new in 3.15, reads any string and deopts on a non-ASCII character,
where `STR_INT` guards that the whole string is ASCII.
-/

namespace PyLean.Bytecode

open Uop

theorem nonneg_of (sub : Int) (h : isNonNegCompact sub = true) : 0 ≤ sub ∧ sub ≤ PyLean.ssizeMax := by
  simp [isNonNegCompact] at h
  unfold PyLean.ssizeMax
  omega

/-- `BINARY_OP_SUBSCR_TUPLE_INT` is `BINARY_OP` for `[]`. -/
theorem subscrTupleInt_spec (e : Env) (hom : Lawful e.om) (hop : e.oparg = 26) (s : St)
    (hs : 2 ≤ s.stack.length) (hlive : ∀ v ∈ s.stack, Live s.regs.rt v) :
    execOp e .BINARY_OP_SUBSCR_TUPLE_INT s = execOp e .BINARY_OP s := by
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | r :: l :: rest, _ =>
    refine guards_spec _ _ _ (BINARY_OP e) _ ?_
    by_cases hr : notCompactInt r = true
    · left; rw [guard_tos_int]; simp [hr]
    · right
      refine ⟨by rw [guard_tos_int]; simp [hr], ?_⟩
      obtain ⟨sub, rfl, _⟩ := notCompactInt_false (by simpa using hr)
      have hl : Live regs.rt l := hlive l (by simp)
      by_cases hlr : ∃ a, l = .ref a
      · obtain ⟨a, rfl⟩ := hlr
        obtain ⟨o, ho⟩ := live_obj hl
        by_cases htup : ∃ items, o = .tuple items
        · obtain ⟨items, rfl⟩ := htup
          right
          refine ⟨guardTop_two regs rest _ _ _ false (notTuple_tuple regs ho), ?_⟩
          by_cases hnn : isNonNegCompact sub = true
          · obtain ⟨hsub, hmax⟩ := nonneg_of sub hnn
            by_cases hi : ∃ v, items[sub.toNat]? = some v
            · obtain ⟨v, hv⟩ := hi
              right
              have hg : e.om.binaryOp e.ctx e.oparg (.ref a) (.int sub) regs.rt = .ok v regs.rt := by
                rw [hop, hom.subscr]
                have := hom.tuple_item e.ctx a items sub.toNat v regs.rt ho hv (by omega)
                rwa [Int.toNat_of_nonneg hsub] at this
              rw [generic_binop e regs rest _ _ v hg]
              apply fast_stk21
              simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hnn,
                hv, pure, EStateM.pure]
            · left
              have hnone : items[sub.toNat]? = none := by
                cases h : items[sub.toNat]? with
                | none => rfl
                | some v => exact absurd ⟨v, h⟩ hi
              apply stk_deopt
              · simp
              · refine ⟨regs, ?_⟩
                simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hnn,
                  hnone, pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw,
                  MonadExceptOf.throw]
          · left
            apply stk_deopt
            · simp
            · refine ⟨regs, ?_⟩
              simp [bind, EStateM.bind, hnn, throw, throwThe, MonadExcept.throw, EStateM.throw,
                MonadExceptOf.throw]
        · left
          have hn : ∀ i, o ≠ .tuple i := fun i hi => htup ⟨i, hi⟩
          exact guardTop_two regs rest _ _ _ true (notTuple_other regs ho hn) |>.trans (by simp)
      · left
        have hn : ∀ a, l ≠ .ref a := fun a ha => hlr ⟨a, ha⟩
        exact guardTop_two regs rest _ _ _ true (notTuple_nonref regs _ hn) |>.trans (by simp)

/-- The generic subscript of a str at an in-range non-negative int. -/
theorem generic_str (e : Env) (hom : Lawful e.om) (hop : e.oparg = 26) (regs : Regs) (rest : List Val)
    (t : String) (sub : Int) (c : Char) (hsub : 0 ≤ sub ∧ sub ≤ PyLean.ssizeMax)
    (hc : t.toList[sub.toNat]? = some c) :
    BINARY_OP e ⟨regs, .int sub :: .str t :: rest⟩ = .ok () ⟨regs, .str (String.singleton c) :: rest⟩ := by
  apply generic_binop
  rw [hop, hom.subscr]
  have := hom.str_item e.ctx t sub.toNat c regs.rt hc (by omega)
  rwa [Int.toNat_of_nonneg hsub.1] at this

/-- `BINARY_OP_SUBSCR_STR_INT` and `BINARY_OP_SUBSCR_USTR_INT` are `BINARY_OP` for `[]`. -/
theorem subscrStrInt_spec (e : Env) (hom : Lawful e.om) (hop : e.oparg = 26) (s : St)
    (hs : 2 ≤ s.stack.length) :
    execOp e .BINARY_OP_SUBSCR_STR_INT s = execOp e .BINARY_OP s ∧
    execOp e .BINARY_OP_SUBSCR_USTR_INT s = execOp e .BINARY_OP s := by
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | r :: l :: rest, _ =>
    have deoptFast : ∀ (f : List Val → BM (List Val)), f [l, r] regs = .error .deopt regs →
        ∃ s', stk 2 1 f ⟨regs, r :: l :: rest⟩ = .error .deopt s' :=
      fun f h => stk_deopt 2 1 f _ (by simp) ⟨regs, by simpa using h⟩
    constructor
    · refine guards_spec _ _ _ (BINARY_OP e) _ ?_
      by_cases hr : notCompactInt r = true
      · left; rw [guard_tos_int]; simp [hr]
      · right
        refine ⟨by rw [guard_tos_int]; simp [hr], ?_⟩
        obtain ⟨sub, rfl, _⟩ := notCompactInt_false (by simpa using hr)
        cases l with
        | str t =>
          by_cases hasc : (t.toList.any fun c => asciiLimit ≤ c.toNat) = true
          · left
            exact (guardTop_two regs rest _ (.str t) _ true (by simp [hasc, pure, EStateM.pure])).trans
              (by simp)
          · right
            refine ⟨(guardTop_two regs rest _ (.str t) _ false
              (by simp only [Bool.not_eq_true] at hasc; simp [hasc, pure, EStateM.pure])).trans
              (by simp), ?_⟩
            by_cases hnn : isNonNegCompact sub = true
            · cases hc : t.toList[sub.toNat]? with
              | none =>
                left
                exact deoptFast _ (by simp [hnn, hc, bind, EStateM.bind, throw, throwThe,
                  MonadExcept.throw, EStateM.throw, MonadExceptOf.throw])
              | some c =>
                right
                rw [generic_str e hom hop regs rest t sub c (nonneg_of sub hnn) hc]
                apply fast_stk21
                simp [hnn, hc, pure, EStateM.pure]
            · left
              exact deoptFast _ (by simp [hnn, bind, EStateM.bind, throw, throwThe, MonadExcept.throw,
                EStateM.throw, MonadExceptOf.throw])
        | _ =>
          left
          exact (guardTop_two regs rest _ _ _ true rfl).trans (by simp)
    · refine guards_spec _ _ _ (BINARY_OP e) _ ?_
      by_cases hr : notCompactInt r = true
      · left; rw [guard_tos_int]; simp [hr]
      · right
        refine ⟨by rw [guard_tos_int]; simp [hr], ?_⟩
        obtain ⟨sub, rfl, _⟩ := notCompactInt_false (by simpa using hr)
        cases l with
        | str t =>
          right
          refine ⟨(strKind.nos_eval regs rest (.str t) (.int sub)).trans (by simp [strKind, notStr]), ?_⟩
          by_cases hnn : isNonNegCompact sub = true
          · cases hc : t.toList[sub.toNat]? with
            | none =>
              left
              exact deoptFast _ (by simp [hnn, hc, bind, EStateM.bind, throw, throwThe,
                MonadExcept.throw, EStateM.throw, MonadExceptOf.throw])
            | some c =>
              by_cases hasc : asciiLimit ≤ c.toNat
              · left
                exact deoptFast _ (by simp [hnn, hc, hasc, bind, EStateM.bind, throw, throwThe,
                  MonadExcept.throw, EStateM.throw, MonadExceptOf.throw])
              · right
                rw [generic_str e hom hop regs rest t sub c (nonneg_of sub hnn) hc]
                apply fast_stk21
                simp [hnn, hc, hasc, bind, EStateM.bind, pure, EStateM.pure]
          · left
            exact deoptFast _ (by simp [hnn, bind, EStateM.bind, throw, throwThe, MonadExcept.throw,
              EStateM.throw, MonadExceptOf.throw])
        | _ =>
          left
          exact (strKind.nos_eval regs rest _ (.int sub)).trans (by simp [strKind, notStr])

/-- Registry form of `subscrTupleInt_spec`. -/
def SubscrTupleInt : Prop := ∀ (e : Env), Lawful e.om → e.oparg = 26 → ∀ (s : St), 2 ≤ s.stack.length →
  (∀ v ∈ s.stack, Live s.regs.rt v) → execOp e .BINARY_OP_SUBSCR_TUPLE_INT s = execOp e .BINARY_OP s
theorem subscrTupleInt_proven : SubscrTupleInt := fun e hom hop s hs hl => subscrTupleInt_spec e hom hop s hs hl

/-- Registry form of `subscrStrInt_spec`. -/
def SubscrStrInt : Prop := ∀ (e : Env), Lawful e.om → e.oparg = 26 → ∀ (s : St), 2 ≤ s.stack.length →
  execOp e .BINARY_OP_SUBSCR_STR_INT s = execOp e .BINARY_OP s ∧
  execOp e .BINARY_OP_SUBSCR_USTR_INT s = execOp e .BINARY_OP s
theorem subscrStrInt_proven : SubscrStrInt := fun e hom hop s hs => subscrStrInt_spec e hom hop s hs

end PyLean.Bytecode
