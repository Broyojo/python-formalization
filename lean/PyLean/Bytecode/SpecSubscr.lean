import PyLean.Bytecode.SpecFastSubscr
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
    have hl : Live regs.rt l := hlive l (by simp)
    obtain ⟨_, F1, F2⟩ := subscrTupleFast_proven regs rest l r hl
    apply withDeopt_eq
    by_cases h : ∃ a items i v, l = .ref a ∧ regs.rt.heap[a]? = some (.tuple items) ∧ r = .int i ∧
        0 ≤ i ∧ i < 2 ^ 30 ∧ items[i.toNat]? = some v
    · right
      obtain ⟨a, items, i, v, rfl, ho, rfl, h0, h1, hv⟩ := h
      rw [F1 a items i v rfl ho rfl h0 h1 hv]
      have hg : e.om.binaryOp e.ctx e.oparg (.ref a) (.int i) regs.rt = .ok v regs.rt := by
        rw [hop, hom.subscr]
        have := hom.tuple_item e.ctx a items i.toNat v regs.rt ho hv
          (by rw [Int.toNat_of_nonneg h0]; unfold PyLean.ssizeMax; omega)
        rwa [Int.toNat_of_nonneg h0] at this
      exact (generic_binop e regs rest _ _ v hg).symm
    · exact Or.inl (F2 h)

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

theorem generic_store (e : Env) (regs : Regs) (rest : List Val) (v c k : Val) (rt : Rt)
    (h : e.om.setItem e.ctx c k v regs.rt = .ok () rt) :
    STORE_SUBSCR e ⟨regs, k :: c :: v :: rest⟩ = .ok () ⟨{ regs with rt := rt }, rest⟩ := by
  simp [STORE_SUBSCR, _SPECIALIZE_STORE_SUBSCR, _STORE_SUBSCR, stk, popN, pushAll, bind, EStateM.bind,
    BM.lift, RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]

/-- `STORE_SUBSCR_LIST_INT` is `STORE_SUBSCR` on every live stack, a negative index included. -/
theorem storeSubscrListInt_spec (e : Env) (hom : Lawful e.om) (s : St) (hs : 3 ≤ s.stack.length)
    (hlive : ∀ v ∈ s.stack, Live s.regs.rt v) :
    execOp e .STORE_SUBSCR_LIST_INT s = execOp e .STORE_SUBSCR s := by
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | k :: c :: v :: rest, _ =>
    refine guards_spec _ _ _ (STORE_SUBSCR e) _ ?_
    by_cases hr : notCompactInt k = true
    · left; rw [guard_tos_int]; simp [hr]
    · right
      refine ⟨by rw [guard_tos_int]; simp [hr], ?_⟩
      obtain ⟨sub, rfl, hcmp⟩ := notCompactInt_false (by simpa using hr)
      have hsm : PyLean.ssizeMin ≤ sub ∧ sub ≤ PyLean.ssizeMax := by
        simp [isCompact] at hcmp; unfold PyLean.ssizeMin PyLean.ssizeMax; omega
      have hl : Live regs.rt c := hlive c (by simp)
      by_cases hcr : ∃ a, c = .ref a
      · obtain ⟨a, rfl⟩ := hcr
        obtain ⟨o, ho⟩ := live_obj hl
        by_cases hlist : ∃ items, o = .list items
        · obtain ⟨items, rfl⟩ := hlist
          right
          refine ⟨(guardTop_two regs (v :: rest) _ _ _ false (notList_list regs ho)), ?_⟩
          by_cases hin : 0 ≤ (if sub < 0 then sub + (items.size : Int) else sub) ∧
              (if sub < 0 then sub + (items.size : Int) else sub) < items.size
          · right
            rw [generic_store e regs rest v (.ref a) (.int sub) _
              (hom.store_list e.ctx a items sub v regs.rt ho hin.1 hin.2 hsm.1 hsm.2)]
            have hn1 : ¬ (if sub < 0 then sub + (items.size : Int) else sub) < 0 := by omega
            have hn2 : ¬ (items.size : Int) ≤ (if sub < 0 then sub + (items.size : Int) else sub) := by omega
            simp [_STORE_SUBSCR_LIST_INT, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift,
              liftM, monadLift, MonadLift.monadLift, getObj, ho, hn1, hn2, setObj, pure, EStateM.pure]
          · left
            apply stk_deopt
            · simp
            · refine ⟨regs, ?_⟩
              by_cases hneg : sub < 0
              · simp only [hneg, ite_true] at hin
                by_cases h1 : sub + (items.size : Int) < 0
                · simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hneg, h1, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
                · have h2 : (items.size : Int) ≤ sub + items.size := by omega
                  simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hneg, h1, h2, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
              · simp only [hneg, ite_false] at hin
                have h1 : ¬ sub < 0 := hneg
                have h2 : (items.size : Int) ≤ sub := by omega
                simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hneg, h2, throw, throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]
        · left
          have hn : ∀ i, o ≠ .list i := fun i hi => hlist ⟨i, hi⟩
          exact guardTop_two regs (v :: rest) _ _ _ true (notList_other regs ho hn) |>.trans (by simp)
      · left
        have hn : ∀ a, c ≠ .ref a := fun a ha => hcr ⟨a, ha⟩
        exact guardTop_two regs (v :: rest) _ _ _ true (notList_nonref regs c hn) |>.trans (by simp)

/-- Registry form of `storeSubscrListInt_spec`. -/
def StoreSubscrListInt : Prop := ∀ (e : Env), Lawful e.om → ∀ (s : St), 3 ≤ s.stack.length →
  (∀ v ∈ s.stack, Live s.regs.rt v) → execOp e .STORE_SUBSCR_LIST_INT s = execOp e .STORE_SUBSCR s
theorem storeSubscrListInt_proven : StoreSubscrListInt :=
  fun e hom s hs hl => storeSubscrListInt_spec e hom s hs hl

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
