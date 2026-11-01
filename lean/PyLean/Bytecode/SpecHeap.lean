import PyLean.Bytecode.SpecBasic

/-!
Specialized forms that read the heap. They need one type invariant on top of the
laws: a reference on the stack points at a live object (`Live`), which is what
"a `PyObject *` on the evaluation stack is valid" means.
-/

namespace PyLean.Bytecode

open Uop

/-- No dangling reference: the invariant `PyStackRef` values always satisfy. -/
def Live (rt : Rt) (v : Val) : Prop := ∀ a, v = .ref a → a < rt.heap.size

theorem live_obj {rt : Rt} {a : Addr} (h : Live rt (.ref a)) : ∃ o, rt.heap[a]? = some o :=
  ⟨rt.heap[a]'(h a rfl), Array.getElem?_eq_getElem (h a rfl)⟩

theorem getObj_ok {rt : Rt} {a : Addr} {o : Obj} (h : rt.heap[a]? = some o) :
    getObj a rt = .ok o rt := by simp [getObj, h]

/-- Laws for containers and iterators. -/
structure LawfulHeap (om : ObjModel) : Prop where
  /-- `list_ass_subscript` at an in-range index. -/
  store_list : ∀ ctx a items (i : Nat) v rt, rt.heap[a]? = some (.list items) → i < items.size →
    om.setItem ctx (.ref a) (.int i) v rt =
      .ok () { rt with heap := rt.heap.setIfInBounds a (.list (items.setIfInBounds i v)) }
  /-- `dict_ass_sub`. -/
  store_dict : ∀ ctx a k v d rt, rt.heap[a]? = some (.dict d) →
    om.setItem ctx (.ref a) k v rt = dictSet om ctx (.ref a) k v rt

/-- Evaluation of `RM.lift`/`BM.lift` around a read of the heap. -/
theorem isExactList_list {rt : Rt} {a : Addr} {items : Array Val}
    (h : rt.heap[a]? = some (.list items)) : isExactList (.ref a) rt = .ok true rt := by
  simp [isExactList, bind, EStateM.bind, getObj, h, pure, EStateM.pure]

/-- The two-guards shape with arbitrary guards. -/
theorem guards_spec (g1 g2 fast g : M Unit) (s : St)
    (h : g1 s = .error .deopt s ∨ (g1 s = .ok () s ∧ (g2 s = .error .deopt s ∨
      (g2 s = .ok () s ∧ ((∃ s', fast s = .error .deopt s') ∨ fast s = g s))))) :
    withDeopt (do g1; g2; fast) g s = g s := by
  apply withDeopt_eq
  rcases h with h | ⟨h1, h | ⟨h2, h⟩⟩
  · left; exact ⟨s, by simp [bind, EStateM.bind, h]⟩
  · left; exact ⟨s, by simp [bind, EStateM.bind, h1, h]⟩
  · rcases h with ⟨s', h⟩ | h
    · left; exact ⟨s', by simp [bind, EStateM.bind, h1, h2, h]⟩
    · right; simp [bind, EStateM.bind, h1, h2, h]

/-- One guard, then the fast path. -/
theorem guard1_spec (g1 fast g : M Unit) (s : St)
    (h : g1 s = .error .deopt s ∨ (g1 s = .ok () s ∧ ((∃ s', fast s = .error .deopt s') ∨ fast s = g s))) :
    withDeopt (do g1; fast) g s = g s := by
  apply withDeopt_eq
  rcases h with h | ⟨h1, h⟩
  · left; exact ⟨s, by simp [bind, EStateM.bind, h]⟩
  · rcases h with ⟨s', h⟩ | h
    · left; exact ⟨s', by simp [bind, EStateM.bind, h1, h]⟩
    · right; simp [bind, EStateM.bind, h1, h]

section Guards
variable (regs : Regs) (rest : List Val)

theorem guard_tos_int (r : Val) :
    _GUARD_TOS_INT ⟨regs, r :: rest⟩ =
      if notInt r then .error .deopt ⟨regs, r :: rest⟩ else .ok () ⟨regs, r :: rest⟩ :=
  guardTop_one regs rest _ r _ rfl

theorem notList_list {a : Addr} {items : Array Val} (h : regs.rt.heap[a]? = some (.list items)) :
    notList (.ref a) regs = .ok false regs := by
  simp [notList, bind, EStateM.bind, isExactList, getObj, h, pure, EStateM.pure, RM.lift, liftM,
    monadLift, MonadLift.monadLift]

theorem notList_other {a : Addr} {o : Obj} (h : regs.rt.heap[a]? = some o)
    (hn : ∀ i, o ≠ .list i) : notList (.ref a) regs = .ok true regs := by
  cases o <;> first
    | exact absurd rfl (hn _)
    | simp [notList, bind, EStateM.bind, isExactList, getObj, h, pure, EStateM.pure, RM.lift, liftM,
        monadLift, MonadLift.monadLift]

theorem notTuple_tuple {a : Addr} {items : Array Val} (h : regs.rt.heap[a]? = some (.tuple items)) :
    notTuple (.ref a) regs = .ok false regs := by
  simp [notTuple, bind, EStateM.bind, isExactTuple, getObj, h, pure, EStateM.pure, RM.lift, liftM,
    monadLift, MonadLift.monadLift]

theorem notTuple_other {a : Addr} {o : Obj} (h : regs.rt.heap[a]? = some o)
    (hn : ∀ i, o ≠ .tuple i) : notTuple (.ref a) regs = .ok true regs := by
  cases o <;> first
    | exact absurd rfl (hn _)
    | simp [notTuple, bind, EStateM.bind, isExactTuple, getObj, h, pure, EStateM.pure, RM.lift, liftM,
        monadLift, MonadLift.monadLift]

theorem notList_nonref (v : Val) (hv : ∀ a, v ≠ .ref a) : notList v regs = .ok true regs := by
  cases v <;> first
    | exact absurd rfl (hv _)
    | simp [notList, bind, EStateM.bind, isExactList, pure, EStateM.pure, RM.lift, liftM,
        monadLift, MonadLift.monadLift]

theorem notTuple_nonref (v : Val) (hv : ∀ a, v ≠ .ref a) : notTuple v regs = .ok true regs := by
  cases v <;> first
    | exact absurd rfl (hv _)
    | simp [notTuple, bind, EStateM.bind, isExactTuple, pure, EStateM.pure, RM.lift, liftM,
        monadLift, MonadLift.monadLift]

end Guards

/-- Fail inside a `stk` body. -/
theorem stk_deopt (p q : Nat) (f : List Val → BM (List Val)) (s : St) (hp : p ≤ s.stack.length)
    (h : ∃ r', f (s.stack.take p).reverse s.regs = .error .deopt r') :
    ∃ s', stk p q f s = .error .deopt s' := by
  obtain ⟨r', hr⟩ := h
  refine ⟨⟨r', s.stack.drop p⟩, ?_⟩
  simp [stk, popN, hp, bind, EStateM.bind, BM.lift, hr]

/-- `BINARY_OP_SUBSCR_LIST_INT`, `BINARY_OP_SUBSCR_TUPLE_INT` and `BINARY_OP_SUBSCR_STR_INT`
agree with `BINARY_OP` for `[]`, on every stack. -/
theorem subscrListInt_spec (e : Env) (hom : Lawful e.om) (hop : e.oparg = 26) (s : St)
    (hs : 2 ≤ s.stack.length) (hlive : ∀ v ∈ s.stack, Live s.regs.rt v) :
    execOp e .BINARY_OP_SUBSCR_LIST_INT s = execOp e .BINARY_OP s := by
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | r :: l :: rest, _ =>
    refine guards_spec _ _ _ (BINARY_OP e) _ ?_
    by_cases hr : notInt r = true
    · left; rw [guard_tos_int]; simp [hr]
    · right
      refine ⟨by rw [guard_tos_int]; simp [hr], ?_⟩
      obtain ⟨sub, rfl⟩ := notInt_false (by simpa using hr)
      -- what `l` is
      have hl : Live regs.rt l := hlive l (by simp)
      by_cases hlr : ∃ a, l = .ref a
      · obtain ⟨a, rfl⟩ := hlr
        obtain ⟨o, ho⟩ := live_obj hl
        by_cases hlist : ∃ items, o = .list items
        · obtain ⟨items, rfl⟩ := hlist
          right
          refine ⟨guardTop_two regs rest _ _ _ false (notList_list regs ho), ?_⟩
          by_cases hc : isNonNegCompact sub = true
          · by_cases hi : ∃ v, items[sub.toNat]? = some v
            · obtain ⟨v, hv⟩ := hi
              right
              have hsub : 0 ≤ sub := by
                simp [isNonNegCompact] at hc; omega
              have hg : e.om.binaryOp e.ctx e.oparg (.ref a) (.int sub) regs.rt = .ok v regs.rt := by
                rw [hop, hom.subscr]
                have := hom.list_item e.ctx a items sub.toNat v regs.rt ho hv
                rwa [Int.toNat_of_nonneg hsub] at this
              rw [generic_binop e regs rest _ _ v hg]
              apply fast_stk21
              simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hc,
                hv, pure, EStateM.pure]
            · left
              apply stk_deopt
              · simp
              · have hnone : items[sub.toNat]? = none := by
                  cases h : items[sub.toNat]? with
                  | none => rfl
                  | some v => exact absurd ⟨v, h⟩ hi
                refine ⟨regs, ?_⟩
                simp [bind, EStateM.bind, RM.lift, liftM, monadLift, MonadLift.monadLift, getObj, ho, hc,
                  hnone, pure, EStateM.pure, throw, throwThe, MonadExcept.throw, EStateM.throw,
                  MonadExceptOf.throw]
          · left
            apply stk_deopt
            · simp
            · refine ⟨regs, ?_⟩
              simp at hc
              simp [hc, bind, EStateM.bind, throw, throwThe, MonadExcept.throw, EStateM.throw,
                MonadExceptOf.throw]
        · left
          have hn : ∀ i, o ≠ .list i := fun i hi => hlist ⟨i, hi⟩
          exact guardTop_two regs rest _ _ _ true (notList_other regs ho hn) |>.trans (by simp)
      · left
        have hn : ∀ a, l ≠ .ref a := fun a ha => hlr ⟨a, ha⟩
        exact guardTop_two regs rest _ _ _ true (notList_nonref regs l hn) |>.trans (by simp)

end PyLean.Bytecode
