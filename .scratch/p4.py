p='lean/PyLean/Bytecode/SpecBasic.lean'
s=open(p).read()
a=s.index('theorem withDeopt_of_deopt')
s=s[:a]+r'''theorem withDeopt_of_deopt {m g : M Unit} {s s' : St} (h : m s = .error .deopt s') :
    withDeopt m g s = g s := by simp [withDeopt, h]

/-- A form that either deopts or matches the generic form is the generic form. -/
theorem withDeopt_eq {m g : M Unit} {s : St} (h : (∃ s', m s = .error .deopt s') ∨ m s = g s) :
    withDeopt m g s = g s := by
  rcases h with ⟨s', h⟩ | h
  · exact withDeopt_of_deopt h
  · simp only [withDeopt, h]
    split
    · rename_i h'; simp [h']
    · rfl

/-! ### The building blocks, evaluated on explicit stacks -/

section Blocks
variable (regs : Regs) (rest : List Val)

theorem peekN_one (x : Val) : peekN 1 ⟨regs, x :: rest⟩ = .ok [x] ⟨regs, x :: rest⟩ := by
  simp [peekN]

theorem peekN_two (x y : Val) :
    peekN 2 ⟨regs, y :: x :: rest⟩ = .ok [x, y] ⟨regs, y :: x :: rest⟩ := by
  simp [peekN]

theorem popN_two (x y : Val) :
    popN 2 ⟨regs, y :: x :: rest⟩ = .ok [x, y] ⟨regs, rest⟩ := by
  simp [popN]

theorem popN_one (x : Val) : popN 1 ⟨regs, x :: rest⟩ = .ok [x] ⟨regs, rest⟩ := by
  simp [popN]

/-- A guard on the top of the stack. -/
theorem guardTop_one (bad : List Val → BM Bool) (x : Val) (b : Bool)
    (h : bad [x] regs = .ok b regs) :
    guardTop 1 bad ⟨regs, x :: rest⟩ =
      if b then .error .deopt ⟨regs, x :: rest⟩ else .ok () ⟨regs, x :: rest⟩ := by
  cases b <;>
  simp [guardTop, peekN, bind, EStateM.bind, BM.lift, h, deoptIf, pure, EStateM.pure, throw,
    throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

/-- A guard on the second value. -/
theorem guardTop_two (bad : List Val → BM Bool) (x y : Val) (b : Bool)
    (h : bad [x, y] regs = .ok b regs) :
    guardTop 2 bad ⟨regs, y :: x :: rest⟩ =
      if b then .error .deopt ⟨regs, y :: x :: rest⟩ else .ok () ⟨regs, y :: x :: rest⟩ := by
  cases b <;>
  simp [guardTop, peekN, bind, EStateM.bind, BM.lift, h, deoptIf, pure, EStateM.pure, throw,
    throwThe, MonadExcept.throw, EStateM.throw, MonadExceptOf.throw]

end Blocks

/-- `x` passes a guard that tests one constructor; used for all three kinds. -/
structure Kind where
  bad : Val → Bool
  tos : M Unit
  nos : M Unit
  tos_eval : ∀ (regs : Regs) rest x, tos ⟨regs, x :: rest⟩ =
    if bad x then .error .deopt ⟨regs, x :: rest⟩ else .ok () ⟨regs, x :: rest⟩
  nos_eval : ∀ (regs : Regs) rest x y, nos ⟨regs, y :: x :: rest⟩ =
    if bad x then .error .deopt ⟨regs, y :: x :: rest⟩ else .ok () ⟨regs, y :: x :: rest⟩

def intKind : Kind where
  bad := notInt
  tos := _GUARD_TOS_INT
  nos := _GUARD_NOS_INT
  tos_eval := fun regs rest x => guardTop_one regs rest _ x _ rfl
  nos_eval := fun regs rest x y => guardTop_two regs rest _ x y _ rfl

def floatKind : Kind where
  bad := notFloat
  tos := _GUARD_TOS_FLOAT
  nos := _GUARD_NOS_FLOAT
  tos_eval := fun regs rest x => guardTop_one regs rest _ x _ rfl
  nos_eval := fun regs rest x y => guardTop_two regs rest _ x y _ rfl

def strKind : Kind where
  bad := notStr
  tos := _GUARD_TOS_UNICODE
  nos := _GUARD_NOS_UNICODE
  tos_eval := fun regs rest x => guardTop_one regs rest _ x _ rfl
  nos_eval := fun regs rest x y => guardTop_two regs rest _ x y _ rfl

/-- The shape of every two-guard specialization: when both guards pass the fast
path equals the generic form, and when one fails it deopts. -/
theorem two_guard_spec (K : Kind) (fast g : M Unit) (s : St) (hs : 2 ≤ s.stack.length)
    (h : ∀ regs l r rest, K.bad r = false → K.bad l = false →
      fast ⟨regs, r :: l :: rest⟩ = g ⟨regs, r :: l :: rest⟩) :
    withDeopt (do K.tos; K.nos; fast) g s = g s := by
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | r :: l :: rest, _ =>
    apply withDeopt_eq
    by_cases hr : K.bad r = true
    · left
      exact ⟨_, by simp [bind, EStateM.bind, K.tos_eval, hr]⟩
    · by_cases hl : K.bad l = true
      · left
        refine ⟨_, ?_⟩
        simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl]
        rfl
      · right
        simp only [Bool.not_eq_true] at hr hl
        simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl]
        exact h regs l r rest hr hl

theorem notInt_false {v : Val} (h : notInt v = false) : ∃ i, v = .int i := by
  cases v <;> simp_all [notInt]

theorem notFloat_false {v : Val} (h : notFloat v = false) : ∃ i, v = .float i := by
  cases v <;> simp_all [notFloat]

theorem notStr_false {v : Val} (h : notStr v = false) : ∃ i, v = .str i := by
  cases v <;> simp_all [notStr]

/-- `_BINARY_OP` on two values the slot handles without touching the state. -/
theorem generic_binop (e : Env) (regs : Regs) (rest : List Val) (l r res : Val)
    (h : e.om.binaryOp e.ctx e.oparg l r regs.rt = .ok res regs.rt) :
    BINARY_OP e ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, res :: rest⟩ := by
  simp [BINARY_OP, _SPECIALIZE_BINARY_OP, _BINARY_OP, stkK, peekN, popN, pushAll, bind, EStateM.bind,
    BM.lift, RM.lift, pure, EStateM.pure, h, monadLift, liftM, MonadLift.monadLift]
  rfl

/-- The fast half of a `(left, right -- res)` body. -/
theorem fast_stk21 (f : List Val → BM (List Val)) (regs : Regs) (rest : List Val) (l r res : Val)
    (h : f [l, r] regs = .ok [res] regs) :
    stk 2 1 f ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, res :: rest⟩ := by
  simp [stk, popN, pushAll, bind, EStateM.bind, BM.lift, pure, EStateM.pure, h]

section Int
variable (e : Env) (hom : Lawful e.om) (s : St) (hs : 2 ≤ s.stack.length)
include hom hs

/-- `BINARY_OP_ADD_INT` is `BINARY_OP` for `+` and `+=`. -/
theorem binaryAddInt_spec (hop : e.oparg = 0 ∨ e.oparg = 13) :
    execOp e .BINARY_OP_ADD_INT s = execOp e .BINARY_OP s := by
  refine two_guard_spec intKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notInt_false hl
  obtain ⟨b, rfl⟩ := notInt_false hr
  rw [generic_binop e regs rest _ _ (.int (a + b)) (hom.add_int _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

theorem binarySubInt_spec (hop : e.oparg = 10 ∨ e.oparg = 23) :
    execOp e .BINARY_OP_SUBTRACT_INT s = execOp e .BINARY_OP s := by
  refine two_guard_spec intKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notInt_false hl
  obtain ⟨b, rfl⟩ := notInt_false hr
  rw [generic_binop e regs rest _ _ (.int (a - b)) (hom.sub_int _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

theorem binaryMulInt_spec (hop : e.oparg = 5 ∨ e.oparg = 18) :
    execOp e .BINARY_OP_MULTIPLY_INT s = execOp e .BINARY_OP s := by
  refine two_guard_spec intKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notInt_false hl
  obtain ⟨b, rfl⟩ := notInt_false hr
  rw [generic_binop e regs rest _ _ (.int (a * b)) (hom.mul_int _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

theorem binaryAddFloat_spec (hop : e.oparg = 0 ∨ e.oparg = 13) :
    execOp e .BINARY_OP_ADD_FLOAT s = execOp e .BINARY_OP s := by
  refine two_guard_spec floatKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  rw [generic_binop e regs rest _ _ (.float (fadd a b)) (hom.add_float _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

theorem binarySubFloat_spec (hop : e.oparg = 10 ∨ e.oparg = 23) :
    execOp e .BINARY_OP_SUBTRACT_FLOAT s = execOp e .BINARY_OP s := by
  refine two_guard_spec floatKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  rw [generic_binop e regs rest _ _ (.float (fsub a b)) (hom.sub_float _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

theorem binaryMulFloat_spec (hop : e.oparg = 5 ∨ e.oparg = 18) :
    execOp e .BINARY_OP_MULTIPLY_FLOAT s = execOp e .BINARY_OP s := by
  refine two_guard_spec floatKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  rw [generic_binop e regs rest _ _ (.float (fmul a b)) (hom.mul_float _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

theorem binaryAddUnicode_spec (hop : e.oparg = 0 ∨ e.oparg = 13) :
    execOp e .BINARY_OP_ADD_UNICODE s = execOp e .BINARY_OP s := by
  refine two_guard_spec strKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notStr_false hl
  obtain ⟨b, rfl⟩ := notStr_false hr
  rw [generic_binop e regs rest _ _ (.str (a ++ b)) (hom.add_str _ _ _ _ _ hop)]
  exact fast_stk21 _ regs rest _ _ _ rfl

end Int

end PyLean.Bytecode
'''
open(p,'w').write(s)
