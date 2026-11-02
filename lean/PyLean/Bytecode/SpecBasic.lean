import PyLean.Bytecode.Exec

/-!
The semantic contract of the adaptive interpreter, part 1: the object-model laws
a specialized fast path relies on, and equality of each specialized instruction
with its generic form.

`Lawful om` lists exactly what a fast path assumes about the object model: that
`PyNumber_Add` on two exact ints is `_PyLong_Add`, and so on. They are the
definitions of those builtin slots, not assumptions about inputs. Every theorem
below is for all stacks, all values and all `Lawful` models. A guard that fails
falls back to the generic form, so the statements have no hypothesis on the
operands; the only preconditions are the specializer's own choice of family
member for an `oparg`, which `_Py_Specialize_BinaryOp` and friends establish, and
a stack that is deep enough, which the compiler's stack-depth pass establishes.
-/

namespace PyLean.Bytecode

open Uop

/-- `float_richcompare` on two doubles, the `Compare:` block of `Objects/floatobject.c`. -/
def floatTable (op : Nat) (x y : Binary64.F64) : Bool :=
  match op with
  | 0 => Binary64.F64.lt x y | 1 => Binary64.F64.le x y | 2 => Binary64.F64.eq x y
  | 3 => Binary64.F64.ne x y | 4 => Binary64.F64.gt x y | _ => Binary64.F64.ge x y

/-- What the builtin slots do on exact operands. -/
structure Lawful (om : ObjModel) : Prop where
  /-- `bool_slot`: `PyObject_IsTrue` on singletons, ints, strs and lists. -/
  true_bool : ∀ ctx b rt, om.isTrue ctx (.bool b) rt = .ok b rt
  true_int : ∀ ctx i rt, om.isTrue ctx (.int i) rt = .ok (i != 0) rt
  true_none : ∀ ctx rt, om.isTrue ctx .none rt = .ok false rt
  true_str : ∀ ctx s rt, om.isTrue ctx (.str s) rt = .ok (s != "") rt
  true_list : ∀ ctx a items rt, rt.heap[a]? = some (.list items) →
    om.isTrue ctx (.ref a) rt = .ok (items.size != 0) rt
  /-- `long_add`, `long_sub`, `long_mul`, for the plain and in-place slots. -/
  add_int : ∀ ctx nb a b rt, (nb = 0 ∨ nb = 13) →
    om.binaryOp ctx nb (.int a) (.int b) rt = .ok (.int (a + b)) rt
  sub_int : ∀ ctx nb a b rt, (nb = 10 ∨ nb = 23) →
    om.binaryOp ctx nb (.int a) (.int b) rt = .ok (.int (a - b)) rt
  mul_int : ∀ ctx nb a b rt, (nb = 5 ∨ nb = 18) →
    om.binaryOp ctx nb (.int a) (.int b) rt = .ok (.int (a * b)) rt
  /-- `float_add`, `float_sub`, `float_mul`. -/
  add_float : ∀ ctx nb a b rt, (nb = 0 ∨ nb = 13) →
    om.binaryOp ctx nb (.float a) (.float b) rt = .ok (.float (fadd a b)) rt
  sub_float : ∀ ctx nb a b rt, (nb = 10 ∨ nb = 23) →
    om.binaryOp ctx nb (.float a) (.float b) rt = .ok (.float (fsub a b)) rt
  mul_float : ∀ ctx nb a b rt, (nb = 5 ∨ nb = 18) →
    om.binaryOp ctx nb (.float a) (.float b) rt = .ok (.float (fmul a b)) rt
  /-- `unicode_concatenate`. -/
  add_str : ∀ ctx nb a b rt, (nb = 0 ∨ nb = 13) →
    om.binaryOp ctx nb (.str a) (.str b) rt = .ok (.str (a ++ b)) rt
  /-- `long_or`, `long_and`, `long_xor`. -/
  or_int : ∀ ctx nb a b rt, (nb = 7 ∨ nb = 20) →
    om.binaryOp ctx nb (.int a) (.int b) rt = .ok (.int (intOr a b)) rt
  and_int : ∀ ctx nb a b rt, (nb = 1 ∨ nb = 14) →
    om.binaryOp ctx nb (.int a) (.int b) rt = .ok (.int (intAnd a b)) rt
  xor_int : ∀ ctx nb a b rt, (nb = 12 ∨ nb = 25) →
    om.binaryOp ctx nb (.int a) (.int b) rt = .ok (.int (intXor a b)) rt
  /-- `_PyEval_BinaryOps[NB_SUBSCR] = PyObject_GetItem`. -/
  subscr : ∀ ctx l r, om.binaryOp ctx 26 l r = om.getItem ctx l r
  /-- `list_subscript`, `tuplesubscript`, `unicode_subscript` at an in-range
  non-negative int. -/
  list_item : ∀ ctx a items (i : Nat) v rt, rt.heap[a]? = some (.list items) → items[i]? = some v →
    (i : Int) ≤ PyLean.ssizeMax → om.getItem ctx (.ref a) (.int i) rt = .ok v rt
  /-- `list_subscript` at a negative int, which counts from the end. The fast path of
  `BINARY_OP_SUBSCR_LIST_INT` relies on this since 3.15. -/
  list_item_neg : ∀ ctx a items (i : Int) v rt, rt.heap[a]? = some (.list items) → i < 0 →
    items[(i + items.size).toNat]? = some v → 0 ≤ i + items.size → PyLean.ssizeMin ≤ i →
    om.getItem ctx (.ref a) (.int i) rt = .ok v rt
  tuple_item : ∀ ctx a items (i : Nat) v rt, rt.heap[a]? = some (.tuple items) → items[i]? = some v →
    (i : Int) ≤ PyLean.ssizeMax → om.getItem ctx (.ref a) (.int i) rt = .ok v rt
  str_item : ∀ ctx s (i : Nat) c rt, s.toList[i]? = some c → (i : Int) ≤ PyLean.ssizeMax →
    om.getItem ctx (.str s) (.int i) rt = .ok (.str (String.singleton c)) rt
  /-- `long_richcompare` and `unicode_compare_eq` give a bool. -/
  cmp_int : ∀ ctx a b op rt, op < 6 →
    om.richCompare ctx (.int a) (.int b) op rt =
      .ok (.bool (match op with
        | 0 => decide (a < b) | 1 => decide (a ≤ b) | 2 => decide (a = b)
        | 3 => decide (a ≠ b) | 4 => decide (a > b) | _ => decide (a ≥ b))) rt
  /-- `list_ass_subscript` at an in-range int, negative ones counting from the end. -/
  store_list : ∀ ctx a items (i : Int) v rt, rt.heap[a]? = some (.list items) →
    0 ≤ (if i < 0 then i + items.size else i) → (if i < 0 then i + items.size else i) < items.size →
    PyLean.ssizeMin ≤ i → i ≤ PyLean.ssizeMax →
    om.setItem ctx (.ref a) (.int i) v rt = .ok ()
      { rt with heap := (rt.heap.setIfInBounds a
          (.list (items.setIfInBounds (if i < 0 then i + items.size else i).toNat v))) }
  /-- `rangeiter_next`: the next value and the iterator advanced, or the end. -/
  range_next : ∀ ctx a start step len rt, rt.heap[a]? = some (.rangeIter start step len) →
    om.iterNext ctx (.ref a) rt = if 0 < len then
      .ok (some (.int start))
        { rt with heap := (rt.heap.setIfInBounds a (.rangeIter (start + step) step (len - 1))) }
    else .ok none rt
  /-- `float_richcompare` gives a bool. -/
  cmp_float : ∀ ctx a b op rt,
    om.richCompare ctx (.float a) (.float b) op rt = .ok (.bool (floatTable op (toF a) (toF b))) rt
  cmp_str : ∀ ctx a b rt, om.richCompare ctx (.str a) (.str b) 2 rt = .ok (.bool (a == b)) rt
  cmp_str_ne : ∀ ctx a b rt, om.richCompare ctx (.str a) (.str b) 3 rt = .ok (.bool (a != b)) rt

theorem withDeopt_of_deopt {m g : M Unit} {s s' : St} (h : m s = .error .deopt s') :
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
  bad := notCompactInt
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
path deopts or equals the generic form, and when one fails it deopts. -/
theorem two_guard_spec (K : Kind) (fast g : M Unit) (s : St) (hs : 2 ≤ s.stack.length)
    (h : ∀ regs l r rest, K.bad r = false → K.bad l = false →
      (∃ s', fast ⟨regs, r :: l :: rest⟩ = .error .deopt s') ∨
        fast ⟨regs, r :: l :: rest⟩ = g ⟨regs, r :: l :: rest⟩) :
    withDeopt (do K.tos; K.nos; fast) g s = g s := by
  obtain ⟨regs, stack⟩ := s
  match stack, hs with
  | r :: l :: rest, _ =>
    apply withDeopt_eq
    by_cases hr : K.bad r = true
    · left
      refine ⟨⟨regs, r :: l :: rest⟩, ?_⟩
      simp [bind, EStateM.bind, K.tos_eval, hr]
    · by_cases hl : K.bad l = true
      · left
        refine ⟨⟨regs, r :: l :: rest⟩, ?_⟩
        simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl]
      · simp only [Bool.not_eq_true] at hr hl
        rcases h regs l r rest hr hl with ⟨s', hd⟩ | he
        · left
          exact ⟨s', by simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl, hd]⟩
        · right
          simp [bind, EStateM.bind, K.tos_eval, K.nos_eval, hr, hl]
          exact he

theorem notInt_false {v : Val} (h : notInt v = false) : ∃ i, v = .int i := by
  cases v <;> simp_all [notInt]

/-- A value that passes `_GUARD_TOS_INT` or `_GUARD_NOS_INT` is a compact int. -/
theorem notCompactInt_false {v : Val} (h : notCompactInt v = false) :
    ∃ i, v = .int i ∧ isCompact i = true := by
  cases v <;> simp_all [notCompactInt]

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

/-- The fast half of a `(left, right -- res)` body. -/
theorem fast_stk21 (f : List Val → BM (List Val)) (regs : Regs) (rest : List Val) (l r res : Val)
    (h : f [l, r] regs = .ok [res] regs) :
    stk 2 1 f ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, res :: rest⟩ := by
  simp [stk, popN, pushAll, bind, EStateM.bind, BM.lift, pure, EStateM.pure, h]

/-- Fail inside a `stk` body. -/
theorem stk_deopt (p q : Nat) (f : List Val → BM (List Val)) (s : St) (hp : p ≤ s.stack.length)
    (h : ∃ r', f (s.stack.take p).reverse s.regs = .error .deopt r') :
    ∃ s', stk p q f s = .error .deopt s' := by
  obtain ⟨r', hr⟩ := h
  refine ⟨⟨r', s.stack.drop p⟩, ?_⟩
  simp [stk, popN, hp, bind, EStateM.bind, BM.lift, hr]

/-- A compact fast path on two compact operands: its result is the generic one when it fits
one digit, and otherwise `EXIT_IF(PyStackRef_IsNull(res))` deopts. -/
theorem compact_fast (e : Env) (regs : Regs) (rest : List Val) (a b x : Int)
    (hg : e.om.binaryOp e.ctx e.oparg (.int a) (.int b) regs.rt = .ok (.int x) regs.rt)
    (f : List Val → BM (List Val)) (hf : f [.int a, .int b] = compactResult x) :
    (∃ s', stk 2 1 f ⟨regs, .int b :: .int a :: rest⟩ = .error .deopt s') ∨
      stk 2 1 f ⟨regs, .int b :: .int a :: rest⟩ = BINARY_OP e ⟨regs, .int b :: .int a :: rest⟩ := by
  by_cases hc : isCompact x = true
  · right
    rw [generic_binop e regs rest _ _ (.int x) hg]
    apply fast_stk21
    simp [hf, compactResult, hc, pure, EStateM.pure]
  · left
    refine stk_deopt 2 1 f _ (by simp) ⟨regs, ?_⟩
    simp [hf, compactResult, hc, throw, throwThe, MonadExcept.throw, EStateM.throw,
      MonadExceptOf.throw]

section Int
variable (e : Env) (hom : Lawful e.om) (s : St) (hs : 2 ≤ s.stack.length)
include hom hs

/-- `BINARY_OP_ADD_INT` is `BINARY_OP` for `+` and `+=`. -/
theorem binaryAddInt_spec (hop : e.oparg = 0 ∨ e.oparg = 13) :
    execOp e .BINARY_OP_ADD_INT s = execOp e .BINARY_OP s := by
  refine two_guard_spec intKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl, _⟩ := notCompactInt_false hl
  obtain ⟨b, rfl, _⟩ := notCompactInt_false hr
  exact compact_fast e regs rest a b (a + b) (hom.add_int _ _ _ _ _ hop) _ rfl

theorem binarySubInt_spec (hop : e.oparg = 10 ∨ e.oparg = 23) :
    execOp e .BINARY_OP_SUBTRACT_INT s = execOp e .BINARY_OP s := by
  refine two_guard_spec intKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl, _⟩ := notCompactInt_false hl
  obtain ⟨b, rfl, _⟩ := notCompactInt_false hr
  exact compact_fast e regs rest a b (a - b) (hom.sub_int _ _ _ _ _ hop) _ rfl

theorem binaryMulInt_spec (hop : e.oparg = 5 ∨ e.oparg = 18) :
    execOp e .BINARY_OP_MULTIPLY_INT s = execOp e .BINARY_OP s := by
  refine two_guard_spec intKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl, _⟩ := notCompactInt_false hl
  obtain ⟨b, rfl, _⟩ := notCompactInt_false hr
  exact compact_fast e regs rest a b (a * b) (hom.mul_int _ _ _ _ _ hop) _ rfl

theorem binaryAddFloat_spec (hop : e.oparg = 0 ∨ e.oparg = 13) :
    execOp e .BINARY_OP_ADD_FLOAT s = execOp e .BINARY_OP s := by
  refine two_guard_spec floatKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  rw [generic_binop e regs rest _ _ (.float (fadd a b)) (hom.add_float _ _ _ _ _ hop)]
  exact Or.inr (fast_stk21 _ regs rest _ _ _ rfl)

theorem binarySubFloat_spec (hop : e.oparg = 10 ∨ e.oparg = 23) :
    execOp e .BINARY_OP_SUBTRACT_FLOAT s = execOp e .BINARY_OP s := by
  refine two_guard_spec floatKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  rw [generic_binop e regs rest _ _ (.float (fsub a b)) (hom.sub_float _ _ _ _ _ hop)]
  exact Or.inr (fast_stk21 _ regs rest _ _ _ rfl)

theorem binaryMulFloat_spec (hop : e.oparg = 5 ∨ e.oparg = 18) :
    execOp e .BINARY_OP_MULTIPLY_FLOAT s = execOp e .BINARY_OP s := by
  refine two_guard_spec floatKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  rw [generic_binop e regs rest _ _ (.float (fmul a b)) (hom.mul_float _ _ _ _ _ hop)]
  exact Or.inr (fast_stk21 _ regs rest _ _ _ rfl)

theorem binaryAddUnicode_spec (hop : e.oparg = 0 ∨ e.oparg = 13) :
    execOp e .BINARY_OP_ADD_UNICODE s = execOp e .BINARY_OP s := by
  refine two_guard_spec strKind _ (BINARY_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notStr_false hl
  obtain ⟨b, rfl⟩ := notStr_false hr
  rw [generic_binop e regs rest _ _ (.str (a ++ b)) (hom.add_str _ _ _ _ _ hop)]
  exact Or.inr (fast_stk21 _ regs rest _ _ _ rfl)

end Int

end PyLean.Bytecode
