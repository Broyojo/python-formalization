import PyLean.Bytecode.SpecToBool

/-!
`COMPARE_OP` and its int and str specializations, `Python/bytecodes.c:3232-3318`.

The oparg packs three things: the comparison (`oparg >> 5`, `Py_LT` .. `Py_GE`), bit 16 for
"coerce the result to bool", and in the low four bits the mask of outcomes for which the
specialized forms answer `True` (`COMPARISON_BIT`, `Include/internal/pycore_code.h:523-540`).
The compiler emits that mask for the comparison (`Python/flowgraph.c`, `compare_masks`), which
is the hypothesis `CmpArg`.

Three contracts:
* With bit 16 set, `COMPARE_OP` is `COMPARE_OP` without it followed by `TO_BOOL`, whatever
  `__lt__` and `__bool__` do, raising included: the compiler fuses the two (3.13+).
* `COMPARE_OP_INT` is `COMPARE_OP` on every stack, given `long_richcompare`.
* `COMPARE_OP_STR` is `COMPARE_OP` for `==` and `!=` on every stack, given `unicode_compare_eq`.

`COMPARE_OP_FLOAT` is not stated: its model compares with Lean's `Float`, which a proof cannot
evaluate, and needs moving to `Binary64` first.
-/

namespace PyLean.Bytecode

open Uop

/-- `COMPARISON_LESS_THAN = 2`, `GREATER_THAN = 4`, `EQUALS = 8`, `UNORDERED = 1`, combined per
comparison as `compare_masks` does. -/
def cmpMask : Nat → Nat
  | 0 => 2 | 1 => 10 | 2 => 8 | 3 => 7 | 4 => 4 | _ => 12

/-- The comparison operand the compiler emits. -/
def CmpArg (n : Nat) : Prop := n >>> 5 < 6 ∧ n &&& 15 = cmpMask (n >>> 5)

/-- What `Py_LT` .. `Py_GE` mean on a total order. -/
def cmpInt (op : Nat) (a b : Int) : Bool :=
  match op with
  | 0 => decide (a < b) | 1 => decide (a ≤ b) | 2 => decide (a = b)
  | 3 => decide (a ≠ b) | 4 => decide (a > b) | _ => decide (a ≥ b)

theorem and_low (x n : Nat) (hx : x &&& 15 = x) : x &&& n = x &&& (n &&& 15) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := congrArg (fun y => y.testBit i) hx
  simp only [Nat.testBit_and] at this ⊢
  cases hxi : x.testBit i <;> simp_all

theorem cmpBit_int (a b : Int) (n : Nat) (h : CmpArg n) :
    (comparisonBit (decide (a ≥ b)) (decide (a ≤ b)) &&& n != 0) = cmpInt (n >>> 5) a b := by
  obtain ⟨hop, hm⟩ := h
  generalize hk : n >>> 5 = op at hop hm
  rcases Int.lt_trichotomy a b with hab | hab | hab
  · have : comparisonBit (decide (a ≥ b)) (decide (a ≤ b)) = 2 := by
      simp [comparisonBit, show ¬ a ≥ b by omega, show a ≤ b by omega]
    rw [this, and_low 2 n (by decide), hm]
    obtain h | h | h | h | h | h : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 := by omega
    all_goals subst h; simp [cmpMask, cmpInt]; omega
  · subst hab
    have : comparisonBit (decide (a ≥ a)) (decide (a ≤ a)) = 8 := by simp [comparisonBit]
    rw [this, and_low 8 n (by decide), hm]
    obtain h | h | h | h | h | h : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 := by omega
    all_goals subst h; simp [cmpMask, cmpInt]
  · have : comparisonBit (decide (a ≥ b)) (decide (a ≤ b)) = 4 := by
      simp [comparisonBit, show a ≥ b by omega, show ¬ a ≤ b by omega]
    rw [this, and_low 4 n (by decide), hm]
    obtain h | h | h | h | h | h : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 := by omega
    all_goals subst h; simp [cmpMask, cmpInt]; omega

/-- With bit 16 set, `COMPARE_OP` is the comparison without it followed by `TO_BOOL`, on every
stack and for every object model, the failure of either step included. -/
def CompareFused : Prop := ∀ (e₀ e₁ : Env) (regs : Regs) (l r : Val) (rest : List Val),
  e₁.oparg >>> 5 = e₀.oparg >>> 5 → e₁.oparg &&& 16 ≠ 0 → e₀.oparg &&& 16 = 0 →
  e₁.om = e₀.om → e₁.ctx = e₀.ctx →
    execOp e₁ .COMPARE_OP ⟨regs, r :: l :: rest⟩ =
      (execOp e₀ .COMPARE_OP *> execOp e₀ .TO_BOOL) ⟨regs, r :: l :: rest⟩

theorem compareFused_proven : CompareFused := by
  intro e₀ e₁ regs l r rest hop h1 h0 hom hctx
  have hb1 : (e₁.oparg &&& 16 != 0) = true := by simpa using h1
  have hb0 : (e₀.oparg &&& 16 != 0) = false := by simpa using h0
  simp only [execOp, COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, SeqRight.seqRight,
    EStateM.seqRight, stk, popN, bind, EStateM.bind, BM.lift, RM.lift, monadLift, liftM,
    MonadLift.monadLift, pure, EStateM.pure, hop, hb1, hb0, hom, hctx]
  simp only [List.length_cons, Nat.le_add_left, ite_true, List.take, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.drop]
  cases hc : e₀.om.richCompare e₀.ctx l r (e₀.oparg >>> 5) regs.rt with
  | error x rt => simp [hc, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure]
  | ok res rt =>
    cases ht : e₀.om.isTrue e₀.ctx res rt with
    | ok b rt' =>
      simp [hc, ht, TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure]
    | error x rt' =>
      simp [hc, ht, TO_BOOL, _SPECIALIZE_TO_BOOL, _TO_BOOL, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure]

/-- Generic `COMPARE_OP` on two ints with the builtin `long_richcompare`. -/
theorem compare_generic_int (e : Env) (hom : Lawful e.om) (regs : Regs) (rest : List Val)
    (a b : Int) (h : CmpArg e.oparg) :
    COMPARE_OP e ⟨regs, .int b :: .int a :: rest⟩ =
      .ok () ⟨regs, .bool (cmpInt (e.oparg >>> 5) a b) :: rest⟩ := by
  have hc : e.om.richCompare e.ctx (.int a) (.int b) (e.oparg >>> 5) regs.rt =
      .ok (.bool (cmpInt (e.oparg >>> 5) a b)) regs.rt := hom.cmp_int e.ctx a b (e.oparg >>> 5) regs.rt h.1
  have ht := hom.true_bool e.ctx (cmpInt (e.oparg >>> 5) a b) regs.rt
  by_cases h16 : (e.oparg &&& 16 != 0) = true
  · simp [COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h16, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure, hc, ht]
  · simp only [Bool.not_eq_true] at h16
    simp [COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h16, stk, popN, pushAll, bind, EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure, hc]

/-- `COMPARE_OP_INT` is `COMPARE_OP` on every stack. -/
def CompareInt : Prop := ∀ (e : Env), Lawful e.om → CmpArg e.oparg → ∀ (s : St),
  2 ≤ s.stack.length → execOp e .COMPARE_OP_INT s = execOp e .COMPARE_OP s

theorem compareInt_proven : CompareInt := by
  intro e hom harg s hs
  refine two_guard_spec intKind _ (COMPARE_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl, ha⟩ := notCompactInt_false hl
  obtain ⟨b, rfl, hb⟩ := notCompactInt_false hr
  right
  rw [compare_generic_int e hom regs rest a b harg, ← cmpBit_int a b e.oparg harg]
  apply fast_stk21
  simp [ha, hb, pure, EStateM.pure]

/-- `COMPARE_OP_STR` is `COMPARE_OP` for `==` and `!=` on every stack. Only those two are
specialized (`_Py_Specialize_CompareOp`), with their masks. -/
def CompareStr : Prop := ∀ (e : Env), Lawful e.om →
  ((e.oparg >>> 5 = 2 ∧ e.oparg &&& 15 = 8) ∨ (e.oparg >>> 5 = 3 ∧ e.oparg &&& 15 = 7)) →
  ∀ (s : St), 2 ≤ s.stack.length → execOp e .COMPARE_OP_STR s = execOp e .COMPARE_OP s

theorem compareStr_proven : CompareStr := by
  intro e hom harg s hs
  refine two_guard_spec strKind _ (COMPARE_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notStr_false hl
  obtain ⟨b, rfl⟩ := notStr_false hr
  right
  have key : ∀ res : Bool,
      COMPARE_OP e ⟨regs, .str b :: .str a :: rest⟩ = .ok () ⟨regs, .bool res :: rest⟩ →
      _COMPARE_OP_STR e ⟨regs, .str b :: .str a :: rest⟩ = .ok () ⟨regs, .bool res :: rest⟩ →
      _COMPARE_OP_STR e ⟨regs, .str b :: .str a :: rest⟩ = COMPARE_OP e ⟨regs, .str b :: .str a :: rest⟩ :=
    fun res h1 h2 => h2.trans h1.symm
  rcases harg with ⟨hop, hm⟩ | ⟨hop, hm⟩
  · have hc := hom.cmp_str e.ctx a b regs.rt
    have ht := hom.true_bool e.ctx (a == b) regs.rt
    refine key (a == b) ?_ ?_
    · by_cases h16 : (e.oparg &&& 16 != 0) = true <;>
      simp_all [COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, stk, popN, pushAll, bind,
        EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure]
    · apply fast_stk21
      by_cases hab : a = b
      · simp [hab, pure, EStateM.pure, and_low 8 e.oparg (by decide), hm]
      · simp [hab, pure, EStateM.pure, and_low 7 e.oparg (by decide), hm]
  · have hc := hom.cmp_str_ne e.ctx a b regs.rt
    have ht := hom.true_bool e.ctx (a != b) regs.rt
    refine key (a != b) ?_ ?_
    · by_cases h16 : (e.oparg &&& 16 != 0) = true <;>
      simp_all [COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, stk, popN, pushAll, bind,
        EStateM.bind, BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure]
    · apply fast_stk21
      by_cases hab : a = b
      · simp [hab, pure, EStateM.pure, and_low 8 e.oparg (by decide), hm]
      · simp [hab, pure, EStateM.pure, and_low 7 e.oparg (by decide), hm]

/-! ## `IS_OP` -/

/-- The bool `IS_OP oparg` pushes for an identity answer `b`: `Py_Is(left, right) ^ oparg`. -/
def isOpResult (oparg : Nat) (b : Bool) : Val := .bool (((if b then 1 else 0) ^^^ oparg) != 0)

/-- `IS_OP oparg` (`Python/bytecodes.c:3320-3328`, `_IS_OP + POP_TOP + POP_TOP`) replaces both
operands by `Py_Is(left, right) ^ oparg` as a bool, for any two values, calling nothing. Identity
is not value equality: two heap objects are one object exactly when they share an address (two
equal lists are not); values that differ are never one object (`1 is 1.0`, `1 is True` are
false); equal singletons (`None`, `True`, a builtin type) always are; for two equal ints, floats,
strs or bytes the answer is the runtime's `sameImmediate`, since CPython's answer there depends on
where each object came from (`x = 10**20; x is 10**20` is false, `y = x; x is y` true). -/
def IsOpRules : Prop := ∀ (e : Env) (regs : Regs) (l r : Val) (rest : List Val),
  (∀ a b, l = .ref a → r = .ref b →
    execOp e .IS_OP ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, isOpResult e.oparg (a == b) :: rest⟩) ∧
  (l ≠ r → execOp e .IS_OP ⟨regs, r :: l :: rest⟩ = .ok () ⟨regs, isOpResult e.oparg false :: rest⟩) ∧
  (singletonVal l = true →
    execOp e .IS_OP ⟨regs, l :: l :: rest⟩ = .ok () ⟨regs, isOpResult e.oparg true :: rest⟩) ∧
  ((∃ i, l = .int i) ∨ (∃ x, l = .float x) ∨ (∃ t, l = .str t) ∨ (∃ b, l = .bytes b) →
    execOp e .IS_OP ⟨regs, l :: l :: rest⟩ = .ok () ⟨regs, isOpResult e.oparg (regs.rt.sameImmediate l l) :: rest⟩)

theorem isOpRules_proven : IsOpRules := by
  intro e regs l r rest
  refine ⟨fun a b hl hr => ?_, fun hne => ?_, fun hs => ?_, fun hi => ?_⟩
  · subst hl hr
    simp [execOp, IS_OP, getRt, stk, popN, pushAll, pyIs, isOpResult, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure]
  · have hb : pyIs regs.rt l r = false := by
      unfold pyIs; split
      · rename_i a b; simp only [beq_eq_false_iff_ne]; intro h; exact hne (by subst h; rfl)
      · simp [hne]
    simp [execOp, IS_OP, getRt, stk, popN, pushAll, hb, isOpResult, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure]
  · have hb : pyIs regs.rt l l = true := by
      unfold pyIs; split
      · simp
      · simp [hs]
    simp [execOp, IS_OP, getRt, stk, popN, pushAll, hb, isOpResult, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure]
  · have hb : pyIs regs.rt l l = regs.rt.sameImmediate l l := by
      rcases hi with ⟨i, rfl⟩ | ⟨x, rfl⟩ | ⟨t, rfl⟩ | ⟨b, rfl⟩ <;> simp [pyIs, singletonVal]
    simp [execOp, IS_OP, getRt, stk, popN, pushAll, hb, isOpResult, bind, EStateM.bind, BM.lift, RM.lift, liftM,
      monadLift, MonadLift.monadLift, pure, EStateM.pure]

end PyLean.Bytecode
