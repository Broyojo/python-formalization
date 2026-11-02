import PyLean.Bytecode.SpecCompare
import PyLean.Bytecode.LawfulBuiltin

/-!
`COMPARE_OP_FLOAT`, `Python/bytecodes.c:3253` and `:3262-3278`.

The specialized form computes `COMPARISON_BIT(dleft, dright)`, which is 1 when either operand is
a NaN (both `>=` and `<=` are false), 2 for less, 4 for greater and 8 for equal, and tests it
against the low four bits of the oparg. That agrees with `float_richcompare` only because two
doubles that are not NaN are in exactly one of those three relations, with `-0.0 == 0.0` and
the infinities at the ends. `f64_cases` proves that of the exact binary64 model, and
`CompareFloat` then states the specialized form is `COMPARE_OP` on every stack.
-/

namespace PyLean.Bytecode

open Uop

/-- Four exclusive outcomes of comparing two doubles. -/
theorem f64_cases (x y : Binary64.F64) :
    (Binary64.F64.lt x y = false ∧ Binary64.F64.lt y x = false ∧ Binary64.F64.eq x y = false ∧ Binary64.F64.eq y x = false ∧
      (Binary64.F64.isNaN x || Binary64.F64.isNaN y) = true) ∨
    (Binary64.F64.lt x y = true ∧ Binary64.F64.lt y x = false ∧ Binary64.F64.eq x y = false ∧ Binary64.F64.eq y x = false ∧
      (Binary64.F64.isNaN x || Binary64.F64.isNaN y) = false) ∨
    (Binary64.F64.lt x y = false ∧ Binary64.F64.lt y x = false ∧ Binary64.F64.eq x y = true ∧ Binary64.F64.eq y x = true ∧
      (Binary64.F64.isNaN x || Binary64.F64.isNaN y) = false) ∨
    (Binary64.F64.lt x y = false ∧ Binary64.F64.lt y x = true ∧ Binary64.F64.eq x y = false ∧ Binary64.F64.eq y x = false ∧
      (Binary64.F64.isNaN x || Binary64.F64.isNaN y) = false) := by
  by_cases hn : (Binary64.F64.isNaN x || Binary64.F64.isNaN y) = true
  · left
    have hn' : (Binary64.F64.isNaN y || Binary64.F64.isNaN x) = true := by rw [Bool.or_comm]; exact hn
    simp [Binary64.F64.lt, Binary64.F64.eq, hn, hn']
  · have hn' : (Binary64.F64.isNaN y || Binary64.F64.isNaN x) = false := by rw [Bool.or_comm]; simpa using hn
    have hn0 : (Binary64.F64.isNaN x || Binary64.F64.isNaN y) = false := by simpa using hn
    right
    cases hxi : Binary64.F64.isInf x <;> cases hyi : Binary64.F64.isInf y <;> cases sx : Binary64.F64.sign x <;> cases sy : Binary64.F64.sign y <;>
      simp [Binary64.F64.lt, Binary64.F64.eq, hn0, hn', hxi, hyi, sx, sy]
    all_goals
      rcases Std.lt_trichotomy (Binary64.F64.toRat x) (Binary64.F64.toRat y) with h | h | h
      · have h1 : ¬ Binary64.F64.toRat y < Binary64.F64.toRat x := Std.not_gt_of_lt h
        have h2 : Binary64.F64.toRat x ≠ Binary64.F64.toRat y := Rat.ne_of_lt h
        have h3 : Binary64.F64.toRat y ≠ Binary64.F64.toRat x := fun e => h2 e.symm
        simp_all
      · simp_all [Std.lt_irrefl]
      · have h1 : ¬ Binary64.F64.toRat x < Binary64.F64.toRat y := Std.not_gt_of_lt h
        have h2 : Binary64.F64.toRat y ≠ Binary64.F64.toRat x := Rat.ne_of_lt h
        have h3 : Binary64.F64.toRat x ≠ Binary64.F64.toRat y := fun e => h2 e.symm
        simp_all


theorem cmpBit_float (x y : Binary64.F64) (n : Nat) (h : CmpArg n) :
    (comparisonBit (Binary64.F64.ge x y) (Binary64.F64.le x y) &&& n != 0) =
      floatTable (n >>> 5) x y := by
  obtain ⟨hop, hm⟩ := h
  generalize hk : n >>> 5 = op at hop hm
  have hops : op = 0 ∨ op = 1 ∨ op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5 := by omega
  rcases f64_cases x y with ⟨h1, h2, h3, h4, -⟩ | ⟨h1, h2, h3, h4, -⟩ | ⟨h1, h2, h3, h4, -⟩ |
      ⟨h1, h2, h3, h4, -⟩
  · have : comparisonBit (Binary64.F64.ge x y) (Binary64.F64.le x y) = 1 := by
      simp [comparisonBit, Binary64.F64.ge, Binary64.F64.le, h1, h2, h3, h4]
    rw [this, and_low 1 n (by decide), hm]
    rcases hops with h | h | h | h | h | h <;> subst h <;>
      simp [cmpMask, floatTable, Binary64.F64.le, Binary64.F64.ge, Binary64.F64.gt, Binary64.F64.ne,
        h1, h2, h3, h4]
  · have : comparisonBit (Binary64.F64.ge x y) (Binary64.F64.le x y) = 2 := by
      simp [comparisonBit, Binary64.F64.ge, Binary64.F64.le, h1, h2, h3, h4]
    rw [this, and_low 2 n (by decide), hm]
    rcases hops with h | h | h | h | h | h <;> subst h <;>
      simp [cmpMask, floatTable, Binary64.F64.le, Binary64.F64.ge, Binary64.F64.gt, Binary64.F64.ne,
        h1, h2, h3, h4]
  · have : comparisonBit (Binary64.F64.ge x y) (Binary64.F64.le x y) = 8 := by
      simp [comparisonBit, Binary64.F64.ge, Binary64.F64.le, h1, h2, h3, h4]
    rw [this, and_low 8 n (by decide), hm]
    rcases hops with h | h | h | h | h | h <;> subst h <;>
      simp [cmpMask, floatTable, Binary64.F64.le, Binary64.F64.ge, Binary64.F64.gt, Binary64.F64.ne,
        h1, h2, h3, h4]
  · have : comparisonBit (Binary64.F64.ge x y) (Binary64.F64.le x y) = 4 := by
      simp [comparisonBit, Binary64.F64.ge, Binary64.F64.le, h1, h2, h3, h4]
    rw [this, and_low 4 n (by decide), hm]
    rcases hops with h | h | h | h | h | h <;> subst h <;>
      simp [cmpMask, floatTable, Binary64.F64.le, Binary64.F64.ge, Binary64.F64.gt, Binary64.F64.ne,
        h1, h2, h3, h4]

theorem compare_generic_float (e : Env) (hom : Lawful e.om) (regs : Regs) (rest : List Val)
    (a b : UInt64) :
    COMPARE_OP e ⟨regs, .float b :: .float a :: rest⟩ =
      .ok () ⟨regs, .bool (floatTable (e.oparg >>> 5) (toF a) (toF b)) :: rest⟩ := by
  have hc := hom.cmp_float e.ctx a b (e.oparg >>> 5) regs.rt
  have ht := hom.true_bool e.ctx (floatTable (e.oparg >>> 5) (toF a) (toF b)) regs.rt
  by_cases h16 : (e.oparg &&& 16 != 0) = true
  · simp [COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h16, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure, hc, ht]
  · simp only [Bool.not_eq_true] at h16
    simp [COMPARE_OP, _SPECIALIZE_COMPARE_OP, _COMPARE_OP, h16, stk, popN, pushAll, bind, EStateM.bind,
      BM.lift, RM.lift, monadLift, liftM, MonadLift.monadLift, pure, EStateM.pure, hc]

/-- `COMPARE_OP_FLOAT` is `COMPARE_OP` on every stack, NaN, infinities and signed zeros included. -/
def CompareFloat : Prop := ∀ (e : Env), Lawful e.om → CmpArg e.oparg → ∀ (s : St),
  2 ≤ s.stack.length → execOp e .COMPARE_OP_FLOAT s = execOp e .COMPARE_OP s

theorem compareFloat_proven : CompareFloat := by
  intro e hom harg s hs
  refine two_guard_spec floatKind _ (COMPARE_OP e) s hs fun regs l r rest hr hl => ?_
  obtain ⟨a, rfl⟩ := notFloat_false hl
  obtain ⟨b, rfl⟩ := notFloat_false hr
  right
  rw [compare_generic_float e hom regs rest a b, ← cmpBit_float (toF a) (toF b) e.oparg harg]
  apply fast_stk21
  simp [pure, EStateM.pure]

end PyLean.Bytecode
