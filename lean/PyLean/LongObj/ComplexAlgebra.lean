import PyLean.LongObj.ComplexCore

/-!
Algebraic properties of the arithmetic in `Objects/complexobject.c`, over any
commutative ring or ordered field.

The hypotheses say that an instance's `CDouble` operations are the ring's, and
that it has no NaN or infinity. Those are properties of the *instance*, not
assumptions about inputs: each theorem then holds for all inputs of that
instance, and shows the source's branch structure computes the intended
function when the arithmetic is exact. `Rat` and `Int` satisfy the hypotheses
(`ratFieldCompat`, `intRingCompat`), so none of this is vacuous.

Binary64 is not such an instance. What these theorems do not say about
rounding, signed zeros, NaN and infinity is covered by the `Dbl` refutations in
`ComplexFindings.lean` and by the open entries that wait on `Binary64`.
-/

namespace PyLean.LongObj.Cplx

open CDouble Lean.Grind

/-- The `CDouble` operations of `R` are those of the commutative ring `R`, which
has no NaN and no infinity. -/
structure RingCompat (R : Type) [CommRing R] [CDouble R] : Prop where
  zero_eq : (CDouble.zero : R) = 0
  one_eq : (CDouble.one : R) = 1
  add_eq : ∀ x y : R, CDouble.add x y = x + y
  sub_eq : ∀ x y : R, CDouble.sub x y = x - y
  mul_eq : ∀ x y : R, CDouble.mul x y = x * y
  neg_eq : ∀ x : R, CDouble.neg x = -x
  isnan_false : ∀ x : R, isnan x = false
  isinf_false : ∀ x : R, isinf x = false

/-- `RingCompat`, for an ordered field: `div` is the field's, `==` is equality,
`>=` is total on the magnitudes `absLt`, a magnitude `<= 0` is zero, and a sum of
two squares vanishes only at zero. -/
structure FieldCompat (R : Type) [Field R] [CDouble R] : Prop extends RingCompat R where
  div_eq : ∀ x y : R, CDouble.div x y = x / y
  eq_iff : ∀ x y : R, CDouble.eq x y = true ↔ x = y
  ge_total : ∀ x y : R, ge x y = true ∨ ge y x = true
  ge_abs_zero : ∀ y : R, ge (0 : R) (absLt y) = true → y = 0
  sq_sum : ∀ x y : R, x * x + y * y = 0 → x = 0

section ring

variable {R : Type} [CommRing R] [CDouble R] (h : RingCompat R)

include h

theorem c_prod_eq (z w : Cx R) :
    c_prod z w = ⟨z.real * w.real - z.imag * w.imag, z.real * w.imag + z.imag * w.real⟩ := by
  simp [c_prod, h.isnan_false, h.mul_eq, h.add_eq, h.sub_eq]

theorem c_sum_eq (a b : Cx R) : c_sum a b = ⟨a.real + b.real, a.imag + b.imag⟩ := by
  simp [c_sum, h.add_eq]

theorem c_diff_eq (a b : Cx R) : c_diff a b = ⟨a.real - b.real, a.imag - b.imag⟩ := by
  simp [c_diff, h.sub_eq]

theorem c_1_eq : (c_1 : Cx R) = ⟨1, 0⟩ := by simp [c_1, h.one_eq, h.zero_eq]

theorem c_prod_assoc (a b c : Cx R) : c_prod (c_prod a b) c = c_prod a (c_prod b c) := by
  simp only [c_prod_eq h]
  cases a; cases b; cases c
  simp only [Cx.mk.injEq]
  constructor <;> grind

theorem c_prod_one_left (a : Cx R) : c_prod c_1 a = a := by
  simp only [c_prod_eq h, c_1_eq h]
  cases a
  simp only [Cx.mk.injEq]
  constructor <;> grind

theorem c_prod_one_right (a : Cx R) : c_prod a c_1 = a := by
  simp only [c_prod_eq h, c_1_eq h]
  cases a
  simp only [Cx.mk.injEq]
  constructor <;> grind

end ring

/-- `x ^ n`, with the complex product of the file. -/
def cxPow {R : Type} [CDouble R] (x : Cx R) : Nat → Cx R
  | 0 => c_1
  | n + 1 => c_prod (cxPow x n) x

section pow

variable {R : Type} [CommRing R] [CDouble R] (h : RingCompat R)

include h

theorem cxPow_add (x : Cx R) (m n : Nat) :
    cxPow x (m + n) = c_prod (cxPow x m) (cxPow x n) := by
  induction n with
  | zero => simp [cxPow, c_prod_one_right h]
  | succ n ih =>
    rw [← Nat.add_assoc]
    simp only [cxPow]
    rw [ih, c_prod_assoc h]

theorem cxPow_two_pow_succ (x : Cx R) (k : Nat) :
    cxPow x (2 ^ (k + 1)) = c_prod (cxPow x (2 ^ k)) (cxPow x (2 ^ k)) := by
  rw [Nat.pow_succ, Nat.mul_two, cxPow_add h]

theorem cxPow_one (x : Cx R) : cxPow x 1 = x := by
  simp [cxPow, c_prod_one_left h]

end pow

theorem wrapLong_two_pow (k : Nat) (hk : k + 1 ≤ 62) :
    wrapLong ((2 : Int) ^ k * 2) = (2 : Int) ^ (k + 1) := by
  have hle : (2 : Int) ^ (k + 1) ≤ 2 ^ 62 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hk
    exact_mod_cast this
  have hpos : (0 : Int) < 2 ^ (k + 1) := Int.pow_pos (by decide)
  have e : (2 : Int) ^ k * 2 = 2 ^ (k + 1) := by rw [Int.pow_succ]
  have m : (2 : Int) ^ (k + 1) % 2 ^ 64 = 2 ^ (k + 1) :=
    Int.emod_eq_of_lt (Int.le_of_lt hpos) (by
      have : (2 : Int) ^ 62 < 2 ^ 64 := by decide
      omega)
  have lt : ¬ (2 : Int) ^ (k + 1) ≥ 2 ^ 63 := by
    have : (2 : Int) ^ 62 < 2 ^ 63 := by decide
    omega
  simp only [wrapLong, e, m]
  rw [ite_eq_right lt]

theorem and_two_pow_ne (n k : Nat) :
    ((n &&& 2 ^ k) != 0) = n.testBit k := by
  by_cases hb : n.testBit k
  · have : (n &&& 2 ^ k) ≠ 0 := by
      intro h0
      have := Nat.testBit_and (x := n) (y := 2 ^ k) (i := k)
      rw [h0] at this
      simp [Nat.testBit_two_pow_self, hb] at this
    simp [hb, this]
  · have : (n &&& 2 ^ k) = 0 := by
      apply Nat.eq_of_testBit_eq
      intro i
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit, Bool.and_eq_false_iff]
      by_cases hi : k = i
      · subst hi; simp at hb; simp [hb]
      · right; simp [hi]
    simp [hb, this]

theorem mod_two_pow_succ' (n k : Nat) :
    n % 2 ^ (k + 1) = n % 2 ^ k + (if n.testBit k then 2 ^ k else 0) := by
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  by_cases h1 : n / 2 ^ k % 2 = 1
  · simp [h1]
  · have h0 : n / 2 ^ k % 2 = 0 := by omega
    simp [h0]

section loop

variable {R : Type} [CommRing R] [CDouble R] (h : RingCompat R)

include h

/-- The invariant of the `while` in `c_powu`: at `mask = 2^k`, `r` is `x` to the
low `k` bits of `n`, and `p` is `x^(2^k)`. It covers the wrap of `mask` at `2^63`,
where the guard is what ends the loop. -/
theorem powuLoop_spec (x : Cx R) (n : Nat) (hn : n < 2 ^ 63) :
    ∀ (fuel k : Nat) (r p : Cx R), k ≤ 62 → 62 - k < fuel →
      r = cxPow x (n % 2 ^ k) → p = cxPow x (2 ^ k) →
      powuLoop fuel ((2 : Int) ^ k) r p (n : Int) = cxPow x n := by
  intro fuel
  induction fuel with
  | zero => intro k r p _ hf; omega
  | succ fuel ih =>
    intro k r p hk hf hr hp
    have hpos : (2 : Int) ^ k > 0 := Int.pow_pos (by decide)
    by_cases hge : (n : Int) ≥ 2 ^ k
    · have hge' : 2 ^ k ≤ n := by
        have : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
        omega
      have hand : longAndNonzero (n : Int) ((2 : Int) ^ k) = n.testBit k := by
        have e : ((2 : Int) ^ k).toNat = 2 ^ k := by
          have h2 : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
          rw [← h2]; exact Int.toNat_natCast _
        simp only [longAndNonzero, Int.toNat_natCast, e]
        exact and_two_pow_ne n k
      have hr' : (if longAndNonzero (n : Int) ((2 : Int) ^ k) then c_prod r p else r)
          = cxPow x (n % 2 ^ (k + 1)) := by
        rw [hand, mod_two_pow_succ']
        by_cases hb : n.testBit k
        · simp only [hb, ite_true]
          rw [cxPow_add h, hr, hp]
        · simp [hb, hr]
      simp only [powuLoop]
      rw [ite_eq_left ⟨hpos, hge⟩]
      by_cases hk' : k + 1 ≤ 62
      · rw [wrapLong_two_pow k hk']
        exact ih (k + 1) _ _ hk' (by omega) hr' (by rw [cxPow_two_pow_succ h, hp])
      · have hk62 : k = 62 := by omega
        subst hk62
        have hw : wrapLong ((2 : Int) ^ 62 * 2) = -(2 : Int) ^ 63 := by decide
        rw [hw]
        have hmod : n % 2 ^ 63 = n := Nat.mod_eq_of_lt hn
        rw [hmod] at hr'
        cases fuel with
        | zero => simpa [powuLoop] using hr'
        | succ f =>
          have hneg : ¬ (-(2 : Int) ^ 63 > 0 ∧ (n : Int) ≥ -(2 : Int) ^ 63) := by
            intro ⟨h1, _⟩
            have : (0 : Int) < 2 ^ 63 := by decide
            omega
          simp only [powuLoop]
          rw [ite_eq_right hneg]
          exact hr'
    · have hlt : n < 2 ^ k := by
        have : ((2 ^ k : Nat) : Int) = (2 : Int) ^ k := by simp
        omega
      have hneg : ¬ ((2 : Int) ^ k > 0 ∧ (n : Int) ≥ 2 ^ k) := fun ⟨_, h2⟩ => hge h2
      simp only [powuLoop]
      rw [ite_eq_right hneg, hr, Nat.mod_eq_of_lt hlt]

end loop

/-- `c_powu x n` is the `n`-th power, for every `n` a non-negative C `long` can
hold. The hypothesis on `n` is the type of the parameter. -/
theorem c_powu_eq_pow {R : Type} [CommRing R] [CDouble R] (h : RingCompat R)
    (x : Cx R) (n : Nat) (hn : n < 2 ^ 63) : c_powu x (n : Int) = cxPow x n := by
  have := powuLoop_spec h x n hn 64 0 c_1 x (by omega) (by omega)
    (by rw [Nat.pow_zero, Nat.mod_one]; rfl) (by simp [cxPow_one h])
  simpa [c_powu] using this

section field

variable {R : Type} [Field R] [CDouble R] (h : FieldCompat R)

include h

theorem isfinite_true (x : R) : isfinite x = true := by
  simp [isfinite, h.isnan_false, h.isinf_false]

theorem absLt_eq_zero (x : R) : absLt x = 0 → x = 0 := by
  unfold absLt
  split
  · rw [h.neg_eq]; intro e; grind
  · exact id

theorem absLt_of_zero {x : R} (hx : x = 0) : absLt x = 0 := by
  simp only [absLt]
  split
  · rw [h.neg_eq, hx]; grind
  · exact hx

theorem eq_false_of_ne {x y : R} (hne : x ≠ y) : CDouble.eq x y = false := by
  cases hb : CDouble.eq x y with
  | false => rfl
  | true => exact absurd ((h.eq_iff x y).1 hb) hne

theorem sq_sum_ne (x y : R) (hne : ¬ (x = 0 ∧ y = 0)) : x * x + y * y ≠ 0 := by
  intro e
  have hx := h.sq_sum x y e
  have hy := h.sq_sum y x (by grind)
  exact hne ⟨hx, hy⟩

/-- A nonzero divisor reaches a real division branch of `_Py_c_quot`, and the
quotient times the divisor is the dividend. -/
theorem c_quot_mul (a b : Cx R) (e : Errno) (hb : ¬ (b.real = 0 ∧ b.imag = 0)) :
    (c_quot a b e).2 = e ∧ c_prod (c_quot a b e).1 b = a := by
  have hss := sq_sum_ne h b.real b.imag hb
  have hprod := c_prod_eq h.toRingCompat
  have hz : (CDouble.zero : R) = 0 := h.zero_eq
  by_cases hge : ge (absLt b.real) (absLt b.imag) = true
  · have hr : b.real ≠ 0 := by
      intro h0
      have hab : absLt b.real = 0 := absLt_of_zero h h0
      rw [hab] at hge
      exact hb ⟨h0, h.ge_abs_zero _ hge⟩
    have hab : CDouble.eq (absLt b.real) CDouble.zero = false := by
      apply eq_false_of_ne h
      intro e0
      rw [hz] at e0
      exact hr (absLt_eq_zero h _ e0)
    have hd : b.real + b.imag * (b.imag / b.real) ≠ 0 := by
      intro e0; apply hss; grind
    simp only [c_quot, hge, ite_true, hab, Bool.false_eq_true, ite_false, h.isnan_false,
      Bool.false_and, h.div_eq, h.add_eq, h.sub_eq, h.mul_eq, hprod]
    refine ⟨trivial, ?_⟩
    cases a with
    | mk ar ai =>
      simp only [Cx.mk.injEq]
      constructor <;> grind
  · have hge' : ge (absLt b.imag) (absLt b.real) = true := by
      rcases h.ge_total (absLt b.real) (absLt b.imag) with h1 | h1
      · exact absurd h1 hge
      · exact h1
    have hi : b.imag ≠ 0 := by
      intro h0
      have hab : absLt b.imag = 0 := absLt_of_zero h h0
      rw [hab] at hge'
      exact hb ⟨h.ge_abs_zero _ hge', h0⟩
    have hd : b.real * (b.real / b.imag) + b.imag ≠ 0 := by
      intro e0; apply hss; grind
    have hgf : ge (absLt b.real) (absLt b.imag) = false := by simpa using hge
    simp only [c_quot, hgf, Bool.false_eq_true, ite_false, hge', ite_true, h.isnan_false,
      Bool.false_and, h.div_eq, h.add_eq, h.sub_eq, h.mul_eq, hprod]
    refine ⟨trivial, ?_⟩
    cases a with
    | mk ar ai =>
      simp only [Cx.mk.injEq]
      constructor <;> grind

/-- A zero divisor sets `EDOM` and gives `0`, whatever the dividend. -/
theorem c_quot_zero (a b : Cx R) (e : Errno) (hb : b.real = 0 ∧ b.imag = 0) :
    c_quot a b e = (⟨0, 0⟩, Errno.edom) := by
  have hz : (CDouble.zero : R) = 0 := h.zero_eq
  have hre := absLt_of_zero h hb.1
  have him := absLt_of_zero h hb.2
  have hge : ge (0 : R) 0 = true := by
    have := (h.eq_iff (0 : R) 0).2 rfl
    simp [ge, this]
  have heq := (h.eq_iff (0 : R) 0).2 rfl
  simp only [c_quot, hre, him, hge, ite_true, hz, heq, h.isnan_false, Bool.false_and,
    Bool.false_eq_true, ite_false]

/-- `_Py_cr_quot` is `_Py_c_quot` with a real divisor, over an ordered field. -/
theorem cr_quot_eq (a : Cx R) (b : R) (e : Errno) :
    cr_quot a b e = c_quot a ⟨b, 0⟩ e := by
  by_cases hb : b = 0
  · have := c_quot_zero h a ⟨b, 0⟩ e ⟨hb, rfl⟩
    rw [this]
    have heq : CDouble.eq b CDouble.zero = true := (h.eq_iff _ _).2 (by rw [h.zero_eq]; exact hb)
    have hc : cr_quot a b e = (⟨CDouble.zero, CDouble.zero⟩, Errno.edom) := by
      simp [cr_quot, ne, heq]
    rw [hc, h.zero_eq]
  · have hne : CDouble.eq b CDouble.zero = false :=
      eq_false_of_ne h (by rw [h.zero_eq]; exact hb)
    have hq := c_quot_mul h a ⟨b, 0⟩ e (fun hh => hb hh.1)
    have hc : cr_quot a b e = (⟨a.real / b, a.imag / b⟩, e) := by
      simp [cr_quot, ne, hne, h.div_eq]
    rw [hc]
    generalize hqq : c_quot a ⟨b, 0⟩ e = q at hq
    obtain ⟨q1, q2⟩ := q
    simp only at hq
    obtain ⟨he, hm⟩ := hq
    subst he
    rw [c_prod_eq h.toRingCompat] at hm
    cases q1 with
    | mk qr qi =>
      cases a with
      | mk ar ai =>
        simp only [Cx.mk.injEq] at hm
        simp only [Prod.mk.injEq, Cx.mk.injEq, and_true]
        obtain ⟨h1, h2⟩ := hm
        constructor <;> grind

/-- `_Py_rc_quot` is `_Py_c_quot` with a real dividend, over an ordered field. -/
theorem rc_quot_eq (a : R) (b : Cx R) (e : Errno) :
    rc_quot a b e = c_quot ⟨a, 0⟩ b e := by
  have hz : (CDouble.zero : R) = 0 := h.zero_eq
  by_cases hb : b.real = 0 ∧ b.imag = 0
  · rw [c_quot_zero h _ b e hb]
    have hre := absLt_of_zero h hb.1
    have him := absLt_of_zero h hb.2
    have heq := (h.eq_iff (0 : R) 0).2 rfl
    have hge : ge (0 : R) 0 = true := by simp [ge, heq]
    simp only [rc_quot, hre, him, hge, ite_true, hz, heq, h.isnan_false, Bool.false_and,
      Bool.false_eq_true, ite_false]
  · by_cases hge : ge (absLt b.real) (absLt b.imag) = true
    · have hr : b.real ≠ 0 := by
        intro h0
        have hab : absLt b.real = 0 := absLt_of_zero h h0
        rw [hab] at hge
        exact hb ⟨h0, h.ge_abs_zero _ hge⟩
      have hab : CDouble.eq (absLt b.real) CDouble.zero = false := by
        apply eq_false_of_ne h
        intro e0
        rw [hz] at e0
        exact hr (absLt_eq_zero h _ e0)
      simp only [rc_quot, c_quot, hge, ite_true, hab, Bool.false_eq_true, ite_false,
        h.isnan_false, Bool.false_and, h.div_eq, h.add_eq, h.sub_eq, h.mul_eq, h.neg_eq, hz]
      simp only [Prod.mk.injEq, Cx.mk.injEq, and_true]
      constructor <;> grind
    · have hgf : ge (absLt b.real) (absLt b.imag) = false := by simpa using hge
      have hge' : ge (absLt b.imag) (absLt b.real) = true := by
        rcases h.ge_total (absLt b.real) (absLt b.imag) with h1 | h1
        · exact absurd h1 hge
        · exact h1
      simp only [rc_quot, c_quot, hgf, Bool.false_eq_true, ite_false, hge', ite_true,
        h.isnan_false, Bool.false_and, h.div_eq, h.add_eq, h.sub_eq, h.mul_eq, h.neg_eq, hz]
      simp only [Prod.mk.injEq, Cx.mk.injEq, and_true]
      constructor <;> grind

/-- A product of nonzero complex numbers over an ordered field is nonzero: the
norm of a product is the product of the norms. -/
theorem c_prod_ne_zero (z w : Cx R) (hz : ¬ (z.real = 0 ∧ z.imag = 0))
    (hw : ¬ (w.real = 0 ∧ w.imag = 0)) :
    ¬ ((c_prod z w).real = 0 ∧ (c_prod z w).imag = 0) := by
  rw [c_prod_eq h.toRingCompat]
  simp only
  intro ⟨h1, h2⟩
  have hn1 := sq_sum_ne h z.real z.imag hz
  have hn2 := sq_sum_ne h w.real w.imag hw
  have hmul : (z.real * z.real + z.imag * z.imag) * (w.real * w.real + w.imag * w.imag) = 0 := by
    grind
  rcases Lean.Grind.Field.of_mul_eq_zero hmul with h3 | h3
  · exact hn1 h3
  · exact hn2 h3

theorem cxPow_ne_zero (x : Cx R) (hx : ¬ (x.real = 0 ∧ x.imag = 0)) (n : Nat) :
    ¬ ((cxPow x n).real = 0 ∧ (cxPow x n).imag = 0) := by
  have hc1 := c_1_eq h.toRingCompat
  induction n with
  | zero =>
    simp only [cxPow, hc1]
    intro ⟨h1, _⟩
    exact Lean.Grind.Field.zero_ne_one h1.symm
  | succ n ih => exact c_prod_ne_zero h _ _ ih hx

end field

/-- `_Py_c_quot` and friends on `Rat`, the witness that `FieldCompat` is
satisfiable. `lt` is the order, `==` is equality. -/
instance ratCDouble : CDouble Rat where
  zero := 0
  one := 1
  hundred := 100
  inf := 0
  nan := 0
  add := (· + ·)
  sub := (· - ·)
  mul := (· * ·)
  div := (· / ·)
  neg := (- ·)
  eq x y := decide (x = y)
  lt x y := decide (x < y)
  isnan _ := false
  isinf _ := false
  copysign x _ := x
  fabs x := if x < 0 then -x else x
  floor x := x
  toLong _ := 0
  ofInt n := some (n : Rat)
  eqInt x n := decide (x = (n : Rat))

/-- Rationals with the exact operations are an instance of `FieldCompat`. -/
theorem ratFieldCompat : FieldCompat Rat where
  zero_eq := rfl
  one_eq := rfl
  add_eq _ _ := rfl
  sub_eq _ _ := rfl
  mul_eq _ _ := rfl
  neg_eq _ := rfl
  isnan_false _ := rfl
  isinf_false _ := rfl
  div_eq _ _ := rfl
  eq_iff x y := by simp [CDouble.eq]
  ge_total x y := by
    simp only [ge, CDouble.lt, CDouble.eq, Bool.or_eq_true, decide_eq_true_eq]
    grind
  ge_abs_zero y := by
    simp only [ge, absLt, CDouble.lt, CDouble.eq, CDouble.zero, CDouble.neg, Bool.or_eq_true,
      decide_eq_true_eq]
    intro hh
    by_cases hy : y < 0 <;> simp only [hy, ite_true, ite_false] at hh <;> grind
  sq_sum x y := by
    intro hh
    have sq : ∀ t : Rat, 0 ≤ t * t := by
      intro t
      rcases Rat.le_total (a := 0) (b := t) with ht | ht
      · exact Rat.mul_nonneg ht ht
      · have hn : 0 ≤ -t := by grind
        have := Rat.mul_nonneg hn hn
        grind
    have hx := sq x
    have hy := sq y
    have hxx : x * x = 0 := by grind
    rcases Rat.mul_eq_zero.1 hxx with h1 | h1 <;> exact h1

end PyLean.LongObj.Cplx
