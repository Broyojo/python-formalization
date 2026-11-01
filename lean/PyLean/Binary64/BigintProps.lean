import PyLean.Binary64.Bigint

/-!
The limb arithmetic of `Python/dtoa.c` computes what its comments say. `Bigint.val` reads
a limb list as a number; each theorem relates a C loop to that number.
-/

namespace PyLean.Binary64

open Bigint

theorem limbsVal_nil : limbsVal [] = 0 := rfl

theorem limbsVal_cons (d : Nat) (ds : List Nat) : limbsVal (d :: ds) = d + 2 ^ 32 * limbsVal ds := rfl

/-- The `multadd` loop computes `b * m + a`. -/
theorem multaddLoop_val (m : Nat) : ∀ (x : List Nat) (c : Nat),
    limbsVal (multaddLoop m x c) = limbsVal x * m + c := by
  intro x
  induction x with
  | nil =>
    intro c
    by_cases h : c = 0
    · simp [multaddLoop, h, limbsVal]
    · simp [multaddLoop, h, limbsVal]
  | cons d ds ih =>
    intro c
    simp only [multaddLoop, limbsVal_cons, ih, Nat.add_mul, Nat.mul_assoc]
    omega

/-- `multadd(b, m, a)` is `b * m + a`. -/
def MultaddValue : Prop := ∀ (b : Bigint) (m a : Nat), (multadd b m a).val = b.val * m + a

theorem multaddValue_proven : MultaddValue := fun b m a => multaddLoop_val m b.x a

theorem multadd_val (b : Bigint) (m a : Nat) : (multadd b m a).val = b.val * m + a :=
  multaddLoop_val m b.x a

/-- The decimal value of digits `i, i + 1, ...`, appended to `v`. -/
def decAppend (dig : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, v => v
  | n + 1, i, v => decAppend dig n (i + 1) (v * 10 + dig i)

theorem s2bLoop_val (dig : Nat → Nat) : ∀ (n i : Nat) (b : Bigint),
    (s2bLoop dig n i b).val = decAppend dig n i b.val := by
  intro n
  induction n with
  | zero => intro i b; rfl
  | succ n ih =>
    intro i b
    simp only [s2bLoop, decAppend, ih, multadd_val]

/-- `s2b` appends the digits past the ninth to `y9`, as decimal digits, and `i2b` holds
its argument. -/
def S2bValue : Prop :=
  (∀ (dig : Nat → Nat) (nd y9 : Nat), y9 < 2 ^ 32 →
    (s2b dig nd y9).val = if nd ≤ 9 then y9 else decAppend dig (nd - 9) 9 y9) ∧
  (∀ i : Nat, (i2b i).val = i)

theorem s2bValue_proven : S2bValue := by
  constructor
  · intro dig nd y9 _
    unfold s2b
    split
    · simp [Bigint.val, limbsVal]
    · rw [s2bLoop_val]; simp [Bigint.val, limbsVal]
  · intro i; simp [i2b, Bigint.val, limbsVal]

/-! ## Bit counting -/

/-- `x &&& (2 ^ n - 2 ^ k)` clears the bits below `k`, for `x < 2 ^ n` and `k ≤ n`. -/
theorem land_high_mask {x n k : Nat} (hx : x < 2 ^ n) (hk : k ≤ n) :
    x &&& (2 ^ n - 2 ^ k) = x / 2 ^ k * 2 ^ k := by
  have h1 : (2 ^ n - 2 ^ k) = (2 ^ (n - k) - 1) * 2 ^ k := by
    rw [Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hk]; simp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, h1, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases hi : k ≤ i
  · have e : i - k + k = i := by omega
    simp only [hi, decide_true, Bool.true_and, e]
    by_cases hin : i < n
    · have : i - k < n - k := by omega
      simp [this]
    · have h2 : x.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega)))
      have : ¬ i - k < n - k := by omega
      simp [h2, this]
  · simp [hi]

theorem mask_zero_iff {x n k : Nat} (hx : x < 2 ^ n) (hk : k ≤ n) :
    (x &&& (2 ^ n - 2 ^ k) == 0) = decide (x < 2 ^ k) := by
  rw [land_high_mask hx hk]
  have hp : 0 < 2 ^ k := Nat.two_pow_pos k
  by_cases h : x < 2 ^ k
  · simp [h, Nat.div_eq_of_lt h]
  · have h1 : 1 ≤ x / 2 ^ k := (Nat.le_div_iff_mul_le hp).2 (by omega)
    have h2 : 0 < x / 2 ^ k * 2 ^ k := Nat.mul_pos h1 hp
    simp [h]; omega

theorem hiStep_ok {x k y a s mask : Nat} (hm : mask = 2 ^ 32 - 2 ^ (a + s)) (hs : a + 2 * s ≤ 32)
    (hy : y = x * 2 ^ k) (h1 : y < 2 ^ 32) (h2 : 2 ^ a ≤ y) :
    (hiStep mask s (k, y)).2 = x * 2 ^ (hiStep mask s (k, y)).1 ∧ (hiStep mask s (k, y)).2 < 2 ^ 32 ∧
      2 ^ (a + s) ≤ (hiStep mask s (k, y)).2 := by
  have hz := mask_zero_iff (x := y) (n := 32) (k := a + s) h1 (by omega)
  rw [← hm] at hz
  unfold hiStep
  simp only [hz, decide_eq_true_eq]
  by_cases hc : y < 2 ^ (a + s)
  · simp only [hc, ↓reduceIte]
    have hlt : y * 2 ^ s < 2 ^ 32 := by
      calc y * 2 ^ s < 2 ^ (a + s) * 2 ^ s := Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos s)
        _ = 2 ^ (a + s + s) := by rw [Nat.pow_add 2 (a + s) s]
        _ ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) (by omega)
    have hsh : shl32 y s = y * 2 ^ s := Nat.mod_eq_of_lt hlt
    rw [hsh]
    refine ⟨by rw [hy, Nat.pow_add, Nat.mul_assoc], hlt, ?_⟩
    rw [Nat.pow_add]
    exact Nat.mul_le_mul_right _ h2
  · simp only [hc, ↓reduceIte]
    exact ⟨hy, h1, by omega⟩

/-- `hi0bits(x)` counts the leading zero bits of a 32-bit `x`. -/
def Hi0bitsSpec : Prop :=
  hi0bits 0 = 32 ∧
    ∀ x, 0 < x → x < 2 ^ 32 → hi0bits x < 32 ∧ 2 ^ 31 ≤ x * 2 ^ hi0bits x ∧ x * 2 ^ hi0bits x < 2 ^ 32

theorem hi0bitsSpec_proven : Hi0bitsSpec := by
  refine ⟨by decide, ?_⟩
  intro x h0 hx
  have hdef : hi0bits x = (fun st : Nat × Nat =>
      if st.2 &&& 0x80000000 == 0 then (if st.2 &&& 0x40000000 == 0 then 32 else st.1 + 1) else st.1)
      (hiStep 0xc0000000 2 (hiStep 0xf0000000 4 (hiStep 0xff000000 8 (hiStep 0xffff0000 16 (0, x))))) := rfl
  rw [hdef]
  obtain ⟨a1, a2, a3⟩ := hiStep_ok (x := x) (k := 0) (y := x) (a := 0) (s := 16) (mask := 0xffff0000)
    (by decide) (by decide) (by simp) hx (by omega)
  generalize hiStep 0xffff0000 16 (0, x) = st1 at *
  obtain ⟨k1, y1⟩ := st1
  obtain ⟨b1, b2, b3⟩ := hiStep_ok (x := x) (k := k1) (y := y1) (a := 16) (s := 8) (mask := 0xff000000)
    (by decide) (by decide) a1 a2 (by simpa using a3)
  generalize hiStep 0xff000000 8 (k1, y1) = st2 at *
  obtain ⟨k2, y2⟩ := st2
  obtain ⟨c1, c2, c3⟩ := hiStep_ok (x := x) (k := k2) (y := y2) (a := 24) (s := 4) (mask := 0xf0000000)
    (by decide) (by decide) b1 b2 (by simpa using b3)
  generalize hiStep 0xf0000000 4 (k2, y2) = st3 at *
  obtain ⟨k3, y3⟩ := st3
  obtain ⟨d1, d2, d3⟩ := hiStep_ok (x := x) (k := k3) (y := y3) (a := 28) (s := 2) (mask := 0xc0000000)
    (by decide) (by decide) c1 c2 (by simpa using c3)
  generalize hiStep 0xc0000000 2 (k3, y3) = st4 at *
  obtain ⟨k4, y4⟩ := st4
  simp only [] at d1 d2 d3 ⊢
  have d3' : 2 ^ 30 ≤ y4 := by simpa using d3
  have e5 := mask_zero_iff (x := y4) (n := 32) (k := 31) d2 (by omega)
  have l5 : (2 ^ 32 - 2 ^ 31 : Nat) = 0x80000000 := by decide
  rw [l5] at e5
  have hpow : ∀ k, x * 2 ^ k < 2 ^ 32 → k < 32 := by
    intro k hk
    have h1 : 2 ^ k ≤ x * 2 ^ k := Nat.le_mul_of_pos_left _ h0
    exact (Nat.pow_lt_pow_iff_right (by omega)).1 (Nat.lt_of_le_of_lt h1 hk)
  rw [e5]
  by_cases h : y4 < 2 ^ 31
  · have e6 := mask_zero_iff (x := y4) (n := 31) (k := 30) h (by omega)
    have l6 : (2 ^ 31 - 2 ^ 30 : Nat) = 0x40000000 := by decide
    rw [l6] at e6
    have h30 : ¬ y4 < 2 ^ 30 := by omega
    simp only [h, decide_true, ↓reduceIte, e6, h30, decide_false, Bool.false_eq_true]
    have e7 : x * 2 ^ (k4 + 1) = 2 * y4 := by rw [Nat.pow_succ, ← Nat.mul_assoc, ← d1]; omega
    rw [e7]
    refine ⟨hpow _ (by omega), by omega, by omega⟩
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    rw [← d1]
    exact ⟨hpow _ (by omega), by omega, d2⟩

theorem loStep_ok {x k y s mask : Nat} (hm : mask = 2 ^ s - 1) (hy : y * 2 ^ k = x)
    (hnz : y % 2 ^ (2 * s) ≠ 0) :
    (loStep mask s (k, y)).2 * 2 ^ (loStep mask s (k, y)).1 = x ∧ (loStep mask s (k, y)).2 % 2 ^ s ≠ 0 := by
  unfold loStep
  simp only [hm, Nat.and_two_pow_sub_one_eq_mod]
  by_cases hc : y % 2 ^ s = 0
  · simp only [hc, beq_self_eq_true, ↓reduceIte]
    have hd : 2 ^ s ∣ y := Nat.dvd_of_mod_eq_zero hc
    obtain ⟨q, rfl⟩ := hd
    have hp : 0 < 2 ^ s := Nat.two_pow_pos s
    rw [Nat.mul_div_cancel_left _ hp]
    constructor
    · rw [← hy, Nat.pow_add]; grind
    · intro hq
      apply hnz
      obtain ⟨t, rfl⟩ := Nat.dvd_of_mod_eq_zero hq
      have : 2 ^ (2 * s) = 2 ^ s * 2 ^ s := by rw [Nat.two_mul, Nat.pow_add]
      rw [this, ← Nat.mul_assoc]
      exact Nat.mul_mod_right _ _
  · have : (y % 2 ^ s == 0) = false := by simpa using hc
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hy, hc⟩

/-- `lo0bits(&y)` strips the trailing zero bits of a nonzero 32-bit `y` and counts them,
and reports 32 for zero. -/
def Lo0bitsSpec : Prop :=
  (lo0bits 0).1 = 32 ∧ ∀ y, 0 < y → y < 2 ^ 32 →
    (lo0bits y).2 * 2 ^ (lo0bits y).1 = y ∧ (lo0bits y).2 % 2 = 1 ∧ (lo0bits y).1 < 32

theorem lo0bitsSpec_proven : Lo0bitsSpec := by
  refine ⟨by decide, ?_⟩
  intro y h0 hy
  have hbit : ∀ r : Nat, r * 2 ^ 0 = y → r = y := by intro r h; simpa using h
  have hcount : ∀ r k, 0 < r → r * 2 ^ k = y → k < 32 := by
    intro r k hr hk
    have h1 : 2 ^ k ≤ r * 2 ^ k := Nat.le_mul_of_pos_left _ hr
    exact (Nat.pow_lt_pow_iff_right (a := 2) (by omega)).1 (Nat.lt_of_le_of_lt h1 (by omega))
  unfold lo0bits
  simp only []
  have m7 : y &&& 7 = y % 8 := Nat.and_two_pow_sub_one_eq_mod y 3
  have m1 : y &&& 1 = y % 2 := Nat.and_two_pow_sub_one_eq_mod y 1
  have m2 : y &&& 2 = 2 * (y / 2 % 2) := by
    have hle : y &&& 2 ≤ 2 := Nat.and_le_right
    have e' : (y &&& 2) % 4 = (y % 4) &&& 2 := by
      have := Nat.and_mod_two_pow (a := y) (b := 2) (n := 2)
      simpa using this
    have hc : y % 4 = 0 ∨ y % 4 = 1 ∨ y % 4 = 2 ∨ y % 4 = 3 := by omega
    rcases hc with h | h | h | h
    · rw [h, show ((0 : Nat) &&& 2) = 0 from rfl] at e'; omega
    · rw [h, show ((1 : Nat) &&& 2) = 0 from rfl] at e'; omega
    · rw [h, show ((2 : Nat) &&& 2) = 2 from rfl] at e'; omega
    · rw [h, show ((3 : Nat) &&& 2) = 2 from rfl] at e'; omega
  rw [m7, m1, m2]
  by_cases c7 : y % 8 = 0
  · have c7' : (y % 8 != 0) = false := by simpa using c7
    simp only [c7', Bool.false_eq_true, ↓reduceIte]
    obtain ⟨a1, a2⟩ := loStep_ok (x := y) (k := 0) (y := y) (s := 16) (mask := 0xffff)
      (by decide) (by simp) (by
        have : y % 2 ^ (2 * 16) = y := Nat.mod_eq_of_lt hy
        rw [this]; omega)
    generalize loStep 0xffff 16 (0, y) = st1 at *
    obtain ⟨k1, y1⟩ := st1
    obtain ⟨b1, b2⟩ := loStep_ok (x := y) (k := k1) (y := y1) (s := 8) (mask := 0xff) (by decide) a1 a2
    generalize loStep 0xff 8 (k1, y1) = st2 at *
    obtain ⟨k2, y2⟩ := st2
    obtain ⟨c1, c2⟩ := loStep_ok (x := y) (k := k2) (y := y2) (s := 4) (mask := 0xf) (by decide) b1 b2
    generalize loStep 0xf 4 (k2, y2) = st3 at *
    obtain ⟨k3, y3⟩ := st3
    obtain ⟨d1, d2⟩ := loStep_ok (x := y) (k := k3) (y := y3) (s := 2) (mask := 0x3) (by decide) c1 c2
    generalize loStep 0x3 2 (k3, y3) = st4 at *
    obtain ⟨k4, y4⟩ := st4
    simp only [] at d1 d2 ⊢
    have d2' : y4 % 4 ≠ 0 := by simpa using d2
    have m1' : y4 &&& 1 = y4 % 2 := Nat.and_two_pow_sub_one_eq_mod y4 1
    rw [m1']
    by_cases ce : y4 % 2 = 0
    · have hx5 : y4 / 2 ≠ 0 := by omega
      simp only [ce, beq_self_eq_true, ↓reduceIte]
      have : (y4 / 2 == 0) = false := by simpa using hx5
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have hv : y4 / 2 * 2 ^ (k4 + 1) = y := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k4), ← Nat.mul_assoc]
        have : y4 / 2 * 2 = y4 := by omega
        rw [this, d1]
      exact ⟨hv, by omega, hcount _ _ (by omega) hv⟩
    · have : (y4 % 2 == 0) = false := by simpa using ce
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact ⟨d1, by omega, hcount _ _ (by omega) d1⟩
  · have c7' : (y % 8 != 0) = true := by simpa using c7
    simp only [c7', ↓reduceIte]
    by_cases c1 : y % 2 = 0
    · have c1' : (y % 2 != 0) = false := by simpa using c1
      simp only [c1', Bool.false_eq_true, ↓reduceIte]
      by_cases c2 : y / 2 % 2 = 0
      · have c2' : (2 * (y / 2 % 2) != 0) = false := by simp [c2]
        simp only [c2', Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, by omega, by omega⟩
      · have c2' : (2 * (y / 2 % 2) != 0) = true := by simp; omega
        simp only [c2', ↓reduceIte]
        refine ⟨by omega, by omega, by omega⟩
    · have c1' : (y % 2 != 0) = true := by simpa using c1
      simp only [c1', ↓reduceIte]
      refine ⟨by simp, by omega, by omega⟩

/-! ## Multiplication -/

theorem limbsVal_append_zero (l : List Nat) (k : Nat) :
    limbsVal (l ++ List.replicate k 0) = limbsVal l := by
  induction l with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [List.nil_append, List.replicate_succ, limbsVal_cons, limbsVal_nil] at ih ⊢; omega
  | cons d ds ih => simp only [List.cons_append, limbsVal_cons, ih]

theorem limbsVal_append (l r : List Nat) :
    limbsVal (l ++ r) = limbsVal l + 2 ^ (32 * l.length) * limbsVal r := by
  induction l with
  | nil => simp [limbsVal]
  | cons d ds ih =>
    simp only [List.cons_append, limbsVal_cons, ih, List.length_cons]
    have : 2 ^ (32 * (ds.length + 1)) = 2 ^ 32 * 2 ^ (32 * ds.length) := by
      rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
    rw [this]
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

/-- The inner loop of `mult`: `xc` gains `y * xa`, with the carry in the slot past `xa`. -/
theorem multInner_shape (y : Nat) : ∀ (xa pre z : List Nat) (c : Nat), pre.length = xa.length →
    ∃ pre' c', multInner y xa (pre ++ 0 :: z) c = pre' ++ c' :: z ∧ pre'.length = xa.length ∧
      limbsVal (pre' ++ c' :: z) = limbsVal (pre ++ 0 :: z) + y * limbsVal xa + c := by
  intro xa
  induction xa with
  | nil =>
    intro pre z c h
    have : pre = [] := List.length_eq_zero_iff.1 (by simpa using h)
    subst this
    refine ⟨[], c, by simp [multInner], rfl, ?_⟩
    simp [limbsVal]; omega
  | cons a as ih =>
    intro pre z c h
    cases pre with
    | nil => simp at h
    | cons p ps =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      obtain ⟨pre', c', e1, e2, e3⟩ := ih ps z ((a * y + p + c) / 2 ^ 32) h
      refine ⟨((a * y + p + c) % 2 ^ 32) :: pre', c', ?_, by simp [e2], ?_⟩
      · simp only [List.cons_append, multInner, e1]
      · simp only [List.cons_append, limbsVal_cons, e3, limbsVal_cons]
        simp only [Nat.mul_add, Nat.mul_left_comm (2 ^ 32) y, Nat.mul_comm a y]
        omega

theorem multOuter_val (xa : List Nat) (hxa : xa ≠ []) : ∀ (ys pre : List Nat) (k : Nat),
    pre.length = xa.length → ys.length ≤ k + 1 →
    limbsVal (multOuter xa ys (pre ++ List.replicate (k + 1) 0)) =
      limbsVal pre + limbsVal xa * limbsVal ys := by
  intro ys
  induction ys with
  | nil =>
    intro pre k _ _
    simp [multOuter, limbsVal_append_zero, limbsVal]
  | cons y ys ih =>
    intro pre k hl hk
    have hrep : List.replicate (k + 1) 0 = 0 :: List.replicate k 0 := rfl
    have step : ∃ pre' c', (if y != 0 then multInner y xa (pre ++ 0 :: List.replicate k 0) 0
        else pre ++ 0 :: List.replicate k 0) = pre' ++ c' :: List.replicate k 0 ∧
        pre'.length = xa.length ∧
        limbsVal (pre' ++ c' :: List.replicate k 0) = limbsVal pre + y * limbsVal xa := by
      by_cases hy : y = 0
      · subst hy
        refine ⟨pre, 0, by simp, hl, ?_⟩
        have : pre ++ 0 :: List.replicate k 0 = pre ++ List.replicate (k + 1) 0 := rfl
        rw [this, limbsVal_append_zero]; simp
      · obtain ⟨pre', c', e1, e2, e3⟩ := multInner_shape y xa pre (List.replicate k 0) 0 hl
        refine ⟨pre', c', by simp [hy, e1], e2, ?_⟩
        have : pre ++ 0 :: List.replicate k 0 = pre ++ List.replicate (k + 1) 0 := rfl
        rw [e3, this, limbsVal_append_zero]; simp
    obtain ⟨pre', c', e1, e2, e3⟩ := step
    rw [hrep]
    simp only [multOuter, e1]
    cases pre' with
    | nil =>
      exfalso; apply hxa; exact List.length_eq_zero_iff.1 (by simpa using e2.symm)
    | cons p ps =>
      simp only [List.cons_append]
      have hlen : (ps ++ [c']).length = xa.length := by simpa using e2
      have hv : limbsVal (p :: (ps ++ [c'])) + 0 = limbsVal pre + y * limbsVal xa := by
        have := e3
        have ee : (p :: ps) ++ c' :: List.replicate k 0 = (p :: (ps ++ [c'])) ++ List.replicate k 0 := by simp
        rw [ee, limbsVal_append_zero] at this
        simpa using this
      cases k with
      | zero =>
        have hys : ys = [] := List.length_eq_zero_iff.1 (by simpa using hk)
        subst hys
        simp only [multOuter, List.replicate_zero, limbsVal_cons, limbsVal_nil, Nat.mul_zero, Nat.add_zero]
        have h2 := hv
        simp only [limbsVal_cons] at h2
        simp only [Nat.add_zero] at h2
        have h3 : limbsVal (ps ++ [c']) = limbsVal (ps ++ c' :: []) := rfl
        grind
      | succ k' =>
        have hrec := ih (ps ++ [c']) k' hlen (by simpa using hk)
        have ee2 : ps ++ c' :: List.replicate (k' + 1) 0 = (ps ++ [c']) ++ List.replicate (k' + 1) 0 := by simp
        rw [ee2, limbsVal_cons, hrec]
        have h2 := hv
        simp only [limbsVal_cons, Nat.add_zero] at h2
        simp only [limbsVal_cons, Nat.mul_add, Nat.add_mul]
        grind

theorem trimHigh_val (x : List Nat) : limbsVal (trimHigh x) = limbsVal x := by
  have h : x.reverse = x.reverse.takeWhile (· == 0) ++ x.reverse.dropWhile (· == 0) :=
    (List.takeWhile_append_dropWhile).symm
  have hz : ∀ t : List Nat, (∀ a ∈ t, a = 0) → t = List.replicate t.length 0 := by
    intro t ht; exact List.eq_replicate_iff.2 ⟨rfl, ht⟩
  have hx : x = (x.reverse.dropWhile (· == 0)).reverse ++ (x.reverse.takeWhile (· == 0)).reverse := by
    conv => lhs; rw [← List.reverse_reverse x, h, List.reverse_append]
  unfold trimHigh
  conv => rhs; rw [hx]
  generalize (x.reverse.dropWhile (· == 0)).reverse = l
  have hall : ∀ a ∈ (x.reverse.takeWhile (· == 0)).reverse, a = 0 := by
    intro a ha
    have := List.all_eq_true.1 (List.all_takeWhile (p := (· == 0)) (l := x.reverse)) a (List.mem_reverse.1 ha)
    simpa using this
  rw [hz _ hall, limbsVal_append_zero]

theorem isZero_val {b : Bigint} (h : b.isZero = true) : b.val = 0 := by
  obtain ⟨s, x⟩ := b
  cases x with
  | nil => rfl
  | cons d ds =>
    cases ds with
    | nil =>
      simp [Bigint.isZero, Bigint.x0, Bigint.wds] at h
      simp [Bigint.val, limbsVal, h]
    | cons e es => simp [Bigint.isZero, Bigint.wds] at h

theorem not_isZero_ne {b : Bigint} (h : b.isZero = false) : b.x ≠ [] := by
  intro hx
  obtain ⟨s, x⟩ := b
  simp only at hx
  subst hx
  simp [Bigint.isZero, Bigint.x0, Bigint.wds] at h

/-- `mult(a, b)` is the product, on any two Bigints. -/
def MultValue : Prop := ∀ a b : Bigint, (mult a b).val = a.val * b.val

theorem multValue_proven : MultValue := by
  intro a0 b0
  unfold mult
  by_cases h : (a0.isZero || b0.isZero) = true
  · simp only [h, ↓reduceIte]
    rcases Bool.or_eq_true _ _ ▸ h with h | h
    · rw [isZero_val h]; simp [Bigint.val, limbsVal]
    · rw [isZero_val h]; simp [Bigint.val, limbsVal]
  · have h' : (a0.isZero || b0.isZero) = false := by simpa using h
    obtain ⟨ha, hb⟩ := Bool.or_eq_false_iff.1 h'
    simp only [h', Bool.false_eq_true, ↓reduceIte]
    have core : ∀ a b : Bigint, a.isZero = false → b.isZero = false →
        limbsVal (trimHigh (multOuter a.x b.x (List.replicate (a.wds + b.wds) 0))) = a.val * b.val := by
      intro a b h1 h2
      rw [trimHigh_val]
      have hbne := not_isZero_ne h2
      obtain ⟨k, hk⟩ : ∃ k, b.wds = k + 1 := by
        cases hb' : b.x with
        | nil => exact absurd hb' hbne
        | cons _ t => exact ⟨t.length, by simp [Bigint.wds, hb']⟩
      have e : List.replicate (a.wds + b.wds) 0 = List.replicate a.wds 0 ++ List.replicate (k + 1) 0 := by
        rw [hk, List.replicate_append_replicate]
      rw [e]
      have := multOuter_val a.x (not_isZero_ne h1) b.x (List.replicate a.wds 0) k (by simp [Bigint.wds])
        (by have : b.x.length = k + 1 := hk; omega)
      rw [this]
      have z := limbsVal_append_zero [] a.wds
      simp only [List.nil_append, limbsVal_nil] at z
      rw [z]; simp [Bigint.val]
    by_cases hlt : a0.wds < b0.wds
    · simp only [hlt, ↓reduceIte]
      show limbsVal _ = _
      rw [core b0 a0 hb ha, Nat.mul_comm]
    · simp only [hlt, ↓reduceIte]
      show limbsVal _ = _
      exact core a0 b0 ha hb

/-- The entries of `p5s`. -/
theorem p5s_val : ∀ i, i < 8 → (p5s[i]!).val = 5 ^ (2 ^ (i + 2)) := by decide +kernel

theorem pow5Loop_val : ∀ (fuel i k : Nat) (b : Bigint), k < 2 ^ fuel → i + fuel ≤ 8 →
    (pow5Loop fuel i k b).val = b.val * (5 ^ (2 ^ (i + 2))) ^ k := by
  intro fuel
  induction fuel with
  | zero => intro i k b hk _; have : k = 0 := by simpa using hk
            subst this; simp [pow5Loop]
  | succ n ih =>
    intro i k b hk hi
    have hi8 : i < 8 := by omega
    have m1 : k &&& 1 = k % 2 := Nat.and_two_pow_sub_one_eq_mod k 1
    have hv : (if k &&& 1 != 0 then mult b (p5s[i]!) else b).val =
        b.val * (5 ^ (2 ^ (i + 2))) ^ (k % 2) := by
      rw [m1]
      by_cases hb : k % 2 = 0
      · simp [hb]
      · have : k % 2 = 1 := by omega
        simp only [this, bne_iff_ne, ne_eq, one_ne_zero, not_false_eq_true, ↓reduceIte, Nat.pow_one]
        rw [multValue_proven b, p5s_val i hi8]
    unfold pow5Loop
    simp only []
    generalize hb1 : (if k &&& 1 != 0 then mult b (p5s[i]!) else b) = b1 at *
    have hpsq : (5 ^ (2 ^ (i + 1 + 2))) = (5 ^ (2 ^ (i + 2))) ^ 2 := by
      rw [← Nat.pow_mul]; congr 1
    have hsplit : ∀ c : Nat, c ^ k = c ^ (k % 2) * (c ^ 2) ^ (k / 2) := by
      intro c
      rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
    by_cases hz : k / 2 = 0
    · simp only [hz, beq_self_eq_true, ↓reduceIte]
      rw [hv]
      have : k = k % 2 := by omega
      conv => rhs; rw [this]
    · have hz' : (k / 2 == 0) = false := by simpa using hz
      simp only [hz', Bool.false_eq_true, ↓reduceIte]
      rw [ih (i + 1) (k / 2) b1 (by rw [Nat.pow_succ] at hk; omega) (by omega), hv, hpsq,
        hsplit (5 ^ (2 ^ (i + 2))), Nat.mul_assoc]

/-- `pow5mult(b, k)` is `b * 5 ** k` for every `k < 1024`, the bound the source asserts. -/
def Pow5multValue : Prop :=
  ∀ (b : Bigint) (k : Nat), k < 1024 → (pow5mult b k).val = b.val * 5 ^ k

theorem pow5multValue_proven : Pow5multValue := by
  intro b k hk
  have m3 : k &&& 3 = k % 4 := Nat.and_two_pow_sub_one_eq_mod k 2
  unfold pow5mult
  simp only [m3]
  have hb : (if k % 4 != 0 then multadd b ([5, 25, 125].getD (k % 4 - 1) 0) 0 else b).val =
      b.val * 5 ^ (k % 4) := by
    have hlt : k % 4 < 4 := Nat.mod_lt _ (by omega)
    generalize k % 4 = r at *
    match r, hlt with
    | 0, _ => simp
    | 1, _ => simp [multadd_val]
    | 2, _ => simp [multadd_val]
    | 3, _ => simp [multadd_val]
  generalize (if k % 4 != 0 then multadd b ([5, 25, 125].getD (k % 4 - 1) 0) 0 else b) = b1 at *
  have hsplit : 5 ^ k = 5 ^ (k % 4) * (5 ^ 4) ^ (k / 4) := by
    rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
  by_cases hz : k / 4 = 0
  · simp only [hz, beq_self_eq_true, ↓reduceIte]
    rw [hb]
    have : k = k % 4 := by omega
    conv => rhs; rw [this]
  · have hz' : (k / 4 == 0) = false := by simpa using hz
    simp only [hz', Bool.false_eq_true, ↓reduceIte]
    rw [pow5Loop_val 8 0 (k / 4) b1 (by omega) (by omega), hb, hsplit, Nat.mul_assoc]
    rfl

end PyLean.Binary64
