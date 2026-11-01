import PyLean.Binary64.BigintProps

/-!
`lshift`, `cmp`, `diff` and `dshift` from `Python/dtoa.c`. These need the invariant the
source comment at dtoa.c:289-292 states: limbs are 32-bit, and the top limb is nonzero
unless the number has a single limb.
-/

namespace PyLean.Binary64

open Bigint

/-- Every limb fits in 32 bits. -/
def Limbs32 (x : List Nat) : Prop := ∀ d ∈ x, d < 2 ^ 32

/-- The invariant of `struct Bigint`, dtoa.c:289-292. -/
structure Normal (b : Bigint) : Prop where
  limbs : Limbs32 b.x
  ne : b.x ≠ []
  top : b.wds = 1 ∨ b.top ≠ 0

theorem lshiftLoop_val {k : Nat} (h0 : 0 < k) (h1 : k < 32) : ∀ (x : List Nat) (z : Nat),
    Limbs32 x → z < 2 ^ k → limbsVal (lshiftLoop k x z) = limbsVal x * 2 ^ k + z := by
  intro x
  induction x with
  | nil =>
    intro z _ _
    by_cases hz : z = 0
    · simp [lshiftLoop, hz, limbsVal]
    · simp [lshiftLoop, hz, limbsVal]
  | cons d ds ih =>
    intro z hl hz
    have hd : d < 2 ^ 32 := hl d (by simp)
    have hds : Limbs32 ds := fun a ha => hl a (by simp [ha])
    have hp : 2 ^ k * 2 ^ (32 - k) = 2 ^ 32 := by
      rw [← Nat.pow_add]; congr 1; omega
    have hw : 0 < 2 ^ (32 - k) := Nat.two_pow_pos _
    have hkp : 0 < 2 ^ k := Nat.two_pow_pos _
    have hq : d / 2 ^ (32 - k) < 2 ^ k := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm, hp]; exact hd
    have hdec := Nat.div_add_mod d (2 ^ (32 - k))
    generalize hQ : d / 2 ^ (32 - k) = Q at *
    generalize hR : d % 2 ^ (32 - k) = R at *
    have hRlt : R < 2 ^ (32 - k) := by rw [← hR]; exact Nat.mod_lt _ hw
    -- the head limb
    have hRp : R * 2 ^ k < 2 ^ 32 := by
      rw [← hp, Nat.mul_comm]
      exact Nat.mul_lt_mul_of_pos_left hRlt hkp
    have hdp : d * 2 ^ k = 2 ^ 32 * Q + R * 2 ^ k := by
      calc d * 2 ^ k = (2 ^ (32 - k) * Q + R) * 2 ^ k := by rw [hdec]
        _ = 2 ^ 32 * Q + R * 2 ^ k := by rw [← hp]; grind
    have hshl : shl32 d k = 2 ^ k * R := by
      unfold shl32
      rw [hdp, Nat.mul_add_mod, Nat.mod_eq_of_lt hRp, Nat.mul_comm]
    have hor : shl32 d k ||| z = shl32 d k + z := by
      rw [hshl]
      exact (Nat.two_pow_add_eq_or_of_lt hz R).symm
    simp only [lshiftLoop, limbsVal_cons, hor]
    rw [hQ, ih Q hds (by omega), hshl]
    have e : (d + 2 ^ 32 * limbsVal ds) * 2 ^ k = d * 2 ^ k + 2 ^ 32 * (limbsVal ds * 2 ^ k) := by grind
    rw [e, hdp, Nat.mul_add]
    grind

theorem limbsVal_replicate_append (n : Nat) (l : List Nat) :
    limbsVal (List.replicate n 0 ++ l) = 2 ^ (32 * n) * limbsVal l := by
  rw [limbsVal_append]
  have z := limbsVal_append_zero [] n
  simp only [List.nil_append, limbsVal_nil] at z
  rw [z]; simp

/-- `lshift(b, k)` is `b * 2 ** k`. -/
def LshiftValue : Prop :=
  ∀ (b : Bigint) (k : Nat), Limbs32 b.x → (lshift b k).val = b.val * 2 ^ k

theorem lshiftValue_proven : LshiftValue := by
  intro b k hl
  unfold lshift
  by_cases hc : (k == 0 || b.isZero) = true
  · simp only [hc, ↓reduceIte]
    rcases Bool.or_eq_true _ _ ▸ hc with h | h
    · have : k = 0 := by simpa using h
      subst this; simp
    · rw [isZero_val h]; simp
  · have hc' : (k == 0 || b.isZero) = false := by simpa using hc
    simp only [hc', Bool.false_eq_true, ↓reduceIte]
    have hk : 2 ^ k = 2 ^ (32 * (k / 32)) * 2 ^ (k % 32) := by
      rw [← Nat.pow_add]; congr 1; omega
    by_cases hr : k % 32 = 0
    · have hr' : (k % 32 != 0) = false := by simpa using hr
      simp only [hr', Bool.false_eq_true, ↓reduceIte]
      show limbsVal _ = _
      rw [limbsVal_replicate_append, hk, hr]
      simp [Bigint.val, Nat.mul_comm]
    · have hr' : (k % 32 != 0) = true := by simpa using hr
      simp only [hr', ↓reduceIte]
      show limbsVal _ = _
      rw [limbsVal_replicate_append, lshiftLoop_val (by omega) (Nat.mod_lt _ (by omega)) _ _ hl
        (Nat.two_pow_pos _), hk]
      simp only [Nat.add_zero, Bigint.val]
      grind

/-! ## Comparison -/

theorem limbsVal_lt : ∀ (x : List Nat), Limbs32 x → limbsVal x < 2 ^ (32 * x.length) := by
  intro x
  induction x with
  | nil => intro _; simp [limbsVal]
  | cons d ds ih =>
    intro hl
    have hd : d < 2 ^ 32 := hl d (by simp)
    have h1 := ih (fun a ha => hl a (by simp [ha]))
    have e : 2 ^ (32 * (d :: ds).length) = 2 ^ 32 * 2 ^ (32 * ds.length) := by
      simp only [List.length_cons]; rw [Nat.mul_add, Nat.pow_add, Nat.mul_comm]
    rw [e, limbsVal_cons]
    have : limbsVal ds + 1 ≤ 2 ^ (32 * ds.length) := h1
    have h2 := Nat.mul_le_mul_left (2 ^ 32) this
    rw [Nat.mul_add] at h2
    omega

theorem reverse_val (a : Nat) (as : List Nat) :
    limbsVal (a :: as).reverse = limbsVal as.reverse + 2 ^ (32 * as.length) * a := by
  rw [List.reverse_cons, limbsVal_append]
  simp [limbsVal]

theorem limbs32_reverse {x : List Nat} (h : Limbs32 x) : Limbs32 x.reverse :=
  fun a ha => h a (List.mem_reverse.1 ha)

/-- The limb loop of `cmp` compares equal-length numbers, top limb first. -/
theorem cmpLoop_spec : ∀ (ra rb : List Nat), ra.length = rb.length →
    Limbs32 ra.reverse → Limbs32 rb.reverse →
    (cmpLoop ra rb < 0 → limbsVal ra.reverse < limbsVal rb.reverse) ∧
    (cmpLoop ra rb = 0 → limbsVal ra.reverse = limbsVal rb.reverse) ∧
    (0 < cmpLoop ra rb → limbsVal rb.reverse < limbsVal ra.reverse) := by
  intro ra
  induction ra with
  | nil =>
    intro rb h _ _
    have : rb = [] := List.length_eq_zero_iff.1 (by simpa using h.symm)
    subst this
    simp [cmpLoop]
  | cons a as ih =>
    intro rb h la lb
    cases rb with
    | nil => simp at h
    | cons b bs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      have las : Limbs32 as.reverse :=
        fun d hd => la d (List.mem_reverse.2 (List.mem_cons_of_mem _ (List.mem_reverse.1 hd)))
      have lbs : Limbs32 bs.reverse :=
        fun d hd => lb d (List.mem_reverse.2 (List.mem_cons_of_mem _ (List.mem_reverse.1 hd)))
      have hih := ih bs h las lbs
      have ha1 := limbsVal_lt as.reverse las
      have hb1 := limbsVal_lt bs.reverse lbs
      simp only [List.length_reverse] at ha1 hb1
      rw [← h] at hb1
      rw [reverse_val, reverse_val, ← h]
      clear ih
      generalize limbsVal as.reverse = A at *
      generalize limbsVal bs.reverse = B at *
      generalize 2 ^ (32 * as.length) = P at *
      unfold cmpLoop
      by_cases hab : a = b
      · subst hab
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨i1, i2, i3⟩ := hih
        exact ⟨fun c => by have := i1 c; omega, fun c => by have := i2 c; omega,
          fun c => by have := i3 c; omega⟩
      · have hne : (a != b) = true := by simpa using hab
        simp only [hne, ↓reduceIte]
        have big : ∀ u v : Nat, u < v → P * u + P ≤ P * v := by
          intro u v huv
          have := Nat.mul_le_mul_left P (show u + 1 ≤ v from huv)
          rwa [Nat.mul_add, Nat.mul_one] at this
        by_cases hlt : a < b
        · have := big a b hlt
          simp only [hlt, ↓reduceIte]
          exact ⟨fun _ => by omega, by intro h0; omega, by intro h0; omega⟩
        · have hgt : b < a := by omega
          have := big b a hgt
          simp only [hlt, ↓reduceIte]
          exact ⟨by intro h0; omega, by intro h0; omega, fun _ => by omega⟩

theorem top_lower {b : Bigint} (hb : Normal b) (h : 1 < b.wds) :
    2 ^ (32 * (b.wds - 1)) ≤ b.val := by
  have hrev : b.x = (b.x.reverse).reverse := by simp
  cases hr : b.x.reverse with
  | nil =>
    exact absurd (List.reverse_eq_nil_iff.1 hr) hb.ne
  | cons t ts =>
    have hx : b.x = (t :: ts).reverse := by rw [← hr]; simp
    have htop : b.top = t := by
      unfold Bigint.top; rw [hx, List.getLastD_eq_getLast?]; simp
    have hlen : b.wds = ts.length + 1 := by
      unfold Bigint.wds; rw [hx]; simp
    have ht : t ≠ 0 := by
      rcases hb.top with h1 | h1
      · omega
      · rwa [htop] at h1
    unfold Bigint.val
    rw [hx, reverse_val]
    have h1 : 1 ≤ t := by omega
    have := Nat.mul_le_mul_left (2 ^ (32 * ts.length)) h1
    rw [hlen]
    simp only [Nat.add_sub_cancel]
    omega

/-- `cmp` on normal Bigints: negative, zero or positive as `a` is below, equal to or above `b`. -/
def CmpSpec : Prop :=
  ∀ a b : Bigint, Normal a → Normal b →
    (cmp a b < 0 ↔ a.val < b.val) ∧ (cmp a b = 0 ↔ a.val = b.val) ∧ (0 < cmp a b ↔ b.val < a.val)

theorem cmpSpec_proven : CmpSpec := by
  intro a b ha hb
  have key : (cmp a b < 0 → a.val < b.val) ∧ (cmp a b = 0 → a.val = b.val) ∧
      (0 < cmp a b → b.val < a.val) := by
    unfold cmp
    by_cases hw : a.wds = b.wds
    · have : ((a.wds : Int) - b.wds != 0) = false := by simp [hw]
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      have := cmpLoop_spec a.x.reverse b.x.reverse (by simp only [List.length_reverse]; exact hw)
        (by simpa using ha.limbs) (by simpa using hb.limbs)
      simpa [Bigint.val] using this
    · have hne : ((a.wds : Int) - b.wds != 0) = true := by simp; omega
      simp only [hne, ↓reduceIte]
      have lt_of : ∀ u v : Bigint, Normal u → Normal v → u.wds < v.wds → u.val < v.val := by
        intro u v hu hv hlt
        have h1 := limbsVal_lt u.x hu.limbs
        have h2 := top_lower hv (by have : 0 < u.wds := List.length_pos_iff.2 hu.ne; omega)
        have h3 : 2 ^ (32 * u.x.length) ≤ 2 ^ (32 * (v.wds - 1)) :=
          Nat.pow_le_pow_right (by omega) (by
            have : u.x.length = u.wds := rfl
            rw [this]; exact Nat.mul_le_mul_left _ (by omega))
        unfold Bigint.val at *
        omega
      refine ⟨fun c => lt_of a b ha hb (by omega), fun c => by omega, fun c => lt_of b a hb ha (by omega)⟩
  obtain ⟨k1, k2, k3⟩ := key
  refine ⟨⟨k1, fun h => ?_⟩, ⟨k2, fun h => ?_⟩, ⟨k3, fun h => ?_⟩⟩
  · rcases Int.lt_trichotomy (cmp a b) 0 with c | c | c
    · exact c
    · have := k2 c; omega
    · have := k3 c; omega
  · rcases Int.lt_trichotomy (cmp a b) 0 with c | c | c
    · have := k1 c; omega
    · exact c
    · have := k3 c; omega
  · rcases Int.lt_trichotomy (cmp a b) 0 with c | c | c
    · have := k1 c; omega
    · have := k2 c; omega
    · exact c

/-! ## Subtraction -/

theorem diffLoop_val : ∀ (a b : List Nat) (br : Nat), Limbs32 a → Limbs32 b → br ≤ 1 →
    limbsVal b + br ≤ limbsVal a → limbsVal (diffLoop a b br) + limbsVal b + br = limbsVal a := by
  intro a
  induction a with
  | nil =>
    intro b br _ _ _ h
    simp only [limbsVal_nil] at h
    simp [diffLoop, limbsVal]; omega
  | cons d ds ih =>
    intro b br la lb hbr h
    have hd : d < 2 ^ 32 := la d (by simp)
    have lds : Limbs32 ds := fun x hx => la x (by simp [hx])
    cases b with
    | nil =>
      simp only [limbsVal_nil, limbsVal_cons] at h ⊢
      simp only [diffLoop]
      generalize hy : (d + 2 ^ 64 - br) % 2 ^ 64 = y
      have hbw : y / 2 ^ 32 % 2 ≤ 1 := by omega
      have e1 : limbsVal [] = 0 := rfl
      have hrec := ih [] (y / 2 ^ 32 % 2) lds (fun x hx => by cases hx) hbw (by
        rw [e1]; omega)
      rw [e1] at hrec
      simp only [limbsVal_cons]
      omega
    | cons e es =>
      have he : e < 2 ^ 32 := lb e (by simp)
      have les : Limbs32 es := fun x hx => lb x (by simp [hx])
      simp only [limbsVal_cons] at h ⊢
      simp only [diffLoop]
      generalize hy : (d + 2 ^ 64 - e - br) % 2 ^ 64 = y
      have hbw : y / 2 ^ 32 % 2 ≤ 1 := by omega
      have hrec := ih es (y / 2 ^ 32 % 2) lds les hbw (by omega)
      simp only [limbsVal_cons]
      omega

/-- `diff(a, b)` is `|a - b|`, and its sign says which side was larger. -/
def DiffValue : Prop :=
  ∀ a b : Bigint, Normal a → Normal b →
    (diff a b).val + min a.val b.val = max a.val b.val ∧
    ((diff a b).sign = true ↔ a.val < b.val)

theorem diffValue_proven : DiffValue := by
  intro a b ha hb
  obtain ⟨c1, c2, c3⟩ := cmpSpec_proven a b ha hb
  unfold diff
  by_cases h0 : cmp a b = 0
  · have heq := c2.1 h0
    simp only [h0, beq_self_eq_true, ↓reduceIte]
    refine ⟨?_, ?_⟩
    · have hm : min a.val b.val = max a.val b.val := by omega
      rw [hm]
      show limbsVal [0] + _ = _
      simp [limbsVal]
    · constructor
      · intro h; cases h
      · intro h; omega
  · have h0' : (cmp a b == 0) = false := by simpa using h0
    simp only [h0', Bool.false_eq_true, ↓reduceIte]
    by_cases hneg : cmp a b < 0
    · have hlt := c1.1 hneg
      simp only [hneg, ↓reduceIte]
      constructor
      · show limbsVal _ + _ = _
        rw [trimHigh_val]
        have := diffLoop_val b.x a.x 0 hb.limbs ha.limbs (by omega) (by
          unfold Bigint.val at hlt; omega)
        simp only [Bigint.val] at hlt ⊢
        omega
      · simpa using hlt
    · have hgt : b.val < a.val := c3.1 (by omega)
      simp only [hneg, ↓reduceIte]
      constructor
      · show limbsVal _ + _ = _
        rw [trimHigh_val]
        have := diffLoop_val a.x b.x 0 ha.limbs hb.limbs (by omega) (by
          unfold Bigint.val at hgt; omega)
        simp only [Bigint.val] at hgt ⊢
        omega
      · simp; omega

/-- `dshift(b, p2)` is the left shift, modulo 32, that leaves 4 leading zero bits in the top
limb of `b * 2 ** max(p2, 0)`, as the comment at dtoa.c:2597-2603 asks. -/
def DshiftSpec : Prop :=
  ∀ (b : Bigint) (p2 : Int), dshift b p2 < 32 ∧
    ((dshift b p2 : Int) + max p2 0 + 4 - (hi0bits b.top : Int)) % 32 = 0

theorem dshiftSpec_proven : DshiftSpec := by
  intro b p2
  unfold dshift
  simp only []
  split <;> omega

end PyLean.Binary64
