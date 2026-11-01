import PyLean.Accel.HeapifyLocalOrder

/-!
The concrete C cache-friendly order (`Modules/_heapqmodule.c:332-363`) is a
valid bottom-up order covering every internal node: with `Q = 2^q`,
`2Q <= m + 1 < 4Q` (so `keep_top_bit(m + 1) = 2Q` and `leftmost = 2Q - 1`),
loop 1 climbs from `[m/2, 2Q - 1)` and loop 2 from `[2Q - 1, m)`.
-/

namespace PyLean.Accel

open PyLean

/-! ### keep_top_bit -/

theorem keepTopBit_go (f : Nat) : ∀ (i x : Nat), 1 ≤ x → x < 2 ^ (f + 1) →
    ∃ R, keepTopBit.go f i x = 2 ^ R * 2 ^ i ∧ 2 ^ R ≤ x ∧ x < 2 ^ (R + 1) := by
  induction f with
  | zero =>
    intro i x h1 h2
    have : x = 1 := by simp at h2; omega
    subst this
    exact ⟨0, by simp [keepTopBit.go, Nat.shiftLeft_eq], by simp, by simp⟩
  | succ f ih =>
    intro i x h1 h2
    simp only [keepTopBit.go]
    by_cases hx : x > 1
    · rw [if_pos hx, shr1]
      have hp : 2 ^ (f + 1 + 1) = 2 ^ (f + 1) * 2 := by rw [Nat.pow_succ]
      obtain ⟨R, e, b1, b2⟩ := ih (i + 1) (x / 2) (by omega) (by omega)
      refine ⟨R + 1, ?_, ?_, ?_⟩
      · rw [e, Nat.pow_succ, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ i)]
      · rw [Nat.pow_succ]; omega
      · have : 2 ^ (R + 1 + 1) = 2 ^ R * 2 * 2 := by rw [Nat.pow_succ, Nat.pow_succ]
        rw [this]; have : 2 ^ (R + 1) = 2 ^ R * 2 := by rw [Nat.pow_succ]
        rw [this] at b2; omega
    · rw [if_neg hx]
      have : x = 1 := by omega
      subst this
      exact ⟨0, by simp [Nat.shiftLeft_eq], by simp, by simp⟩

theorem keepTopBit_spec (x : Nat) (h : 1 ≤ x) :
    ∃ R, keepTopBit x = 2 ^ R ∧ 2 ^ R ≤ x ∧ x < 2 ^ (R + 1) := by
  have h2 : x < 2 ^ (x + 1) := by
    have := Nat.lt_two_pow_self (n := x)
    have := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_succ x)
    omega
  obtain ⟨R, e, b⟩ := keepTopBit_go x 0 x h h2
  exact ⟨R, by simp [keepTopBit, e], b⟩

/-! ### The right sibling's climb origin -/

theorem half_add (w t q : Nat) (ht : 1 ≤ t) (h : (w + 1) * 2 ^ t < 2 * 2 ^ q) :
    (2 * w + 2 + 1) * 2 ^ (t - 1) = (w + 1) * 2 ^ t + 2 ^ (t - 1) ∧
      (w + 1) * 2 ^ t + 2 ^ (t - 1) < 2 * 2 ^ q ∧ 1 ≤ 2 ^ (t - 1) := by
  have hT : 2 ^ t = 2 ^ (t - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  have e1 : (2 * w + 2 + 1) * 2 ^ (t - 1) = 2 * ((w + 1) * 2 ^ (t - 1)) + 2 ^ (t - 1) := by
    rw [show 2 * w + 2 + 1 = 2 * (w + 1) + 1 by omega, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
  have e2 : (w + 1) * 2 ^ t = 2 * ((w + 1) * 2 ^ (t - 1)) := by
    rw [hT, ← Nat.mul_assoc, Nat.mul_comm _ 2]
  have hpos := Nat.two_pow_pos (t - 1)
  refine ⟨by rw [e1, e2], ?_, hpos⟩
  have htq : t ≤ q + 1 := by
    by_cases htq : t ≤ q + 1
    · exact htq
    · have := Nat.pow_le_pow_right (n := 2) (by decide) (show q + 2 ≤ t by omega)
      have := Nat.le_mul_of_pos_left (2 ^ t) (show 0 < w + 1 by omega)
      have : 2 ^ (q + 2) = 2 ^ q * 2 * 2 := by rw [Nat.pow_succ, Nat.pow_succ]
      omega
  have hK : 2 * 2 ^ q = 2 ^ t * 2 ^ (q + 1 - t) := by
    rw [← Nat.pow_add, show t + (q + 1 - t) = q + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  rw [hK] at h ⊢
  have h' : 2 ^ t * (w + 1) < 2 ^ t * 2 ^ (q + 1 - t) := by rw [Nat.mul_comm]; exact h
  have hw := Nat.lt_of_mul_lt_mul_left h'
  have h3 : 2 ^ t * (w + 2) ≤ 2 ^ t * 2 ^ (q + 1 - t) := Nat.mul_le_mul_left _ (by omega)
  have h4 : 2 ^ t * (w + 2) = (w + 1) * 2 ^ t + 2 ^ t := by
    rw [Nat.mul_comm, show w + 2 = (w + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
  omega

/-! ### The two loops -/

theorem c_phase1 (m q : Nat) (h1 : 2 * 2 ^ q ≤ m + 1) (h2 : m + 1 < 4 * 2 ^ q) :
    ∀ i, m / 2 ≤ i → i < 2 * 2 ^ q - 1 → ∀ w, Vis i w → w < m ∧ ¬ (fun _ => False) w ∧
      (∀ i', i < i' → i' < 2 * 2 ^ q - 1 → ¬ Vis i' w) ∧ (w = i → m ≤ 2 * w + 1) ∧
      (2 * w + 2 < m → (fun _ => False) (2 * w + 2) ∨
        ∃ i', i < i' ∧ i' < 2 * 2 ^ q - 1 ∧ Vis i' (2 * w + 2)) := by
  intro i hi1 hi2 w hw
  have hle := vis_le hw
  obtain ⟨t, ht⟩ := hw
  refine ⟨by omega, fun h => h, ?_, fun e => by omega, ?_⟩
  · rintro i' hi' hi'' ⟨t', ht'⟩
    have := row_unique (w + 1) t t' (2 ^ q) (by omega) (by omega) (by omega) (by omega) (by omega)
    subst this; omega
  · intro hm
    cases t with
    | zero => simp at ht; omega
    | succ t =>
      obtain ⟨e, b, p⟩ := half_add w (t + 1) q (by omega) (by omega)
      refine Or.inr ⟨i + 2 ^ t, by simp at p; omega, by simp at e b; omega, t, ?_⟩
      simp at e; omega

theorem c_phase2 (m q : Nat) (h1 : 2 * 2 ^ q ≤ m + 1) (h2 : m + 1 < 4 * 2 ^ q) :
    ∀ i, 2 * 2 ^ q - 1 ≤ i → i < m → ∀ w, Vis i w → w < m ∧
      ¬ (fun j => False ∨ ∃ i', m / 2 ≤ i' ∧ i' < 2 * 2 ^ q - 1 ∧ Vis i' j) w ∧
      (∀ i', i < i' → i' < m → ¬ Vis i' w) ∧ (w = i → m ≤ 2 * w + 1) ∧
      (2 * w + 2 < m → (fun j => False ∨ ∃ i', m / 2 ≤ i' ∧ i' < 2 * 2 ^ q - 1 ∧ Vis i' j) (2 * w + 2) ∨
        ∃ i', i < i' ∧ i' < m ∧ Vis i' (2 * w + 2)) := by
  intro i hi1 hi2 w hw
  have hle := vis_le hw
  obtain ⟨t, ht⟩ := hw
  refine ⟨by omega, ?_, ?_, fun e => by omega, ?_⟩
  · rintro (h | ⟨i', hi'1, hi'2, t', ht'⟩)
    · exact h
    · by_cases htt : t ≤ t'
      · have := mul_pow_le_mul_pow (w + 1) t t' htt; omega
      · have := mul_pow_lt_mul_pow (w + 1) t' t (by omega) (by omega); omega
  · rintro i' hi' hi'' ⟨t', ht'⟩
    have := row_unique (w + 1) t t' (2 * 2 ^ q) (by omega) (by omega) (by omega) (by omega) (by omega)
    subst this; omega
  · intro hm
    cases t with
    | zero => simp at ht; omega
    | succ t =>
      have hq : 2 * (2 * 2 ^ q) = 2 * 2 ^ (q + 1) := by rw [Nat.pow_succ]; omega
      obtain ⟨e, b, p⟩ := half_add w (t + 1) (q + 1) (by omega) (by omega)
      simp only [Nat.add_sub_cancel] at e b p
      by_cases hlt : i + 2 ^ t < m
      · exact Or.inr ⟨i + 2 ^ t, by omega, hlt, t, by omega⟩
      · cases t with
        | zero => simp at e; omega
        | succ t =>
          have e3 : (2 * w + 2 + 1) * 2 ^ (t + 1) = (2 * w + 2 + 1) * 2 ^ t * 2 := by
            rw [Nat.pow_succ, Nat.mul_assoc]
          have hZ := Nat.le_mul_of_pos_right (2 * w + 2 + 1) (Nat.two_pow_pos t)
          refine Or.inl (Or.inr ⟨(2 * w + 2 + 1) * 2 ^ t - 1, by omega, by omega, t, by omega⟩)

theorem c_cover (m q j : Nat) (h1 : 2 * 2 ^ q ≤ m + 1) (h2 : m + 1 < 4 * 2 ^ q) (hj : j < m) :
    (∃ i, m / 2 ≤ i ∧ i < 2 * 2 ^ q - 1 ∧ Vis i j) ∨ (∃ i, 2 * 2 ^ q - 1 ≤ i ∧ i < m ∧ Vis i j) := by
  obtain ⟨r, -, b1, b2⟩ := keepTopBit_spec (j + 1) (by omega)
  have hr : r ≤ q + 1 := by
    by_cases hr : r ≤ q + 1
    · exact hr
    · have := Nat.pow_le_pow_right (n := 2) (by decide) (show q + 2 ≤ r by omega)
      have : 2 ^ (q + 2) = 2 ^ q * 2 * 2 := by rw [Nat.pow_succ, Nat.pow_succ]
      omega
  by_cases hrq : r = q + 1
  · subst hrq
    rw [Nat.pow_succ] at b1
    exact Or.inr ⟨j, by omega, hj, 0, by simp⟩
  · have hs : 2 ^ r * 2 ^ (q - r) = 2 ^ q := by rw [← Nat.pow_add]; congr 1; omega
    have c1 : 2 ^ q ≤ (j + 1) * 2 ^ (q - r) := by rw [← hs]; exact Nat.mul_le_mul_right _ b1
    have c2 : (j + 1) * 2 ^ (q - r) < 2 * 2 ^ q := by
      have := Nat.mul_lt_mul_of_pos_right b2 (Nat.two_pow_pos (q - r))
      rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm 2, ← Nat.mul_assoc, hs] at this
      omega
    by_cases hy : m / 2 ≤ (j + 1) * 2 ^ (q - r) - 1
    · exact Or.inl ⟨(j + 1) * 2 ^ (q - r) - 1, hy, by omega, q - r, by omega⟩
    · have e : (j + 1) * 2 ^ (q - r + 1) = (j + 1) * 2 ^ (q - r) * 2 := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      exact Or.inr ⟨(j + 1) * 2 ^ (q - r) * 2 - 1, by omega, by omega, q - r + 1, by omega⟩

/-- The C order: validity and coverage. -/
theorem c_order (m q : Nat) (h1 : 2 * 2 ^ q ≤ m + 1) (h2 : m + 1 < 4 * 2 ^ q) :
    HValid m (fun _ => False)
      ((downFrom (m / 2) (2 * 2 ^ q - 1)).flatMap (fun i => climbSeq (i + 1) i) ++
        (downFrom (2 * 2 ^ q - 1) m).flatMap (fun i => climbSeq (i + 1) i)) ∧
    ∀ j, j ∈ (downFrom (m / 2) (2 * 2 ^ q - 1)).flatMap (fun i => climbSeq (i + 1) i) ++
        (downFrom (2 * 2 ^ q - 1) m).flatMap (fun i => climbSeq (i + 1) i) ↔ j < m := by
  obtain ⟨v1, a1⟩ := phase_valid m (m / 2) (2 * 2 ^ q - 1) (fun _ => False) (c_phase1 m q h1 h2)
    _ (2 * 2 ^ q - 1) rfl (by omega) (Nat.le_refl _) (fun _ => False) (by
      intro j; constructor
      · intro h; exact h.elim
      · rintro (h | ⟨i', h1, h2, -⟩)
        · exact h
        · omega)
  let D1 := fun j => False ∨ ∃ i', m / 2 ≤ i' ∧ i' < 2 * 2 ^ q - 1 ∧ Vis i' j
  obtain ⟨v2, a2⟩ := phase_valid m (2 * 2 ^ q - 1) m D1 (c_phase2 m q h1 h2)
    _ m rfl (by omega) (Nat.le_refl _)
    (fun j => False ∨ j ∈ (downFrom (m / 2) (2 * 2 ^ q - 1)).flatMap (fun i => climbSeq (i + 1) i)) (by
      intro j
      rw [a1 j]
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨i', h1, h2, -⟩)
        · exact h
        · omega)
  refine ⟨hvalid_append m _ _ _ v1 v2, fun j => ?_⟩
  have := a2 j
  rw [List.mem_append]
  constructor
  · intro h
    have h' : ((False ∨ j ∈ (downFrom (m / 2) (2 * 2 ^ q - 1)).flatMap (fun i => climbSeq (i + 1) i)) ∨
        j ∈ (downFrom (2 * 2 ^ q - 1) m).flatMap (fun i => climbSeq (i + 1) i)) := by
      rcases h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    rcases this.1 h' with hD | ⟨i', -, h2, h3⟩
    · rcases hD with hD | ⟨i', -, h2, h3⟩
      · exact hD.elim
      · have := vis_le h3; omega
    · have := vis_le h3; omega
  · intro hj
    have h' := this.2 (by
      rcases c_cover m q j h1 h2 hj with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h)
    rcases h' with (h | h) | h
    · exact h.elim
    · exact Or.inl h
    · exact Or.inr h

end PyLean.Accel
