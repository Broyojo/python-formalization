import PyLean.Accel.HeapifyLocalCanon

/-!
The Python heapify order and the C cache-friendly order
(`Modules/_heapqmodule.c:332-363`) both sift every internal node exactly
once, each after its internal children.

In 1-based numbering `u = i + 1`, the climb started at loop index `i` sifts
`u, u/2, u/4, ...` down to the first odd one, so it visits exactly the nodes
`w` with `i + 1 = (w + 1) * 2^t` (`Vis i w`). Loop 1 starts climbs at the
nodes `[mhalf, leftmost)` of the row above the last internal row, loop 2 at
the nodes `[leftmost, m)` of the last internal row.
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

theorem par_child {k c : Nat} (h : par c = k) (h0 : c ≠ 0) : c = 2 * k + 1 ∨ c = 2 * k + 2 := by
  unfold par at h; omega

/-! ### Generic validity facts -/

theorem hvalid_append (m : Nat) :
    ∀ (σ1 σ2 : List Nat) (D : Nat → Prop), HValid m D σ1 → HValid m (fun j => D j ∨ j ∈ σ1) σ2 →
      HValid m D (σ1 ++ σ2) := by
  intro σ1
  induction σ1 with
  | nil =>
    intro σ2 D _ h2
    have : (fun j => D j ∨ j ∈ ([] : List Nat)) = D := by funext j; simp
    rw [this] at h2; exact h2
  | cons k σ ih =>
    intro σ2 D h1 h2
    obtain ⟨a, b, c, d⟩ := h1
    refine ⟨a, b, c, ih σ2 _ d ?_⟩
    have e : (fun j => (D j ∨ j = k) ∨ j ∈ σ) = (fun j => D j ∨ j ∈ k :: σ) := by
      funext j; apply propext; simp only [List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
    rw [e]; exact h2

theorem hvalid_congr (m : Nat) (σ : List Nat) (D D' : Nat → Prop) (h : ∀ j, D j ↔ D' j)
    (hv : HValid m D σ) : HValid m D' σ := by
  have : D = D' := funext fun j => propext (h j)
  rw [← this]; exact hv

/-! ### The Python order -/

theorem hvalid_py (m : Nat) :
    ∀ k, k ≤ m → ∀ D : Nat → Prop, (∀ j, D j ↔ (k ≤ j ∧ j < m)) → HValid m D (List.range k).reverse := by
  intro k
  induction k with
  | zero => intro _ D _; simp [HValid]
  | succ k ih =>
    intro hk D hD
    rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine ⟨by omega, fun h => by have := (hD k).1 h; omega, ?_, ?_⟩
    · intro c hc hc0 hcm
      rcases par_child hc hc0 with rfl | rfl <;> exact (hD _).2 ⟨by omega, hcm⟩
    · apply ih (by omega)
      intro j
      rw [hD]
      omega

/-! ### Climbs -/

/-- The nodes sifted by `climb fuel h j`, in order. -/
def climbSeq : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, j => j :: (if j % 2 = 0 then [] else climbSeq f (j >>> 1))

theorem foldl_siftup_length (lt : α → α → Bool) :
    ∀ (σ : List Nat) (h : List α), (σ.foldl (fun h i => pySiftup lt h i) h).length = h.length := by
  intro σ
  induction σ with
  | nil => intro h; rfl
  | cons k σ ih => intro h; rw [List.foldl_cons, ih, pySiftup_length]

theorem climbSeq_le : ∀ f j w, w ∈ climbSeq f j → w ≤ j := by
  intro f
  induction f with
  | zero => intro j w h; simp [climbSeq] at h
  | succ f ih =>
    intro j w h
    simp only [climbSeq, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · split at h
      · simp at h
      · have := ih _ _ h; rw [shr1] at this; omega

theorem climb_eq (lt : α → α → Bool) :
    ∀ fuel (h : List α) j, (∀ w ∈ climbSeq fuel j, w < h.length) →
      climb lt fuel h j = .ok ((climbSeq fuel j).foldl (fun h i => pySiftup lt h i) h) := by
  intro fuel
  induction fuel with
  | zero => intro h j _; rfl
  | succ f ih =>
    intro h j hw
    simp only [climb, climbSeq]
    rw [cSiftup_eq lt h j (hw j (by simp [climbSeq]))]
    simp only [bind, Except.bind]
    split
    · rfl
    · rename_i hj
      simp only [List.foldl_cons]
      apply ih
      intro w hwm
      rw [pySiftup_length]
      exact hw w (by simp only [climbSeq, List.mem_cons]; right; rw [if_neg hj]; exact hwm)

theorem mem_downFrom (lo hi k : Nat) : k ∈ downFrom lo hi ↔ lo ≤ k ∧ k < hi := by
  simp only [downFrom, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨a, ha, rfl⟩; omega
  · intro h; exact ⟨hi - 1 - k, by omega, by omega⟩

theorem downFrom_cons (lo hi : Nat) (h : lo < hi) : downFrom lo hi = (hi - 1) :: downFrom lo (hi - 1) := by
  apply List.ext_getElem
  · simp [downFrom]; omega
  · intro k h1 h2
    cases k with
    | zero => simp [downFrom]
    | succ k => simp [downFrom]; omega

theorem downFrom_self (lo : Nat) : downFrom lo lo = [] := by simp [downFrom]

theorem forDown_climb (lt : α → α → Bool) :
    ∀ (is : List Nat) (h : List α), (∀ i ∈ is, i < h.length) →
      forDown (fun h i => climb lt (i + 1) h i) h is =
        .ok ((is.flatMap (fun i => climbSeq (i + 1) i)).foldl (fun h i => pySiftup lt h i) h) := by
  intro is
  induction is with
  | nil => intro h _; rfl
  | cons i is ih =>
    intro h hi
    simp only [forDown, List.foldlM_cons, List.flatMap_cons, List.foldl_append]
    rw [climb_eq lt (i + 1) h i (fun w hw => by
      have := climbSeq_le _ _ _ hw; have := hi i (by simp); omega)]
    simp only [bind, Except.bind]
    exact ih _ (fun j hj => by rw [foldl_siftup_length]; exact hi j (by simp [hj]))

/-! ### Powers of two -/

/-- `w` is sifted by the climb started at `i`. -/
def Vis (i w : Nat) : Prop := ∃ t, i + 1 = (w + 1) * 2 ^ t

theorem pow_split (a d : Nat) : 2 ^ (a + d) = 2 ^ a * 2 ^ d := Nat.pow_add 2 a d

theorem mul_pow_lt_mul_pow (X a b : Nat) (hX : 0 < X) (h : a < b) : X * 2 ^ a * 2 ≤ X * 2 ^ b := by
  have e : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← Nat.pow_add]; congr 1; omega
  have h2 : 2 ≤ 2 ^ (b - a) := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) (show 1 ≤ b - a by omega); simpa using this
  rw [e, ← Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ h2

theorem mul_pow_le_mul_pow (X a b : Nat) (h : a ≤ b) : X * 2 ^ a ≤ X * 2 ^ b :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) h)

/-- Two scalings of the same `X` by powers of two inside one row `[B, 2B)` are equal. -/
theorem row_unique (X a b B : Nat) (hX : 0 < X) (ha1 : B ≤ X * 2 ^ a) (ha2 : X * 2 ^ a < 2 * B)
    (hb1 : B ≤ X * 2 ^ b) (hb2 : X * 2 ^ b < 2 * B) : a = b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · have := mul_pow_lt_mul_pow X a b hX h; omega
  · exact h
  · have := mul_pow_lt_mul_pow X b a hX h; omega

theorem vis_le {i j : Nat} (h : Vis i j) : j ≤ i := by
  obtain ⟨t, ht⟩ := h
  have := Nat.le_mul_of_pos_right (j + 1) (Nat.two_pow_pos t); omega

theorem vis_left {i w : Nat} (h : Vis i w) (hne : w ≠ i) : Vis i (2 * w + 1) := by
  obtain ⟨t, ht⟩ := h
  cases t with
  | zero => simp at ht; omega
  | succ t =>
    refine ⟨t, ?_⟩
    rw [ht, Nat.pow_succ, show 2 * w + 1 + 1 = (w + 1) * 2 by omega, Nat.mul_assoc,
      Nat.mul_comm 2 (2 ^ t)]

theorem vis_half {i w : Nat} (h : Vis i w) (hw : w % 2 = 1) : Vis i (w / 2) := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t + 1, ?_⟩
  rw [ht, Nat.pow_succ, show w + 1 = (w / 2 + 1) * 2 by omega, Nat.mul_assoc,
    Nat.mul_comm 2 (2 ^ t)]

/-- If `x * 2^a = y * 2^b` with `x < y`, then `y = x * 2^(a - b)` and `b < a`. -/
theorem pow_ratio (x y a b : Nat) (h : x * 2 ^ a = y * 2 ^ b) (hxy : x < y) :
    b < a ∧ y = x * 2 ^ (a - b) := by
  have hba : b < a := by
    by_cases hab : a ≤ b
    · have h1 := mul_pow_le_mul_pow x a b hab
      have h2 : x * 2 ^ b < y * 2 ^ b := Nat.mul_lt_mul_of_pos_right hxy (Nat.two_pow_pos b)
      omega
    · omega
  refine ⟨hba, ?_⟩
  have e : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, ← Nat.mul_assoc] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos b) h).symm

/-- Strictly between two consecutive climb nodes there is no climb node, and a
node below `w` in the climb makes `w` odd. -/
theorem vis_between {i j w : Nat} (hj : Vis i j) (hw : Vis i w) (hjw : j < w) :
    w % 2 = 1 ∧ j ≤ w / 2 := by
  obtain ⟨a, ha⟩ := hj
  obtain ⟨b, hb⟩ := hw
  obtain ⟨hba, e⟩ := pow_ratio (j + 1) (w + 1) a b (ha.symm.trans hb) (by omega)
  have : 2 ^ (a - b) = 2 ^ (a - b - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [this, ← Nat.mul_assoc] at e
  have := Nat.le_mul_of_pos_right (j + 1) (Nat.two_pow_pos (a - b - 1))
  omega

/-! ### Validity of one climb -/

theorem climb_valid (m i : Nat) (D0 : Nat → Prop)
    (H : ∀ w, Vis i w → w < m ∧ ¬ D0 w ∧ (w = i → m ≤ 2 * w + 1) ∧ (2 * w + 2 < m → D0 (2 * w + 2))) :
    ∀ f w (D : Nat → Prop), w < f → Vis i w → (∀ j, D j ↔ D0 j ∨ (Vis i j ∧ w < j)) →
      HValid m D (climbSeq f w) ∧ (∀ j, (D j ∨ j ∈ climbSeq f w) ↔ (D0 j ∨ Vis i j)) := by
  intro f
  induction f with
  | zero => intro w _ hw; omega
  | succ f ih =>
    intro w D hwf hv hD
    obtain ⟨h1, h2, h3, h4⟩ := H w hv
    have hnD : ¬ D w := by
      intro h; rcases (hD w).1 h with h | h
      · exact h2 h
      · omega
    have hch : ∀ c, par c = w → c ≠ 0 → c < m → D c := by
      intro c hc hc0 hcm
      rcases par_child hc hc0 with rfl | rfl
      · by_cases e : w = i
        · have := h3 e; omega
        · exact (hD _).2 (Or.inr ⟨vis_left hv e, by omega⟩)
      · exact (hD _).2 (Or.inl (h4 hcm))
    simp only [climbSeq]
    by_cases hev : w % 2 = 0
    · simp only [hev, if_true]
      refine ⟨⟨h1, hnD, hch, trivial⟩, ?_⟩
      intro j
      simp only [List.mem_singleton]
      constructor
      · rintro (h | rfl)
        · rcases (hD j).1 h with h | h
          · exact Or.inl h
          · exact Or.inr h.1
        · exact Or.inr hv
      · rintro (h | h)
        · exact Or.inl ((hD j).2 (Or.inl h))
        · rcases Nat.lt_trichotomy j w with hl | rfl | hl
          · have := (vis_between h hv hl).1; omega
          · exact Or.inr rfl
          · exact Or.inl ((hD j).2 (Or.inr ⟨h, hl⟩))
    · simp only [hev, if_false, shr1]
      have hodd : w % 2 = 1 := by omega
      have hv' := vis_half hv hodd
      have hD' : ∀ j, (D j ∨ j = w) ↔ D0 j ∨ (Vis i j ∧ w / 2 < j) := by
        intro j
        constructor
        · rintro (h | rfl)
          · rcases (hD j).1 h with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h.1, by omega⟩
          · exact Or.inr ⟨hv, by omega⟩
        · rintro (h | ⟨h, hl⟩)
          · exact Or.inl ((hD j).2 (Or.inl h))
          · rcases Nat.lt_trichotomy j w with hl' | rfl | hl'
            · have := (vis_between h hv hl').2; omega
            · exact Or.inr rfl
            · exact Or.inl ((hD j).2 (Or.inr ⟨h, hl'⟩))
      obtain ⟨r1, r2⟩ := ih (w / 2) (fun j => D j ∨ j = w) (by omega) hv' hD'
      refine ⟨⟨h1, hnD, hch, r1⟩, ?_⟩
      intro j
      rw [← r2 j]
      simp only [List.mem_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)

/-! ### Validity of one loop of climbs -/

theorem phase_valid (m lo hi : Nat) (D0 : Nat → Prop)
    (H : ∀ i, lo ≤ i → i < hi → ∀ w, Vis i w → w < m ∧ ¬ D0 w ∧
      (∀ i', i < i' → i' < hi → ¬ Vis i' w) ∧ (w = i → m ≤ 2 * w + 1) ∧
      (2 * w + 2 < m → D0 (2 * w + 2) ∨ ∃ i', i < i' ∧ i' < hi ∧ Vis i' (2 * w + 2))) :
    ∀ d c, c - lo = d → lo ≤ c → c ≤ hi → ∀ D : Nat → Prop,
      (∀ j, D j ↔ D0 j ∨ ∃ i', c ≤ i' ∧ i' < hi ∧ Vis i' j) →
      HValid m D ((downFrom lo c).flatMap (fun i => climbSeq (i + 1) i)) ∧
      ∀ j, (D j ∨ j ∈ (downFrom lo c).flatMap (fun i => climbSeq (i + 1) i)) ↔
        D0 j ∨ ∃ i', lo ≤ i' ∧ i' < hi ∧ Vis i' j := by
  intro d
  induction d with
  | zero =>
    intro c hc hlo _ D hD
    have hcl : c = lo := by omega
    subst hcl
    rw [downFrom_self]
    refine ⟨trivial, fun j => ?_⟩
    simp only [List.flatMap_nil, List.not_mem_nil, or_false]
    exact hD j
  | succ d ih =>
    intro c hc hlo hhi D hD
    rw [downFrom_cons lo c (by omega), List.flatMap_cons]
    have hi1 : c - 1 + 1 = c := by omega
    rw [hi1]
    -- the climb from c - 1
    have Hc : ∀ w, Vis (c - 1) w → w < m ∧ ¬ D w ∧ (w = c - 1 → m ≤ 2 * w + 1) ∧
        (2 * w + 2 < m → D (2 * w + 2)) := by
      intro w hw
      obtain ⟨a1, a2, a3, a4, a5⟩ := H (c - 1) (by omega) (by omega) w hw
      refine ⟨a1, ?_, a4, ?_⟩
      · intro h
        rcases (hD w).1 h with h | ⟨i', h1, h2, h3⟩
        · exact a2 h
        · exact a3 i' (by omega) h2 h3
      · intro hm
        rcases a5 hm with h | ⟨i', h1, h2, h3⟩
        · exact (hD _).2 (Or.inl h)
        · exact (hD _).2 (Or.inr ⟨i', by omega, h2, h3⟩)
    obtain ⟨v1, v2⟩ := climb_valid m (c - 1) D Hc c (c - 1) D (by omega) ⟨0, by simp⟩ (by
      intro j
      constructor
      · intro h; exact Or.inl h
      · rintro (h | ⟨h, hl⟩)
        · exact h
        · have := vis_le h; omega)
    obtain ⟨w1, w2⟩ := ih (c - 1) (by omega) (by omega) (by omega)
      (fun j => D j ∨ j ∈ climbSeq c (c - 1)) (by
        intro j
        rw [v2 j, hD j]
        constructor
        · rintro ((h | ⟨i', h1, h2, h3⟩) | h)
          · exact Or.inl h
          · exact Or.inr ⟨i', by omega, h2, h3⟩
          · exact Or.inr ⟨c - 1, Nat.le_refl _, by omega, h⟩
        · rintro (h | ⟨i', h1, h2, h3⟩)
          · exact Or.inl (Or.inl h)
          · by_cases e : i' = c - 1
            · subst e; exact Or.inr h3
            · exact Or.inl (Or.inr ⟨i', by omega, h2, h3⟩))
    refine ⟨hvalid_append m _ _ D v1 w1, fun j => ?_⟩
    rw [← w2 j, List.mem_append]
    constructor
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

end PyLean.Accel
