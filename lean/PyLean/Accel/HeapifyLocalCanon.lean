import PyLean.Accel.HeapifyLocal

/-!
The canonical bottom-up heapify `hcanon`, and the theorem that sifting every
internal node once, each after its internal children, in any order, yields
`hcanon 0` (for an arbitrary comparison).
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

/-! ### Subtree facts -/

theorem desc_decomp {k p : Nat} (h : Desc k p) : p = k ∨ Desc (2 * k + 1) p ∨ Desc (2 * k + 2) p := by
  induction h with
  | refl => exact Or.inl rfl
  | @left c _ ih =>
    rcases ih with rfl | h | h
    · exact Or.inr (Or.inl Desc.refl)
    · exact Or.inr (Or.inl (Desc.left h))
    · exact Or.inr (Or.inr (Desc.left h))
  | @right c _ ih =>
    rcases ih with rfl | h | h
    · exact Or.inr (Or.inr Desc.refl)
    · exact Or.inr (Or.inl (Desc.right h))
    · exact Or.inr (Or.inr (Desc.right h))

theorem desc_comparable : ∀ (p a b : Nat), Desc a p → Desc b p → Desc a b ∨ Desc b a := by
  intro p
  induction p using Nat.strongRecOn with
  | _ p ih =>
    intro a b ha hb
    by_cases hpa : p = a
    · subst hpa; exact Or.inr hb
    · by_cases hpb : p = b
      · subst hpb; exact Or.inl ha
      · have h1 := ha.up hpa
        have h2 := hb.up hpb
        have : par p < p := by have := ha.le; unfold par; omega
        exact ih (par p) this a b h1 h2

theorem desc_ne_of_lt {a b : Nat} (h : b < a) : ¬ Desc a b := fun d => by have := d.le; omega

theorem siblings_disjoint (k p : Nat) (h1 : Desc (2 * k + 1) p) (h2 : Desc (2 * k + 2) p) : False := by
  rcases desc_comparable p _ _ h1 h2 with h | h
  · have := h.up (by omega)
    have h' : par (2 * k + 2) = k := by unfold par; omega
    rw [h'] at this
    exact desc_ne_of_lt (by omega) this
  · exact desc_ne_of_lt (by omega) h

theorem desc_child_k {k : Nat} : Desc k (2 * k + 1) ∧ Desc k (2 * k + 2) :=
  ⟨Desc.left Desc.refl, Desc.right Desc.refl⟩

theorem at!_eq_getElem' (l : List α) (i : Nat) (h : i < l.length) : at! l i = l[i] := by
  simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem list_ext_at! (l1 l2 : List α) (hl : l1.length = l2.length) (h : ∀ p, at! l1 p = at! l2 p) :
    l1 = l2 := by
  apply List.ext_getElem hl
  intro i h1 h2
  rw [← at!_eq_getElem' _ _ h1, ← at!_eq_getElem' _ _ h2, h]

/-! ### siftup on a leaf -/

theorem sdLoop_start (lt : α → α → Bool) (x : α) (s fuel : Nat) (h : List α) :
    pySiftdownLoop lt x s fuel h s = (h, s) := by
  cases fuel <;> simp [pySiftdownLoop]

theorem suLoop_leaf (lt : α → α → Bool) (e fuel : Nat) (h : List α) (pos : Nat) (hp : e ≤ 2 * pos + 1) :
    pySiftupLoop lt e fuel h pos = (h, pos) := by
  cases fuel with
  | zero => rfl
  | succ f => simp only [pySiftupLoop]; rw [if_neg (by omega)]

theorem pySiftup_leaf (lt : α → α → Bool) (l : List α) (k : Nat) (hk : l.length ≤ 2 * k + 1) :
    pySiftup lt l k = l := by
  simp only [pySiftup]
  rw [suLoop_leaf lt _ _ l k hk]
  simp only [set_at!_self, pySiftdown, sdLoop_start]

/-! ### The canonical bottom-up heapify of a subtree -/

/-- Heapify the subtree of `k` bottom-up (children first, then sift `k`). -/
def hcanon (lt : α → α → Bool) (n : Nat) (k : Nat) (l : List α) : List α :=
  if k < n then pySiftup lt (hcanon lt n (2 * k + 2) (hcanon lt n (2 * k + 1) l)) k else l
termination_by n - k

theorem hcanon_eq (lt : α → α → Bool) (n k : Nat) (l : List α) :
    hcanon lt n k l =
      if k < n then pySiftup lt (hcanon lt n (2 * k + 2) (hcanon lt n (2 * k + 1) l)) k else l := by
  rw [hcanon]

theorem hcanon_props (lt : α → α → Bool) (n : Nat) :
    ∀ d k, n - k = d → ∀ (l : List α),
      (hcanon lt n k l).length = l.length ∧
      (∀ q, ¬ Desc k q → at! (hcanon lt n k l) q = at! l q) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro k hd l
    rw [hcanon_eq]
    split
    · rename_i hk
      obtain ⟨a1, b1⟩ := ih (n - (2 * k + 1)) (by omega) (2 * k + 1) rfl l
      obtain ⟨a2, b2⟩ := ih (n - (2 * k + 2)) (by omega) (2 * k + 2) rfl (hcanon lt n (2 * k + 1) l)
      refine ⟨by rw [pySiftup_length, a2, a1], ?_⟩
      intro q hq
      rw [pySiftup_frame lt _ k q hq, b2 q (fun h => hq (desc_child_k.2.trans h)),
        b1 q (fun h => hq (desc_child_k.1.trans h))]
    · exact ⟨rfl, fun _ _ => rfl⟩

theorem hcanon_length (lt : α → α → Bool) (n k : Nat) (l : List α) :
    (hcanon lt n k l).length = l.length := (hcanon_props lt n _ k rfl l).1

theorem hcanon_frame (lt : α → α → Bool) (n k : Nat) (l : List α) :
    ∀ q, ¬ Desc k q → at! (hcanon lt n k l) q = at! l q := (hcanon_props lt n _ k rfl l).2

theorem hcanon_local (lt : α → α → Bool) (n : Nat) :
    ∀ d k, n - k = d → ∀ (l1 l2 : List α), l1.length = l2.length → AgreeOn k l1 l2 →
      AgreeOn k (hcanon lt n k l1) (hcanon lt n k l2) := by
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
    intro k hd l1 l2 hl ha
    rw [hcanon_eq lt n k l1, hcanon_eq lt n k l2]
    split
    · rename_i hk
      have e1 : AgreeOn k (hcanon lt n (2 * k + 1) l1) (hcanon lt n (2 * k + 1) l2) := by
        intro p hp
        by_cases h : Desc (2 * k + 1) p
        · exact ih _ (by omega) (2 * k + 1) rfl l1 l2 hl (fun q hq => ha q (desc_child_k.1.trans hq)) p h
        · rw [hcanon_frame _ _ _ _ p h, hcanon_frame _ _ _ _ p h, ha p hp]
      have hl1 : (hcanon lt n (2 * k + 1) l1).length = (hcanon lt n (2 * k + 1) l2).length := by
        simp [hcanon_length, hl]
      have e2 : AgreeOn k (hcanon lt n (2 * k + 2) (hcanon lt n (2 * k + 1) l1))
          (hcanon lt n (2 * k + 2) (hcanon lt n (2 * k + 1) l2)) := by
        intro p hp
        by_cases h : Desc (2 * k + 2) p
        · exact ih _ (by omega) (2 * k + 2) rfl _ _ hl1 (fun q hq => e1 q (desc_child_k.2.trans hq)) p h
        · rw [hcanon_frame _ _ _ _ p h, hcanon_frame _ _ _ _ p h, e1 p hp]
      exact pySiftup_local lt _ _ k (by simp [hcanon_length, hl]) e2
    · exact ha

theorem hcanon_leaf (lt : α → α → Bool) (n k : Nat) (l : List α) (hl : l.length = n)
    (hk : n ≤ 2 * k + 1) : hcanon lt n k l = l := by
  rw [hcanon_eq]
  split
  · rw [hcanon_eq lt n (2 * k + 1), if_neg (by omega), hcanon_eq lt n (2 * k + 2), if_neg (by omega)]
    exact pySiftup_leaf lt l k (by omega)
  · rfl

/-! ### Any children-first order yields `hcanon 0` -/

/-- Invariant after sifting the set `D` of internal nodes. -/
structure HInv (lt : α → α → Bool) (n : Nat) (init : List α) (D : Nat → Prop) (l : List α) : Prop where
  len : l.length = n
  lt_m : ∀ j, D j → j < n / 2
  closed : ∀ j c, D j → par c = j → c ≠ 0 → c < n / 2 → D c
  untouched : ∀ p, (∀ j, D j → ¬ Desc j p) → at! l p = at! init p
  top : ∀ j, D j → (j = 0 ∨ ¬ D (par j)) → AgreeOn j l (hcanon lt n j init)

/-- `σ` sifts internal nodes, each once and after its internal children. -/
def HValid (m : Nat) : (Nat → Prop) → List Nat → Prop
  | _, [] => True
  | D, k :: σ => k < m ∧ ¬ D k ∧ (∀ c, par c = k → c ≠ 0 → c < m → D c) ∧
      HValid m (fun j => D j ∨ j = k) σ

theorem HInv.closure {lt : α → α → Bool} {n : Nat} {init : List α} {D : Nat → Prop} {l : List α}
    (h : HInv lt n init D l) {j p : Nat} (hd : Desc j p) (hj : D j) (hp : p < n / 2) : D p := by
  induction hd with
  | refl => exact hj
  | @left c _ ih =>
    exact h.closed c _ (ih (by omega)) (by unfold par; omega) (by omega) hp
  | @right c _ ih =>
    exact h.closed c _ (ih (by omega)) (by unfold par; omega) (by omega) hp

theorem hinv_step (lt : α → α → Bool) (n : Nat) (init : List α) (hinit : init.length = n)
    (D : Nat → Prop) (l : List α) (h : HInv lt n init D l) (k : Nat) (hk : k < n / 2) (hnk : ¬ D k)
    (hch : ∀ c, par c = k → c ≠ 0 → c < n / 2 → D c) :
    HInv lt n init (fun j => D j ∨ j = k) (pySiftup lt l k) := by
  have hkn : k < n := by omega
  have notAnc : ∀ j, D j → ¬ Desc j k := fun j hj hd => hnk (h.closure hd hj hk)
  -- values on a child subtree are canonical
  have child : ∀ c, par c = k → c ≠ 0 → ∀ p, Desc c p → at! l p = at! (hcanon lt n c init) p := by
    intro c hc hc0 p hp
    by_cases hcm : c < n / 2
    · exact h.top c (hch c hc hc0 hcm) (Or.inr (by rw [hc]; exact hnk)) p hp
    · rw [hcanon_leaf lt n c init hinit (by omega)]
      apply h.untouched
      intro j hj hjp
      rcases desc_comparable p j c hjp hp with hjc | hcj
      · by_cases e : j = c
        · subst e; exact hcm (h.lt_m _ hj)
        · have := hjc.up (Ne.symm e)
          rw [hc] at this
          exact notAnc j hj this
      · have := hcj.le; have := h.lt_m j hj; omega
  refine ⟨by rw [pySiftup_length, h.len], ?_, ?_, ?_, ?_⟩
  · rintro j (hj | rfl)
    · exact h.lt_m j hj
    · exact hk
  · rintro j c (hj | rfl) hc hc0 hcm
    · exact Or.inl (h.closed j c hj hc hc0 hcm)
    · exact Or.inl (hch c hc hc0 hcm)
  · intro p hp
    have hkp : ¬ Desc k p := fun d => hp k (Or.inr rfl) d
    rw [pySiftup_frame lt l k p hkp]
    exact h.untouched p (fun j hj => hp j (Or.inl hj))
  · rintro j hj htop
    rcases hj with hj | rfl
    · -- an older top node: its subtree is disjoint from k's
      have htop' : j = 0 ∨ ¬ D (par j) := by
        rcases htop with h0 | h0
        · exact Or.inl h0
        · exact Or.inr (fun hh => h0 (Or.inl hh))
      intro p hp
      have hkp : ¬ Desc k p := by
        intro hkp
        rcases desc_comparable p j k hp hkp with hjk | hkj
        · exact notAnc j hj hjk
        · have hjk : j ≠ k := fun e => hnk (e ▸ hj)
          have hjm := h.lt_m j hj
          have key : ∀ c, par c = k → c ≠ 0 → Desc c j → False := by
            intro c hc hc0 hcj
            have hj0 : j ≠ 0 := by have := hcj.le; omega
            by_cases e : j = c
            · rcases htop with h0 | h0
              · exact hj0 h0
              · exact h0 (Or.inr (by rw [e]; exact hc))
            · have hpj : ¬ D (par j) := by
                rcases htop' with h0 | h0
                · exact absurd h0 hj0
                · exact h0
              have hup := hcj.up e
              have hpm : par j < n / 2 := by unfold par; omega
              exact hpj (h.closure hup (hch c hc hc0 (by have := hcj.le; omega)) hpm)
          rcases desc_decomp hkj with e | hc | hc
          · exact hjk e
          · exact key _ (by unfold par; omega) (by omega) hc
          · exact key _ (by unfold par; omega) (by omega) hc
      rw [pySiftup_frame lt l k p hkp]
      exact h.top j hj htop' p hp
    · -- the new node
      rw [hcanon_eq, if_pos hkn]
      apply pySiftup_local lt _ _ j (by rw [h.len, hcanon_length, hcanon_length, hinit])
      intro p hp
      rcases desc_decomp hp with rfl | hc | hc
      · rw [h.untouched p (fun j' hj' => notAnc j' hj'),
          hcanon_frame _ _ _ _ p (desc_ne_of_lt (by omega)),
          hcanon_frame _ _ _ _ p (desc_ne_of_lt (by omega))]
      · rw [child _ (by unfold par; omega) (by omega) p hc,
          hcanon_frame _ _ (2 * j + 2) _ p (fun h2 => siblings_disjoint j p hc h2)]
      · rw [child _ (by unfold par; omega) (by omega) p hc]
        apply hcanon_local lt n _ _ rfl _ _ (by rw [hcanon_length]) _ p hc
        intro q hq
        exact (hcanon_frame lt n _ init q (fun h1 => siblings_disjoint j q h1 hq)).symm

theorem hinv_process (lt : α → α → Bool) (n : Nat) (init : List α) (hinit : init.length = n) :
    ∀ (σ : List Nat) (D : Nat → Prop) (l : List α), HInv lt n init D l → HValid (n / 2) D σ →
      HInv lt n init (fun j => D j ∨ j ∈ σ) (σ.foldl (fun h i => pySiftup lt h i) l) := by
  intro σ
  induction σ with
  | nil =>
    intro D l h _
    have : (fun j => D j ∨ j ∈ ([] : List Nat)) = D := by funext j; simp
    rw [List.foldl_nil, this]; exact h
  | cons k σ ih =>
    intro D l h hv
    obtain ⟨hk, hnk, hch, hv'⟩ := hv
    have h' := hinv_step lt n init hinit D l h k hk hnk hch
    have := ih _ _ h' hv'
    have e : (fun j => (D j ∨ j = k) ∨ j ∈ σ) = (fun j => D j ∨ j ∈ k :: σ) := by
      funext j; apply propext; simp only [List.mem_cons]
      constructor
      · rintro ((h1 | h1) | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h1)
      · rintro (h1 | h1 | h1)
        · exact Or.inl (Or.inl h1)
        · exact Or.inl (Or.inr h1)
        · exact Or.inr h1
    rw [List.foldl_cons, ← e]
    exact this

/-- Sifting all internal nodes of an `n`-element list once each, children
first, gives `hcanon 0`, whatever the order. -/
theorem foldl_eq_hcanon (lt : α → α → Bool) (n : Nat) (init : List α) (hinit : init.length = n)
    (hm : 0 < n / 2) (σ : List Nat) (hv : HValid (n / 2) (fun _ => False) σ)
    (hcov : ∀ j, j ∈ σ ↔ j < n / 2) :
    σ.foldl (fun h i => pySiftup lt h i) init = hcanon lt n 0 init := by
  have h0 : HInv lt n init (fun _ => False) init :=
    ⟨hinit, fun _ h => h.elim, fun _ _ h => h.elim, fun _ _ => rfl, fun _ h => h.elim⟩
  have h := hinv_process lt n init hinit σ _ init h0 hv
  have ha := h.top 0 (Or.inr ((hcov 0).2 hm)) (Or.inl rfl)
  apply list_ext_at! _ _ (by rw [h.len, hcanon_length, hinit])
  intro p
  exact ha p (desc_zero p)

end PyLean.Accel
