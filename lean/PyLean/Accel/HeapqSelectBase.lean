import PyLean.Accel.HeapqSelect
import PyLean.Accel.HeapqProps
import PyLean.Accel.SelectProps

/-!
Tools for the `nsmallest` / `nlargest` / `merge` theorems: lexicographic strict weak orders,
the rank of an element in a finite universe (which turns a strict weak order on the
elements actually present into an int key), and the commutation of the pure heap functions of
`Heap.lean` with relabelling the items.
-/

namespace PyLean.Accel.Heapq

open PyLean

/-! ### Strict weak orders -/

theorem sw_equiv_trans {α : Type} {r : α → α → Bool} (h : Accel.StrictWeak r) {a b c : α}
    (h1 : r a b = false) (h2 : r b a = false) (h3 : r b c = false) (h4 : r c b = false) :
    r a c = false ∧ r c a = false := by
  constructor
  · cases hac : r a c
    · rfl
    · rcases h.negTrans a b c hac with h' | h'
      · rw [h1] at h'; cases h'
      · rw [h3] at h'; cases h'
  · cases hca : r c a
    · rfl
    · rcases h.negTrans c b a hca with h' | h'
      · rw [h4] at h'; cases h'
      · rw [h2] at h'; cases h'

/-- The lexicographic product of two strict weak orders. -/
def lexLt {α β : Type} (r : α → α → Bool) (s : β → β → Bool) (x y : α × β) : Bool :=
  r x.1 y.1 || (!r x.1 y.1 && !r y.1 x.1 && s x.2 y.2)

theorem StrictWeak.lex {α β : Type} {r : α → α → Bool} {s : β → β → Bool} (hr : Accel.StrictWeak r)
    (hs : Accel.StrictWeak s) : Accel.StrictWeak (lexLt r s) where
  irrefl x := by simp [lexLt, hr.irrefl, hs.irrefl]
  trans x y z h1 h2 := by
    obtain ⟨x, x2⟩ := x; obtain ⟨y, y2⟩ := y; obtain ⟨z, z2⟩ := z
    simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    rcases h1 with h1 | ⟨⟨h1a, h1b⟩, h1c⟩ <;> rcases h2 with h2 | ⟨⟨h2a, h2b⟩, h2c⟩
    · exact Or.inl (hr.trans _ _ _ h1 h2)
    · left
      rcases hr.negTrans x z y h1 with h | h
      · exact h
      · rw [h2b] at h; cases h
    · left
      rcases hr.negTrans y x z h2 with h | h
      · rw [h1b] at h; cases h
      · exact h
    · obtain ⟨e1, e2⟩ := sw_equiv_trans hr h1a h1b h2a h2b
      exact Or.inr ⟨⟨e1, e2⟩, hs.trans _ _ _ h1c h2c⟩
  negTrans x y z h := by
    obtain ⟨x, x2⟩ := x; obtain ⟨y, y2⟩ := y; obtain ⟨z, z2⟩ := z
    simp only [lexLt, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at *
    rcases h with h | ⟨⟨ha, hb⟩, hc⟩
    · rcases hr.negTrans x y z h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr (Or.inl h')
    · cases hxy : r x y
      · cases hyz : r y z
        · -- x ~ y ~ z
          have hyx : r y x = false := by
            cases hyx : r y x
            · rfl
            · rcases hr.negTrans y z x hyx with h' | h'
              · rw [hyz] at h'; cases h'
              · rw [hb] at h'; cases h'
          have hzy : r z y = false := by
            cases hzy : r z y
            · rfl
            · rcases hr.negTrans z x y hzy with h' | h'
              · rw [hb] at h'; cases h'
              · rw [hxy] at h'; cases h'
          rcases hs.negTrans x2 y2 z2 hc with h' | h'
          · exact Or.inl (Or.inr ⟨⟨rfl, hyx⟩, h'⟩)
          · exact Or.inr (Or.inr ⟨⟨rfl, hzy⟩, h'⟩)
        · exact Or.inr (Or.inl rfl)
      · exact Or.inl (Or.inl rfl)

theorem StrictWeak.pullback {α β : Type} {r : β → β → Bool} (hr : Accel.StrictWeak r) (f : α → β) :
    Accel.StrictWeak (fun a b => r (f a) (f b)) where
  irrefl a := hr.irrefl _
  trans _ _ _ h1 h2 := hr.trans _ _ _ h1 h2
  negTrans _ _ _ h := hr.negTrans _ _ _ h

def intLtB (a b : Int) : Bool := decide (a < b)

theorem strictWeak_intLtB : Accel.StrictWeak intLtB := Accel.strictWeak_int

/-! ### Rank in a finite universe -/

/-- How many items of `K` are below `a`. -/
def rank {α : Type} (r : α → α → Bool) (K : List α) (a : α) : Nat := K.countP (fun y => r y a)

theorem countP_lt_of {α : Type} (p q : α → Bool) :
    ∀ (K : List α), (∀ y ∈ K, p y = true → q y = true) → (∃ y ∈ K, q y = true ∧ p y = false) →
      K.countP p < K.countP q
  | [], _, ⟨y, hy, _⟩ => by simp at hy
  | x :: K, h, ⟨y, hy, hq, hp⟩ => by
    simp only [List.countP_cons]
    have hle := List.countP_mono_left (l := K) (fun z hz => h z (by simp [hz]))
    rcases List.mem_cons.1 hy with rfl | hy
    · simp only [hp, hq]; simp; omega
    · have := countP_lt_of p q K (fun z hz => h z (by simp [hz])) ⟨y, hy, hq, hp⟩
      have hx := h x (by simp)
      cases hpx : p x <;> cases hqx : q x <;> simp_all <;> omega

theorem rank_le {α : Type} {r : α → α → Bool} (hr : Accel.StrictWeak r) (K : List α) {a b : α}
    (h : r a b = false) : rank r K b ≤ rank r K a := by
  apply List.countP_mono_left
  intro y _ hy
  rcases hr.negTrans y a b hy with h' | h'
  · exact h'
  · rw [h] at h'; cases h'

theorem rank_lt {α : Type} {r : α → α → Bool} (hr : Accel.StrictWeak r) (K : List α) {a b : α}
    (ha : a ∈ K) (h : r a b = true) : rank r K a < rank r K b := by
  apply countP_lt_of
  · intro y _ hy; exact hr.trans _ _ _ hy h
  · exact ⟨a, ha, h, hr.irrefl a⟩

/-- On items of `K`, `r` is the order of the ranks. -/
theorem rank_spec {α : Type} {r : α → α → Bool} (hr : Accel.StrictWeak r) (K : List α) {a b : α}
    (ha : a ∈ K) (hb : b ∈ K) : r a b = decide (rank r K a < rank r K b) := by
  cases h : r a b
  · have := rank_le hr K h; simp; omega
  · have := rank_lt hr K ha h; simp [this]

/-! ### Relabelling the items of the pure heap functions -/

variable {β γ : Type} [Inhabited β] [Inhabited γ]

theorem at!_map' (φ : β → γ) (hd : φ default = default) (l : List β) (i : Nat) :
    Accel.at! (l.map φ) i = φ (Accel.at! l i) := by
  simp only [Accel.at!, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp [hd]

variable (φ : β → γ) (hd : φ default = default) (lt : β → β → Bool) (lt' : γ → γ → Bool)
  (hφ : ∀ a b, lt' (φ a) (φ b) = lt a b)

include hd hφ in
theorem pySiftdownLoop_map (x : β) (s : Nat) :
    ∀ (fuel : Nat) (l : List β) (pos : Nat),
      Accel.pySiftdownLoop lt' (φ x) s fuel (l.map φ) pos =
        ((Accel.pySiftdownLoop lt x s fuel l pos).1.map φ, (Accel.pySiftdownLoop lt x s fuel l pos).2) := by
  intro fuel
  induction fuel with
  | zero => intro l pos; rfl
  | succ fuel ih =>
    intro l pos
    simp only [Accel.pySiftdownLoop, at!_map' φ hd, hφ]
    split
    · split
      · rw [← List.map_set, ih]
      · rfl
    · rfl

include hd hφ in
theorem pySiftdown_map (l : List β) (s pos : Nat) :
    Accel.pySiftdown lt' (l.map φ) s pos = (Accel.pySiftdown lt l s pos).map φ := by
  simp only [Accel.pySiftdown, at!_map' φ hd]
  rw [pySiftdownLoop_map φ hd lt lt' hφ, List.map_set]

include hd hφ in
theorem pySiftupLoop_map (endpos : Nat) :
    ∀ (fuel : Nat) (l : List β) (pos : Nat),
      Accel.pySiftupLoop lt' endpos fuel (l.map φ) pos =
        ((Accel.pySiftupLoop lt endpos fuel l pos).1.map φ, (Accel.pySiftupLoop lt endpos fuel l pos).2) := by
  intro fuel
  induction fuel with
  | zero => intro l pos; rfl
  | succ fuel ih =>
    intro l pos
    simp only [Accel.pySiftupLoop, at!_map' φ hd, hφ]
    split
    · rw [← List.map_set, ih]
    · rfl

include hd hφ in
theorem pySiftup_map (l : List β) (pos : Nat) :
    Accel.pySiftup lt' (l.map φ) pos = (Accel.pySiftup lt l pos).map φ := by
  simp only [Accel.pySiftup, at!_map' φ hd, List.length_map]
  rw [pySiftupLoop_map φ hd lt lt' hφ, ← List.map_set, pySiftdown_map φ hd lt lt' hφ]

include hd hφ in
theorem pyHeapify_map (l : List β) :
    Accel.pyHeapify lt' (l.map φ) = (Accel.pyHeapify lt l).map φ := by
  simp only [Accel.pyHeapify, List.length_map]
  generalize (List.range (l.length / 2)).reverse = is
  induction is generalizing l with
  | nil => rfl
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [pySiftup_map φ hd lt lt' hφ, ih]

include hd hφ in
theorem pyHeapreplace_map (l : List β) (item : β) :
    Accel.pyHeapreplace lt' (l.map φ) (φ item) =
      (Accel.pyHeapreplace lt l item).map (fun p => (φ p.1, p.2.map φ)) := by
  cases l with
  | nil => rfl
  | cons y ys =>
    have e1 : Accel.pyHeapreplace lt' ((y :: ys).map φ) (φ item) =
        .ok (Accel.at! ((y :: ys).map φ) 0, Accel.pySiftup lt' (((y :: ys).map φ).set 0 (φ item)) 0) := rfl
    have e2 : Accel.pyHeapreplace lt (y :: ys) item =
        .ok (Accel.at! (y :: ys) 0, Accel.pySiftup lt ((y :: ys).set 0 item) 0) := rfl
    rw [e1, e2, at!_map' φ hd, ← List.map_set, pySiftup_map φ hd lt lt' hφ]
    rfl

end PyLean.Accel.Heapq
