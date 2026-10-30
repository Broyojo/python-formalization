import PyLean.Accel.Select

/-!
Python's `sorted(l, key=kf)` as a specification: the stable sort by an int key.
`StableSortedBy kf l l'` says `l'` is sorted by `kf` and, for every key value,
lists the items with that key in the order they have in `l`. That determines
`l'` uniquely, and `List.mergeSort` satisfies it.
-/

namespace PyLean.Accel

/-- The stable sort of `l` by `kf`. -/
def stableSort (kf : Int → Int) (l : List Int) : List Int :=
  l.mergeSort (fun a b => decide (kf a ≤ kf b))

def StableSortedBy (kf : Int → Int) (l l' : List Int) : Prop :=
  l'.Pairwise (fun a b => kf a ≤ kf b) ∧
    ∀ k, l'.filter (fun e => kf e == k) = l.filter (fun e => kf e == k)

theorem sorted_filter_unique (kf : Int → Int) :
    ∀ (l1 l2 : List Int), l1.Pairwise (fun a b => kf a ≤ kf b) → l2.Pairwise (fun a b => kf a ≤ kf b) →
      (∀ k, l1.filter (fun e => kf e == k) = l2.filter (fun e => kf e == k)) → l1 = l2 := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 _ _ hf
    cases l2 with
    | nil => rfl
    | cons b t2 =>
      have := hf (kf b)
      simp at this
  | cons a t1 ih =>
    intro l2 h1 h2 hf
    have hmem : ∀ x, x ∈ a :: t1 ↔ x ∈ l2 := by
      intro x
      have := hf (kf x)
      constructor
      · intro hx
        have : x ∈ (a :: t1).filter (fun e => kf e == kf x) := List.mem_filter.2 ⟨hx, by simp⟩
        rw [hf (kf x)] at this
        exact (List.mem_filter.1 this).1
      · intro hx
        have : x ∈ l2.filter (fun e => kf e == kf x) := List.mem_filter.2 ⟨hx, by simp⟩
        rw [← hf (kf x)] at this
        exact (List.mem_filter.1 this).1
    cases l2 with
    | nil => have := (hmem a).1 (by simp); simp at this
    | cons b t2 =>
      have hab : kf a = kf b := by
        have ha : a ∈ b :: t2 := (hmem a).1 (by simp)
        have hb : b ∈ a :: t1 := (hmem b).2 (by simp)
        have e1 : kf b ≤ kf a := by
          rcases List.mem_cons.1 ha with rfl | ha
          · exact Int.le_refl _
          · exact (List.pairwise_cons.1 h2).1 a ha
        have e2 : kf a ≤ kf b := by
          rcases List.mem_cons.1 hb with rfl | hb
          · exact Int.le_refl _
          · exact (List.pairwise_cons.1 h1).1 b hb
        omega
      have hk := hf (kf a)
      simp only [List.filter_cons, beq_self_eq_true, if_true, hab] at hk
      simp only [← hab, beq_self_eq_true, if_true, List.cons.injEq] at hk
      obtain ⟨rfl, ht⟩ := hk
      congr 1
      apply ih t2 (List.pairwise_cons.1 h1).2 (List.pairwise_cons.1 h2).2
      intro k
      by_cases hka : kf a = k
      · subst hka; exact ht
      · have := hf k
        simp only [List.filter_cons] at this
        have hne : (kf a == k) = false := by simp [hka]
        rw [hne] at this
        simpa using this

theorem stableSorted_unique (kf : Int → Int) (l l1 l2 : List Int) (h1 : StableSortedBy kf l l1)
    (h2 : StableSortedBy kf l l2) : l1 = l2 :=
  sorted_filter_unique kf l1 l2 h1.1 h2.1 (fun k => (h1.2 k).trans (h2.2 k).symm)

theorem stableSort_spec (kf : Int → Int) (l : List Int) : StableSortedBy kf l (stableSort kf l) := by
  have trans : ∀ a b c : Int, decide (kf a ≤ kf b) = true → decide (kf b ≤ kf c) = true →
      decide (kf a ≤ kf c) = true := by
    intro a b c h1 h2; simp at *; omega
  have total : ∀ a b : Int, (decide (kf a ≤ kf b) || decide (kf b ≤ kf a)) = true := by
    intro a b; simp; omega
  refine ⟨?_, ?_⟩
  · have := List.pairwise_mergeSort trans total l
    exact this.imp (fun h => by simpa using h)
  · intro k
    let p : Int → Bool := fun e => kf e == k
    have hsub : List.Sublist (l.filter p) (stableSort kf l) := by
      apply List.sublist_mergeSort trans total _ (List.filter_sublist)
      apply List.Pairwise.imp_of_mem _ (List.pairwise_of_forall (R := fun _ _ => True) (fun _ _ => trivial))
      intro a b ha hb _
      have := (List.mem_filter.1 ha).2
      have := (List.mem_filter.1 hb).2
      simp_all [p]
    have hsub2 : List.Sublist (l.filter p) ((stableSort kf l).filter p) := by
      have := hsub.filter p
      rwa [List.filter_filter, show (fun x => p x && p x) = p by funext x; simp] at this
    have hlen : ((stableSort kf l).filter p).length = (l.filter p).length :=
      ((List.mergeSort_perm l _).filter p).length_eq
    exact (hsub2.eq_of_length hlen.symm).symm

theorem stableSort_eq (kf : Int → Int) (l l' : List Int) (h : StableSortedBy kf l l') :
    stableSort kf l = l' :=
  stableSorted_unique kf l _ _ (stableSort_spec kf l) h

theorem stableSort_perm (kf : Int → Int) (l : List Int) : (stableSort kf l).Perm l :=
  List.mergeSort_perm l _

/-! ### Stable insertion -/

/-- Insert `e` after every item whose key is `<= kf e`. -/
def insS (kf : Int → Int) (e : Int) : List Int → List Int
  | [] => [e]
  | a :: l => if kf a ≤ kf e then a :: insS kf e l else e :: a :: l

theorem mem_insS (kf : Int → Int) (e x : Int) : ∀ l, x ∈ insS kf e l ↔ x = e ∨ x ∈ l
  | [] => by simp [insS]
  | a :: l => by
    simp only [insS]
    split
    · simp only [List.mem_cons, mem_insS kf e x l]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
    · simp

theorem length_insS (kf : Int → Int) (e : Int) : ∀ l, (insS kf e l).length = l.length + 1
  | [] => rfl
  | a :: l => by simp only [insS]; split <;> simp [length_insS kf e l]

theorem pairwise_insS (kf : Int → Int) (e : Int) :
    ∀ l : List Int, l.Pairwise (fun a b => kf a ≤ kf b) →
      (insS kf e l).Pairwise (fun a b => kf a ≤ kf b)
  | [], _ => by simp [insS]
  | a :: l, h => by
    simp only [insS]
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    split
    · rename_i hae
      refine List.pairwise_cons.2 ⟨?_, pairwise_insS kf e l h2⟩
      intro x hx
      rcases (mem_insS kf e x l).1 hx with rfl | hx
      · exact hae
      · exact h1 x hx
    · rename_i hae
      refine List.pairwise_cons.2 ⟨?_, h⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · omega
      · have := h1 x hx; omega

theorem filter_insS (kf : Int → Int) (e k : Int) :
    ∀ l : List Int, l.Pairwise (fun a b => kf a ≤ kf b) →
      (insS kf e l).filter (fun x => kf x == k) =
        l.filter (fun x => kf x == k) ++ (if kf e = k then [e] else [])
  | [], _ => by by_cases h : kf e = k <;> simp [insS, h]
  | a :: l, h => by
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 h
    simp only [insS]
    split
    · rw [List.filter_cons, List.filter_cons, filter_insS kf e k l h2]
      split <;> simp
    · rename_i hae
      by_cases hk : kf e = k
      · have hnil : (a :: l).filter (fun x => kf x == k) = [] := by
          rw [List.filter_eq_nil_iff]
          intro x hx
          rcases List.mem_cons.1 hx with rfl | hx
          · simp; omega
          · have := h1 x hx; simp; omega
        rw [List.filter_cons, hnil]
        simp [hk]
      · rw [List.filter_cons]
        simp [hk]

/-- Sorting `P ++ [e]` is inserting `e` into the sorted `P`. -/
theorem stableSort_append_single (kf : Int → Int) (P : List Int) (e : Int) :
    stableSort kf (P ++ [e]) = insS kf e (stableSort kf P) := by
  apply stableSort_eq
  have hs := stableSort_spec kf P
  refine ⟨pairwise_insS kf e _ hs.1, ?_⟩
  intro k
  rw [filter_insS kf e k _ hs.1, hs.2 k, List.filter_append]
  by_cases h : kf e = k <;> simp [h]

theorem take_insS (kf : Int → Int) (e : Int) :
    ∀ (n : Nat) (L : List Int), (insS kf e L).take n = (insS kf e (L.take n)).take n
  | 0, _ => by simp
  | n + 1, [] => by simp
  | n + 1, a :: L => by
    simp only [List.take_succ_cons, insS]
    split
    · simp only [List.take_succ_cons]
      rw [take_insS kf e n L]
    · simp only [List.take_succ_cons]
      congr 1
      cases n with
      | zero => simp
      | succ n => simp [List.take_take]

/-- Inserting before the last item. -/
theorem insS_before_last (kf : Int → Int) (e z : Int) (hz : kf e < kf z) :
    ∀ L0 : List Int, insS kf e (L0 ++ [z]) = insS kf e L0 ++ [z]
  | [] => by simp [insS]; omega
  | a :: L0 => by
    simp only [List.cons_append, insS]
    split
    · rw [insS_before_last kf e z hz L0]; rfl
    · rfl

/-- Inserting after every item. -/
theorem insS_of_all_le (kf : Int → Int) (e : Int) :
    ∀ L : List Int, (∀ x ∈ L, kf x ≤ kf e) → insS kf e L = L ++ [e]
  | [], _ => rfl
  | a :: L, h => by
    simp only [insS, if_pos (h a (by simp)), List.cons_append]
    rw [insS_of_all_le kf e L (fun x hx => h x (by simp [hx]))]

/-- `take n` of the stable sort after appending one item. -/
theorem take_stableSort_snoc (kf : Int → Int) (n : Nat) (P : List Int) (e : Int) :
    (stableSort kf (P ++ [e])).take n = (insS kf e ((stableSort kf P).take n)).take n := by
  rw [stableSort_append_single, take_insS]

theorem stableSort_nil (kf : Int → Int) : stableSort kf [] = [] := by simp [stableSort]

theorem stableSort_single (kf : Int → Int) (x : Int) : stableSort kf [x] = [x] := by
  simp [stableSort]

end PyLean.Accel
