import PyLean.Accel.HeapqSelect

/-!
The stable sort by an int key over any element type (the `StableSort.lean` facts, with the
elements no longer ints), and the extraction of its first item.
-/

namespace PyLean.Accel.Heapq

variable {γ : Type}

/-- The stable sort of `l` by `kf`. -/
def gStableSort (kf : γ → Int) (l : List γ) : List γ :=
  l.mergeSort (fun a b => decide (kf a ≤ kf b))

def gStableSortedBy (kf : γ → Int) (l l' : List γ) : Prop :=
  l'.Pairwise (fun a b => kf a ≤ kf b) ∧
    ∀ k, l'.filter (fun e => kf e == k) = l.filter (fun e => kf e == k)

theorem gSorted_filter_unique (kf : γ → Int) :
    ∀ (l1 l2 : List γ), l1.Pairwise (fun a b => kf a ≤ kf b) → l2.Pairwise (fun a b => kf a ≤ kf b) →
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

theorem gStableSorted_unique (kf : γ → Int) (l l1 l2 : List γ) (h1 : gStableSortedBy kf l l1)
    (h2 : gStableSortedBy kf l l2) : l1 = l2 :=
  gSorted_filter_unique kf l1 l2 h1.1 h2.1 (fun k => (h1.2 k).trans (h2.2 k).symm)

theorem gStableSort_spec (kf : γ → Int) (l : List γ) : gStableSortedBy kf l (gStableSort kf l) := by
  have trans : ∀ a b c : γ, decide (kf a ≤ kf b) = true → decide (kf b ≤ kf c) = true →
      decide (kf a ≤ kf c) = true := by
    intro a b c h1 h2; simp at *; omega
  have total : ∀ a b : γ, (decide (kf a ≤ kf b) || decide (kf b ≤ kf a)) = true := by
    intro a b; simp; omega
  refine ⟨?_, ?_⟩
  · have := List.pairwise_mergeSort trans total l
    exact this.imp (fun h => by simpa using h)
  · intro k
    let p : γ → Bool := fun e => kf e == k
    have hsub : List.Sublist (l.filter p) (gStableSort kf l) := by
      apply List.sublist_mergeSort trans total _ (List.filter_sublist)
      apply List.Pairwise.imp_of_mem _ (List.pairwise_of_forall (R := fun _ _ => True) (fun _ _ => trivial))
      intro a b ha hb _
      have := (List.mem_filter.1 ha).2
      have := (List.mem_filter.1 hb).2
      simp_all [p]
    have hsub2 : List.Sublist (l.filter p) ((gStableSort kf l).filter p) := by
      have := hsub.filter p
      rwa [List.filter_filter, show (fun x => p x && p x) = p by funext x; simp] at this
    have hlen : ((gStableSort kf l).filter p).length = (l.filter p).length :=
      ((List.mergeSort_perm l _).filter p).length_eq
    exact (hsub2.eq_of_length hlen.symm).symm

theorem gStableSort_eq (kf : γ → Int) (l l' : List γ) (h : gStableSortedBy kf l l') :
    gStableSort kf l = l' :=
  gStableSorted_unique kf l _ _ (gStableSort_spec kf l) h

theorem gStableSort_perm (kf : γ → Int) (l : List γ) : (gStableSort kf l).Perm l :=
  List.mergeSort_perm l _

theorem gStableSort_extract (kf : γ → Int) (A B : List γ) (x : γ)
    (hA : ∀ y ∈ A, kf x < kf y) (hB : ∀ y ∈ B, kf x ≤ kf y) :
    gStableSort kf (A ++ x :: B) = x :: gStableSort kf (A ++ B) := by
  apply gStableSort_eq
  have hs := gStableSort_spec kf (A ++ B)
  refine ⟨List.pairwise_cons.2 ⟨?_, hs.1⟩, ?_⟩
  · intro y hy
    rw [(gStableSort_perm kf _).mem_iff, List.mem_append] at hy
    rcases hy with hy | hy
    · exact Int.le_of_lt (hA y hy)
    · exact hB y hy
  · intro k
    rw [List.filter_cons, hs.2 k, List.filter_append, List.filter_append, List.filter_cons]
    by_cases hk : kf x = k
    · have hnil : A.filter (fun e => kf e == k) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy; have := hA y hy; simp; omega
      simp [hk, hnil]
    · simp [hk]

theorem gStableSort_of_sorted (kf : γ → Int) (l : List γ) (h : l.Pairwise (fun a b => kf a ≤ kf b)) :
    gStableSort kf l = l :=
  gStableSort_eq kf l l ⟨h, fun _ => rfl⟩

end PyLean.Accel.Heapq
