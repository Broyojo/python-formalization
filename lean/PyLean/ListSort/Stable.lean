import PyLean.ListSort.Model

/-!
The specification: the stable sort by an `Int`-valued key `kf`.

`SS kf l l'` says `l'` is sorted by `kf` and, for every key value, lists the
items with that key in the order they have in `l`. It determines `l'` uniquely
(`ss_unique`) and `stableSort` (core's `List.mergeSort`) satisfies it, so it is
"sorted permutation + stability" in one predicate. Items are compared with
`ltOf kf a b = decide (kf a < kf b)`; Python ints compared with `<` are the case
`kf = id`, and `(value, index)` pairs compared by value are `kf = Prod.fst`.
-/

namespace PyLean.ListSort

variable {α : Type}

def ltOf (kf : α → Int) (a b : α) : Bool := decide (kf a < kf b)

def Sorted (kf : α → Int) (l : List α) : Prop := l.Pairwise (fun a b => kf a ≤ kf b)

/-- Same items per key, in the same order. -/
def FEq (kf : α → Int) (l l' : List α) : Prop :=
  ∀ k, l.filter (fun e => kf e == k) = l'.filter (fun e => kf e == k)

def SS (kf : α → Int) (l l' : List α) : Prop := Sorted kf l' ∧ FEq kf l l'

def stableSort (kf : α → Int) (l : List α) : List α :=
  l.mergeSort (fun a b => decide (kf a ≤ kf b))

theorem FEq.refl (kf : α → Int) (l : List α) : FEq kf l l := fun _ => rfl
theorem FEq.symm {kf : α → Int} {l l' : List α} (h : FEq kf l l') : FEq kf l' l := fun k => (h k).symm
theorem FEq.trans {kf : α → Int} {l1 l2 l3 : List α} (h1 : FEq kf l1 l2) (h2 : FEq kf l2 l3) :
    FEq kf l1 l3 := fun k => (h1 k).trans (h2 k)
theorem FEq.append {kf : α → Int} {a a' b b' : List α} (ha : FEq kf a a') (hb : FEq kf b b') :
    FEq kf (a ++ b) (a' ++ b') := fun k => by rw [List.filter_append, List.filter_append, ha k, hb k]

/-- Blocks whose keys never coincide commute. -/
theorem FEq.comm {kf : α → Int} {a b : List α} (h : ∀ x ∈ a, ∀ y ∈ b, kf x ≠ kf y) :
    FEq kf (a ++ b) (b ++ a) := by
  intro k
  rw [List.filter_append, List.filter_append]
  by_cases ha : a.filter (fun e => kf e == k) = []
  · rw [ha]; simp
  · have hb : b.filter (fun e => kf e == k) = [] := by
      obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ ha
      have hx1 := (List.mem_filter.1 hx).1
      have hx2 : kf x = k := by simpa using (List.mem_filter.1 hx).2
      rw [List.filter_eq_nil_iff]
      intro y hy
      have := h x hx1 y hy
      simp; omega
    rw [hb]; simp

theorem FEq.mem {kf : α → Int} {l l' : List α} (h : FEq kf l l') (x : α) : x ∈ l ↔ x ∈ l' := by
  have := h (kf x)
  constructor
  · intro hx
    have : x ∈ l.filter (fun e => kf e == kf x) := List.mem_filter.2 ⟨hx, by simp⟩
    rw [h (kf x)] at this
    exact (List.mem_filter.1 this).1
  · intro hx
    have : x ∈ l'.filter (fun e => kf e == kf x) := List.mem_filter.2 ⟨hx, by simp⟩
    rw [← h (kf x)] at this
    exact (List.mem_filter.1 this).1

theorem sorted_filter_unique (kf : α → Int) :
    ∀ (l1 l2 : List α), Sorted kf l1 → Sorted kf l2 → FEq kf l1 l2 → l1 = l2 := by
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
    have hmem := hf.mem
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
      simp only [List.filter_cons, beq_self_eq_true, ite_true, hab] at hk
      simp only [← hab, List.cons.injEq] at hk
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

theorem ss_unique {kf : α → Int} {l l1 l2 : List α} (h1 : SS kf l l1) (h2 : SS kf l l2) : l1 = l2 :=
  sorted_filter_unique kf l1 l2 h1.1 h2.1 (h1.2.symm.trans h2.2)

theorem stableSort_spec (kf : α → Int) (l : List α) : SS kf l (stableSort kf l) := by
  have trans : ∀ a b c : α, decide (kf a ≤ kf b) = true → decide (kf b ≤ kf c) = true →
      decide (kf a ≤ kf c) = true := by
    intro a b c h1 h2; simp at *; omega
  have total : ∀ a b : α, (decide (kf a ≤ kf b) || decide (kf b ≤ kf a)) = true := by
    intro a b; simp; omega
  refine ⟨?_, ?_⟩
  · have := List.pairwise_mergeSort trans total l
    exact this.imp (fun h => by simpa using h)
  · intro k
    let p : α → Bool := fun e => kf e == k
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
    exact hsub2.eq_of_length hlen.symm

theorem ss_eq_stableSort {kf : α → Int} {l l' : List α} (h : SS kf l l') : l' = stableSort kf l :=
  ss_unique h (stableSort_spec kf l)

/-- `FEq` implies the same multiset of items. -/
theorem FEq.perm {kf : α → Int} {l l' : List α} (h : FEq kf l l') : l.Perm l' := by
  have h1 := (List.mergeSort_perm l (fun a b => decide (kf a ≤ kf b)))
  have h2 := (List.mergeSort_perm l' (fun a b => decide (kf a ≤ kf b)))
  have : stableSort kf l = stableSort kf l' :=
    ss_unique (stableSort_spec kf l) ⟨(stableSort_spec kf l').1, h.trans (stableSort_spec kf l').2⟩
  unfold stableSort at this
  rw [this] at h1
  exact h1.symm.trans h2

theorem SS.perm {kf : α → Int} {l l' : List α} (h : SS kf l l') : l.Perm l' := h.2.perm

theorem SS.length {kf : α → Int} {l l' : List α} (h : SS kf l l') : l'.length = l.length :=
  h.perm.length_eq.symm

theorem Sorted.ss {kf : α → Int} {l : List α} (h : Sorted kf l) : SS kf l l := ⟨h, FEq.refl kf l⟩

/-- Sorting the pieces first does not change the stable sort. -/
theorem SS.of_parts {kf : α → Int} {P Q A B M : List α} (hA : SS kf P A) (hB : SS kf Q B)
    (hM : SS kf (A ++ B) M) : SS kf (P ++ Q) M :=
  ⟨hM.1, (FEq.append hA.2 hB.2).trans hM.2⟩

theorem sorted_append {kf : α → Int} {a b : List α} :
    Sorted kf (a ++ b) ↔ Sorted kf a ∧ Sorted kf b ∧ ∀ x ∈ a, ∀ y ∈ b, kf x ≤ kf y := by
  simp [Sorted, List.pairwise_append]

theorem sorted_cons {kf : α → Int} {a : α} {l : List α} :
    Sorted kf (a :: l) ↔ (∀ y ∈ l, kf a ≤ kf y) ∧ Sorted kf l := by
  simp [Sorted, List.pairwise_cons]

/-- A prefix that is sorted and below everything after it stays in front. -/
theorem ss_prefix {kf : α → Int} {X Y R : List α} (hX : Sorted kf X)
    (hXY : ∀ x ∈ X, ∀ y ∈ Y, kf x ≤ kf y) (hR : SS kf Y R) : SS kf (X ++ Y) (X ++ R) := by
  refine ⟨sorted_append.2 ⟨hX, hR.1, fun x hx y hy => hXY x hx y ((hR.2.mem y).2 hy)⟩, ?_⟩
  exact FEq.append (FEq.refl kf X) hR.2

/-- A sorted block `X` that is strictly below `A` and below `Y` moves in front of `A`. -/
theorem ss_mid_prefix {kf : α → Int} {A X Y R : List α} (hX : Sorted kf X)
    (hXA : ∀ x ∈ X, ∀ a ∈ A, kf x < kf a) (hXY : ∀ x ∈ X, ∀ y ∈ Y, kf x ≤ kf y)
    (hR : SS kf (A ++ Y) R) : SS kf (A ++ X ++ Y) (X ++ R) := by
  refine ⟨sorted_append.2 ⟨hX, hR.1, fun x hx y hy => ?_⟩, ?_⟩
  · rcases List.mem_append.1 ((hR.2.mem y).2 hy) with h | h
    · exact Int.le_of_lt (hXA x hx y h)
    · exact hXY x hx y h
  · have hc : FEq kf (A ++ X) (X ++ A) :=
      FEq.comm (fun a ha x hx => by have := hXA x hx a ha; omega)
    have : FEq kf (A ++ X ++ Y) (X ++ (A ++ Y)) := by
      rw [← List.append_assoc]; exact FEq.append hc (FEq.refl kf Y)
    exact this.trans (FEq.append (FEq.refl kf X) hR.2)

/-- A sorted suffix above everything before it stays at the end. -/
theorem ss_suffix {kf : α → Int} {X Y R : List α} (hX : Sorted kf X)
    (hYX : ∀ y ∈ Y, ∀ x ∈ X, kf y ≤ kf x) (hR : SS kf Y R) : SS kf (Y ++ X) (R ++ X) := by
  refine ⟨sorted_append.2 ⟨hR.1, hX, fun y hy x hx => hYX y ((hR.2.mem y).2 hy) x hx⟩, ?_⟩
  exact FEq.append hR.2 (FEq.refl kf X)

/-- A sorted block `X` that is above `A` and strictly above `B` moves behind `B`. -/
theorem ss_mid_suffix {kf : α → Int} {A X B R : List α} (hX : Sorted kf X)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, kf a ≤ kf x) (hBX : ∀ b ∈ B, ∀ x ∈ X, kf b < kf x)
    (hR : SS kf (A ++ B) R) : SS kf (A ++ X ++ B) (R ++ X) := by
  refine ⟨sorted_append.2 ⟨hR.1, hX, fun y hy x hx => ?_⟩, ?_⟩
  · rcases List.mem_append.1 ((hR.2.mem y).2 hy) with h | h
    · exact hAX y h x hx
    · exact Int.le_of_lt (hBX y h x hx)
  · have hc : FEq kf (X ++ B) (B ++ X) :=
      FEq.comm (fun x hx b hb => by have := hBX b hb x hx; omega)
    have : FEq kf (A ++ X ++ B) (A ++ B ++ X) := by
      rw [List.append_assoc, List.append_assoc]; exact FEq.append (FEq.refl kf A) hc
    exact this.trans (FEq.append hR.2 (FEq.refl kf X))

/-- Two blocks whose keys are strictly ordered the other way round swap. -/
theorem ss_swap {kf : α → Int} {P Q R S : List α} (hP : SS kf P R) (hQ : SS kf Q S)
    (h : ∀ x ∈ Q, ∀ y ∈ P, kf x < kf y) : SS kf (P ++ Q) (S ++ R) := by
  refine ⟨sorted_append.2 ⟨hQ.1, hP.1, fun x hx y hy =>
    Int.le_of_lt (h x ((hQ.2.mem x).2 hx) y ((hP.2.mem y).2 hy))⟩, ?_⟩
  have hc : FEq kf (P ++ Q) (Q ++ P) := FEq.comm (fun y hy x hx => by have := h x hx y hy; omega)
  exact hc.trans (FEq.append hQ.2 hP.2)

/-- All items of a list with one key: it is its own stable sort. -/
theorem sorted_of_const {kf : α → Int} {l : List α} {c : Int} (h : ∀ x ∈ l, kf x = c) :
    Sorted kf l := by
  unfold Sorted
  exact List.pairwise_of_forall_mem_list (fun a ha b hb => by rw [h a ha, h b hb]; exact Int.le_refl _)

end PyLean.ListSort
