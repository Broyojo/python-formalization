import PyLean.ListSort.FallibleBridge

/-! # The merges and the main loop with a comparison that never raises are the model's -/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

theorem loLoopF_pure (f : α → α → Bool) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out A B : List α) (ms : MS),
      loLoopF (pureLt f) fuel g mg ac bc out A B ms =
        ((loLoop f fuel g mg ac bc out A B ms).1, (loLoop f fuel g mg ac bc out A B ms).2, none) := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out A B ms; rfl
  | succ fuel ih =>
    intro g mg ac bc out A B ms
    cases g with
    | false =>
      rcases A with _ | ⟨a, A'⟩ <;> rcases B with _ | ⟨b, B'⟩ <;> simp only [loLoopF, loLoop]
      simp only [isltF, islt, pureLt]
      by_cases hf : f b a = true
      · simp only [hf, ↓reduceIte]
        by_cases h1 : B' = [] <;> by_cases h2 : bc + 1 ≥ mg <;> simp only [h1, h2, ↓reduceIte, ih]
      · have hf' : f b a = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : A'.length = 1 <;> by_cases h2 : ac + 1 ≥ mg <;> simp only [h1, h2, ↓reduceIte, ih]
    | true =>
      rcases B with _ | ⟨b, B'⟩ <;> simp only [loLoopF, loLoop]
      rw [gallopRightF_pure]
      generalize gallopRight f b _ _ _ _ = G
      obtain ⟨k, ms1⟩ := G
      simp only
      generalize A.take k = A0
      generalize A.drop k = A1
      by_cases c1 : k ≠ 0 ∧ A1.length = 1
      · simp only [if_pos c1]
      simp only [if_neg c1]
      by_cases c2 : k ≠ 0 ∧ A1.length = 0
      · simp only [if_pos c2]
      simp only [if_neg c2]
      by_cases c3 : B' = []
      · simp only [c3, ↓reduceIte]
      simp only [c3, ↓reduceIte]
      rcases A1 with _ | ⟨a, A'⟩
      · rfl
      simp only
      rw [gallopLeftF_pure]
      generalize gallopLeft f a _ _ _ _ = G
      obtain ⟨k2, ms2⟩ := G
      simp only
      by_cases d1 : k2 ≠ 0 ∧ B'.drop k2 = []
      · simp only [if_pos d1]
      simp only [if_neg d1]
      by_cases d2 : A'.length = 1
      · simp only [if_pos d2]
      simp only [if_neg d2]
      by_cases d3 : k ≥ MIN_GALLOP ∨ k2 ≥ MIN_GALLOP <;> simp only [d3, ↓reduceIte, ih]

theorem mergeLoF_pure (f : α → α → Bool) (A B : List α) (ms : MS) :
    mergeLoF (pureLt f) A B ms = ((mergeLo f A B ms).1, (mergeLo f A B ms).2, none) := by
  rcases B with _ | ⟨b, B'⟩ <;> simp only [mergeLoF, mergeLo]
  by_cases h1 : B' = [] <;> by_cases h2 : A.length = 1 <;> simp only [h1, h2, ↓reduceIte, loLoopF_pure]

theorem hiLoopF_pure (f : α → α → Bool) :
    ∀ (fuel : Nat) (g : Bool) (mg ac bc : Nat) (out Ar Br : List α) (ms : MS),
      hiLoopF (pureLt f) fuel g mg ac bc out Ar Br ms =
        ((hiLoop f fuel g mg ac bc out Ar Br ms).1, (hiLoop f fuel g mg ac bc out Ar Br ms).2, none) := by
  intro fuel
  induction fuel with
  | zero => intro g mg ac bc out Ar Br ms; rfl
  | succ fuel ih =>
    intro g mg ac bc out Ar Br ms
    cases g with
    | false =>
      rcases Ar with _ | ⟨a, Ar'⟩ <;> rcases Br with _ | ⟨b, Br'⟩ <;> simp only [hiLoopF, hiLoop]
      simp only [isltF, islt, pureLt]
      by_cases hf : f b a = true
      · simp only [hf, ↓reduceIte]
        by_cases h1 : Ar' = [] <;> by_cases h2 : ac + 1 ≥ mg <;> simp only [h1, h2, ↓reduceIte, ih]
      · have hf' : f b a = false := by simpa using hf
        simp only [hf', Bool.false_eq_true, ↓reduceIte]
        by_cases h1 : Br'.length = 1 <;> by_cases h2 : bc + 1 ≥ mg <;> simp only [h1, h2, ↓reduceIte, ih]
    | true =>
      rcases Br with _ | ⟨b, Br'⟩ <;> simp only [hiLoopF, hiLoop]
      rw [gallopRightF_pure]
      generalize gallopRight f b _ _ _ _ = G
      obtain ⟨k0, ms1⟩ := G
      simp only
      generalize Ar.length - k0 = k
      generalize Ar.take k = A0
      generalize Ar.drop k = A1
      by_cases c1 : k ≠ 0 ∧ A1 = []
      · simp only [if_pos c1]
      simp only [if_neg c1]
      by_cases c2 : Br'.length = 1
      · simp only [if_pos c2]
      simp only [if_neg c2]
      rcases A1 with _ | ⟨a, Ar'⟩
      · rfl
      simp only
      rw [gallopLeftF_pure]
      generalize gallopLeft f a _ _ _ _ = G
      obtain ⟨k2, ms2⟩ := G
      simp only
      generalize Br'.length - k2 = kb
      by_cases d1 : kb ≠ 0 ∧ (Br'.drop kb).length = 1
      · simp only [if_pos d1]
      simp only [if_neg d1]
      by_cases d2 : kb ≠ 0 ∧ Br'.drop kb = []
      · simp only [if_pos d2]
      simp only [if_neg d2]
      by_cases d3 : Ar' = []
      · simp only [d3, ↓reduceIte]
      simp only [d3, ↓reduceIte]
      by_cases d4 : k ≥ MIN_GALLOP ∨ kb ≥ MIN_GALLOP <;> simp only [d4, ↓reduceIte, ih]

theorem mergeHiF_pure (f : α → α → Bool) (A B : List α) (ms : MS) :
    mergeHiF (pureLt f) A B ms = ((mergeHi f A B ms).1, (mergeHi f A B ms).2, none) := by
  simp only [mergeHiF, mergeHi]
  generalize A.reverse = Ar
  rcases Ar with _ | ⟨a, Ar'⟩
  · rfl
  simp only
  by_cases h1 : Ar' = [] <;> by_cases h2 : B.length = 1 <;> simp only [h1, h2, ↓reduceIte, hiLoopF_pure]

theorem mergeAtF_pure (f : α → α → Bool) (A B : List α) (ms : MS) :
    mergeAtF (pureLt f) A B ms = ((mergeAt f A B ms).1, (mergeAt f A B ms).2, none) := by
  rcases B with _ | ⟨b0, B'⟩ <;> simp only [mergeAtF, mergeAt]
  rw [gallopRightF_pure]
  generalize gallopRight f b0 _ _ _ _ = G
  obtain ⟨k, ms1⟩ := G
  simp only
  generalize A.drop k = A1
  rcases hl : A1.getLast? with _ | alast
  · rfl
  simp only
  rw [gallopLeftF_pure]
  generalize gallopLeft f alast _ _ _ _ = G
  obtain ⟨nb, ms2⟩ := G
  simp only
  by_cases h0 : nb = 0
  · simp only [h0, ↓reduceIte]
  simp only [h0, ↓reduceIte]
  by_cases h1 : A1.length ≤ ((b0 :: B').take nb).length
  · simp only [h1, ↓reduceIte, mergeLoF_pure]
  · simp only [h1, ↓reduceIte, mergeHiF_pure]

theorem mergeAtArrF_pure (f : α → α → Bool) (base na nb : Nat) (arr : List α) (ms : MS) :
    mergeAtArrF (pureLt f) base na nb (arr, ms, none) =
      ((mergeAtArr f base na nb (arr, ms)).1, (mergeAtArr f base na nb (arr, ms)).2, none) := by
  simp only [mergeAtArrF, mergeAtArr, mergeAtF_pure]

end PyLean.ListSort
