import PyLean.Accel.HeapifyLocalC

/-!
`heapify` / `heapify_max`: the C twin (`heapify_internal`, with the
cache-friendly order above 2500 items) builds exactly the list the Python
twin builds. Both orders sift every internal node once, children first
(`HeapifyLocalOrder`, `HeapifyLocalC`), and every such order produces the
canonical bottom-up heap `hcanon 0` (`HeapifyLocalCanon`), for any comparison.
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

theorem downFrom_zero (m : Nat) : downFrom 0 m = (List.range m).reverse := by
  apply List.ext_getElem (by simp [downFrom])
  intro i h1 h2
  simp only [downFrom, List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

theorem forDown_siftup_eq (lt : α → α → Bool) :
    ∀ (is : List Nat) (h : List α), (∀ i ∈ is, i < h.length) →
      forDown (fun h i => cSiftup lt h i) h is = .ok (is.foldl (fun h i => pySiftup lt h i) h) := by
  intro is
  induction is with
  | nil => intro h _; rfl
  | cons i is ih =>
    intro h hi
    simp only [forDown, List.foldlM_cons, List.foldl_cons]
    rw [cSiftup_eq lt h i (hi i (by simp))]
    simp only [bind, Except.bind]
    exact ih _ (fun j hj => by rw [pySiftup_length]; exact hi j (by simp [hj]))

/-- C `heapify` equals Python `heapify` on lists of at most 2500 items. -/
theorem cHeapify_small (lt : α → α → Bool) (x : List α) (hn : x.length ≤ 2500) :
    cHeapify lt x = .ok (pyHeapify lt x) := by
  simp only [cHeapify, if_neg (Nat.not_lt.2 hn), pyHeapify, shr1, downFrom_zero]
  apply forDown_siftup_eq
  intro i hi
  simp at hi; omega

/-- C/Python agreement of `heapify` (and `heapify_max` via `maxLt`), for every
element type, comparison and length, including the cache-friendly order that
`_heapqmodule.c:375-376` uses above 2500 items. -/
def HeapifyTwinsAgree : Prop :=
  ∀ (α : Type) [Inhabited α] (lt : α → α → Bool) (x : List α),
    cHeapify lt x = .ok (pyHeapify lt x)

/-- C `heapify` above 2500 items: the cache-friendly order gives the Python result. -/
theorem cCacheFriendly_eq (lt : α → α → Bool) (x : List α) (hn : 2500 < x.length) :
    cCacheFriendlyHeapify lt x = .ok (pyHeapify lt x) := by
  obtain ⟨R, hR, b1, b2⟩ := keepTopBit_spec (x.length / 2 + 1) (by omega)
  cases R with
  | zero => simp at b2; omega
  | succ q =>
    have hP : 2 ^ (q + 1) = 2 * 2 ^ q := by rw [Nat.pow_succ, Nat.mul_comm]
    have h1 : 2 * 2 ^ q ≤ x.length / 2 + 1 := by rw [← hP]; exact b1
    have h2 : x.length / 2 + 1 < 4 * 2 ^ q := by
      have : 2 ^ (q + 1 + 1) = 4 * 2 ^ q := by rw [Nat.pow_succ, Nat.pow_succ]; omega
      omega
    obtain ⟨hv, hcov⟩ := c_order (x.length / 2) q h1 h2
    simp only [cCacheFriendlyHeapify, shr1, hR, hP]
    rw [forDown_climb lt _ x (fun i hi => by rw [mem_downFrom] at hi; omega)]
    simp only [bind, Except.bind]
    rw [forDown_climb lt _ _ (fun i hi => by rw [mem_downFrom] at hi; rw [foldl_siftup_length]; omega)]
    rw [← List.foldl_append, foldl_eq_hcanon lt x.length x rfl (by omega) _ hv hcov]
    unfold pyHeapify
    rw [foldl_eq_hcanon lt x.length x rfl (by omega) _
      (hvalid_py _ _ (Nat.le_refl _) _ (fun j => ⟨False.elim, fun h => by omega⟩))
      (fun j => by simp)]

theorem heapifyTwinsAgree_proven : HeapifyTwinsAgree := by
  intro α _ lt x
  by_cases hn : x.length ≤ 2500
  · exact cHeapify_small lt x hn
  · simp only [cHeapify, if_pos (show x.length > 2500 by omega)]
    exact cCacheFriendly_eq lt x (by omega)

end PyLean.Accel
