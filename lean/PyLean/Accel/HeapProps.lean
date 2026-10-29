import PyLean.Accel.HeapCorrect

/-!
The heap invariant for the public functions. Generic lemmas are stated for
any strict weak order; the registry properties instantiate them for ints
(`heapLt false` for the min-heap functions, `heapLt true` for `*_max`).
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

theorem strictWeak_heapLt (isMax : Bool) : StrictWeak (heapLt isMax) := by
  cases isMax
  · exact strictWeak_int
  · exact strictWeak_int.maxLt

theorem at!_eq_getElem (l : List α) (i : Nat) (h : i < l.length) : at! l i = l[i] := by
  simp [at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem at!_append_lt (l r : List α) (i : Nat) (h : i < l.length) : at! (l ++ r) i = at! l i := by
  rw [at!_eq_getElem _ _ (by simp; omega), at!_eq_getElem _ _ h, List.getElem_append_left h]

theorem mem_iff_at! (l : List α) (e : α) : e ∈ l ↔ ∃ i, i < l.length ∧ at! l i = e := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, h, rfl⟩; exact ⟨i, h, at!_eq_getElem l i h⟩
  · rintro ⟨i, h, rfl⟩; exact ⟨i, h, (at!_eq_getElem l i h).symm⟩

/-- The root of a heap is minimal: `not heap[c] < heap[0]`. -/
theorem root_min {lt : α → α → Bool} (hlt : StrictWeak lt) (l : List α) (hh : IsHeap lt l) :
    ∀ c, c < l.length → lt (at! l c) (at! l 0) = false := by
  intro c
  induction c using Nat.strongRecOn with
  | _ c ih =>
    intro hc
    by_cases h0 : c = 0
    · subst h0; exact hlt.irrefl _
    · have h1 := hh c hc (desc_zero c) h0
      have h2 := ih (par c) (by unfold par; omega) (by unfold par; omega)
      exact hlt.le_trans _ _ _ h2 h1

theorem root_min_mem {lt : α → α → Bool} (hlt : StrictWeak lt) (l : List α) (hh : IsHeap lt l) :
    ∀ e ∈ l, lt e (at! l 0) = false := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := (mem_iff_at! l e).1 he
  exact root_min hlt l hh i hi

/-- Pairs not touching position 0 are as in the original heap. -/
theorem pre_root {lt : α → α → Bool} (l l' : List α) (hh : IsHeap lt l) (hlen : l'.length ≤ l.length)
    (hsame : ∀ i, i ≠ 0 → i < l'.length → at! l' i = at! l i) :
    ∀ c, c < l'.length → Desc 0 c → c ≠ 0 → par c ≠ 0 → PairOk lt l' c := by
  intro c hc _ hc0 hp0
  have := hh c (by omega) (desc_zero c) hc0
  unfold PairOk at *
  rw [hsame c hc0 hc, hsame (par c) hp0 (by unfold par; omega)]
  exact this

theorem pySiftup_root {lt : α → α → Bool} (hlt : StrictWeak lt) (l l' : List α) (hh : IsHeap lt l)
    (hlen : l'.length ≤ l.length) (hne : l' ≠ [])
    (hsame : ∀ i, i ≠ 0 → i < l'.length → at! l' i = at! l i) :
    IsHeap lt (pySiftup lt l' 0) ∧ (pySiftup lt l' 0).Perm l' := by
  have h := pySiftup_correct hlt l' 0 (List.length_pos_iff.2 hne) (pre_root l l' hh hlen hsame)
  exact ⟨h.1, h.2.1⟩

/-- `heappush`. -/
theorem pyHeappush_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (heap : List α) (item : α)
    (hh : IsHeap lt heap) :
    IsHeap lt (pyHeappush lt heap item) ∧ (pyHeappush lt heap item).Perm (item :: heap) := by
  simp only [pyHeappush, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  have hinv : UpInv lt (heap ++ [item]) 0 heap.length := by
    refine ⟨?_, ?_, desc_zero _⟩
    · intro c hc _ hc0 hcn
      simp only [List.length_append, List.length_singleton] at hc
      have := hh c (by omega) (desc_zero c) hc0
      unfold PairOk at *
      rw [at!_append_lt _ _ _ (by omega), at!_append_lt _ _ _ (by unfold par; omega)]
      exact this
    · intro _ c hc hc0 hcp
      simp only [List.length_append, List.length_singleton] at hc
      unfold par at hcp; omega
  have h := pySiftdown_correct hlt (heap ++ [item]) 0 heap.length (by simp) hinv
  exact ⟨h.1, h.2.trans List.perm_append_comm⟩

/-- `heappop`. -/
theorem pyHeappop_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (heap : List α)
    (hh : IsHeap lt heap) (hne : heap ≠ []) :
    ∃ v h', pyHeappop lt heap = .ok (v, h') ∧ IsHeap lt h' ∧ (v :: h').Perm heap ∧
      ∀ e ∈ heap, lt e v = false := by
  have hmin := root_min_mem hlt heap hh
  obtain ⟨d, last, hd⟩ : ∃ d last, heap = d ++ [last] := ⟨heap.dropLast, heap.getLast hne,
    (List.dropLast_concat_getLast hne).symm⟩
  subst hd
  have hgl : (d ++ [last]).getLast? = some last := by simp
  have hdl : (d ++ [last]).dropLast = d := by simp
  simp only [pyHeappop, hgl, hdl]
  cases d with
  | nil =>
    refine ⟨last, [], rfl, fun c hc => by simp at hc, List.Perm.refl _, ?_⟩
    intro e he; simp at he; subst he; exact hlt.irrefl _
  | cons d0 dt =>
    simp only [ne_eq, reduceCtorEq, not_false_eq_true, if_true]
    have h0 : at! (d0 :: dt) 0 = d0 := rfl
    rw [h0]
    have hroot : at! (d0 :: dt ++ [last]) 0 = d0 := rfl
    rw [hroot] at hmin
    have hset : (d0 :: dt).set 0 last = last :: dt := rfl
    obtain ⟨r1, r2⟩ := pySiftup_root hlt (d0 :: dt ++ [last]) ((d0 :: dt).set 0 last) hh
      (by simp) (by simp) (by
        intro i hi0 hi
        simp only [List.length_set] at hi
        rw [at!_set_ne _ _ _ _ (Ne.symm hi0), at!_append_lt _ _ _ hi])
    refine ⟨d0, _, rfl, r1, ?_, hmin⟩
    rw [hset] at r2 ⊢
    refine (List.Perm.cons d0 r2).trans ?_
    simp only [List.cons_append]
    exact List.Perm.cons d0 (List.perm_append_comm.trans (by simp)).symm

/-- `heapreplace`. -/
theorem pyHeapreplace_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (heap : List α) (item : α)
    (hh : IsHeap lt heap) (hne : heap ≠ []) :
    ∃ v h', pyHeapreplace lt heap item = .ok (v, h') ∧ IsHeap lt h' ∧
      (v :: h').Perm (item :: heap) ∧ ∀ e ∈ heap, lt e v = false := by
  have hmin := root_min_mem hlt heap hh
  cases heap with
  | nil => exact absurd rfl hne
  | cons y ys =>
    simp only [pyHeapreplace, reduceCtorEq, if_false]
    have hy : at! (y :: ys) 0 = y := rfl
    rw [hy] at hmin ⊢
    obtain ⟨r1, r2⟩ := pySiftup_root hlt (y :: ys) ((y :: ys).set 0 item) hh (by simp) (by simp)
      (fun i hi0 hi => at!_set_ne _ _ _ _ (Ne.symm hi0))
    refine ⟨y, _, rfl, r1, ?_, hmin⟩
    have hset : (y :: ys).set 0 item = item :: ys := rfl
    rw [hset] at r2
    exact (List.Perm.cons y r2).trans (List.Perm.swap item y ys)

/-- `heappushpop`. -/
theorem pyHeappushpop_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (heap : List α) (item : α)
    (hh : IsHeap lt heap) :
    IsHeap lt (pyHeappushpop lt heap item).2 ∧
      ((pyHeappushpop lt heap item).1 :: (pyHeappushpop lt heap item).2).Perm (item :: heap) ∧
      ∀ e ∈ item :: heap, lt e (pyHeappushpop lt heap item).1 = false := by
  have hmin := root_min_mem hlt heap hh
  simp only [pyHeappushpop]
  by_cases hc : heap ≠ [] ∧ lt (at! heap 0) item = true
  · rw [if_pos hc]
    obtain ⟨r1, r2⟩ := pySiftup_root hlt heap (heap.set 0 item) hh (by simp) (by
      intro h; apply hc.1; cases heap <;> simp_all)
      (fun i hi0 hi => at!_set_ne _ _ _ _ (Ne.symm hi0))
    refine ⟨r1, ?_, ?_⟩
    · cases heap with
      | nil => exact absurd rfl hc.1
      | cons y ys =>
        have hset : (y :: ys).set 0 item = item :: ys := rfl
        rw [hset] at r2
        exact (List.Perm.cons _ r2).trans (List.Perm.swap item _ ys)
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · exact hlt.asymm _ _ hc.2
      · exact hmin e he
  · rw [if_neg hc]
    refine ⟨hh, List.Perm.refl _, ?_⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact hlt.irrefl _
    · have hn : lt (at! heap 0) item = false := by
        cases h : lt (at! heap 0) item
        · rfl
        · exact absurd ⟨List.ne_nil_of_mem he, h⟩ hc
      exact hlt.le_trans _ _ _ hn (hmin e he)

/-- `heapify` in the Python order. -/
theorem pyHeapify_correct {lt : α → α → Bool} (hlt : StrictWeak lt) (x : List α) :
    IsHeap lt (pyHeapify lt x) ∧ (pyHeapify lt x).Perm x := by
  -- Inv k l: every pair whose parent is `>= k` is in order.
  let Inv : Nat → List α → Prop := fun k l =>
    ∀ c, c < l.length → c ≠ 0 → k ≤ par c → PairOk lt l c
  have step : ∀ k (l : List α), l.length = x.length → k ≤ x.length / 2 →
      Inv k l → IsHeap lt (((List.range k).reverse).foldl (fun h i => pySiftup lt h i) l) ∧
        (((List.range k).reverse).foldl (fun h i => pySiftup lt h i) l).Perm l := by
    intro k
    induction k with
    | zero =>
      intro l _ _ hinv
      refine ⟨fun c hc _ hc0 => hinv c hc hc0 (Nat.zero_le _), List.Perm.refl _⟩
    | succ k ih =>
      intro l hl hk hinv
      rw [List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.foldl_cons]
      have hkl : k < l.length := by omega
      obtain ⟨s1, s2, s3⟩ := pySiftup_correct hlt l k hkl (by
        intro c hc hdc hck hpk
        exact hinv c hc (by have := hdc.le; omega) (by have := (hdc.up hck).le; omega))
      have hlen' : (pySiftup lt l k).length = x.length := by rw [pySiftup_length, hl]
      have hinv' : Inv k (pySiftup lt l k) := by
        intro c hc hc0 hkc
        rw [pySiftup_length] at hc
        by_cases hd : Desc k c
        · exact s1 c (by rw [pySiftup_length]; exact hc) hd (by intro e; subst e; unfold par at hkc; omega)
        · have hdp : ¬ Desc k (par c) := by
            intro h'
            exact hd (Desc.child h' rfl hc0)
          have hpk : par c ≠ k := fun e => hdp (e ▸ Desc.refl)
          have := hinv c hc hc0 (by omega)
          unfold PairOk at *
          rw [s3 c hd, s3 (par c) hdp]
          exact this
      obtain ⟨r1, r2⟩ := ih (pySiftup lt l k) hlen' (by omega) hinv'
      exact ⟨r1, r2.trans s2⟩
  have hinit : Inv (x.length / 2) x := by
    intro c hc hc0 hk; unfold par at hk; omega
  exact step (x.length / 2) x rfl (Nat.le_refl _) hinit

/-! ### Registry properties -/

/-- The heap invariant (Lib/heapq.py:3-4, `heap[k] <= heap[2*k+1]` and
`heap[k] <= heap[2*k+2]`; for the `*_max` functions the max-heap invariant,
Doc/library/heapq.rst:104-150) is kept by every operation on an int heap, the
list is permuted as documented, and the popped / returned item is the
smallest (largest for `_max`) one. Stated for the Python twins; the C twins
compute the same lists (`HeapTwinsAgree`). -/
def HeapOpsKeepInvariant : Prop :=
  ∀ (isMax : Bool) (heap : List Int) (item : Int),
    IsHeap (heapLt isMax) heap →
      (IsHeap (heapLt isMax) (pyHeappush (heapLt isMax) heap item) ∧
        (pyHeappush (heapLt isMax) heap item).Perm (item :: heap)) ∧
      (heap ≠ [] → ∃ v h', pyHeappop (heapLt isMax) heap = .ok (v, h') ∧
        IsHeap (heapLt isMax) h' ∧ (v :: h').Perm heap ∧ ∀ e ∈ heap, heapLt isMax e v = false) ∧
      (heap ≠ [] → ∃ v h', pyHeapreplace (heapLt isMax) heap item = .ok (v, h') ∧
        IsHeap (heapLt isMax) h' ∧ (v :: h').Perm (item :: heap) ∧
        ∀ e ∈ heap, heapLt isMax e v = false) ∧
      (IsHeap (heapLt isMax) (pyHeappushpop (heapLt isMax) heap item).2 ∧
        ((pyHeappushpop (heapLt isMax) heap item).1 :: (pyHeappushpop (heapLt isMax) heap item).2).Perm
          (item :: heap) ∧
        ∀ e ∈ item :: heap, heapLt isMax e (pyHeappushpop (heapLt isMax) heap item).1 = false)

theorem heapOpsKeepInvariant_proven : HeapOpsKeepInvariant := by
  intro isMax heap item hh
  have hlt := strictWeak_heapLt isMax
  exact ⟨pyHeappush_correct hlt heap item hh, pyHeappop_correct hlt heap hh,
    pyHeapreplace_correct hlt heap item hh, pyHeappushpop_correct hlt heap item hh⟩

/-- `heapify(x)` / `heapify_max(x)` (Lib/heapq.py:171-180, :211-215) turn any
int list into a min-heap / max-heap holding the same items. -/
def HeapifyMakesHeap : Prop :=
  ∀ (isMax : Bool) (x : List Int),
    IsHeap (heapLt isMax) (pyHeapify (heapLt isMax) x) ∧ (pyHeapify (heapLt isMax) x).Perm x

theorem heapifyMakesHeap_proven : HeapifyMakesHeap :=
  fun isMax x => pyHeapify_correct (strictWeak_heapLt isMax) x

end PyLean.Accel
