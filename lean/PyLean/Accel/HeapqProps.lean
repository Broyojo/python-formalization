import PyLean.Accel.HeapqBridge

/-!
Registry properties of the effectful heap models with an honest comparison, and the
cache-friendly `heapify` order under fallible comparisons.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {σ α : Type} [Inhabited α]

/-! ### The public Python functions with an honest comparison -/

theorem pyHeappush_pure (mx : Bool) (r : α → α → Bool) (item : α) (w : HW σ α) :
    (pyHeappush listSeq (pureCmp r) mx item).run w =
      (.ok (), { w with heap := Accel.pyHeappush (heapOrd mx r) w.heap item }) := by
  simp only [pyHeappush]
  rw [Eff.run_bind_ok (listAppend_run _ _), Eff.run_bind_ok (listLen_run _),
    pySiftdown_pure mx r _ _ 0 ((w.heap ++ [item]).length - 1) (by simp) (by simp) _ (by simp)]
  rfl

theorem pyHeappop_pure (mx : Bool) (r : α → α → Bool) (w : HW σ α) :
    (pyHeappop listSeq (pureCmp r) mx).run w =
      match Accel.pyHeappop (heapOrd mx r) w.heap with
      | .ok (v, h') => (.ok v, { w with heap := h' })
      | .error e => (.error e, w) := by
  rcases w with ⟨st, h⟩
  cases h with
  | nil => rfl
  | cons y ys =>
    have hl : (y :: ys).getLast? = some (at! (y :: ys) ys.length) := by
      rw [List.getLast?_eq_getElem?]
      simp [at!, List.getD_eq_getElem?_getD]
    have hd : (y :: ys).dropLast = (y :: ys).take ys.length := by
      rw [List.dropLast_eq_take]; simp
    simp only [pyHeappop, Accel.pyHeappop, hl, hd]
    rw [Eff.run_bind_ok (listPop_run_cons y ys st), Eff.run_bind_ok (listTruth_run _)]
    by_cases h0 : ys.length = 0
    · have : ys = [] := List.eq_nil_of_length_eq_zero h0
      subst this
      rfl
    · have hne : (y :: ys).take ys.length ≠ [] := by
        apply List.ne_nil_of_length_pos; simp; omega
      have hne' : ((y :: ys).take ys.length).isEmpty = false := by
        cases hh : (y :: ys).take ys.length with
        | nil => exact absurd hh hne
        | cons _ _ => rfl
      simp only [hne', Bool.not_false, ↓reduceIte, ne_eq, hne, not_false_eq_true]
      rw [Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < ((y :: ys).take ys.length).length by
          simp; omega)),
        Eff.run_bind_ok (listSet_run 0 0 (by simp) _ (show 0 < ((y :: ys).take ys.length).length by
          simp; omega)),
        Eff.run_bind_ok (pySiftup_pure mx r 0 0 (by simp) _ (by simp; omega))]
      rfl

theorem pyHeapreplace_pure (mx : Bool) (r : α → α → Bool) (item : α) (w : HW σ α) :
    (pyHeapreplace listSeq (pureCmp r) mx item).run w =
      match Accel.pyHeapreplace (heapOrd mx r) w.heap item with
      | .ok (v, h') => (.ok v, { w with heap := h' })
      | .error e => (.error e, w) := by
  rcases w with ⟨st, h⟩
  cases h with
  | nil => rfl
  | cons y ys =>
    simp only [pyHeapreplace, Accel.pyHeapreplace, reduceCtorEq, ↓reduceIte]
    rw [Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (listSet_run 0 0 (by simp) _ (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (pySiftup_pure mx r 0 0 (by simp) _ (by simp))]
    rfl

theorem pyHeappushpop_pure (mx : Bool) (r : α → α → Bool) (item : α) (w : HW σ α) :
    (pyHeappushpop listSeq (pureCmp r) mx item).run w =
      (.ok (Accel.pyHeappushpop (heapOrd mx r) w.heap item).1,
        { w with heap := (Accel.pyHeappushpop (heapOrd mx r) w.heap item).2 }) := by
  rcases w with ⟨st, h⟩
  simp only [pyHeappushpop, pyTopLt, Eff.bind_assoc, Eff.ite_bind]
  rw [Eff.run_bind_ok (listTruth_run _)]
  cases h with
  | nil => rfl
  | cons y ys =>
    simp only [List.isEmpty_cons, Bool.not_false, ↓reduceIte]
    rw [Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < (y :: ys).length by simp)),
      Eff.run_bind_ok (pyLtOrd_pure _ _ _ _ _)]
    simp only [Accel.pyHeappushpop, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
    cases hc : heapOrd mx r (at! (y :: ys) 0) item
    · rfl
    · simp only [↓reduceIte]
      rw [Eff.run_bind_ok (listGet_run 0 0 (by simp) (show 0 < (y :: ys).length by simp)),
        Eff.run_bind_ok (listSet_run 0 0 (by simp) _ (show 0 < (y :: ys).length by simp)),
        Eff.run_bind_ok (pySiftup_pure mx r 0 0 (by simp) _ (by simp))]
      rfl

theorem pyEffFor_pure (mx : Bool) (r : α → α → Bool) :
    ∀ (is : List Nat) (w : HW σ α), (∀ i ∈ is, i < w.heap.length) →
      (effFor (fun i => pySiftup listSeq (pureCmp r) mx (i : Int)) is).run w =
        (.ok (), { w with heap := is.foldl (fun h i => Accel.pySiftup (heapOrd mx r) h i) w.heap }) := by
  intro is
  induction is with
  | nil => intro w _; rfl
  | cons i is ih =>
    intro w hi
    simp only [effFor]
    rw [Eff.run_bind_ok (pySiftup_pure mx r _ i rfl w (hi i (by simp)))]
    rw [ih _ (fun j hj => by simp only [Accel.pySiftup_length]; exact hi j (by simp [hj]))]
    rfl

theorem pyHeapify_pure (mx : Bool) (r : α → α → Bool) (w : HW σ α) :
    (pyHeapify listSeq (pureCmp r) mx).run w =
      (.ok (), { w with heap := Accel.pyHeapify (heapOrd mx r) w.heap }) := by
  simp only [pyHeapify]
  rw [Eff.run_bind_ok (listLen_run w), pyEffFor_pure mx r _ w (fun i hi => by simp at hi; omega)]
  rfl

/-! ### The C heapify with an honest comparison -/

theorem cClimb_pure (mx : Bool) (r : α → α → Bool) :
    ∀ (fuel j : Nat) (w : HW σ α), (∀ v ∈ Accel.climbSeq fuel j, v < w.heap.length) → j < fuel →
      (cClimb mx (pureCmp r) fuel j).run w =
        (.ok (), { w with heap :=
          ((Accel.climbSeq fuel j).foldl (fun h i => Accel.pySiftup (heapOrd mx r) h i) w.heap) }) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ h; omega
  | succ f ih =>
    intro j w hv hj
    simp only [cClimb, Accel.climbSeq]
    rw [Eff.run_bind_ok (cSiftup_pure mx r j w (hv j (by simp [Accel.climbSeq])))]
    by_cases he : j % 2 = 0
    · rw [if_pos he, if_pos he]; rfl
    · rw [if_neg he, if_neg he]
      rw [ih _ _ (fun v hvm => by
          simp only [Accel.pySiftup_length]
          exact hv v (by simp only [Accel.climbSeq, List.mem_cons]; right; rw [if_neg he]; exact hvm))
        (by rw [shr1']; omega)]
      rfl

theorem cEffForClimb_pure (mx : Bool) (r : α → α → Bool) :
    ∀ (is : List Nat) (w : HW σ α), (∀ i ∈ is, i < w.heap.length) →
      (effFor (fun i => cClimb mx (pureCmp r) (i + 1) i) is).run w =
        (.ok (), { w with heap := ((is.flatMap (fun i => Accel.climbSeq (i + 1) i)).foldl
          (fun h i => Accel.pySiftup (heapOrd mx r) h i) w.heap) }) := by
  intro is
  induction is with
  | nil => intro w _; rfl
  | cons i is ih =>
    intro w hi
    simp only [effFor, List.flatMap_cons, List.foldl_append]
    rw [Eff.run_bind_ok (cClimb_pure mx r (i + 1) i w (fun v hv => by
      have := Accel.climbSeq_le _ _ _ hv; have := hi i (by simp); omega) (by omega))]
    rw [ih _ (fun j hj => by
      simp only [Accel.foldl_siftup_length]; exact hi j (by simp [hj]))]

theorem cHeapify_pure (mx : Bool) (r : α → α → Bool) (tp : String) (w : HW σ α) :
    (cHeapify mx (pureCmp r) ⟨true, tp⟩).run w =
      (.ok (), { w with heap := Accel.pyHeapify (heapOrd mx r) w.heap }) := by
  by_cases hn : w.heap.length ≤ 2500
  · have hs := heapify_sim mx (fun a b s => (.ok (r a b), s)) tp w hn
    change Rel ((cHeapify mx (pureCmp r) ⟨true, tp⟩).run w)
      ((pyHeapify listSeq (pureCmp r) mx).run w) at hs
    rw [pyHeapify_pure] at hs
    rcases hc : (cHeapify mx (pureCmp r) ⟨true, tp⟩).run w with ⟨rc, wc⟩
    rw [hc] at hs
    cases rc with
    | ok u => obtain ⟨-, rfl⟩ := hs; rfl
    | error e => cases e <;> exact hs.elim
  · simp only [cHeapify, cChecked, ↓reduceIte, cHeapifyInternal]
    rw [Eff.run_bind_ok (cSize_run w), if_pos (by omega)]
    simp only [cCacheFriendly]
    rw [Eff.run_bind_ok (cSize_run w)]
    have hk := keepTopBit_le (w.heap.length >>> 1 + 1) (by omega)
    have hk' := hk
    rw [shr1'] at hk'
    have hA : ∀ i ∈ downFrom (w.heap.length >>> 1 >>> 1) (keepTopBit (w.heap.length >>> 1 + 1) - 1),
        i < w.heap.length := by
      intro i hi
      rw [Accel.mem_downFrom] at hi
      simp only [shr1'] at hi
      omega
    have hB : ∀ i ∈ downFrom (keepTopBit (w.heap.length >>> 1 + 1) - 1) (w.heap.length >>> 1),
        i < w.heap.length := by
      intro i hi
      rw [Accel.mem_downFrom] at hi
      simp only [shr1'] at hi
      omega
    rw [Eff.run_bind_ok (cEffForClimb_pure mx r _ w hA)]
    rw [cEffForClimb_pure mx r _ _ (fun i hi => by
      simp only [Accel.foldl_siftup_length]; exact hB i hi)]
    -- the old pure model computes the same two folds, and equals the Python heapify
    have hold := Accel.cCacheFriendly_eq (heapOrd mx r) w.heap (by omega)
    simp only [Accel.cCacheFriendlyHeapify] at hold
    rw [Accel.forDown_climb _ _ _ hA] at hold
    simp only [bind, Except.bind] at hold
    rw [Accel.forDown_climb _ _ _ (fun i hi => by
      simp only [Accel.foldl_siftup_length]; exact hB i hi)] at hold
    rw [← List.foldl_append] at hold ⊢
    simp only [Except.ok.injEq] at hold
    rw [hold]

/-! ### Registry properties -/

theorem strictWeak_heapOrd {r : α → α → Bool} (h : Accel.StrictWeak r) (mx : Bool) :
    Accel.StrictWeak (heapOrd mx r) := by
  cases mx
  · exact h
  · exact h.maxLt

/-- **The heap invariant, for any element type with an honest strict weak order.** For every
element type and every comparison `r` that is a strict weak order (a pure `__lt__` that never
raises), run as the Python twin's `<`: on a min-heap (max-heap for `mx`), `heappush`,
`heappop`, `heapreplace` and `heappushpop` succeed, leave a heap, permute the items as
documented, and pop / return the smallest (largest) item.

Source: Lib/heapq.py:3-4 (`heap[k] <= heap[2*k+1]` and `heap[k] <= heap[2*k+2]`, read with `<=`
as `not >`), the docstrings at :134, :139, :149-158, :165; Doc/library/heapq.rst for the
`*_max` functions. The C twins compute the same (`HeapTwinsAgree`). -/
def HeapOpsKeepInvariant : Prop :=
  ∀ (σ α : Type) [Inhabited α] (r : α → α → Bool) (mx : Bool) (w : HW σ α) (item : α),
    Accel.StrictWeak r → Accel.IsHeap (heapOrd mx r) w.heap →
      (∃ h', (pyHeappush listSeq (pureCmp r) mx item).run w = (.ok (), { w with heap := h' }) ∧
        Accel.IsHeap (heapOrd mx r) h' ∧ h'.Perm (item :: w.heap)) ∧
      (w.heap ≠ [] → ∃ v h', (pyHeappop listSeq (pureCmp r) mx).run w = (.ok v, { w with heap := h' }) ∧
        Accel.IsHeap (heapOrd mx r) h' ∧ (v :: h').Perm w.heap ∧
        ∀ e ∈ w.heap, heapOrd mx r e v = false) ∧
      (w.heap ≠ [] → ∃ v h',
        (pyHeapreplace listSeq (pureCmp r) mx item).run w = (.ok v, { w with heap := h' }) ∧
        Accel.IsHeap (heapOrd mx r) h' ∧ (v :: h').Perm (item :: w.heap) ∧
        ∀ e ∈ w.heap, heapOrd mx r e v = false) ∧
      (∃ v h', (pyHeappushpop listSeq (pureCmp r) mx item).run w = (.ok v, { w with heap := h' }) ∧
        Accel.IsHeap (heapOrd mx r) h' ∧ (v :: h').Perm (item :: w.heap) ∧
        ∀ e ∈ item :: w.heap, heapOrd mx r e v = false)

theorem heapOpsKeepInvariant_proven : HeapOpsKeepInvariant := by
  intro σ α _ r mx w item hr hh
  have hlt := strictWeak_heapOrd hr mx
  refine ⟨?_, fun hne => ?_, fun hne => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := Accel.pyHeappush_correct hlt w.heap item hh
    exact ⟨_, pyHeappush_pure mx r item w, h1, h2⟩
  · obtain ⟨v, h', e, h1, h2, h3⟩ := Accel.pyHeappop_correct hlt w.heap hh hne
    refine ⟨v, h', ?_, h1, h2, h3⟩
    rw [pyHeappop_pure, e]
  · obtain ⟨v, h', e, h1, h2, h3⟩ := Accel.pyHeapreplace_correct hlt w.heap item hh hne
    refine ⟨v, h', ?_, h1, h2, h3⟩
    rw [pyHeapreplace_pure, e]
  · obtain ⟨h1, h2, h3⟩ := Accel.pyHeappushpop_correct hlt w.heap item hh
    exact ⟨_, _, pyHeappushpop_pure mx r item w, h1, h2, h3⟩

/-- **`heapify` makes a heap.** For every element type, strict weak order `r` (an honest
`__lt__`) and list, the Python `heapify` (`heapify_max`) succeeds and leaves a min-heap
(max-heap) holding the same items. Source: Lib/heapq.py:171-180, :211-215;
Doc/library/heapq.rst. -/
def HeapifyMakesHeap : Prop :=
  ∀ (σ α : Type) [Inhabited α] (r : α → α → Bool) (mx : Bool) (w : HW σ α),
    Accel.StrictWeak r →
      ∃ h', (pyHeapify listSeq (pureCmp r) mx).run w = (.ok (), { w with heap := h' }) ∧
        Accel.IsHeap (heapOrd mx r) h' ∧ h'.Perm w.heap

theorem heapifyMakesHeap_proven : HeapifyMakesHeap := by
  intro σ α _ r mx w hr
  obtain ⟨h1, h2⟩ := Accel.pyHeapify_correct (strictWeak_heapOrd hr mx) w.heap
  exact ⟨_, pyHeapify_pure mx r w, h1, h2⟩

/-- **C and Python `heapify` agree at every length, with an honest comparison.** For every
element type, every pure comparison `r` (no order assumption), the min- and max-heap variants
and every list, the C `heapify` (which above 2500 items sifts in the cache-friendly order of
`cache_friendly_heapify`, `_heapqmodule.c:332-363`, using `keep_top_bit`, :300-310) and the
Python `heapify` both succeed and leave the same list. Source: the comment at
`_heapqmodule.c:326-329` ("both ways ... produce exactly the same heap"). -/
def HeapifyTwinsAgree : Prop :=
  ∀ (σ α : Type) [Inhabited α] (r : α → α → Bool) (mx : Bool) (w : HW σ α) (tp : String),
    Rel ((cHeapify mx (pureCmp r) ⟨true, tp⟩).run w) ((pyHeapify listSeq (pureCmp r) mx).run w)

theorem heapifyTwinsAgree_proven : HeapifyTwinsAgree := by
  intro σ α _ r mx w tp
  rw [cHeapify_pure, pyHeapify_pure]
  exact ⟨rfl, rfl⟩

/-- `heapify` agreement at every length for every comparison that does not touch the list but
may raise or keep state (`HeapTwinsAgree` proves it up to 2500 items). -/
def HeapifyTwinsAgreeFallible : Prop :=
  ∀ (σ α : Type) [Inhabited α] (f : α → α → σ → Except PyExc Bool × σ) (mx : Bool) (w : HW σ α)
    (tp : String),
    Rel ((cHeapify mx (ofSt f) ⟨true, tp⟩).run w) ((pyHeapify listSeq (ofSt f) mx).run w)

/-- A comparison that raises at once and records its left operand. -/
def raiseRecord : Nat → Nat → Nat → Except PyExc Bool × Nat :=
  fun a _ _ => (.error (.named "ValueError" "cmp"), a)

theorem Rel.st {β : Type} {r : Except CErr β × HW σ α} {p : Except PyExc β × HW σ α}
    (h : Rel r p) : r.2.st = p.2.st := by
  rcases r with ⟨r, w1⟩
  rcases p with ⟨p, w2⟩
  cases r with
  | ok a => cases p with
    | ok b => exact congrArg HW.st h.2
    | error _ => exact h.elim
  | error e => cases e with
    | crash _ => cases p <;> exact h.elim
    | py e1 => cases p with
      | ok _ => exact h.elim
      | error e2 => exact h.2

set_option maxRecDepth 100000 in
theorem cHeapify2501 :
    ((cHeapify false (ofSt raiseRecord) ⟨true, "list"⟩).run ⟨0, List.range 2501⟩).2.st = 2045 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem pyHeapify2501 :
    ((pyHeapify listSeq (ofSt raiseRecord) false).run ⟨0, List.range 2501⟩).2.st = 2499 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- `heapify(list(range(2501)))` with a comparison that raises: C compares
`heap[2045] < heap[2046]` first (the cache-friendly order starts at `leftmost - 1 = 1022`), Python
`heap[2499] < heap[2500]` (it starts at `n // 2 - 1 = 1249`), so the comparison sees different
operands and the exceptions it raises can differ. -/
theorem heapifyTwinsAgreeFallible_refuted : ¬ HeapifyTwinsAgreeFallible := by
  intro h
  have := (h Nat Nat raiseRecord false ⟨0, List.range 2501⟩ "list").st
  rw [cHeapify2501, pyHeapify2501] at this
  exact absurd this (by decide)

end PyLean.Accel.Heapq
