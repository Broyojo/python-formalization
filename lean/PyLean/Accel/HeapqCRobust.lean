import PyLean.Accel.HeapqRobust

/-!
The public C functions (`_heapq.heappush`, `heappop`, `heapreplace`, `heappushpop`, `heapify`
and their `*_max` variants, with the clinic argument check) under any comparison.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {σ α : Type} [Inhabited α]

/-! ### heapify -/

theorem effFor_out (lt : Cmp σ α) (body : Nat → CM σ α Unit) (n : Nat) :
    ∀ (is : List Nat), (∀ i ∈ is, ∀ w : HW σ α, w.heap.length = n →
        Out lt (fun _ w' => w'.heap.length = n) ((body i).run w)) →
      ∀ w : HW σ α, w.heap.length = n →
        Out lt (fun _ w' => w'.heap.length = n) ((effFor body is).run w) := by
  intro is
  induction is with
  | nil => intro _ w hw; exact hw
  | cons i is ih =>
    intro hb w hw
    simp only [effFor]
    exact Out.bind (hb i (by simp) w hw)
      (fun _ w1 h1 => ih (fun j hj => hb j (by simp [hj])) w1 h1)

theorem cClimb_out (mx : Bool) (lt : Cmp σ α) (n : Nat) :
    ∀ (fuel j : Nat) (w : HW σ α), w.heap.length = n → j < n → j < fuel →
      Out lt (fun _ w' => w'.heap.length = n) ((cClimb mx lt fuel j).run w) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro j w hw hj hf
    simp only [cClimb]
    have h1 := cSiftup_out mx lt j w (by omega)
    rw [hw] at h1
    refine Out.bind h1 (fun _ w1 hw1 => ?_)
    by_cases he : j % 2 = 0
    · rw [if_pos he]; exact hw1
    · rw [if_neg he]
      exact ih _ w1 hw1 (by rw [shr1']; omega) (by rw [shr1']; omega)

theorem keepTopBit_le (x : Nat) (h : 1 ≤ x) : keepTopBit x ≤ x := by
  obtain ⟨R, e, b, -⟩ := Accel.keepTopBit_spec x h
  omega

theorem cHeapifyInternal_out (mx : Bool) (lt : Cmp σ α) (w : HW σ α) :
    Out lt (fun _ w' => w'.heap.length = w.heap.length) ((cHeapifyInternal mx lt).run w) := by
  simp only [cHeapifyInternal, Eff.run_bind, cSize_run]
  by_cases hn : w.heap.length > 2500
  · rw [if_pos hn]
    simp only [cCacheFriendly, Eff.run_bind, cSize_run]
    have hk := keepTopBit_le (w.heap.length >>> 1 + 1) (by omega)
    have hb : ∀ lo hi, hi ≤ w.heap.length >>> 1 → ∀ i ∈ downFrom lo hi, ∀ w' : HW σ α,
        w'.heap.length = w.heap.length →
        Out lt (fun _ w'' => w''.heap.length = w.heap.length) ((cClimb mx lt (i + 1) i).run w') := by
      intro lo hi hhi i hi' w' hw'
      rw [Accel.mem_downFrom] at hi'
      exact cClimb_out mx lt _ _ _ w' hw' (by rw [shr1'] at hhi; omega) (by omega)
    have h1 := effFor_out lt (fun i => cClimb mx lt (i + 1) i) w.heap.length _
      (hb (w.heap.length >>> 1 >>> 1) (keepTopBit (w.heap.length >>> 1 + 1) - 1) (by omega)) w rfl
    have := Out.bind (f := fun _ => effFor (fun i => cClimb mx lt (i + 1) i)
      (downFrom (keepTopBit (w.heap.length >>> 1 + 1) - 1) (w.heap.length >>> 1))) h1
      (fun _ w1 hw1 => effFor_out lt _ _ _ (hb _ _ (Nat.le_refl _)) w1 hw1)
    simpa only [Eff.run_bind] using this
  · rw [if_neg hn]
    refine effFor_out lt _ _ _ (fun i hi w' hw' => ?_) w rfl
    rw [Accel.mem_downFrom, shr1'] at hi
    have := cSiftup_out mx lt i w' (by omega)
    rw [hw'] at this
    exact this

/-! ### The public functions -/

/-- The outcomes a public C function may have: those of `Out`, or `IndexError('index out of
range')` where `idxOk` allows it. -/
def COut (lt : Cmp σ α) {β : Type} (P : β → HW σ α → Prop) (idxOk : Prop)
    (r : Except CErr β × HW σ α) : Prop :=
  Out lt P r ∨ (r.1 = .error (.py idxErr) ∧ idxOk)

theorem COut.ok_of {lt : Cmp σ α} {β : Type} {P : β → HW σ α → Prop} {idxOk : Prop}
    {r : Except CErr β × HW σ α} (h : COut lt P idxOk r) (hn : NoRaise lt) (hk : KeepsLen lt)
    (hi : ¬ idxOk) : ∃ b w', r = (.ok b, w') ∧ P b w' := by
  rcases r with ⟨r, w'⟩
  rcases h with h | ⟨_, h⟩
  · cases r with
    | ok b => exact ⟨b, w', rfl, h⟩
    | error e =>
      cases e with
      | py e =>
        rcases h with ⟨_, h⟩ | h
        · exact absurd hk h
        · exact absurd hn h.not_noRaise
      | crash _ => exact h.elim
  · exact absurd h hi

theorem Out.ok_of {lt : Cmp σ α} {β : Type} {P : β → HW σ α → Prop} {r : Except CErr β × HW σ α}
    (h : Out lt P r) (hn : NoRaise lt) (hk : KeepsLen lt) : ∃ b w', r = (.ok b, w') :=
  match COut.ok_of (idxOk := False) (Or.inl h) hn hk id with
  | ⟨b, w', e, _⟩ => ⟨b, w', e⟩

theorem cHeappush_out (mx : Bool) (lt : Cmp σ α) (tp : String) (item : α) (w : HW σ α) :
    Out lt (fun _ w' => w'.heap.length = w.heap.length + 1)
      ((cHeappush mx lt ⟨true, tp⟩ item).run w) := by
  simp only [cHeappush, cChecked, if_true, Eff.run_bind, cAppend_run, cSize_run]
  have := cSiftdown_out mx lt 0 ((w.heap ++ [item]).length - 1) { w with heap := w.heap ++ [item] }
    (by simp)
  simpa using this

/-- `x >>= fun _ => pure v` keeps the outcome of `x`. -/
theorem Out.then_pure {lt : Cmp σ α} {β : Type} {P : Unit → HW σ α → Prop} {Q : β → HW σ α → Prop}
    {x : CM σ α Unit} {v : β} {w : HW σ α} (h : Out lt P (x.run w)) (hPQ : ∀ w', P () w' → Q v w') :
    Out lt Q ((x >>= fun _ => pure v).run w) :=
  Out.bind h (fun _ w' hp => hPQ w' hp)

theorem cHeappop_out (mx : Bool) (lt : Cmp σ α) (tp : String) (w : HW σ α) :
    COut lt (fun _ w' => w'.heap.length = w.heap.length - 1) (w.heap = [])
      ((cHeappop mx lt ⟨true, tp⟩).run w) := by
  simp only [cHeappop, cChecked, if_true, cHeappopInternal]
  rw [Eff.run_bind_ok (cSize_run w)]
  by_cases h0 : w.heap.length = 0
  · rw [if_pos h0]
    exact Or.inr ⟨rfl, List.eq_nil_of_length_eq_zero h0⟩
  · rw [if_neg h0, Eff.run_bind_ok (cItem_run (show w.heap.length - 1 < w.heap.length by omega)),
      Eff.run_bind_ok (cDelTail_run _ _)]
    left
    by_cases h1 : w.heap.length - 1 = 0
    · rw [if_pos h1]; simp only [Eff.run_pure, Out, List.length_take]; omega
    · rw [if_neg h1,
        Eff.run_bind_ok (cItem_run (show 0 < (w.heap.take (w.heap.length - 1)).length by
          simp; omega)),
        Eff.run_bind_ok (cStore_run (show 0 < (w.heap.take (w.heap.length - 1)).length by
          simp; omega))]
      exact Out.then_pure (cSiftup_out mx lt 0 _ (by simp; omega)) (fun w' h => by simp at h; omega)

theorem cHeapreplace_out (mx : Bool) (lt : Cmp σ α) (tp : String) (item : α) (w : HW σ α) :
    COut lt (fun _ w' => w'.heap.length = w.heap.length) (w.heap = [])
      ((cHeapreplace mx lt ⟨true, tp⟩ item).run w) := by
  simp only [cHeapreplace, cChecked, if_true, cHeapreplaceInternal]
  rw [Eff.run_bind_ok (cSize_run w)]
  by_cases h0 : w.heap.length = 0
  · rw [if_pos h0]
    exact Or.inr ⟨rfl, List.eq_nil_of_length_eq_zero h0⟩
  · rw [if_neg h0, Eff.run_bind_ok (cItem_run (show 0 < w.heap.length by omega)),
      Eff.run_bind_ok (cStore_run (show 0 < w.heap.length by omega))]
    left
    have := cSiftup_out mx lt 0 { w with heap := w.heap.set 0 item } (by simp; omega)
    exact Out.then_pure this (fun w' h => by simp at h; omega)

theorem cHeappushpop_out (mx : Bool) (lt : Cmp σ α) (tp : String) (item : α) (w : HW σ α) :
    COut lt (fun _ w' => KeepsLen lt → w'.heap.length = w.heap.length) (¬ KeepsLen lt)
      ((cHeappushpop mx lt ⟨true, tp⟩ item).run w) := by
  simp only [cHeappushpop, cChecked, if_true, cHeappushpopImpl]
  rw [Eff.run_bind_ok (cSize_run w)]
  by_cases h0 : w.heap.length = 0
  · rw [if_pos h0]; exact Or.inl (fun _ => rfl)
  · rw [if_neg h0, Eff.run_bind_ok (cItem_run (show 0 < w.heap.length by omega))]
    obtain ⟨a, b, hab⟩ := cLtOrd_eq mx lt (at! w.heap 0) item
    rw [hab]
    rcases h : (lt a b).run w with ⟨r, w1⟩
    cases r with
    | error e =>
      rw [Eff.run_bind_err (show (cLt lt a b).run w = (.error (.py e), w1) by rw [cLt_run, h])]
      exact Or.inl (Or.inr ⟨a, b, w, w1, h⟩)
    | ok c =>
      rw [Eff.run_bind_ok (show (cLt lt a b).run w = (.ok c, w1) by rw [cLt_run, h])]
      have hkl : KeepsLen lt → w1.heap.length = w.heap.length := fun hk => by
        have := hk a b w; rw [h] at this; exact this
      cases c
      · simp only [Bool.not_false, if_true, Eff.run_pure]; exact Or.inl hkl
      · simp only [Bool.not_true, Bool.false_eq_true, if_false]
        rw [Eff.run_bind_ok (cSize_run w1)]
        by_cases h1 : w1.heap.length = 0
        · rw [if_pos h1]
          exact Or.inr ⟨rfl, fun hk => h0 (by rw [← hkl hk]; exact h1)⟩
        · rw [if_neg h1, Eff.run_bind_ok (cItem_run (show 0 < w1.heap.length by omega)),
            Eff.run_bind_ok (cStore_run (show 0 < w1.heap.length by omega))]
          left
          have := cSiftup_out mx lt 0 { w1 with heap := w1.heap.set 0 item } (by simp; omega)
          exact Out.then_pure this (fun w' h2 hk => by simp at h2; rw [h2]; exact hkl hk)

theorem cHeapify_out (mx : Bool) (lt : Cmp σ α) (tp : String) (w : HW σ α) :
    Out lt (fun _ w' => w'.heap.length = w.heap.length) ((cHeapify mx lt ⟨true, tp⟩).run w) := by
  simp only [cHeapify, cChecked, if_true]
  exact cHeapifyInternal_out mx lt w

/-- **The C functions under any comparison.** For every element type, every comparison
(raising, returning an object whose truth test raises, stateful, reading or mutating the heap
list in any way), both the min-heap and the `*_max` variants, and any list:

* none of `heappush`, `heappop`, `heapreplace`, `heappushpop`, `heapify` reads or writes the
  list out of bounds or exhausts its loop fuel, and each raises only an exception the
  comparison raised, `RuntimeError('list changed size during iteration')` when the comparison
  can change the list's length, or `IndexError('index out of range')`: for `heappop` and
  `heapreplace` only on an empty heap, for `heappushpop` only when the comparison can change
  the length (it emptied the list; `_heapqmodule.c:285-288`);
* on success the list has its documented length (one more for `heappush`, one fewer for
  `heappop`, the same for `heapreplace` and `heapify`, and for `heappushpop` the same when the
  comparison cannot change the length);
* hence with a comparison that never raises and never changes the length, every call
  succeeds (`heappop` and `heapreplace` on a non-empty heap), even if the comparison
  overwrites items;
* an argument that fails `PyList_Check` raises `TypeError` with clinic's message before
  anything else runs, even on what would be an empty heap.

Source: invariant (no crash, no internal error); the `RuntimeError` checks at
`_heapqmodule.c:53-57`, `:103-107`, `:435-439`, `:485-489`. -/
def CHeapRobust : Prop :=
  ∀ (σ α : Type) [Inhabited α] (lt : Cmp σ α) (mx : Bool) (w : HW σ α) (item : α) (tp : String),
    (Out lt (fun _ w' => w'.heap.length = w.heap.length + 1)
        ((cHeappush mx lt ⟨true, tp⟩ item).run w) ∧
     COut lt (fun _ w' => w'.heap.length = w.heap.length - 1) (w.heap = [])
       ((cHeappop mx lt ⟨true, tp⟩).run w) ∧
     COut lt (fun _ w' => w'.heap.length = w.heap.length) (w.heap = [])
       ((cHeapreplace mx lt ⟨true, tp⟩ item).run w) ∧
     COut lt (fun _ w' => KeepsLen lt → w'.heap.length = w.heap.length) (¬ KeepsLen lt)
       ((cHeappushpop mx lt ⟨true, tp⟩ item).run w) ∧
     Out lt (fun _ w' => w'.heap.length = w.heap.length)
       ((cHeapify mx lt ⟨true, tp⟩).run w)) ∧
    (NoRaise lt → KeepsLen lt →
      (∃ w', (cHeappush mx lt ⟨true, tp⟩ item).run w = (.ok (), w')) ∧
      (w.heap ≠ [] → ∃ v w', (cHeappop mx lt ⟨true, tp⟩).run w = (.ok v, w')) ∧
      (w.heap ≠ [] → ∃ v w', (cHeapreplace mx lt ⟨true, tp⟩ item).run w = (.ok v, w')) ∧
      (∃ v w', (cHeappushpop mx lt ⟨true, tp⟩ item).run w = (.ok v, w')) ∧
      (∃ w', (cHeapify mx lt ⟨true, tp⟩).run w = (.ok (), w'))) ∧
    ((cHeappush mx lt ⟨false, tp⟩ item).run w =
       (.error (.py (badArg (fnName "heappush" mx) "argument 1" tp)), w) ∧
     (cHeappop mx lt ⟨false, tp⟩).run w =
       (.error (.py (badArg (fnName "heappop" mx) "argument" tp)), w) ∧
     (cHeapreplace mx lt ⟨false, tp⟩ item).run w =
       (.error (.py (badArg (fnName "heapreplace" mx) "argument 1" tp)), w) ∧
     (cHeappushpop mx lt ⟨false, tp⟩ item).run w =
       (.error (.py (badArg (fnName "heappushpop" mx) "argument 1" tp)), w) ∧
     (cHeapify mx lt ⟨false, tp⟩).run w =
       (.error (.py (badArg (fnName "heapify" mx) "argument" tp)), w))

theorem cHeapRobust_proven : CHeapRobust := by
  intro σ α _ lt mx w item tp
  have h1 := cHeappush_out mx lt tp item w
  have h2 := cHeappop_out mx lt tp w
  have h3 := cHeapreplace_out mx lt tp item w
  have h4 := cHeappushpop_out mx lt tp item w
  have h5 := cHeapify_out mx lt tp w
  refine ⟨⟨h1, h2, h3, h4, h5⟩, fun hn hk => ⟨?_, fun hne => ?_, fun hne => ?_, ?_, ?_⟩,
    ⟨rfl, rfl, rfl, rfl, rfl⟩⟩
  · obtain ⟨b, w', e⟩ := h1.ok_of hn hk; exact ⟨w', e⟩
  · obtain ⟨b, w', e, _⟩ := h2.ok_of hn hk hne; exact ⟨b, w', e⟩
  · obtain ⟨b, w', e, _⟩ := h3.ok_of hn hk hne; exact ⟨b, w', e⟩
  · obtain ⟨b, w', e, _⟩ := h4.ok_of hn hk (fun h => h hk); exact ⟨b, w', e⟩
  · obtain ⟨b, w', e⟩ := h5.ok_of hn hk; exact ⟨w', e⟩

end PyLean.Accel.Heapq
