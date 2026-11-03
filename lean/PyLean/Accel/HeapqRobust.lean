import PyLean.Accel.HeapqModel
import PyLean.Accel.HeapifyTwins

/-!
The C heap functions under an arbitrary comparison (one that may raise, return an object
whose truth test raises, keep state, read the list, or append to, pop from, clear or
overwrite it): they never access the list out of bounds, never run out of loop fuel, and
raise only what the comparison raised, `RuntimeError('list changed size during iteration')`
when a comparison changed the list's length, or `IndexError('index out of range')` for an
empty heap. The `IndexError` of `siftup` / `siftdown` (`_heapqmodule.c:34-37`, `:80-83`) is
unreachable from the public functions.
-/

namespace PyLean.Accel.Heapq

open PyLean

theorem Eff.run_bind_ok {W ε β γ : Type} {x : Eff W ε β} {f : β → Eff W ε γ} {w w' : W} {b : β}
    (h : x.run w = (.ok b, w')) : (x >>= f).run w = (f b).run w' := by
  simp [h]

theorem Eff.run_bind_err {W ε β γ : Type} {x : Eff W ε β} {f : β → Eff W ε γ} {w w' : W} {e : ε}
    (h : x.run w = (.error e, w')) : (x >>= f).run w = (.error e, w') := by
  simp [h]

theorem shr1' (n : Nat) : n >>> 1 = n / 2 := by rw [Nat.shiftRight_eq_div_pow]

variable {σ α : Type} [Inhabited α]

/-! ### Primitive steps -/

@[simp] theorem cSize_run (w : HW σ α) : (cSize : CM σ α Nat).run w = (.ok w.heap.length, w) := rfl

theorem cItem_run {i : Nat} {w : HW σ α} (h : i < w.heap.length) :
    (cItem i : CM σ α α).run w = (.ok (at! w.heap i), w) := by
  simp [cItem, h]

theorem cStore_run {i : Nat} {v : α} {w : HW σ α} (h : i < w.heap.length) :
    (cStore i v : CM σ α Unit).run w = (.ok (), { w with heap := w.heap.set i v }) := by
  simp [cStore, h]

@[simp] theorem cAppend_run (v : α) (w : HW σ α) :
    (cAppend v : CM σ α Unit).run w = (.ok (), { w with heap := w.heap ++ [v] }) := rfl

@[simp] theorem cDelTail_run (lo : Nat) (w : HW σ α) :
    (cDelTail lo : CM σ α Unit).run w = (.ok (), { w with heap := w.heap.take lo }) := rfl

@[simp] theorem cRaise_run {β : Type} (e : PyExc) (w : HW σ α) :
    (cRaise e : CM σ α β).run w = (.error (.py e), w) := rfl

theorem cLt_run (lt : Cmp σ α) (a b : α) (w : HW σ α) :
    (cLt lt a b).run w = match (lt a b).run w with
      | (.ok c, w') => (.ok c, w')
      | (.error e, w') => (.error (.py e), w') := rfl

/-- The comparison in either operand order is one call of `lt`. -/
theorem cLtOrd_eq (mx : Bool) (lt : Cmp σ α) (x y : α) :
    ∃ a b, cLtOrd mx lt x y = cLt lt a b := by
  cases mx
  · exact ⟨x, y, rfl⟩
  · exact ⟨y, x, rfl⟩

/-! ### What a comparison may do -/

/-- The comparison never changes the length of the heap list. -/
def KeepsLen (lt : Cmp σ α) : Prop := ∀ a b w, ((lt a b).run w).2.heap.length = w.heap.length

/-- `e` is an exception the comparison can raise. -/
def CbErr (lt : Cmp σ α) (e : PyExc) : Prop := ∃ a b w w', (lt a b).run w = (.error e, w')

/-- The comparison never raises. -/
def NoRaise (lt : Cmp σ α) : Prop := ∀ a b w e w', (lt a b).run w ≠ (.error e, w')

theorem CbErr.not_noRaise {lt : Cmp σ α} {e : PyExc} (h : CbErr lt e) : ¬ NoRaise lt := by
  obtain ⟨a, b, w, w', h⟩ := h
  exact fun hn => hn a b w e w' h

/-- The outcomes a C step may have: success satisfying `P`; a size change detected after a
comparison that can change the list's length; or an exception the comparison raised.
Never a crash. -/
def Out (lt : Cmp σ α) {β : Type} (P : β → HW σ α → Prop) : Except CErr β × HW σ α → Prop
  | (.ok b, w') => P b w'
  | (.error (.py e), _) => (e = sizeChanged ∧ ¬ KeepsLen lt) ∨ CbErr lt e
  | (.error (.crash _), _) => False

theorem Out.bind {lt : Cmp σ α} {β γ : Type} {P : β → HW σ α → Prop} {Q : γ → HW σ α → Prop}
    {x : CM σ α β} {f : β → CM σ α γ} {w : HW σ α} (hx : Out lt P (x.run w))
    (hf : ∀ b w', P b w' → Out lt Q ((f b).run w')) : Out lt Q ((x >>= f).run w) := by
  rcases h : x.run w with ⟨r, w1⟩
  rw [h] at hx
  cases r with
  | ok b => rw [Eff.run_bind_ok h]; exact hf b w1 hx
  | error e =>
    rw [Eff.run_bind_err h]
    cases e with
    | py e => exact hx
    | crash _ => exact hx.elim

theorem Out.mono {lt : Cmp σ α} {β : Type} {P Q : β → HW σ α → Prop} {r : Except CErr β × HW σ α}
    (h : Out lt P r) (hPQ : ∀ b w, P b w → Q b w) : Out lt Q r := by
  rcases r with ⟨r, w⟩
  cases r with
  | ok b => exact hPQ b w h
  | error e => cases e <;> exact h

/-- One comparison, followed by `PyList_GET_SIZE` and the size re-check against `size`. -/
theorem cmp_out (lt : Cmp σ α) (a b : α) (size : Nat) (w : HW σ α) (hw : w.heap.length = size)
    {β : Type} (Q : β → HW σ α → Prop) (k : Bool → CM σ α β)
    (hk : ∀ c w1, w1.heap.length = size → Out lt Q ((k c).run w1)) :
    Out lt Q ((do
      let c ← cLt lt a b
      let size' ← cSize
      if size ≠ size' then cRaise sizeChanged else k c : CM σ α β).run w) := by
  simp only [Eff.run_bind, cLt_run]
  rcases h : (lt a b).run w with ⟨r, w1⟩
  cases r with
  | error e => exact Or.inr ⟨a, b, w, w1, h⟩
  | ok c =>
    simp only [cSize_run]
    by_cases hs : size = w1.heap.length
    · rw [if_neg (fun h => h hs)]; exact hk c w1 hs.symm
    · rw [if_pos hs]
      refine Or.inl ⟨rfl, fun hk => ?_⟩
      have := hk a b w
      rw [h] at this
      exact hs (by simp at this; omega)

/-! ### siftdown -/

theorem cSiftdownLoop_out (mx : Bool) (lt : Cmp σ α) (s0 size : Nat) :
    ∀ (fuel : Nat) (newitem : α) (pos : Nat) (w : HW σ α), w.heap.length = size → pos < size →
      pos < fuel →
      Out lt (fun _ w' => w'.heap.length = size)
        ((cSiftdownLoop mx lt s0 size fuel newitem pos).run w) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro newitem pos w hw hpos hf
    simp only [cSiftdownLoop]
    by_cases hgt : pos > s0
    · rw [if_pos hgt]
      have hpp : (pos - 1) >>> 1 < pos := by rw [shr1']; omega
      rw [Eff.run_bind_ok (cItem_run (show (pos - 1) >>> 1 < w.heap.length by omega))]
      obtain ⟨a, b, hab⟩ := cLtOrd_eq mx lt newitem (at! w.heap ((pos - 1) >>> 1))
      rw [hab]
      refine cmp_out lt a b size w hw _ _ (fun c w1 hw1 => ?_)
      cases c
      · simp only [Bool.not_false, if_true, Eff.run_pure, Out]; exact hw1
      · simp only [Bool.not_true, Bool.false_eq_true, if_false]
        rw [Eff.run_bind_ok (cItem_run (show (pos - 1) >>> 1 < w1.heap.length by omega)),
          Eff.run_bind_ok (cItem_run (show pos < w1.heap.length by omega)),
          Eff.run_bind_ok (cStore_run (show (pos - 1) >>> 1 < w1.heap.length by omega)),
          Eff.run_bind_ok (cStore_run (show pos < (w1.heap.set ((pos - 1) >>> 1) _).length by
            simp; omega))]
        exact ih _ _ _ (by simp; omega) (by omega) (by omega)
    · rw [if_neg hgt]
      exact hw

theorem cSiftdown_out (mx : Bool) (lt : Cmp σ α) (s0 pos : Nat) (w : HW σ α)
    (hpos : pos < w.heap.length) :
    Out lt (fun _ w' => w'.heap.length = w.heap.length) ((cSiftdown mx lt s0 pos).run w) := by
  simp only [cSiftdown, Eff.run_bind, cSize_run, if_neg (Nat.not_le.2 hpos), cItem_run hpos]
  exact cSiftdownLoop_out mx lt s0 _ _ _ _ w rfl hpos (by omega)

/-! ### siftup -/

theorem cChild_out (mx : Bool) (lt : Cmp σ α) (endpos cp : Nat) (w : HW σ α)
    (hw : w.heap.length = endpos) (hcp : cp < endpos) :
    Out lt (fun c w' => cp ≤ c ∧ c < endpos ∧ w'.heap.length = endpos)
      ((cChild mx lt endpos cp).run w) := by
  unfold cChild
  by_cases hr : cp + 1 < endpos
  · rw [if_pos hr]
    rw [Eff.run_bind_ok (cItem_run (show (if mx then cp + 1 else cp) < w.heap.length by
        split <;> omega)),
      Eff.run_bind_ok (cItem_run (show (if mx then cp else cp + 1) < w.heap.length by
        split <;> omega))]
    refine cmp_out lt _ _ endpos w hw _ _ (fun c w1 hw1 => ?_)
    simp only [Eff.run_pure, Out]
    refine ⟨by omega, ?_, hw1⟩
    split <;> omega
  · rw [if_neg hr]
    exact ⟨Nat.le_refl _, hcp, hw⟩

theorem cSiftupLoop_out (mx : Bool) (lt : Cmp σ α) (endpos : Nat) :
    ∀ (fuel pos : Nat) (w : HW σ α), w.heap.length = endpos → pos < endpos →
      endpos - pos < fuel →
      Out lt (fun p w' => p < endpos ∧ w'.heap.length = endpos)
        ((cSiftupLoop mx lt endpos (endpos >>> 1) fuel pos).run w) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro pos w hw hpos hf
    simp only [cSiftupLoop]
    by_cases hlim : pos < endpos >>> 1
    · rw [if_pos hlim]
      have hc : 2 * pos + 1 < endpos := by rw [shr1'] at hlim; omega
      refine Out.bind (cChild_out mx lt endpos (2 * pos + 1) w hw hc) (fun cp w1 ⟨h1, h2, h3⟩ => ?_)
      rw [Eff.run_bind_ok (cItem_run (show cp < w1.heap.length by omega)),
        Eff.run_bind_ok (cItem_run (show pos < w1.heap.length by omega)),
        Eff.run_bind_ok (cStore_run (show cp < w1.heap.length by omega)),
        Eff.run_bind_ok (cStore_run (show pos < (w1.heap.set cp _).length by simp; omega))]
      exact ih cp _ (by simp; omega) h2 (by omega)
    · rw [if_neg hlim]
      exact ⟨hpos, hw⟩

theorem cSiftup_out (mx : Bool) (lt : Cmp σ α) (pos : Nat) (w : HW σ α)
    (hpos : pos < w.heap.length) :
    Out lt (fun _ w' => w'.heap.length = w.heap.length) ((cSiftup mx lt pos).run w) := by
  simp only [cSiftup, Eff.run_bind, cSize_run, if_neg (Nat.not_le.2 hpos)]
  have hl := cSiftupLoop_out mx lt w.heap.length (w.heap.length + 1) pos w rfl hpos (by omega)
  have := Out.bind (f := fun p => cSiftdown mx lt pos p) (Q := fun _ w' => w'.heap.length = w.heap.length)
    hl (fun p w1 ⟨h1, h2⟩ => by
      have := cSiftdown_out mx lt pos p w1 (by omega)
      rw [h2] at this; exact this)
  simpa only [Eff.run_bind] using this

end PyLean.Accel.Heapq
