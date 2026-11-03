import PyLean.Accel.HeapqTwinsPub
import PyLean.Accel.HeapProps

/-!
With an honest comparison (`pureCmp r`: a pure Boolean, no exception, no effect) the effectful
models compute what the pure models of `Heap.lean` compute, so the correctness theorems of
`HeapProps.lean` / `HeapifyTwins.lean` (proven there for any strict weak order) apply to them.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {σ α : Type} [Inhabited α]

/-- The order a heap is kept in: `r` for the min-heap functions, `r` with swapped operands
(`maxLt r`) for the `*_max` functions. -/
def heapOrd (mx : Bool) (r : α → α → Bool) : α → α → Bool := if mx then Accel.maxLt r else r

theorem pyLtOrd_pure (mx : Bool) (r : α → α → Bool) (x y : α) (w : HW σ α) :
    (pyLtOrd (pureCmp r) mx x y).run w = (.ok (heapOrd mx r x y), w) := by
  cases mx <;> rfl

/-! ### Python twin -/

theorem pySdLoop_pure (mx : Bool) (r : α → α → Bool) (s0 : Nat) (newitem : α) :
    ∀ (fnew fold pos : Nat) (heap : List α) (st : σ), pos < heap.length → pos ≤ fold →
      pos < fnew →
      ((pySiftdownLoop listSeq (pureCmp r) mx (s0 : Int) newitem fnew (pos : Int)) >>= fun p =>
          listSeq.set p newitem).run ⟨st, heap⟩ =
        (.ok (), ⟨st, (Accel.pySiftdownLoop (heapOrd mx r) newitem s0 fold heap pos).1.set
          (Accel.pySiftdownLoop (heapOrd mx r) newitem s0 fold heap pos).2 newitem⟩) ∧
      (Accel.pySiftdownLoop (heapOrd mx r) newitem s0 fold heap pos).2 ≤ pos := by
  intro fnew
  induction fnew with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ fnew ih =>
    intro fold pos heap st hpos hfold hf
    simp only [pySiftdownLoop]
    by_cases hgt : pos > s0
    · have hgt' : (pos : Int) > (s0 : Int) := by omega
      obtain ⟨fold, rfl⟩ : ∃ k, fold = k + 1 := ⟨fold - 1, by omega⟩
      simp only [Accel.pySiftdownLoop]
      rw [if_pos hgt, if_pos hgt', pp_int pos (by omega)]
      have hpp : (pos - 1) >>> 1 < pos := by rw [shr1']; omega
      simp only [Eff.bind_assoc]
      rw [Eff.run_bind_ok (listGet_run _ _ rfl (show (pos - 1) >>> 1 < heap.length by omega)),
        Eff.run_bind_ok (pyLtOrd_pure _ _ _ _ _)]
      cases hc : heapOrd mx r newitem (at! heap ((pos - 1) >>> 1))
      · simp only [Bool.false_eq_true, ↓reduceIte, Eff.run_pure, Eff.pure_bind]
        rw [listSet_run _ pos rfl _ hpos]
        exact ⟨rfl, Nat.le_refl _⟩
      · simp only [↓reduceIte, Eff.bind_assoc]
        rw [Eff.run_bind_ok (listSet_run _ pos rfl _ hpos)]
        obtain ⟨h1, h2⟩ := ih fold ((pos - 1) >>> 1) (heap.set pos (at! heap ((pos - 1) >>> 1))) st
          (by simp; omega) (by omega) (by omega)
        exact ⟨h1, by omega⟩
    · have hgt' : ¬ (pos : Int) > (s0 : Int) := by omega
      rw [if_neg hgt', Eff.pure_bind, listSet_run _ pos rfl _ hpos]
      cases fold with
      | zero => exact ⟨rfl, Nat.le_refl _⟩
      | succ fold =>
        simp [Accel.pySiftdownLoop, hgt]

theorem pySiftdown_pure (mx : Bool) (r : α → α → Bool) (si pi : Int) (s0 pos : Nat)
    (hs : si = (s0 : Int)) (hp : pi = (pos : Int)) (w : HW σ α) (h : pos < w.heap.length) :
    (pySiftdown listSeq (pureCmp r) mx si pi).run w =
      (.ok (), { w with heap := Accel.pySiftdown (heapOrd mx r) w.heap s0 pos }) := by
  subst hs hp
  simp only [pySiftdown]
  rw [Eff.run_bind_ok (listGet_run _ pos rfl h), Int.toNat_natCast]
  exact (pySdLoop_pure mx r s0 (at! w.heap pos) (pos + 1) pos pos w.heap w.st h (Nat.le_refl _)
    (by omega)).1

theorem pyTakeRight_pure (mx : Bool) (r : α → α → Bool) (endpos cp : Nat) (heap : List α) (st : σ)
    (hlen : heap.length = endpos) (hcp : cp < endpos) :
    (pyTakeRight listSeq (pureCmp r) mx endpos (cp : Int) ((cp : Int) + 1)).run ⟨st, heap⟩ =
      (.ok (decide (cp + 1 < endpos ∧ (!heapOrd mx r (at! heap cp) (at! heap (cp + 1))) = true)),
        ⟨st, heap⟩) := by
  unfold pyTakeRight
  by_cases hr : cp + 1 < endpos
  · have hr' : (cp : Int) + 1 < (endpos : Int) := by omega
    rw [if_pos hr', show ((cp : Int) + 1) = ((cp + 1 : Nat) : Int) by omega]
    cases mx
    · simp only [pyChildLt, Bool.false_eq_true, ↓reduceIte, Eff.bind_assoc]
      rw [Eff.run_bind_ok (listGet_run _ cp rfl (show cp < heap.length by omega)),
        Eff.run_bind_ok (listGet_run _ (cp + 1) rfl (show cp + 1 < heap.length by omega))]
      simp [pureCmp, ofSt, heapOrd, hr]
    · simp only [pyChildLt, ↓reduceIte, Eff.bind_assoc]
      rw [Eff.run_bind_ok (listGet_run _ (cp + 1) rfl (show cp + 1 < heap.length by omega)),
        Eff.run_bind_ok (listGet_run _ cp rfl (show cp < heap.length by omega))]
      simp [pureCmp, ofSt, heapOrd, Accel.maxLt, hr]
  · have hr' : ¬ (cp : Int) + 1 < (endpos : Int) := by omega
    rw [if_neg hr']
    simp [hr]

theorem pySuLoop_pure (mx : Bool) (r : α → α → Bool) (endpos : Nat) :
    ∀ (fnew fold pos : Nat) (heap : List α) (st : σ), heap.length = endpos → pos < endpos →
      endpos - pos ≤ fold → endpos - pos < fnew →
      (pySiftupLoop listSeq (pureCmp r) mx endpos fnew (pos : Int)).run ⟨st, heap⟩ =
        (.ok ((Accel.pySiftupLoop (heapOrd mx r) endpos fold heap pos).2 : Int),
          ⟨st, (Accel.pySiftupLoop (heapOrd mx r) endpos fold heap pos).1⟩) ∧
      (Accel.pySiftupLoop (heapOrd mx r) endpos fold heap pos).2 < endpos := by
  intro fnew
  induction fnew with
  | zero => intro _ _ _ _ _ _ _ h; omega
  | succ fnew ih =>
    intro fold pos heap st hlen hpos hfold hf
    obtain ⟨fold, rfl⟩ : ∃ k, fold = k + 1 := ⟨fold - 1, by omega⟩
    simp only [pySiftupLoop, Accel.pySiftupLoop]
    by_cases hc : 2 * pos + 1 < endpos
    · have hc' : 2 * (pos : Int) + 1 < (endpos : Int) := by omega
      rw [if_pos hc', if_pos hc, show 2 * (pos : Int) + 1 = ((2 * pos + 1 : Nat) : Int) by omega,
        Eff.run_bind_ok (pyTakeRight_pure mx r endpos (2 * pos + 1) heap st hlen hc)]
      by_cases hb : 2 * pos + 1 + 1 < endpos ∧
          (!heapOrd mx r (at! heap (2 * pos + 1)) (at! heap (2 * pos + 1 + 1))) = true
      · simp only [decide_eq_true hb, ↓reduceIte, if_pos hb]
        rw [show ((2 * pos + 1 : Nat) : Int) + 1 = ((2 * pos + 1 + 1 : Nat) : Int) by omega,
          Eff.run_bind_ok (listGet_run _ (2 * pos + 1 + 1) rfl (show 2 * pos + 1 + 1 < heap.length by
            omega)),
          Eff.run_bind_ok (listSet_run _ pos rfl _ (show pos < heap.length by omega))]
        exact ih fold _ _ st (by simp; omega) hb.1 (by omega) (by omega)
      · simp only [decide_eq_false hb, Bool.false_eq_true, ↓reduceIte, if_neg hb]
        rw [Eff.run_bind_ok (listGet_run _ (2 * pos + 1) rfl (show 2 * pos + 1 < heap.length by
            omega)),
          Eff.run_bind_ok (listSet_run _ pos rfl _ (show pos < heap.length by omega))]
        exact ih fold _ _ st (by simp; omega) hc (by omega) (by omega)
    · have hc' : ¬ 2 * (pos : Int) + 1 < (endpos : Int) := by omega
      rw [if_neg hc', if_neg hc]
      exact ⟨rfl, hpos⟩

theorem pySiftup_pure (mx : Bool) (r : α → α → Bool) (pi : Int) (pos : Nat) (hp : pi = (pos : Int))
    (w : HW σ α) (h : pos < w.heap.length) :
    (pySiftup listSeq (pureCmp r) mx pi).run w =
      (.ok (), { w with heap := Accel.pySiftup (heapOrd mx r) w.heap pos }) := by
  subst hp
  simp only [pySiftup]
  rw [Eff.run_bind_ok (listLen_run w), Eff.run_bind_ok (listGet_run _ pos rfl h)]
  obtain ⟨h1, h2⟩ := pySuLoop_pure mx r w.heap.length (w.heap.length + 1) w.heap.length pos w.heap
    w.st rfl h (by omega) (by omega)
  rw [Eff.run_bind_ok h1]
  have hl := Accel.pySiftupLoop_length (heapOrd mx r) w.heap.length w.heap.length w.heap pos
  rw [Eff.run_bind_ok (listSet_run _ _ rfl _ (show _ < _ by simp only; omega)),
    pySiftdown_pure mx r _ _ pos _ rfl rfl _ (by simp; omega)]
  rfl

/-! ### C siftup -/

theorem cSiftup_pure (mx : Bool) (r : α → α → Bool) (pos : Nat) (w : HW σ α)
    (h : pos < w.heap.length) :
    (cSiftup mx (pureCmp r) pos).run w =
      (.ok (), { w with heap := Accel.pySiftup (heapOrd mx r) w.heap pos }) := by
  have hs := siftup_sim mx (fun a b s => (.ok (r a b), s)) pos w h
  have hp := pySiftup_pure (σ := σ) mx r _ pos rfl w h
  change Rel ((cSiftup mx (pureCmp r) pos).run w) ((pySiftup listSeq (pureCmp r) mx (pos : Int)).run w) at hs
  rw [hp] at hs
  rcases hc : (cSiftup mx (pureCmp r) pos).run w with ⟨rc, wc⟩
  rw [hc] at hs
  cases rc with
  | ok u => obtain ⟨-, rfl⟩ := hs; rfl
  | error e => cases e <;> exact hs.elim

end PyLean.Accel.Heapq
