import PyLean.Accel.HeapCorrect

/-!
Locality of `siftup` for an arbitrary comparison, and the canonical result of
any bottom-up heapify order: sifting every internal node once, each after its
internal children, yields `hcanon 0`.
-/

namespace PyLean.Accel

open PyLean

variable {α : Type} [Inhabited α]

/-- `l1` and `l2` agree on the subtree of `k`. -/
def AgreeOn (k : Nat) (l1 l2 : List α) : Prop := ∀ p, Desc k p → at! l1 p = at! l2 p

theorem agreeOn_set {k : Nat} {l1 l2 : List α} (hl : l1.length = l2.length) (h : AgreeOn k l1 l2)
    (p : Nat) (v : α) : AgreeOn k (l1.set p v) (l2.set p v) := by
  intro q hq
  rw [at!_set, at!_set, hl, h q hq]

theorem at!_set_out {l : List α} {k p q : Nat} (v : α) (hp : Desc k p) (hq : ¬ Desc k q) :
    at! (l.set p v) q = at! l q := at!_set_ne _ _ _ _ (fun e => hq (e ▸ hp))

theorem sdLoop_local (lt : α → α → Bool) (newitem : α) (s : Nat) :
    ∀ (fuel : Nat) (h1 h2 : List α) (pos : Nat), h1.length = h2.length → AgreeOn s h1 h2 →
      Desc s pos →
      (pySiftdownLoop lt newitem s fuel h1 pos).2 = (pySiftdownLoop lt newitem s fuel h2 pos).2 ∧
      AgreeOn s (pySiftdownLoop lt newitem s fuel h1 pos).1 (pySiftdownLoop lt newitem s fuel h2 pos).1 ∧
      Desc s (pySiftdownLoop lt newitem s fuel h1 pos).2 := by
  intro fuel
  induction fuel with
  | zero => intro h1 h2 pos _ ha hd; exact ⟨rfl, ha, hd⟩
  | succ fuel ih =>
    intro h1 h2 pos hl ha hd
    simp only [pySiftdownLoop]
    by_cases hgt : pos > s
    · rw [if_pos hgt, if_pos hgt]
      have hdp : Desc s ((pos - 1) >>> 1) := by rw [shr1]; exact hd.up (by omega)
      rw [ha _ hdp]
      by_cases hc : lt newitem (at! h2 ((pos - 1) >>> 1)) = true
      · rw [if_pos hc, if_pos hc]
        exact ih _ _ _ (by simp [hl]) (agreeOn_set hl ha _ _) hdp
      · rw [if_neg hc, if_neg hc]; exact ⟨rfl, ha, hd⟩
    · rw [if_neg hgt, if_neg hgt]; exact ⟨rfl, ha, hd⟩

theorem sdLoop_frame (lt : α → α → Bool) (newitem : α) (s : Nat) :
    ∀ (fuel : Nat) (h : List α) (pos : Nat), Desc s pos →
      Desc s (pySiftdownLoop lt newitem s fuel h pos).2 ∧
      ∀ q, ¬ Desc s q → at! (pySiftdownLoop lt newitem s fuel h pos).1 q = at! h q := by
  intro fuel
  induction fuel with
  | zero => intro h pos hd; exact ⟨hd, fun _ _ => rfl⟩
  | succ fuel ih =>
    intro h pos hd
    simp only [pySiftdownLoop]
    by_cases hgt : pos > s
    · rw [if_pos hgt]
      have hdp : Desc s ((pos - 1) >>> 1) := by rw [shr1]; exact hd.up (by omega)
      by_cases hc : lt newitem (at! h ((pos - 1) >>> 1)) = true
      · rw [if_pos hc]
        obtain ⟨r1, r2⟩ := ih (h.set pos (at! h ((pos - 1) >>> 1))) _ hdp
        exact ⟨r1, fun q hq => (r2 q hq).trans (at!_set_out _ hd hq)⟩
      · rw [if_neg hc]; exact ⟨hd, fun _ _ => rfl⟩
    · rw [if_neg hgt]; exact ⟨hd, fun _ _ => rfl⟩

theorem suLoop_local (lt : α → α → Bool) (endpos s : Nat) :
    ∀ (fuel : Nat) (h1 h2 : List α) (pos : Nat), h1.length = h2.length → AgreeOn s h1 h2 →
      Desc s pos →
      (pySiftupLoop lt endpos fuel h1 pos).2 = (pySiftupLoop lt endpos fuel h2 pos).2 ∧
      AgreeOn s (pySiftupLoop lt endpos fuel h1 pos).1 (pySiftupLoop lt endpos fuel h2 pos).1 ∧
      Desc s (pySiftupLoop lt endpos fuel h1 pos).2 := by
  intro fuel
  induction fuel with
  | zero => intro h1 h2 pos _ ha hd; exact ⟨rfl, ha, hd⟩
  | succ fuel ih =>
    intro h1 h2 pos hl ha hd
    simp only [pySiftupLoop]
    by_cases hc : 2 * pos + 1 < endpos
    · rw [if_pos hc, if_pos hc]
      have d1 : Desc s (2 * pos + 1) := Desc.left hd
      have d2 : Desc s (2 * pos + 1 + 1) := Desc.right hd
      rw [ha _ d1, ha _ d2]
      by_cases hr : (2 * pos + 1 + 1 < endpos ∧ (!lt (at! h2 (2 * pos + 1)) (at! h2 (2 * pos + 1 + 1))) = true)
      · rw [if_pos hr, ha _ d2]
        exact ih _ _ _ (by simp [hl]) (agreeOn_set hl ha _ _) d2
      · rw [if_neg hr, ha _ d1]
        exact ih _ _ _ (by simp [hl]) (agreeOn_set hl ha _ _) d1
    · rw [if_neg hc, if_neg hc]; exact ⟨rfl, ha, hd⟩

theorem suLoop_frame (lt : α → α → Bool) (endpos s : Nat) :
    ∀ (fuel : Nat) (h : List α) (pos : Nat), Desc s pos →
      Desc s (pySiftupLoop lt endpos fuel h pos).2 ∧
      ∀ q, ¬ Desc s q → at! (pySiftupLoop lt endpos fuel h pos).1 q = at! h q := by
  intro fuel
  induction fuel with
  | zero => intro h pos hd; exact ⟨hd, fun _ _ => rfl⟩
  | succ fuel ih =>
    intro h pos hd
    simp only [pySiftupLoop]
    by_cases hc : 2 * pos + 1 < endpos
    · rw [if_pos hc]
      have d1 : Desc s (2 * pos + 1) := Desc.left hd
      have d2 : Desc s (2 * pos + 1 + 1) := Desc.right hd
      by_cases hr : (2 * pos + 1 + 1 < endpos ∧ (!lt (at! h (2 * pos + 1)) (at! h (2 * pos + 1 + 1))) = true)
      · rw [if_pos hr]
        obtain ⟨r1, r2⟩ := ih _ _ d2
        exact ⟨r1, fun q hq => (r2 q hq).trans (at!_set_out _ hd hq)⟩
      · rw [if_neg hr]
        obtain ⟨r1, r2⟩ := ih _ _ d1
        exact ⟨r1, fun q hq => (r2 q hq).trans (at!_set_out _ hd hq)⟩
    · rw [if_neg hc]; exact ⟨hd, fun _ _ => rfl⟩

theorem pySiftdown_local (lt : α → α → Bool) (h1 h2 : List α) (s pos : Nat)
    (hl : h1.length = h2.length) (ha : AgreeOn s h1 h2) (hd : Desc s pos) :
    AgreeOn s (pySiftdown lt h1 s pos) (pySiftdown lt h2 s pos) := by
  simp only [pySiftdown]
  rw [ha pos hd]
  obtain ⟨e, a, -⟩ := sdLoop_local lt (at! h2 pos) s pos h1 h2 pos hl ha hd
  rw [e]
  exact agreeOn_set (by simp [pySiftdownLoop_length, hl]) a _ _

theorem pySiftdown_frame (lt : α → α → Bool) (h : List α) (s pos : Nat) (hd : Desc s pos) :
    ∀ q, ¬ Desc s q → at! (pySiftdown lt h s pos) q = at! h q := by
  intro q hq
  simp only [pySiftdown]
  obtain ⟨d, f⟩ := sdLoop_frame lt (at! h pos) s pos h pos hd
  rw [at!_set_out _ d hq, f q hq]

theorem pySiftup_local (lt : α → α → Bool) (h1 h2 : List α) (k : Nat)
    (hl : h1.length = h2.length) (ha : AgreeOn k h1 h2) :
    AgreeOn k (pySiftup lt h1 k) (pySiftup lt h2 k) := by
  simp only [pySiftup]
  rw [hl, ha k Desc.refl]
  obtain ⟨e, a, d⟩ := suLoop_local lt h2.length k h2.length h1 h2 k hl ha Desc.refl
  rw [e]
  rw [e] at d
  exact pySiftdown_local lt _ _ k _ (by simp [pySiftupLoop_length, hl]) (agreeOn_set
    (by simp [pySiftupLoop_length, hl]) a _ _) d

theorem pySiftup_frame (lt : α → α → Bool) (h : List α) (k : Nat) :
    ∀ q, ¬ Desc k q → at! (pySiftup lt h k) q = at! h q := by
  intro q hq
  simp only [pySiftup]
  obtain ⟨d, f⟩ := suLoop_frame lt h.length k h.length h k Desc.refl
  rw [pySiftdown_frame lt _ k _ d q hq, at!_set_out _ d hq, f q hq]

end PyLean.Accel
