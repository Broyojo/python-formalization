import PyLean.Accel.HeapqMergeProps
import PyLean.Accel.HeapqStable

/-!
Tools for the `merge` sortedness proof: `merge`'s heap holds entry references (indices into
the entry store), so the pure heap functions run on index lists with the comparison read
through the store. These lemmas relabel index lists to entry lists. The relabelling has no
default to preserve, so the lemmas track that every access is in range.
-/

namespace PyLean.Accel.Heapq

open PyLean

variable {β γ : Type} [Inhabited β] [Inhabited γ]

theorem at!_map_lt (φ : β → γ) (l : List β) (i : Nat) (h : i < l.length) :
    Accel.at! (l.map φ) i = φ (Accel.at! l i) := by
  simp [Accel.at!, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
    List.getElem?_eq_getElem (show i < (l.map φ).length by simpa using h)]

variable (φ : β → γ) (lt' : γ → γ → Bool)

theorem pySiftdownLoop_mapR (x : β) (s : Nat) :
    ∀ (fuel : Nat) (l : List β) (pos : Nat), pos < l.length →
      Accel.pySiftdownLoop lt' (φ x) s fuel (l.map φ) pos =
        ((Accel.pySiftdownLoop (fun a b => lt' (φ a) (φ b)) x s fuel l pos).1.map φ,
          (Accel.pySiftdownLoop (fun a b => lt' (φ a) (φ b)) x s fuel l pos).2) := by
  intro fuel
  induction fuel with
  | zero => intro l pos _; rfl
  | succ fuel ih =>
    intro l pos hpos
    simp only [Accel.pySiftdownLoop]
    split
    · rename_i hgt
      have hpp : (pos - 1) >>> 1 < l.length := by rw [shr1']; omega
      rw [at!_map_lt φ l _ hpp]
      split
      · rw [← List.map_set, ih _ _ (by simp; rw [shr1']; omega)]
      · rfl
    · rfl

theorem pySiftdownLoop_lt (lt : β → β → Bool) (x : β) (s : Nat) :
    ∀ (fuel : Nat) (l : List β) (pos : Nat), (Accel.pySiftdownLoop lt x s fuel l pos).2 ≤ pos := by
  intro fuel
  induction fuel with
  | zero => intro l pos; exact Nat.le_refl _
  | succ fuel ih =>
    intro l pos
    simp only [Accel.pySiftdownLoop]
    split
    · split
      · have := ih (l.set pos (Accel.at! l ((pos - 1) >>> 1))) ((pos - 1) >>> 1)
        rw [shr1'] at this ⊢; omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem pySiftdown_mapR (l : List β) (s pos : Nat) (h : pos < l.length) :
    Accel.pySiftdown lt' (l.map φ) s pos = (Accel.pySiftdown (fun a b => lt' (φ a) (φ b)) l s pos).map φ := by
  simp only [Accel.pySiftdown]
  rw [at!_map_lt φ l pos h, pySiftdownLoop_mapR φ lt' _ s pos l pos h, List.map_set]

theorem pySiftupLoop_mapR (endpos : Nat) :
    ∀ (fuel : Nat) (l : List β) (pos : Nat), l.length = endpos →
      Accel.pySiftupLoop lt' endpos fuel (l.map φ) pos =
        ((Accel.pySiftupLoop (fun a b => lt' (φ a) (φ b)) endpos fuel l pos).1.map φ,
          (Accel.pySiftupLoop (fun a b => lt' (φ a) (φ b)) endpos fuel l pos).2) := by
  intro fuel
  induction fuel with
  | zero => intro l pos _; rfl
  | succ fuel ih =>
    intro l pos hl
    simp only [Accel.pySiftupLoop]
    split
    · rename_i hc
      have hcp : (if 2 * pos + 1 + 1 < endpos ∧ (!lt' (Accel.at! (l.map φ) (2 * pos + 1))
            (Accel.at! (l.map φ) (2 * pos + 1 + 1))) = true then 2 * pos + 1 + 1 else 2 * pos + 1) =
          (if 2 * pos + 1 + 1 < endpos ∧ (!(fun a b => lt' (φ a) (φ b)) (Accel.at! l (2 * pos + 1))
            (Accel.at! l (2 * pos + 1 + 1))) = true then 2 * pos + 1 + 1 else 2 * pos + 1) := by
        by_cases hr : 2 * pos + 1 + 1 < endpos
        · rw [at!_map_lt φ l _ (by omega), at!_map_lt φ l _ (by omega)]
        · simp [hr]
      rw [hcp]
      generalize hc' : (if 2 * pos + 1 + 1 < endpos ∧ (!(fun a b => lt' (φ a) (φ b)) (Accel.at! l (2 * pos + 1))
            (Accel.at! l (2 * pos + 1 + 1))) = true then 2 * pos + 1 + 1 else 2 * pos + 1) = c
      have hclt : c < endpos := by rw [← hc']; split <;> omega
      rw [at!_map_lt φ l c (by omega), ← List.map_set, ih _ _ (by simp; omega)]
    · rfl

theorem pySiftup_mapR (l : List β) (pos : Nat) (h : pos < l.length) :
    Accel.pySiftup lt' (l.map φ) pos = (Accel.pySiftup (fun a b => lt' (φ a) (φ b)) l pos).map φ := by
  simp only [Accel.pySiftup, List.length_map]
  rw [at!_map_lt φ l pos h, pySiftupLoop_mapR φ lt' l.length l.length l pos rfl, ← List.map_set]
  have hlt := (Accel.siftupLoop_twins (fun a b => lt' (φ a) (φ b)) (Accel.at! l pos) l.length l.length l pos h rfl).2.1
  rw [pySiftdown_mapR φ lt' _ pos _ (by simp [Accel.pySiftupLoop_length]; exact hlt)]

/-! ### The pure heap functions permute, for any comparison -/

theorem cSiftdownLoop_perm (lt : β → β → Bool) (x : β) (s : Nat) :
    ∀ (fuel : Nat) (arr : List β) (pos : Nat), pos < arr.length →
      (Accel.cSiftdownLoop lt x s fuel arr pos).Perm arr := by
  intro fuel
  induction fuel with
  | zero => intro arr pos _; exact List.Perm.refl _
  | succ fuel ih =>
    intro arr pos hpos
    simp only [Accel.cSiftdownLoop]
    split
    · split
      · have hpp : (pos - 1) >>> 1 < pos := by rw [shr1']; omega
        have hsw : (arr.set ((pos - 1) >>> 1) (Accel.at! arr pos)).set pos (Accel.at! arr ((pos - 1) >>> 1)) =
            Accel.sw arr ((pos - 1) >>> 1) pos := rfl
        rw [hsw]
        exact (ih _ _ (by rw [Accel.sw_length]; omega)).trans (Accel.sw_perm arr _ _ (by omega) hpos)
      · exact List.Perm.refl _
    · exact List.Perm.refl _

theorem cSiftupLoop_perm (lt : β → β → Bool) (endpos : Nat) :
    ∀ (fuel : Nat) (arr : List β) (pos : Nat), arr.length = endpos → pos < endpos →
      (Accel.cSiftupLoop lt endpos (endpos >>> 1) fuel arr pos).1.Perm arr ∧
        (Accel.cSiftupLoop lt endpos (endpos >>> 1) fuel arr pos).2 < endpos := by
  intro fuel
  induction fuel with
  | zero => intro arr pos _ hpos; exact ⟨List.Perm.refl _, hpos⟩
  | succ fuel ih =>
    intro arr pos hl hpos
    simp only [Accel.cSiftupLoop]
    split
    · rename_i hlim
      have hc : 2 * pos + 1 < endpos := by rw [shr1'] at hlim; omega
      generalize hcp : (if 2 * pos + 1 + 1 < endpos then
          (if lt (Accel.at! arr (2 * pos + 1)) (Accel.at! arr (2 * pos + 1 + 1)) = true then 2 * pos + 1
            else 2 * pos + 1 + 1) else 2 * pos + 1) = cp
      have hcp' : cp < endpos ∧ pos < cp := by rw [← hcp]; split <;> (try split) <;> omega
      have hsw : (arr.set cp (Accel.at! arr pos)).set pos (Accel.at! arr cp) = Accel.sw arr cp pos := rfl
      rw [hsw]
      obtain ⟨h1, h2⟩ := ih (Accel.sw arr cp pos) cp (by rw [Accel.sw_length]; exact hl) hcp'.1
      exact ⟨h1.trans (Accel.sw_perm arr cp pos (by omega) (by omega)), h2⟩
    · exact ⟨List.Perm.refl _, hpos⟩

theorem pySiftup_perm (lt : β → β → Bool) (l : List β) (pos : Nat) (h : pos < l.length) :
    (Accel.pySiftup lt l pos).Perm l := by
  have hc := Accel.cSiftup_eq lt l pos h
  simp only [Accel.cSiftup, if_neg (Nat.not_le.2 h)] at hc
  obtain ⟨h1, h2⟩ := cSiftupLoop_perm lt l.length l.length l pos rfl h
  rw [Accel.cSiftdown, if_neg (Nat.not_le.2 (by rw [h1.length_eq]; exact h2))] at hc
  rw [← Except.ok.inj hc]
  exact (cSiftdownLoop_perm lt _ _ _ _ _ (by rw [h1.length_eq]; exact h2)).trans h1

theorem pyHeappop_mapR (l : List β) (hne : l ≠ []) :
    Accel.pyHeappop lt' (l.map φ) =
      (Accel.pyHeappop (fun a b => lt' (φ a) (φ b)) l).map (fun p => (φ p.1, p.2.map φ)) := by
  obtain ⟨d, last, rfl⟩ : ∃ d last, l = d ++ [last] :=
    ⟨l.dropLast, l.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  simp only [Accel.pyHeappop, List.map_append, List.map_cons, List.map_nil, List.getLast?_append,
    List.getLast?_singleton, Option.some_or, List.dropLast_concat]
  cases d with
  | nil => rfl
  | cons d0 dt =>
    simp only [List.map_cons, ne_eq, reduceCtorEq, not_false_eq_true, if_true]
    rw [← List.map_cons, at!_map_lt φ (d0 :: dt) 0 (by simp), ← List.map_set,
      pySiftup_mapR φ lt' _ 0 (by simp)]
    rfl

theorem pyHeapify_mapR (l : List β) :
    Accel.pyHeapify lt' (l.map φ) = (Accel.pyHeapify (fun a b => lt' (φ a) (φ b)) l).map φ := by
  simp only [Accel.pyHeapify, List.length_map]
  have : ∀ (is : List Nat) (m : List β), m.length = l.length → (∀ i ∈ is, i < l.length) →
      is.foldl (fun h i => Accel.pySiftup lt' h i) (m.map φ) =
        (is.foldl (fun h i => Accel.pySiftup (fun a b => lt' (φ a) (φ b)) h i) m).map φ := by
    intro is
    induction is with
    | nil => intro m _ _; rfl
    | cons i is ih =>
      intro m hm hi
      simp only [List.foldl_cons]
      rw [pySiftup_mapR φ lt' m i (by rw [hm]; exact hi i (by simp))]
      exact ih _ (by rw [Accel.pySiftup_length, hm]) (fun j hj => hi j (by simp [hj]))
  exact this _ l rfl (fun i hi => by simp at hi; omega)

end PyLean.Accel.Heapq
