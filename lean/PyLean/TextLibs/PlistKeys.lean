import PyLean.TextLibs.PlistLayout

/-! The keys `_flatten` and `_write_object` keep of a dict: its `str` keys, in the order written,
pairwise different when the dict's are. -/

namespace PyLean.TextLibs.Plist

open PyLean PyLean.TextLibs

def isStrKey (H : WHeap) (q : Nat × Nat) : Bool := (keyStr H q.1).isSome

theorem keptItems_filter (H : WHeap) (skip : Bool) :
    ∀ (its kept : List (Nat × Nat)), keptItems H skip its = .ok kept → kept = its.filter (isStrKey H)
  | [], kept, h => by simp [keptItems] at h; subst h; rfl
  | (k, v) :: its, kept, h => by
    simp only [keptItems] at h
    by_cases hk : (keyStr H k).isNone = true
    · rw [if_pos hk] at h
      split at h
      · have := keptItems_filter H skip its kept h
        rw [this, List.filter_cons]
        simp [isStrKey, Option.isNone_iff_eq_none.mp hk]
      · cases h
    · rw [if_neg hk] at h
      simp only [bind, Except.bind] at h
      cases hr : keptItems H skip its with
      | error e => rw [hr] at h; cases h
      | ok rest =>
        rw [hr] at h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h
        rw [keptItems_filter H skip its rest hr, List.filter_cons]
        have : (keyStr H k).isSome = true := by
          cases hh : keyStr H k <;> simp_all
        simp [isStrKey, this]

theorem dictItems_perm (H : WHeap) (cfg : WCfg) (items its : List (Nat × Nat))
    (h : dictItems H cfg items = .ok its) : ∃ l, l.Sublist items ∧ its.Perm l := by
  unfold dictItems at h
  split at h
  · split at h
    · cases h
      exact ⟨_, List.filter_sublist, List.mergeSort_perm _ _⟩
    · split at h
      · cases h
      · cases h
        exact ⟨items, List.Sublist.refl _, List.mergeSort_perm _ _⟩
  · cases h
    exact ⟨items, List.Sublist.refl _, List.Perm.refl _⟩

/-- `str` keys of a dict are pairwise different strings (the type invariant of a dict). -/
def KeysDistinct (H : WHeap) (items : List (Nat × Nat)) : Prop :=
  ((items.filter (isStrKey H)).map fun q => keyStr H q.1).Pairwise (· ≠ ·)

theorem written_keys (H : WHeap) (cfg : WCfg) (items kept : List (Nat × Nat))
    (hd : KeysDistinct H items) (h : writtenItems H cfg items = .ok kept) :
    (∀ q ∈ kept, (keyStr H q.1).isSome = true) ∧ (kept.map fun q => keyStr H q.1).Pairwise (· ≠ ·) := by
  simp only [writtenItems, bind, Except.bind] at h
  cases hi : dictItems H cfg items with
  | error e => rw [hi] at h; cases h
  | ok its =>
    rw [hi] at h
    simp only at h
    have hk := keptItems_filter H cfg.skipkeys its kept h
    subst hk
    obtain ⟨l, hl, hp⟩ := dictItems_perm H cfg items its hi
    refine ⟨fun q hq => by simpa [isStrKey] using (List.mem_filter.mp hq).2, ?_⟩
    have h1 : ((l.filter (isStrKey H)).map fun q => keyStr H q.1).Pairwise (· ≠ ·) :=
      List.Pairwise.sublist ((hl.filter _).map _) hd
    exact ((hp.filter _).map _).pairwise_iff (fun h e => h e.symm) |>.mpr h1

end PyLean.TextLibs.Plist
