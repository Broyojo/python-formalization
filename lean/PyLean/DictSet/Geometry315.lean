import PyLean.DictSet.Body

/-!
The table sizes that `sys.getsizeof` and the timing of the next resize show: what
`new_keys_object`, `insert_to_emptydict`, `insertion_resize` and `insert_combined_dict` build
(CPython 3.15.2, `Objects/dictobject.c`).
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type}

/-- What a successful `dictresize` leaves: a combined table of the size asked, `USABLE_FRACTION`
of it minus the entries moved over, and the same number of items. -/
theorem dictResize_ok [DecidableEq K] {mp s : PyDict K V} {l : Nat} {u : Bool} (h : dictResize l u mp = (.ok (), s)) :
    ∃ k', s.body = .combined k' ∧ k'.log2Size = l ∧
      k'.usable = (usableFraction (2 ^ l) : Int) - mp.used ∧ s.used = mp.used ∧
      k'.kind = (if (if mp.body.isUnicode then u else false) then .unicode else .general) := by
  have hk := fun k' hs => dictResize_kind (k' := k') h hs
  unfold dictResize at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · simp at h
    · have h1 := congrArg Prod.snd h
      simp only at h1
      rw [← h1]
      refine ⟨_, rfl, by simp [newKeysObject], by simp [newKeysObject], rfl, ?_⟩
      exact hk _ (by rw [← h1])

/-- The geometry, for every key protocol: `new_keys_object` gives `2**l` empty slots, no entry,
`USABLE_FRACTION(2**l)` usable, unicode as asked; `insert_to_emptydict` gives the 8-slot table, unicode
exactly for an exact `str` key, with 4 usable left and the one entry; `insertion_resize` gives a
table of `calculate_log2_keysize(GROWTH_RATE(used))` with `USABLE_FRACTION` of it less `used` usable;
`insert_combined_dict` on a table with room, and no non-`str` key for a unicode table, keeps the size
and kind and appends with one usable fewer, while on a table with no room it first takes the
`insertion_resize` size. -/
def TableGeometry : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (KO : KeyOps K) (id l : Nat) (u : Bool)
    (key : K) (hash : Int) (value : V) (mp s : PyDict K V),
    ((newKeysObject id l u : Keys K V).log2Size = l ∧
      (newKeysObject id l u : Keys K V).indices = List.replicate (2 ^ l) DKIX_EMPTY ∧
      (newKeysObject id l u : Keys K V).entries = [] ∧
      (newKeysObject id l u : Keys K V).usable = usableFraction (2 ^ l) ∧
      (newKeysObject id l u : Keys K V).kind = (if u then .unicode else .general)) ∧
    (insertToEmptyDict P key hash value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = 3 ∧ k'.usable = 4 ∧
        k'.kind = (if P.isStr key then .unicode else .general) ∧
        k'.entries = [some ⟨key, hash, value⟩] ∧ s.used = mp.used + 1) ∧
    (insertionResize u mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = calculateLog2Keysize (growthRate mp.used) ∧
        k'.usable = (usableFraction (2 ^ calculateLog2Keysize (growthRate mp.used)) : Int) - mp.used) ∧
    (∀ k, mp.body = .combined k → (k.kind != .general && !KO.isStr key) = false → 0 < k.usable →
      insertCombinedDict KO hash key value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = k.log2Size ∧ k'.kind = k.kind ∧
        k'.usable = k.usable - 1 ∧ k'.entries = k.entries ++ [some ⟨key, hash, value⟩]) ∧
    (∀ k, mp.body = .combined k → (k.kind != .general && !KO.isStr key) = false → k.usable ≤ 0 →
      insertCombinedDict KO hash key value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = calculateLog2Keysize (growthRate mp.used))

theorem tableGeometry_proven : TableGeometry := by
  intro K V _ P KO id l u key hash value mp s
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, fun h => ?_, fun h => ?_, fun k hb hs hu h => ?_,
    fun k hb hs hu h => ?_⟩
  · simp only [insertToEmptyDict, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · simp [newKeysObject, usableFraction, PyDict_LOG_MINSIZE]
    · cases P.isStr key <;> rfl
  · obtain ⟨k', h1, h2, h3, _, _⟩ := dictResize_ok h
    exact ⟨k', h1, h2, h3⟩
  · have hu' : ¬ (k.usable ≤ 0) := by omega
    simp only [insertCombinedDict, Body.isUnicode, Body.kind, hb, hs, Bool.false_eq_true, if_false,
      Body.usable, hu'] at h
    split at h
    · rename_i k' hk
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      simp only [appendEntry] at hk
      split at hk
      · simp only [Except.ok.injEq] at hk
        subst hk
        exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
      · simp at hk
    · simp at h
  · simp only [insertCombinedDict, Body.isUnicode, Body.kind, hb, hs, Bool.false_eq_true, if_false,
      Body.usable, hu, if_true] at h
    split at h
    · simp at h
    · rename_i a mp2 hr
      obtain ⟨k2, hk2, hl2, _, _, _⟩ := dictResize_ok (by simpa [insertionResize] using hr)
      rw [hk2] at h
      simp only at h
      split at h
      · rename_i k' hk
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        simp only [appendEntry] at hk
        split at hk
        · simp only [Except.ok.injEq] at hk
          subst hk
          exact ⟨_, rfl, hl2⟩
        · simp at hk
      · simp at h

end PyLean.DictSet
