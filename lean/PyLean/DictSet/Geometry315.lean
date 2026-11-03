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

/-- The tail of `insert_combined_dict` (:1886-1906): the entry goes at the end, one usable fewer,
same size and kind. -/
theorem appendEntry_ok {k k' : Keys K V} {key : K} {hash : Int} {value : V}
    (h : appendEntry k key hash value = .ok k') :
    k'.log2Size = k.log2Size ∧ k'.kind = k.kind ∧ k'.usable = k.usable - 1 ∧
      k'.entries = k.entries ++ [some ⟨key, hash, value⟩] := by
  simp only [appendEntry] at h
  split at h
  · simp only [Except.ok.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · simp at h

/-- After the first test of `insert_combined_dict`: the second test (:1879-1884) and the tail, on a
dict `mp1` whose table is combined. -/
theorem icd_rest [DecidableEq K] {mp1 s : PyDict K V} {k1 : Keys K V} {key : K} {hash : Int}
    {value : V} (hb : mp1.body = .combined k1)
    (h : (match (if mp1.body.usable ≤ 0 then insertionResize true mp1 else (.ok (), mp1)) with
      | (.error e, s) => (.error e, s)
      | (.ok _, mp2) =>
        match mp2.body with
        | .combined k =>
          match appendEntry k key hash value with
          | .ok k' => (.ok (), { mp2 with body := .combined k' })
          | .error e => (.error e, mp2)
        | .split _ _ => (.error .modelFuel, mp2) : Py Unit × PyDict K V) = (.ok (), s)) :
    ∃ k', s.body = .combined k' ∧ k'.entries.getLast? = some (some ⟨key, hash, value⟩) ∧
      (k1.usable ≤ 0 → k'.log2Size = calculateLog2Keysize (growthRate mp1.used) ∧
        k'.kind = (if k1.kind != .general then .unicode else .general)) ∧
      (¬ k1.usable ≤ 0 → k'.log2Size = k1.log2Size ∧ k'.usable = k1.usable - 1 ∧ k'.kind = k1.kind ∧
        k'.entries = k1.entries ++ [some ⟨key, hash, value⟩]) := by
  have hu1 : mp1.body.usable = k1.usable := by simp [Body.usable, hb]
  have hU : mp1.body.isUnicode = (k1.kind != .general) := by simp [Body.isUnicode, Body.kind, hb]
  by_cases hu : k1.usable ≤ 0
  · rw [hu1, if_pos hu] at h
    split at h
    · simp at h
    · rename_i a mp2 hr
      obtain ⟨k2, hk2, hl2, _, _, hkind⟩ := dictResize_ok (by simpa [insertionResize] using hr)
      rw [hk2] at h
      simp only at h
      split at h
      · rename_i k' hk
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨a1, a2, _, a4⟩ := appendEntry_ok hk
        refine ⟨k', rfl, by simp [a4], fun _ => ⟨by rw [a1, hl2], ?_⟩, fun h' => absurd hu h'⟩
        rw [a2, hkind, hU]
        cases (k1.kind != .general) <;> rfl
      · simp at h
  · rw [hu1, if_neg hu] at h
    simp only [hb] at h
    split at h
    · rename_i k' hk
      simp only [Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨a1, a2, a3, a4⟩ := appendEntry_ok hk
      exact ⟨k', rfl, by simp [a4], fun h' => absurd h' hu, fun _ => ⟨a1, a3, a2, a4⟩⟩
    · simp at h

/-- `new_keys_object`'s choice of index width (:803-816), `log2_bytes`: one byte per slot below 256
slots, two below 65536, eight from 2**32, four otherwise. -/
theorem log2IndexBytes_eq (l : Nat) :
    log2IndexBytes l =
      (if l < 8 then l else if l < 16 then l + 1 else if 32 ≤ l then l + 3 else l + 2) := by
  simp only [log2IndexBytes, ge_iff_le]

/-- The geometry, for every key protocol. `new_keys_object` gives `2**l` empty slots, no entry,
`USABLE_FRACTION(2**l)` usable, the kind asked, and indices of 1, 2, 4 or 8 bytes by the size, which
is the `__sizeof__` of the table. `insert_to_emptydict` gives the 8-slot table, unicode exactly for
an exact `str` key, with 4 usable left and the one entry. `insertion_resize` gives a table of
`calculate_log2_keysize(GROWTH_RATE(used))`, with `USABLE_FRACTION` of it less `used` usable, unicode
exactly when the dict was and the caller allows it. `insert_combined_dict`: with a non-`str` key into
a unicode table (split ones included) the result is a general table; otherwise, with room it keeps the
size and kind and appends with one usable fewer, and with no room it first takes the
`insertion_resize` size, unicode exactly when the table was; in every case the entry is the last. -/
def TableGeometry : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (KO : KeyOps K) (id l : Nat) (u : Bool)
    (key : K) (hash : Int) (value : V) (mp s : PyDict K V),
    ((newKeysObject id l u : Keys K V).log2Size = l ∧
      (newKeysObject id l u : Keys K V).indices = List.replicate (2 ^ l) DKIX_EMPTY ∧
      (newKeysObject id l u : Keys K V).entries = [] ∧
      (newKeysObject id l u : Keys K V).usable = usableFraction (2 ^ l) ∧
      (newKeysObject id l u : Keys K V).kind = (if u then .unicode else .general) ∧
      (l ≠ 0 → (newKeysObject id l u : Keys K V).bytes =
        32 + 2 ^ (if l < 8 then l else if l < 16 then l + 1 else if 32 ≤ l then l + 3 else l + 2) +
          usableFraction (2 ^ l) * (if u then 16 else 24))) ∧
    (insertToEmptyDict P key hash value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = 3 ∧ k'.usable = 4 ∧
        k'.kind = (if P.isStr key then .unicode else .general) ∧
        k'.entries = [some ⟨key, hash, value⟩] ∧ s.used = mp.used + 1) ∧
    (insertionResize u mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = calculateLog2Keysize (growthRate mp.used) ∧
        k'.usable = (usableFraction (2 ^ calculateLog2Keysize (growthRate mp.used)) : Int) - mp.used ∧
        k'.kind = (if (if mp.body.isUnicode then u else false) then .unicode else .general)) ∧
    ((mp.body.isUnicode && !KO.isStr key) = true → insertCombinedDict KO hash key value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.kind = .general ∧
        k'.entries.getLast? = some (some ⟨key, hash, value⟩)) ∧
    (∀ k, mp.body = .combined k → (k.kind != .general && !KO.isStr key) = false → 0 < k.usable →
      insertCombinedDict KO hash key value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = k.log2Size ∧ k'.kind = k.kind ∧
        k'.usable = k.usable - 1 ∧ k'.entries = k.entries ++ [some ⟨key, hash, value⟩]) ∧
    ((mp.body.isUnicode && !KO.isStr key) = false → mp.body.usable ≤ 0 →
      insertCombinedDict KO hash key value mp = (.ok (), s) →
      ∃ k', s.body = .combined k' ∧ k'.log2Size = calculateLog2Keysize (growthRate mp.used) ∧
        k'.kind = (if mp.body.isUnicode then .unicode else .general) ∧
        k'.entries.getLast? = some (some ⟨key, hash, value⟩))

theorem tableGeometry_proven : TableGeometry := by
  intro K V _ P KO id l u key hash value mp s
  refine ⟨⟨rfl, rfl, rfl, rfl, rfl, fun hl => ?_⟩, fun h => ?_, fun h => ?_, fun hs h => ?_,
    fun k hb hs hu h => ?_, fun hs hu h => ?_⟩
  · have he : (l == 0) = false := by simpa using hl
    rw [← log2IndexBytes_eq]
    cases u <;> simp [Keys.bytes, newKeysObject, Keys.isEmpty, Keys.size, he]
  · simp only [insertToEmptyDict, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    refine ⟨_, rfl, rfl, ?_, ?_, rfl, rfl⟩
    · simp [newKeysObject, usableFraction, PyDict_LOG_MINSIZE]
    · cases P.isStr key <;> rfl
  · obtain ⟨k', h1, h2, h3, _, h5⟩ := dictResize_ok h
    exact ⟨k', h1, h2, h3, h5⟩
  · simp only [insertCombinedDict, hs, if_true] at h
    split at h
    · simp at h
    · rename_i a mp1 hr
      obtain ⟨k1, hk1, _, _, _, hkind⟩ := dictResize_ok (by simpa [insertionResize] using hr)
      have hg : k1.kind = .general := by rw [hkind]; cases mp.body.isUnicode <;> rfl
      obtain ⟨k', a1, a2, a3, a4⟩ := icd_rest hk1 h
      refine ⟨k', a1, ?_, a2⟩
      by_cases hu : k1.usable ≤ 0
      · rw [(a3 hu).2, hg]; rfl
      · rw [(a4 hu).2.2.1, hg]
  · have hU : mp.body.isUnicode = (k.kind != .general) := by simp [Body.isUnicode, Body.kind, hb]
    have hs' : (mp.body.isUnicode && !KO.isStr key) = false := by rw [hU]; exact hs
    simp only [insertCombinedDict, hs', Bool.false_eq_true, if_false] at h
    obtain ⟨k', a1, _, _, a4⟩ := icd_rest hb h
    obtain ⟨b1, b2, b3, b4⟩ := a4 (by omega)
    exact ⟨k', a1, b1, b3, b2, b4⟩
  · simp only [insertCombinedDict, hs, Bool.false_eq_true, if_false] at h
    rw [if_pos hu] at h
    split at h
    · simp at h
    · rename_i a mp2 hr
      obtain ⟨k2, hk2, hl2, _, _, hkind⟩ := dictResize_ok (by simpa [insertionResize] using hr)
      rw [hk2] at h
      simp only at h
      split at h
      · rename_i k' hk
        simp only [Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨a1, a2, _, a4⟩ := appendEntry_ok hk
        refine ⟨k', rfl, by rw [a1, hl2], ?_, by simp [a4]⟩
        rw [a2, hkind]
        cases mp.body.isUnicode <;> rfl
      · simp at h

end PyLean.DictSet
