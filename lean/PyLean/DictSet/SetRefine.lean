import PyLean.DictSet.SetTable

/-!
The set table refines a list without duplicates.

Under the contract of `__hash__` and `__eq__`: `add`, `in`, `discard`, `pop`, `clear` and iteration
do what the list does. Table order is not insertion order and a resize changes it, so the list is
compared up to permutation. A resize can fail, so a run may stop with `MemoryError`.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type} [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}
  {so : SetObj K}

theorem noNull_first {so : SetObj K} {key : K} {u t j t1 j1 : Nat}
    (d : ∀ t'', t'' < t → ∀ j', j' ≤ linearProbes (spos so.mask u t'') so.mask →
      ¬ SStop so eqv key (spos so.mask u t'' + j'))
    (e : ∀ j', j' < j → ¬ SStop so eqv key (spos so.mask u t + j'))
    (h : (t1 < t ∧ j1 ≤ linearProbes (spos so.mask u t1) so.mask) ∨ (t1 = t ∧ j1 < j)) :
    NoNull so u t1 j1 := by
  have hnn : ∀ s, ¬ SStop so eqv key s → so.slot s ≠ .null := fun s hs hn => hs (Or.inl hn)
  rcases h with ⟨h1, h2⟩ | ⟨rfl, h2⟩
  · exact ⟨fun t' a j' b => hnn _ (d t' (by omega) j' b), fun j' a => hnn _ (d t1 h1 j' (by omega))⟩
  · exact ⟨fun t' a j' b => hnn _ (d t' a j' b), fun j' a => hnn _ (e j' (by omega))⟩

/-- A first stop at a NULL means the key is not in the table: a key has no NULL before it. -/
theorem absent_of_null (H : HonestSet P hf eqv) (w : SetCore hf eqv so) {key : K} {t j : Nat}
    (b : j ≤ linearProbes (spos so.mask (toU64 (hf key)) t) so.mask)
    (hnull : so.slot (spos so.mask (toU64 (hf key)) t + j) = .null)
    (d : ∀ t'', t'' < t → ∀ j', j' ≤ linearProbes (spos so.mask (toU64 (hf key)) t'') so.mask →
      ¬ SStop so eqv key (spos so.mask (toU64 (hf key)) t'' + j'))
    (e : ∀ j', j' < j → ¬ SStop so eqv key (spos so.mask (toU64 (hf key)) t + j')) :
    ∀ s' k h, so.slot s' = .active k h → eqv k key = false := by
  intro s' k h hs'
  cases hq : eqv k key with
  | false => rfl
  | true =>
    exfalso
    have hhash : toU64 h = toU64 (hf key) := by
      rw [w.hashes s' k h hs', H.hash_cons _ _ hq]
    obtain ⟨t', j', _, h2, h3, h4⟩ := w.reach s' k h hs'
    rw [hhash] at h2 h3 h4
    have hstop : SStop so eqv key (spos so.mask (toU64 (hf key)) t' + j') := by
      rw [h3]
      exact Or.inr ⟨k, h, hs', hq⟩
    by_cases hlt : t' < t
    · exact d t' hlt j' h2 hstop
    · by_cases hgt : t < t'
      · exact h4.1 t hgt j b hnull
      · have ht : t' = t := by omega
        subst ht
        by_cases hj : j' < j
        · exact e j' hj hstop
        · by_cases hj2 : j < j'
          · exact h4.2 j hj2 hnull
          · have : j' = j := by omega
            subst this
            rw [h3, hs'] at hnull
            simp at hnull

omit [DecidableEq K] in
theorem any_keys_true (so : SetObj K) (s : Nat) (k : K) (h : Int) (key : K)
    (hs : so.slot s = .active k h) (heq : eqv k key = true) :
    (setKeys so).any (eqv · key) = true := by
  have hm : (k, h) ∈ setEntries so := (mem_setEntries so k h).mpr ⟨s, hs⟩
  exact List.any_eq_true.mpr ⟨k, List.mem_map.mpr ⟨(k, h), hm, rfl⟩, heq⟩

omit [DecidableEq K] in
theorem any_keys_false (so : SetObj K) (key : K)
    (hne : ∀ s' k h, so.slot s' = .active k h → eqv k key = false) :
    (setKeys so).any (eqv · key) = false := by
  refine List.any_eq_false.mpr ?_
  intro x hx hq
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  obtain ⟨s, hs⟩ := (mem_setEntries so e.1 e.2).mp (by simpa using he)
  rw [hne s e.1 e.2 hs] at hq
  simp at hq

/-- What `set_add_entry` asks of `set_table_resize` for a table of `used` keys (:206-208). -/
def setGrowMin (used : Nat) : Nat := if used > 50000 then used * 2 else used * 4

/-- A set of `used` keys that would have to grow past what `PyMem_NEW` can give, the one reason an
add can fail for an honest key. -/
def SetTooBig (used : Nat) : Prop := SetResizeRefused (setGrowMin used)

section Add

theorem addAux_active (n : Nat) (so : SetObj K) {key : K} {hash : Int}
    (h : addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash) so.mask none
      so = (.ok .active, so)) :
    setAddEntryAux P key hash (n + 1) so = (.ok (), so) := by
  simp only [setAddEntryAux, M.bind_run, M.get_run]
  simp [h]

theorem addAux_unused (n : Nat) (so : SetObj K) {key : K} {hash : Int} {slot m : Nat}
    (h : addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash) so.mask none
      so = (.ok (.unused slot none m), so)) :
    let so' : SetObj K := { so with
      fill := so.fill + 1, used := so.used + 1, table := so.table.set slot (.active key hash) }
    setAddEntryAux P key hash (n + 1) so =
      if so'.fill * 5 < m * 3 then (.ok (), so') else setGrow so' := by
  intro so'
  have hf : so'.fill = so.fill + 1 := rfl
  rw [hf]
  simp only [setAddEntryAux, M.bind_run, M.get_run]
  simp only [h]
  by_cases hc : (so.fill + 1) * 5 < m * 3 <;> simp [M.bind_run, M.put_run, so', hc]

theorem addAux_dummy (n : Nat) (so : SetObj K) {key : K} {hash : Int} {slot m f : Nat}
    (h : addOuter P key hash (setProbeFuel so.mask) (toU64 hash &&& so.mask) (toU64 hash) so.mask none
      so = (.ok (.unused slot (some f) m), so)) (hd : so.slot f = .dummy) :
    setAddEntryAux P key hash (n + 1) so =
      (.ok (), { so with used := so.used + 1, table := so.table.set f (.active key hash) }) := by
  simp only [setAddEntryAux, M.bind_run, M.get_run]
  simp only [h]
  simp only [M.bind_run, M.get_run, hd]
  rfl

/-- `set_add_entry` on a well-formed set, on all its paths: the key is there and nothing changes; or
it goes in at a dummy the walk passed, or at the first NULL, resizing if the load limit is reached. -/
theorem setAddEntry_spec (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) :
    ((setKeys so).any (eqv · key) = true ∧ setAddEntry P key (hf key) so = (.ok (), so)) ∨
    ((setKeys so).any (eqv · key) = false ∧
      ((SetTooBig (so.used + 1) ∧ ∃ s, setAddEntry P key (hf key) so = (.error memoryError, s)) ∨
       ∃ so', setAddEntry P key (hf key) so = (.ok (), so') ∧ SetWF hf eqv so' ∧
         (setEntries so').Perm ((key, hf key) :: setEntries so))) := by
  let u := toU64 (hf key)
  obtain ⟨t0, ht0, hn0⟩ := w.null_on_walk u (toU64_lt _)
  obtain ⟨t, j, _, a, b, c, d0, e, f⟩ := addOuter_walk (P := P) H w key u
    (setProbeFuel so.mask) 0 none ⟨t0, by omega, by omega, 0, by omega, Or.inl (by simpa using hn0)⟩
  have d : ∀ t'', t'' < t → ∀ j', j' ≤ linearProbes (spos so.mask u t'') so.mask →
      ¬ SStop so eqv key (spos so.mask u t'' + j') := fun t'' h1 => d0 t'' (by omega) h1
  have ht : t < setProbeFuel so.mask := by omega
  rcases f with ⟨f1, k, h, f2, f3⟩ | ⟨f1, fs, f2, f3⟩
  · left
    exact ⟨any_keys_true so _ k h key f2 f3, addAux_active 255 so f1⟩
  · right
    have hne := absent_of_null H w.toSetCore b f1 d e
    refine ⟨any_keys_false so key hne, ?_⟩
    have hsym := H.symm
    rcases f2 with rfl | ⟨t1, j1, _, g2, g3, g4⟩
    · have hnn : NoNull so u t j := ⟨fun t' h1 j' h2 hn => d t' h1 j' h2 (Or.inl hn),
        fun j' h1 hn => e j' h1 (Or.inl hn)⟩
      have hle := w.block_le u t j b
      have hlt : spos so.mask u t + j < so.table.length := by have := w.len; omega
      have hcount := countP_set_up (fun x : Slot K => !x.isNull) (.active key (hf key)) so.table
        (spos so.mask u t + j) hlt
        (by rw [slot_get so _ hlt, f1]; rfl) rfl
      obtain ⟨g1, g2⟩ := setCore_ins hsym w.toSetCore key t j ht b hnn (by rw [f1]) hne (so.fill + 1)
        (by rw [hcount, w.fill])
      let so1 : SetObj K := { so with
        fill := so.fill + 1, used := so.used + 1
        table := so.table.set (spos so.mask u t + j) (.active key (hf key)) }
      have hrun : setAddEntry P key (hf key) so =
          if so1.fill * 5 < so.mask * 3 then (.ok (), so1) else setGrow so1 :=
        addAux_unused 255 so f3
      by_cases hl : so1.fill * 5 < so.mask * 3
      · right
        rw [if_pos hl] at hrun
        exact ⟨so1, hrun, { toSetCore := g1, load := hl }, g2⟩
      · rw [if_neg hl] at hrun
        have hgrow : setGrow so1 =
            setTableResize (if so1.used > 50000 then so1.used * 2 else so1.used * 4) so1 := rfl
        rcases setTableResize_spec hsym so1 g1
            (if so1.used > 50000 then so1.used * 2 else so1.used * 4)
            (by split <;> omega) with h1 | ⟨so2, h1, h2, h3⟩
        · left
          exact ⟨h1.1, so1, by rw [hrun, hgrow, h1.2]⟩
        · right
          exact ⟨so2, by rw [hrun, hgrow, h1], h2, h3.trans g2⟩
    · obtain ⟨rfl⟩ : fs = some (spos so.mask u t1 + j1) := g3
      have hnn : NoNull so u t1 j1 := noNull_first d e g2
      have hj1 : j1 ≤ linearProbes (spos so.mask u t1) so.mask := by
        rcases g2 with ⟨_, h2⟩ | ⟨rfl, h2⟩ <;> omega
      have ht1 : t1 < setProbeFuel so.mask := by
        rcases g2 with ⟨h1, _⟩ | ⟨rfl, _⟩ <;> omega
      have hle := w.block_le u t1 j1 hj1
      have hlt : spos so.mask u t1 + j1 < so.table.length := by have := w.len; omega
      have hcount := countP_set_same (fun x : Slot K => !x.isNull) (.active key (hf key)) so.table
        (spos so.mask u t1 + j1) hlt (by rw [slot_get so _ hlt, g4]; rfl)
      obtain ⟨h1, h2⟩ := setCore_ins hsym w.toSetCore key t1 j1 ht1 hj1 hnn (by rw [g4]) hne so.fill
        (by rw [hcount, w.fill])
      right
      exact ⟨_, addAux_dummy 255 so f3 g4, { toSetCore := h1, load := w.load }, h2⟩

end Add

section Ops

omit [DecidableEq K] in
theorem getD_replicate_null (n i : Nat) : (List.replicate n (Slot.null : Slot K)).getD i .null = .null := by
  simp only [List.getD, List.getElem?_replicate]
  split <;> simp

theorem setHashKey_ok (H : HonestSet P hf eqv) (key : K) (so : SetObj K) :
    setHashKey P key so = (.ok (hf key), so) := by
  simp [setHashKey, H.hash_ok]

theorem setHashKey_bind {β : Type} (H : HonestSet P hf eqv) (key : K) (f : Int → SM K β)
    (so : SetObj K) : (setHashKey P key >>= f) so = f (hf key) so :=
  M.bind_ok (setHashKey_ok H key so)

/-- `key in s`. -/
theorem setContains_spec (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) :
    setContainsKey P key so = (.ok ((setKeys so).any (eqv · key)), so) := by
  obtain ⟨s, h1, h2⟩ := setLookkey_spec H w key
  simp only [setContainsKey, setHashKey_bind H, setContainsEntry, M.bind_run, h1, M.get_run]
  rcases h2 with ⟨hn, hne⟩ | ⟨k, h, hs, heq⟩
  · simp [hn, any_keys_false so key hne]
  · simp [hs, any_keys_true so s k h key hs heq]

/-- `s.discard(key)`. -/
theorem setDiscard_spec (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) :
    ((setKeys so).any (eqv · key) = false ∧ setDiscardKey P key so = (.ok false, so)) ∨
    ∃ so', setDiscardKey P key so = (.ok true, so') ∧ SetWF hf eqv so' ∧
      (setKeys so').Perm ((setKeys so).filter fun x => !eqv x key) := by
  obtain ⟨s, h1, h2⟩ := setLookkey_spec H w key
  rcases h2 with ⟨hn, hne⟩ | ⟨k, h, hs, heq⟩
  · left
    refine ⟨any_keys_false so key hne, ?_⟩
    simp only [setDiscardKey, setHashKey_bind H, setDiscardEntry, M.bind_run, h1, M.get_run]
    simp [hn]
  · right
    obtain ⟨g1, g2⟩ := setCore_del w.toSetCore s k h hs
    refine ⟨_, ?_, { toSetCore := g1, load := w.load }, ?_⟩
    · simp only [setDiscardKey, setHashKey_bind H, setDiscardEntry, M.bind_run, h1, M.get_run]
      simp [hs, M.bind_run, M.put_run]
    · have hmap := g2.map (·.1)
      have hkeys : (setKeys so).Perm (k :: setKeys
          { so with used := so.used - 1, table := so.table.set s .dummy }) := hmap
      refine List.Perm.trans ?_ (hkeys.filter _).symm
      simp only [List.filter_cons, heq, Bool.not_true, Bool.false_eq_true, if_false]
      have hall : ∀ x ∈ setKeys { so with used := so.used - 1, table := so.table.set s .dummy },
          (!eqv x key) = true := by
        intro x hx
        have hlt := slot_lt so s _ (by simp) hs
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        obtain ⟨s', hs'⟩ := (mem_setEntries _ e.1 e.2).mp (by simpa using he)
        have hsl := slot_set so s s' .dummy hlt
        have hs2 : so.slot s' = .active e.1 e.2 ∧ s' ≠ s := by
          have h3 : ({ so with table := so.table.set s .dummy } : SetObj K).slot s' =
              .active e.1 e.2 := hs'
          rw [hsl] at h3
          split at h3
          · simp at h3
          · rename_i hne
            exact ⟨h3, hne⟩
        cases hq : eqv e.1 key with
        | false => rfl
        | true =>
          exact absurd (w.uniq s' e.1 e.2 s k h hs2.1 hs (H.trans _ key _ hq (by rw [H.symm]; exact heq)))
            hs2.2
      rw [List.filter_eq_self.mpr hall]

/-- `s.add(key)`. -/
theorem setAddKey_spec (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) :
    ((setKeys so).any (eqv · key) = true ∧ setAddKey P key so = (.ok (), so)) ∨
    ((setKeys so).any (eqv · key) = false ∧
      ((SetTooBig (so.used + 1) ∧ ∃ s, setAddKey P key so = (.error memoryError, s)) ∨
       ∃ so', setAddKey P key so = (.ok (), so') ∧ SetWF hf eqv so' ∧
         (setKeys so').Perm (key :: setKeys so))) := by
  have hunf : setAddKey P key so = setAddEntry P key (hf key) so := setHashKey_bind H key _ so
  rw [hunf]
  rcases setAddEntry_spec H w key with h | ⟨h1, h2⟩
  · exact Or.inl h
  · right
    refine ⟨h1, ?_⟩
    rcases h2 with h | ⟨so', a, b, c⟩
    · exact Or.inl h
    · exact Or.inr ⟨so', a, b, by simpa [setKeys] using c.map Prod.fst⟩

/-- `set_clear_internal`. -/
theorem setClear_spec (w : SetWF hf eqv so) :
    SetWF hf eqv (setClearInternal so) ∧ setEntries (setClearInternal so) = [] := by
  have hempty : SetWF hf eqv (setEmptyToMinsize so) ∧ setEntries (setEmptyToMinsize so) = [] := by
    have hslot : ∀ i, (setEmptyToMinsize so).slot i = .null := fun i =>
      getD_replicate_null 8 i
    have hent : setEntries (setEmptyToMinsize so) = [] := rfl
    refine ⟨{ log := ⟨3, rfl⟩, len := rfl, small := Nat.le_refl 7
              reach := fun s k h hs => by rw [hslot] at hs; simp at hs
              hashes := fun s k h hs => by rw [hslot] at hs; simp at hs
              uniq := fun s1 k1 h1 s2 k2 h2 a _ _ => by rw [hslot] at a; simp at a
              fill := rfl
              used := by rw [hent]; rfl
              load := by
                show 0 * 5 < 7 * 3
                decide }, hent⟩
  simp only [setClearInternal]
  split
  · exact hempty
  · split
    · exact hempty
    · rename_i hf0
      have hz : so.fill = 0 := by omega
      refine ⟨w, ?_⟩
      have hc : so.table.countP (fun x => !x.isNull) = 0 := by rw [← w.fill, hz]
      have hall := List.countP_eq_zero.mp hc
      have : ∀ x ∈ so.table, slotEntry x = none := by
        intro x hx
        have := hall x hx
        cases x <;> simp_all [Slot.isNull]
      simp only [setEntries_eq]
      exact List.filterMap_eq_nil_iff.mpr this

end Ops

section Program

/-- A run of `add` and `discard`, stopped by the first exception. -/
def setOpsRun (P : Proto K (SetObj K)) : List (SOp K) → SetObj K → Py (SetObj K)
  | [], s => .ok s
  | .add k :: rest, s =>
    match setAddKey P k s with
    | (.ok _, s') => setOpsRun P rest s'
    | (.error e, _) => .error e
  | .discard k :: rest, s =>
    match setDiscardKey P k s with
    | (.ok _, s') => setOpsRun P rest s'
    | (.error e, _) => .error e

omit [DecidableEq K] in
theorem setAbs_perm (hsym : ∀ a b, eqv a b = eqv b a) :
    ∀ (ops : List (SOp K)) (l l' : List K), l.Perm l' →
      (setAbs eqv ops l).Perm (setAbs eqv ops l') := by
  intro ops
  induction ops with
  | nil => intro l l' h; exact h
  | cons op rest ih =>
    intro l l' h
    cases op with
    | add k =>
      simp only [setAbs]
      rw [h.any_eq]
      split
      · exact ih _ _ h
      · exact ih _ _ (h.append_right _)
    | discard k =>
      simp only [setAbs]
      exact ih _ _ (h.filter _)

omit [DecidableEq K] in
theorem wf_empty_set (hf : K → Int) (eqv : K → K → Bool) : SetWF hf eqv ({} : SetObj K) ∧
    setKeys ({} : SetObj K) = [] := by
  have hslot : ∀ i, ({} : SetObj K).slot i = .null := fun i => getD_replicate_null 8 i
  have hent : setEntries ({} : SetObj K) = [] := rfl
  refine ⟨{ log := ⟨3, rfl⟩, len := rfl, small := Nat.le_refl 7
            reach := fun s k h hs => by rw [hslot] at hs; simp at hs
            hashes := fun s k h hs => by rw [hslot] at hs; simp at hs
            uniq := fun s1 k1 h1 s2 k2 h2 a _ _ => by rw [hslot] at a; simp at a
            fill := rfl
            used := by rw [hent]; rfl
            load := by
              show 0 * 5 < 7 * 3
              decide }, ?_⟩
  rfl

theorem setOpsRun_spec (H : HonestSet P hf eqv) :
    ∀ (ops : List (SOp K)) (so : SetObj K) (l : List K), SetWF hf eqv so → (setKeys so).Perm l →
      (setOpsRun P ops so = .error memoryError ∧ ∃ n, n ≤ so.used + ops.length ∧ SetTooBig n) ∨
      ∃ so', setOpsRun P ops so = .ok so' ∧ SetWF hf eqv so' ∧ (setKeys so').Perm (setAbs eqv ops l) := by
  intro ops
  induction ops with
  | nil =>
    intro so l w h
    exact Or.inr ⟨so, rfl, w, h⟩
  | cons op rest ih =>
    intro so l w hp
    cases op with
    | add k =>
      simp only [setOpsRun, setAbs]
      rw [← hp.any_eq]
      rcases setAddKey_spec H w k with ⟨h1, h2⟩ | ⟨h1, h3⟩
      · simp only [h2, h1, if_true]
        rcases ih so l w hp with ⟨g1, n, g2, g3⟩ | g
        · exact Or.inl ⟨g1, n, by simp only [List.length_cons]; omega, g3⟩
        · exact Or.inr g
      · simp only [h1, Bool.false_eq_true, if_false]
        rcases h3 with ⟨hb, s, h3⟩ | ⟨so', a, b, c⟩
        · left
          exact ⟨by simp [h3], so.used + 1, by simp, hb⟩
        · simp only [a]
          have hu : so'.used = so.used + 1 := by
            have h1 := b.used
            have h2 := w.used
            have h3 := c.length_eq
            simp only [setKeys, List.length_map, List.length_cons] at h3
            omega
          rcases ih so' _ b (c.trans ((hp.cons k).trans (List.perm_append_singleton k l).symm)) with
            ⟨g1, n, g2, g3⟩ | g
          · exact Or.inl ⟨g1, n, by simp only [List.length_cons]; omega, g3⟩
          · exact Or.inr g
    | discard k =>
      simp only [setOpsRun, setAbs]
      rcases setDiscard_spec H w k with ⟨h1, h2⟩ | ⟨so', a, b, c⟩
      · simp only [h2]
        have hall : ∀ x ∈ l, (!eqv x k) = true := by
          intro x hx
          have h3 : l.any (eqv · k) = false := by rw [← hp.any_eq]; exact h1
          have := List.any_eq_false.mp h3 x hx
          simpa using this
        have hp' : (setKeys so).Perm (l.filter fun x => !eqv x k) := by
          rw [List.filter_eq_self.mpr hall]
          exact hp
        rcases ih so _ w hp' with ⟨g1, n, g2, g3⟩ | g
        · exact Or.inl ⟨g1, n, by simp only [List.length_cons]; omega, g3⟩
        · exact Or.inr g
      · simp only [a]
        have hu : so'.used ≤ so.used := by
          have h1 := b.used
          have h2 := w.used
          have h3 := c.length_eq
          have h4 := List.length_filter_le (fun x => !eqv x k) (setKeys so)
          simp only [setKeys, List.length_map] at h3 h4
          omega
        rcases ih so' _ b (c.trans (hp.filter _)) with ⟨g1, n, g2, g3⟩ | g
        · exact Or.inl ⟨g1, n, by simp only [List.length_cons]; omega, g3⟩
        · exact Or.inr g

end Program

/-- The set table refines a list without duplicates: from an empty set, a run of `add` and `discard`
leaves a well-formed table that holds what the list holds, and `in` answers as the list does; or it
stops with `MemoryError`, and then some set of no more keys than the run has steps needed a table
`PyMem_NEW` refuses. -/
def SetTableRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (ops : List (SOp K)) (key : K),
      (setOpsRun P ops {} = .error memoryError ∧ ∃ n, n ≤ ops.length ∧ SetTooBig n) ∨
      ∃ so, setOpsRun P ops {} = .ok so ∧ SetWF hf eqv so ∧ (setKeys so).Perm (setAbs eqv ops []) ∧
        (setContainsKey P key so).1 = .ok ((setAbs eqv ops []).any (eqv · key))

theorem setTableRefines_proven : SetTableRefines := by
  intro K _ P hf eqv H ops key
  obtain ⟨w0, h0⟩ := wf_empty_set hf eqv
  rcases setOpsRun_spec H ops {} [] w0 (by rw [h0]) with ⟨h, n, g1, g2⟩ | ⟨so, a, b, c⟩
  · exact Or.inl ⟨h, n, by simpa using g1, g2⟩
  · refine Or.inr ⟨so, a, b, c, ?_⟩
    rw [setContains_spec H b key, c.any_eq]

section Pop

omit [DecidableEq K] in
/-- `set.pop`'s scan wraps at the end of the table, and it finds an entry at distance `d`. -/
theorem popScan_finds (so : SetObj K) (hm : 0 < so.mask + 1) :
    ∀ (f i d : Nat), i ≤ so.mask → d < f →
      (∃ k h, so.slot ((i + d) % (so.mask + 1)) = .active k h) →
      ∃ s k h, setPop.scan so f i = some (s, k) ∧ so.slot s = .active k h := by
  intro f
  induction f with
  | zero => intro i d _ h; omega
  | succ f ih =>
    intro i d hi hd hex
    by_cases hat : ∃ k h, so.slot i = .active k h
    · obtain ⟨k, h, hs⟩ := hat
      exact ⟨i, k, h, by simp [setPop.scan, hs], hs⟩
    · have hscan : setPop.scan so (f + 1) i =
          setPop.scan so f (if i + 1 > so.mask then 0 else i + 1) := by
        simp only [setPop.scan]
        cases hc : so.slot i with
        | null => rfl
        | dummy => rfl
        | active k h => exact absurd ⟨k, h, hc⟩ hat
      rw [hscan]
      have hd0 : d ≠ 0 := by
        rintro rfl
        obtain ⟨k, h, hs⟩ := hex
        rw [Nat.add_zero, Nat.mod_eq_of_lt (by omega)] at hs
        exact hat ⟨k, h, hs⟩
      obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
      refine ih _ d' (by split <;> omega) (by omega) ?_
      have hmod : ((if i + 1 > so.mask then 0 else i + 1) + d') % (so.mask + 1) =
          (i + (d' + 1)) % (so.mask + 1) := by
        split
        · have hi' : i = so.mask := by omega
          subst hi'
          have : so.mask + (d' + 1) = d' + (so.mask + 1) := by omega
          rw [this, Nat.add_mod_right, Nat.zero_add]
        · congr 1
          omega
      rw [hmod]
      exact hex

/-- `set.pop` removes one entry, whichever the finger reaches, and raises on an empty set. -/
theorem setPop_spec (w : SetWF hf eqv so) :
    (setKeys so = [] ∧ setPop so = (.error (.keyError "'pop from an empty set'"), so)) ∨
    ∃ key h so', setPop so = (.ok key, so') ∧ SetWF hf eqv so' ∧
      (setEntries so).Perm ((key, h) :: setEntries so') := by
  by_cases h0 : so.used = 0
  · left
    have hent : setEntries so = [] := by
      apply List.length_eq_zero_iff.mp
      rw [← w.used]
      exact h0
    refine ⟨by simp [setKeys, hent], ?_⟩
    simp [setPop, M.bind_run, M.get_run, h0]
  · right
    have hne : setEntries so ≠ [] := by
      intro he
      have := w.used
      rw [he] at this
      exact h0 this
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hne
    obtain ⟨s, hs⟩ := (mem_setEntries so e.1 e.2).mp (by simpa using he)
    have hlt := slot_lt so s _ (by simp) hs
    have hsm : s ≤ so.mask := by have := w.len; omega
    let i := so.finger &&& so.mask
    have hi : i ≤ so.mask := Nat.and_le_right
    have hd : ∃ d, d < so.mask + 2 ∧ (i + d) % (so.mask + 1) = s := by
      by_cases his : i ≤ s
      · exact ⟨s - i, by omega, by
          rw [show i + (s - i) = s by omega]
          exact Nat.mod_eq_of_lt (by omega)⟩
      · refine ⟨s + (so.mask + 1) - i, by omega, ?_⟩
        rw [show i + (s + (so.mask + 1) - i) = s + (so.mask + 1) by omega, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨d, hd1, hd2⟩ := hd
    obtain ⟨s', k, h, hsc, hs'⟩ := popScan_finds so (by omega) (so.mask + 2) i d hi hd1
      ⟨e.1, e.2, by rw [hd2]; exact hs⟩
    obtain ⟨g1, g2⟩ := setCore_del w.toSetCore s' k h hs'
    refine ⟨k, h, { so with table := so.table.set s' .dummy, used := so.used - 1, finger := s' + 1 },
      ?_, { toSetCore := g1.of_fields rfl rfl rfl rfl, load := w.load }, g2⟩
    have hn0 : (so.used == 0) = false := by simpa using h0
    simp only [setPop, M.bind_run, M.get_run, hn0, Bool.false_eq_true, if_false]
    have hsc' : setPop.scan so (so.mask + 2) (so.finger &&& so.mask) = some (s', k) := hsc
    simp [hsc', M.bind_run, M.put_run]

end Pop

section Iter

omit [DecidableEq K] in
/-- `set_next` reads the table from `i`: the next entry and where to go on. -/
theorem setNext_spec (t : List (Slot K)) (mask : Nat) (hlen : t.length = mask + 1) :
    ∀ (f i : Nat), mask + 1 < i + f → i ≤ mask + 1 →
      match (t.drop i).filterMap slotEntry with
      | [] => setNext t mask f i = none
      | (k, h) :: rest => ∃ i', i < i' ∧ i' ≤ mask + 1 ∧ setNext t mask f i = some (i', k, h) ∧
          (t.drop i').filterMap slotEntry = rest := by
  intro f
  induction f with
  | zero => intro i h1 h2; omega
  | succ f ih =>
    intro i h1 h2
    by_cases hi : i > mask
    · have hd : t.drop i = [] := List.drop_eq_nil_of_le (by omega)
      simp [hd, setNext, hi]
    · have hlt : i < t.length := by omega
      have hdrop : t.drop i = t[i] :: t.drop (i + 1) := List.drop_eq_getElem_cons hlt
      have hget : t.getD i .null = t[i] := by simp [List.getD, hlt]
      have hrec := ih (i + 1) (by omega) (by omega)
      have hstep0 : setNext t mask (f + 1) i =
          match t.getD i .null with
          | .active k h => some (i + 1, k, h)
          | _ => setNext t mask f (i + 1) := by
        have e : setNext t mask (f + 1) i = if i > mask then none else
            (match t.getD i .null with
             | .active k h => some (i + 1, k, h)
             | _ => setNext t mask f (i + 1)) := rfl
        rw [e, if_neg hi]
      have skip : (∀ k h, t[i] ≠ .active k h) → setNext t mask (f + 1) i = setNext t mask f (i + 1) := by
        intro hn
        rw [hstep0, hget]
        cases hc : t[i] with
        | null => rfl
        | dummy => rfl
        | active k h => exact absurd hc (hn k h)
      have finish : (t.drop (i + 1)).filterMap slotEntry = (t.drop i).filterMap slotEntry →
          setNext t mask (f + 1) i = setNext t mask f (i + 1) →
          match (t.drop i).filterMap slotEntry with
          | [] => setNext t mask (f + 1) i = none
          | (k, h) :: rest => ∃ i', i < i' ∧ i' ≤ mask + 1 ∧ setNext t mask (f + 1) i = some (i', k, h) ∧
              (t.drop i').filterMap slotEntry = rest := by
        intro he hs
        rw [← he, hs]
        generalize (t.drop (i + 1)).filterMap slotEntry = R at hrec
        cases R with
        | nil => exact hrec
        | cons x r =>
          obtain ⟨k, h⟩ := x
          obtain ⟨i', a, b, c, d⟩ := hrec
          exact ⟨i', by omega, b, c, d⟩
      cases hc : t[i] with
      | null =>
        exact finish (by rw [hdrop, hc]; rfl) (skip (by simp [hc]))
      | dummy =>
        exact finish (by rw [hdrop, hc]; rfl) (skip (by simp [hc]))
      | active k h =>
        rw [hdrop, hc]
        exact ⟨i + 1, by omega, by omega, by rw [hstep0, hget, hc], rfl⟩

omit [DecidableEq K] in
/-- Draining an iterator over a set that does not change gives the rest of the table, in order. -/
theorem setiterDrain_spec (so : SetObj K) (hlen : so.table.length = so.mask + 1) :
    ∀ (fuel : Nat) (si : SetIter) (acc : List K), si.alive = true → si.used = so.used →
      si.pos ≤ so.mask + 1 → so.mask + 2 < si.pos + fuel →
      (setiterDrain so fuel si acc).1 =
        .ok (acc.reverse ++ ((so.table.drop si.pos).filterMap slotEntry).map (·.1)) := by
  intro fuel
  induction fuel with
  | zero => intro si acc _ _ h1 h2; omega
  | succ fuel ih =>
    intro si acc h1 h2 h3 h4
    have hn := setNext_spec so.table so.mask hlen (so.mask + 2) si.pos (by omega) h3
    simp only [setiterDrain, setiterNext, h1, h2, Bool.not_true, Bool.false_eq_true, if_false,
      bne_self_eq_false]
    cases he : (so.table.drop si.pos).filterMap slotEntry with
    | nil =>
      rw [he] at hn
      simp [hn]
    | cons x rest =>
      obtain ⟨k, h⟩ := x
      rw [he] at hn
      obtain ⟨i', a, b, c, d⟩ := hn
      simp only [c]
      have := ih { used := (so.used : Int), pos := i', len := si.len - 1 } (k :: acc) rfl rfl b
        (by simp only []; omega)
      simpa [d] using this

end Iter

/-- `s.pop()`: raises on an empty set; otherwise one entry leaves, and the table stays well formed. -/
def SetPopSpec : Prop :=
  ∀ (K : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K), SetWF hf eqv so →
    (setKeys so = [] ∧ setPop so = (.error (.keyError "'pop from an empty set'"), so)) ∨
    ∃ key h so', setPop so = (.ok key, so') ∧ SetWF hf eqv so' ∧
      (setEntries so).Perm ((key, h) :: setEntries so')
theorem setPopSpec_proven : SetPopSpec := fun _ _ _ _ _ w => setPop_spec w

/-- `s.clear()` keeps the table well formed and empties it. -/
def SetClearSpec : Prop :=
  ∀ (K : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K), SetWF hf eqv so →
    SetWF hf eqv (setClearInternal so) ∧ setEntries (setClearInternal so) = []
theorem setClearSpec_proven : SetClearSpec := fun _ _ _ _ _ w => setClear_spec w

/-- Iterating over a set that does not change gives its keys, in table order, each once. -/
def SetIterOrder : Prop :=
  ∀ (K : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K), SetWF hf eqv so →
    (setiterDrain so (so.mask + 3) (setIterNew so) []).1 = .ok (setKeys so)
theorem setIterOrder_proven : SetIterOrder := by
  intro K _ hf eqv so w
  have h := setiterDrain_spec so w.len (so.mask + 3) (setIterNew so) [] rfl rfl (by simp [setIterNew])
    (by simp [setIterNew])
  simpa [setIterNew, setKeys, setEntries_eq] using h

section Failure
variable (P : Proto K (SetObj K)) (key startkey : K) (hash : Int) (slot mask : Nat)
  (so s' : SetObj K) (e : PyExc) (fr : Bool)

/-- With a raising `__eq__`, `set_lookkey` raises it, and what `__eq__` did stands. -/
theorem lookStep_raises (hs : so.slot slot = .active startkey hash) (h1 : startkey ≠ key)
    (h2 : ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true))
    (hq : P.eq startkey key so = (.error e, s')) :
    lookStep P fr key hash slot mask so = (.error e, s') := by
  simp [lookStep, M.bind_run, M.get_run, hs, h1, h2, hq]

/-- With a set whose table `__eq__` changed, `set_lookkey` restarts, whatever `__eq__` answered, while
a frozenset does not look: it cannot change. -/
theorem lookStep_changed (b : Bool) (hs : so.slot slot = .active startkey hash) (h1 : startkey ≠ key)
    (h2 : ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true))
    (hq : P.eq startkey key so = (.ok b, s'))
    (hch : setChanged s' so.tableId slot startkey = true) :
    lookStep P false key hash slot mask so = (.ok (.inl .restart), s') := by
  simp [lookStep, M.bind_run, M.get_run, hs, h1, h2, hq, hch]

/-- `set_add_entry` tests the answer first (:173-174) and the table after it (:177), the reverse of
`set_lookkey` (:118, :120): an `__eq__` that answers yes and changes the table is believed. -/
theorem addStep_trusts_yes (fs : Option Nat) (hs : so.slot slot = .active startkey hash)
    (h1 : startkey ≠ key)
    (h2 : ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true))
    (hq : P.eq startkey key so = (.ok true, s')) :
    addStep P key hash slot mask fs so = (.ok (.inl .active), s') := by
  simp [addStep, M.bind_run, M.get_run, hs, h1, h2, hq]

theorem addStep_raises (fs : Option Nat) (hs : so.slot slot = .active startkey hash)
    (h1 : startkey ≠ key)
    (h2 : ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true))
    (hq : P.eq startkey key so = (.error e, s')) :
    addStep P key hash slot mask fs so = (.error e, s') := by
  simp [addStep, M.bind_run, M.get_run, hs, h1, h2, hq]

/-- `set_add_entry` on an answer of no, and a changed table: it restarts (:177-178). -/
theorem addStep_changed (fs : Option Nat) (hs : so.slot slot = .active startkey hash)
    (h1 : startkey ≠ key)
    (h2 : ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true))
    (hq : P.eq startkey key so = (.ok false, s'))
    (hch : setChanged s' so.tableId slot startkey = true) :
    addStep P key hash slot mask fs so = (.ok (.inl .restart), s') := by
  simp [addStep, M.bind_run, M.get_run, hs, h1, h2, hq, hch]

theorem setHash_fails (hh : P.hash key = .error e) :
    setAddKey P key so = (.error (setUnhashableType P key e), so) ∧
    setContainsKey P key so = (.error (setUnhashableType P key e), so) ∧
    setDiscardKey P key so = (.error (setUnhashableType P key e), so) := by
  simp [setAddKey, setContainsKey, setDiscardKey, setHashKey, hh, M.bind_run]

end Failure

/-- The failure paths of the set probes, for every key protocol. -/
def SetProbeFailure : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key startkey : K) (hash : Int) (slot mask : Nat)
    (so s' : SetObj K) (e : PyExc) (fs : Option Nat),
    so.slot slot = .active startkey hash → startkey ≠ key →
    ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true) →
    (P.eq startkey key so = (.error e, s') →
      (∀ fr, lookStep P fr key hash slot mask so = (.error e, s')) ∧
      addStep P key hash slot mask fs so = (.error e, s')) ∧
    (setChanged s' so.tableId slot startkey = true →
      (∀ b, P.eq startkey key so = (.ok b, s') →
        lookStep P false key hash slot mask so = (.ok (.inl .restart), s')) ∧
      (P.eq startkey key so = (.ok false, s') →
        addStep P key hash slot mask fs so = (.ok (.inl .restart), s')))
theorem setProbeFailure_proven : SetProbeFailure := by
  intro K _ P key startkey hash slot mask so s' e fs hs h1 h2
  refine ⟨fun hq => ⟨fun fr => lookStep_raises P key startkey hash slot mask so s' e fr hs h1 h2 hq,
    addStep_raises P key startkey hash slot mask so s' e fs hs h1 h2 hq⟩, fun hch => ⟨?_, ?_⟩⟩
  · exact fun b hq => lookStep_changed P key startkey hash slot mask so s' b hs h1 h2 hq hch
  · exact fun hq => addStep_changed P key startkey hash slot mask so s' fs hs h1 h2 hq hch

/-- `set_add_entry` and `set_lookkey` differ on an `__eq__` that answers yes and changes the table:
the lookup goes round again, the add stops, believing it. -/
def SetAddTrustsYes : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key startkey : K) (hash : Int) (slot mask : Nat)
    (so s' : SetObj K) (fs : Option Nat),
    so.slot slot = .active startkey hash → startkey ≠ key →
    ¬ ((P.isStr startkey = true ∧ P.isStr key = true) ∧ P.strEq startkey key = true) →
    P.eq startkey key so = (.ok true, s') → setChanged s' so.tableId slot startkey = true →
    lookStep P false key hash slot mask so = (.ok (.inl .restart), s') ∧
    addStep P key hash slot mask fs so = (.ok (.inl .active), s')
theorem setAddTrustsYes_proven : SetAddTrustsYes := by
  intro K _ P key startkey hash slot mask so s' fs hs h1 h2 hq hch
  exact ⟨lookStep_changed P key startkey hash slot mask so s' true hs h1 h2 hq hch,
    addStep_trusts_yes P key startkey hash slot mask so s' fs hs h1 h2 hq⟩

/-- A failed hash, for every key protocol. -/
def SetHashFailure : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (key : K) (so : SetObj K) (e : PyExc),
    P.hash key = .error e →
    setAddKey P key so = (.error (setUnhashableType P key e), so) ∧
    setContainsKey P key so = (.error (setUnhashableType P key e), so) ∧
    setDiscardKey P key so = (.error (setUnhashableType P key e), so)
theorem setHashFailure_proven : SetHashFailure := fun _ _ P key so e hh => setHash_fails P key so e hh

end PyLean.DictSet
