import PyLean.DictSet.SetChain

/-!
`set_add_entry` and `set_table_resize`.

The add path differs from the lookup in one way that matters: it remembers the last dummy it passed
(`freeslot`) and stores there. That slot lies on the walk of the hash before the first NULL, so the
new entry still has no NULL before it. `set_add_entry` stores before it resizes, so a resize starts
from `SetCore`, with the load limit possibly reached.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type}

section Add
variable [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}

theorem addStep_null (fs : Option Nat) (key : K) (slot : Nat) (hash : Int) (hn : so.slot slot = .null) :
    addStep P key hash slot so.mask fs so = (.ok (.inl (.unused slot fs so.mask)), so) := by
  simp [addStep, M.bind_run, M.get_run, hn]

theorem addStep_dummy (fs : Option Nat) (key : K) (slot : Nat) (hash : Int) (hn : so.slot slot = .dummy) :
    addStep P key hash slot so.mask fs so = (.ok (.inr (so.mask, some slot)), so) := by
  simp [addStep, M.bind_run, M.get_run, hn]

theorem addStep_match (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (fs : Option Nat) (key : K)
    (slot : Nat) (k : K) (h : Int) (hs : so.slot slot = .active k h) (heq : eqv k key = true) :
    addStep P key (hf key) slot so.mask fs so = (.ok (.inl .active), so) := by
  have hh : h = hf key := (w.hashes slot k h hs).trans (H.hash_cons _ _ heq)
  subst hh
  by_cases h1 : k = key
  · simp [addStep, M.bind_run, M.get_run, hs, h1]
  · by_cases h2 : (P.isStr k = true ∧ P.isStr key = true) ∧ P.strEq k key = true
    · simp [addStep, M.bind_run, M.get_run, hs, h1, h2]
    · simp [addStep, M.bind_run, M.get_run, hs, h1, h2, H.eq_ok, heq]

theorem addStep_pass (H : HonestSet P hf eqv) (fs : Option Nat) (key : K)
    (slot : Nat) (k : K) (h : Int) (hs : so.slot slot = .active k h) (hne : eqv k key = false) :
    addStep P key (hf key) slot so.mask fs so = (.ok (.inr (so.mask, fs)), so) := by
  have hc := setChanged_same so slot k h hs
  by_cases hh : h = hf key
  · have h1 : k ≠ key := by
      intro he
      rw [he, H.refl] at hne
      simp at hne
    have h2 : ¬ ((P.isStr k = true ∧ P.isStr key = true) ∧ P.strEq k key = true) := by
      rintro ⟨⟨h3, h4⟩, h5⟩
      rw [H.str_eq _ _ h3 h4, hne] at h5
      simp at h5
    simp [addStep, M.bind_run, M.get_run, hs, hh, h1, h2, H.eq_ok, hne, hc]
  · simp [addStep, M.bind_run, M.get_run, hs, hh]

/-- `freeslot` after a run of a block: what it was, or a dummy this run passed. -/
def FsGood (so : SetObj K) (slot j : Nat) (fs0 fs : Option Nat) : Prop :=
  fs = fs0 ∨ ∃ j', j' < j ∧ fs = some (slot + j') ∧ so.slot (slot + j') = .dummy

open Classical in
theorem addScan_walk (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) :
    ∀ (p slot : Nat) (fs : Option Nat),
      (∃ j, j ≤ p ∧ SStop so eqv key (slot + j) ∧ (∀ j', j' < j → ¬ SStop so eqv key (slot + j')) ∧
        ((addScan P key (hf key) p slot so.mask fs so = (.ok .active, so) ∧
            ∃ k h, so.slot (slot + j) = .active k h ∧ eqv k key = true) ∨
         (so.slot (slot + j) = .null ∧ ∃ fs', FsGood so slot j fs fs' ∧
            addScan P key (hf key) p slot so.mask fs so =
              (.ok (.unused (slot + j) fs' so.mask), so)))) ∨
      ((∀ j, j ≤ p → ¬ SStop so eqv key (slot + j)) ∧ ∃ fs', FsGood so slot (p + 1) fs fs' ∧
        addScan P key (hf key) p slot so.mask fs so = (.ok (.next fs' so.mask), so)) := by
  have hstep : ∀ (slot : Nat) (fs : Option Nat), ¬ SStop so eqv key slot →
      ∃ fs1, FsGood so slot 1 fs fs1 ∧
        addStep P key (hf key) slot so.mask fs so = (.ok (.inr (so.mask, fs1)), so) := by
    intro slot fs hs
    cases hc : so.slot slot with
    | null => exact absurd (Or.inl hc) hs
    | dummy =>
      exact ⟨some slot, Or.inr ⟨0, by omega, rfl, hc⟩, addStep_dummy fs key slot _ hc⟩
    | active k h =>
      have hne : eqv k key = false := by
        cases hq : eqv k key with
        | false => rfl
        | true => exact absurd (Or.inr ⟨k, h, hc, hq⟩) hs
      exact ⟨fs, Or.inl rfl, addStep_pass H fs key slot k h hc hne⟩
  have hstop : ∀ (p slot : Nat) (fs : Option Nat), SStop so eqv key slot →
      (addScan P key (hf key) p slot so.mask fs so = (.ok .active, so) ∧
        ∃ k h, so.slot (slot + 0) = .active k h ∧ eqv k key = true) ∨
      (so.slot (slot + 0) = .null ∧ ∃ fs', FsGood so slot 0 fs fs' ∧
        addScan P key (hf key) p slot so.mask fs so = (.ok (.unused (slot + 0) fs' so.mask), so)) := by
    intro p slot fs hs
    rcases hs with hn | ⟨k, h, hc, heq⟩
    · right
      refine ⟨hn, fs, Or.inl rfl, ?_⟩
      cases p <;> simp [addScan, M.bind_run, addStep_null fs key slot _ hn]
    · left
      refine ⟨?_, k, h, hc, heq⟩
      cases p <;> simp [addScan, M.bind_run, addStep_match H w fs key slot k h hc heq]
  intro p
  induction p with
  | zero =>
    intro slot fs
    by_cases hs : SStop so eqv key slot
    · exact Or.inl ⟨0, by omega, hs, fun j' h => by omega, hstop 0 slot fs hs⟩
    · right
      obtain ⟨fs1, h1, h2⟩ := hstep slot fs hs
      refine ⟨fun j h => ?_, fs1, h1, ?_⟩
      · have : j = 0 := by omega
        subst this
        exact hs
      · simp [addScan, M.bind_run, h2]
  | succ p ih =>
    intro slot fs
    by_cases hs : SStop so eqv key slot
    · exact Or.inl ⟨0, by omega, hs, fun j' h => by omega, hstop (p + 1) slot fs hs⟩
    · obtain ⟨fs1, h1, h2⟩ := hstep slot fs hs
      have hrun : addScan P key (hf key) (p + 1) slot so.mask fs so =
          addScan P key (hf key) p (slot + 1) so.mask fs1 so := by
        simp [addScan, M.bind_run, h2]
      have hshift : ∀ j, slot + 1 + j = slot + (j + 1) := fun j => by omega
      have hgood : ∀ j fs', FsGood so (slot + 1) j fs1 fs' → FsGood so slot (j + 1) fs fs' := by
        intro j fs' hf'
        rcases hf' with rfl | ⟨j', a, rfl, c⟩
        · rcases h1 with rfl | ⟨j0, a, rfl, c⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨j0, by omega, rfl, c⟩
        · refine Or.inr ⟨j' + 1, by omega, ?_, ?_⟩
          · rw [hshift]
          · rw [← hshift]
            exact c
      rcases ih (slot + 1) fs1 with ⟨j, a, b, c, d⟩ | ⟨a, fs', b, c⟩
      · left
        refine ⟨j + 1, by omega, by rw [← hshift]; exact b, ?_, ?_⟩
        · intro j' hj'
          cases j' with
          | zero => exact hs
          | succ j' =>
            have := c j' (by omega)
            rwa [hshift] at this
        · rw [hrun]
          rcases d with ⟨e, k, h, f, g⟩ | ⟨e, fs', f, g⟩
          · left
            refine ⟨e, k, h, ?_, g⟩
            rw [← hshift]
            exact f
          · right
            refine ⟨by rw [← hshift]; exact e, fs', hgood j fs' f, ?_⟩
            rw [g, hshift]
      · right
        refine ⟨?_, fs', hgood (p + 1) fs' b, by rw [hrun, c]⟩
        intro j hj
        cases j with
        | zero => exact hs
        | succ j =>
          have := a j (by omega)
          rwa [hshift] at this

/-- `freeslot` after the walk up to `(t, j)`: what it was, or a dummy the walk passed. -/
def FsWalk (so : SetObj K) (u t0 t j : Nat) (fs0 fs : Option Nat) : Prop :=
  fs = fs0 ∨ ∃ t1 j1, t0 ≤ t1 ∧ ((t1 < t ∧ j1 ≤ linearProbes (spos so.mask u t1) so.mask) ∨
    (t1 = t ∧ j1 < j)) ∧ fs = some (spos so.mask u t1 + j1) ∧
    so.slot (spos so.mask u t1 + j1) = .dummy

open Classical in
theorem addOuter_walk (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) (u : Nat) :
    ∀ (fuel t : Nat) (fs : Option Nat),
      (∃ t', t ≤ t' ∧ t' < t + fuel ∧ ∃ j, j ≤ linearProbes (spos so.mask u t') so.mask ∧
        SStop so eqv key (spos so.mask u t' + j)) →
      ∃ t' j, t ≤ t' ∧ t' < t + fuel ∧ j ≤ linearProbes (spos so.mask u t') so.mask ∧
        SStop so eqv key (spos so.mask u t' + j) ∧
        (∀ t'', t ≤ t'' → t'' < t' → ∀ j', j' ≤ linearProbes (spos so.mask u t'') so.mask →
          ¬ SStop so eqv key (spos so.mask u t'' + j')) ∧
        (∀ j', j' < j → ¬ SStop so eqv key (spos so.mask u t' + j')) ∧
        ((addOuter P key (hf key) fuel (spos so.mask u t) (probeState so.mask u t).2 so.mask fs so =
            (.ok .active, so) ∧
            ∃ k h, so.slot (spos so.mask u t' + j) = .active k h ∧ eqv k key = true) ∨
         (so.slot (spos so.mask u t' + j) = .null ∧ ∃ fs', FsWalk so u t t' j fs fs' ∧
            addOuter P key (hf key) fuel (spos so.mask u t) (probeState so.mask u t).2 so.mask fs so =
              (.ok (.unused (spos so.mask u t' + j) fs' so.mask), so))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro t fs ⟨t', h1, h2, _⟩
    omega
  | succ fuel ih =>
    intro t fs hex
    rcases addScan_walk (P := P) H w key (linearProbes (spos so.mask u t) so.mask)
      (spos so.mask u t) fs with ⟨j, h1, h2, h3, h4⟩ | ⟨h1, fs1, h2, h3⟩
    · refine ⟨t, j, by omega, by omega, h1, h2, fun t'' a b => by omega, h3, ?_⟩
      rcases h4 with ⟨a, b⟩ | ⟨a, fs', b, c⟩
      · left
        refine ⟨?_, b⟩
        simp [addOuter, M.bind_run, a]
      · right
        refine ⟨a, fs', ?_, ?_⟩
        · rcases b with rfl | ⟨j', e, rfl, g⟩
          · exact Or.inl rfl
          · exact Or.inr ⟨t, j', by omega, Or.inr ⟨rfl, e⟩, rfl, g⟩
        · simp [addOuter, M.bind_run, c]
    · have hnext : ∃ t', t + 1 ≤ t' ∧ t' < t + 1 + fuel ∧ ∃ j,
          j ≤ linearProbes (spos so.mask u t') so.mask ∧ SStop so eqv key (spos so.mask u t' + j) := by
        obtain ⟨t', a, b, j, c, d⟩ := hex
        have hne : t' ≠ t := by
          intro he
          subst he
          exact h1 j c d
        exact ⟨t', by omega, by omega, j, c, d⟩
      obtain ⟨t', j, a, b, c, d, e, f, g⟩ := ih (t + 1) fs1 hnext
      have hn : setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2 =
          probeState so.mask u (t + 1) := by
        rw [setProbeStep_eq]
        rfl
      have hg : addOuter P key (hf key) (fuel + 1) (spos so.mask u t) (probeState so.mask u t).2
          so.mask fs so =
          addOuter P key (hf key) fuel (spos so.mask u (t + 1)) (probeState so.mask u (t + 1)).2
            so.mask fs1 so := by
        simp only [addOuter, M.bind_run, h3]
        show addOuter P key (hf key) fuel
          (setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2).1
          (setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2).2 so.mask fs1 so = _
        rw [hn]
        rfl
      refine ⟨t', j, by omega, by omega, c, d, ?_, f, ?_⟩
      · intro t'' h4 h5 j' h6
        by_cases he : t'' = t
        · subst he
          exact h1 j' h6
        · exact e t'' (by omega) h5 j' h6
      · rw [hg]
        rcases g with g | ⟨g1, fs', g2, g3⟩
        · exact Or.inl g
        · refine Or.inr ⟨g1, fs', ?_, g3⟩
          rcases g2 with rfl | ⟨t1, j1, g4, g5, g6, g7⟩
          · rcases h2 with rfl | ⟨j0, g4, rfl, g5⟩
            · exact Or.inl rfl
            · have hlt : t < t' := by omega
              exact Or.inr ⟨t, j0, by omega, Or.inl ⟨hlt, by omega⟩, rfl, g5⟩
          · exact Or.inr ⟨t1, j1, by omega, g5, g6, g7⟩

end Add

section Fields
variable {hf : K → Int} {eqv : K → K → Bool}

/-- `SetCore` depends on the mask, the table and the two counts, and on nothing else. -/
theorem SetCore.of_fields {so so' : SetObj K} (w : SetCore hf eqv so) (hm : so'.mask = so.mask)
    (ht : so'.table = so.table) (hf' : so'.fill = so.fill) (hu : so'.used = so.used) :
    SetCore hf eqv so' := by
  have hs : ∀ i, so'.slot i = so.slot i := fun i => by simp [SetObj.slot, ht]
  have he : setEntries so' = setEntries so := by simp [setEntries, ht]
  refine { log := hm ▸ w.log, len := by rw [ht, hm]; exact w.len, small := hm ▸ w.small
           reach := ?_, hashes := ?_, uniq := ?_, fill := ?_, used := ?_ }
  · intro s k h h1
    rw [hs] at h1
    obtain ⟨t, j, a, b, c, d⟩ := w.reach s k h h1
    rw [hm]
    exact ⟨t, j, a, b, c, NoNull.mono (so := so) (so' := so') hm (fun i hi => by rw [hs]; exact hi) d⟩
  · intro s k h h1
    rw [hs] at h1
    exact w.hashes s k h h1
  · intro s1 k1 h1 s2 k2 h2 a b c
    rw [hs] at a b
    exact w.uniq s1 k1 h1 s2 k2 h2 a b c
  · rw [hf', ht]
    exact w.fill
  · rw [hu, he]
    exact w.used

theorem SetCore.block_le {so : SetObj K} (w : SetCore hf eqv so) (u t j : Nat)
    (hj : j ≤ linearProbes (spos so.mask u t) so.mask) : spos so.mask u t + j ≤ so.mask := by
  have h1 := w.spos_lt u t
  simp only [linearProbes] at hj
  split at hj <;> omega

end Fields

section Insert
variable [DecidableEq K] {hf : K → Int} {eqv : K → K → Bool}

/-- Storing a new key at a slot that holds no entry, on the walk of its hash with no NULL before. -/
theorem setCore_ins (hsym : ∀ a b, eqv a b = eqv b a) (w : SetCore hf eqv so) (key : K) (t j : Nat)
    (ht : t < setProbeFuel so.mask)
    (hj : j ≤ linearProbes (spos so.mask (toU64 (hf key)) t) so.mask)
    (hnn : NoNull so (toU64 (hf key)) t j)
    (hold : slotEntry (so.slot (spos so.mask (toU64 (hf key)) t + j)) = none)
    (hne : ∀ s' k h, so.slot s' = .active k h → eqv k key = false)
    (fill' : Nat) :
    let s := spos so.mask (toU64 (hf key)) t + j
    let so' : SetObj K := { so with
      fill := fill', used := so.used + 1, table := so.table.set s (.active key (hf key)) }
    fill' = (so.table.set s (.active key (hf key))).countP (fun x => !x.isNull) →
    SetCore hf eqv so' ∧ (setEntries so').Perm ((key, hf key) :: setEntries so) := by
  intro s so' hfill
  have hle := w.block_le _ t j hj
  have hlt : s < so.table.length := by have := w.len; omega
  have hsl : ∀ i, so'.slot i = if i = s then .active key (hf key) else so.slot i := fun i => by
    have := slot_set so s i (.active key (hf key)) hlt
    simpa [so', SetObj.slot] using this
  have hne' : ∀ i, so.slot i ≠ .null → so'.slot i ≠ .null := by
    intro i hi
    rw [hsl]
    split
    · simp
    · exact hi
  have hback : ∀ i k' h', so'.slot i = .active k' h' →
      (i = s ∧ k' = key ∧ h' = hf key) ∨ (i ≠ s ∧ so.slot i = .active k' h') := by
    intro i k' h' hi
    rw [hsl] at hi
    split at hi
    · rename_i he
      simp only [Slot.active.injEq] at hi
      exact Or.inl ⟨he, hi.1.symm, hi.2.symm⟩
    · rename_i hn
      exact Or.inr ⟨hn, hi⟩
  have hp := filterMap_set_add (slotEntry (K := K)) (.active key (hf key)) (key, hf key) rfl
    so.table s hlt (by rw [slot_get so s hlt]; exact hold)
  refine ⟨{ log := w.log, small := w.small, len := by simp [so', w.len], reach := ?_, hashes := ?_,
            uniq := ?_, fill := hfill, used := ?_ }, hp⟩
  · intro i k' h' hi
    rcases hback i k' h' hi with ⟨rfl, rfl, rfl⟩ | ⟨_, hi2⟩
    · exact ⟨t, j, ht, hj, rfl, NoNull.mono (so := so) (so' := so') rfl hne' hnn⟩
    · obtain ⟨t', j', a, b, c, d⟩ := w.reach i k' h' hi2
      exact ⟨t', j', a, b, c, NoNull.mono (so := so) (so' := so') rfl hne' d⟩
  · intro i k' h' hi
    rcases hback i k' h' hi with ⟨_, rfl, rfl⟩ | ⟨_, hi2⟩
    · rfl
    · exact w.hashes i k' h' hi2
  · intro s1 k1 h1 s2 k2 h2 a b c
    rcases hback s1 k1 h1 a with ⟨r1, rfl, rfl⟩ | ⟨_, a'⟩ <;>
      rcases hback s2 k2 h2 b with ⟨r2, rfl, rfl⟩ | ⟨_, b'⟩
    · omega
    · rw [hsym, hne s2 k2 h2 b'] at c
      simp at c
    · rw [hne s1 k1 h1 a'] at c
      simp at c
    · exact w.uniq s1 k1 h1 s2 k2 h2 a' b' c
  · have hlen := hp.length_eq
    simp only [List.length_cons] at hlen
    have e1 : setEntries so' = (so.table.set s (.active key (hf key))).filterMap slotEntry := rfl
    have e2 : setEntries so = so.table.filterMap slotEntry := rfl
    show so.used + 1 = (setEntries so').length
    rw [w.used, e1, e2, hlen]

end Insert

section Clean
variable {hf : K → Int} {eqv : K → K → Bool}

theorem cleanScan_succ (t : List (Slot K)) (i j : Nat) :
    cleanScan t i (j + 1) =
      match t.getD (i + LINEAR_PROBES - j) .null with
      | .null => some (i + LINEAR_PROBES - j)
      | _ => cleanScan t i j := rfl

theorem cleanScan_walk (table : List (Slot K)) (i : Nat) : ∀ j, j ≤ LINEAR_PROBES →
    (∃ off, 10 - j ≤ off ∧ off ≤ 9 ∧ table.getD (i + off) .null = .null ∧
      (∀ off', 10 - j ≤ off' → off' < off → table.getD (i + off') .null ≠ .null) ∧
      cleanScan table i j = some (i + off)) ∨
    ((∀ off, 10 - j ≤ off → off ≤ 9 → table.getD (i + off) .null ≠ .null) ∧
      cleanScan table i j = none) := by
  intro j
  induction j with
  | zero =>
    intro _
    right
    exact ⟨fun off h1 h2 => by omega, rfl⟩
  | succ j ih =>
    intro hj
    have hl : LINEAR_PROBES = 9 := rfl
    have e : i + LINEAR_PROBES - j = i + (10 - (j + 1)) := by omega
    by_cases hn : table.getD (i + (10 - (j + 1))) .null = .null
    · left
      refine ⟨10 - (j + 1), by omega, by omega, hn, fun off' a b => by omega, ?_⟩
      rw [cleanScan_succ, e, hn]
    · have hs : cleanScan table i (j + 1) = cleanScan table i j := by
        rw [cleanScan_succ, e]
        cases hc : table.getD (i + (10 - (j + 1))) .null with
        | null => exact absurd hc hn
        | dummy => rfl
        | active k h => rfl
      rw [hs]
      rcases ih (by omega) with ⟨off, a, b, c, d, f⟩ | ⟨a, b⟩
      · left
        refine ⟨off, by omega, b, c, ?_, f⟩
        intro off' h1 h2
        by_cases he : off' = 10 - (j + 1)
        · rw [he]
          exact hn
        · exact d off' (by omega) h2
      · right
        refine ⟨?_, b⟩
        intro off h1 h2
        by_cases he : off = 10 - (j + 1)
        · rw [he]
          exact hn
        · exact a off (by omega) h2

/-- A step of `set_insert_clean` from a slot that is not NULL. -/
theorem cleanSlot_nonnull (t : List (Slot K)) (mask fuel i p : Nat) (h : t.getD i .null ≠ .null) :
    setInsertCleanSlot t mask (fuel + 1) i p =
      match (if i + LINEAR_PROBES ≤ mask then cleanScan t i LINEAR_PROBES else none) with
      | some s => .ok s
      | none =>
        setInsertCleanSlot t mask fuel (setProbeStep mask i p).1 (setProbeStep mask i p).2 := by
  simp only [setInsertCleanSlot]
  cases hc : t.getD i .null with
  | null => exact absurd hc h
  | dummy => rfl
  | active k e => rfl

open Classical in
/-- `set_insert_clean` stops at the first NULL on the walk. -/
theorem cleanSlot_walk (so : SetObj K) (u : Nat) :
    ∀ (fuel t : Nat),
      (∃ t', t ≤ t' ∧ t' < t + fuel ∧ ∃ j, j ≤ linearProbes (spos so.mask u t') so.mask ∧
        so.slot (spos so.mask u t' + j) = .null) →
      ∃ t' j, t ≤ t' ∧ t' < t + fuel ∧ j ≤ linearProbes (spos so.mask u t') so.mask ∧
        so.slot (spos so.mask u t' + j) = .null ∧
        (∀ t'', t ≤ t'' → t'' < t' → ∀ j', j' ≤ linearProbes (spos so.mask u t'') so.mask →
          so.slot (spos so.mask u t'' + j') ≠ .null) ∧
        (∀ j', j' < j → so.slot (spos so.mask u t' + j') ≠ .null) ∧
        setInsertCleanSlot so.table so.mask fuel (spos so.mask u t) (probeState so.mask u t).2 =
          .ok (spos so.mask u t' + j) := by
  intro fuel
  induction fuel with
  | zero =>
    intro t ⟨t', h1, h2, _⟩
    omega
  | succ fuel ih =>
    intro t hex
    have hsl : ∀ i, so.slot i = so.table.getD i .null := fun _ => rfl
    have hl9 : LINEAR_PROBES = 9 := rfl
    have hn : setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2 =
        probeState so.mask u (t + 1) := by
      rw [setProbeStep_eq]
      rfl
    by_cases h0 : so.slot (spos so.mask u t) = .null
    · refine ⟨t, 0, by omega, by omega, by omega, h0, fun t'' a b => by omega,
        fun j' h => by omega, ?_⟩
      have h0' : so.table.getD (spos so.mask u t) .null = .null := (hsl _).symm.trans h0
      simp only [setInsertCleanSlot, h0']
      rfl
    · have hstep := cleanSlot_nonnull so.table so.mask fuel (spos so.mask u t)
        (probeState so.mask u t).2 (by rw [← hsl]; exact h0)
      have goOn : (∀ j, j ≤ linearProbes (spos so.mask u t) so.mask →
            so.slot (spos so.mask u t + j) ≠ .null) →
          (if spos so.mask u t + LINEAR_PROBES ≤ so.mask then
            cleanScan so.table (spos so.mask u t) LINEAR_PROBES else none) = none →
          ∃ t' j, t ≤ t' ∧ t' < t + (fuel + 1) ∧ j ≤ linearProbes (spos so.mask u t') so.mask ∧
            so.slot (spos so.mask u t' + j) = .null ∧
            (∀ t'', t ≤ t'' → t'' < t' → ∀ j', j' ≤ linearProbes (spos so.mask u t'') so.mask →
              so.slot (spos so.mask u t'' + j') ≠ .null) ∧
            (∀ j', j' < j → so.slot (spos so.mask u t' + j') ≠ .null) ∧
            setInsertCleanSlot so.table so.mask (fuel + 1) (spos so.mask u t)
              (probeState so.mask u t).2 = .ok (spos so.mask u t' + j) := by
        intro hall hnone
        obtain ⟨t', a, b, j, c, d⟩ := hex
        have hne : t' ≠ t := fun he => by
          subst he
          exact hall j c d
        obtain ⟨t2, j2, e1, e2, e3, e4, e5, e6, e7⟩ :=
          ih (t + 1) ⟨t', by omega, by omega, j, c, d⟩
        refine ⟨t2, j2, by omega, by omega, e3, e4, ?_, e6, ?_⟩
        · intro t'' h1 h2 j' h3
          by_cases he : t'' = t
          · subst he
            exact hall j' h3
          · exact e5 t'' (by omega) h2 j' h3
        · rw [hstep, hnone]
          simp only [hn]
          exact e7
      by_cases hl : spos so.mask u t + LINEAR_PROBES ≤ so.mask
      · rcases cleanScan_walk so.table (spos so.mask u t) LINEAR_PROBES (Nat.le_refl _) with
          ⟨off, a, b, c, d, f⟩ | ⟨a, b⟩
        · refine ⟨t, off, by omega, by omega, ?_, (hsl _).trans c, fun t'' a b => by omega, ?_, ?_⟩
          · simp only [linearProbes, if_pos hl]
            exact b
          · intro j' hj' hnull
            by_cases hz : j' = 0
            · subst hz
              exact h0 hnull
            · exact d j' (by omega) hj' ((hsl _).symm.trans hnull)
          · rw [hstep, if_pos hl, f]
        · apply goOn
          · intro j hj hnull
            simp only [linearProbes, if_pos hl] at hj
            by_cases hz : j = 0
            · subst hz
              exact h0 hnull
            · exact a j (by omega) hj ((hsl _).symm.trans hnull)
          · rw [if_pos hl, b]
      · apply goOn
        · intro j hj hnull
          simp only [linearProbes, if_neg hl] at hj
          have hz : j = 0 := by omega
          subst hz
          exact h0 hnull
        · rw [if_neg hl]

end Clean

section Resize
variable [DecidableEq K] {hf : K → Int} {eqv : K → K → Bool}

/-- A set object with this table and `n` entries, none of them dummies. -/
def withT (so : SetObj K) (m : Nat) (t : List (Slot K)) (n : Nat) : SetObj K :=
  { so with mask := m, table := t, fill := n, used := n }

omit [DecidableEq K] in
theorem slot_active_iff (so : SetObj K) (i : Nat) (k : K) (h : Int) :
    so.slot i = .active k h ↔ so.table[i]? = some (.active k h) := by
  simp only [SetObj.slot, List.getD]
  cases hg : so.table[i]? with
  | none => simp
  | some x => simp

omit [DecidableEq K] in
theorem mem_filterMap_slot (l : List (Slot K)) (x : K × Int) (h : x ∈ l.filterMap slotEntry) :
    ∃ j : Nat, l[j]? = some (Slot.active x.1 x.2) := by
  obtain ⟨y, hy, hq⟩ := List.mem_filterMap.mp h
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  refine ⟨j, ?_⟩
  cases hc : l[j] with
  | null => simp [hc] at hq
  | dummy => simp [hc] at hq
  | active k' h' =>
    simp only [hc, Option.some.injEq] at hq
    subst hq
    simp [hj, hc]

omit [DecidableEq K] in
theorem table_pairwise {eqv : K → K → Bool} : ∀ l : List (Slot K),
    (∀ (i j : Nat) (k1 : K) (h1 : Int) (k2 : K) (h2 : Int), l[i]? = some (Slot.active k1 h1) →
      l[j]? = some (Slot.active k2 h2) → eqv k1 k2 = true → i = j) →
    (l.filterMap slotEntry).Pairwise (fun a b => eqv a.1 b.1 = false) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
    intro hu
    have ht := ih (fun i j k1 h1 k2 h2 a' b c => by
      have := hu (i + 1) (j + 1) k1 h1 k2 h2 (by simpa using a') (by simpa using b) c
      omega)
    cases a with
    | null => simpa using ht
    | dummy => simpa using ht
    | active k h =>
      simp only [List.filterMap_cons]
      refine List.pairwise_cons.mpr ⟨?_, ht⟩
      intro e he
      obtain ⟨j, hj⟩ := mem_filterMap_slot t e he
      cases hq : eqv k e.1 with
      | false => rfl
      | true =>
        have := hu 0 (j + 1) k h e.1 e.2 (by simp) (by simpa using hj) hq
        omega

/-- `set_table_resize`'s copy loop (@3.14.7:359-372): every entry goes to the first NULL on its walk. -/
theorem reinsert_spec (hsym : ∀ a b, eqv a b = eqv b a) (so : SetObj K) (m : Nat) :
    ∀ (src acc : List (Slot K)) (n : Nat),
      SetCore hf eqv (withT so m acc n) →
      n + (src.filterMap slotEntry).length ≤ m →
      (∀ e ∈ src.filterMap slotEntry, e.2 = hf e.1) →
      (src.filterMap slotEntry).Pairwise (fun a b => eqv a.1 b.1 = false) →
      (∀ e ∈ src.filterMap slotEntry, ∀ s k h,
        (withT so m acc n).slot s = .active k h → eqv k e.1 = false) →
      ∃ t, reinsertAll m acc src = .ok t ∧
        SetCore hf eqv (withT so m t (n + (src.filterMap slotEntry).length)) ∧
        (t.filterMap slotEntry).Perm (src.filterMap slotEntry ++ acc.filterMap slotEntry) := by
  intro src
  induction src with
  | nil =>
    intro acc n w _ _ _ _
    exact ⟨acc, rfl, w, by simp⟩
  | cons x rest ih =>
    intro acc n w hroom hh hp hne
    cases x with
    | null =>
      have := ih acc n w (by simpa using hroom) (by simpa using hh) (by simpa using hp)
        (by simpa using hne)
      simpa [reinsertAll] using this
    | dummy =>
      have := ih acc n w (by simpa using hroom) (by simpa using hh) (by simpa using hp)
        (by simpa using hne)
      simpa [reinsertAll] using this
    | active k h =>
      have hcons : (Slot.active k h :: rest).filterMap slotEntry =
          (k, h) :: rest.filterMap slotEntry := rfl
      rw [hcons] at hroom hh hp hne ⊢
      simp only [List.length_cons] at hroom ⊢
      have hh0 : h = hf k := hh (k, h) (by simp)
      subst hh0
      have hrest := List.pairwise_cons.mp hp
      let A := withT so m acc n
      have hfree : A.fill ≤ A.mask := by
        show n ≤ m
        omega
      let u := toU64 (hf k)
      obtain ⟨t0, ht0, hn0⟩ := w.null_on_walk hfree u (toU64_lt _)
      obtain ⟨t', j, _, a, b, c, d, e, f⟩ := cleanSlot_walk A u (setProbeFuel A.mask) 0
        ⟨t0, Nat.zero_le _, by rw [Nat.zero_add]; exact ht0, 0, Nat.zero_le _, hn0⟩
      have f' : setInsertCleanSlot acc m (setProbeFuel m) (toU64 (hf k) &&& m) (toU64 (hf k)) =
          .ok (spos m u t' + j) := f
      have hnn : NoNull A u t' j := ⟨fun t'' h1 j' h2 => d t'' (by omega) h1 j' h2, e⟩
      have hle : spos A.mask u t' + j ≤ A.mask := w.block_le u t' j b
      have hlt : spos m u t' + j < acc.length := by
        have hl : A.table.length = A.mask + 1 := w.len
        show spos A.mask u t' + j < A.table.length
        omega
      have hcount := countP_set_up (fun x : Slot K => !x.isNull) (.active k (hf k)) acc
        (spos m u t' + j) hlt
        (by
          have : acc[spos m u t' + j] = .null := by
            have h2 : acc[spos m u t' + j] = A.slot (spos m u t' + j) :=
              slot_get A (spos m u t' + j) hlt
            exact h2.trans c
          rw [this]
          rfl) rfl
      have hfill : n + 1 = (acc.set (spos m u t' + j) (.active k (hf k))).countP (fun x => !x.isNull) := by
        rw [hcount]
        have : n = acc.countP (fun x => !x.isNull) := w.fill
        omega
      obtain ⟨g1, g2⟩ := setCore_ins hsym w k t' j (by simpa using a) b hnn
        (by
          show slotEntry (A.slot (spos A.mask u t' + j)) = none
          rw [c])
        (fun s' k' h' hs => hne (k, hf k) (by simp) s' k' h' hs) (n + 1) hfill
      let acc' := acc.set (spos m u t' + j) (.active k (hf k))
      have w' : SetCore hf eqv (withT so m acc' (n + 1)) :=
        g1.of_fields rfl rfl rfl rfl
      have hslot : ∀ i, (withT so m acc' (n + 1)).slot i =
          if i = spos m u t' + j then .active k (hf k) else A.slot i := fun i => by
        have := slot_set A (spos m u t' + j) i (.active k (hf k)) hlt
        simpa [A, withT, acc', SetObj.slot] using this
      have hne' : ∀ e ∈ rest.filterMap slotEntry, ∀ s k' h,
          (withT so m acc' (n + 1)).slot s = .active k' h → eqv k' e.1 = false := by
        intro e he s k' h' hs
        rw [hslot] at hs
        split at hs
        · simp only [Slot.active.injEq] at hs
          rw [← hs.1]
          exact hrest.1 e he
        · exact hne e (by simp [he]) s k' h' hs
      obtain ⟨t, r1, r2, r3⟩ := ih acc' (n + 1) w' (by omega)
        (fun e he => hh e (by simp [he])) hrest.2 hne'
      refine ⟨t, ?_, ?_, ?_⟩
      · simp only [reinsertAll, setInsertClean, f']
        exact r1
      · have e1 : n + 1 + (rest.filterMap slotEntry).length =
            n + ((rest.filterMap slotEntry).length + 1) := by omega
        rw [← e1]
        exact r2
      · have hg2 : (acc'.filterMap slotEntry).Perm ((k, hf k) :: acc.filterMap slotEntry) := g2
        refine r3.trans ?_
        have := (List.Perm.append_left (rest.filterMap slotEntry) hg2)
        refine this.trans ?_
        exact List.perm_middle

theorem setNewSize_stop (m : Nat) : ∀ (f n : Nat), 0 < n →
    (m < setNewSize m f n ∨ setNewSize m f n = n * 2 ^ f) ∧ ∃ k, setNewSize m f n = n * 2 ^ k := by
  intro f
  induction f with
  | zero =>
    intro n _
    exact ⟨Or.inr (by simp [setNewSize]), 0, by simp [setNewSize]⟩
  | succ f ih =>
    intro n hn
    by_cases hle : n ≤ m
    · have e : setNewSize m (f + 1) n = setNewSize m f (n * 2) := by
        simp [setNewSize, hle, Nat.shiftLeft_eq]
      rw [e]
      obtain ⟨a, k, c⟩ := ih (n * 2) (by omega)
      refine ⟨?_, k + 1, ?_⟩
      · rcases a with a | a
        · exact Or.inl a
        · refine Or.inr ?_
          rw [a, Nat.pow_succ]
          simp [Nat.mul_assoc, Nat.mul_comm]
      · rw [c, Nat.pow_succ]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    · have e : setNewSize m (f + 1) n = n := by
        simp [setNewSize, hle]
      rw [e]
      exact ⟨Or.inl (by omega), 0, by simp⟩

/-- The table `set_table_resize` would pick for `minused` is more than `PyMem_NEW` can give (@3.14.7:343). -/
def SetResizeRefused (minused : Nat) : Prop :=
  (2 ^ 63 - 1) / 16 < setNewSize minused 64 PySet_MINSIZE

/-- `set_table_resize`, from any table that may have reached the load limit, with no assumption on
the size asked for: it refuses a table it cannot allocate, and otherwise gives a table within the
load limit that holds the same entries. The hypothesis is what every call site passes. -/
theorem setTableResize_spec (hsym : ∀ a b, eqv a b = eqv b a) (so : SetObj K)
    (w : SetCore hf eqv so) (minused : Nat) (hmin : so.used * 2 ≤ minused) :
    (SetResizeRefused minused ∧ setTableResize minused so = (.error memoryError, so)) ∨
    ∃ so', setTableResize minused so = (.ok (), so') ∧ SetWF hf eqv so' ∧
      (setEntries so').Perm (setEntries so) ∧ so'.peers = so.peers ∧ so'.ident = so.ident ∧
      minused ≤ so'.mask := by
  let r := setNewSize minused 64 PySet_MINSIZE
  obtain ⟨hstop, k, hk⟩ := setNewSize_stop minused 64 PySet_MINSIZE (by decide)
  have hr : setNewSize minused 64 PySet_MINSIZE = r := rfl
  rw [hr] at hstop hk
  have h8 : (PySet_MINSIZE : Nat) = 8 := rfl
  have hge : 8 ≤ r := by
    rw [hk, h8]
    have := Nat.pow_pos (a := 2) (n := k) (by omega)
    have hm := Nat.le_mul_of_pos_right 8 this
    exact hm
  by_cases hno : (r = PySet_MINSIZE ∧ so.mask + 1 = PySet_MINSIZE) ∧ so.fill = so.used
  · right
    have h1 : r = 8 := hno.1.1.trans h8
    have h2 : so.mask + 1 = 8 := hno.1.2.trans h8
    have h3 : so.fill = so.used := hno.2
    have hm : minused < 8 := by
      rcases hstop with a | a
      · omega
      · rw [h1, h8] at a
        omega
    refine ⟨so, ?_, { toSetCore := w, load := by omega }, List.Perm.refl _, rfl, rfl, by omega⟩
    simp [setTableResize, M.bind_run, M.get_run, hr, hno]
  · by_cases hbig : 576460752303423487 < r
    · left
      refine ⟨?_, ?_⟩
      · unfold SetResizeRefused
        rw [hr]
        omega
      · simp [setTableResize, M.bind_run, M.get_run, hr, hno, hbig, memoryError]
    · right
      have hlim : r ≤ 576460752303423487 := by omega
      have hm : minused < r := by
        rcases hstop with a | a
        · exact a
        · exfalso
          rw [a, h8] at hlim
          exact absurd hlim (by decide)
      let m := r - 1
      let so0 := withT so m (List.replicate r .null) 0
      have hrm : m + 1 = r := by omega
      have hslot0 : ∀ i, so0.slot i = .null := by
        intro i
        simp only [SetObj.slot, so0, withT, List.getD]
        by_cases hi : i < r <;> simp [List.getElem?_replicate, hi]
      have hent0 : (List.replicate r (Slot.null : Slot K)).filterMap slotEntry = [] := by
        simp [List.filterMap_replicate]
      have w0 : SetCore hf eqv so0 :=
        { log := ⟨k + 3, by
            show m + 1 = _
            rw [hrm, hk, h8, Nat.pow_add]
            simp [Nat.mul_comm]⟩
          len := by
            show (List.replicate r (Slot.null : Slot K)).length = m + 1
            rw [hrm]
            simp
          small := by
            show 7 ≤ m
            omega
          reach := fun s k' h hs => by
            rw [hslot0] at hs
            simp at hs
          hashes := fun s k' h hs => by
            rw [hslot0] at hs
            simp at hs
          uniq := fun s1 k1 h1 s2 k2 h2 a _ _ => by
            rw [hslot0] at a
            simp at a
          fill := by
            show 0 = (List.replicate r (Slot.null : Slot K)).countP _
            simp [List.countP_replicate, Slot.isNull]
          used := by
            show 0 = ((List.replicate r (Slot.null : Slot K)).filterMap slotEntry).length
            rw [hent0]
            rfl }
      have huniq : (so.table.filterMap slotEntry).Pairwise (fun a b => eqv a.1 b.1 = false) :=
        table_pairwise so.table (fun i j k1 h1 k2 h2 a b c =>
          w.uniq i k1 h1 j k2 h2 ((slot_active_iff so i k1 h1).mpr a)
            ((slot_active_iff so j k2 h2).mpr b) c)
      have hlen : (so.table.filterMap slotEntry).length = so.used := w.used.symm
      have hhash : ∀ e ∈ so.table.filterMap slotEntry, e.2 = hf e.1 := by
        intro e he
        obtain ⟨j, hj⟩ := mem_filterMap_slot so.table e he
        exact w.hashes j e.1 e.2 ((slot_active_iff so j e.1 e.2).mpr hj)
      obtain ⟨t, r1, r2, r3⟩ := reinsert_spec hsym so m so.table (List.replicate r .null) 0 w0
        (by rw [hlen]; omega) hhash huniq
        (fun e _ s k' h hs => by
          rw [hslot0] at hs
          simp at hs)
      rw [hent0, List.append_nil] at r3
      rw [hlen] at r2
      simp only [Nat.zero_add] at r2
      let so' : SetObj K := { so with
        mask := m, table := t, fill := so.used
        tableId := if r == PySet_MINSIZE then 0 else so.nextId
        nextId := so.nextId + 1 }
      refine ⟨so', ?_, ?_, r3, rfl, rfl, ?_⟩
      · have hr1 : reinsertAll (r - 1) (List.replicate r Slot.null) so.table = .ok t := r1
        simp [setTableResize, M.bind_run, M.get_run, M.lift_run, hr, hno, hbig, hr1, so', m]
      · exact { toSetCore := r2.of_fields rfl rfl rfl rfl
                load := by
                  show so.used * 5 < m * 3
                  omega }
      · show minused ≤ m
        omega

end Resize

end PyLean.DictSet
