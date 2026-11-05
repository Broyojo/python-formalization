import PyLean.DictSet.SetProps
import PyLean.DictSet.Probe

/-!
The probing invariant of a set table.

A set probes in blocks: an outer step `t` picks a position on the sequence dicts use, and the block
at that position scans up to ten neighbouring slots (`LINEAR_PROBES` plus the first). `NoNull` says
that no NULL slot comes before a position on that walk. A key in the table is on the walk of its
hash with none before it. As with dicts, this is why a deleted slot becomes `dummy` and not NULL.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type}

theorem setProbeStep_eq (mask i p : Nat) : setProbeStep mask i p = probeStep mask i p := by
  simp only [setProbeStep, probeStep]
  have h : i * 5 + 1 + p >>> PERTURB_SHIFT = i * 5 + p >>> PERTURB_SHIFT + 1 := by omega
  rw [h, Nat.and_comm]

/-- The start of the block of outer step `t`. -/
def spos (mask u t : Nat) : Nat := (probeState mask u t).1

def Slot.isNull : Slot K → Bool
  | .null => true
  | _ => false

/-- No NULL slot before offset `j` of the block of outer step `t`. -/
def NoNull (so : SetObj K) (u t j : Nat) : Prop :=
  (∀ t', t' < t → ∀ j', j' ≤ linearProbes (spos so.mask u t') so.mask →
    so.slot (spos so.mask u t' + j') ≠ .null) ∧
  (∀ j', j' < j → so.slot (spos so.mask u t + j') ≠ .null)

/-- What a set table satisfies at every moment, including the moment in `set_add_entry` after the
store and before the resize. -/
structure SetCore (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K) : Prop where
  log : ∃ n, so.mask + 1 = 2 ^ n
  len : so.table.length = so.mask + 1
  small : 7 ≤ so.mask
  reach : ∀ s k h, so.slot s = .active k h → ∃ t j, t < setProbeFuel so.mask ∧
    j ≤ linearProbes (spos so.mask (toU64 h) t) so.mask ∧ spos so.mask (toU64 h) t + j = s ∧
    NoNull so (toU64 h) t j
  hashes : ∀ s k h, so.slot s = .active k h → h = hf k
  uniq : ∀ s1 k1 h1 s2 k2 h2, so.slot s1 = .active k1 h1 → so.slot s2 = .active k2 h2 →
    eqv k1 k2 = true → s1 = s2
  fill : so.fill = so.table.countP (fun x => !x.isNull)
  used : so.used = (setEntries so).length

/-- The invariant of a set table between operations: the load also leaves a NULL slot. -/
structure SetWF (hf : K → Int) (eqv : K → K → Bool) (so : SetObj K) : Prop extends
    SetCore hf eqv so where
  load : so.fill * 5 < so.mask * 3

section Null
variable {hf : K → Int} {eqv : K → K → Bool}

/-- A table with fewer filled slots than slots has a NULL one, which is what ends a failing search
(:517-519). -/
theorem SetCore.exists_null {so : SetObj K} (w : SetCore hf eqv so) (hfree : so.fill ≤ so.mask) :
    ∃ s, s ≤ so.mask ∧ so.slot s = .null := by
  apply Classical.byContradiction
  intro hn
  have hall : ∀ x ∈ so.table, (!x.isNull) = true := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    have hi' : i ≤ so.mask := by have := w.len; omega
    cases hq : so.table[i] with
    | null =>
      exact absurd ⟨i, hi', by simp [SetObj.slot, List.getD, hi, hq]⟩ hn
    | dummy => rfl
    | active k h => rfl
  have hc := List.countP_eq_length.mpr hall
  have h1 := w.fill
  have h3 := w.len
  omega

/-- Every outer step starts inside the table. -/
theorem SetCore.spos_lt {so : SetObj K} (w : SetCore hf eqv so) (u t : Nat) :
    spos so.mask u t ≤ so.mask := by
  obtain ⟨n, hn⟩ := w.log
  have hm : so.mask = 2 ^ n - 1 := by omega
  have := probe_lt n u t
  simp only [spos]
  rw [hm]
  omega

/-- A NULL slot is on every walk within the fuel. -/
theorem SetCore.null_on_walk {so : SetObj K} (w : SetCore hf eqv so) (hfree : so.fill ≤ so.mask)
    (u : Nat) (hu : u < 2 ^ 64) :
    ∃ t, t < setProbeFuel so.mask ∧ so.slot (spos so.mask u t) = .null := by
  obtain ⟨n, hn⟩ := w.log
  obtain ⟨s, hs, hnull⟩ := w.exists_null hfree
  have hm : so.mask = 2 ^ n - 1 := by omega
  obtain ⟨t, ht, hp⟩ := probe_reaches_all n u s hu (by omega)
  refine ⟨t, ?_, ?_⟩
  · simp only [setProbeFuel]
    omega
  · simp only [spos]
    rw [hm, hp, ← hnull]

theorem SetWF.null_on_walk {so : SetObj K} (w : SetWF hf eqv so) (u : Nat) (hu : u < 2 ^ 64) :
    ∃ t, t < setProbeFuel so.mask ∧ so.slot (spos so.mask u t) = .null := by
  have h1 := w.load
  exact w.toSetCore.null_on_walk (by omega) u hu

end Null

section Look
variable [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}

theorem setChanged_same (so : SetObj K) (slot : Nat) (k : K) (h : Int)
    (hs : so.slot slot = .active k h) : setChanged so so.tableId slot k = false := by
  simp [setChanged, hs]

/-- Where a search for `key` stops. -/
def SStop (so : SetObj K) (eqv : K → K → Bool) (key : K) (s : Nat) : Prop :=
  so.slot s = .null ∨ ∃ k h, so.slot s = .active k h ∧ eqv k key = true

theorem lookStep_stop (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (fr : Bool) (key : K) (slot : Nat)
    (hst : SStop so eqv key slot) :
    lookStep P fr key (hf key) slot so = (.ok (.inl (.found slot)), so) := by
  rcases hst with hn | ⟨k, h, hs, heq⟩
  · cases fr <;> simp [lookStep, compareFrozen, compareLocked, M.bind_run, M.get_run, hn]
  · have hh : h = hf key := (w.hashes slot k h hs).trans (H.hash_cons _ _ heq)
    subst hh
    have hc := setChanged_same so slot k _ hs
    by_cases h1 : k = key
    · cases fr <;> simp [lookStep, compareFrozen, compareLocked, M.bind_run, M.get_run, hs, h1]
    · by_cases h2 : (P.isStr k = true ∧ P.isStr key = true) ∧ P.strEq k key = true
      · cases fr
        · simp [lookStep, compareLocked, M.bind_run, M.get_run, hs, h1, h2]
        · simp [lookStep, compareFrozen, M.bind_run, M.get_run, hs, h1, H.eq_ok, heq]
      · cases fr <;> simp [lookStep, compareFrozen, compareLocked, M.bind_run, M.get_run, hs, h1, h2,
          H.eq_ok, heq, hc]

theorem lookStep_pass (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (fr : Bool) (key : K) (slot : Nat)
    (hst : ¬ SStop so eqv key slot) :
    lookStep P fr key (hf key) slot so = (.ok (.inr ()), so) := by
  cases hs : so.slot slot with
  | null => exact absurd (Or.inl hs) hst
  | dummy => cases fr <;> simp [lookStep, compareFrozen, compareLocked, M.bind_run, M.get_run, hs]
  | active k h =>
    have hne : eqv k key = false := by
      cases hq : eqv k key with
      | false => rfl
      | true => exact absurd (Or.inr ⟨k, h, hs, hq⟩) hst
    have hc := setChanged_same so slot k h hs
    have h1 : k ≠ key := by
      intro he
      rw [he, H.refl] at hne
      simp at hne
    by_cases hh : h = hf key
    · have h2 : ¬ ((P.isStr k = true ∧ P.isStr key = true) ∧ P.strEq k key = true) := by
        rintro ⟨⟨h3, h4⟩, h5⟩
        rw [H.str_eq _ _ h3 h4, hne] at h5
        simp at h5
      cases fr <;> simp [lookStep, compareFrozen, compareLocked, M.bind_run, M.get_run, hs, hh, h1, h2,
        H.eq_ok, hne, hc]
    · cases fr <;> simp [lookStep, compareFrozen, compareLocked, M.bind_run, M.get_run, hs, hh, h1]

open Classical in
/-- One block of `set_lookkey`: it stops at the first stop in the block, or goes on. -/
theorem lookScan_walk (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (fr : Bool) (key : K) :
    ∀ (p slot : Nat),
      (∃ j, j ≤ p ∧ SStop so eqv key (slot + j) ∧ (∀ j', j' < j → ¬ SStop so eqv key (slot + j')) ∧
        lookScan P fr key (hf key) p slot so = (.ok (.found (slot + j)), so)) ∨
      ((∀ j, j ≤ p → ¬ SStop so eqv key (slot + j)) ∧
        lookScan P fr key (hf key) p slot so = (.ok .next, so)) := by
  intro p
  induction p with
  | zero =>
    intro slot
    by_cases hs : SStop so eqv key slot
    · left
      refine ⟨0, by omega, hs, fun j' h => by omega, ?_⟩
      simp [lookScan, M.bind_run, lookStep_stop H w fr key slot hs]
    · right
      refine ⟨fun j h => ?_, ?_⟩
      · have : j = 0 := by omega
        subst this
        exact hs
      · simp [lookScan, M.bind_run, lookStep_pass H w fr key slot hs]
  | succ p ih =>
    intro slot
    by_cases hs : SStop so eqv key slot
    · left
      refine ⟨0, by omega, hs, fun j' h => by omega, ?_⟩
      simp [lookScan, M.bind_run, lookStep_stop H w fr key slot hs]
    · have hstep : lookScan P fr key (hf key) (p + 1) slot so =
          lookScan P fr key (hf key) p (slot + 1) so := by
        simp [lookScan, M.bind_run, lookStep_pass H w fr key slot hs]
      have hshift : ∀ j, slot + 1 + j = slot + (j + 1) := fun j => by omega
      rcases ih (slot + 1) with ⟨j, h1, h2, h3, h4⟩ | ⟨h1, h2⟩
      · left
        refine ⟨j + 1, by omega, by rw [← hshift]; exact h2, ?_, ?_⟩
        · intro j' hj'
          cases j' with
          | zero => exact hs
          | succ j' =>
            have := h3 j' (by omega)
            rwa [hshift] at this
        · rw [hstep, h4, hshift]
      · right
        refine ⟨?_, by rw [hstep, h2]⟩
        intro j hj
        cases j with
        | zero => exact hs
        | succ j =>
          have := h1 j (by omega)
          rwa [hshift] at this

open Classical in
/-- The outer loop of `set_lookkey`: if a stop lies on the walk within the fuel, the search ends at
the first one and changes nothing. -/
theorem lookOuter_walk (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (fr : Bool) (key : K)
    (u : Nat) :
    ∀ (fuel t : Nat),
      (∃ t', t ≤ t' ∧ t' < t + fuel ∧ ∃ j, j ≤ linearProbes (spos so.mask u t') so.mask ∧
        SStop so eqv key (spos so.mask u t' + j)) →
      ∃ t' j, t ≤ t' ∧ t' < t + fuel ∧ j ≤ linearProbes (spos so.mask u t') so.mask ∧
        SStop so eqv key (spos so.mask u t' + j) ∧
        (∀ t'', t ≤ t'' → t'' < t' → ∀ j', j' ≤ linearProbes (spos so.mask u t'') so.mask →
          ¬ SStop so eqv key (spos so.mask u t'' + j')) ∧
        (∀ j', j' < j → ¬ SStop so eqv key (spos so.mask u t' + j')) ∧
        lookOuter P fr key (hf key) so.mask fuel (spos so.mask u t) (probeState so.mask u t).2 so =
          (.ok (some (spos so.mask u t' + j)), so) := by
  intro fuel
  induction fuel with
  | zero =>
    intro t ⟨t', h1, h2, _⟩
    omega
  | succ fuel ih =>
    intro t hex
    rcases lookScan_walk (P := P) H w fr key (linearProbes (spos so.mask u t) so.mask)
      (spos so.mask u t) with ⟨j, h1, h2, h3, h4⟩ | ⟨h1, h2⟩
    · refine ⟨t, j, by omega, by omega, h1, h2, fun t'' a b => by omega, h3, ?_⟩
      simp [lookOuter, M.bind_run, h4]
    · have hnext : ∃ t', t + 1 ≤ t' ∧ t' < t + 1 + fuel ∧ ∃ j,
          j ≤ linearProbes (spos so.mask u t') so.mask ∧ SStop so eqv key (spos so.mask u t' + j) := by
        obtain ⟨t', a, b, j, c, d⟩ := hex
        have hne : t' ≠ t := by
          intro he
          subst he
          exact h1 j c d
        exact ⟨t', by omega, by omega, j, c, d⟩
      obtain ⟨t', j, a, b, c, d, e, f, g⟩ := ih (t + 1) hnext
      refine ⟨t', j, by omega, by omega, c, d, ?_, f, ?_⟩
      · intro t'' h3 h4 j' h5
        by_cases he : t'' = t
        · subst he
          exact h1 j' h5
        · exact e t'' (by omega) h4 j' h5
      · have hn : setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2 =
            probeState so.mask u (t + 1) := by
          rw [setProbeStep_eq]
          rfl
        have hg : lookOuter P fr key (hf key) so.mask (fuel + 1) (spos so.mask u t)
            (probeState so.mask u t).2 so =
            lookOuter P fr key (hf key) so.mask fuel (spos so.mask u (t + 1))
              (probeState so.mask u (t + 1)).2 so := by
          simp only [lookOuter, M.bind_run, h2]
          show lookOuter P fr key (hf key) so.mask fuel
            (setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2).1
            (setProbeStep so.mask (spos so.mask u t) (probeState so.mask u t).2).2 so = _
          rw [hn]
          rfl
        rw [hg]
        exact g

theorem setLookkeyAux_ok (n : Nat) (so : SetObj K) (s : Nat) {key : K} {hash : Int}
    (h : lookOuter P false key hash so.mask (setProbeFuel so.mask) (toU64 hash &&& so.mask)
      (toU64 hash) so = (.ok (some s), so)) :
    setLookkeyAux P key hash (n + 1) so = (.ok s, so) := by
  simp only [setLookkeyAux, M.bind_run, M.get_run]
  simp [h]

/-- `set_do_lookup`, with either compare function, in the outcomes that matter: it changes nothing,
and it stops at a NULL only when no equal key is in the table. -/
theorem lookOuter_spec (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (fr : Bool) (key : K) :
    ∃ s, lookOuter P fr key (hf key) so.mask (setProbeFuel so.mask) (toU64 (hf key) &&& so.mask)
        (toU64 (hf key)) so = (.ok (some s), so) ∧
      ((so.slot s = .null ∧ ∀ s' k h, so.slot s' = .active k h → eqv k key = false) ∨
       ∃ k h, so.slot s = .active k h ∧ eqv k key = true) := by
  let u := toU64 (hf key)
  obtain ⟨t0, ht0, hn0⟩ := w.null_on_walk u (toU64_lt _)
  obtain ⟨t, j, _, a, b, c, d, e, f⟩ := lookOuter_walk (P := P) H w fr key u
    (setProbeFuel so.mask) 0 ⟨t0, by omega, by omega, 0, by omega, Or.inl hn0⟩
  have f' : lookOuter P fr key (hf key) so.mask (setProbeFuel so.mask)
      (toU64 (hf key) &&& so.mask) (toU64 (hf key)) so =
      (.ok (some (spos so.mask u t + j)), so) := f
  refine ⟨spos so.mask u t + j, f', ?_⟩
  · rcases c with hnull | ⟨k, h, hs, heq⟩
    · left
      refine ⟨hnull, ?_⟩
      intro s' k h hs'
      cases hq : eqv k key with
      | false => rfl
      | true =>
        exfalso
        have hhash : toU64 h = u := by
          simp only [u]
          rw [w.hashes s' k h hs', H.hash_cons _ _ hq]
        obtain ⟨t', j', _, h2, h3, h4⟩ := w.reach s' k h hs'
        rw [hhash] at h2 h3 h4
        have hstop : SStop so eqv key (spos so.mask u t' + j') := by
          rw [h3]
          exact Or.inr ⟨k, h, hs', hq⟩
        by_cases hlt : t' < t
        · exact d t' (by omega) hlt j' h2 hstop
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
                rw [h3] at hnull
                rw [hs'] at hnull
                simp at hnull
    · exact Or.inr ⟨k, h, hs, heq⟩

/-- `set_lookkey`: `set_do_lookup` with the compare function the object's type selects. -/
theorem setLookkey_spec (H : HonestSet P hf eqv) (w : SetWF hf eqv so) (key : K) :
    ∃ s, setLookkey P key (hf key) so = (.ok s, so) ∧
      ((so.slot s = .null ∧ ∀ s' k h, so.slot s' = .active k h → eqv k key = false) ∨
       ∃ k h, so.slot s = .active k h ∧ eqv k key = true) := by
  cases hfr : so.frozenExact with
  | true =>
    obtain ⟨s, h1, h2⟩ := lookOuter_spec (P := P) H w true key
    refine ⟨s, ?_, h2⟩
    simp only [setLookkey, M.bind_run, M.get_run, hfr, if_true]
    simp [h1]
  | false =>
    obtain ⟨s, h1, h2⟩ := lookOuter_spec (P := P) H w false key
    refine ⟨s, ?_, h2⟩
    simp only [setLookkey, M.bind_run, M.get_run, hfr]
    exact setLookkeyAux_ok 255 so _ h1

end Look

section Slots

theorem slot_set (so : SetObj K) (s i : Nat) (x : Slot K) (hs : s < so.table.length) :
    ({ so with table := so.table.set s x } : SetObj K).slot i = if i = s then x else so.slot i := by
  simp only [SetObj.slot]
  by_cases h : i = s
  · subst h
    simp [hs]
  · simp only [h, if_false, List.getD, List.getElem?_set_ne (Ne.symm h)]

/-- Keeping every non-NULL slot non-NULL keeps every `NoNull`. -/
theorem NoNull.mono {so so' : SetObj K} {u t j : Nat} (hm : so'.mask = so.mask)
    (hk : ∀ i, so.slot i ≠ .null → so'.slot i ≠ .null) (h : NoNull so u t j) : NoNull so' u t j := by
  rw [NoNull, hm]
  exact ⟨fun t' a j' b => hk _ (h.1 t' a j' b), fun j' a => hk _ (h.2 j' a)⟩

theorem mem_setEntries (so : SetObj K) (k : K) (h : Int) :
    (k, h) ∈ setEntries so ↔ ∃ s, so.slot s = .active k h := by
  simp only [setEntries, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hq⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    refine ⟨i, ?_⟩
    cases hc : so.table[i] with
    | null => simp [hc] at hq
    | dummy => simp [hc] at hq
    | active k' h' =>
      simp only [hc, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      simp [SetObj.slot, List.getD, hi, hc]
  · rintro ⟨s, hs⟩
    simp only [SetObj.slot, List.getD] at hs
    cases hg : so.table[s]? with
    | none => simp [hg] at hs
    | some x =>
      simp only [hg, Option.getD_some] at hs
      subst hs
      exact ⟨_, List.mem_of_getElem? hg, rfl⟩

/-- The entries of a table, as `set_next` gives them. -/
abbrev slotEntry : Slot K → Option (K × Int)
  | .active k h => some (k, h)
  | _ => none

theorem setEntries_eq (so : SetObj K) : setEntries so = so.table.filterMap slotEntry := rfl

/-- Filling a slot that held no entry adds one entry, somewhere. -/
theorem filterMap_set_add {α : Type} (f : Slot K → Option α) (x : Slot K) (y : α) (hx : f x = some y) :
    ∀ (l : List (Slot K)) (s : Nat), (hs : s < l.length) → f l[s] = none →
      (((l.set s x).filterMap f).Perm (y :: l.filterMap f)) := by
  intro l
  induction l with
  | nil => intro s hs; simp at hs
  | cons a t ih =>
    intro s hs h0
    cases s with
    | zero =>
      simp only [List.getElem_cons_zero] at h0
      simp [List.filterMap_cons, hx, h0]
    | succ s =>
      simp only [List.getElem_cons_succ] at h0
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hs
      have hp := ih s hs h0
      simp only [List.set_cons_succ, List.filterMap_cons]
      cases hf : f a with
      | none => simpa using hp
      | some b => exact (List.Perm.cons b hp).trans (List.Perm.swap y b _)

/-- Clearing a slot that held an entry removes that entry. -/
theorem filterMap_set_del {α : Type} (f : Slot K → Option α) (x : Slot K) (y : α) (hx : f x = none) :
    ∀ (l : List (Slot K)) (s : Nat), (hs : s < l.length) → f l[s] = some y →
      (l.filterMap f).Perm (y :: (l.set s x).filterMap f) := by
  intro l
  induction l with
  | nil => intro s hs; simp at hs
  | cons a t ih =>
    intro s hs h0
    cases s with
    | zero =>
      simp only [List.getElem_cons_zero] at h0
      simp [List.filterMap_cons, hx, h0]
    | succ s =>
      simp only [List.getElem_cons_succ] at h0
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hs
      have hp := ih s hs h0
      simp only [List.set_cons_succ, List.filterMap_cons]
      cases hf : f a with
      | none => simpa using hp
      | some b => exact (List.Perm.cons b hp).trans (List.Perm.swap y b _)

theorem countP_set_same {α : Type} (p : α → Bool) (x : α) :
    ∀ (l : List α) (s : Nat), (hs : s < l.length) → p l[s] = p x →
      (l.set s x).countP p = l.countP p := by
  intro l
  induction l with
  | nil => intro s hs; simp at hs
  | cons a t ih =>
    intro s hs h0
    cases s with
    | zero =>
      simp only [List.getElem_cons_zero] at h0
      simp [List.countP_cons, h0]
    | succ s =>
      simp only [List.getElem_cons_succ] at h0
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hs
      simp [List.countP_cons, ih s hs h0]

theorem countP_set_up {α : Type} (p : α → Bool) (x : α) :
    ∀ (l : List α) (s : Nat), (hs : s < l.length) → p l[s] = false → p x = true →
      (l.set s x).countP p = l.countP p + 1 := by
  intro l
  induction l with
  | nil => intro s hs; simp at hs
  | cons a t ih =>
    intro s hs h0 h1
    cases s with
    | zero =>
      simp only [List.getElem_cons_zero] at h0
      simp [List.countP_cons, h0, h1]
    | succ s =>
      simp only [List.getElem_cons_succ] at h0
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hs
      simp only [List.set_cons_succ, List.countP_cons, ih s hs h0 h1]
      omega

end Slots

section Discard
variable [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}

/-- The keys a set holds. -/
def setKeys (so : SetObj K) : List K := (setEntries so).map (·.1)

omit [DecidableEq K] in
theorem slot_lt (so : SetObj K) (s : Nat) (x : Slot K) (hx : x ≠ .null) (h : so.slot s = x) :
    s < so.table.length := by
  by_cases hs : s < so.table.length
  · exact hs
  · simp only [SetObj.slot] at h
    have hn : so.table[s]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD, hn, Option.getD_none] at h
    exact absurd h.symm hx

omit [DecidableEq K] in
theorem slot_get (so : SetObj K) (s : Nat) (hs : s < so.table.length) : so.table[s] = so.slot s := by
  simp [SetObj.slot, List.getD, hs]

/-- Deleting an entry: the slot becomes `dummy`, not NULL, so every chain through it stays. This is
the reason for dummies, and `fill` does not drop. -/
theorem setCore_del (w : SetCore hf eqv so) (s : Nat) (k : K) (h : Int) (hs : so.slot s = .active k h) :
    let so' : SetObj K := { so with used := so.used - 1, table := so.table.set s .dummy }
    SetCore hf eqv so' ∧ (setEntries so).Perm ((k, h) :: setEntries so') := by
  intro so'
  have hlt := slot_lt so s _ (by simp) hs
  have hsl : ∀ i, so'.slot i = if i = s then .dummy else so.slot i := fun i => by
    have := slot_set so s i .dummy hlt
    simpa [so', SetObj.slot] using this
  have hne : ∀ i, so.slot i ≠ .null → so'.slot i ≠ .null := by
    intro i hi
    rw [hsl]
    split
    · simp
    · exact hi
  have hback : ∀ i k' h', so'.slot i = .active k' h' → i ≠ s ∧ so.slot i = .active k' h' := by
    intro i k' h' hi
    rw [hsl] at hi
    split at hi
    · simp at hi
    · rename_i hn
      exact ⟨hn, hi⟩
  have hp := filterMap_set_del (slotEntry (K := K)) .dummy (k, h) rfl so.table s hlt
    (by rw [slot_get so s hlt, hs])
  refine ⟨{ log := w.log, small := w.small, len := by simp [so', w.len], reach := ?_, hashes := ?_,
            uniq := ?_, fill := ?_, used := ?_ }, hp⟩
  · intro i k' h' hi
    obtain ⟨_, hi2⟩ := hback i k' h' hi
    obtain ⟨t, j, a, b, c, d⟩ := w.reach i k' h' hi2
    exact ⟨t, j, a, b, c, NoNull.mono (so := so) (so' := so') rfl hne d⟩
  · intro i k' h' hi
    exact w.hashes i k' h' (hback i k' h' hi).2
  · intro s1 k1 h1 s2 k2 h2 a b c
    exact w.uniq s1 k1 h1 s2 k2 h2 (hback _ _ _ a).2 (hback _ _ _ b).2 c
  · have : (so.table.set s .dummy).countP (fun x => !x.isNull) = so.table.countP (fun x => !x.isNull) :=
      countP_set_same _ _ _ _ hlt (by rw [slot_get so s hlt, hs]; rfl)
    show so.fill = (so.table.set s .dummy).countP _
    rw [this]
    exact w.fill
  · have hlen := hp.length_eq
    simp only [List.length_cons] at hlen
    have hu := w.used
    show so.used - 1 = (setEntries so').length
    rw [hu, setEntries_eq so, hlen]
    rfl

end Discard

end PyLean.DictSet
