import PyLean.DictSet.SetHash

/-!
The set algebra on well-formed tables, for an honest key protocol: `update`, `|`, and what they do to
the list of keys. Table order depends on history, so lists are compared up to permutation.
-/

namespace PyLean.DictSet

open PyLean

variable {K : Type} [DecidableEq K] {P : Proto K (SetObj K)} {hf : K → Int} {eqv : K → K → Bool}

/-- The list form of the `set_add_entry` loops. -/
def addList (P : Proto K (SetObj K)) : List (K × Int) → SM K Unit
  | [] => pure ()
  | (k, h) :: rest => do
    setAddEntry P k h
    addList P rest

/-- Keys of `l` that `so` does not hold. -/
def notIn (eqv : K → K → Bool) (keys : List K) (l : List (K × Int)) : List (K × Int) :=
  l.filter fun e => !keys.any (eqv · e.1)

theorem setKeys_length (w : SetWF hf eqv so) : (setKeys so).length = so.used := by
  simp [setKeys, w.used]

omit [DecidableEq K] in
theorem entries_hash {so : SetObj K} (w : SetCore hf eqv so) :
    ∀ e ∈ setEntries so, e.2 = hf e.1 := by
  intro e he
  obtain ⟨s, hs⟩ := (mem_setEntries so e.1 e.2).mp (by simpa using he)
  exact w.hashes s e.1 e.2 hs

omit [DecidableEq K] in
theorem entries_pairwise {so : SetObj K} (w : SetCore hf eqv so) :
    (setEntries so).Pairwise (fun a b => eqv a.1 b.1 = false) := by
  rw [setEntries_eq]
  exact table_pairwise so.table (fun i j k1 h1 k2 h2 a b c =>
    w.uniq i k1 h1 j k2 h2 ((slot_active_iff so i k1 h1).mpr a)
      ((slot_active_iff so j k2 h2).mpr b) c)

/-- `set_add_entry` over a list of entries with distinct keys: what is new goes in. -/
theorem addList_spec (H : HonestSet P hf eqv) :
    ∀ (l : List (K × Int)) (so : SetObj K), SetWF hf eqv so → (∀ e ∈ l, e.2 = hf e.1) →
      l.Pairwise (fun a b => eqv a.1 b.1 = false) →
      (∃ n s, n ≤ so.used + l.length ∧ SetTooBig n ∧ addList P l so = (.error memoryError, s)) ∨
      ∃ so', addList P l so = (.ok (), so') ∧ SetWF hf eqv so' ∧
        (setEntries so').Perm (setEntries so ++ notIn eqv (setKeys so) l) ∧
        so'.peers = so.peers ∧ so'.ident = so.ident := by
  intro l
  induction l with
  | nil =>
    intro so w _ _
    exact Or.inr ⟨so, rfl, w, by simp [notIn], rfl, rfl⟩
  | cons e rest ih =>
    intro so w hh hp
    obtain ⟨k, h⟩ := e
    have hek : h = hf k := hh (k, h) (by simp)
    subst hek
    have hrest : ∀ x ∈ rest, eqv k x.1 = false := fun x hx => (List.pairwise_cons.mp hp).1 x hx
    have hp' := (List.pairwise_cons.mp hp).2
    have hh' : ∀ e ∈ rest, e.2 = hf e.1 := fun e he => hh e (by simp [he])
    simp only [addList, M.bind_run]
    rcases setAddEntry_spec H w k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h2]
      rcases ih so w hh' hp' with ⟨n, s, a, b, c⟩ | ⟨so', a, b, c, d, e⟩
      · exact Or.inl ⟨n, s, by simp only [List.length_cons]; omega, b, c⟩
      · refine Or.inr ⟨so', a, b, ?_, d, e⟩
        simpa [notIn, h1] using c
    · rcases h2 with ⟨hb, s, h3⟩ | ⟨s1, a1, b1, c1, d1, e1⟩
      · left
        refine ⟨so.used + 1, s, by simp, hb, ?_⟩
        rw [h3]
      · rw [a1]
        have hu : s1.used = so.used + 1 := by
          have := b1.used
          have h4 := w.used
          have h5 := c1.length_eq
          simp only [List.length_cons] at h5
          omega
        have hkeys : (setKeys s1).Perm (k :: setKeys so) := by
          simpa [setKeys] using c1.map (·.1)
        have hflt : notIn eqv (setKeys s1) rest = notIn eqv (setKeys so) rest := by
          apply List.filter_congr
          intro x hx
          rw [hkeys.any_eq]
          simp [hrest x hx]
        rcases ih s1 b1 hh' hp' with ⟨n, s, a, b, c⟩ | ⟨so', a, b, c, d, e⟩
        · exact Or.inl ⟨n, s, by simp only [List.length_cons]; omega, b, c⟩
        · refine Or.inr ⟨so', a, b, ?_, d.trans d1, e.trans e1⟩
          rw [hflt] at c
          refine c.trans ?_
          have hhead : notIn eqv (setKeys so) ((k, hf k) :: rest) =
              (k, hf k) :: notIn eqv (setKeys so) rest := by
            simp [notIn, h1]
          rw [hhead]
          exact (c1.append_right _).trans (List.perm_middle.symm)

omit [DecidableEq K] in
theorem live_peer {s : SetObj K} {id : Nat} {b : SetBody K} (hne : s.ident ≠ id)
    (hp : s.peers.find? (·.ident == id) = some b) : s.live id = b := by
  have h : (s.ident == id) = false := by simpa using hne
  simp [SetObj.live, h, hp]

/-- The last loop of `set_merge_lock_held` is `addList` over the entries, while the source stays. -/
theorem setMergeLoop_eq (H : HonestSet P hf eqv) {o : SetObj K} (wo : SetWF hf eqv o)
    (p : List (SetBody K)) (hp : p.find? (·.ident == o.ident) = some o.toSetBody) (i0 : Nat)
    (hi0 : i0 ≠ o.ident) :
    ∀ (fuel i : Nat) (s : SetObj K), SetWF hf eqv s → s.ident = i0 → s.peers = p →
      o.mask + 1 < i + fuel → i ≤ o.mask + 1 →
      setMergeLoop P o.ident fuel i s = addList P ((o.table.drop i).filterMap slotEntry) s := by
  intro fuel
  induction fuel with
  | zero => intro i _ _ _ _ h _; omega
  | succ fuel ih =>
    intro i s w hi hps hf1 hle
    have hl : s.live o.ident = o.toSetBody :=
      live_peer (by rw [hi]; exact hi0) (by rw [hps]; exact hp)
    have hlen : o.table.length = o.mask + 1 := wo.len
    by_cases hgt : i > o.mask
    · have hd : o.table.drop i = [] := List.drop_eq_nil_of_le (by omega)
      have hb : (o.mask < i) = True := by simpa using hgt
      simp [setMergeLoop, M.bind_run, M.get_run, hl, hgt, hd, addList]
    · have hlt : i < o.table.length := by omega
      have hdrop : o.table.drop i = o.table[i] :: o.table.drop (i + 1) :=
        List.drop_eq_getElem_cons hlt
      have hget : o.table.getD i .null = o.table[i] := by simp [List.getD, hlt]
      have hunf : setMergeLoop P o.ident (fuel + 1) i s =
          (match o.table[i] with
           | .active key hash => do
             setAddEntry P key hash
             setMergeLoop P o.ident fuel (i + 1)
           | _ => setMergeLoop P o.ident fuel (i + 1)) s := by
        simp only [setMergeLoop, M.bind_run, M.get_run, hl]
        simp only [hgt, if_false, hget]
        rfl
      rw [hunf, hdrop]
      cases hx : o.table[i] with
      | null =>
        simp only [List.filterMap_cons, slotEntry]
        exact ih (i + 1) s w hi hps (by omega) (by omega)
      | dummy =>
        simp only [List.filterMap_cons, slotEntry]
        exact ih (i + 1) s w hi hps (by omega) (by omega)
      | active key hash =>
        have hslot : o.slot i = .active key hash := by
          simp only [SetObj.slot]
          rw [hget, hx]
        have hh : hash = hf key := wo.hashes i key hash hslot
        subst hh
        simp only [List.filterMap_cons, slotEntry, addList, M.bind_run]
        rcases setAddEntry_spec H w key with ⟨_, h2⟩ | ⟨_, h2⟩
        · rw [h2]
          exact ih (i + 1) s w hi hps (by omega) (by omega)
        · rcases h2 with ⟨_, s', h3⟩ | ⟨s1, a1, b1, _, d1, e1⟩
          · rw [h3]
          · rw [a1]
            exact ih (i + 1) s1 b1 (e1.trans hi) (d1.trans hps) (by omega) (by omega)

/-- `set_merge_lock_held` once the source is in the state, for an honest protocol: every path ends
with what `so` held and the source's keys it did not, and the one way to fail is a table too big. -/
theorem setMergeIn_spec (H : HonestSet P hf eqv) {so o : SetObj K} (w : SetWF hf eqv so)
    (wo : SetWF hf eqv o) (hne : so.ident ≠ o.ident)
    (hp : so.peers.find? (·.ident == o.ident) = some o.toSetBody) :
    (∃ s, setMergeIn P o.ident so = (.error memoryError, s) ∧
      (SetResizeRefused ((so.used + o.used) * 2) ∨ ∃ n, n ≤ so.used + o.used ∧ SetTooBig n)) ∨
    ∃ so', setMergeIn P o.ident so = (.ok (), so') ∧ SetWF hf eqv so' ∧
      (setEntries so').Perm (setEntries so ++ notIn eqv (setKeys so) (setEntries o)) ∧
      so'.peers = so.peers ∧ so'.ident = so.ident := by
  have hl : so.live o.ident = o.toSetBody := live_peer hne hp
  have hsym := H.symm
  have hne' : ¬ o.ident = so.ident := fun h => hne h.symm
  have hlo : (setEntries o).length = o.used := wo.used.symm
  by_cases h0 : o.used = 0
  · right
    have he : setEntries o = [] := List.length_eq_zero_iff.mp (by omega)
    refine ⟨so, ?_, w, by simp [he, notIn], rfl, rfl⟩
    simp [setMergeIn, M.bind_run, M.get_run, hl, hne', h0]
  -- what comes after the one big resize
  have after : ∀ s1 : SetObj K, SetWF hf eqv s1 → (setEntries s1).Perm (setEntries so) →
      s1.peers = so.peers → s1.ident = so.ident →
      (s1.fill = 0 → o.used * 5 < s1.mask * 3) →
      (∃ s, setMergeRest P o.toSetBody s1 = (.error memoryError, s) ∧
        ∃ n, n ≤ so.used + o.used ∧ SetTooBig n) ∨
      ∃ so', setMergeRest P o.toSetBody s1 = (.ok (), so') ∧ SetWF hf eqv so' ∧
        (setEntries so').Perm (setEntries so ++ notIn eqv (setKeys so) (setEntries o)) ∧
        so'.peers = so.peers ∧ so'.ident = so.ident := by
    intro s1 w1 hperm hps hid hroom
    have hkeys : (setKeys s1).Perm (setKeys so) := by
      simpa [setKeys] using hperm.map (·.1)
    have hused1 : s1.used = so.used := by
      have h1 := w1.used
      have h2 := w.used
      have h3 := hperm.length_eq
      omega
    by_cases hf0 : s1.fill = 0
    · right
      have hent : setEntries s1 = [] := by
        have h1 := counts_fill s1.table
        have h2 := w1.fill
        have h3 : (activeHashes s1.table).length = 0 := by omega
        rw [activeHashes_eq] at h3
        have h4 : (s1.table.filterMap slotEntry).length = 0 := by simpa using h3
        rw [setEntries_eq]
        exact List.length_eq_zero_iff.mp h4
      have hnil : setEntries so = [] := List.Perm.eq_nil (hperm.symm.trans (by rw [hent]))
      have hkn : setKeys so = [] := by simp [setKeys, hnil]
      have hflt : notIn eqv (setKeys so) (setEntries o) = setEntries o := by
        simp [notIn, hkn]
      have hus : s1.used = 0 := by
        have := w1.used
        rw [hent] at this
        simpa using this
      rw [hnil, hflt, List.nil_append]
      by_cases hc : s1.mask = o.mask ∧ o.fill = o.used
      · obtain ⟨hm, hfu⟩ := hc
        have hb : (s1.fill == 0 && s1.mask == o.mask && o.fill == o.used) = true := by
          simp [hf0, hm, hfu]
        let s2 : SetObj K := { s1 with table := o.table, fill := o.fill, used := o.used }
        refine ⟨s2, ?_, ?_, ?_, hps, hid⟩
        · simp [setMergeRest, M.bind_run, M.get_run, M.put_run, hf0, hm, hfu, M.pure_run, s2]
        · exact { toSetCore := wo.toSetCore.of_fields (so' := s2) hm rfl rfl rfl
                  load := by
                    show o.fill * 5 < s1.mask * 3
                    rw [hm]
                    exact wo.load }
        · exact List.Perm.refl _
      · have hb : (s1.fill == 0 && s1.mask == o.mask && o.fill == o.used) = false := by
          by_cases hm : s1.mask = o.mask
          · have h2 : ¬ o.fill = o.used := fun h => hc ⟨hm, h⟩
            simp [hm, h2]
          · simp [hm]
        have hb0 : (s1.fill == 0) = true := by simpa using hf0
        have hr := hroom hf0
        have w0 : SetCore hf eqv (withT s1 s1.mask s1.table 0) :=
          w1.toSetCore.of_fields rfl rfl hf0.symm hus.symm
        have hempty : ∀ s' k h, (withT s1 s1.mask s1.table 0).slot s' = .active k h → False := by
          intro s' k h hs
          have : (k, h) ∈ setEntries s1 := by
            apply (mem_setEntries s1 k h).mpr
            exact ⟨s', hs⟩
          rw [hent] at this
          simp at this
        have hsrc : o.table.filterMap slotEntry = setEntries o := (setEntries_eq o).symm
        obtain ⟨t, r1, r2, r3⟩ := reinsert_spec hsym s1 s1.mask o.table s1.table 0 w0
          (by rw [hsrc, hlo]; omega) (by rw [hsrc]; exact entries_hash wo.toSetCore)
          (by rw [hsrc]; exact entries_pairwise wo.toSetCore)
          (fun e _ s' k h hs => (hempty s' k h hs).elim)
        rw [hsrc, hlo] at r2
        simp only [Nat.zero_add] at r2
        rw [hsrc] at r3
        have hacc : s1.table.filterMap slotEntry = [] := by rw [← setEntries_eq]; exact hent
        rw [hacc, List.append_nil] at r3
        refine ⟨withT s1 s1.mask t o.used, ?_, ?_, r3, hps, hid⟩
        · have hc2 : (s1.mask == o.mask && o.fill == o.used) = false := by
            simpa [hf0] using hb
          simp only [setMergeRest, M.bind_run, M.get_run]
          simp only [hb0, Bool.true_and, hc2, Bool.false_eq_true, if_false, if_true, M.bind_run,
            M.lift_run, r1]
          rfl
        · exact { toSetCore := r2, load := by
                    show o.used * 5 < s1.mask * 3
                    exact hr }
    · have hb : (s1.fill == 0 && s1.mask == o.mask && o.fill == o.used) = false := by
        simp [hf0]
      have hb0 : (s1.fill == 0) = false := by simpa using hf0
      have hfuel : setLoopFuel s1 o.ident = 4 * (o.mask + 1) + 64 := by
        simp only [setLoopFuel]
        rw [live_peer (by rw [hid]; exact hne) (by rw [hps]; exact hp)]
      have hloop : setMergeRest P o.toSetBody s1 =
          addList P (setEntries o) s1 := by
        simp only [setMergeRest, M.bind_run, M.get_run]
        simp only [hb, Bool.false_eq_true, if_false, hb0]
        have := setMergeLoop_eq H wo so.peers hp so.ident hne (setLoopFuel s1 o.ident) 0 s1 w1 hid hps
          (by rw [hfuel]; omega) (by omega)
        rw [setEntries_eq]
        simpa using this
      rw [hloop]
      rcases addList_spec H (setEntries o) s1 w1 (entries_hash wo.toSetCore)
          (entries_pairwise wo.toSetCore) with ⟨n, s, a, b, c⟩ | ⟨so', a, b, c, d, e⟩
      · exact Or.inl ⟨s, c, n, by omega, b⟩
      · refine Or.inr ⟨so', a, b, ?_, d.trans hps, e.trans hid⟩
        have hflt : notIn eqv (setKeys s1) (setEntries o) = notIn eqv (setKeys so) (setEntries o) := by
          apply List.filter_congr
          intro x _
          rw [hkeys.any_eq]
        rw [hflt] at c
        exact c.trans (hperm.append_right _)
  by_cases hbig : (so.fill + o.used) * 5 ≥ so.mask * 3
  · rcases setTableResize_spec hsym so w.toSetCore ((so.used + o.used) * 2) (by omega) with
      ⟨h1, h2⟩ | ⟨s1, a1, b1, c1, d1, e1, f1⟩
    · left
      refine ⟨so, ?_, Or.inl h1⟩
      simp [setMergeIn, M.bind_run, M.get_run, hl, hne', h0, hbig, h2]
    · have hu1 : s1.used = so.used := by
        have h1 := b1.used
        have h2 := w.used
        have h3 := c1.length_eq
        omega
      have hrun : setMergeIn P o.ident so = setMergeRest P o.toSetBody s1 := by
        simp [setMergeIn, M.bind_run, M.get_run, hl, hne', h0, hbig, a1]
      rw [hrun]
      rcases after s1 b1 c1 d1 e1 (fun _ => by omega) with ⟨s, a, n, c, d⟩ | g
      · exact Or.inl ⟨s, a, Or.inr ⟨n, c, d⟩⟩
      · exact Or.inr g
  · have hrun : setMergeIn P o.ident so = setMergeRest P o.toSetBody so := by
      simp [setMergeIn, M.bind_run, M.get_run, hl, hne', h0, hbig]
    rw [hrun]
    rcases after so w (List.Perm.refl _) rfl rfl (fun h => by omega) with ⟨s, a, n, c, d⟩ | g
    · exact Or.inl ⟨s, a, Or.inr ⟨n, c, d⟩⟩
    · exact Or.inr g


/-- `set_merge_lock_held`, whole, from another set: every path gives what `so` held and the source's
keys it did not, and the one way to fail is a table `PyMem_NEW` refuses. From itself it does nothing.
`so.peers = []` is the state with nothing else in hand, and the identities are object identity. -/
def SetMergeRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ so o : SetObj K, SetWF hf eqv so → SetWF hf eqv o → so.peers = [] →
      (so.ident = o.ident → setMerge P o so = (.ok (), so)) ∧
      (so.ident ≠ o.ident →
        (∃ s, setMerge P o so = (.error memoryError, s) ∧
          (SetResizeRefused ((so.used + o.used) * 2) ∨ ∃ n, n ≤ so.used + o.used ∧ SetTooBig n)) ∨
        ∃ so', setMerge P o so = (.ok (), so') ∧ SetWF hf eqv so' ∧
          (setEntries so').Perm (setEntries so ++ notIn eqv (setKeys so) (setEntries o)) ∧
          so'.peers = [] ∧ so'.ident = so.ident)
theorem setMergeRefines_proven : SetMergeRefines := by
  intro K _ P hf eqv H so o w wo hps
  refine ⟨fun he => ?_, fun hne => ?_⟩
  · have h1 : (so.ident == o.ident) = true := by simpa using he
    have hl : so.live o.ident = so.toSetBody := by simp [SetObj.live, he]
    simp [setMerge, withPeer, h1, setMergeIn, M.bind_run, M.get_run, hl, he]
  · have h1 : (so.ident == o.ident) = false := by simpa using hne
    let s0 : SetObj K := { so with peers := [o.toSetBody] }
    have w0 : SetWF hf eqv s0 :=
      { toSetCore := w.toSetCore.of_fields rfl rfl rfl rfl, load := w.load }
    have hfind : s0.peers.find? (·.ident == o.ident) = some o.toSetBody := by simp [s0]
    have hrun : setMerge P o so =
        (match setMergeIn P o.ident s0 with
         | (r, s) => (r, { s with peers := s.peers.dropLast })) := by
      simp [setMerge, withPeer, h1, hps, s0]
    rcases setMergeIn_spec H w0 wo hne hfind with ⟨s, a, b⟩ | ⟨so', a, b, c, d, e⟩
    · left
      exact ⟨_, by rw [hrun, a], b⟩
    · right
      refine ⟨{ so' with peers := so'.peers.dropLast }, by rw [hrun, a],
        { toSetCore := b.toSetCore.of_fields rfl rfl rfl rfl, load := b.load }, c, ?_, e⟩
      simp [d, s0]

/-- The list form of `forNext`. -/
def forList (body : K → Int → SM K Bool) : List (K × Int) → SM K Bool
  | [] => pure false
  | (k, h) :: rest => do
    if ← body k h then return true
    forList body rest

omit [DecidableEq K] in
/-- A `set_next` loop walks the entries of a set the body leaves alone. `I` is what holds of the state
between turns. -/
theorem forNext_list {b : SetObj K} (hlen : b.table.length = b.mask + 1)
    (body : K → Int → SM K Bool) (I : SetObj K → Prop)
    (hI : ∀ s, I s → s.live b.ident = b.toSetBody)
    (hbody : ∀ k h s r s', (k, h) ∈ setEntries b → I s → body k h s = (.ok r, s') → I s') :
    ∀ (fuel pos : Nat) (s : SetObj K), I s → pos ≤ b.mask + 1 →
      ((b.table.drop pos).filterMap slotEntry).length < fuel →
      forNext b.ident body fuel pos s = forList body ((b.table.drop pos).filterMap slotEntry) s := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ h; omega
  | succ fuel ih =>
    intro pos s hs hp hf
    have hl := hI s hs
    have hn := setNext_spec b.table b.mask hlen (b.mask + 2) pos (by omega) hp
    have hget : forNext b.ident body (fuel + 1) pos s =
        (match setNext b.table b.mask (b.mask + 2) pos with
         | none => pure false
         | some (pos', key, hash) => do
           if ← body key hash then return true
           forNext b.ident body fuel pos') s := by
      simp only [forNext, M.bind_run, M.get_run, hl]
      rfl
    rw [hget]
    cases hq : (b.table.drop pos).filterMap slotEntry with
    | nil =>
      rw [hq] at hn
      simp only at hn
      rw [hn]
      rfl
    | cons e rest =>
      rw [hq] at hn hf
      obtain ⟨k, h⟩ := e
      simp only at hn
      obtain ⟨i', h1, h2, h3, h4⟩ := hn
      rw [h3]
      simp only [forList, M.bind_run]
      cases hb : body k h s with
      | mk r s1 =>
        cases r with
        | error e => rfl
        | ok c =>
          cases c with
          | true => rfl
          | false =>
            have hmem : (k, h) ∈ (b.table.drop pos).filterMap slotEntry := by simp [hq]
            have hmem2 : (k, h) ∈ setEntries b := by
              obtain ⟨x, hx, hxe⟩ := List.mem_filterMap.mp hmem
              rw [setEntries_eq]
              exact List.mem_filterMap.mpr ⟨x, List.mem_of_mem_drop hx, hxe⟩
            have hs1 := hbody k h s false s1 hmem2 hs hb
            have := ih i' s1 hs1 h2 (by rw [h4]; simpa using hf)
            rw [h4] at this
            exact this

theorem swapIn_found {s : SetObj K} {b : SetBody K} (hne : s.ident ≠ b.ident) (hb : b ∈ s.peers)
    (huniq : ∀ x ∈ s.peers, x.ident = b.ident → x = b) :
    s.swapIn b.ident = { toSetBody := b, peers := s.peers.map fun p =>
      if p.ident == b.ident then s.toSetBody else p } := by
  have h1 : (s.ident == b.ident) = false := by simpa using hne
  have hf : ∃ x, s.peers.find? (·.ident == b.ident) = some x := by
    cases hq : s.peers.find? (·.ident == b.ident) with
    | some x => exact ⟨x, rfl⟩
    | none =>
      have := List.find?_eq_none.mp hq b hb
      simp at this
  obtain ⟨x, hx⟩ := hf
  have hxm := List.mem_of_find?_eq_some hx
  have hxi : x.ident = b.ident := by simpa using List.find?_some hx
  have hxb := huniq x hxm hxi
  simp [SetObj.swapIn, h1, hx, hxb]


/-- A set in the peers changes place with the focus and back without a trace, if its identity is
unique and none of the peers has the identity of the focus. -/
theorem swapIn_back {s : SetObj K} {b : SetBody K} (hne : s.ident ≠ b.ident) (hb : b ∈ s.peers)
    (huniq : ∀ x ∈ s.peers, x.ident = b.ident → x = b) (hs : ∀ x ∈ s.peers, x.ident ≠ s.ident) :
    (s.swapIn b.ident).swapIn s.ident = s := by
  rw [swapIn_found hne hb huniq]
  let t : SetObj K := { toSetBody := b, peers := s.peers.map fun p =>
    if p.ident == b.ident then s.toSetBody else p }
  have h1 : t.ident ≠ s.toSetBody.ident := fun h => hne h.symm
  have h2 : s.toSetBody ∈ t.peers := by
    refine List.mem_map.mpr ⟨b, hb, by simp⟩
  have h3 : ∀ x ∈ t.peers, x.ident = s.toSetBody.ident → x = s.toSetBody := by
    intro x hx hi
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    by_cases he : p.ident = b.ident
    · simp [he]
    · have : (p.ident == b.ident) = false := by simpa using he
      simp only [this, Bool.false_eq_true, if_false] at hi ⊢
      exact absurd hi (hs p hp)
  have h4 := swapIn_found (s := t) (b := s.toSetBody) h1 h2 h3
  show t.swapIn s.ident = s
  have e : s.ident = s.toSetBody.ident := rfl
  rw [e, h4]
  have hpeers : (t.peers.map fun p => if p.ident == s.toSetBody.ident then t.toSetBody else p) =
      s.peers := by
    simp only [t, List.map_map]
    conv => rhs; rw [← List.map_id s.peers]
    apply List.map_congr_left
    intro p hp
    by_cases he : p.ident = b.ident
    · have hpb := huniq p hp he
      simp [he, hpb]
    · have h6 : ¬ p.ident = s.ident := hs p hp
      simp [Function.comp, he, h6]
  rw [hpeers]

/-- `set_contains_entry` on a set among the peers, for an honest protocol: the answer of the list,
and the state as it was. -/
theorem onSet_contains (H : HonestSet P hf eqv) {s A : SetObj K} (wa : SetWF hf eqv A) (key : K)
    (hne : s.ident ≠ A.ident) (hA : A.toSetBody ∈ s.peers)
    (huniq : ∀ x ∈ s.peers, x.ident = A.ident → x = A.toSetBody)
    (hs : ∀ x ∈ s.peers, x.ident ≠ s.ident) :
    onSet A.ident (setContainsEntry P key (hf key)) s =
      (.ok ((setKeys A).any (eqv · key)), s) := by
  have ht := swapIn_found (s := s) (b := A.toSetBody) hne hA huniq
  have hback := swapIn_back (s := s) (b := A.toSetBody) hne hA huniq hs
  have e0 : A.toSetBody.ident = A.ident := rfl
  rw [e0] at ht hback
  let t := s.swapIn A.ident
  have wt : SetWF hf eqv t := by
    have hm : t.mask = A.mask := by simp only [t, ht]
    have htb : t.table = A.table := by simp only [t, ht]
    have hfi : t.fill = A.fill := by simp only [t, ht]
    have hu : t.used = A.used := by simp only [t, ht]
    exact { toSetCore := wa.toSetCore.of_fields hm htb hfi hu
            load := by rw [hfi, hm]; exact wa.load }
  have hk : setKeys t = setKeys A := by
    have htb : t.table = A.table := by simp only [t, ht]
    simp [setKeys, setEntries, htb]
  have hc := setContains_hash H wt key
  rw [hk] at hc
  simp only [onSet]
  show (match setContainsEntry P key (hf key) t with
    | (r, s') => (r, s'.swapIn s.ident)) = _
  rw [hc]
  simp only
  rw [show t.swapIn s.ident = s from hback]

/-- What the loop of a set operation keeps of the state: the table's invariant, and who it is. -/
def LoopInv (hf : K → Int) (eqv : K → K → Bool) (i0 : Nat) (p : List (SetBody K)) (s : SetObj K) :
    Prop :=
  SetWF hf eqv s ∧ s.ident = i0 ∧ s.peers = p

/-- A body that adds exactly the keys `q` passes is `addList` over them. -/
theorem forList_add (H : HonestSet P hf eqv) (i0 : Nat) (p : List (SetBody K)) (q : K → Bool)
    (body : K → Int → SM K Bool)
    (hq : ∀ k s, LoopInv hf eqv i0 p s →
      body k (hf k) s = (if q k then (do setAddEntry P k (hf k); return false) else pure false) s) :
    ∀ (l : List (K × Int)) (s : SetObj K), LoopInv hf eqv i0 p s → (∀ e ∈ l, e.2 = hf e.1) →
      forList body l s = (do addList P (l.filter fun e => q e.1); return false) s := by
  intro l
  induction l with
  | nil => intro s _ _; rfl
  | cons e rest ih =>
    intro s hs hh
    obtain ⟨k, h⟩ := e
    have hek : h = hf k := hh (k, h) (by simp)
    subst hek
    have hh' : ∀ e ∈ rest, e.2 = hf e.1 := fun e he => hh e (by simp [he])
    obtain ⟨w, hi, hps⟩ := id hs
    simp only [forList, M.bind_run, hq k s hs]
    by_cases hqk : q k = true
    · simp only [hqk, if_true, List.filter_cons, addList, M.bind_run]
      rcases setAddEntry_spec H w k with ⟨_, h2⟩ | ⟨_, h2⟩
      · simp only [h2, M.pure_run]
        have := ih s hs hh'
        simpa [M.bind_run] using this
      · rcases h2 with ⟨_, s', h3⟩ | ⟨s1, a1, b1, _, d1, e1⟩
        · simp only [h3]
        · simp only [a1, M.pure_run]
          have := ih s1 ⟨b1, e1.trans hi, d1.trans hps⟩ hh'
          simpa [M.bind_run] using this
    · have hf1 : q k = false := by simpa using hqk
      simp only [hf1, Bool.false_eq_true, if_false, List.filter_cons, M.pure_run]
      exact ih s hs hh'

/-- The empty object of `make_new_set_basetype` is well formed, among any peers. -/
theorem newBasetype_wf (hf : K → Int) (eqv : K → K → Bool) (so : SetBody K) (id : Nat)
    (p : List (SetBody K)) :
    SetWF hf eqv { newBasetype so id with peers := p } ∧
      setEntries ({ newBasetype so id with peers := p } : SetObj K) = [] := by
  obtain ⟨w0, _⟩ := wf_empty_set (K := K) hf eqv
  have hc : SetCore hf eqv ({ newBasetype so id with peers := p } : SetObj K) :=
    w0.toSetCore.of_fields rfl rfl rfl rfl
  exact ⟨{ toSetCore := hc, load := w0.load }, rfl⟩


omit [DecidableEq K] in
theorem find_unique {p : List (SetBody K)} {b : SetBody K} (hb : b ∈ p)
    (huniq : ∀ x ∈ p, x.ident = b.ident → x = b) : p.find? (·.ident == b.ident) = some b := by
  cases hq : p.find? (·.ident == b.ident) with
  | some x =>
    have hxm := List.mem_of_find?_eq_some hq
    have hxi : x.ident = b.ident := by simpa using List.find?_some hq
    rw [huniq x hxm hxi]
  | none =>
    have := List.find?_eq_none.mp hq b hb
    simp at this

/-- The world of a set operation on two sets, with the result in focus. -/
structure TwoSets (i0 : Nat) (p : List (SetBody K)) (A B : SetObj K) : Prop where
  neA : i0 ≠ A.ident
  neB : i0 ≠ B.ident
  memA : A.toSetBody ∈ p
  memB : B.toSetBody ∈ p
  uniqA : ∀ x ∈ p, x.ident = A.ident → x = A.toSetBody
  uniqB : ∀ x ∈ p, x.ident = B.ident → x = B.toSetBody
  focus : ∀ x ∈ p, x.ident ≠ i0

/-- A `set_next` loop over `B` that adds what `q` passes: the fuel is enough and `B` stays. -/
theorem forNext_add (H : HonestSet P hf eqv) {i0 : Nat} {p : List (SetBody K)} {A B : SetObj K}
    (w : TwoSets i0 p A B) (wb : SetWF hf eqv B) (q : K → Bool) (body : K → Int → SM K Bool)
    (hq : ∀ k s, LoopInv hf eqv i0 p s →
      body k (hf k) s = (if q k then (do setAddEntry P k (hf k); return false) else pure false) s)
    (s : SetObj K) (hs : LoopInv hf eqv i0 p s) :
    forNext B.ident body (setLoopFuel s B.ident) 0 s =
      (do addList P ((setEntries B).filter fun e => q e.1); return false) s := by
  have hfind : p.find? (·.ident == B.ident) = some B.toSetBody := find_unique w.memB w.uniqB
  have hI : ∀ s', LoopInv hf eqv i0 p s' → s'.live B.ident = B.toSetBody := fun s' h =>
    live_peer (by rw [h.2.1]; exact w.neB) (by rw [h.2.2]; exact hfind)
  have hbody : ∀ k h s' r s'', (k, h) ∈ setEntries B → LoopInv hf eqv i0 p s' →
      body k h s' = (.ok r, s'') → LoopInv hf eqv i0 p s'' := by
    intro k h s' r s'' hm hi hb
    have hh : h = hf k := entries_hash wb.toSetCore (k, h) hm
    subst hh
    rw [hq k s' hi] at hb
    by_cases hqk : q k = true
    · simp only [hqk, if_true, M.bind_run] at hb
      obtain ⟨w1, i1, p1⟩ := id hi
      rcases setAddEntry_spec H w1 k with ⟨_, h2⟩ | ⟨_, h2⟩
      · rw [h2] at hb
        simp only [M.pure_run, Prod.mk.injEq] at hb
        rw [← hb.2]
        exact hi
      · rcases h2 with ⟨_, s2, h3⟩ | ⟨s1, a1, b1, _, d1, e1⟩
        · rw [h3] at hb
          simp at hb
        · rw [a1] at hb
          simp only [M.pure_run, Prod.mk.injEq] at hb
          rw [← hb.2]
          exact ⟨b1, e1.trans i1, d1.trans p1⟩
    · have hf1 : q k = false := by simpa using hqk
      simp only [hf1, Bool.false_eq_true, if_false, M.pure_run, Prod.mk.injEq] at hb
      rw [← hb.2]
      exact hi
  have hfuel : setLoopFuel s B.ident = 4 * (B.mask + 1) + 64 := by
    simp only [setLoopFuel]
    rw [hI s hs]
  have hlen : ((B.table.drop 0).filterMap slotEntry).length ≤ B.mask + 1 := by
    have h1 := wb.used
    have h2 : (setEntries B).length ≤ B.table.length := by
      rw [setEntries_eq]
      exact List.length_filterMap_le _ _
    have h3 := wb.len
    simpa [setEntries_eq] using (by omega : (setEntries B).length ≤ B.mask + 1)
  have h1 := forNext_list wb.len body (LoopInv hf eqv i0 p) hI hbody (setLoopFuel s B.ident) 0 s hs
    (by omega) (by rw [hfuel]; omega)
  have h2 := forList_add H i0 p q body hq (setEntries B) s hs (entries_hash wb.toSetCore)
  rw [h1]
  simpa [setEntries_eq] using h2

/-- The body of the loop of `set_intersection`, for an honest protocol. -/
theorem interBody (H : HonestSet P hf eqv) {i0 : Nat} {p : List (SetBody K)} {A B : SetObj K}
    (w : TwoSets i0 p A B) (wa : SetWF hf eqv A) (k : K) (s : SetObj K)
    (hs : LoopInv hf eqv i0 p s) :
    (do
      let rv ← onSet A.ident (setContainsEntry P k (hf k))
      if rv then setAddEntry P k (hf k)
      return false : SM K Bool) s =
    (if (setKeys A).any (eqv · k) then (do setAddEntry P k (hf k); return false) else pure false) s := by
  have h := onSet_contains H wa k (s := s) (by rw [hs.2.1]; exact w.neA) (by rw [hs.2.2]; exact w.memA)
    (by rw [hs.2.2]; exact w.uniqA) (by rw [hs.2.1, hs.2.2]; exact w.focus)
  simp only [M.bind_run, h]

omit [DecidableEq K] in
theorem onResult_ok {α : Type} {r so s : SetObj K} {m : SM K α} {a : α}
    (h : m { r with peers := so.toSetBody :: so.peers } = (.ok a, s))
    (hp : s.peers = so.toSetBody :: so.peers) :
    onResult r m so = (.ok (a, { s with peers := [] }), so) := by
  simp [onResult, h, hp]

omit [DecidableEq K] in
theorem onResult_err {α : Type} {r so s : SetObj K} {m : SM K α} {e : PyExc}
    (h : m { r with peers := so.toSetBody :: so.peers } = (.error e, s)) :
    ∃ so', onResult r m so = (.error e, so') := by
  simp [onResult, h]

/-- The world of a set operation on `so` and `o` with a new result in focus. -/
structure Pair (so o : SetObj K) (id : Nat) : Prop where
  ne : so.ident ≠ o.ident
  id1 : id ≠ so.ident
  id2 : id ≠ o.ident

/-- With the result in focus, either of the two sets can be walked and the other looked in. -/
theorem Pair.two {so o : SetObj K} {id : Nat} (h : Pair so o id) {A B : SetObj K}
    (hA : A = so ∨ A = o) (hB : B = so ∨ B = o) :
    TwoSets id [so.toSetBody, o.toSetBody] A B := by
  have huq : ∀ {X : SetObj K}, (X = so ∨ X = o) →
      ∀ x ∈ [so.toSetBody, o.toSetBody], x.ident = X.ident → x = X.toSetBody := by
    intro X hX x hx hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hX with rfl | rfl <;> rcases hx with rfl | rfl
    · rfl
    · exact absurd hi.symm h.ne
    · exact absurd hi h.ne
    · rfl
  have hmem : ∀ {X : SetObj K}, (X = so ∨ X = o) → X.toSetBody ∈ [so.toSetBody, o.toSetBody] := by
    intro X hX
    rcases hX with rfl | rfl <;> simp
  have hneX : ∀ {X : SetObj K}, (X = so ∨ X = o) → id ≠ X.ident := by
    intro X hX
    rcases hX with rfl | rfl
    · exact h.id1
    · exact h.id2
  refine { neA := hneX hA, neB := hneX hB, memA := hmem hA, memB := hmem hB, uniqA := huq hA
           uniqB := huq hB, focus := ?_ }
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact fun e => h.id1 e.symm
  · exact fun e => h.id2 e.symm

/-- A loop on a new result that amounts to adding the entries `l` of a well-formed set, filtered. -/
theorem onResult_list (H : HonestSet P hf eqv) {s0 : SetObj K} (id : Nat) (loop : SM K Bool)
    (l : List (K × Int)) (hh : ∀ e ∈ l, e.2 = hf e.1)
    (hp : l.Pairwise (fun a b => eqv a.1 b.1 = false))
    (hloop : loop { newBasetype s0.toSetBody id with peers := s0.toSetBody :: s0.peers } =
      (do addList P l; return false)
        { newBasetype s0.toSetBody id with peers := s0.toSetBody :: s0.peers }) :
    (∃ n so', n ≤ l.length ∧ SetTooBig n ∧
      (onResult (newBasetype s0.toSetBody id) loop) s0 = (.error memoryError, so')) ∨
    ∃ r, (onResult (newBasetype s0.toSetBody id) loop) s0 = (.ok (false, r), s0) ∧
      SetWF hf eqv r ∧ (setEntries r).Perm l ∧ r.ident = id ∧ r.peers = [] := by
  let p := s0.toSetBody :: s0.peers
  obtain ⟨wr, her⟩ := newBasetype_wf hf eqv s0.toSetBody id p
  let r0 : SetObj K := { newBasetype s0.toSetBody id with peers := p }
  have hkr : setKeys r0 = [] := by simp [setKeys, r0, her]
  rcases addList_spec H l r0 wr hh hp with ⟨n, s, a, b, c⟩ | ⟨r1, a, b, c, d, e⟩
  · left
    have hl : loop r0 = (.error memoryError, s) := by
      have h2 : loop r0 = (do addList P l; return false) r0 := hloop
      rw [h2, M.bind_run, c]
    obtain ⟨so', h1⟩ := onResult_err (r := newBasetype s0.toSetBody id) (so := s0) hl
    have hu0 : r0.used = 0 := rfl
    exact ⟨n, so', by omega, b, h1⟩
  · right
    have hl : loop r0 = (.ok false, r1) := by
      have h2 : loop r0 = (do addList P l; return false) r0 := hloop
      rw [h2, M.bind_run, a]
      rfl
    have h1 := onResult_ok (r := newBasetype s0.toSetBody id) (so := s0) hl d
    refine ⟨{ r1 with peers := [] }, h1,
      { toSetCore := b.toSetCore.of_fields rfl rfl rfl rfl, load := b.load }, ?_, e, rfl⟩
    have hni : notIn eqv [] l = l := by simp [notIn]
    rw [hkr, her, hni] at c
    show (setEntries r1).Perm _
    simpa using c

/-- The sets swapped as `set_intersection` swaps them (:1727-1731). -/
def interA (so o : SetObj K) : SetObj K := if o.used > so.used then o else so
def interB (so o : SetObj K) : SetObj K := if o.used > so.used then so else o

/-- The branch of `set_intersection` for two sets, with `o` already among the peers. -/
theorem interSets_spec (H : HonestSet P hf eqv) {so o : SetObj K} {id : Nat} (hP : Pair so o id)
    (w : SetWF hf eqv so) (wo : SetWF hf eqv o) (s0 : SetObj K) (hb : s0.toSetBody = so.toSetBody)
    (hps : s0.peers = [o.toSetBody]) :
    (∃ n s, n ≤ (interB so o).used ∧ SetTooBig n ∧
      setIntersectionSets P o id s0 = (.error memoryError, s)) ∨
    ∃ r, setIntersectionSets P o id s0 = (.ok r, s0) ∧ SetWF hf eqv r ∧
      (setEntries r).Perm ((setEntries (interB so o)).filter
        fun e => (setKeys (interA so o)).any (eqv · e.1)) ∧ r.ident = id ∧ r.peers = [] := by
  let A := interA so o
  let B := interB so o
  have hA : A = so ∨ A = o := by
    simp only [A, interA]
    split
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hB : B = so ∨ B = o := by
    simp only [B, interB]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hw : TwoSets id [so.toSetBody, o.toSetBody] A B := hP.two hA hB
  have wA : SetWF hf eqv A := by rcases hA with h | h <;> rw [h] <;> assumption
  have wB : SetWF hf eqv B := by rcases hB with h | h <;> rw [h] <;> assumption
  have hid0 : s0.ident = so.ident := congrArg SetBody.ident hb
  have hu0 : s0.used = so.used := congrArg SetBody.used hb
  have hlive : s0.live o.ident = o.toSetBody :=
    live_peer (by rw [hid0]; exact hP.ne) (by simp [hps])
  have hp0 : s0.toSetBody :: s0.peers = [so.toSetBody, o.toSetBody] := by rw [hb, hps]
  obtain ⟨wr, _⟩ := newBasetype_wf hf eqv s0.toSetBody id [so.toSetBody, o.toSetBody]
  have hinv : LoopInv hf eqv id [so.toSetBody, o.toSetBody]
      { newBasetype s0.toSetBody id with peers := s0.toSetBody :: s0.peers } := by
    rw [hp0]
    exact ⟨wr, rfl, rfl⟩
  have hloop : setInterLoop P A.ident B.ident
      { newBasetype s0.toSetBody id with peers := s0.toSetBody :: s0.peers } =
      (do addList P ((setEntries B).filter fun e => (setKeys A).any (eqv · e.1)); return false)
        { newBasetype s0.toSetBody id with peers := s0.toSetBody :: s0.peers } :=
    forNext_add H hw wB (fun k => (setKeys A).any (eqv · k)) _
      (fun k s hs => interBody H hw wA k s hs) _ hinv
  have hsets : setIntersectionSets P o id s0 =
      (match onResult (newBasetype s0.toSetBody id) (setInterLoop P A.ident B.ident) s0 with
       | (.ok r, s) => (.ok r.2, s)
       | (.error e, s) => (.error e, s)) := by
    simp only [setIntersectionSets, M.bind_run, M.get_run, hlive]
    have e1 : (if o.toSetBody.used > s0.used then o.toSetBody.ident else s0.ident) = A.ident := by
      simp only [A, interA, hu0, hid0]
      split <;> rfl
    have e2 : (if o.toSetBody.used > s0.used then s0.ident else o.toSetBody.ident) = B.ident := by
      simp only [B, interB, hu0, hid0]
      split <;> rfl
    rw [e1, e2]
    cases onResult (newBasetype s0.toSetBody id) (setInterLoop P A.ident B.ident) s0 with
    | mk res s =>
      cases res <;> rfl
  have hlen : ((setEntries B).filter fun e => (setKeys A).any (eqv · e.1)).length ≤ B.used := by
    have h1 := List.length_filter_le (fun e : K × Int => (setKeys A).any (eqv · e.1)) (setEntries B)
    have h2 := wB.used
    omega
  rcases onResult_list H (s0 := s0) id (setInterLoop P A.ident B.ident)
      ((setEntries B).filter fun e => (setKeys A).any (eqv · e.1))
      (fun e he => entries_hash wB.toSetCore e (List.mem_filter.mp he).1)
      ((entries_pairwise wB.toSetCore).filter _) hloop with ⟨n, so', a, b, c⟩ | ⟨r, a, b, c, d, e⟩
  · left
    refine ⟨n, so', Nat.le_trans a hlen, b, ?_⟩
    rw [hsets, c]
  · right
    refine ⟨r, ?_, b, c, d, e⟩
    rw [hsets, a]

/-- `set_intersection` on two sets, for an honest protocol. It walks the smaller and looks in the
larger, so the objects of the result come from the one walked. -/
def SetInterRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so o : SetObj K) (id : Nat), SetWF hf eqv so → SetWF hf eqv o →
      so.peers = [] → so.ident ≠ o.ident → id ≠ so.ident → id ≠ o.ident →
      (∃ n s, n ≤ (interB so o).used ∧ SetTooBig n ∧
        setIntersection P (.set o) id so = (.error memoryError, s)) ∨
      ∃ r, setIntersection P (.set o) id so = (.ok r, so) ∧ SetWF hf eqv r ∧
        (setEntries r).Perm ((setEntries (interB so o)).filter
          fun e => (setKeys (interA so o)).any (eqv · e.1))
theorem setInterRefines_proven : SetInterRefines := by
  intro K _ P hf eqv H so o id w wo hps hne hid1 hid2
  have hne1 : ¬ o.ident = so.ident := fun h => hne h.symm
  let s0 : SetObj K := { so with peers := [o.toSetBody] }
  have hrun0 : setIntersection P (.set o) id so =
      (match setIntersectionSets P o id s0 with
       | (r, s) => (r, { s with peers := s.peers.dropLast })) := by
    simp [setIntersection, withPeer, M.bind_run, M.get_run, hne, hne1, hps, s0]
  have hso : ({ s0 with peers := s0.peers.dropLast } : SetObj K) = so := by
    show ({ toSetBody := so.toSetBody, peers := [] } : SetObj K) = so
    rw [← hps]
  rcases interSets_spec H ⟨hne, hid1, hid2⟩ w wo s0 rfl rfl with ⟨n, s, a, b, c⟩ | ⟨r, a, b, c, _, _⟩
  · left
    refine ⟨n, { s with peers := s.peers.dropLast }, a, b, ?_⟩
    rw [hrun0, c]
  · right
    refine ⟨r, ?_, b, c⟩
    rw [hrun0, a]
    simp only
    rw [hso]

/-- Keys of `so` that no entry of `l` equals. -/
def notAmong (eqv : K → K → Bool) (l : List (K × Int)) (keys : List K) : List K :=
  keys.filter fun x => !l.any fun e => eqv x e.1

omit [DecidableEq K] in
theorem notAmong_nil (keys : List K) : notAmong eqv [] keys = keys :=
  List.filter_eq_self.mpr (fun x _ => by simp)

/-- For an honest protocol a discard cannot fail, whatever the list: what equals an entry goes. -/
theorem discardList_spec (H : HonestSet P hf eqv) :
    ∀ (l : List (K × Int)) (so : SetObj K), SetWF hf eqv so → (∀ e ∈ l, e.2 = hf e.1) →
      ∃ so', discardList P l so = (.ok (), so') ∧ SetWF hf eqv so' ∧
        (setKeys so').Perm (notAmong eqv l (setKeys so)) ∧
        so'.peers = so.peers ∧ so'.ident = so.ident := by
  intro l
  induction l with
  | nil =>
    intro so w _
    exact ⟨so, rfl, w, by rw [notAmong_nil], rfl, rfl⟩
  | cons e rest ih =>
    intro so w hh
    obtain ⟨k, h⟩ := e
    have hek : h = hf k := hh (k, h) (by simp)
    subst hek
    have hh' : ∀ e ∈ rest, e.2 = hf e.1 := fun e he => hh e (by simp [he])
    have hd : setDiscardKey P k so = setDiscardEntry P k (hf k) so := setHashKey_bind H k _ so
    have hcons : notAmong eqv ((k, hf k) :: rest) (setKeys so) =
        notAmong eqv rest ((setKeys so).filter fun x => !eqv x k) := by
      simp only [notAmong, List.filter_filter]
      apply List.filter_congr
      intro x _
      simp [List.any_cons, Bool.not_or, Bool.and_comm]
    rcases setDiscard_spec H w k with ⟨h1, h2⟩ | ⟨_, s1, a1, b1, c1, d1, e1⟩
    · rw [hd] at h2
      obtain ⟨so', a, b, c, d, e⟩ := ih so w hh'
      refine ⟨so', ?_, b, ?_, d, e⟩
      · simp only [discardList, M.bind_run, h2]
        exact a
      · rw [hcons]
        have hall : (setKeys so).filter (fun x => !eqv x k) = setKeys so := by
          apply List.filter_eq_self.mpr
          intro x hx
          have := List.any_eq_false.mp h1 x hx
          simpa using this
        rw [hall]
        exact c
    · rw [hd] at a1
      obtain ⟨so', a, b, c, d, e⟩ := ih s1 b1 hh'
      refine ⟨so', ?_, b, ?_, d.trans d1, e.trans e1⟩
      · simp only [discardList, M.bind_run, a1]
        exact a
      · rw [hcons]
        exact c.trans (c1.filter _)

/-- What is in `keys` and not in `l`, and what is in `l` and not in `keys`. -/
theorem symList_spec (H : HonestSet P hf eqv) :
    ∀ (l : List (K × Int)) (so : SetObj K), SetWF hf eqv so → (∀ e ∈ l, e.2 = hf e.1) →
      l.Pairwise (fun a b => eqv a.1 b.1 = false) →
      (∃ n s, n ≤ so.used + l.length ∧ SetTooBig n ∧ symList P l so = (.error memoryError, s)) ∨
      ∃ so', symList P l so = (.ok (), so') ∧ SetWF hf eqv so' ∧
        (setKeys so').Perm (notAmong eqv l (setKeys so) ++ (notIn eqv (setKeys so) l).map (·.1)) ∧
        so'.peers = so.peers ∧ so'.ident = so.ident := by
  intro l
  induction l with
  | nil =>
    intro so w _ _
    exact Or.inr ⟨so, rfl, w, by simp [notAmong_nil, notIn], rfl, rfl⟩
  | cons e rest ih =>
    intro so w hh hp
    obtain ⟨k, h⟩ := e
    have hek : h = hf k := hh (k, h) (by simp)
    subst hek
    have hh' : ∀ e ∈ rest, e.2 = hf e.1 := fun e he => hh e (by simp [he])
    have hrest : ∀ x ∈ rest, eqv k x.1 = false := fun x hx => (List.pairwise_cons.mp hp).1 x hx
    have hp' := (List.pairwise_cons.mp hp).2
    have hd : setDiscardKey P k so = setDiscardEntry P k (hf k) so := setHashKey_bind H k _ so
    have hsym := H.symm
    simp only [symList, symDiffStep, M.bind_run]
    rcases setDiscard_spec H w k with ⟨h1, h2⟩ | ⟨hhas, s1, a1, b1, c1, d1, e1⟩
    · -- not there: it goes in
      rw [hd] at h2
      simp only [h2, Bool.not_false, if_true, M.bind_run]
      rcases setAddEntry_spec H w k with ⟨h3, _⟩ | ⟨_, h4⟩
      · rw [h1] at h3
        simp at h3
      · rcases h4 with ⟨hb, s, h5⟩ | ⟨s2, a2, b2, c2, d2, e2⟩
        · left
          refine ⟨so.used + 1, s, by simp, hb, ?_⟩
          simp [h5]
        · have hkeys : (setKeys s2).Perm (k :: setKeys so) := by
            simpa [setKeys] using c2.map (·.1)
          rcases ih s2 b2 hh' hp' with ⟨n, s, a, b, c⟩ | ⟨so', a, b, c, d, e⟩
          · left
            have hu : s2.used = so.used + 1 := by
              have h5 := b2.used
              have h6 := w.used
              have h7 := c2.length_eq
              simp only [List.length_cons] at h7
              omega
            refine ⟨n, s, by simp only [List.length_cons]; omega, b, ?_⟩
            simp [a2, c]
          · right
            refine ⟨so', ?_, b, ?_, d.trans d2, e.trans e2⟩
            · simp [a2, a]
            · refine c.trans ?_
              have hn1 : notIn eqv (setKeys s2) rest = notIn eqv (setKeys so) rest := by
                apply List.filter_congr
                intro x hx
                rw [hkeys.any_eq]
                simp [hrest x hx]
              have hn2 : (notAmong eqv rest (setKeys s2)).Perm
                  (k :: notAmong eqv rest (setKeys so)) := by
                have := hkeys.filter (fun x => !rest.any fun e => eqv x e.1)
                simp only [notAmong] at this ⊢
                refine this.trans ?_
                rw [List.filter_cons_of_pos]
                have : rest.any (fun e => eqv k e.1) = false := by
                  apply List.any_eq_false.mpr
                  intro x hx
                  simp [hrest x hx]
                simp [this]
              have hn3 : notIn eqv (setKeys so) ((k, hf k) :: rest) =
                  (k, hf k) :: notIn eqv (setKeys so) rest := by
                simp [notIn, h1]
              have hn4 : notAmong eqv ((k, hf k) :: rest) (setKeys so) =
                  notAmong eqv rest (setKeys so) := by
                apply List.filter_congr
                intro x hx
                have := List.any_eq_false.mp h1 x hx
                have h8 : eqv x k = false := by simpa using this
                simp [List.any_cons, h8]
              rw [hn1, hn3, hn4]
              simp only [List.map_cons]
              exact (hn2.append_right _).trans (List.perm_middle.symm)
    · -- there: it goes out
      rw [hd] at a1
      simp only [a1, Bool.not_true, Bool.false_eq_true, if_false, M.pure_run]
      have hn1 : notIn eqv (setKeys s1) rest = notIn eqv (setKeys so) rest := by
        apply List.filter_congr
        intro x hx
        rw [c1.any_eq]
        have hxk := hrest x hx
        have : ((setKeys so).filter (fun y => !eqv y k)).any (eqv · x.1) =
            (setKeys so).any (eqv · x.1) := by
          cases hq : (setKeys so).any (eqv · x.1) with
          | true =>
            obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp hq
            apply List.any_eq_true.mpr
            refine ⟨y, List.mem_filter.mpr ⟨hy, ?_⟩, hyx⟩
            cases hyk : eqv y k with
            | false => rfl
            | true =>
              have h1 : eqv k x.1 = true := H.trans k y x.1 (by rw [hsym]; exact hyk) hyx
              rw [hxk] at h1
              simp at h1
          | false =>
            apply List.any_eq_false.mpr
            intro y hy
            exact List.any_eq_false.mp hq y (List.mem_filter.mp hy).1
        rw [this]
      have hn3 : notIn eqv (setKeys so) ((k, hf k) :: rest) = notIn eqv (setKeys so) rest := by
        simp [notIn, hhas]
      have hn4 : notAmong eqv ((k, hf k) :: rest) (setKeys so) =
          notAmong eqv rest ((setKeys so).filter fun x => !eqv x k) := by
        simp only [notAmong, List.filter_filter]
        apply List.filter_congr
        intro x _
        simp [List.any_cons, Bool.not_or, Bool.and_comm]
      have hu : s1.used ≤ so.used := by
        have h5 := b1.used
        have h6 := w.used
        have h7 := c1.length_eq
        have h8 := List.length_filter_le (fun x => !eqv x k) (setKeys so)
        simp only [setKeys, List.length_map] at h7 h8
        omega
      rcases ih s1 b1 hh' hp' with ⟨n, s, a, b, c⟩ | ⟨so', a, b, c, d, e⟩
      · exact Or.inl ⟨n, s, by simp only [List.length_cons]; omega, b, c⟩
      · refine Or.inr ⟨so', a, b, ?_, d.trans d1, e.trans e1⟩
        refine c.trans ?_
        rw [hn1, hn3, hn4]
        exact (c1.filter _).append_right _


/-- What the loops of an update keep: `LoopInv`, with `o` among the peers. -/
theorem loopInv_live {i0 : Nat} {p : List (SetBody K)} {o : SetObj K}
    (hmem : o.toSetBody ∈ p) (huniq : ∀ x ∈ p, x.ident = o.ident → x = o.toSetBody) (hne : i0 ≠ o.ident)
    (s : SetObj K) (hs : LoopInv hf eqv i0 p s) : s.live o.ident = o.toSetBody :=
  live_peer (by rw [hs.2.1]; exact hne) (by rw [hs.2.2]; exact find_unique hmem huniq)

theorem forList_discard (l : List (K × Int)) : ∀ s,
    forList (fun k h => do
      let _ ← setDiscardEntry P k h
      return false) l s = (do discardList P l; return false) s := by
  induction l with
  | nil => intro s; rfl
  | cons e rest ih =>
    intro s
    obtain ⟨k, h⟩ := e
    simp only [forList, discardList, M.bind_run]
    cases hb : setDiscardEntry P k h s with
    | mk r s1 =>
      cases r with
      | error e => rfl
      | ok c =>
        simp only [M.pure_run]
        have := ih s1
        simpa [M.bind_run] using this

/-- The set branch of `set_difference_update_internal`: the loop is `discardList`. -/
theorem setDiscardLoop_eq (H : HonestSet P hf eqv) {i0 : Nat} {p : List (SetBody K)} {o : SetObj K}
    (wo : SetWF hf eqv o) (hmem : o.toSetBody ∈ p)
    (huniq : ∀ x ∈ p, x.ident = o.ident → x = o.toSetBody) (hne : i0 ≠ o.ident)
    (s : SetObj K) (hs : LoopInv hf eqv i0 p s) :
    setDiscardLoop P o.ident s = (do discardList P (setEntries o); return false) s := by
  have hI := loopInv_live (hf := hf) (eqv := eqv) hmem huniq hne
  have hbody : ∀ k h s' r s'', (k, h) ∈ setEntries o → LoopInv hf eqv i0 p s' →
      (do let _ ← setDiscardEntry P k h; return false : SM K Bool) s' = (.ok r, s'') →
      LoopInv hf eqv i0 p s'' := by
    intro k h s' r s'' hm hi hb
    have hh : h = hf k := entries_hash wo.toSetCore (k, h) hm
    subst hh
    obtain ⟨w1, i1, p1⟩ := id hi
    have hd : setDiscardKey P k s' = setDiscardEntry P k (hf k) s' := setHashKey_bind H k _ s'
    simp only [M.bind_run] at hb
    rcases setDiscard_spec H w1 k with ⟨_, h2⟩ | ⟨_, s1, a1, b1, _, d1, e1⟩
    · rw [hd] at h2
      rw [h2] at hb
      simp only [M.pure_run, Prod.mk.injEq] at hb
      rw [← hb.2]
      exact hi
    · rw [hd] at a1
      rw [a1] at hb
      simp only [M.pure_run, Prod.mk.injEq] at hb
      rw [← hb.2]
      exact ⟨b1, e1.trans i1, d1.trans p1⟩
  have hfuel : setLoopFuel s o.ident = 4 * (o.mask + 1) + 64 := by
    simp only [setLoopFuel]
    rw [hI s hs]
  have hlen : ((o.table.drop 0).filterMap slotEntry).length ≤ o.mask + 1 := by
    have h2 : (setEntries o).length ≤ o.table.length := by
      rw [setEntries_eq]
      exact List.length_filterMap_le _ _
    have h3 := wo.len
    simpa [setEntries_eq] using (by omega : (setEntries o).length ≤ o.mask + 1)
  have h1 := forNext_list wo.len (fun k h => do
    let _ ← setDiscardEntry P k h
    return false) (LoopInv hf eqv i0 p) hI hbody (setLoopFuel s o.ident) 0 s hs
    (by omega) (by rw [hfuel]; omega)
  have h2 := forList_discard (P := P) (setEntries o) s
  simp only [setDiscardLoop, M.bind_run, M.get_run]
  rw [h1]
  exact h2


/-- A key of `so` equals an entry of the intersection exactly when it equals an entry of `o`. -/
theorem notAmong_inter (H : HonestSet P hf eqv) {so o : SetObj K} {tmp : List (K × Int)}
    (hp : tmp.Perm ((setEntries so).filter fun e => (setKeys o).any (eqv · e.1))) :
    notAmong eqv tmp (setKeys so) = notAmong eqv (setEntries o) (setKeys so) := by
  apply List.filter_congr
  intro x hx
  have hsym := H.symm
  have key : tmp.any (fun e => eqv x e.1) = (setEntries o).any (fun e => eqv x e.1) := by
    cases hq : (setEntries o).any (fun e => eqv x e.1) with
    | true =>
      obtain ⟨e', he', hxe⟩ := List.any_eq_true.mp hq
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      apply List.any_eq_true.mpr
      refine ⟨e, hp.symm.mem_iff.mp (List.mem_filter.mpr ⟨he, ?_⟩), H.refl _⟩
      apply List.any_eq_true.mpr
      exact ⟨e'.1, List.mem_map.mpr ⟨e', he', rfl⟩, by rw [hsym]; exact hxe⟩
    | false =>
      apply List.any_eq_false.mpr
      intro e he
      have h1 := List.mem_filter.mp (hp.mem_iff.mp he)
      obtain ⟨y, hy, hye⟩ := List.any_eq_true.mp h1.2
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp hy
      have h2 := List.any_eq_false.mp hq e' he'
      intro hxe
      have h3 : eqv x e'.1 = true := H.trans x e.1 e'.1 hxe (by rw [hsym]; exact hye)
      simp [h3] at h2
  simp only [key]

/-- The tail of `set_difference_update_internal`. -/
theorem setPurgeDummies_spec (H : HonestSet P hf eqv) {s : SetObj K} (w : SetWF hf eqv s) :
    (SetTooBig s.used ∧ ∃ s', setPurgeDummies s = (.error memoryError, s')) ∨
    ∃ s', setPurgeDummies s = (.ok (), s') ∧ SetWF hf eqv s' ∧
      (setEntries s').Perm (setEntries s) ∧ s'.peers = s.peers ∧ s'.ident = s.ident := by
  by_cases h : s.fill - s.used ≤ s.mask / 4
  · right
    refine ⟨s, ?_, w, List.Perm.refl _, rfl, rfl⟩
    simp only [setPurgeDummies, M.bind_run, M.get_run]
    rw [if_pos h]
    rfl
  · have hg : setPurgeDummies s = setTableResize (setGrowMin s.used) s := by
      simp only [setPurgeDummies, M.bind_run, M.get_run]
      rw [if_neg h]
      rfl
    rw [hg]
    rcases setTableResize_spec H.symm s w.toSetCore (setGrowMin s.used)
        (by simp only [setGrowMin]; split <;> omega) with ⟨h1, h2⟩ | ⟨s', a, b, c, d, e, _⟩
    · exact Or.inl ⟨h1, s, h2⟩
    · exact Or.inr ⟨s', a, b, c, d, e⟩

/-- `set_difference_update_internal` from another set, for an honest protocol: what equals a key of
`o` goes, on either of its routes, and the one way to fail is a table too big. -/
def SetDiffUpdateRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so o : SetObj K) (id : Nat), SetWF hf eqv so → SetWF hf eqv o →
      so.peers = [] → so.ident ≠ o.ident → id ≠ so.ident → id ≠ o.ident →
      (∃ n s, n ≤ so.used ∧ SetTooBig n ∧
        setDifferenceUpdateInternal P (.set o) id so = (.error memoryError, s)) ∨
      ∃ so', setDifferenceUpdateInternal P (.set o) id so = (.ok (), so') ∧ SetWF hf eqv so' ∧
        (setKeys so').Perm (notAmong eqv (setEntries o) (setKeys so)) ∧ so'.peers = []
theorem setDiffUpdateRefines_proven : SetDiffUpdateRefines := by
  intro K _ P hf eqv H so o id w wo hps hne hid1 hid2
  have hne1 : ¬ o.ident = so.ident := fun h => hne h.symm
  let s0 : SetObj K := { so with peers := [o.toSetBody] }
  have w0 : SetWF hf eqv s0 := { toSetCore := w.toSetCore.of_fields rfl rfl rfl rfl, load := w.load }
  have hk0 : setKeys s0 = setKeys so := rfl
  have hlive : s0.live o.ident = o.toSetBody := live_peer hne (by simp [s0])
  have hrun : setDifferenceUpdateInternal P (.set o) id so =
      (match setDiffUpdateSets P o id s0 with
       | (.ok _, s) => setPurgeDummies { s with peers := s.peers.dropLast }
       | (.error e, s) => (.error e, { s with peers := s.peers.dropLast })) := by
    simp only [setDifferenceUpdateInternal, M.bind_run, M.get_run]
    simp only [hne, hne1, beq_iff_eq, decide_false, Bool.false_eq_true, if_false]
    rw [M.bind_run]
    have h1 : withPeer o (setDiffUpdateSets P o id) so =
        (match setDiffUpdateSets P o id s0 with
         | (r, s) => (r, { s with peers := s.peers.dropLast })) := by
      simp [withPeer, hne, hps, s0]
    rw [h1]
    cases setDiffUpdateSets P o id s0 with
    | mk r s => cases r <;> rfl
  -- both routes end the same way
  have after : ∀ s1 : SetObj K, setDiffUpdateSets P o id s0 = (.ok (), s1) → SetWF hf eqv s1 →
      (setKeys s1).Perm (notAmong eqv (setEntries o) (setKeys so)) → s1.peers = [o.toSetBody] →
      (∃ n s, n ≤ so.used ∧ SetTooBig n ∧
        setDifferenceUpdateInternal P (.set o) id so = (.error memoryError, s)) ∨
      ∃ so', setDifferenceUpdateInternal P (.set o) id so = (.ok (), so') ∧ SetWF hf eqv so' ∧
        (setKeys so').Perm (notAmong eqv (setEntries o) (setKeys so)) ∧ so'.peers = [] := by
    intro s1 h1 w1 hk hp1
    let s2 : SetObj K := { s1 with peers := s1.peers.dropLast }
    have w2 : SetWF hf eqv s2 :=
      { toSetCore := w1.toSetCore.of_fields rfl rfl rfl rfl, load := w1.load }
    have hk2 : setKeys s2 = setKeys s1 := rfl
    have hu : s2.used ≤ so.used := by
      have h3 := w2.used
      have h4 := w.used
      have h5 := hk.length_eq
      have h6 := List.length_filter_le (fun x => !(setEntries o).any fun e => eqv x e.1) (setKeys so)
      simp only [notAmong, setKeys, List.length_map] at h5 h6
      show s1.used ≤ so.used
      have h7 : s1.used = (setEntries s1).length := w1.used
      omega
    rcases setPurgeDummies_spec H w2 with ⟨hb, s', h2⟩ | ⟨s3, a, b, c, d, _⟩
    · left
      exact ⟨s2.used, s', hu, hb, by rw [hrun, h1]; exact h2⟩
    · right
      refine ⟨s3, by rw [hrun, h1]; exact a, b, ?_, ?_⟩
      · have hc : (setKeys s3).Perm (setKeys s2) := by simpa [setKeys] using c.map (·.1)
        rw [hk2] at hc
        exact hc.trans hk
      · rw [d]
        simp [s2, hp1]
  by_cases hbig : o.used >>> 3 > so.used
  · -- the intersection route
    have hgt : o.used > so.used := by
      have : o.used >>> 3 ≤ o.used := by
        rw [Nat.shiftRight_eq_div_pow]
        exact Nat.div_le_self _ _
      omega
    have hA : interA so o = o := by simp [interA, hgt]
    have hB : interB so o = so := by simp [interB, hgt]
    have hinter : setIntersection P (.set o) id s0 = setIntersectionSets P o id s0 := by
      simp [setIntersection, withPeer, M.bind_run, M.get_run, hne, hne1, s0]
    have hunf : setDiffUpdateSets P o id s0 =
        (match setIntersectionSets P o id s0 with
         | (.ok tmp, s) => discardList P (setEntries tmp) s
         | (.error e, s) => (.error e, s)) := by
      simp only [setDiffUpdateSets, M.bind_run, M.get_run, hlive]
      have : (o.toSetBody.used >>> 3 > s0.used) := hbig
      simp only [this, if_true, M.bind_run, hinter]
      cases setIntersectionSets P o id s0 with
      | mk r s => cases r <;> rfl
    rcases interSets_spec H ⟨hne, hid1, hid2⟩ w wo s0 rfl rfl with
      ⟨n, s, a, b, c⟩ | ⟨r, a, b, c, _, _⟩
    · left
      rw [hB] at a
      refine ⟨n, { s with peers := s.peers.dropLast }, a, b, ?_⟩
      rw [hrun, hunf, c]
    · rw [hA, hB] at c
      obtain ⟨s1, a1, b1, c1, d1, _⟩ := discardList_spec H (setEntries r) s0 w0
        (entries_hash b.toSetCore)
      have hk : (setKeys s1).Perm (notAmong eqv (setEntries o) (setKeys so)) := by
        rw [hk0, notAmong_inter H c] at c1
        exact c1
      exact after s1 (by rw [hunf, a]; exact a1) b1 hk d1
  · -- the loop
    have hinv : LoopInv hf eqv so.ident [o.toSetBody] s0 := ⟨w0, rfl, rfl⟩
    have hloop := setDiscardLoop_eq H wo (p := [o.toSetBody]) (by simp)
      (fun x hx _ => by simpa using hx) hne s0 hinv
    obtain ⟨s1, a1, b1, c1, d1, _⟩ := discardList_spec H (setEntries o) s0 w0
      (entries_hash wo.toSetCore)
    have hunf : setDiffUpdateSets P o id s0 = (.ok (), s1) := by
      simp only [setDiffUpdateSets, M.bind_run, M.get_run, hlive]
      have : ¬ (o.toSetBody.used >>> 3 > s0.used) := hbig
      simp only [this, if_false, M.bind_run, hloop, a1, M.pure_run]
    rw [hk0] at c1
    exact after s1 hunf b1 c1 d1


/-- `set_symmetric_difference_update_set`'s loop is `symList`, as long as the source stays. -/
theorem symDiffSet_eq (H : HonestSet P hf eqv) {i0 : Nat} {p : List (SetBody K)} {o : SetObj K}
    (wo : SetWF hf eqv o) (hmem : o.toSetBody ∈ p)
    (huniq : ∀ x ∈ p, x.ident = o.ident → x = o.toSetBody) (hne : i0 ≠ o.ident)
    (s : SetObj K) (hs : LoopInv hf eqv i0 p s) :
    (forNext o.ident (fun key hash => do
      symDiffStep P key hash
      return false) (setLoopFuel s o.ident) 0 s) =
      (do symList P (setEntries o); return false) s := by
  have hI := loopInv_live (hf := hf) (eqv := eqv) hmem huniq hne
  have hbody : ∀ k h s' r s'', (k, h) ∈ setEntries o → LoopInv hf eqv i0 p s' →
      (do symDiffStep P k h; return false : SM K Bool) s' = (.ok r, s'') →
      LoopInv hf eqv i0 p s'' := by
    intro k h s' r s'' hm hi hb
    have hh : h = hf k := entries_hash wo.toSetCore (k, h) hm
    subst hh
    obtain ⟨w1, i1, p1⟩ := id hi
    have hd : setDiscardKey P k s' = setDiscardEntry P k (hf k) s' := setHashKey_bind H k _ s'
    simp only [M.bind_run, symDiffStep] at hb
    rcases setDiscard_spec H w1 k with ⟨h1, h2⟩ | ⟨_, s1, a1, b1, _, d1, e1⟩
    · rw [hd] at h2
      rw [h2] at hb
      simp only [Bool.not_false, if_true, M.bind_run] at hb
      rcases setAddEntry_spec H w1 k with ⟨_, h3⟩ | ⟨_, h4⟩
      · rw [h3] at hb
        simp only [M.pure_run, Prod.mk.injEq] at hb
        rw [← hb.2]
        exact hi
      · rcases h4 with ⟨_, s3, h5⟩ | ⟨s2, a2, b2, _, d2, e2⟩
        · rw [h5] at hb
          simp at hb
        · rw [a2] at hb
          simp only [M.pure_run, Prod.mk.injEq] at hb
          rw [← hb.2]
          exact ⟨b2, e2.trans i1, d2.trans p1⟩
    · rw [hd] at a1
      rw [a1] at hb
      simp only [Bool.not_true, Bool.false_eq_true, if_false, M.pure_run, Prod.mk.injEq] at hb
      rw [← hb.2]
      exact ⟨b1, e1.trans i1, d1.trans p1⟩
  have hfuel : setLoopFuel s o.ident = 4 * (o.mask + 1) + 64 := by
    simp only [setLoopFuel]
    rw [hI s hs]
  have hlen : ((o.table.drop 0).filterMap slotEntry).length ≤ o.mask + 1 := by
    have h2 : (setEntries o).length ≤ o.table.length := by
      rw [setEntries_eq]
      exact List.length_filterMap_le _ _
    have h3 := wo.len
    simpa [setEntries_eq] using (by omega : (setEntries o).length ≤ o.mask + 1)
  have h1 := forNext_list wo.len (fun k h => do
    symDiffStep P k h
    return false) (LoopInv hf eqv i0 p) hI hbody (setLoopFuel s o.ident) 0 s hs
    (by omega) (by rw [hfuel]; omega)
  rw [h1]
  have h2 : ∀ (l : List (K × Int)) (s : SetObj K),
      forList (fun k h => do symDiffStep P k h; return false) l s =
        (do symList P l; return false) s := by
    intro l
    induction l with
    | nil => intro s; rfl
    | cons e rest ih =>
      intro s
      obtain ⟨k, h⟩ := e
      simp only [forList, symList, M.bind_run]
      cases hb : symDiffStep P k h s with
      | mk r s1 =>
        cases r with
        | error e => rfl
        | ok c =>
          simp only [M.pure_run]
          have := ih s1
          simpa [M.bind_run] using this
  exact h2 _ s

/-- `set_symmetric_difference_update_impl` from another set, for an honest protocol: what the two
share goes, and what only `o` has comes in. -/
def SetSymUpdateRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so o : SetObj K) (id : Nat), SetWF hf eqv so → SetWF hf eqv o →
      so.peers = [] →
      (so.ident = o.ident →
        setSymmetricDifferenceUpdate P (.set o) id so = (.ok (), setClearInternal so)) ∧
      (so.ident ≠ o.ident →
        (∃ n s, n ≤ so.used + o.used ∧ SetTooBig n ∧
          setSymmetricDifferenceUpdate P (.set o) id so = (.error memoryError, s)) ∨
        ∃ so', setSymmetricDifferenceUpdate P (.set o) id so = (.ok (), so') ∧ SetWF hf eqv so' ∧
          (setKeys so').Perm (notAmong eqv (setEntries o) (setKeys so) ++
            (notIn eqv (setKeys so) (setEntries o)).map (·.1)) ∧ so'.peers = [])
theorem setSymUpdateRefines_proven : SetSymUpdateRefines := by
  intro K _ P hf eqv H so o id w wo hps
  refine ⟨fun he => ?_, fun hne => ?_⟩
  · have h1 : o.ident = so.ident := he.symm
    simp [setSymmetricDifferenceUpdate, M.bind_run, M.get_run, M.put_run, h1]
  · have hne1 : ¬ o.ident = so.ident := fun h => hne h.symm
    let s0 : SetObj K := { so with peers := [o.toSetBody] }
    have w0 : SetWF hf eqv s0 :=
      { toSetCore := w.toSetCore.of_fields rfl rfl rfl rfl, load := w.load }
    have hrun : setSymmetricDifferenceUpdate P (.set o) id so =
        (match symDiffSet P o.ident s0 with
         | (r, s) => (r, { s with peers := s.peers.dropLast })) := by
      simp [setSymmetricDifferenceUpdate, M.bind_run, M.get_run, hne1, withPeer, hne, hps, s0]
    have hinv : LoopInv hf eqv so.ident [o.toSetBody] s0 := ⟨w0, rfl, rfl⟩
    have hloop := symDiffSet_eq H wo (p := [o.toSetBody]) (by simp)
      (fun x hx _ => by simpa using hx) hne s0 hinv
    have hsets : symDiffSet P o.ident s0 =
        (match symList P (setEntries o) s0 with
         | (.ok _, s) => (.ok (), s)
         | (.error e, s) => (.error e, s)) := by
      simp only [symDiffSet, M.bind_run, M.get_run]
      rw [hloop, M.bind_run]
      cases symList P (setEntries o) s0 with
      | mk r s => cases r <;> rfl
    rcases symList_spec H (setEntries o) s0 w0 (entries_hash wo.toSetCore)
        (entries_pairwise wo.toSetCore) with ⟨n, s, a, b, c⟩ | ⟨s1, a, b, c, d, _⟩
    · left
      refine ⟨n, { s with peers := s.peers.dropLast }, ?_, b, ?_⟩
      · have h1 := wo.used
        have h2 : s0.used = so.used := rfl
        omega
      · rw [hrun, hsets, c]
    · right
      refine ⟨{ s1 with peers := s1.peers.dropLast }, ?_,
        { toSetCore := b.toSetCore.of_fields rfl rfl rfl rfl, load := b.load }, c, ?_⟩
      · rw [hrun, hsets, a]
      · simp [d, s0]


/-- A list of keys all found in another, with no two equal in either, is no longer than it. -/
theorem pigeon (H : HonestSet P hf eqv) :
    ∀ (l m : List K), l.Pairwise (fun a b => eqv a b = false) →
      m.Pairwise (fun a b => eqv a b = false) → l.all (fun k => m.any (eqv · k)) = true →
      l.length ≤ m.length := by
  intro l
  induction l with
  | nil => intro _ _ _ _; simp
  | cons x t ih =>
    intro m hl hm ha
    have hall := List.all_eq_true.mp ha
    obtain ⟨y, hy, hyx⟩ := List.any_eq_true.mp (hall x (by simp))
    have hsym := H.symm
    let m' := m.filter fun w => !eqv w x
    have hlt : m'.length < m.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨y, hy, by simp [hyx]⟩
    have hrest : t.all (fun k => m'.any (eqv · k)) = true := by
      apply List.all_eq_true.mpr
      intro z hz
      obtain ⟨w, hw, hwz⟩ := List.any_eq_true.mp (hall z (by simp [hz]))
      apply List.any_eq_true.mpr
      refine ⟨w, List.mem_filter.mpr ⟨hw, ?_⟩, hwz⟩
      have hxz : eqv x z = false := (List.pairwise_cons.mp hl).1 z hz
      cases hq : eqv w x with
      | false => rfl
      | true =>
        have : eqv x z = true := H.trans x w z (by rw [hsym]; exact hq) hwz
        rw [hxz] at this
        simp at this
    have := ih m' (List.pairwise_cons.mp hl).2 (hm.filter _) hrest
    simp only [List.length_cons]
    omega

/-- A body that leaves the state alone, over a list: the first `true` stops it. -/
theorem forList_pure (body : K → Int → SM K Bool) (q : K → Bool) (s : SetObj K) :
    ∀ l : List (K × Int), (∀ e ∈ l, body e.1 e.2 s = (.ok (q e.1), s)) →
      forList body l s = (.ok (l.any fun e => q e.1), s) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons e rest ih =>
    intro h
    obtain ⟨k, c⟩ := e
    have h1 := h (k, c) (by simp)
    simp only [forList, M.bind_run]
    rw [h1]
    cases hq : q k with
    | true => simp [hq]
    | false =>
      simp only [hq, Bool.false_eq_true, if_false, List.any_cons, Bool.false_or]
      exact ih fun e he => h e (by simp [he])

/-- `set_issubset_impl` on two sets, for an honest protocol: the list answer, on the size shortcut as
well as through the loop. -/
def SetSubsetRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so o : SetObj K) (id : Nat), SetWF hf eqv so → SetWF hf eqv o →
      so.peers = [] → so.ident ≠ o.ident →
      setIssubset P (.set o) id so = (.ok ((setKeys so).all fun k => (setKeys o).any (eqv · k)), so)
theorem setSubsetRefines_proven : SetSubsetRefines := by
  intro K _ P hf eqv H so o id w wo hps hne
  have hne1 : ¬ o.ident = so.ident := fun h => hne h.symm
  let s0 : SetObj K := { so with peers := [o.toSetBody] }
  have w0 : SetWF hf eqv s0 := { toSetCore := w.toSetCore.of_fields rfl rfl rfl rfl, load := w.load }
  have hlive : s0.live o.ident = o.toSetBody := live_peer hne (by simp [s0])
  have hk0 : setKeys s0 = setKeys so := rfl
  have hso : ({ s0 with peers := s0.peers.dropLast } : SetObj K) = so := by
    show ({ toSetBody := so.toSetBody, peers := [] } : SetObj K) = so
    rw [← hps]
  have hrun : setIssubset P (.set o) id so =
      (match setSubsetSets P o s0 with
       | (r, s) => (r, { s with peers := s.peers.dropLast })) := by
    simp [setIssubset, M.bind_run, M.get_run, withPeer, hne, hps, s0]
  have hkp : ∀ {X : SetObj K}, SetWF hf eqv X → (setKeys X).Pairwise (fun a b => eqv a b = false) := by
    intro X wx
    simpa [setKeys, List.pairwise_map] using entries_pairwise wx.toSetCore
  have hlen : ∀ {X : SetObj K}, SetWF hf eqv X → (setKeys X).length = X.used := by
    intro X wx
    have := wx.used
    simp [setKeys, this]
  rw [hrun]
  by_cases hgt : so.used > o.used
  · have hsets : setSubsetSets P o s0 = (.ok false, s0) := by
      simp only [setSubsetSets, M.bind_run, M.get_run, hlive]
      have : s0.used > o.toSetBody.used := hgt
      simp [this]
    rw [hsets]
    simp only
    rw [hso]
    have hall : (setKeys so).all (fun k => (setKeys o).any (eqv · k)) = false := by
      cases hq : (setKeys so).all (fun k => (setKeys o).any (eqv · k)) with
      | false => rfl
      | true =>
        have := pigeon H (setKeys so) (setKeys o) (hkp w) (hkp wo) hq
        rw [hlen w, hlen wo] at this
        omega
    rw [hall]
  · have hfuel : setLoopFuel s0 so.ident = 4 * (so.mask + 1) + 64 := by
      have : s0.live so.ident = s0.toSetBody := by simp [SetObj.live, s0]
      simp only [setLoopFuel]
      rw [this]
    have hbody0 : ∀ k, onSet o.ident (setContainsEntry P k (hf k)) s0 =
        (.ok ((setKeys o).any (eqv · k)), s0) := fun k =>
      onSet_contains H wo k hne (by simp [s0]) (fun x hx _ => by simpa [s0] using hx)
        (fun x hx => by
          have : x = o.toSetBody := by simpa [s0] using hx
          rw [this]
          exact fun e => hne e.symm)
    let body : K → Int → SM K Bool := fun key hash => do
      let rv ← onSet o.ident (setContainsEntry P key hash)
      return !rv
    have hlist := forNext_list (b := s0) w0.len body (fun s => s = s0)
      (fun s hs => by rw [hs]; simp [SetObj.live])
      (fun k h s r s' hm hs hb => by
        have hh : h = hf k := entries_hash w0.toSetCore (k, h) hm
        subst hh
        subst hs
        simp only [body, M.bind_run, hbody0, M.pure_run, Prod.mk.injEq] at hb
        exact hb.2.symm)
      (setLoopFuel s0 so.ident) 0 s0 rfl (by omega) (by
        have h2 : (setEntries s0).length ≤ s0.table.length := by
          rw [setEntries_eq]
          exact List.length_filterMap_le _ _
        have h3 := w0.len
        have h4 : ((s0.table.drop 0).filterMap slotEntry).length ≤ s0.mask + 1 := by
          simpa [setEntries_eq] using (by omega : (setEntries s0).length ≤ s0.mask + 1)
        rw [hfuel]
        have : s0.mask = so.mask := rfl
        omega)
    have hl2 := forList_pure body (fun k => !(setKeys o).any (eqv · k)) s0 (setEntries s0)
      (fun e he => by
        have hh : e.2 = hf e.1 := entries_hash w0.toSetCore e he
        obtain ⟨k, c⟩ := e
        simp only at hh
        subst hh
        simp only [body, M.bind_run, hbody0, M.pure_run])
    have hsets : setSubsetSets P o s0 =
        (.ok (!(setEntries s0).any fun e => !(setKeys o).any (eqv · e.1)), s0) := by
      simp only [setSubsetSets, M.bind_run, M.get_run, hlive]
      have h5 : ¬ s0.used > o.toSetBody.used := hgt
      simp only [h5, if_false]
      have e : (s0.table.drop 0).filterMap slotEntry = setEntries s0 := (setEntries_eq s0).symm
      have h6 : s0.ident = so.ident := rfl
      have h7 : forNext s0.ident body (setLoopFuel s0 so.ident) 0 s0 =
          forList body (setEntries s0) s0 := by
        rw [← e]
        exact hlist
      show (forNext s0.ident body (setLoopFuel s0 s0.ident) 0 >>= fun miss => pure (!miss)) s0 = _
      rw [M.bind_run]
      have h8 : setLoopFuel s0 s0.ident = setLoopFuel s0 so.ident := rfl
      rw [h8, h7, hl2]
      rfl
    rw [hsets]
    simp only
    rw [hso]
    have hconv : (!(setEntries s0).any fun e => !(setKeys o).any (eqv · e.1)) =
        (setKeys so).all fun k => (setKeys o).any (eqv · k) := by
      rw [← hk0, Bool.eq_iff_iff]
      constructor
      · intro h
        apply List.all_eq_true.mpr
        intro k hk
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hk
        have h1 : (setEntries s0).any (fun e => !(setKeys o).any (eqv · e.1)) = false := by
          simpa using h
        have := List.any_eq_false.mp h1 e he
        simpa using this
      · intro h
        have h1 : (setEntries s0).any (fun e => !(setKeys o).any (eqv · e.1)) = false := by
          apply List.any_eq_false.mpr
          intro e he
          have := List.all_eq_true.mp h e.1 (List.mem_map.mpr ⟨e, he, rfl⟩)
          simp [this]
        simp [h1]
    rw [hconv]


/-- A `set_next` loop whose body changes nothing and only answers about each key. -/
theorem forNext_probe {B s0 : SetObj K} (wB : SetWF hf eqv B)
    (hlive : s0.live B.ident = B.toSetBody) (q : K → Bool) (body : K → Int → SM K Bool)
    (hb : ∀ k, body k (hf k) s0 = (.ok (q k), s0)) (fuel : Nat) (hfuel : B.mask + 1 < fuel) :
    forNext B.ident body fuel 0 s0 = (.ok ((setEntries B).any fun e => q e.1), s0) := by
  have h1 := forNext_list wB.len body (fun s => s = s0) (fun s hs => by rw [hs]; exact hlive)
    (fun k h s r s' hm hs hb' => by
      have hh : h = hf k := entries_hash wB.toSetCore (k, h) hm
      subst hh
      subst hs
      rw [hb k] at hb'
      simp only [Prod.mk.injEq] at hb'
      exact hb'.2.symm)
    fuel 0 s0 rfl (by omega) (by
      have h2 : (setEntries B).length ≤ B.table.length := by
        rw [setEntries_eq]
        exact List.length_filterMap_le _ _
      have h3 := wB.len
      have h4 : ((B.table.drop 0).filterMap slotEntry).length ≤ B.mask + 1 := by
        simpa [setEntries_eq] using (by omega : (setEntries B).length ≤ B.mask + 1)
      omega)
  have h2 := forList_pure body q s0 (setEntries B) (fun e he => by
    have hh : e.2 = hf e.1 := entries_hash wB.toSetCore e he
    obtain ⟨k, c⟩ := e
    simp only at hh
    subst hh
    exact hb k)
  rw [h1]
  exact h2

theorem onSet_self {α : Type} {s : SetObj K} {m : SM K α} {r : Py α}
    (h : m s = (r, s)) : onSet s.ident m s = (r, s) := by
  simp [onSet, SetObj.swapIn, h]

/-- `set_isdisjoint_impl` on two exact sets, for an honest protocol. -/
def SetDisjointRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ so o : SetObj K, SetWF hf eqv so → SetWF hf eqv o →
      so.peers = [] → so.ident ≠ o.ident → o.exact = true →
      setIsdisjoint P (.set o) so = (.ok (!(setKeys so).any fun k => (setKeys o).any (eqv · k)), so)
theorem setDisjointRefines_proven : SetDisjointRefines := by
  intro K _ P hf eqv H so o w wo hps hne hex
  have hne1 : ¬ o.ident = so.ident := fun h => hne h.symm
  let s0 : SetObj K := { so with peers := [o.toSetBody] }
  have w0 : SetWF hf eqv s0 := { toSetCore := w.toSetCore.of_fields rfl rfl rfl rfl, load := w.load }
  have hlive : s0.live o.ident = o.toSetBody := live_peer hne (by simp [s0])
  have hself : s0.live s0.ident = s0.toSetBody := by simp [SetObj.live]
  have hk0 : setKeys s0 = setKeys so := rfl
  have hso : ({ s0 with peers := s0.peers.dropLast } : SetObj K) = so := by
    show ({ toSetBody := so.toSetBody, peers := [] } : SetObj K) = so
    rw [← hps]
  have hrun : setIsdisjoint P (.set o) so =
      (match setDisjointSets P o s0 with
       | (r, s) => (r, { s with peers := s.peers.dropLast })) := by
    simp [setIsdisjoint, M.bind_run, M.get_run, hne1, hex, withPeer, hne, hps, s0]
  have honO : ∀ k, onSet o.ident (setContainsEntry P k (hf k)) s0 =
      (.ok ((setKeys o).any (eqv · k)), s0) := fun k =>
    onSet_contains H wo k hne (by simp [s0]) (fun x hx _ => by simpa [s0] using hx)
      (fun x hx => by
        have : x = o.toSetBody := by simpa [s0] using hx
        rw [this]
        exact fun e => hne e.symm)
  have honS : ∀ k, onSet s0.ident (setContainsEntry P k (hf k)) s0 =
      (.ok ((setKeys so).any (eqv · k)), s0) := fun k =>
    onSet_self (setContains_hash H w0 k)
  have hsymm : ∀ a b : List K,
      (a.any fun k => b.any (eqv · k)) = (b.any fun k => a.any (eqv · k)) := by
    intro a b
    rw [Bool.eq_iff_iff]
    simp only [List.any_eq_true]
    constructor
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨y, hy, x, hx, by rw [H.symm]; exact hxy⟩
    · rintro ⟨x, hx, y, hy, hxy⟩
      exact ⟨y, hy, x, hx, by rw [H.symm]; exact hxy⟩
  have hanyMap : ∀ (X : SetObj K) (q : K → Bool),
      ((setEntries X).any fun e => q e.1) = (setKeys X).any q := by
    intro X q
    simp [setKeys, List.any_map, Function.comp_def]
  have hsets : setDisjointSets P o s0 =
      (.ok (!(setKeys so).any fun k => (setKeys o).any (eqv · k)), s0) := by
    simp only [setDisjointSets, M.bind_run, M.get_run, hlive]
    by_cases hgt : o.used > so.used
    · have e1 : (if o.toSetBody.used > s0.used then o.toSetBody.ident else s0.ident) = o.ident :=
        if_pos hgt
      have e2 : (if o.toSetBody.used > s0.used then s0.ident else o.toSetBody.ident) = s0.ident :=
        if_pos hgt
      rw [e1, e2]
      have hfuel : setLoopFuel s0 s0.ident = 4 * (s0.mask + 1) + 64 := by
        simp only [setLoopFuel]
        rw [hself]
      have h := forNext_probe w0 hself (fun k => (setKeys o).any (eqv · k))
        (fun key hash => onSet o.ident (setContainsEntry P key hash)) honO
        (setLoopFuel s0 s0.ident) (by rw [hfuel]; omega)
      rw [h]
      have hm : ((setEntries s0).any fun e => (setKeys o).any (eqv · e.1)) =
          (setKeys so).any fun k => (setKeys o).any (eqv · k) :=
        hanyMap s0 (fun k => (setKeys o).any (eqv · k))
      simp only [M.pure_run]
      rw [hm]
    · have e1 : (if o.toSetBody.used > s0.used then o.toSetBody.ident else s0.ident) = s0.ident :=
        if_neg hgt
      have e2 : (if o.toSetBody.used > s0.used then s0.ident else o.toSetBody.ident) = o.ident :=
        if_neg hgt
      rw [e1, e2]
      have hfuel : setLoopFuel s0 o.ident = 4 * (o.mask + 1) + 64 := by
        simp only [setLoopFuel]
        rw [hlive]
      have h := forNext_probe wo hlive (fun k => (setKeys so).any (eqv · k))
        (fun key hash => onSet s0.ident (setContainsEntry P key hash)) honS
        (setLoopFuel s0 o.ident) (by rw [hfuel]; omega)
      rw [h]
      have hm : ((setEntries o).any fun e => (setKeys so).any (eqv · e.1)) =
          (setKeys o).any fun k => (setKeys so).any (eqv · k) :=
        hanyMap o (fun k => (setKeys so).any (eqv · k))
      simp only [M.pure_run]
      rw [hm, hsymm]
  rw [hrun, hsets]
  simp only
  rw [hso]

/-- `set_copy_impl`, for an honest protocol: a new set with the same entries, and `so` unchanged. -/
def SetCopyRefines : Prop :=
  ∀ (K : Type) [DecidableEq K] (P : Proto K (SetObj K)) (hf : K → Int) (eqv : K → K → Bool),
    HonestSet P hf eqv → ∀ (so : SetObj K) (id : Nat), SetWF hf eqv so → so.peers = [] →
      id ≠ so.ident →
      (∃ s, setCopy P id so = (.error memoryError, s) ∧
        (SetResizeRefused ((0 + so.used) * 2) ∨ ∃ n, n ≤ 0 + so.used ∧ SetTooBig n)) ∨
      ∃ r, setCopy P id so = (.ok r, so) ∧ SetWF hf eqv r ∧ (setEntries r).Perm (setEntries so) ∧
        r.ident = id ∧ r.peers = []
theorem setCopyRefines_proven : SetCopyRefines := by
  intro K _ P hf eqv H so id w hps hid
  let p := [so.toSetBody]
  obtain ⟨wr, her⟩ := newBasetype_wf hf eqv so.toSetBody id p
  let r0 : SetObj K := { newBasetype so.toSetBody id with peers := p }
  have hkr : setKeys r0 = [] := by simp [setKeys, r0, her]
  have hp0 : so.toSetBody :: so.peers = p := by rw [hps]
  have hfind : r0.peers.find? (·.ident == so.ident) = some so.toSetBody := by simp [r0, p]
  have hu0 : r0.used = 0 := rfl
  have hne0 : r0.ident ≠ so.ident := hid
  have hm : setMerge P so r0 = setMergeIn P so.ident r0 := by
    have : (r0.peers.any (·.ident == so.ident)) = true := by simp [r0, p]
    simp [setMerge, withPeer, this]
  have hcopy : setCopy P id so =
      (match onResult (newBasetype so.toSetBody id) (setMerge P so) so with
       | (.ok x, s) => (.ok x.2, s)
       | (.error e, s) => (.error e, s)) := by
    simp only [setCopy, M.bind_run, M.get_run]
    cases onResult (newBasetype so.toSetBody id) (setMerge P so) so with
    | mk r s => cases r <;> rfl
  have hstart : ({ newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } : SetObj K)
      = r0 := by
    simp only [r0, hp0]
  rcases setMergeIn_spec H wr w hne0 hfind with ⟨s, a, b⟩ | ⟨r1, a, b, c, d, e⟩
  · left
    have h0 : setMerge P so { newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } =
        (.error memoryError, s) := by
      rw [hstart, hm, a]
    obtain ⟨so', h1⟩ := onResult_err (r := newBasetype so.toSetBody id) (so := so) h0
    exact ⟨so', by rw [hcopy, h1], b⟩
  · right
    have h0 : setMerge P so { newBasetype so.toSetBody id with peers := so.toSetBody :: so.peers } =
        (.ok (), r1) := by
      rw [hstart, hm, a]
    have hp1 : r1.peers = so.toSetBody :: so.peers := by rw [d, hp0]
    have h1 := onResult_ok (r := newBasetype so.toSetBody id) (so := so) h0 hp1
    refine ⟨{ r1 with peers := [] }, by rw [hcopy, h1],
      { toSetCore := b.toSetCore.of_fields rfl rfl rfl rfl, load := b.load }, ?_, e, rfl⟩
    show (setEntries r1).Perm _
    have hni : notIn eqv [] (setEntries so) = setEntries so := by simp [notIn]
    rw [her, hkr, hni] at c
    simpa using c

end PyLean.DictSet
