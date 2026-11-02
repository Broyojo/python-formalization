import PyLean.DictSet.Props2
import PyLean.DictSet.Stable

/-!
The wrappers over lookup, insertion and deletion, and `update`, on a well-formed combined table.
`mergeLoop` with `override == 1` is `d[k] = v` for each pair of the other dict, with the hash
already known, so `update` folds `assocSet` over the source.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

section
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- `dict.pop(key, default)`: `dict_pop_default`. -/
theorem popDefault_spec (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d)
    (hfz : d.frozen = false) (key : K) (dflt : Option V) :
    (assocGet eqv (dictAssoc d) key = none ∧
      dictPopDefault P key dflt d =
        (match dflt with
         | some x => (.ok x, d)
         | none => (.error (keyErr P key), d))) ∨
    ∃ v d', assocGet eqv (dictAssoc d) key = some v ∧ dictPopDefault P key dflt d = (.ok v, d') ∧
      DictInv hf eqv P.isStr d' ∧ dictAssoc d' = assocDel eqv (dictAssoc d) key := by
  rcases pop_spec H d hd key hfz with ⟨h1, h2⟩ | ⟨v, d', h1, h2, h3, h4⟩
  · left
    refine ⟨h1, ?_⟩
    simp only [dictPopDefault, M.bind_run, h2]
    cases dflt <;> rfl
  · right
    refine ⟨v, d', h1, ?_, h3, h4⟩
    simp only [dictPopDefault, M.bind_run, h2]
    rfl

/-- `_PyDict_StoreSubscript`: `d[key] = v` and `del d[key]`, through one entry point. -/
theorem assSub_spec (d : PyDict K V) (key : K) (w : Option V) :
    dictAssSub P key w d =
      match w with
      | none => dictDelItem P key d
      | some v => dictSetItem P key v d := by
  cases w <;> rfl

/-- The C-string entry points: a key that could be built behaves as that key, and a failure to
build one raises before the dict is touched. -/
theorem withCKey_spec {α : Type} (mk : Py K) (act : K → DM K V α) (d : PyDict K V) :
    withCKey mk act d =
      match mk with
      | .ok k => act k d
      | .error e => (.error e, d) := by
  cases mk <;> rfl

end

/-- The other dict's pairs, as `dict_dict_merge` reads them. -/
def assocUpdateFrom {K V : Type} (eqv : K → K → Bool) (l : List (K × V)) :
    List (K × V × Int) → List (K × V)
  | [] => l
  | (k, v, _) :: rest => assocUpdateFrom eqv (assocSet eqv l k v) rest

section
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

/-- `insertdict` from a known hash, on any table, empty keys excepted. -/
theorem insertDict_inv (H : Honest P hf eqv) (mp : PyDict K V) (hd : DictInv hf eqv P.isStr mp)
    (key : K) (v : V) :
    (TooBig mp.used ∧ insertDict P key (hf key) v mp = (.error memoryError, mp)) ∨
    ∃ d', insertDict P key (hf key) v mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocSet eqv (dictAssoc mp) key v := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have ha : dictAssoc mp = k.items := by simp [dictAssoc, hb]
  rw [ha]
  exact insertDict_spec H mp k hb w hu key v

/-- `mergeLoop` with `override == 1`: each pair is `insertdict` with its stored hash. A failure is
`MemoryError`, and it may come after earlier pairs went in, as in C. -/
theorem mergeLoop_spec (H : Honest P hf eqv) :
    ∀ (es : List (K × V × Int)) (d : PyDict K V), DictInv hf eqv P.isStr d →
      (∀ e ∈ es, e.2.2 = hf e.1) →
      (∃ s, mergeLoop P 1 es d = (.error memoryError, s) ∧ TooBig s.used) ∨
      ∃ d', mergeLoop P 1 es d = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = assocUpdateFrom eqv (dictAssoc d) es := by
  intro es
  induction es with
  | nil =>
    intro d hd _
    exact Or.inr ⟨d, rfl, hd, rfl⟩
  | cons e rest ih =>
    intro d hd hh
    obtain ⟨key, v, h⟩ := e
    have hh0 : h = hf key := hh (key, v, h) (by simp)
    subst hh0
    have hrest : ∀ e ∈ rest, e.2.2 = hf e.1 := fun e he => hh e (by simp [he])
    have hunf : mergeLoop P 1 ((key, v, hf key) :: rest) d =
        (insertDict P key (hf key) v >>= fun _ => mergeLoop P 1 rest) d := by
      simp only [mergeLoop, mergeStep]
      rfl
    rcases insertDict_inv H d hd key v with ⟨hbig, h1⟩ | ⟨d1, h1, h2, h3⟩
    · left
      exact ⟨d, by rw [hunf]; exact M.bind_err h1, hbig⟩
    · have hnext : mergeLoop P 1 ((key, v, hf key) :: rest) d = mergeLoop P 1 rest d1 := by
        rw [hunf]
        exact M.bind_ok h1
      rcases ih d1 h2 hrest with ⟨s, h4, h4b⟩ | ⟨d2, h4, h5, h6⟩
      · exact Or.inl ⟨s, by rw [hnext]; exact h4, h4b⟩
      · refine Or.inr ⟨d2, by rw [hnext]; exact h4, h5, ?_⟩
        rw [h6, h3]
        rfl

/-- A clone is the table it was cloned from: `ident` plays no part in any invariant. -/
theorem wf_clone {isStr : K → Bool} (k : Keys K V) (w : WF hf eqv isStr k) (id : Nat) :
    WF hf eqv isStr (cloneCombinedDictKeys id k) :=
  { toChain := ⟨w.len, w.range, w.inj, w.reach⟩
    hashes := w.hashes, uniq := w.uniq, strs := w.strs, notSplit := w.notSplit, load := w.load
    nent := w.nent, usableNN := w.usableNN, small := w.small }

/-- Pairs with pairwise distinct keys, none in `l`, are simply appended. -/
theorem update_distinct : ∀ (es : List (K × V × Int)) (l : List (K × V)),
    es.Pairwise (fun a b => eqv a.1 b.1 = false) → (∀ e ∈ es, l.any (fun p => eqv p.1 e.1) = false) →
    assocUpdateFrom eqv l es = l ++ es.map fun e => (e.1, e.2.1) := by
  intro es
  induction es with
  | nil => intro l _ _; simp [assocUpdateFrom]
  | cons e rest ih =>
    intro l hp hn
    obtain ⟨key, v, h⟩ := e
    have h0 := hn (key, v, h) (by simp)
    have hset : assocSet eqv l key v = l ++ [(key, v)] := by simp [assocSet, h0]
    simp only [assocUpdateFrom, hset]
    have hp' := List.pairwise_cons.mp hp
    rw [ih _ hp'.2]
    · simp
    · intro e he
      simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_false_iff]
      exact ⟨hn e (by simp [he]), hp'.1 e he⟩

omit [DecidableEq K] in
/-- `peer` plays no part in the invariant or in the list a dict stands for. -/
theorem dictInv_peer {isStr : K → Bool} (d : PyDict K V) (hd : DictInv hf eqv isStr d)
    (p : Option (PeerDict K V)) : DictInv hf eqv isStr { d with peer := p } :=
  let ⟨⟨k, hb, w, hu⟩⟩ := hd
  ⟨⟨k, hb, w, hu⟩⟩

/-- If no callback touches the source, `mergeLive` is the snapshot. -/
theorem mergeLive_items (hp : ∀ a b s, (P.eq a b s).2.peer = s.peer) (ov : Nat)
    (other : PyDict K V) (ok : Keys K V)
    (hob : other.body = .combined ok) (d : PyDict K V) :
    mergeLive P ov other.used (mergeFuel other) 0 { d with peer := some other.toPeer } =
      mergeLoop P ov (dictItems other) { d with peer := some other.toPeer } := by
  have hn : other.body.nentries = ok.nentries := by simp [Body.nentries, hob]
  have hf1 : ok.nentries < 0 + mergeFuel other := by
    simp only [mergeFuel, hn]
    generalize 2 ^ other.body.log2Size = t
    omega
  have h := mergeLive_quiet hp ov other ok hob (mergeFuel other) 0
    { d with peer := some other.toPeer } rfl (Nat.zero_le _) hf1
  have hfuel := dictNextAll_fuel other ok hob (mergeFuel other) (other.body.nentries + other.used + 1) 0
    (Nat.zero_le _) hf1 (by omega)
  rw [hfuel] at h
  exact h

/-- The tail of `dict_dict_merge`, from any well-formed target. -/
theorem mergeRest_spec (H : Honest P hf eqv) (mp other : PyDict K V) (ok : Keys K V)
    (hob : other.body = .combined ok)
    (hd : DictInv hf eqv P.isStr mp)
    (hh : ∀ e ∈ dictItems other, e.2.2 = hf e.1) :
    (∃ s, mergeRest P other 1 mp = (.error memoryError, s) ∧
      (TooBig s.used ∨ 64 ≤ estimateLog2Keysize (mp.used + other.used))) ∨
    ∃ d', mergeRest P other 1 mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocUpdateFrom eqv (dictAssoc mp) (dictItems other) := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have tail : ∀ d : PyDict K V, DictInv hf eqv P.isStr d →
      (∃ s, mergeLive P 1 other.used (mergeFuel other) 0 { d with peer := some other.toPeer } =
        (.error memoryError, s) ∧ TooBig s.used) ∨
      ∃ d', mergeLive P 1 other.used (mergeFuel other) 0 { d with peer := some other.toPeer } =
        (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = assocUpdateFrom eqv (dictAssoc d) (dictItems other) := by
    intro d hd0
    rw [mergeLive_items (fun a b s => by rw [H.eq_ok]) 1 other ok hob]
    exact mergeLoop_spec H (dictItems other) _ (dictInv_peer d hd0 _) hh
  simp only [mergeRest]
  by_cases hr : usableFraction (2 ^ mp.body.log2Size) < other.used
  · rw [if_pos hr]
    by_cases hlt : estimateLog2Keysize (mp.used + other.used) < 64
    · have hroom : mp.used ≤ usableFraction (2 ^ estimateLog2Keysize (mp.used + other.used)) := by
        have := estimateRoom_proven (mp.used + other.used)
        omega
      obtain ⟨k', h1, h2, h3, _, _, _, _⟩ := dictResize_spec H mp k hb w hu _ hlt hroom other.body.isUnicode
      rw [h1]
      let d1 : PyDict K V := { mp with nextId := mp.nextId + 1, body := .combined k' }
      have hd1 : DictInv hf eqv P.isStr d1 := ⟨⟨k', rfl, h2, by simp [d1, hu, h3]⟩⟩
      have ha : dictAssoc d1 = dictAssoc mp := by
        simp [dictAssoc, d1, hb, Keys.items, h3]
      rcases tail d1 hd1 with ⟨s, a1, a2⟩ | ⟨d', a1, a2, a3⟩
      · exact Or.inl ⟨s, a1, Or.inl a2⟩
      · exact Or.inr ⟨d', a1, a2, by rw [a3, ha]⟩
    · left
      refine ⟨mp, ?_, Or.inr (by omega)⟩
      simp only [dictResize]
      rw [if_pos (by omega)]
  · rw [if_neg hr]
    rcases tail mp hd with ⟨s, a1, a2⟩ | h
    · exact Or.inl ⟨s, a1, Or.inl a2⟩
    · exact Or.inr h

/-- `dict_dict_merge` with `override == 1`, the operation behind `update`, `|=` and `dict(d)`:
the fold of `d[k] = v` over the source, whichever of its paths runs. -/
theorem dictDictMerge_spec (H : Honest P hf eqv) (mp other : PyDict K V)
    (hd : DictInv hf eqv P.isStr mp) (ho : DictInv hf eqv P.isStr other)
    (hne : other.ident ≠ mp.ident) :
    (∃ s, dictDictMerge P other 1 mp = (.error memoryError, s) ∧
      (TooBig s.used ∨ 64 ≤ estimateLog2Keysize (mp.used + other.used))) ∨
    ∃ d', dictDictMerge P other 1 mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
      dictAssoc d' = assocUpdateFrom eqv (dictAssoc mp) (dictItems other) := by
  obtain ⟨ok, hob, wo, huo⟩ := ho.wf
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have hit := dictItems_spec other ok hob
  have hh : ∀ e ∈ dictItems other, e.2.2 = hf e.1 := by
    intro e he
    rw [hit] at he
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
    obtain ⟨t, ht⟩ := (mem_live ok x).mp hx
    exact wo.hashes t x ht
  have hrest := mergeRest_spec H mp other ok hob hd hh
  have hid : (other.ident == mp.ident) = false := by simpa using hne
  simp only [dictDictMerge, hid, Bool.false_or]
  by_cases h0 : other.used = 0
  · right
    have hnil : liveEntries ok = [] := List.length_eq_zero_iff.mp (by omega)
    refine ⟨mp, by simp [h0], hd, ?_⟩
    simp [hit, hnil, assocUpdateFrom]
  · have hn0 : (other.used == 0) = false := by simpa using h0
    simp only [hn0, Bool.false_eq_true, if_false]
    by_cases hm : mp.used = 0
    · have hm0 : (mp.used == 0) = true := by simpa using hm
      simp only [hm0, if_true, hb, hob]
      by_cases hc : (other.used == ok.nentries &&
          (ok.log2Size == PyDict_LOG_MINSIZE ||
            decide (usableFraction (ok.size / 2) < other.used))) = true
      · right
        rw [if_pos hc]
        have hnil : liveEntries k = [] := List.length_eq_zero_iff.mp (by omega)
        have hl : dictAssoc mp = [] := by simp [dictAssoc, hb, Keys.items, hnil]
        refine ⟨_, rfl, ⟨⟨_, rfl, wf_clone ok wo mp.nextId, ?_⟩⟩, ?_⟩
        · simpa [cloneCombinedDictKeys, liveEntries] using huo
        · have hpair := pairwise_of_uniq eqv ok.entries
            (fun i1 e1 i2 e2 a b c =>
              wo.uniq i1 e1 i2 e2 ((entry_iff ok i1 e1).mpr a) ((entry_iff ok i2 e2).mpr b) c)
          have hdist : (dictItems other).Pairwise (fun a b => eqv a.1 b.1 = false) := by
            rw [hit]
            exact List.pairwise_map.mpr hpair
          rw [hl, update_distinct (eqv := eqv) (dictItems other) [] hdist (by simp), hit]
          simp [dictAssoc, cloneCombinedDictKeys, Keys.items, liveEntries, Function.comp_def]
      · rw [if_neg hc]
        exact hrest
    · have hm0 : (mp.used == 0) = false := by simpa using hm
      simp only [hm0, Bool.false_eq_true, if_false]
      exact hrest

/-- The slow path of `dict_merge` with `override == 1`: `d[k] = E[k]` for each key. -/
theorem mergeGeneric_spec (H : Honest P hf eqv) (getitem : K → DM K V V) :
    ∀ (ks : List K) (vs : List V) (d : PyDict K V), DictInv hf eqv P.isStr d →
      ks.length = vs.length → (∀ p ∈ ks.zip vs, ∀ s, getitem p.1 s = (.ok p.2, s)) →
      (∃ s, mergeGenericLoop P getitem 1 ks d = (.error memoryError, s) ∧ TooBig s.used) ∨
      ∃ d', mergeGenericLoop P getitem 1 ks d = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = (ks.zip vs).foldl (fun l p => assocSet eqv l p.1 p.2) (dictAssoc d) := by
  intro ks
  induction ks with
  | nil =>
    intro vs d hd _ _
    exact Or.inr ⟨d, rfl, hd, rfl⟩
  | cons key rest ih =>
    intro vs d hd hl hg
    cases vs with
    | nil => simp at hl
    | cons v vrest =>
      have hg0 : ∀ s, getitem key s = (.ok v, s) := hg (key, v) (by simp)
      have hunf : mergeGenericLoop P getitem 1 (key :: rest) d =
          (dictSetItem P key v >>= fun _ => mergeGenericLoop P getitem 1 rest) d := by
        simp only [mergeGenericLoop, bne_self_eq_false, Bool.false_eq_true, if_false]
        simp [M.bind_run, M.pure_run, hg0]
      rcases dictSetItem_spec H d hd key v with ⟨hbig, h1⟩ | ⟨d1, h1, h2, h3⟩
      · exact Or.inl ⟨d, by rw [hunf]; exact M.bind_err h1, hbig⟩
      · have hnext : mergeGenericLoop P getitem 1 (key :: rest) d =
            mergeGenericLoop P getitem 1 rest d1 := by
          rw [hunf]
          exact M.bind_ok h1
        rcases ih vrest d1 h2 (by simpa using hl) (fun p hp => hg p (by simp [hp])) with
          ⟨s, h4, h4b⟩ | ⟨d2, h4, h5, h6⟩
        · exact Or.inl ⟨s, by rw [hnext]; exact h4, h4b⟩
        · refine Or.inr ⟨d2, by rw [hnext]; exact h4, h5, ?_⟩
          rw [h6, h3]
          rfl

/-- The sequence route of `dict.update`: pairs in order, with the error of the first bad element
reported after the earlier pairs went in, as `for k, v in E: D[k] = v` does. -/
theorem seq2_spec (H : Honest P hf eqv) :
    ∀ (ps : List (K × V)) (i : Nat) (d : PyDict K V), DictInv hf eqv P.isStr d →
      (∃ s, seq2Loop P true i (ps.map fun p => pure (some (Seq2Item.pair p.1 p.2))) d =
        (.error memoryError, s) ∧ TooBig s.used) ∨
      ∃ d', seq2Loop P true i (ps.map fun p => pure (some (Seq2Item.pair p.1 p.2))) d = (.ok (), d') ∧
        DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = ps.foldl (fun l p => assocSet eqv l p.1 p.2) (dictAssoc d) := by
  intro ps
  induction ps with
  | nil =>
    intro i d hd
    exact Or.inr ⟨d, rfl, hd, rfl⟩
  | cons p rest ih =>
    intro i d hd
    obtain ⟨key, v⟩ := p
    have hunf : seq2Loop P true i (((key, v) :: rest).map fun p => pure (some (Seq2Item.pair p.1 p.2))) d =
        (dictSetItem P key v >>= fun _ =>
          seq2Loop P true (i + 1) (rest.map fun p => pure (some (Seq2Item.pair p.1 p.2)))) d := by
      simp only [List.map_cons, seq2Loop]
      simp [M.bind_run]
    rcases dictSetItem_spec H d hd key v with ⟨hbig, h1⟩ | ⟨d1, h1, h2, h3⟩
    · exact Or.inl ⟨d, by rw [hunf]; exact M.bind_err h1, hbig⟩
    · have hnext : seq2Loop P true i (((key, v) :: rest).map fun p => pure (some (Seq2Item.pair p.1 p.2))) d =
          seq2Loop P true (i + 1) (rest.map fun p => pure (some (Seq2Item.pair p.1 p.2))) d1 := by
        rw [hunf]
        exact M.bind_ok h1
      rcases ih (i + 1) d1 h2 with ⟨s, h4, h4b⟩ | ⟨d2, h4, h5, h6⟩
      · exact Or.inl ⟨s, by rw [hnext]; exact h4, h4b⟩
      · refine Or.inr ⟨d2, by rw [hnext]; exact h4, h5, ?_⟩
        rw [h6, h3]
        rfl

end

/-- `dict_merge` and the exact-dict route of `update`, `|=`: `d.update(other)`. -/
def DictMergeRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp other : PyDict K V), DictInv hf eqv P.isStr mp →
      DictInv hf eqv P.isStr other → other.ident ≠ mp.ident →
      (∃ s, dictMerge P (.dict other) 1 mp = (.error memoryError, s) ∧
        (TooBig s.used ∨ 64 ≤ estimateLog2Keysize (mp.used + other.used))) ∨
      ∃ d', dictMerge P (.dict other) 1 mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = assocUpdateFrom eqv (dictAssoc mp) (dictItems other)
theorem dictMergeRefines_proven : DictMergeRefines := fun _ _ _ _ _ _ H mp other hd ho hne =>
  dictDictMerge_spec H mp other hd ho hne

/-- `d.update(d)` does nothing. -/
def DictMergeSelf : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (mp other : PyDict K V),
    other.ident = mp.ident → dictDictMerge P other 1 mp = (.ok (), mp)
theorem dictMergeSelf_proven : DictMergeSelf := by
  intro K V _ P mp other h
  simp [dictDictMerge, h]

/-- The mapping route: `for k in E.keys(): D[k] = E[k]`. -/
def MergeMappingRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (getitem : K → DM K V V) (ks : List K) (vs : List V) (d : PyDict K V),
      DictInv hf eqv P.isStr d → ks.length = vs.length →
      (∀ p ∈ ks.zip vs, ∀ s, getitem p.1 s = (.ok p.2, s)) →
      (∃ s, dictMerge P (.mapping (pure ks) getitem) 1 d = (.error memoryError, s) ∧ TooBig s.used) ∨
      ∃ d', dictMerge P (.mapping (pure ks) getitem) 1 d = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = (ks.zip vs).foldl (fun l p => assocSet eqv l p.1 p.2) (dictAssoc d)
theorem mergeMappingRefines_proven : MergeMappingRefines := by
  intro K V _ P hf eqv H getitem ks vs d hd hl hg
  have hunf : dictMerge P (.mapping (pure ks) getitem) 1 d = mergeGenericLoop P getitem 1 ks d := by
    simp only [dictMerge, M.bind_run, M.pure_run]
  rw [hunf]
  exact mergeGeneric_spec H getitem ks vs d hd hl hg

/-- The sequence route: `for k, v in E: D[k] = v`. -/
def MergeSeq2Refines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (ps : List (K × V)) (d : PyDict K V), DictInv hf eqv P.isStr d →
      (∃ s, mergeFromSeq2 P { steps := ps.map fun p => pure (some (Seq2Item.pair p.1 p.2)) } true d =
        (.error memoryError, s) ∧ TooBig s.used) ∨
      ∃ d', mergeFromSeq2 P { steps := ps.map fun p => pure (some (Seq2Item.pair p.1 p.2)) } true d =
        (.ok (), d') ∧
        DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = ps.foldl (fun l p => assocSet eqv l p.1 p.2) (dictAssoc d)
theorem mergeSeq2Refines_proven : MergeSeq2Refines := fun _ _ _ _ _ _ H ps d hd =>
  seq2_spec H ps 0 d hd

/-- `dict_update_arg` picks the route its docstring describes. -/
def UpdateArgRoutes : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (d : PyDict K V)
    (hk : DM K V Bool) (m : MergeArg K V) (q : ReIter (PyDict K V) (Seq2Item K V)) (x : PyDict K V),
    dictUpdateArg P (.exact x) d = dictMerge P (.dict x) 1 d ∧
    (∀ d', hk d = (.ok true, d') → dictUpdateArg P (.other hk m q) d = dictMerge P m 1 d') ∧
    (∀ d', hk d = (.ok false, d') → dictUpdateArg P (.other hk m q) d = mergeFromSeq2 P q true d') ∧
    (∀ e d', hk d = (.error e, d') → dictUpdateArg P (.other hk m q) d = (.error e, d'))
theorem updateArgRoutes_proven : UpdateArgRoutes := by
  intro K V _ P d hk m q x
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> intros <;> simp_all [dictUpdateArg, M.bind_run]

/-- `dict.pop`, with and without a default. -/
def PopDefaultSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → d.frozen = false →
    ∀ (key : K) (dflt : Option V),
      (assocGet eqv (dictAssoc d) key = none ∧
        dictPopDefault P key dflt d =
          (match dflt with
           | some x => (.ok x, d)
           | none => (.error (keyErr P key), d))) ∨
      ∃ v d', assocGet eqv (dictAssoc d) key = some v ∧ dictPopDefault P key dflt d = (.ok v, d') ∧
        DictInv hf eqv P.isStr d' ∧ dictAssoc d' = assocDel eqv (dictAssoc d) key
theorem popDefaultSpec_proven : PopDefaultSpec := fun _ _ _ _ _ _ H d hd hfz key dflt =>
  popDefault_spec H d hd hfz key dflt

/-- `d[k] = v` and `del d[k]` through `mp_ass_subscript`. -/
def AssSubDispatch : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (d : PyDict K V) (key : K) (w : Option V),
    dictAssSub P key w d =
      match w with
      | none => dictDelItem P key d
      | some v => dictSetItem P key v d
theorem assSubDispatch_proven : AssSubDispatch := fun _ _ _ _ d key w => assSub_spec d key w

/-- A new dict is well formed and empty. -/
def NewDictEmpty : Prop :=
  ∀ (K V : Type) [DecidableEq K] (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool) (id n : Nat),
    DictInv hf eqv isStr ({ ident := id, nextId := n } : PyDict K V) ∧
      dictAssoc ({ ident := id, nextId := n } : PyDict K V) = []
theorem newDictEmpty_proven : NewDictEmpty := by
  intro K V _ hf eqv isStr id n
  refine ⟨dictInv_new hf eqv isStr id n, ?_⟩
  simp [dictAssoc, Keys.items, liveEntries, emptyKeys]

/-- The C-string wrappers. -/
def CKeyWrappers : Prop :=
  ∀ (K V α : Type) [DecidableEq K] (mk : Py K) (act : K → DM K V α) (d : PyDict K V),
    withCKey mk act d =
      match mk with
      | .ok k => act k d
      | .error e => (.error e, d)
theorem cKeyWrappers_proven : CKeyWrappers := fun _ _ _ _ mk act d => withCKey_spec mk act d

end PyLean.DictSet
