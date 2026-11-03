import PyLean.DictSet.Props315

/-!
`copy`, `|` and `|=` (CPython 3.15.2, `Objects/dictobject.c`).
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-! ## What the table operations keep: the identity and the type of the receiver -/

/-- The identity of an object and whether it is a frozendict: what Python code cannot change. -/
def idf (s : PyDict K V) : Nat × Bool := (s.ident, s.frozen)

section Ident
variable (P : Proto K (PyDict K V))

omit [DecidableEq K] in
theorem dictResize_idf (l : Nat) (u : Bool) (mp : PyDict K V) :
    idf (dictResize l u mp).2 = idf mp := by
  simp only [dictResize]
  split
  · rfl
  · split <;> rfl

omit [DecidableEq K] in
theorem insertCombined_idf (KO : KeyOps K) (hash : Int) (key : K) (value : V) (mp : PyDict K V) :
    idf (insertCombinedDict KO hash key value mp).2 = idf mp := by
  simp only [insertCombinedDict]
  have h1 : idf (if mp.body.isUnicode && !KO.isStr key then insertionResize false mp
      else (.ok (), mp)).2 = idf mp := by
    split
    · exact dictResize_idf _ _ _
    · rfl
  split
  · rename_i e s heq
    rw [heq] at h1
    exact h1
  · rename_i a mp1 heq
    rw [heq] at h1
    have h2 : idf (if mp1.body.usable ≤ 0 then insertionResize true mp1
        else (.ok (), mp1)).2 = idf mp1 := by
      split
      · exact dictResize_idf _ _ _
      · rfl
    split
    · rename_i e s heq2
      rw [heq2] at h2
      exact h2.trans h1
    · rename_i a2 mp2 heq2
      rw [heq2] at h2
      have h3 := h2.trans h1
      split
      · split
        · exact h3
        · exact h3
      · exact h3

omit [DecidableEq K] in
theorem storeValue_idf (value : V) (ix : Nat) (mp : PyDict K V) :
    idf (storeValue value ix mp).2 = idf mp := by
  simp only [storeValue]
  split
  · rfl
  · split <;> rfl

theorem insertAfterLookup_idf (key : K) (hash : Int) (value : V) (ix : Int) (old : Option V)
    (mp : PyDict K V) : idf (insertAfterLookup P key hash value ix old mp).2 = idf mp := by
  simp only [insertAfterLookup]
  split
  · have h := insertCombined_idf P.toKeyOps hash key value mp
    split
    · rename_i a s heq
      rw [heq] at h
      exact h
    · rename_i e s heq
      rw [heq] at h
      exact h
  · exact storeValue_idf _ _ _

omit [DecidableEq K] in
theorem insertSplitValue_idf (value : V) (ix : Nat) (mp : PyDict K V) :
    idf (insertSplitValue (K := K) value ix mp).2 = idf mp := by
  simp only [insertSplitValue, M.bind_run, M.get_run]
  cases hb : mp.body with
  | combined k => rfl
  | split k v =>
    simp only []
    cases v.get ix <;> rfl

variable {P}

theorem insertDict_idf (hp : ∀ a b s, idf (P.eq a b s).2 = idf s) (key : K) (hash : Int)
    (value : V) (mp : PyDict K V) : idf (insertDict P key hash value mp).2 = idf mp := by
  have via : idf (match dictLookup P key hash mp with
      | (.ok (ix, old), mp') => insertAfterLookup P key hash value ix old mp'
      | (.error e, mp') => ((.error e, mp') : Py Unit × PyDict K V)).2 = idf mp := by
    have hl := dictLookup_stable P idf hp key hash mp
    split
    · rename_i ix old mp' heq
      rw [heq] at hl
      exact (insertAfterLookup_idf P key hash value ix old mp').trans hl
    · rename_i e mp' heq
      rw [heq] at hl
      exact hl
  simp only [insertDict]
  split
  · split
    · split
      · rfl
      · rename_i ix keys' heq
        split
        · exact insertSplitValue_idf _ _ _
        · exact insertAfterLookup_idf P key hash value ix none _
    · exact via
  · exact via

theorem mergeStep_idf (hp : ∀ a b s, idf (P.eq a b s).2 = idf s) (ov : Nat) (key : K)
    (hash : Int) (value : V) (mp : PyDict K V) :
    idf (mergeStep P ov key hash value mp).2 = idf mp := by
  simp only [mergeStep]
  split
  · exact insertDict_idf hp key hash value mp
  · have hl := dictLookup_stable P idf hp key hash mp
    simp only [dictContainsKnownHash, M.bind_run]
    rcases hk : dictLookup P key hash mp with ⟨a, s⟩
    rw [hk] at hl
    cases a with
    | error e => exact hl
    | ok r =>
      simp only [M.pure_run]
      split
      · exact (insertDict_idf hp key hash value s).trans hl
      · split
        · exact hl
        · exact hl

theorem mergeLive_idf (hp : ∀ a b s, idf (P.eq a b s).2 = idf s) (ov orig : Nat) :
    ∀ (fuel : Nat) (pos : Int) (mp : PyDict K V), idf (mergeLive P ov orig fuel pos mp).2 = idf mp := by
  intro fuel
  induction fuel with
  | zero => intro pos mp; rfl
  | succ fuel ih =>
    intro pos mp
    cases hpe : mp.peer with
    | none => (simp only [mergeLive, hpe]) <;> rfl
    | some src =>
      cases hn : dictNext src.toDict pos with
      | none => (simp only [mergeLive, hpe, hn]) <;> rfl
      | some t =>
        obtain ⟨pos', key, value, hash⟩ := t
        have h1 := mergeStep_idf hp ov key hash value mp
        simp only [mergeLive, hpe, hn]
        rcases hs : mergeStep P ov key hash value mp with ⟨a, s⟩
        rw [hs] at h1
        cases a with
        | error e => exact h1
        | ok u =>
          show idf (match s.peer with
            | none => ((.error .modelFuel, s) : Py Unit × PyDict K V)
            | some src' => if orig != src'.used then (.error mergeMutated, s)
                else mergeLive P ov orig fuel pos' s).2 = idf mp
          cases hps : s.peer with
          | none => exact h1
          | some src' =>
            show idf (if orig != src'.used then ((.error mergeMutated, s) : Py Unit × PyDict K V)
                else mergeLive P ov orig fuel pos' s).2 = idf mp
            split
            · exact h1
            · exact (ih pos' s).trans h1

theorem mergeRest_idf (hp : ∀ a b s, idf (P.eq a b s).2 = idf s) (other : PyDict K V) (ov : Nat)
    (mp : PyDict K V) : idf (mergeRest P other ov mp).2 = idf mp := by
  simp only [mergeRest]
  have h1 : idf (if usableFraction (2 ^ mp.body.log2Size) < other.used then
      dictResize (estimateLog2Keysize (mp.used + other.used)) other.body.isUnicode mp
      else (.ok (), mp)).2 = idf mp := by
    split
    · exact dictResize_idf _ _ _
    · rfl
  split
  · rename_i e s heq
    rw [heq] at h1
    exact h1
  · rename_i u s heq
    rw [heq] at h1
    exact (mergeLive_idf hp ov other.used _ 0 _).trans h1

theorem dictDictMerge_idf (hp : ∀ a b s, idf (P.eq a b s).2 = idf s) (other : PyDict K V)
    (ov : Nat) (mp : PyDict K V) : idf (dictDictMerge P other ov mp).2 = idf mp := by
  simp only [dictDictMerge]
  split
  · rfl
  · split
    · split
      · split
        · rfl
        · exact mergeRest_idf hp _ _ _
      · exact mergeRest_idf hp _ _ _
    · exact mergeRest_idf hp _ _ _

end Ident

section Copy
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

omit [DecidableEq K] in
/-- `_PyDict_Next` reads only the body and `ma_used`. -/
theorem dictNextAll_congr (a b : PyDict K V) (h : ∀ p, dictNext a p = dictNext b p) :
    ∀ (f : Nat) (p : Int), dictNextAll a f p = dictNextAll b f p := by
  intro f
  induction f with
  | zero => intro p; rfl
  | succ f ih =>
    intro p
    simp only [dictNextAll, h p]
    cases dictNext b p with
    | none => rfl
    | some t =>
      obtain ⟨p', k, v, hh⟩ := t
      simp only [ih]

/-- The copy of a split dict: its shared keys and a copy of its values. -/
def splitCopyOf (mp : PyDict K V) (k : Keys K Unit) (v : Values V) (id : Nat) (fz : Bool) : PyDict K V :=
  { ident := id, used := mp.used, body := .split k (copyValues v), nextId := mp.nextId, frozen := fz }

/-- The fast copy of a combined dict: a clone of its keys. -/
def cloneCopyOf (mp : PyDict K V) (k : Keys K V) (id n : Nat) (fz : Bool) : PyDict K V :=
  { ident := id, used := mp.used, nextId := n, frozen := fz, body := .combined (cloneCombinedDictKeys mp.nextId k) }

omit [DecidableEq K] in
theorem dictItems_split_copy (mp : PyDict K V) (k : Keys K Unit) (v : Values V)
    (hb : mp.body = .split k v) (id : Nat) (fz : Bool) :
    dictItems (splitCopyOf mp k v id fz) = dictItems mp := by
  have hn : ∀ p, dictNext (splitCopyOf mp k v id fz) p = dictNext mp p := by
    intro p
    simp only [dictNext, hb, splitCopyOf, cloneCopyOf]
    rfl
  simp only [dictItems, hb, Body.nentries, splitCopyOf, cloneCopyOf]
  exact dictNextAll_congr _ _ hn _ _

omit [DecidableEq K] in
theorem dictItems_clone (mp : PyDict K V) (k : Keys K V) (hb : mp.body = .combined k) (id n : Nat)
    (fz : Bool) :
    dictItems (cloneCopyOf mp k id n fz) = dictItems mp := by
  have hn : ∀ p, dictNext (cloneCopyOf mp k id n fz) p = dictNext mp p := by
    intro p
    simp only [dictNext, hb, splitCopyOf, cloneCopyOf]
    rfl
  simp only [dictItems, hb, Body.nentries, splitCopyOf, cloneCopyOf]
  exact dictNextAll_congr _ _ hn _ _

/-- The pairs of a well-formed dict, put one by one into an empty one, are the dict's pairs. -/
theorem assocUpdate_nil_items {isStr : K → Bool} (mp : PyDict K V) (k : Keys K V)
    (hb : mp.body = .combined k) (w : WF hf eqv isStr k) :
    assocUpdateFrom eqv [] (dictItems mp) = k.items := by
  have hit := dictItems_spec mp k hb
  have hpair := pairwise_of_uniq eqv k.entries
    (fun i1 e1 i2 e2 a b c =>
      w.uniq i1 e1 i2 e2 ((entry_iff k i1 e1).mpr a) ((entry_iff k i2 e2).mpr b) c)
  have hdist : (dictItems mp).Pairwise (fun a b => eqv a.1 b.1 = false) := by
    rw [hit]
    exact List.pairwise_map.mpr hpair
  rw [update_distinct (eqv := eqv) (dictItems mp) [] hdist (by simp), hit]
  simp [Keys.items, liveEntries, Function.comp_def]

theorem dictInv_fresh {isStr : K → Bool} (id n : Nat) (fz : Bool) :
    DictInv hf eqv isStr ({ ident := id, nextId := n, frozen := fz } : PyDict K V) :=
  ⟨⟨emptyKeys, rfl, wf_empty _ _ _, by simp [liveEntries, emptyKeys]⟩⟩

omit [DecidableEq K] in
theorem dictAssoc_fresh (id n : Nat) (fz : Bool) :
    dictAssoc ({ ident := id, nextId := n, frozen := fz } : PyDict K V) = [] := by
  simp [dictAssoc, Keys.items, liveEntries, emptyKeys]

/-- `copy_lock_held_untracked` on a well-formed dict whose `tp_iter` is `dict_iter`, for an honest
protocol. -/
theorem copy_refines (H : Honest P hf eqv) (mp : PyDict K V) (hd : DictInv hf eqv P.isStr mp)
    (id : Nat) (asFrozen : Bool) (asMap : MergeArg K V) (hid : id ≠ mp.ident) :
    copyLockHeldUntracked P mp id asFrozen true asMap = .error memoryError ∨
    ∃ c, copyLockHeldUntracked P mp id asFrozen true asMap = .ok c ∧ DictInv hf eqv P.isStr c ∧
      dictAssoc c = dictAssoc mp ∧ c.ident = id ∧ c.frozen = asFrozen := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  by_cases h0 : mp.used = 0
  · right
    have hnil : liveEntries k = [] := List.length_eq_zero_iff.mp (by omega)
    refine ⟨{ ident := id, nextId := mp.nextId, frozen := asFrozen },
      by simp [copyLockHeldUntracked, h0], dictInv_fresh _ _ _, ?_, rfl, rfl⟩
    rw [dictAssoc_fresh]
    simp [dictAssoc, hb, Keys.items, hnil]
  · have h0' : (mp.used == 0) = false := by simpa using h0
    by_cases hc : k.nentries * 2 / 3 ≤ mp.used
    · right
      refine ⟨cloneCopyOf mp k id (mp.nextId + 1) asFrozen,
        by simp [copyLockHeldUntracked, cloneCopyOf, h0', hb, hc], ⟨⟨_, rfl, wf_clone k w mp.nextId, ?_⟩⟩,
        ?_, rfl, rfl⟩
      · simpa [cloneCopyOf, cloneCombinedDictKeys, liveEntries] using hu
      · simp [dictAssoc, hb, cloneCopyOf, cloneCombinedDictKeys, Keys.items, liveEntries]
    · have hc': decide (mp.used ≥ k.nentries * 2 / 3) = false := by
        simp only [decide_eq_false_iff_not]
        omega
      have hm : copyLockHeldUntracked P mp id asFrozen true asMap =
          match dictDictMerge P mp 1
            ({ ident := id, nextId := mp.nextId, frozen := asFrozen } : PyDict K V) with
          | (.ok _, d) => .ok { d with peer := none }
          | (.error e, _) => .error e := by
        (simp only [copyLockHeldUntracked, h0', hb, hc', Bool.true_and, Bool.false_eq_true, if_false,
          if_true, dictMerge]) <;> rfl
      have hidf := dictDictMerge_idf (P := P) (fun a b s => by rw [H.eq_ok]) mp 1
        ({ ident := id, nextId := mp.nextId, frozen := asFrozen } : PyDict K V)
      rcases dictDictMerge_spec H _ mp (dictInv_fresh id mp.nextId asFrozen) hd (Ne.symm hid) with
        ⟨s, h1, _⟩ | ⟨d', h1, h2, h3⟩
      · left
        rw [hm, h1]
      · right
        rw [h1] at hidf
        have ha : dictAssoc ({ d' with peer := none } : PyDict K V) = dictAssoc d' := rfl
        refine ⟨{ d' with peer := none }, by rw [hm, h1], dictInv_peer d' h2 none, ?_,
          congrArg Prod.fst hidf, congrArg Prod.snd hidf⟩
        rw [ha, h3, dictAssoc_fresh, assocUpdate_nil_items mp k hb w]
        simp [dictAssoc, hb]

end Copy

/-- `dict.copy`, `PyDict_Copy`, `anydict_copy_untracked`, `_PyDict_CopyAsDict`, `frozendict.copy`,
for every key protocol. `PyDict_Copy` refuses what is not a dict, a frozendict included. The copy is
a new object, a frozendict exactly when asked: `anydict_copy_untracked` asks for one when the source
is one, `_PyDict_CopyAsDict` never does. An empty source gives an empty object; a split source gives
the same shared keys and a copy of the values, which iterates as the source does, with no callback
run; a combined source with at most a third of its entries deleted and `dict_iter` as `tp_iter` gives
a clone, which iterates as the source does; anything else is `dict_merge(copy, o, 1)`, by the fast
route when `tp_iter` is `dict_iter`, by `keys()` and `o[key]` otherwise. `frozendict.copy` of an exact
frozendict is the object itself. -/
def CopyBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (mp : PyDict K V) (id : Nat)
    (asFrozen iterIsDict : Bool) (asMap : MergeArg K V),
    pyDictCopyC P false mp id iterIsDict asMap = .error badInternalCall ∧
    (mp.frozen = true → pyDictCopyC P true mp id iterIsDict asMap = .error badInternalCall) ∧
    (mp.frozen = false → dictCopyImpl P mp id iterIsDict asMap =
      copyLockHeldUntracked P mp id false iterIsDict asMap) ∧
    anydictCopyUntracked P mp id iterIsDict asMap =
      copyLockHeldUntracked P mp id mp.frozen iterIsDict asMap ∧
    dictCopyAsDict P mp id iterIsDict asMap = copyLockHeldUntracked P mp id false iterIsDict asMap ∧
    frozendictCopyImpl P mp true id iterIsDict asMap = .ok mp ∧
    frozendictCopyImpl P mp false id iterIsDict asMap = anydictCopyUntracked P mp id iterIsDict asMap ∧
    (mp.used = 0 → copyLockHeldUntracked P mp id asFrozen iterIsDict asMap =
      .ok { ident := id, nextId := mp.nextId, frozen := asFrozen }) ∧
    (mp.used ≠ 0 → ∀ k v, mp.body = .split k v →
      ∃ c, copyLockHeldUntracked P mp id asFrozen iterIsDict asMap = .ok c ∧ c.ident = id ∧
        c.frozen = asFrozen ∧ c.used = mp.used ∧ c.body = .split k (copyValues v) ∧
        dictItems c = dictItems mp) ∧
    (mp.used ≠ 0 → ∀ k, mp.body = .combined k → iterIsDict = true → k.nentries * 2 / 3 ≤ mp.used →
      ∃ c, copyLockHeldUntracked P mp id asFrozen iterIsDict asMap = .ok c ∧ c.ident = id ∧
        c.frozen = asFrozen ∧ c.used = mp.used ∧ dictItems c = dictItems mp) ∧
    (mp.used ≠ 0 → ∀ k, mp.body = .combined k → ¬(iterIsDict = true ∧ k.nentries * 2 / 3 ≤ mp.used) →
      copyLockHeldUntracked P mp id asFrozen iterIsDict asMap =
        match dictMerge P (if iterIsDict then .dict mp else asMap) 1
          ({ ident := id, nextId := mp.nextId, frozen := asFrozen } : PyDict K V) with
        | (.ok _, d) => .ok { d with peer := none }
        | (.error e, _) => .error e)

theorem copyBody_proven : CopyBody := by
  intro K V _ P mp id asFrozen iterIsDict asMap
  refine ⟨by simp [pyDictCopyC], fun h => by simp [pyDictCopyC, h],
    fun h => by simp [dictCopyImpl, pyDictCopyC, h],
    by cases h : mp.frozen <;> simp [anydictCopyUntracked, h],
    by cases h : mp.frozen <;> simp [dictCopyAsDict, h], by simp [frozendictCopyImpl],
    by simp [frozendictCopyImpl], fun h => by simp [copyLockHeldUntracked, h], ?_, ?_, ?_⟩
  · intro h0 k v hb
    have h0' : (mp.used == 0) = false := by simpa using h0
    exact ⟨splitCopyOf mp k v id asFrozen, by simp [copyLockHeldUntracked, splitCopyOf, h0', hb], rfl, rfl, rfl, rfl,
      dictItems_split_copy mp k v hb id asFrozen⟩
  · intro h0 k hb hi hc
    have h0' : (mp.used == 0) = false := by simpa using h0
    exact ⟨cloneCopyOf mp k id (mp.nextId + 1) asFrozen,
      by simp [copyLockHeldUntracked, cloneCopyOf, h0', hb, hi, hc], rfl, rfl, rfl,
      dictItems_clone mp k hb id (mp.nextId + 1) asFrozen⟩
  · intro h0 k hb hc
    have h0' : (mp.used == 0) = false := by simpa using h0
    have hc' : (iterIsDict && decide (mp.used ≥ k.nentries * 2 / 3)) = false := by
      cases hi : iterIsDict
      · rfl
      · simp only [Bool.true_and, decide_eq_false_iff_not]
        intro hh
        exact hc ⟨hi, hh⟩
    (simp only [copyLockHeldUntracked, h0', hb, hc', Bool.false_eq_true, if_false]) <;> rfl

/-- A copy of a well-formed dict, for an honest protocol and a type that keeps `dict_iter`: a new
well-formed dict or frozendict, as asked, with the given identity and the same pairs in the same
order, whichever of the three routes runs; the one failure is `MemoryError`. -/
def CopyRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V), DictInv hf eqv P.isStr mp →
      ∀ (id : Nat) (asFrozen : Bool) (asMap : MergeArg K V), id ≠ mp.ident →
        copyLockHeldUntracked P mp id asFrozen true asMap = .error memoryError ∨
        ∃ c, copyLockHeldUntracked P mp id asFrozen true asMap = .ok c ∧ DictInv hf eqv P.isStr c ∧
          dictAssoc c = dictAssoc mp ∧ c.ident = id ∧ c.frozen = asFrozen

theorem copyRefines_proven : CopyRefines := fun _ _ _ _ _ _ H mp hd id fz asMap hid =>
  copy_refines H mp hd id fz asMap hid

/-! ## `|` and `|=` -/

/-- `_PyDict_Or`, `frozendict_or` and `_PyDict_IOr`, for every key protocol and every right operand.
`NotImplemented` unless both operands are dicts or frozendicts; otherwise a copy of `self` made by
`anydict_copy_untracked` (so a frozendict exactly when `self` is one) that `dict_update_arg` then
updates from `other`, a failure of either being the result. `frozendict_or` on an exact frozendict
`self` gives back `other` itself when `self` is empty and `other` an exact frozendict, and `self`
itself when `other` is an exact empty dict or frozendict; anything else goes to `_PyDict_Or`.
`|=` updates `self` in place and returns it. -/
def OrBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (self other : OrOperand K V) (id : Nat)
    (sIt : Bool) (sMap : MergeArg K V) (oArg : UpdateArg K V) (d : PyDict K V),
    (¬(self.isAny = true ∧ other.isAny = true) →
      pyDictOr P self.isAny other.isAny self.d id sIt sMap oArg = .ok none) ∧
    (self.isAny = true → other.isAny = true →
      pyDictOr P self.isAny other.isAny self.d id sIt sMap oArg =
        match anydictCopyUntracked P self.d id sIt sMap with
        | .error e => .error e
        | .ok new =>
          match dictUpdateArg P oArg new with
          | (.ok _, d) => .ok (some { d with peer := none })
          | (.error e, _) => .error e) ∧
    (self.isAny = true → self.exact = true → self.d.frozen = true → self.d.used = 0 →
      other.isAny = true → other.exact = true → other.d.frozen = true →
      frozendictOr315 P self other id sIt sMap oArg = .ok (some other.d)) ∧
    (self.isAny = true → self.exact = true → self.d.frozen = true →
      (self.d.used ≠ 0 ∨ other.d.frozen = false) → other.isAny = true → other.exact = true →
      other.d.used = 0 → frozendictOr315 P self other id sIt sMap oArg = .ok (some self.d)) ∧
    (¬(self.isAny = true ∧ self.exact = true ∧ self.d.frozen = true) →
      frozendictOr315 P self other id sIt sMap oArg =
        pyDictOr P self.isAny other.isAny self.d id sIt sMap oArg) ∧
    pyDictIOr P oArg d =
      match dictUpdateArg P oArg d with
      | (.ok _, s) => (.ok s, s)
      | (.error e, s) => (.error e, s)

theorem orBody_proven : OrBody := by
  intro K V _ P self other id sIt sMap oArg d
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun a b c e f g i => ?_, fun a b c e f g i => ?_, fun h => ?_, ?_⟩
  · simp only [pyDictOr]
    cases h1 : self.isAny <;> cases h2 : other.isAny <;> simp_all
  · unfold pyDictOr
    rw [h1, h2]
    rfl
  · simp [frozendictOr315, a, b, c, e, f, g, i]
  · have hn : ¬(self.d.used = 0 ∧ other.d.frozen = true) := by
      rintro ⟨x, y⟩
      rcases e with e | e
      · exact e x
      · rw [y] at e; exact Bool.noConfusion e
    simp only [frozendictOr315, a, b, c, f, g, i, Bool.and_self, Bool.true_and, beq_self_eq_true,
      if_true]
    rw [if_neg]
    simpa using hn
  · have : (self.isAny && self.exact && self.d.frozen) = false := by
      cases h1 : self.isAny <;> cases h2 : self.exact <;> cases h3 : self.d.frozen <;> simp_all
    simp only [frozendictOr315, this, Bool.false_eq_true, if_false]
  · simp only [pyDictIOr, M.bind_run, M.get_run]
    rcases dictUpdateArg P oArg d with ⟨r, s⟩
    cases r <;> rfl

/-- `self | other` on two well-formed exact dicts or frozendicts, for an honest protocol: a new
well-formed object, a frozendict exactly when `self` is, holding `self`'s pairs updated in order by
`other`'s, as `d = self.copy(); d.update(other)` would; the one failure is `MemoryError`. The
shortcuts of `frozendict_or` agree with this: an empty `self` and an exact frozendict `other` give
`other`'s pairs, and an empty `other` gives `self`'s. -/
def OrRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (s o : PyDict K V), DictInv hf eqv P.isStr s → DictInv hf eqv P.isStr o →
      ∀ (id : Nat) (sMap : MergeArg K V), id ≠ s.ident → id ≠ o.ident →
        pyDictOr P true true s id true sMap (.exact o) = .error memoryError ∨
        ∃ r, pyDictOr P true true s id true sMap (.exact o) = .ok (some r) ∧
          DictInv hf eqv P.isStr r ∧ r.ident = id ∧ r.frozen = s.frozen ∧
          dictAssoc r = assocUpdateFrom eqv (dictAssoc s) (dictItems o) ∧
          (s.used = 0 → dictAssoc r = dictAssoc o) ∧ (o.used = 0 → dictAssoc r = dictAssoc s)

theorem orRefines_proven : OrRefines := by
  intro K V _ P hf eqv H s o hs ho id sMap h1 h2
  have hcopy : anydictCopyUntracked P s id true sMap =
      copyLockHeldUntracked P s id s.frozen true sMap := by
    cases h : s.frozen <;> simp [anydictCopyUntracked, h]
  rcases copy_refines H s hs id s.frozen sMap h1 with hc | ⟨c, hc, hci, hca, hcid, hcf⟩
  · left
    simp [pyDictOr, hcopy, hc]
  · have hne : o.ident ≠ c.ident := by rw [hcid]; exact Ne.symm h2
    have hidf := dictDictMerge_idf (P := P) (fun a b s => by rw [H.eq_ok]) o 1 c
    have hupd : dictUpdateArg P (.exact o) c = dictDictMerge P o 1 c := rfl
    obtain ⟨ko, hob, wo, huo⟩ := ho.wf
    have hall : assocUpdateFrom eqv [] (dictItems o) = dictAssoc o := by
      rw [assocUpdate_nil_items o ko hob wo]
      simp [dictAssoc, hob]
    rcases dictDictMerge_spec H c o hci ho hne with ⟨t, h3, _⟩ | ⟨d', h3, h4, h5⟩
    · left
      simp [pyDictOr, hcopy, hc, hupd, h3]
    · right
      rw [h3] at hidf
      refine ⟨{ d' with peer := none }, by simp [pyDictOr, hcopy, hc, hupd, h3],
        dictInv_peer d' h4 none, ?_, ?_, ?_, ?_, ?_⟩
      · show d'.ident = id
        rw [← hcid]; exact congrArg Prod.fst hidf
      · show d'.frozen = s.frozen
        rw [← hcf]; exact congrArg Prod.snd hidf
      · show dictAssoc d' = _
        rw [h5, hca]
      · intro h0
        show dictAssoc d' = _
        obtain ⟨k, hb, w, hu⟩ := hs.wf
        have hnil : liveEntries k = [] := List.length_eq_zero_iff.mp (by omega)
        have : dictAssoc s = [] := by simp [dictAssoc, hb, Keys.items, hnil]
        rw [h5, hca, this, hall]
      · intro h0
        show dictAssoc d' = _
        have hnil : liveEntries ko = [] := List.length_eq_zero_iff.mp (by omega)
        have : dictItems o = [] := by rw [dictItems_spec o ko hob, hnil]; rfl
        rw [h5, hca, this]
        rfl

end PyLean.DictSet
