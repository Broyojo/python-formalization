import PyLean.DictSet.Ops315
import PyLean.DictSet.Iter

/-!
Properties of the bodies in `Ops315.lean`. Unless a statement says `Honest`, it holds for every key
protocol, including a `__hash__` that raises and an `__eq__` that raises or changes either dict.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-! ## `pop` -/

/-- `PyDict_Pop`, `pop_lock_held`, `dict.pop` and `PyDict_PopString`, branch by branch, for every key
protocol, including a `__hash__` that changes the dict (`d1` is the dict as `__hash__` left it). An
empty dict answers before the key is hashed; a failed hash goes through `dict_unhashable_type`; after
the hash `_PyDict_Pop_KnownHash` tests for an empty dict again; a failed lookup is the result in the
state `__eq__` left; a slot with no value (a key of the shared keys this split dict has no value for)
is a miss, and nothing is deleted or read through it; a value is deleted by `delitem_common` on the
state the lookup left. `dict.pop` turns a miss into the default or `KeyError(key)`. -/
def PopBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (d : PyDict K V),
    d.frozen = false →
    let d1 := P.hashEff key d
    (d.used = 0 → pyDictPop P true key d = (.ok none, d)) ∧
    (d.used ≠ 0 → ∀ e, P.hash key = .error e →
      pyDictPop P true key d = (.error (dictUnhashableType P d1.frozen key e), d1)) ∧
    (d.used ≠ 0 → ∀ h, P.hash key = .ok h →
      (d1.used = 0 → pyDictPop P true key d = (.ok none, d1)) ∧
      (d1.used ≠ 0 →
        (∀ e s, dictLookup P key h d1 = (.error e, s) → pyDictPop P true key d = (.error e, s)) ∧
        (∀ ix s, dictLookup P key h d1 = (.ok (ix, none), s) → pyDictPop P true key d = (.ok none, s)) ∧
        (∀ v s, dictLookup P key h d1 = (.ok (DKIX_EMPTY, some v), s) →
          pyDictPop P true key d = (.ok none, s)) ∧
        (∀ ix v s, ix ≠ DKIX_EMPTY → dictLookup P key h d1 = (.ok (ix, some v), s) →
          pyDictPop P true key d =
            match delitemCommon h ix.toNat s with
            | (.ok _, s') => (.ok (some v), s')
            | (.error e, s') => (.error e, s')))) ∧
    (∀ s, pyDictPop P true key d = (.ok none, s) →
      (∀ dv, dictPopDefault P key (some dv) d = (.ok dv, s)) ∧
      dictPopDefault P key none d = (.error (keyErr P key), s)) ∧
    (∀ v s, pyDictPop P true key d = (.ok (some v), s) →
      ∀ dflt, dictPopDefault P key dflt d = (.ok v, s)) ∧
    (∀ e s, pyDictPop P true key d = (.error e, s) →
      ∀ dflt, dictPopDefault P key dflt d = (.error e, s)) ∧
    (∀ e, pyDictPopString P true (.error e) d = (.error e, d)) ∧
    pyDictPopString P true (.ok key) d = pyDictPop P true key d

theorem popBody_proven : PopBody := by
  intro K V _ P key d hfz d1
  have hpd : ∀ dflt, dictPopDefault P key dflt d =
      match pyDictPop P true key d with
      | (.ok (some v), s) => (.ok v, s)
      | (.ok none, s) => match dflt with
        | some dv => (.ok dv, s)
        | none => (.error (keyErr P key), s)
      | (.error e, s) => (.error e, s) := by
    intro dflt
    simp only [dictPopDefault, M.bind_run]
    rcases pyDictPop P true key d with ⟨r, s⟩
    cases r with
    | error e => rfl
    | ok o =>
      cases o with
      | some v => rfl
      | none => cases dflt <;> rfl
  refine ⟨fun h0 => ?_, fun h0 e he => ?_, fun h0 h hh => ⟨fun h1 => ?_, fun h1 => ⟨?_, ?_, ?_, ?_⟩⟩,
    ?_, ?_, ?_, ?_, rfl⟩
  · simp [pyDictPop, hfz, h0]
  · simp [pyDictPop, hfz, h0, he, d1]
  · simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, d1, h1]
  · intro e s hl
    simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl, d1, h1]
  · intro ix s hl
    simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl, d1, h1]
  · intro v s hl
    simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl, d1, h1]
  · intro ix v s hix hl
    have hne : (ix == DKIX_EMPTY) = false := by simpa using hix
    have h1' : ((P.hashEff key d).used == 0) = false := by simpa [d1] using h1
    simp only [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl, hne, Bool.not_true, Bool.false_eq_true,
      if_false, beq_iff_eq, Bool.false_eq_true, d1, h1']
    rcases delitemCommon h ix.toNat s with ⟨r, s'⟩
    cases r <;> rfl
  · intro s hs
    refine ⟨fun dv => ?_, ?_⟩ <;> rw [hpd, hs]
  · intro v s hs dflt
    rw [hpd, hs]
  · intro e s hs dflt
    rw [hpd, hs]
  · intro e
    rfl

/-! ## `setdefault` through the C API -/

/-- `PyDict_SetDefaultRef` never dereferences NULL on a fresh instance `__dict__`, for every key type
keeping the hash/eq contract. -/
def PyDictSetDefaultRefNoCrash : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (attrs : List K) (key : K) (dflt : V),
      (pyDictSetDefaultRef P true key dflt
        (newDictWithSharedKeys 1 (dictNewKeysForClass P attrs))).1 ≠ .error (crash "")

theorem pyDictSetDefaultRefNoCrash_refuted : ¬PyDictSetDefaultRefNoCrash := by
  intro h
  exact h Nat Nat strSubProto _ _ strSubProto_honest [0] 1 7 (by decide +kernel)

/-- `PyDict_SetDefault` keeps its contract on a fresh instance `__dict__`: it returns the value now
under the key, or NULL with an exception set; never NULL without one. -/
def PyDictSetDefaultContract : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (attrs : List K) (key : K) (dflt : V),
      (pyDictSetDefaultC P true key dflt
        (newDictWithSharedKeys 1 (dictNewKeysForClass P attrs))).1 ≠ .ok none

theorem pyDictSetDefaultContract_refuted : ¬PyDictSetDefaultContract := by
  intro h
  exact h Nat Nat strSubProto _ _ strSubProto_honest [0] 1 7 (by decide +kernel)

/-- Whether a merge that succeeded left `key` in the dict. -/
def seq2KeptCheck (P : Proto K (PyDict K V)) (key : K) (r : Py Unit × PyDict K V) : Bool :=
  match r with
  | (.ok (), d) => decide ((pyDictContains P key d).1 = .ok true)
  | (.error _, _) => true

/-- `PyDict_MergeFromSeq2(d, [(key, v)], 0)` on a fresh instance `__dict__` that does not hold `key`
puts `key` in, for every key type keeping the hash/eq contract: override 0 keeps only the keys
already there. -/
def MergeSeq2KeepsAbsent : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (attrs : List K) (key : K) (v : V),
      (pyDictContains P key (newDictWithSharedKeys 1 (dictNewKeysForClass P attrs))).1 = .ok false →
      seq2KeptCheck P key (pyDictMergeFromSeq2C P true
        (ReIter.ofIterable { items := [Seq2Item.pair key v] }) false
        (newDictWithSharedKeys 1 (dictNewKeysForClass P attrs))) = true

theorem mergeSeq2KeepsAbsent_refuted : ¬MergeSeq2KeepsAbsent := by
  intro h
  exact absurd (h Nat Nat strSubProto _ _ strSubProto_honest [0] 1 7 (by decide +kernel))
    (by decide +kernel)

/-! ## `setdefault` on a dict that keeps the contract -/

section SD
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

theorem dictInv_emptyKeys_assoc (mp : PyDict K V) (hd : DictInv hf eqv P.isStr mp)
    (hE : mp.body.isEmptyKeys = true) : dictAssoc mp = [] := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have hlog : k.log2Size = 0 := by simpa [Body.isEmptyKeys, Body.log2Size, hb] using hE
  have hnil : k.entries = [] := by
    have h1 := w.nent
    have h2 := w.usableNN
    have hU : usableFraction k.size = 0 := by simp [Keys.size, hlog, usableFraction]
    rw [hU] at h1
    have : k.nentries = 0 := by omega
    exact List.length_eq_zero_iff.mp this
  simp [dictAssoc, hb, Keys.items, liveEntries, hnil]

/-- `dict_setdefault_ref_lock_held` on a well-formed dict, for an honest protocol. -/
theorem setdefault_refines (H : Honest P hf eqv) (mp : PyDict K V) (hd : DictInv hf eqv P.isStr mp)
    (key : K) (dflt : V) (r i : Bool) :
    (∀ v, assocGet eqv (dictAssoc mp) key = some v →
      dictSetdefaultRef P key dflt r i mp = (.ok (1, some v), mp)) ∧
    (assocGet eqv (dictAssoc mp) key = none →
      (TooBig mp.used ∧ dictSetdefaultRef P key dflt r i mp = (.error memoryError, mp)) ∨
      ∃ d', dictSetdefaultRef P key dflt r i mp = (.ok (0, some dflt), d') ∧
        DictInv hf eqv P.isStr d' ∧ dictAssoc d' = assocSet eqv (dictAssoc mp) key dflt) := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  by_cases hE : mp.body.isEmptyKeys = true
  · have ha := dictInv_emptyKeys_assoc mp hd hE
    refine ⟨fun v hv => by simp [ha, assocGet] at hv, fun _ => ?_⟩
    have hsd : dictSetdefaultRef P key dflt r i mp =
        match dictSetItem P key dflt mp with
        | (.ok _, s) => (.ok (0, some dflt), s)
        | (.error e, s) => (.error e, s) := by
      simp only [dictSetdefaultRef, dictSetItem, M.bind_run, hashKey_ok H, M.get_run, hE, H.hash_ok, H.hash_quiet,
        if_true]
      rfl
    rcases dictSetItem_spec H mp hd key dflt with ⟨hbig, h1⟩ | ⟨d', h1, h2, h3⟩
    · left; exact ⟨hbig, by rw [hsd, h1]⟩
    · right; exact ⟨d', by rw [hsd, h1], h2, h3⟩
  · have hE' : mp.body.isEmptyKeys = false := by simpa using hE
    have hEk : (Body.combined k : Body K V).isEmptyKeys = false := hb ▸ hE'
    obtain ⟨ix, hl, hnone, hsome⟩ := lookup_assoc H mp hd key
    refine ⟨fun v hv => ?_, fun hv => ?_⟩
    · have hix := hsome v hv
      have hne : (ix == DKIX_EMPTY) = false := by
        simp only [DKIX_EMPTY, beq_eq_false_iff_ne]; omega
      have hne2 : ix ≠ DKIX_EMPTY := by simp only [DKIX_EMPTY]; omega
      simp [dictSetdefaultRef, M.bind_run, hashKey_ok H, M.get_run, hEk, hb, hl, hv, hne, hne2]
    · have hix := hnone hv
      subst hix
      have hins : insertDict P key (hf key) dflt mp =
          match insertCombinedDict P.toKeyOps (hf key) key dflt mp with
          | (.ok _, s) => (.ok (), { s with used := s.used + 1 })
          | (.error e, s) => (.error e, s) := by
        (simp only [insertDict, hb, hl, hv, insertAfterLookup]) <;> rfl
      have hsd : dictSetdefaultRef P key dflt r i mp =
          match insertCombinedDict P.toKeyOps (hf key) key dflt mp with
          | (.ok _, s) => (.ok (0, some dflt), { s with used := s.used + 1 })
          | (.error e, s) => (.error e, s) := by
        simp only [dictSetdefaultRef, M.bind_run, hashKey_ok H, M.get_run, hEk, hb,
          Bool.false_eq_true, if_false, hl, hv, beq_self_eq_true, if_true]
        rcases insertCombinedDict P.toKeyOps (hf key) key dflt mp with ⟨a, t⟩
        cases a <;> rfl
      rcases insertDict_inv H mp hd key dflt with ⟨hbig, h1⟩ | ⟨d', h1, h2, h3⟩
      · left
        refine ⟨hbig, ?_⟩
        rw [hsd]
        rw [hins] at h1
        revert h1
        rcases insertCombinedDict P.toKeyOps (hf key) key dflt mp with ⟨a, t⟩
        cases a with
        | ok u => intro h1; simp at h1
        | error e => intro h1; simp only [Prod.mk.injEq] at h1; rw [h1.1, h1.2]
      · right
        refine ⟨d', ?_, h2, h3⟩
        rw [hsd]
        rw [hins] at h1
        revert h1
        rcases insertCombinedDict P.toKeyOps (hf key) key dflt mp with ⟨a, t⟩
        cases a with
        | ok u => intro h1; simp only [Prod.mk.injEq] at h1; rw [← h1.2]
        | error e => intro h1; simp at h1

end SD

/-- `dict.setdefault`, `PyDict_SetDefaultRef`, `PyDict_SetDefault`, on a well-formed dict and for an
honest protocol: a present key gives status 1 and its value, the dict unchanged; an absent one is
stored with the default, status 0, by `insert_to_emptydict` on an empty table and
`insert_combined_dict` otherwise, as `d[key] = default` would, or `MemoryError`. -/
def SetdefaultRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V), DictInv hf eqv P.isStr mp →
      ∀ (key : K) (dflt : V) (r i : Bool),
      (∀ v, assocGet eqv (dictAssoc mp) key = some v →
        dictSetdefaultRef P key dflt r i mp = (.ok (1, some v), mp)) ∧
      (assocGet eqv (dictAssoc mp) key = none →
        (TooBig mp.used ∧ dictSetdefaultRef P key dflt r i mp = (.error memoryError, mp)) ∨
        ∃ d', dictSetdefaultRef P key dflt r i mp = (.ok (0, some dflt), d') ∧
          DictInv hf eqv P.isStr d' ∧ dictAssoc d' = assocSet eqv (dictAssoc mp) key dflt)

theorem setdefaultRefines_proven : SetdefaultRefines := fun _ _ _ _ _ _ H mp hd key dflt r i =>
  setdefault_refines H mp hd key dflt r i

/-- The split-table branch of `dict_setdefault_ref_lock_held` (:4817-4830) for an exact `str` key, for
every protocol, on the dict as `__hash__` left it: a failed `insert_split_key` is the result; a slot of
the shared keys with a value
gives status 1 and that value; a slot with none stores the default there with
`_PyDict_InsertSplitValue`, status 0. -/
def SetdefaultSplitStr : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (dflt : V) (r i : Bool)
    (mp : PyDict K V) (keys keys' : Keys K Unit) (vals : Values V) (h : Int) (ix : Int),
    P.hash key = .ok h → (P.hashEff key mp).body = .split keys vals →
    (P.hashEff key mp).body.isEmptyKeys = false →
    P.isStr key = true →
    (∀ e, insertSplitKey P keys key h = .error e →
      dictSetdefaultRef P key dflt r i mp = (.error e, P.hashEff key mp)) ∧
    (insertSplitKey P keys key h = .ok (ix, keys') → ix ≠ DKIX_EMPTY →
      (∀ v, vals.get ix.toNat = some v →
        dictSetdefaultRef P key dflt r i mp = (.ok (1, some v), { P.hashEff key mp with body := .split keys' vals })) ∧
      (vals.get ix.toNat = none →
        dictSetdefaultRef P key dflt r i mp =
          (do insertSplitValue dflt ix.toNat; return ((0 : Nat), some dflt))
            { P.hashEff key mp with body := .split keys' vals }))

theorem setdefaultSplitStr_proven : SetdefaultSplitStr := by
  intro K V _ P key dflt r i mp keys keys' vals h ix hh hb hE hs
  have hEk : (Body.split keys vals : Body K V).isEmptyKeys = false := hb ▸ hE
  refine ⟨fun e he => ?_, fun hk hne => ⟨fun v hv => ?_, fun hv => ?_⟩⟩
  · simp [dictSetdefaultRef, M.bind_run, M.lift_run, M.put_run, hashKey, hh, hEk, hb, hs, he]
  · have : (ix != DKIX_EMPTY) = true := by simpa using hne
    simp [dictSetdefaultRef, M.bind_run, M.lift_run, M.put_run, hashKey, hh, hEk, hb, hs, hk, this, hv, hne]
  · have : (ix != DKIX_EMPTY) = true := by simpa using hne
    simp [dictSetdefaultRef, M.bind_run, M.lift_run, M.put_run, hashKey, hh, hEk, hb, hs, hk, this, hv, hne]

end PyLean.DictSet
