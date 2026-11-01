import PyLean.DictSet.Props

/-!
The C API read family, `pop`, `clear`, sizes and forward iteration, on a well-formed combined
table. Each of these functions has its own definition in `DictOps.lean`, following its own
branches; the theorems here run them through the lookup and deletion results.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

section
variable {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}

theorem hashKey_ok (H : Honest P hf eqv) (key : K) (s : PyDict K V) :
    hashKey P key s = (.ok (hf key), s) := by
  simp only [hashKey, H.hash_ok]
  rfl

/-- The read family. All of them agree with the list, and none changes the dict. -/
theorem read_family (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d) (key : K) :
    let r := assocGet eqv (dictAssoc d) key
    dictGetitemSuppress P true key d = (.ok r, d) ∧
    dictGetItemKnownHash P true key (hf key) d = (.ok r, d) ∧
    dictGetItemRefKnownHash P key (hf key) d = (.ok r, d) ∧
    pyDictGetItemRef P true key d = (.ok r, d) ∧
    dictGetItemRefUnicode P key d = (.ok r, d) ∧
    pyDictGetItemWithError P true key d = (.ok r, d) ∧
    dictGetItemWithErrorUnchecked P key d = (.ok r, d) := by
  obtain ⟨ix, h1, _, _⟩ := lookup_assoc H d hd key
  intro r
  have hl : dictLookup P key (hf key) d = (.ok (ix, r), d) := h1
  have hb : ∀ {β : Type} (f : Int × Option V → DM K V β),
      (dictLookup P key (hf key) >>= f) d = f (ix, r) d := fun f => M.bind_ok hl
  have hh : ∀ {β : Type} (f : Int → DM K V β),
      (hashKey P key >>= f) d = f (hf key) d := fun f => M.bind_ok (hashKey_ok H key d)
  have known : dictGetItemKnownHash P true key (hf key) d = (.ok r, d) := by
    simp only [dictGetItemKnownHash, Bool.not_true, Bool.false_eq_true, if_false]
    show (pure PUnit.unit >>= fun _ => dictLookup P key (hf key) >>= fun r => pure r.2) d = _
    simp only [M.bind_run, M.pure_run, hl]
  have refk : dictGetItemRefKnownHash P key (hf key) d = (.ok r, d) := by
    simp only [dictGetItemRefKnownHash, hb]
    cases r <;> rfl
  refine ⟨?_, known, refk, ?_, ?_, ?_, ?_⟩
  · simp only [dictGetitemSuppress, Bool.not_true, Bool.false_eq_true, if_false, H.hash_ok]
    simp only [M.tryCatch, hb]
    rfl
  · simp only [pyDictGetItemRef, Bool.not_true, Bool.false_eq_true, if_false]
    show (pure PUnit.unit >>= fun _ => hashKey P key >>= fun h => dictGetItemRefKnownHash P key h) d = _
    simp only [M.bind_run, M.pure_run, hashKey_ok H key d, refk]
  · simp only [dictGetItemRefUnicode, hh, hb]
    cases r <;> rfl
  · simp only [pyDictGetItemWithError, Bool.not_true, Bool.false_eq_true, if_false]
    show (pure PUnit.unit >>= fun _ => hashKey P key >>= fun h =>
      dictLookup P key h >>= fun r => pure r.2) d = _
    simp only [M.bind_run, M.pure_run, hashKey_ok H key d, hl]
  · simp only [dictGetItemWithErrorUnchecked, M.bind_run, M.lift_run, H.hash_ok, known]

/-- `key in d`. -/
theorem contains_spec (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d) (key : K) :
    pyDictContains P key d = (.ok (assocGet eqv (dictAssoc d) key).isSome, d) ∧
    dictContainsKnownHash P key (hf key) d = (.ok (assocGet eqv (dictAssoc d) key).isSome, d) := by
  obtain ⟨ix, h1, h2, h3⟩ := lookup_assoc H d hd key
  have known : dictContainsKnownHash P key (hf key) d =
      (.ok (assocGet eqv (dictAssoc d) key).isSome, d) := by
    simp only [dictContainsKnownHash, M.bind_run, h1, M.pure_run]
    cases hq : assocGet eqv (dictAssoc d) key with
    | none => simp [h2 hq, DKIX_EMPTY]
    | some v =>
      have := h3 v hq
      have hne : (ix != DKIX_EMPTY) = true := by
        simp [DKIX_EMPTY]
        omega
      simp [hne]
  refine ⟨?_, known⟩
  simp only [pyDictContains, M.bind_run, hashKey_ok H key d, known]

/-- `d[key]`, without `__missing__`. -/
theorem subscript_spec (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d) (key : K) :
    dictSubscript P none key d =
      match assocGet eqv (dictAssoc d) key with
      | some v => (.ok v, d)
      | none => (.error (keyErr P key), d) := by
  obtain ⟨ix, h1, _, h3⟩ := lookup_assoc H d hd key
  simp only [dictSubscript, M.bind_run, hashKey_ok H key d, h1]
  cases hq : assocGet eqv (dictAssoc d) key with
  | none => rfl
  | some v =>
    have := h3 v hq
    have hne : (ix == DKIX_EMPTY) = false := by
      simp [DKIX_EMPTY]
      omega
    simp [hne]

/-- `dict.pop` without a default, through every layer: `dict_pop_default`, `PyDict_Pop`,
`pop_lock_held`, `_PyDict_Pop_KnownHash`. -/
theorem pop_spec (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d) (key : K) :
    (assocGet eqv (dictAssoc d) key = none ∧ pyDictPop P true key d = (.ok none, d)) ∨
    ∃ v d', assocGet eqv (dictAssoc d) key = some v ∧ pyDictPop P true key d = (.ok (some v), d') ∧
      DictInv hf eqv P.isStr d' ∧ dictAssoc d' = assocDel eqv (dictAssoc d) key := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  have ha : dictAssoc d = k.items := by simp [dictAssoc, hb]
  obtain ⟨ix, h1, h2, h3⟩ := lookup_assoc H d hd key
  by_cases h0 : d.used = 0
  · left
    have hnil : liveEntries k = [] := List.length_eq_zero_iff.mp (by omega)
    have hget : assocGet eqv (dictAssoc d) key = none := by
      simp [ha, Keys.items, hnil, assocGet]
    refine ⟨hget, ?_⟩
    simp [pyDictPop, h0]
  · cases hq : assocGet eqv (dictAssoc d) key with
    | none =>
      left
      refine ⟨rfl, ?_⟩
      rw [hq] at h1
      simp [pyDictPop, dictPopKnownHash, h0, H.hash_ok, h1]
    | some v =>
      right
      rcases dichotomy (eqv := eqv) k key with ⟨t, e, a, b⟩ | hno
      · have hhash : e.hash = hf key := (w.hashes t e a).trans (H.hash_cons _ _ b)
        have hl := lookup_found H d k hb w key t e a b
        obtain ⟨d', c1, c2, c3⟩ := delitemCommon_spec H d k hb w hu key t e a b
        rw [hhash] at c1
        have hval : e.value = v := by
          rw [hl] at h1
          rw [hq] at h1
          have := congrArg Prod.fst h1
          simp at this
          exact this.2
        refine ⟨v, d', rfl, ?_, c2, by rw [ha]; exact c3⟩
        have hne2 : ((t : Int) == DKIX_EMPTY) = false := by
          simp [DKIX_EMPTY]
        simp [pyDictPop, dictPopKnownHash, h0, H.hash_ok, hl, hne2, c1, hval]
      · rw [ha] at hq
        simp only [assocGet, Option.map_eq_some_iff, Prod.exists] at hq
        obtain ⟨a, b, h5, _⟩ := hq
        have := List.find?_some (p := fun p : K × V => eqv p.1 key) h5
        have hmem := List.mem_of_find?_eq_some h5
        simp only [Keys.items, List.mem_map] at hmem
        obtain ⟨e, he, heq⟩ := hmem
        obtain ⟨t, ht⟩ := (mem_live k e).mp he
        have h6 := hno t e ht
        rw [Prod.mk.injEq] at heq
        rw [heq.1] at h6
        simp [h6] at this

/-- `d.clear()` empties the list, and the table is still well formed. -/
theorem clear_spec (d : PyDict K V) (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool)
    (hd : DictInv hf eqv isStr d) :
    DictInv hf eqv isStr (dictClear d) ∧ dictAssoc (dictClear d) = [] := by
  obtain ⟨k, hb, w, hu⟩ := hd.wf
  by_cases hE : d.body.isEmptyKeys = true
  · have hlog : k.log2Size = 0 := by simpa [Body.isEmptyKeys, Body.log2Size, hb] using hE
    have hnil : k.entries = [] := by
      have h1 := w.nent
      have h2 := w.usableNN
      have hU : usableFraction k.size = 0 := by simp [Keys.size, hlog, usableFraction]
      rw [hU] at h1
      have : k.nentries = 0 := by omega
      exact List.length_eq_zero_iff.mp this
    simp only [dictClear, hE, if_true]
    exact ⟨hd, by simp [dictAssoc, hb, Keys.items, liveEntries, hnil]⟩
  · have hd' : dictClear d = { d with used := 0, body := .combined emptyKeys } := by
      unfold dictClear
      rw [if_neg hE, hb]
    rw [hd']
    refine ⟨⟨⟨emptyKeys, rfl, wf_empty hf eqv isStr, by simp [liveEntries, emptyKeys]⟩⟩, ?_⟩
    simp [dictAssoc, Keys.items, liveEntries, emptyKeys]

/-- `len(d)`: `ma_used` is the length of the list. -/
theorem len_spec (d : PyDict K V) (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool)
    (hd : DictInv hf eqv isStr d) : d.used = (dictAssoc d).length := by
  obtain ⟨k, hb, _, hu⟩ := hd.wf
  simp [dictAssoc, hb, Keys.items, hu]

end

/-- A forward iterator over an unchanged dict yields the rest of the list, then stops. -/
theorem forward_drain (d : PyDict K V) (k : Keys K V) (hb : d.body = .combined k) :
    ∀ (fuel : Nat) (di : DictIter) (i : Nat) (acc : List (K × V)),
      di.alive = true → di.rev = false → di.used = d.used → di.pos = (i : Int) →
      di.len = (((k.entries.drop i).filterMap id).length : Int) →
      ((k.entries.drop i).filterMap id).length < fuel →
      (dictiterDrain d fuel di acc).1 =
        .ok (acc.reverse ++ ((k.entries.drop i).filterMap id).map fun e => (e.key, e.value)) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ _ h; omega
  | succ fuel ih =>
    intro di i acc ha hr hu hp hl hf
    have hne : (di.used != (d.used : Int)) = false := by simp [hu]
    rcases scanFrom_spec (k.entries.drop i) i with ⟨h1, h2⟩ | ⟨m, e, h1, h2⟩
    · have hn : dictiterNext d di =
          (.ok none, { di with alive := false }) := by
        simp [dictiterNext, hr, dictiterNextForward, ha, hu, hb, hp, h1]
      simp only [dictiterDrain, hn, h2]
      simp
    · have hlen : ((k.entries.drop i).filterMap id).length =
          ((k.entries.drop (i + m + 1)).filterMap id).length + 1 := by
        have hd : (k.entries.drop i).drop (m + 1) = k.entries.drop (i + m + 1) := by
          rw [List.drop_drop]
          congr 1 <;> omega
        rw [h2, hd]
        simp
      have hl0 : (di.len == 0) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]
        rw [hl]
        omega
      have hn : dictiterNext d di = (.ok (some (e.key, e.value)),
          { di with pos := ((i + m : Nat) : Int) + 1, len := di.len - 1 }) := by
        simp [dictiterNext, hr, dictiterNextForward, ha, hu, hb, hp, h1, hl0]
      have hd : (k.entries.drop i).drop (m + 1) = k.entries.drop (i + m + 1) := by
        rw [List.drop_drop]
        congr 1 <;> omega
      simp only [dictiterDrain, hn]
      rw [ih { di with pos := ((i + m : Nat) : Int) + 1, len := di.len - 1 } (i + m + 1)
        ((e.key, e.value) :: acc) ha hr hu (by simp) (by simp only [hl]; omega) (by omega)]
      rw [h2, hd]
      simp

/-- The C API reads. -/
def ReadFamily : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → ∀ key : K,
      let r := assocGet eqv (dictAssoc d) key
      dictGetitemSuppress P true key d = (.ok r, d) ∧
      dictGetItemKnownHash P true key (hf key) d = (.ok r, d) ∧
      dictGetItemRefKnownHash P key (hf key) d = (.ok r, d) ∧
      pyDictGetItemRef P true key d = (.ok r, d) ∧
      dictGetItemRefUnicode P key d = (.ok r, d) ∧
      pyDictGetItemWithError P true key d = (.ok r, d) ∧
      dictGetItemWithErrorUnchecked P key d = (.ok r, d)
theorem readFamily_proven : ReadFamily := fun _ _ _ _ _ _ H d hd key => read_family H d hd key

/-- `key in d`. -/
def ContainsSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → ∀ key : K,
      pyDictContains P key d = (.ok (assocGet eqv (dictAssoc d) key).isSome, d) ∧
      dictContainsKnownHash P key (hf key) d = (.ok (assocGet eqv (dictAssoc d) key).isSome, d)
theorem containsSpec_proven : ContainsSpec := fun _ _ _ _ _ _ H d hd key => contains_spec H d hd key

/-- `d[key]`. -/
def SubscriptSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → ∀ key : K,
      dictSubscript P none key d =
        match assocGet eqv (dictAssoc d) key with
        | some v => (.ok v, d)
        | none => (.error (keyErr P key), d)
theorem subscriptSpec_proven : SubscriptSpec := fun _ _ _ _ _ _ H d hd key =>
  subscript_spec H d hd key

/-- `dict.pop`: removes what the list holds, and an absent key changes nothing. -/
def PopSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → ∀ key : K,
      (assocGet eqv (dictAssoc d) key = none ∧ pyDictPop P true key d = (.ok none, d)) ∨
      ∃ v d', assocGet eqv (dictAssoc d) key = some v ∧ pyDictPop P true key d = (.ok (some v), d') ∧
        DictInv hf eqv P.isStr d' ∧ dictAssoc d' = assocDel eqv (dictAssoc d) key
theorem popSpec_proven : PopSpec := fun _ _ _ _ _ _ H d hd key => pop_spec H d hd key

/-- `d.clear()`. -/
def ClearSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (d : PyDict K V) (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool),
    DictInv hf eqv isStr d → DictInv hf eqv isStr (dictClear d) ∧ dictAssoc (dictClear d) = []
theorem clearSpec_proven : ClearSpec := fun _ _ _ d hf eqv isStr hd => clear_spec d hf eqv isStr hd

/-- `len(d)`. -/
def LenSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (d : PyDict K V) (hf : K → Int) (eqv : K → K → Bool) (isStr : K → Bool),
    DictInv hf eqv isStr d → d.used = (dictAssoc d).length
theorem lenSpec_proven : LenSpec := fun _ _ _ d hf eqv isStr hd => len_spec d hf eqv isStr hd

end PyLean.DictSet
