import PyLean.DictSet.Props2

/-!
Failure paths. Nothing here assumes `Honest`: these hold for every key protocol, including one
whose `__hash__` raises and whose `__eq__` raises or mutates the dict being probed. They are what
the refinement theorems leave out.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `PyDict_GetItem` never raises, for any protocol and any dict: "PyDict_GetItem() suppresses all
errors" (`dictobject.c:2290-2299`). This is the function's whole contract, and it is why a failing
comparison can look like a missing key. -/
theorem dictGetitemSuppress_total (P : Proto K (PyDict K V)) (isDict : Bool) (key : K)
    (d : PyDict K V) : ∃ r d', dictGetitemSuppress P isDict key d = (.ok r, d') := by
  unfold dictGetitemSuppress
  cases isDict with
  | false => exact ⟨none, d, rfl⟩
  | true =>
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    cases hh : P.hash key with
    | error e => exact ⟨none, d, rfl⟩
    | ok h =>
      simp only [M.tryCatch]
      cases hr : (dictLookup P key h >>= fun r => pure r.2) d with
      | mk a s =>
        cases a with
        | error e => exact ⟨none, s, rfl⟩
        | ok v => exact ⟨v, s, rfl⟩

/-- Every entry point that hashes first reports a failed hash as `dict_unhashable_type` does and
leaves the dict alone: an exact `TypeError` is rewritten, anything else passes through. -/
theorem hash_failure (P : Proto K (PyDict K V)) (key : K) (e : PyExc) (hh : P.hash key = .error e)
    (d : PyDict K V) (v : V) :
    let err := dictUnhashableType P key e
    dictSetItem P key v d = (.error err, d) ∧
    dictDelItem P key d = (.error err, d) ∧
    pyDictContains P key d = (.error err, d) ∧
    dictSubscript P none key d = (.error err, d) ∧
    dictGet P key v d = (.error err, d) ∧
    pyDictGetItemWithError P true key d = (.error err, d) ∧
    pyDictGetItemRef P true key d = (.error err, d) := by
  intro err
  have hk : ∀ {β : Type} (f : Int → DM K V β), (hashKey P key >>= f) d = (.error err, d) := by
    intro β f
    apply M.bind_err
    simp only [hashKey, hh]
    rfl
  refine ⟨?_, ?_, hk _, hk _, hk _, ?_, ?_⟩
  · simp only [dictSetItem, hh, err]
  · simp only [dictDelItem, hh, err]
  · simp only [pyDictGetItemWithError, Bool.not_true, Bool.false_eq_true, if_false]
    show (pure PUnit.unit >>= fun _ => hashKey P key >>= fun h =>
      dictLookup P key h >>= fun r => pure r.2) d = _
    rw [M.bind_run]
    exact hk _
  · simp only [pyDictGetItemRef, Bool.not_true, Bool.false_eq_true, if_false]
    show (pure PUnit.unit >>= fun _ => hashKey P key >>= fun h =>
      dictGetItemRefKnownHash P key h) d = _
    rw [M.bind_run]
    exact hk _

/-- On an empty dict `pop` answers before hashing, so an unhashable key is not an error there, while
on any non-empty dict it is. Both halves are reachable: `{}.pop([], 1)` returns 1. -/
theorem pop_hash_order (P : Proto K (PyDict K V)) (key : K) (e : PyExc) (hh : P.hash key = .error e)
    (d : PyDict K V) :
    (d.used = 0 → pyDictPop P true key d = (.ok none, d)) ∧
    (d.used ≠ 0 → pyDictPop P true key d = (.error (dictUnhashableType P key e), d)) := by
  constructor
  · intro h
    simp [pyDictPop, h]
  · intro h
    simp [pyDictPop, h, hh]

/-- A comparison that raises on the first entry the search compares ends the search with that
exception, and whatever the comparison had done to the state stands. -/
theorem doLookup_raises {σ : Type} (getIx : σ → Nat → Int) (check : Nat → M σ Int) (mask u : Nat)
    (s s' : σ) (e : PyExc) (fuel : Nat) (hix : getIx s (u &&& mask) ≥ 0)
    (hck : check (getIx s (u &&& mask)).toNat s = (.error e, s')) :
    doLookup getIx check (fuel + 1) mask (u &&& mask) u s = (.error e, s') := by
  simp only [doLookup]
  rw [if_pos hix]
  simp only [hck]

/-- `compare_generic` on a comparison that raises: `DKIX_ERROR`, and `__eq__`'s effects stand. -/
theorem compareGeneric_raises (P : Proto K (PyDict K V)) (mp mp' : PyDict K V) (ix : Nat) (key epKey : K)
    (hash : Int) (e : PyExc) (he : mp.body.entryKH ix = some (epKey, hash)) (hne : epKey ≠ key)
    (hq : P.eq epKey key mp = (.error e, mp')) :
    compareGeneric P ix key hash mp = (.error e, mp') := by
  simp [compareGeneric, he, hne, hq]

/-- `compare_generic` when `__eq__` changed the table under it: `DKIX_KEY_CHANGED`, whatever `__eq__`
answered. That is the check at `dictobject.c:1118`, which keeps a stale answer from being trusted. -/
theorem compareGeneric_changed (P : Proto K (PyDict K V)) (mp mp' : PyDict K V) (ix : Nat) (key epKey : K)
    (hash : Int) (b : Bool) (he : mp.body.entryKH ix = some (epKey, hash)) (hne : epKey ≠ key)
    (hq : P.eq epKey key mp = (.ok b, mp'))
    (hch : stillThere mp' mp.body.ident ix epKey = false) :
    compareGeneric P ix key hash mp = (.ok DKIX_KEY_CHANGED, mp') := by
  simp [compareGeneric, he, hne, hq, hch]

/-- `_Py_dict_lookup` restarts on `DKIX_KEY_CHANGED`: the answer is the one on the mutated dict. -/
theorem lookup_restarts (P : Proto K (PyDict K V)) (key : K) (hash : Int) (n : Nat) (mp mp' : PyDict K V)
    (hg : mp.body.kind = .general)
    (hr : dictkeysGenericLookup P mp.body.mask (probeFuel mp.body.log2Size) key hash mp =
      (.ok DKIX_KEY_CHANGED, mp')) :
    dictLookupAux P key hash (n + 1) mp = dictLookupAux P key hash n mp' := by
  simp only [dictLookupAux, hg, bne_self_eq_false, Bool.false_eq_true, if_false, hr]
  rfl

/-- `__missing__`: a subclass's hook runs on an absent key, and its outcome, value or exception, is
the result (`dictobject.c:3520-3530`). -/
theorem subscript_missing {P : Proto K (PyDict K V)} {hf : K → Int} {eqv : K → K → Bool}
    (H : Honest P hf eqv) (d : PyDict K V) (hd : DictInv hf eqv P.isStr d) (key : K)
    (f : K → Py V) (habs : assocGet eqv (dictAssoc d) key = none) :
    dictSubscript P (some f) key d = (f key, d) := by
  obtain ⟨ix, h1, _, _⟩ := lookup_assoc H d hd key
  rw [habs] at h1
  simp only [dictSubscript, M.bind_run, hashKey_ok H key d, h1]
  rfl

/-- `PyDict_GetItem` never raises. -/
def GetItemSuppressed : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (isDict : Bool) (key : K) (d : PyDict K V),
    ∃ r d', dictGetitemSuppress P isDict key d = (.ok r, d')
theorem getItemSuppressed_proven : GetItemSuppressed := fun _ _ _ P isDict key d =>
  dictGetitemSuppress_total P isDict key d

/-- A failed hash, for any protocol. -/
def HashFailureFamily : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (e : PyExc), P.hash key = .error e →
    ∀ (d : PyDict K V) (v : V),
      let err := dictUnhashableType P key e
      dictSetItem P key v d = (.error err, d) ∧
      dictDelItem P key d = (.error err, d) ∧
      pyDictContains P key d = (.error err, d) ∧
      dictSubscript P none key d = (.error err, d) ∧
      dictGet P key v d = (.error err, d) ∧
      pyDictGetItemWithError P true key d = (.error err, d) ∧
      pyDictGetItemRef P true key d = (.error err, d)
theorem hashFailureFamily_proven : HashFailureFamily := fun _ _ _ P key e hh d v =>
  hash_failure P key e hh d v

/-- `dict.pop` on an empty dict does not hash the key; on a non-empty one it does. -/
def PopHashOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (e : PyExc), P.hash key = .error e →
    ∀ d : PyDict K V,
      (d.used = 0 → pyDictPop P true key d = (.ok none, d)) ∧
      (d.used ≠ 0 → pyDictPop P true key d = (.error (dictUnhashableType P key e), d))
theorem popHashOrder_proven : PopHashOrder := fun _ _ _ P key e hh d => pop_hash_order P key e hh d

/-- `compare_generic`, the paths `Honest` rules out: a raising `__eq__`, and one that changes the table. -/
def CompareGenericFailure : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (mp mp' : PyDict K V) (ix : Nat) (key epKey : K)
    (hash : Int), mp.body.entryKH ix = some (epKey, hash) → epKey ≠ key →
    (∀ e, P.eq epKey key mp = (.error e, mp') → compareGeneric P ix key hash mp = (.error e, mp')) ∧
    (∀ b, P.eq epKey key mp = (.ok b, mp') → stillThere mp' mp.body.ident ix epKey = false →
      compareGeneric P ix key hash mp = (.ok DKIX_KEY_CHANGED, mp'))
theorem compareGenericFailure_proven : CompareGenericFailure := fun _ _ _ P mp mp' ix key epKey hash he hne =>
  ⟨fun e hq => compareGeneric_raises P mp mp' ix key epKey hash e he hne hq,
   fun b hq hch => compareGeneric_changed P mp mp' ix key epKey hash b he hne hq hch⟩

/-- `_Py_dict_lookup`'s `goto start`. -/
def LookupRestarts : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (hash : Int) (n : Nat)
    (mp mp' : PyDict K V), mp.body.kind = .general →
    dictkeysGenericLookup P mp.body.mask (probeFuel mp.body.log2Size) key hash mp =
      (.ok DKIX_KEY_CHANGED, mp') →
    dictLookupAux P key hash (n + 1) mp = dictLookupAux P key hash n mp'
theorem lookupRestarts_proven : LookupRestarts := fun _ _ _ P key hash n mp mp' hg hr =>
  lookup_restarts P key hash n mp mp' hg hr

/-- `d[key]` on an absent key of a subclass with `__missing__`. -/
def MissingHook : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → ∀ (key : K) (f : K → Py V),
      assocGet eqv (dictAssoc d) key = none → dictSubscript P (some f) key d = (f key, d)
theorem missingHook_proven : MissingHook := fun _ _ _ _ _ _ H d hd key f habs =>
  subscript_missing H d hd key f habs

end PyLean.DictSet
