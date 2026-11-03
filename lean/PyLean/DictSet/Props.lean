import PyLean.DictSet.DictProps2

/-!
The dict properties as closed statements for the registry. Each quantifies over every key type
that keeps the `__hash__`/`__eq__` contract and every well-formed combined table.
-/

namespace PyLean.DictSet

open PyLean

/-- `j -> 5*j + 1` visits every residue mod `2^n` within `2^n` steps. -/
def LcgFullPeriod : Prop := ∀ n x y : Nat, ∃ k, k < 2 ^ n ∧ lcg x k % 2 ^ n = y % 2 ^ n
theorem lcgFullPeriod_proven : LcgFullPeriod := lcg_full_period

/-- Every slot is on the probe sequence of every 64-bit hash. -/
def ProbeReachesAll : Prop :=
  ∀ n u s : Nat, u < 2 ^ 64 → s < 2 ^ n → ∃ j, j < 2 ^ n + 13 ∧ (probeState (2 ^ n - 1) u j).1 = s
theorem probeReachesAll_proven : ProbeReachesAll := probe_reaches_all

/-- `0 < USABLE_FRACTION(n) < n` for `n >= 2` (`dictobject.c:575-576`). -/
def UsableFractionBounds : Prop := ∀ n, 2 ≤ n → 0 < usableFraction n ∧ usableFraction n < n
theorem usableFractionBounds_proven : UsableFractionBounds := by
  intro n h
  refine ⟨?_, usableFraction_lt n (by omega)⟩
  simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one]
  omega

/-- `calculate_log2_keysize`: the table it picks holds `minsize`, and is at least 8. -/
def Log2KeysizeRoom : Prop := ∀ m, max m 8 ≤ 2 ^ calculateLog2Keysize m
theorem log2KeysizeRoom_proven : Log2KeysizeRoom := calculateLog2_room

/-- `estimate_log2_keysize`: "reserve enough size to insert n entries without resizing"
(`dictobject.c:606-610`). -/
def EstimateRoom : Prop := ∀ n, n ≤ usableFraction (2 ^ estimateLog2Keysize n)
theorem estimateRoom_proven : EstimateRoom := by
  intro n
  have h := calculateLog2_room ((n * 3 + 1) / 2)
  have e : estimateLog2Keysize n = calculateLog2Keysize ((n * 3 + 1) / 2) := rfl
  rw [e]
  simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one]
  generalize 2 ^ calculateLog2Keysize ((n * 3 + 1) / 2) = S at *
  omega

/-- Every entry index fits the signed slot width `dictkeys_set_index` picks for the table size
(`dictobject.c:550-566`): its `assert(ix <= 0x7f)` and `assert(ix <= 0x7fff)` cannot fail. The
largest index is below `USABLE_FRACTION(2**n)`. -/
def IndexWidthFits : Prop :=
  ∀ n, (n < 8 → usableFraction (2 ^ n) ≤ 0x7f + 1) ∧ (n < 16 → usableFraction (2 ^ n) ≤ 0x7fff + 1) ∧
    (n < 32 → usableFraction (2 ^ n) ≤ 0x7fffffff + 1)
theorem indexWidthFits_proven : IndexWidthFits := by
  intro n
  have mono : ∀ m, n < m → 2 ^ n ≤ 2 ^ (m - 1) := fun m h =>
    Nat.pow_le_pow_right (by omega) (by omega)
  simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := mono 8 h
    simp only [Nat.reduceSub, Nat.reducePow] at this
    omega
  · have := mono 16 h
    simp only [Nat.reduceSub, Nat.reducePow] at this
    omega
  · have := mono 32 h
    simp only [Nat.reduceSub, Nat.reducePow] at this
    omega

/-- After a growth resize there is room for at least one insertion, so `dk_usable` never
reaches the insert negative. -/
def GrowthRoom : Prop :=
  ∀ used, used < usableFraction (2 ^ calculateLog2Keysize (growthRate used))
theorem growthRoom_proven : GrowthRoom := growth_room

/-- `_Py_dict_lookup` finds an entry with an equal key, and changes nothing. -/
def LookupFound : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V) (k : Keys K V), mp.body = .combined k →
      WF hf eqv P.isStr k → ∀ (key : K) (ix : Nat) (e : Ent K V), k.entry ix = some e →
      eqv e.key key = true → dictLookup P key (hf key) mp = (.ok ((ix : Int), some e.value), mp)
theorem lookupFound_proven : LookupFound := fun _ _ _ _ _ _ H mp k hb w key ix e he heq =>
  lookup_found H mp k hb w key ix e he heq

/-- `_Py_dict_lookup` stops at an empty slot when no entry has an equal key. -/
def LookupMissing : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V) (k : Keys K V), mp.body = .combined k →
      WF hf eqv P.isStr k → ∀ key : K, (∀ ix e, k.entry ix = some e → eqv e.key key = false) →
      dictLookup P key (hf key) mp = (.ok (DKIX_EMPTY, none), mp)
theorem lookupMissing_proven : LookupMissing := fun _ _ _ _ _ _ H mp k hb w key hno =>
  lookup_missing H mp k hb w key hno

/-- `dict[key]` agrees with the association list. -/
def LookupAssoc : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (d : PyDict K V), DictInv hf eqv P.isStr d → ∀ key : K,
      ∃ ix, dictLookup P key (hf key) d = (.ok (ix, assocGet eqv (dictAssoc d) key), d)
theorem lookupAssoc_proven : LookupAssoc := fun _ _ _ _ _ _ H d hd key =>
  let ⟨ix, h, _, _⟩ := lookup_assoc H d hd key
  ⟨ix, h⟩

/-- `d[key] = v` is the list operation; the table stays well formed. The only failure is
`MemoryError`, with the dict unchanged, and only when a resize would need `2 ** 64` slots. -/
def SetItemRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V), DictInv hf eqv P.isStr mp → ∀ (key : K) (v : V),
      (TooBig mp.used ∧ dictSetItem P key v mp = (.error memoryError, mp)) ∨
      ∃ d', dictSetItem P key v mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc d' = assocSet eqv (dictAssoc mp) key v
theorem setItemRefines_proven : SetItemRefines := fun _ _ _ _ _ _ H mp hd key v =>
  dictSetItem_spec H mp hd key v

/-- A new key goes last; everything before it keeps its place. -/
def InsertionOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (eqv : K → K → Bool) (l : List (K × V)) (key : K) (v : V),
    l.any (fun p => eqv p.1 key) = false → assocSet eqv l key v = l ++ [(key, v)]
theorem insertionOrder_proven : InsertionOrder := by
  intro K V _ eqv l key v h
  simp [assocSet, h]

/-- Overwriting a key does not move it. -/
def OverwriteKeepsOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (eqv : K → K → Bool) (l : List (K × V)) (key : K) (v : V),
    (assocSet eqv l key v).map (·.1) = (if l.any (fun p => eqv p.1 key) then l.map (·.1)
      else l.map (·.1) ++ [key])
theorem overwriteKeepsOrder_proven : OverwriteKeepsOrder := by
  intro K V _ eqv l key v
  by_cases h : l.any (fun p => eqv p.1 key) = true
  · simp only [assocSet, h, if_true, List.map_map]
    apply List.map_congr_left
    intro p _
    by_cases hq : eqv p.1 key = true <;> simp [hq]
  · simp [assocSet, h]

/-- `PyDict_DelItem` (:2925-2936) on a frozendict: the hash, then the test of
`_PyDict_DelItem_KnownHash_LockHeld` (:2941-2949). -/
theorem dictDelItemChecked_frozen {K V : Type} [DecidableEq K] {P : Proto K (PyDict K V)}
    {hf : K → Int} {eqv : K → K → Bool} (H : Honest P hf eqv) (key : K) (mp : PyDict K V)
    (hfz : mp.frozen = true) :
    dictDelItemChecked P true key mp = (.error (frozendictNoSupport "deletion"), mp) := by
  simp [dictDelItemChecked, dictDelItemKnownHashChecked, H.hash_ok, H.hash_quiet, hfz]

/-- `PyDict_DelItem` on a dict is the body after the test. -/
theorem dictDelItemChecked_dict {K V : Type} [DecidableEq K] {P : Proto K (PyDict K V)}
    {hf : K → Int} {eqv : K → K → Bool} (H : Honest P hf eqv) (key : K) (mp : PyDict K V)
    (hfz : mp.frozen = false) : dictDelItemChecked P true key mp = dictDelItem P key mp := by
  simp [dictDelItemChecked, dictDelItemKnownHashChecked, dictDelItem, H.hash_ok, H.hash_quiet, hfz]

/-- `PyDict_DelItem`: a frozendict refuses with the `TypeError` of `frozendict_does_not_support`
and is unchanged; on a dict, `del d[key]` is the list operation, and a missing key raises and
changes nothing. -/
def DelItemRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V), DictInv hf eqv P.isStr mp → ∀ key : K,
      (mp.frozen = true ∧
        dictDelItemChecked P true key mp = (.error (frozendictNoSupport "deletion"), mp)) ∨
      (mp.frozen = false ∧
        (((dictAssoc mp).any (fun p => eqv p.1 key) = false ∧
          dictDelItemChecked P true key mp = (.error (keyErr P key), mp)) ∨
        ((dictAssoc mp).any (fun p => eqv p.1 key) = true ∧
          ∃ d', dictDelItemChecked P true key mp = (.ok (), d') ∧ DictInv hf eqv P.isStr d' ∧
            dictAssoc d' = assocDel eqv (dictAssoc mp) key)))
theorem delItemRefines_proven : DelItemRefines := by
  intro K V _ P hf eqv H mp hd key
  cases hfz : mp.frozen with
  | true => exact Or.inl ⟨rfl, dictDelItemChecked_frozen H key mp hfz⟩
  | false =>
    right
    refine ⟨rfl, ?_⟩
    rw [dictDelItemChecked_dict H key mp hfz]
    exact dictDelItem_spec H mp hd key

/-- `dict.popitem()` is LIFO (`Doc/library/stdtypes.rst`). -/
def PopitemLifo : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V), DictInv hf eqv P.isStr mp →
      (dictAssoc mp = [] ∧
        dictPopitem mp = (.error (.keyError "'popitem(): dictionary is empty'"), mp)) ∨
      ∃ p d', dictPopitem mp = (.ok p, d') ∧ DictInv hf eqv P.isStr d' ∧
        dictAssoc mp = dictAssoc d' ++ [p]
theorem popitemLifo_proven : PopitemLifo := fun _ _ _ _ _ _ H mp hd => dictPopitem_spec H mp hd

/-- `_PyDict_Next`, hence `keys()`, `values()`, `items()`, yields the list in order. -/
def IterationOrder : Prop :=
  ∀ (K V : Type) [DecidableEq K] (mp : PyDict K V) (k : Keys K V), mp.body = .combined k →
    dictItemsList mp = k.items
theorem iterationOrder_proven : IterationOrder := fun _ _ _ mp k hb => dictItemsList_spec mp k hb

/-- `dict.get(key, default)`. -/
def DictGetSpec : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V), DictInv hf eqv P.isStr mp → ∀ (key : K) (dflt : V),
      dictGet P key dflt mp = (.ok ((assocGet eqv (dictAssoc mp) key).getD dflt), mp)
theorem dictGetSpec_proven : DictGetSpec := fun _ _ _ _ _ _ H mp hd key dflt =>
  dictGet_spec H mp hd key dflt

/-- A run of `d[k] = v` and `del d[k]` from `{}`, against the same run on a list. -/
inductive DOp (K V : Type) where
  | set (k : K) (v : V)
  | del (k : K)

def absRun {K V : Type} (eqv : K → K → Bool) : List (DOp K V) → List (K × V) → List (K × V)
  | [], l => l
  | .set k v :: rest, l => absRun eqv rest (assocSet eqv l k v)
  | .del k :: rest, l => absRun eqv rest (assocDel eqv l k)

/-- `none` is `MemoryError`. -/
def conRun {K V : Type} [DecidableEq K] (P : Proto K (PyDict K V)) :
    List (DOp K V) → PyDict K V → Option (PyDict K V)
  | [], d => some d
  | .set k v :: rest, d =>
    match dictSetItem P k v d with
    | (.ok _, d') => conRun P rest d'
    | (.error _, _) => none
  | .del k :: rest, d => conRun P rest (dictDelItem P k d).2

/-- The model equals an association list, over every program of these operations. -/
def ModelEqualsAssoc : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (ops : List (DOp K V)) (d d' : PyDict K V), DictInv hf eqv P.isStr d →
      conRun P ops d = some d' → dictAssoc d' = absRun eqv ops (dictAssoc d)

/-- Deleting a missing key changes nothing, so a list filter is the right abstraction. -/
theorem assocDel_missing {K V : Type} (eqv : K → K → Bool) (l : List (K × V)) (key : K)
    (h : l.any (fun p => eqv p.1 key) = false) : assocDel eqv l key = l := by
  apply List.filter_eq_self.mpr
  intro p hp
  have := List.any_eq_false.mp h p hp
  simpa using this

theorem modelEqualsAssoc_proven : ModelEqualsAssoc := by
  intro K V _ P hf eqv H ops
  induction ops with
  | nil =>
    intro d d' _ h
    simp only [conRun, Option.some.injEq] at h
    subst h
    rfl
  | cons op rest ih =>
    intro d d' hd h
    cases op with
    | set k v =>
      simp only [conRun] at h
      rcases dictSetItem_spec H d hd k v with ⟨_, h1⟩ | ⟨d1, h1, h2, h3⟩
      · rw [h1] at h
        simp at h
      · rw [h1] at h
        simp only [absRun]
        rw [← h3]
        exact ih d1 d' h2 h
    | del k =>
      simp only [conRun] at h
      rcases dictDelItem_spec H d hd k with ⟨h1, h2⟩ | ⟨_, d1, h1, h2, h3⟩
      · rw [h2] at h
        simp only [absRun]
        rw [assocDel_missing eqv _ k h1]
        exact ih d d' hd h
      · rw [h1] at h
        simp only [absRun]
        rw [← h3]
        exact ih d1 d' h2 h

end PyLean.DictSet
