import PyLean.DictSet.Reentrant
import PyLean.DictSet.Failure

/-!
Whole bodies, stated so that a wrong version of the function fails.

Each statement here says what the function does on every branch, not only on the ones a refinement
theorem reaches, and each holds for every key protocol unless it says otherwise.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- `do_lookup`, one turn of the loop at any position: a check that raises ends the search; a
negative answer is returned as it stands, which is how `DKIX_KEY_CHANGED` leaves; a positive answer
returns the index; zero goes on from the next slot; an empty slot ends the search, and a dummy
goes on. -/
def DoLookupBody : Prop :=
  ∀ (σ : Type) (getIx : σ → Nat → Int) (check : Nat → M σ Int) (fuel mask i p : Nat) (s : σ),
    let ix := getIx s i
    let n := probeStep mask i p
    let R := doLookup getIx check (fuel + 1) mask i p s
    (0 ≤ ix →
      (∀ e s', check ix.toNat s = (.error e, s') → R = (.error e, s')) ∧
      (∀ c s', check ix.toNat s = (.ok c, s') → c < 0 → R = (.ok c, s')) ∧
      (∀ c s', check ix.toNat s = (.ok c, s') → 0 < c → R = (.ok ix, s')) ∧
      (∀ s', check ix.toNat s = (.ok 0, s') → R = doLookup getIx check fuel mask n.1 n.2 s')) ∧
    (ix = DKIX_EMPTY → R = (.ok DKIX_EMPTY, s)) ∧
    (ix < 0 → ix ≠ DKIX_EMPTY → R = doLookup getIx check fuel mask n.1 n.2 s)
theorem doLookupBody_proven : DoLookupBody := by
  intro σ getIx check fuel mask i p s ix n R
  refine ⟨fun h0 => ⟨fun e s' h => ?_, fun c s' h hc => ?_, fun c s' h hc => ?_, fun s' h => ?_⟩,
    fun h => ?_, fun h1 h2 => ?_⟩
  · simp only [R, doLookup]
    rw [if_pos h0, h]
  · simp only [R, doLookup]
    rw [if_pos h0, h]
    simp [hc]
  · simp only [R, doLookup]
    rw [if_pos h0, h]
    have h1 : ¬ c < 0 := by omega
    have h2 : (c != 0) = true := by
      simp only [bne_iff_ne]
      omega
    simp [h1, h2]
    rfl
  · simp only [R, doLookup]
    rw [if_pos h0, h]
    simp
    rfl
  · have h0 : ¬ getIx s i ≥ 0 := by
      show ¬ ix ≥ 0
      rw [h]
      decide
    have h3 : (getIx s i == DKIX_EMPTY) = true := by
      show (ix == DKIX_EMPTY) = true
      rw [h]
      decide
    simp only [R, doLookup]
    rw [if_neg h0, if_pos h3]
  · have h0 : ¬ getIx s i ≥ 0 := by
      show ¬ ix ≥ 0
      omega
    have h3 : ¬ (getIx s i == DKIX_EMPTY) = true := by
      show ¬ (ix == DKIX_EMPTY) = true
      simpa using h2
    simp only [R, doLookup]
    rw [if_neg h0, if_neg h3]

/-- `_Py_bit_length` is no more than it has to be. -/
theorem bitLength_le (n : Nat) (h : n ≠ 0) : 2 ^ (bitLength n - 1) ≤ n := by
  unfold bitLength
  rw [if_neg (by simpa using h)]
  simpa using Nat.log2_self_le h

/-- `calculate_log2_keysize` picks the smallest table of at least 8 slots with room for `minsize`. -/
def KeysizeSmallest : Prop :=
  ∀ m : Nat, let r := calculateLog2Keysize m
    3 ≤ r ∧ max m 8 ≤ 2 ^ r ∧ 2 ^ (r - 1) < max m 8
theorem keysizeSmallest_proven : KeysizeSmallest := by
  intro m r
  have h1 : max m 8 ≤ 2 ^ r := by
    have := calculateLog2_room m
    simpa [r] using this
  have h2 : 2 ^ (r - 1) < max m 8 := by
    have e : r = bitLength (max m 8 - 1) := rfl
    have := bitLength_le (max m 8 - 1) (by omega)
    rw [← e] at this
    omega
  refine ⟨?_, h1, h2⟩
  by_cases h : 3 ≤ r
  · exact h
  · exfalso
    have : 2 ^ r ≤ 2 ^ 2 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- `estimate_log2_keysize` is the reverse of `USABLE_FRACTION` (:568-572): the smallest table of at
least 8 slots whose usable fraction holds `n` entries. -/
def EstimateSmallest : Prop :=
  ∀ n : Nat, let r := estimateLog2Keysize n
    r = calculateLog2Keysize ((n * 3 + 1) / 2) ∧ 3 ≤ r ∧ n ≤ usableFraction (2 ^ r) ∧
      (3 < r → usableFraction (2 ^ (r - 1)) < n)
theorem estimateSmallest_proven : EstimateSmallest := by
  intro n r
  obtain ⟨h1, h2, h3⟩ := keysizeSmallest_proven ((n * 3 + 1) / 2)
  have e : calculateLog2Keysize ((n * 3 + 1) / 2) = r := rfl
  rw [e] at h1 h2 h3
  refine ⟨rfl, h1, ?_, ?_⟩
  · simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one]
    omega
  · intro hr
    have h8 : 2 ^ 3 ≤ 2 ^ (r - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    simp only [usableFraction, Nat.shiftLeft_eq, Nat.pow_one]
    have : (2 : Nat) ^ 3 = 8 := rfl
    omega

/-- `dict_getitem`, with what it reports: not a dict is silent; a failed hash and a failed lookup go
to `sys.unraisablehook`, a `KeyError` from the lookup being dropped silently; and a good lookup gives
its value. -/
def DictGetitemBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (d s : PyDict K V) (e : PyExc)
    (h : Int) (r : Int × Option V) (m : String),
    dictGetitemFull P false key d = (.ok (none, none), d) ∧
    (P.hash key = .error e → dictGetitemFull P true key d = (.ok (none, some e), d)) ∧
    (P.hash key = .ok h →
      (dictLookup P key h d = (.ok r, s) → dictGetitemFull P true key d = (.ok (r.2, none), s)) ∧
      (dictLookup P key h d = (.error (.keyError m), s) →
        dictGetitemFull P true key d = (.ok (none, none), s)) ∧
      ((∀ m', e ≠ .keyError m') → dictLookup P key h d = (.error e, s) →
        dictGetitemFull P true key d = (.ok (none, some e), s)))
theorem dictGetitemBody_proven : DictGetitemBody := by
  intro K V _ P key d s e h r m
  refine ⟨rfl, fun hh => ?_, fun hh => ⟨fun hl => ?_, fun hl => ?_, fun hn hl => ?_⟩⟩
  · simp [dictGetitemFull, hh]
  · simp [dictGetitemFull, hh, hl]
  · simp [dictGetitemFull, hh, hl]
  · cases e with
    | keyError m' => exact absurd rfl (hn m')
    | _ => simp [dictGetitemFull, hh, hl]

/-- `dictGetitemFull` is `dictGetitemSuppress`, which the difftest and the older theorems use, with the
report added: the value and the state are the same. -/
def GetitemLink : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (isDict : Bool) (key : K) (d : PyDict K V),
    (dictGetitemFull P isDict key d).2 = (dictGetitemSuppress P isDict key d).2 ∧
    (dictGetitemFull P isDict key d).1.map Prod.fst = (dictGetitemSuppress P isDict key d).1
theorem getitemLink_proven : GetitemLink := by
  intro K V _ P isDict key d
  cases isDict with
  | false => exact ⟨rfl, rfl⟩
  | true =>
    cases hh : P.hash key with
    | error e => simp [dictGetitemFull, dictGetitemSuppress, hh, Except.map]
    | ok h =>
      cases hl : dictLookup P key h d with
      | mk r s =>
        cases r with
        | error e =>
          cases e <;>
            simp [dictGetitemFull, dictGetitemSuppress, hh, hl, M.tryCatch, M.bind_run, Except.map]
        | ok x =>
          simp [dictGetitemFull, dictGetitemSuppress, hh, hl, M.tryCatch, M.bind_run, Except.map]

/-- `_PyDict_DelItem_KnownHash_LockHeld` after its check, for every key protocol: a failed lookup is
the result, in the state it left (:2864-2865); no slot, or a slot with no value, is `KeyError`
(:2866-2869); and a value goes to `delitem_common` on that state (:2873). -/
def DelKnownHashBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (hash : Int)
    (d s : PyDict K V) (e : PyExc) (ix : Int) (old : Option V),
    (dictLookup P key hash d = (.error e, s) → dictDelItemKnownHash P key hash d = (.error e, s)) ∧
    (dictLookup P key hash d = (.ok (ix, old), s) → (ix = DKIX_EMPTY ∨ old = none) →
      dictDelItemKnownHash P key hash d = (.error (keyErr P key), s)) ∧
    (∀ v, dictLookup P key hash d = (.ok (ix, some v), s) → ix ≠ DKIX_EMPTY →
      dictDelItemKnownHash P key hash d = delitemCommon hash ix.toNat s)
theorem delKnownHashBody_proven : DelKnownHashBody := by
  intro K V _ P key hash d s e ix old
  refine ⟨fun h => ?_, fun h hc => ?_, fun v h hne => ?_⟩
  · simp [dictDelItemKnownHash, h]
  · rcases hc with rfl | rfl
    · cases old <;> simp [dictDelItemKnownHash, h]
    · simp [dictDelItemKnownHash, h]
  · have e1 : (ix == DKIX_EMPTY) = false := by simpa using hne
    simp [dictDelItemKnownHash, h, e1]

/-- `dict_subscript` on every branch, for any `__missing__`: a good slot gives its value, whatever
`missing` is; and with no value, an exact dict raises `KeyError`, while a subclass runs the special
lookup, whose failure is the result, and calls what it finds on the state it left, which either may
have changed. With nothing found the result is `KeyError`. -/
def SubscriptBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (h : Int)
    (mp s s' : PyDict K V) (ix : Int) (old : Option V)
    (look : DM K V (Option (K → DM K V V))) (missing : Option (DM K V (Option (K → DM K V V)))),
    P.hash key = .ok h → dictLookup P key h mp = (.ok (ix, old), s) →
    (∀ v, old = some v → ix ≠ DKIX_EMPTY → dictSubscript P missing key mp = (.ok v, s)) ∧
    ((old = none ∨ ix = DKIX_EMPTY) →
      dictSubscript P none key mp = (.error (keyErr P key), s) ∧
      (∀ e, look s = (.error e, s') → dictSubscript P (some look) key mp = (.error e, s')) ∧
      (look s = (.ok none, s') →
        dictSubscript P (some look) key mp = (.error (keyErr P key), s')) ∧
      (∀ f, look s = (.ok (some f), s') → dictSubscript P (some look) key mp = f key s'))
theorem subscriptBody_proven : SubscriptBody := by
  intro K V _ P key h mp s s' ix old look missing hh hl
  have hk : ∀ {β : Type} (f : Int → DM K V β), (hashKey P key >>= f) mp = f h mp := by
    intro β f
    simp [hashKey, hh, M.bind_run]
  have hs : ∀ m, dictSubscript P m key mp =
      (match old with
       | some v => if ix == DKIX_EMPTY then subscriptMissing P m key else pure v
       | none => subscriptMissing P m key) s := by
    intro m
    simp only [dictSubscript]
    rw [hk, M.bind_run, hl]
    cases old <;> rfl
  refine ⟨fun v hv hne => ?_, fun hc => ⟨?_, fun e he => ?_, fun he => ?_, fun f he => ?_⟩⟩
  · have e1 : (ix == DKIX_EMPTY) = false := by simpa using hne
    rw [hs]
    simp [hv, e1]
  all_goals
    rw [hs]
    have hm : ∀ m : Option (DM K V (Option (K → DM K V V))),
        (match old with
         | some v => if ix == DKIX_EMPTY then subscriptMissing P m key else pure v
         | none => subscriptMissing P m key) = subscriptMissing P m key := by
      intro m
      rcases hc with rfl | rfl
      · rfl
      · cases old with
        | none => rfl
        | some v => simp
    rw [hm]
  · rfl
  · simp [subscriptMissing, M.bind_run, he]
  · simp [subscriptMissing, M.bind_run, he]
  · simp [subscriptMissing, M.bind_run, he]

/-- The `PyDict_Check` of `_PyDict_DelItem_KnownHash_LockHeld`, `clear_lock_held` and
`dict_setdefault_ref_lock_held`: something that is not a dict gets a `SystemError` from the first
and last, and nothing at all from the second, and a dict goes on to the body. -/
def DictChecks : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (hash : Int) (dflt : V)
    (r i : Bool) (d : PyDict K V),
    dictDelItemKnownHashChecked P false key hash d = (.error badInternalCall, d) ∧
    dictDelItemKnownHashChecked P true key hash d = dictDelItemKnownHash P key hash d ∧
    dictClearChecked false d = d ∧ dictClearChecked true d = dictClear d ∧
    dictSetdefaultRefChecked P false key dflt r i d = (.error badInternalCall, d) ∧
    dictSetdefaultRefChecked P true key dflt r i d = dictSetdefaultRef P key dflt r i d
theorem dictChecks_proven : DictChecks := by
  intro K V _ P key hash dflt r i d
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- What `dictresize` makes of the flag it is given (:2082-2084, :2093). -/
theorem dictResize_kind {mp s : PyDict K V} {l : Nat} {u : Bool} {k' : Keys K V}
    (h : dictResize l u mp = (.ok (), s)) (hs : s.body = .combined k') :
    k'.kind = if (if mp.body.isUnicode then u else false) then .unicode else .general := by
  unfold dictResize at h
  split at h
  · simp at h
  · simp only at h
    split at h
    · simp at h
    · have h1 := congrArg Prod.snd h
      simp only at h1
      rw [← h1] at hs
      simp only [Body.combined.injEq] at hs
      rw [← hs]
      cases hu : (if mp.body.isUnicode then u else false) <;> simp [newKeysObject, hu]

/-- `dictresize` on every route, for any table in either form: a size of 64 bits or more is refused;
otherwise every live entry moves over in order and the index table finds them again, which is
`build_indices_generic` on a general table and `build_indices_unicode` otherwise; and the new table is
unicode exactly when the old one was and the caller allows it. -/
def DictResizeRefines : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (hf : K → Int) (eqv : K → K → Bool),
    Honest P hf eqv → ∀ (mp : PyDict K V) (log2New : Nat) (unicode : Bool),
    (64 ≤ log2New → dictResize log2New unicode mp = (.error memoryError, mp)) ∧
    (log2New < 64 → mp.used ≤ usableFraction (2 ^ log2New) →
      let isU := if mp.body.isUnicode then unicode else false
      let kindOk := fun k' : Keys K V =>
        k'.kind = if isU then .unicode else .general
      (∀ k, mp.body = .combined k → WF hf eqv P.isStr k → mp.used = (liveEntries k).length →
        ∃ k' : Keys K V, dictResize log2New unicode mp =
            (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
          WF hf eqv P.isStr k' ∧ liveEntries k' = liveEntries k ∧ k'.log2Size = log2New ∧
          k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used ∧ kindOk k') ∧
      (∀ k v, mp.body = .split k v → SplitWF hf eqv P.isStr k v mp.used →
        ∃ k' : Keys K V, dictResize log2New unicode mp =
            (.ok (), { mp with nextId := mp.nextId + 1, body := .combined k' }) ∧
          WF hf eqv P.isStr k' ∧ liveEntries k' = live k v ∧ k'.log2Size = log2New ∧
          k'.usable = (usableFraction (2 ^ log2New) : Int) - mp.used ∧ kindOk k'))
theorem dictResizeRefines_proven : DictResizeRefines := by
  intro K V _ P hf eqv H mp log2New unicode
  constructor
  · intro h
    simp [dictResize, h]
  intro hlt hroom isU kindOk
  refine ⟨fun k hb w hu => ?_, fun k v hb w => ?_⟩
  · obtain ⟨k', h1, h2, h3, h4, h5, _, _⟩ := dictResize_spec H mp k hb w hu log2New hlt hroom unicode
    exact ⟨k', h1, h2, h3, h4, h5, dictResize_kind h1 rfl⟩
  · obtain ⟨k', h1, h2, h3, h4, h5, _⟩ := dictResize_split H mp k v hb w log2New hlt hroom unicode
    exact ⟨k', h1, h2, h3, h4, h5, dictResize_kind h1 rfl⟩

/-- `dictresize` leaving the split form of an instance's dict, `:2138-2142`: the inline values are
invalidated and emptied, in the same number of slots, and the dict is the one that now answers. -/
def ResizeInvalidatesInline : Prop :=
  ∀ (K V : Type) (d : PyDict K V) (k : Keys K V) (s : ObjSt K V), d.body = .combined k →
    let i := (syncDict true d s).inst
    i.dict = some d ∧ i.inlineV.valid = false ∧ i.inlineV.order = [] ∧
      i.inlineV.capacity = s.inst.inlineV.capacity ∧ ∀ ix, i.inlineV.get ix = none
theorem resizeInvalidatesInline_proven : ResizeInvalidatesInline := by
  intro K V d k s hb i
  have hi : i = { s.inst with dict := some d, inlineV := invalidateInline s.inst.inlineV } := by
    simp [i, syncDict, hb]
  refine ⟨by rw [hi], by rw [hi]; rfl, by rw [hi]; rfl, ?_, fun ix => ?_⟩
  · rw [hi]
    simp [Values.capacity, invalidateInline]
  · rw [hi]
    simp only [Values.get, invalidateInline, List.getElem?_map]
    cases s.inst.inlineV.values[ix]? <;> rfl

/-- `dict_dealloc`: a watcher that kept a reference gets the dict as it left it, not cleared; with
no such watcher the dict is gone. -/
def DictDeallocBody : Prop :=
  ∀ (K V : Type) (watch : PyDict K V → Bool × PyDict K V) (mp s : PyDict K V),
    (watch mp = (true, s) → dictDealloc watch mp = some s) ∧
    (watch mp = (false, s) → dictDealloc watch mp = none)
theorem dictDeallocBody_proven : DictDeallocBody := by
  intro K V watch mp s
  exact ⟨fun h => by simp [dictDealloc, h], fun h => by simp [dictDealloc, h]⟩

end PyLean.DictSet
