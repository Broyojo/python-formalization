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

/-- `PyDict_Pop`, `dict.pop` and `PyDict_PopString`, branch by branch, for every key protocol. An
empty dict answers before the key is hashed; a failed hash goes through `dict_unhashable_type`; a
failed lookup is the result in the state `__eq__` left; a slot with no value (a key of the shared
keys this split dict has no value for) is a miss, and nothing is deleted or read through it; a
value is deleted by `delitem_common` on the state the lookup left. `dict.pop` turns a miss into
the default or `KeyError(key)`. -/
def PopBody : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)) (key : K) (d : PyDict K V),
    d.frozen = false →
    (d.used = 0 → pyDictPop P true key d = (.ok none, d)) ∧
    (d.used ≠ 0 → ∀ e, P.hash key = .error e →
      pyDictPop P true key d = (.error (dictUnhashableType P d.frozen key e), d)) ∧
    (d.used ≠ 0 → ∀ h, P.hash key = .ok h →
      (∀ e s, dictLookup P key h d = (.error e, s) → pyDictPop P true key d = (.error e, s)) ∧
      (∀ ix s, dictLookup P key h d = (.ok (ix, none), s) → pyDictPop P true key d = (.ok none, s)) ∧
      (∀ v s, dictLookup P key h d = (.ok (DKIX_EMPTY, some v), s) →
        pyDictPop P true key d = (.ok none, s)) ∧
      (∀ ix v s, ix ≠ DKIX_EMPTY → dictLookup P key h d = (.ok (ix, some v), s) →
        pyDictPop P true key d =
          match delitemCommon h ix.toNat s with
          | (.ok _, s') => (.ok (some v), s')
          | (.error e, s') => (.error e, s'))) ∧
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
  intro K V _ P key d hfz
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
  refine ⟨fun h0 => ?_, fun h0 e he => ?_, fun h0 h hh => ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, rfl⟩
  · simp [pyDictPop, hfz, h0]
  · simp [pyDictPop, hfz, h0, he]
  · intro e s hl
    simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl]
  · intro ix s hl
    simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl]
  · intro v s hl
    simp [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl]
  · intro ix v s hix hl
    have hne : (ix == DKIX_EMPTY) = false := by simpa using hix
    simp only [pyDictPop, hfz, h0, hh, dictPopKnownHash, hl, hne, Bool.not_true, Bool.false_eq_true,
      if_false, beq_iff_eq, Bool.false_eq_true]
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

end PyLean.DictSet

