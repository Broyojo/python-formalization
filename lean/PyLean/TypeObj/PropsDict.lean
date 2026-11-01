import PyLean.TypeObj.Call

/-!
Properties of the dict lookup, `_Py_dict_lookup` through `compare_generic`,
`Objects/dictobject.c:1102`, modelled by `dictProbe`. They quantify over every `Rt`, so over
every `__eq__` and `__hash__`, and over every dict.
-/

namespace PyLean.TypeObj

/-- **A different hash never runs `__eq__`.** When no entry from `i` on is the key or shares its
hash, the lookup answers "absent" and leaves the world exactly as it was, whatever `Rt` does: no
comparison ran. The fuel hypothesis says the loop may visit every remaining entry, which is the
model's bound and not a property of the dict. -/
def DictProbeSkipsOtherHashes : Prop :=
  ∀ (rt : Rt) (a : Addr) (key : Val) (h : Int) (w : World) (fuel i : Nat),
    (dictEntries w a).length - i < fuel →
    (∀ (j : Nat) (k v : Val), i ≤ j → (dictEntries w a)[j]? = some (k, v) →
      k.is key = false ∧ storedHash w a k ≠ h) →
    dictProbe rt a key h fuel i w = .ok none w

theorem dictProbeSkipsOtherHashes_proven : DictProbeSkipsOtherHashes := by
  intro rt a key h w fuel
  induction fuel with
  | zero => intro i h1; omega
  | succ fuel ih =>
    intro i h1 hall
    rw [dictProbe]
    simp only [M.bind_app, getW_app]
    cases he : (dictEntries w a)[i]? with
    | none => simp
    | some e =>
      obtain ⟨k, v⟩ := e
      obtain ⟨h2, h3⟩ := hall i k v (Nat.le_refl i) he
      have hlt : i < (dictEntries w a).length := by
        rcases List.getElem?_eq_some_iff.mp he with ⟨hi, _⟩
        exact hi
      have h4 : (dictEntries w a).length - (i + 1) < fuel := by omega
      have h5 : ∀ (j : Nat) (k v : Val), i + 1 ≤ j → (dictEntries w a)[j]? = some (k, v) →
          k.is key = false ∧ storedHash w a k ≠ h := fun j k v hj hg =>
        hall j k v (by omega) hg
      simp [h2, h3, ih (i + 1) h4 h5]

/-- **A key object already present is found without running Python code.** If the entry at `i` is
the key itself, and no entry between `s` and `i` is the key or shares its hash, the lookup gives
`i` and leaves the world as it was, for every `Rt`: the identity test comes before any `__eq__`. -/
def DictProbeFindsIdentical : Prop :=
  ∀ (rt : Rt) (a : Addr) (key : Val) (h : Int) (w : World) (fuel s i : Nat) (k v : Val),
    s ≤ i → i - s < fuel → (dictEntries w a)[i]? = some (k, v) → k.is key = true →
    (∀ (j : Nat) (k' v' : Val), s ≤ j → j < i → (dictEntries w a)[j]? = some (k', v') →
      k'.is key = false ∧ storedHash w a k' ≠ h) →
    dictProbe rt a key h fuel s w = .ok (some i) w

theorem dictProbeFindsIdentical_proven : DictProbeFindsIdentical := by
  intro rt a key h w fuel
  induction fuel with
  | zero => intro s i k v _ h1; omega
  | succ fuel ih =>
    intro s i k v h0 h1 hi hk hall
    rw [dictProbe]
    simp only [M.bind_app, getW_app]
    by_cases hs : s = i
    · subst hs
      simp [hi, hk]
    · have hlt : s < i := by omega
      cases he : (dictEntries w a)[s]? with
      | none =>
        have : s < (dictEntries w a).length := by
          rcases List.getElem?_eq_some_iff.mp hi with ⟨hi', _⟩
          omega
        rw [List.getElem?_eq_getElem this] at he
        simp at he
      | some e =>
        obtain ⟨k', v'⟩ := e
        obtain ⟨h2, h3⟩ := hall s k' v' (Nat.le_refl s) hlt he
        have h4 : i - (s + 1) < fuel := by omega
        have h5 : ∀ (j : Nat) (k' v' : Val), s + 1 ≤ j → j < i →
            (dictEntries w a)[j]? = some (k', v') →
            k'.is key = false ∧ storedHash w a k' ≠ h := fun j k' v' hj hji hg =>
          hall j k' v' (by omega) hji hg
        simp [h2, h3, ih (s + 1) i k v (by omega) h4 hi hk h5]

end PyLean.TypeObj
