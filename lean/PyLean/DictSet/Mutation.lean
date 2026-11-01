import PyLean.DictSet.DictProps

/-!
The table invariant under a lying or mutating `__eq__`.

`_Py_dict_lookup` runs the user's `__eq__` (through `compare_generic` / `compare_unicode_generic`).
`__eq__` may return anything and may mutate the dict. The model threads the comparison's state, so
the lookup's only route to changing the table is that comparison. This file proves it: when `__eq__`
does not mutate (a *lying* comparison, returning arbitrary booleans but leaving the object alone),
`_Py_dict_lookup` leaves the table byte-identical, whatever it answers. Hence `Chain`, `WF` and
`DictInv` all survive a lying `__eq__`; the only invariant risk is a genuinely *mutating* one, which
is the `DKIX_KEY_CHANGED` path (`dictobject.c:1062`, `:1118`) the model already carries.
-/

namespace PyLean.DictSet

open PyLean

variable {K V : Type} [DecidableEq K]

/-- A comparison that does not mutate the object: `__eq__` may lie in its boolean, but leaves the
state it was given. `PyObject_RichCompareBool`'s own identity shortcut is of this kind. -/
def EqPure (P : Proto K (PyDict K V)) : Prop := ∀ a b mp, (P.eq a b mp).2 = mp

section Pure
variable {σ : Type}

/-- If `check` preserves the state, the whole probe loop does, at any fuel and offset. -/
theorem doLookup_pure (getIx : σ → Nat → Int) (check : Nat → M σ Int)
    (hc : ∀ ix s, (check ix s).2 = s) :
    ∀ (fuel mask i perturb : Nat) (s : σ), (doLookup getIx check fuel mask i perturb s).2 = s := by
  intro fuel
  induction fuel with
  | zero => intro mask i perturb s; rfl
  | succ fuel ih =>
    intro mask i perturb s
    simp only [doLookup]
    split
    · split
      · rename_i e s' heq
        have hs : s' = s := by have := hc (getIx s i).toNat s; rw [heq] at this; exact this
        subst hs; rfl
      · rename_i cmp s' heq
        have hs : s' = s := by have := hc (getIx s i).toNat s; rw [heq] at this; exact this
        subst hs
        split
        · rfl
        · split
          · rfl
          · exact ih _ _ _ _
    · split
      · rfl
      · exact ih _ _ _ _

end Pure

variable (P : Proto K (PyDict K V))

/-- `compare_generic` mutates only through `__eq__`. -/
theorem compareGeneric_pure (hp : EqPure P) (ix : Nat) (key : K) (hash : Int) (mp : PyDict K V) :
    (compareGeneric P ix key hash mp).2 = mp := by
  simp only [compareGeneric]
  rcases h : mp.body.entryKH ix with _ | ⟨epKey, epHash⟩
  · simp only [h]
  · simp only [h]
    split
    · rfl
    · split
      · split
        · rename_i e mp' heq
          have : mp' = mp := by have := hp epKey key mp; rw [heq] at this; exact this
          subst this; rfl
        · rename_i b mp' heq
          have : mp' = mp := by have := hp epKey key mp; rw [heq] at this; exact this
          subst this
          split <;> rfl
      · rfl

/-- `compare_unicode_generic` mutates only through `__eq__`. -/
theorem compareUnicodeGeneric_pure (hp : EqPure P) (ix : Nat) (key : K) (hash : Int)
    (mp : PyDict K V) : (compareUnicodeGeneric P ix key hash mp).2 = mp := by
  simp only [compareUnicodeGeneric]
  rcases h : mp.body.entryKH ix with _ | ⟨epKey, epHash⟩
  · simp only [h]
  · simp only [h]
    split
    · split
      · rename_i e mp' heq
        have : mp' = mp := by have := hp epKey key mp; rw [heq] at this; exact this
        subst this; rfl
      · rename_i b mp' heq
        have : mp' = mp := by have := hp epKey key mp; rw [heq] at this; exact this
        subst this
        split <;> rfl
    · rfl

/-- Every dispatch branch of the lookup's inner scan preserves the state. -/
theorem bigLookup_pure (hp : EqPure P) (key : K) (hash : Int) (mp : PyDict K V) :
    (if mp.body.kind != .general then
        if P.isStr key then
          doLookup bodyIx (checkUnicode P key hash) (probeFuel mp.body.log2Size) mp.body.mask
            (toU64 hash &&& mp.body.mask) (toU64 hash) mp
        else unicodekeysLookupGeneric P mp.body.mask (probeFuel mp.body.log2Size) key hash mp
      else dictkeysGenericLookup P mp.body.mask (probeFuel mp.body.log2Size) key hash mp).2 = mp := by
  split
  · split
    · exact doLookup_pure _ _ (fun ix s => rfl) _ _ _ _ mp
    · simp only [unicodekeysLookupGeneric]
      exact doLookup_pure _ _ (fun ix s => compareUnicodeGeneric_pure P hp ix key hash s) _ _ _ _ mp
  · simp only [dictkeysGenericLookup]
    exact doLookup_pure _ _ (fun ix s => compareGeneric_pure P hp ix key hash s) _ _ _ _ mp

/-- `_Py_dict_lookup` preserves the table when `__eq__` does not mutate, whatever it answers. -/
theorem dictLookupAux_pure (hp : EqPure P) (key : K) (hash : Int) :
    ∀ (n : Nat) (mp : PyDict K V), (dictLookupAux P key hash n mp).2 = mp := by
  intro n
  induction n with
  | zero => intro mp; rfl
  | succ n ih =>
    intro mp
    simp only [dictLookupAux]
    split
    · rename_i e mp' heq
      have : mp' = mp := by have := bigLookup_pure P hp key hash mp; rw [heq] at this; exact this
      subst this; rfl
    · rename_i ix mp' heq
      have : mp' = mp := by have := bigLookup_pure P hp key hash mp; rw [heq] at this; exact this
      subst this
      split
      · exact ih _
      · rfl

/-- `dictLookup` preserves the table when `__eq__` does not mutate. -/
theorem dictLookup_pure (hp : EqPure P) (key : K) (hash : Int) (mp : PyDict K V) :
    (dictLookup P key hash mp).2 = mp :=
  dictLookupAux_pure P hp key hash restartFuel mp

/-- The table invariant survives a lying (non-mutating) `__eq__`: after `_Py_dict_lookup` the dict
is byte-identical, so `DictInv` still holds, no matter what the comparison answered. -/
def InvUnderLyingEq : Prop :=
  ∀ (K V : Type) [DecidableEq K] (P : Proto K (PyDict K V)), EqPure P →
    ∀ (hf : K → Int) (eqv : K → K → Bool) (mp : PyDict K V), DictInv hf eqv P.isStr mp →
      ∀ (key : K) (hash : Int),
        (dictLookup P key hash mp).2 = mp ∧ DictInv hf eqv P.isStr (dictLookup P key hash mp).2

theorem invUnderLyingEq_proven : InvUnderLyingEq := by
  intro K V _ P hp hf eqv mp hd key hash
  have h := dictLookup_pure P hp key hash mp
  exact ⟨h, by rw [h]; exact hd⟩

end PyLean.DictSet
