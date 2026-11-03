import PyLean.Core

/-!
The pre-sort check of `list_sort_impl` (Objects/listobject.c:3027-3123, CPython 3.15.2): the scan of
the keys for type homogeneity and the choice of `ms.key_compare` and `ms.tuple_elem_compare`.

The check looks at a key only through its exact type (`Py_IS_TYPE`, by identity), whether a `str` is
of the 1-byte kind, whether an `int` is compact, whether the key is an exact non-empty tuple, and its
type's `tp_richcompare`. `KeyInfo` records exactly that. That each chosen compare answers as
`PyObject_RichCompareBool(v, w, Py_LT)` for its class is stated elsewhere: `unsafe_latin_compare` and
`unsafe_tuple_compare` in `bytesobj-sort-compare-agree`, `unsafe_long_compare` and
`unsafe_object_compare` over ints in `listsort-long-compare`, `unsafe_object_compare` in general in
`listsort-object-compare`; `unsafe_float_compare` is the C double `<` that `float_richcompare` uses.
-/

namespace PyLean.ListSort

/-- A key's exact type as the check tests it (`Py_TYPE(key)`, compared by identity): `str`, `int`,
`float`, `tuple`, or another type, identified by `id`, with whether its `tp_richcompare` is set. -/
inductive KeyTy where
  | str | int | float | tuple
  | other (id : Nat) (hasRich : Bool)
  deriving DecidableEq, Repr

/-- `key_type->tp_richcompare != NULL` (:3101): `str`, `int`, `float` and `tuple` all have one. -/
def KeyTy.hasRich : KeyTy → Bool
  | .other _ r => r
  | _ => true

/-- What the check reads of one object: its exact type; for a `str`, whether `PyUnicode_KIND` is
`PyUnicode_1BYTE_KIND` (:3077); for an `int`, `_PyLong_IsCompact` (:3071). -/
structure ElemInfo where
  ty : KeyTy
  latin : Bool := true
  compact : Bool := true
  deriving DecidableEq, Repr

/-- A key, and its first item when it is an exact non-empty tuple
(`Py_IS_TYPE(key, &PyTuple_Type) && Py_SIZE(key) > 0`, :3035-3036, :3050). -/
structure KeyInfo where
  self : ElemInfo
  first : Option ElemInfo := none
  deriving DecidableEq, Repr

/-- The compare functions the check can store in `ms.key_compare`; `tuple e` is
`unsafe_tuple_compare` with `ms.tuple_elem_compare = e`. -/
inductive KeyCmp where
  | latin | long | float | object | safe
  | tuple (elem : KeyCmp)
  deriving DecidableEq, Repr

/-- `keys_are_in_tuples`, `keys_are_all_same_type`, `strings_are_latin`, `ints_are_bounded`. -/
structure Scan where
  inTuples : Bool
  sameType : Bool
  latin : Bool
  bounded : Bool
  deriving DecidableEq, Repr

/-- The loop over the keys, listobject.c:3047-3085, with its two `break`s. -/
def scanKeys (keyType : KeyTy) : List KeyInfo → Scan → Scan
  | [], st => st
  | k :: ks, st =>
    if st.inTuples && k.first.isNone then { st with inTuples := false, sameType := false }
    else
      let key := if st.inTuples then k.first.getD k.self else k.self
      if key.ty ≠ keyType then
        if !st.inTuples then { st with sameType := false }
        else scanKeys keyType ks { st with sameType := false }
      else
        let st :=
          if st.sameType then
            if keyType = .int && st.bounded && !key.compact then { st with bounded := false }
            else if keyType = .str && st.latin && !key.latin then { st with latin := false }
            else st
          else st
        scanKeys keyType ks st

/-- The choice, listobject.c:3087-3122. -/
def chooseCompare (keyType : KeyTy) (st : Scan) : KeyCmp :=
  let kc :=
    if st.sameType then
      if keyType = .str && st.latin then .latin
      else if keyType = .int && st.bounded then .long
      else if keyType = .float then .float
      else if keyType.hasRich then .object
      else .safe
    else .safe
  if st.inTuples then .tuple (if keyType = .tuple then .safe else kc) else kc

/-- The pre-sort check, listobject.c:3033-3123: nothing for fewer than two keys (`saved_ob_size > 1`);
otherwise the first key is taken as representative (:3034-3040) and the scan starts from it. -/
def preSortCheck : List KeyInfo → Option KeyCmp
  | [] => none
  | [_] => none
  | k0 :: k1 :: ks =>
    let inT := k0.first.isSome
    let keyType := if inT then (k0.first.getD k0.self).ty else k0.self.ty
    some (chooseCompare keyType (scanKeys keyType (k0 :: k1 :: ks) ⟨inT, true, true, true⟩))

/-- The compare for keys that are not compared through tuples: a type-specific one when every key has
the exact type `t`, with every `str` of the 1-byte kind or every `int` compact, any `float`, or
`unsafe_object_compare` for any other type with a `tp_richcompare`; `safe_object_compare` otherwise. -/
def baseCompare (t : KeyTy) (xs : List ElemInfo) : KeyCmp :=
  if xs.all (fun x => x.ty = t) then
    if t = .str ∧ xs.all (·.latin) then .latin
    else if t = .int ∧ xs.all (·.compact) then .long
    else if t = .float then .float
    else if t.hasRich then .object
    else .safe
  else .safe

/-- The selection described without the loop: if the first key is an exact non-empty tuple, then
either every key is one and the compare is `unsafe_tuple_compare` with the element compare
`baseCompare` of the first items (`safe_object_compare` for tuples of tuples), or some key is not and
the compare is `safe_object_compare`; otherwise `baseCompare` of the keys. -/
def selectSpec (k0 : KeyInfo) (keys : List KeyInfo) : KeyCmp :=
  match k0.first with
  | some f0 =>
    if keys.all (fun k => k.first.isSome) then
      .tuple (if f0.ty = .tuple then .safe else baseCompare f0.ty (keys.map (fun k => k.first.getD k.self)))
    else .safe
  | none => baseCompare k0.self.ty (keys.map (·.self))

/-- `list.sort`'s pre-sort check (listobject.c:3033-3123) for every list of at least two keys, as
`selectSpec`: the loop's breaks and flags choose exactly the documented specialisation ("if the keys
are all the same type", listsort.txt and the comment at :3027-3032), with the first key's type as
the reference, the first items of tuples standing for the tuples, and `safe_object_compare` as soon
as the types differ or not every key is a non-empty tuple when the first one is. -/
def PreSortSelect : Prop :=
  ∀ (k0 k1 : KeyInfo) (ks : List KeyInfo),
    preSortCheck (k0 :: k1 :: ks) = some (selectSpec k0 (k0 :: k1 :: ks))

/-- One pass of the scan on a flat key of the reference type. -/
theorem scan_cons_flat (t : KeyTy) (k : KeyInfo) (ks : List KeyInfo) (l b : Bool) (hty : k.self.ty = t) :
    scanKeys t (k :: ks) ⟨false, true, l, b⟩ =
      scanKeys t ks ⟨false, true, if t = .str then l && k.self.latin else l,
        if t = .int then b && k.self.compact else b⟩ := by
  simp only [scanKeys, Bool.false_and, Bool.false_eq_true, if_false, hty, ne_eq, not_true_eq_false,
    if_true]
  cases t <;> cases l <;> cases b <;> cases k.self.latin <;> cases k.self.compact <;> simp

/-- A flat key of another type ends the scan (the `break` at :3065). -/
theorem scan_cons_flat_diff (t : KeyTy) (k : KeyInfo) (ks : List KeyInfo) (l b : Bool) (hty : ¬ k.self.ty = t) :
    scanKeys t (k :: ks) ⟨false, true, l, b⟩ = ⟨false, false, l, b⟩ := by
  simp [scanKeys, hty]

/-- A key that is not a non-empty tuple ends a tuple scan (the `break` at :3053). -/
theorem scan_cons_tup_none (t : KeyTy) (k : KeyInfo) (ks : List KeyInfo) (s l b : Bool) (hf : k.first = none) :
    scanKeys t (k :: ks) ⟨true, s, l, b⟩ = ⟨false, false, l, b⟩ := by
  simp [scanKeys, hf]

/-- A tuple whose first item has another type clears `keys_are_all_same_type` and the scan goes on
(:3063-3068). -/
theorem scan_cons_tup_diff (t : KeyTy) (k : KeyInfo) (ks : List KeyInfo) (s l b : Bool) (f : ElemInfo)
    (hf : k.first = some f) (hty : ¬ f.ty = t) :
    scanKeys t (k :: ks) ⟨true, s, l, b⟩ = scanKeys t ks ⟨true, false, l, b⟩ := by
  simp [scanKeys, hf, hty]

/-- A tuple whose first item has the reference type: the flags are updated while the types agree. -/
theorem scan_cons_tup (t : KeyTy) (k : KeyInfo) (ks : List KeyInfo) (s l b : Bool) (f : ElemInfo)
    (hf : k.first = some f) (hty : f.ty = t) :
    scanKeys t (k :: ks) ⟨true, s, l, b⟩ =
      scanKeys t ks ⟨true, s, if s && t = .str then l && f.latin else l,
        if s && t = .int then b && f.compact else b⟩ := by
  simp only [scanKeys, hf, Option.isNone_some, Bool.and_false, Bool.false_eq_true, if_false, if_true,
    Option.getD_some, hty, ne_eq, not_true_eq_false]
  cases t <;> cases s <;> cases l <;> cases b <;> cases f.latin <;> cases f.compact <;> simp

/-- The scan when the keys are not in tuples. -/
theorem scan_flat (t : KeyTy) : ∀ (ks : List KeyInfo) (l b : Bool),
    (scanKeys t ks ⟨false, true, l, b⟩).inTuples = false ∧
    (scanKeys t ks ⟨false, true, l, b⟩).sameType = ks.all (fun k => k.self.ty = t) ∧
    (ks.all (fun k => k.self.ty = t) = true →
      (scanKeys t ks ⟨false, true, l, b⟩).latin = (if t = .str then l && ks.all (·.self.latin) else l) ∧
      (scanKeys t ks ⟨false, true, l, b⟩).bounded = (if t = .int then b && ks.all (·.self.compact) else b))
  | [], l, b => by simp [scanKeys]
  | k :: ks, l, b => by
    by_cases hty : k.self.ty = t
    · rw [scan_cons_flat t k ks l b hty]
      obtain ⟨a1, a2, a3⟩ := scan_flat t ks (if t = .str then l && k.self.latin else l)
        (if t = .int then b && k.self.compact else b)
      refine ⟨a1, by rw [a2]; simp [hty], fun hall => ?_⟩
      have hall' : ks.all (fun k => decide (k.self.ty = t)) = true := by
        simp only [List.all_cons, Bool.and_eq_true] at hall; exact hall.2
      obtain ⟨b1, b2⟩ := a3 hall'
      rw [b1, b2]
      cases t <;> simp [List.all_cons, Bool.and_assoc]
    · rw [scan_cons_flat_diff t k ks l b hty]
      simp [hty]

/-- The scan when the keys are in tuples, from any flags. -/
theorem scan_tup (t : KeyTy) : ∀ (ks : List KeyInfo) (s l b : Bool),
    (scanKeys t ks ⟨true, s, l, b⟩).inTuples = ks.all (fun k => k.first.isSome) ∧
    (ks.all (fun k => k.first.isSome) = false → (scanKeys t ks ⟨true, s, l, b⟩).sameType = false) ∧
    (ks.all (fun k => k.first.isSome) = true →
      (scanKeys t ks ⟨true, s, l, b⟩).sameType = (s && ks.all (fun k => (k.first.getD k.self).ty = t)) ∧
      ((scanKeys t ks ⟨true, s, l, b⟩).sameType = true →
        (scanKeys t ks ⟨true, s, l, b⟩).latin =
          (if t = .str then l && ks.all (fun k => (k.first.getD k.self).latin) else l) ∧
        (scanKeys t ks ⟨true, s, l, b⟩).bounded =
          (if t = .int then b && ks.all (fun k => (k.first.getD k.self).compact) else b)))
  | [], s, l, b => by simp [scanKeys]
  | k :: ks, s, l, b => by
    rcases hf : k.first with _ | f
    · rw [scan_cons_tup_none t k ks s l b hf]
      simp [hf]
    · by_cases hty : f.ty = t
      · rw [scan_cons_tup t k ks s l b f hf hty]
        obtain ⟨a1, a2, a3⟩ := scan_tup t ks s (if s && t = .str then l && f.latin else l)
          (if s && t = .int then b && f.compact else b)
        refine ⟨by rw [a1]; simp [hf], fun h => a2 (by simpa [hf] using h), fun hall => ?_⟩
        have hall' : ks.all (fun k => k.first.isSome) = true := by simpa [hf] using hall
        obtain ⟨b1, b2⟩ := a3 hall'
        refine ⟨by rw [b1]; simp [hf, hty], fun hs => ?_⟩
        obtain ⟨c1, c2⟩ := b2 hs
        rw [b1] at hs
        have hs' : s = true := by simp only [Bool.and_eq_true] at hs; exact hs.1
        subst hs'
        rw [c1, c2]
        cases t <;> simp [hf, List.all_cons, Bool.and_assoc]
      · rw [scan_cons_tup_diff t k ks s l b f hf hty]
        obtain ⟨a1, a2, a3⟩ := scan_tup t ks false l b
        refine ⟨by rw [a1]; simp [hf], fun h => a2 (by simpa [hf] using h), fun hall => ?_⟩
        have hall' : ks.all (fun k => k.first.isSome) = true := by simpa [hf] using hall
        obtain ⟨b1, b2⟩ := a3 hall'
        refine ⟨by rw [b1]; simp [hf, hty], fun hs => ?_⟩
        rw [b1] at hs
        simp at hs

theorem preSortSelect_proven : PreSortSelect := by
  intro k0 k1 ks
  unfold preSortCheck selectSpec
  rcases hf : k0.first with _ | f0
  · simp only [hf, Option.isSome_none, Bool.false_eq_true, if_false]
    obtain ⟨h1, h2, h3⟩ := scan_flat k0.self.ty (k0 :: k1 :: ks) true true
    generalize scanKeys k0.self.ty (k0 :: k1 :: ks) ⟨false, true, true, true⟩ = R at h1 h2 h3 ⊢
    unfold chooseCompare baseCompare
    rw [h1, h2]
    simp only [List.all_map, Function.comp_def, Bool.false_eq_true, if_false]
    by_cases hall : (k0 :: k1 :: ks).all (fun k => decide (k.self.ty = k0.self.ty)) = true
    · obtain ⟨h4, h5⟩ := h3 hall
      rw [h4, h5, if_pos hall, if_pos hall]
      generalize k0.self.ty = t
      cases t <;> simp
    · rw [Bool.not_eq_true] at hall
      simp [hall]
  · simp only [hf, Option.isSome_some, if_true, Option.getD_some]
    obtain ⟨h1, h2, h3⟩ := scan_tup f0.ty (k0 :: k1 :: ks) true true true
    generalize scanKeys f0.ty (k0 :: k1 :: ks) ⟨true, true, true, true⟩ = R at h1 h2 h3 ⊢
    unfold chooseCompare
    rw [h1]
    by_cases hall : (k0 :: k1 :: ks).all (fun k => k.first.isSome) = true
    · rw [if_pos hall, if_pos hall]
      obtain ⟨h4, h5⟩ := h3 hall
      by_cases hft : f0.ty = .tuple
      · rw [if_pos hft, if_pos hft]
      · rw [if_neg hft, if_neg hft]
        unfold baseCompare
        rw [h4]
        simp only [Bool.true_and, List.all_map, Function.comp_def]
        by_cases hsame : (k0 :: k1 :: ks).all (fun k => decide ((k.first.getD k.self).ty = f0.ty)) = true
        · obtain ⟨h6, h7⟩ := h5 (by rw [h4, hsame]; rfl)
          rw [h6, h7, if_pos hsame, if_pos hsame]
          revert hft
          generalize f0.ty = t
          intro hft
          cases t <;> simp at hft ⊢
        · rw [Bool.not_eq_true] at hsame
          simp [hsame]
    · rw [Bool.not_eq_true] at hall
      rw [hall]
      simp only [Bool.false_eq_true, if_false]
      rw [h2 hall]
      simp

end PyLean.ListSort
