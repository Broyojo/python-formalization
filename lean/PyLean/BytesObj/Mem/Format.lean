import PyLean.BytesObj.Mem.Lemmas

/-!
Properties of the format handling: `get_native_fmtchar`, `get_native_fmtstr`,
`adjust_fmt`, `equiv_format`, and the two casts.
-/

namespace PyLean.BytesObj.Mem

open PyLean

theorem fmtSize_pos_iff (c : Char) : fmtSize c > 0 ↔ nativeChar c = true := by
  unfold fmtSize nativeChar
  split <;> simp_all <;> omega

theorem nativeChar_nul : nativeChar '\x00' = false := by decide

/-- The text of a format code: one character, or the two of `Zf` and `Zd`. -/
def codeText (c : Char) : List Char :=
  if c = zfCode then ['Z', 'f'] else if c = zdCode then ['Z', 'd'] else [c]

/-- The size of a format code in `struct`'s native table. -/
def codeSize (c : Char) : Option Nat :=
  if c = zfCode then some 8 else if c = zdCode then some 16 else nativeSize c

/-- The two tables of the source agree: for every string, `get_native_fmtchar` accepts it
exactly when `get_native_fmtstr` does, and the string `get_native_fmtstr` returns is
`[@]` and the format `get_native_fmtchar` returns, one character or `Zf` or `Zd`, whose size is the
size of that entry in `struct`'s native table. Source: the NOT_REACHED comment at
memoryobject.c:1345. -/
def NativeFormatAgree : Prop :=
  ∀ fmt : List Char,
    (getNativeFmtchar fmt).isSome = (getNativeFmtstr fmt).isSome ∧
    ∀ c size, getNativeFmtchar fmt = some (c, size) →
      stripAt ((getNativeFmtstr fmt).getD []) = codeText c ∧ 0 < size ∧
      codeSize c = some size.toNat

theorem nativeSize_of (c : Char) (h : nativeChar c = true) :
    nativeSize c = some (fmtSize c).toNat := by
  unfold nativeChar at h
  unfold nativeSize fmtSize
  split at h <;> first | rfl | simp_all

theorem nativeChar_code (c : Char) (h : nativeChar c = true) : c ≠ zfCode ∧ c ≠ zdCode := by
  constructor
  · rintro rfl
    exact absurd h (by decide)
  · rintro rfl
    exact absurd h (by decide)

theorem native_agree_core (f : List Char) (mk : List Char → List Char)
    (hm : ∀ l, cc l 0 = cc f 0 → stripAt (mk l) = l) :
    let A : Option (Char × Int) :=
      if cc f 0 = 'Z' then
        if cc f 1 = 'f' ∧ cc f 2 = '\x00' then some (zfCode, 8)
        else if cc f 1 = 'd' ∧ cc f 2 = '\x00' then some (zdCode, 16)
        else none
      else
        if fmtSize (cc f 0) > 0 ∧ cc f 1 = '\x00' then some (cc f 0, fmtSize (cc f 0)) else none
    let B : Option (List Char) :=
      if cc f 0 = '\x00' then none
      else if cc f 0 = 'Z' then
        if cc f 1 = '\x00' ∨ cc f 2 ≠ '\x00' then none
        else if cc f 1 = 'f' ∨ cc f 1 = 'd' then some (mk ['Z', cc f 1])
        else none
      else if cc f 1 ≠ '\x00' then none
      else if nativeChar (cc f 0) then some (mk [cc f 0])
      else none
    A.isSome = B.isSome ∧ ∀ c size, A = some (c, size) →
      stripAt (B.getD []) = codeText c ∧ 0 < size ∧ codeSize c = some size.toNat := by
  intro A B
  have hZ0 : ('Z' : Char) ≠ '\x00' := by decide
  by_cases hz : cc f 0 = 'Z'
  · have h00 : cc f 0 ≠ '\x00' := by rw [hz]; exact hZ0
    have hA : A = (if cc f 1 = 'f' ∧ cc f 2 = '\x00' then some (zfCode, (8 : Int))
        else if cc f 1 = 'd' ∧ cc f 2 = '\x00' then some (zdCode, 16) else none) := if_pos hz
    have hB : B = (if cc f 1 = '\x00' ∨ cc f 2 ≠ '\x00' then none
        else if cc f 1 = 'f' ∨ cc f 1 = 'd' then some (mk ['Z', cc f 1]) else none) := by
      show (if cc f 0 = '\x00' then none else _) = _
      rw [if_neg h00, if_pos hz]
    rw [hA, hB]
    by_cases h2 : cc f 2 = '\x00'
    · by_cases hf : cc f 1 = 'f'
      · have e1 := hm ['Z', 'f'] (by rw [hz]; rfl)
        simp only [hf, h2, and_self, ↓reduceIte, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
          true_or, Option.getD_some, ne_eq, not_true_eq_false, or_false, show ('f' : Char) ≠ '\x00' by decide,
          reduceCtorEq, false_or]
        refine ⟨trivial, ?_⟩
        rintro c size ⟨rfl, rfl⟩
        exact ⟨by simpa [codeText] using e1, by decide, by simp [codeSize]⟩
      · by_cases hd : cc f 1 = 'd'
        · have e1 := hm ['Z', 'd'] (by rw [hz]; rfl)
          simp only [hd, h2, and_self, ↓reduceIte, Option.isSome_some, Option.some.injEq, Prod.mk.injEq,
            or_true, Option.getD_some, ne_eq, not_true_eq_false, or_false,
            show ('d' : Char) ≠ '\x00' by decide, show ('d' : Char) ≠ 'f' by decide, false_and,
            reduceCtorEq, false_or]
          refine ⟨trivial, ?_⟩
          rintro c size ⟨rfl, rfl⟩
          exact ⟨by simpa [codeText, show zdCode ≠ zfCode by decide] using e1, by decide,
            by simp [codeSize, show zdCode ≠ zfCode by decide]⟩
        · simp [hf, hd, h2]
    · simp [h2]
  · have hA : A = (if fmtSize (cc f 0) > 0 ∧ cc f 1 = '\x00' then some (cc f 0, fmtSize (cc f 0)) else none) :=
      if_neg hz
    by_cases hnat : nativeChar (cc f 0) = true
    · have h0 : cc f 0 ≠ '\x00' := fun e => by rw [e] at hnat; simp [nativeChar_nul] at hnat
      have hs := (fmtSize_pos_iff _).2 hnat
      have hB : B = (if cc f 1 ≠ '\x00' then none else if nativeChar (cc f 0) then some (mk [cc f 0]) else none) := by
        show (if cc f 0 = '\x00' then none else _) = _
        rw [if_neg h0, if_neg hz]
      rw [hA, hB]
      by_cases h1 : cc f 1 = '\x00'
      · have e1 := hm [cc f 0] rfl
        obtain ⟨c1, c2⟩ := nativeChar_code _ hnat
        simp only [hs, h1, true_and, ↓reduceIte, ne_eq, not_true_eq_false, hnat, Option.isSome_some,
          Option.some.injEq, Prod.mk.injEq, Option.getD_some, true_and]
        rintro c size ⟨rfl, rfl⟩
        refine ⟨by simpa [codeText, c1, c2] using e1, hs, ?_⟩
        simp only [codeSize, c1, c2, ↓reduceIte]
        exact nativeSize_of _ hnat
      · simp [h1]
    · have hs : ¬ fmtSize (cc f 0) > 0 := fun h => hnat ((fmtSize_pos_iff _).1 h)
      have hA' : A = none := by rw [hA]; simp [hs]
      have hB : B = none := by
        show (if cc f 0 = '\x00' then none else if cc f 0 = 'Z' then _ else
          if cc f 1 ≠ '\x00' then none else if nativeChar (cc f 0) then some _ else none) = none
        by_cases h0 : cc f 0 = '\x00'
        · rw [if_pos h0]
        · rw [if_neg h0, if_neg hz, if_neg hnat]
          split <;> rfl
      rw [hA', hB]
      simp

theorem nativeFormatAgree_proven : NativeFormatAgree := by
  intro fmt
  unfold getNativeFmtchar getNativeFmtstr
  dsimp only
  by_cases ha : cc fmt 0 = '@'
  · simp only [ha, ite_true]
    exact native_agree_core (fmt.drop 1) (fun l => '@' :: l) (fun l _ => by simp [stripAt, cc])
  · simp only [ha, ite_false]
    refine native_agree_core fmt id fun l hl => ?_
    simp [stripAt, hl, ha]

/-! ## A concrete view, for the refutations -/

/-- `b` bytes, as `memoryview(bytearray(...))` sees them. -/
def plainBuf (n : Int) : Buf :=
  { obj := some (.exp 0), buf := 0, len := n, itemsize := 1, readonly := false, ndim := 1,
    format := some ['B'], shape := some [n], strides := some [1] }

/-- A state with one managed buffer and view `0` over the store `m`. -/
def oneView (m : Mem) : St :=
  let b := plainBuf m.length
  { mem := m, mbufs := [{ master := b, exports := 1 }],
    mvs := [{ view := b, flags := initFlags b }], unhashable := [none] }

/-- `memoryview.cast` accepts only `[@]c` for a native `c`: its message says the
destination format "must be a native format prefixed with an optional '@'". -/
def CastWholeFormat : Prop :=
  ∀ (st : St) (self : Nat) (format : List Char) (i : Nat) (st' : St),
    memoryviewCast self format none st = (.ok i, st') → format.length ≤ 2

/-- `memoryview(bytearray(2)).cast('B\0xyz')` succeeds: `cast_to_1D` hands
`PyBytes_AS_STRING(asciifmt)` to two functions that stop at the first NUL. -/
theorem castWholeFormat_refuted : ¬ CastWholeFormat := by
  intro h
  have := h (oneView [97, 98]) 0 ['B', '\x00', 'x'] 1
    (memoryviewCast 0 ['B', '\x00', 'x'] none (oneView [97, 98])).2 (by rfl)
  simp at this

end PyLean.BytesObj.Mem
