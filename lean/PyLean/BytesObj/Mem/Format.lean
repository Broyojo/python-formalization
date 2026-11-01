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

/-- The two tables of the source agree: for every string, `get_native_fmtchar` accepts it
exactly when `get_native_fmtstr` does, and the string `get_native_fmtstr` returns is
`[@]c` for the character `get_native_fmtchar` returns, whose size is the size of that
code in `struct`'s native table. Source: the NOT_REACHED comment at memoryobject.c:1345,
and "native single character format" in the error message at @3.14.7:1297. -/
def NativeFormatAgree : Prop :=
  ∀ fmt : List Char,
    (getNativeFmtchar fmt).isSome = (getNativeFmtstr fmt).isSome ∧
    ∀ c size, getNativeFmtchar fmt = some (c, size) →
      stripAt ((getNativeFmtstr fmt).getD []) = [c] ∧ 0 < size ∧
      nativeSize c = some size.toNat

theorem nativeSize_of (c : Char) (h : nativeChar c = true) :
    nativeSize c = some (fmtSize c).toNat := by
  unfold nativeChar at h
  unfold nativeSize fmtSize
  split at h <;> first | rfl | simp_all

theorem nativeFormatAgree_proven : NativeFormatAgree := by
  intro fmt
  unfold getNativeFmtchar getNativeFmtstr
  dsimp only
  by_cases ha : cc fmt 0 = '@'
  · simp only [ha, ite_true]
    generalize fmt.drop 1 = f
    by_cases hnat : nativeChar (cc f 0) = true
    · have h0 : cc f 0 ≠ '\x00' := fun e => by rw [e] at hnat; simp [nativeChar_nul] at hnat
      have hs := (fmtSize_pos_iff _).2 hnat
      by_cases h1 : cc f 1 = '\x00'
      · simp only [hs, h1, h0, hnat, true_and, ite_true, ne_eq, not_true_eq_false, or_false, ite_false,
          Option.isSome_some, Option.some.injEq, Prod.mk.injEq, Option.getD_some]
        rintro c size ⟨rfl, rfl⟩
        exact ⟨by simp [stripAt, cc], hs, nativeSize_of _ hnat⟩
      · simp [h1]
    · have hs : ¬ fmtSize (cc f 0) > 0 := fun h => hnat ((fmtSize_pos_iff _).1 h)
      simp only [hs, false_and, ite_false, Option.isSome_none]
      by_cases h1 : cc f 0 = '\x00' ∨ cc f 1 ≠ '\x00'
      · simp [h1]
      · simp [h1, hnat]
  · simp only [ha, ite_false]
    by_cases hnat : nativeChar (cc fmt 0) = true
    · have h0 : cc fmt 0 ≠ '\x00' := fun e => by rw [e] at hnat; simp [nativeChar_nul] at hnat
      have hs := (fmtSize_pos_iff _).2 hnat
      by_cases h1 : cc fmt 1 = '\x00'
      · simp only [hs, h1, h0, hnat, true_and, ite_true, ne_eq, not_true_eq_false, or_false, ite_false,
          Option.isSome_some, Option.some.injEq, Prod.mk.injEq, Option.getD_some]
        rintro c size ⟨rfl, rfl⟩
        refine ⟨?_, hs, nativeSize_of _ hnat⟩
        have : cc [cc fmt 0] 0 = cc fmt 0 := rfl
        simp [stripAt, this, ha]
      · simp [h1]
    · have hs : ¬ fmtSize (cc fmt 0) > 0 := fun h => hnat ((fmtSize_pos_iff _).1 h)
      simp only [hs, false_and, ite_false, Option.isSome_none]
      by_cases h1 : cc fmt 0 = '\x00' ∨ cc fmt 1 ≠ '\x00'
      · simp [h1]
      · simp [h1, hnat]

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
destination format "must be a native single character format prefixed with an optional
'@'". -/
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
