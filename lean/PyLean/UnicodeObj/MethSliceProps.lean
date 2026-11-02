import PyLean.UnicodeObj.MethSlice
import PyLean.UnicodeObj.MethStripProps

/-!
Properties of indexing and slicing a `str`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- Python's `s[a:b]` for int bounds (Library Reference, "Common Sequence Operations",
note 4): a negative bound counts from the end, and both are clipped to `[0, len(s)]`; any int
is allowed. -/
def sliceDoc (s : Str) (a b : Int) : Str :=
  (s.drop (clipIndex s.length a)).take (clipIndex s.length b - clipIndex s.length a)

/-- For every string and every pair of bound objects (ints of any size, `None`, objects whose
`__index__` answers or raises, objects without `__index__`): the 3.15 fast path
`_PyUnicode_BinarySlice` that `s[a:b]` runs gives exactly what `unicode_subscript` gives for
`s[slice(a, b)]`, result or exception; and for int bounds it is Python's slice.
Type invariant: `len(s) <= PY_SSIZE_T_MAX`. -/
def SliceTwin : Prop :=
  ∀ (s : Str), (s.length : Int) ≤ ssizeMax →
    (∀ start stop : Arg,
      unicodeBinarySlice s start stop = unicodeSubscript s (.slice ⟨start, stop, .none⟩)) ∧
    (∀ a b : Int, unicodeBinarySlice s (.int a) (.int b) = .ok (sliceDoc s a b))

theorem unpack_none_step (start stop : Arg) :
    sliceUnpackObj ⟨start, stop, .none⟩ =
      (sliceIndex start 0 >>= fun a => sliceIndex stop ssizeMax >>= fun b => pure (a, b, 1)) := by
  unfold sliceUnpackObj sliceIndex
  cases start <;> cases stop <;> rfl

theorem adjust_step1 (len start stop : Int) (h : 0 ≤ len) :
    0 ≤ (RangeSlice.adjustIndices len start stop 1).1 ∧
    (RangeSlice.adjustIndices len start stop 1).1 ≤ len ∧
    0 ≤ (RangeSlice.adjustIndices len start stop 1).2.1 ∧
    (RangeSlice.adjustIndices len start stop 1).2.1 ≤ len ∧
    (RangeSlice.adjustIndices len start stop 1).2.2 =
      (if (RangeSlice.adjustIndices len start stop 1).1 < (RangeSlice.adjustIndices len start stop 1).2.1
       then (RangeSlice.adjustIndices len start stop 1).2.1 - (RangeSlice.adjustIndices len start stop 1).1
       else 0) := by
  simp only [RangeSlice.adjustIndices, RangeSlice.adjustOne, Int.tdiv_one]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> repeat' split
  all_goals omega

theorem binary_ok (s : Str) (start stop : Arg) (a b : Int) (ha : sliceIndex start 0 = .ok a)
    (hb : sliceIndex stop ssizeMax = .ok b) :
    unicodeBinarySlice s start stop =
      pyUnicodeSubstring s (RangeSlice.adjustIndices s.length a b 1).1
        (RangeSlice.adjustIndices s.length a b 1).2.1 := by
  unfold unicodeBinarySlice unpackIndices
  rw [ha, hb]
  rfl

/-- The branches of `unicode_subscript` for a step of 1. -/
def subStep1 (s : Str) (A B n : Int) : Py Str :=
  if n ≤ 0 then .ok []
  else if A = 0 ∧ (1 : Int) = 1 ∧ n = s.length then .ok s
  else if (1 : Int) = 1 then pyUnicodeSubstring s A (A + n)
  else .ok ((List.range n.toNat).map fun (i : Nat) => s.getD (A + (i : Int) * 1).toNat 0)

theorem sub_ok (s : Str) (start stop : Arg) (a b : Int) (ha : sliceIndex start 0 = .ok a)
    (hb : sliceIndex stop ssizeMax = .ok b) :
    unicodeSubscript s (.slice ⟨start, stop, .none⟩) =
      subStep1 s (RangeSlice.adjustIndices s.length a b 1).1
        (RangeSlice.adjustIndices s.length a b 1).2.1
        (RangeSlice.adjustIndices s.length a b 1).2.2 := by
  show (sliceUnpackObj ⟨start, stop, .none⟩ >>= _) = _
  rw [unpack_none_step, ha, hb]
  rfl

theorem sub_err_start (s : Str) (start stop : Arg) (e : PyExc) (ha : sliceIndex start 0 = .error e) :
    unicodeSubscript s (.slice ⟨start, stop, .none⟩) = .error e := by
  show (sliceUnpackObj ⟨start, stop, .none⟩ >>= _) = _
  rw [unpack_none_step, ha]
  rfl

theorem sub_err_stop (s : Str) (start stop : Arg) (a : Int) (e : PyExc)
    (ha : sliceIndex start 0 = .ok a) (hb : sliceIndex stop ssizeMax = .error e) :
    unicodeSubscript s (.slice ⟨start, stop, .none⟩) = .error e := by
  show (sliceUnpackObj ⟨start, stop, .none⟩ >>= _) = _
  rw [unpack_none_step, ha, hb]
  rfl

theorem subStep1_eq (s : Str) (a b : Int) :
    subStep1 s (RangeSlice.adjustIndices s.length a b 1).1
        (RangeSlice.adjustIndices s.length a b 1).2.1
        (RangeSlice.adjustIndices s.length a b 1).2.2 =
      pyUnicodeSubstring s (RangeSlice.adjustIndices s.length a b 1).1
        (RangeSlice.adjustIndices s.length a b 1).2.1 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := adjust_step1 s.length a b (by omega)
  generalize RangeSlice.adjustIndices s.length a b 1 = r at *
  obtain ⟨A, B, n⟩ := r
  simp only at h1 h2 h3 h4 h5 ⊢
  unfold subStep1
  rw [substringDoc_proven s A B, if_neg (show ¬ (A < 0 ∨ B < 0) by omega)]
  by_cases hn : n ≤ 0
  · rw [if_pos hn]
    have : (B - A).toNat = 0 := by split at h5 <;> omega
    rw [this]; simp
  · rw [if_neg hn]
    have hAB : A < B ∧ n = B - A := by split at h5 <;> omega
    by_cases hw : A = 0 ∧ n = s.length
    · rw [if_pos ⟨hw.1, rfl, hw.2⟩, hw.1]
      simp only [Int.toNat_zero, List.drop_zero, Int.sub_zero]
      rw [List.take_of_length_le (by omega)]
    · rw [if_neg (fun h => hw ⟨h.1, h.2.2⟩), if_pos rfl, show A + n = B by omega,
        substringDoc_proven s A B, if_neg (show ¬ (A < 0 ∨ B < 0) by omega)]

theorem sliceTwin_proven : SliceTwin := by
  intro s hlen
  refine ⟨?_, ?_⟩
  · intro start stop
    cases ha : sliceIndex start 0 with
    | error e =>
      rw [sub_err_start s start stop e ha]
      unfold unicodeBinarySlice unpackIndices
      rw [ha]
      rfl
    | ok a =>
      cases hb : sliceIndex stop ssizeMax with
      | error e =>
        rw [sub_err_stop s start stop a e ha hb]
        unfold unicodeBinarySlice unpackIndices
        rw [ha, hb]
        rfl
      | ok b =>
        rw [binary_ok s start stop a b ha hb, sub_ok s start stop a b ha hb, subStep1_eq]
  · intro x y
    have hclamp : ∀ (v : Int) (d : Int), sliceIndex (.int v) d =
        .ok (if v < ssizeMin then ssizeMin else if v > ssizeMax then ssizeMax else v) := by
      intro v d
      show (if -(2 ^ 30) < v ∧ v < 2 ^ 30 then .ok v else asSsizeClamp (.int v)) = _
      by_cases h : -(2 ^ 30) < v ∧ v < 2 ^ 30
      · rw [if_pos h, if_neg (by unfold ssizeMin; omega), if_neg (by unfold ssizeMax; omega)]
      · rw [if_neg h]; rfl
    have hone : ∀ v : Int, RangeSlice.adjustOne
        (if v < ssizeMin then ssizeMin else if v > ssizeMax then ssizeMax else v) s.length 1 =
        clipIndex s.length v := by
      intro v
      simp only [RangeSlice.adjustOne, clipIndex]
      unfold ssizeMin ssizeMax at *
      repeat' split
      all_goals omega
    rw [binary_ok s _ _ _ _ (hclamp x 0) (hclamp y ssizeMax)]
    simp only [RangeSlice.adjustIndices]
    rw [hone x, hone y, substringDoc_proven, if_neg (by omega)]
    unfold sliceDoc
    congr 2
    all_goals (first | omega | simp)

/-- `s[i]` for every object `i`: an int (or `__index__` answer) `v` in `[-len(s), len(s))` gives
the character at `v`, counted from the end when negative; any other int raises `IndexError`
(`cannot fit` beyond `Py_ssize_t`); an exception from `__index__` propagates; an object without
`__index__` raises `TypeError`. For every string with a `Py_ssize_t` length. -/
def IndexDoc : Prop :=
  ∀ (s : Str) (a : Arg), (s.length : Int) ≤ ssizeMax →
    unicodeSubscript s (.obj a) =
      if a.hasIndex then
        match numberIndex a with
        | .error e => .error e
        | .ok v =>
          if v < ssizeMin ∨ v > ssizeMax then
            .error (.indexError s!"cannot fit '{a.tpName}' into an index-sized integer")
          else if -(s.length : Int) ≤ v ∧ v < s.length then
            .ok [s.getD (if v < 0 then v + s.length else v).toNat 0]
          else .error (.indexError "string index out of range")
      else .error (.typeError s!"string indices must be integers, not '{a.tpName}'")

theorem indexDoc_proven : IndexDoc := by
  intro s a hlen
  show (if a.hasIndex then _ else _) = _
  by_cases hi : a.hasIndex = true
  · rw [if_pos hi, if_pos hi]
    unfold asSsizeIndexError
    cases numberIndex a with
    | error e => rfl
    | ok v =>
      show (if v < ssizeMin ∨ v > ssizeMax then _ else _) >>= _ = _
      by_cases hr : v < ssizeMin ∨ v > ssizeMax
      · rw [if_pos hr]; simp only [if_pos hr]; rfl
      · rw [if_neg hr]
        simp only [if_neg hr]
        show unicodeGetitem s (if v < 0 then v + s.length else v) = _
        unfold unicodeGetitem
        by_cases hin : -(s.length : Int) ≤ v ∧ v < s.length
        · rw [if_pos hin, if_neg (by split <;> omega)]
        · rw [if_neg hin, if_pos (by split <;> omega)]
  · rw [if_neg hi, if_neg hi]

end PyLean.UnicodeObj
