import PyLean.Sequences.ArrayOps

/-!
`array.array` and text, pickling: `tounicode`, `fromunicode`, `__reduce_ex__`,
`_array_reconstructor`.
-/

namespace PyLean.Sequences

open PyLean

set_option linter.unusedSectionVars false

/-- A code point `str` can hold, surrogates included. -/
def isCodePoint (c : Nat) : Prop := c ≤ 1114111

/-- A `w` array of these code points, built by `array('w', s)`. -/
def wArr (cps : List Nat) : Arr :=
  ⟨.w, cps.map (fun c : Nat => (c : Int)), cps.length, decide (cps.length > 0), 0, "array"⟩

/-- `array('w', s).tounicode() == s` for every `str` `s`. Refuted: `tounicode` decodes
UTF-32 with `byteorder == 0`, so a leading U+FEFF is dropped as a byte order mark, and
surrogates, which `str` allows and `w` stores, raise `UnicodeDecodeError`. -/
def ArrayToUnicodeW : Prop :=
  ∀ cps : List Nat, (∀ c ∈ cps, isCodePoint c) → arrToUnicode (wArr cps) = .ok cps

theorem arrayToUnicodeW_refuted : ¬ ArrayToUnicodeW := by
  intro h
  have := h [65279, 97] (by intro c hc; simp at hc; unfold isCodePoint; omega)
  have e : arrToUnicode (wArr [65279, 97]) = .ok [97] := by decide
  rw [e] at this
  simp at this

theorem map_cast_toNat (cps : List Nat) : (cps.map (fun c : Nat => (c : Int))).map Int.toNat = cps := by
  induction cps with
  | nil => rfl
  | cons c cs ih => simp only [List.map_cons, ih]; simp

/-- `tounicode` round-trips on `u` for every `str`, and on `w` when `s` has no surrogates
and does not start with U+FEFF, the two cases `ArrayToUnicodeW` refutes. Other typecodes
raise `ValueError`. -/
def ArrayToUnicodeChecked : Prop :=
  (∀ cps : List Nat, (∀ c ∈ cps, isCodePoint c ∧ ¬ (55296 ≤ c ∧ c ≤ 57343)) → cps.head? ≠ some 65279 →
    arrToUnicode (wArr cps) = .ok cps) ∧
  (∀ cps : List Nat, (∀ c ∈ cps, isCodePoint c) →
    arrToUnicode { wArr cps with tc := .u } = .ok cps) ∧
  (∀ a : Arr, a.tc ≠ .u → a.tc ≠ .w → (arrToUnicode a).raises "ValueError")

theorem any_bad (cps : List Nat) (h : ∀ c ∈ cps, isCodePoint c ∧ ¬ (55296 ≤ c ∧ c ≤ 57343)) :
    (cps.map (fun c : Nat => (c : Int))).any (fun x => decide (x > 1114111 ∨ (55296 ≤ x ∧ x ≤ 57343))) = false := by
  rw [List.any_eq_false]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  have := h c hc
  unfold isCodePoint at this
  simp only [decide_eq_true_eq]
  omega

theorem find_bad (cps : List Nat) (h : ∀ c ∈ cps, isCodePoint c) :
    (cps.map (fun c : Nat => (c : Int))).find? (fun x => decide (x < 0 ∨ x > 1114111)) = none := by
  rw [List.find?_eq_none]
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨c, hc, rfl⟩ := hx
  have := h c hc
  unfold isCodePoint at this
  simp only [decide_eq_true_eq]
  omega

theorem arrToUnicode_w (items : List Int) (al : Int) (hb : Bool) (ex : Nat) (tn : String) :
    arrToUnicode ⟨.w, items, al, hb, ex, tn⟩ = decodeUTF32Native items := rfl

theorem arrToUnicode_u (items : List Int) (al : Int) (hb : Bool) (ex : Nat) (tn : String) :
    arrToUnicode ⟨.u, items, al, hb, ex, tn⟩ =
      match items.find? (fun x => decide (x < 0 ∨ x > 1114111)) with
      | some x => .error (.valueError s!"~character U+{x} is not in range [U+0000; U+10ffff]")
      | none => .ok (items.map Int.toNat) := rfl

theorem arrayToUnicodeChecked_proven : ArrayToUnicodeChecked := by
  refine ⟨fun cps h hh => ?_, fun cps h => ?_, fun a h1 h2 => ?_⟩
  · have hbody : bomSplit (cps.map (fun c : Nat => (c : Int))) = (cps.map (fun c : Nat => (c : Int)), false) := by
      cases cps with
      | nil => rfl
      | cons c cs =>
        have hc := h c (by simp)
        unfold isCodePoint at hc
        have h1 : (c : Int) ≠ 65279 := by
          intro e
          apply hh
          simp only [List.head?_cons, Option.some.injEq]
          omega
        have h2 : (c : Int) ≠ 4294836224 := by omega
        simp only [List.map_cons]
        unfold bomSplit
        split
        · rename_i heq
          simp only [List.cons.injEq] at heq
          exact absurd heq.1 h1
        · rename_i heq
          simp only [List.cons.injEq] at heq
          exact absurd heq.1 h2
        · rfl
    unfold wArr
    rw [arrToUnicode_w]
    unfold decodeUTF32Native
    simp only [hbody, Bool.false_eq_true, ite_false]
    rw [any_bad cps h]
    simp only [Bool.false_eq_true, ite_false, map_cast_toNat]
  · unfold wArr
    rw [arrToUnicode_u]
    simp only [find_bad cps h, map_cast_toNat]
  · simp only [arrToUnicode, bind, Except.bind, throwE]
    rw [iteT ⟨h1, h2⟩]
    exact ⟨_, rfl, rfl⟩

/-- `a.fromunicode(s)` appends the code points of `s` for every `u` or `w` array without
exported buffers (the result fits) and every `s`. Refuted by `array('w').fromunicode('')`:
`PyUnicode_AsUCS4` refuses the NULL buffer of an empty array with an exception the method
ignores, so it returns a result with an exception set. -/
def ArrayFromUnicode : Prop :=
  ∀ (a : Arr) (s : List Nat), (a.tc = .u ∨ a.tc = .w) → a.exports = 0 → a.Alloc →
    a.Fits (a.items.length + s.length) →
    (arrFromUnicode a s).map (·.items) = .ok (a.items ++ s.map (fun c : Nat => (c : Int)))

theorem arrayFromUnicode_refuted : ¬ ArrayFromUnicode := by
  intro h
  have := h ⟨.w, [], 0, false, 0, "array"⟩ [] (Or.inr rfl) rfl
    ⟨by simp, fun _ => rfl⟩ (by unfold Arr.Fits ssizeMax TC.itemsize; simp)
  have e : arrFromUnicode ⟨.w, [], 0, false, 0, "array"⟩ [] = .error (.named "SystemError"
      "<method 'fromunicode' of 'array.array' objects> returned a result with an exception set") := by decide
  rw [e] at this
  simp [Except.map] at this

theorem arrResize_hasBuf (a a' : Arr) (n : Int) (hs : (a.items.length : Int) ≤ n) (ha : a.Alloc)
    (hb : a.hasBuf = true ∨ n > 0)
    (hr : arrResize a n = .ok a') : a'.hasBuf = true := by
  have hal := ha.1
  unfold arrResize at hr
  dsimp only at hr
  split at hr
  · simp at hr
  · split at hr
    · rename_i hc
      have : a' = { a with items := resized a.items n } := by simpa using hr.symm
      subst this
      exact hc.2.2
    · split at hr
      · rename_i hc hz
        exfalso
        rcases hb with hb | hb
        · apply hc
          exact ⟨by omega, by omega, hb⟩
        · omega
      · generalize n / 16 + (if (a.items.length : Int) < 8 then (3 : Int) else 7) + n = na at hr
        split at hr
        · have : a' = { a with items := resized a.items n, hasBuf := true, allocated := na } := by
            simpa using hr.symm
          subst this
          rfl
        · simp at hr

/-- The same with the case refuted above excluded: a `u` array, or a `w` array that has a
buffer or receives at least one character. Other typecodes raise `ValueError`. -/
def ArrayFromUnicodeChecked : Prop :=
  (∀ (a : Arr) (s : List Nat), (a.tc = .u ∨ (a.tc = .w ∧ (a.hasBuf = true ∨ s ≠ []))) → a.exports = 0 →
    a.Alloc → a.Fits (a.items.length + s.length) →
    (arrFromUnicode a s).map (·.items) = .ok (a.items ++ s.map (fun c : Nat => (c : Int)))) ∧
  (∀ (a : Arr) (s : List Nat), a.tc ≠ .u → a.tc ≠ .w → (arrFromUnicode a s).raises "ValueError")

theorem memcpy_map (l : List Int) (s : List Nat) :
    memcpy (l ++ List.replicate s.length 0) l.length (s.map (fun c : Nat => (c : Int))) =
      l ++ s.map (fun c : Nat => (c : Int)) := by
  have := memcpy_end l (s.map (fun c : Nat => (c : Int)))
  rwa [List.length_map] at this

theorem resized_add (l : List Int) (k : Nat) :
    resized l ((l.length : Int) + k) = l ++ List.replicate k 0 := by
  by_cases hk : k = 0
  · subst hk
    simp only [Int.natCast_zero, Int.add_zero, List.replicate_zero, List.append_nil]
    exact resized_same l
  · exact resized_grow l k (by omega)

theorem arrayFromUnicodeChecked_proven : ArrayFromUnicodeChecked := by
  refine ⟨fun a s hc hx ha hf => ?_, fun a s h1 h2 => ?_⟩
  · obtain ⟨a', hr, hi, ht, _⟩ := arrResize_ok a (a.items.length + s.length) hx (by omega) hf
    have hres : a'.items = a.items ++ List.replicate s.length 0 := by rw [hi]; exact resized_add _ _
    have hnz : s ≠ [] → (s.length : Int) > 0 := fun hs => by
      have : s.length ≠ 0 := fun h => hs (List.eq_nil_of_length_eq_zero h)
      omega
    rcases hc with hu | ⟨hw, hb⟩
    · have h1 : ¬ (a.tc ≠ .u ∧ a.tc ≠ .w) := fun h => h.1 hu
      simp only [arrFromUnicode, bind, Except.bind, pure, Except.pure, throwE]
      rw [iteF h1, iteT hu]
      by_cases hs : s = []
      · subst hs
        simp [Except.map]
      · have hnz' : s.length > 0 := by have := hnz hs; omega
        rw [iteT hnz', hr]
        simp only [Except.map]
        rw [hres]
        exact congrArg _ (memcpy_map a.items s)
    · have h1 : ¬ (a.tc ≠ .u ∧ a.tc ≠ .w) := fun h => h.2 hw
      have h2 : ¬ a.tc = .u := by rw [hw]; decide
      have hbuf : a'.hasBuf = true := arrResize_hasBuf a a' _ (by omega) ha
        (hb.elim Or.inl (fun hs => Or.inr (by have := hnz hs; omega))) hr
      have h3 : ¬ ((a.items.length : Int) + s.length > ssizeMax / 4) := by
        have h4 : TC.itemsize .w = 4 := rfl
        unfold Arr.Fits at hf
        rw [hw, h4] at hf
        omega
      simp only [arrFromUnicode, bind, Except.bind, pure, Except.pure, throwE]
      rw [iteF h1, iteF h2, iteF h3, hr]
      simp only [hbuf, Bool.not_true, Bool.false_eq_true, ite_false, Except.map]
      rw [hres]
      exact congrArg _ (memcpy_map a.items s)
  · simp only [arrFromUnicode, bind, Except.bind, throwE]
    rw [iteT ⟨h1, h2⟩]
    exact ⟨_, rfl, rfl⟩

/-! ### Pickling -/

theorem arrResize_keeps (a a' : Arr) (n : Int) (h : arrResize a n = .ok a') :
    a'.tc = a.tc ∧ a'.tname = a.tname := by
  unfold arrResize at h
  dsimp only at h
  split at h
  · simp at h
  · split at h
    · have : a' = { a with items := resized a.items n } := by simpa using h.symm
      subst this
      exact ⟨rfl, rfl⟩
    · split at h
      · have : a' = { a with items := [], hasBuf := false, allocated := 0 } := by simpa using h.symm
        subst this
        exact ⟨rfl, rfl⟩
      · generalize n / 16 + (if (a.items.length : Int) < 8 then (3 : Int) else 7) + n = na at h
        split at h
        · have : a' = { a with items := resized a.items n, hasBuf := true, allocated := na } := by
            simpa using h.symm
          subst this
          exact ⟨rfl, rfl⟩
        · simp at h

theorem arrFromBytes_keeps (a a' : Arr) (bs : List Nat) (w : Int) (h : arrFromBytes a bs w = .ok a') :
    a'.tc = a.tc ∧ a'.tname = a.tname := by
  unfold arrFromBytes at h
  simp only [bind, Except.bind, pure, Except.pure, throwE] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · split at h
        · simp at h
        · cases hr : arrResize a ((a.items.length : Int) + (bs.length : Int) / a.tc.itemsize) with
          | error e => simp [hr] at h
          | ok a1 =>
            rw [hr] at h
            have : a' = { a1 with items := (memcpy a1.items a.items.length
                ((chunks a.tc.itemsize.toNat bs bs.length).map (itemOfBytes a.tc))) } := by simpa using h.symm
            subst this
            exact arrResize_keeps a a1 _ hr
      · have : a' = a := by simpa using h.symm
        subst this
        exact ⟨rfl, rfl⟩

theorem arrNew_bytes (t : String) (tc : TC) (bs : List Nat) :
    arrNew t tc.code (.bytes bs) = arrFromBytes ⟨tc, [], 0, false, 0, t⟩ bs 1 := by
  unfold arrNew
  simp only [arrNewBad_bytes, find_code, Option.isSome_none, Bool.false_eq_true, ite_false]
  rw [show newArr t tc 0 = .ok ⟨tc, [], 0, false, 0, t⟩ from newArr_ok t tc 0 (fits_zero ⟨tc, [], 0, false, 0, t⟩)]
  simp only
  cases arrFromBytes ⟨tc, [], 0, false, 0, t⟩ bs 1 <;> rfl

theorem mformat_range (tc : TC) : ¬ (mformatOf tc < 0 ∨ mformatOf tc > 27) := by cases tc <;> decide

theorem mapM_set_int (tc : TC) (hi : tc.isInteger = true) (l : List Int) (h : ∀ x ∈ l, tc.lo ≤ x ∧ x ≤ tc.hi) :
    (l.map PyVal.int).mapM (tcSetitem tc true) = .ok l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons]
    rw [List.mapM_cons, tcSetitem_range tc hi x (h x (by simp))]
    simp only [bind, Except.bind, ih (fun y hy => h y (by simp [hy])), pure, Except.pure]

/-- `pickle` of an array, for every array (type invariant `WF`, `len` fits). From protocol 3
on, `__reduce_ex__` gives the array's bytes and its machine format, and
`_array_reconstructor` on them rebuilds the same type, typecode and items, for every
typecode. Below protocol 3 it gives a list, and `array(typecode, list)` rebuilds the items,
for the integer typecodes (float items wait for `Binary64`; the character typecodes need
items that decode). A `protocol` outside a C `long` raises `OverflowError`, a non-int
`TypeError`. The other machine formats of the reconstructor are mirrored and
difftested; `ArrayReconstructUTF` covers the unicode ones. -/
def ArrayReduce : Prop :=
  ∀ (a : Arr) (p : Int), a.WF → a.Fits a.items.length →
    (3 ≤ p → p ≤ longMax →
      arrReduceEx a (.int p) = .ok (.asBytes a.tname a.tc.code (mformatOf a.tc) (arrToBytes a)) ∧
      ∃ b, reconstruct a.tname a.tc.code (mformatOf a.tc) (arrToBytes a) = .ok b ∧
        b.items = a.items ∧ b.tc = a.tc ∧ b.tname = a.tname) ∧
    (longMin ≤ p → p < 3 → a.tc.isInteger = true →
      arrReduceEx a (.int p) = .ok (.asList a.tname a.tc.code (a.items.map .int)) ∧
      ∃ b, arrNew a.tname a.tc.code (.list (a.items.map .int)) = .ok b ∧
        b.items = a.items ∧ b.tc = a.tc ∧ b.tname = a.tname) ∧
    ((p < longMin ∨ p > longMax) → (arrReduceEx a (.int p)).raises "OverflowError") ∧
    (arrReduceEx a (.str [])).raises "TypeError"

theorem arrayReduce_proven : ArrayReduce := by
  intro a p hw hf
  have hl : longMin ≤ p ∧ p ≤ longMax → asLongV (.int p) = .ok p := fun h => asLongV_ok p h.1 h.2
  have hm3 : longMin ≤ 3 := by decide
  have h3m : (3 : Int) ≤ longMax := by decide
  refine ⟨fun h0 h1 => ⟨?_, ?_⟩, fun h0 h1 hi => ⟨?_, ?_⟩, fun h => ?_, ⟨_, rfl, rfl⟩⟩
  · simp only [arrReduceEx, hl ⟨Int.le_trans hm3 h0, h1⟩]
    rw [iteF (by omega)]
  · let e : Arr := ⟨a.tc, [], 0, false, 0, a.tname⟩
    have hr := arrayBytesRoundTrip_proven e a rfl hw rfl (by
      unfold Arr.Fits at *
      simpa [e] using hf)
    obtain ⟨⟨a', h1', h2⟩, _⟩ := hr
    obtain ⟨h3, h4⟩ := arrFromBytes_keeps e a' _ _ h1'
    refine ⟨a', ?_, by rw [h2]; simp [e], h3, h4⟩
    unfold reconstruct
    rw [find_code]
    simp only
    rw [iteF (mformat_range a.tc), iteT trivial]
    unfold makeArray
    rw [arrNew_bytes]
    exact h1'
  · simp only [arrReduceEx, hl ⟨h0, Int.le_trans (Int.le_of_lt h1) h3m⟩]
    rw [iteT h1]
    simp only [arrToList, mapM_get_int a.tc hi]
  · obtain ⟨b, h2, h3, h4, _, h5⟩ := arrNew_list a.tname a.tc (a.items.map .int) a.items
      (mapM_set_int a.tc hi _ hw) (by simpa [Arr.Fits] using hf)
    exact ⟨b, h2, h3, h4, h5⟩
  · have : asLongV (.int p) = .error (.overflowError "Python int too large to convert to C long") := by
      simp only [asLongV, toIndex, bind, Except.bind, pure, Except.pure]
      rw [iteF (by omega)]
      rfl
    simp only [arrReduceEx, this]
    exact ⟨_, rfl, rfl⟩

/-- `f` and `d` items. Every stored bit pattern reads as a Python float and stores back
unchanged. Waits for `lean/PyLean/Binary64/`; NaN patterns in `f` go through the C
float-to-double conversion. -/
def ArrayFloatItems : Prop :=
  (∀ b : Nat, b < 4294967296 → ∃ v, tcGetitem .f b = .ok v ∧ tcSetitem .f true v = .ok b) ∧
  (∀ b : Nat, b < 18446744073709551616 → ∃ v, tcGetitem .d b = .ok v ∧ tcSetitem .d true v = .ok b)

/-- `del a[s]` agrees with `del l[s]` on the items, for every array without exported buffers
and every slice with int/None parts. -/
def ArrayDelSliceAgree : Prop :=
  ∀ (a : Arr) (s : RangeSlice.Slice), a.exports = 0 → a.Fits a.items.length →
    (arrAssSlice a s .delete).map (·.items) = listAssSubscript a.items s none

/-- The integer typecodes read and store the same value, through `getarrayitem` and the
`*_getitem` and `*_setitem` functions, for every in-range value. -/
def ArrayGetSet : Prop :=
  ∀ (tc : TC) (x : Int), tc.isInteger = true → tc.lo ≤ x → x ≤ tc.hi →
    tcSetitem tc true (.int x) = .ok x ∧ tcGetitem tc x = .ok (.int x) ∧
    ∀ (a : Arr) (i : Int), a.tc = tc → ix a.items i = x → a.get i = .ok (.int x)

theorem arrayGetSet_proven : ArrayGetSet := by
  intro tc x hi h0 h1
  refine ⟨tcSetitem_range tc hi x ⟨h0, h1⟩, tcGetitem_int tc hi x, fun a i ht hx => ?_⟩
  unfold Arr.get
  rw [ht, hx]
  exact tcGetitem_int tc hi x

/-- The UTF-32-BE bytes of code points. -/
def utf32be (cps : List Nat) : List Nat :=
  cps.flatMap (fun c => [c / 16777216 % 256, c / 65536 % 256, c / 256 % 256, c % 256])

/-- `array._array_reconstructor(array, 'w', UTF32_BE, s.encode('utf-32-be'))` rebuilds `s`,
for every string without surrogates: the path pickles take across byte orders. Refuted:
`mformat_descriptors` gives the UTF rows sizes 4 and 8 instead of 2 and 4, so any
odd-length string fails with `ValueError: string length not a multiple of item size`. -/
def ArrayReconstructUTF : Prop :=
  ∀ cps : List Nat, (∀ c ∈ cps, c ≤ 1114111 ∧ ¬ (55296 ≤ c ∧ c ≤ 57343)) →
    ∃ b, reconstruct "array" "w" 21 (utf32be cps) = .ok b ∧ b.items = cps.map (fun c : Nat => (c : Int))

theorem arrayReconstructUTF_refuted : ¬ ArrayReconstructUTF := by
  intro h
  obtain ⟨b, h1, _⟩ := h [97] (by intro c hc; simp at hc; subst hc; decide)
  have e : reconstruct "array" "w" 21 (utf32be [97]) =
      .error (.valueError "string length not a multiple of item size") := by decide
  rw [e] at h1
  simp at h1

end PyLean.Sequences
