import PyLean.StrSearch.Basic

/-!
`find`, `rfind`, `index`, `rindex`, `count`, `startswith`, `endswith`:
the `str` implementation (`any_find_slice`, `unicode_count_impl`, `tailmatch`
in unicodeobject.c) against the `bytes` one (`find_internal`,
`_Py_bytes_count`, `tailmatch` in bytes_methods.c), and both against the
documented "within `s[start:end]`".
-/

set_option linter.deprecated false

namespace PyLean.StrSearch

open PyLean

/-- `a + r` for a found offset `r`, else -1. -/
def optOff (a : Int) : Option Nat → Int
  | some r => a + r
  | none => -1

theorem rfindL_nil (w : Seq) : rfindL [] w = some w.length := by
  rw [rfindL_eq_some]
  refine ⟨⟨by simp, by simp⟩, fun j hj ho => ?_⟩
  have := ho.1; simp at this; omega

theorem findL_nil (w : Seq) : findL [] w = some 0 := by
  rw [findL_eq_some]; exact ⟨⟨by simp, by simp⟩, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem length_window {s : Seq} {a n : Int} (ha : 0 ≤ a) (hn : 0 ≤ n) (h : a + n ≤ s.length) :
    (window s a n).length = n.toNat := by
  simp [window]; omega

theorem findChar_eq (w : Seq) (c : Nat) (fwd : Bool) :
    findChar w c fwd = optIdx ((if fwd then findL else rfindL) [c] w) := by
  cases fwd <;> rfl

theorem optIdx_eq_neg_one {o : Option Nat} : optIdx o = -1 ↔ o = none := by
  cases o <;> simp [optIdx]

theorem optIdx_nonneg_iff {o : Option Nat} : 0 ≤ optIdx o ↔ o ≠ none := by
  cases o <;> simp [optIdx]

theorem fastsearch_search {w p : Seq} (h : p.length ≤ w.length) (hp : p ≠ []) (m : Int) :
    fastsearch w p m .search = optIdx (findL p w) := by
  have : p.length ≠ 0 := by simpa using hp
  simp [fastsearch, this]; omega

theorem fastsearch_rsearch {w p : Seq} (h : p.length ≤ w.length) (hp : p ≠ []) (m : Int) :
    fastsearch w p m .rsearch = optIdx (rfindL p w) := by
  have : p.length ≠ 0 := by simpa using hp
  simp [fastsearch, this]; omega

theorem stringlibFind_eq {w p : Seq} (h : p.length ≤ w.length) (off : Int) :
    stringlibFind w p off = optOff off (findL p w) := by
  unfold stringlibFind
  by_cases hp : p = []
  · subst hp; simp [findL_nil, optOff]
  · have : p.length ≠ 0 := by simpa using hp
    rw [if_neg this, fastsearch_search h hp]
    cases findL p w <;> simp [optIdx, optOff]; omega

theorem stringlibRFind_eq {w p : Seq} (h : p.length ≤ w.length) (off : Int) :
    stringlibRFind w p off = optOff off (rfindL p w) := by
  unfold stringlibRFind
  by_cases hp : p = []
  · subst hp; simp [rfindL_nil, optOff]; omega
  · have : p.length ≠ 0 := by simpa using hp
    rw [if_neg this, fastsearch_rsearch h hp]
    cases rfindL p w <;> simp [optIdx, optOff]; omega

/-- The core of `any_find_slice` and `find_internal` once the indices are
adjusted and the window is long enough: the first/last occurrence in the window,
shifted by `start`. -/
theorem searchCore_eq (s sub : Seq) (a b : Int) (fwd : Bool) (ha : 0 ≤ a) (hb : b ≤ s.length)
    (hab : sub.length ≤ b - a) :
    (if sub.length = 1 then
        (let r := findChar (window s a (b - a)) sub.head! fwd; if r = -1 then -1 else a + r)
      else if fwd then stringlibFind (window s a (b - a)) sub a
      else stringlibRFind (window s a (b - a)) sub a) =
    optOff a ((if fwd then findL else rfindL) sub (window s a (b - a))) := by
  have hw : (window s a (b - a)).length = (b - a).toNat := length_window ha (by omega) (by omega)
  have hl : sub.length ≤ (window s a (b - a)).length := by rw [hw]; omega
  by_cases h1 : sub.length = 1
  · rw [if_pos h1]
    obtain ⟨c, hc⟩ : ∃ c, sub = [c] := by
      match sub, h1 with
      | [c], _ => exact ⟨c, rfl⟩
    subst hc
    simp only [List.head!, findChar_eq]
    cases (if fwd then findL else rfindL) [c] (window s a (b - a)) with
    | none => simp [optIdx, optOff]
    | some r => simp [optIdx, optOff]
  · rw [if_neg h1]
    cases fwd
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact stringlibRFind_eq hl a
    · simp only [↓reduceIte]; exact stringlibFind_eq hl a

/-- `any_find_slice` by result. -/
theorem anyFindSlice_eq (s sub : Seq) (st en : Int) (fwd : Bool) :
    anyFindSlice s sub st en fwd =
      if kindOf s < kindOf sub ∨ (adjustIndices st en s.length).2 - (adjustIndices st en s.length).1 < sub.length
      then -1
      else optOff (adjustIndices st en s.length).1 ((if fwd then findL else rfindL) sub
        (window s (adjustIndices st en s.length).1
          ((adjustIndices st en s.length).2 - (adjustIndices st en s.length).1))) := by
  unfold anyFindSlice
  have ha := adjust_fst_nonneg st en s.length
  have hb := adjust_snd_le st en s.length (by omega)
  generalize adjustIndices st en s.length = ab at *
  obtain ⟨a, b⟩ := ab
  simp only at ha hb ⊢
  by_cases hk : kindOf s < kindOf sub
  · simp [hk]
  · by_cases hlt : b - a < sub.length
    · simp [hk, hlt]
    · simp only [hk, hlt, ↓reduceIte, or_self]
      exact searchCore_eq s sub a b fwd ha hb (by omega)

/-- `find_internal` by result (buffer argument). -/
theorem bytesFindInternal_eq (s sub : Seq) (st en : Int) (fwd : Bool) :
    bytesFindInternal s (.buf sub) st en fwd =
      .ok (if (adjustIndices st en s.length).2 - (adjustIndices st en s.length).1 < sub.length
      then -1
      else optOff (adjustIndices st en s.length).1 ((if fwd then findL else rfindL) sub
        (window s (adjustIndices st en s.length).1
          ((adjustIndices st en s.length).2 - (adjustIndices st en s.length).1)))) := by
  unfold bytesFindInternal
  have ha := adjust_fst_nonneg st en s.length
  have hb := adjust_snd_le st en s.length (by omega)
  generalize adjustIndices st en s.length = ab at *
  obtain ⟨a, b⟩ := ab
  simp only at ha hb ⊢
  simp only [parseFindsByte, bind, Except.bind, pure, Except.pure]
  by_cases hlt : b - a < sub.length
  · simp [hlt]
  · simp only [hlt, ↓reduceIte]
    rw [← searchCore_eq s sub a b fwd ha hb (by omega)]
    by_cases h1 : sub.length = 1
    · simp only [h1, ↓reduceIte, findChar_eq]
      cases (if fwd then findL else rfindL) [sub.head!] (window s a (b - a)) with
      | none => simp [optIdx]
      | some r => simp [optIdx]; omega
    · simp only [h1, ↓reduceIte]
      cases fwd <;> rfl

theorem optOff_cases {a : Int} (ha : 0 ≤ a) (o : Option Nat) : optOff a o = -1 ∨ 0 ≤ optOff a o := by
  cases o <;> simp [optOff]; omega

theorem anyFindSlice_cases (s sub : Seq) (st en : Int) (fwd : Bool) :
    anyFindSlice s sub st en fwd = -1 ∨ 0 ≤ anyFindSlice s sub st en fwd := by
  rw [anyFindSlice_eq]
  split
  · simp
  · exact optOff_cases (adjust_fst_nonneg st en s.length) _

theorem strFind_eq_any (s sub : Seq) (start «end» : Option Int) (fwd : Bool) :
    strFind s sub start «end» fwd = anyFindSlice s sub (argStart start) (argEnd «end») fwd := by
  unfold strFind
  rcases anyFindSlice_cases s sub (argStart start) (argEnd «end») fwd with h | h
  · simp [h]
  · simp only [show ¬ anyFindSlice s sub (argStart start) (argEnd «end») fwd < 0 by omega, ↓reduceIte]

theorem bytes_kind {s sub : Seq} (hs : ∀ x ∈ s, x < 256) (hsub : ∀ x ∈ sub, x < 256) :
    ¬ kindOf s < kindOf sub := by
  rw [kindOf_of_all hs, kindOf_of_all hsub]; omega

/-! ## str vs bytes -/

/-- `str` and `bytes` agree on `find`, `rfind`, `index`, `rindex` and `count`
for every argument, when both strings are byte-valued (latin-1 `str`, any
`bytes`); and `bytes` accepts an int `v` in `range(256)` exactly like `bytes([v])`. -/
def FindStrBytes : Prop :=
  ∀ (s sub : Seq) (start «end» : Option Int) (fwd : Bool),
    (∀ x ∈ s, x < 256) → (∀ x ∈ sub, x < 256) →
      bytesFind s (.buf sub) start «end» fwd = .ok (strFind s sub start «end» fwd) ∧
      (bytesIndex s (.buf sub) start «end» fwd).toOption = (strIndex s sub start «end» fwd).toOption ∧
      bytesCount s (.buf sub) start «end» = .ok (strCount s sub start «end») ∧
      ∀ v : Nat, v < 256 →
        bytesFind s (.byte v) start «end» fwd = bytesFind s (.buf [v]) start «end» fwd ∧
        bytesCount s (.byte v) start «end» = bytesCount s (.buf [v]) start «end»

theorem findStrBytes_proven : FindStrBytes := by
  intro s sub start «end» fwd hs hsub
  have hk := bytes_kind hs hsub
  have hfind : bytesFind s (.buf sub) start «end» fwd = .ok (strFind s sub start «end» fwd) := by
    rw [bytesFind, bytesFindInternal_eq, strFind_eq_any, anyFindSlice_eq]
    simp only [hk, false_or]
  refine ⟨hfind, ?_, ?_, ?_⟩
  · have hb : bytesFindInternal s (.buf sub) (argStart start) (argEnd «end») fwd =
        .ok (strFind s sub start «end» fwd) := hfind
    simp only [strIndex, bytesIndex, ← strFind_eq_any, hb, bind, Except.bind, pure, Except.pure]
    split <;> rfl
  · simp only [bytesCount, strCount, parseFindsByte, bind, Except.bind, pure, Except.pure, hk,
      ↓reduceIte]
    congr 1
    have ha := adjust_fst_nonneg (argStart start) (argEnd «end») s.length
    have hb := adjust_snd_le (argStart start) (argEnd «end») s.length (by omega)
    generalize adjustIndices (argStart start) (argEnd «end») s.length = ab at *
    obtain ⟨a, b⟩ := ab
    simp only at ha hb ⊢
    split
    · next hlt =>
      unfold stringlibCount
      split
      · rfl
      · have hp : sub.length ≠ 0 := by omega
        have hw : (window s a (b - a)).length < sub.length := by
          simp [window]; omega
        simp [hp, fastsearch, hw]
    · rfl
  · intro v hv
    have hv' : clampSsize (v : Int) = v := by unfold clampSsize ssizeMin ssizeMax; omega
    constructor
    · simp only [bytesFind, bytesFindInternal, parseFindsByte, hv']
      rw [if_neg (by omega)]
      simp
    · simp only [bytesCount, parseFindsByte, hv']
      rw [if_neg (by omega)]
      simp

/-! ## find within `[start, end)` -/

/-- `i` is an admissible answer of `find(sub, start, end)`: the match starts at
or after the normalised start and ends at or before the normalised end. -/
def InRange (s sub : Seq) (a b : Int) (i : Nat) : Prop :=
  a ≤ i ∧ (i : Int) + sub.length ≤ b ∧ Occ s sub i

/-- The occurrences of `sub` in the window are exactly the admissible ones. -/
theorem occ_window_iff {s sub : Seq} {a b : Int} (ha : 0 ≤ a) (hb : b ≤ s.length) (hab : a ≤ b) (r : Nat) :
    Occ (window s a (b - a)) sub r ↔ InRange s sub a b (a.toNat + r) := by
  rw [window, occ_window (by omega)]
  unfold InRange
  constructor
  · intro ⟨h1, h2⟩; exact ⟨by omega, by omega, h1⟩
  · intro ⟨h1, h2, h3⟩; exact ⟨h3, by omega⟩

/-- Every admissible index is `a + r` for an occurrence `r` in the window. -/
theorem inRange_shift {s sub : Seq} {a b : Int} {i : Nat} (ha : 0 ≤ a) (h : InRange s sub a b i) :
    i = a.toNat + (i - a.toNat) := by
  have := h.1; omega

/-- The `find`/`rfind` docstring, "the lowest (highest) index in S where
substring sub is found, such that sub is contained within S[start:end]", read
with `start`/`end` normalised by `ADJUST_INDICES` (the reading given in
python/cpython#68431): `find` returns the least admissible index and `rfind`
the greatest, or -1 when there is none. Holds for every `str` (any code
points) and every argument. -/
def FindExtreme : Prop :=
  ∀ (s sub : Seq) (start «end» : Option Int),
    let a := (adjustIndices (argStart start) (argEnd «end») s.length).1
    let b := (adjustIndices (argStart start) (argEnd «end») s.length).2
    ((strFind s sub start «end» true = -1 ∧ ∀ i, ¬ InRange s sub a b i) ∨
      ∃ i : Nat, strFind s sub start «end» true = i ∧ InRange s sub a b i ∧
        ∀ j, InRange s sub a b j → i ≤ j) ∧
    ((strFind s sub start «end» false = -1 ∧ ∀ i, ¬ InRange s sub a b i) ∨
      ∃ i : Nat, strFind s sub start «end» false = i ∧ InRange s sub a b i ∧
        ∀ j, InRange s sub a b j → j ≤ i)

theorem findExtreme_proven : FindExtreme := by
  intro s sub start «end»
  simp only [strFind_eq_any, anyFindSlice_eq]
  have ha := adjust_fst_nonneg (argStart start) (argEnd «end») s.length
  have hb := adjust_snd_le (argStart start) (argEnd «end») s.length (by omega)
  generalize adjustIndices (argStart start) (argEnd «end») s.length = ab at *
  obtain ⟨a, b⟩ := ab
  simp only at ha hb ⊢
  by_cases hk : kindOf s < kindOf sub
  · simp only [hk, true_or, ↓reduceIte, true_and]
    have : ∀ i, ¬ InRange s sub a b i := fun i h => not_occ_of_kind hk i h.2.2
    exact ⟨Or.inl this, Or.inl this⟩
  by_cases hlt : b - a < sub.length
  · simp only [hlt, or_true, ↓reduceIte, true_and]
    have : ∀ i, ¬ InRange s sub a b i := fun i h => by have := h.1; have := h.2.1; omega
    exact ⟨Or.inl this, Or.inl this⟩
  simp only [hk, hlt, or_self, ↓reduceIte, Bool.false_eq_true]
  have hab : a ≤ b := by omega
  constructor
  · have hc := findL_correct sub (window s a (b - a))
    cases hf : findL sub (window s a (b - a)) with
    | none =>
      rw [hf] at hc
      left; refine ⟨rfl, fun i hi => ?_⟩
      rw [inRange_shift ha hi, ← occ_window_iff ha hb hab] at hi
      exact hc _ hi
    | some r =>
      rw [hf] at hc
      right; refine ⟨a.toNat + r, by simp [optOff]; omega, (occ_window_iff ha hb hab r).mp hc.1, ?_⟩
      intro j hj
      have hj' := hj
      rw [inRange_shift ha hj, ← occ_window_iff ha hb hab] at hj'
      have hj1 := hj.1
      rcases Nat.lt_or_ge j (a.toNat + r) with hl | hl
      · exact absurd hj' (hc.2 (j - a.toNat) (by omega))
      · exact hl
  · have hc := rfindL_correct sub (window s a (b - a))
    cases hf : rfindL sub (window s a (b - a)) with
    | none =>
      rw [hf] at hc
      left; refine ⟨rfl, fun i hi => ?_⟩
      rw [inRange_shift ha hi, ← occ_window_iff ha hb hab] at hi
      exact hc _ hi
    | some r =>
      rw [hf] at hc
      right; refine ⟨a.toNat + r, by simp [optOff]; omega, (occ_window_iff ha hb hab r).mp hc.1, ?_⟩
      intro j hj
      have hj' := hj
      rw [inRange_shift ha hj, ← occ_window_iff ha hb hab] at hj'
      have hj1 := hj.1
      rcases Nat.lt_or_ge (a.toNat + r) j with hl | hl
      · exact absurd hj' (hc.2 (j - a.toNat) (by omega))
      · exact hl

/-- Python's slice bounds for step 1 (`slice(start, end).indices(len)`,
Objects/sliceobject.c `PySlice_AdjustIndices`): like `ADJUST_INDICES` but the
start is also clamped to `len`. -/
def sliceBounds (start «end» : Option Int) (len : Nat) : Int × Int :=
  let fix (x : Int) : Int := if x < 0 then max (x + len) 0 else min x len
  (fix (argStart start), fix (argEnd «end»))

/-- The literal reading of the docstrings of `find`, `count` and
`startswith` ("such that sub is contained within S[start:end]",
"occurrences ... in string S[start:end]", "With optional start, test S
beginning at that position"): each equals the same operation on the slice
`s[start:end]` (with `find`'s answer shifted by the slice start). -/
def FindSliceLiteral : Prop :=
  ∀ (s sub : Seq) (start «end» : Option Int),
    let a := (sliceBounds start «end» s.length).1
    let b := (sliceBounds start «end» s.length).2
    let t := window s a (b - a)
    strFind s sub start «end» = optOff a (findL sub t) ∧
    strCount s sub start «end» = strCount t sub none none ∧
    strStartswith s (.one sub) start «end» = strStartswith t (.one sub) none none

/-- `'abc'.find('', 4)` is -1 although `'abc'[4:]` is `''`, in which `''` is
found at index 0 (python/cpython#68431). -/
theorem findSliceLiteral_refuted : ¬ FindSliceLiteral := by
  intro h
  have := (h [97, 98, 99] [] (some 4) none).1
  revert this
  decide

/-! ## startswith / endswith -/

theorem matchAt_nil (s : Seq) (i : Int) : matchAt s [] i = true := by
  simp [matchAt, List.isPrefixOf]

theorem tailmatch_str_bytes (s sub : Seq) (st en : Int) (fwd : Bool) :
    strTailmatch s sub st en fwd = bytesTailmatch s sub st en fwd := by
  simp only [strTailmatch, bytesTailmatch]
  have ha := adjust_fst_nonneg st en s.length
  have hb := adjust_snd_le st en s.length (by omega)
  generalize adjustIndices st en s.length = ab at *
  obtain ⟨a, b⟩ := ab
  simp only at ha hb ⊢
  cases fwd <;> simp only [Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] <;>
    repeat' split
  all_goals first
    | rfl
    | omega
    | (have h0 : sub = [] := List.eq_nil_of_length_eq_zero (by omega)
       subst h0; simp [matchAt_nil])
    | (congr 1; omega)

/-- `str.startswith`/`endswith` (`tailmatch`, unicodeobject.c:9946-10007) and
`bytes.startswith`/`endswith` (`tailmatch`, bytes_methods.c:640-686) are
written differently but agree for every receiver, prefix or tuple of
prefixes, and `start`/`end`. -/
def TailmatchStrBytes : Prop :=
  ∀ (s : Seq) (a : Affix) (start «end» : Option Int),
    strStartswith s a start «end» = bytesStartswith s a start «end» ∧
    strEndswith s a start «end» = bytesEndswith s a start «end»

theorem tailmatchStrBytes_proven : TailmatchStrBytes := by
  intro s a start «end»
  simp [strStartswith, bytesStartswith, strEndswith, bytesEndswith, tailmatch_str_bytes]

/-! ## rfind on the reversed string -/

theorem rev_window (s : Seq) (n i : Nat) (h : i + n ≤ s.length) :
    (s.reverse.drop (s.length - n - i)).take n = ((s.drop i).take n).reverse := by
  rw [List.drop_reverse, List.take_reverse]
  simp only [List.length_take]
  have e1 : s.length - (s.length - n - i) = i + n := by omega
  rw [e1, show min (i + n) s.length - n = i by omega, List.drop_take]
  simp

theorem occ_reverse {s p : Seq} {i : Nat} (h : i + p.length ≤ s.length) :
    Occ s p i ↔ Occ s.reverse p.reverse (s.length - p.length - i) := by
  unfold Occ
  simp only [List.length_reverse]
  rw [rev_window s p.length i h, List.reverse_inj]
  constructor
  · intro ⟨_, h2⟩; exact ⟨by omega, h2⟩
  · intro ⟨_, h2⟩; exact ⟨h, h2⟩

theorem rfindL_reverse (p s : Seq) :
    rfindL p s = (findL p.reverse s.reverse).map (fun k => s.length - p.length - k) := by
  have hc := findL_correct p.reverse s.reverse
  cases hf : findL p.reverse s.reverse with
  | none =>
    rw [hf] at hc
    rw [Option.map_none, rfindL_eq_none]
    intro i hi
    have hl := hi.1
    exact hc _ ((occ_reverse hl).mp hi)
  | some k =>
    rw [hf] at hc
    have hk := hc.1.1
    simp only [List.length_reverse] at hk
    rw [Option.map_some, rfindL_eq_some]
    have e : s.length - p.length - (s.length - p.length - k) = k := by omega
    refine ⟨(occ_reverse (by omega)).mpr (by rw [e]; exact hc.1), fun j hj ho => ?_⟩
    have hl := ho.1
    exact hc.2 _ (by omega) ((occ_reverse hl).mp ho)

theorem kindOf_reverse (s : Seq) : kindOf s.reverse = kindOf s := by
  simp [kindOf, List.all_reverse]

theorem adjust_default (n : Nat) (h : (n : Int) ≤ ssizeMax) :
    adjustIndices (argStart none) (argEnd none) n = ((0 : Int), (n : Int)) := by
  simp only [adjustIndices, argStart, argEnd]
  apply Prod.ext <;> simp only [] <;> (repeat' split) <;> omega

theorem window_full (s : Seq) : window s 0 ((s.length : Int) - 0) = s := by
  simp [window]

theorem window_full' (s : Seq) : window s 0 (s.length : Int) = s := by
  simp [window]

/-- `s.rfind(sub)` is the mirror image of `s[::-1].find(sub[::-1])`:
`len(s) - len(sub) - r` when that finds `r`, and -1 otherwise
(`default_rfind` against `default_find`/two-way). Precondition: `len(s) ≤
sys.maxsize` (true of every `str`). -/
def RFindReverse : Prop :=
  ∀ (s sub : Seq), (s.length : Int) ≤ ssizeMax →
    strFind s sub none none false =
      (let r := strFind s.reverse sub.reverse none none true
       if r < 0 then -1 else s.length - sub.length - r)

theorem rfindReverse_proven : RFindReverse := by
  intro s sub hs
  have hs' : (s.reverse.length : Int) ≤ ssizeMax := by simpa using hs
  simp only [strFind_eq_any, anyFindSlice_eq, adjust_default _ hs,
    kindOf_reverse, List.length_reverse, window_full, Bool.false_eq_true, ↓reduceIte]
  have := window_full s.reverse
  simp only [List.length_reverse] at this
  rw [this, rfindL_reverse]
  have hc := findL_correct sub.reverse s.reverse
  cases hf : findL sub.reverse s.reverse with
  | none => simp [optOff]
  | some k =>
    rw [hf] at hc
    have hk' := hc.1.1
    simp only [List.length_reverse] at hk'
    simp only [Option.map_some, optOff]
    split <;> (try split) <;> omega

/-! ## count against repeated find -/

/-- `n = 0; i = start; while (j := s.find(sub, i, end)) >= 0: n += 1; i = j + len(sub)`,
with fuel (each round moves `i` forward by at least `len(sub) ≥ 1`). -/
def countByFind (s sub : Seq) (en : Option Int) : Nat → Option Int → Nat
  | 0, _ => 0
  | fuel + 1, i =>
    let j := strFind s sub i en
    if j < 0 then 0 else 1 + countByFind s sub en fuel (some (j + sub.length))

theorem adjust_snd_indep (st st' en len : Int) :
    (adjustIndices st en len).2 = (adjustIndices st' en len).2 := rfl

theorem adjust_fst_of_nonneg (st en len : Int) (h : 0 ≤ st) : (adjustIndices st en len).1 = st := by
  simp [adjustIndices]; omega

theorem argStart_le (start : Option Int) : argStart start ≤ ssizeMax := by
  cases start <;> simp [argStart, clampSsize, ssizeMax, ssizeMin] <;> omega

theorem adjust_fst_le (st en len : Int) (hst : st ≤ ssizeMax) (hl : len ≤ ssizeMax) (hl0 : 0 ≤ len) :
    (adjustIndices st en len).1 ≤ ssizeMax := by
  simp only [adjustIndices]; split <;> (try split) <;> omega

theorem argStart_some {i : Int} (h0 : 0 ≤ i) (h1 : i ≤ ssizeMax) : argStart (some i) = i := by
  simp [argStart, clampSsize, ssizeMin]; omega

theorem countAll_short {p w : Seq} (hp : p ≠ []) (h : w.length < p.length) : countAll p w = 0 := by
  apply countAll_none
  rw [findL_eq_none]; exact not_occ_of_long h

theorem window_drop (s : Seq) (i : Int) (b : Int) (k : Nat) (hi : 0 ≤ i) (hk : i + k ≤ b) :
    (window s i (b - i)).drop k = window s (i + k) (b - (i + k)) := by
  simp only [window, List.drop_take, List.drop_drop]
  congr 2 <;> omega

theorem stringlibCount_full {p w : Seq} {n : Int} (hp : p ≠ []) (hn : n = w.length)
    (hl : p.length ≤ w.length) (hM : (w.length : Int) < ssizeMax) :
    stringlibCount w n p ssizeMax = countAll p w := by
  have hpl : p.length ≠ 0 := by simpa using hp
  have hle := countAll_le hp w
  have hM' : ssizeMax ≠ 0 := by unfold ssizeMax; omega
  unfold stringlibCount fastsearch
  simp only [show ¬ n < 0 by omega, hpl, ↓reduceIte, show ¬ w.length < p.length by omega,
    hM', and_false, or_self]
  rw [if_neg (by omega)]
  omega

/-- The repeated-find loop from a non-negative start `i` counts the matches
in `s[i:b]`. -/
theorem countByFind_some (s sub : Seq) (en : Option Int) (hp : sub ≠ []) (hs : (s.length : Int) < ssizeMax)
    (hk : ¬ kindOf s < kindOf sub) :
    ∀ (fuel : Nat) (i : Nat), (i : Int) ≤ (adjustIndices 0 (argEnd en) s.length).2 →
      (adjustIndices 0 (argEnd en) s.length).2 - i < fuel →
      countByFind s sub en fuel (some i) =
        countAll sub (window s i ((adjustIndices 0 (argEnd en) s.length).2 - i)) := by
  have hb := adjust_snd_le 0 (argEnd en) s.length (by omega)
  generalize hB : (adjustIndices 0 (argEnd en) s.length).2 = b at hb
  have hpl : sub.length ≥ 1 := List.length_pos_iff.mpr hp
  intro fuel
  induction fuel with
  | zero => intro i hi hf; omega
  | succ fuel ih =>
    intro i hi hf
    have hfind : strFind s sub (some i) en true =
        if b - i < sub.length then -1 else optOff i (findL sub (window s i (b - i))) := by
      rw [strFind_eq_any, anyFindSlice_eq, argStart_some (by omega) (by omega),
        adjust_fst_of_nonneg _ _ _ (by omega), adjust_snd_indep (i : Int) 0, hB]
      simp only [hk, false_or, ↓reduceIte]
    simp only [countByFind]
    rw [hfind]
    by_cases hlt : b - i < sub.length
    · rw [if_pos hlt, countAll_short hp (by simp [window]; omega)]; simp
    · rw [if_neg hlt]
      have hc := findL_correct sub (window s i (b - i))
      cases hf' : findL sub (window s i (b - i)) with
      | none => rw [countAll_none hf']; simp [optOff]
      | some r =>
        rw [hf'] at hc
        have hr := hc.1.1
        simp only [window, List.length_take, List.length_drop] at hr
        simp only [optOff, show ¬ ((i : Int) + r < 0) by omega, ↓reduceIte]
        rw [countAll_some hp hf', window_drop s i b (r + sub.length) (by omega) (by omega)]
        have := ih (i + r + sub.length) (by omega) (by omega)
        rw [show ((i : Int) + r + sub.length) = ((i + r + sub.length : Nat) : Int) by omega, this]
        congr 3 <;> omega

/-- `s.count(sub, start, end)` equals the number of rounds of the loop
`i = start; while (j := s.find(sub, i, end)) >= 0: i = j + len(sub)` for a
non-empty `sub` (the docstring's "non-overlapping occurrences"), for every
`str` and every `start`/`end`. Precondition: `len(s) < sys.maxsize` (true of
every `str`). -/
def CountRepeatedFind : Prop :=
  ∀ (s sub : Seq) (start en : Option Int), sub ≠ [] → (s.length : Int) < ssizeMax →
    strCount s sub start en = countByFind s sub en (s.length + 1) start

theorem countRepeatedFind_proven : CountRepeatedFind := by
  intro s sub start en hp hs
  have hpl : sub.length ≥ 1 := List.length_pos_iff.mpr hp
  have ha := adjust_fst_nonneg (argStart start) (argEnd en) s.length
  have hb := adjust_snd_le (argStart start) (argEnd en) s.length (by omega)
  have haM := adjust_fst_le (argStart start) (argEnd en) s.length (argStart_le start) (by omega) (by omega)
  by_cases hk : kindOf s < kindOf sub
  · have : strFind s sub start en true = -1 := by
      rw [strFind_eq_any, anyFindSlice_eq]; simp [hk]
    simp [strCount, hk, countByFind, this]
  -- the first round of the loop sees the same indices as a loop started at `a`
  generalize hA : (adjustIndices (argStart start) (argEnd en) s.length).1 = a at ha haM
  have hfirst : strFind s sub start en true = strFind s sub (some a.toNat) en true := by
    rw [strFind_eq_any, strFind_eq_any, anyFindSlice_eq, anyFindSlice_eq,
      argStart_some (i := (a.toNat : Int)) (by omega) (by omega),
      adjust_fst_of_nonneg (a.toNat : Int) (argEnd en) s.length (by omega), hA,
      adjust_snd_indep (a.toNat : Int) (argStart start)]
    simp only [show ((a.toNat : Nat) : Int) = a by omega]
  have hloop : countByFind s sub en (s.length + 1) start =
      countByFind s sub en (s.length + 1) (some a.toNat) := by
    simp only [countByFind, hfirst]
  rw [hloop]
  have hB : (adjustIndices 0 (argEnd en) s.length).2 = (adjustIndices (argStart start) (argEnd en) s.length).2 :=
    adjust_snd_indep _ _ _ _
  generalize hb' : (adjustIndices (argStart start) (argEnd en) s.length).2 = b at hb hB
  have hcount : strCount s sub start en =
      if b - a < sub.length then 0 else countAll sub (window s a (b - a)) := by
    simp only [strCount, hk, ↓reduceIte, hA, hb']
    split
    · rfl
    · next hlt =>
      have hw : (window s a (b - a)).length = (b - a).toNat := length_window ha (by omega) (by omega)
      rw [stringlibCount_full hp (by rw [hw]; omega) (by rw [hw]; omega) (by rw [hw]; omega)]
  rw [hcount]
  by_cases hlt : b - a < sub.length
  · simp only [hlt, ↓reduceIte]
    have : strFind s sub (some a.toNat) en true = -1 := by
      rw [← hfirst, strFind_eq_any, anyFindSlice_eq, hA, hb']; simp [hlt]
    simp only [countByFind]; rw [this]; rfl
  · simp only [hlt, ↓reduceIte]
    have := countByFind_some s sub en hp hs hk (s.length + 1) a.toNat (by rw [hB]; omega)
      (by rw [hB]; omega)
    rw [this, hB, show ((a.toNat : Nat) : Int) = a by omega]

/-! ## partition against find -/

/-- The partition triple built from a `find`/`rfind` result. -/
def partitionOf (s sep : Seq) (i : Int) (left : Bool) : Seq × Seq × Seq :=
  if i < 0 then (if left then (s, [], []) else ([], [], s))
  else (s.take i.toNat, sep, s.drop (i.toNat + sep.length))

theorem strFind_whole (s sub : Seq) (fwd : Bool) (hs : (s.length : Int) ≤ ssizeMax) :
    strFind s sub none none fwd =
      if kindOf s < kindOf sub ∨ s.length < sub.length then -1
      else optIdx ((if fwd then findL else rfindL) sub s) := by
  rw [strFind_eq_any, anyFindSlice_eq, adjust_default _ hs]
  simp only [Int.sub_zero, window_full']
  by_cases h : kindOf s < kindOf sub ∨ s.length < sub.length
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]
    cases (if fwd then findL else rfindL) sub s <;> simp [optOff, optIdx]

/-- `s.partition(sep)` is `(s[:i], sep, s[i+len(sep):])` for `i = s.find(sep)`,
or `(s, '', '')` when `i == -1`; `rpartition` likewise with `rfind` and
`('', '', s)`; an empty `sep` raises `ValueError`. For `str` (any code points)
and `bytes`/`bytearray`. Precondition: `len(s) ≤ sys.maxsize`. -/
def PartitionFind : Prop :=
  ∀ (s sep : Seq), (s.length : Int) ≤ ssizeMax →
    (sep = [] → strPartition s sep = .error (.valueError "empty separator") ∧
       strRPartition s sep = .error (.valueError "empty separator") ∧
       bytesPartition s sep = .error (.valueError "empty separator") ∧
       bytesRPartition s sep = .error (.valueError "empty separator")) ∧
    (sep ≠ [] →
      strPartition s sep = .ok (partitionOf s sep (strFind s sep none none true) true) ∧
      strRPartition s sep = .ok (partitionOf s sep (strFind s sep none none false) false) ∧
      bytesPartition s sep = (bytesFind s (.buf sep) none none true).map (partitionOf s sep · true) ∧
      bytesRPartition s sep = (bytesFind s (.buf sep) none none false).map (partitionOf s sep · false))

theorem partition_core (s sep : Seq) (hp : sep ≠ []) (fwd : Bool) :
    (if fwd then stringlibPartition s sep else stringlibRPartition s sep) =
      .ok (partitionOf s sep (if s.length < sep.length then -1
        else optIdx ((if fwd then findL else rfindL) sep s)) fwd) := by
  have hl : sep.length ≠ 0 := by simpa using hp
  by_cases hlt : s.length < sep.length
  · have h1 : fastsearch s sep (-1) .search = -1 := by simp [fastsearch, hlt]
    have h2 : fastsearch s sep (-1) .rsearch = -1 := by simp [fastsearch, hlt]
    cases fwd <;> simp [stringlibPartition, stringlibRPartition, hl, h1, h2, hlt, partitionOf]
  · rw [if_neg hlt]
    cases fwd
    · simp only [Bool.false_eq_true, ↓reduceIte, stringlibRPartition, hl,
        fastsearch_rsearch (w := s) (p := sep) (by omega) hp, partitionOf]
      split <;> rfl
    · simp only [↓reduceIte, stringlibPartition, hl, fastsearch_search (w := s) (p := sep) (by omega) hp,
        partitionOf]
      split <;> rfl

theorem partitionFind_proven : PartitionFind := by
  intro s sep hs
  constructor
  · intro h; subst h
    have : kindOf ([] : Seq) = 1 := rfl
    have := kindOf_cases s
    simp [strPartition, strRPartition, bytesPartition, bytesRPartition, stringlibPartition,
      stringlibRPartition, *]
    omega
  · intro hp
    have hb : ∀ fwd, bytesFind s (.buf sep) none none fwd =
        .ok (if s.length < sep.length then -1 else optIdx ((if fwd then findL else rfindL) sep s)) := by
      intro fwd
      rw [bytesFind, bytesFindInternal_eq, adjust_default _ hs]
      simp only [Int.sub_zero, window_full']
      by_cases h : s.length < sep.length
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h]
        cases (if fwd then findL else rfindL) sep s <;> simp [optOff, optIdx]
    have pc := partition_core s sep hp
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [strFind_whole _ _ _ hs, strPartition]
      by_cases hk : kindOf s < kindOf sep ∨ s.length < sep.length
      · rw [if_pos hk, if_pos hk]; simp [partitionOf]
      · rw [if_neg hk, if_neg hk]
        have := pc true; simp only [↓reduceIte] at this; rw [this]
        congr 2; rw [if_neg (by omega)]; rfl
    · rw [strFind_whole _ _ _ hs, strRPartition]
      by_cases hk : kindOf s < kindOf sep ∨ s.length < sep.length
      · rw [if_pos hk, if_pos hk]; simp [partitionOf]
      · rw [if_neg hk, if_neg hk]
        have := pc false; simp only [Bool.false_eq_true, ↓reduceIte] at this; rw [this]
        congr 2; rw [if_neg (by omega)]; rfl
    · rw [hb, bytesPartition]; have := pc true; simp only [↓reduceIte] at this; rw [this]; rfl
    · rw [hb, bytesRPartition]; have := pc false; simp only [Bool.false_eq_true, ↓reduceIte] at this
      rw [this]; rfl

end PyLean.StrSearch
