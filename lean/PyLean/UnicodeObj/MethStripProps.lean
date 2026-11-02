import PyLean.UnicodeObj.MethStrip
import PyLean.UnicodeObj.MethCase

/-!
Properties of `str.strip` and its helpers.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## `PyUnicode_FindChar` against its documentation -/

/-- The C API documentation of `PyUnicode_FindChar`: "Return the first position of the
character ch in unicode[start:end] using the given direction (direction == 1 means to do a
forward search, direction == -1 a backward search) ... -1 indicates that no match was found".
`unicode[start:end]` is Python's slice, and the position counts from the start of `unicode`. -/
def findCharDoc (str : Str) (ch : Nat) (start «end» : Int) (direction : Int) : Int :=
  let a := clipIndex str.length start
  let b := clipIndex str.length «end»
  let w := (str.drop a).take (b - a)
  let r := if direction > 0 then findUnit w ch else rfindUnit w ch
  if r = -1 then -1 else a + r

/-- For every string and every `Py_UCS4` (a 32-bit value), every `start`, `end` and direction,
`PyUnicode_FindChar` returns the documented position. In particular the casts of `findchar` to
the string's unit type never turn a character the string does not contain into one it does
(`'Ł'` against a Latin-1 string holding `'A'`). Type invariants: `Str.Valid str`,
`ch < 2**32`. -/
def FindCharDoc : Prop :=
  ∀ (str : Str) (ch : Nat) (start «end» direction : Int), Str.Valid str → ch < 2 ^ 32 →
    pyUnicodeFindChar str ch start «end» direction = findCharDoc str ch start «end» direction

theorem mem_lt_kindWidth {s : Str} (hs : Str.Valid s) {x : Nat} (hx : x ∈ s) :
    x < 2 ^ (8 * kindWidth s) := by
  have hle : x ≤ maxCharOf s := (le_foldl_max s 0).2 x hx
  have hv := hs x hx
  unfold maxUnicode at hv
  unfold kindWidth canonicalKind kindOfMax
  by_cases h1 : maxCharOf s < 128
  · rw [if_pos h1]; simp only [Kind.width]; omega
  · rw [if_neg h1]
    by_cases h2 : maxCharOf s < 256
    · rw [if_pos h2]; simp only [Kind.width]; omega
    · rw [if_neg h2]
      by_cases h3 : maxCharOf s < 65536
      · rw [if_pos h3]; simp only [Kind.width]; omega
      · rw [if_neg h3]; simp only [Kind.width]; omega

theorem findUnit_none {units : List Nat} {u : Nat} (h : u ∉ units) : findUnit units u = -1 := by
  unfold findUnit
  have : units.findIdx? (· == u) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    rw [beq_eq_false_iff_ne]; rintro rfl; exact h hx
  rw [this]

theorem rfindUnit_none {units : List Nat} {u : Nat} (h : u ∉ units) : rfindUnit units u = -1 := by
  unfold rfindUnit
  have : units.reverse.findIdx? (· == u) = none := by
    rw [List.findIdx?_eq_none_iff]
    intro x hx
    rw [beq_eq_false_iff_ne]; rintro rfl; exact h (List.mem_reverse.1 hx)
  rw [this]

theorem kindWidth_cases (s : Str) : kindWidth s = 1 ∨ kindWidth s = 2 ∨ kindWidth s = 4 := by
  unfold kindWidth
  cases canonicalKind s <;> simp [Kind.width]

/-- The cast in `findchar` is harmless when every unit fits the width. -/
theorem findchar_exact (units : List Nat) (width ch : Nat) (dir : Int)
    (hw : width = 1 ∨ width = 2 ∨ width = 4) (hu : ∀ x ∈ units, x < 2 ^ (8 * width))
    (hch : ch < 2 ^ 32) :
    findchar units width ch dir = if dir > 0 then findUnit units ch else rfindUnit units ch := by
  unfold findchar
  by_cases hfit : ch < 2 ^ (8 * width)
  · have e : ch % 2 ^ (8 * width) = ch := Nat.mod_eq_of_lt hfit
    simp only [e, ne_eq, not_true_eq_false, and_false, if_false]
  · have hn : ch ∉ units := fun hm => hfit (hu ch hm)
    have h4 : width ≠ 4 := by rintro rfl; exact hfit hch
    have hne : ch % 2 ^ (8 * width) ≠ ch := by
      intro e; apply hfit; rw [← e]; exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by simp))
    rw [if_pos ⟨h4, hne⟩]
    split
    · exact (findUnit_none hn).symm
    · exact (rfindUnit_none hn).symm

theorem adjust_facts (start e : Int) (n : Nat) :
    (clipIndex n e : Int) = (StrSearch.adjustIndices start e n).2 ∧
    0 ≤ (StrSearch.adjustIndices start e n).2 ∧ (StrSearch.adjustIndices start e n).2 ≤ n ∧
    0 ≤ (StrSearch.adjustIndices start e n).1 ∧
    (clipIndex n start : Int) = min (StrSearch.adjustIndices start e n).1 n := by
  simp only [StrSearch.adjustIndices, clipIndex]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> repeat' split
  all_goals omega

theorem findCharDoc_proven : FindCharDoc := by
  intro str ch start e dir hs hch
  obtain ⟨hb, he0, hen, hs0, ha⟩ := adjust_facts start e str.length
  unfold pyUnicodeFindChar findCharDoc
  generalize StrSearch.adjustIndices start e str.length = p at *
  obtain ⟨s', e'⟩ := p
  simp only at hb he0 hen hs0 ha ⊢
  generalize clipIndex str.length start = a at *
  generalize clipIndex str.length e = b at *
  by_cases hlt : e' - s' < 1
  · rw [if_pos hlt]
    have hw : (str.drop a).take (b - a) = [] := by
      apply List.eq_nil_of_length_eq_zero; simp; omega
    rw [hw]
    simp [findUnit, rfindUnit]
  · rw [if_neg hlt]
    have ha' : (a : Int) = s' := by omega
    have hwin : StrSearch.window str s' (e' - s') = (str.drop a).take (b - a) := by
      unfold StrSearch.window; congr 2 <;> omega
    rw [hwin, findchar_exact _ _ _ _ (kindWidth_cases str)
      (fun x hx => mem_lt_kindWidth hs (List.mem_of_mem_drop (List.mem_of_mem_take hx))) hch, ha']

/-! ## `strip` against its documentation -/

/-- The documented result: "Return a copy of the string with the leading and trailing
characters removed. The chars argument is a string specifying the set of characters to be
removed. If omitted or None, the chars argument defaults to removing whitespace. The chars
argument is not a prefix or suffix; rather, all combinations of its values are stripped";
`lstrip` removes only leading and `rstrip` only trailing ones. -/
def stripSpec (p : Nat → Bool) (st : StripKind) (s : Str) : Str :=
  let s1 := if st = .right then s else s.dropWhile p
  if st = .left then s1 else (s1.reverse.dropWhile p).reverse

/-- For every string and each of `strip`, `lstrip`, `rstrip`: with a `str` argument the result
removes exactly the leading and/or trailing characters that belong to it; with `None` (or no
argument) exactly the leading and/or trailing whitespace, as `str.isspace` defines it, in
either representation of `self`; any other argument raises `TypeError` naming the method.
Type invariants: `Str.Valid s`, `Str.Valid chars`. -/
def StripDoc : Prop :=
  ∀ (s : Str) (st : StripKind), Str.Valid s →
    (∀ chars : Str, Str.Valid chars →
      doArgstrip s st (.str chars) = .ok (stripSpec (fun c => decide (c ∈ chars)) st s)) ∧
    doArgstrip s st .none = .ok (stripSpec (fun c => unicodeIsSpace [c]) st s) ∧
    (∀ a : Arg, a ≠ .none → (∀ t, a ≠ .str t) →
      doArgstrip s st a = .error (.typeError s!"{st.name} arg must be None or str"))

theorem leftScan_eq (p : Nat → Bool) (s : Str) : ∀ k i, s.length - i = k → i ≤ s.length →
    leftScan p s i = i + ((s.drop i).takeWhile p).length := by
  intro k
  induction k with
  | zero =>
    intro i h hi
    have e : i = s.length := by omega
    subst e
    rw [leftScan]; simp
  | succ k ih =>
    intro i h hi
    have hlt : i < s.length := by omega
    rw [leftScan, if_pos hlt, getD_drop_cons s i hlt, List.takeWhile_cons]
    split
    · next hp => rw [ih (i + 1) (by omega) (by omega)]; simp; omega
    · next hp => simp

theorem rightScan_eq (p : Nat → Bool) (s : Str) (i : Nat) : ∀ m, i ≤ m → m ≤ s.length →
    rightScan p s i ((m : Int) - 1) + 1 = i + (((s.take m).drop i).reverse.dropWhile p).length := by
  intro m
  induction m with
  | zero =>
    intro h1 h2
    have e : i = 0 := by omega
    subst e
    rw [rightScan, if_neg (by omega)]; simp
  | succ m ih =>
    intro h1 h2
    by_cases hm : i = m + 1
    · subst hm
      rw [rightScan, if_neg (by omega)]
      simp
    · have him : i ≤ m := by omega
      have hlt : m < s.length := by omega
      have e1 : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by omega
      rw [e1, rightScan, if_pos (by omega)]
      have hseg : (s.take (m + 1)).drop i = (s.take m).drop i ++ [s.getD m 0] := by
        rw [getD_eq_of_lt s m hlt, List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.drop_append_of_le_length (by simp; omega)]
      have e2 : (m : Int).toNat = m := by simp
      rw [hseg, List.reverse_append, e2]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
        List.dropWhile_cons]
      split
      · exact ih him (by omega)
      · simp; omega

theorem substring_ok (s : Str) (i j : Nat) (hij : i ≤ j) (hj : j ≤ s.length) :
    pyUnicodeSubstring s i j = .ok ((s.drop i).take (j - i)) := by
  unfold pyUnicodeSubstring
  have em : min (j : Int) s.length = j := by omega
  simp only [em]
  by_cases h0 : (i : Int) = 0 ∧ (j : Int) = s.length
  · rw [if_pos h0]
    have hi : i = 0 := by omega
    have hj' : j = s.length := by omega
    subst hi; subst hj'
    simp
  · rw [if_neg h0, if_neg (by omega)]
    by_cases h1 : (i : Int) ≥ s.length ∨ (j : Int) < i
    · rw [if_pos h1]
      have : j - i = 0 ∨ s.length ≤ i := by omega
      rcases this with h | h
      · rw [h]; simp
      · rw [List.drop_eq_nil_of_le h]; simp
    · rw [if_neg h1]
      have e3 : (i : Int).toNat = i := by simp
      have e4 : ((j : Int) - i).toNat = j - i := by omega
      rw [e3, e4]

theorem drop_takeWhile_length (p : Nat → Bool) (s : Str) :
    s.drop (s.takeWhile p).length = s.dropWhile p := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := s)
  calc s.drop (s.takeWhile p).length
      = (s.takeWhile p ++ s.dropWhile p).drop (s.takeWhile p).length := by rw [h]
    _ = s.dropWhile p := List.drop_left

theorem takeWhile_length_le (p : Nat → Bool) (s : Str) : (s.takeWhile p).length ≤ s.length := by
  have := congrArg List.length (List.takeWhile_append_dropWhile (p := p) (l := s))
  simp only [List.length_append] at this
  omega

theorem mem_of_mem_dropWhile' {p : Nat → Bool} {s : Str} {c : Nat} (hc : c ∈ s.dropWhile p) :
    c ∈ s := by
  rw [← List.takeWhile_append_dropWhile (p := p) (l := s)]
  exact List.mem_append_right _ hc

theorem rev_dropWhile_rev (p : Nat → Bool) (t : Str) :
    (t.reverse.dropWhile p).reverse = t.take (t.reverse.dropWhile p).length := by
  have h := List.takeWhile_append_dropWhile (p := p) (l := t.reverse)
  have ht : t = (t.reverse.dropWhile p).reverse ++ (t.reverse.takeWhile p).reverse := by
    rw [← List.reverse_append, h, List.reverse_reverse]
  conv => rhs; rw [ht]
  rw [List.take_left' (by simp)]

theorem leftScan_spec (p : Nat → Bool) (s : Str) :
    leftScan p s 0 ≤ s.length ∧ s.drop (leftScan p s 0) = s.dropWhile p := by
  rw [leftScan_eq p s s.length 0 (by omega) (by omega)]
  simp only [Nat.zero_add, List.drop_zero]
  exact ⟨takeWhile_length_le p s, drop_takeWhile_length p s⟩

theorem substring_to_end (s : Str) (i : Nat) (hi : i ≤ s.length) :
    pyUnicodeSubstring s i s.length = .ok (s.drop i) := by
  rw [substring_ok s i s.length hi (Nat.le_refl _), List.take_of_length_le (by simp)]

theorem substring_right (p : Nat → Bool) (s : Str) (i : Nat) (hi : i ≤ s.length) :
    pyUnicodeSubstring s i (rightScan p s i ((s.length : Int) - 1) + 1) =
      .ok (((s.drop i).reverse.dropWhile p).reverse) := by
  have hr := rightScan_eq p s i s.length hi (Nat.le_refl _)
  rw [List.take_of_length_le (Nat.le_refl _)] at hr
  have hL : ((s.drop i).reverse.dropWhile p).length ≤ s.length - i := by
    have := congrArg List.length
      (List.takeWhile_append_dropWhile (p := p) (l := (s.drop i).reverse))
    simp only [List.length_append, List.length_reverse, List.length_drop] at this
    omega
  rw [hr]
  have e : ((i + ((s.drop i).reverse.dropWhile p).length : Nat) : Int) =
      (i : Int) + (((s.drop i).reverse.dropWhile p).length : Int) := by omega
  rw [← e, substring_ok s i _ (by omega) (by omega), rev_dropWhile_rev p (s.drop i)]
  congr 2
  omega

theorem stripWith_spec (p : Nat → Bool) (st : StripKind) (s : Str) :
    stripWith p st s = .ok (stripSpec p st s) := by
  obtain ⟨hl, hd⟩ := leftScan_spec p s
  cases st with
  | left =>
    simp only [stripWith, stripSpec, ne_eq, reduceCtorEq, not_false_eq_true, if_true,
      not_true_eq_false, if_false]
    rw [substring_to_end s _ hl, hd]
  | right =>
    simp only [stripWith, stripSpec, ne_eq, reduceCtorEq, not_false_eq_true, if_true,
      not_true_eq_false, if_false]
    have := substring_right p s 0 (Nat.zero_le _)
    simpa using this
  | both =>
    simp only [stripWith, stripSpec, ne_eq, reduceCtorEq, not_false_eq_true, if_true, if_false]
    rw [substring_right p s _ hl, hd]

theorem dropWhile_congr (p q : Nat → Bool) (l : List Nat) (h : ∀ c ∈ l, p c = q c) :
    l.dropWhile p = l.dropWhile q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.dropWhile_cons, h x List.mem_cons_self]
    rw [ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem stripSpec_congr (p q : Nat → Bool) (st : StripKind) (s : Str) (h : ∀ c ∈ s, p c = q c) :
    stripSpec p st s = stripSpec q st s := by
  have h1 : s.dropWhile p = s.dropWhile q := dropWhile_congr p q s h
  cases st with
  | left =>
    simp only [stripSpec, reduceCtorEq, if_true, if_false]
    exact h1
  | right =>
    simp only [stripSpec, reduceCtorEq, if_true, if_false]
    rw [dropWhile_congr p q _ (fun c hc => h c (List.mem_reverse.1 hc))]
  | both =>
    simp only [stripSpec, reduceCtorEq, if_false]
    rw [h1, dropWhile_congr p q _ (fun c hc => h c (mem_of_mem_dropWhile' (List.mem_reverse.1 hc)))]

theorem xstrip_pred (sep : Str) (hsep : Str.Valid sep) (c : Nat) (hc : c ≤ maxUnicode) :
    (bloom (makeBloomMask sep) c && decide (pyUnicodeFindChar sep c 0 sep.length 1 ≥ 0)) =
      decide (c ∈ sep) := by
  have hc32 : c < 2 ^ 32 := by unfold maxUnicode at hc; omega
  rw [findCharDoc_proven sep c 0 sep.length 1 hsep hc32]
  unfold findCharDoc clipIndex
  have e0 : (if (0 : Int) < 0 then (max 0 ((0 : Int) + sep.length)).toNat
      else (min (0 : Int) sep.length).toNat) = 0 := by split <;> omega
  have e1 : (if (sep.length : Int) < 0 then (max 0 ((sep.length : Int) + sep.length)).toNat
      else (min (sep.length : Int) sep.length).toNat) = sep.length := by split <;> omega
  simp only [e0, e1, Nat.sub_zero, List.drop_zero, List.take_length,
    show (1 : Int) > 0 by omega, if_true]
  by_cases hm : c ∈ sep
  · have hb := bloomSuperset_proven sep c hm
    have hs : (sep.findIdx? (· == c)).isSome := by
      rw [List.findIdx?_isSome]; simp [List.any_eq_true]; exact hm
    obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hs
    simp [hb, hm, findUnit, hk]
  · simp [hm, findUnit_none hm]

theorem stripDoc_proven : StripDoc := by
  intro s st hs
  refine ⟨?_, ?_, ?_⟩
  · intro chars hchars
    simp only [doArgstrip, xstrip, stripWith_spec]
    rw [stripSpec_congr _ _ st s (fun c hc => xstrip_pred chars hchars c (hs c hc))]
  · simp only [doArgstrip, doStrip]
    split
    · next ha =>
      rw [stripWith_spec]
      congr 1
      apply stripSpec_congr
      intro c hc
      have h := mem_ascii ha hc
      show asciiWhitespaceTable c = isSpace c
      unfold isSpace asciiWhitespaceTable
      rw [if_pos h]
    · rw [stripWith_spec]
      rfl
  · intro a hn hs'
    cases a with
    | none => exact absurd rfl hn
    | str t => exact absurd rfl (hs' t)
    | _ => rfl

end PyLean.UnicodeObj
