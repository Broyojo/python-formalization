import PyLean.Accel.Select
import PyLean.Accel.BisectProps
import PyLean.Accel.HeapProps
import PyLean.Accel.Selection

/-!
`nsmallest`, `nlargest` and `merge` against the "equivalent" `sorted(...)`
expressions their docs give.
-/

namespace PyLean.Accel

open PyLean

/-- Sorted by key in descending order. -/
def SortedRevBy (key : Option (Int → Int)) (a : List Int) : Prop :=
  a.Pairwise (fun u v => applyKey key v ≤ applyKey key u)

/-- `nsmallest` docstring, Lib/heapq.py:477-481 and Doc/library/heapq.rst:188-193:
"Equivalent to: `sorted(iterable, key=key)[:n]`", for every count `n >= 0`
(negative `n` has no meaning, python/cpython#57483), sized or not, with or
without key, including the order of items with equal keys. -/
def NsmallestIsSortedPrefix : Prop :=
  ∀ (n : Int) (it : List Int) (sized : Bool) (key : Option (Int → Int)), 0 ≤ n →
    nsmallest n it sized key = .ok (sliceTo (pySorted key it) n)

/-- `nlargest` docstring, Lib/heapq.py:537-541 and Doc/library/heapq.rst:179-185:
"Equivalent to: `sorted(iterable, key=key, reverse=True)[:n]`", for `n >= 0`. -/
def NlargestIsSortedPrefix : Prop :=
  ∀ (n : Int) (it : List Int) (sized : Bool) (key : Option (Int → Int)), 0 ≤ n →
    nlargest n it sized key = .ok (sliceTo (pySortedRev key it) n)

/-- `merge` docstring, Lib/heapq.py:330-346 and Doc/library/heapq.rst:154-176:
for inputs each sorted by key (descending when `reverse=True`), the output is
`sorted(itertools.chain(*iterables), key=key, reverse=reverse)`, ties included. -/
def MergeIsSorted : Prop :=
  ∀ (its : List (List Int)) (key : Option (Int → Int)) (reverse : Bool),
    (∀ it ∈ its, if reverse then SortedRevBy key it else SortedBy key it) →
    merge its key reverse =
      .ok (if reverse then pySortedRev key its.flatten else pySorted key its.flatten)

/-! ### The tuple orders -/

theorem strictWeak_lt2 : StrictWeak lt2 where
  irrefl a := by simp [lt2]
  trans a b c h1 h2 := by simp [lt2] at *; omega
  negTrans a b c h := by simp [lt2] at *; omega

theorem strictWeak_lt3 : StrictWeak lt3 where
  irrefl a := by simp [lt3, lt2]
  trans a b c h1 h2 := by simp [lt3, lt2] at *; omega
  negTrans a b c h := by simp [lt3, lt2] at *; omega

/-! ### The four decorations as instances of the generic selection -/

/-- `nsmallest`, `key=None`: `(elem, order)`. -/
def selS1 : SelSpec (Int × Int) where
  lt := lt2
  dec e o := (e, o)
  eOf t := t.1
  topOf t := t.1
  kf := applyKey none
  tagf o := o
  ostep o := o + 1
  ord0 i := i

/-- `nsmallest` with a key: `(key(elem), order, elem)`. -/
def selS2 (f : Int → Int) : SelSpec (Int × Int × Int) where
  lt := lt3
  dec e o := (f e, o, e)
  eOf t := t.2.2
  topOf t := t.1
  kf := applyKey (some f)
  tagf o := o
  ostep o := o + 1
  ord0 i := i

/-- `nlargest`, `key=None`: `(elem, order)` in a min-heap, orders `0, -1, ...`. -/
def selS3 : SelSpec (Int × Int) where
  lt := maxLt lt2
  dec e o := (e, o)
  eOf t := t.1
  topOf t := -t.1
  kf e := -applyKey none e
  tagf o := -o
  ostep o := o - 1
  ord0 i := -(i : Int)

/-- `nlargest` with a key. -/
def selS4 (f : Int → Int) : SelSpec (Int × Int × Int) where
  lt := maxLt lt3
  dec e o := (f e, o, e)
  eOf t := t.2.2
  topOf t := -t.1
  kf e := -applyKey (some f) e
  tagf o := -o
  ostep o := o - 1
  ord0 i := -(i : Int)

theorem selS1_good : selS1.Good where
  sw := strictWeak_lt2
  eOf_dec _ _ := rfl
  topOf_dec _ _ := rfl
  lt_dec e e' o o' _ := by
    show lt2 (e, o) (e', o') = decide (e < e' ∨ (e = e' ∧ o < o'))
    simp only [lt2]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
  lt_key e e' o o' h := by
    simp only [selS1, applyKey] at h
    simp only [selS1, lt2]; simp; omega
  tag_step _ := rfl
  tag_ord0 _ := rfl

theorem selS2_good (f : Int → Int) : (selS2 f).Good where
  sw := strictWeak_lt3
  eOf_dec _ _ := rfl
  topOf_dec _ _ := rfl
  lt_dec e e' o o' h := by
    have h' : o ≠ o' := h
    show lt3 (f e, o, e) (f e', o', e') = decide (f e < f e' ∨ (f e = f e' ∧ o < o'))
    simp only [lt3, lt2]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
    omega
  lt_key e e' o o' h := by
    simp only [selS2, applyKey] at h
    simp only [selS2, lt3, lt2]; simp; omega
  tag_step _ := rfl
  tag_ord0 _ := rfl

theorem selS3_good : selS3.Good where
  sw := strictWeak_lt2.maxLt
  eOf_dec _ _ := rfl
  topOf_dec _ _ := rfl
  lt_dec e e' o o' _ := by
    show maxLt lt2 (e, o) (e', o') = decide (-e < -e' ∨ (-e = -e' ∧ -o < -o'))
    simp only [maxLt, lt2]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
    omega
  lt_key e e' o o' h := by
    simp only [selS3, applyKey] at h
    simp only [selS3, maxLt, lt2]; simp; omega
  tag_step o := by simp [selS3]; omega
  tag_ord0 _ := by simp [selS3]

theorem selS4_good (f : Int → Int) : (selS4 f).Good where
  sw := strictWeak_lt3.maxLt
  eOf_dec _ _ := rfl
  topOf_dec _ _ := rfl
  lt_dec e e' o o' h := by
    have h' : -o ≠ -o' := h
    show maxLt lt3 (f e, o, e) (f e', o', e') = decide (-f e < -f e' ∨ (-f e = -f e' ∧ -o < -o'))
    simp only [maxLt, lt3, lt2]
    rw [Bool.eq_iff_iff]
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
    omega
  lt_key e e' o o' h := by
    simp only [selS4, applyKey] at h
    simp only [selS4, maxLt, lt3, lt2]; simp; omega
  tag_step o := by simp [selS4]; omega
  tag_ord0 _ := by simp [selS4]

theorem nsmallestLoop_eq : ∀ (rest : List Int) (result : List (Int × Int)) (top order : Int),
    nsmallestLoop result top order rest = selLoop selS1 result top order rest
  | [], _, _, _ => rfl
  | e :: rest, result, top, order => by
    simp only [nsmallestLoop, selLoop, nsmallestLoop_eq rest]
    rfl

theorem nsmallestKeyLoop_eq (f : Int → Int) : ∀ (rest : List Int) (result : List (Int × Int × Int))
    (top order : Int), nsmallestKeyLoop f result top order rest = selLoop (selS2 f) result top order rest
  | [], _, _, _ => rfl
  | e :: rest, result, top, order => by
    simp only [nsmallestKeyLoop, selLoop, nsmallestKeyLoop_eq f rest]
    rfl

theorem nlargestLoop_eq : ∀ (rest : List Int) (result : List (Int × Int)) (top order : Int),
    nlargestLoop result top order rest = selLoop selS3 result (-top) order rest
  | [], _, _, _ => rfl
  | e :: rest, result, top, order => by
    simp only [nlargestLoop, selLoop, nlargestLoop_eq rest]
    have : (top < e) = (selS3.kf e < -top) := by
      simp only [selS3, applyKey]; apply propext; omega
    simp only [this]
    rfl

theorem nlargestKeyLoop_eq (f : Int → Int) : ∀ (rest : List Int) (result : List (Int × Int × Int))
    (top order : Int), nlargestKeyLoop f result top order rest = selLoop (selS4 f) result (-top) order rest
  | [], _, _, _ => rfl
  | e :: rest, result, top, order => by
    simp only [nlargestKeyLoop, selLoop, nlargestKeyLoop_eq f rest]
    have : (top < f e) = ((selS4 f).kf e < -top) := by
      simp only [selS4, applyKey]; apply propext; omega
    simp only [this]
    rfl

/-! ### min/max -/

theorem foldl_minmax (better : Int → Int → Bool) (key : Option (Int → Int)) (kf : Int → Int)
    (hb : ∀ a b, better (applyKey key a) (applyKey key b) = decide (kf a < kf b)) :
    ∀ (xs P : List Int) (best : Int), (stableSort kf P).head? = some best →
      some (xs.foldl (fun best y => if better (applyKey key y) (applyKey key best) then y else best) best) =
        (stableSort kf (P ++ xs)).head?
  | [], P, best, h => by simp [h]
  | y :: xs, P, best, h => by
    simp only [List.foldl_cons]
    rw [show P ++ y :: xs = (P ++ [y]) ++ xs by simp]
    apply foldl_minmax better key kf hb xs
    rw [stableSort_append_single]
    obtain ⟨rest, hr⟩ : ∃ rest, stableSort kf P = best :: rest := by
      cases hs : stableSort kf P with
      | nil => rw [hs] at h; cases h
      | cons b rest => rw [hs] at h; cases h; exact ⟨rest, rfl⟩
    rw [hr, hb]
    simp only [insS]
    by_cases hk : kf best ≤ kf y
    · rw [if_pos hk, if_neg (by simp; omega)]; rfl
    · rw [if_neg hk, if_pos (by simp; omega)]; rfl

theorem pyMinMax_eq (better : Int → Int → Bool) (key : Option (Int → Int)) (kf : Int → Int)
    (hb : ∀ a b, better (applyKey key a) (applyKey key b) = decide (kf a < kf b)) (it : List Int) :
    pyMinMax better key it = (stableSort kf it).head? := by
  cases it with
  | nil => simp [pyMinMax, stableSort_nil]
  | cons x xs =>
    simp only [pyMinMax]
    have := foldl_minmax better key kf hb xs [x] x (by simp [stableSort_single])
    simpa using this

theorem take_one_head (l : List Int) :
    (match l.head? with | none => [] | some r => [r]) = l.take 1 := by
  cases l <;> rfl

theorem sliceTo_nonneg {γ : Type} (l : List γ) (n : Int) (h : 0 ≤ n) : sliceTo l n = l.take n.toNat := by
  simp [sliceTo, h]

theorem pySortedRev_eq (key : Option (Int → Int)) (l : List Int) :
    pySortedRev key l = stableSort (fun e => -applyKey key e) l := by
  simp only [pySortedRev, stableSort]
  congr 1
  funext a b
  apply decide_eq_decide.2; omega

theorem nsmallestIsSortedPrefix_proven : NsmallestIsSortedPrefix := by
  intro n it sized key hn
  have hsl := sliceTo_nonneg (pySorted key it) n hn
  simp only [nsmallest]
  by_cases h1 : n = 1
  · subst h1
    simp only [if_true, pure, Except.pure]
    rw [pyMinMax_eq _ key (applyKey key) (fun a b => rfl), hsl]
    exact congrArg Except.ok (take_one_head _)
  · rw [if_neg h1]
    by_cases h2 : sized = true ∧ n ≥ it.length
    · rw [if_pos h2]; rfl
    · rw [if_neg h2, hsl]
      cases key with
      | none =>
        have := selAlgo_spec selS1_good n.toNat n (by simp [selS1]; omega) it
        simp only [selAlgo, selS1] at this
        simp only [nsmallestLoop_eq]
        exact this
      | some f =>
        have := selAlgo_spec (selS2_good f) n.toNat n (by simp [selS2]; omega) it
        simp only [selAlgo, selS2] at this
        simp only [nsmallestKeyLoop_eq]
        exact this

theorem nlargestIsSortedPrefix_proven : NlargestIsSortedPrefix := by
  intro n it sized key hn
  have hsl := sliceTo_nonneg (pySortedRev key it) n hn
  simp only [nlargest]
  by_cases h1 : n = 1
  · subst h1
    simp only [if_true, pure, Except.pure]
    rw [pyMinMax_eq _ key (fun e => -applyKey key e) (fun a b => by
      apply decide_eq_decide.2; omega), hsl, pySortedRev_eq]
    exact congrArg Except.ok (take_one_head _)
  · rw [if_neg h1]
    by_cases h2 : sized = true ∧ n ≥ it.length
    · rw [if_pos h2]; rfl
    · rw [if_neg h2, hsl, pySortedRev_eq]
      cases key with
      | none =>
        have := selAlgo_spec selS3_good n.toNat (-n) (by simp [selS3]; omega) it
        simp only [selAlgo, selS3] at this
        simp only [nlargestLoop_eq]
        exact this
      | some f =>
        have := selAlgo_spec (selS4_good f) n.toNat (-n) (by simp [selS4]; omega) it
        simp only [selAlgo, selS4] at this
        simp only [nlargestKeyLoop_eq]
        exact this

end PyLean.Accel
