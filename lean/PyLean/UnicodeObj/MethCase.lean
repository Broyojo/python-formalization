import PyLean.UnicodeObj.TextProps

/-!
The six case methods of `str` against the documented algorithm, position by position.

`str.upper`, `str.lower` and `str.casefold` are documented as the algorithms of section 3.13
of the Unicode Standard ("Default Case Conversion"): every character is replaced by its full
mapping, `Uppercase_Mapping`, `Lowercase_Mapping` or `Case_Folding`, with the one context
rule `Final_Sigma` for U+03A3. `str.title`: "words start with uppercased characters and all
remaining cased characters have lower case", where a word starts after a character that is
not cased (the docs: "The algorithm uses a simple language-independent definition of a word
as groups of consecutive letters", and the apostrophe example). `str.capitalize`: "first
character put into titlecase and the rest lowercased". `str.swapcase`: "uppercase characters
converted to lowercase and vice versa".

The specifications below index the input directly: output position `i` is a function of
`s[i]`, the text before it and the text after it. The C loops instead carry a running state
(`previous_is_cased`, the write index `k`, `maxchar`), read the context through
`lower_ucs4(kind, data, length, i, ...)`, and copy through a buffer of the kind `maxchar`
selects. The tables are the full Unicode 16 tables of `unicodectype.c` (`Ctype.lean`); the
`Final_Sigma` test is CPython's `final_sigma`, which `unicodeobj-text-final-sigma-regex` shows
differs from the Standard's for 267 characters.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- Lowercase mapping of position `i` of `s` in context (Unicode 3.13, `Final_Sigma` by
CPython's `final_sigma`): U+03A3 becomes final U+03C2 or medial U+03C3, every other character
its `Lowercase_Mapping`. -/
def docLowerAt (s : Str) (i : Nat) : List Nat :=
  let c := s.getD i 0
  if c = 0x3A3 then [if finalSigma (s.take i).reverse (s.drop (i + 1)) then 0x3C2 else 0x3C3]
  else toLowerFull c

/-- The output built position by position: the concatenation of `g 0, g 1, ..., g (len-1)`. -/
def perIndex (s : Str) (g : Nat → List Nat) : Str := (List.range s.length).flatMap g

/-- `str.title` at position `i`: titlecase after a character that is not cased (or at the
start), lowercase after a cased one. -/
def docTitleAt (s : Str) (i : Nat) : List Nat :=
  if i ≠ 0 ∧ isCased (s.getD (i - 1) 0) = true then docLowerAt s i else toTitleFull (s.getD i 0)

/-- `str.swapcase` at position `i`. -/
def docSwapAt (s : Str) (i : Nat) : List Nat :=
  let c := s.getD i 0
  if isUppercase c then docLowerAt s i else if isLowercase c then toUpperFull c else [c]

/-- `str.capitalize` at position `i`. -/
def docCapAt (s : Str) (i : Nat) : List Nat :=
  if i = 0 then toTitleFull (s.getD 0 0) else docLowerAt s i

def tooLong : PyExc := .overflowError "string is too long"

/-- For every string: `upper`, `lower` and `casefold` are the full Unicode mappings applied
position by position (with `Final_Sigma` for `lower`), `title` titlecases exactly the
characters that follow a non-cased one, `capitalize` titlecases the first and lowercases the
rest in context, and `swapcase` lowercases uppercase and uppercases lowercase characters,
leaving the rest. The only failure is `case_operation`'s `OverflowError`, for more than
`PY_SSIZE_T_MAX // 12` characters, which the ASCII shortcuts of `upper`, `lower` and
`casefold` and the empty string of `capitalize` skip. Type invariant: `Str.Valid s`. -/
def CaseDocSpec : Prop :=
  ∀ s : Str, Str.Valid s →
    unicodeUpper s = (if isAscii s ∨ s.length ≤ caseLengthLimit
      then .ok (perIndex s fun i => toUpperFull (s.getD i 0)) else .error tooLong) ∧
    unicodeLower s = (if isAscii s ∨ s.length ≤ caseLengthLimit
      then .ok (perIndex s (docLowerAt s)) else .error tooLong) ∧
    unicodeCasefold s = (if isAscii s ∨ s.length ≤ caseLengthLimit
      then .ok (perIndex s fun i => toFoldedFull (s.getD i 0)) else .error tooLong) ∧
    unicodeTitle s = (if s.length ≤ caseLengthLimit
      then .ok (perIndex s (docTitleAt s)) else .error tooLong) ∧
    unicodeCapitalize s = (if s.length = 0 ∨ s.length ≤ caseLengthLimit
      then .ok (perIndex s (docCapAt s)) else .error tooLong) ∧
    unicodeSwapcase s = (if s.length ≤ caseLengthLimit
      then .ok (perIndex s (docSwapAt s)) else .error tooLong)

/-! ## The loops, position by position -/

theorem getD_eq_of_lt (s : Str) (k : Nat) (hk : k < s.length) : s.getD k 0 = s[k] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]

theorem getD_drop_cons (s : Str) (k : Nat) (hk : k < s.length) :
    s.drop k = s.getD k 0 :: s.drop (k + 1) := by
  rw [getD_eq_of_lt s k hk]
  exact List.drop_eq_getElem_cons hk

theorem take_succ_reverse (s : Str) (k : Nat) (hk : k < s.length) :
    (s.take (k + 1)).reverse = s.getD k 0 :: (s.take k).reverse := by
  rw [getD_eq_of_lt s k hk, List.take_succ, List.getElem?_eq_getElem hk]
  simp

theorem range_succ_flatMap (n : Nat) (g : Nat → List Nat) :
    (List.range (n + 1)).flatMap g = g 0 ++ (List.range n).flatMap (fun j => g (j + 1)) := by
  rw [List.range_succ_eq_map]
  simp [List.flatMap_cons, List.flatMap_map]

theorem mapLoop_perIndex (f : List Nat → Nat → List Nat → List Nat) (s : Str) :
    ∀ n k o, k + n = s.length →
      (mapLoop f (s.take k).reverse (s.drop k) o).res =
        o.res ++ (List.range n).flatMap
          (fun j => f (s.take (k + j)).reverse (s.getD (k + j) 0) (s.drop (k + j + 1))) := by
  intro n
  induction n with
  | zero =>
    intro k o h
    have : s.drop k = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, mapLoop]
  | succ n ih =>
    intro k o h
    have hk : k < s.length := by omega
    rw [getD_drop_cons s k hk, mapLoop, ← take_succ_reverse s k hk, ih (k + 1) _ (by omega),
      range_succ_flatMap]
    simp only [emit, Nat.add_zero, List.append_assoc]
    congr 3
    funext j
    rw [show k + (j + 1) = k + 1 + j by omega]

theorem titleLoop_perIndex (s : Str) :
    ∀ n k o, k + n = s.length →
      (titleLoop (k ≠ 0 && isCased (s.getD (k - 1) 0)) (s.take k).reverse (s.drop k) o).res =
        o.res ++ (List.range n).flatMap (fun j => docTitleAt s (k + j)) := by
  intro n
  induction n with
  | zero =>
    intro k o h
    have : s.drop k = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, titleLoop]
  | succ n ih =>
    intro k o h
    have hk : k < s.length := by omega
    rw [getD_drop_cons s k hk, titleLoop, ← take_succ_reverse s k hk]
    have e : isCased (s.getD k 0) = (k + 1 ≠ 0 && isCased (s.getD (k + 1 - 1) 0)) := by simp
    rw [e, ih (k + 1) _ (by omega), range_succ_flatMap]
    simp only [emit, Nat.add_zero, List.append_assoc]
    have hm : (if (k ≠ 0 && isCased (s.getD (k - 1) 0)) = true then
        lowerUcs4 (s.take k).reverse (s.getD k 0) (s.drop (k + 1))
        else toTitleFull (s.getD k 0)) = docTitleAt s k := by
      simp only [docTitleAt, docLowerAt, lowerUcs4, handleCapitalSigma, Bool.and_eq_true,
        decide_eq_true_eq]
    rw [hm]
    congr 3
    funext j
    rw [show k + (j + 1) = k + 1 + j by omega]

theorem lowerUcs4_at (s : Str) (i : Nat) :
    lowerUcs4 (s.take i).reverse (s.getD i 0) (s.drop (i + 1)) = docLowerAt s i := rfl

theorem mapLoop_perIndex0 (f : List Nat → Nat → List Nat → List Nat) (s : Str) :
    (mapLoop f [] s startOut).res =
      (List.range s.length).flatMap (fun j => f (s.take j).reverse (s.getD j 0) (s.drop (j + 1))) := by
  have := mapLoop_perIndex f s s.length 0 startOut (by omega)
  simpa only [Nat.zero_add, List.take_zero, List.reverse_nil, List.drop_zero, startOut,
    List.nil_append] using this

theorem doLower_perIndex (s : Str) : (doLower s).res = perIndex s (docLowerAt s) := by
  simp only [doLower, doUpperOrLower, mapLoop_perIndex0, perIndex, ite_true, lowerUcs4_at]

theorem doUpper_perIndex (s : Str) :
    (doUpper s).res = perIndex s fun i => toUpperFull (s.getD i 0) := by
  have e : ∀ j, (if false = true then lowerUcs4 (s.take j).reverse (s.getD j 0) (s.drop (j + 1))
      else toUpperFull (s.getD j 0)) = toUpperFull (s.getD j 0) := fun _ =>
    if_neg Bool.false_ne_true
  simp only [doUpper, doUpperOrLower, mapLoop_perIndex0, perIndex, e]

theorem doCasefold_perIndex (s : Str) :
    (doCasefold s).res = perIndex s fun i => toFoldedFull (s.getD i 0) := by
  rw [doCasefold, mapLoop_perIndex0, perIndex]

theorem doSwapcase_perIndex (s : Str) : (doSwapcase s).res = perIndex s (docSwapAt s) := by
  have e : ∀ j, swapcaseMap (s.take j).reverse (s.getD j 0) (s.drop (j + 1)) = docSwapAt s j :=
    fun j => by simp only [swapcaseMap, docSwapAt, lowerUcs4_at]
  simp only [doSwapcase, mapLoop_perIndex0, perIndex, e]

theorem doTitle_perIndex (s : Str) : (doTitle s).res = perIndex s (docTitleAt s) := by
  have := titleLoop_perIndex s s.length 0 startOut (by omega)
  simp only [Nat.zero_add, List.take_zero, List.reverse_nil, List.drop_zero, startOut,
    List.nil_append, ne_eq, not_true_eq_false, decide_false, Bool.false_and] at this
  exact this

theorem doCapitalize_perIndex (s : Str) : (doCapitalize s).res = perIndex s (docCapAt s) := by
  cases s with
  | nil => rfl
  | cons c cs =>
    have h : (mapLoop lowerUcs4 [c] cs (emit startOut (toTitleFull c))).res =
        toTitleFull c ++ (List.range cs.length).flatMap (fun j => docLowerAt (c :: cs) (1 + j)) :=
      mapLoop_perIndex lowerUcs4 (c :: cs) cs.length 1 _ (by simp; omega)
    rw [show doCapitalize (c :: cs) = mapLoop lowerUcs4 [c] cs (emit startOut (toTitleFull c))
      from rfl, h, perIndex, List.length_cons, range_succ_flatMap]
    congr 1
    congr 1
    funext j
    rw [docCapAt, if_neg (Nat.add_one_ne_zero j), Nat.add_comm]

/-! ## The ASCII shortcuts -/

theorem asciiUpperOrLower_perIndex (s : Str) (h : isAscii s = true) :
    asciiUpperOrLower false s = perIndex s (fun i => toUpperFull (s.getD i 0)) ∧
    asciiUpperOrLower true s = perIndex s (docLowerAt s) ∧
    asciiUpperOrLower true s = perIndex s (fun i => toFoldedFull (s.getD i 0)) := by
  obtain ⟨h1, h2, h3⟩ := caseAsciiFastPath_proven s h
  exact ⟨h1.trans (doUpper_perIndex s), h2.trans (doLower_perIndex s),
    h3.trans (doCasefold_perIndex s)⟩

theorem caseDocSpec_proven : CaseDocSpec := by
  intro s hs
  have hg := caseOutputBound_proven s hs
  have fast := asciiUpperOrLower_perIndex s
  by_cases hl : s.length ≤ caseLengthLimit
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [if_pos (Or.inr hl), unicodeUpper]
      split
      · next ha => rw [(fast ha).1]
      · rw [caseOperation_good hl hg.1, doUpper_perIndex]
    · rw [if_pos (Or.inr hl), unicodeLower]
      split
      · next ha => rw [(fast ha).2.1]
      · rw [caseOperation_good hl hg.2.1, doLower_perIndex]
    · rw [if_pos (Or.inr hl), unicodeCasefold]
      split
      · next ha => rw [(fast ha).2.2]
      · rw [caseOperation_good hl hg.2.2.1, doCasefold_perIndex]
    · rw [if_pos hl, unicodeTitle, caseOperation_good hl hg.2.2.2.2.1, doTitle_perIndex]
    · rw [if_pos (Or.inr hl), unicodeCapitalize]
      split
      · next h0 =>
        rw [List.length_eq_zero_iff.mp h0]; rfl
      · rw [caseOperation_good hl hg.2.2.2.2.2, doCapitalize_perIndex]
    · rw [if_pos hl, unicodeSwapcase, caseOperation_good hl hg.2.2.2.1, doSwapcase_perIndex]
  · have hgt : s.length > caseLengthLimit := by omega
    have hne : s.length ≠ 0 := by unfold caseLengthLimit at hgt; omega
    have err : ∀ perform, caseOperation perform s = .error tooLong := by
      intro perform; simp [caseOperation, hgt, tooLong]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [unicodeUpper]
      split
      · next ha => rw [if_pos (Or.inl ha), (fast ha).1]
      · next ha => rw [if_neg (by simp [ha, hl]), err]
    · rw [unicodeLower]
      split
      · next ha => rw [if_pos (Or.inl ha), (fast ha).2.1]
      · next ha => rw [if_neg (by simp [ha, hl]), err]
    · rw [unicodeCasefold]
      split
      · next ha => rw [if_pos (Or.inl ha), (fast ha).2.2]
      · next ha => rw [if_neg (by simp [ha, hl]), err]
    · rw [if_neg hl, unicodeTitle, err]
    · rw [if_neg (by simp [hne, hl]), unicodeCapitalize, if_neg hne, err]
    · rw [if_neg hl, unicodeSwapcase, err]

end PyLean.UnicodeObj
