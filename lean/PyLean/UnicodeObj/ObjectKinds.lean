import PyLean.UnicodeObj.TextCase

/-!
The PEP 393 representations: what concatenation, slicing, repetition and the
constructors compute for the kind of their result. Objects/unicodeobject.c.

`Kind` is the representation, and `canonicalKind s` the one `_PyUnicode_CheckConsistency`
demands of a finished string. `PyUnicode_MAX_CHAR_VALUE(str)` is `(canonicalKind str).maxChar`.
-/

namespace PyLean.UnicodeObj

open PyLean

theorem foldl_max_ge (s : Str) (a : Nat) : a ≤ s.foldl max a := by
  induction s generalizing a with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_mem (s : Str) (a : Nat) : ∀ c ∈ s, c ≤ s.foldl max a := by
  induction s generalizing a with
  | nil => intro c hc; simp at hc
  | cons x xs ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge xs _)
    · exact ih _ c hc

theorem foldl_max_le (s : Str) (a m : Nat) (ha : a ≤ m) (h : ∀ c ∈ s, c ≤ m) :
    s.foldl max a ≤ m := by
  induction s generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    exact ih _ (Nat.max_le.2 ⟨ha, h x List.mem_cons_self⟩)
      (fun c hc => h c (List.mem_cons_of_mem _ hc))

theorem maxCharOf_append (a b : Str) : maxCharOf (a ++ b) = max (maxCharOf a) (maxCharOf b) := by
  apply Nat.le_antisymm
  · exact foldl_max_le _ _ _ (Nat.zero_le _) (fun c hc => by
      rcases List.mem_append.1 hc with h | h
      · exact Nat.le_trans (foldl_max_mem a 0 c h) (Nat.le_max_left _ _)
      · exact Nat.le_trans (foldl_max_mem b 0 c h) (Nat.le_max_right _ _))
  · exact Nat.max_le.2
      ⟨foldl_max_le _ _ _ (Nat.zero_le _) (fun c hc => foldl_max_mem _ 0 c (List.mem_append_left _ hc)),
       foldl_max_le _ _ _ (Nat.zero_le _) (fun c hc => foldl_max_mem _ 0 c (List.mem_append_right _ hc))⟩

/-- `PyUnicode_IS_ASCII` holds exactly for canonical kind `ascii`, on every string. -/
def IsAsciiKind : Prop :=
  ∀ s : Str, canonicalKind s = .ascii ↔ isAscii s = true

theorem isAsciiKind_proven : IsAsciiKind := by
  intro s
  simp only [canonicalKind, kindOfMax, isAscii, List.all_eq_true, decide_eq_true_eq]
  constructor
  · intro h c hc
    have := foldl_max_mem s 0 c hc
    have hm : maxCharOf s < 128 := by
      by_cases h1 : maxCharOf s < 128
      · exact h1
      · simp only [h1, if_false] at h
        split at h
        · cases h
        · split at h <;> cases h
    simp only [maxCharOf] at hm
    omega
  · intro h
    have : maxCharOf s < 128 := by
      have := foldl_max_le s 0 127 (by omega) (fun c hc => by have := h c hc; omega)
      simp only [maxCharOf]
      omega
    simp [this]

/-- `PyUnicode_Concat`, unicodeobject.c:11634-11680, on two strings: the text and the
`maxchar` passed to `PyUnicode_New`. `right` being a `str` is the type check. -/
def pyUnicodeConcat (l r : Str) : Py (Str × Nat) :=
  if l.isEmpty then .ok (r, (canonicalKind r).maxChar)
  else if r.isEmpty then .ok (l, (canonicalKind l).maxChar)
  else if (l.length : Int) > ssizeMax - r.length then
    .error (.overflowError "strings are too large to concat")
  else .ok (l ++ r, max (canonicalKind l).maxChar (canonicalKind r).maxChar)

/-- `str + str` allocates exactly the canonical kind of the result, although it only
looks at the kinds of the operands. For all valid strings. -/
def ConcatKind : Prop :=
  ∀ (l r t : Str) (m : Nat), Str.Valid l → Str.Valid r → pyUnicodeConcat l r = .ok (t, m) →
    t = l ++ r ∧ kindOfMax m = canonicalKind t

theorem maxChar_kind (s : Str) (h : Str.Valid s) :
    maxCharOf s ≤ (canonicalKind s).maxChar := by
  have hv : maxCharOf s ≤ maxUnicode := foldl_max_le _ _ _ (Nat.zero_le _) h
  have hm : maxUnicode = 0x10FFFF := rfl
  simp only [canonicalKind, kindOfMax]
  repeat' split
  all_goals simp only [Kind.maxChar]
  all_goals omega

theorem kindOfMax_maxChar (s : Str) :
    kindOfMax (canonicalKind s).maxChar = canonicalKind s := by
  simp only [canonicalKind, kindOfMax]
  repeat' split
  all_goals first | rfl | (simp only [Kind.maxChar] at *; omega)

theorem kind_max (a b : Nat) (ha : a ≤ 0x10FFFF) (hb : b ≤ 0x10FFFF) :
    kindOfMax (max (kindOfMax a).maxChar (kindOfMax b).maxChar) = kindOfMax (max a b) := by
  simp only [kindOfMax]
  repeat' split
  all_goals first | rfl | (simp only [Kind.maxChar] at *; omega)

theorem concatKind_proven : ConcatKind := by
  intro l r t m hl hr h
  have hml : maxCharOf l ≤ 0x10FFFF := foldl_max_le _ _ _ (Nat.zero_le _) hl
  have hmr : maxCharOf r ≤ 0x10FFFF := foldl_max_le _ _ _ (Nat.zero_le _) hr
  unfold pyUnicodeConcat at h
  split at h
  · rename_i h0
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have : l = [] := by simpa using h0
    subst this
    exact ⟨by simp, kindOfMax_maxChar _⟩
  · split at h
    · rename_i _ h0
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : r = [] := by simpa using h0
      subst this
      exact ⟨by simp, kindOfMax_maxChar _⟩
    · split at h
      · cases h
      · simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨rfl, ?_⟩
        simp only [canonicalKind]
        rw [maxCharOf_append]
        exact kind_max _ _ hml hmr

/-- `kind_maxchar_limit`, unicodeobject.c:2291-2303. -/
def kindMaxcharLimit : Kind → Nat
  | .ascii | .ucs1 => 0x80
  | .ucs2 => 0x100
  | .ucs4 => 0x10000

/-- The `max_char` loop of `unicode_subscript`, unicodeobject.c:14625-14632, with its
early `break`. -/
def sliceMaxLoop (limit : Nat) : List Nat → Nat → Nat
  | [], m => m
  | c :: cs, m =>
    if c > m then (if c ≥ limit then c else sliceMaxLoop limit cs c)
    else sliceMaxLoop limit cs m

/-- `max_char` of the general case of `unicode_subscript`, unicodeobject.c:14620-14636. -/
def sliceMaxChar (src sub : Str) : Nat :=
  if isAscii src then 127 else sliceMaxLoop (kindMaxcharLimit (canonicalKind src)) sub 0

theorem sliceMaxLoop_spec (limit : Nat) (sub : Str) (m : Nat) :
    sliceMaxLoop limit sub m = sub.foldl max m ∨
    (limit ≤ sliceMaxLoop limit sub m ∧ sliceMaxLoop limit sub m ∈ sub) := by
  induction sub generalizing m with
  | nil => exact Or.inl rfl
  | cons c cs ih =>
    simp only [sliceMaxLoop, List.foldl_cons]
    by_cases h : c > m
    · simp only [h, if_true]
      by_cases hl : c ≥ limit
      · simp only [hl, if_true]
        exact Or.inr ⟨hl, List.mem_cons_self⟩
      · simp only [hl, if_false]
        have e : max m c = c := by omega
        rw [e]
        rcases ih c with h1 | ⟨h1, h2⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩
    · simp only [h, if_false]
      have e : max m c = m := by omega
      rw [e]
      rcases ih m with h1 | ⟨h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, List.mem_cons_of_mem _ h2⟩

/-- An extended slice `s[start:stop:step]` allocates the canonical kind of its result,
despite the early `break` of the `max_char` loop, and every character fits. For every
valid non-empty selection `sub` of the characters of `src`. -/
def SliceKind : Prop :=
  ∀ src sub : Str, Str.Valid src → sub ≠ [] → (∀ c ∈ sub, c ∈ src) →
    kindOfMax (sliceMaxChar src sub) = canonicalKind sub

theorem sliceKind_proven : SliceKind := by
  intro src sub hv hne hsub
  have hsv : maxCharOf sub ≤ maxCharOf src :=
    foldl_max_le _ _ _ (Nat.zero_le _) (fun c hc => foldl_max_mem _ 0 c (hsub c hc))
  have hmax : maxCharOf src ≤ 0x10FFFF := foldl_max_le _ _ _ (Nat.zero_le _) hv
  unfold sliceMaxChar
  by_cases ha : isAscii src = true
  · simp only [ha, if_true]
    have h1 := (isAsciiKind_proven src).2 ha
    have h2 : maxCharOf src < 128 := by
      simp only [canonicalKind, kindOfMax] at h1
      by_cases h3 : maxCharOf src < 128
      · exact h3
      · simp only [h3, if_false] at h1
        split at h1
        · cases h1
        · split at h1 <;> cases h1
    simp only [canonicalKind, kindOfMax]
    rw [if_pos (by omega), if_pos (by omega)]
  · simp only [ha, if_false]
    have hk : canonicalKind src ≠ .ascii := fun h => ha ((isAsciiKind_proven src).1 h)
    generalize hkk : canonicalKind src = k at *
    rcases sliceMaxLoop_spec (kindMaxcharLimit k) sub 0 with h | ⟨h1, h2⟩
    · rw [h]
      rfl
    · generalize sliceMaxLoop (kindMaxcharLimit k) sub 0 = m at *
      have hm := foldl_max_mem sub 0 m h2
      simp only [canonicalKind, kindOfMax] at hkk ⊢
      simp only [maxCharOf] at *
      cases k <;> simp only [kindMaxcharLimit] at h1 <;> grind

/-- `unicode_repeat`, unicodeobject.c:12816-12867, for `len` a `Py_ssize_t`. -/
def unicodeRepeat (s : Str) (len : Int) : Py Str :=
  if len < 1 then .ok []
  else if len = 1 then .ok s
  else if (s.length : Int) > ssizeMax / len then
    .error (.overflowError "repeated string is too long")
  else .ok ((List.replicate len.toNat s).flatten)

/-- `s * n` is `n` copies, for every string and `n`, and raises only when the length
exceeds `PY_SSIZE_T_MAX`. The division in the overflow test is exact: no silent
wraparound of `len * length`. -/
def RepeatLength : Prop :=
  ∀ (s : Str) (n : Int), 1 < n → n ≤ ssizeMax →
    (∃ r, unicodeRepeat s n = .ok r ∧ (r.length : Int) = n * s.length ∧
      (r.length : Int) ≤ ssizeMax) ∨
    (unicodeRepeat s n = .error (.overflowError "repeated string is too long") ∧
      n * s.length > ssizeMax)

theorem repeatLength_proven : RepeatLength := by
  intro s n h1 h2
  unfold unicodeRepeat
  have hn : ¬ n < 1 := by omega
  have hn1 : ¬ n = 1 := by omega
  simp only [hn, hn1, if_false]
  have hdiv : ((s.length : Int) > ssizeMax / n) ↔ n * s.length > ssizeMax := by
    have hpos : 0 < n := by omega
    constructor
    · intro h
      have := Int.lt_mul_of_ediv_lt hpos h
      simpa [Int.mul_comm] using this
    · intro h
      exact Int.ediv_lt_of_lt_mul hpos (by simpa [Int.mul_comm] using h)
  by_cases h : (s.length : Int) > ssizeMax / n
  · right
    simp only [h, if_true]
    exact ⟨rfl, hdiv.1 h⟩
  · left
    simp only [h, if_false]
    have hle : ¬ n * s.length > ssizeMax := fun e => h (hdiv.2 e)
    have hlen : (((List.replicate n.toNat s).flatten).length : Int) = n * s.length := by
      simp only [List.length_flatten, List.map_replicate, List.sum_replicate]
      have : ((n.toNat : Int)) = n := by omega
      simp [Nat.cast_mul, this]
    exact ⟨_, rfl, hlen, by omega⟩

/-- `unicode_compare`, unicodeobject.c:11194-11307: -1, 0 or 1 by code points. The
twelve kind pairs and the `memcmp` paths all compute this. -/
def unicodeCompare : Str → Str → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs =>
    if a = b then unicodeCompare as bs else if a < b then -1 else 1

/-- `unicode_compare` is a total order on strings: antisymmetric, and 0 exactly on equal
strings, for every pair. -/
def CompareOrder : Prop :=
  ∀ a b : Str, unicodeCompare a b = - unicodeCompare b a ∧ (unicodeCompare a b = 0 ↔ a = b)

theorem compareOrder_proven : CompareOrder := by
  intro a
  induction a with
  | nil =>
    intro b
    cases b <;> simp [unicodeCompare]
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp [unicodeCompare]
    | cons y ys =>
      have := ih ys
      simp only [unicodeCompare, List.cons.injEq]
      by_cases h : x = y
      · subst h
        simpa using this
      · have h' : ¬ y = x := fun e => h e.symm
        simp only [h, h', if_false, false_and, iff_false]
        by_cases hl : x < y
        · have : ¬ y < x := by omega
          simp [hl, this]
        · have : y < x := by omega
          simp [hl, this]

end PyLean.UnicodeObj
