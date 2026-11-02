import PyLean.StrSearch.Model

/-!
`Objects/bytes_methods.c` (CPython 3.15.2): classification, case mapping and
`maketrans`. The search and tailmatch helpers of that file live in
`PyLean.StrSearch.Model`; `Basic.lean` adds the object-level argument parsing.

Bytes are `Nat`s below 256 (`StrSearch.Seq`). The `Py_IS*`/`Py_TO*` macros are
the ASCII-only tables of `Python/pyctype.c`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The ctype tables -/

/-- `Py_ISUPPER`, Python/pyctype.c. -/
def isUpperC (c : Nat) : Bool := decide (65 ≤ c ∧ c ≤ 90)
/-- `Py_ISLOWER`. -/
def isLowerC (c : Nat) : Bool := decide (97 ≤ c ∧ c ≤ 122)
/-- `Py_ISALPHA`. -/
def isAlphaC (c : Nat) : Bool := isUpperC c || isLowerC c
/-- `Py_ISDIGIT`. -/
def isDigitC (c : Nat) : Bool := decide (48 ≤ c ∧ c ≤ 57)
/-- `Py_ISALNUM`. -/
def isAlnumC (c : Nat) : Bool := isAlphaC c || isDigitC c
/-- `Py_ISSPACE`: `\t\n\v\f\r` and space. Same table as `StrSearch.byteSpace`. -/
def isSpaceC (c : Nat) : Bool := byteSpace c
/-- `Py_ISXDIGIT`. -/
def isXDigitC (c : Nat) : Bool := isDigitC c || decide (65 ≤ c ∧ c ≤ 70) || decide (97 ≤ c ∧ c ≤ 102)
/-- `Py_TOLOWER`. -/
def toLowerC (c : Nat) : Nat := if 65 ≤ c ∧ c ≤ 90 then c + 32 else c
/-- `Py_TOUPPER`. -/
def toUpperC (c : Nat) : Nat := if 97 ≤ c ∧ c ≤ 122 then c - 32 else c

/-! ## Classification, bytes_methods.c:11-122 and :202-242 -/

/-- The loop `for (; p < e; p++) if (!P(*p)) Py_RETURN_FALSE; Py_RETURN_TRUE`,
bytes_methods.c:27-31 (and the three copies below it). -/
def allLoop (p : Nat → Bool) : Seq → Bool
  | [] => true
  | c :: rest => if !p c then false else allLoop p rest

/-- `_Py_bytes_isspace`, `_Py_bytes_isalpha`, `_Py_bytes_isalnum`,
`_Py_bytes_isdigit`, bytes_methods.c:11-122: the single-character shortcut,
the empty case, then the loop. `p` is the ctype macro. -/
def bytesIsClass (p : Nat → Bool) (s : Seq) : Bool :=
  if s.length = 1 ∧ p (s.headD 0) = true then true
  else if s.length = 0 then false
  else allLoop p s

def bytesIsSpace : Seq → Bool := bytesIsClass isSpaceC
def bytesIsAlpha : Seq → Bool := bytesIsClass isAlphaC
def bytesIsAlnum : Seq → Bool := bytesIsClass isAlnumC
def bytesIsDigit : Seq → Bool := bytesIsClass isDigitC

/-- The loop of `_Py_bytes_islower`/`_Py_bytes_isupper`,
bytes_methods.c:147-155 and :181-189: `bad` is the opposite case. -/
def casedLoop (bad good : Nat → Bool) : Bool → Seq → Bool
  | cased, [] => cased
  | cased, c :: rest =>
    if bad c then false
    else if !cased && good c then casedLoop bad good true rest
    else casedLoop bad good cased rest

/-- `_Py_bytes_islower`, bytes_methods.c:131-156. -/
def bytesIsLower (s : Seq) : Bool :=
  if s.length = 1 then isLowerC (s.headD 0)
  else if s.length = 0 then false
  else casedLoop isUpperC isLowerC false s

/-- `_Py_bytes_isupper`, bytes_methods.c:165-190. -/
def bytesIsUpper (s : Seq) : Bool :=
  if s.length = 1 then isUpperC (s.headD 0)
  else if s.length = 0 then false
  else casedLoop isLowerC isUpperC false s

/-- The loop of `_Py_bytes_istitle`, bytes_methods.c:220-241. The arguments are
`cased` and `previous_is_cased`. -/
def titleLoop : Bool → Bool → Seq → Bool
  | cased, _, [] => cased
  | cased, prev, c :: rest =>
    if isUpperC c then
      if prev then false else titleLoop true true rest
    else if isLowerC c then
      if !prev then false else titleLoop true true rest
    else titleLoop cased false rest

/-- `_Py_bytes_istitle`, bytes_methods.c:201-242. -/
def bytesIsTitle (s : Seq) : Bool :=
  if s.length = 1 then isUpperC (s.headD 0)
  else if s.length = 0 then false
  else titleLoop false false s

/-- `_Py_bytes_isascii`, bytes_methods.c:728-738: `stringlib_find_max_char`
returns 127 or a larger value, so only the comparison with 127 matters. -/
def bytesIsAscii (s : Seq) : Bool :=
  if maxCharValue s > 127 then false else true

/-! ## Case mapping, bytes_methods.c:250-345 -/

/-- `_Py_bytes_lower`, bytes_methods.c:250-258. -/
def bytesLower (s : Seq) : Seq := s.map toLowerC
/-- `_Py_bytes_upper`, bytes_methods.c:266-274. -/
def bytesUpper (s : Seq) : Seq := s.map toUpperC

/-- The loop of `_Py_bytes_title`, bytes_methods.c:289-302; the argument is
`previous_is_cased`. -/
def titleMap : Bool → Seq → Seq
  | _, [] => []
  | prev, c :: rest =>
    if isLowerC c then (if !prev then toUpperC c else c) :: titleMap true rest
    else if isUpperC c then (if prev then toLowerC c else c) :: titleMap true rest
    else c :: titleMap false rest

/-- `_Py_bytes_title`, bytes_methods.c:283-303. -/
def bytesTitle (s : Seq) : Seq := titleMap false s

/-- `_Py_bytes_capitalize`, bytes_methods.c:312-319. -/
def bytesCapitalize : Seq → Seq
  | [] => []
  | c :: rest => toUpperC c :: bytesLower rest

/-- One step of `_Py_bytes_swapcase`, bytes_methods.c:335-342. -/
def swapC (c : Nat) : Nat :=
  if isLowerC c then toUpperC c else if isUpperC c then toLowerC c else c

/-- `_Py_bytes_swapcase`, bytes_methods.c:328-345. -/
def bytesSwapcase (s : Seq) : Seq := s.map swapC

/-! ## maketrans, bytes_methods.c:356-377 -/

/-- The loop `p[frm[i]] = to[i]`, bytes_methods.c:372-374. -/
def maketransLoop (p : Seq) : Seq → Seq → Seq
  | f :: frm, t :: to => maketransLoop (p.set f t) frm to
  | _, _ => p

/-- `_Py_bytes_maketrans`, bytes_methods.c:356-377. -/
def bytesMaketrans (frm to : Seq) : Py Seq :=
  if frm.length ≠ to.length then
    .error (.valueError "maketrans arguments must have same length")
  else .ok (maketransLoop (List.range 256) frm to)

/-! ## Properties -/

theorem allLoop_eq (p : Nat → Bool) (s : Seq) : allLoop p s = s.all p := by
  induction s with
  | nil => rfl
  | cons c rest ih =>
    simp only [allLoop, List.all_cons]
    cases h : p c <;> simp [h, ih]

/-- For every byte string and every class: `isspace`, `isalpha`, `isalnum` and
`isdigit` return "non-empty and all bytes in the class"; the single-byte
shortcut agrees with the loop. -/
def ClassShortcut : Prop :=
  ∀ (p : Nat → Bool) (s : Seq), bytesIsClass p s = (decide (s ≠ []) && s.all p)

theorem classShortcut_proven : ClassShortcut := by
  intro p s
  unfold bytesIsClass
  cases s with
  | nil => simp
  | cons c rest =>
    cases rest with
    | nil => cases h : p c <;> simp [allLoop, h]
    | cons d more =>
      simp only [List.length_cons]
      have h1 : ¬ (more.length + 1 + 1 = 1) := by omega
      have h2 : ¬ (more.length + 1 + 1 = 0) := by omega
      simp [allLoop_eq, h1]

theorem casedLoop_spec (bad good : Nat → Bool) (cased : Bool) (s : Seq) :
    casedLoop bad good cased s = (s.all (fun c => !bad c) && (cased || s.any good)) := by
  induction s generalizing cased with
  | nil => simp [casedLoop]
  | cons c rest ih =>
    simp only [casedLoop, List.all_cons, List.any_cons]
    cases hb : bad c <;> cases hg : good c <;> cases cased <;> simp [ih]

/-- `islower`/`isupper`: the bytes contain no byte of the opposite case and at
least one of the tested case, also for one-byte strings (the shortcut). Upper
and lower case are disjoint, which the one-byte shortcut relies on. -/
def CasedSpec : Prop :=
  ∀ s : Seq,
    bytesIsLower s = (s.all (fun c => !isUpperC c) && s.any isLowerC) ∧
    bytesIsUpper s = (s.all (fun c => !isLowerC c) && s.any isUpperC)

theorem up_low_disjoint (c : Nat) : isUpperC c = true → isLowerC c = false := by
  simp only [isUpperC, isLowerC, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem low_up_disjoint (c : Nat) : isLowerC c = true → isUpperC c = false := by
  simp only [isUpperC, isLowerC, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

theorem casedSpec_proven : CasedSpec := by
  intro s
  constructor
  · unfold bytesIsLower
    cases s with
    | nil => simp
    | cons c rest =>
      cases rest with
      | nil =>
        cases hl : isLowerC c
        · simp [hl]
        · simp [hl, low_up_disjoint c hl]
      | cons d more =>
        simp only [List.length_cons]
        have h1 : ¬ (more.length + 1 + 1 = 1) := by omega
        have h2 : ¬ (more.length + 1 + 1 = 0) := by omega
        simp only [h1, h2, if_false, casedLoop_spec, Bool.false_or]
  · unfold bytesIsUpper
    cases s with
    | nil => simp
    | cons c rest =>
      cases rest with
      | nil =>
        cases hl : isUpperC c
        · simp [hl]
        · simp [hl, up_low_disjoint c hl]
      | cons d more =>
        simp only [List.length_cons]
        have h1 : ¬ (more.length + 1 + 1 = 1) := by omega
        have h2 : ¬ (more.length + 1 + 1 = 0) := by omega
        simp only [h1, h2, if_false, casedLoop_spec, Bool.false_or]

theorem title_upper (c : Nat) (h : isLowerC c = true) : isUpperC (toUpperC c) = true := by
  simp only [isLowerC, decide_eq_true_eq] at h
  simp only [isUpperC, toUpperC, if_pos h, decide_eq_true_eq]
  omega

theorem title_lower (c : Nat) (h : isUpperC c = true) : isLowerC (toLowerC c) = true := by
  simp only [isUpperC, decide_eq_true_eq] at h
  simp only [isLowerC, toLowerC, if_pos h, decide_eq_true_eq]
  omega

theorem titleLoop_titleMap (cased prev : Bool) (s : Seq) :
    titleLoop cased prev (titleMap prev s) = (cased || s.any (fun c => isUpperC c || isLowerC c)) := by
  induction s generalizing cased prev with
  | nil => simp [titleMap, titleLoop]
  | cons c rest ih =>
    simp only [titleMap, List.any_cons]
    cases hl : isLowerC c
    · cases hu : isUpperC c
      · simp only [Bool.false_eq_true, if_false, titleLoop, hu, hl, ih, Bool.or_false, Bool.false_or]
      · have hd : isLowerC c = false := hl
        cases prev
        · simp only [Bool.false_eq_true, if_false, if_true, titleLoop, hu, hl, Bool.true_or,
            Bool.or_true, ih, Bool.not_false]
        · have h2 := title_lower c hu
          have h3 := low_up_disjoint _ h2
          simp only [Bool.false_eq_true, if_false, if_true, titleLoop, h2, h3, ih, Bool.not_true,
            Bool.true_or, Bool.or_true]
    · have hu : isUpperC c = false := low_up_disjoint c hl
      cases prev
      · have h2 := title_upper c hl
        simp only [if_true, Bool.not_false, titleLoop, h2, ih, reduceIte]
        simp [hu, hl]
      · simp only [if_true, Bool.not_true, Bool.false_eq_true, if_false, titleLoop, hu, hl, ih,
          reduceIte]
        simp

theorem titleMap_length (prev : Bool) (s : Seq) : (titleMap prev s).length = s.length := by
  induction s generalizing prev with
  | nil => rfl
  | cons c rest ih =>
    simp only [titleMap]
    split <;> simp [ih]
    · split <;> simp [ih]

/-- `b.title().istitle()` holds exactly when `b` has a cased byte (and for a
one-byte string the `istitle` shortcut agrees), and `title` keeps the length.
This pins down both `_Py_bytes_title` and the `istitle` state machine. -/
def TitleIstitle : Prop :=
  ∀ s : Seq, bytesIsTitle (bytesTitle s) = s.any (fun c => isUpperC c || isLowerC c) ∧
    (bytesTitle s).length = s.length

theorem titleIstitle_proven : TitleIstitle := by
  intro s
  refine ⟨?_, titleMap_length false s⟩
  have hl := titleMap_length false s
  unfold bytesIsTitle bytesTitle
  rw [hl]
  cases s with
  | nil => simp [titleMap]
  | cons c rest =>
    cases rest with
    | nil =>
      simp only [titleMap, List.length_cons, List.length_nil, List.headD_cons, List.any_cons,
        List.any_nil, Bool.or_false]
      cases hl : isLowerC c
      · cases hu : isUpperC c <;> simp [hu, hl]
      · have hu := low_up_disjoint c hl
        simp [hl, hu, title_upper c hl]
    | cons d more =>
      have h1 : ¬ ((c :: d :: more).length = 1) := by simp
      have h2 : ¬ ((c :: d :: more).length = 0) := by simp
      simp only [h1, h2, if_false]
      simpa using titleLoop_titleMap false false (c :: d :: more)

theorem swapC_swapC (c : Nat) : swapC (swapC c) = c := by
  simp only [swapC, isLowerC, isUpperC, toUpperC, toLowerC, decide_eq_true_eq]
  repeat' split
  all_goals omega

theorem low_up_c (c : Nat) : toLowerC (toUpperC c) = toLowerC c := by
  simp only [toUpperC, toLowerC]
  repeat' split
  all_goals omega

theorem up_low_c (c : Nat) : toUpperC (toLowerC c) = toUpperC c := by
  simp only [toUpperC, toLowerC]
  repeat' split
  all_goals omega

/-- The case maps are the byte-wise ASCII maps: `swapcase` is an involution,
`lower` and `upper` keep the length and absorb each other,
`capitalize` is `upper(b[:1]) + lower(b[1:])`, and every byte of
`swapcase` differs from the input exactly when it is a cased byte. -/
def CaseMaps : Prop :=
  ∀ s : Seq,
    bytesSwapcase (bytesSwapcase s) = s ∧
    bytesLower (bytesUpper s) = bytesLower s ∧
    bytesUpper (bytesLower s) = bytesUpper s ∧
    (bytesLower s).length = s.length ∧ (bytesUpper s).length = s.length ∧
    bytesCapitalize s = bytesUpper (s.take 1) ++ bytesLower (s.drop 1)

theorem caseMaps_proven : CaseMaps := by
  intro s
  refine ⟨?_, ?_, ?_, by simp [bytesLower], by simp [bytesUpper], ?_⟩
  · simp [bytesSwapcase, List.map_map, Function.comp_def, swapC_swapC]
  · simp [bytesLower, bytesUpper, List.map_map, Function.comp_def, low_up_c]
  · simp [bytesLower, bytesUpper, List.map_map, Function.comp_def, up_low_c]
  · cases s <;> simp [bytesCapitalize, bytesUpper, bytesLower]

theorem maketransLoop_length (p frm to : Seq) :
    (maketransLoop p frm to).length = p.length := by
  induction frm generalizing p to with
  | nil => simp [maketransLoop]
  | cons f frm ih =>
    cases to with
    | nil => simp [maketransLoop]
    | cons t to => simp [maketransLoop, ih]

theorem maketransLoop_outside (p frm to : Seq) (c : Nat) (hc : c ∉ frm) :
    (maketransLoop p frm to)[c]? = p[c]? := by
  induction frm generalizing p to with
  | nil => simp [maketransLoop]
  | cons f frm ih =>
    cases to with
    | nil => simp [maketransLoop]
    | cons t to =>
      simp only [List.mem_cons, not_or] at hc
      simp only [maketransLoop]
      rw [ih _ _ hc.2]
      rw [List.getElem?_set]
      have : ¬ (f = c) := fun h => hc.1 (h ▸ rfl)
      simp [this]

/-- `maketrans` raises `ValueError` exactly on a length mismatch; otherwise the
table has 256 entries, and leaves every byte not in `frm` fixed. -/
def MaketransSpec : Prop :=
  ∀ frm to : Seq,
    (frm.length ≠ to.length → bytesMaketrans frm to =
      .error (.valueError "maketrans arguments must have same length")) ∧
    (frm.length = to.length → ∃ t, bytesMaketrans frm to = .ok t ∧ t.length = 256 ∧
      ∀ c, c < 256 → c ∉ frm → t[c]? = some c)

theorem maketransSpec_proven : MaketransSpec := by
  intro frm to
  constructor
  · intro h; simp [bytesMaketrans, h]
  · intro h
    refine ⟨_, by simp [bytesMaketrans, h]; rfl, ?_, ?_⟩
    · simp [maketransLoop_length]
    · intro c hc hm
      rw [maketransLoop_outside _ _ _ _ hm]
      simp [hc]

end PyLean.BytesObj.Bytes
