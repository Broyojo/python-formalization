import PyLean.StrSearch.Basic

/-!
`strip` family and `splitlines`: the `str` ASCII fast path against the
general path, `bytearray`'s explicit whitespace list against `bytes`'
`Py_ISSPACE`, and `str` against `bytes` away from the documented
differences in what counts as whitespace or a line break.
-/

set_option linter.deprecated false

namespace PyLean.StrSearch

open PyLean

theorem takeWhile_congr {f g : Nat → Bool} : ∀ {l : Seq}, (∀ x ∈ l, f x = g x) →
    l.takeWhile f = l.takeWhile g
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.takeWhile_cons, h a (by simp)]
    split
    · rw [takeWhile_congr (fun x hx => h x (by simp [hx]))]
    · rfl

theorem dropWhile_congr {f g : Nat → Bool} : ∀ {l : Seq}, (∀ x ∈ l, f x = g x) →
    l.dropWhile f = l.dropWhile g
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.dropWhile_cons, h a (by simp)]
    split
    · exact dropWhile_congr (fun x hx => h x (by simp [hx]))
    · rfl

theorem stripWith_congr {f g : Nat → Bool} (t : StripType) {s : Seq} (h : ∀ x ∈ s, f x = g x) :
    stripWith f t s = stripWith g t s := by
  simp only [stripWith]
  rw [takeWhile_congr h]
  have h' : ∀ x ∈ (s.drop (if t ≠ .right then (s.takeWhile g).length else 0)).reverse, f x = g x :=
    fun x hx => h x (List.mem_of_mem_drop (List.mem_reverse.mp hx))
  rw [dropWhile_congr h']

theorem lineBreak_congr {f g : Nat → Bool} (keep : Bool) {s : Seq} (h : ∀ x ∈ s, f x = g x) :
    lineBreak f keep s = lineBreak g keep s := by
  have hnf : ∀ x ∈ s, (!f x) = (!g x) := fun x hx => by rw [h x hx]
  simp only [lineBreak, takeWhile_congr hnf, dropWhile_congr hnf]

theorem splitlines_congr {f g : Nat → Bool} (keep : Bool) :
    ∀ (s : Seq), (∀ x ∈ s, f x = g x) → splitlines f keep s = splitlines g keep s := by
  intro s
  induction s using (measure List.length).wf.induction with
  | _ s ih =>
    intro h
    unfold splitlines
    by_cases hs : s = []
    · simp [hs]
    · simp only [hs, ↓reduceDIte, lineBreak_congr keep h]
      congr 1
      exact ih _ (lineBreak_snd_len g keep hs) (fun x hx => h x (lineBreak_snd_mem g keep hx))

theorem lineBreak_append (isLB : Nat → Bool) (s : Seq) :
    (lineBreak isLB true s).1 ++ (lineBreak isLB true s).2 = s := by
  have e := List.takeWhile_append_dropWhile (p := fun x => !isLB x) (l := s)
  unfold lineBreak
  split
  · next h => rw [h] at e; simpa using e
  · next c cs h =>
    rw [h] at e
    split
    · next hc =>
      obtain ⟨rfl, h2⟩ := hc
      cases cs with
      | nil => simp at h2
      | cons d ds =>
        simp at h2; subst h2
        simpa using e
    · simpa using e

theorem splitlines_flatten (isLB : Nat → Bool) :
    ∀ s : Seq, (splitlines isLB true s).flatten = s := by
  intro s
  induction s using (measure List.length).wf.induction with
  | _ s ih =>
    rw [splitlines]
    by_cases hs : s = []
    · simp [hs]
    · simp only [hs, ↓reduceDIte, List.flatten_cons]
      rw [ih _ (lineBreak_snd_len isLB true hs), lineBreak_append]

/-- Characters that `str.isspace()` accepts but `bytes.isspace()` does not,
among the byte values. -/
def strOnlySpace (c : Nat) : Bool := (0x1c ≤ c ∧ c ≤ 0x1f) || c == 0x85 || c == 0xa0

/-- Characters that end a line for `str.splitlines()` but not for
`bytes.splitlines()`, among the byte values. -/
def strOnlyLinebreak (c : Nat) : Bool := c == 11 || c == 12 || (0x1c ≤ c ∧ c ≤ 0x1e) || c == 0x85

/-- `str.strip`/`lstrip`/`rstrip` without `chars` take an ASCII fast path
(`_Py_ascii_whitespace`, unicodeobject.c:12428-12452) that agrees with the
general `Py_UNICODE_ISSPACE` path; `bytearray`'s explicit list `"\t\n\r\f\v "`
(bytearrayobject.c:2433-2435) agrees with `bytes`' `Py_ISSPACE`; and `str`
agrees with `bytes` on byte-valued strings without the characters only `str`
treats as whitespace (U+001C..U+001F, U+0085, U+00A0); with an explicit
`chars` argument `str`, `bytes` and `bytearray` always agree. -/
def StripPaths : Prop :=
  ∀ (s : Seq) (chars : Option Seq) (t : StripType),
    strStrip s none t = stripWith uniSpace t s ∧
    bytearrayStrip s chars t = bytesStrip s chars t ∧
    ((∀ x ∈ s, x < 256 ∧ strOnlySpace x = false) → strStrip s none t = bytesStrip s none t) ∧
    (∀ cs, strStrip s (some cs) t = bytesStrip s (some cs) t)

theorem stripPaths_proven : StripPaths := by
  intro s chars t
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [strStrip]
    split
    · next ha =>
      apply stripWith_congr
      intro x hx
      have : x < 128 := by simpa using List.all_eq_true.mp ha x hx
      simp only [asciiWhitespaceTable, uniSpace]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        List.contains_cons, List.contains_nil, Bool.or_false]
      omega
    · rfl
  · cases chars with
    | some cs => rfl
    | none =>
      simp only [bytearrayStrip, bytesStrip, Option.getD_none]
      apply stripWith_congr
      intro x _
      simp only [byteSpace]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        List.contains_cons, List.contains_nil, Bool.or_false]
      omega
  · intro h
    simp only [strStrip, bytesStrip]
    split
    · next ha =>
      apply stripWith_congr
      intro x hx
      have : x < 128 := by simpa using List.all_eq_true.mp ha x hx
      have h2 := (h x hx).2
      simp only [strOnlySpace, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h2
      simp only [asciiWhitespaceTable, byteSpace]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        List.contains_cons, List.contains_nil, Bool.or_false]
      omega
    · apply stripWith_congr
      intro x hx
      have h1 := (h x hx).1
      have h2 := (h x hx).2
      simp only [strOnlySpace, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h2
      simp only [uniSpace, byteSpace]
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
        List.contains_cons, List.contains_nil, Bool.or_false]
      omega
  · intro cs; rfl

/-- `str.splitlines` and `bytes.splitlines` agree on byte-valued strings
without the line boundaries only `str` recognises (\v, \f, \x1c, \x1d,
\x1e, \x85; documented in stdtypes.rst for `str.splitlines`); and with
`keepends=True` the lines concatenate back to the string. -/
def SplitlinesStrBytes : Prop :=
  ∀ (s : Seq) (keep : Bool),
    ((∀ x ∈ s, x < 256 ∧ strOnlyLinebreak x = false) → strSplitlines s keep = bytesSplitlines s keep) ∧
    (strSplitlines s true).flatten = s ∧ (bytesSplitlines s true).flatten = s

theorem splitlinesStrBytes_proven : SplitlinesStrBytes := by
  intro s keep
  refine ⟨?_, splitlines_flatten _ s, splitlines_flatten _ s⟩
  intro h
  apply splitlines_congr
  intro x hx
  have h2 := (h x hx).2
  have h1 := (h x hx).1
  simp only [strOnlyLinebreak, Bool.or_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at h2
  simp only [uniLinebreak, byteLinebreak]
  rw [Bool.eq_iff_iff]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.contains_cons, List.contains_nil, Bool.or_false]
  omega

end PyLean.StrSearch
