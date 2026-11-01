import PyLean.Pickle.IntLineProps

/-! Lemmas about the text parsers. -/

namespace PyLean.Pickle

open PyLean

theorem takeWhile_ne_zero_of_not_mem {l : Bytes} (h : (0 : UInt8) ∉ l) :
    l.takeWhile (· ≠ 0) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : a ≠ 0 := fun e => h (e ▸ List.mem_cons_self)
    have hl : (0 : UInt8) ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.takeWhile_cons_of_pos (by simpa using ha), ih hl]

theorem takeWhile_ne_zero_append_zero {l : Bytes} (r : Bytes) (h : (0 : UInt8) ∉ l) :
    (l ++ 0 :: r).takeWhile (· ≠ 0) = l := by
  induction l with
  | nil => rw [List.nil_append, List.takeWhile_cons_of_neg (by simp)]
  | cons a l ih =>
    have ha : a ≠ 0 := fun e => h (e ▸ List.mem_cons_self)
    have hl : (0 : UInt8) ∉ l := fun m => h (List.mem_cons_of_mem _ m)
    rw [List.cons_append, List.takeWhile_cons_of_pos (by simpa using ha), ih hl]

theorem skipSpace_append_space (l : Bytes) {c : UInt8} (hc : isSpace c = true) :
    skipSpace (l ++ [c]) = if skipSpace l = [] then [] else skipSpace l ++ [c] := by
  induction l with
  | nil => simp [skipSpace, hc]
  | cons a l ih =>
    simp only [List.cons_append, skipSpace]
    split
    · exact ih
    · simp

set_option maxRecDepth 20000 in
theorem isSpace_not_digit_all : ∀ n < 256, isSpace n.toUInt8 = true → isDigit n.toUInt8 = false := by
  decide

theorem isSpace_not_digit {c : UInt8} (hc : isSpace c = true) : isDigit c = false := by
  have := isSpace_not_digit_all c.toNat c.toNat_lt
  rw [show c.toNat.toUInt8 = c by simp] at this
  exact this hc

theorem isSpace_ne_underscore {c : UInt8} (hc : isSpace c = true) : c ≠ 0x5f := by
  intro h; subst h; simp [isSpace] at hc

theorem scanDigits_append (p : Bool) (l : Bytes) {c : UInt8} (hd : isDigit c = false) (hu : c ≠ 0x5f) :
    scanDigits p (l ++ [c]) = ((scanDigits p l).1, (scanDigits p l).2.1, (scanDigits p l).2.2 ++ [c]) := by
  have hu' : (c == 0x5f) = false := by simpa using hu
  induction l generalizing p with
  | nil => simp [scanDigits, hd, hu']
  | cons a l ih =>
    simp only [List.cons_append, scanDigits]
    split
    · simp [ih]
    · split
      · split
        · simp
        · exact ih true
      · simp

theorem skipSpace_nil_iff (l : Bytes) {c : UInt8} (hc : isSpace c = true) :
    skipSpace (l ++ [c]) = [] ↔ skipSpace l = [] := by
  rw [skipSpace_append_space l hc]; split <;> simp_all

theorem lfsBase_append_space (neg : Bool) (r : Bytes) {c : UInt8} (hc : isSpace c = true) :
    lfsBase neg (r ++ [c]) = lfsBase neg r := by
  have hd := isSpace_not_digit hc
  have hu := isSpace_ne_underscore hc
  cases r with
  | nil =>
    have hu' : (c == 0x5f) = false := by simpa using hu
    simp [lfsBase, scanDigits, hd, hu', hc, skipSpace]
    split <;> simp_all
  | cons a r =>
    by_cases ha : a = 0x5f
    · subst ha; simp [lfsBase]
    · have e1 : lfsBase neg (a :: r ++ [c]) = (let (ds, ok, rest) := scanDigits false (a :: r ++ [c])
          if !ok then PLRes.syntax else if ds = [] then .syntax else if skipSpace rest ≠ [] then .syntax
          else if ds.length > maxStrDigits then .limit ds.length
          else .ok (if neg then -(digitsVal ds : Int) else digitsVal ds)) := by
        simp only [List.cons_append, lfsBase]; split
        · rename_i h; simp at h; exact absurd h.1 ha
        · rfl
      have e2 : lfsBase neg (a :: r) = (let (ds, ok, rest) := scanDigits false (a :: r)
          if !ok then PLRes.syntax else if ds = [] then .syntax else if skipSpace rest ≠ [] then .syntax
          else if ds.length > maxStrDigits then .limit ds.length
          else .ok (if neg then -(digitsVal ds : Int) else digitsVal ds)) := by
        simp only [lfsBase]; split
        · rename_i h; simp at h; exact absurd h.1 ha
        · rfl
      rw [e1, e2, scanDigits_append false (a :: r) hd hu]
      simp only [ne_eq, skipSpace_nil_iff _ hc]

/-- A trailing whitespace byte does not change `PyLong_FromString`. -/
theorem pyLongFromString_append_space (s : Bytes) {c : UInt8} (hc : isSpace c = true) :
    pyLongFromString (s ++ [c]) = pyLongFromString s := by
  unfold pyLongFromString
  rw [skipSpace_append_space s hc]
  by_cases h : skipSpace s = []
  · rw [if_pos h, h]
  · rw [if_neg h]
    generalize skipSpace s = s1 at h ⊢
    cases s1 with
    | nil => exact absurd rfl h
    | cons a r =>
      simp only [List.cons_append]
      by_cases h1 : a = 0x2b
      · subst h1; exact lfsBase_append_space false r hc
      · by_cases h2 : a = 0x2d
        · subst h2; exact lfsBase_append_space true r hc
        · have e1 : ∀ t : Bytes, signSplit (a :: t) = (false, a :: t) := by
            intro t; unfold signSplit; split <;> rename_i heq
            · simp at heq; exact absurd heq.1 h1
            · simp at heq; exact absurd heq.1 h2
            · rfl
          simp only [e1]
          have := lfsBase_append_space false (a :: r) hc
          simpa using this

end PyLean.Pickle
