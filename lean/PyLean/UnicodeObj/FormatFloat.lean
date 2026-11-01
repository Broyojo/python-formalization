import PyLean.UnicodeObj.FormatProps

/-!
What of float formatting can be modelled before `lean/PyLean/Binary64/` exists.
`parse_number` is string logic. The rest waits for a binary64 type.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `Py_ISDIGIT`. -/
def pyDigit (c : Nat) : Bool := decide (48 ≤ c) && decide (c ≤ 57)

/-- What `parse_number` does after the integer digits: `has_decimal`, `n_frac`,
`n_remainder`. -/
def parseRest (rest : List Nat) : Bool × Nat × Nat :=
  let hasDecimal := rest.head? == some 46
  let r := if hasDecimal then rest.tail else rest
  (hasDecimal, (r.takeWhile pyDigit).length, (r.dropWhile pyDigit).length)

/-- `parse_number`, formatter_unicode.c:489-516: the digits before the point,
`has_decimal`, `n_frac`, `n_remainder`. -/
def parseNumber (s : Str) : Nat × Bool × Nat × Nat :=
  ((s.takeWhile pyDigit).length, parseRest (s.dropWhile pyDigit))

/-- `parse_number` splits the number with nothing lost: the digits, the decimal point, the
fraction and the remainder add up to its length, for every string. -/
def ParseNumberSplit : Prop :=
  ∀ s : Str,
    (parseNumber s).1 + (if (parseNumber s).2.1 = true then 1 else 0) + (parseNumber s).2.2.1 +
      (parseNumber s).2.2.2 = s.length

theorem take_drop_length (p : Nat → Bool) (l : List Nat) :
    (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  rw [← List.length_append, List.takeWhile_append_dropWhile]

theorem split_rest (rest : List Nat) :
    (if (parseRest rest).1 = true then 1 else 0) + (parseRest rest).2.1 + (parseRest rest).2.2 =
      rest.length := by
  simp only [parseRest]
  by_cases hd : (rest.head? == some 46) = true
  · simp only [hd, if_true]
    have h2 := take_drop_length pyDigit rest.tail
    cases rest with
    | nil => simp at hd
    | cons x xs =>
      simp only [List.tail_cons, List.length_cons] at *
      omega
  · simp only [hd, if_false, Bool.false_eq_true]
    have h2 := take_drop_length pyDigit rest
    omega

theorem parseNumberSplit_proven : ParseNumberSplit := by
  intro s
  have h1 := take_drop_length pyDigit s
  have h2 := split_rest (s.dropWhile pyDigit)
  show (s.takeWhile pyDigit).length + (if (parseRest (s.dropWhile pyDigit)).1 = true then 1 else 0) +
    (parseRest (s.dropWhile pyDigit)).2.1 + (parseRest (s.dropWhile pyDigit)).2.2 = s.length
  omega

/-- `format(v, '')` is `str(v)` for an int, and `format(s, '')` is `s`: the empty-spec branch
of the dispatchers, which goes through `format_obj` for a subclass. -/
def FormatEmptySpec : Prop :=
  (∀ (v : Int) (name : String) (shown : Str),
    formatLongAdvanced v name [] shown = .ok (some shown)) ∧
  (∀ s : Str, formatStrAdvanced s [] = .ok s)

theorem formatEmptySpec_proven : FormatEmptySpec :=
  ⟨fun _ _ _ => rfl, fun _ => rfl⟩

/-- A placeholder for the entries that wait on `lean/PyLean/Binary64/`. There is no binary64
type yet to state them over, so each entry gives its property in words and points here.
It is `False` so that it cannot be proven by accident: such an entry has to get a real
statement before it can be settled. -/
def PendingBinary64 : Prop := False

end PyLean.UnicodeObj
