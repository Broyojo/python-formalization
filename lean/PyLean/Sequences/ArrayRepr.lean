import PyLean.Sequences.ArrayItems

/-!
`repr(a)` (`array_repr`, `Modules/arraymodule.c:2702-2727`, CPython 3.15.2) against the promise of
Doc/library/array.rst:298-312: "The string representation is guaranteed to be able to be converted
back to an array with the same type and value using `eval()`, so long as the `array` class has
been imported using `from array import array`. Variables `inf` and `nan` must also be defined if
it contains corresponding floating-point values."
-/

namespace PyLean.Sequences

open PyLean

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_'
def isIdChar (c : Char) : Bool := c.isAlphanum || c == '_'

/-- The names in an expression text: maximal runs of letters, digits and `_` that start with a
letter or `_` not preceded by a digit, letter, `_` or `.` (so the `e` of `1e+300` and the `j` of
`2j` belong to their number), outside string literals. `q` is the open quote, `num` whether the
previous character continues a number, `cur` the name being read. -/
def identsGo : List Char → Option Char → Bool → String → List String → List String
  | [], _, _, cur, acc => if cur = "" then acc else acc ++ [cur]
  | c :: cs, some q, _, _, acc => if c == q then identsGo cs none false "" acc else identsGo cs (some q) false "" acc
  | c :: cs, none, num, cur, acc =>
    let acc := if cur = "" ∨ isIdChar c then acc else acc ++ [cur]
    if cur ≠ "" ∧ isIdChar c then identsGo cs none false (cur.push c) acc
    else if c == '\'' || c == '"' then identsGo cs (some c) false "" acc
    else if isIdStart c && !num then identsGo cs none false (String.singleton c) acc
    else identsGo cs none (isIdChar c || c == '.') "" acc

def identsOf (s : String) : List String := identsGo s.toList none false "" []

/-- What `eval(repr(a))` needs, for the typecodes whose initializer is a list of numbers: the
only names in `repr(a)` are the array type and `inf` and `nan`, the names the documentation asks
to be defined.

Refuted for `Zd` and `Zf`, new in 3.15: an item is a complex number, and `complex_repr` writes an
infinite or NaN imaginary part as `infj` or `nanj` (`array('Zd', [infj])`,
`array('Zd', [(1+nanj)])`), names that `eval` cannot resolve with `inf` and `nan` defined. -/
def ArrayReprNames : Prop :=
  ∀ (a : Arr) (s : String), a.Decodes → a.tc ≠ .u → a.tc ≠ .w → arrRepr a = .ok s →
    ∀ x ∈ identsOf s, x = a.tname ∨ x = "inf" ∨ x = "nan"

theorem arrayReprNames_refuted : ¬ ArrayReprNames := by
  intro h
  let a : Arr := ⟨.Zd, [0x7ff0000000000000 * 18446744073709551616], 1, true, 0, "array"⟩
  have hd : a.Decodes := by
    intro x hx
    simp only [a, List.mem_singleton] at hx
    subst hx
    exact ⟨_, rfl⟩
  have hr : arrRepr a = .ok "array('Zd', [infj])" := by decide +kernel
  have := h a _ hd (by decide) (by decide) hr "infj" (by decide +kernel)
  revert this
  decide

/-- Two `w` arrays of the same type with the same `repr` hold the same characters: a
consequence of the `eval` promise for the typecode whose initializer is a string.

Refuted: `array_repr` takes the string from `tounicode()` (:2716), which decodes UTF-32 with
`byteorder = 0` and so drops a leading U+FEFF as a byte order mark
(bugs/sequences-array-w-tounicode-bom.yaml): `array('w', '﻿a')` and `array('w', 'a')` both
print as `array('w', 'a')`. -/
def ArrayReprWInjective : Prop :=
  ∀ (a b : Arr), a.tc = .w → b.tc = .w → a.tname = b.tname → a.Decodes → b.Decodes →
    arrRepr a = arrRepr b → a.items = b.items

theorem arrayReprWInjective_refuted : ¬ ArrayReprWInjective := by
  intro h
  let a : Arr := ⟨.w, [65279, 97], 2, true, 0, "array"⟩
  let b : Arr := ⟨.w, [97], 1, true, 0, "array"⟩
  have ha : a.Decodes := by
    intro x hx
    simp only [a, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> exact ⟨_, rfl⟩
  have hb : b.Decodes := by
    intro x hx
    simp only [b, List.mem_singleton] at hx
    subst hx
    exact ⟨_, rfl⟩
  have hr : arrRepr a = arrRepr b := by decide +kernel
  have := h a b rfl rfl rfl ha hb hr
  revert this
  decide

end PyLean.Sequences
