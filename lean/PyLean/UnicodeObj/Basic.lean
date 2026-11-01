import PyLean.Core
import PyLean.StrSearch.Model

/-!
Shared vocabulary of the `UnicodeObj` model (`Objects/unicodeobject.c`,
CPython 3.14.7).

A `str` is the list of its code points and a `bytes` the list of its byte
values. Code points are `Nat`, not `Char`: Python strings can hold lone
surrogates, which Lean's `Char` and `String` cannot. Every model that takes a
`Str` may assume the type invariant `Str.Valid` (each code point at most
0x10FFFF), and a property that needs it says so.
-/

namespace PyLean.UnicodeObj

open PyLean

abbrev Str := StrSearch.Seq
abbrev Bytes := StrSearch.Seq

/-- `MAX_UNICODE`, Objects/unicodeobject.c. -/
def maxUnicode : Nat := 0x10FFFF

/-- Type invariant of `str`: every element is a code point. -/
def Str.Valid (s : Str) : Prop := ∀ c ∈ s, c ≤ maxUnicode

/-- Type invariant of `bytes`. -/
def Bytes.Valid (b : Bytes) : Prop := ∀ c ∈ b, c < 256

/-- Largest code point, 0 for the empty string. -/
def maxCharOf (s : Str) : Nat := s.foldl max 0

/-- The four PEP 393 representations. `ascii` is compact-ASCII (1 byte per
character with `state.ascii` set). -/
inductive Kind where
  | ascii | ucs1 | ucs2 | ucs4
  deriving Repr, DecidableEq, Inhabited

/-- Bytes per character (`PyUnicode_KIND`). -/
def Kind.width : Kind → Nat
  | .ascii | .ucs1 => 1
  | .ucs2 => 2
  | .ucs4 => 4

/-- `PyUnicode_MAX_CHAR_VALUE`, Include/cpython/unicodeobject.h. -/
def Kind.maxChar : Kind → Nat
  | .ascii => 0x7f
  | .ucs1 => 0xff
  | .ucs2 => 0xffff
  | .ucs4 => 0x10ffff

/-- The kind selection of `PyUnicode_New`, unicodeobject.c:1278-1371. -/
def kindOfMax (maxchar : Nat) : Kind :=
  if maxchar < 128 then .ascii
  else if maxchar < 256 then .ucs1
  else if maxchar < 65536 then .ucs2
  else .ucs4

/-- The canonical kind of a string: what `_PyUnicode_CheckConsistency`
requires of every ready string. -/
def canonicalKind (s : Str) : Kind := kindOfMax (maxCharOf s)

/-- The code points of an ASCII Lean string literal. -/
def lit (s : String) : Str := s.toList.map Char.toNat

/-- Lower-case hexadecimal digit. -/
def hexLower (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- `width` lower-case hex digits of `n`, most significant first. -/
def hexDigits (width n : Nat) : Str :=
  (List.range width).reverse.map fun i => hexLower ((n >>> (4 * i)) &&& 15)

/-- Render code points as a Lean string, for exception messages. Models only
pass valid scalar values here; anything else prints as U+FFFD. -/
def toLeanString (s : Str) : String :=
  String.ofList (s.map fun c => if c.isValidChar then Char.ofNat c else '�')

end PyLean.UnicodeObj
