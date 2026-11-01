import PyLean.LongObj.ComplexCore

/-!
String parsing for `complex()`: `complex_from_string_inner` and
`complex_subtype_from_string` (`Objects/complexobject.c:950-1101`), with the two
helpers they call, `_Py_string_to_number_with_underscores`
(`Python/pystrtod.c:345-402`) and `_PyUnicode_TransformDecimalAndSpaceToASCII`
(`Objects/unicodeobject.c:9515-9558`), and `float_from_string_inner`
(`Objects/floatobject.c:139-177`) for the twin property.

A `const char *` is the remaining suffix as a `List Nat` of code units, and
reading past the end gives the terminating NUL (`cur`). A string may hold NUL
anywhere, so `cur` returning `0` does not by itself mean the end: only `len`
does, exactly as in the C.

The conversion to double is a parameter, `Strtod R`. The Unicode database is a
parameter too, `UniDB`.
-/

namespace PyLean.LongObj.Cplx

open CDouble

/-- `*s`: the current character, or the terminating NUL. -/
def cur (s : List Nat) : Nat := s.headD 0

/-- `Py_ISSPACE`: `PY_CTF_SPACE` in `_Py_ctype_table`, `Python/pyctype.c`, is set
for exactly `\t \n \v \f \r` and space. -/
def isSpaceC (c : Nat) : Bool :=
  c == 32 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13

/-- `while (Py_ISSPACE(*s)) s++;`, with the offset carried along. -/
def skipSpace : List Nat → Nat → List Nat × Nat
  | [], i => ([], i)
  | c :: t, i => if isSpaceC c then skipSpace t (i + 1) else (c :: t, i)

/-- The conversion step of `PyOS_string_to_double`: the value, and how many
characters it consumed. `0` is `end == s`. -/
abbrev Strtod (R : Type) := List Nat → R × Nat

def chPlus : Nat := 43
def chMinus : Nat := 45
def chLParen : Nat := 40
def chRParen : Nat := 41
def chJ : Nat := 106
def chUpperJ : Nat := 74
def chUnderscore : Nat := 95

/-- `*s == 'j' || *s == 'J'`. -/
def isJ (c : Nat) : Bool := c == chJ || c == chUpperJ

/-- `*s == '+' || *s == '-'`. -/
def isSign (c : Nat) : Bool := c == chPlus || c == chMinus

section parse

variable {R : Type} [CDouble R]

/-- `y = *s == '+' ? 1.0 : -1.0;`, lines 997 and 1017. -/
def signOne (c : Nat) : R := if c == chPlus then one else neg one

/-- Lines 971-1026: `x`, `y`, the rest of the string and the offset, or `none`
for `goto parse_error`. -/
def parseBody (sd : Strtod R) (p : List Nat) (i : Nat) :
    Option (R × R × List Nat × Nat) :=
  let (z, n) := sd p
  if n ≠ 0 then
    -- all 4 forms starting with <float> land here
    let p := p.drop n
    let i := i + n
    if isSign (cur p) then
      -- <float><signed-float>j | <float><sign>j
      let x := z
      let (y₀, m) := sd p
      let (y, p, i) : R × List Nat × Nat :=
        if m ≠ 0 then (y₀, p.drop m, i + m)   -- <float><signed-float>j
        else (signOne (cur p), p.tail, i + 1) -- <float><sign>j
      if !isJ (cur p) then none
      else some (x, y, p.tail, i + 1)
    else if isJ (cur p) then
      some (zero, z, p.tail, i + 1)           -- <float>j
    else
      some (z, zero, p, i)                    -- <float>
  else
    -- not starting with <float>; must be <sign>j or j
    let (y, p, i) : R × List Nat × Nat :=
      if isSign (cur p) then (signOne (cur p), p.tail, i + 1)
      else (one, p, i)
    if !isJ (cur p) then none
    else some (zero, y, p.tail, i + 1)

def malformed : PyExc := .valueError "complex() arg is a malformed string"

/-- `complex_from_string_inner`, lines 930-1051, up to the allocation of the
result. `PyOS_string_to_double` reports failure as `end == s` with a `ValueError`
that the caller clears (lines 972-978, 985-991), so only `n = 0` is visible. -/
def complex_from_string_inner (sd : Strtod R) (s : List Nat) (len : Nat) : Py (Cx R) :=
  let (p, i) := skipSpace s 0
  let (p, i, got_bracket) : List Nat × Nat × Bool :=
    if cur p == chLParen then
      let (p', i') := skipSpace p.tail (i + 1)
      (p', i', true)
    else (p, i, false)
  match parseBody sd p i with
  | none => .error malformed
  | some (x, y, p, i) =>
    let (p, i) := skipSpace p i
    let tail : Option (List Nat × Nat) :=
      if got_bracket then
        if cur p != chRParen then none
        else some (skipSpace p.tail (i + 1))
      else some (p, i)
    match tail with
    | none => .error malformed
    | some (_, i) =>
      if i != len then .error malformed
      else .ok ⟨x, y⟩

end parse

/-- The loop of `_Py_string_to_number_with_underscores`, lines 367-382 of
`Python/pystrtod.c`: runs up to the first NUL. Returns the characters kept (in
reverse), the last character, and how far it got; `none` is `goto error`. -/
def underscoreScan : List Nat → Nat → List Nat → Nat → Option (List Nat × Nat × Nat)
  | [], prev, out, n => some (out, prev, n)
  | c :: t, prev, out, n =>
    if c == 0 then some (out, prev, n)
    else if c == chUnderscore then
      if !(48 ≤ prev && prev ≤ 57) then none
      else underscoreScan t c out (n + 1)
    else
      if prev == chUnderscore && !(48 ≤ c && c ≤ 57) then none
      else underscoreScan t c (c :: out) (n + 1)

/-- `strchr(s, '_')`: does an underscore occur before the first NUL? -/
def hasUnderscore (s : List Nat) : Bool :=
  (s.takeWhile (· != 0)).contains chUnderscore

/-- `_Py_string_to_number_with_underscores`, `Python/pystrtod.c:345-402`.
`objRepr` is the `%R` of the original object in the error message. -/
def withUnderscores {α : Type} (s : List Nat) (origLen : Nat) (what objRepr : String)
    (inner : List Nat → Nat → Py α) : Py α :=
  let err : Py α :=
    .error (.valueError s!"could not convert string to {what}: {objRepr}")
  if !hasUnderscore s then inner s origLen
  else
    match underscoreScan s 0 [] 0 with
    | none => err
    | some (out, prev, n) =>
      if prev == chUnderscore then err
      else if n != origLen then err
      else inner out.reverse out.length

/-- The Unicode database, as used by the transform. -/
structure UniDB where
  /-- `Py_UNICODE_ISSPACE`. -/
  isSpace : Nat → Bool
  /-- `Py_UNICODE_TODECIMAL`; `none` is `-1`. -/
  toDecimal : Nat → Option Nat

/-- The loop of `_PyUnicode_TransformDecimalAndSpaceToASCII`, lines 9635-9653.
An unconvertible character becomes `?` and ends the string. -/
def transformLoop (db : UniDB) : List Nat → List Nat
  | [] => []
  | ch :: t =>
    if ch < 127 then ch :: transformLoop db t
    else if db.isSpace ch then 32 :: transformLoop db t
    else
      match db.toDecimal ch with
      | none => [63]
      | some d => (48 + d) :: transformLoop db t

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`, lines 9614-9657: an ASCII
string comes back unchanged. -/
def transformDecimalAndSpace (db : UniDB) (s : List Nat) : List Nat :=
  if s.all (· < 128) then s else transformLoop db s

section parse2

variable {R : Type} [CDouble R]

/-- `complex_subtype_from_string` on a `str`, lines 1053-1069 and 1077-1080. The
`TypeError` branch on lines 1070-1075 is dead: the only caller,
`actual_complex_new`, has already checked `PyUnicode_Check` on line 1116. It is
mirrored in `complex_subtype_from_string` in `ComplexObj.lean`. -/
def complex_from_str (db : UniDB) (sd : Strtod R) (v : List Nat) (objRepr : String) :
    Py (Cx R) :=
  let s := transformDecimalAndSpace db v
  withUnderscores s s.length "complex" objRepr (complex_from_string_inner sd)

/-- `while (s < last && Py_ISSPACE(*s)) s++;`, `Objects/floatobject.c:146-148`. -/
def floatLead (len : Nat) : List Nat → Nat → Nat × List Nat
  | [], i => (i, [])
  | c :: t, i =>
    if i < len && isSpaceC c then floatLead len t (i + 1) else (i, c :: t)

/-- `while (s < last - 1 && Py_ISSPACE(last[-1])) last--;`, lines 167-169. `fuel`
counts the characters left to look at. -/
def floatTrail (s : List Nat) (i : Nat) : Nat → Nat → Nat
  | 0, last => last
  | fuel + 1, last =>
    if i + 1 < last && isSpaceC (s.getD (last - 1) 0) then floatTrail s i fuel (last - 1)
    else last

/-- `float_from_string_inner`, `Objects/floatobject.c:139-177`, up to the
allocation of the result. The twin of `complex_from_string_inner`. `last` is the
index one past the end. -/
def float_from_string_inner (sd : Strtod R) (s : List Nat) (len : Nat) (objRepr : String) :
    Py R :=
  let err : Py R := .error (.valueError s!"could not convert string to float: {objRepr}")
  let (i, p) := floatLead len s 0
  if i == len then err
  else
    let last := floatTrail s i len len
    let (x, n) := sd p
    if i + n != last then err else .ok x

/-- `PyFloat_FromString` on a `str`, `Objects/floatobject.c:180-227`, the path
that goes through the same transform and `float_from_string_inner`. -/
def float_from_str (db : UniDB) (sd : Strtod R) (v : List Nat) (objRepr : String) : Py R :=
  let s := transformDecimalAndSpace db v
  withUnderscores s s.length "float" objRepr (fun t n => float_from_string_inner sd t n objRepr)

end parse2

end PyLean.LongObj.Cplx
