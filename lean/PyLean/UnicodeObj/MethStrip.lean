import PyLean.UnicodeObj.MethBasic

/-!
`str.strip`, `str.lstrip`, `str.rstrip` (Objects/unicodeobject.c:12317-12558) with the helpers
they run: `PyUnicode_FindChar` (:9692-9709), `findchar` (:1009-1036) and `PyUnicode_Substring`
(:12388-12419).

The C loops walk indices; the models walk the same indices with the same tests in the same
order (`termination_by` the distance left), and keep both representations of `self`: the
1-byte table lookup of the ASCII branch of `do_strip` and the `Py_UNICODE_ISSPACE` of the
other branch; the bloom test and then `PyUnicode_FindChar` of `_PyUnicode_XStrip`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-! ## `PyUnicode_Substring` -/

/-- `PyUnicode_Substring`, unicodeobject.c:12388-12419. Both branches (`_PyUnicode_FromASCII`
and `PyUnicode_FromKindAndData`) copy the characters `start .. end-1`; returning `self`
unchanged is modelled by its value. -/
def pyUnicodeSubstring (s : Str) (start «end» : Int) : Py Str :=
  let length : Int := s.length
  let «end» := min «end» length
  if start = 0 ∧ «end» = length then .ok s
  else if start < 0 ∨ «end» < 0 then .error (.indexError "string index out of range")
  else if start ≥ length ∨ «end» < start then .ok []
  else .ok ((s.drop start.toNat).take («end» - start).toNat)

/-! ## `findchar` and `PyUnicode_FindChar` -/

/-- The PEP 393 kind holding `s`: `PyUnicode_KIND`, 1, 2 or 4 bytes. The ASCII and Latin-1
strings are both 1-byte. -/
def kindWidth (s : Str) : Nat := (canonicalKind s).width

/-- `ucs1lib_find_char` and friends (Objects/stringlib/fastsearch.h): first (or last) index
whose unit equals the unit `u`; -1 when none. -/
def findUnit (units : List Nat) (u : Nat) : Int :=
  match units.findIdx? (· == u) with
  | some i => i
  | none => -1

def rfindUnit (units : List Nat) (u : Nat) : Int :=
  match units.reverse.findIdx? (· == u) with
  | some i => (units.length : Int) - 1 - i
  | none => -1

/-- `findchar`, unicodeobject.c:1009-1036, on a buffer of `width`-byte units. The search
functions take the character cast to the unit type, `(Py_UCS1) ch` or `(Py_UCS2) ch`, so a
character that does not survive the cast is reported missing first (:1016-1017, :1023-1024). -/
def findchar (units : List Nat) (width : Nat) (ch : Nat) (direction : Int) : Int :=
  let u := ch % 2 ^ (8 * width)
  if width ≠ 4 ∧ u ≠ ch then -1
  else if direction > 0 then findUnit units u else rfindUnit units u

/-- `PyUnicode_FindChar`, unicodeobject.c:9692-9709. `ADJUST_INDICES` is
`StrSearch.adjustIndices`. -/
def pyUnicodeFindChar (str : Str) (ch : Nat) (start «end» : Int) (direction : Int) : Int :=
  let (start, «end») := StrSearch.adjustIndices start «end» str.length
  if «end» - start < 1 then -1
  else
    let result := findchar (StrSearch.window str start («end» - start)) (kindWidth str) ch direction
    if result = -1 then -1 else start + result

/-! ## The loops -/

/-- `while (i < len) { if (!strip(data[i])) break; i++; }` -/
def leftScan (strip : Nat → Bool) (s : Str) (i : Nat) : Nat :=
  if i < s.length then
    if strip (s.getD i 0) then leftScan strip s (i + 1) else i
  else i
termination_by s.length - i

/-- `j--; while (j >= i) { if (!strip(data[j])) break; j--; } j++;` from `j = len`. -/
def rightScan (strip : Nat → Bool) (s : Str) (i : Nat) (j : Int) : Int :=
  if j ≥ i then
    if strip (s.getD j.toNat 0) then rightScan strip s i (j - 1) else j
  else j
termination_by (j + 1 - i).toNat

/-- `LEFTSTRIP`, `RIGHTSTRIP`, `BOTHSTRIP`, unicodeobject.c:12318-12320. -/
inductive StripKind where
  | left | right | both
  deriving DecidableEq, Repr

/-- `STRIPNAME`, unicodeobject.c:12323. -/
def StripKind.name : StripKind → String
  | .left => "lstrip"
  | .right => "rstrip"
  | .both => "strip"

/-- The shared shape of the three loops: the left scan unless `RIGHTSTRIP`, the right scan
unless `LEFTSTRIP`, then `PyUnicode_Substring(self, i, j)`. -/
def stripWith (strip : Nat → Bool) (st : StripKind) (s : Str) : Py Str :=
  let len := s.length
  let i := if st ≠ .right then leftScan strip s 0 else 0
  let j : Int := if st ≠ .left then rightScan strip s i (len - 1) + 1 else len
  pyUnicodeSubstring s i j

/-- `_Py_ascii_whitespace[ch]`, unicodeobject.c:381-409. -/
def asciiWhitespaceTable (ch : Nat) : Bool := asciiWhitespace.contains ch

/-- `_PyUnicode_XStrip`, unicodeobject.c:12329-12373: a character is stripped when it passes
the bloom filter of `sepobj` (:12349, :12362) and `PyUnicode_FindChar(sepobj, ch, 0, seplen, 1)`
finds it (:12351, :12364). -/
def xstrip (s : Str) (st : StripKind) (sep : Str) : Py Str :=
  let sepmask := makeBloomMask sep
  stripWith (fun ch => bloom sepmask ch && decide (pyUnicodeFindChar sep ch 0 sep.length 1 ≥ 0)) st s

/-- `do_strip`, unicodeobject.c:12422-12482: the ASCII branch reads `_Py_ascii_whitespace`
(:12428-12452), the other `Py_UNICODE_ISSPACE` (:12453-12478). -/
def doStrip (s : Str) (st : StripKind) : Py Str :=
  if isAscii s then stripWith asciiWhitespaceTable st s
  else stripWith isSpace st s

/-- `do_argstrip`, unicodeobject.c:12485-12499. -/
def doArgstrip (s : Str) (st : StripKind) (sep : Arg) : Py Str :=
  match sep with
  | .none => doStrip s st
  | .str sep => xstrip s st sep
  | _ => .error (.typeError s!"{st.name} arg must be None or str")

/-- `unicode_strip_impl` (:12515-12519), `unicode_lstrip_impl` (:12534-12538),
`unicode_rstrip_impl` (:12553-12557). -/
def unicodeStrip (s : Str) (chars : Arg) : Py Str := doArgstrip s .both chars
def unicodeLstrip (s : Str) (chars : Arg) : Py Str := doArgstrip s .left chars
def unicodeRstrip (s : Str) (chars : Arg) : Py Str := doArgstrip s .right chars

end PyLean.UnicodeObj
