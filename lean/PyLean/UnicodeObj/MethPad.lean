import PyLean.UnicodeObj.MethBasic

/-!
`str.center`, `str.ljust`, `str.rjust`, `str.zfill` (Objects/unicodeobject.c), their shared
`pad` (:10258-10297), the fill-character converter `convert_uc` (:10910-10927), the clinic
wrappers (Objects/clinic/unicodeobject.c.h) and the size checks of `PyUnicode_New`
(:1278-1371).
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `sizeof(PyASCIIObject)` and `sizeof(PyCompactUnicodeObject)` on a 64-bit build
(`sys.getsizeof('') == 41`, `sys.getsizeof('Ā') == 60`). -/
def asciiStructSize : Int := 40
def compactStructSize : Int := 56

/-- `char_size` and `struct_size` of `PyUnicode_New` for `maxchar`, unicodeobject.c:1295-1317. -/
def newSizes (maxchar : Nat) : Int × Int :=
  if maxchar < 128 then (1, asciiStructSize)
  else if maxchar < 256 then (1, compactStructSize)
  else if maxchar < 65536 then (2, compactStructSize)
  else (4, compactStructSize)

def memoryError : PyExc := .named "MemoryError" ""

/-- The checks of `PyUnicode_New`, unicodeobject.c:1278-1329, before the allocation:
the empty string, a too-large `maxchar` (:1310-1314), a negative size (:1320-1324), and
the size limit that keeps `struct_size + (size + 1) * char_size` from overflowing
(:1325-1326). A failure of `PyObject_Malloc` itself (:1332-1335) is not modelled. -/
def pyUnicodeNew (size : Int) (maxchar : Nat) : Py Unit :=
  if size = 0 then .ok ()
  else
    let (charSize, structSize) := newSizes maxchar
    if maxchar ≥ 65536 ∧ maxchar > maxUnicode then
      .error (.named "SystemError" "invalid maximum character passed to PyUnicode_New")
    else if size < 0 then .error (.named "SystemError" "Negative size passed to PyUnicode_New")
    else if size > (ssizeMax - structSize) / charSize - 1 then .error memoryError
    else .ok ()

/-- `PyUnicode_MAX_CHAR_VALUE`: the largest value of the kind holding `s`. -/
def maxCharValue (s : Str) : Nat := (canonicalKind s).maxChar

/-- `pad`, unicodeobject.c:10258-10297. -/
def pad (s : Str) (left right : Int) (fill : Nat) : Py Str := do
  let left := if left < 0 then 0 else left
  let right := if right < 0 then 0 else right
  if left = 0 ∧ right = 0 then return s
  if left > ssizeMax - s.length ∨ right > ssizeMax - (left + s.length) then
    throw (.overflowError "padded string is too long")
  let maxchar := max (maxCharValue s) fill
  pyUnicodeNew (left + s.length + right) maxchar
  return List.replicate left.toNat fill ++ s ++ List.replicate right.toNat fill

/-- `convert_uc`, unicodeobject.c:10910-10927. -/
def convertUc : Arg → Py Nat
  | .str c =>
    if c.length ≠ 1 then .error (.typeError "The fill character must be exactly one character long")
    else .ok (c.getD 0 0)
  | a => .error (.typeError s!"The fill character must be a unicode character, not {a.tpName}")

/-- `unicode_center_impl`, unicodeobject.c:10943-10955. -/
def unicodeCenterImpl (s : Str) (width : Int) (fill : Nat) : Py Str :=
  if (s.length : Int) ≥ width then .ok s
  else
    let marg := width - s.length
    -- `marg` and `width` are positive here, so `&` acts on their magnitudes
    let left : Int := marg / 2 + ((marg.toNat &&& (width.toNat &&& 1) : Nat) : Int)
    pad s left (marg - left) fill

/-- `unicode_ljust_impl`, unicodeobject.c:12294-12301. -/
def unicodeLjustImpl (s : Str) (width : Int) (fill : Nat) : Py Str :=
  if (s.length : Int) ≥ width then .ok s else pad s 0 (width - s.length) fill

/-- `unicode_rjust_impl`, unicodeobject.c:12858-12865. -/
def unicodeRjustImpl (s : Str) (width : Int) (fill : Nat) : Py Str :=
  if (s.length : Int) ≥ width then .ok s else pad s (width - s.length) 0 fill

/-- `unicode_zfill_impl`, unicodeobject.c:13331-13362. `PyUnicode_READ(kind, data, fill)` reads
the first character of `self`, or the terminating NUL that `PyUnicode_New` writes when `self`
is empty (:1351-1364). -/
def unicodeZfillImpl (s : Str) (width : Int) : Py Str := do
  if (s.length : Int) ≥ width then return s
  let fill := width - s.length
  let u ← pad s fill 0 48
  let chr := (u ++ [0]).getD fill.toNat 0
  if chr = 43 ∨ chr = 45 then
    return (u.set 0 chr).set fill.toNat 48
  return u

/-- The clinic wrappers (Objects/clinic/unicodeobject.c.h): `width` through the `Py_ssize_t`
converter first (:115-126 for `center`), then `fillchar` through `convert_uc`, default `' '`. -/
def fillArg : Option Arg → Py Nat
  | none => .ok 32
  | some a => convertUc a

def unicodeCenter (s : Str) (width : Arg) (fill : Option Arg) : Py Str := do
  let w ← argSsizeObj width
  let f ← fillArg fill
  unicodeCenterImpl s w f

def unicodeLjust (s : Str) (width : Arg) (fill : Option Arg) : Py Str := do
  let w ← argSsizeObj width
  let f ← fillArg fill
  unicodeLjustImpl s w f

def unicodeRjust (s : Str) (width : Arg) (fill : Option Arg) : Py Str := do
  let w ← argSsizeObj width
  let f ← fillArg fill
  unicodeRjustImpl s w f

def unicodeZfill (s : Str) (width : Arg) : Py Str := do
  let w ← argSsizeObj width
  unicodeZfillImpl s w

end PyLean.UnicodeObj
