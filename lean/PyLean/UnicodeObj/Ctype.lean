import PyLean.UnicodeObj.Basic
import PyLean.UnicodeObj.Tables

/-!
`Objects/unicodectype.c`: the character database, reading the generated tables
of `Objects/unicodetype_db.h` (`Tables.lean`) exactly as the C code does.
-/

namespace PyLean.UnicodeObj

open Tables

/-- Element `i` of a packed literal with `w`-bit elements. -/
def pick (table w i : Nat) : Nat := (table >>> (w * i)) &&& (2 ^ w - 1)

/-- Element `i` of a chunked table: `bits` is the log2 of the chunk size. -/
def pickChunked (chunk : Nat → Nat) (bits w i : Nat) : Nat :=
  pick (chunk (i >>> bits)) w (i &&& (2 ^ bits - 1))

/-- Sign extension of a 32-bit field (`const int`). -/
def int32 (v : Nat) : Int := if v < 2 ^ 31 then v else (v : Int) - 2 ^ 32

/-- `_PyUnicode_TypeRecord`, unicodectype.c:28-39. -/
structure TypeRecord where
  upper : Int
  lower : Int
  title : Int
  decimal : Nat
  digit : Nat
  flags : Nat
  deriving Repr, DecidableEq

def recordAt (i : Nat) : TypeRecord :=
  let r := pickChunked typeRecordsChunk 4 128 i
  { upper := int32 (r &&& 0xFFFFFFFF)
    lower := int32 ((r >>> 32) &&& 0xFFFFFFFF)
    title := int32 ((r >>> 64) &&& 0xFFFFFFFF)
    decimal := (r >>> 96) &&& 0xFF
    digit := (r >>> 104) &&& 0xFF
    flags := (r >>> 112) &&& 0xFFFF }

/-- `gettyperecord`, unicodectype.c:44-58. -/
def gettyperecord (code : Nat) : TypeRecord :=
  let index :=
    if code ≥ 0x110000 then 0
    else
      let index := pickChunked index1Chunk 6 16 (code >>> shift)
      pickChunked index2Chunk 6 16 ((index <<< shift) + (code &&& ((1 <<< shift) - 1)))
  recordAt index

/-! Masks, unicodectype.c:14-26. -/
def ALPHA_MASK : Nat := 0x01
def DECIMAL_MASK : Nat := 0x02
def DIGIT_MASK : Nat := 0x04
def LOWER_MASK : Nat := 0x08
def TITLE_MASK : Nat := 0x40
def UPPER_MASK : Nat := 0x80
def XID_START_MASK : Nat := 0x100
def XID_CONTINUE_MASK : Nat := 0x200
def PRINTABLE_MASK : Nat := 0x400
def NUMERIC_MASK : Nat := 0x800
def CASE_IGNORABLE_MASK : Nat := 0x1000
def CASED_MASK : Nat := 0x2000
def EXTENDED_CASE_MASK : Nat := 0x4000

def hasFlag (ctype : TypeRecord) (mask : Nat) : Bool := (ctype.flags &&& mask) != 0

/-- `ch + delta` in `Py_UCS4` (unsigned 32-bit wraparound). -/
def addUCS4 (ch : Nat) (delta : Int) : Nat := (((ch : Int) + delta) % (2 ^ 32)).toNat

def extendedCaseAt (i : Nat) : Nat := pickChunked extendedCaseChunk 5 32 i

/-- `_PyUnicode_ToTitlecase`, unicodectype.c:63-70. -/
def toTitlecase (ch : Nat) : Nat :=
  let ctype := gettyperecord ch
  if hasFlag ctype EXTENDED_CASE_MASK then extendedCaseAt (ctype.title.toNat &&& 0xFFFF)
  else addUCS4 ch ctype.title

/-- `_PyUnicode_IsTitlecase`, unicodectype.c:75-80. -/
def isTitlecase (ch : Nat) : Bool := hasFlag (gettyperecord ch) TITLE_MASK
/-- `_PyUnicode_IsXidStart`, unicodectype.c:85-90. -/
def isXidStart (ch : Nat) : Bool := hasFlag (gettyperecord ch) XID_START_MASK
/-- `_PyUnicode_IsXidContinue`, unicodectype.c:95-100. -/
def isXidContinue (ch : Nat) : Bool := hasFlag (gettyperecord ch) XID_CONTINUE_MASK

/-- `_PyUnicode_ToDecimalDigit`, unicodectype.c:105-110. -/
def toDecimalDigit (ch : Nat) : Int :=
  let ctype := gettyperecord ch
  if hasFlag ctype DECIMAL_MASK then ctype.decimal else -1
/-- `_PyUnicode_IsDecimalDigit`, unicodectype.c:112-117. -/
def isDecimalDigit (ch : Nat) : Bool := !decide (toDecimalDigit ch < 0)
/-- `_PyUnicode_ToDigit`, unicodectype.c:122-127. -/
def toDigit (ch : Nat) : Int :=
  let ctype := gettyperecord ch
  if hasFlag ctype DIGIT_MASK then ctype.digit else -1
/-- `_PyUnicode_IsDigit`, unicodectype.c:129-134. -/
def isDigit (ch : Nat) : Bool := !decide (toDigit ch < 0)
/-- `_PyUnicode_IsNumeric`, unicodectype.c:139-144. -/
def isNumeric (ch : Nat) : Bool := hasFlag (gettyperecord ch) NUMERIC_MASK
/-- `_PyUnicode_IsPrintable`, unicodectype.c:151-156. -/
def isPrintable (ch : Nat) : Bool := hasFlag (gettyperecord ch) PRINTABLE_MASK
/-- `_PyUnicode_IsLowercase`, unicodectype.c:161-166. -/
def isLowercase (ch : Nat) : Bool := hasFlag (gettyperecord ch) LOWER_MASK
/-- `_PyUnicode_IsUppercase`, unicodectype.c:171-176. -/
def isUppercase (ch : Nat) : Bool := hasFlag (gettyperecord ch) UPPER_MASK

/-- `_PyUnicode_ToUppercase`, unicodectype.c:181-188. -/
def toUppercase (ch : Nat) : Nat :=
  let ctype := gettyperecord ch
  if hasFlag ctype EXTENDED_CASE_MASK then extendedCaseAt (ctype.upper.toNat &&& 0xFFFF)
  else addUCS4 ch ctype.upper
/-- `_PyUnicode_ToLowercase`, unicodectype.c:193-200. -/
def toLowercase (ch : Nat) : Nat :=
  let ctype := gettyperecord ch
  if hasFlag ctype EXTENDED_CASE_MASK then extendedCaseAt (ctype.lower.toNat &&& 0xFFFF)
  else addUCS4 ch ctype.lower

/-- The `for` loop shared by the `_Full` functions. -/
def extendedRun (index n : Nat) : List Nat :=
  (List.range n).map fun i => extendedCaseAt (index + i)

/-- One `_PyUnicode_To*Full` body, with `field` the record's case field. -/
def toFull (field : TypeRecord → Int) (ch : Nat) : List Nat :=
  let ctype := gettyperecord ch
  if hasFlag ctype EXTENDED_CASE_MASK then
    let v := (field ctype).toNat
    extendedRun (v &&& 0xFFFF) (v >>> 24)
  else [addUCS4 ch (field ctype)]

/-- `_PyUnicode_ToLowerFull`, unicodectype.c:202-216. -/
def toLowerFull : Nat → List Nat := toFull TypeRecord.lower
/-- `_PyUnicode_ToTitleFull`, unicodectype.c:218-232. -/
def toTitleFull : Nat → List Nat := toFull TypeRecord.title
/-- `_PyUnicode_ToUpperFull`, unicodectype.c:234-248. -/
def toUpperFull : Nat → List Nat := toFull TypeRecord.upper

/-- `_PyUnicode_ToFoldedFull`, unicodectype.c:250-263. -/
def toFoldedFull (ch : Nat) : List Nat :=
  let ctype := gettyperecord ch
  let lower := ctype.lower.toNat
  if hasFlag ctype EXTENDED_CASE_MASK && ((lower >>> 20) &&& 7) != 0 then
    extendedRun ((lower &&& 0xFFFF) + (lower >>> 24)) ((lower >>> 20) &&& 7)
  else toLowerFull ch

/-- `_PyUnicode_IsCased`, unicodectype.c:265-270. -/
def isCased (ch : Nat) : Bool := hasFlag (gettyperecord ch) CASED_MASK
/-- `_PyUnicode_IsCaseIgnorable`, unicodectype.c:272-277. -/
def isCaseIgnorable (ch : Nat) : Bool := hasFlag (gettyperecord ch) CASE_IGNORABLE_MASK
/-- `_PyUnicode_IsAlpha`, unicodectype.c:282-287. -/
def isAlpha (ch : Nat) : Bool := hasFlag (gettyperecord ch) ALPHA_MASK

/-- `_PyUnicode_IsWhitespace`, unicodetype_db.h:6546. -/
def isWhitespaceDb (ch : Nat) : Bool := Tables.whitespace.contains ch
/-- `_PyUnicode_IsLinebreak`, unicodetype_db.h:6587. -/
def isLinebreak (ch : Nat) : Bool := Tables.linebreak.contains ch

/-- `_Py_ascii_whitespace`, the table behind `Py_UNICODE_ISSPACE`. -/
def asciiWhitespace : List Nat := [9, 10, 11, 12, 13, 0x1C, 0x1D, 0x1E, 0x1F, 0x20]

/-- `Py_UNICODE_ISSPACE`, Include/cpython/unicodeobject.h:742-747. -/
def isSpace (ch : Nat) : Bool :=
  if ch < 128 then asciiWhitespace.contains ch else isWhitespaceDb ch

/-- `Py_UNICODE_ISALNUM`, Include/cpython/unicodeobject.h. -/
def isAlnum (ch : Nat) : Bool :=
  isAlpha ch || isDecimalDigit ch || isDigit ch || isNumeric ch

example : isAlpha 0x41 = true := by decide
example : toUpperFull 0xDF = [83, 83] := by decide
example : toFoldedFull 0xDF = [115, 115] := by decide
example : isPrintable 0x7F = false := by decide
example : toLowercase 0x10FFFF = 0x10FFFF := by decide

end PyLean.UnicodeObj
