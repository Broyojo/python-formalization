import PyLean.UnicodeObj.TextTable

/-!
Case mapping and the `is*` predicates: Objects/unicodeobject.c:9788-10017 and
:11784-12251, with `_Py_bytes_lower`/`_Py_bytes_upper` (Objects/bytes_methods.c) for
the ASCII fast paths.

A string is read through its index in C (`PyUnicode_READ(kind, data, i)`). The
models walk the list and keep the already-read prefix reversed in `before`, so
`handle_capital_sigma` can scan in both directions. `PyUnicode_IS_ASCII` is
`isAscii`, which is exact because kinds are canonical.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- `PyUnicode_IS_ASCII`. -/
def isAscii (s : Str) : Bool := s.all (· < 128)

/-- `Py_ISUPPER`/`Py_ISLOWER`/`Py_TOLOWER`/`Py_TOUPPER`, Python/pyctype.c. -/
def pyIsUpper (c : Nat) : Bool := decide (65 ≤ c) && decide (c ≤ 90)
def pyIsLower (c : Nat) : Bool := decide (97 ≤ c) && decide (c ≤ 122)
def pyToLower (c : Nat) : Nat := if pyIsUpper c then c + 32 else c
def pyToUpper (c : Nat) : Nat := if pyIsLower c then c - 32 else c

/-- `ascii_upper_or_lower`, unicodeobject.c:9788-9804. -/
def asciiUpperOrLower (lower : Bool) (s : Str) : Str :=
  if lower then s.map pyToLower else s.map pyToUpper

/-- First element that is not case-ignorable: the two `for` loops of
`handle_capital_sigma`. -/
def firstNotIgnorable : List Nat → Option Nat
  | [] => none
  | c :: cs => if !isCaseIgnorable c then some c else firstNotIgnorable cs

/-- `final_sigma`, unicodeobject.c:9818-9831. -/
def finalSigma (before after : List Nat) : Bool :=
  match firstNotIgnorable before with
  | none => false
  | some c =>
    isCased c &&
      match firstNotIgnorable after with
      | none => true
      | some c => !isCased c

/-- `handle_capital_sigma`, unicodeobject.c:9807-9833. `before` is the text
before the sigma, nearest character first, and `after` the text following it. -/
def handleCapitalSigma (before after : List Nat) : Nat :=
  if finalSigma before after then 0x3C2 else 0x3C3

/-- `lower_ucs4`, unicodeobject.c:9836-9845. -/
def lowerUcs4 (before : List Nat) (c : Nat) (after : List Nat) : List Nat :=
  if c = 0x3A3 then [handleCapitalSigma before after] else toLowerFull c

/-- The output of a `do_*` function: the buffer `res` and `*maxchar`. -/
structure CaseOut where
  res : Str
  maxchar : Nat
  deriving Repr, DecidableEq

/-- The inner `for (j = 0; j < n_res; j++)` loop of every `do_*` function. -/
def emit (o : CaseOut) (mapped : List Nat) : CaseOut :=
  { res := o.res ++ mapped, maxchar := mapped.foldl max o.maxchar }

/-- The outer loop shared by `do_swapcase`, `do_upper_or_lower` and
`do_casefold`, and the tail of `do_capitalize`. -/
def mapLoop (f : List Nat → Nat → List Nat → List Nat) :
    List Nat → List Nat → CaseOut → CaseOut
  | _, [], o => o
  | before, c :: cs, o => mapLoop f (c :: before) cs (emit o (f before c cs))

def startOut : CaseOut := { res := [], maxchar := 0 }

/-- `do_capitalize`, unicodeobject.c:9848-9869. `s` is not empty at every call. -/
def doCapitalize : Str → CaseOut
  | [] => startOut
  | c :: cs => mapLoop lowerUcs4 [c] cs (emit startOut (toTitleFull c))

/-- The loop body of `do_swapcase`, unicodeobject.c:9872-9894. -/
def swapcaseMap (before : List Nat) (c : Nat) (after : List Nat) : List Nat :=
  if isUppercase c then lowerUcs4 before c after
  else if isLowercase c then toUpperFull c
  else [c]

def doSwapcase (s : Str) : CaseOut := mapLoop swapcaseMap [] s startOut

/-- `do_upper_or_lower`, unicodeobject.c:9897-9915. -/
def doUpperOrLower (lower : Bool) (s : Str) : CaseOut :=
  mapLoop (fun b c a => if lower then lowerUcs4 b c a else toUpperFull c) [] s startOut

/-- `do_upper`, unicodeobject.c:9918-9921. -/
def doUpper : Str → CaseOut := doUpperOrLower false
/-- `do_lower`, unicodeobject.c:9924-9927. -/
def doLower : Str → CaseOut := doUpperOrLower true

/-- `do_casefold`, unicodeobject.c:9930-9944. -/
def doCasefold (s : Str) : CaseOut := mapLoop (fun _ c _ => toFoldedFull c) [] s startOut

/-- The loop of `do_title`, unicodeobject.c:9947-9971. -/
def titleLoop : Bool → List Nat → List Nat → CaseOut → CaseOut
  | _, _, [], o => o
  | previousIsCased, before, c :: cs, o =>
    let mapped := if previousIsCased then lowerUcs4 before c cs else toTitleFull c
    titleLoop (isCased c) (c :: before) cs (emit o mapped)

def doTitle (s : Str) : CaseOut := titleLoop false [] s startOut

/-- `(size_t) length > PY_SSIZE_T_MAX / (3 * sizeof(Py_UCS4))`. -/
def caseLengthLimit : Nat := (2 ^ 63 - 1) / 12

/-- A `Py_UCS4` stored in a unit of kind `k`: `_PyUnicode_CONVERT_BYTES(Py_UCS4, Py_UCS1, ...)`
and `(Py_UCS4, Py_UCS2, ...)` keep the low 8 or 16 bits, the `memcpy` of the 4-byte kind keeps
all 32. -/
def storeAs (k : Kind) (c : Nat) : Nat := c % 2 ^ (8 * k.width)

/-- `case_operation`, unicodeobject.c:9974-10017: the length check (:9987-9990), `perform`
(:9994), `PyUnicode_New(newlength, maxchar)` choosing the kind `kindOfMax maxchar` (:9995),
and the copy of `tmp` into a buffer of that kind (:10001-10013). The `PyMem_Malloc` and
`PyUnicode_New` allocation failures (`MemoryError`) are not modelled. -/
def caseOperation (perform : Str → CaseOut) (s : Str) : Py Str :=
  if s.length > caseLengthLimit then .error (.overflowError "string is too long")
  else
    let o := perform s
    .ok (o.res.map (storeAs (kindOfMax o.maxchar)))

/-- `unicode_title_impl`, unicodeobject.c:10867-10871. -/
def unicodeTitle (s : Str) : Py Str := caseOperation doTitle s
/-- `unicode_capitalize_impl`, unicodeobject.c:10883-10889. -/
def unicodeCapitalize (s : Str) : Py Str :=
  if s.length = 0 then .ok s else caseOperation doCapitalize s
/-- `unicode_casefold_impl`, unicodeobject.c:10898-10904. -/
def unicodeCasefold (s : Str) : Py Str :=
  if isAscii s then .ok (asciiUpperOrLower true s) else caseOperation doCasefold s
/-- `unicode_lower_impl`, unicodeobject.c:12310-12316. -/
def unicodeLower (s : Str) : Py Str :=
  if isAscii s then .ok (asciiUpperOrLower true s) else caseOperation doLower s
/-- `unicode_swapcase_impl`, unicodeobject.c:13128-13132. -/
def unicodeSwapcase (s : Str) : Py Str := caseOperation doSwapcase s
/-- `unicode_upper_impl`, unicodeobject.c:13310-13316. -/
def unicodeUpper (s : Str) : Py Str :=
  if isAscii s then .ok (asciiUpperOrLower false s) else caseOperation doUpper s

/-! ## The `is*` predicates, unicodeobject.c:11784-12251 -/

/-- `unicode_islower_impl`'s loop, :11821-11830. -/
def isLowerLoop : List Nat → Bool → Bool
  | [], cased => cased
  | ch :: cs, cased =>
    if isUppercase ch || isTitlecase ch then false
    else isLowerLoop cs (if !cased && isLowercase ch then true else cased)

/-- `unicode_islower_impl`, :11800-11831. -/
def unicodeIsLower : Str → Bool
  | [ch] => isLowercase ch
  | [] => false
  | s => isLowerLoop s false

/-- `unicode_isupper_impl`'s loop, :11864-11873. -/
def isUpperLoop : List Nat → Bool → Bool
  | [], cased => cased
  | ch :: cs, cased =>
    if isLowercase ch || isTitlecase ch then false
    else isUpperLoop cs (if !cased && isUppercase ch then true else cased)

/-- `unicode_isupper_impl`, :11843-11874. -/
def unicodeIsUpper : Str → Bool
  | [ch] => isUppercase ch
  | [] => false
  | s => isUpperLoop s false

/-- `unicode_istitle_impl`'s loop, :11909-11929. -/
def isTitleLoop : List Nat → Bool → Bool → Bool
  | [], cased, _ => cased
  | ch :: cs, cased, previousIsCased =>
    if isUppercase ch || isTitlecase ch then
      if previousIsCased then false else isTitleLoop cs true true
    else if isLowercase ch then
      if !previousIsCased then false else isTitleLoop cs true true
    else isTitleLoop cs cased false

/-- `unicode_istitle_impl`, :11886-11930. -/
def unicodeIsTitle : Str → Bool
  | [ch] => isTitlecase ch || isUppercase ch
  | [] => false
  | s => isTitleLoop s false false

/-- The shape of `isspace`, `isalpha`, `isalnum`, `isdecimal`, `isdigit` and
`isnumeric`: the one-character shortcut, the empty case, the loop. -/
def allShape (p : Nat → Bool) : Str → Bool
  | [ch] => p ch
  | [] => false
  | s => s.all p

/-- `unicode_isspace_impl`, :11942-11968. -/
def unicodeIsSpace := allShape isSpace
/-- `unicode_isalpha_impl`, :11980-12005. -/
def unicodeIsAlpha := allShape isAlpha
/-- `unicode_isalnum_impl`, :12018-12045. -/
def unicodeIsAlnum := allShape isAlnum
/-- `unicode_isdecimal_impl`, :12057-12082. -/
def unicodeIsDecimal := allShape isDecimalDigit
/-- `unicode_isdigit_impl`, :12094-12120. -/
def unicodeIsDigit := allShape isDigit
/-- `unicode_isnumeric_impl`, :12132-12157. -/
def unicodeIsNumeric := allShape isNumeric

/-- `unicode_isprintable_impl`, :12229-12251 (no empty case: `''.isprintable()`
is `True`). -/
def unicodeIsPrintable : Str → Bool
  | [ch] => isPrintable ch
  | s => s.all isPrintable

/-- The `for` loop of `_PyUnicode_ScanIdentifier`, :12184-12190. -/
def scanContinue : Nat → List Nat → Nat
  | i, [] => i
  | i, ch :: cs => if !isXidContinue ch then i else scanContinue (i + 1) cs

/-- `_PyUnicode_ScanIdentifier`, :12160-12191. -/
def scanIdentifier : Str → Nat
  | [] => 0
  | ch :: cs =>
    if !isXidStart ch && ch != 0x5F then 0 else scanContinue 1 cs

/-- `PyUnicode_IsIdentifier`, :12194-12200. -/
def pyUnicodeIsIdentifier (s : Str) : Bool :=
  s.length != 0 && scanIdentifier s == s.length

/-- `make_bloom_mask`, unicodeobject.c:922-957. `BLOOM_WIDTH` is 64 on this
platform. -/
def makeBloomMask (s : Str) : Nat := s.foldl (fun m ch => m ||| (1 <<< (ch &&& 63))) 0

/-- `BLOOM(mask, ch)`, unicodeobject.c. -/
def bloom (mask ch : Nat) : Bool := (mask &&& (1 <<< (ch &&& 63))) != 0

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`'s loop, :9536-9554. Writing
`?` and cutting the length ends the loop. -/
def transformLoop : List Nat → Str
  | [] => []
  | ch :: cs =>
    if ch < 127 then ch :: transformLoop cs
    else if isSpace ch then 32 :: transformLoop cs
    else
      let decimal := toDecimalDigit ch
      if decimal < 0 then [63] else (48 + decimal.toNat) :: transformLoop cs

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`, :9515-9558. -/
def transformDecimalAndSpace (s : Str) : Str :=
  if isAscii s then s else transformLoop s

/-! ## `bytes` twins, Objects/stringlib/ctype.h over Objects/bytes_methods.c -/

/-- `Py_ISSPACE`, `Py_ISALPHA`, `Py_ISDIGIT`, `Py_ISALNUM`, Python/pyctype.c. -/
def pyIsSpace (c : Nat) : Bool := c == 32 || (9 ≤ c && c ≤ 13)
def pyIsAlpha (c : Nat) : Bool := pyIsLower c || pyIsUpper c
def pyIsDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57
def pyIsAlnum (c : Nat) : Bool := pyIsAlpha c || pyIsDigit c

/-- The shape of `_Py_bytes_isspace`/`isalpha`/`isalnum`/`isdigit`,
bytes_methods.c:12-130: one-byte shortcut, empty case, loop. -/
def bytesAllShape := allShape

/-- `_Py_bytes_islower`'s loop, bytes_methods.c:132-164. -/
def bytesIsLowerLoop : List Nat → Bool → Bool
  | [], cased => cased
  | c :: cs, cased =>
    if pyIsUpper c then false else bytesIsLowerLoop cs (if !cased && pyIsLower c then true else cased)

def bytesIsLower : Bytes → Bool
  | [c] => pyIsLower c
  | [] => false
  | s => bytesIsLowerLoop s false

/-- `_Py_bytes_isupper`'s loop, bytes_methods.c:166-198. -/
def bytesIsUpperLoop : List Nat → Bool → Bool
  | [], cased => cased
  | c :: cs, cased =>
    if pyIsLower c then false else bytesIsUpperLoop cs (if !cased && pyIsUpper c then true else cased)

def bytesIsUpper : Bytes → Bool
  | [c] => pyIsUpper c
  | [] => false
  | s => bytesIsUpperLoop s false

/-- `_Py_bytes_istitle`'s loop, bytes_methods.c:202-248. -/
def bytesIsTitleLoop : List Nat → Bool → Bool → Bool
  | [], cased, _ => cased
  | c :: cs, cased, previousIsCased =>
    if pyIsUpper c then
      if previousIsCased then false else bytesIsTitleLoop cs true true
    else if pyIsLower c then
      if !previousIsCased then false else bytesIsTitleLoop cs true true
    else bytesIsTitleLoop cs cased false

def bytesIsTitle : Bytes → Bool
  | [c] => pyIsUpper c
  | [] => false
  | s => bytesIsTitleLoop s false false

/-- `_Py_bytes_lower`, bytes_methods.c:251-258. -/
def bytesLower (b : Bytes) : Bytes := b.map pyToLower
/-- `_Py_bytes_upper`, bytes_methods.c:267-274. -/
def bytesUpper (b : Bytes) : Bytes := b.map pyToUpper

/-- `_Py_bytes_title`'s loop, bytes_methods.c:284-303. -/
def bytesTitleLoop : Bool → List Nat → List Nat
  | _, [] => []
  | previousIsCased, c :: cs =>
    if pyIsLower c then
      (if !previousIsCased then pyToUpper c else c) :: bytesTitleLoop true cs
    else if pyIsUpper c then
      (if previousIsCased then pyToLower c else c) :: bytesTitleLoop true cs
    else c :: bytesTitleLoop false cs

def bytesTitle (b : Bytes) : Bytes := bytesTitleLoop false b

/-- `_Py_bytes_capitalize`, bytes_methods.c:313-319. -/
def bytesCapitalize : Bytes → Bytes
  | [] => []
  | c :: cs => pyToUpper c :: bytesLower cs

/-- `_Py_bytes_swapcase`, bytes_methods.c:329-345. -/
def bytesSwapcase (b : Bytes) : Bytes :=
  b.map fun c => if pyIsLower c then pyToUpper c else if pyIsUpper c then pyToLower c else c

end PyLean.UnicodeObj
