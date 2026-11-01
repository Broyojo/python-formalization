import PyLean.UnicodeObj.TextTable

/-!
Case mapping and the `is*` predicates: Objects/unicodeobject.c:10023-10252 and
:12055-12519, with `_Py_bytes_lower`/`_Py_bytes_upper` (Objects/bytes_methods.c) for
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

/-- `ascii_upper_or_lower`, unicodeobject.c:10023-10039. -/
def asciiUpperOrLower (lower : Bool) (s : Str) : Str :=
  if lower then s.map pyToLower else s.map pyToUpper

/-- First element that is not case-ignorable: the two `for` loops of
`handle_capital_sigma`. -/
def firstNotIgnorable : List Nat → Option Nat
  | [] => none
  | c :: cs => if !isCaseIgnorable c then some c else firstNotIgnorable cs

/-- `final_sigma`, unicodeobject.c:10053-10066. -/
def finalSigma (before after : List Nat) : Bool :=
  match firstNotIgnorable before with
  | none => false
  | some c =>
    isCased c &&
      match firstNotIgnorable after with
      | none => true
      | some c => !isCased c

/-- `handle_capital_sigma`, unicodeobject.c:10042-10068. `before` is the text
before the sigma, nearest character first, and `after` the text following it. -/
def handleCapitalSigma (before after : List Nat) : Nat :=
  if finalSigma before after then 0x3C2 else 0x3C3

/-- `lower_ucs4`, unicodeobject.c:10071-10080. -/
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

/-- `do_capitalize`, unicodeobject.c:10083-10104. `s` is not empty at every call. -/
def doCapitalize : Str → CaseOut
  | [] => startOut
  | c :: cs => mapLoop lowerUcs4 [c] cs (emit startOut (toTitleFull c))

/-- The loop body of `do_swapcase`, unicodeobject.c:10107-10129. -/
def swapcaseMap (before : List Nat) (c : Nat) (after : List Nat) : List Nat :=
  if isUppercase c then lowerUcs4 before c after
  else if isLowercase c then toUpperFull c
  else [c]

def doSwapcase (s : Str) : CaseOut := mapLoop swapcaseMap [] s startOut

/-- `do_upper_or_lower`, unicodeobject.c:10132-10150. -/
def doUpperOrLower (lower : Bool) (s : Str) : CaseOut :=
  mapLoop (fun b c a => if lower then lowerUcs4 b c a else toUpperFull c) [] s startOut

/-- `do_upper`, unicodeobject.c:10153-10156. -/
def doUpper : Str → CaseOut := doUpperOrLower false
/-- `do_lower`, unicodeobject.c:10159-10162. -/
def doLower : Str → CaseOut := doUpperOrLower true

/-- `do_casefold`, unicodeobject.c:10165-10179. -/
def doCasefold (s : Str) : CaseOut := mapLoop (fun _ c _ => toFoldedFull c) [] s startOut

/-- The loop of `do_title`, unicodeobject.c:10182-10206. -/
def titleLoop : Bool → List Nat → List Nat → CaseOut → CaseOut
  | _, _, [], o => o
  | previousIsCased, before, c :: cs, o =>
    let mapped := if previousIsCased then lowerUcs4 before c cs else toTitleFull c
    titleLoop (isCased c) (c :: before) cs (emit o mapped)

def doTitle (s : Str) : CaseOut := titleLoop false [] s startOut

/-- `(size_t) length > PY_SSIZE_T_MAX / (3 * sizeof(Py_UCS4))`. -/
def caseLengthLimit : Nat := (2 ^ 63 - 1) / 12

/-- `case_operation`, unicodeobject.c:10209-10252. The kind of the result is
`kindOfMax maxchar`, the `PyUnicode_New(newlength, maxchar)` call. -/
def caseOperation (perform : Str → CaseOut) (s : Str) : Py Str :=
  if s.length > caseLengthLimit then .error (.overflowError "string is too long")
  else .ok (perform s).res

/-- `unicode_title_impl`, unicodeobject.c:11101-11105. -/
def unicodeTitle (s : Str) : Py Str := caseOperation doTitle s
/-- `unicode_capitalize_impl`, unicodeobject.c:11117-11123. -/
def unicodeCapitalize (s : Str) : Py Str :=
  if s.length = 0 then .ok s else caseOperation doCapitalize s
/-- `unicode_casefold_impl`, unicodeobject.c:11132-11138. -/
def unicodeCasefold (s : Str) : Py Str :=
  if isAscii s then .ok (asciiUpperOrLower true s) else caseOperation doCasefold s
/-- `unicode_lower_impl`, unicodeobject.c:12578-12584. -/
def unicodeLower (s : Str) : Py Str :=
  if isAscii s then .ok (asciiUpperOrLower true s) else caseOperation doLower s
/-- `unicode_swapcase_impl`, unicodeobject.c:13377-13381. -/
def unicodeSwapcase (s : Str) : Py Str := caseOperation doSwapcase s
/-- `unicode_upper_impl`, unicodeobject.c:13558-13564. -/
def unicodeUpper (s : Str) : Py Str :=
  if isAscii s then .ok (asciiUpperOrLower false s) else caseOperation doUpper s

/-! ## The `is*` predicates, unicodeobject.c:12055-12519 -/

/-- `unicode_islower_impl`'s loop, :12092-12101. -/
def isLowerLoop : List Nat → Bool → Bool
  | [], cased => cased
  | ch :: cs, cased =>
    if isUppercase ch || isTitlecase ch then false
    else isLowerLoop cs (if !cased && isLowercase ch then true else cased)

/-- `unicode_islower_impl`, :12071-12102. -/
def unicodeIsLower : Str → Bool
  | [ch] => isLowercase ch
  | [] => false
  | s => isLowerLoop s false

/-- `unicode_isupper_impl`'s loop, :12135-12144. -/
def isUpperLoop : List Nat → Bool → Bool
  | [], cased => cased
  | ch :: cs, cased =>
    if isLowercase ch || isTitlecase ch then false
    else isUpperLoop cs (if !cased && isUppercase ch then true else cased)

/-- `unicode_isupper_impl`, :12114-12145. -/
def unicodeIsUpper : Str → Bool
  | [ch] => isUppercase ch
  | [] => false
  | s => isUpperLoop s false

/-- `unicode_istitle_impl`'s loop, :12180-12200. -/
def isTitleLoop : List Nat → Bool → Bool → Bool
  | [], cased, _ => cased
  | ch :: cs, cased, previousIsCased =>
    if isUppercase ch || isTitlecase ch then
      if previousIsCased then false else isTitleLoop cs true true
    else if isLowercase ch then
      if !previousIsCased then false else isTitleLoop cs true true
    else isTitleLoop cs cased false

/-- `unicode_istitle_impl`, :12157-12201. -/
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

/-- `unicode_isspace_impl`, :12213-12239. -/
def unicodeIsSpace := allShape isSpace
/-- `unicode_isalpha_impl`, :12251-12276. -/
def unicodeIsAlpha := allShape isAlpha
/-- `unicode_isalnum_impl`, :12288-12315. -/
def unicodeIsAlnum := allShape isAlnum
/-- `unicode_isdecimal_impl`, :12327-12352. -/
def unicodeIsDecimal := allShape isDecimalDigit
/-- `unicode_isdigit_impl`, :12364-12390. -/
def unicodeIsDigit := allShape isDigit
/-- `unicode_isnumeric_impl`, :12402-12427. -/
def unicodeIsNumeric := allShape isNumeric

/-- `unicode_isprintable_impl`, :12497-12519 (no empty case: `''.isprintable()`
is `True`). -/
def unicodeIsPrintable : Str → Bool
  | [ch] => isPrintable ch
  | s => s.all isPrintable

/-- The `for` loop of `_PyUnicode_ScanIdentifier`, :12454-12460. -/
def scanContinue : Nat → List Nat → Nat
  | i, [] => i
  | i, ch :: cs => if !isXidContinue ch then i else scanContinue (i + 1) cs

/-- `_PyUnicode_ScanIdentifier`, :12430-12461. -/
def scanIdentifier : Str → Nat
  | [] => 0
  | ch :: cs =>
    if !isXidStart ch && ch != 0x5F then 0 else scanContinue 1 cs

/-- `PyUnicode_IsIdentifier`, :12464-12470. -/
def pyUnicodeIsIdentifier (s : Str) : Bool :=
  s.length != 0 && scanIdentifier s == s.length

/-- `make_bloom_mask`, unicodeobject.c:1002-1037. `BLOOM_WIDTH` is 64 on this
platform. -/
def makeBloomMask (s : Str) : Nat := s.foldl (fun m ch => m ||| (1 <<< (ch &&& 63))) 0

/-- `BLOOM(mask, ch)`, unicodeobject.c. -/
def bloom (mask ch : Nat) : Bool := (mask &&& (1 <<< (ch &&& 63))) != 0

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`'s loop, :9635-9653. Writing
`?` and cutting the length ends the loop. -/
def transformLoop : List Nat → Str
  | [] => []
  | ch :: cs =>
    if ch < 127 then ch :: transformLoop cs
    else if isSpace ch then 32 :: transformLoop cs
    else
      let decimal := toDecimalDigit ch
      if decimal < 0 then [63] else (48 + decimal.toNat) :: transformLoop cs

/-- `_PyUnicode_TransformDecimalAndSpaceToASCII`, :9614-9657. -/
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
