import PyLean.DiffCore
import PyLean.StrSearch.Diff
import PyLean.UnicodeObj.Repr
import PyLean.UnicodeObj.TextTranslate
import PyLean.UnicodeObj.TextDedent

/-! Difftest handler for the text slice (`fn` names start with `text_`). -/

namespace PyLean.UnicodeObj.TextDiff

open Lean PyLean PyLean.Diff PyLean.StrSearch

def encStr (s : Str) : Json := toJson s

def getItem (j : Json) : Except String MapItem := do
  match ← getStr j "t" with
  | "none" => return .pyNone
  | "int" => return .int (← getInt j "v")
  | "str" => return .str (← getSeq j "s")
  | "wrong" => return .wrong
  | "raise" => return .raises (.valueError "boom")
  | t => throw s!"bad item {t}"

def encItem : MapItem → Json
  | .pyNone => Json.arr #["none"]
  | .int v => Json.arr #["int", toJson v]
  | .str s => Json.arr #["str", toJson s]
  | .wrong => Json.arr #["wrong"]
  | .missing => Json.arr #["missing"]
  | .raises _ => Json.arr #["raise"]

def getTable (j : Json) : Except String TransDict := do
  let arr ← (← field j "table").getArr?
  arr.toList.mapM fun e => do
    let pair ← e.getArr?
    let k ← (pair[0]!).getInt?
    return (k, ← getItem pair[1]!)

def caseOp : String → Option (Str → Py Str)
  | "upper" => some unicodeUpper
  | "lower" => some unicodeLower
  | "title" => some unicodeTitle
  | "capitalize" => some unicodeCapitalize
  | "casefold" => some unicodeCasefold
  | "swapcase" => some unicodeSwapcase
  | _ => none

def isOp : String → Option (Str → Bool)
  | "isascii" => some isAscii
  | "islower" => some unicodeIsLower
  | "isupper" => some unicodeIsUpper
  | "istitle" => some unicodeIsTitle
  | "isspace" => some unicodeIsSpace
  | "isalpha" => some unicodeIsAlpha
  | "isalnum" => some unicodeIsAlnum
  | "isdecimal" => some unicodeIsDecimal
  | "isdigit" => some unicodeIsDigit
  | "isnumeric" => some unicodeIsNumeric
  | "isprintable" => some unicodeIsPrintable
  | "isidentifier" => some pyUnicodeIsIdentifier
  | _ => none

def bytesOp : String → Option (Bytes → Json)
  | "isspace" => some fun b => toJson (allShape pyIsSpace b)
  | "isalpha" => some fun b => toJson (allShape pyIsAlpha b)
  | "isalnum" => some fun b => toJson (allShape pyIsAlnum b)
  | "isdigit" => some fun b => toJson (allShape pyIsDigit b)
  | "isascii" => some fun b => toJson (b.all (· < 128))
  | "islower" => some fun b => toJson (bytesIsLower b)
  | "isupper" => some fun b => toJson (bytesIsUpper b)
  | "istitle" => some fun b => toJson (bytesIsTitle b)
  | "lower" => some fun b => toJson (bytesLower b)
  | "upper" => some fun b => toJson (bytesUpper b)
  | "title" => some fun b => toJson (bytesTitle b)
  | "capitalize" => some fun b => toJson (bytesCapitalize b)
  | "swapcase" => some fun b => toJson (bytesSwapcase b)
  | _ => none

def getOkOr (r : Py Str) : Str := match r with | .ok s => s | .error _ => []

/-- Everything the sweep compares for one code point. -/
def sweepValues (c : Nat) : List Nat :=
  let b (x : Bool) : Nat := if x then 1 else 0
  let upper := getOkOr (unicodeUpper [c])
  let lower := getOkOr (unicodeLower [c])
  let title := getOkOr (unicodeTitle [c])
  let fold := getOkOr (unicodeCasefold [c])
  [b (unicodeIsAlpha [c]), b (unicodeIsDecimal [c]), b (unicodeIsDigit [c]),
   b (unicodeIsNumeric [c]), b (unicodeIsPrintable [c]), b (unicodeIsLower [c]),
   b (unicodeIsUpper [c]), b (unicodeIsTitle [c]), b (unicodeIsSpace [c]),
   b (pyUnicodeIsIdentifier [c]), b (pyUnicodeIsIdentifier [97, c]),
   b (isLinebreak c), b (isCased c), b (isCaseIgnorable c),
   (toDecimalDigit c + 1).toNat, (toDigit c + 1).toNat,
   toUppercase c, toLowercase c, toTitlecase c,
   upper.length] ++ upper ++ [lower.length] ++ lower ++ [title.length] ++ title ++
  [fold.length] ++ fold

def sweepPrime : Nat := 2 ^ 61 - 1

def sweepHash (lo hi : Nat) : Nat :=
  (List.range (hi - lo)).foldl (fun h i =>
    (sweepValues (lo + i)).foldl (fun h v => (h * 1000003 + v + 1) % sweepPrime) h) 0

/-- The text between the first and the last `"""` of a line list, for the
`python -c` probe. -/
def stripQuotes (s : Str) : Str :=
  let rec dropTo : Nat → Str → Str
    | 0, r => r
    | n + 1, r =>
      match r with
      | [] => []
      | 34 :: 34 :: 34 :: t => t
      | _ :: t => dropTo n t
  let a := dropTo s.length s
  (dropTo a.length a.reverse).reverse

def run (fn : String) (j : Json) : Except String Json := do
  match fn with
  | "text_case" =>
    let some f := caseOp (← getStr j "op") | throw "bad op"
    return encPy encStr (f (← getSeq j "s"))
  | "text_is" =>
    let some f := isOp (← getStr j "op") | throw "bad op"
    return encPy toJson (.ok (f (← getSeq j "s")) : Py Bool)
  | "text_bytes" =>
    let some f := bytesOp (← getStr j "op") | throw "bad op"
    return encPy id (.ok (f (← getSeq j "s")) : Py Json)
  | "text_repr" => return encPy encStr (.ok (unicodeRepr (← getSeq j "s")) : Py Str)
  | "text_translate" =>
    let d ← getTable j
    return encPy encStr (unicodeTranslate (← getSeq j "s") (dictMapping d))
  | "text_translate_strict" =>
    let d ← getTable j
    return encPy encStr (pyUnicodeTranslateStrict (← getSeq j "s") (dictMapping d))
  | "text_maketrans_str" =>
    let z ← getOptSeq j "z"
    let y ← getOptSeq j "y"
    return encPy (fun d => Json.arr (d.map fun e => Json.arr #[toJson e.1, encItem e.2]).toArray)
      (unicodeMaketrans (.str (← getSeq j "x")) y z)
  | "text_maketrans_dict" =>
    let arr ← (← field j "x").getArr?
    let items ← arr.toList.mapM fun e => do
      let pair ← e.getArr?
      let kj := pair[0]!
      let k : MkKey ← match ← getStr kj "t" with
        | "str" => pure (.str (← getSeq kj "s"))
        | "int" => pure (.int (← getInt kj "v"))
        | _ => pure .other
      return (k, ← getItem pair[1]!)
    return encPy (fun d => Json.arr (d.map fun e => Json.arr #[toJson e.1, encItem e.2]).toArray)
      (unicodeMaketrans (.dict items) none none)
  | "text_maketrans_other" =>
    return encPy (fun _ => Json.null) (unicodeMaketrans .other (← getOptSeq j "y") none)
  | "text_dedent" => return encPy encStr (.ok (textwrapDedent (← getSeq j "s")) : Py Str)
  | "text_dedent_c" =>
    -- `python -c` appends '\n' (Python/initconfig.c), so the buffer always ends with one.
    match pyUnicodeDedent ((← getSeq j "s") ++ [10]) with
    | none => throw "dedent undefined"
    | some r =>
      let c := r.headD 0
      let v : Json := if c == 32 || c == 9 then toJson (-1 : Int) else toJson (stripQuotes r)
      return Json.mkObj [("ok", v)]
  | "text_transform" => return encPy encStr (.ok (transformDecimalAndSpace (← getSeq j "s")) : Py Str)
  | "text_sweep" => return encPy toJson (.ok (sweepHash (← getNat j "lo") (← getNat j "hi")) : Py Nat)
  | _ => throw s!"unknown fn {fn}"

def handler : Handler := fun fn j =>
  if fn.startsWith "text_" then some (run fn j) else none

end PyLean.UnicodeObj.TextDiff
