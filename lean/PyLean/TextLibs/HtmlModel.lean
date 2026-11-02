import PyLean.Core
import PyLean.TextLibs.Html5Table

/-!
`Lib/html/__init__.py`, CPython 3.15.2. Strings are lists of code points. Arguments are `str`, and
`quote` is a flag, as a stated scope limit: the functions use nothing but `str` methods on them, so
they accept any object that has those methods.

`re.sub` with `_charref` is written out: `matchRef` is the pattern, and `subLoop` the scan.
-/

namespace PyLean.TextLibs.Html

open PyLean

/-- `s.replace(c, r)`, for a one-character needle. -/
def replaceCh (s : List Nat) (c : Nat) (r : List Nat) : List Nat :=
  s.flatMap fun x => if x == c then r else [x]

def eAmp : List Nat := [38, 97, 109, 112, 59]
def eLt : List Nat := [38, 108, 116, 59]
def eGt : List Nat := [38, 103, 116, 59]
def eQuot : List Nat := [38, 113, 117, 111, 116, 59]
def eApos : List Nat := [38, 35, 120, 50, 55, 59]

/-- `escape`, `Lib/html/__init__.py:12-25`. -/
def escape (s : List Nat) (quote : Bool) : List Nat :=
  let s := replaceCh s 38 eAmp
  let s := replaceCh s 60 eLt
  let s := replaceCh s 62 eGt
  if quote then replaceCh (replaceCh s 34 eQuot) 39 eApos else s

/-- `_invalid_charrefs`, `Lib/html/__init__.py:30-65`. -/
def invalidCharrefs : List (Nat × Nat) :=
  [(0x00, 0xfffd), (0x0d, 0x0d), (0x80, 0x20ac), (0x81, 0x81), (0x82, 0x201a), (0x83, 0x0192),
   (0x84, 0x201e), (0x85, 0x2026), (0x86, 0x2020), (0x87, 0x2021), (0x88, 0x02c6), (0x89, 0x2030),
   (0x8a, 0x0160), (0x8b, 0x2039), (0x8c, 0x0152), (0x8d, 0x8d), (0x8e, 0x017d), (0x8f, 0x8f),
   (0x90, 0x90), (0x91, 0x2018), (0x92, 0x2019), (0x93, 0x201c), (0x94, 0x201d), (0x95, 0x2022),
   (0x96, 0x2013), (0x97, 0x2014), (0x98, 0x02dc), (0x99, 0x2122), (0x9a, 0x0161), (0x9b, 0x203a),
   (0x9c, 0x0153), (0x9d, 0x9d), (0x9e, 0x017e), (0x9f, 0x0178)]

/-- The last group of `_invalid_codepoints`, `Lib/html/__init__.py:82-88`. -/
def otherInvalid : List Nat :=
  [0xb, 0xfffe, 0xffff, 0x1fffe, 0x1ffff, 0x2fffe, 0x2ffff, 0x3fffe, 0x3ffff, 0x4fffe, 0x4ffff,
   0x5fffe, 0x5ffff, 0x6fffe, 0x6ffff, 0x7fffe, 0x7ffff, 0x8fffe, 0x8ffff, 0x9fffe, 0x9ffff,
   0xafffe, 0xaffff, 0xbfffe, 0xbffff, 0xcfffe, 0xcffff, 0xdfffe, 0xdffff, 0xefffe, 0xeffff,
   0xffffe, 0xfffff, 0x10fffe, 0x10ffff]

/-- `num in _invalid_codepoints`, `Lib/html/__init__.py:67-88`. -/
def invalidCodepoint (n : Nat) : Bool :=
  (1 ≤ n && n ≤ 8) || (0xe ≤ n && n ≤ 0x1f) || (0x7f ≤ n && n ≤ 0x9f) || (0xfdd0 ≤ n && n ≤ 0xfdef) ||
    otherInvalid.contains n

/-- `Lib/html/__init__.py:99-105`. -/
def numRef (num : Nat) : List Nat :=
  match invalidCharrefs.lookup num with
  | some c => [c]
  | none =>
    if (0xD800 ≤ num && num ≤ 0xDFFF) || num > 0x10FFFF then [0xFFFD]
    else if invalidCodepoint num then []
    else [num]

def isDigit (c : Nat) : Bool := 48 ≤ c && c ≤ 57

def isHex (c : Nat) : Bool := isDigit c || (97 ≤ c && c ≤ 102) || (65 ≤ c && c ≤ 70)

def hexDigit (c : Nat) : Nat :=
  if isDigit c then c - 48 else if 97 ≤ c then c - 87 else c - 55

/-- `int(s)`, for ASCII digits, and its limit, `sys.get_int_max_str_digits()`. It counts all the digits,
leading zeros too. -/
def intDec (ds : List Nat) : Py Nat :=
  if ds.length > 4300 then
    .error (.valueError s!"Exceeds the limit (4300 digits) for integer string conversion: value has {ds.length} digits; use sys.set_int_max_str_digits() to increase the limit")
  else .ok (ds.foldl (fun v c => v * 10 + (c - 48)) 0)

/-- `int(s, 16)`: a power of two, so the limit does not apply. -/
def intHex (ds : List Nat) : Nat := ds.foldl (fun v c => v * 16 + hexDigit c) 0

/-- `s.rstrip(';')`. -/
def rstripSemi (s : List Nat) : List Nat := (s.reverse.dropWhile (· == 59)).reverse

/-- `s in _html5`, and `_html5[s]`. -/
def look (s : List Nat) : Option (List Nat) := html5.lookup s

/-- The `for` of `Lib/html/__init__.py:111-113`: `x` runs down to 2. -/
def prefixLoop (s : List Nat) : Nat → Option (List Nat)
  | 0 => none
  | 1 => none
  | x + 2 =>
    match look (s.take (x + 2)) with
    | some v => some (v ++ s.drop (x + 2))
    | none => prefixLoop s (x + 1)

/-- The named branch, `Lib/html/__init__.py:106-115`. -/
def namedRef (s : List Nat) : List Nat :=
  match look s with
  | some v => v
  | none =>
    match prefixLoop s (s.length - 1) with
    | some r => r
    | none => 38 :: s

/-- `_replace_charref`, `Lib/html/__init__.py:91-115`, on `s.group(1)`, which is not empty. -/
def replaceCharref (s : List Nat) : Py (List Nat) :=
  match s with
  | 35 :: c :: r =>
    if c == 120 || c == 88 then .ok (numRef (intHex (rstripSemi r)))
    else
      match intDec (rstripSemi (c :: r)) with
      | .ok n => .ok (numRef n)
      | .error e => .error e
  | _ => .ok (namedRef s)

/-- `<class>{0,max}`, greedy: what it takes, and the rest. -/
def takeSpan (p : Nat → Bool) : Nat → List Nat → List Nat × List Nat
  | 0, s => ([], s)
  | _ + 1, [] => ([], [])
  | n + 1, c :: r =>
    if p c then
      let x := takeSpan p n r
      (c :: x.1, x.2)
    else ([], c :: r)

/-- `;?`. -/
def optSemi : List Nat → List Nat × List Nat
  | 59 :: r => ([59], r)
  | s => ([], s)

/-- The set of the third alternative. -/
def nameChar (c : Nat) : Bool :=
  !(c == 9 || c == 10 || c == 12 || c == 32 || c == 60 || c == 38 || c == 35 || c == 59)

/-- A run of `p`, then `;?`. The pattern ends there, so nothing backtracks. -/
def runSemi (p : Nat → Bool) (max : Nat) (s : List Nat) : Option (List Nat × List Nat) :=
  let a := takeSpan p max s
  if a.1.isEmpty then none
  else
    let b := optSemi a.2
    some (a.1 ++ b.1, b.2)

/-- `_charref`, `Lib/html/__init__.py:118-120`, after the `&`: group 1 and the rest. -/
def matchRef (s : List Nat) : Option (List Nat × List Nat) :=
  match s with
  | 35 :: t =>
    match runSemi isDigit t.length t with
    | some (g, r) => some (35 :: g, r)
    | none =>
      match t with
      | x :: u =>
        if x == 120 || x == 88 then
          match runSemi isHex u.length u with
          | some (g, r) => some (35 :: x :: g, r)
          | none => none
        else none
      | [] => none
  | _ => runSemi nameChar 32 s

/-- `_charref.sub(_replace_charref, s)`. -/
def subLoop : Nat → List Nat → Py (List Nat)
  | 0, _ => .error .modelFuel
  | _ + 1, [] => .ok []
  | fuel + 1, c :: r =>
    if c == 38 then
      match matchRef r with
      | some (g, rest) =>
        match replaceCharref g with
        | .error e => .error e
        | .ok x =>
          match subLoop fuel rest with
          | .error e => .error e
          | .ok y => .ok (x ++ y)
      | none =>
        match subLoop fuel r with
        | .error e => .error e
        | .ok y => .ok (38 :: y)
    else
      match subLoop fuel r with
      | .error e => .error e
      | .ok y => .ok (c :: y)

/-- `unescape`, `Lib/html/__init__.py:122-132`. -/
def unescape (s : List Nat) : Py (List Nat) :=
  if !s.contains 38 then .ok s else subLoop (s.length + 1) s

end PyLean.TextLibs.Html
