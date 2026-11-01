import PyLean.UnicodeObj.TextCase

/-!
`_PyUnicode_Dedent` (Objects/unicodeobject.c:14352-14500), used by `python -c`
(Modules/main.c:258), and its documented twin `textwrap.dedent`
(Lib/textwrap.py:416-444).

The C code walks the UTF-8 bytes. It only compares them with `'\n'`, `' '` and
`'\t'`, and copies the rest verbatim, so the model works on any list of units;
`Text = code points` and `Text = UTF-8 bytes` give the same result up to encoding.
`PyUnicode_AsUTF8AndSize` failing on a lone surrogate is not modelled here (see
`CodecUtf8`).
-/

namespace PyLean.UnicodeObj

/-- One line of the buffer: the units up to `'\n'`, whether a `'\n'` ended it
(`iter < end`), and what follows. -/
def nextLine : List Nat → List Nat × Bool × List Nat
  | [] => ([], false, [])
  | 10 :: rest => ([], true, rest)
  | c :: rest =>
    let (line, nl, r) := nextLine rest
    (c :: line, nl, r)

/-- `leading_whitespace_end - line_start`, unicodeobject.c:14366-14378: the offset
of the first unit other than `' '` and `'\t'`, if there is one. -/
def leadingEnd : List Nat → Nat → Option Nat
  | [], _ => none
  | c :: cs, i => if c != 32 && c != 9 then some i else leadingEnd cs (i + 1)

/-- The common-prefix loop, unicodeobject.c:14399-14408. -/
def commonLen : List Nat → List Nat → Nat
  | a :: as, b :: bs => if a == b then 1 + commonLen as bs else 0
  | _, _ => 0

/-- The `for` loop of `search_longest_common_leading_whitespace`,
unicodeobject.c:14362-14416. `start` is the text of the current longest
whitespace (`_start`), already cut to `_len`. Fuel bounds the number of lines. -/
def searchLeading : Nat → List Nat → Option (List Nat) → Nat
  | 0, _, _ => 0
  | _ + 1, [], none => 0
  | _ + 1, [], some start => start.length
  | fuel + 1, src, start =>
    let (line, _, rest) := nextLine src
    match leadingEnd line 0 with
    | some 0 => 0
    | none => searchLeading fuel rest start
    | some e =>
      let ws := line.take e
      match start with
      | none => searchLeading fuel rest (some ws)
      | some st =>
        let newLen := commonLen st ws
        if newLen = 0 then 0 else searchLeading fuel rest (some (st.take newLen))

/-- The result of the C copy loop: `none` when `new_line_len` is negative, which
in C is `memcpy(dest_iter, ..., (size_t)negative)`. -/
def dedentLoop (wsLen : Nat) : Nat → List Nat → Str → Option Str
  | 0, _, out => some out
  | _ + 1, [], out => some out
  | fuel + 1, src, out =>
    let (line, appendNewline, rest) := nextLine src
    let inLeading := line.all fun c => c == 32 || c == 9
    if inLeading && appendNewline then dedentLoop wsLen fuel rest (out ++ [10])
    else if line.length < wsLen then none
    else
      dedentLoop wsLen fuel rest
        (out ++ line.drop wsLen ++ if appendNewline then [10] else [])

/-- `_PyUnicode_Dedent`, unicodeobject.c:14430-14500. -/
def pyUnicodeDedent (src : Str) : Option Str :=
  if src.length = 0 then some src
  else
    let whitespaceLen := searchLeading (src.length + 1) src none
    if whitespaceLen = 0 then some src
    else dedentLoop whitespaceLen (src.length + 1) src []

/-! ## `textwrap.dedent` -/

/-- `text.split('\n')`. -/
def splitNl (fuel : Nat) (s : Str) : List Str :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    let (line, nl, rest) := nextLine s
    if nl then line :: splitNl fuel rest else [line]

/-- `str.isspace`, restated from `allShape`. -/
def strIsSpace (s : Str) : Bool := unicodeIsSpace s

/-- Lexicographic `<` of Python strings. -/
def strLt : Str → Str → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a == b then strLt as bs else decide (a < b)

/-- `min(lines, default='')` and `max(lines, default='')`. -/
def strMin : List Str → Str
  | [] => []
  | l :: ls => ls.foldl (fun m x => if strLt x m then x else m) l

def strMax : List Str → Str
  | [] => []
  | l :: ls => ls.foldl (fun m x => if strLt m x then x else m) l

/-- The `for margin, c in enumerate(l1)` loop, Lib/textwrap.py:440-442. The loop
variable stays at the index of the `break`, or at the last index. -/
def marginLoop (l2 : Str) : Nat → List Nat → Nat
  | _, [] => 0
  | i, [c] =>
    if some c != l2[i]? || !(c == 32 || c == 9) then i else i
  | i, c :: cs =>
    if some c != l2[i]? || !(c == 32 || c == 9) then i else marginLoop l2 (i + 1) cs

/-- `textwrap.dedent`, Lib/textwrap.py:429-444, on `str` input. -/
def textwrapDedent (text : Str) : Str :=
  let lines := splitNl (text.length + 1) text
  let nonBlank := lines.filter fun l => l.length != 0 && !strIsSpace l
  let l1 := strMin nonBlank
  let l2 := strMax nonBlank
  let margin := marginLoop l2 0 l1
  let out := lines.map fun l => if !strIsSpace l then l.drop margin else []
  (out.intersperse [10]).flatten

example : textwrapDedent (lit "  a\n  b\n") = lit "a\nb\n" := by decide
example : pyUnicodeDedent (lit "  a\n  b\n") = some (lit "a\nb\n") := by decide

end PyLean.UnicodeObj
