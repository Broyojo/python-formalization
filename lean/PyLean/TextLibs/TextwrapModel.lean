import PyLean.Core
import PyLean.UnicodeObj.Ctype

/-!
Model of `TextWrapper._wrap_chunks` and `_handle_long_word`, `Lib/textwrap.py:197-339`, CPython 3.14.7.
The regexes of `_split` and the munging before it are not modelled here: these two functions take any
list of chunks, and everything about line length and lost text is decided in them. `chunks` is kept in
reading order, so its head is `chunks[-1]` of the reversed list CPython uses.

The loops take fuel. The fuel runs out exactly on the inputs where CPython never returns, which the
difftest checks by counting calls of `_handle_long_word`.
-/

namespace PyLean.TextLibs.Textwrap

open PyLean

/-- A list of strings. -/
abbrev L := List (List Nat)

/-- The attributes the two functions read. -/
structure TW where
  width : Int
  initial : List Nat := []
  subsequent : List Nat := []
  dropWs : Bool := true
  breakLong : Bool := true
  breakHyph : Bool := true
  maxLines : Option Int := none
  placeholder : List Nat := [32, 91, 46, 46, 46, 93]
  deriving Repr, Inhabited

/-- `s.strip() == ''`. -/
def blank (s : List Nat) : Bool := s.all PyLean.UnicodeObj.isSpace

/-- `s.lstrip()`. -/
def lstrip (s : List Nat) : List Nat := s.dropWhile PyLean.UnicodeObj.isSpace

/-- `s.rstrip()`. -/
def rstrip (s : List Nat) : List Nat := (lstrip s.reverse).reverse

/-- `sum(map(len, cur_line))`. -/
def lenOf : L → Nat
  | [] => 0
  | x :: r => x.length + lenOf r

/-- The measure that bounds the outer loop: every character, and two steps for every chunk. -/
def size (l : L) : Nat := lenOf l + 2 * l.length

/-- `s.rfind('-')`, `Lib/textwrap.py:220`. -/
def rfindHyphen (pre : List Nat) : Option Nat :=
  (pre.reverse.findIdx? (· == 45)).map (fun i => pre.length - 1 - i)

/-- The end of the piece `_handle_long_word` cuts, `Lib/textwrap.py:215-222`. -/
def cutEnd (t : TW) (chunk : List Nat) (space : Nat) : Nat :=
  if t.breakHyph && decide (chunk.length > space) then
    match rfindHyphen (chunk.take space) with
    | some hyphen => if hyphen > 0 && (chunk.take hyphen).any (· != 45) then hyphen + 1 else space
    | none => space
  else space

/-- `space_left`, `Lib/textwrap.py:207-210`. -/
def spaceLeft (curLen : Nat) (width : Int) : Int := if width < 1 then 1 else width - curLen

/-- `_handle_long_word`, `Lib/textwrap.py:197-236`, on `chunk :: rest`. It gives the chunks and the
current line. -/
def handleLong (t : TW) (chunk : List Nat) (rest cur : L) (curLen : Nat) (width : Int) : L × L :=
  if t.breakLong && decide (spaceLeft curLen width > 0) then
    let e := cutEnd t chunk (spaceLeft curLen width).toNat
    (chunk.drop e :: rest, cur ++ [chunk.take e])
  else if cur.isEmpty then (rest, [chunk])
  else (chunk :: rest, cur)

/-- `indent`, `Lib/textwrap.py:274-277`. -/
def indentOf (t : TW) (lines : L) : List Nat := if lines.isEmpty then t.initial else t.subsequent

/-- `width`, `Lib/textwrap.py:280`. -/
def widthOf (t : TW) (lines : L) : Int := t.width - (indentOf t lines).length

/-- `Lib/textwrap.py:284-285`. -/
def startChunks (t : TW) (lines : L) : L → L
  | [] => []
  | c0 :: r0 => if t.dropWs && blank c0 && !lines.isEmpty then r0 else c0 :: r0

/-- The inner `while chunks`, `Lib/textwrap.py:287-297`: the line, its length, and the chunks left. -/
def fill (width : Int) : L → L → Nat → L × Nat × L
  | [], cur, n => (cur, n, [])
  | c :: r, cur, n =>
    if ((n + c.length : Nat) : Int) ≤ width then fill width r (cur ++ [c]) (n + c.length)
    else (cur, n, c :: r)

/-- `Lib/textwrap.py:301-303`: the chunks, the line and its length. -/
def longStep (t : TW) (width : Int) (cur : L) (n : Nat) : L → L × L × Nat
  | [] => ([], cur, n)
  | c :: r =>
    if (c.length : Int) > width then
      let h := handleLong t c r cur n width
      (h.1, h.2, lenOf h.2)
    else (c :: r, cur, n)

/-- `Lib/textwrap.py:306-308`. -/
def dropTail (t : TW) (cur : L) (n : Nat) : L × Nat :=
  if t.dropWs && !cur.isEmpty && blank (cur.getLastD []) then
    (cur.dropLast, n - (cur.getLastD []).length)
  else (cur, n)

/-- One pass of `Lib/textwrap.py:284-308`: the line, its length, and the chunks left. -/
def lineOf (t : TW) (lines chunks : L) : L × Nat × L :=
  let width := widthOf t lines
  let a := fill width (startChunks t lines chunks) [] 0
  let b := longStep t width a.1 a.2.1 a.2.2
  let c := dropTail t b.2.1 b.2.2
  (c.1, c.2, b.1)

/-- The condition of `Lib/textwrap.py:311-316`. -/
def fits (t : TW) (lines ch : L) (n : Nat) : Bool :=
  match t.maxLines with
  | none => true
  | some m =>
    decide ((lines.length + 1 : Int) < m) ||
      ((ch.isEmpty || (t.dropWs && ch.length == 1 && blank (ch.headD []))) &&
        decide ((n : Int) ≤ widthOf t lines))

/-- The `while cur_line`, `Lib/textwrap.py:321-337`, over the reversed line, so that `del cur_line[-1]`
is the tail. Every way out of it leaves the outer loop too. -/
def placeLoop (t : TW) (indent : List Nat) (lines : L) (width : Int) : L → Int → L
  | [], _ =>
    match lines.getLast? with
    | some last =>
      let prev := rstrip last
      if ((prev.length + t.placeholder.length : Nat) : Int) ≤ t.width then
        lines.dropLast ++ [prev ++ t.placeholder]
      else lines ++ [indent ++ lstrip t.placeholder]
    | none => lines ++ [indent ++ lstrip t.placeholder]
  | x :: rest, n =>
    if !blank x && decide (n + t.placeholder.length ≤ width) then
      lines ++ [indent ++ ((x :: rest).reverse ++ [t.placeholder]).flatten]
    else placeLoop t indent lines width rest (n - x.length)

/-- The outer `while chunks`, `Lib/textwrap.py:266-337`. -/
def loop (t : TW) : Nat → L → L → Py L
  | 0, _, _ => .error .modelFuel
  | _ + 1, lines, [] => .ok lines
  | fuel + 1, lines, c0 :: r0 =>
    let r := lineOf t lines (c0 :: r0)
    if r.1.isEmpty then loop t fuel lines r.2.2
    else if fits t lines r.2.2 r.2.1 then
      loop t fuel (lines ++ [indentOf t lines ++ r.1.flatten]) r.2.2
    else .ok (placeLoop t (indentOf t lines) lines (widthOf t lines) r.1.reverse r.2.1)

/-- The check of `Lib/textwrap.py:254-260`. -/
def tooBig (t : TW) : Bool :=
  match t.maxLines with
  | none => false
  | some m =>
    let indent := if m > 1 then t.subsequent else t.initial
    decide (((indent.length + (lstrip t.placeholder).length : Nat) : Int) > t.width)

/-- `_wrap_chunks`, `Lib/textwrap.py:238-339`. -/
def wrapChunks (t : TW) (chunks : L) : Py L :=
  if t.width ≤ 0 then .error (.valueError s!"invalid width {t.width} (must be > 0)")
  else if tooBig t then .error (.valueError "placeholder too large for max width")
  else loop t (size chunks + 2) [] chunks

end PyLean.TextLibs.Textwrap
