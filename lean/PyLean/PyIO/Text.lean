import PyLean.PyIO.Basic

/-!
Text helpers shared by the two `StringIO` models: UTF-8 with the
`surrogatepass` error handler (`Objects/unicodeobject.c`, `Python/codecs.c`),
newline scanning and translation (the `IncrementalNewlineDecoder` of
`Modules/_io/textio.c:328-519` and `Lib/_pyio.py:1948-2030`), and the
`repr()` of an ASCII `str` (for `illegal newline value: %r`).
-/

namespace PyLean.PyIO

open PyLean

/-! ## UTF-8 -/

/-- UTF-8 encoding of one code point; surrogates are encoded as three bytes
(`surrogatepass`). -/
def utf8Enc1 (c : Nat) : List Nat :=
  if c < 0x80 then [c]
  else if c < 0x800 then [0xC0 + c / 64, 0x80 + c % 64]
  else if c < 0x10000 then [0xE0 + c / 4096, 0x80 + c / 64 % 64, 0x80 + c % 64]
  else [0xF0 + c / 262144, 0x80 + c / 4096 % 64, 0x80 + c / 64 % 64, 0x80 + c % 64]

def utf8Enc (s : List Nat) : List Nat := s.flatMap utf8Enc1

def isSurrogate (c : Nat) : Bool := 0xD800 ≤ c && c ≤ 0xDFFF

def isCont (b : Nat) : Bool := 0x80 ≤ b && b ≤ 0xBF

/-- Sequence length announced by a lead byte (0: invalid start byte). -/
def seqLen (b0 : Nat) : Nat :=
  if b0 < 0x80 then 1
  else if 0xC2 ≤ b0 ∧ b0 ≤ 0xDF then 2
  else if 0xE0 ≤ b0 ∧ b0 ≤ 0xEF then 3
  else if 0xF0 ≤ b0 ∧ b0 ≤ 0xF4 then 4
  else 0

/-- Allowed range of the second byte (unicodeobject.c, `asciilib_utf8_decode`
in Objects/stringlib/codecs.h). For `0xED` the strict range is `80..9F`; the
`surrogatepass` handler also accepts `A0..BF` (an encoded surrogate) when the
whole three-byte sequence is present, and the decoder keeps a truncated
`ED A0..BF` as incomplete (unicodeobject.c:5346-5352). -/
def secondOk (b0 b1 : Nat) : Bool :=
  if b0 = 0xE0 then 0xA0 ≤ b1 && b1 ≤ 0xBF
  else if b0 = 0xF0 then 0x90 ≤ b1 && b1 ≤ 0xBF
  else if b0 = 0xF4 then 0x80 ≤ b1 && b1 ≤ 0x8F
  else isCont b1

/-- Outcome of decoding the sequence at the head of the input. -/
inductive Dec1 where
  | char (c : Nat) (n : Nat)
  | incomplete
  | invalid

def utf8Dec1 (l : List Nat) : Dec1 :=
  match l with
  | [] => .incomplete
  | b0 :: rest =>
    let n := seqLen b0
    if n = 0 then .invalid
    else if n = 1 then .char b0 1
    else
      let tail := rest.take (n - 1)
      let okPrefix : Bool := match tail with
        | [] => true
        | b1 :: bs => secondOk b0 b1 && bs.all isCont
      if !okPrefix then .invalid
      else if tail.length < n - 1 then .incomplete
      else
        let v := tail.foldl (fun acc b => acc * 64 + (b - 0x80)) (if n = 2 then b0 - 0xC0 else if n = 3 then b0 - 0xE0 else b0 - 0xF0)
        .char v n

/-- `codecs.utf_8_decode(data, 'surrogatepass', final)`: the decoded code
points and the unconsumed tail (an incomplete sequence when not `final`). -/
def utf8DecF (final : Bool) : Nat → List Nat → Py (List Nat × List Nat)
  | 0, _ => .error .modelFuel
  | _, [] => .ok ([], [])
  | fuel + 1, l =>
    match utf8Dec1 l with
    | .invalid => .error unicodeDecodeError
    | .incomplete => if final then .error unicodeDecodeError else .ok ([], l)
    | .char c n =>
      match utf8DecF final fuel (l.drop n) with
      | .error e => .error e
      | .ok (cs, t) => .ok (c :: cs, t)

def utf8Dec (final : Bool) (l : List Nat) : Py (List Nat × List Nat) :=
  utf8DecF final (l.length + 1) l

/-! ## Newlines -/

def cr : Nat := 13
def lf : Nat := 10

/-- Which kinds of newline occur: `(lone \r, lone \n, \r\n)`. -/
structure NlKinds where
  cr : Bool
  lf : Bool
  crlf : Bool
  deriving Repr, DecidableEq, Inhabited

def NlKinds.union (a b : NlKinds) : NlKinds := ⟨a.cr || b.cr, a.lf || b.lf, a.crlf || b.crlf⟩

def nlKinds : List Nat → NlKinds
  | [] => ⟨false, false, false⟩
  | 13 :: 10 :: r => (nlKinds r).union ⟨false, false, true⟩
  | 13 :: r => (nlKinds r).union ⟨true, false, false⟩
  | 10 :: r => (nlKinds r).union ⟨false, true, false⟩
  | _ :: r => nlKinds r

/-- `\r\n` and lone `\r` become `\n`. -/
def translateNl : List Nat → List Nat
  | [] => []
  | 13 :: 10 :: r => 10 :: translateNl r
  | 13 :: r => 10 :: translateNl r
  | c :: r => c :: translateNl r

/-- `s.replace('\n', nl)`. -/
def replaceLf (nl : List Nat) : List Nat → List Nat
  | [] => []
  | c :: r => if c = 10 then nl ++ replaceLf nl r else c :: replaceLf nl r

/-- The `newlines` attribute for a set of seen kinds (textio.c:639-663,
_pyio.py:2020-2031; both use the same order). -/
def newlinesVal (k : NlKinds) : Val :=
  match k.cr, k.lf, k.crlf with
  | false, false, false => .none
  | true, false, false => .str [13]
  | false, true, false => .str [10]
  | false, false, true => .str [13, 10]
  | true, true, false => .list [.str [13], .str [10]]
  | true, false, true => .list [.str [13], .str [13, 10]]
  | false, true, true => .list [.str [10], .str [13, 10]]
  | true, true, true => .list [.str [13], .str [10], .str [13, 10]]

/-- `str.find(sub, start)` on code-point lists (`-1` when absent). -/
def findFrom (l sub : List Nat) (start : Nat) : Int :=
  let rec go (i : Nat) (rest : List Nat) (fuel : Nat) : Int :=
    match fuel with
    | 0 => -1
    | fuel + 1 =>
      if sub.isPrefixOf rest then i else
      match rest with
      | [] => -1
      | _ :: r => go (i + 1) r fuel
  go start (l.drop start) (l.length + 1)

/-! ## `repr()` of a str (ASCII only) -/

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `repr(s)` for code points below 0x7F (`Objects/unicodeobject.c`,
`unicode_repr`); `none` for other strings. -/
def reprAscii (s : List Nat) : Option String :=
  if s.any (· ≥ 0x7F) then none else
  let q : Nat := if s.contains 39 && !s.contains 34 then 34 else 39
  let esc (c : Nat) : List Char :=
    if c = q ∨ c = 92 then ['\\', Char.ofNat c]
    else if c = 9 then ['\\', 't'] else if c = 10 then ['\\', 'n'] else if c = 13 then ['\\', 'r']
    else if c < 32 then ['\\', 'x', hexDigit (c / 16), hexDigit (c % 16)]
    else [Char.ofNat c]
  some (String.ofList (Char.ofNat q :: (s.flatMap esc ++ [Char.ofNat q])))

def illegalNewline (s : List Nat) : PyExc :=
  match reprAscii s with
  | some r => .valueError s!"illegal newline value: {r}"
  | none => .valueError "~illegal newline value"

/-- A `StringIO` operation (both twins). -/
inductive SOp where
  | read (size : Option Int)
  | readline (size : Option Int)
  | readlines (hint : Option Int)
  | write (s : List Nat)
  | seek (pos : Int) (whence : Int)
  | tell
  | truncate (size : Option Int)
  | getvalue
  | close
  | next
  | closed
  | newlines
  /-- `f.seek(f.tell())`: the result of `seek`, or the exception of either call. -/
  | seekTell
  deriving Repr, DecidableEq, Inhabited

end PyLean.PyIO
