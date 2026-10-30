import PyLean.PyIO.Text

/-!
The C `io.StringIO` (`Modules/_io/stringio.c`), CPython 3.14.7, plus the
inherited `_io._IOBase.readlines` (`Modules/_io/iobase.c:704-777`) and the
line search `_PyIO_find_line_ending` (`Modules/_io/textio.c:2105-2205`).

The buffer is a list of code points (`Py_UCS4`). The accumulating
(`_PyUnicodeWriter`) and realized states hold the same text and are not
distinguished. The embedded `IncrementalNewlineDecoder` is always called
with `final=1` (stringio.c:181-182), so its `pendingcr` stays clear; only
`seennl` and `translate` are kept.
-/

namespace PyLean.PyIO

open PyLean

structure SCState where
  buf : List Nat
  pos : Nat
  closed : Bool
  /-- `readnl`: `none` for `newline=None`. -/
  readnl : Option (List Nat)
  readuniversal : Bool
  readtranslate : Bool
  writenl : Option (List Nat)
  /-- The decoder exists iff `readuniversal`; `seennl` as a set of kinds. -/
  hasDecoder : Bool
  translate : Bool
  seennl : NlKinds
  deriving Repr, DecidableEq, Inhabited

namespace SC

def closedErr : PyExc := .valueError "I/O operation on closed file"

/-- `resize_buffer`, stringio.c:76-128, for a request of `size` characters
that exceeds the current allocation. -/
def resizeCheck (size : Nat) : Py Unit :=
  let size := size + 1
  if (size : Int) > ssizeMax then .error (.overflowError "new buffer size too large") else
  let alloc := size + 1
  if alloc > (2 ^ 64 - 1) / 4 then .error (.overflowError "new buffer size too large") else
  if 4 * alloc ≥ memLimit then .error memoryError else .ok ()

/-- `write_str`, stringio.c:172-265. The decoder records newline kinds
before the length checks, so a failing write still updates `newlines`. -/
def writeStr (s : SCState) (obj : List Nat) : SCState × Py Unit :=
  let (s, decoded) :=
    if s.hasDecoder then
      ({ s with seennl := s.seennl.union (nlKinds obj) },
       if s.translate then translateNl obj else obj)
    else (s, obj)
  let decoded := match s.writenl with
    | some nl => replaceLf nl decoded
    | none => decoded
  let len : Nat := decoded.length
  if (s.pos : Int) > ssizeMax - (len : Int) then (s, .error (.overflowError "new position too large")) else
  let r : Py Unit := if s.pos + len > s.buf.length then resizeCheck (s.pos + len) else .ok ()
  match r with
  | .error e => (s, .error e)
  | .ok () => ({ s with buf := writeAt s.buf s.pos decoded, pos := s.pos + len }, .ok ())

/-- `_io_StringIO___init___impl`, stringio.c:644-743. `newline` is `none`
for `None`; the default is `'\n'`. `PyUnicode_AsUTF8` fails on a lone
surrogate; the validity test then reads the UTF-8 bytes as a C string, i.e.
only up to the first NUL. -/
def init (value : Option (List Nat)) (newline : Option (List Nat)) : Py SCState := do
  let cstr : Option (List Nat) ← match newline with
    | none => pure none
    | some nl =>
      if nl.any isSurrogate then throw unicodeEncodeError
      else pure (some ((utf8Enc nl).takeWhile (· ≠ 0)))
  match cstr, newline with
  | some c, some nl =>
    if !(c = [] ∨ c = [10] ∨ c = [13] ∨ c = [13, 10]) then throw (illegalNewline nl)
  | _, _ => pure ()
  let readuniversal := match cstr with
    | none => true
    | some c => c = []
  let s : SCState :=
    { buf := [], pos := 0, closed := false
      readnl := cstr
      readuniversal := readuniversal
      readtranslate := cstr.isNone
      writenl := match cstr with
        | some (13 :: _) => cstr
        | _ => none
      hasDecoder := readuniversal
      translate := cstr.isNone
      seennl := ⟨false, false, false⟩ }
  let value := value.getD []
  if value.length > 0 then
    match writeStr s value with
    | (_, .error e) => throw e
    | (s, .ok ()) => pure { s with pos := 0 }
  else pure s

/-- `_PyIO_find_line_ending`, textio.c:2127-2205, on `buf[pos:pos+limit]`
(the C code sets a NUL sentinel at the end, stringio.c:401-407): the length
of the line including its ending, or `none`. -/
def findLineEnding (s : SCState) (seg : List Nat) : Option Nat :=
  if s.readtranslate then (findIdx? seg 10).map (· + 1)
  else if s.readuniversal then
    let rec uni (i : Nat) : List Nat → Option Nat
      | [] => none
      | 10 :: _ => some (i + 1)
      | 13 :: 10 :: _ => some (i + 2)
      | 13 :: _ => some (i + 1)
      | _ :: r => uni (i + 1) r
    uni 0 seg
  else
    let nl := s.readnl.getD []
    let p := findFrom seg nl 0
    if p ≥ 0 then some (p.toNat + nl.length) else none

/-- `_stringio_readline`, stringio.c:388-416. -/
def readlineRaw (s : SCState) (limit : Int) : SCState × List Nat :=
  if s.pos ≥ s.buf.length then (s, []) else
  let avail := s.buf.length - s.pos
  let limit : Nat := if limit < 0 ∨ limit > avail then avail else limit.toNat
  let seg := slice s.buf s.pos limit
  let len := (findLineEnding s seg).getD limit
  ({ s with pos := s.pos + len }, slice s.buf s.pos len)

/-- `stringio_iternext`, stringio.c:437-474 (exact `StringIO` type). -/
def next (s : SCState) : SCState × Py Val :=
  if s.closed then (s, .error closedErr) else
  let (s', l) := readlineRaw s (-1)
  if l = [] then (s', .error .stopIteration) else (s', .ok (.str l))

/-- The loop of `_io__IOBase_readlines_impl`, iobase.c:745-768. -/
def readlinesLoop (hint : Int) : SCState → Int → List Atom → Nat → SCState × Py Val
  | s, _, _, 0 => (s, .error .modelFuel)
  | s, length, acc, fuel + 1 =>
    match next s with
    | (s', .error .stopIteration) => (s', .ok (.list acc.reverse))
    | (s', .error e) => (s', .error e)
    | (s', .ok v) =>
      let line := match v with
        | .str l => l
        | _ => []
      let acc := Atom.str line :: acc
      if hint > 0 ∧ (line.length : Int) > hint - length then (s', .ok (.list acc.reverse))
      else readlinesLoop hint s' (length + line.length) acc fuel

/-- `_io__IOBase_readlines_impl`, iobase.c:716-777: the hint is converted
first; `iter(self)` (`iobase_iter`, iobase.c:676-683) raises if closed; for
`hint <= 0` the list is extended with every line. -/
def readlines (s : SCState) (hint : Option Int) : SCState × Py Val :=
  match optSsize (-1) hint with
  | .error e => (s, .error e)
  | .ok hint =>
    if s.closed then (s, .error (.valueError "I/O operation on closed file.")) else
    readlinesLoop hint s 0 [] (s.buf.length - s.pos + 2)

/-- `_io_StringIO_seek_impl`, stringio.c:497-535, after Argument Clinic
converted `pos` (`Py_ssize_t`) and `whence` (`int`). -/
def seek (s : SCState) (pos whence : Int) : SCState × Py Val :=
  match argSsize pos with
  | .error e => (s, .error e)
  | .ok pos =>
  match argCInt whence with
  | .error e => (s, .error e)
  | .ok whence =>
  if s.closed then (s, .error closedErr) else
  if whence ≠ 0 ∧ whence ≠ 1 ∧ whence ≠ 2 then
    (s, .error (.valueError s!"Invalid whence ({whence}, should be 0, 1 or 2)")) else
  if pos < 0 ∧ whence = 0 then (s, .error (.valueError s!"Negative seek position {pos}")) else
  if whence ≠ 0 ∧ pos ≠ 0 then (s, .error (osError "Can't do nonzero cur-relative seeks")) else
  let pos : Nat := if whence = 1 then s.pos else if whence = 2 then s.buf.length else pos.toNat
  ({ s with pos := pos }, .ok (.int pos))

def step (s : SCState) : SOp → SCState × Py Val
  | .seekTell => if s.closed then (s, .error closedErr) else seek s s.pos 0
  | .read size =>
    match optSsize (-1) size with
    | .error e => (s, .error e)
    | .ok size =>
      if s.closed then (s, .error closedErr) else
      -- stringio.c:356-380
      let n : Int := (s.buf.length : Int) - s.pos
      let size : Int := if size < 0 ∨ size > n then (if n < 0 then 0 else n) else size
      ({ s with pos := s.pos + size.toNat }, .ok (.str (slice s.buf s.pos size.toNat)))
  | .readline size =>
    match optSsize (-1) size with
    | .error e => (s, .error e)
    | .ok size =>
      if s.closed then (s, .error closedErr) else
      let (s', l) := readlineRaw s size
      (s', .ok (.str l))
  | .readlines h => readlines s h
  | .write obj =>
    -- stringio.c:548-567
    if s.closed then (s, .error closedErr) else
    if obj.length > 0 then
      match writeStr s obj with
      | (s', .error e) => (s', .error e)
      | (s', .ok ()) => (s', .ok (.int obj.length))
    else (s, .ok (.int 0))
  | .seek pos whence => seek s pos whence
  | .tell => if s.closed then (s, .error closedErr) else (s, .ok (.int s.pos))
  | .truncate size =>
    -- stringio.c:477-495; `None` means the current position
    match optSsize s.pos size with
    | .error e => (s, .error e)
    | .ok size =>
      if s.closed then (s, .error closedErr) else
      if size < 0 then (s, .error (.valueError s!"Negative size value {size}")) else
      let s := if size < s.buf.length then { s with buf := s.buf.take size.toNat } else s
      (s, .ok (.int size))
  | .getvalue => if s.closed then (s, .error closedErr) else (s, .ok (.str s.buf))
  | .close => ({ s with closed := true, buf := [] }, .ok .none)
  | .next => next s
  | .closed => (s, .ok (.bool s.closed))
  | .newlines =>
    -- stringio.c:1017-1027
    if s.closed then (s, .error closedErr) else
    if s.hasDecoder then (s, .ok (newlinesVal s.seennl)) else (s, .ok .none)

end SC

/-- Run the C `StringIO(value, newline)` constructor and the operations. -/
def runSC (value : Option (List Nat)) (newline : Option (List Nat)) (ops : List SOp) : Py (List (Py Val)) :=
  match SC.init value newline with
  | .error e => .error e
  | .ok s => .ok (runOps' SC.step s ops)
where
  runOps' (step : SCState → SOp → SCState × Py Val) : SCState → List SOp → List (Py Val)
    | _, [] => []
    | s, o :: os => let (s', r) := step s o; r :: runOps' step s' os

end PyLean.PyIO
