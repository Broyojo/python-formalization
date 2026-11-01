import PyLean.Datetime.Calendar
import PyLean.Fractions.Model

/-!
String and sequence primitives shared by the `calendar` and `statistics` models.

Text is `List Char` (one element per code point, as `len(str)` counts them).
`str.center`, `str.rstrip`, `str.join`, `str * int`, list indexing and slicing
are mirrored here because every formatter in `Lib/calendar.py` is built from them.
Widths are modelled as unbounded ints: `MemoryError` and the `Py_ssize_t` overflow
of `str.center` for absurd widths are outside the model.
-/

namespace PyLean.CoreLibs.CalStat

open PyLean

abbrev Str := List Char

/-- A string literal as `Str`. -/
def lit (t : String) : Str := t.toList

def spaces (n : Nat) : Str := List.replicate n ' '

/-- `str.center(width)`, Objects/unicodeobject.c `unicode_center_impl`:
`marg = width - len; left = marg / 2 + (marg & width & 1)`. -/
def center (s : Str) (width : Int) : Str :=
  if (s.length : Int) ≥ width then s
  else
    let marg := width - s.length
    let left := marg / 2 + (if marg % 2 = 1 ∧ width % 2 = 1 then 1 else 0)
    spaces left.toNat ++ s ++ spaces (marg - left).toNat

/-- Characters `str.rstrip()` removes, restricted to the ASCII whitespace the
formatters can meet (Objects/unicodetype_db.h, `_PyUnicode_IsWhitespace`). -/
def isSpaceChar (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0b' || c == '\x0c' ||
  c == '\x1c' || c == '\x1d' || c == '\x1e' || c == '\x1f'

/-- `str.rstrip()`. -/
def rstrip (s : Str) : Str := (s.reverse.dropWhile isSpaceChar).reverse

/-- `sep.join(parts)`. -/
def join (sep : Str) (parts : List Str) : Str := sep.intercalate parts

/-- `s * n` for a Python int `n`: empty when `n <= 0`. -/
def strTimes (s : Str) (n : Int) : Str := (List.replicate n.toNat s).flatten

/-- `'\n' * l`. -/
def nl (l : Int) : Str := strTimes ['\n'] l

/-- `repr(i)` / `'%d' % i` / `'%s' % i` for an int, with the 4300-digit limit. -/
def reprInt (i : Int) : Py Str := Fractions.strInt i

/-- `'%2i' % i`. -/
def fmt2i (i : Int) : Str :=
  let s := (if i < 0 then ['-'] else []) ++ Nat.toDigits 10 i.natAbs
  spaces (2 - s.length) ++ s

/-- `lst[i]`, Objects/listobject.c `list_subscript`. -/
def pyIndex {α : Type} (xs : List α) (i : Int) : Py α :=
  let n : Int := xs.length
  let j := if i < 0 then i + n else i
  if j < 0 ∨ j ≥ n then
    -- `PyNumber_AsSsize_t(item, PyExc_IndexError)` comes first for an index beyond `Py_ssize_t`
    if i ≥ 2 ^ 63 ∨ i < -(2 ^ 63) then .error (.indexError "cannot fit 'int' into an index-sized integer")
    else .error (.indexError "list index out of range")
  else match xs[j.toNat]? with
    | some x => .ok x
    | none => .error (.indexError "list index out of range")

/-- `s[:stop]` for an int `stop`. -/
def sliceTo {α : Type} (xs : List α) (stop : Int) : List α :=
  let n : Int := xs.length
  let e := if stop < 0 then max (stop + n) 0 else min stop n
  xs.take e.toNat

/-- `slice.indices(n)`, Objects/sliceobject.c `PySlice_AdjustIndices` for `step != 0`,
followed by the index sequence. `start` and `stop` are optional; the step is an int. -/
def sliceIndices (n : Nat) (start stop : Option Int) (step : Int) : List Nat :=
  let n' : Int := n
  let lower : Int := if step < 0 then -1 else 0
  let upper : Int := if step < 0 then n' - 1 else n'
  let adj (v : Int) : Int :=
    if v < 0 then max (v + n') lower else min v upper
  let s := match start with
    | some v => adj v
    | none => if step < 0 then upper else lower
  let e := match stop with
    | some v => adj v
    | none => if step < 0 then lower else upper
  let count : Nat :=
    if step < 0 then (if e < s then ((s - e - 1) / (-step) + 1).toNat else 0)
    else (if s < e then ((e - s - 1) / step + 1).toNat else 0)
  (List.range count).map (fun (i : Nat) => (s + (i : Int) * step).toNat)

/-- `lst[start:stop:step]`. -/
def pySlice {α : Type} (xs : List α) (start stop : Option Int) (step : Int) : Py (List α) :=
  if step = 0 then .error (.valueError "slice step cannot be zero")
  else .ok ((sliceIndices xs.length start stop step).filterMap (fun i => xs[i]?))

/-- `list(range(a, b))`. -/
def rangeI (a b : Int) : List Int := (List.range (b - a).toNat).map (fun (i : Nat) => a + (i : Int))

/-- `[xs[i:i+k] for i in range(0, len(xs), k)]` for `k > 0`. -/
def chunksGo {α : Type} (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | _ + 1, [] => []
  | f + 1, x :: xs => (x :: xs).take k :: chunksGo k f ((x :: xs).drop k)

def chunks {α : Type} (k : Nat) (xs : List α) : List (List α) := chunksGo k xs.length xs

/-- `[xs[i:i+width] for i in range(0, len(xs), width)]` for an arbitrary int:
`range` rejects a zero step and is empty for a negative one
(Objects/rangeobject.c `compute_range_length` and `range_new`). -/
def pyChunks {α : Type} (width : Int) (xs : List α) : Py (List (List α)) :=
  if width = 0 then .error (.valueError "range() arg 3 must not be zero")
  else if width < 0 then .ok []
  else .ok (chunks width.toNat xs)

end PyLean.CoreLibs.CalStat
