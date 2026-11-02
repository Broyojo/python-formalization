import PyLean.UnicodeObj.MethStrip
import PyLean.RangeSlice.Model

/-!
Indexing and slicing a `str`: `unicode_subscript` (Objects/unicodeobject.c:13803-13871),
`unicode_getitem` (:11706-11725) and the 3.15 fast path `_PyUnicode_BinarySlice`
(:12375-12385), which the `BINARY_SLICE` opcode (Python/bytecodes.c:1079-1105) runs for
`s[a:b]` on an exact `str`, while `s[a:b:c]` and `s[slice(a, b)]` go through
`unicode_subscript`. `PySlice_AdjustIndices` (Objects/sliceobject.c:265-304) is
`RangeSlice.adjustIndices`.
-/

namespace PyLean.UnicodeObj

open PyLean

/-- A `slice` object: its three fields, any objects. -/
structure SliceObj where
  start : Arg
  stop : Arg
  step : Arg

/-- `PySlice_Unpack`, Objects/sliceobject.c:219-262: the step first, then start, then stop,
each through `_PyEval_SliceIndex`. -/
def sliceUnpackObj (r : SliceObj) : Py (Int × Int × Int) := do
  let step ← match r.step with
    | .none => pure 1
    | x => do
      let st ← sliceIndexNotNone x
      if st = 0 then throw (.valueError "slice step cannot be zero")
      pure (if st < -ssizeMax then -ssizeMax else st)
  let start ← match r.start with
    | .none => pure (if step < 0 then ssizeMax else 0)
    | x => sliceIndexNotNone x
  let stop ← match r.stop with
    | .none => pure (if step < 0 then ssizeMin else ssizeMax)
    | x => sliceIndexNotNone x
  return (start, stop, step)

/-- `unicode_getitem`, unicodeobject.c:11706-11725; `unicode_char` builds the one-character
string. -/
def unicodeGetitem (s : Str) (index : Int) : Py Str :=
  if index < 0 ∨ index ≥ s.length then .error (.indexError "string index out of range")
  else .ok [s.getD index.toNat 0]

/-- What `s[item]` receives: an object, or a `slice`. -/
inductive SubItem where
  | obj (a : Arg)
  | slice (r : SliceObj)

/-- `unicode_subscript`, unicodeobject.c:13803-13871. The general case (:13837-13866) copies
`slicelength` characters from `start` by `step`; its `size_t` cursor stays in the string
(`RangeSlice` proves the same cursor right for lists), and the kind it computes is not
visible in the value. -/
def unicodeSubscript (s : Str) : SubItem → Py Str
  | .obj a =>
    if a.hasIndex then do
      let i ← asSsizeIndexError a
      let i := if i < 0 then i + s.length else i
      unicodeGetitem s i
    else .error (.typeError s!"string indices must be integers, not '{a.tpName}'")
  | .slice r => do
    let (start, stop, step) ← sliceUnpackObj r
    let (start, _, slicelength) := RangeSlice.adjustIndices s.length start stop step
    if slicelength ≤ 0 then return []
    else if start = 0 ∧ step = 1 ∧ slicelength = s.length then return s
    else if step = 1 then pyUnicodeSubstring s start (start + slicelength)
    else return (List.range slicelength.toNat).map fun (i : Nat) => s.getD (start + (i : Int) * step).toNat 0

/-- `_PyEval_UnpackIndices`, Python/ceval.c:2981-2999, for a length that is never negative. -/
def unpackIndices (start stop : Arg) (len : Int) : Py (Int × Int) := do
  let istart ← sliceIndex start 0
  let istop ← sliceIndex stop ssizeMax
  let (a, b, _) := RangeSlice.adjustIndices len istart istop 1
  return (a, b)

/-- `_PyUnicode_BinarySlice`, unicodeobject.c:12375-12385. -/
def unicodeBinarySlice (s : Str) (start stop : Arg) : Py Str := do
  let (a, b) ← unpackIndices start stop s.length
  pyUnicodeSubstring s a b

end PyLean.UnicodeObj
