import PyLean.UnicodeObj.TextProps2

/-!
Arguments of the `str` methods (Objects/unicodeobject.c, CPython 3.15.2) and the conversions
their Argument Clinic wrappers (Objects/clinic/unicodeobject.c.h) and the slice machinery
(Python/ceval.c, Objects/abstract.c) apply to them.

An argument is an `int` (a `bool` is the int 0 or 1), a `str`, `None`, a tuple, an instance of
a class with `__index__`, or an instance of some other class. `__index__` is fallible: its
answer is an int or the exception it raises (a non-int answer is the `TypeError` of
`_PyNumber_Index`, :1432-1437, which the difftest builds into the answer). Subclasses of `str`
and `int` are out of scope.
-/

namespace PyLean.UnicodeObj

open PyLean

inductive Arg where
  | int (v : Int)
  | str (s : Str)
  | none
  | tuple (items : List Arg)
  /-- An instance of class `tp` whose `__index__` answers `r`. -/
  | index (tp : String) (r : Py Int)
  /-- An instance of class `tp` with no `__index__` (a float, a list, ...). -/
  | other (tp : String)

/-- `Py_TYPE(obj)->tp_name`. -/
def Arg.tpName : Arg → String
  | .int _ => "int"
  | .str _ => "str"
  | .none => "NoneType"
  | .tuple _ => "tuple"
  | .index tp _ => tp
  | .other tp => tp

/-- `_PyIndex_Check`: the type has `nb_index`. -/
def Arg.hasIndex : Arg → Bool
  | .int _ | .index _ _ => true
  | _ => false

/-- `_PyNumber_Index`, Objects/abstract.c:1410-1449. -/
def numberIndex : Arg → Py Int
  | .int v => .ok v
  | .index _ r => r
  | a => .error (.typeError s!"'{a.tpName}' object cannot be interpreted as an integer")

def ssizeOverflowExc : PyExc := .overflowError "Python int too large to convert to C ssize_t"

/-- `PyLong_AsSsize_t`, Objects/longobject.c. -/
def mLongAsSsize (v : Int) : Py Int :=
  if v < ssizeMin ∨ v > ssizeMax then .error ssizeOverflowExc else .ok v

/-- The clinic `Py_ssize_t` converter, e.g. Objects/clinic/unicodeobject.c.h:115-126:
`_PyNumber_Index`, then `PyLong_AsSsize_t`. -/
def argSsizeObj (a : Arg) : Py Int := do
  let v ← numberIndex a
  mLongAsSsize v

/-- `PyNumber_AsSsize_t(item, NULL)`, Objects/abstract.c:1468-1513: out-of-range values
saturate. -/
def asSsizeClamp (a : Arg) : Py Int := do
  let v ← numberIndex a
  .ok (if v < ssizeMin then ssizeMin else if v > ssizeMax then ssizeMax else v)

/-- `PyNumber_AsSsize_t(item, PyExc_IndexError)`: out-of-range values raise `IndexError`. -/
def asSsizeIndexError (a : Arg) : Py Int := do
  let v ← numberIndex a
  if v < ssizeMin ∨ v > ssizeMax then
    .error (.indexError s!"cannot fit '{a.tpName}' into an index-sized integer")
  else .ok v

/-- `_PyEval_SliceIndexNotNone`, Python/ceval.c:2957-2979. A compact int is one digit,
`|v| < 2**30`. -/
def sliceIndexNotNone (a : Arg) : Py Int :=
  match a with
  | .int v => if -(2 ^ 30) < v ∧ v < 2 ^ 30 then .ok v else asSsizeClamp a
  | _ =>
    if a.hasIndex then asSsizeClamp a
    else .error (.typeError "slice indices must be integers or have an __index__ method")

/-- `_PyEval_SliceIndex`, Python/ceval.c:2948-2955: `None` keeps the default. -/
def sliceIndex (a : Arg) (dflt : Int) : Py Int :=
  match a with
  | .none => .ok dflt
  | _ => sliceIndexNotNone a

/-- What a Python slice index means for a sequence of length `n`: the documented reading
(negative counts from the end, then clipped to `[0, n]`), for any int. -/
def clipIndex (n : Nat) (x : Int) : Nat :=
  if x < 0 then (max 0 (x + n)).toNat else (min x n).toNat

end PyLean.UnicodeObj
