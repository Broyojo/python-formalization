import PyLean.BytesObj.Bytes.Heap

/-!
More of `Objects/bytearrayobject.c` (CPython 3.15.2) on the heap model of `Heap.lean`: one model per
delegating method, the clinic conversion of `fillchar` for `center`/`ljust`/`rjust`, and
`PyObject_IsTrue` of the `keepends` of `splitlines`.
-/

namespace PyLean.BytesObj.Bytes

open PyLean PyLean.StrSearch

/-! ## The delegating methods, :2098-2176 and :2203-2523

Each is `stringlib_<name>(self, NULL)` in a critical section (a no-op without free threading).
`stringlib/ctype.h` calls `_Py_bytes_<name>(STRINGLIB_STR(self), STRINGLIB_LEN(self))` for a
predicate; a map first makes `PyByteArray_FromStringAndSize(NULL, STRINGLIB_LEN(self))` and returns
`NULL` when that fails, then fills it with `_Py_bytes_<name>`. -/

/-- `bytearray_isalnum`, :2098-2106 (`_Py_bytes_isalnum`). -/
def baIsalnumE : E Bool := baPredE bytesIsAlnum
/-- `bytearray_isalpha`, :2108-2116 (`_Py_bytes_isalpha`). -/
def baIsalphaE : E Bool := baPredE bytesIsAlpha
/-- `bytearray_isascii`, :2118-2126 (`_Py_bytes_isascii`). -/
def baIsasciiE : E Bool := baPredE bytesIsAscii
/-- `bytearray_isdigit`, :2128-2136 (`_Py_bytes_isdigit`). -/
def baIsdigitE : E Bool := baPredE bytesIsDigit
/-- `bytearray_islower`, :2138-2146 (`_Py_bytes_islower`). -/
def baIslowerE : E Bool := baPredE bytesIsLower
/-- `bytearray_isspace`, :2148-2156 (`_Py_bytes_isspace`). -/
def baIsspaceE : E Bool := baPredE bytesIsSpace
/-- `bytearray_istitle`, :2158-2166 (`_Py_bytes_istitle`). -/
def baIstitleE : E Bool := baPredE bytesIsTitle
/-- `bytearray_isupper`, :2168-2176 (`_Py_bytes_isupper`). -/
def baIsupperE : E Bool := baPredE bytesIsUpper
/-- `bytearray_capitalize`, :2203-2211 (`_Py_bytes_capitalize`). -/
def baCapitalizeE : E Seq := baMapE bytesCapitalize
/-- `bytearray_swapcase`, :2485-2493 (`_Py_bytes_swapcase`). -/
def baSwapcaseE : E Seq := baMapE bytesSwapcase
/-- `bytearray_title`, :2495-2503 (`_Py_bytes_title`). -/
def baTitleE : E Seq := baMapE bytesTitle
/-- `bytearray_upper`, :2505-2513 (`_Py_bytes_upper`). -/
def baUpperE : E Seq := baMapE bytesUpper
/-- `bytearray_lower`, :2515-2523 (`_Py_bytes_lower`). -/
def baLowerE : E Seq := baMapE bytesLower

/-! ## `center`, `ljust`, `rjust` with their `fillchar` -/

def PadKind.fname : PadKind → String
  | .center => "center"
  | .ljust => "ljust"
  | .rjust => "rjust"
  | .zfill => "zfill"

/-- The `char` converter of `fillchar`, stringlib/clinic/transmogrify.h.h:116-139 (`ljust`), :184-207
(`rjust`) and :252-275 (`center`). It runs after `width` was converted, so it sees `self` as the
`__index__` of `width` left it. `PyBytes_Check` holds for a subclass of `bytes`, whose
`PyBytes_GET_SIZE` is the stored size, not its `__len__`. Anything else is `_PyArg_BadArgument`,
Python/getargs.c:663-670. -/
def fillCharE (fname : String) : Option Arg → E Nat
  | none => pure 32
  | some a =>
    let ofBytes (kind : String) (s : Seq) : E Nat :=
      if s.length ≠ 1 then
        throw (.typeError s!"{fname}(): argument 2 must be a byte string of length 1, not a {kind} object of length {s.length}")
      else pure (s.headD 0)
    match a with
    | .obj (.bytes s) => ofBytes "bytes" s
    | .slen _ _ s => ofBytes "bytes" s
    | .obj (.bytearray s) => ofBytes "bytearray" s
    | .me => do
      let s ← curSeq
      ofBytes "bytearray" s
    | .obj .none => throw (.typeError s!"{fname}() argument 2 must be a byte string of length 1, not None")
    | a => throw (.typeError s!"{fname}() argument 2 must be a byte string of length 1, not {a.typeName}")

/-- `bytearray_center`, `bytearray_ljust` and `bytearray_rjust` (:2213-2221, :2641-2659): the clinic
converts `width` (`_PyNumber_Index`, `PyLong_AsSsize_t`), then `fillchar`, then
`stringlib_<name>_impl` (stringlib/transmogrify.h) reads `self`. -/
def baJustE (k : PadKind) (width : Arg) (fill : Option Arg) : E Seq := do
  let w ← clinicSsizeE width
  let f ← fillCharE k.fname fill
  let s ← curSeq
  E.lift (padOp k s w f)

/-! ## `splitlines(keepends)` -/

/-- The `keepends` argument as `PyObject_IsTrue` sees it: a C object of truth value `b` (no Python
code runs), a class whose `__bool__` runs `acts` and returns or raises `res` (a non-`bool` result is
the `TypeError` of `slot_nb_bool`, carried by `res`), or `self`, which has no `nb_bool` and is true
when `bytearray_length` is not 0. -/
inductive TArg where
  | obj (b : Bool)
  | cls (acts : List Act) (res : Py Bool)
  | me

/-- `PyObject_IsTrue`, Objects/object.c. -/
def isTrueE : TArg → E Bool
  | .obj b => pure b
  | .cls acts res => runCb acts res
  | .me => do
    let n ← curSize
    return decide (n ≠ 0)

/-- `bytearray.splitlines(keepends)`: the clinic (clinic/bytearrayobject.c.h:1657-1674) runs
`PyObject_IsTrue(keepends)` and returns on `-1`, then `bytearray_splitlines_impl`, :2674-2682,
passes `PyByteArray_AS_STRING(self)` and `PyByteArray_GET_SIZE(self)` as they are then to
`stringlib_splitlines`. -/
def baSplitlinesTE (keepends : Option TArg) : E (List Seq) := do
  let k ← match keepends with
    | none => pure false
    | some a => isTrueE a
  let s ← curSeq
  return bytesSplitlines s k

/-! ## Buffer export and release, :69-106 -/

/-- `bytearray_getbuffer_lock_held`, :69-86, and `bytearray_getbuffer`, :88-96: a `NULL` view is the
`BufferError` of :74-78; `PyBuffer_FillInfo` (Objects/abstract.c:774-810, `readonly` 0) refuses
`PyBUF_READ` (0x100) and `PyBUF_WRITE` (0x200) with `PyErr_BadInternalCall` (:784-786) and accepts
every other flag value; then the view shows `ob_start` and `Py_SIZE`, writable, and `ob_exports`
goes up. -/
def baGetBufferC (b : BA) (viewNull : Bool) (flags : Int) : Py ((Seq × Bool) × BA) :=
  if viewNull then .error (bufferError "bytearray_getbuffer: view==NULL argument is obsolete")
  else if flags ≠ 0 ∧ (flags = 0x100 ∨ flags = 0x200) then
    .error (systemError "Objects/abstract.c:785: bad argument to internal function")
  else .ok ((b.seq, false), baGetBuffer b)

/-! ## `__sizeof__` for a type of any basic size -/

/-- `bytearray_sizeof_impl`, :2813-2823: `_PyObject_SIZE(Py_TYPE(self))` is the type's basic size
(64 for `bytearray` on LP64, and for a subclass without `__slots__`), plus the `bytes` object when
there is storage. -/
def baSizeofT (basic : Int) (self : BA) : Int :=
  if self.alloc > 0 then basic + bytesObjectSize + self.alloc else basic

/-! ## `resize(size)` with its clinic conversion -/

/-- `bytearray.resize(size)`: the clinic converts `size` with `_PyNumber_Index` and
`PyLong_AsSsize_t` (clinic/bytearrayobject.c.h:611-634), then `bytearray_resize_impl`, :1588-1602. -/
def baResizeMethodE (size : Arg) : E Unit := do
  let n ← clinicSsizeE size
  liftBA fun b => baResizeMethod b n

/-! ## `reverse()`, the swap loop -/

/-- `*head = *tail; *tail = swap` at positions `a` and `b`. -/
def swapAt (d : List Int) (a b : Nat) : List Int := (d.set a (d.getD b 0)).set b (d.getD a 0)

/-- The loop of `bytearray_reverse_impl`, :2033-2050, after `k` rounds: round `i` swaps `head = i`
and `tail = n - 1 - i`. -/
def reverseLoop (n : Nat) (d : List Int) : Nat → List Int
  | 0 => d
  | k + 1 => swapAt (reverseLoop n d k) k (n - 1 - k)

/-- `bytearray_reverse_impl`: `n / 2` rounds of the swap loop. -/
def baReverseLoop (self : BA) : BA :=
  { self with data := reverseLoop self.data.length self.data (self.data.length / 2) }

/-! ## The iterator: `bytearray_iter` and `__setstate__` of any object -/

/-- `bytearray_iter`, :3179-3195: `PyErr_BadInternalCall` for an object that is not a bytearray (which
`tp_iter` never passes), else a new iterator at index 0. -/
def baIterOf (isBytearray : Bool) : Py BAIter :=
  if !isBytearray then .error (systemError "Objects/bytearrayobject.c:3185: bad argument to internal function")
  else .ok { index := 0 }

/-- `bytearrayiter_setstate`, :3110-3132, on any object: `PyLong_AsSsize_t` takes only an `int` (a
`bool` included) and does not call `__index__` (Objects/longobject.c:708-720). -/
def baIterSetstateObj (seq : BA) (it : BAIter) (state : Obj) : Py BAIter :=
  match state.longValue? with
  | none => .error (.typeError "an integer is required")
  | some v => baIterSetstate seq it v

/-- What `next` yields from `it` on an object that does not change, with fuel. -/
def baDrain (seq : BA) : Nat → BAIter → List Int
  | 0, _ => []
  | k + 1, it =>
    match baIterNext seq it with
    | (some v, it') => v :: baDrain seq k it'
    | (none, _) => []

end PyLean.BytesObj.Bytes
