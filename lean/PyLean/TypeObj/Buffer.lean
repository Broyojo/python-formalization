import PyLean.TypeObj.Model

/-!
The buffer helpers of `Objects/abstract.c:450-804`, which are pure integer logic over a
`Py_buffer` description: contiguity tests, `PyBuffer_GetPointer`, the index odometers,
`PyBuffer_FillContiguousStrides`, `PyBuffer_FromContiguous`, `PyObject_CopyData`.

Addresses are offsets from `view->buf`. `suboffsets` other than NULL make
`PyBuffer_GetPointer` chase a pointer, which has no offset; such a view is `none` here.
-/

namespace PyLean.TypeObj

/-- The fields of a `Py_buffer` these functions read. -/
structure BufView where
  len : Int
  itemsize : Int
  ndim : Nat
  shape : List Int
  strides : Option (List Int) := none
  hasSuboffsets : Bool := false
  deriving Repr, Inhabited

/-- The stride test of `_IsCContiguous` and `_IsFortranContiguous`, given the dimensions
in the order the C loop visits them. -/
def stridesMatch : Int → List (Int × Int) → Bool
  | _, [] => true
  | sd, (dim, st) :: rest => if dim > 1 && st != sd then false else stridesMatch (sd * dim) rest

/-- `_IsCContiguous`, `Objects/abstract.c:491`. -/
def isCContiguous (v : BufView) : Bool :=
  if v.len == 0 then true else
  match v.strides with
  | none => true
  | some st => stridesMatch v.itemsize (v.shape.zip st).reverse

/-- `_IsFortranContiguous`, `Objects/abstract.c:451`. -/
def isFortranContiguous (v : BufView) : Bool :=
  if v.len == 0 then true else
  match v.strides with
  | none =>
    if v.ndim ≤ 1 then true
    else (v.shape.filter (· > 1)).length ≤ 1
  | some st => stridesMatch v.itemsize (v.shape.zip st)

/-- `PyBuffer_IsContiguous`, `Objects/abstract.c:518`. -/
def isContiguous (v : BufView) (order : Char) : Bool :=
  if v.hasSuboffsets then false
  else if order == 'C' then isCContiguous v
  else if order == 'F' then isFortranContiguous v
  else if order == 'A' then isCContiguous v || isFortranContiguous v
  else false

/-- `strides[i] * indices[i]` over `ndim` dimensions. Reading past the end of `indices` is
out of bounds in C; here it reads the value `oob`, which is what the memory after the
allocation happens to hold. -/
def getPointerFrom (oob : Int) : List Int → List Int → Int
  | [], _ => 0
  | s :: ss, [] => s * oob + getPointerFrom oob ss []
  | s :: ss, i :: is => s * i + getPointerFrom oob ss is

/-- `PyBuffer_GetPointer`, `Objects/abstract.c:534`, as an offset. -/
def getPointer (v : BufView) (indices : List Int) : Int :=
  getPointerFrom 0 ((v.strides.getD []).take v.ndim) indices

/-- One step of `_Py_add_one_to_index_F`, `Objects/abstract.c:550`: increment the first
digit that can, zeroing those that cannot. -/
def addOneF : List Int → List Int → List Int
  | [], _ | _, [] => []
  | i :: is, s :: ss => if i < s - 1 then (i + 1) :: is else 0 :: addOneF is ss

/-- `_Py_add_one_to_index_C`, `Objects/abstract.c:566`: the same from the last digit. -/
def addOneC (index shape : List Int) : List Int :=
  (addOneF index.reverse shape.reverse).reverse

/-- `PyBuffer_FillContiguousStrides`, `Objects/abstract.c:740`, for `'F'`: the strides in
order. -/
def fillStridesF : Int → List Int → List Int
  | _, [] => []
  | sd, d :: ds => sd :: fillStridesF (sd * d) ds

/-- `PyBuffer_FillContiguousStrides` for any other order: from the last dimension. -/
def fillStridesC (sd : Int) (shape : List Int) : List Int :=
  (fillStridesF sd shape.reverse).reverse

/-- `PyBuffer_FillContiguousStrides`, `Objects/abstract.c:740`. -/
def fillContiguousStrides (shape : List Int) (itemsize : Int) (fort : Char) : List Int :=
  if fort == 'F' then fillStridesF itemsize shape else fillStridesC itemsize shape

/-- What `PyObject_CopyData` does after its checks. -/
inductive CopyPlan where
  /-- `memcpy(dest, src, src.len)`. -/
  | memcpy (n : Int)
  /-- Element copies, each `(dest offset, src offset)`. -/
  | elements (pairs : List (Int × Int))
  deriving Repr, Inhabited

/-- The loop of `PyObject_CopyData`, `Objects/abstract.c:727-732`: the index is incremented
before each copy, so `(0, ..., 0)` comes last. `oob` as in `getPointerFrom`. -/
def copyLoop (dest src : BufView) : Nat → List Int → List (Int × Int)
  | 0, _ => []
  | n + 1, idx =>
    let idx' := addOneC idx src.shape
    (getPointerFrom 0 ((dest.strides.getD []).take dest.ndim) idx',
      getPointerFrom 0 ((src.strides.getD []).take src.ndim) idx') :: copyLoop dest src n idx'

/-- `PyObject_CopyData`, `Objects/abstract.c:669`, after `PyObject_GetBuffer`. -/
def copyDataPlan (dest src : BufView) : Except String CopyPlan :=
  if dest.len < src.len then .error "destination is too small to receive data from source"
  else if (isContiguous dest 'C' && isContiguous src 'C') ||
      (isContiguous dest 'F' && isContiguous src 'F') then .ok (.memcpy src.len)
  else
    let elements := src.shape.foldl (· * ·) 1
    .ok (.elements (copyLoop dest src elements.toNat (List.replicate src.ndim 0)))

end PyLean.TypeObj
