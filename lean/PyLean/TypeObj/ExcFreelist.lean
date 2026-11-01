import PyLean.TypeObj.ExcCore

/-!
The `MemoryError` freelist, `Objects/exceptions.c:4024-4150`.

The object model has no reference counts, so `dealloc` never runs in a scenario. The freelist
is modelled on its own here: a list of the `PyBaseExceptionObject` bodies that
`MemoryError_dealloc` keeps, and `get_memory_error` reuses, with the interpreter state as an
explicit argument. `BaseException_clear` is modelled here because this is where its effect
is visible: the object survives it.
-/

namespace PyLean.TypeObj

/-- `MEMERRORS_SAVE`, `Objects/exceptions.c:4024`. -/
def memerrorsSave : Nat := 16

/-- `BaseException_clear`, `Objects/exceptions.c:133`: `dict`, `args`, `notes`, `traceback`,
`cause` and `context`, and nothing else. `suppress_context` is not a reference. -/
def baseExceptionClear (d : ExcData) : ExcData :=
  { d with args := [], notes := none, traceback := .none, cause := none, context := none }

/-- `state->memerrors_freelist`, most recently freed first. -/
abbrev MemFreelist := List ExcData

/-- `MemoryError_dealloc`, `Objects/exceptions.c:4093`. `exact` is
`Py_IS_TYPE(self, PyExc_MemoryError)`. -/
def memoryErrorDealloc (exact : Bool) (d : ExcData) (s : MemFreelist) : MemFreelist :=
  let d := baseExceptionClear d
  if !exact then s
  else if s.length < memerrorsSave then d :: s
  else s

/-- The outcome of `get_memory_error`: a freelist entry, the shared last-resort error when
allocation is not allowed, or a fresh object. -/
inductive MemGot where
  | reused (d : ExcData)
  | lastResort
  | fresh (d : ExcData)

/-- `get_memory_error`, `Objects/exceptions.c:4035`. The freelist path ignores `args`. -/
def getMemoryError (allowAllocation : Bool) (args : List Val) (s : MemFreelist) :
    MemGot × MemFreelist :=
  match s with
  | d :: rest => (.reused { d with args := [] }, rest)
  | [] => if allowAllocation then (.fresh { args := args }, []) else (.lastResort, [])

/-- `_PyErr_NoMemory`, `Objects/exceptions.c:4077`, past the startup check. -/
def pyErrNoMemory (s : MemFreelist) : MemGot × MemFreelist := getMemoryError false [] s

/-- `preallocate_memerrors`, `Objects/exceptions.c:4122`: sixteen objects made and released. -/
def preallocateMemerrors : MemFreelist :=
  (List.range memerrorsSave).foldl (fun s _ => memoryErrorDealloc true { args := [] } s) []

/-- `free_preallocated_memerrors`, `Objects/exceptions.c:4143`. -/
def freePreallocatedMemerrors (_s : MemFreelist) : MemFreelist := []

end PyLean.TypeObj
