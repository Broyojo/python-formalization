import PyLean.BytesObj.Seq.Repr

/-!
`tuple(iterable)`, `tuple.__new__`, `tuple.__getnewargs__`, the dispatch of `t[item]` and of the rich
comparison, and `repr` with a failing `Py_ReprEnter` (Objects/tupleobject.c, CPython 3.15.2).

`tuple(iterable)` runs `PySequence_Tuple` (Objects/abstract.c:2004-2078), which iterates any object
that is not an exact tuple or list. The iterator is user code: `TIter.next k` is what the `k`-th call
of `PyIter_Next` gives, `none` when it is exhausted (`NULL` with no exception, or a `StopIteration`,
which `iternext` clears, abstract.c:2873-2893) and `.error e` when it raises anything else. This is
the most general iterator `PySequence_Tuple` can see: the tuple under construction is not reachable
from Python until it is returned, so nothing the iterator does to other objects shows in the result
(the GC's `gc.get_objects` is the one way to reach it, outside the model).
-/

namespace PyLean.BytesObj.Seq

open PyLean
open PyLean.RangeSlice (Slice)

variable {α ρ : Type}

/-! ## `PySequence_Tuple` -/

/-- An iterator as `PySequence_Tuple` drives it. `hint` is its `__length_hint__`, which
`PySequence_Tuple` does not call (abstract.c:2004-2078 never consults `PyObject_LengthHint`). -/
structure TIter (α : Type) where
  next : Nat → Option (Py α)
  hint : Py Int := .ok 0

/-- The argument of `tuple(x)` by what `PySequence_Tuple` tests: an exact tuple (`PyTuple_CheckExact`,
:2014) or an exact list (`PyList_CheckExact`, :2021); anything else goes through `PyObject_GetIter`
(:2025-2027), whose result is `.iter`: an iterator, or the exception of a raising `__iter__`, of
`__iter__` returning a non-iterator (abstract.c:2824-2831), and so on. A subclass instance of tuple or
list is `.iter` with its class's iterator. `.notIterable` is an object with neither `tp_iter` nor the
sequence protocol, whose type is named `tpName` (abstract.c:2818-2822). -/
inductive TupArg (α : Type) where
  | exactTuple (t : Tup α)
  | exactList (items : List α)
  | iter (it : Py (TIter α))
  | notIterable (tpName : String)

/-- The items of an `exactTuple` argument, which `tuple(t)` hands back as `.arg 0`. -/
def TupArg.selfItems : Option (TupArg α) → List α
  | some (.exactTuple t) => t.items
  | _ => []

/-- The list phase of `PySequence_Tuple`, abstract.c:2051-2070: each further item is appended with
`_PyList_AppendTakeRef` (:2061), an exception from the iterator or the append is the result
(:2054-2058, :2061-2065), and at the end `_PyList_AsTupleAndClear(list)` (:2068). `fuel` bounds the
number of `PyIter_Next` calls. -/
def seqTupleList (next : Nat → Option (Py α)) : Nat → Nat → LObj α → Py (TRes α)
  | 0, _, _ => .error .modelFuel
  | fuel + 1, k, o =>
    match next k with
    | none =>
      match listAsTupleAndClear o with
      | .ok (r, _) => .ok r
      | .error e => .error e
    | some (.error e) => .error e
    | some (.ok x) =>
      match listAppend o x with
      | .ok o' => seqTupleList next fuel (k + 1) o'
      | .error e => .error e

/-- The buffer phase of `PySequence_Tuple`, abstract.c:2029-2050: up to 8 items go into a stack
buffer (:2031-2041); an iterator that stops first gives `_PyTuple_FromArraySteal(buffer, n)` (:2038),
one that raises gives its exception (:2034-2035, `goto fail`). After 8 items the buffer moves into
`PyList_New(16)` with size 8 (:2042-2050), and the list phase takes over. `n` counts the buffer slots
left. -/
def seqTupleBuf (next : Nat → Option (Py α)) (fuel : Nat) : Nat → Nat → List α → Py (TRes α)
  | 0, k, buf => seqTupleList next fuel k { items := buf, allocated := 16, hasItems := true }
  | n + 1, k, buf =>
    match next k with
    | none => tupleFromArraySteal buf
    | some (.error e) => .error e
    | some (.ok x) => seqTupleBuf next fuel n (k + 1) (buf ++ [x])

/-- `PySequence_Tuple(v)`, Objects/abstract.c:2004-2078: an exact tuple is returned (`Py_NewRef`,
:2014-2020), an exact list goes through `PyList_AsTuple` (:2021-2022, `tupleFromArray`), anything else
is iterated. -/
def pySequenceTuple (mayTrack : α → Bool) (fuel : Nat) : TupArg α → Py (TRes α)
  | .exactTuple _ => .ok (.arg 0)
  | .exactList l => tupleFromArray mayTrack l
  | .notIterable name => .error (.typeError s!"'{trunc200 name}' object is not iterable")
  | .iter (.error e) => .error e
  | .iter (.ok src) => seqTupleBuf src.next fuel 8 0 []

/-! ## `tuple.__new__` -/

/-- `tuple_new_impl(&PyTuple_Type, iterable)`, tupleobject.c:813-819: the singleton without an
argument (:814-816), `PySequence_Tuple` with one (:818). -/
def tupleNewExact (mayTrack : α → Bool) (fuel : Nat) (iterable : Option (TupArg α)) : Py (TRes α) :=
  match iterable with
  | none => .ok .empty
  | some a => pySequenceTuple mayTrack fuel a

/-- `tuple_subtype_new(type, iterable)`, tupleobject.c:843-876: `tuple(iterable)` first (:853-855),
whose failure is the result; then `type->tp_alloc(type, n)`, a fresh instance of the subclass even
for `n = 0` ("This may allocate an empty tuple that is not the global one", :857), holding the items
(:863-866), with the hash cache reset (:869) and tracked (:871-874). `tp_alloc` failing is out of
memory, outside the model. -/
def tupleSubtypeNew (mayTrack : α → Bool) (fuel : Nat) (iterable : Option (TupArg α)) : Py (TRes α) :=
  match tupleNewExact mayTrack fuel iterable with
  | .error e => .error e
  | .ok tmp =>
    .ok (.fresh { items := tmp.items (TupArg.selfItems iterable) [], exact := false, tracked := true,
                  hash := -1 })

/-- `tuple_new_impl(type, iterable)`, tupleobject.c:807-820: a type other than `tuple` is a subclass,
which goes to `tuple_subtype_new` (:811-812). -/
def tupleNewImpl (mayTrack : α → Bool) (fuel : Nat) (isTuple : Bool) (iterable : Option (TupArg α)) :
    Py (TRes α) :=
  if !isTuple then tupleSubtypeNew mayTrack fuel iterable
  else tupleNewExact mayTrack fuel iterable

/-- `tuple(*args, **kwargs)`: `tuple_vectorcall(type, args, nargsf, kwnames)`, tupleobject.c:822-841.
Keyword names are refused first (`_PyArg_NoKwnames`, :826, Python/getargs.c:2979-2993), then more than
one argument (`_PyArg_CheckPositional("tuple", nargs, 0, 1)`, :831, Python/getargs.c:2861-2866), then
one argument is `tuple_new_impl` and none the singleton. `type` is always `tuple` itself: a subclass
does not inherit the type's own `tp_vectorcall` (Objects/typeobject.c:9000-9003 copies only
`tp_vectorcall_offset`), so it is called through `tp_new`. -/
def tupleVectorcall (mayTrack : α → Bool) (fuel : Nat) (args : List (TupArg α)) (nkw : Nat) :
    Py (TRes α) :=
  if nkw ≠ 0 then .error (.typeError "tuple() takes no keyword arguments")
  else if args.length > 1 then
    .error (.typeError s!"tuple expected at most 1 argument, got {args.length}")
  else
    match args with
    | a :: _ => tupleNewImpl mayTrack fuel true (some a)
    | [] => .ok .empty

/-- `t.__getnewargs__()`, `tuple___getnewargs___impl`, tupleobject.c:960-965:
`Py_BuildValue("(N)", tuple_slice(self, 0, Py_SIZE(self)))`, a fresh 1-tuple (`PyTuple_New(1)`, so
tracked) whose item is the slice: `self` for an exact tuple, a new exact tuple of the items for a
subclass instance. A failed slice is `NULL` for `N`, and `Py_BuildValue` returns `NULL` with its
exception. -/
def tupleGetnewargs (mayTrack : α → Bool) (a : Tup α) : Py (Tup (TRes α)) :=
  match tupleSlice mayTrack a 0 a.items.length with
  | .error e => .error e
  | .ok r => .ok { items := [r], tracked := true }

/-! ## `t[item]` -/

/-- `t[item]` by what `tuple_subscript` tests: `_PyIndex_Check(item)` (tupleobject.c:904) holds for an
`int` (any `PyLong_Check` object, whose `__index__` is not called) and for an object with `nb_index`,
whose `__index__` is user code that may raise (`.index tpName r`, `r` its result; the tuple cannot
change); `PySlice_Check(item)` (:911) for a slice, here with int/None parts; anything else is
`.other`. `tpName` is `Py_TYPE(item)->tp_name`. -/
inductive TSubItem where
  | int (n : Int) (tpName : String := "int")
  | index (tpName : String) (r : Py Int)
  | slice (s : Slice)
  | other (tpName : String)

/-- `TypeError("tuple indices must be integers or slices, not %.200s")`, tupleobject.c:948-952. -/
def tupleIndicesError (tpName : String) : PyExc :=
  .typeError s!"tuple indices must be integers or slices, not {trunc200 tpName}"

/-- `tuple_subscript(op, item)`, tupleobject.c:900-954. The index arm is
`PyNumber_AsSsize_t(item, PyExc_IndexError)` (:905-907), which runs `__index__` and refuses a value
outside `Py_ssize_t` with `IndexError` naming the item's type, then the size added to a negative index
(:908-909) and `tuple_item` (:910). The slice arm is `tupleGetSlice` (:911-946). The result is the
item (`.inl`) or the tuple (`.inr`). -/
def tupleSubscript (a : Tup α) : TSubItem → Py (α ⊕ TRes α)
  | .slice s =>
    match tupleGetSlice a s with
    | .ok r => .ok (.inr r)
    | .error e => .error e
  | .other tp => .error (tupleIndicesError tp)
  | .int n tp => idxArm tp (.ok n)
  | .index tp r => idxArm tp r
where
  idxArm (tp : String) (r : Py Int) : Py (α ⊕ TRes α) :=
    match r with
    | .error e => .error e
    | .ok n =>
      match asSsizeIndexError tp n with
      | .error e => .error e
      | .ok i =>
        let i := if i < 0 then i + a.items.length else i
        match tupleItem a.items i with
        | .ok v => .ok (.inl v)
        | .error e => .error e

/-! ## Rich comparison -/

/-- `tuple_richcompare(v, w, op)` with the operands' types, tupleobject.c:737-788: `none` is an
object that is not a tuple (`PyTuple_Check`, so a subclass instance is `some`), and
`Py_RETURN_NOTIMPLEMENTED` (:744-745) is the outer `none`. -/
def tupleRichcompareAny (E : ElemOps α ρ) (op : CmpOp) (v w : Option (List α)) : Option (Py ρ) :=
  match v, w with
  | some v, some w => some (tupleRichcompare E op v w)
  | _, _ => none

/-! ## `repr` -/

/-- `tuple_repr(self)`, tupleobject.c:285-353, with `Py_ReprEnter` (Objects/object.c) as `enter`: `1`
(`.ok true`) when the tuple is already being printed, `0` (`.ok false`) otherwise, and `-1` (`.error`)
when it fails, which returns `NULL` (:298-301). The empty tuple is `"()"` before it is asked (:290-292).
The element loop and the closing are `tupleReprBody` (:303-347); an element's `__repr__` that raises
or returns a non-string (`PyUnicodeWriter_WriteRepr`, :332-334) is the result, through `error:`
(:349-352). The `PyUnicodeWriter` calls fail only out of memory, outside the model. -/
def tupleReprE (elem : α → Py String) (enter : Py Bool) (items : List α) : Py String :=
  if items.length = 0 then .ok "()"
  else
    match enter with
    | .error e => .error e
    | .ok true => .ok "(...)"
    | .ok false => tupleReprBody elem items

end PyLean.BytesObj.Seq
