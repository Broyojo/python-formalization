import PyLean.Sequences.ListModel

/-!
`xml.etree.ElementTree.Element` as a sequence of children, CPython 3.15.2: the C accelerator
(`Modules/_elementtree.c`, `element_subscr` .. `element_ass_subscr`) and the pure-Python twin
(`Lib/xml/etree/ElementTree.py:208-220`), which stores its children in a `list` and so runs
`list_subscript` / `list_ass_subscript` (modelled in `Sequences/ListModel.lean`).

Children are values of an abstract type `α`, compared by identity. An Element whose `extra` is
NULL is the empty list: every branch on `self->extra == NULL` in these functions does what the
same branch does for length 0 (`create_extra` only fails on allocation, which is not modelled,
nor is `element_resize` running out of memory).

The assigned value of a slice store is an `Arg`: a list or tuple, a one-shot iterator, or a
non-iterable. An iterator is fallible and re-entrant: its first `__next__` runs `eff` on the
element's children (Python code may mutate the element it is being assigned into), it then
yields `xs`, and it ends with `StopIteration` or raises `stop`. The model runs the whole effect
at the first `__next__`; effects spread over later items are out of scope.
-/

namespace PyLean.TextLibs.Etree

open PyLean PyLean.Sequences
open PyLean.RangeSlice (Slice sliceUnpack adjustIndices toU listSlicePositions)

variable {α : Type} [Inhabited α]

/-- The value assigned to a slice. -/
inductive Arg (α : Type) where
  /-- A list or tuple: `PySequence_Fast` hands back its items, and iterating it again gives
  the same items. -/
  | seq (xs : List α)
  /-- A one-shot iterator such as a generator; exhausted once it has ended or raised. -/
  | iter (xs : List α) (stop : Option PyExc) (eff : List α → List α)
  /-- An object that is not iterable; `tyName` is `type(value).__name__`. -/
  | notIter (tyName : String)

/-- How each twin recognises an Element: C's `Element_Check` (an instance of the C type) or
Python's `isinstance(e, _Element_Py)`, with the type's `tp_name` and `__name__` for messages.
Each twin checks for its own class, so comparing the twins uses one `isElem`. -/
structure Ty (α : Type) where
  isElem : α → Bool
  tpName : α → String
  pyName : α → String

/-- The difftest's and the refutations' children: numbers below 1000 are Elements, the rest ints. -/
def caseTy : Ty Nat := { isElem := (· < 1000), tpName := fun _ => "int", pyName := fun _ => "int" }

/-- The children after a store or delete, and its outcome. -/
abbrev Out (α : Type) := List α × Py Unit

/-- `raise_type_error`, Modules/_elementtree.c:530-535: `"%.200s"` of `tp_name`. -/
def typeErrC (T : Ty α) (x : α) : PyExc :=
  .typeError s!"expected an Element, not \"{String.ofList ((T.tpName x).toList.take 200)}\""

/-- `_assert_is_element`, Lib/xml/etree/ElementTree.py:248-252. -/
def typeErrPy (T : Ty α) (x : α) : PyExc :=
  .typeError s!"expected an Element, not {T.pyName x}"

/-- The first item that is not an Element, in order. -/
def firstBad (T : Ty α) (xs : List α) : Option α := xs.find? (fun x => !T.isElem x)

/-! ## The C accelerator -/

/-- `element_getitem`, Modules/_elementtree.c:1520-1533, reached from the index branch of
`element_subscr`, :1815-1824 (`PyNumber_AsSsize_t(item, PyExc_IndexError)`, then one wrap
of a negative index). -/
def getItemC (kids : List α) (i : Int) : Py α := do
  let i ← subIndex i
  let i := if i < 0 then i + kids.length else i
  if i < 0 ∨ i ≥ kids.length then throw (.indexError "child index out of range")
  return ix kids i

/-- The slice branch of `element_subscr`, :1825-1858: `PySlice_Unpack`, then
`PySlice_AdjustIndices`, then `slicelen` items from a `size_t` cursor advanced by `step`. -/
def getSliceC (kids : List α) (s : Slice) : Py (List α) := do
  let (start, stop, step) ← sliceUnpack s
  let (start, _, slicelen) := adjustIndices kids.length start stop step
  if slicelen ≤ 0 then return []
  return (List.range slicelen.toNat).map fun (i : Nat) => ix kids (toU (toU start + (i : Int) * toU step))

/-- `element_setitem`, :1776-1808: bounds first, then the type of the new child; `none`
deletes (`del e[i]`). -/
def setItemC (T : Ty α) (kids : List α) (index : Int) (v : Option α) : Out α :=
  if index < 0 ∨ index ≥ kids.length then (kids, .error (.indexError "child assignment index out of range"))
  else match v with
    | some x => if T.isElem x then (kids.set index.toNat x, .ok ()) else (kids, .error (typeErrC T x))
    | none => (kids.eraseIdx index.toNat, .ok ())

/-- The index branch of `element_ass_subscr`, :1871-1880. -/
def assItemC (T : Ty α) (kids : List α) (i : Int) (v : Option α) : Out α :=
  match subIndex i with
  | .error e => (kids, .error e)
  | .ok i => setItemC T kids (if i < 0 then i + kids.length else i) v

/-- `PySequence_Fast(value, "assignment expects an iterable")`, :1964: the children after the
iteration ran, and the items or the exception. -/
def fastC (kids : List α) : Arg α → List α × Py (List α)
  | .seq xs => (kids, .ok xs)
  | .iter xs stop eff => (eff kids, match stop with | none => .ok xs | some e => .error e)
  | .notIter _ => (kids, .error (.typeError "assignment expects an iterable"))

/-- `for (i = stop; i < length; i++) children[i + newlen - slicelen] = children[i];`
(:2024-2025), with `d = newlen - slicelen < 0`. -/
def shiftDown (mem : List α) (stop length d : Int) : List α :=
  (List.range (length - stop).toNat).foldl
    (fun m (k : Nat) => m.set (stop + k + d).toNat (ix m (stop + k))) mem

/-- `for (i = length-1; i >= stop; i--) children[i + newlen - slicelen] = children[i];`
(:2028-2029), with `d = newlen - slicelen > 0`. -/
def shiftUp (mem : List α) (stop length d : Int) : List α :=
  (List.range (length - stop).toNat).foldl
    (fun m (k : Nat) => m.set (length - 1 - k + d).toNat (ix m (length - 1 - k))) mem

/-- `e[s] = value`: the store half of the slice branch of `element_ass_subscr`, :1881-1893 and
:1963-2046. Unlike `list_ass_subscript` it never clips `stop` to `start`: `PySlice_AdjustIndices`
can leave `stop < start` for `step == 1`, and the shift loops then start at `stop` while the
store loop writes from `start`. `element_resize` (:1991) only grows the buffer (fresh slots are
`default` here), so a `TypeError` from the item check leaves the children as they were. The
replace loop is the one `list_ass_subscript` uses, `storeLoop` (listobject.c:3893-3898). -/
def setSliceC (T : Ty α) (kids : List α) (s : Slice) (v : Arg α) : Out α :=
  match sliceUnpack s with
  | .error e => (kids, .error e)
  | .ok (start, stop, step) =>
    let (kids, seqR) := fastC kids v
    match seqR with
    | .error e => (kids, .error e)
    | .ok seq =>
      let newlen : Int := seq.length
      let length : Int := kids.length
      let (start, stop, slicelen) := adjustIndices length start stop step
      if step ≠ 1 ∧ newlen ≠ slicelen then
        (kids, .error (.valueError
          s!"attempt to assign sequence of size {seq.length} to extended slice of size {slicelen}"))
      else
        let mem := if newlen > slicelen then kids ++ List.replicate (newlen - slicelen).toNat default
          else kids
        match firstBad T seq with
        | some x => (kids, .error (typeErrC T x))
        | none =>
          let d := newlen - slicelen
          let mem := if newlen < slicelen then shiftDown mem stop length d
            else if newlen > slicelen then shiftUp mem stop length d else mem
          let mem := storeLoop mem start step seq
          (mem.take (length + d).toNat, .ok ())

/-- `del e[s]`: :1895-1961. After `PySlice_AdjustIndices` the deletion is, statement for
statement, the extended-slice deletion of `list_ass_subscript` (`delExtended`,
listobject.c:3789-3829): the same reversal of a negative step (:1908-1912), the same compaction
loop and `num_moved` clip (:1930-1945), the same tail move (:1948-1954) and shrink (:1956). C
runs it for `step == 1` too, where `list` takes `list_ass_slice`. -/
def delSliceC (kids : List α) (s : Slice) : Out α :=
  match sliceUnpack s with
  | .error e => (kids, .error e)
  | .ok (start, stop, step) =>
    let (start, stop, slicelen) := adjustIndices kids.length start stop step
    if slicelen ≤ 0 then (kids, .ok ())
    else match delExtended kids start stop step slicelen with
      | .ok m => (m, .ok ())
      | .error e => (kids, .error e)

/-- The final branch of `element_subscr` and `element_ass_subscr` (:1859-1863, :2048-2052): a
key that is neither an index nor a slice. -/
def badKeyC : PyExc := .typeError "element indices must be integers"

/-! ## The pure-Python twin -/

/-- `Element.__getitem__`, ElementTree.py:208-209, for an int: `self._children[index]`. -/
def getItemPy (kids : List α) (i : Int) : Py α := listGetItem kids i

/-- `Element.__getitem__` for a slice: `list_subscript`'s slice branch. -/
def getSlicePy (kids : List α) (s : Slice) : Py (List α) := do
  let ps ← listSlicePositions kids.length s
  return ps.map (ix kids)

def ofList (kids : List α) : Py (List α) → Out α
  | .ok m => (m, .ok ())
  | .error e => (kids, .error e)

/-- `Element.__setitem__` for an int, ElementTree.py:211-217: the type check first, then
`self._children[index] = element`. -/
def setItemPy (T : Ty α) (kids : List α) (i : Int) (x : α) : Out α :=
  if !T.isElem x then (kids, .error (typeErrPy T x))
  else ofList kids (listAssItem kids i (some x))

/-- `Element.__setitem__` for a slice, ElementTree.py:212-217: `for elt in element:
self._assert_is_element(elt)` iterates the value once, then `self._children[index] = element`
hands the same object to `list_ass_subscript`, which iterates it again. A one-shot iterator is
exhausted by then and contributes no items. -/
def setSlicePy (T : Ty α) (kids : List α) (s : Slice) : Arg α → Out α
  | .notIter n => (kids, .error (.typeError s!"'{n}' object is not iterable"))
  | .seq xs =>
    match firstBad T xs with
    | some x => (kids, .error (typeErrPy T x))
    | none => ofList kids (listAssSubscript kids s (some xs))
  | .iter xs stop eff =>
    let kids := eff kids
    match firstBad T xs with
    | some x => (kids, .error (typeErrPy T x))
    | none =>
      match stop with
      | some e => (kids, .error e)
      | none => ofList kids (listAssSubscript kids s (some []))

/-- `Element.__delitem__`, ElementTree.py:219-220, for an int. -/
def delItemPy (kids : List α) (i : Int) : Out α := ofList kids (listAssItem kids i none)

/-- `Element.__delitem__` for a slice. -/
def delSlicePy (kids : List α) (s : Slice) : Out α := ofList kids (listAssSubscript kids s none)

end PyLean.TextLibs.Etree
