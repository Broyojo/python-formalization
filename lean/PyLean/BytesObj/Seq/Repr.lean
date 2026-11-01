import PyLean.BytesObj.Seq.ListModel

/-!
`repr` of tuples and lists: `tuple_repr` (tupleobject.c:239-307), `list_repr`
(listobject.c:629-641) and `list_repr_impl` (:574-627), with `Py_ReprEnter` /
`Py_ReprLeave` (Objects/object.c:3003-3060).

Two layers:

* `listReprLoop` is the C loop over a list that `repr(item)` may change, with an
  abstract `elem` callback; `tupleReprLoop` is its tuple twin.
* `reprObj` runs both over a heap of objects that can contain cycles. The
  per-thread `Py_Repr` list is the `stack` argument, so `Py_ReprLeave` is simply
  returning. Recursion depth is limited in CPython by `Py_EnterRecursiveCall`
  (`RecursionError`) in `PyObject_Repr`, which is outside this model; the difftest
  stays below it.
-/

namespace PyLean.BytesObj.Seq

open PyLean

variable {α : Type}

/-- The element loop of `tuple_repr`, tupleobject.c:276-289. -/
def tupleReprLoop (elem : α → Py String) : Nat → List α → String → Py String
  | _, [], acc => .ok acc
  | i, x :: xs, acc =>
    let acc := if i > 0 then acc ++ ", " else acc
    match elem x with
    | .ok s => tupleReprLoop elem (i + 1) xs (acc ++ s)
    | .error e => .error e

/-- `tuple_repr` after `Py_ReprEnter` returned 0, tupleobject.c:257-301. -/
def tupleReprBody (elem : α → Py String) (items : List α) : Py String :=
  match tupleReprLoop elem 0 items "(" with
  | .ok acc => .ok (acc ++ (if items.length = 1 then ",)" else ")"))
  | .error e => .error e

/-- `tuple_repr(self)`, tupleobject.c:239-307. `entered` is `Py_ReprEnter` returning 1. -/
def tupleRepr (elem : α → Py String) (entered : Bool) (items : List α) : Py String :=
  if items.length = 0 then .ok "()"
  else if entered then .ok "(...)"
  else tupleReprBody elem items

/-- The element loop of `list_repr_impl`, listobject.c:596-613: the size and the
slot are reread on each pass because `repr(item)` may change the list. -/
def listReprLoop (elem : LObj α → α → Py String × LObj α) :
    Nat → Nat → String → LObj α → Py String × LObj α
  | 0, _, _, o => (.error .modelFuel, o)
  | fuel + 1, i, acc, o =>
    if h : i < o.items.length then
      let item := o.items[i]
      let acc := if i > 0 then acc ++ ", " else acc
      match elem o item with
      | (.ok s, o') => listReprLoop elem fuel (i + 1) (acc ++ s) o'
      | (.error e, o') => (.error e, o')
    else (.ok (acc ++ "]"), o)

/-- `list_repr(self)`, listobject.c:629-641, with `list_repr_impl`, :574-627. -/
def listRepr (elem : LObj α → α → Py String × LObj α) (fuel : Nat) (entered : Bool) (o : LObj α) :
    Py String × LObj α :=
  if o.items.length = 0 then (.ok "[]", o)
  else if entered then (.ok "[...]", o)
  else listReprLoop elem fuel 0 "[" o

/-! ## A heap of containers -/

/-- A reference to something `repr` can print. -/
inductive RObj where
  /-- An object with a fixed repr. -/
  | atom (s : String)
  /-- A list or tuple in the heap, by `id`. -/
  | ref (id : Nat)
  deriving Repr, DecidableEq, Inhabited

/-- One container of the heap: is it a list, and its items. -/
structure RCell where
  isList : Bool
  items : List RObj
  deriving Repr, DecidableEq, Inhabited

abbrev RHeap := List RCell

/-- `repr(obj)` with `stack` the current `Py_Repr` list. `fuel` bounds the depth. -/
def reprObj (h : RHeap) : Nat → List Nat → RObj → Py String
  | _, _, .atom s => .ok s
  | 0, _, .ref _ => .error .modelFuel
  | fuel + 1, stack, .ref id =>
    match h[id]? with
    | none => .error (cUB "dangling heap reference")
    | some cell =>
      let entered := stack.contains id
      let elem := reprObj h fuel (id :: stack)
      if cell.isList then
        (listRepr (fun o x => (elem x, o)) (cell.items.length + 1) entered { items := cell.items }).1
      else
        tupleRepr elem entered cell.items

end PyLean.BytesObj.Seq
