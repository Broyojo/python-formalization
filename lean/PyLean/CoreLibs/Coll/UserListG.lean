import PyLean.CoreLibs.Coll.UserList
import PyLean.CoreLibs.Coll.Counter

/-!
`collections.UserList` with the Python code its methods call, Lib/collections/__init__.py:1285-1411
(CPython 3.15.2): `list(other)` and `list.extend(other)` over fallible iterators, the exact-type test
of `__init__`, object identities for `__init__`, `copy` and `__copy__`, element comparisons that
raise or return any object, and the reflected method of a non-list operand.

Elements `α` are objects by identity (`DecidableEq α` is `is`). A `list` subclass is taken not to
override the comparison dunders.
-/

namespace PyLean.CoreLibs.Coll

open PyLean

variable {α : Type}

/-! ### Operands -/

/-- An operand: a `UserList` (its `data`), an exact `list` (its id and items), a `list` subclass
(its storage, and what its `__iter__` yields), or any other object (`iter()` and `next()`; a
non-iterable's `TypeError` as `.error`). -/
inductive LOpndP (α : Type) where
  | user (l : List α)
  | list (lid : Nat) (l : List α)
  | listSub (l : List α) (it : Py (FIt α))
  | other (ty : String) (it : Py (FIt α))

/-- `list(it)`: `list_extend` of an empty list, which fails as a whole (the list is discarded). -/
def listOfIt (it : Py (FIt α)) : Py (List α) := do
  let it ← it
  match it.stop with
  | none => pure it.xs
  | some e => .error e

/-- `list(other)`: an exact list (`list_extend`'s `PyList_CheckExact` fast path) by its items; a
`UserList` by `Sequence.__iter__`, which yields its items; anything else by iteration. -/
def listOfP : LOpndP α → Py (List α)
  | .user l | .list _ l => .ok l
  | .listSub _ it | .other _ it => listOfIt it

/-- `l.extend(other)`, `l += other` on a `list`: `list_extend`, Objects/listobject.c, appending item by
item from a non-exact-list operand, so an iterator that raises leaves the items read so far. -/
def listExtendP (l : List α) : LOpndP α → Out (List α)
  | .user u => (l ++ u, none)
  | .list _ m => (l ++ m, none)
  | .listSub _ it | .other _ it => forPy (fun l (x : α) => .ok (l ++ [x])) l it

/-- A `UserList` object: id, class, the id and items of its `data` list. -/
structure ULO (α : Type) where
  id : Nat
  cls : String
  dataId : Nat
  data : List α
  deriving Repr, DecidableEq

/-- `UserList.__init__`, :1288-1297: `self.data = []` (the new list `freshD`); then
`self.data[:] = initlist` for an exact `list` (:1292-1293), `self.data[:] = initlist.data[:]` for a
`UserList` (:1294-1295), else `self.data = list(initlist)` (:1296-1297), a list subclass through its
`__iter__`. The object is the new `fresh`. -/
def ulNewP (fresh freshD : Nat) (cls : String) : Option (LOpndP α) → Py (ULO α)
  | none => .ok ⟨fresh, cls, freshD, []⟩
  | some (.list _ l) => .ok ⟨fresh, cls, freshD, l⟩
  | some (.user l) => .ok ⟨fresh, cls, freshD, l⟩
  | some o => do
    let l ← listOfP o
    pure ⟨fresh, cls, freshD, l⟩

/-- `UserList.__copy__`, :1370-1375: a new instance `fresh`, `__dict__` copied from `self`, then
`data` replaced by `self.data[:]`, the new list `freshD`. -/
def ulCopyDunderO (fresh freshD : Nat) (u : ULO α) : ULO α := ⟨fresh, u.cls, freshD, u.data.take u.data.length⟩

/-- `UserList.copy`, :1392-1393: `self.__class__(self)`. -/
def ulCopyO (fresh freshD : Nat) (u : ULO α) : Py (ULO α) := ulNewP fresh freshD u.cls (some (.user u.data))

/-! ### `+`, `+=`, `extend` -/

/-- `UserList.__add__`, :1338-1343. A `list` subclass is concatenated by its storage. -/
def ulAddP (u : UL α) : LOpndP α → Py (UL α)
  | .user l | .list _ l | .listSub l _ => .ok ⟨u.cls, u.data ++ l⟩
  | o => do
    let l ← listOfP o
    pure ⟨u.cls, u.data ++ l⟩

/-- `UserList.__radd__`, :1345-1350. -/
def ulRaddP (u : UL α) : LOpndP α → Py (UL α)
  | .user l | .list _ l | .listSub l _ => .ok ⟨u.cls, l ++ u.data⟩
  | o => do
    let l ← listOfP o
    pure ⟨u.cls, l ++ u.data⟩

/-- `UserList.__iadd__`, :1352-1359: `self.data += other.data`, `self.data += other` for a `list`
(so `list_extend`), else `self.data += list(other)`, whose `list(other)` runs to the end before
anything is appended. -/
def ulIaddP (u : UL α) : LOpndP α → Out (UL α)
  | .user l => (⟨u.cls, u.data ++ l⟩, none)
  | o@(.list _ _) | o@(.listSub _ _) =>
    let r := listExtendP u.data o
    (⟨u.cls, r.1⟩, r.2)
  | o =>
    match listOfP o with
    | .ok l => (⟨u.cls, u.data ++ l⟩, none)
    | .error e => (u, some e)

/-- `UserList.extend`, :1407-1411: `self.data.extend(other.data)` or `self.data.extend(other)`. -/
def ulExtendP (u : UL α) : LOpndP α → Out (UL α)
  | .user l => (⟨u.cls, u.data ++ l⟩, none)
  | o =>
    let r := listExtendP u.data o
    (⟨u.cls, r.1⟩, r.2)

/-! ### Comparisons, `in`, `count` -/

/-- A comparison's result: a `bool`, or the object an element comparison (or the operand's
reflected method) returned. -/
inductive CRes (β : Type) where
  | bool (b : Bool)
  | obj (o : β)
  deriving Repr, DecidableEq

/-- The elements' comparisons: `PyObject_RichCompareBool(v, w, Py_EQ)` when `v is not w`, and
`PyObject_RichCompare(v, w, op)`, each Python code that may raise. -/
structure ElemOps (α β : Type) where
  eqB : α → α → Py Bool
  rich : CmpOp → α → α → Py β

/-- `PyObject_RichCompareBool(v, w, Py_EQ)`: identity first. -/
def eqId [DecidableEq α] {β : Type} (E : ElemOps α β) (v w : α) : Py Bool :=
  if v = w then .ok true else E.eqB v w

/-- The search for the first index whose items differ, Objects/listobject.c:3478-3495. -/
def firstDiff [DecidableEq α] {β : Type} (E : ElemOps α β) : List α → List α → Py (Option (α × α))
  | x :: xs, y :: ys => do
    let k ← eqId E x y
    if k then firstDiff E xs ys else pure (some (x, y))
  | _, _ => .ok none

/-- `size(v) op size(w)`. -/
def cmpLen (op : CmpOp) (a b : Nat) : Bool :=
  match op with
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)
  | .eq => decide (a = b)
  | .gt => decide (a > b)
  | .ge => decide (a ≥ b)

/-- `list_richcompare_impl`, Objects/listobject.c:3459-3519, between two lists. -/
def listRichP [DecidableEq α] {β : Type} (E : ElemOps α β) (op : CmpOp) (v w : List α) : Py (CRes β) :=
  if v.length ≠ w.length ∧ op = .eq then .ok (.bool false)          -- :3470-3476
  else do
    let d ← firstDiff E v w
    match d with
    | none => pure (.bool (cmpLen op v.length w.length))           -- :3497-3500
    | some (x, y) =>
      if op = .eq then pure (.bool false)                          -- :3503-3505
      else CRes.obj <$> E.rich op x y                              -- :3510-3518

/-- The operand of a comparison: a `UserList`, a `list`, or another object with its reflected
method for each operator (`__gt__` for `<`, `__eq__` for `==`, ...; `none` is `NotImplemented`). -/
inductive COpnd (α β : Type) where
  | user (l : List α)
  | list (l : List α)
  | other (ty : String) (refl : CmpOp → Option (Py β))

/-- `__lt__`, ..., `__ge__`, :1302-1318: `self.data op self.__cast(other)`, `__cast` unwrapping a
`UserList` only. A non-list operand gets `NotImplemented` from `list`, then its reflected method;
both `NotImplemented`: identity for `==` (false), `TypeError` otherwise. -/
def ulCmpP [DecidableEq α] {β : Type} (E : ElemOps α β) (op : CmpOp) (u : UL α) : COpnd α β → Py (CRes β)
  | .user l | .list l => listRichP E op u.data l
  | .other ty refl =>
    match refl op with
    | some r => CRes.obj <$> r
    | none =>
      if op = .eq then .ok (.bool false)
      else .error (.typeError s!"'{op.sym}' not supported between instances of 'list' and '{ty}'")

/-- `UserList.__contains__`, :1320-1321: `item in self.data`, `list_contains` (Objects/listobject.c:677-690)
comparing each element with `item`, stopping at the first true answer or exception. -/
def ulContainsP [DecidableEq α] {β : Type} (E : ElemOps α β) (u : UL α) (x : α) : Py Bool :=
  let rec go : List α → Py Bool
    | [] => .ok false
    | y :: ys => do
      let k ← eqId E y x
      if k then pure true else go ys
  go u.data

/-- `UserList.count`, :1395-1396: `list.count`, Objects/listobject.c:3387-3410. -/
def ulCountP [DecidableEq α] {β : Type} (E : ElemOps α β) (u : UL α) (x : α) : Py Nat :=
  let rec go : List α → Py Nat
    | [] => .ok 0
    | y :: ys => do
      let k ← eqId E y x
      let n ← go ys
      pure (if k then n + 1 else n)
  go u.data

end PyLean.CoreLibs.Coll
