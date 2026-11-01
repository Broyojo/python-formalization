import PyLean.Accel.Select
import PyLean.Sequences.ListModel

/-!
`collections.UserList`, Lib/collections/__init__.py:1285-1411 (CPython 3.14.7).

`UserList` is a wrapper: what it adds to `list` is operand dispatch, re-wrapping in
`self.__class__`, and `__cast`. The wrapped `list` methods are the fields of `ListOps`,
over an abstract element type. `intOps` instantiates them with the mirrors of
Objects/listobject.c in `PyLean.Sequences`, for the difftest and the properties that need the
real `list`.
-/

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.RangeSlice (Slice listSlicePositions)

/-- A rich-comparison operator. -/
inductive CmpOp where
  | lt | le | eq | gt | ge
  deriving Repr, DecidableEq

/-- The operator's symbol, as in the `TypeError`. -/
def CmpOp.sym : CmpOp → String
  | .lt => "<" | .le => "<=" | .eq => "==" | .gt => ">" | .ge => ">="

/-- The `list` methods `UserList` delegates to. -/
structure ListOps (α : Type) where
  getItem : List α → Int → Py α
  getSlice : List α → Slice → Py (List α)
  setItem : List α → Int → α → Py (List α)
  delItem : List α → Int → Py (List α)
  assSlice : List α → Slice → Option (List α) → Py (List α)
  insert : List α → Int → α → Py (List α)
  pop : List α → Option Int → Py (α × List α)
  remove : List α → α → Py (List α)
  index : List α → α → Option Int → Option Int → Py Int
  count : List α → α → Int
  contains : List α → α → Bool
  repeatL : List α → Int → Py (List α)
  irepeat : List α → Int → Py (List α)
  reverse : List α → List α
  /-- `l.sort(reverse=r)`. -/
  sort : List α → Bool → List α
  /-- `list_richcompare` between two lists. -/
  rich : CmpOp → List α → List α → Bool
  repr : List α → String

variable {α : Type}

/-- A `UserList` is `self.data`, with `self.__class__.__name__`. -/
structure UL (α : Type) where
  cls : String
  data : List α
  deriving Repr, DecidableEq

/-- An operand: a `UserList`, a `list`, another iterable, or a non-iterable (`ty` is the
type name). -/
inductive LOpnd (α : Type) where
  | user (l : List α)
  | list (l : List α)
  | iter (ty : String) (l : List α)
  | noniter (ty : String)
  deriving Repr, DecidableEq

/-- `list(other)`. -/
def iterOf : LOpnd α → Py (List α)
  | .user l | .list l | .iter _ l => .ok l
  | .noniter ty => .error (.typeError s!"'{ty}' object is not iterable")

/-- `UserList.__init__`, :1309-1318; `none` is `initlist=None`. -/
def ulNew (cls : String) : Option (LOpnd α) → Py (UL α)
  | none => .ok ⟨cls, []⟩
  | some (.list l) => .ok ⟨cls, l⟩
  | some (.user l) => .ok ⟨cls, l⟩
  | some o => do
    let l ← iterOf o
    return ⟨cls, l⟩

/-- `UserList.__cast`, :1338-1339: a `list` to compare with, or the type name of
some other object. -/
def ulCast : LOpnd α → List α ⊕ String
  | .user l | .list l => .inl l
  | .iter ty _ | .noniter ty => .inr ty

/-- `__lt__`, `__le__`, `__eq__`, `__gt__`, `__ge__`, :1323-1336: `self.data op
self.__cast(other)`. A list against a non-list is `NotImplemented` on both sides, so `==`
is identity and the orderings raise. -/
def ulCmp (ops : ListOps α) (op : CmpOp) (u : UL α) (o : LOpnd α) : Py Bool :=
  match ulCast o with
  | .inl l => .ok (ops.rich op u.data l)
  | .inr ty =>
    if op = .eq then .ok false
    else .error (.typeError s!"'{op.sym}' not supported between instances of 'list' and '{ty}'")

/-- `UserList.__repr__`, :1320-1321. -/
def ulRepr (ops : ListOps α) (u : UL α) : String := ops.repr u.data

/-- `UserList.__contains__`, :1341-1342. -/
def ulContains (ops : ListOps α) (u : UL α) (x : α) : Bool := ops.contains u.data x

/-- `UserList.__len__`, :1344-1345. -/
def ulLen (u : UL α) : Nat := u.data.length

/-- `UserList.__getitem__`, :1347-1351, int index. -/
def ulGetitem (ops : ListOps α) (u : UL α) (i : Int) : Py α := ops.getItem u.data i

/-- `UserList.__getitem__`, slice: `self.__class__(self.data[i])`. -/
def ulGetslice (ops : ListOps α) (u : UL α) (s : Slice) : Py (UL α) := do
  let l ← ops.getSlice u.data s
  return ⟨u.cls, l⟩

/-- Store a new `self.data`. -/
def withData (u : UL α) (r : Py (List α)) : Py (UL α) := r.map (fun l => { u with data := l })

/-- `UserList.__setitem__`, :1353-1354, int index. -/
def ulSetitem (ops : ListOps α) (u : UL α) (i : Int) (x : α) : Py (UL α) :=
  withData u (ops.setItem u.data i x)

/-- `UserList.__setitem__` with a slice. -/
def ulSetslice (ops : ListOps α) (u : UL α) (s : Slice) (v : List α) : Py (UL α) :=
  withData u (ops.assSlice u.data s (some v))

/-- `UserList.__delitem__`, :1356-1357, int index. -/
def ulDelitem (ops : ListOps α) (u : UL α) (i : Int) : Py (UL α) :=
  withData u (ops.delItem u.data i)

/-- `UserList.__delitem__` with a slice. -/
def ulDelslice (ops : ListOps α) (u : UL α) (s : Slice) : Py (UL α) :=
  withData u (ops.assSlice u.data s none)

/-- `UserList.__add__`, :1359-1364. -/
def ulAdd (u : UL α) : LOpnd α → Py (UL α)
  | .user l => .ok ⟨u.cls, u.data ++ l⟩
  | .list l => .ok ⟨u.cls, u.data ++ l⟩
  | o => do
    let l ← iterOf o
    return ⟨u.cls, u.data ++ l⟩

/-- `UserList.__radd__`, :1366-1371. -/
def ulRadd (u : UL α) : LOpnd α → Py (UL α)
  | .user l => .ok ⟨u.cls, l ++ u.data⟩
  | .list l => .ok ⟨u.cls, l ++ u.data⟩
  | o => do
    let l ← iterOf o
    return ⟨u.cls, l ++ u.data⟩

/-- `UserList.__iadd__`, :1373-1380. -/
def ulIadd (u : UL α) : LOpnd α → Py (UL α)
  | .user l => .ok { u with data := u.data ++ l }
  | .list l => .ok { u with data := u.data ++ l }
  | o => do
    let l ← iterOf o
    return { u with data := u.data ++ l }

/-- `UserList.__mul__`, :1382-1383, and `__rmul__`, :1385. -/
def ulMul (ops : ListOps α) (u : UL α) (n : Int) : Py (UL α) := do
  let l ← ops.repeatL u.data n
  return ⟨u.cls, l⟩

/-- `UserList.__imul__`, :1387-1389. -/
def ulImul (ops : ListOps α) (u : UL α) (n : Int) : Py (UL α) := withData u (ops.irepeat u.data n)

/-- `UserList.__copy__`, :1391-1396. -/
def ulCopyDunder (u : UL α) : UL α := { u with data := u.data.take u.data.length }

/-- `UserList.append`, :1398-1399. -/
def ulAppend (u : UL α) (x : α) : UL α := { u with data := u.data ++ [x] }

/-- `UserList.insert`, :1401-1402. -/
def ulInsert (ops : ListOps α) (u : UL α) (i : Int) (x : α) : Py (UL α) :=
  withData u (ops.insert u.data i x)

/-- `UserList.pop`, :1404-1405. -/
def ulPop (ops : ListOps α) (u : UL α) (i : Option Int) : Py (α × UL α) :=
  (ops.pop u.data i).map (fun r => (r.1, { u with data := r.2 }))

/-- `UserList.remove`, :1407-1408. -/
def ulRemove (ops : ListOps α) (u : UL α) (x : α) : Py (UL α) := withData u (ops.remove u.data x)

/-- `UserList.clear`, :1410-1411. -/
def ulClear (u : UL α) : UL α := { u with data := [] }

/-- `UserList.copy`, :1413-1414: `self.__class__(self)`. -/
def ulCopy (u : UL α) : Py (UL α) := ulNew u.cls (some (.user u.data))

/-- `UserList.count`, :1416-1417. -/
def ulCount (ops : ListOps α) (u : UL α) (x : α) : Int := ops.count u.data x

/-- `UserList.index`, :1419-1420. -/
def ulIndex (ops : ListOps α) (u : UL α) (x : α) (start stop : Option Int) : Py Int :=
  ops.index u.data x start stop

/-- `UserList.reverse`, :1422-1423. -/
def ulReverse (ops : ListOps α) (u : UL α) : UL α := { u with data := ops.reverse u.data }

/-- `UserList.sort`, :1425-1426. -/
def ulSort (ops : ListOps α) (u : UL α) (r : Bool) : UL α := { u with data := ops.sort u.data r }

/-- `UserList.extend`, :1428-1432. -/
def ulExtend (u : UL α) : LOpnd α → Py (UL α)
  | .user l => .ok { u with data := u.data ++ l }
  | o => do
    let l ← iterOf o
    return { u with data := u.data ++ l }

/-! ### `list` on ints: the `PyLean.Sequences` mirrors -/

/-- First-difference comparison of `list_richcompare`, Objects/listobject.c. -/
def cmpVal (op : CmpOp) (a b : Int) : Bool :=
  match op with
  | .lt => decide (a < b)
  | .le => decide (a ≤ b)
  | .eq => decide (a = b)
  | .gt => decide (a > b)
  | .ge => decide (a ≥ b)

def listRich (op : CmpOp) : List Int → List Int → Bool
  | x :: xs, y :: ys => if x = y then listRich op xs ys else cmpVal op x y
  | a, b => cmpVal op a.length b.length

/-- `repr(list of ints)`. -/
def listRepr (l : List Int) : String := "[" ++ ", ".intercalate (l.map toString) ++ "]"

/-- `list` of ints, as `ListOps`. -/
def intOps : ListOps Int where
  getItem := Sequences.listGetItem
  getSlice := fun l s => do
    let ps ← listSlicePositions l.length s
    return ps.map (Sequences.ix l)
  setItem := fun l i x => Sequences.listAssItem l i (some x)
  delItem := fun l i => Sequences.listAssItem l i none
  assSlice := Sequences.listAssSubscript
  insert := Sequences.listInsert
  pop := Sequences.listPop
  remove := Sequences.listRemove
  index := Sequences.listIndex
  count := Sequences.listCount
  contains := fun l x => l.contains x
  repeatL := Sequences.listRepeat
  irepeat := Sequences.listIRepeat
  reverse := List.reverse
  sort := fun l r => if r then Accel.pySortedRev none l else Accel.pySorted none l
  rich := listRich
  repr := listRepr

/-! ### A `list` and a `UserList` driven by the same program -/

/-- A mutating `list` call, as data. -/
inductive LOp (α : Type) where
  | append (x : α)
  | insert (i : Int) (x : α)
  | pop (i : Option Int)
  | remove (x : α)
  | clear
  | extend (l : List α)
  | reverse
  | sort (r : Bool)
  | setitem (i : Int) (x : α)
  | setslice (s : Slice) (v : List α)
  | delitem (i : Int)
  | delslice (s : Slice)
  | iadd (l : List α)
  | imul (n : Int)
  deriving Repr

/-- The call on a real `list`. `clear` and `append` have no failure. -/
def lStep (ops : ListOps α) : LOp α → List α → Py (List α)
  | .append x, l => .ok (l ++ [x])
  | .insert i x, l => ops.insert l i x
  | .pop i, l => (ops.pop l i).map (·.2)
  | .remove x, l => ops.remove l x
  | .clear, _ => .ok []
  | .extend e, l => .ok (l ++ e)
  | .reverse, l => .ok (ops.reverse l)
  | .sort r, l => .ok (ops.sort l r)
  | .setitem i x, l => ops.setItem l i x
  | .setslice s v, l => ops.assSlice l s (some v)
  | .delitem i, l => ops.delItem l i
  | .delslice s, l => ops.assSlice l s none
  | .iadd e, l => .ok (l ++ e)
  | .imul n, l => ops.irepeat l n

/-- The call on a `UserList`. -/
def uStep (ops : ListOps α) : LOp α → UL α → Py (UL α)
  | .append x, u => .ok (ulAppend u x)
  | .insert i x, u => ulInsert ops u i x
  | .pop i, u => (ulPop ops u i).map (·.2)
  | .remove x, u => ulRemove ops u x
  | .clear, u => .ok (ulClear u)
  | .extend e, u => ulExtend u (.list e)
  | .reverse, u => .ok (ulReverse ops u)
  | .sort r, u => .ok (ulSort ops u r)
  | .setitem i x, u => ulSetitem ops u i x
  | .setslice s v, u => ulSetslice ops u s v
  | .delitem i, u => ulDelitem ops u i
  | .delslice s, u => ulDelslice ops u s
  | .iadd e, u => ulIadd u (.list e)
  | .imul n, u => ulImul ops u n

def runL (ops : ListOps α) : List (LOp α) → List α → Py (List α)
  | [], l => .ok l
  | c :: t, l => do
    let l' ← lStep ops c l
    runL ops t l'

def runU (ops : ListOps α) : List (LOp α) → UL α → Py (UL α)
  | [], u => .ok u
  | c :: t, u => do
    let u' ← uStep ops c u
    runU ops t u'

end PyLean.CoreLibs.Coll
