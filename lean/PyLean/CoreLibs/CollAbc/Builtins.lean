import PyLean.CoreLibs.CollAbc.Model

/-!
The builtin behaviour each mixin is compared with: `list`, `dict` and `set`, mirrored
from `Objects/listobject.c` and `Objects/dictobject.c`, and those builtins packaged as
instances of the primitive structures of `Model.lean`.
-/

namespace PyLean.CoreLibs.CollAbc

open PyLean

/-- `list.__getitem__` with an `int`, Objects/listobject.c `list_subscript`. -/
def listGet {α : Type} (xs : List α) (i : Int) : Py α :=
  let n : Int := xs.length
  let j := if i < 0 then i + n else i
  if j < 0 ∨ j ≥ n then .error (.indexError "list index out of range")
  else
    match xs[j.toNat]? with
    | some v => .ok v
    | none => .error (.indexError "list index out of range")

/-- `del xs[i]`. -/
def listDel {α : Type} (xs : List α) (i : Int) : Py (List α) :=
  let n : Int := xs.length
  let j := if i < 0 then i + n else i
  if j < 0 ∨ j ≥ n then .error (.indexError "list assignment index out of range")
  else .ok (xs.eraseIdx j.toNat)

/-- `xs[i] = v`. -/
def listSetItem {α : Type} (xs : List α) (i : Int) (v : α) : Py (List α) :=
  let n : Int := xs.length
  let j := if i < 0 then i + n else i
  if j < 0 ∨ j ≥ n then .error (.indexError "list assignment index out of range")
  else .ok (xs.set j.toNat v)

/-- `list.insert`, Objects/listobject.c:476 `ins1`: negative counts from the end and both
ends clamp. -/
def listInsert {α : Type} (xs : List α) (i : Int) (v : α) : List α :=
  let n : Int := xs.length
  let w := if i < 0 then max (i + n) 0 else min i n
  xs.take w.toNat ++ v :: xs.drop w.toNat

/-- `list.pop(index)`, Objects/listobject.c:1531 `list_pop_impl`. -/
def listPop {α : Type} (xs : List α) (index : Int) : Py (α × List α) :=
  if xs.isEmpty then .error (.indexError "pop from empty list")
  else
    let n : Int := xs.length
    let j := if index < 0 then index + n else index
    if j < 0 ∨ j ≥ n then .error (.indexError "pop index out of range")
    else
      match xs[j.toNat]? with
      | some v => .ok (v, xs.eraseIdx j.toNat)
      | none => .error (.indexError "pop index out of range")

/-- The loop of `list_index_impl`, Objects/listobject.c: from `i` while `i < stop`
and `i` is a valid index. -/
def listIndexLoop {α : Type} (E : EqOps α) (value : α) (xs : List α) (stop : Int) :
    (fuel : Nat) → Int → Py (Option Int)
  | 0, _ => .error .modelFuel
  | fuel + 1, i =>
    if i < stop then
      match xs[i.toNat]? with
      | none => .ok none
      | some v => do
        if ← E.same v value then return some i
        listIndexLoop E value xs stop fuel (i + 1)
    else .ok none

/-- `list.index(value, start, stop)`, Objects/listobject.c:3283-3312 `list_index_impl`, with
`none` for the `ValueError`. Indices are already `Py_ssize_t`, clamped by
`_PyEval_SliceIndexNotNone`, which keeps the outcome for any `list` shorter than
`sys.maxsize`. -/
def listIndex {α : Type} (E : EqOps α) (xs : List α) (value : α) (start stop : Int)
    (fuel : Nat) : Py (Option Int) :=
  let n : Int := xs.length
  let start := if start < 0 then max (start + n) 0 else start
  let stop := if stop < 0 then max (stop + n) 0 else stop
  listIndexLoop E value xs stop fuel start

/-- `list.__contains__`, Objects/listobject.c:650-666 `list_contains`. -/
def listContains {α : Type} (E : EqOps α) (value : α) : List α → Py Bool
  | [] => .ok false
  | v :: vs => do
    if ← E.same v value then return true
    listContains E value vs

/-- `list.count`, Objects/listobject.c:3324-3347 `list_count_impl`; its `obj == value` test is the identity half of `same`. -/
def listCount {α : Type} (E : EqOps α) (value : α) : List α → Py Nat
  | [] => .ok 0
  | v :: vs => do
    let hit ← E.same v value
    let rest ← listCount E value vs
    pure ((if hit then 1 else 0) + rest)

/-- `list.remove`, Objects/listobject.c:3362-3382 `list_remove_impl`: `none` for the `ValueError`. -/
def listRemove {α : Type} (E : EqOps α) (value : α) : List α → Py (Option (List α))
  | [] => .ok none
  | v :: vs => do
    if ← E.same v value then return some vs
    match ← listRemove E value vs with
    | some r => pure (some (v :: r))
    | none => pure none

/-- A `list` as a `Sequence`. -/
def listSeq {α : Type} (xs : List α) : Seq α := ⟨listGet xs, .ok xs.length⟩

/-- A `list` as a `MutableSequence`. -/
def listMSeq {α : Type} : MSeq (List α) α where
  getitem := listGet
  setitem := listSetItem
  delitem := listDel
  insert s i v := .ok (listInsert s i v)
  len s := .ok s.length

/-- A `set`, as the list of its distinct elements in iteration order. -/
def listSet {α : Type} [DecidableEq α] (xs : List α) : SetV α :=
  ⟨.ok xs.length, .ok xs, fun x => .ok (decide (x ∈ xs)), none⟩

/-- The set of the elements of a list: what the constructor `cls(it)` does. -/
def dedup {α : Type} [DecidableEq α] : List α → List α → List α
  | seen, [] => seen.reverse
  | seen, x :: xs => if x ∈ seen then dedup seen xs else dedup (x :: seen) xs

def mkSet {α : Type} [DecidableEq α] (xs : List α) : SetV α := listSet (dedup [] xs)

/-- A `set` as a `MutableSet`, in insertion order. -/
def listMSet {α : Type} [DecidableEq α] : MSet (List α) α where
  view := listSet
  add s x := .ok (if x ∈ s then s else s ++ [x])
  discard s x := .ok (s.erase x)
  fromIter := mkSet

/-- `d[k]` on a `dict` kept as its item list. -/
def dictGet {K V : Type} [DecidableEq K] (d : List (K × V)) (k : K) : Py V :=
  match d.lookup k with
  | some v => .ok v
  | none => .error (.keyError "~key")

/-- A `dict` as a `Mapping`. -/
def dictMap {K V : Type} [DecidableEq K] (d : List (K × V)) : MapV K V :=
  ⟨dictGet d, .ok (d.map Prod.fst), .ok d.length, none⟩

/-- `d[k] = v`: an existing key keeps its position. -/
def dictSet {K V : Type} [DecidableEq K] (d : List (K × V)) (k : K) (v : V) : List (K × V) :=
  if d.any (fun p => p.1 = k) then d.map (fun p => if p.1 = k then (k, v) else p)
  else d ++ [(k, v)]

/-- `del d[k]`. -/
def dictDel {K V : Type} [DecidableEq K] (d : List (K × V)) (k : K) : Py (List (K × V)) :=
  if d.any (fun p => p.1 = k) then .ok (d.filter (fun p => p.1 ≠ k))
  else .error (.keyError "~key")

/-- A `dict` as a `MutableMapping`. -/
def dictMMap {K V : Type} [DecidableEq K] : MMap (List (K × V)) K V where
  view := dictMap
  setitem d k v := .ok (dictSet d k v)
  delitem := dictDel

/-- `dict.pop(key[, default])`, Objects/dictobject.c:3112 `_PyDict_Pop_KnownHash`. -/
def builtinDictPop {K V : Type} [DecidableEq K] (d : List (K × V)) (k : K) (default : Option V) :
    Py (V × List (K × V)) :=
  match d.lookup k with
  | some v => .ok (v, d.filter (fun p => p.1 ≠ k))
  | none =>
    match default with
    | some x => .ok (x, d)
    | none => .error (.keyError "~key")

/-- `dict.setdefault`, Objects/dictobject.c:4409 `dict_setdefault_ref_lock_held`. -/
def builtinDictSetdefault {K V : Type} [DecidableEq K] (d : List (K × V)) (k : K) (default : V) :
    V × List (K × V) :=
  match d.lookup k with
  | some v => (v, d)
  | none => (default, d ++ [(k, default)])

/-- `dict.update` applied to a list of pairs, in order. -/
def builtinDictUpdate {K V : Type} [DecidableEq K] (d : List (K × V)) (xs : List (K × V)) :
    List (K × V) :=
  xs.foldl (fun acc p => dictSet acc p.1 p.2) d

end PyLean.CoreLibs.CollAbc
