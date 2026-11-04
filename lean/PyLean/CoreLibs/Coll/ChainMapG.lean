import PyLean.CoreLibs.Coll.ChainMap

/-!
`ChainMap` beyond plain dicts, Lib/collections/__init__.py:1040-1168 (CPython 3.15.2):
`__getitem__` and `__contains__` over arbitrary mappings, `__repr__` under its
`reprlib.recursive_repr` guard, `fromkeys` over a fallible iterable, and `copy`, `__or__`,
`__ior__`, `clear` on objects with identities.

Not modelled: a `__missing__` of a map (a `defaultdict`) storing the value it returns; the
`GMap` view is read-only.
-/

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Hier isA builtinHier)

variable {κ ν : Type} [DecidableEq κ]

/-! ### Arbitrary mappings in `maps` -/

/-- A mapping as `__getitem__` and `in` use it: `m[key]` (`__getitem__`, which for a dict subclass
may call `__missing__`, and may raise anything) and `key in m` (`__contains__`). -/
structure GMap (κ ν : Type) where
  getitem : κ → Py ν
  contains : κ → Py Bool

/-- A plain dict: `KeyError(key)` on an absent key. -/
def dictG (rk : κ → String) (d : D κ ν) : GMap κ ν where
  getitem k := match D.get? d k with
    | some v => .ok v
    | none => .error (.keyError (rk k))
  contains k := .ok (D.mem d k)

/-- A `defaultdict` holding `d`: `d[key]` on an absent key returns `default_factory()`; `in` only
looks at `d`. -/
def defaultG (d : D κ ν) (factory : Py ν) : GMap κ ν where
  getitem k := match D.get? d k with
    | some v => .ok v
    | none => factory
  contains k := .ok (D.mem d k)

/-- `ChainMap.__getitem__`, :1064-1070: `mapping[key]` for each map in turn (:1065-1066), an
exception that is a `KeyError` under `H` moving on (:1067-1069, `except KeyError: pass`), any other
exception propagating; then `self.__missing__(key)` (:1070). -/
def cmGetitemG (H : Hier) (miss : κ → Py ν) : List (GMap κ ν) → κ → Py ν
  | [], k => miss k
  | m :: t, k =>
    match m.getitem k with
    | .ok v => .ok v
    | .error e => if isA H e "KeyError" then cmGetitemG H miss t k else .error e

/-- `ChainMap.__contains__`, :1084-1088: `any(key in m for m in self.maps)`. -/
def cmContainsG : List (GMap κ ν) → κ → Py Bool
  | [], _ => .ok false
  | m :: t, k => do
    let b ← m.contains k
    if b then pure true else cmContainsG t k

/-! ### `__repr__` and `recursive_repr` -/

/-- An entry of `maps`: a dict, or a `ChainMap` object (by id). -/
inductive MRef (κ ν : Type) where
  | dict (d : D κ ν)
  | chain (id : Nat)

/-- `ChainMap.__repr__`, :1093-1095, wrapped by `reprlib.recursive_repr()` (Lib/reprlib.py:9-24):
`running` holds the ids whose `__repr__` is in progress on this thread (`repr_running`); a
recursive call returns `'...'` (:17-18). `heap i` is object `i`'s class name and maps, `rd` is
`repr` of a dict (free to raise). -/
def cmReprR (rd : D κ ν → Py String) (heap : Nat → Option (String × List (MRef κ ν))) :
    Nat → List Nat → Nat → Py String
  | 0, _, _ => .error .modelFuel
  | fuel + 1, running, i =>
    if i ∈ running then .ok "..."
    else match heap i with
      | none => .error (.named "NameError" "~no such object")
      | some (cls, maps) => do
        let parts ← maps.mapM (fun m => match m with
          | .dict d => rd d
          | .chain j => cmReprR rd heap fuel (i :: running) j)
        pure (cls ++ "(" ++ ", ".intercalate parts ++ ")")

/-! ### `fromkeys` -/

/-- `ChainMap.fromkeys(iterable, value)`, :1097-1100: `cls(dict.fromkeys(iterable, value))`,
`dict.fromkeys` storing each key in turn. -/
def cmFromkeysP (K : KOps κ) (it : Py (FIt κ)) (value : ν) : Py (CMap κ ν) := do
  let d ← (forPy (fun d k => dSet K d k value) [] it).toPy
  pure (cmNew [d])

/-! ### Objects: `copy`, `__or__`, `__ior__`, `clear` -/

/-- A `ChainMap` object: its id, and `maps` as `(id, contents)` of each mapping object. -/
structure CMapO (κ ν : Type) where
  id : Nat
  maps : List (Nat × D κ ν)
  deriving Repr, DecidableEq

/-- `ChainMap.copy`, :1102-1104: `self.__class__(self.maps[0].copy(), *self.maps[1:])`, a new
object `fresh` whose first map is the new dict `fresh0` (`dict.copy`) and whose other maps are
`self`'s own objects. -/
def cmCopyO (fresh fresh0 : Nat) (c : CMapO κ ν) : Py (CMapO κ ν) :=
  match c.maps with
  | [] => .error noMap
  | (_, m) :: t => .ok ⟨fresh, (fresh0, D.update [] m) :: t⟩

/-- `ChainMap.__ior__`, :1151-1153: `self.maps[0].update(other)` in place, then `self`. `other`
is what `dict.update` reads from it, pair by pair: a non-iterable's `TypeError` before any pair,
or a failure part way, after which the pairs already stored stay in `maps[0]`. -/
def cmIorO (K : KOps κ) (c : CMapO κ ν) (other : Py (FIt (κ × ν))) : Out (CMapO κ ν) :=
  match c.maps with
  | [] => (c, some noMap)
  | (i, m) :: t =>
    let r := forPy (fun d (p : κ × ν) => dSet K d p.1 p.2) m other
    (⟨c.id, (i, r.1) :: t⟩, r.2)

/-- `ChainMap.__or__`, :1155-1160: `NotImplemented` (`none`) for a non-`Mapping`, else
`m = self.copy(); m.maps[0].update(other); return m`; an exception discards `m`. -/
def cmOrO (K : KOps κ) (fresh fresh0 : Nat) (c : CMapO κ ν) (other : Option (Py (FIt (κ × ν)))) :
    Option (Py (CMapO κ ν)) :=
  other.map (fun o => do
    let m ← cmCopyO fresh fresh0 c
    (cmIorO K m o).toPy)

/-- `ChainMap.__ror__`, :1162-1168, with `dict(other)` (:1165) Python code that may raise (a
`Mapping` whose `keys()` or `[]` raises); the later updates are from dicts. -/
def cmRorP (c : CMap κ ν) (other : Option (Py (D κ ν))) : Option (Py (CMap κ ν)) :=
  other.map (fun p => p.map (fun o => cmNew [c.maps.reverse.foldl D.update (D.update [] o)]))

/-- `ChainMap.clear`, :1147-1149: `self.maps[0].clear()` in place. -/
def cmClearO (c : CMapO κ ν) : Py (CMapO κ ν) :=
  match c.maps with
  | [] => .error noMap
  | (i, _) :: t => .ok ⟨c.id, (i, []) :: t⟩

/-- The contents of the maps. -/
def CMapO.view (c : CMapO κ ν) : List (D κ ν) := c.maps.map (·.2)

end PyLean.CoreLibs.Coll
