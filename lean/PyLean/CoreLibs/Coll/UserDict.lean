import PyLean.CoreLibs.Coll.ChainMap

/-!
`collections.UserDict`, Lib/collections/__init__.py:1175-1278 (CPython 3.15.2), with
the methods it inherits from `MutableMapping`, Lib/_collections_abc.py:930-992. Those
are copied here because `UserDict` differs from `dict` through them.

`miss` is the subclass hook: `none` when the class has no `__missing__`, `some f`
when `self.__class__.__missing__(self, key)` returns `f key`. A `__missing__` that
raises is a `KeyError` path equal to having none.
-/

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- A `UserDict` is its `self.data`; `cls` is `self.__class__.__name__`. -/
structure UD (κ ν : Type) where
  cls : String
  data : D κ ν
  deriving Repr, DecidableEq

/-- `self.update(src)`: `MutableMapping.update`, _collections_abc.py:965-984, which stores
through `__setitem__`. -/
def udUpdate (u : UD κ ν) (src : List (κ × ν)) (kwds : D κ ν) : UD κ ν :=
  { u with data := D.update (D.update u.data src) kwds }

/-- `UserDict.__init__`, :1137-1142. -/
def udNew (cls : String) (src : Option (List (κ × ν))) (kwargs : D κ ν) : UD κ ν :=
  let u : UD κ ν := ⟨cls, []⟩
  let u := match src with
    | some s => udUpdate u s []
    | none => u
  if kwargs.isEmpty then u else udUpdate u kwargs []

/-- `UserDict.__len__`, :1144-1145. -/
def udLen (u : UD κ ν) : Nat := u.data.length

/-- `UserDict.__getitem__`, :1147-1152. -/
def udGetitem (rk : κ → String) (miss : Option (κ → ν)) (u : UD κ ν) (k : κ) : Py ν :=
  if D.mem u.data k then
    match D.get? u.data k with
    | some v => .ok v
    | none => .error (.keyError (rk k))
  else
    match miss with
    | some f => .ok (f k)
    | none => .error (.keyError (rk k))

/-- `UserDict.__setitem__`, :1154-1155. -/
def udSetitem (u : UD κ ν) (k : κ) (v : ν) : UD κ ν := { u with data := D.set u.data k v }

/-- `UserDict.__delitem__`, :1157-1158: `del self.data[key]`. -/
def udDelitem (rk : κ → String) (u : UD κ ν) (k : κ) : Py (UD κ ν) :=
  if D.mem u.data k then .ok { u with data := D.del u.data k } else .error (.keyError (rk k))

/-- `list(u)`, `UserDict.__iter__`, :1160-1161. -/
def udIter (u : UD κ ν) : List κ := D.keys u.data

/-- `UserDict.__contains__`, :1165-1166. -/
def udContains (u : UD κ ν) (k : κ) : Bool := D.mem u.data k

/-- `UserDict.get`, :1168-1171. -/
def udGet (rk : κ → String) (miss : Option (κ → ν)) (u : UD κ ν) (k : κ) (default : Option ν) :
    Py (Option ν) :=
  if udContains u k then (udGetitem rk miss u k).map some else .ok default

/-- `UserDict.__repr__`, :1185-1186. -/
def udRepr (rk : κ → String) (rv : ν → String) (u : UD κ ν) : String := reprD rk rv u.data

/-- The right operand of `|`: a `UserDict`, a `dict`, a `frozendict`, or anything else. -/
inductive UOpnd (κ ν : Type) where
  | user (d : D κ ν)
  | dict (d : D κ ν)
  | frozen (d : D κ ν)
  | other
  deriving Repr, DecidableEq

/-- `UserDict.__or__`, :1188-1193; `none` is `NotImplemented`. `self.__class__(d)`
copies `d` through `__init__`. -/
def udOr (u : UD κ ν) : UOpnd κ ν → Option (UD κ ν)
  | .user d | .dict d | .frozen d => some (udNew u.cls (some (D.or_ u.data d)) [])
  | .other => none

/-- `UserDict.__ror__`, :1195-1200. -/
def udRor (u : UD κ ν) : UOpnd κ ν → Option (UD κ ν)
  | .user d | .dict d | .frozen d => some (udNew u.cls (some (D.or_ d u.data)) [])
  | .other => none

/-- `UserDict.__ior__`, :1202-1207, on the pairs of `other`. -/
def udIor (u : UD κ ν) (other : List (κ × ν)) : UD κ ν := { u with data := D.update u.data other }

/-- `UserDict.__copy__`, :1209-1214, and `UserDict.copy`, :1216-1227, which go through
different code for subclasses and agree on `data` and the class. -/
def udCopyDunder (u : UD κ ν) : UD κ ν := { u with data := D.update [] u.data }

/-- `UserDict.copy`, :1216-1227. On `UserDict` itself: `UserDict(self.data.copy())`. On
a subclass: `copy.copy` of the object with `data` swapped for `{}`, then `c.update(self)`. -/
def udCopy (u : UD κ ν) : UD κ ν :=
  if u.cls = "UserDict" then udNew "UserDict" (some u.data) []
  else udUpdate (udCopyDunder { u with data := [] }) u.data []

/-- `UserDict.fromkeys`, :1229-1234. -/
def udFromkeys (cls : String) (it : List κ) (value : ν) : UD κ ν :=
  it.foldl (fun d k => udSetitem d k value) ⟨cls, []⟩

/-! ### Inherited from `MutableMapping` -/

/-- `MutableMapping.pop`, _collections_abc.py:930-943: `value = self[key]`, and on
`KeyError` the default; then `del self[key]`, which is outside the `try`. -/
def udPop (rk : κ → String) (miss : Option (κ → ν)) (u : UD κ ν) (k : κ) (default : Option ν) :
    Py (ν × UD κ ν) :=
  match udGetitem rk miss u k with
  | .error e =>
    match default with
    | some d => .ok (d, u)
    | none => .error e
  | .ok v => do
    let u' ← udDelitem rk u k
    return (v, u')

/-- `dict.popitem()`. -/
def dictPopitem (d : D κ ν) : Py ((κ × ν) × D κ ν) :=
  match D.popitem? d with
  | some r => .ok r
  | none => .error (.keyError "'popitem(): dictionary is empty'")

/-- `UserDict.popitem`, Lib/collections/__init__.py:1260-1268: `self.data.popitem()`, so last in, first out. It no longer
reads `__getitem__` or `__delitem__`, so `__missing__` plays no part. -/
def udPopitem (_rk : κ → String) (_miss : Option (κ → ν)) (u : UD κ ν) : Py ((κ × ν) × UD κ ν) :=
  (dictPopitem u.data).map (fun r => (r.1, { u with data := r.2 }))

/-- `MutableMapping.setdefault`, _collections_abc.py:986-992. -/
def udSetdefault (rk : κ → String) (miss : Option (κ → ν)) (u : UD κ ν) (k : κ) (default : ν) :
    ν × UD κ ν :=
  match udGetitem rk miss u k with
  | .ok v => (v, u)
  | .error _ => (default, udSetitem u k default)

/-- The `while True: self.popitem()` loop of `MutableMapping.clear`,
_collections_abc.py:957-963, stopping at the `KeyError`. -/
def udClearLoop (rk : κ → String) (miss : Option (κ → ν)) : Nat → UD κ ν → UD κ ν
  | 0, u => u
  | n + 1, u =>
    match udPopitem rk miss u with
    | .ok (_, u') => udClearLoop rk miss n u'
    | .error _ => u

/-- `MutableMapping.clear`. `len + 1` iterations reach the `KeyError`. -/
def udClear (rk : κ → String) (miss : Option (κ → ν)) (u : UD κ ν) : UD κ ν :=
  udClearLoop rk miss (u.data.length + 1) u

/-- `(k, v) in u.items()`: `ItemsView.__contains__`, _collections_abc.py:873-880. -/
def udItemsContains [DecidableEq ν] (rk : κ → String) (miss : Option (κ → ν)) (u : UD κ ν)
    (k : κ) (v : ν) : Bool :=
  match udGetitem rk miss u k with
  | .error _ => false
  | .ok w => decide (w = v)

/-- `list(reversed(u))`: `Mapping` sets `__reversed__ = None`, _collections_abc.py:824, and
`UserDict` does not override it. -/
def udReversed (u : UD κ ν) : Py (List κ) :=
  .error (.typeError s!"'{u.cls}' object is not reversible")

/-! ### The same methods on `dict` and on a `dict` subclass with `__missing__` -/

/-- `list(reversed(d))`, since 3.8. -/
def dictReversed (d : D κ ν) : Py (List κ) := .ok (D.keys d).reverse

/-- `d[k]` on a `dict` subclass, `dict_subscript`: `__missing__` is only called by the
subscript. -/
def dictGetitem (rk : κ → String) (miss : Option (κ → ν)) (d : D κ ν) (k : κ) : Py ν :=
  match D.get? d k with
  | some v => .ok v
  | none =>
    match miss with
    | some f => .ok (f k)
    | none => .error (.keyError (rk k))

/-- `dict.pop(k[, default])`: does not consult `__missing__`. -/
def dictPop (rk : κ → String) (d : D κ ν) (k : κ) (default : Option ν) : Py (ν × D κ ν) :=
  match D.get? d k, default with
  | some v, _ => .ok (v, D.del d k)
  | none, some x => .ok (x, d)
  | none, none => .error (.keyError (rk k))

/-- `dict.setdefault(k, default)`: does not consult `__missing__`. -/
def dictSetdefault (d : D κ ν) (k : κ) (default : ν) : ν × D κ ν :=
  match D.get? d k with
  | some v => (v, d)
  | none => (default, D.set d k default)

/-- `(k, v) in d.items()`, `dictitems_contains`: looks the key up with
`PyDict_GetItemRef`, which never calls `__missing__`. -/
def dictItemsContains [DecidableEq ν] (d : D κ ν) (k : κ) (v : ν) : Bool :=
  match D.get? d k with
  | some w => decide (w = v)
  | none => false

end PyLean.CoreLibs.Coll
