import PyLean.CoreLibs.Coll.UserDict

/-!
`collections.UserDict` with Python code where the source calls it, Lib/collections/__init__.py:1175-1278
(CPython 3.15.2), and `MutableMapping.update`, Lib/_collections_abc.py:965-984: a fallible
constructor argument, a `__missing__` that may raise, `__repr__` with `dict_repr`'s recursion guard,
`__ior__`'s two branches, `__copy__` and `copy` on objects, and `fromkeys` over a fallible iterable.

Scope: `__setitem__` is `UserDict`'s (a subclass overriding it is out of scope); callbacks are pure
functions (a `__missing__` that mutates `self` is out of scope).
-/

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-! ### `MutableMapping.update` and `__init__` -/

/-- The positional argument of `update`, as `MutableMapping.update` reads it: a `Mapping`
(`for key in other: self[key] = other[key]`, _collections_abc.py:974-976), an object with `keys()`
(`for key in other.keys()`, :977-979), or an iterable of pairs (`for key, value in other`,
:980-982), each item unpacked (a non-pair raises). The keywords follow (:983-984). -/
inductive USrc (κ ν : Type) where
  | mapping (keys : Py (FIt κ)) (getitem : κ → Py ν)
  | keyed (keys : Py (FIt κ)) (getitem : κ → Py ν)
  | pairs (it : Py (FIt (Py (κ × ν))))

/-- A `dict` as the argument. -/
def dictUSrc (d : D κ ν) : USrc κ ν :=
  .mapping (.ok (FIt.ofList (D.keys d))) (fun k => match D.get? d k with
    | some v => .ok v
    | none => .error (.keyError "~key"))

/-- `self.update(other)` on the storage, `self[key] = value` being `self.data[key] = value`. -/
def udUpdateP (K : KOps κ) (d : D κ ν) : USrc κ ν → Out (D κ ν)
  | .mapping ks g | .keyed ks g => forPy (fun d k => do
      let v ← g k
      dSet K d k v) d ks
  | .pairs it => forPy (fun d p => do
      let (k, v) ← p
      dSet K d k v) d it

/-- `UserDict.__init__`, :1177-1182: `self.data = {}`, `self.update(dict)` unless it is `None`,
then `self.update(kwargs)` when there are keywords; an exception leaves no object. -/
def udNewP (K : KOps κ) (src : Option (USrc κ ν)) (kwargs : D κ ν) : Py (D κ ν) :=
  let r : Out (D κ ν) := match src with
    | some s => udUpdateP K [] s
    | none => ([], none)
  (r.andThen (fun d => if kwargs.isEmpty then (d, none) else udUpdateP K d (dictUSrc kwargs))).toPy

/-! ### `__getitem__`, `__contains__` -/

/-- `UserDict.__getitem__`, :1188-1193: `key in self.data` (:1189), then `self.data[key]`, then
`self.__class__.__missing__(self, key)` when the class has one (`miss`, Python code that may
raise), else `KeyError(key)`. -/
def udGetitemP (K : KOps κ) (rk : κ → String) (miss : Option (κ → Py ν)) (u : UD κ ν) (k : κ) : Py ν := do
  let present ← dMem K u.data k
  if present then
    match D.get? u.data k with
    | some v => pure v
    | none => .error (.keyError (rk k))
  else
    match miss with
    | some f => f k
    | none => .error (.keyError (rk k))

/-- `UserDict.__contains__`, :1206-1207: `key in self.data`. -/
def udContainsP (K : KOps κ) (u : UD κ ν) (k : κ) : Py Bool := dMem K u.data k

/-! ### `__repr__` -/

/-- A value of a `UserDict`: an ordinary object, or a `UserDict` (by id). -/
inductive VRef (ν : Type) where
  | plain (v : ν)
  | ud (id : Nat)

/-- `UserDict.__repr__`, :1216-1217, `repr(self.data)`: `anydict_repr_impl` (Objects/dictobject.c:3642-3700), whose
`Py_ReprEnter` (:3647-3650) on the dict prints `{...}` for a dict whose `repr` is in progress (`running`, the
ids of the `UserDict`s whose data is being printed). `heap i` is object `i`'s data. -/
def udReprR (rk : κ → Py String) (rv : ν → Py String) (heap : Nat → Option (D κ (VRef ν))) :
    Nat → List Nat → Nat → Py String
  | 0, _, _ => .error .modelFuel
  | fuel + 1, running, i =>
    if i ∈ running then .ok "{...}"
    else match heap i with
      | none => .error (.named "NameError" "~no such object")
      | some d => do
        let parts ← d.mapM (fun p => do
          let a ← rk p.1
          let b ← match p.2 with
            | .plain v => rv v
            | .ud j => udReprR rk rv heap fuel (i :: running) j
          pure (a ++ ": " ++ b))
        pure ("{" ++ ", ".intercalate parts ++ "}")

/-! ### `__ior__` -/

/-- The operand of `|=`: a `UserDict` (its `.data` is used, :1234-1235), or anything else, given
as what `dict |= other` (`dict_update_arg`) reads from it: its items in order, a failure part way,
or the `TypeError` of a non-iterable. -/
inductive IorOpnd (κ ν : Type) where
  | user (d : D κ ν)
  | other (it : Py (FIt (κ × ν)))

/-- `UserDict.__ior__`, :1233-1238: `self.data |= other.data` or `self.data |= other`, then
`self`. -/
def udIorP (K : KOps κ) (u : UD κ ν) : IorOpnd κ ν → Out (UD κ ν)
  | .user d => (⟨u.cls, D.update u.data d⟩, none)
  | .other it =>
    let r := forPy (fun d (p : κ × ν) => dSet K d p.1 p.2) u.data it
    (⟨u.cls, r.1⟩, r.2)

/-! ### `__copy__`, `copy`, `fromkeys` -/

/-- A `UserDict` object: id, class, `data`, and the rest of its `__dict__`. -/
structure UDO (κ ν α : Type) where
  id : Nat
  cls : String
  data : D κ ν
  attrs : List (String × α)
  deriving Repr, DecidableEq

/-- `UserDict.__copy__`, :1240-1245: a new instance `fresh` of `self.__class__`, its `__dict__`
updated from `self`'s, and `data` replaced by `self.data.copy()`. -/
def udCopyDunderO {α : Type} (fresh : Nat) (u : UDO κ ν α) : UDO κ ν α :=
  ⟨fresh, u.cls, D.update [] u.data, u.attrs⟩

/-- `UserDict.copy`, :1247-1257. For `UserDict` itself, `UserDict(self.data.copy())`, the new
object `fresh`. For a subclass: `self.data = {}`, `c = copy.copy(self)` (`copyFn`, the class's
`__copy__`, Python code that may raise), `self.data` restored by the `finally`, then
`c.update(self)`. Returns `self` as it is left, and the result. -/
def udCopyO {α : Type} (K : KOps κ) (copyFn : UDO κ ν α → Py (UDO κ ν α)) (fresh : Nat) (u : UDO κ ν α) :
    UDO κ ν α × Py (UDO κ ν α) :=
  if u.cls = "UserDict" then (u, .ok ⟨fresh, "UserDict", D.update [] u.data, []⟩)
  else
    match copyFn { u with data := [] } with
    | .error e => (u, .error e)
    | .ok c =>
      let r := udUpdateP K c.data (dictUSrc u.data)
      (u, (Out.toPy r).map (fun d => { c with data := d }))

/-- `UserDict.fromkeys`, :1272-1277: `d = cls()`, then `d[key] = value` for each key. -/
def udFromkeysP (K : KOps κ) (cls : String) (it : Py (FIt κ)) (value : ν) : Py (UD κ ν) :=
  (forPy (fun d k => dSet K d k value) [] it).toPy.map (fun d => ⟨cls, d⟩)

end PyLean.CoreLibs.Coll
