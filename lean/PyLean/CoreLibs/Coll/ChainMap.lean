import PyLean.CoreLibs.Coll.Counter

/-!
`collections.ChainMap`, Lib/collections/__init__.py:1040-1168 (CPython 3.14.7).

Each underlying mapping is a plain dict over abstract keys and values. `self.maps` is
a public list, so a `ChainMap` is its list of dicts, and the "at least one map"
invariant is only established by `__init__`: the empty list is modelled too.

Not modelled: object identity (the model is pure, so `copy` sharing `maps[1:]` with the
original is not observable here) and the `reprlib.recursive_repr` guard, which only acts
on a `ChainMap` that contains itself. The difference between `mapping[key]` and
`key in mapping` for a `defaultdict` needs a mapping that is not a dict; see the
`__missing__` parameter for the subclass hook instead.
-/

namespace PyLean.CoreLibs.Coll

open PyLean

variable {κ ν : Type} [DecidableEq κ]

/-- `repr` of a `str`, for the short keys and messages that reach it: double
quotes when the text holds a single quote. -/
def pyStrRepr (s : String) : String :=
  if s.toList.contains '\'' then "\"" ++ s ++ "\"" else "'" ++ s ++ "'"

/-- `KeyError(msg)` with a `str` argument: `str(e)` is `repr(msg)`. -/
def keyErrorStr (msg : String) : PyExc := .keyError (pyStrRepr msg)

/-- `repr(dict)`. -/
def reprD (rk : κ → String) (rv : ν → String) (d : D κ ν) : String :=
  "{" ++ ", ".intercalate (d.map (fun p => rk p.1 ++ ": " ++ rv p.2)) ++ "}"

/-- `dict.popitem()`: removes the last item. -/
def D.popitem? (d : D κ ν) : Option ((κ × ν) × D κ ν) :=
  match d.getLast? with
  | none => none
  | some p => some (p, d.dropLast)

/-- `set.add` on the list of a set's members. -/
def addK (s : List κ) (x : κ) : List κ := if x ∈ s then s else s ++ [x]

/-- A `ChainMap`: `self.maps`. -/
structure CMap (κ ν : Type) where
  maps : List (D κ ν)
  deriving Repr, DecidableEq

/-- `ChainMap(*maps)`, :1054-1059: `list(maps) or [{}]`. -/
def cmNew : List (D κ ν) → CMap κ ν
  | [] => ⟨[[]]⟩
  | l => ⟨l⟩

/-- The `for mapping in self.maps` loop of `__getitem__`, :1065-1069. -/
def cmLookup : List (D κ ν) → κ → Option ν
  | [], _ => none
  | m :: t, k =>
    match D.get? m k with
    | some v => some v
    | none => cmLookup t k

/-- `ChainMap.__missing__`, :1061-1062; a subclass may replace it. -/
def cmMissing {β : Type} (rk : κ → String) (k : κ) : Py β := .error (.keyError (rk k))

/-- `ChainMap.__getitem__`, :1064-1070, with `self.__missing__` as `miss`. -/
def cmGetitem (miss : κ → Py ν) (c : CMap κ ν) (k : κ) : Py ν :=
  match cmLookup c.maps k with
  | some v => .ok v
  | none => miss k

/-- `ChainMap.__contains__`, :1084-1088. -/
def cmContains (c : CMap κ ν) (k : κ) : Bool := c.maps.any (fun m => D.mem m k)

/-- `ChainMap.get`, :1072-1073. -/
def cmGet (miss : κ → Py ν) (c : CMap κ ν) (k : κ) (default : Option ν) : Py (Option ν) :=
  if cmContains c k then (cmGetitem miss c k).map some else .ok default

/-- `ChainMap.__len__`, :1075-1076: `len(set().union(*self.maps))`. -/
def cmLen (c : CMap κ ν) : Nat :=
  (c.maps.foldl (fun s m => (D.keys m).foldl addK s) []).length

/-- `list(ChainMap)`, `__iter__`, :1078-1082: scan the maps from last to first. -/
def cmIter (c : CMap κ ν) : List κ :=
  D.keys ((c.maps.reverse.map (fun m => D.fromkeys (D.keys m) ())).foldl D.or_ [])

/-- `ChainMap.__bool__`, :1090-1091: `any(self.maps)`. -/
def cmBool (c : CMap κ ν) : Bool := c.maps.any (fun m => !m.isEmpty)

/-- `ChainMap.__repr__`, :1093-1095. -/
def cmRepr (cls : String) (rk : κ → String) (rv : ν → String) (c : CMap κ ν) : String :=
  cls ++ "(" ++ ", ".intercalate (c.maps.map (reprD rk rv)) ++ ")"

/-- `ChainMap.fromkeys`, :1097-1100. -/
def cmFromkeys (it : List κ) (value : ν) : CMap κ ν := cmNew [D.fromkeys it value]

/-- `self.maps[0]` on an empty `maps`. -/
def noMap : PyExc := .indexError "list index out of range"

/-- `ChainMap.copy`, :1102-1104: `self.__class__(self.maps[0].copy(), *self.maps[1:])`. -/
def cmCopy (c : CMap κ ν) : Py (CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | m :: t => .ok (cmNew (m :: t))

/-- `ChainMap.new_child`, :1108-1117. `m` is the mapping argument, `kwargs` the keywords. -/
def cmNewChild (c : CMap κ ν) (m : Option (D κ ν)) (kwargs : D κ ν) : CMap κ ν :=
  let child := match m with
    | none => kwargs
    | some m => if kwargs.isEmpty then m else D.update m kwargs
  cmNew (child :: c.maps)

/-- `ChainMap.parents`, :1119-1122: `self.__class__(*self.maps[1:])`. -/
def cmParents (c : CMap κ ν) : CMap κ ν := cmNew c.maps.tail

/-- `ChainMap.__setitem__`, :1124-1125. -/
def cmSetitem (c : CMap κ ν) (k : κ) (v : ν) : Py (CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | m :: t => .ok ⟨D.set m k v :: t⟩

/-- The `KeyError` of `__delitem__` and `pop`, :1131, :1145. -/
def notInFirst (rk : κ → String) (k : κ) : PyExc :=
  keyErrorStr ("Key not found in the first mapping: " ++ rk k)

/-- `ChainMap.__delitem__`, :1127-1131. -/
def cmDelitem (rk : κ → String) (c : CMap κ ν) (k : κ) : Py (CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | m :: t => if D.mem m k then .ok ⟨D.del m k :: t⟩ else .error (notInFirst rk k)

/-- `ChainMap.popitem`, :1133-1138. -/
def cmPopitem (c : CMap κ ν) : Py ((κ × ν) × CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | m :: t =>
    match D.popitem? m with
    | some (p, m') => .ok (p, ⟨m' :: t⟩)
    | none => .error (keyErrorStr "No keys found in the first mapping.")

/-- `ChainMap.pop`, :1140-1145: `dict.pop(key, *args)` on `maps[0]`. -/
def cmPop (rk : κ → String) (c : CMap κ ν) (k : κ) (default : Option ν) : Py (ν × CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | m :: t =>
    match D.get? m k, default with
    | some v, _ => .ok (v, ⟨D.del m k :: t⟩)
    | none, some d => .ok (d, c)
    | none, none => .error (notInFirst rk k)

/-- `ChainMap.clear`, :1147-1149. -/
def cmClear (c : CMap κ ν) : Py (CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | _ :: t => .ok ⟨[] :: t⟩

/-- `ChainMap.__ior__`, :1151-1153, on a mapping's items. -/
def cmIor (c : CMap κ ν) (other : List (κ × ν)) : Py (CMap κ ν) :=
  match c.maps with
  | [] => .error noMap
  | m :: t => .ok ⟨D.update m other :: t⟩

/-- `ChainMap.__or__`, :1155-1160; `none` is `NotImplemented`. -/
def cmOr (c : CMap κ ν) (other : Option (List (κ × ν))) : Option (Py (CMap κ ν)) :=
  other.map (fun o => do
    let r ← cmCopy c
    cmIor r o)

/-- `ChainMap.__ror__`, :1162-1168. -/
def cmRor (c : CMap κ ν) (other : Option (D κ ν)) : Option (CMap κ ν) :=
  other.map (fun o =>
    let m := c.maps.reverse.foldl D.update (D.update [] o)
    cmNew [m])

/-- `dict(chainmap)` as a flat dict: earlier maps win, last map's keys come first. -/
def flat : List (D κ ν) → D κ ν
  | [] => []
  | m :: t => D.update (flat t) m

end PyLean.CoreLibs.Coll
