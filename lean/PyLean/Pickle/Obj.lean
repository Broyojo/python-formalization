import PyLean.Pickle.Long
import PyLean.Pickle.Value

/-!
Objects built by the unpicklers, and the Python object operations they call
(`dict.__setitem__`, `set.add`, `list.append`, `frozenset(...)`, hashing,
`==`). Mutable objects (list, dict, set, bytearray) live in a heap and are
referenced by address, so that a memoized list sees later `APPEND`s.
-/

namespace PyLean.Pickle

open PyLean

inductive DV where
  | none
  | bool (b : Bool)
  | int (i : Int)
  | str (s : List Nat)
  | bytes (b : Bytes)
  | tuple (xs : List DV)
  | frozenset (xs : List DV)
  /-- A mutable object in the heap. -/
  | ref (a : Nat)
  | glob (g : Glob)
  deriving Repr, Inhabited

inductive HObj where
  | list (xs : List DV)
  | dict (kvs : List (DV × DV))
  | set (xs : List DV)
  | bytearray (b : Bytes)
  deriving Repr, Inhabited

abbrev Heap := List HObj

def HObj.typeName : HObj → String
  | .list _ => "list"
  | .dict _ => "dict"
  | .set _ => "set"
  | .bytearray _ => "bytearray"

def DV.typeName (h : Heap) : DV → String
  | .none => "NoneType"
  | .bool _ => "bool"
  | .int _ => "int"
  | .str _ => "str"
  | .bytes _ => "bytes"
  | .tuple _ => "tuple"
  | .frozenset _ => "frozenset"
  | .ref a => match h[a]? with
    | some o => o.typeName
    | Option.none => "?"
  | .glob .codecsEncode => "builtin_function_or_method"
  | .glob _ => "type"

mutual
/-- `hash(v)` fails with this type name, or `none` if `v` is hashable. -/
def unhashableIn (h : Heap) : DV → Option String
  | .ref a => some ((DV.ref a).typeName h)
  | .tuple xs => unhashableInList h xs
  | _ => none
def unhashableInList (h : Heap) : List DV → Option String
  | [] => none
  | x :: xs => match unhashableIn h x with
    | some t => some t
    | none => unhashableInList h xs
end

mutual
/-- `a == b` for hashable values (`int`/`bool` compare by value). -/
def pyEq : DV → DV → Bool
  | .none, .none => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .bool a, .int b => (if a then 1 else 0) == b
  | .int a, .bool b => a == (if b then 1 else 0)
  | .str a, .str b => a == b
  | .bytes a, .bytes b => a == b
  | .tuple xs, .tuple ys => pyEqList xs ys
  | .frozenset xs, .frozenset ys => xs.length == ys.length && subsetOf xs ys
  | .glob a, .glob b => a == b
  | .ref a, .ref b => a == b
  | _, _ => false
def pyEqList : List DV → List DV → Bool
  | [], [] => true
  | x :: xs, y :: ys => pyEq x y && pyEqList xs ys
  | _, _ => false
/-- Every element of the first list equals some element of the second. -/
def subsetOf : List DV → List DV → Bool
  | [], _ => true
  | x :: xs, ys => memEq x ys && subsetOf xs ys
def memEq (x : DV) : List DV → Bool
  | [] => false
  | y :: ys => pyEq x y || memEq x ys
end

def unhashableMsg (h : Heap) (k : DV) (what : String) (inner : String) : PyExc :=
  .typeError s!"cannot use '{k.typeName h}' as {what} (unhashable type: '{inner}')"

/-- `d[k] = v` on a dict's items: an equal key keeps its original object. -/
def dictInsert (kvs : List (DV × DV)) (k v : DV) : List (DV × DV) :=
  if kvs.any (fun p => pyEq p.1 k) then kvs.map (fun p => if pyEq p.1 k then (p.1, v) else p)
  else kvs ++ [(k, v)]

def setInsert (xs : List DV) (x : DV) : List DV :=
  if memEq x xs then xs else xs ++ [x]

/-- `PyDict_SetItem` / `dict.__setitem__` with hashing. -/
def dictSet (h : Heap) (kvs : List (DV × DV)) (k v : DV) : Py (List (DV × DV)) :=
  match unhashableIn h k with
  | some t => .error (unhashableMsg h k "a dict key" t)
  | none => .ok (dictInsert kvs k v)

/-- `set.add` / `set.update` one element. -/
def setAdd (h : Heap) (xs : List DV) (x : DV) : Py (List DV) :=
  match unhashableIn h x with
  | some t => .error (unhashableMsg h x "a set element" t)
  | none => .ok (setInsert xs x)

def setAddAll (h : Heap) (xs : List DV) : List DV → Py (List DV)
  | [] => .ok xs
  | y :: ys => do setAddAll h (← setAdd h xs y) ys

/-- `frozenset(items)` / `PyFrozenSet_New`. -/
def mkFrozenset (h : Heap) (items : List DV) : Py DV := .frozenset <$> setAddAll h [] items

def Heap.get (h : Heap) (a : Nat) : HObj := h.getD a (.list [])
def Heap.set (h : Heap) (a : Nat) (o : HObj) : Heap := List.set h a o
def Heap.alloc (h : Heap) (o : HObj) : Heap × DV := (h ++ [o], .ref h.length)

/-- `operator.index(k)` for a list/bytearray subscript. -/
def indexOf (h : Heap) (what : String) (k : DV) : Py Int :=
  match k with
  | .int i => if i < ssizeMin ∨ i > ssizeMax then .error (.indexError "cannot fit 'int' into an index-sized integer") else .ok i
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error (.typeError s!"{what} indices must be integers or slices, not {k.typeName h}")

/-- The int value `bytearray` stores (`_getbytevalue`). -/
def byteValue (h : Heap) (v : DV) : Py UInt8 :=
  match v with
  | .int i => if 0 ≤ i ∧ i < 256 then .ok i.toNat.toUInt8 else .error (.valueError "byte must be in range(0, 256)")
  | .bool b => .ok (if b then 1 else 0)
  | _ => .error (.typeError s!"'{v.typeName h}' object cannot be interpreted as an integer")

/-- `obj[k] = v` (`PyObject_SetItem`). -/
def setItem (h : Heap) (obj k v : DV) : Py Heap :=
  match obj with
  | .ref a => match h.get a with
    | .dict kvs => do return h.set a (.dict (← dictSet h kvs k v))
    | .list xs => do
      let i ← indexOf h "list" k
      let j := if i < 0 then i + xs.length else i
      if j < 0 ∨ j ≥ xs.length then .error (.indexError "list assignment index out of range")
      else return h.set a (.list (xs.set j.toNat v))
    | .bytearray b => do
      let i ← indexOf h "bytearray" k
      let bv ← byteValue h v
      let j := if i < 0 then i + b.length else i
      if j < 0 ∨ j ≥ b.length then .error (.indexError "bytearray index out of range")
      else return h.set a (.bytearray (b.set j.toNat bv))
    | .set _ => .error (.typeError "'set' object does not support item assignment")
  | .glob _ => .error (excluded "global as SETITEM target")
  | _ => .error (.typeError s!"'{obj.typeName h}' object does not support item assignment")

/-- `list.append(v)` (or `bytearray.append`). -/
def appendTo (h : Heap) (obj v : DV) : Py Heap :=
  match obj with
  | .ref a => match h.get a with
    | .list xs => .ok (h.set a (.list (xs ++ [v])))
    | .bytearray b => do return h.set a (.bytearray (b ++ [← byteValue h v]))
    | o => .error (attributeError s!"'{o.typeName}' object has no attribute 'append'")
  | .glob _ => .error (excluded "global as APPEND target")
  | _ => .error (attributeError s!"'{obj.typeName h}' object has no attribute 'append'")

/-- `bytearray.extend(items)`: all items are converted before any is added. -/
def bytesOfItems (h : Heap) : List DV → Py Bytes
  | [] => .ok []
  | v :: vs => do return (← byteValue h v) :: (← bytesOfItems h vs)

/-- Does `obj` have an `extend` method? -/
def hasExtend (h : Heap) : DV → Bool
  | .ref a => match h.get a with
    | .list _ | .bytearray _ => true
    | _ => false
  | _ => false

/-- `obj.extend(items)` for an object that has `extend`. -/
def extendObj (h : Heap) (obj : DV) (items : List DV) : Py Heap :=
  match obj with
  | .ref a => match h.get a with
    | .list xs => .ok (h.set a (.list (xs ++ items)))
    | .bytearray b => do return h.set a (.bytearray (b ++ (← bytesOfItems h items)))
    | _ => .ok h
  | _ => .ok h

/-- Call `append` for each item in turn. -/
def appendEach (h : Heap) (obj : DV) : List DV → Py Heap
  | [] => .ok h
  | v :: vs => do appendEach (← appendTo h obj v) obj vs

/-- `set_obj.add` looked up on an object that is not a `set`. -/
def noAdd (h : Heap) (obj : DV) : PyExc :=
  match obj with
  | .glob _ => excluded "global as ADDITEMS target"
  | _ => attributeError s!"'{obj.typeName h}' object has no attribute 'add'"

def isSetRef (h : Heap) : DV → Bool
  | .ref a => match h.get a with
    | .set _ => true
    | _ => false
  | _ => false

/-- `set.update(items)` on a heap set. -/
def setUpdate (h : Heap) (obj : DV) (items : List DV) : Py Heap :=
  match obj with
  | .ref a => match h.get a with
    | .set xs => do return h.set a (.set (← setAddAll h xs items))
    | _ => .ok h
  | _ => .ok h

/-- Calling one of the five globals (`REDUCE`), as the round trip needs. -/
def callGlob (h : Heap) (g : Glob) (args : List DV) : Py (Heap × DV) :=
  match g, args with
  | .codecsEncode, [.str s, .str l] =>
    if l = (ascii "latin1").map (·.toNat) then
      if s.all (· < 256) then .ok (h, .bytes (s.map (·.toUInt8)))
      else .error (.named "UnicodeEncodeError" "~'latin-1' codec can't encode")
    else .error (excluded "codecs.encode encoding")
  | .bytes, [] => .ok (h, .bytes [])
  | .bytearray, [] => .ok (h.alloc (.bytearray []))
  | .bytearray, [.bytes b] => .ok (h.alloc (.bytearray b))
  | .set, [.ref a] => match h.get a with
    | .list xs => do
      let s ← setAddAll h [] xs
      return h.alloc (.set s)
    | _ => .error (excluded "set argument")
  | .frozenset, [.ref a] => match h.get a with
    | .list xs => do return (h, ← mkFrozenset h xs)
    | _ => .error (excluded "frozenset argument")
  | _, _ => .error (excluded "call")

/-- `find_class(module, name)` restricted to the five globals; with
`fix_imports` and protocol < 3, `__builtin__` is `builtins`
(`_compat_pickle.IMPORT_MAPPING`). -/
def findGlob (proto : Nat) (module name : List Nat) : Py Glob :=
  let m := if proto < 3 ∧ module = (ascii "__builtin__").map (·.toNat) then (ascii "builtins").map (·.toNat) else module
  let gs := [Glob.codecsEncode, .bytes, .bytearray, .set, .frozenset]
  match gs.find? (fun g => (ascii g.module).map (·.toNat) = m ∧ (ascii g.name).map (·.toNat) = name) with
  | some g => .ok g
  | none => .error (excluded "find_class")

end PyLean.Pickle
