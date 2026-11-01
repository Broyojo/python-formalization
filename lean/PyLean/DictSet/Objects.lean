import PyLean.DictSet.Views

/-!
The concrete objects the differential test instantiates the generic models with. Each
object arrives with its hash and its equality class, computed by the running CPython, so
randomised string hashes and float hashing need no model of their own.
-/

namespace PyLean.DictSet

open PyLean

/-- One object of a test's pool. -/
structure Atom where
  uid : Nat
  /-- Equality class: `==` holds between atoms of one class. -/
  cls : Nat
  hash : Int
  /-- 0: hashable; 1: `TypeError` from `hash()`; 2: `hash()` raises `ValueError`. -/
  hkind : Nat := 0
  isStr : Bool := false
  isStrLike : Bool := false
  /-- `__eq__` raises `ValueError('eq')`. -/
  raises : Bool := false
  /-- `__eq__` mutates the container: 1 clears it, 2 pops an item. -/
  act : Nat := 0
  rep : String := ""
  tname : String := ""
  /-- For a `set` object: the hash of the equal frozenset. -/
  fs : Option Int := none
  deriving DecidableEq, Repr, Inhabited

/-- A pool object, or a pair built by the items views. -/
inductive DObj where
  | atom (a : Atom)
  | tuple (a b : DObj)
  deriving DecidableEq, Repr, Inhabited

namespace DObj

/-- `tuple_hash` (`Objects/tupleobject.c`) of a pair. -/
def tupleHash (a b : Int) : Int :=
  let p1 : Nat := 11400714785074694791
  let p2 : Nat := 14029467366897019727
  let p5 : Nat := 2870177450012600261
  let m : Nat := 2 ^ 64
  let rot (x : Nat) : Nat := ((x <<< 31) % m) ||| (x >>> 33)
  let lane (acc v : Nat) : Nat := (rot ((acc + v * p2) % m) * p1) % m
  let acc := lane (lane p5 (toU64 a)) (toU64 b)
  let acc := (acc + (2 ^^^ (p5 ^^^ 3527539))) % m
  if acc == m - 1 then 1546275796 else toI64 acc

def hash : DObj → Py Int
  | .atom a =>
    match a.hkind with
    | 0 => .ok a.hash
    | 1 => .error (.typeError s!"unhashable type: '{a.tname}'")
    | _ => .error (.valueError "hash")
  | .tuple a b =>
    match hash a with
    | .error e => .error e
    | .ok ha =>
      match hash b with
      | .error e => .error e
      | .ok hb => .ok (tupleHash ha hb)

/-- `PyObject_RichCompareBool(a, b, Py_EQ)` without side effects. -/
def eq (x y : DObj) : Py Bool :=
  if x = y then .ok true else
  match x, y with
  | .atom a, .atom b =>
    if a.raises || b.raises then .error (.valueError "eq") else .ok (a.cls == b.cls)
  | .tuple a b, .tuple c d =>
    match eq a c with
    | .error e => .error e
    | .ok false => .ok false
    | .ok true => eq b d
  | _, _ => .ok false

/-- Which mutation `x == y` performs. -/
def action : DObj → DObj → Nat
  | .atom a, .atom b => if a.act != 0 then a.act else b.act
  | _, _ => 0

def isStr : DObj → Bool
  | .atom a => a.isStr
  | _ => false
def isStrLike : DObj → Bool
  | .atom a => a.isStrLike
  | _ => false
def strEq : DObj → DObj → Bool
  | .atom a, .atom b => a.cls == b.cls
  | _, _ => false
def reprStr : DObj → String
  | .atom a => a.rep
  | .tuple a b => s!"({reprStr a}, {reprStr b})"
def typeName : DObj → String
  | .atom a => a.tname
  | .tuple _ _ => "tuple"
/-- `PySet_Check(key) ? frozenset_hash_impl(key)`. -/
def setHash : DObj → Option Int
  | .atom a => a.fs
  | _ => none
def uid : DObj → Nat
  | .atom a => a.uid
  | _ => 0

end DObj

def dKeyOps : KeyOps DObj :=
  { hash := DObj.hash, isStr := DObj.isStr, isStrLike := DObj.isStrLike, strEq := DObj.strEq
    reprStr := DObj.reprStr, repr := fun k => .ok k.reprStr, typeName := DObj.typeName }

abbrev DD := PyDict DObj DObj
abbrev DS := SetObj DObj

/-- `__eq__` on a key whose comparison may clear or pop from the dict being probed. -/
def dProto : Proto DObj DD :=
  { dKeyOps with
    eq := fun a b s =>
      match DObj.action a b with
      | 1 => (.ok false, dictClear s)
      | 2 =>
        match dictPopitem s with
        | (_, s') => (.ok false, s')
      | _ => (DObj.eq a b, s) }

def sProto : Proto DObj DS :=
  { dKeyOps with
    eq := fun a b s =>
      match DObj.action a b with
      | 1 => (.ok false, setClearInternal s)
      | 2 =>
        match setPop s with
        | (_, s') => (.ok false, s')
      | _ => (DObj.eq a b, s) }

def dEnv : Env DObj DObj :=
  { D := dProto
    S := sProto
    pair := DObj.tuple
    unpair := fun
      | .tuple a b => some (a, b)
      | _ => none
    veq := DObj.eq
    vrepr := fun k => .ok k.reprStr }

end PyLean.DictSet
