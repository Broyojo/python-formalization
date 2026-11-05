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
  /-- 0: hashable; 1: `TypeError` from `hash()`; 2: `hash()` raises `ValueError`; 3: it clears the
  target dict, then raises `ValueError`. -/
  hkind : Nat := 0
  isStr : Bool := false
  isStrLike : Bool := false
  /-- `__eq__` raises `ValueError('eq')`. -/
  raises : Bool := false
  /-- `__eq__` mutates a dict: 1 clears it, 2 pops an item, `10 + i` pops an item and stores its
  value under pool object `i`, which keeps the number of items. -/
  act : Nat := 0
  rep : String := ""
  tname : String := ""
  /-- For a `set` object: the hash of the equal frozenset. -/
  fs : Option Int := none
  /-- Not equal to itself. -/
  nan : Bool := false
  /-- `__repr__` does to the target dict what `act` would, then answers `rep`. -/
  ract : Nat := 0
  /-- `__eq__` raises `KESub("eq")`, a subclass of `KeyError`, instead of `ValueError('eq')`. -/
  rk : Bool := false
  /-- `__hash__` first does `evil_act` number `hact` to the target set (`KH`, `SH` in the test). -/
  hact : Nat := 0
  /-- What that `__hash__` then does: 0 answers `hash`, 1 raises `TypeError("no")`, 2 raises
  `TESub("te")` (a subclass of `TypeError`), 3 raises `ValueError("hv")`. -/
  hres : Nat := 0
  /-- For a `set` object (`PySet_Check`): its elements, distinct ints added in this order. -/
  sbody : Option (List Int) := none
  deriving DecidableEq, Repr, Inhabited

/-- What `a == b` raises when one of them raises: the left operand's `__eq__` runs first. -/
def Atom.eqExc (a b : Atom) : PyExc :=
  let r := if a.raises then a else b
  if r.rk then .named "KESub" "'eq'" else .valueError "eq"

/-- `PyErr_GivenExceptionMatches(e, PyExc_KeyError)` for what the test objects raise. -/
def isKeyErrorTest (e : PyExc) : Bool :=
  isKeyErrorExact e || e == .named "KESub" "'eq'"

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
    if a.raises || b.raises then .error (Atom.eqExc a b) else .ok (a.cls == b.cls)
  | .tuple a b, .tuple c d =>
    match eq a c with
    | .error e => .error e
    | .ok false => .ok false
    | .ok true => eq b d
  | _, _ => .ok false

/-- `operator.eq`: no identity shortcut (an object not equal to itself stays unequal). -/
def plainEq (x y : DObj) : Py Bool :=
  match x, y with
  | .atom a, .atom b =>
    if a.raises || b.raises then .error (Atom.eqExc a b)
    else .ok (a.cls == b.cls && !a.nan && !b.nan)
  | _, _ => eq x y

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
/-- What `repr(x)` does to the target dict. -/
def reprAct : DObj → Nat
  | .atom a => a.ract
  | _ => 0

end DObj

def dKeyOps : KeyOps DObj :=
  { hash := DObj.hash, isStr := DObj.isStr, isStrLike := DObj.isStrLike, strEq := DObj.strEq
    reprStr := DObj.reprStr, repr := fun k => .ok k.reprStr, typeName := DObj.typeName }

abbrev DD := PyDict DObj DObj
abbrev DS := SetObj DObj

/-- `__hash__` clears the dict before it raises (the test's `HClear`, `hkind` 3). -/
def DObj.hashClears : DObj → Bool
  | .atom a => a.hkind == 3
  | _ => false

/-- `__eq__` on a key whose comparison may clear or pop from the dict being probed, and `__hash__`
that may clear it. -/
def dProto : Proto DObj DD :=
  { dKeyOps with
    hashEff := fun k s => if k.hashClears then dictClear s else s
    eq := fun a b s =>
      match DObj.action a b with
      | 1 => (.ok false, dictClear s)
      | 2 =>
        match dictPopitem s with
        | (_, s') => (.ok false, s')
      | _ => (DObj.eq a b, s) }

/-- A comparison with no side effect, for the insertion inside `evilAct`. -/
def plainProto : Proto DObj DD :=
  { dKeyOps with eq := fun a b s => (DObj.eq a b, s) }

/-- What `evil_act` in the test does to a dict. -/
def evilAct (pool : Array DObj) (n : Nat) (t : DD) : DD :=
  match n with
  | 0 => t
  | 1 => dictClear t
  | 2 => (dictPopitem t).2
  | n =>
    match dictPopitem t with
    | (.ok (_, v), t') => (dictSetItem plainProto pool[n - 10]! v t').2
    | (.error _, t') => t'

/-- `KEvil.__eq__` answers `False`, or raises once it has acted if the key is flagged so. -/
def evilAnswer (a b : DObj) : Py Bool :=
  match a, b with
  | .atom x, .atom y => if x.raises || y.raises then .error (Atom.eqExc x y) else .ok false
  | _, _ => .ok false

/-- `__eq__` acting on the dict being probed. -/
def selfProto (pool : Array DObj) : Proto DObj DD :=
  { dKeyOps with
    eq := fun a b s =>
      match DObj.action a b with
      | 0 => (DObj.eq a b, s)
      | n => (evilAnswer a b, evilAct pool n s) }

/-- `__eq__` acting on the other dict: the source, while a merge runs. -/
def peerProto (pool : Array DObj) : Proto DObj DD :=
  { dKeyOps with
    eq := fun a b s =>
      match DObj.action a b with
      | 0 => (DObj.eq a b, s)
      | n =>
        (evilAnswer a b,
         match s.peer with
         | some p => { s with peer := some (evilAct pool n p.toDict).toPeer }
         | none => s) }

/-- A comparison with no side effect, for the insertion inside `evilSet`. -/
def plainSet : Proto DObj DS :=
  { dKeyOps with eq := fun a b s => (DObj.eq a b, s) }

/-- `PyErr_ExceptionMatches(PyExc_TypeError)` for what the test objects raise: `TESub` is the test's
subclass of `TypeError`. -/
def isTypeErrorTest (e : PyExc) : Bool :=
  match e with
  | .typeError _ => true
  | .named "TESub" _ => true
  | _ => false

/-- What a `KH` or `SH` `__hash__` answers once it has acted. -/
def hookAnswer (a : Atom) : Py Int :=
  match a.hres with
  | 0 => .ok a.hash
  | 1 => .error (.typeError "no")
  | 2 => .error (.named "TESub" "te")
  | _ => .error (.valueError "hv")

/-- The body of a set of distinct ints, built as `set(l)` builds it. Its elements stand in for the
ints: only their hashes and the counts reach `frozenset_hash_impl`. -/
def intSetBody (l : List Int) : SetBody DObj :=
  let step := fun (p : DS × Nat) (h : Int) =>
    let k := DObj.atom { uid := 1000000000 + p.2, cls := 1000000000 + p.2, hash := h }
    ((setAddEntry plainSet k h p.1).2, p.2 + 1)
  (l.foldl step (({} : DS), 0)).1.toSetBody

/-- `PySet_Check(key)` and the key's body: the test's set keys are never changed. -/
def testKeySet (k : DObj) (_ : DS) : Option (SetBody DObj) :=
  match k with
  | .atom a => a.sbody.map intSetBody
  | _ => none

def sProto : Proto DObj DS :=
  { dKeyOps with
    isTypeError := isTypeErrorTest
    hashM := fun k s =>
      match k with
      | .atom a => if a.hres == 0 then (DObj.hash k, s) else (hookAnswer a, s)
      | _ => (DObj.hash k, s)
    eq := fun a b s =>
      match DObj.action a b with
      | 1 => (.ok false, setClearInternal s)
      | 2 =>
        match setPop s with
        | (_, s') => (.ok false, s')
      | _ => (DObj.eq a b, s) }

/-- What `evil_act` in the test does to a set. -/
def evilSet (pool : Array DObj) (n : Nat) (t : DS) : DS :=
  match n with
  | 0 => t
  | 1 => setClearInternal t
  | 2 => (setPop t).2
  | n =>
    match setPop t with
    | (.ok _, t') => (setAddKey plainSet pool[n - 10]! t').2
    | (.error _, t') => t'

/-- `__eq__` acting on the set with this identity, wherever it is in the state. -/
def sProtoAt (pool : Array DObj) (id : Nat) : Proto DObj DS :=
  { dKeyOps with
    isTypeError := isTypeErrorTest
    hashM := fun k s =>
      match k with
      | .atom a =>
        if a.hres == 0 && a.hact == 0 then (DObj.hash k, s)
        else
          let s' := if s.ident == id || s.peers.any (·.ident == id) then
              (evilSet pool a.hact (s.swapIn id)).swapIn s.ident
            else s
          (if a.hres == 0 then .ok a.hash else hookAnswer a, s')
      | _ => (DObj.hash k, s)
    eq := fun a b s =>
      match DObj.action a b with
      | 0 => (DObj.eq a b, s)
      | n =>
        (evilAnswer a b,
         if s.ident == id || s.peers.any (·.ident == id) then
           (evilSet pool n (s.swapIn id)).swapIn s.ident
         else s) }

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
