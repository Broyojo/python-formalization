import PyLean.Core

/-!
`Lib/abc.py` (CPython 3.14.7), which is a thin class over `Modules/_abc.c`: `ABCMeta.__new__`, `register`,
`__instancecheck__` and `__subclasscheck__` each make one call into C. The C functions are mirrored, with the
three weak sets and the global invalidation counter, and with hooks that can raise.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- What `__subclasshook__` returns. -/
inductive HookRet where
  | tru | fals | notImplemented
  /-- Anything else. -/
  | other
  deriving Repr, DecidableEq

/-- A class hierarchy. `hook cls sub` is `cls.__subclasshook__(sub)`. `isAbc c` says that `issubclass(_, c)` goes
through `ABCMeta`; for another class it is the plain type test. -/
structure AbcWorld where
  hook : Nat → Nat → Py HookRet
  mro : Nat → List Nat
  subclasses : Nat → List Nat
  isAbc : Nat → Bool

/-- `_abc_data`, Modules/_abc.c:42-50. -/
structure AbcData where
  registry : List Nat := []
  cache : List Nat := []
  neg : List Nat := []
  version : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- All the ABCs' data, and `abc_invalidation_counter`. -/
structure AbcState where
  data : List (Nat × AbcData) := []
  counter : Nat := 0
  deriving Repr, DecidableEq

def AbcState.get (s : AbcState) (c : Nat) : AbcData := (s.data.lookup c).getD {}

def AbcState.put (s : AbcState) (c : Nat) (d : AbcData) : AbcState :=
  { s with data := (c, d) :: s.data }

/-- `_add_to_weak_set` on the positive cache. -/
def addCache (s : AbcState) (c sub : Nat) : AbcState :=
  let d := s.get c
  s.put c { d with cache := sub :: d.cache }

def addNeg (s : AbcState) (c sub : Nat) : AbcState :=
  let d := s.get c
  s.put c { d with neg := sub :: d.neg }

mutual
  /-- `_abc__abc_subclasscheck_impl`, Modules/_abc.c:705-842, after the class check of the argument. -/
  def subCheck (W : AbcWorld) : Nat → Nat → Nat → AbcState → Py Bool × AbcState
    | 0, _, _, s => (.error .modelFuel, s)
    | fuel + 1, cls, sub, s =>
      let d := s.get cls
      if sub ∈ d.cache then (.ok true, s) else
      let afterNeg (s : AbcState) : Py Bool × AbcState :=
        match W.hook cls sub with
        | .error e => (.error e, s)
        | .ok .tru => (.ok true, addCache s cls sub)
        | .ok .fals => (.ok false, addNeg s cls sub)
        | .ok .other =>
          (.error (.assertionError
            "__subclasshook__ must return either False, True, or NotImplemented"), s)
        | .ok .notImplemented =>
          if cls ∈ W.mro sub then (.ok true, addCache s cls sub)
          else if sub ∈ (s.get cls).registry then (.ok true, s)  -- `subclasscheck_check_registry`, fast path
          else
            match anySub W fuel sub (s.get cls).registry s with
            | (.error e, s) => (.error e, s)
            | (.ok true, s) => (.ok true, addCache s cls sub)
            | (.ok false, s) =>
              match anySub W fuel sub (W.subclasses cls) s with
              | (.error e, s) => (.error e, s)
              | (.ok true, s) => (.ok true, addCache s cls sub)
              | (.ok false, s) => (.ok false, addNeg s cls sub)
      if d.version < s.counter then
        afterNeg (s.put cls { d with neg := [], version := s.counter })
      else if sub ∈ d.neg then (.ok false, s)
      else afterNeg s

  /-- `PyObject_IsSubclass(sub, x)` over a list, stopping at the first true or the first failure: the loops of
  `subclasscheck_check_registry`, :845-905, and step 6 of the check, :806-830. -/
  def anySub (W : AbcWorld) : Nat → Nat → List Nat → AbcState → Py Bool × AbcState
    | 0, _, _, s => (.error .modelFuel, s)
    | _ + 1, _, [], s => (.ok false, s)
    | fuel + 1, sub, x :: xs, s =>
      if W.isAbc x then
        match subCheck W fuel x sub s with
        | (.error e, s) => (.error e, s)
        | (.ok true, s) => (.ok true, s)
        | (.ok false, s) => anySub W fuel sub xs s
      else if x ∈ W.mro sub then (.ok true, s)
      else anySub W fuel sub xs s
end

/-- `_abc__abc_subclasscheck_impl` with its first test: `issubclass(1, C)`. -/
def subclassCheck (W : AbcWorld) (fuel cls : Nat) (sub : Option Nat) (s : AbcState) : Py Bool × AbcState :=
  match sub with
  | none => (.error (.typeError "issubclass() arg 1 must be a class"), s)
  | some c => subCheck W fuel cls c s

/-- `PyObject_IsSubclass(a, b)`. -/
def isSubclass (W : AbcWorld) (fuel a b : Nat) (s : AbcState) : Py Bool × AbcState :=
  if W.isAbc b then subCheck W fuel b a s else (.ok (decide (b ∈ W.mro a)), s)

/-- `_abc__abc_register_impl`, Modules/_abc.c:556-606, and `ABCMeta.register`, Lib/abc.py:110-115. The result is
the subclass, as a class decorator wants. The `Py_TPFLAGS_SEQUENCE` copy at :590-598 only affects `match`. -/
def register (W : AbcWorld) (fuel cls : Nat) (sub : Option Nat) (s : AbcState) : Py Nat × AbcState :=
  match sub with
  | none => (.error (.typeError "Can only register classes"), s)
  | some c =>
    match isSubclass W fuel c cls s with
    | (.error e, s) => (.error e, s)
    | (.ok true, s) => (.ok c, s)
    | (.ok false, s) =>
      match isSubclass W fuel cls c s with
      | (.error e, s) => (.error e, s)
      | (.ok true, s) => (.error (.named "RuntimeError" "Refusing to create an inheritance cycle"), s)
      | (.ok false, s) =>
        let d := s.get cls
        (.ok c, { s.put cls { d with registry := c :: d.registry } with counter := s.counter + 1 })

/-- `_abc__abc_instancecheck_impl`, Modules/_abc.c:619-692. `klass` is `instance.__class__`, which may raise, and
`subtype` is `type(instance)`. -/
def instanceCheck (W : AbcWorld) (fuel cls : Nat) (klass : Py Nat) (subtype : Nat) (s : AbcState) :
    Py Bool × AbcState :=
  match klass with
  | .error e => (.error e, s)
  | .ok k =>
    let d := s.get cls
    if k ∈ d.cache then (.ok true, s) else
    if subtype = k then
      if d.version = s.counter ∧ k ∈ d.neg then (.ok false, s)
      else subCheck W fuel cls k s
    else
      match subCheck W fuel cls k s with
      | (.error e, s) => (.error e, s)
      | (.ok true, s) => (.ok true, s)
      | (.ok false, s) => subCheck W fuel cls subtype s

/-- A value in a class, as the abstract method machinery reads it: `getattr(value, "__isabstractmethod__",
False)` followed by a truth test, which may raise. -/
abbrev IsAbs := Py Bool

/-- A class as `compute_abstract_methods` and `update_abstractmethods` read it. -/
structure AbsClass where
  /-- `cls.__dict__.items()`, with the abstractness of each value. -/
  own : List (String × IsAbs)
  /-- `base.__abstractmethods__` for each base, empty for a base without it. -/
  parents : List (List String)
  /-- The abstractness of `getattr(cls, name)`, `none` when the class has no such attribute. -/
  lookup : String → Option IsAbs

/-- Add the names whose test says so; the first failure stops it. -/
def absScan {β : Type} (name : β → String) (test : β → IsAbs) : List β → Py (List String)
  | [] => .ok []
  | x :: xs =>
    match test x with
    | .error e => .error e
    | .ok b =>
      match absScan name test xs with
      | .error e => .error e
      | .ok r => .ok (if b then name x :: r else r)

def inheritedScan (c : AbsClass) : List (List String) → Py (List String)
  | [] => .ok []
  | names :: rest =>
    match absScan id (fun n => (c.lookup n).getD (.ok false)) names with
    | .error e => .error e
    | .ok a =>
      match inheritedScan c rest with
      | .error e => .error e
      | .ok r => .ok (a ++ r)

/-- `compute_abstract_methods`, Modules/_abc.c:362-484, run by `ABCMeta.__new__`, Lib/abc.py:105-108: the class's
own items first, then what the bases list. -/
def computeAbstract (c : AbsClass) : Py (List String) :=
  match absScan Prod.fst Prod.snd c.own with
  | .error e => .error e
  | .ok a =>
    match inheritedScan c c.parents with
    | .error e => .error e
    | .ok b => .ok (a ++ b)

/-- `update_abstractmethods`, Lib/abc.py:146-181: the same two scans the other way round. `none` when the class has
no `__abstractmethods__`, which leaves it alone. -/
def updateAbstract (hasAbs : Bool) (c : AbsClass) : Py (Option (List String)) :=
  if !hasAbs then .ok none else
  match inheritedScan c c.parents with
  | .error e => .error e
  | .ok a =>
    match absScan Prod.fst Prod.snd c.own with
    | .error e => .error e
    | .ok b => .ok (some (a ++ b))

/-- `funcobj.__isabstractmethod__ = True`: the object gets the flag, unless the `setattr` fails, as on a builtin. -/
def markAbstract {α : Type} (fail : Option PyExc) (f : α) : Py (α × Bool) :=
  match fail with
  | some e => .error e
  | none => .ok (f, true)

/-- `abstractmethod`, Lib/abc.py:7-25, and `abstractclassmethod.__init__`, :43-45, and
`abstractstaticmethod.__init__`, :63-65, which set the flag and then call `super().__init__`, which accepts any
object: the wrapper is made only if the `setattr` passed. -/
def abstractWrap {α β : Type} (fail : Option PyExc) (wrap : α → β) (f : α) : Py β :=
  match markAbstract fail f with
  | .error e => .error e
  | .ok (g, _) => .ok (wrap g)

end PyLean.CoreLibs.Operator
