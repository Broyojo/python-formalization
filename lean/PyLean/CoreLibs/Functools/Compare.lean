import PyLean.CoreLibs.Functools.Model

/-!
`total_ordering` and `cmp_to_key`, Lib/functools.py and Modules/_functoolsmodule.c.

A comparison in Python returns an arbitrary object, so results here have an abstract type `ρ`, with a
truth test that may raise. `or` and `and` return one of their operands, not a Boolean, and the generated
methods keep that. `cmp_to_key` is two different programs: Python reads `.obj` from whatever `other` is,
C tests the exact type.
-/

namespace PyLean.CoreLibs.Functools

open PyLean

/-- A dunder's result: a value, or `NotImplemented`. -/
inductive Ret (α : Type) where
  | val (a : α)
  | notImplemented
  deriving Repr, DecidableEq, Inhabited

/-! ### `total_ordering` -/

/-- The four root comparisons, spelled as the method names. -/
inductive OrdOp where
  | lt | le | gt | ge
  deriving Repr, DecidableEq, Inhabited

def OrdOp.name : OrdOp → String
  | .lt => "__lt__"
  | .le => "__le__"
  | .gt => "__gt__"
  | .ge => "__ge__"

/-- The keys of `_convert`, in source order. -/
def ordOps : List OrdOp := [.lt, .le, .gt, .ge]

/-- The body shape of each generated method, Lib/functools.py:89-171. -/
inductive Shape where
  /-- `return not op_result and self != other` -/
  | notAndNe
  /-- `return op_result or self == other` -/
  | orEq
  /-- `return not op_result` -/
  | notOp
  /-- `return not op_result or self == other` -/
  | notOrEq
  /-- `return op_result and self != other` -/
  | andNe
  deriving Repr, DecidableEq

/-- `_convert`, Lib/functools.py:173-186. -/
def convert : OrdOp → List (OrdOp × Shape)
  | .lt => [(.gt, .notAndNe), (.le, .orEq), (.ge, .notOp)]
  | .le => [(.ge, .notOrEq), (.lt, .andNe), (.gt, .notOp)]
  | .gt => [(.lt, .notAndNe), (.ge, .orEq), (.le, .notOp)]
  | .ge => [(.le, .notOrEq), (.gt, .andNe), (.lt, .notOp)]

/-- What a generated method touches: `type(self).__root__(self, other)`, the operators `==` and `!=`
with their raw results, the truth test of a result, which may raise, and the two `bool`s. -/
structure OrdPrims (α ρ : Type) where
  root : α → α → Py (Ret ρ)
  eq : α → α → Py ρ
  ne : α → α → Py ρ
  truth : ρ → Py Bool
  ofBool : Bool → ρ

/-- One generated method, `_gt_from_lt` through `_lt_from_ge`, Lib/functools.py:89-171. The result of
`or` and `and` is an operand, so `op_result` itself or the raw `==` or `!=` result. -/
def derived {α ρ : Type} (P : OrdPrims α ρ) (s : Shape) (a b : α) : Py (Ret ρ) := do
  match ← P.root a b with
  | .notImplemented => pure .notImplemented
  | .val op =>
    match s with
    | .notAndNe =>
      if ← P.truth op then pure (.val (P.ofBool false)) else .val <$> P.ne a b
    | .orEq =>
      if ← P.truth op then pure (.val op) else .val <$> P.eq a b
    | .notOp => do pure (.val (P.ofBool (!(← P.truth op))))
    | .notOrEq =>
      if ← P.truth op then .val <$> P.eq a b else pure (.val (P.ofBool true))
    | .andNe =>
      if ← P.truth op then .val <$> P.ne a b else pure (.val op)

/-- A class as `total_ordering` reads and writes it. `attr o` is the identity of `getattr(cls, op, None)`,
found through the MRO, so an inherited comparison counts; `objectAttr o` is `getattr(object, op, None)`.
`setAttr` is `setattr(cls, opname, opfunc)`, which a metaclass may refuse; `opfunc` is known by its `Shape`. -/
structure OrdClass where
  attr : OrdOp → Py (Option Nat)
  objectAttr : OrdOp → Option Nat
  setAttr : OrdOp → Shape → Py Unit

/-- `{op for op in _convert if getattr(cls, op, None) is not getattr(object, op, None)}`,
Lib/functools.py:191. -/
def rootsOf (c : OrdClass) : List OrdOp → Py (List OrdOp)
  | [] => .ok []
  | o :: os => do
    let a ← c.attr o
    let rest ← rootsOf c os
    pure (if a != c.objectAttr o then o :: rest else rest)

/-- `max(roots)`, Lib/functools.py:194, on the method names as strings. -/
def maxRoot (roots : List OrdOp) : Option OrdOp :=
  if .lt ∈ roots then some .lt
  else if .le ∈ roots then some .le
  else if .gt ∈ roots then some .gt
  else if .ge ∈ roots then some .ge
  else none

/-- `for opname, opfunc in _convert[root]: if opname not in roots: setattr(...)`,
Lib/functools.py:195-198: the methods added, each with its function, stopping at the first refused `setattr`.
`opfunc.__name__ = opname` at :197 writes to the shared function; a generated method has the name of its slot. -/
def addMissing (c : OrdClass) (roots : List OrdOp) : List (OrdOp × Shape) → Py (List (OrdOp × Shape))
  | [] => .ok []
  | (o, s) :: rest =>
    if o ∈ roots then addMissing c roots rest
    else do
      c.setAttr o s
      let more ← addMissing c roots rest
      pure ((o, s) :: more)

/-- `total_ordering(cls)`, Lib/functools.py:188-199: the root and the methods added. -/
def totalOrdering (c : OrdClass) : Py (OrdOp × List (OrdOp × Shape)) := do
  let roots ← rootsOf c ordOps
  match maxRoot roots with
  | none => throw (.valueError "must define at least one ordering operation: < > <= >=")
  | some root =>
    let added ← addMissing c roots (convert root)
    pure (root, added)

/-! ### `cmp_to_key` -/

inductive CmpOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq, Inhabited

/-- What the key's comparison does with the result `res` of `mycmp`: `res op 0`, an arbitrary object
that may raise, and the truth test `object.__ne__` applies. -/
structure KeyOps (ρ τ : Type) where
  cmp0 : ρ → CmpOp → Py τ
  truth : τ → Py Bool
  ofBool : Bool → τ

/-- The right operand of a comparison of key objects. -/
inductive KeyOther (α : Type) where
  /-- A key object of this `cmp_to_key`, with its `obj`, or none for one that has not got one. -/
  | key (obj : Option α)
  /-- Another object with an `obj` attribute. -/
  | duck (obj : α)
  /-- An object without `obj`. -/
  | plain
  deriving Repr, DecidableEq

def noObjAttr : PyExc := .named "AttributeError" "~object has no attribute 'obj'"

/-- `K.__lt__` and siblings, Lib/functools.py:212-221: `mycmp(self.obj, other.obj) < 0`, reading `.obj`
from whatever `other` is. `__ne__` is not defined, so it is `object.__ne__`, the negation of the truth
of `__eq__`. -/
def keyComparePy {α ρ τ : Type} (K : KeyOps ρ τ) (mycmp : α → α → Py ρ) (op : CmpOp)
    (x : Option α) (other : KeyOther α) : Py τ := do
  let a ← match x with
    | some a => pure a
    | none => throw noObjAttr
  let b ← match other with
    | .key (some b) | .duck b => pure b
    | .key none | .plain => throw noObjAttr
  let r ← mycmp a b
  match op with
  | .ne => do
    let e ← K.cmp0 r .eq
    pure (K.ofBool (!(← K.truth e)))
  | _ => K.cmp0 r op

/-- `keyobject_richcompare`, Modules/_functoolsmodule.c:912-943: the exact-type test comes first, and
`res op 0` is one `PyObject_RichCompare`. -/
def keyCompareC {α ρ τ : Type} (K : KeyOps ρ τ) (mycmp : α → α → Py ρ) (op : CmpOp)
    (x : Option α) (other : KeyOther α) : Py τ :=
  match other with
  | .duck _ | .plain => .error (.typeError "other argument must be K instance")
  | .key y =>
    match x, y with
    | some a, some b => do
      let r ← mycmp a b
      K.cmp0 r op
    | _, _ => .error (.named "AttributeError" "object")

/-- `K.__init__`, Lib/functools.py:210-211, and `keyobject_call`, Modules/_functoolsmodule.c:891-909:
exactly one argument, positional or by the keyword `obj`. -/
def keyNew {α : Type} (pos : List α) (kw : List (String × α)) : Py α :=
  match pos, kw with
  | [a], [] => .ok a
  | [], [("obj", a)] => .ok a
  | _, _ => .error (.typeError "~K() takes exactly one argument 'obj'")

end PyLean.CoreLibs.Functools
