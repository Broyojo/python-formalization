import PyLean.CoreLibs.Operator.Proto

/-!
`itemgetter`, `attrgetter`, `methodcaller`, Lib/operator.py:240-342 and Modules/_operator.c:1016-1908.

The classes differ between the twins in storage and in how they check a call, and agree, or are meant to, on
what a call does. Each constructor, `__call__`, `__repr__` and `__reduce__` is mirrored in both.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- `_PyArg_NoKeywords` and `_PyArg_CheckPositional`, Modules/_operator.c:1113-1116, in that order. -/
def oneArgC (name : String) (nargs nkw : Nat) : Option PyExc :=
  if nkw ≠ 0 then some (.typeError s!"{name}() takes no keyword arguments")
  else if nargs ≠ 1 then
    some (.typeError s!"{name} expected 1 argument, got {nargs}")
  else none

/-- The argument check of `methodcaller_vectorcall`, Modules/_operator.c:1633-1636: positional first. -/
def oneArgVectorC (name : String) (nargs nkw : Nat) : Option PyExc :=
  if nargs ≠ 1 then some (.typeError s!"{name} expected 1 argument, got {nargs}")
  else if nkw ≠ 0 then some (.typeError s!"{name}() takes no keyword arguments")
  else none

/-- `__call__(self, obj, /)`: the Python signature. The message embeds the qualified name. -/
def oneArgPy (nargs nkw : Nat) : Option PyExc :=
  if nkw ≠ 0 ∨ nargs ≠ 1 then some (.typeError "~__call__() takes one positional argument") else none

/-- `__init__(self, x, /, *rest)`: the Python signature. -/
def newArgPy (nargs nkw : Nat) : Option PyExc :=
  if nkw ≠ 0 ∨ nargs = 0 then some (.typeError "~__init__() needs one positional argument") else none

/-- `itemgetter`, the C constructor's view: `PyArg_UnpackTuple` for fewer than two arguments, no keywords. -/
def newArgC (name : String) (nargs nkw : Nat) : Option PyExc :=
  if nkw ≠ 0 then some (.typeError s!"{name}() takes no keyword arguments")
  else if nargs = 0 then some (.typeError s!"{name} expected 1 argument, got 0")
  else none

/-- What a getter returns: the value, or the tuple. -/
inductive Out (α : Type) where
  | one (v : α)
  | many (vs : List α)
  deriving Repr, DecidableEq

/-- `tuple(f(x) for x in xs)`, and the `for` loops of the C `*_call_impl`: the first failure stops it. -/
def mapPy {β γ : Type} (f : β → Py γ) : List β → Py (List γ)
  | [] => .ok []
  | x :: xs =>
    match f x with
    | .error e => .error e
    | .ok y =>
      match mapPy f xs with
      | .error e => .error e
      | .ok ys => .ok (y :: ys)

/-! ### `itemgetter` -/

/-- A key: `exactInt` is `PyLong_CheckExact(item)` with its value. -/
structure ItemKey (κ : Type) where
  key : κ
  exactInt : Option Int

/-- `ig->index`, Modules/_operator.c:1062-1076: the value of an exact `int` that fits and is not negative. -/
def fastIndex {κ : Type} (k : ItemKey κ) : Option Nat :=
  match k.exactInt with
  | some n => if 0 ≤ n ∧ n ≤ ssizeMax then some n.toNat else none
  | none => none

/-- The operand of a call: an exact `tuple`, or anything else, with `get` being `PyObject_GetItem(obj, key)`. -/
structure ItemObj (α κ : Type) where
  exactTuple : Option (List α)
  get : κ → Py α

/-- `itemgetter.__call__`, Lib/operator.py:290-297: `obj[item]`, or the tuple of `obj[i]`. -/
def itemCallPy {α κ : Type} (items : List (ItemKey κ)) (o : ItemObj α κ) : Py (Out α) :=
  match items with
  | [k] =>
    match o.get k.key with
    | .error e => .error e
    | .ok v => .ok (.one v)
  | _ =>
    match mapPy (fun k => o.get k.key) items with
    | .error e => .error e
    | .ok vs => .ok (.many vs)

/-- `itemgetter_call_impl`, Modules/_operator.c:1136-1169. The tuple shortcut is for one item only. -/
def itemCallC {α κ : Type} (items : List (ItemKey κ)) (o : ItemObj α κ) : Py (Out α) :=
  match items with
  | [k] =>
    let slow : Py (Out α) :=
      match o.get k.key with
      | .error e => .error e
      | .ok v => .ok (.one v)
    match fastIndex k, o.exactTuple with
    | some i, some xs =>
      match xs[i]? with
      | some v => .ok (.one v)
      | none => slow
    | _, _ => slow
  | _ =>
    match mapPy (fun k => o.get k.key) items with
    | .error e => .error e
    | .ok vs => .ok (.many vs)

/-- `itemgetter.__repr__` and `attrgetter.__repr__`, Lib/operator.py:271-274 and :302-305: the items joined. -/
def joinArgs : List String → String
  | [] => ""
  | x :: xs => xs.foldl (fun a s => a ++ ", " ++ s) x

def reprPy {κ : Type} (rep : κ → Py String) (cls : String) (items : List κ) : Py String :=
  match mapPy rep items with
  | .error e => .error e
  | .ok rs => .ok (cls ++ "(" ++ joinArgs rs ++ ")")

/-- `tuple_repr` of two or more items: `"(a, b)"`. -/
def tupleRepr {κ : Type} (rep : κ → Py String) (items : List κ) : Py String :=
  match mapPy rep items with
  | .error e => .error e
  | .ok rs => .ok ("(" ++ joinArgs rs ++ ")")

/-- `itemgetter_repr`, Modules/_operator.c:1172-1189, and `attrgetter_repr`, :1525-1555. `running` is
`Py_ReprEnter`, which the Python classes do not call: `(...)` instead of recursing. -/
def reprC {κ : Type} (rep : κ → Py String) (running : Bool) (cls : String) (items : List κ) : Py String :=
  if running then .ok (cls ++ "(...)") else
  match items with
  | [k] =>
    match rep k with
    | .error e => .error e
    | .ok r => .ok (cls ++ "(" ++ r ++ ")")
  | _ =>
    match tupleRepr rep items with
    | .error e => .error e
    | .ok t => .ok (cls ++ t)

/-! ### `attrgetter` -/

/-- A `.`-free name, as characters. -/
abbrev Chain := List (List Char)

/-- `attr.split('.')` and the loop at Modules/_operator.c:1304-1345, on the characters. -/
def splitChars : List Char → Chain
  | [] => [[]]
  | c :: cs =>
    match splitChars cs with
    | [] => [[]]
    | r :: rs => if c = '.' then [] :: r :: rs else (c :: r) :: rs

/-- `dotjoinattr`, Modules/_operator.c:1487-1499. -/
def joinChars : Chain → List Char
  | [] => []
  | [r] => r
  | r :: rs => r ++ '.' :: joinChars rs

/-- The argument of `attrgetter` or `methodcaller`. -/
inductive AttrArg where
  | str (s : List Char)
  /-- A `str` subclass with this value, and what its own `split('.')` returns. C reads the characters. -/
  | strSub (s : List Char) (split : Chain)
  | other
  deriving Repr, DecidableEq

def attrNameMsg := "attribute name must be a string"

/-- An attribute lookup: `getattr(obj, name)`, on a value of the abstract type. -/
abbrev GetAttr (α : Type) := α → List Char → Py α

/-- `for name in names: obj = getattr(obj, name)`, Lib/operator.py:257-259, and `dotted_getattr`,
Modules/_operator.c:1397-1427. -/
def dotted {α : Type} (ga : GetAttr α) : α → Chain → Py α
  | obj, [] => .ok obj
  | obj, n :: ns =>
    match ga obj n with
    | .error e => .error e
    | .ok v => dotted ga v ns

/-- What an `attrgetter` holds: `_attrs` in Python, with the names the closure splits. -/
structure AttrPy where
  attrs : List AttrArg
  names : List Chain
  deriving Repr, DecidableEq

/-- The check at Lib/operator.py:252 and the `attr.split('.')` at :255. -/
def namePy : AttrArg → Py Chain
  | .str s => .ok (splitChars s)
  | .strSub _ c => .ok c
  | .other => .error (.typeError attrNameMsg)

/-- The check and the split at Modules/_operator.c:1283-1345. -/
def nameC : AttrArg → Py Chain
  | .str s | .strSub s _ => .ok (splitChars s)
  | .other => .error (.typeError attrNameMsg)

/-- `attrgetter.__init__`, Lib/operator.py:250-266: one attribute directly, and for more a getter each, so
the check at :252 runs for each, in order, after `_attrs` is set. -/
def attrgetterNewPy (args : List AttrArg) : Py AttrPy :=
  match mapPy namePy args with
  | .error e => .error e
  | .ok names => .ok ⟨args, names⟩

/-- What `attrgetter_new`, Modules/_operator.c:1262-1367, stores: the characters of each name, split, whatever
the class of the `str`. -/
def attrgetterNewC (args : List AttrArg) : Py (List Chain) :=
  mapPy nameC args

/-- `attrgetter.__call__` in both twins: one name gives the value, more give the tuple, in order. -/
def attrCall {α : Type} (ga : GetAttr α) (names : List Chain) (obj : α) : Py (Out α) :=
  match names with
  | [c] =>
    match dotted ga obj c with
    | .error e => .error e
    | .ok v => .ok (.one v)
  | _ =>
    match mapPy (dotted ga obj) names with
    | .error e => .error e
    | .ok vs => .ok (.many vs)

/-- `attrgetter_args`, Modules/_operator.c:1502-1523, what `__reduce__` and `__repr__` rebuild. -/
def attrArgsC (names : List Chain) : List (List Char) := names.map joinChars

/-- `attrgetter.__reduce__`, Lib/operator.py:276-277: the stored arguments. -/
def attrArgsPy (g : AttrPy) : List (List Char) :=
  g.attrs.filterMap (fun a => match a with
    | .str s | .strSub s _ => some s
    | .other => none)

/-! ### `attrgetter` with name objects

`nameC` keeps the characters of a name, which is all an exact `str` has. A `str` subclass also has an identity and
methods of its own, and C keeps the object for an undotted name, so these definitions keep it. -/

/-- What `attrgetter_new` keeps for one name, Modules/_operator.c:1283-1350. An undotted name is the object itself,
interned (:1304-1307), and `_PyUnicode_InternMortal` leaves a `str` subclass as it is (Objects/unicodeobject.c:14306-
14310). A dotted name becomes a tuple of new exact `str` parts (`PyUnicode_Substring`, :1308-1349). -/
inductive CAttr where
  | single (a : AttrArg)
  | chain (parts : Chain)
  deriving Repr, DecidableEq

/-- The `PyUnicode_Check` and the dot count of `attrgetter_new`, :1287-1304. -/
def nameCObj : AttrArg → Py CAttr
  | .other => .error (.typeError attrNameMsg)
  | .str s => if '.' ∈ s then .ok (.chain (splitChars s)) else .ok (.single (.str s))
  | .strSub s c => if '.' ∈ s then .ok (.chain (splitChars s)) else .ok (.single (.strSub s c))

def attrgetterNewCObj (args : List AttrArg) : Py (List CAttr) := mapPy nameCObj args

/-- `getattr(obj, name)` given the name object: `PyObject_GetAttr` passes it on, and a `__getattribute__` or
`__getattr__` written in Python, or a dict lookup through the name's own `__eq__`, sees it. -/
abbrev GetAttrObj (α : Type) := α → AttrArg → Py α

/-- `dotted_getattr`, Modules/_operator.c:1397-1427: a tuple is walked with its exact parts (:1403-1418), a single
name is looked up as it is (:1419-1424). -/
def dottedObj {α : Type} (ga : GetAttrObj α) (obj : α) : CAttr → Py α
  | .single a => ga obj a
  | .chain c => dotted (fun o n => ga o (.str n)) obj c

/-- `attrgetter_call_impl`, Modules/_operator.c:1455-1484. -/
def attrCallCObj {α : Type} (ga : GetAttrObj α) (stored : List CAttr) (obj : α) : Py (Out α) :=
  match stored with
  | [x] =>
    match dottedObj ga obj x with
    | .error e => .error e
    | .ok v => .ok (.one v)
  | _ =>
    match mapPy (dottedObj ga obj) stored with
    | .error e => .error e
    | .ok vs => .ok (.many vs)

/-- `attrgetter.__call__` in Python, Lib/operator.py:255-259: `getattr` with the parts `attr.split('.')` returned, so
with exact `str` objects. -/
def attrCallPyObj {α : Type} (ga : GetAttrObj α) (g : AttrPy) (obj : α) : Py (Out α) :=
  attrCall (fun o n => ga o (.str n)) g.names obj

/-- `dotjoinattr`, Modules/_operator.c:1487-1499: a tuple is joined with `"."` into a new exact `str`, anything else
is itself. -/
def dotjoinObj : CAttr → AttrArg
  | .single a => a
  | .chain c => .str (joinChars c)

/-- `attrgetter_repr`, Modules/_operator.c:1525-1555: one name prints `%R` of its `dotjoinattr` (:1536-1544), more
print the tuple of `attrgetter_args` (:1545-1552). `rep` is `repr` of a name object. -/
def attrReprC (rep : AttrArg → Py String) (running : Bool) (cls : String) (stored : List CAttr) : Py String :=
  reprC rep running cls (stored.map dotjoinObj)

/-! ### `methodcaller` -/

/-- A `methodcaller`: the fields of both twins. -/
structure Mc (α : Type) where
  name : List Char
  args : List α
  kw : List (String × α)
  deriving Repr, DecidableEq

/-- `methodcaller.__init__`, Lib/operator.py:319-324. -/
def mcNewPy {α : Type} (name : Option AttrArg) (args : List α) (kw : List (String × α)) : Py (Mc α) :=
  match name with
  | none => .error (.typeError "~methodcaller.__init__() missing 1 required positional argument: 'name'")
  | some (.str s) | some (.strSub s _) => .ok ⟨s, args, kw⟩
  | some .other => .error (.typeError "method name must be a string")

/-- `methodcaller_new`, Modules/_operator.c:1690-1741. -/
def mcNewC {α : Type} (name : Option AttrArg) (args : List α) (kw : List (String × α)) : Py (Mc α) :=
  match name with
  | none => .error (.typeError "methodcaller needs at least one argument, the method name")
  | some (.str s) | some (.strSub s _) => .ok ⟨s, args, kw⟩
  | some .other => .error (.typeError "method name must be a string")

/-- `getattr(obj, name)` gives a bound method, and calling it gives a result. Both steps may raise. -/
abbrev Meth (α β : Type) := α → List Char → Py (List α → List (String × α) → Py β)

/-- `methodcaller.__call__`, Lib/operator.py:326-327, and `methodcaller_call`, Modules/_operator.c:1779-1796. -/
def mcCall {α β : Type} (m : Meth α β) (c : Mc α) (obj : α) : Py β :=
  match m obj c.name with
  | .error e => .error e
  | .ok f => f c.args c.kw

/-- `_methodcaller_initialize_vectorcall`, Modules/_operator.c:1649-1686: the positional arguments, then the
keyword values, and the keyword names apart. -/
def vectorcallArgs {α : Type} (args : List α) (kw : List (String × α)) : List α × List String :=
  (args ++ kw.map Prod.snd, kw.map Prod.fst)

/-- `methodcaller_vectorcall`, :1628-1646, with `PyObject_VectorcallMethod`: `nargs` is the positional part of
`tmp_args`, and the rest are the values of `kwnames`. -/
def mcVectorcall {α β : Type} (m : Meth α β) (c : Mc α) (obj : α) : Py β :=
  let (flat, names) := vectorcallArgs c.args c.kw
  let n := c.args.length
  match m obj c.name with
  | .error e => .error e
  | .ok f => f (flat.take n) (names.zip (flat.drop n))

/-- Whether the vectorcall path is set up, Modules/_operator.c:1730-1737: `_METHODCALLER_MAX_ARGS`, and the size
counts the name. -/
def usesVectorcall (nargs nkw : Nat) : Bool := decide (nargs + 1 + nkw < 8)

/-- What a call runs in C. -/
def mcCallC {α β : Type} (m : Meth α β) (c : Mc α) (obj : α) : Py β :=
  if usesVectorcall c.args.length c.kw.length then mcVectorcall m c obj else mcCall m c obj

/-- `methodcaller.__repr__`, Lib/operator.py:329-335. `nameRep` is `repr(self._name)`, which a `str` subclass can
make raise; it is the first thing evaluated (:330). -/
def mcReprPy {α : Type} (rep : α → Py String) (cls : String) (nameRep : Py String) (c : Mc α) : Py String :=
  match nameRep with
  | .error e => .error e
  | .ok nameRepr =>
    match mapPy rep c.args with
    | .error e => .error e
    | .ok a =>
      match mapPy (fun p => (rep p.2).map (fun r => p.1 ++ "=" ++ r)) c.kw with
      | .error e => .error e
      | .ok k => .ok (cls ++ "(" ++ joinArgs (nameRepr :: a ++ k) ++ ")")

/-- `methodcaller_repr`, Modules/_operator.c:1799-1873, with the guard as in `reprC`. The name's `%R` is evaluated
when the format is: at :1816 with no arguments, otherwise at :1865, after every argument and keyword. -/
def mcReprC {α : Type} (rep : α → Py String) (running : Bool) (cls : String) (nameRep : Py String) (c : Mc α) :
    Py String :=
  if running then .ok (cls ++ "(...)") else
  if c.args.isEmpty && c.kw.isEmpty then nameRep.map (fun nameRepr => cls ++ "(" ++ nameRepr ++ ")") else
  match mapPy rep c.args with
  | .error e => .error e
  | .ok a =>
    match mapPy (fun p => (rep p.2).map (fun r => p.1 ++ "=" ++ r)) c.kw with
    | .error e => .error e
    | .ok k =>
      match nameRep with
      | .error e => .error e
      | .ok nameRepr => .ok (cls ++ "(" ++ nameRepr ++ ", " ++ joinArgs (a ++ k) ++ ")")

/-- What `__reduce__` returns. -/
inductive McReduce (α : Type) where
  /-- `(cls, (name, *args))`. -/
  | plain (name : List Char) (args : List α)
  /-- `(partial(cls, name, **kw), args)`. -/
  | viaPartial (name : List Char) (kw : List (String × α)) (args : List α)
  deriving Repr, DecidableEq

/-- `methodcaller.__reduce__`, Lib/operator.py:337-342, and `methodcaller_reduce`, Modules/_operator.c:1876-1908. -/
def mcReduce {α : Type} (c : Mc α) : McReduce α :=
  if c.kw.isEmpty then .plain c.name c.args else .viaPartial c.name c.kw c.args

/-- Calling what `__reduce__` returned. -/
def mcRebuild {α : Type} (new : Option AttrArg → List α → List (String × α) → Py (Mc α)) : McReduce α → Py (Mc α)
  | .plain n a => new (some (.str n)) a []
  | .viaPartial n k a => new (some (.str n)) a k

end PyLean.CoreLibs.Operator
