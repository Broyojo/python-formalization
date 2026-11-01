import PyLean.Core

/-!
`Lib/operator.py` and `Modules/_operator.c`, `Lib/copy.py`, `Lib/abc.py` (CPython 3.14.7).

Most of the module is one line per operator, so the operators are mirrored once, as the dispatch
algorithm over abstract slots: `binaryOp1` is `binary_op1`, Objects/abstract.c:930-980. The functions
that differ between the twins (`concat`, `iconcat`, `length_hint`, `index`, `indexOf`, `countOf`, the
callable classes) are mirrored twice.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- A dunder's result: a value, or `NotImplemented`. -/
inductive Ret (α : Type) where
  | val (a : α)
  | notImplemented
  deriving Repr, DecidableEq, Inhabited

/-! ### The binary, in-place and comparison families -/

/-- The slots `binary_op1` sees for one operator and one pair of operands. `none` is a null slot;
`right` is null when the two types share the slot. -/
structure BinSlots (α : Type) where
  left : Option (α → α → Py (Ret α))
  right : Option (α → α → Py (Ret α))
  /-- `PyType_IsSubtype(Py_TYPE(w), Py_TYPE(v))`. -/
  rightIsSubtype : Bool

/-- `binary_op1`, Objects/abstract.c:930-980. -/
def binaryOp1 {α : Type} (S : BinSlots α) (v w : α) : Py (Ret α) :=
  let tryRight : Option (α → α → Py (Ret α)) → Py (Ret α) := fun slot =>
    match slot with
    | none => .ok .notImplemented
    | some f => f v w
  match S.left with
  | none => tryRight S.right
  | some sv =>
    match S.right, S.rightIsSubtype with
    | some sw, true => do
      match ← sw v w with
      | .val x => pure (.val x)
      | .notImplemented => sv v w
    | r, _ => do
      match ← sv v w with
      | .val x => pure (.val x)
      | .notImplemented => tryRight r

/-- The operators of the `operator` module whose C function is `PyNumber_<Op>(a, b)` and whose Python
function is the operator expression, with their symbols, as in the `unsupported operand` message. -/
def binarySymbols : List (String × String) :=
  [("add", "+"), ("sub", "-"), ("mul", "*"), ("matmul", "@"), ("floordiv", "//"), ("truediv", "/"),
   ("mod", "%"), ("lshift", "<<"), ("rshift", ">>"), ("and_", "&"), ("xor", "^"), ("or_", "|"),
   ("pow", "** or pow()")]

def unsupported (sym lt rt : String) : PyExc :=
  .typeError s!"unsupported operand type(s) for {sym}: '{lt}' and '{rt}'"

/-- `a op b`: `operator.add` and friends in both twins. Python evaluates the expression, C calls
`PyNumber_Add` (`_operator_add_impl`); both reach `binary_op1`, then raise. -/
def binaryOp {α : Type} (S : BinSlots α) (sym lt rt : String) (v w : α) : Py α := do
  match ← binaryOp1 S v w with
  | .val x => pure x
  | .notImplemented => throw (unsupported sym lt rt)

/-- `a op= b`: `binary_iop1`, Objects/abstract.c:1218: the in-place slot, then `binary_op1`. -/
def inplaceOp {α : Type} (islot : Option (α → α → Py (Ret α))) (S : BinSlots α) (sym lt rt : String)
    (v w : α) : Py α := do
  match islot with
  | some f =>
    match ← f v w with
    | .val x => return x
    | .notImplemented => pure ()
  | none => pure ()
  binaryOp S (sym ++ "=") lt rt v w

/-- The two reflected comparison methods `do_richcompare`, Objects/object.c:1046, tries, with the
subclass-first rule, and the default for `==` and `!=`. -/
structure CmpSlots (α : Type) where
  left : α → α → Py (Ret Bool)
  right : α → α → Py (Ret Bool)
  rightIsSubtypeOverride : Bool

inductive RichOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq

def RichOp.sym : RichOp → String
  | .lt => "<" | .le => "<=" | .eq => "==" | .ne => "!=" | .gt => ">" | .ge => ">="

/-- `do_richcompare`, Objects/object.c:1046-1095. -/
def richCompare {α : Type} (S : CmpSlots α) (op : RichOp) (same : Bool) (lt rt : String) (v w : α) :
    Py Bool := do
  if S.rightIsSubtypeOverride then
    match ← S.right w v with
    | .val b => return b
    | .notImplemented => pure ()
  match ← S.left v w with
  | .val b => return b
  | .notImplemented => pure ()
  if !S.rightIsSubtypeOverride then
    match ← S.right w v with
    | .val b => return b
    | .notImplemented => pure ()
  match op with
  | .eq => pure same
  | .ne => pure (!same)
  | _ => throw (.typeError s!"'{op.sym}' not supported between instances of '{lt}' and '{rt}'")

/-! ### Unary operators and identity -/

/-- `operator.neg`, `pos`, `abs`, `inv`: the unary slot, else `TypeError`. -/
def unaryOp {α : Type} (slot : Option (α → Py α)) (desc tn : String) (v : α) : Py α :=
  match slot with
  | some f => f v
  | none => .error (.typeError s!"bad operand type for {desc}: '{tn}'")

/-- `operator.truth` and `not_`, on the truth value of the operand. -/
def truth (b : Py Bool) : Py Bool := b

def not_ (b : Py Bool) : Py Bool := do pure (!(← b))

/-- `operator.is_`, `is_not`, `is_none`, `is_not_none`. -/
def isOp {α : Type} (same : α → α → Bool) (a b : α) : Bool := same a b

/-- What `__index__` looks like on an operand. -/
inductive IndexSlot where
  /-- An `int`, or `__index__` returning this `int`. -/
  | int (n : Int)
  /-- No `__index__`. -/
  | none
  /-- `__index__` returning a non-`int`. -/
  | badResult
  deriving Repr, DecidableEq

/-- `index(a)`, Lib/operator.py:95-97: `a.__index__()`. -/
def indexPy : IndexSlot → Py (Option Int)
  | .int n => .ok (some n)
  | .none => .error (.named "AttributeError" "~object has no attribute '__index__'")
  | .badResult => .ok none

/-- `_operator_index`, Modules/_operator.c:698-702, through `PyNumber_Index`, Objects/abstract.c:1400. -/
def indexC : IndexSlot → Py (Option Int)
  | .int n => .ok (some n)
  | .none => .error (.typeError "~object cannot be interpreted as an integer")
  | .badResult => .error (.typeError "~__index__ returned non-int")

/-! ### `concat`, `iconcat` -/

/-- What `concat(a, b)` sees of its operands. -/
structure ConcatArgs (α : Type) where
  /-- `hasattr(a, '__getitem__')`. -/
  hasGetitem : Bool
  /-- `a`'s `sq_concat`. -/
  sqConcat : Option (α → α → Py α)
  /-- `a`'s `sq_inplace_concat`. -/
  sqInplace : Option (α → α → Py α)
  /-- `PySequence_Check(a)`, `PySequence_Check(b)`. -/
  seqA : Bool
  seqB : Bool
  /-- `BINARY_OP1(a, b, nb_add)` and `BINARY_IOP1`. -/
  nbAdd : α → α → Py (Ret α)
  nbIAdd : α → α → Py (Ret α)

def noConcat (tn : String) : PyExc := .typeError s!"'{tn}' object can't be concatenated"

/-- `PyNumber_Add`, Objects/abstract.c:1128: `nb_add`, then `sq_concat`. -/
def plus {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α := do
  match ← A.nbAdd a b with
  | .val x => pure x
  | .notImplemented =>
    match A.sqConcat with
    | some f => f a b
    | none => throw (unsupported "+" lt rt)

/-- `PyNumber_InPlaceAdd`, Objects/abstract.c:1297: `nb_inplace_add` and `nb_add`, then the sequence
slots. -/
def plusEq {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α := do
  match ← A.nbIAdd a b with
  | .val x => pure x
  | .notImplemented =>
    match A.sqInplace, A.sqConcat with
    | some f, _ => f a b
    | none, some f => f a b
    | none, none => throw (unsupported "+=" lt rt)

/-- `concat`, Lib/operator.py:154-159. -/
def concatPy {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α :=
  if !A.hasGetitem then .error (noConcat lt) else plus A lt rt a b

/-- `iconcat`, Lib/operator.py:357-363. -/
def iconcatPy {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α :=
  if !A.hasGetitem then .error (noConcat lt) else plusEq A lt rt a b

/-- `_operator_concat_impl`, Modules/_operator.c:461-465, through `PySequence_Concat`,
Objects/abstract.c:1712-1735. -/
def concatC {α : Type} (A : ConcatArgs α) (lt : String) (a b : α) : Py α :=
  match A.sqConcat with
  | some f => f a b
  | none =>
    if A.seqA && A.seqB then do
      match ← A.nbAdd a b with
      | .val x => pure x
      | .notImplemented => throw (noConcat lt)
    else .error (noConcat lt)

/-- `_operator_iconcat_impl`, Modules/_operator.c:474-478, through `PySequence_InPlaceConcat`,
Objects/abstract.c:1769-1795. -/
def iconcatC {α : Type} (A : ConcatArgs α) (lt : String) (a b : α) : Py α :=
  match A.sqInplace, A.sqConcat with
  | some f, _ => f a b
  | none, some f => f a b
  | none, none =>
    if A.seqA && A.seqB then do
      match ← A.nbIAdd a b with
      | .val x => pure x
      | .notImplemented => throw (noConcat lt)
    else .error (noConcat lt)

/-! ### Subscripting, `contains`, `call` -/

/-- `contains(a, b)`, Lib/operator.py:161-163, and `_operator_contains_impl`, Modules/_operator.c:491:
the container is the first argument, so `slot` is `type(a).__contains__`. -/
def containsOp {α : Type} (slot : α → α → Py Bool) (a b : α) : Py Bool := slot a b

/-- `getitem(a, b)`, :177-179. -/
def getitemOp {α : Type} (slot : α → α → Py α) (a b : α) : Py α := slot a b

/-- `setitem(a, b, c)`, :189-191, and `delitem(a, b)`, :173-175: the slot's effect, and `None`. -/
def storeOp {σ : Type} (slot : σ → Py σ) (s : σ) : Py (Unit × σ) := do
  let s' ← slot s
  pure ((), s')

/-- `call(obj, /, *args)`, Lib/operator.py:234-236, and `_operator_call`, Modules/_operator.c:928-937,
which checks for the positional argument first. -/
def callOp {α β : Type} (apply : α → List α → Py β) : List α → Py β
  | [] => .error (.typeError "~call expected at least 1 argument, got 0")
  | obj :: rest => apply obj rest

/-! ### `countOf`, `indexOf` -/

/-- `i is b or i == b`, and `PyObject_RichCompareBool`. -/
abbrev Same (α : Type) := α → α → Py Bool

/-- `for i in a: if i is b or i == b: count += 1`, Lib/operator.py:165-171, and
`_PySequence_IterSearch`, Objects/abstract.c:2129, with `PY_ITERSEARCH_COUNT`. `err` ends the
iteration with an exception. -/
def countOf {α : Type} (same : Same α) (b : α) : List α → Option PyExc → Py Nat
  | [], none => .ok 0
  | [], some e => .error e
  | x :: xs, e => do
    let hit ← same x b
    let n ← countOf same b xs e
    pure ((if hit then 1 else 0) + n)

def indexMsg := "sequence.index(x): x not in sequence"

/-- `indexOf`, Lib/operator.py:181-187, and `PY_ITERSEARCH_INDEX`. -/
def indexOf {α : Type} (same : Same α) (b : α) : Nat → List α → Option PyExc → Py Nat
  | _, [], none => .error (.valueError indexMsg)
  | _, [], some e => .error e
  | i, x :: xs, e => do
    if ← same x b then return i
    indexOf same b (i + 1) xs e

/-! ### `length_hint` -/

/-- What `__length_hint__` returns. -/
inductive HintRet where
  | int (n : Int)
  | notImplemented
  /-- Something that is not an `int`, of the named type. -/
  | other (tn : String)
  deriving Repr, DecidableEq

/-- What `length_hint` sees of an object. -/
structure HintObj where
  /-- `len(obj)`; a missing `__len__` is the `TypeError` case. -/
  len : Py Nat
  /-- `type(obj).__length_hint__`, called; `none` when there is none. -/
  hint : Option (Py HintRet)
  deriving Repr

/-- The `default` argument. -/
inductive HintDefault where
  | int (n : Int)
  /-- Not an `int`, with an `__index__` returning `n`. -/
  | indexable (n : Int)
  | other (tn : String)
  deriving Repr, DecidableEq

def isTypeError : PyExc → Bool
  | .typeError _ => true
  | _ => false

def negativeHint := "__length_hint__() should return >= 0"

/-- `length_hint`, Lib/operator.py:193-230. -/
def lengthHintPy (o : HintObj) (default : HintDefault) : Py Int := do
  let d ← match default with
    | .int n => pure n
    | .indexable _ => throw (.typeError "~object cannot be interpreted as an integer")
    | .other tn => throw (.typeError s!"'{tn}' object cannot be interpreted as an integer")
  match o.len with
  | .ok n => return n
  | .error e => if !isTypeError e then throw e
  match o.hint with
  | none => pure d
  | some h =>
    match h with
    | .error e => if isTypeError e then pure d else throw e
    | .ok .notImplemented => pure d
    | .ok (.other tn) => throw (.typeError s!"__length_hint__ must be integer, not {tn}")
    | .ok (.int v) =>
      if v < 0 then throw (.valueError negativeHint) else pure v

/-- `Py_ssize_t` conversion of a Python `int`. -/
def toSsize (n : Int) : Py Int :=
  if n > ssizeMax ∨ n < ssizeMin then
    .error (.overflowError "Python int too large to convert to C ssize_t")
  else .ok n

/-- `_operator_length_hint_impl`, Modules/_operator.c:826-831, with the argument-clinic conversion
of `default` to `Py_ssize_t`, and `PyObject_LengthHint`, Objects/abstract.c:95. -/
def lengthHintC (o : HintObj) (default : HintDefault) : Py Int := do
  let d ← match default with
    | .int n => toSsize n
    | .indexable n => toSsize n
    | .other tn => throw (.typeError s!"'{tn}' object cannot be interpreted as an integer")
  match o.len with
  | .ok n => return n
  | .error e => if !isTypeError e then throw e
  match o.hint with
  | none => pure d
  | some h =>
    match h with
    | .error e => if isTypeError e then pure d else throw e
    | .ok .notImplemented => pure d
    | .ok (.other tn) => throw (.typeError s!"__length_hint__ must be an integer, not {tn}")
    | .ok (.int v) =>
      let r ← toSsize v
      if r < 0 then throw (.valueError negativeHint) else pure r

/-! ### `itemgetter` -/

/-- An item getter: the items in order. -/
abbrev Items (κ : Type) := List κ

/-- `obj[item]` and `tuple(obj[i] for i in items)`, Lib/operator.py:287-300. `get` is `obj[i]`. -/
def itemgetterPy {κ α : Type} (get : κ → Py α) : Items κ → Py (List α)
  | [] => .ok []
  | i :: is => do
    let v ← get i
    let vs ← itemgetterPy get is
    pure (v :: vs)

/-- `itemgetter_call_impl`, Modules/_operator.c:1136-1169, for one exact `int` item on an exact
`tuple`, the fast path; the slow path is `PyObject_GetItem`. -/
def itemgetterFast {α : Type} (obj : List α) (index : Int) (get : Int → Py α) : Py α :=
  if index ≥ 0 ∧ index < obj.length then
    match obj[index.toNat]? with
    | some v => .ok v
    | none => get index
  else get index

/-- `tuple.__getitem__` with an `int`. -/
def tupleGet {α : Type} (xs : List α) (i : Int) : Py α :=
  let n : Int := xs.length
  let j := if i < 0 then i + n else i
  if j < 0 ∨ j ≥ n then .error (.indexError "tuple index out of range")
  else
    match xs[j.toNat]? with
    | some v => .ok v
    | none => .error (.indexError "tuple index out of range")

/-- `itemgetter.__repr__`, Lib/operator.py:302-305, and `itemgetter_repr`, Modules/_operator.c:1172. -/
def getterReprPy (cls : String) (items : List String) : String :=
  s!"{cls}({", ".intercalate items})"

/-- The C form: `%s(%R)` for one item, `%s%R` with the tuple otherwise. -/
def getterReprC (cls : String) (items : List String) : String :=
  match items with
  | [i] => s!"{cls}({i})"
  | _ => s!"{cls}({", ".intercalate items})"

/-! ### `attrgetter` -/

/-- `attr.split('.')`. -/
def splitDots (attr : String) : List String := attr.splitOn "."

/-- An attribute lookup: `getattr(obj, name)`, on a value of the abstract type. -/
abbrev GetAttr (α : Type) := α → String → Py α

/-- The chain `for name in names: obj = getattr(obj, name)`, Lib/operator.py:257-259, and
`dotted_getattr`, Modules/_operator.c:1397-1427. -/
def dotted {α : Type} (ga : GetAttr α) : α → List String → Py α
  | obj, [] => .ok obj
  | obj, n :: ns => do dotted ga (← ga obj n) ns

/-- The argument of `attrgetter`. -/
inductive AttrArg where
  | str (s : String)
  | other
  deriving Repr, DecidableEq

def attrNameMsg := "attribute name must be a string"

/-- `attrgetter.__init__`, Lib/operator.py:250-266, the validity check; `attrgetter_new`,
Modules/_operator.c:1262-1367 does the same in one loop. -/
def attrgetterNew (args : List AttrArg) : Py (List String) :=
  args.mapM (fun a => match a with
    | .str s => .ok s
    | .other => .error (.typeError attrNameMsg))

/-- `attrgetter_call_impl`, Modules/_operator.c:1456-1484, and the two `func`s in the Python class:
the one-attribute form returns the value, the others the tuple. The result is a list here. -/
def attrgetterCall {α : Type} (ga : GetAttr α) (obj : α) : List String → Py (List α)
  | [] => .ok []
  | a :: as => do
    let v ← dotted ga obj (splitDots a)
    let vs ← attrgetterCall ga obj as
    pure (v :: vs)

/-- `dotjoinattr`, Modules/_operator.c:1487-1499: the names joined back. -/
def dotJoin (names : List String) : String := ".".intercalate names

/-! ### `methodcaller` -/

/-- `methodcaller.__init__`, Lib/operator.py:319-324, and `methodcaller_new`,
Modules/_operator.c:1690-1741, on the name argument. -/
def methodcallerNewPy (name : Option AttrArg) : Py String :=
  match name with
  | none => .error (.typeError "~methodcaller() missing 1 required positional argument: 'name'")
  | some (.str s) => .ok s
  | some .other => .error (.typeError "method name must be a string")

def methodcallerNewC (name : Option AttrArg) : Py String :=
  match name with
  | none => .error (.typeError "methodcaller needs at least one argument, the method name")
  | some (.str s) => .ok s
  | some .other => .error (.typeError "method name must be a string")

/-- A method call: `getattr(obj, name)(*args, **kwargs)`, Lib/operator.py:326-327. -/
structure MethodCall (α : Type) where
  name : String
  args : List α
  kw : List (String × α)
  deriving Repr, DecidableEq

/-- `methodcaller_vectorcall`, Modules/_operator.c:1628-1646, flattens keyword values after the
positional arguments and passes the names; `_methodcaller_initialize_vectorcall`, :1649-1686. -/
def vectorcallArgs {α : Type} (args : List α) (kw : List (String × α)) : List α × List String :=
  (args ++ kw.map Prod.snd, kw.map Prod.fst)

/-- `PyObject_VectorcallMethod` on the flattened form: the last `kwnames` values are keywords. -/
def unflatten {α : Type} (name : String) (flat : List α) (names : List String) : MethodCall α :=
  let n := flat.length - names.length
  ⟨name, flat.take n, names.zip (flat.drop n)⟩

/-- Whether the vectorcall path is set up, Modules/_operator.c:1730-1737: `_METHODCALLER_MAX_ARGS`. -/
def usesVectorcall (nargs nkw : Nat) : Bool := decide (nargs + 1 + nkw < 8)

/-- `methodcaller.__repr__`, Lib/operator.py:329-335, and `methodcaller_repr`,
Modules/_operator.c:1798-1872. -/
def methodcallerRepr (cls nameRepr : String) (args : List String) (kw : List (String × String)) :
    String :=
  let parts := nameRepr :: args ++ kw.map (fun p => s!"{p.1}={p.2}")
  s!"{cls}({", ".intercalate parts})"

/-- `methodcaller.__reduce__`, Lib/operator.py:337-342, and `methodcaller_reduce`,
Modules/_operator.c:1875-1907: the constructor arguments, a `partial` for keywords. -/
inductive McReduce (α : Type) where
  | plain (ctorArgs : List α)
  | viaPartial (kw : List (String × α)) (args : List α)
  deriving Repr, DecidableEq

def methodcallerReduce {α : Type} (name : α) (args : List α) (kw : List (String × α)) : McReduce α :=
  if kw.isEmpty then .plain (name :: args) else .viaPartial kw args

/-! ### `_compare_digest` -/

/-- The loop of `_tscmp`, Modules/_operator.c:802-804. -/
def tscmpLoop : Nat → List Nat → List Nat → Nat
  | r, a :: as, b :: bs => tscmpLoop (r ||| (a ^^^ b)) as bs
  | r, _, _ => r

/-- `_tscmp`, Modules/_operator.c:772-807: with unequal lengths it compares `b` with itself and
starts the result at 1. -/
def tscmp (a b : List Nat) : Bool :=
  if a.length = b.length then tscmpLoop 0 a b == 0 else tscmpLoop 1 b b == 0

/-- The arguments of `_compare_digest`. -/
inductive DigestArg where
  | str (ascii : Bool) (data : List Nat)
  | buffer (data : List Nat)
  | other (tn : String)
  deriving Repr, DecidableEq

/-- `_operator__compare_digest_impl`, Modules/_operator.c:852-916. -/
def compareDigest : DigestArg → DigestArg → Py Bool
  | .str aa a, .str ab b =>
    if !aa || !ab then
      .error (.typeError "comparing strings with non-ASCII characters is not supported")
    else .ok (tscmp a b)
  | .buffer a, .buffer b => .ok (tscmp a b)
  | .other ta, .other tb =>
    .error (.typeError
      s!"unsupported operand types(s) or combination of types: '{ta}' and '{tb}'")
  | .str _ _, .other tb =>
    .error (.typeError
      s!"unsupported operand types(s) or combination of types: 'str' and '{tb}'")
  | .other ta, .str _ _ =>
    .error (.typeError
      s!"unsupported operand types(s) or combination of types: '{ta}' and 'str'")
  | _, _ => .error (.typeError "~a bytes-like object is required")

/-! ### `Lib/copy.py` -/

/-- A heap of objects: ids are list positions. -/
inductive Cell where
  | atom (n : Int)
  | list (items : List Nat)
  | tuple (items : List Nat)
  | dict (items : List (Nat × Nat))
  deriving Repr, DecidableEq, Inhabited

/-- The state of a `deepcopy` run. `memo` maps an id to its copy. -/
structure Heap where
  cells : List Cell
  memo : List (Nat × Nat)
  deriving Repr, DecidableEq

def Heap.get (h : Heap) (i : Nat) : Cell := h.cells.getD i (.atom 0)

def Heap.alloc (h : Heap) (c : Cell) : Heap × Nat :=
  ({ h with cells := h.cells ++ [c] }, h.cells.length)

def Heap.set (h : Heap) (i : Nat) (c : Cell) : Heap :=
  { h with cells := h.cells.set i c }

def Heap.remember (h : Heap) (x y : Nat) : Heap := { h with memo := (x, y) :: h.memo }

mutual
  /-- `deepcopy(x, memo)`, Lib/copy.py:110-163, on the built-in containers, with `_deepcopy_list`,
  :172-178, `_deepcopy_tuple`, :181-195, `_deepcopy_dict`, :198-203. -/
  def deepcopy : Nat → Heap → Nat → Py (Heap × Nat)
    | 0, _, _ => .error .modelFuel
    | fuel + 1, h, x =>
      match h.get x with
      | .atom _ => .ok (h, x)
      | c =>
        match h.memo.lookup x with
        | some y => .ok (h, y)
        | none => do
          match c with
          | .list items =>
            let (h1, y) := h.alloc (.list [])
            let h2 := h1.remember x y
            let (h3, ys) ← deepList fuel h2 items
            let h4 := h3.set y (.list ys)
            pure (h4, y)
          | .tuple items =>
            let (h1, ys) ← deepList fuel h items
            match h1.memo.lookup x with
            | some y => pure (h1, y)
            | none =>
              if ys == items then pure (h1, x)
              else
                let (h2, y) := h1.alloc (.tuple ys)
                pure (h2.remember x y, y)
          | .dict items =>
            let (h1, y) := h.alloc (.dict [])
            let h2 := h1.remember x y
            let (h3, ys) ← deepPairs fuel h2 items
            pure (h3.set y (.dict ys), y)
          | .atom _ => .ok (h, x)

  /-- `for a in x: append(deepcopy(a, memo))`. -/
  def deepList : Nat → Heap → List Nat → Py (Heap × List Nat)
    | 0, _, _ => .error .modelFuel
    | _ + 1, h, [] => .ok (h, [])
    | fuel + 1, h, a :: as => do
      let (h1, y) ← deepcopy fuel h a
      let (h2, ys) ← deepList fuel h1 as
      pure (h2, y :: ys)

  /-- `y[deepcopy(key, memo)] = deepcopy(value, memo)`. The key is copied first. -/
  def deepPairs : Nat → Heap → List (Nat × Nat) → Py (Heap × List (Nat × Nat))
    | 0, _, _ => .error .modelFuel
    | _ + 1, h, [] => .ok (h, [])
    | fuel + 1, h, (k, v) :: rest => do
      let (h1, k') ← deepcopy fuel h k
      let (h2, v') ← deepcopy fuel h1 v
      let (h3, ys) ← deepPairs fuel h2 rest
      pure (h3, (k', v') :: ys)
end

/-- `_deepcopy_method`, Lib/copy.py:206-207: the function is shared, `__self__` is deep-copied. -/
def deepMethod (fuel : Nat) (h : Heap) (func self : Nat) : Py (Heap × Nat × Nat) := do
  let (h', s) ← deepcopy fuel h self
  pure (h', func, s)

/-- What `copy(x)` does by type, Lib/copy.py:62-100. -/
inductive CopyKind where
  | atomic
  | builtinContainer
  | isType
  | hasCopy
  /-- A `__reduce_ex__` result: a string, or a tuple of this length. -/
  | reduceStr
  | reduceTuple (len : Nat)
  deriving Repr, DecidableEq

/-- The route `copy` takes. `_reconstruct(x, None, *rv)`, Lib/copy.py:228-230, takes at most five
values; a six-item `__reduce__` tuple with a `state_setter`, which `pickle` accepts, raises `TypeError`. -/
def copyRoute : CopyKind → Py String
  | .atomic => .ok "same"
  | .builtinContainer => .ok "cls.copy"
  | .isType => .ok "same"
  | .hasCopy => .ok "__copy__"
  | .reduceStr => .ok "same"
  | .reduceTuple n =>
    if n < 2 then .error (.typeError "~_reconstruct() missing required positional arguments")
    else if n > 5 then .error (.typeError "~_reconstruct() takes too many positional arguments")
    else .ok "reconstruct"

/-- `pickle` accepts two to six items, Modules/_pickle.c `save_reduce`. -/
def pickleReduceOk (n : Nat) : Bool := decide (2 ≤ n) && decide (n ≤ 6)

/-- The state step of `_reconstruct`, Lib/copy.py:238-252: `(state, slotstate)` for a 2-tuple. -/
def stateStep {α : Type} (st : Option (List (String × α))) (slot : Option (List (String × α)))
    (d : List (String × α)) : List (String × α) :=
  let d := match st with
    | some s => d ++ s
    | none => d
  match slot with
  | some s => d ++ s
  | none => d

/-- `replace(obj, **changes)`, Lib/copy.py:276-286. -/
def replaceRoute (hasReplace : Bool) (cls : String) : Py Unit :=
  if hasReplace then .ok () else .error (.typeError s!"replace() does not support {cls} objects")

/-! ### `Lib/abc.py` -/

/-- A class as `update_abstractmethods` sees it: the abstract names of its bases, the abstractness of a
name as seen from the class, and its own namespace. -/
structure AbcClass where
  hasAbstractmethods : Bool
  parents : List (List String)
  isAbstract : String → Bool
  own : List (String × Bool)

/-- `update_abstractmethods`, Lib/abc.py:146-181: the new `__abstractmethods__`, in discovery order,
or `none` when the class is not an ABC. -/
def updateAbstract (c : AbcClass) : Option (List String) :=
  if !c.hasAbstractmethods then none
  else
    let fromParents := c.parents.flatMap (fun names => names.filter c.isAbstract)
    some (fromParents ++ (c.own.filter Prod.snd).map Prod.fst)

/-- `abstractmethod`, Lib/abc.py:7-25, and `abstractclassmethod.__init__`,
`abstractstaticmethod.__init__`: the flag is set on the function. -/
def markAbstract (flags : List (String × Bool)) : List (String × Bool) :=
  ("__isabstractmethod__", true) :: flags.filter (fun p => p.1 ≠ "__isabstractmethod__")

/-- A class as an ABC check sees it. -/
structure AbcWorld where
  /-- `__subclasshook__`: `some b`, or `none` for `NotImplemented`. -/
  hook : Nat → Nat → Option Bool
  mro : Nat → List Nat
  /-- `cls._abc_registry`. -/
  registry : Nat → List Nat
  subclasses : Nat → List Nat

/-- `_abc__abc_subclasscheck_impl`, Modules/_abc.c, without the caches: the hook, the MRO, the
registry, and the subclasses. `ABCMeta.__subclasscheck__`, Lib/abc.py:121-123, delegates to it. -/
def abcSubclassCheck (W : AbcWorld) : (fuel : Nat) → (cls sub : Nat) → Bool
  | 0, _, _ => false
  | fuel + 1, cls, sub =>
    match W.hook cls sub with
    | some b => b
    | none =>
      (W.mro sub).contains cls ||
      (W.registry cls).any (fun r => abcSubclassCheck W fuel r sub) ||
      (W.subclasses cls).any (fun s => abcSubclassCheck W fuel s sub)

/-- `ABCMeta.register`, Lib/abc.py:110-115, through `_abc__abc_register_impl`: returns the class; a
cycle raises `RuntimeError`. -/
def abcRegister (W : AbcWorld) (fuel : Nat) (cls sub : Nat) : Py (Nat × Bool) :=
  if abcSubclassCheck W fuel cls sub then .ok (sub, false)
  else if abcSubclassCheck W fuel sub cls then
    .error (.named "RuntimeError" "Refusing to create an inheritance cycle")
  else .ok (sub, true)

end PyLean.CoreLibs.Operator
