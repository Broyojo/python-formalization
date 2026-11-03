import PyLean.Core

/-!
`Lib/operator.py` and `Modules/_operator.c`, the functions (CPython 3.15.2).

Nearly every function here is one line, and that line is an entry into the object protocols: `a + b` in
Python reaches `PyNumber_Add` through `BINARY_OP`, and `_operator_add_impl` calls it directly. So the two twins
of such a function are one program, and what is mirrored here is that program: `binary_op1` and
`slot_nb_*` with their slot identities, `sq_concat` and `sq_repeat`, `do_richcompare`, `PyObject_IsTrue`,
`PyObject_GetItem` and the rest, in Objects/abstract.c, Objects/object.c and Objects/typeobject.c.

Where the twins are different programs (`concat`, `iconcat`, `length_hint`, `index`, `indexOf`, `countOf`, the
callable classes), each is mirrored on its own.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- A dunder's result: a value, or `NotImplemented`. -/
inductive Ret (α : Type) where
  | val (a : α)
  | notImplemented
  deriving Repr, DecidableEq, Inhabited

/-! ### `binary_op1` and the number slots -/

/-- A number slot of a type. Its identity counts, because `binary_op1` compares slot pointers. -/
structure Slot (α : Type) where
  id : Nat
  run : α → α → Py (Ret α)

/-- What `binary_op1` reads for one operator and one pair of operands. -/
structure BinArgs (α : Type) where
  /-- `NB_BINOP(Py_TYPE(v)->tp_as_number, op_slot)`. -/
  sv : Option (Slot α)
  sw : Option (Slot α)
  /-- `Py_IS_TYPE(w, Py_TYPE(v))`. -/
  sameType : Bool
  /-- `PyType_IsSubtype(Py_TYPE(w), Py_TYPE(v))`. -/
  subtype : Bool
  lt : String
  rt : String

/-- `slotw` of `binary_op1`, Objects/abstract.c:954-963: null for the same type and for the same slot. -/
def BinArgs.slotw {α : Type} (A : BinArgs α) : Option (Slot α) :=
  if A.sameType then none else
  match A.sw, A.sv with
  | some w, some v => if w.id = v.id then none else some w
  | w, _ => w

/-- `binary_op1`, Objects/abstract.c:940-990. -/
def binaryOp1 {α : Type} (A : BinArgs α) (v w : α) : Py (Ret α) :=
  match A.sv with
  | none =>
    match A.slotw with
    | some sw => sw.run v w
    | none => .ok .notImplemented
  | some sv =>
    match A.slotw with
    | none => sv.run v w
    | some sw =>
      if A.subtype then
        match sw.run v w with
        | .error e => .error e
        | .ok (.val x) => .ok (.val x)
        | .ok .notImplemented => sv.run v w   -- `slotw = NULL`
      else
        match sv.run v w with
        | .error e => .error e
        | .ok (.val x) => .ok (.val x)
        | .ok .notImplemented => sw.run v w

def binopError (sym lt rt : String) : PyExc :=
  .typeError s!"unsupported operand type(s) for {sym}: '{lt}' and '{rt}'"

/-- `binary_op`, Objects/abstract.c:1010-1019: `PyNumber_Subtract` and the rest of `BINARY_FUNC`, so the body of
`a - b`, `a & b`, ... in Python and of `_operator_sub_impl`, ... in C. -/
def binaryOp {α : Type} (A : BinArgs α) (sym : String) (v w : α) : Py α :=
  match binaryOp1 A v w with
  | .error e => .error e
  | .ok (.val x) => .ok x
  | .ok .notImplemented => .error (binopError sym A.lt A.rt)

/-- What a heap class gives one operator, as `SLOT1BINFULL` in Objects/typeobject.c sees it: the slot is
the same C function for every class, so the reflected logic lives here and not in `binary_op1`. -/
structure HeapPair (α : Type) where
  /-- `Py_TYPE(self)->tp_as_number->SLOTNAME == TESTFUNC`, and the same for `other`. -/
  selfHeap : Bool
  otherHeap : Bool
  sameType : Bool
  subtype : Bool
  /-- `method_is_overloaded(self, other, RDUNDER)`. -/
  overloaded : Py Bool
  /-- `vectorcall_maybe(DUNDER)` on `self, other`, `NotImplemented` when the method is missing. -/
  dunder : α → α → Py (Ret α)
  /-- `vectorcall_maybe(RDUNDER)` on `other, self`. -/
  rdunder : α → α → Py (Ret α)

/-- `SLOT1BINFULL`, Objects/typeobject.c. `__rop__` runs first when `other` is a subclass that overrides it. -/
def slotBinary {α : Type} (P : HeapPair α) (self other : α) : Py (Ret α) :=
  let doOther := !P.sameType && P.otherHeap
  let last (d : Bool) : Py (Ret α) := if d then P.rdunder other self else .ok .notImplemented
  let forward (d : Bool) : Py (Ret α) :=
    match P.dunder self other with
    | .error e => .error e
    | .ok (.val x) => .ok (.val x)
    | .ok .notImplemented => if P.sameType then .ok .notImplemented else last d
  if P.selfHeap then
    if doOther && P.subtype then
      match P.overloaded with
      | .error e => .error e
      | .ok false => forward doOther
      | .ok true =>
        match P.rdunder other self with
        | .error e => .error e
        | .ok (.val x) => .ok (.val x)
        | .ok .notImplemented => forward false
    else forward doOther
  else last doOther

/-! ### `+` and `*`, with the sequence slots -/

/-- The sequence slots `PyNumber_Add` and `PyNumber_Multiply` read. `hasV` and `hasW` are `tp_as_sequence !=
NULL`, which holds for every heap class, whether or not it has `__mul__` or `__add__`. -/
structure SeqArgs (α : Type) where
  concat : Option (α → α → Py α)
  iconcat : Option (α → α → Py α)
  repeatV : Option (α → Int → Py α)
  irepeatV : Option (α → Int → Py α)
  repeatW : Option (α → Int → Py α)
  hasV : Bool
  hasW : Bool
  /-- `_PyIndex_Check(x)`, with what `_PyNumber_Index(x)` gives. -/
  index : α → Option (Py Int)
  tn : α → String

/-- The range test of `PyNumber_AsSsize_t`, Objects/abstract.c:1468-1512, with `err` as the exception. -/
def fitSsize (mk : String → PyExc) (tn : String) (n : Int) : Py Int :=
  if n > ssizeMax ∨ n < ssizeMin then .error (mk s!"cannot fit '{tn}' into an index-sized integer")
  else .ok n

/-- `sequence_repeat`, Objects/abstract.c:1156-1173. -/
def sequenceRepeat {α : Type} (Q : SeqArgs α) (f : α → Int → Py α) (seq n : α) : Py α :=
  match Q.index n with
  | none => .error (.typeError s!"can't multiply sequence by non-int of type '{Q.tn n}'")
  | some r =>
    match r with
    | .error e => .error e
    | .ok i =>
      match fitSsize .overflowError (Q.tn n) i with
      | .error e => .error e
      | .ok c => f seq c

/-- `PyNumber_Add`, Objects/abstract.c:1137-1154, for `a + b` and `_operator_add_impl`. -/
def numberAdd {α : Type} (A : BinArgs α) (Q : SeqArgs α) (v w : α) : Py α :=
  match binaryOp1 A v w with
  | .error e => .error e
  | .ok (.val x) => .ok x
  | .ok .notImplemented =>
    match Q.concat with
    | some f => f v w
    | none => .error (binopError "+" A.lt A.rt)

/-- `PyNumber_Multiply`, Objects/abstract.c:1176-1192, for `a * b` and `_operator_mul_impl`. -/
def numberMul {α : Type} (A : BinArgs α) (Q : SeqArgs α) (v w : α) : Py α :=
  match binaryOp1 A v w with
  | .error e => .error e
  | .ok (.val x) => .ok x
  | .ok .notImplemented =>
    match Q.repeatV with
    | some f => sequenceRepeat Q f v w
    | none =>
      match Q.repeatW with
      | some f => sequenceRepeat Q f w v
      | none => .error (binopError "*" A.lt A.rt)

/-- `ternary_op`, Objects/abstract.c:1029-1121, with `z` being `None`: `NoneType` has no `nb_power`, so the
third step finds nothing and the order is that of `binary_op1`. `op_name` is what the error says. -/
def ternaryOp {α : Type} (A : BinArgs α) (name : String) (v w : α) : Py α :=
  binaryOp A name v w

/-- `PyNumber_Power(a, b, None)`, for `a ** b` and `_operator_pow_impl`. -/
def numberPow {α : Type} (A : BinArgs α) (v w : α) : Py α := ternaryOp A "** or pow()" v w

/-! ### In-place operators -/

/-- `binary_iop1`, Objects/abstract.c:1227-1251: the in-place slot, then `binary_op1`. -/
def binaryIop1 {α : Type} (iop : Option (α → α → Py (Ret α))) (A : BinArgs α) (v w : α) : Py (Ret α) :=
  match iop with
  | none => binaryOp1 A v w
  | some f =>
    match f v w with
    | .error e => .error e
    | .ok (.val x) => .ok (.val x)
    | .ok .notImplemented => binaryOp1 A v w

/-- `binary_iop`, Objects/abstract.c:1259-1269: `PyNumber_InPlaceSubtract` and the rest of `INPLACE_BINOP`. -/
def inplaceOp {α : Type} (iop : Option (α → α → Py (Ret α))) (A : BinArgs α) (sym : String) (v w : α) :
    Py α :=
  match binaryIop1 iop A v w with
  | .error e => .error e
  | .ok (.val x) => .ok x
  | .ok .notImplemented => .error (binopError sym A.lt A.rt)

/-- `PyNumber_InPlaceAdd`, Objects/abstract.c:1306-1327. -/
def inplaceAdd {α : Type} (iop : Option (α → α → Py (Ret α))) (A : BinArgs α) (Q : SeqArgs α) (v w : α) :
    Py α :=
  match binaryIop1 iop A v w with
  | .error e => .error e
  | .ok (.val x) => .ok x
  | .ok .notImplemented =>
    let err : Py α := .error (binopError "+=" A.lt A.rt)
    if Q.hasV then
      match Q.iconcat with
      | some f => f v w
      | none =>
        match Q.concat with
        | some f => f v w
        | none => err
    else err

/-- `PyNumber_InPlaceMultiply`, Objects/abstract.c:1329-1356. The right operand's `sq_repeat` is tried only
under `else if (mw != NULL)`, so only when the left type has no `tp_as_sequence` at all. A heap class always
has it, with or without a repeat slot, which is where this differs from `PyNumber_Multiply`. -/
def inplaceMul {α : Type} (iop : Option (α → α → Py (Ret α))) (A : BinArgs α) (Q : SeqArgs α) (v w : α) :
    Py α :=
  match binaryIop1 iop A v w with
  | .error e => .error e
  | .ok (.val x) => .ok x
  | .ok .notImplemented =>
    let err : Py α := .error (binopError "*=" A.lt A.rt)
    if Q.hasV then
      match Q.irepeatV with
      | some f => sequenceRepeat Q f v w
      | none =>
        match Q.repeatV with
        | some f => sequenceRepeat Q f v w
        | none => err
    else if Q.hasW then
      match Q.repeatW with
      | some f => sequenceRepeat Q f w v
      | none => err
    else err

/-- `ternary_iop`, Objects/abstract.c:1271-1287, with `z` being `None`: `PyNumber_InPlacePower`. -/
def inplacePow {α : Type} (iop : Option (α → α → Py (Ret α))) (A : BinArgs α) (v w : α) : Py α :=
  match iop with
  | none => ternaryOp A "**=" v w
  | some f =>
    match f v w with
    | .error e => .error e
    | .ok (.val x) => .ok x
    | .ok .notImplemented => ternaryOp A "**=" v w

/-! ### Comparison -/

inductive RichOp where
  | lt | le | eq | ne | gt | ge
  deriving Repr, DecidableEq

def RichOp.sym : RichOp → String
  | .lt => "<" | .le => "<=" | .eq => "==" | .ne => "!=" | .gt => ">" | .ge => ">="

/-- `_Py_swapped_op`, Objects/object.c:1044. -/
def RichOp.swapped : RichOp → RichOp
  | .lt => .gt | .le => .ge | .eq => .eq | .ne => .ne | .gt => .lt | .ge => .le

/-- What `do_richcompare` reads. The result is any object, so it has the type of the operands, and `ofBool`
gives `True` and `False`. `identical` is `v == w` on the pointers. -/
structure CmpArgs (α : Type) where
  rv : Option (RichOp → α → α → Py (Ret α))
  rw : Option (RichOp → α → α → Py (Ret α))
  sameType : Bool
  subtype : Bool
  identical : Bool
  ofBool : Bool → α
  lt : String
  rt : String

/-- `do_richcompare`, Objects/object.c:1049-1097. The result is what the method returned, unconverted. -/
def richCompare {α : Type} (A : CmpArgs α) (op : RichOp) (v w : α) : Py α :=
  let default : Py α :=
    match op with
    | .eq => .ok (A.ofBool A.identical)
    | .ne => .ok (A.ofBool (!A.identical))
    | _ => .error (.typeError
        s!"'{op.sym}' not supported between instances of '{A.lt}' and '{A.rt}'")
  let reverse : Py α :=
    match A.rw with
    | none => default
    | some f =>
      match f op.swapped w v with
      | .error e => .error e
      | .ok (.val x) => .ok x
      | .ok .notImplemented => default
  let forward (next : Py α) : Py α :=
    match A.rv with
    | none => next
    | some f =>
      match f op v w with
      | .error e => .error e
      | .ok (.val x) => .ok x
      | .ok .notImplemented => next
  let first := !A.sameType && A.subtype && A.rw.isSome
  if first then
    match A.rw with
    | none => default
    | some f =>
      match f op.swapped w v with
      | .error e => .error e
      | .ok (.val x) => .ok x
      | .ok .notImplemented => forward default
  else forward reverse

/-- `object_richcompare`, Objects/typeobject.c, the slot of a class that does not define the operator: `==`
is identity, `!=` runs `__eq__` and inverts the truth of its result, and the orderings do not answer. -/
def objectRichcompare {α : Type} (identical : Bool) (ofBool : Bool → α) (eq : Py (Ret α))
    (truth : α → Py Bool) (op : RichOp) : Py (Ret α) :=
  match op with
  | .eq => if identical then .ok (.val (ofBool true)) else .ok .notImplemented
  | .ne =>
    match eq with
    | .error e => .error e
    | .ok .notImplemented => .ok .notImplemented
    | .ok (.val r) =>
      match truth r with
      | .error e => .error e
      | .ok b => .ok (.val (ofBool (!b)))
  | _ => .ok .notImplemented

/-! ### Truth -/

/-- An object as `PyObject_IsTrue` sees it. -/
inductive TruthObj where
  | tru
  | fals
  | none
  /-- `nb_bool`, or a `__bool__` returning a `bool`, or raising. -/
  | bool (r : Py Bool)
  /-- A `__bool__` returning this type, which is not `bool`. -/
  | badBool (rn tn : String)
  /-- `__bool__ = None`. -/
  | noneBool (tn : String)
  /-- `__len__`, its result as an `int`. -/
  | len (r : Py Int)
  /-- No truth slot at all. -/
  | plain

/-- `slot_sq_length`, Objects/typeobject.c: not negative, tested first, and then it must fit. -/
def sqLength (r : Py Int) : Py Int :=
  match r with
  | .error e => .error e
  | .ok n =>
    if n < 0 then .error (.valueError "__len__() should return >= 0")
    else fitSsize .overflowError "int" n

/-- `PyObject_IsTrue`, Objects/object.c:2139-2164, with `slot_nb_bool`, Objects/typeobject.c:10904. -/
def isTrue : TruthObj → Py Bool
  | .tru => .ok true
  | .fals => .ok false
  | .none => .ok false
  | .bool r => r
  | .badBool rn tn => .error (.typeError s!"{rn}.__bool__() must return a bool, not {tn}")
  | .noneBool tn => .error (.typeError s!"'{tn}' cannot be interpreted as a boolean")
  | .len r =>
    match sqLength r with
    | .error e => .error e
    | .ok n => .ok (decide (n > 0))
  | .plain => .ok true

/-- `truth(a)`, Lib/operator.py:57-59: `True if a else False`; `_operator_truth_impl`, Modules/_operator.c:51. -/
def truthOp (o : TruthObj) : Py Bool := isTrue o

/-- `not_(a)`, Lib/operator.py:53-55, and `PyObject_Not`, Objects/object.c:2167-2174, through
`_operator_not__impl`, Modules/_operator.c:253. -/
def notOp (o : TruthObj) : Py Bool :=
  match isTrue o with
  | .error e => .error e
  | .ok b => .ok (!b)

/-! ### Unary operators and `index` -/

inductive UnOp where
  | neg | pos | abs | inv
  deriving Repr, DecidableEq

def UnOp.desc : UnOp → String
  | .neg => "unary -" | .pos => "unary +" | .abs => "abs()" | .inv => "unary ~"

/-- `UNARY_FUNC`, Objects/abstract.c:1371-1389: `-a`, `+a`, `abs(a)` and `~a` in Python, and `PyNumber_Negative`
and the others in `_operator_neg`, ... in C. -/
def unaryOp {α : Type} (slot : Option (α → Py α)) (op : UnOp) (tn : String) (v : α) : Py α :=
  match slot with
  | some f => f v
  | none => .error (.typeError s!"bad operand type for {op.desc}: '{tn}'")

/-- What an `__index__` gives. -/
inductive IndexRet where
  | exact (n : Int)
  /-- An instance of a strict subclass of `int`, with this value. -/
  | sub (n : Int)
  | other (tn : String)
  deriving Repr, DecidableEq

/-- What `operator.index` reads of its operand. The Python twin does an attribute lookup and the C twin reads
the type's slot, so they can see two different things. -/
structure IndexObj where
  /-- `PyLong_Check(item)`, with its value. -/
  isInt : Option Int
  /-- `nb_index` of the type, run. -/
  slot : Option (Py IndexRet)
  /-- An `__index__` in the instance dict, run. A type attribute that is not a data descriptor loses to it. -/
  inst : Option (Py IndexRet)
  tn : String
  /-- The `DeprecationWarning` of Objects/abstract.c:1442, when it raises. -/
  warn : Option PyExc

/-- `index(a)`, Lib/operator.py:95-97: `a.__index__()`, whatever that returns. -/
def indexPy (o : IndexObj) : Py IndexRet :=
  match o.inst with
  | some r => r
  | none =>
    match o.isInt with
    | some n => .ok (.exact n)
    | none =>
      match o.slot with
      | some r => r
      | none => .error (.named "AttributeError" s!"'{o.tn}' object has no attribute '__index__'")

/-- `_operator_index`, Modules/_operator.c:698-702, through `PyNumber_Index`, Objects/abstract.c:1452-1460, and
`_PyNumber_Index`, :1410-1447. -/
def indexC (o : IndexObj) : Py IndexRet :=
  match o.isInt with
  | some n => .ok (.exact n)
  | none =>
    match o.slot with
    | none => .error (.typeError s!"'{o.tn}' object cannot be interpreted as an integer")
    | some r =>
      match r with
      | .error e => .error e
      | .ok (.exact n) => .ok (.exact n)
      | .ok (.other tn) => .error (.typeError s!"{o.tn}.__index__() must return an int, not {tn}")
      | .ok (.sub n) =>
        match o.warn with
        | some e => .error e
        | none => .ok (.exact n)

/-! ### Subscripts -/

/-- What `PyObject_GetItem` reads for `o[key]`. -/
structure GetArgs (α : Type) where
  /-- `mp_subscript(o, key)`. -/
  mp : Option (Py α)
  /-- `sq_item`. -/
  sqItem : Option (Int → Py α)
  /-- `sq_length(o)`. -/
  sqLen : Option (Py Int)
  /-- `PyType_Check(o)`: for `type` itself, the `GenericAlias`; for another class, what its
  `__class_getitem__` gives, `none` when it has none or it is `None`. -/
  asType : Option (Py (Option α))
  /-- `_PyIndex_Check(key)`. -/
  keyIndex : Option (Py Int)
  tn : String
  keyTn : String

/-- `PySequence_GetItem`, Objects/abstract.c:1841-1867, with `sq_item` present. -/
def sequenceGetItem {α : Type} (A : GetArgs α) (f : Int → Py α) (i : Int) : Py α :=
  if i < 0 then
    match A.sqLen with
    | none => f i
    | some l =>
      match l with
      | .error e => .error e
      | .ok n => f (i + n)
  else f i

/-- `PyObject_GetItem`, Objects/abstract.c:155-201: `a[b]`, and `_operator_getitem_impl`. -/
def getItem {α : Type} (A : GetArgs α) : Py α :=
  match A.mp with
  | some r => r
  | none =>
    match A.sqItem with
    | some f =>
      match A.keyIndex with
      | none => .error (.typeError s!"sequence index must be integer, not '{A.keyTn}'")
      | some r =>
        match r with
        | .error e => .error e
        | .ok n =>
          match fitSsize .indexError A.keyTn n with
          | .error e => .error e
          | .ok i => sequenceGetItem A f i
    | none =>
      match A.asType with
      | some r =>
        match r with
        | .error e => .error e
        | .ok (some v) => .ok v
        | .ok none => .error (.typeError s!"type '{A.tn}' is not subscriptable")
      | none => .error (.typeError s!"'{A.tn}' object is not subscriptable")

/-- What `PyObject_SetItem` and `PyObject_DelItem` read. `σ` is the effect. -/
structure SetArgs (σ : Type) where
  /-- `mp_ass_subscript`. -/
  mp : Option (Py σ)
  /-- `tp_as_sequence != NULL`. -/
  hasSeq : Bool
  /-- `sq_ass_item`. -/
  sqAss : Option (Int → Py σ)
  sqLen : Option (Py Int)
  keyIndex : Option (Py Int)
  tn : String
  keyTn : String

def objMsg (tn what : String) : PyExc := .typeError s!"'{tn}' object {what}"

/-- `PySequence_SetItem`, :1893-1917, and `PySequence_DelItem`, :1926-1950, with the message of the last line. -/
def sequenceSet {σ : Type} (A : SetArgs σ) (i : Int) (notSupported : String) : Py σ :=
  match A.sqAss with
  | some f =>
    if i < 0 then
      match A.sqLen with
      | none => f i
      | some l =>
        match l with
        | .error e => .error e
        | .ok n => f (i + n)
    else f i
  | none =>
    match A.mp with
    | some _ => .error (.typeError s!"{A.tn} is not a sequence")
    | none => .error (objMsg A.tn notSupported)

/-- The shared body of `PyObject_SetItem`, Objects/abstract.c:236-267, and `PyObject_DelItem`, :270-301. -/
def assignItem {σ : Type} (A : SetArgs σ) (bottom seqBottom : String) : Py σ :=
  match A.mp with
  | some r => r
  | none =>
    let err : Py σ := .error (objMsg A.tn bottom)
    if A.hasSeq then
      match A.keyIndex with
      | some r =>
        match r with
        | .error e => .error e
        | .ok n =>
          match fitSsize .indexError A.keyTn n with
          | .error e => .error e
          | .ok i => sequenceSet A i seqBottom
      | none =>
        match A.sqAss with
        | some _ => .error (.typeError s!"sequence index must be integer, not '{A.keyTn}'")
        | none => err
    else err

/-- `a[b] = c`, and `_operator_setitem_impl`. -/
def setItem {σ : Type} (A : SetArgs σ) : Py σ :=
  assignItem A "does not support item assignment" "does not support item assignment"

/-- `del a[b]`, and `_operator_delitem_impl`. The sequence path has another wording, Objects/abstract.c:1948. -/
def delItem {σ : Type} (A : SetArgs σ) : Py σ :=
  assignItem A "does not support item deletion" "doesn't support item deletion"

/-! ### Iteration: `countOf`, `indexOf`, `contains` -/

/-- `iter(a)`: it failed, or it gives these items and then ends or raises. -/
inductive IterArg (α : Type) where
  | fail (e : PyExc)
  | items (xs : List α) (err : Option PyExc)

/-- `i is b or i == b` in Python, and `PyObject_RichCompareBool(item, obj, Py_EQ)`, Objects/object.c:1122-1154,
in C, with the truth test of the result. The `==` may raise, and so may `__bool__` of what it returns. -/
abbrev Same (α : Type) := α → α → Py Bool

/-- The `TypeError` handling of `_PySequence_IterSearch`, Objects/abstract.c:2150-2162. `PyErr_ExceptionMatches`
also matches a subclass of `TypeError`; `PyExc` has no class hierarchy, so such an exception is modelled as
`.typeError` (scope limit). -/
def iterError (tn : String) (contains : Bool) (e : PyExc) : PyExc :=
  match e with
  | .typeError _ =>
    if contains then .typeError s!"argument of type '{tn}' is not a container or iterable"
    else .typeError s!"argument of type '{tn}' is not iterable"
  | e => e

/-- The loop of `countOf`, Lib/operator.py:168-171, and of `_PySequence_IterSearch` with
`PY_ITERSEARCH_COUNT`, Objects/abstract.c:2166-2215. The next item is read after the comparison. -/
def countLoop {α : Type} (same : Same α) (b : α) : Nat → List α → Option PyExc → Py Nat
  | n, [], none => .ok n
  | _, [], some e => .error e
  | n, x :: xs, e =>
    match same x b with
    | .error e' => .error e'
    | .ok hit => countLoop same b (if hit then n + 1 else n) xs e

def countOfPy {α : Type} (same : Same α) (b : α) : IterArg α → Py Nat
  | .fail e => .error e
  | .items xs e => countLoop same b 0 xs e

/-- `_operator_countOf_impl`, Modules/_operator.c:521, through `PySequence_Count`. -/
def countOfC {α : Type} (same : Same α) (tn : String) (b : α) : IterArg α → Py Nat
  | .fail e => .error (iterError tn false e)
  | .items xs e => countLoop same b 0 xs e

def indexMsg := "sequence.index(x): x not in sequence"

/-- The loop of `indexOf`, Lib/operator.py:183-187, and `PY_ITERSEARCH_INDEX`. -/
def indexLoop {α : Type} (same : Same α) (b : α) : Nat → List α → Option PyExc → Py Nat
  | _, [], none => .error (.valueError indexMsg)
  | _, [], some e => .error e
  | i, x :: xs, e =>
    match same x b with
    | .error e' => .error e'
    | .ok true => .ok i
    | .ok false => indexLoop same b (i + 1) xs e

def indexOfPy {α : Type} (same : Same α) (b : α) : IterArg α → Py Nat
  | .fail e => .error e
  | .items xs e => indexLoop same b 0 xs e

/-- `_operator_indexOf_impl`, Modules/_operator.c:508, through `PySequence_Index`. -/
def indexOfC {α : Type} (same : Same α) (tn : String) (b : α) : IterArg α → Py Nat
  | .fail e => .error (iterError tn false e)
  | .items xs e => indexLoop same b 0 xs e

/-- `PY_ITERSEARCH_CONTAINS`. -/
def containsLoop {α : Type} (same : Same α) (b : α) : List α → Option PyExc → Py Bool
  | [], none => .ok false
  | [], some e => .error e
  | x :: xs, e =>
    match same x b with
    | .error e' => .error e'
    | .ok true => .ok true
    | .ok false => containsLoop same b xs e

/-- `PySequence_Contains`, Objects/abstract.c:2240-2250: `b in a`, Lib/operator.py:161-163, and
`_operator_contains_impl`, Modules/_operator.c:491. The container is the first argument of `contains`. -/
def containsOp {α : Type} (slot : Option (Py Bool)) (same : Same α) (tn : String) (b : α) (a : IterArg α) :
    Py Bool :=
  match slot with
  | some r => r
  | none =>
    match a with
    | .fail e => .error (iterError tn true e)
    | .items xs e => containsLoop same b xs e

/-- `call(obj, /, *args, **kwargs)`, Lib/operator.py:234-236: a missing `obj` is the signature's `TypeError`. -/
def callPy {α β : Type} (apply : α → List α → List (String × α) → Py β) (pos : List α)
    (kw : List (String × α)) : Py β :=
  match pos with
  | [] => .error (.typeError "call() missing 1 required positional argument: 'obj'")
  | obj :: rest => apply obj rest kw

/-- `_operator_call`, Modules/_operator.c:928-937. -/
def callC {α β : Type} (apply : α → List α → List (String × α) → Py β) (pos : List α)
    (kw : List (String × α)) : Py β :=
  match pos with
  | [] => .error (.typeError "call expected at least 1 argument, got 0")
  | obj :: rest => apply obj rest kw

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

/-- `PyNumber_Add`, Objects/abstract.c:1138: `nb_add`, then `sq_concat`. -/
def plus {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α := do
  match ← A.nbAdd a b with
  | .val x => pure x
  | .notImplemented =>
    match A.sqConcat with
    | some f => f a b
    | none => throw (binopError "+" lt rt)

/-- `PyNumber_InPlaceAdd`, Objects/abstract.c:1307: `nb_inplace_add` and `nb_add`, then the sequence
slots. -/
def plusEq {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α := do
  match ← A.nbIAdd a b with
  | .val x => pure x
  | .notImplemented =>
    match A.sqInplace, A.sqConcat with
    | some f, _ => f a b
    | none, some f => f a b
    | none, none => throw (binopError "+=" lt rt)

/-- `concat`, Lib/operator.py:154-159. -/
def concatPy {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α :=
  if !A.hasGetitem then .error (noConcat lt) else plus A lt rt a b

/-- `iconcat`, Lib/operator.py:357-363. -/
def iconcatPy {α : Type} (A : ConcatArgs α) (lt rt : String) (a b : α) : Py α :=
  if !A.hasGetitem then .error (noConcat lt) else plusEq A lt rt a b

/-- `_operator_concat_impl`, Modules/_operator.c:461-465, through `PySequence_Concat`,
Objects/abstract.c:1721-1744. -/
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
Objects/abstract.c:1778-1804. -/
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

/-! ### `length_hint` -/

/-- What `__length_hint__` returns. -/
inductive HintRet where
  | int (n : Int)
  | notImplemented
  /-- Something that is not an `int`, of the named type. -/
  | other (tn : String)
  deriving Repr, DecidableEq

/-- What the class holds as `__length_hint__`. The twins reach it differently: C through `_PyObject_LookupSpecial`
(Objects/abstract.c:113), which runs the descriptor's `__get__` with the object, then a call with no argument
(:120); Python through `type(obj).__length_hint__` (Lib/operator.py:213-216), which runs `__get__` with no
instance, then `hint(obj)` (:218-221). -/
inductive HintDesc where
  /-- A function: C calls the bound method, Python the function with `obj`; one call, this outcome. -/
  | func (r : Py HintRet)
  /-- A `staticmethod`: both unwrap it; C calls it with no argument (`noArg`), Python with `obj` (`withObj`). -/
  | static (noArg withObj : Py HintRet)
  /-- A `property`: C's lookup runs the getter on `obj`, which can raise, and calls what it returns (`get`);
  Python gets the property object itself, and calling it is a `TypeError`. -/
  | prop (get : Py (Py HintRet))
  deriving Repr

/-- C: the lookup's exception, or the outcome of the call. -/
def hintLookupC : HintDesc → Py (Py HintRet)
  | .func r => .ok r
  | .static r _ => .ok r
  | .prop g => g

/-- Python: the outcome of `hint(obj)`. -/
def hintCallPy : HintDesc → Py HintRet
  | .func r => r
  | .static _ r => r
  | .prop _ => .error (.typeError "'property' object is not callable")

/-- What `length_hint` sees of an object. -/
structure HintObj where
  /-- `len(obj)`; a missing `__len__` is the `TypeError` case. -/
  len : Py Nat
  /-- `__length_hint__` on the class; `none` when there is none. -/
  hint : Option HintDesc
  /-- `%T` of the object. -/
  tn : String := "O"
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

/-- The message of `PyObject_LengthHint`, Objects/abstract.c:147-148. -/
def negativeHintC (o : HintObj) : String := s!"{o.tn}.__length_hint__() must return a non-negative int"

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
    match hintCallPy h with
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
of `default` to `Py_ssize_t`, and `PyObject_LengthHint`, Objects/abstract.c:95-150, whose `_PyObject_LookupSpecial` failure propagates whatever its class (:113-116). -/
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
    match hintLookupC h with
    | .error e => throw e
    | .ok call =>
      match call with
      | .error e => if isTypeError e then pure d else throw e
      | .ok .notImplemented => pure d
      | .ok (.other tn) => throw (.typeError s!"{o.tn}.__length_hint__() must return an int, not {tn}")
      | .ok (.int v) =>
        let r ← toSsize v
        if r < 0 then throw (.valueError (negativeHintC o)) else pure r

/-! ### `_compare_digest` -/

/-- The loop of `_tscmp`, Modules/_operator.c:802-804. -/
def tscmpLoop : Nat → List Nat → List Nat → Nat
  | r, a :: as, b :: bs => tscmpLoop (r ||| (a ^^^ b)) as bs
  | r, _, _ => r

/-- `_tscmp`, Modules/_operator.c:772-807: with unequal lengths it compares `b` with itself and
starts the result at 1. -/
def tscmp (a b : List Nat) : Bool :=
  if a.length = b.length then tscmpLoop 0 a b == 0 else tscmpLoop 1 b b == 0

/-- The arguments of `_compare_digest`. A buffer exporter's `PyObject_GetBuffer(x, PyBUF_SIMPLE)` gives a
one-dimensional view of these bytes, raises (a non-contiguous `memoryview` raises `BufferError`), or gives a view
with `ndim > 1` (a `memoryview` gives `ndim = 1` for a simple request, so that case needs another exporter). -/
inductive DigestArg where
  /-- A `str` (`PyUnicode_Check`, so a subclass too), with `Py_TYPE(x)->tp_name`. -/
  | str (ascii : Bool) (data : List Nat) (tn : String)
  | buffer (data : List Nat)
  | bufferErr (e : PyExc)
  | bufferNd
  | other (tn : String)
  deriving Repr, DecidableEq

/-- `PyObject_CheckBuffer`. -/
def DigestArg.hasBuffer : DigestArg → Bool
  | .buffer _ | .bufferErr _ | .bufferNd => true
  | _ => false

/-- `Py_TYPE(x)->tp_name` of an argument without the buffer protocol, as :877-880 print it. -/
def DigestArg.tn : DigestArg → String
  | .str _ _ tn => tn
  | .other tn => tn
  | _ => "?"

def ndimMsg := "Buffer must be single dimension"

/-- `PyObject_GetBuffer(x, &view, PyBUF_SIMPLE)` and the `ndim > 1` test, Modules/_operator.c:884-892 and
:894-904. -/
def digestBuffer : DigestArg → Py (List Nat)
  | .buffer d => .ok d
  | .bufferErr e => .error e
  | .bufferNd => .error (.named "BufferError" ndimMsg)
  | _ => .error (.typeError "~a bytes-like object is required")

/-- `_operator__compare_digest_impl`, Modules/_operator.c:852-916: two `str` compare their ASCII data (:858-870);
otherwise, with neither a buffer exporter, the `TypeError` naming both types (:876-882); else `a`'s buffer, then
`b`'s, each failing on its own (:884-904). -/
def compareDigest : DigestArg → DigestArg → Py Bool
  | .str aa a _, .str ab b _ =>
    if !aa || !ab then
      .error (.typeError "comparing strings with non-ASCII characters is not supported")
    else .ok (tscmp a b)
  | a, b =>
    if !a.hasBuffer && !b.hasBuffer then
      .error (.typeError
        s!"unsupported operand types(s) or combination of types: '{a.tn}' and '{b.tn}'")
    else
      match digestBuffer a with
      | .error e => .error e
      | .ok da =>
        match digestBuffer b with
        | .error e => .error e
        | .ok db => .ok (tscmp da db)

end PyLean.CoreLibs.Operator
