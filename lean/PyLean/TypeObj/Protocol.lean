import PyLean.TypeObj.Exceptions

/-!
The abstract object protocols: rich comparison, truth, hashing, repr/str
(`Objects/object.c`), numbers, sequences, mappings, iteration, `isinstance`
(`Objects/abstract.c`), and the `slot_*` dispatchers behind them
(`Objects/typeobject.c:9941-10630`).

Each `call*` function applies the C function stored in a slot. The builtin value types
(`int`, `str`, `tuple`, `list`, `dict`) have just enough of their C slots to exercise the
protocols; the full semantics of those types belongs to the `LongObj`, `UnicodeObj`,
`Sequences` and `DictSet` modules.
-/

namespace PyLean.TypeObj

/-! ## Truth and comparison -/

/-- `PyObject_RichCompareBool`, `Objects/object.c:1119`. -/
def richCompareBool (rt : Rt) (v w : Val) (op : CmpOp) : M Bool := do
  if v.is w then
    if op == .eq then return true
    else if op == .ne then return false
  let res ← rt.richCompare v w op
  match res with
  | .bool b => pure b
  | r => rt.isTrue r

/-- `Py_RETURN_RICHCOMPARE(a, b, op)` on integers. -/
def cmpInt (a b : Int) : CmpOp → Bool
  | .lt => a < b | .le => a ≤ b | .eq => a = b | .ne => a ≠ b | .gt => a > b | .ge => a ≥ b

/-- The shared loop of `list_richcompare_impl` (`Objects/listobject.c:3396`) and
`tuple_richcompare` (`Objects/tupleobject.c:660`) after the length shortcut: find the
first index whose items are not equal. `none` means one sequence ran out. -/
def firstDiff (rt : Rt) : List Val → List Val → M (Option (Val × Val))
  | [], _ | _, [] => pure none
  | a :: as, b :: bs => do
    if a.is b then firstDiff rt as bs
    else
      let k ← richCompareBool rt a b .eq
      if k then firstDiff rt as bs else pure (some (a, b))

/-- `tuple_richcompare`, `Objects/tupleobject.c:660`, given both item lists. -/
def seqRichcompare (rt : Rt) (vs ws : List Val) (op : CmpOp) : M Val := do
  match ← firstDiff rt vs ws with
  | none => pure (.bool (cmpInt vs.length ws.length op))
  | some (a, b) =>
    if op == .eq then pure (.bool false)
    else if op == .ne then pure (.bool true)
    else rt.richCompare a b op

/-- `list_richcompare_impl`, `Objects/listobject.c:3396`: adds the length shortcut. -/
def listRichcompare (rt : Rt) (vs ws : List Val) (op : CmpOp) : M Val :=
  if vs.length != ws.length && (op == .eq || op == .ne) then
    pure (.bool (op == .ne))
  else seqRichcompare rt vs ws op

/-- Lexicographic order of code points, `PyUnicode_Compare`. -/
def strCompare : List Char → List Char → Int
  | [], [] => 0
  | [], _ => -1
  | _, [] => 1
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then -1 else if b.toNat < a.toNat then 1 else strCompare as bs

/-- `object_richcompare`, `Objects/typeobject.c:6967`, for the cases that do not recurse
into the slot. `eqSlot` is `tp_richcompare(self, other, Py_EQ)`. -/
def objectRichcompare (rt : Rt) (eqSlot : M Val) (self other : Val) (op : CmpOp) : M Val :=
  match op with
  | .eq => pure (if self.is other then .bool true else .notImpl)
  | .ne => do
    let res ← eqSlot
    match res with
    | .notImpl => pure .notImpl
    | r =>
      let ok ← rt.isTrue r
      pure (.bool (!ok))
  | _ => pure .notImpl

/-- `slot_tp_richcompare`, `Objects/typeobject.c:10471`. -/
def slotTpRichcompare (rt : Rt) (self other : Val) (op : CmpOp) : M Val := do
  match ← maybeCallSpecial rt self op.dunder [other] false with
  | .res r => pure r
  | _ => pure .notImpl

/-- `method_richcompare`, `Objects/classobject.c:210`. -/
def methodRichcompare (rt : Rt) (self other : Val) (op : CmpOp) : M Val := do
  let w ← getW
  match op, payloadOf w self, payloadOf w other with
  | .eq, some (.bound f1 s1), some (.bound f2 s2)
  | .ne, some (.bound f1 s1), some (.bound f2 s2) =>
    let eq ← richCompareBool rt f1 f2 .eq
    let eq := eq && s1.is s2
    pure (.bool (if op == .eq then eq else !eq))
  | _, _, _ => pure .notImpl

/-- `Py_RETURN_RICHCOMPARE` result for `long_richcompare`, `Objects/longobject.c:3543`. -/
def longRichcompare (w : World) (a b : Val) (op : CmpOp) : Val :=
  match intOf w a, intOf w b with
  | some x, some y => .bool (cmpInt x y op)
  | _, _ => .notImpl

/-- `PyUnicode_RichCompare`, `Objects/unicodeobject.c:11538`. -/
def unicodeRichcompare (w : World) (a b : Val) (op : CmpOp) : Val :=
  match strOf w a, strOf w b with
  | some x, some y => .bool (cmpInt (strCompare x.toList y.toList) 0 op)
  | _, _ => .notImpl

/-- `dict_equal`, `Objects/dictobject.c`, for the value comparisons. -/
def dictEqualLoop (rt : Rt) (bs : List (Val × Val)) : List (Val × Val) → M Bool
  | [] => pure true
  | (k, av) :: rest => do
    match dictLookup bs k with
    | none => pure false
    | some bv =>
      if ← richCompareBool rt bv av .eq then dictEqualLoop rt bs rest else pure false

/-- `dict_richcompare`, `Objects/dictobject.c:4332`. -/
def dictRichcompare (rt : Rt) (a b : List (Val × Val)) (op : CmpOp) : M Val := do
  if op == .eq || op == .ne then
    let eq ← if a.length != b.length then pure false else dictEqualLoop rt b a
    pure (.bool (if op == .eq then eq else !eq))
  else pure .notImpl

/-- A `tp_richcompare` that never reaches back into `object_richcompare` with `Py_NE`. -/
def callRichcompareEq (rt : Rt) (f : SlotFn) (a b : Val) (op : CmpOp) : M Val := do
  let w ← getW
  match f with
  | .generic => slotTpRichcompare rt a b op
  | .c .object | .c .none => objectRichcompare rt (pure .notImpl) a b op
  | .c .int | .c .bool => pure (longRichcompare w a b op)
  | .c .str => pure (unicodeRichcompare w a b op)
  | .c .tuple =>
    match tupleOf w a, tupleOf w b with
    | some x, some y => seqRichcompare rt x y op
    | _, _ => pure .notImpl
  | .c .list =>
    match listOf w a, listOf w b with
    | some x, some y => listRichcompare rt x y op
    | _, _ => pure .notImpl
  | .c .method => methodRichcompare rt a b op
  | .c .dict =>
    match dictOf w a, dictOf w b with
    | some x, some y => dictRichcompare rt x y op
    | _, _ => pure .notImpl
  | .c .float =>
    match a, b with
    | .float _, .float _ => unmodelled
    | _, _ => pure .notImpl
  | .c .builtinFn =>
    -- `meth_richcompare`, `Objects/methodobject.c:318`.
    match op, payloadOf w a, payloadOf w b with
    | .eq, some (.builtin f s1), some (.builtin g s2)
    | .ne, some (.builtin f s1), some (.builtin g s2) =>
      let same := (match s1, s2 with
        | some x, some y => x.is y
        | none, none => true
        | _, _ => false) && f == g
      pure (.bool (if op == .eq then same else !same))
    | _, _, _ => pure .notImpl
  | .c .methodWrapper =>
    -- `wrapper_richcompare`, `Objects/descrobject.c:1320`.
    match op, payloadOf w a, payloadOf w b with
    | .eq, some (.methodWrapper d1 s1), some (.methodWrapper d2 s2)
    | .ne, some (.methodWrapper d1 s1), some (.methodWrapper d2 s2) =>
      let same := d1.is d2 && s1.is s2
      pure (.bool (if op == .eq then same else !same))
    | _, _, _ => pure .notImpl
  | _ => unmodelled

/-- Call the `tp_richcompare` function `f`. `object_richcompare` with `Py_NE` calls
`Py_TYPE(self)->tp_richcompare(self, other, Py_EQ)`. -/
def callRichcompare (rt : Rt) (f : SlotFn) (a b : Val) (op : CmpOp) : M Val := do
  match f with
  | .c .object | .c .none =>
    let eqSlot : M Val := do
      let w ← getW
      match slotOf w (typeOf w a) .tp_richcompare with
      | none => pure .notImpl
      | some g => callRichcompareEq rt g a b .eq
    objectRichcompare rt eqSlot a b op
  | _ => callRichcompareEq rt f a b op

/-- `do_richcompare`, `Objects/object.c:1046`. -/
def doRichcompare (rt : Rt) (v w' : Val) (op : CmpOp) : M Val := do
  let w ← getW
  let tv := typeOf w v
  let tw := typeOf w w'
  let (checked, r1) ←
    if tv != tw && isSubtype w tw tv then
      match slotOf w tw .tp_richcompare with
      | some f => do
        let r ← callRichcompare rt f w' v op.swapped
        pure (true, r)
      | none => pure (false, Val.notImpl)
    else pure (false, Val.notImpl)
  match r1 with
  | .notImpl =>
    let w ← getW
    let r2 ← match slotOf w (typeOf w v) .tp_richcompare with
      | some f => callRichcompare rt f v w' op
      | none => pure Val.notImpl
    match r2 with
    | .notImpl =>
      let w ← getW
      let r3 ←
        if !checked then
          match slotOf w (typeOf w w') .tp_richcompare with
          | some f => callRichcompare rt f w' v op.swapped
          | none => pure Val.notImpl
        else pure Val.notImpl
      match r3 with
      | .notImpl =>
        let w ← getW
        match op with
        | .eq => pure (.bool (v.is w'))
        | .ne => pure (.bool (!v.is w'))
        | _ =>
          typeErr s!"'{op.str}' not supported between instances of '{trunc 100 (typeName w v)}' and '{trunc 100 (typeName w w')}'"
      | r => pure r
    | r => pure r
  | r => pure r

/-- `PyObject_Hash` failure, `PyObject_HashNotImplemented`, `Objects/object.c:1145`. -/
def hashNotImplemented {α : Type} (v : Val) : M α := do
  let w ← getW
  typeErr s!"unhashable type: '{trunc 200 (typeName w v)}'"

/-- `_PyHASH_MODULUS`, 2^61 - 1. -/
def hashModulus : Nat := 2 ^ 61 - 1

/-- `long_hash`, `Objects/longobject.c`. -/
def longHash (i : Int) : Int :=
  let h := (i.natAbs % hashModulus : Nat)
  let r : Int := if i < 0 then -(h : Int) else h
  if r == -1 then -2 else r

/-- The transformation of `slot_tp_hash`, `Objects/typeobject.c:10325-10335`. -/
def hashOfInt (i : Int) : Int :=
  let h := if inSsize i then i else longHash i
  if h == -1 then -2 else h

/-- `slot_tp_hash`, `Objects/typeobject.c:10303`. -/
def slotTpHash (rt : Rt) (self : Val) : M Int := do
  let m ← maybeCallSpecial rt self "__hash__" [] true
  match m with
  | .isNone | .missing => hashNotImplemented self
  | .res res =>
    let w ← getW
    match intOf w res with
    | none => typeErr "__hash__ method should return an integer"
    | some i => pure (hashOfInt i)

/-- Call the `tp_hash` function `f`. -/
def callHash (rt : Rt) (f : SlotFn) (v : Val) : M Int := do
  let w ← getW
  match f with
  | .hashNotImpl => hashNotImplemented v
  | .generic => slotTpHash rt v
  | .c .int | .c .bool => pure (longHash ((intOf w v).getD 0))
  | .c .none => pure 0xfca86420
  | .c .object | .c .type | .c .function | .c .property | .c .method =>
    pure (match v with
      | .obj a => (a : Int)
      | _ => 0)
  | .c .str => pure 0
  | .c .tuple =>
    for x in ((tupleOf w v).getD []) do
      let _ ← rt.hash x
    pure 0
  | _ => unmodelled

/-- `PyObject_Hash`, `Objects/object.c:1153`. -/
def pyHash (rt : Rt) (v : Val) : M Int := do
  let w ← getW
  match slotOf w (typeOf w v) .tp_hash with
  | some f => callHash rt f v
  | none => hashNotImplemented v

/-- `slot_tp_repr`, `Objects/typeobject.c:10287`. The address is rendered as `0x0`:
addresses are not part of the model. -/
def slotTpRepr (rt : Rt) (self : Val) : M Val := do
  match ← maybeCallSpecial rt self "__repr__" [] false with
  | .res r => pure r
  | _ =>
    let w ← getW
    pure (.str s!"<{typeName w self} object at 0x0>")

/-- `object_repr`, `Objects/typeobject.c:6928`. -/
def objectRepr (w : World) (self : Val) : String :=
  let tp := typeOf w self
  let d := tdata w tp
  let mod : Option String :=
    if d.heap then
      match NameDict.get? d.dict "__module__" with
      | some (.str m) => some m
      | _ => none
    else
      match (d.name.splitOn ".") with
      | [_] => some "builtins"
      | parts => some (".".intercalate parts.dropLast)
  match mod with
  | some m =>
    if m != "builtins" then s!"<{m}.{typeQualname w tp} object at 0x0>"
    else s!"<{d.name} object at 0x0>"
  | none => s!"<{d.name} object at 0x0>"

/-- `type_repr`, `Objects/typeobject.c:2294`. -/
def typeRepr (w : World) (t : Addr) : String :=
  let d := tdata w t
  let mod : Option String :=
    if d.heap then
      match NameDict.get? d.dict "__module__" with
      | some (.str m) => some m
      | _ => none
    else
      match (d.name.splitOn ".") with
      | [_] => some "builtins"
      | parts => some (".".intercalate parts.dropLast)
  match mod with
  | some m =>
    if m != "builtins" then s!"<class '{m}.{typeQualname w t}'>"
    else s!"<class '{d.name}'>"
  | none => s!"<class '{d.name}'>"

/-- The `CFn` families that belong to `Objects/exceptions.c`. -/
def isExcFamily : CFn → Bool
  | .exception | .exceptionGroup | .stopIteration | .systemExit | .importError | .osError
  | .nameError | .attributeError | .syntaxError | .keyError | .memoryError
  | .unicodeEncodeError | .unicodeDecodeError | .unicodeTranslateError => true
  | _ => false

/-- Comma-joined reprs. -/
def reprList (rt : Rt) : List Val → M (List String)
  | [] => pure []
  | x :: xs => do
    let r ← rt.repr x
    let rs ← reprList rt xs
    pure (r :: rs)

/-- Loop bound for iteration. A model limit, not a Python one. -/
def iterFuel : Nat := 100000

/-- Remove the first entry that is `v`: the search of `Py_ReprLeave`, `Objects/object.c:3053`. -/
def reprStackErase (v : Val) : List Val → List Val
  | [] => []
  | x :: xs => if x.is v then xs else x :: reprStackErase v xs

/-- `Py_ReprEnter`, `Objects/object.c:3003`, and `Py_ReprLeave`, `:3037`, around `body`: an
object already on the stack gives `cycle`, and every exit from `body` leaves the stack, as the
`error:` labels of `list_repr_impl` and `dict_repr_lock_held` do. -/
def withRepr (v : Val) (cycle : String) (body : M Val) : M Val := do
  let w ← getW
  if w.reprStack.any (·.is v) then pure (.str cycle)
  else
    modW fun w => { w with reprStack := v :: w.reprStack }
    let leave : M Unit := modW fun w => { w with reprStack := reprStackErase v w.reprStack }
    let r ← tryM body fun e => do
      leave
      raise e
    leave
    pure r

/-- The loop of `list_repr_impl`, `Objects/listobject.c:596`: `repr` may mutate the list, so the
size and the item are read again each time. -/
def listReprLoop (rt : Rt) (v : Val) : Nat → Nat → List String → M (List String)
  | 0, _, _ => raise .fuel
  | fuel + 1, i, acc => do
    let w ← getW
    match ((listOf w v).getD [])[i]? with
    | none => pure acc.reverse
    | some item =>
      let r ← rt.repr item
      listReprLoop rt v fuel (i + 1) (r :: acc)

/-- The loop of `dict_repr_lock_held`, `Objects/dictobject.c:3434`: `repr(key)`, then
`repr(value)`, pair by pair, with the dict read again each time. A deletion during the loop is
not exact: `_PyDict_Next` walks a table with dummy entries, and the model has a list. -/
def dictReprLoop (rt : Rt) (v : Val) : Nat → Nat → List String → M (List String)
  | 0, _, _ => raise .fuel
  | fuel + 1, i, acc => do
    let w ← getW
    match ((dictOf w v).getD [])[i]? with
    | none => pure acc.reverse
    | some (k, x) =>
      let kr ← rt.repr k
      let vr ← rt.repr x
      dictReprLoop rt v fuel (i + 1) ((kr ++ ": " ++ vr) :: acc)

/-- Call the `tp_repr` function `f`. -/
def callRepr (rt : Rt) (f : SlotFn) (v : Val) : M Val := do
  let w ← getW
  match f with
  | .generic => slotTpRepr rt v
  | .c .object => pure (.str (objectRepr w v))
  | .c .none => pure (.str "None")
  | .c .notImpl => pure (.str "NotImplemented")
  | .c .ellipsis => pure (.str "Ellipsis")
  | .c .bool =>
    match v with
    | .bool b => pure (.str (if b then "True" else "False"))
    | _ => pure (.str (toString ((intOf w v).getD 0)))
  | .c .int => pure (.str (toString ((intOf w v).getD 0)))
  | .c .str => pure (.str (reprStr ((strOf w v).getD "")))
  | .c .type =>
    match v with
    | .obj a => pure (.str (typeRepr w a))
    | _ => unmodelled
  | .c .tuple =>
    -- `tuple_repr`, `Objects/tupleobject.c:240`: the empty check comes before the guard.
    let xs := (tupleOf w v).getD []
    if xs.isEmpty then pure (.str "()") else
    withRepr v "(...)" do
      let rs ← reprList rt xs
      match rs with
      | [r] => pure (.str s!"({r},)")
      | _ => pure (.str ("(" ++ ", ".intercalate rs ++ ")"))
  | .c .list =>
    -- `list_repr_impl`, `Objects/listobject.c:575`.
    withRepr v "[...]" do
      let rs ← listReprLoop rt v iterFuel 0 []
      pure (.str ("[" ++ ", ".intercalate rs ++ "]"))
  | .c .dict =>
    -- `dict_repr_lock_held`, `Objects/dictobject.c:3403`: the guard comes before the empty check.
    withRepr v "{...}" do
      let rs ← dictReprLoop rt v iterFuel 0 []
      pure (.str ("{" ++ ", ".intercalate rs ++ "}"))
  | .c e => if isExcFamily e then excCallRepr rt e v else unmodelled
  | _ => unmodelled

/-- `PyObject_Repr`, `Objects/object.c:757`. -/
def pyRepr (rt : Rt) (v : Val) : M String := do
  let w ← getW
  let res ← match slotOf w (typeOf w v) .tp_repr with
    | some f => callRepr rt f v
    | none => pure (.str s!"<{typeName w v} object at 0x0>")
  let w ← getW
  match strOf w res with
  | some s => pure s
  | none => typeErr s!"__repr__ returned non-string (type {trunc 200 (typeName w res)})"

/-- Call the `tp_str` function `f`. -/
def callStr (rt : Rt) (f : SlotFn) (v : Val) : M Val := do
  let w ← getW
  match f with
  | .generic => vectorcallMethod rt "__str__" [v]
  | .c e =>
    if isExcFamily e then excCallStr rt e v else
    match e with
    | .object =>
      match slotOf w (typeOf w v) .tp_repr with
      | some r => callRepr rt r v
      | none => pure (.str (objectRepr w v))
    | .str => pure (.str ((strOf w v).getD ""))
    | _ => unmodelled
  | _ => unmodelled

/-- `PyObject_Str`, `Objects/object.c:799`. -/
def pyStr (rt : Rt) (v : Val) : M String := do
  match v with
  | .str s => pure s
  | _ =>
    let w ← getW
    match slotOf w (typeOf w v) .tp_str with
    | none => rt.repr v
    | some f =>
      let res ← callStr rt f v
      let w ← getW
      match strOf w res with
      | some s => pure s
      | none => typeErr s!"__str__ returned non-string (type {trunc 200 (typeName w res)})"

/-! ## Index conversion -/

/-- `_PyIndex_Check`: the type has `nb_index`. -/
def indexCheck (w : World) (v : Val) : Bool :=
  hasGroup w (typeOf w v) .number && (slotOf w (typeOf w v) .nb_index).isSome

/-- Call `nb_index`. -/
def callUnaryNb (rt : Rt) (s : Slot) (dunder : Name) (f : SlotFn) (v : Val) : M Val := do
  let w ← getW
  match f, s with
  | .generic, _ => vectorcallMethod rt dunder [v]
  | .c .int, .nb_index | .c .int, .nb_int | .c .int, .nb_positive | .c .bool, .nb_index
  | .c .bool, .nb_int =>
    pure (.int ((intOf w v).getD 0))
  | .c .int, .nb_negative => pure (.int (-((intOf w v).getD 0)))
  | .c .int, .nb_invert | .c .bool, .nb_invert => pure (.int (-((intOf w v).getD 0) - 1))
  | .c .int, .nb_absolute => pure (.int ((((intOf w v).getD 0).natAbs : Nat) : Int))
  | _, _ => unmodelled

/-- `_PyNumber_Index`, `Objects/abstract.c:1400`. The `DeprecationWarning` for a strict
`int` subclass does not change the result. -/
def numberIndex (rt : Rt) (item : Val) : M Val := do
  let w ← getW
  match intOf w item with
  | some _ => pure item
  | none =>
    if !indexCheck w item then
      typeErr s!"'{trunc 200 (typeName w item)}' object cannot be interpreted as an integer"
    else
      match slotOf w (typeOf w item) .nb_index with
      | none => unmodelled
      | some f =>
        let result ← callUnaryNb rt .nb_index "__index__" f item
        let w ← getW
        match intOf w result with
        | some _ => pure result
        | none => typeErr s!"__index__ returned non-int (type {trunc 200 (typeName w result)})"

/-- `PyNumber_Index`, `Objects/abstract.c:1446`: an exact `int`. -/
def pyNumberIndex (rt : Rt) (item : Val) : M Int := do
  let v ← numberIndex rt item
  let w ← getW
  pure ((intOf w v).getD 0)

/-- `PyNumber_AsSsize_t`, `Objects/abstract.c:1458`. `err = none` clips to the
`Py_ssize_t` range. -/
def numberAsSsize (rt : Rt) (item : Val) (err : Option Addr) : M Int := do
  let i ← pyNumberIndex rt item
  if inSsize i then pure i else
  match err with
  | none => pure (if i < 0 then PyLean.ssizeMin else PyLean.ssizeMax)
  | some e =>
    let w ← getW
    raiseC e s!"cannot fit '{trunc 200 (typeName w item)}' into an index-sized integer"

/-! ## Sizes -/

/-- `slot_sq_length`, `Objects/typeobject.c:10018`. -/
def slotSqLength (rt : Rt) (self : Val) : M Int := do
  let res ← vectorcallMethod rt "__len__" [self]
  let idx ← pyNumberIndex rt res
  if idx < 0 then valueErr "__len__() should return >= 0"
  else numberAsSsize rt (.int idx) (some B.OverflowError)

/-- Call `sq_length` or `mp_length`. -/
def callLen (rt : Rt) (f : SlotFn) (v : Val) : M Int := do
  let w ← getW
  match f with
  | .generic => slotSqLength rt v
  | .c .str => pure (((strOf w v).getD "").toList.length : Nat)
  | .c .tuple => pure (((tupleOf w v).getD []).length : Nat)
  | .c .list => pure (((listOf w v).getD []).length : Nat)
  | .c .dict => pure (((dictOf w v).getD []).length : Nat)
  | .c .mappingproxy =>
    match payloadOf w v with
    | some (.typeDictProxy t) => pure ((tdata w t).dict.length : Nat)
    | _ => unmodelled
  | _ => unmodelled

/-- The filled slot `s` of the type of `v`, honouring NULL `tp_as_*` structs. -/
def slotIn (w : World) (v : Val) (s : Slot) : Option SlotFn :=
  if hasGroup w (typeOf w v) s.group then slotOf w (typeOf w v) s else none

/-- `PyMapping_Size`, `Objects/abstract.c:2267`. -/
def pyMappingSize (rt : Rt) (o : Val) : M Int := do
  let w ← getW
  match slotIn w o .mp_length with
  | some f => callLen rt f o
  | none =>
    match slotIn w o .sq_length with
    | some _ => typeErr s!"{trunc 200 (typeName w o)} is not a mapping"
    | none => typeErr s!"object of type '{trunc 200 (typeName w o)}' has no len()"

/-- `PyObject_Size`, `Objects/abstract.c:57`. -/
def pyObjectSize (rt : Rt) (o : Val) : M Int := do
  let w ← getW
  match slotIn w o .sq_length with
  | some f => callLen rt f o
  | none => pyMappingSize rt o

/-- `PySequence_Size`, `Objects/abstract.c:1681`. -/
def pySequenceSize (rt : Rt) (s : Val) : M Int := do
  let w ← getW
  match slotIn w s .sq_length with
  | some f => callLen rt f s
  | none =>
    match slotIn w s .mp_length with
    | some _ => typeErr s!"{trunc 200 (typeName w s)} is not a sequence"
    | none => typeErr s!"object of type '{trunc 200 (typeName w s)}' has no len()"

/-- `_PyObject_HasLen`, `Objects/abstract.c:83`. -/
def hasLen (w : World) (o : Val) : Bool :=
  (slotIn w o .sq_length).isSome || (slotIn w o .mp_length).isSome

/-- `PyObject_LengthHint`, `Objects/abstract.c:95`. -/
def pyLengthHint (rt : Rt) (o : Val) (dflt : Int) : M Int := do
  let w ← getW
  let first : M (Option Int) :=
    if hasLen w o then
      catchMatch B.TypeError (some <$> pyObjectSize rt o) (pure none)
    else pure none
  match ← first with
  | some r => pure r
  | none =>
    match ← lookupSpecial rt o "__length_hint__" with
    | none => pure dflt
    | some hint =>
      let r? ← catchMatch B.TypeError (some <$> rt.call hint [] []) (pure none)
      match r? with
      | none => pure dflt
      | some .notImpl => pure dflt
      | some result =>
        let w ← getW
        match intOf w result with
        | none =>
          typeErr s!"__length_hint__ must be an integer, not {trunc 100 (typeName w result)}"
        | some i =>
          if !inSsize i then overflowErr "Python int too large to convert to C ssize_t"
          else if i < 0 then valueErr "__length_hint__() should return >= 0"
          else pure i

/-- `slot_nb_bool`, `Objects/typeobject.c:10202`. -/
def slotNbBool (rt : Rt) (self : Val) : M Bool := do
  let m ← maybeCallSpecial rt self "__bool__" [] true
  let w ← getW
  match m with
  | .isNone => typeErr s!"'{trunc 200 (typeName w self)}' cannot be interpreted as a boolean"
  | .missing =>
    match ← maybeCallSpecial rt self "__len__" [] false with
    | .res v => rt.isTrue v
    | _ => pure true
  | .res value =>
    match value with
    | .bool b => pure b
    | _ => typeErr s!"__bool__ should return bool, returned {typeName w value}"

/-- `PyObject_IsTrue`, `Objects/object.c:2060`. -/
def pyIsTrue (rt : Rt) (v : Val) : M Bool := do
  match v with
  | .bool b => pure b
  | .none => pure false
  | _ =>
    let w ← getW
    match slotIn w v .nb_bool with
    | some f =>
      match f with
      | .generic => slotNbBool rt v
      | .c .int | .c .bool => pure (((intOf w v).getD 0) != 0)
      | .c .notImpl => typeErr "NotImplemented should not be used in a boolean context"
      | .c .none => pure false
      | _ => unmodelled
    | none =>
      match slotIn w v .mp_length with
      | some f =>
        let n ← callLen rt f v
        pure (n > 0)
      | none =>
        match slotIn w v .sq_length with
        | some f =>
          let n ← callLen rt f v
          pure (n > 0)
        | none => pure true

/-! ## Binary operators -/

/-- `method_is_overloaded`, `Objects/typeobject.c:9941`. -/
def methodIsOverloaded (rt : Rt) (left right : Val) (n : Name) : M Bool := do
  let w ← getW
  match ← rt.getOptionalAttr (.obj (typeOf w right)) n with
  | none => pure false
  | some b =>
    let w ← getW
    match ← rt.getOptionalAttr (.obj (typeOf w left)) n with
    | none => pure true
    | some a => richCompareBool rt a b .ne

/-- `SLOT1BINFULL`, `Objects/typeobject.c:9971`, for slot `s` with `extra` trailing
arguments (`slot_nb_power` with a modulus copies this macro, `:10149`). -/
def slot1Bin (rt : Rt) (s : Slot) (dunder rdunder : Name) (self other : Val)
    (extra : List Val) : M Val := do
  let w ← getW
  let doOther := typeOf w self != typeOf w other && slotIn w other s == some .generic
  if slotIn w self s == some .generic then
    let tryRev : M (Option Val × Bool) :=
      if doOther && isSubtype w (typeOf w other) (typeOf w self) then do
        if ← methodIsOverloaded rt self other rdunder then
          let r ← vectorcallMaybe rt rdunder ([other, self] ++ extra)
          match r with
          | .notImpl => pure (none, false)
          | r => pure (some r, false)
        else pure (none, doOther)
      else pure (none, doOther)
    let (early, doOther') ← tryRev
    match early with
    | some r => pure r
    | none =>
      let r ← vectorcallMaybe rt dunder ([self, other] ++ extra)
      let w ← getW
      match r with
      | .notImpl =>
        if typeOf w other == typeOf w self then pure r
        else if doOther' then vectorcallMaybe rt rdunder ([other, self] ++ extra)
        else pure .notImpl
      | r => pure r
  else if doOther then vectorcallMaybe rt rdunder ([other, self] ++ extra)
  else pure .notImpl

/-- Slot and dunder names of each binary number operation. -/
structure NbOp where
  slot : Slot
  islot : Slot
  dunder : Name
  rdunder : Name
  idunder : Name
  /-- `op_name` for `binop_type_error`, and the same for the in-place form. -/
  name : String
  iname : String
  deriving Repr, Inhabited

def nbAdd : NbOp := ⟨.nb_add, .nb_inplace_add, "__add__", "__radd__", "__iadd__", "+", "+="⟩
def nbSub : NbOp := ⟨.nb_subtract, .nb_inplace_subtract, "__sub__", "__rsub__", "__isub__", "-", "-="⟩
def nbMul : NbOp := ⟨.nb_multiply, .nb_inplace_multiply, "__mul__", "__rmul__", "__imul__", "*", "*="⟩
def nbMatmul : NbOp := ⟨.nb_matrix_multiply, .nb_inplace_matrix_multiply, "__matmul__", "__rmatmul__", "__imatmul__", "@", "@="⟩
def nbMod : NbOp := ⟨.nb_remainder, .nb_inplace_remainder, "__mod__", "__rmod__", "__imod__", "%", "%="⟩
def nbFloordiv : NbOp := ⟨.nb_floor_divide, .nb_inplace_floor_divide, "__floordiv__", "__rfloordiv__", "__ifloordiv__", "//", "//="⟩
def nbTruediv : NbOp := ⟨.nb_true_divide, .nb_inplace_true_divide, "__truediv__", "__rtruediv__", "__itruediv__", "/", "/="⟩
def nbLshift : NbOp := ⟨.nb_lshift, .nb_inplace_lshift, "__lshift__", "__rlshift__", "__ilshift__", "<<", "<<="⟩
def nbRshift : NbOp := ⟨.nb_rshift, .nb_inplace_rshift, "__rshift__", "__rrshift__", "__irshift__", ">>", ">>="⟩
def nbAnd : NbOp := ⟨.nb_and, .nb_inplace_and, "__and__", "__rand__", "__iand__", "&", "&="⟩
def nbOr : NbOp := ⟨.nb_or, .nb_inplace_or, "__or__", "__ror__", "__ior__", "|", "|="⟩
def nbXor : NbOp := ⟨.nb_xor, .nb_inplace_xor, "__xor__", "__rxor__", "__ixor__", "^", "^="⟩
def nbDivmod : NbOp := ⟨.nb_divmod, .nb_divmod, "__divmod__", "__rdivmod__", "", "divmod()", ""⟩

/-- The `NbOp` of a binary number slot. -/
def nbOpOfSlot : Slot → NbOp
  | .nb_add => nbAdd | .nb_subtract => nbSub | .nb_multiply => nbMul
  | .nb_matrix_multiply => nbMatmul | .nb_remainder => nbMod | .nb_divmod => nbDivmod
  | .nb_floor_divide => nbFloordiv | .nb_true_divide => nbTruediv
  | .nb_lshift => nbLshift | .nb_rshift => nbRshift | .nb_and => nbAnd | .nb_or => nbOr
  | .nb_xor => nbXor
  | _ => nbAdd

/-- `x & y` on Python ints, two's complement of unbounded width. -/
def intAnd (a b : Int) : Int :=
  if a ≥ 0 then
    if b ≥ 0 then ((a.toNat &&& b.toNat : Nat) : Int)
    else (PyLean.notAnd (-b - 1).toNat a.toNat : Nat)
  else if b ≥ 0 then (PyLean.notAnd (-a - 1).toNat b.toNat : Nat)
  else -(((-a - 1).toNat ||| (-b - 1).toNat : Nat) : Int) - 1

/-- `x | y` on Python ints: `~(~x & ~y)`. -/
def intOr (a b : Int) : Int := -(intAnd (-a - 1) (-b - 1)) - 1

/-- `x ^ y` on Python ints. -/
def intXor (a b : Int) : Int :=
  let ua := if a ≥ 0 then a.toNat else (-a - 1).toNat
  let ub := if b ≥ 0 then b.toNat else (-b - 1).toNat
  let r : Int := ((ua ^^^ ub : Nat) : Int)
  if (a < 0) != (b < 0) then -r - 1 else r

/-- Hash a dict key with `dict_unhashable_type`, `Objects/dictobject.c`: an unhashable
key's `TypeError` is replaced. -/
def dictHashKey (rt : Rt) (key : Val) : M Unit := do
  let _ ← tryM (rt.hash key) fun e => do
    let w ← getW
    match e with
    | .exc c m v =>
      if c == B.TypeError then
        let t ← match v with
          | some x => rt.str x
          | none => pure m
        typeErr s!"cannot use '{typeFQN w (typeOf w key)}' as a dict key ({t})"
      else raise e
    | _ => raise e

/-- `PyDict_MergeFromSeq2`, `Objects/dictobject.c`: each item must be a pair. -/
def mergeSeq2 (rt : Rt) : Nat → List (Val × Val) → List Val → M (List (Val × Val))
  | _, es, [] => pure es
  | i, es, x :: xs => do
    let w ← getW
    let items ← tryM (rt.listItems x) fun e => do
      let w ← getW
      if excMatches w e B.TypeError then
        typeErr "object is not iterable"
      else raise e
    match items with
    | [k, v] =>
      let _ := w
      dictHashKey rt k
      mergeSeq2 rt (i + 1) (dictSetEntry es k v) xs
    | _ =>
      valueErr s!"dictionary update sequence element #{i} has length {items.length}; 2 is required"

/-- The generic path of `dict_merge`, `Objects/dictobject.c`: `PyMapping_Keys(b)`, then
`b[key]` for each key. -/
def dictMergeKeys (rt : Rt) (b : Val) : List (Val × Val) → List Val → M (List (Val × Val))
  | es, [] => pure es
  | es, k :: ks => do
    let v ← rt.getItem b k
    dictHashKey rt k
    dictMergeKeys rt b (dictSetEntry es k v) ks

/-- `dict_update_arg`, `Objects/dictobject.c`: an exact dict is merged; otherwise `keys`
decides between a mapping merge and a sequence of pairs. A dict subclass keeping `dict_iter`
merges directly. -/
def dictUpdateArg (rt : Rt) (es : List (Val × Val)) (x : Val) : M (List (Val × Val)) := do
  let w ← getW
  if typeOf w x == B.dict then
    pure (((dictOf w x).getD []).foldl (fun d (k, v) => dictSetEntry d k v) es)
  else
    match ← rt.getOptionalAttr x "keys" with
    | some _ =>
      let w ← getW
      if (dictOf w x).isSome && slotOf w (typeOf w x) .tp_iter == some (.c .dict) then
        pure (((dictOf w x).getD []).foldl (fun d (k, v) => dictSetEntry d k v) es)
      else
        let f ← rt.getAttr x "keys"
        let out ← rt.call f [] []
        -- `method_output_as_list`, `Objects/abstract.c:2433-2447`: only `PyObject_GetIter` has
        -- its TypeError replaced, not an error raised by the iteration itself.
        let it ← tryM (rt.getIter out) fun e => do
          let w ← getW
          if excMatches w e B.TypeError then
            typeErr s!"{trunc 200 (typeName w x)}.keys() returned a non-iterable (type {trunc 200 (typeName w out)})"
          else raise e
        let keys ← rt.listItems it
        dictMergeKeys rt x es keys
    | none =>
      let items ← rt.listItems x
      mergeSeq2 rt 0 es items

/-- `long_add`, `long_sub`, ... on values that passed `CHECK_BINOP`. -/
def longBinary (s : Slot) (a b : Int) : M Val :=
  match s with
  | .nb_add => pure (.int (a + b))
  | .nb_subtract => pure (.int (a - b))
  | .nb_multiply => pure (.int (a * b))
  | .nb_floor_divide =>
    if b == 0 then raiseC B.ZeroDivisionError "division by zero"
    else pure (.int (Int.fdiv a b))
  | .nb_true_divide =>
    -- A float whose bits are not modelled: `long_true_divide` belongs to `LongObj`.
    if b == 0 then raiseC B.ZeroDivisionError "division by zero"
    else pure (.float 0)
  | .nb_remainder =>
    if b == 0 then raiseC B.ZeroDivisionError "division by zero"
    else pure (.int (Int.fmod a b))
  | .nb_divmod =>
    if b == 0 then raiseC B.ZeroDivisionError "division by zero"
    else pure (.tuple [.int (Int.fdiv a b), .int (Int.fmod a b)])
  | .nb_and => pure (.int (intAnd a b))
  | .nb_or => pure (.int (intOr a b))
  | .nb_xor => pure (.int (intXor a b))
  | .nb_lshift =>
    if b < 0 then valueErr "negative shift count"
    else if b > 100000 then unmodelled
    else pure (.int (a * 2 ^ b.toNat))
  | .nb_rshift =>
    if b < 0 then valueErr "negative shift count"
    else if b > 100000 then pure (.int (if a < 0 then -1 else 0))
    else pure (.int (Int.fdiv a (2 ^ b.toNat)))
  | _ => unmodelled

/-- Call a binary number slot function `f`. -/
def callNbBinary (rt : Rt) (s : Slot) (f : SlotFn) (a b : Val) : M Val := do
  let w ← getW
  match f with
  | .generic =>
    let op := nbOpOfSlot s
    slot1Bin rt s op.dunder op.rdunder a b []
  | .c .int =>
    match intOf w a, intOf w b with
    | some x, some y => longBinary s x y
    | _, _ => pure .notImpl
  | .c .bool =>
    match a, b with
    | .bool x, .bool y =>
      match s with
      | .nb_and => pure (.bool (x && y))
      | .nb_or => pure (.bool (x || y))
      | .nb_xor => pure (.bool (xor x y))
      | _ => unmodelled
    | _, _ =>
      match intOf w a, intOf w b with
      | some x, some y => longBinary s x y
      | _, _ => pure .notImpl
  | .c .float =>
    match intOf w a, intOf w b, a, b with
    | none, _, .float _, _ | _, none, _, .float _ => unmodelled
    | _, _, _, _ => pure .notImpl
  | .c .type =>
    -- `_Py_union_type_or`: only classes and `None` are unionable.
    let unionable (x : Val) : Bool := x.is .none || typeCheck w x
    if unionable a && unionable b then
      if a.is b then pure a else alloc B.unionType .plain
    else pure .notImpl
  | .c .str =>
    -- `unicode_mod`: `%` formatting needs a `str` on the left. Only format strings with
    -- no conversion are modelled: `PyUnicode_Format` then checks the arguments were used.
    match strOf w a with
    | none => pure .notImpl
    | some fmt =>
      if fmt.contains '%' then unmodelled
      else if (slotIn w b .mp_subscript).isSome && (tupleOf w b).isNone && (strOf w b).isNone then
        pure (.str fmt)
      else
        match tupleOf w b with
        | some [] => pure (.str fmt)
        | _ => typeErr "not all arguments converted during string formatting"
  | .c .dict =>
    -- `dict_or`, `Objects/dictobject.c`, through `dict_update_arg`: a non-exact dict is first
    -- asked for `keys`, then merged directly if it has `dict_iter`.
    match dictOf w a, dictOf w b with
    | some x, some _ =>
      let merged ← dictUpdateArg rt x b
      alloc B.dict (.dict merged)
    | _, _ => pure .notImpl
  | _ => unmodelled

/-- `binary_op1`, `Objects/abstract.c:930`. -/
def binaryOp1 (rt : Rt) (v w' : Val) (s : Slot) : M Val := do
  let w ← getW
  let slotv := slotIn w v s
  let slotw0 : Option SlotFn :=
    if typeOf w w' != typeOf w v then
      let sw := slotIn w w' s
      if sw == slotv then none else sw
    else none
  let afterV (slotw : Option SlotFn) : M Val :=
    match slotw with
    | some sw => callNbBinary rt s sw v w'
    | none => pure .notImpl
  match slotv with
  | some sv =>
    let first : M (Option Val × Option SlotFn) :=
      match slotw0 with
      | some sw =>
        if isSubtype w (typeOf w w') (typeOf w v) then do
          let x ← callNbBinary rt s sw v w'
          match x with
          | .notImpl => pure (none, none)
          | x => pure (some x, none)
        else pure (none, slotw0)
      | none => pure (none, slotw0)
    let (early, slotw) ← first
    match early with
    | some x => pure x
    | none =>
      let x ← callNbBinary rt s sv v w'
      match x with
      | .notImpl => afterV slotw
      | x => pure x
  | none => afterV slotw0

/-- `binop_type_error`, `Objects/abstract.c:989`. -/
def binopTypeError {α : Type} (v w' : Val) (name : String) : M α := do
  let w ← getW
  typeErr s!"unsupported operand type(s) for {trunc 100 name}: '{trunc 100 (typeName w v)}' and '{trunc 100 (typeName w w')}'"

/-- `binary_op`, `Objects/abstract.c:1001`. -/
def binaryOp (rt : Rt) (v w' : Val) (s : Slot) (name : String) : M Val := do
  match ← binaryOp1 rt v w' s with
  | .notImpl => binopTypeError v w' name
  | r => pure r

/-- Python-level `str` repetition. -/
def strRepeat (s : String) (n : Int) : String :=
  String.join (List.replicate n.toNat s)

/-- Repeat a list, `n` copies. -/
def listRepeat (xs : List Val) (n : Int) : List Val :=
  (List.replicate n.toNat xs).flatten

/-- `sq_concat` of the builtin sequences. -/
def callSqConcat (rt : Rt) (f : SlotFn) (a b : Val) : M Val := do
  let w ← getW
  match f with
  | .c .str =>
    match strOf w a, strOf w b with
    | some x, some y => pure (.str (x ++ y))
    | _, _ => typeErr s!"can only concatenate str (not \"{trunc 200 (typeName w b)}\") to str"
  | .c .tuple =>
    match tupleOf w a, tupleOf w b with
    | some x, some y => pure (.tuple (x ++ y))
    | _, _ => typeErr s!"can only concatenate tuple (not \"{trunc 200 (typeName w b)}\") to tuple"
  | .c .list =>
    match listOf w a, listOf w b with
    | some x, some y => alloc B.list (.list (x ++ y))
    | _, _ => typeErr s!"can only concatenate list (not \"{trunc 200 (typeName w b)}\") to list"
  | _ =>
    let _ := rt
    unmodelled

/-- `sq_repeat` of the builtin sequences. -/
def callSqRepeat (f : SlotFn) (a : Val) (n : Int) : M Val := do
  let w ← getW
  let k := if n < 0 then 0 else n
  let size : Nat := match f with
    | .c .str => ((strOf w a).getD "").length
    | .c .tuple => ((tupleOf w a).getD []).length
    | .c .list => ((listOf w a).getD []).length
    | _ => 0
  -- An allocation of 2^48 items fails: `PyErr_NoMemory` in `list_repeat` and friends.
  if size != 0 && k * size ≥ 2 ^ 48 then
    if (k * size : Int) > PyLean.ssizeMax && f == .c .str then
      overflowErr "repeated string is too long"
    raiseC B.MemoryError ""
  if size != 0 && k * size > 1000000 then unmodelled else
  let k := if size == 0 then 0 else k
  match f with
  | .c .str => pure (.str (strRepeat ((strOf w a).getD "") k))
  | .c .tuple => pure (.tuple (listRepeat ((tupleOf w a).getD []) k))
  | .c .list => alloc B.list (.list (listRepeat ((listOf w a).getD []) k))
  | _ => unmodelled

/-- Append `items` to the list at `addr`. -/
def listAppendAll (addr : Addr) (items : List Val) : M Unit :=
  modObj addr fun o =>
    match o.body with
    | .list xs => { o with body := .list (xs ++ items) }
    | body => { o with body := body }

/-- The reservation of `list_extend_iter_lock_held`, `Objects/listobject.c:1241-1259`. When
`m + n` overflows the hint is ignored (:1241), so the loop still runs. Otherwise
`list_preallocate_exact` or `list_resize` fails on a size no allocator can serve. -/
def listReserve (m n : Int) : M Unit :=
  if m > PyLean.ssizeMax - n then pure ()
  else if m + n ≥ 2 ^ 48 then raiseC B.MemoryError ""
  else pure ()

/-- The loop of `list_extend_iter_lock_held`, `Objects/listobject.c:1262-1283`: each item goes
into the list as it arrives, so the items before a raising `__next__` stay, and the iterator
sees and can change the list. -/
def listExtendLoop (rt : Rt) (addr : Addr) (it : Val) : Nat → M Unit
  | 0 => raise .fuel
  | fuel + 1 => do
    match ← rt.iterNext it with
    | none => pure ()
    | some x =>
      listAppendAll addr [x]
      listExtendLoop rt addr it fuel

/-- `list_extend_iter_lock_held`, `Objects/listobject.c:1225`. -/
def listExtendIter (rt : Rt) (addr : Addr) (b : Val) : M Unit := do
  let it ← rt.getIter b
  let n ← pyLengthHint rt b 8
  let w ← getW
  listReserve ((listOf w (.obj addr)).getD []).length n
  listExtendLoop rt addr it iterFuel

/-- The keys of a dict, in order. -/
def dictKeyList (w : World) (d : Val) : List Val := ((dictOf w d).getD []).map (·.1)

/-- `_list_extend`, `Objects/listobject.c:1402`, in the order of its branches. Extending a list
with itself is `list_inplace_repeat(self, 2)` (:1407) and runs no Python code; exact lists,
tuples, dicts and `dict_keys` are read directly; anything else is iterated. -/
def listExtend (rt : Rt) (self : Val) (addr : Addr) (b : Val) : M Unit := do
  let w ← getW
  if self.is b then listAppendAll addr ((listOf w self).getD [])
  else
    match b with
    | .tuple xs => listAppendAll addr xs
    | _ =>
      if typeOf w b == B.list then listAppendAll addr ((listOf w b).getD [])
      else if typeOf w b == B.dict then listAppendAll addr (dictKeyList w b)
      else if typeOf w b == B.dictKeys then
        match payloadOf w b with
        | some (.seqIter (some d) _) => listAppendAll addr (dictKeyList w d)
        | _ => unmodelled
      else listExtendIter rt addr b

/-- `sq_inplace_concat` of `list`: `list_inplace_concat` extends with any iterable and
returns the list; the other sequences have only `sq_concat`. -/
def callSqInplaceConcat (rt : Rt) (f : SlotFn) (a b : Val) : M Val := do
  match f, a with
  | .c .list, .obj addr =>
    listExtend rt a addr b
    pure a
  | _, _ => callSqConcat rt f a b

/-- `sq_inplace_repeat` of `list`: `list_inplace_repeat`. -/
def callSqInplaceRepeat (f : SlotFn) (a : Val) (n : Int) : M Val := do
  match f, a with
  | .c .list, .obj addr =>
    let r ← callSqRepeat f a n
    let w ← getW
    modObj addr fun o => { o with body := .list ((listOf w r).getD []) }
    pure a
  | _, _ => callSqRepeat f a n

/-- `sequence_repeat`, `Objects/abstract.c:1147`. -/
def sequenceRepeat (rt : Rt) (f : SlotFn) (seq n : Val) : M Val := do
  let w ← getW
  if indexCheck w n then
    let count ← numberAsSsize rt n (some B.OverflowError)
    callSqRepeat f seq count
  else typeErr s!"can't multiply sequence by non-int of type '{trunc 200 (typeName w n)}'"

/-- `sequence_repeat` with the `sq_inplace_repeat` function. -/
def sequenceRepeatInplace (rt : Rt) (f : SlotFn) (seq n : Val) : M Val := do
  let w ← getW
  if indexCheck w n then
    let count ← numberAsSsize rt n (some B.OverflowError)
    callSqInplaceRepeat f seq count
  else typeErr s!"can't multiply sequence by non-int of type '{trunc 200 (typeName w n)}'"

/-- `PyNumber_Add`, `Objects/abstract.c:1128`. -/
def pyNumberAdd (rt : Rt) (v w' : Val) : M Val := do
  match ← binaryOp1 rt v w' .nb_add with
  | .notImpl =>
    let w ← getW
    match slotIn w v .sq_concat with
    | some f => callSqConcat rt f v w'
    | none => binopTypeError v w' "+"
  | r => pure r

/-- `PyNumber_Multiply`, `Objects/abstract.c:1166`. -/
def pyNumberMultiply (rt : Rt) (v w' : Val) : M Val := do
  match ← binaryOp1 rt v w' .nb_multiply with
  | .notImpl =>
    let w ← getW
    match slotIn w v .sq_repeat with
    | some f => sequenceRepeat rt f v w'
    | none =>
      match slotIn w w' .sq_repeat with
      | some f => sequenceRepeat rt f w' v
      | none => binopTypeError v w' "*"
  | r => pure r

/-- `binary_iop1`, `Objects/abstract.c:1218`. -/
def binaryIop1 (rt : Rt) (v w' : Val) (islot s : Slot) : M Val := do
  let w ← getW
  let r1 ← match slotIn w v islot with
    | some f => callInplace rt f (nbOpOfISlot islot).idunder v w'
    | none => pure Val.notImpl
  match r1 with
  | .notImpl => binaryOp1 rt v w' s
  | r => pure r
where
  nbOpOfISlot : Slot → NbOp
    | .nb_inplace_add => nbAdd | .nb_inplace_subtract => nbSub | .nb_inplace_multiply => nbMul
    | .nb_inplace_matrix_multiply => nbMatmul | .nb_inplace_remainder => nbMod
    | .nb_inplace_floor_divide => nbFloordiv | .nb_inplace_true_divide => nbTruediv
    | .nb_inplace_lshift => nbLshift | .nb_inplace_rshift => nbRshift
    | .nb_inplace_and => nbAnd | .nb_inplace_or => nbOr | .nb_inplace_xor => nbXor
    | _ => nbAdd
  /-- `SLOT1(slot_nb_inplace_*, __i*__)`, `Objects/typeobject.c:10263`. -/
  callInplace (rt : Rt) (f : SlotFn) (idunder : Name) (a b : Val) : M Val := do
    match f, a with
    | .generic, _ => vectorcallMethod rt idunder [a, b]
    | .c .dict, .obj addr =>
      -- `dict_ior`, `Objects/dictobject.c`.
      let w ← getW
      let merged ← dictUpdateArg rt ((dictOf w a).getD []) b
      modObj addr fun o => { o with body := .dict merged }
      pure a
    | .c .list, .obj _ =>
      -- `update_one_slot` puts `list_inplace_concat` in `nb_inplace_add` of a list subclass:
      -- `__iadd__` has the same wrapper for `nb_inplace_add` and `sq_inplace_concat`.
      if idunder == "__iadd__" then callSqInplaceConcat rt f a b else unmodelled
    | _, _ => unmodelled

/-- `binary_iop`, `Objects/abstract.c:1250`. -/
def binaryIop (rt : Rt) (v w' : Val) (islot s : Slot) (name : String) : M Val := do
  match ← binaryIop1 rt v w' islot s with
  | .notImpl => binopTypeError v w' name
  | r => pure r

/-- `PyNumber_InPlaceAdd`, `Objects/abstract.c:1297`. -/
def pyNumberInPlaceAdd (rt : Rt) (v w' : Val) : M Val := do
  match ← binaryIop1 rt v w' .nb_inplace_add .nb_add with
  | .notImpl =>
    let w ← getW
    if hasGroup w (typeOf w v) .sequence then
      match slotIn w v .sq_inplace_concat, slotIn w v .sq_concat with
      | some f, _ => callSqInplaceConcat rt f v w'
      | none, some f => callSqConcat rt f v w'
      | none, none => binopTypeError v w' "+="
    else binopTypeError v w' "+="
  | r => pure r

/-- `PyNumber_InPlaceMultiply`, `Objects/abstract.c:1320`. Note the `else if` at `:1336`:
the right operand's `sq_repeat` is consulted only when the left operand has no
`tp_as_sequence` at all. -/
def pyNumberInPlaceMultiply (rt : Rt) (v w' : Val) : M Val := do
  match ← binaryIop1 rt v w' .nb_inplace_multiply .nb_multiply with
  | .notImpl =>
    let w ← getW
    if hasGroup w (typeOf w v) .sequence then
      match slotIn w v .sq_inplace_repeat, slotIn w v .sq_repeat with
      | some f, _ => sequenceRepeatInplace rt f v w'
      | none, some f => sequenceRepeat rt f v w'
      | none, none => binopTypeError v w' "*="
    else if hasGroup w (typeOf w w') .sequence then
      match slotIn w w' .sq_repeat with
      | some f => sequenceRepeat rt f w' v
      | none => binopTypeError v w' "*="
    else binopTypeError v w' "*="
  | r => pure r

/-- `slot_nb_power`, `Objects/typeobject.c:10149`. -/
def slotNbPower (rt : Rt) (self other modulus : Val) : M Val :=
  match modulus with
  | .none => slot1Bin rt .nb_power "__pow__" "__rpow__" self other []
  | m => slot1Bin rt .nb_power "__pow__" "__rpow__" self other [m]

/-- `long_pow` for the cases with an exact result: non-negative exponent, no modulus. -/
def longPow (w : World) (a b z : Val) : M Val :=
  match intOf w a, intOf w b, z with
  | some x, some y, .none =>
    if y < 0 then
      -- `long_pow` hands negative exponents to `float_pow`.
      if x == 0 then raiseC B.ZeroDivisionError "zero to a negative power"
      else pure (.float 0)
    else if y > 10000 then unmodelled else pure (.int (x ^ y.toNat))
  | some x, some y, z' =>
    match intOf w z' with
    | none => pure .notImpl
    | some m =>
      if m == 0 then valueErr "pow() 3rd argument cannot be 0"
      else if y < 0 || y > 10000 then unmodelled
      else pure (.int (Int.fmod (x ^ y.toNat) m))
  | _, _, _ => pure .notImpl

/-- Call `nb_power`. -/
def callNbPower (rt : Rt) (f : SlotFn) (a b c : Val) : M Val := do
  let w ← getW
  match f with
  | .generic => slotNbPower rt a b c
  | .c .int => longPow w a b c
  | _ => unmodelled

/-- `ternary_op`, `Objects/abstract.c:1020`. -/
def ternaryOp (rt : Rt) (v w' z : Val) (name : String) : M Val := do
  let w ← getW
  let s : Slot := .nb_power
  let slotv := slotIn w v s
  let slotw0 : Option SlotFn :=
    if typeOf w w' != typeOf w v then
      let sw := slotIn w w' s
      if sw == slotv then none else sw
    else none
  let afterZ (slotw : Option SlotFn) : M Val := do
    let w ← getW
    let slotz0 := slotIn w z s
    let slotz := if slotz0 == slotv || slotz0 == slotw then none else slotz0
    let x ← match slotz with
      | some f => callNbPower rt f v w' z
      | none => pure Val.notImpl
    match x with
    | .notImpl =>
      let w ← getW
      if z.is .none then
        typeErr s!"unsupported operand type(s) for {trunc 100 name}: '{trunc 100 (typeName w v)}' and '{trunc 100 (typeName w w')}'"
      else
        typeErr s!"unsupported operand type(s) for {trunc 100 name}: '{trunc 100 (typeName w v)}', '{trunc 100 (typeName w w')}', '{trunc 100 (typeName w z)}'"
    | x => pure x
  let afterV (slotw : Option SlotFn) : M Val := do
    let x ← match slotw with
      | some f => callNbPower rt f v w' z
      | none => pure Val.notImpl
    match x with
    | .notImpl => afterZ slotw
    | x => pure x
  match slotv with
  | some sv =>
    let first : M (Option Val × Option SlotFn) :=
      match slotw0 with
      | some sw =>
        if isSubtype w (typeOf w w') (typeOf w v) then do
          let x ← callNbPower rt sw v w' z
          match x with
          | .notImpl => pure (none, none)
          | x => pure (some x, none)
        else pure (none, slotw0)
      | none => pure (none, slotw0)
    let (early, slotw) ← first
    match early with
    | some x => pure x
    | none =>
      let x ← callNbPower rt sv v w' z
      match x with
      | .notImpl => afterV slotw
      | x => pure x
  | none => afterV slotw0

/-- `PyNumber_Power`, `Objects/abstract.c:1190`. -/
def pyNumberPower (rt : Rt) (v w' z : Val) : M Val := ternaryOp rt v w' z "** or pow()"

/-- `ternary_iop`, `Objects/abstract.c:1262`. `slot_nb_inplace_power` drops the third
argument (`Objects/typeobject.c:10270`). -/
def ternaryIop (rt : Rt) (v w' z : Val) : M Val := do
  let w ← getW
  let x ← match slotIn w v .nb_inplace_power with
    | some .generic => vectorcallMethod rt "__ipow__" [v, w']
    | some _ => unmodelled
    | none => pure Val.notImpl
  match x with
  | .notImpl => ternaryOp rt v w' z "**="
  | x => pure x

/-- `UNARY_FUNC`, `Objects/abstract.c:1364`. -/
def unaryFunc (rt : Rt) (s : Slot) (dunder descr : String) (o : Val) : M Val := do
  let w ← getW
  match slotIn w o s with
  | some f => callUnaryNb rt s dunder f o
  | none => typeErr s!"bad operand type for {descr}: '{trunc 200 (typeName w o)}'"

def pyNumberNegative (rt : Rt) := unaryFunc rt .nb_negative "__neg__" "unary -"
def pyNumberPositive (rt : Rt) := unaryFunc rt .nb_positive "__pos__" "unary +"
def pyNumberInvert (rt : Rt) := unaryFunc rt .nb_invert "__invert__" "unary ~"
def pyNumberAbsolute (rt : Rt) := unaryFunc rt .nb_absolute "__abs__" "abs()"

/-- `PyNumber_Check`, `Objects/abstract.c:903` (no `complex` in this model). -/
def pyNumberCheck (w : World) (o : Val) : Bool :=
  (slotIn w o .nb_index).isSome || (slotIn w o .nb_int).isSome || (slotIn w o .nb_float).isSome

/-- `PyLong_FromUnicodeObject(s, 10)` for ASCII decimal literals with surrounding
whitespace and a sign. `LongObj` has the full parser. -/
def parseIntLiteral (s : String) : Option Int :=
  let t := (s.trimAscii).toString
  let (neg, digits) := match t.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  if digits.isEmpty || !digits.all Char.isDigit then none
  else
    let n : Nat := digits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0
    some (if neg then -(n : Int) else n)

/-- `PyNumber_Long`, `Objects/abstract.c:1509`, up to the string-parsing fallbacks. -/
def pyNumberLong (rt : Rt) (o : Val) : M Val := do
  match o with
  | .int _ => pure o
  | _ =>
    let w ← getW
    match slotIn w o .nb_int with
    | some f =>
      let result ← callUnaryNb rt .nb_int "__int__" f o
      let w ← getW
      match result with
      | .int _ => pure result
      | _ =>
        match intOf w result with
        | some i => pure (.int i)
        | none => typeErr s!"__int__ returned non-int (type {trunc 200 (typeName w result)})"
    | none =>
      match slotIn w o .nb_index with
      | some _ => .int <$> pyNumberIndex rt o
      | none =>
        match strOf w o with
        | some st =>
          match parseIntLiteral st with
          | some i => pure (.int i)
          | none =>
            let r ← rt.repr o
            valueErr s!"invalid literal for int() with base 10: {r}"
        | none =>
          typeErr s!"int() argument must be a string, a bytes-like object or a real number, not '{trunc 200 (typeName w o)}'"

/-- `PyNumber_Float`, `Objects/abstract.c:1592`, up to the string-parsing fallback. -/
def pyNumberFloat (rt : Rt) (o : Val) : M Val := do
  match o with
  | .float _ => pure o
  | _ =>
    let w ← getW
    match slotIn w o .nb_float with
    | some f =>
      let res ← match f with
        | .generic => vectorcallMethod rt "__float__" [o]
        | _ => unmodelled
      let w ← getW
      match res with
      | .float _ => pure res
      | _ =>
        match payloadOf w res with
        | some (.boxed (.float b)) => pure (.float b)
        | _ =>
          typeErr s!"{trunc 50 (typeName w o)}.__float__ returned non-float (type {trunc 50 (typeName w res)})"
    | none =>
      match slotIn w o .nb_index with
      | some _ =>
        let _ ← numberIndex rt o
        unmodelled
      | none =>
        match payloadOf w o with
        | some (.boxed (.float b)) => pure (.float b)
        | _ =>
          typeErr s!"float() argument must be a string or a real number, not '{trunc 200 (typeName w o)}'"

/-! ## Sequences, mappings, iteration -/

/-- `slot_sq_contains`, `sq_item`, ... use these. `PySequence_Check`,
`Objects/abstract.c:1672`. -/
def pySequenceCheck (w : World) (s : Val) : Bool :=
  (dictOf w s).isNone && (slotIn w s .sq_item).isSome

/-- `PyMapping_Check`, `Objects/abstract.c:2260`. -/
def pyMappingCheck (w : World) (o : Val) : Bool := (slotIn w o .mp_subscript).isSome

/-- `slot_sq_item`, `Objects/typeobject.c:10046`, and `sq_item` of builtin sequences. -/
def callSqItem (rt : Rt) (f : SlotFn) (s : Val) (i : Int) : M Val := do
  let w ← getW
  let at' (xs : List Val) (msg : String) : M Val :=
    if i < 0 then indexErr msg else
    match xs[i.toNat]? with
    | some x => pure x
    | none => indexErr msg
  match f with
  | .generic => vectorcallMethod rt "__getitem__" [s, .int i]
  | .c .tuple => at' ((tupleOf w s).getD []) "tuple index out of range"
  | .c .list => at' ((listOf w s).getD []) "list index out of range"
  | .c .str =>
    at' (((strOf w s).getD "").toList.map fun c => Val.str c.toString) "string index out of range"
  | _ => unmodelled

/-- Call `mp_subscript`. Builtin sequences take integer indices; slices belong to the
`RangeSlice` and `Sequences` modules. -/
def callMpSubscript (rt : Rt) (f : SlotFn) (o key : Val) : M Val := do
  let w ← getW
  let bySeq (slotF : SlotFn) (kind : String) : M Val := do
    if indexCheck w key then
      let i ← numberAsSsize rt key (some B.IndexError)
      let n ← callLen rt slotF o
      callSqItem rt slotF o (if i < 0 then i + n else i)
    else if kind == "str" then
      typeErr s!"string indices must be integers, not '{trunc 200 (typeName w key)}'"
    else
      typeErr s!"{kind} indices must be integers or slices, not {trunc 200 (typeName w key)}"
  match f with
  | .generic => vectorcallMethod rt "__getitem__" [o, key]
  | .c .list => bySeq f "list"
  | .c .tuple => bySeq f "tuple"
  | .c .str => bySeq f "str"
  | .c .dict =>
    dictHashKey rt key
    match dictLookup ((dictOf w o).getD []) key with
    | some v => pure v
    | none =>
      let x ← alloc B.KeyError (.exc { args := [key] })
      raise (.exc B.KeyError "" (some x))
  | .c .mappingproxy =>
    match payloadOf w o, key with
    | some (.typeDictProxy t), .str n =>
      match NameDict.get? (tdata w t).dict n with
      | some v => pure v
      | none =>
        let x ← alloc B.KeyError (.exc { args := [key] })
        raise (.exc B.KeyError "" (some x))
    | _, _ => unmodelled
  | _ => unmodelled

/-- `PySequence_GetItem`, `Objects/abstract.c:1832`. -/
def pySequenceGetItem (rt : Rt) (s : Val) (i : Int) : M Val := do
  let w ← getW
  match slotIn w s .sq_item with
  | some f =>
    let i' ← if i < 0 then
        match slotIn w s .sq_length with
        | some lf => do
          let l ← callLen rt lf s
          pure (i + l)
        | none => pure i
      else pure i
    callSqItem rt f s i'
  | none =>
    match slotIn w s .mp_subscript with
    | some _ => typeErr s!"{trunc 200 (typeName w s)} is not a sequence"
    | none => typeErr s!"'{trunc 200 (typeName w s)}' object does not support indexing"

/-- `PyObject_GetItem`, `Objects/abstract.c:153`. `type[int]` (generic aliases) is left
out. -/
def pyGetItem (rt : Rt) (o key : Val) : M Val := do
  let w ← getW
  match slotIn w o .mp_subscript with
  | some f => callMpSubscript rt f o key
  | none =>
    match slotIn w o .sq_item with
    | some _ =>
      if indexCheck w key then
        let v ← numberAsSsize rt key (some B.IndexError)
        pySequenceGetItem rt o v
      else
        typeErr s!"sequence index must be integer, not '{trunc 200 (typeName w key)}'"
    | none =>
      match asType w o with
      | some oa =>
        if oa == B.type then unmodelled else
        let meth ← rt.getOptionalAttr o "__class_getitem__"
        match meth with
        | some m =>
          if m.is .none then typeErr s!"type '{trunc 200 (tpName w oa)}' is not subscriptable"
          else rt.call m [key] []
        | none => typeErr s!"type '{trunc 200 (tpName w oa)}' is not subscriptable"
      | none => typeErr s!"'{trunc 200 (typeName w o)}' object is not subscriptable"

/-- `slot_mp_ass_subscript`/`slot_sq_ass_item` and the list and dict `mp_ass_subscript`. -/
def callAssSubscript (rt : Rt) (f : SlotFn) (o key : Val) (value : Option Val) : M Unit := do
  let w ← getW
  match f with
  | .generic =>
    match value with
    | none => let _ ← vectorcallMethod rt "__delitem__" [o, key]
    | some v => let _ ← vectorcallMethod rt "__setitem__" [o, key, v]
  | .c .dict =>
    dictHashKey rt key
    let w ← getW
    let es := (dictOf w o).getD []
    match o with
    | .obj a =>
      match value with
      | some v => modObj a fun ob => { ob with body := .dict (dictSetEntry es key v) }
      | none =>
        match dictLookup es key with
        | some _ => modObj a fun ob => { ob with body := .dict (dictDelEntry es key) }
        | none =>
          let x ← alloc B.KeyError (.exc { args := [key] })
          raise (.exc B.KeyError "" (some x))
    | _ => unmodelled
  | .c .list =>
    let xs := (listOf w o).getD []
    if indexCheck w key then
      let i ← numberAsSsize rt key (some B.IndexError)
      let i := if i < 0 then i + xs.length else i
      if i < 0 || i ≥ xs.length then indexErr "list assignment index out of range" else
      match o, value with
      | .obj a, some v => modObj a fun ob => { ob with body := .list (xs.set i.toNat v) }
      | .obj a, none => modObj a fun ob => { ob with body := .list (xs.eraseIdx i.toNat) }
      | _, _ => unmodelled
    else typeErr s!"list indices must be integers or slices, not {trunc 200 (typeName w key)}"
  | _ => unmodelled

/-- `PySequence_SetItem`/`PySequence_DelItem`, `Objects/abstract.c:1884`, `:1917`. -/
def pySequenceSetItem (rt : Rt) (s : Val) (i : Int) (value : Option Val) : M Unit := do
  let w ← getW
  let verb := match value with
    | some _ => "does not support item assignment"
    | none => "doesn't support item deletion"
  match slotIn w s .sq_ass_item with
  | some f =>
    let i' ← if i < 0 then
        match slotIn w s .sq_length with
        | some lf => do
          let l ← callLen rt lf s
          pure (i + l)
        | none => pure i
      else pure i
    callAssSubscript rt f s (.int i') value
  | none =>
    match slotIn w s .mp_ass_subscript with
    | some _ => typeErr s!"{trunc 200 (typeName w s)} is not a sequence"
    | none => typeErr s!"'{trunc 200 (typeName w s)}' object {verb}"

/-- `PyObject_SetItem` and `PyObject_DelItem`, `Objects/abstract.c:226`, `:260`. -/
def pySetItem (rt : Rt) (o key : Val) (value : Option Val) : M Unit := do
  let w ← getW
  let verb := match value with
    | some _ => "assignment"
    | none => "deletion"
  match slotIn w o .mp_ass_subscript with
  | some f => callAssSubscript rt f o key value
  | none =>
    if hasGroup w (typeOf w o) .sequence then
      if indexCheck w key then
        let v ← numberAsSsize rt key (some B.IndexError)
        pySequenceSetItem rt o v value
      else if (slotIn w o .sq_ass_item).isSome then
        typeErr s!"sequence index must be integer, not '{trunc 200 (typeName w key)}'"
      else typeErr s!"'{trunc 200 (typeName w o)}' object does not support item {verb}"
    else typeErr s!"'{trunc 200 (typeName w o)}' object does not support item {verb}"

/-- `PySeqIter_New`, `Objects/iterobject.c`. -/
def pySeqIterNew (seq : Val) : M Val := alloc B.seqIter (.seqIter (some seq) 0)

/-- `slot_tp_iter`, `Objects/typeobject.c:10496`. -/
def slotTpIter (rt : Rt) (self : Val) : M Val := do
  let m ← maybeCallSpecial rt self "__iter__" [] true
  match m with
  | .res r => pure r
  | m =>
    let attrIsNone := match m with
      | .isNone => true
      | _ => false
    let hasGetitem ← do
      match ← lookupMethodEx rt self "__getitem__" false with
      | .missing => pure false
      | _ => pure true
    if attrIsNone || !hasGetitem then
      let w ← getW
      typeErr s!"'{trunc 200 (typeName w self)}' object is not iterable"
    else pySeqIterNew self

/-- Call the `tp_iter` function `f`. -/
def callIter (rt : Rt) (f : SlotFn) (o : Val) : M Val := do
  match f with
  | .generic => slotTpIter rt o
  | .c .list => alloc B.listIter (.seqIter (some o) 0)
  | .c .dict =>
    let w ← getW
    let keys ← alloc B.list (.list (((dictOf w o).getD []).map (·.1)))
    alloc B.dictKeyIter (.seqIter (some keys) 0)
  | .c .dictKeys =>
    -- `dictkeys_iter`, `Objects/dictobject.c:6150`: a key iterator over the view's dict.
    let w ← getW
    match o with
    | .obj a =>
      match w.get a with
      | .val { body := .seqIter (some d) _, .. } =>
        let keys ← alloc B.list (.list (((dictOf w d).getD []).map (·.1)))
        alloc B.dictKeyIter (.seqIter (some keys) 0)
      | _ => unmodelled
    | _ => unmodelled
  | .c .tuple => alloc B.tupleIter (.seqIter (some o) 0)
  | .c .str => alloc B.strIter (.seqIter (some o) 0)
  | .c .seqIter | .c .listIter | .c .tupleIter | .c .strIter => pure o
  | _ => unmodelled

/-- `PyIter_Check`, `Objects/abstract.c:2850`. -/
def pyIterCheck (w : World) (o : Val) : Bool :=
  match slotOf w (typeOf w o) .tp_iternext with
  | none | some .nextNotImpl => false
  | some _ => true

/-- `PyObject_GetIter`, `Objects/abstract.c:2806`. -/
def pyGetIter (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  match slotOf w (typeOf w o) .tp_iter with
  | none =>
    if pySequenceCheck w o then pySeqIterNew o
    else typeErr s!"'{trunc 200 (typeName w o)}' object is not iterable"
  | some f =>
    let res ← callIter rt f o
    let w ← getW
    if pyIterCheck w res then pure res
    else typeErr s!"iter() returned non-iterator of type '{trunc 100 (typeName w res)}'"

/-- `iter_iternext`, `Objects/iterobject.c:53`. `none` is NULL with no exception. -/
def seqIterNext (rt : Rt) (a : Addr) : M (Option Val) := do
  let w ← getW
  match w.get a with
  | .val { body := .seqIter none _, .. } => pure none
  | .val { body := .seqIter (some seq) i, .. } =>
    if i == PyLean.ssizeMax then overflowErr "iter index too large" else
    let clear : M (Option Val) := do
      modObj a fun o => { o with body := .seqIter none i }
      pure none
    tryM (do
        let r ← pySequenceGetItem rt seq i
        modObj a fun o => { o with body := .seqIter (some seq) (i + 1) }
        pure (some r))
      fun e => do
        let w ← getW
        if excMatches w e B.IndexError || excMatches w e B.StopIteration then clear
        else raise e
  | _ => unmodelled

/-- `listiter_next`/`tupleiter_next`/`unicodeiter_next`: stop at the end of the sequence
and drop the reference, `Objects/listobject.c:4019`. -/
def builtinIterNext (rt : Rt) (f : SlotFn) (a : Addr) : M (Option Val) := do
  let w ← getW
  match w.get a with
  | .val { body := .seqIter none _, .. } => pure none
  | .val { body := .seqIter (some seq) i, .. } =>
    let itemF : SlotFn := match f with
      | .c .listIter => .c .list
      | .c .tupleIter => .c .tuple
      | _ => .c .str
    let n ← callLen rt itemF seq
    if i < n then
      let r ← callSqItem rt itemF seq i
      modObj a fun o => { o with body := .seqIter (some seq) (i + 1) }
      pure (some r)
    else
      modObj a fun o => { o with body := .seqIter none i }
      pure none
  | _ => unmodelled

/-- Call `tp_iternext`; `none` is NULL with no exception set. -/
def callIterNext (rt : Rt) (f : SlotFn) (it : Val) : M (Option Val) := do
  let w ← getW
  match f, it with
  | .generic, _ => some <$> vectorcallMethod rt "__next__" [it]
  | .nextNotImpl, _ => typeErr s!"'{trunc 200 (typeName w it)}' object is not iterable"
  | .c .seqIter, .obj a => seqIterNext rt a
  | .c .listIter, .obj a | .c .tupleIter, .obj a | .c .strIter, .obj a =>
    builtinIterNext rt f a
  | _, _ => unmodelled

/-- `iternext` and `PyIter_Next`, `Objects/abstract.c:2867`, `:2917`. -/
def pyIterNext (rt : Rt) (it : Val) : M (Option Val) := do
  let w ← getW
  match slotOf w (typeOf w it) .tp_iternext with
  | some f => catchMatch B.StopIteration (callIterNext rt f it) (pure none)
  | none => unmodelled

/-- `PySequence_List` by iteration; `fuel` bounds the loop. -/
def collectIter (rt : Rt) (it : Val) : Nat → M (List Val)
  | 0 => raise .fuel
  | fuel + 1 => do
    match ← rt.iterNext it with
    | none => pure []
    | some x =>
      let rest ← collectIter rt it fuel
      pure (x :: rest)

/-- `PySequence_Tuple`, `Objects/abstract.c:1996`, items only. The eight-item stack
buffer of `:2021` changes nothing visible. -/
def pySequenceTuple (rt : Rt) (v : Val) : M (List Val) := do
  match v with
  | .tuple xs => pure xs
  | _ =>
    let w ← getW
    match listOf w v, typeOf w v == B.list with
    | some xs, true => pure xs
    | _, _ =>
      let it ← rt.getIter v
      collectIter rt it iterFuel

/-- `PySequence_List`, `Objects/abstract.c:2072`, items only, through `list_extend`
(`Objects/listobject.c`): exact lists and tuples are copied, anything else is iterated
after `PyObject_LengthHint(iterable, 8)` sizes the result. The hint is observable: it
calls `__len__` or `__length_hint__`. -/
def pySequenceList (rt : Rt) (v : Val) : M (List Val) := do
  let w ← getW
  match v with
  | .tuple xs => pure xs
  | _ =>
    match listOf w v, typeOf w v == B.list with
    | some xs, true => pure xs
    | _, _ =>
      let it ← rt.getIter v
      let n ← pyLengthHint rt v 8
      -- `list_preallocate_exact`: a size no allocator can serve.
      if n ≥ 2 ^ 48 then raiseC B.MemoryError ""
      collectIter rt it iterFuel

/-- The three operations of `_PySequence_IterSearch`. -/
inductive IterSearchOp where
  | count | index | contains
  deriving DecidableEq, Repr

/-- The loop of `_PySequence_IterSearch`, `Objects/abstract.c:2156-2203`. -/
def iterSearchLoop (rt : Rt) (it obj : Val) (op : IterSearchOp) : Nat → Int → M (Option Int)
  | 0, _ => raise .fuel
  | fuel + 1, n => do
    match ← rt.iterNext it with
    | none => pure none
    | some item =>
      let cmp ← richCompareBool rt item obj .eq
      if cmp then
        match op with
        | .count => iterSearchLoop rt it obj op fuel (n + 1)
        | .index => pure (some n)
        | .contains => pure (some 1)
      else if op == .index then iterSearchLoop rt it obj op fuel (n + 1)
      else iterSearchLoop rt it obj op fuel n

/-- The count of `PY_ITERSEARCH_COUNT` on exhaustion lives in the accumulator; this
variant returns it. -/
def iterCountLoop (rt : Rt) (it obj : Val) : Nat → Int → M Int
  | 0, _ => raise .fuel
  | fuel + 1, n => do
    match ← rt.iterNext it with
    | none => pure n
    | some item =>
      let cmp ← richCompareBool rt item obj .eq
      iterCountLoop rt it obj fuel (if cmp then n + 1 else n)

/-- `_PySequence_IterSearch`, `Objects/abstract.c:2129`. -/
def pySequenceIterSearch (rt : Rt) (seq obj : Val) (op : IterSearchOp) : M Int := do
  let it ← tryM (rt.getIter seq) fun e => do
    let w ← getW
    if excMatches w e B.TypeError then
      if op == .contains then
        typeErr s!"argument of type '{trunc 200 (typeName w seq)}' is not a container or iterable"
      else
        typeErr s!"argument of type '{trunc 200 (typeName w seq)}' is not iterable"
    else raise e
  match op with
  | .count => iterCountLoop rt it obj iterFuel 0
  | .index =>
    match ← iterSearchLoop rt it obj .index iterFuel 0 with
    | some n => pure n
    | none => valueErr "sequence.index(x): x not in sequence"
  | .contains =>
    match ← iterSearchLoop rt it obj .contains iterFuel 0 with
    | some n => pure n
    | none => pure 0

/-- `slot_sq_contains`, `Objects/typeobject.c:10089`. -/
def slotSqContains (rt : Rt) (self value : Val) : M Bool := do
  match ← maybeCallSpecial rt self "__contains__" [value] true with
  | .isNone =>
    let w ← getW
    typeErr s!"'{trunc 200 (typeName w self)}' object is not a container"
  | .missing =>
    let r ← pySequenceIterSearch rt self value .contains
    pure (r != 0)
  | .res r => rt.isTrue r

/-- `list_contains`/`tuple_contains`: identity-or-equality search. -/
def anyEq (rt : Rt) (x : Val) : List Val → M Bool
  | [] => pure false
  | y :: ys => do
    if ← richCompareBool rt y x .eq then pure true else anyEq rt x ys

/-- `PyUnicode_Contains`. -/
def strContains (s t : List Char) : Bool :=
  match s with
  | [] => t.isEmpty
  | _ :: rest => t.isPrefixOf s || strContains rest t

/-- Call `sq_contains`. -/
def callContains (rt : Rt) (f : SlotFn) (seq ob : Val) : M Bool := do
  let w ← getW
  match f with
  | .generic => slotSqContains rt seq ob
  | .c .tuple => anyEq rt ob ((tupleOf w seq).getD [])
  | .c .list => anyEq rt ob ((listOf w seq).getD [])
  | .c .dict =>
    dictHashKey rt ob
    let w ← getW
    pure (dictLookup ((dictOf w seq).getD []) ob).isSome
  | .c .str =>
    match strOf w ob with
    | some t => pure (strContains ((strOf w seq).getD "").toList t.toList)
    | none =>
      typeErr s!"'in <string>' requires string as left operand, not {trunc 200 (typeName w ob)}"
  | _ => unmodelled

/-- `PySequence_Contains`, `Objects/abstract.c:2231`. -/
def pySequenceContains (rt : Rt) (seq ob : Val) : M Bool := do
  let w ← getW
  match slotIn w seq .sq_contains with
  | some f => callContains rt f seq ob
  | none =>
    let r ← pySequenceIterSearch rt seq ob .contains
    pure (r != 0)

/-! ## `isinstance` and `issubclass` -/

/-- `abstract_get_bases`, `Objects/abstract.c:2515`. -/
def abstractGetBases (rt : Rt) (cls : Val) : M (Option (List Val)) := do
  match ← rt.getOptionalAttr cls "__bases__" with
  | none => pure none
  | some b =>
    let w ← getW
    pure (tupleOf w b)

mutual
  /-- `abstract_issubclass`, `Objects/abstract.c:2529`. `fuel` stands in for the
  recursion limit and bounds the loop. -/
  def abstractIssubclass (rt : Rt) (fuel : Nat) (derived cls : Val) : M Bool :=
    match fuel with
    | 0 => raise .fuel
    | fuel + 1 => do
      if derived.is cls then return true
      match ← abstractGetBases rt derived with
      | none => pure false
      | some [] => pure false
      | some [b] => abstractIssubclass rt fuel b cls
      | some bs => abstractAny rt fuel bs cls
  /-- The `for` at `Objects/abstract.c:2568`. -/
  def abstractAny (rt : Rt) (fuel : Nat) (bs : List Val) (cls : Val) : M Bool :=
    match bs with
    | [] => pure false
    | b :: rest => do
      if ← abstractIssubclass rt fuel b cls then pure true
      else
        match fuel with
        | 0 => raise .fuel
        | fuel + 1 => abstractAny rt fuel rest cls
end

/-- `check_class`, `Objects/abstract.c:2580`: `false` raises. -/
def checkClass (rt : Rt) (cls : Val) (error : String) : M Unit := do
  match ← abstractGetBases rt cls with
  | none => typeErr error
  | some _ => pure ()

/-- Recursion bound for class walks. A model limit: the interpreter would raise
`RecursionError` first. -/
def walkFuel : Nat := 2000

/-- `object_isinstance`, `Objects/abstract.c:2596`. -/
def objectIsinstance (rt : Rt) (inst cls : Val) : M Bool := do
  let w ← getW
  match asType w cls with
  | some ca =>
    if isSubtype w (typeOf w inst) ca then pure true
    else
      match ← rt.getOptionalAttr inst "__class__" with
      | none => pure false
      | some icls =>
        let w ← getW
        match asType w icls with
        | some ia =>
          if ia != typeOf w inst then pure (isSubtype w ia ca) else pure false
        | none => pure false
  | none =>
    checkClass rt cls "isinstance() arg 2 must be a type, a tuple of types, or a union"
    match ← rt.getOptionalAttr inst "__class__" with
    | none => pure false
    | some icls => abstractIssubclass rt walkFuel icls cls

/-- `object_recursive_isinstance`, `Objects/abstract.c:2632`. Union objects are left
out. -/
def objectRecursiveIsinstance (rt : Rt) : Nat → Val → Val → M Bool
  | 0, _, _ => raise .fuel
  | fuel + 1, inst, cls => do
    let w ← getW
    if (asType w cls).isSome && (Val.obj (typeOf w inst)).is cls then return true
    if typeOf w cls == B.type then return ← objectIsinstance rt inst cls
    match tupleOf w cls with
    | some xs =>
      anyTuple fuel inst xs
    | none =>
      match ← lookupSpecial rt cls "__instancecheck__" with
      | some checker =>
        let res ← rt.call checker [inst] []
        rt.isTrue res
      | none => objectIsinstance rt inst cls
where
  anyTuple (fuel : Nat) (inst : Val) : List Val → M Bool
    | [] => pure false
    | x :: xs => do
      if ← objectRecursiveIsinstance rt fuel inst x then pure true else anyTuple fuel inst xs

/-- `PyObject_IsInstance`, `Objects/abstract.c:2697`. -/
def pyIsInstance (rt : Rt) (inst cls : Val) : M Bool :=
  objectRecursiveIsinstance rt walkFuel inst cls

/-- `recursive_issubclass`, `Objects/abstract.c:2705`. -/
def recursiveIssubclass (rt : Rt) (derived cls : Val) : M Bool := do
  let w ← getW
  match asType w cls, asType w derived with
  | some c, some d => pure (isSubtype w d c)
  | _, _ =>
    checkClass rt derived "issubclass() arg 1 must be a class"
    checkClass rt cls "issubclass() arg 2 must be a class, a tuple of classes, or a union"
    abstractIssubclass rt walkFuel derived cls

/-- `object_issubclass`, `Objects/abstract.c:2725`. -/
def objectIssubclass (rt : Rt) : Nat → Val → Val → M Bool
  | 0, _, _ => raise .fuel
  | fuel + 1, derived, cls => do
    let w ← getW
    if typeOf w cls == B.type then
      if derived.is cls then return true
      return ← recursiveIssubclass rt derived cls
    match tupleOf w cls with
    | some xs => anyTuple fuel derived xs
    | none =>
      match ← lookupSpecial rt cls "__subclasscheck__" with
      | some checker =>
        let res ← rt.call checker [derived] []
        rt.isTrue res
      | none => recursiveIssubclass rt derived cls
where
  anyTuple (fuel : Nat) (derived : Val) : List Val → M Bool
    | [] => pure false
    | x :: xs => do
      if ← objectIssubclass rt fuel derived x then pure true else anyTuple fuel derived xs

/-- `PyObject_IsSubclass`, `Objects/abstract.c:2785`. -/
def pyIsSubclass (rt : Rt) (derived cls : Val) : M Bool :=
  objectIssubclass rt walkFuel derived cls

end PyLean.TypeObj
