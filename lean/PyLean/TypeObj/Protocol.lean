import PyLean.TypeObj.FloatOps

/-!
The abstract object protocols: rich comparison, truth, hashing, repr/str
(`Objects/object.c`), numbers, sequences, mappings, iteration, `isinstance`
(`Objects/abstract.c`), and the `slot_*` dispatchers behind them
(`Objects/typeobject.c:10643-11344`).

Each `call*` function applies the C function stored in a slot. The builtin value types
(`int`, `str`, `tuple`, `list`, `dict`) have just enough of their C slots to exercise the
protocols; the full semantics of those types belongs to the `LongObj`, `UnicodeObj`,
`Sequences` and `DictSet` modules.
-/

namespace PyLean.TypeObj

/-- Loop bound for iteration. A model limit, not a Python one. -/
def iterFuel : Nat := 100000

/-! ## Truth and comparison -/

/-- `PyObject_RichCompareBool`, `Objects/object.c:1122`. -/
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

/-- The shared loop of `list_richcompare_impl` (`Objects/listobject.c:3459`) and
`tuple_richcompare` (`Objects/tupleobject.c:738`) after the length shortcut: find the
first index whose items are not equal. `none` means one sequence ran out. -/
def firstDiff (rt : Rt) : List Val → List Val → M (Option (Val × Val))
  | [], _ | _, [] => pure none
  | a :: as, b :: bs => do
    if a.is b then firstDiff rt as bs
    else
      let k ← richCompareBool rt a b .eq
      if k then firstDiff rt as bs else pure (some (a, b))

/-- `tuple_richcompare`, `Objects/tupleobject.c:738`, given both item lists. -/
def seqRichcompare (rt : Rt) (vs ws : List Val) (op : CmpOp) : M Val := do
  match ← firstDiff rt vs ws with
  | none => pure (.bool (cmpInt vs.length ws.length op))
  | some (a, b) =>
    if op == .eq then pure (.bool false)
    else if op == .ne then pure (.bool true)
    else rt.richCompare a b op

/-- `list_richcompare_impl`, `Objects/listobject.c:3459`: adds the length shortcut. -/
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

/-- The value has one object in CPython 3.15.2, so equal values are the same object: `None`,
`NotImplemented`, `Ellipsis`, the bools, the small ints `-5..256` (`_PyLong_SMALL_INTS`), the empty
string and the one-character Latin-1 strings (`_Py_LATIN1_CHR`), the empty tuple, and heap objects
(by address). -/
def identityDetermined : Val → Bool
  | .obj _ | .none | .notImpl | .ellipsis | .bool _ => true
  | .int i => decide (-5 ≤ i) && decide (i ≤ 256)
  | .str s => decide (s.toList.length ≤ 1) && s.toList.all (fun c => decide (c.toNat < 256))
  | .tuple [] => true
  | _ => false

/-- `self == other` on `PyObject *`, where the model knows it. Different values are different
objects (`Val.is` is implied by identity). Equal values of a kind without a unique object (a big
`int`, a `float`, a longer `str`, a non-empty tuple) may or may not be one object in CPython:
`object.__eq__(int('1'*30), int('1'*30))` is `NotImplemented` there, while `x = 10**30;
object.__eq__(x, x)` is `True`. The model does not track that identity, so it answers `none`. -/
def identityKnown (v w : Val) : Option Bool :=
  if !v.is w then some false else if identityDetermined v then some true else none

/-- `object_richcompare`, `Objects/typeobject.c:7577-7618`, for the cases that do not recurse
into the slot. `eqSlot` is `tp_richcompare(self, other, Py_EQ)` of the type of `self`, and is
`NotImplemented` when that slot is NULL (`:7593-7596`, `callRichcompare`). `Py_EQ` compares
pointers (`:7587`); where the model cannot tell (`identityKnown`), it stops (`gap%`). -/
def objectRichcompare (rt : Rt) (eqSlot : M Val) (self other : Val) (op : CmpOp) : M Val :=
  match op with
  | .eq =>
    match identityKnown self other with
    | some true => pure (.bool true)
    | some false => pure .notImpl
    | none => gap%
  | .ne => do
    let res ← eqSlot
    match res with
    | .notImpl => pure .notImpl
    | r =>
      let ok ← rt.isTrue r
      pure (.bool (!ok))
  | _ => pure .notImpl

/-- `slot_tp_richcompare`, `Objects/typeobject.c:11172`. -/
def slotTpRichcompare (rt : Rt) (self other : Val) (op : CmpOp) : M Val := do
  match ← maybeCallSpecial rt self op.dunder [other] false with
  | .res r => pure r
  | _ => pure .notImpl

/-- `method_richcompare`, `Objects/classobject.c:225`. -/
def methodRichcompare (rt : Rt) (self other : Val) (op : CmpOp) : M Val := do
  let w ← getW
  match op, payloadOf w self, payloadOf w other with
  | .eq, some (.bound f1 s1), some (.bound f2 s2)
  | .ne, some (.bound f1 s1), some (.bound f2 s2) =>
    let eq ← richCompareBool rt f1 f2 .eq
    let eq := eq && s1.is s2
    pure (.bool (if op == .eq then eq else !eq))
  | _, _, _ => pure .notImpl

/-- `Py_RETURN_RICHCOMPARE` result for `long_richcompare`, `Objects/longobject.c:3626`. -/
def longRichcompare (w : World) (a b : Val) (op : CmpOp) : Val :=
  match intOf w a, intOf w b with
  | some x, some y => .bool (cmpInt x y op)
  | _, _ => .notImpl

/-- `PyUnicode_RichCompare`, `Objects/unicodeobject.c:11263`. -/
def unicodeRichcompare (w : World) (a b : Val) (op : CmpOp) : Val :=
  match strOf w a, strOf w b with
  | some x, some y => .bool (cmpInt (strCompare x.toList y.toList) 0 op)
  | _, _ => .notImpl

/-- The hash of a str. CPython randomises it per process, so only equality of hashes can be
observed. This is FNV-1a over the code points, kept away from the small ints of ordinary code. -/
def strHash (t : String) : Int :=
  let h := t.toList.foldl (fun (acc : Nat) c => ((acc ^^^ c.toNat) * 1099511628211) % 2 ^ 64)
    14695981039346656037
  ((h % 2 ^ 61 : Nat) : Int) + 2 ^ 61

/-- The entries of the dict at `a`. -/
def dictEntries (w : World) (a : Addr) : List (Val × Val) :=
  match (w.objAt a).body with
  | .dict es | .frozen es => es
  | _ => []

/-- `me_hash` of key `k` of the dict at `a`. A key with no record was stored by a C path of the
model, and is an exact str. -/
def storedHash (w : World) (a : Addr) (k : Val) : Int :=
  match (w.objAt a).keyHashes.find? (·.1.is k), k with
  | some (_, h), _ => h
  | none, .str t => strHash t
  | none, _ => 0

/-- `_Py_dict_lookup`, `Objects/dictobject.c:1328`, through `compare_generic`, `:1182`: identity,
then the stored hash, then `PyObject_RichCompareBool(startkey, key, Py_EQ)`, and a restart when
the entry changed under the comparison (`:1121`). `some i` is the index of the entry.

The model has no hash table, so it visits entries in insertion order. Only entries of equal hash
can be compared, and those share a probe sequence in the same order, unless a deletion left a slot
that a later key reused. C deletes in place, so deleting another entry during the comparison
leaves `ep->me_key` alone; the list here closes the gap, so the entry is found again by identity,
and only its removal restarts. A resize during the comparison also restarts C
(`dk != mp->ma_keys`), which the model cannot see. -/
def dictProbe (rt : Rt) (a : Addr) (key : Val) (hash : Int) : Nat → Nat → M (Option Nat)
  | 0, _ => raise .fuel
  | fuel + 1, i => do
    let w ← getW
    match (dictEntries w a)[i]? with
    | none => pure none
    | some (k, _) =>
      if k.is key then pure (some i)
      else if storedHash w a k == hash then
        let cmp ← richCompareBool rt k key .eq
        let w ← getW
        match (dictEntries w a).findIdx? (·.1.is k) with
        | some j =>
          if cmp then pure (some j) else dictProbe rt a key hash fuel (j + 1)
        | none => dictProbe rt a key hash fuel 0
      else dictProbe rt a key hash fuel (i + 1)

/-- The loop of `dict_equal_lock_held`, `Objects/dictobject.c:4633`: for each entry of `a`, look
its key up in `b` with the stored hash, then compare `aval` with `bval`. Both dicts are read again
each time, because the comparisons can change them. -/
def dictEqualLoop (rt : Rt) (a b : Addr) : Nat → Nat → M Bool
  | 0, _ => raise .fuel
  | fuel + 1, i => do
    let w ← getW
    match (dictEntries w a)[i]? with
    | none => pure true
    | some (k, aval) =>
      match ← dictProbe rt b k (storedHash w a k) iterFuel 0 with
      | none => pure false
      | some j =>
        let w ← getW
        match (dictEntries w b)[j]? with
        | none => pure false
        | some (_, bval) =>
          if ← richCompareBool rt aval bval .eq then dictEqualLoop rt a b fuel (i + 1)
          else pure false

/-- `dict_richcompare`, `Objects/dictobject.c:4695`. -/
def dictRichcompare (rt : Rt) (a b : Addr) (op : CmpOp) : M Val := do
  if op == .eq || op == .ne then
    let w ← getW
    let eq ← if (dictEntries w a).length != (dictEntries w b).length then pure false
      else dictEqualLoop rt a b iterFuel 0
    pure (.bool (if op == .eq then eq else !eq))
  else pure .notImpl

/-- `pp->mapping` of a `mappingproxy`. The proxy of a class has no dict object in this model, so
`tp_dict` is read out as one at each use, which is when C reads it. -/
def proxyMapping (self : Val) : M Val := do
  let w ← getW
  match payloadOf w self with
  | some (.proxy m) => pure m
  | some (.typeDictProxy t) =>
    alloc B.dict (.dict ((tdata w t).dict.map fun (k, v) => (Val.str k, v)))
  | _ => gap%

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
  | .c .mappingproxy =>
    -- `mappingproxy_richcompare`, `Objects/descrobject.c:1233`: an exact `dict` is only handed to
    -- what cannot keep it, and anything else gets a copy.
    if op == .eq || op == .ne then
      let m ← proxyMapping a
      let w ← getW
      if typeOf w m == B.dict &&
          !(typeOf w b == B.dict || typeOf w b == B.frozendict || typeOf w b == B.mappingproxy) then
        let c ← allocCell (.val { (w.objAt (match m with
          | .obj x => x
          | _ => 0)) with cls := B.dict, dict := none, slotVals := [] })
        rt.richCompare (.obj c) b op
      else rt.richCompare m b op
    else pure .notImpl
  | .c .dict | .c .frozendict =>
    match a, b, anyDictOf w a, anyDictOf w b with
    | .obj x, .obj y, some _, some _ => dictRichcompare rt x y op
    | _, _, _, _ => pure .notImpl
  | .c .float =>
    -- `float_richcompare`, `Objects/floatobject.c:406`, with its exact comparison of an int.
    match floatOf w a with
    | some x =>
      let bop : Binary64.CmpOp := match op with
        | .lt => .lt
        | .le => .le
        | .eq => .eq
        | .ne => .ne
        | .gt => .gt
        | .ge => .ge
      match Binary64.float_richcompare x (floatObj w b) bop with
      | some r => pure (.bool r)
      | none => pure .notImpl
    | none => pure .notImpl
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
    -- `wrapper_richcompare`, `Objects/descrobject.c:1344`.
    match op, payloadOf w a, payloadOf w b with
    | .eq, some (.methodWrapper d1 s1), some (.methodWrapper d2 s2)
    | .ne, some (.methodWrapper d1 s1), some (.methodWrapper d2 s2) =>
      let same := d1.is d2 && s1.is s2
      pure (.bool (if op == .eq then same else !same))
    | _, _, _ => pure .notImpl
  | _ => gap%

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

/-- `do_richcompare`, `Objects/object.c:1049`. -/
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

/-- `PyObject_Hash` failure, `PyObject_HashNotImplemented`, `Objects/object.c:1151`. -/
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

/-- The transformation of `slot_tp_hash`, `Objects/typeobject.c:11026-11036`. -/
def hashOfInt (i : Int) : Int :=
  let h := if inSsize i then i else longHash i
  if h == -1 then -2 else h

/-- `slot_tp_hash`, `Objects/typeobject.c:11004`. -/
def slotTpHash (rt : Rt) (self : Val) : M Int := do
  let m ← maybeCallSpecial rt self "__hash__" [] true
  match m with
  | .isNone | .missing => hashNotImplemented self
  | .res res =>
    let w ← getW
    match intOf w res with
    | none => typeErr "__hash__ method should return an integer"
    | some i => pure (hashOfInt i)

/-- The loop of `tuple_hash`, `Objects/tupleobject.c:392-401`, over 64-bit unsigned values. -/
def tupleHashLoop (rt : Rt) (acc : Nat) : List Val → M Nat
  | [] => pure acc
  | x :: xs => do
    let h ← rt.hash x
    let lane := (h % 2 ^ 64).toNat
    let acc := (acc + lane * 14029467366897019727) % 2 ^ 64
    let acc := ((acc <<< 31) % 2 ^ 64) ||| (acc >>> 33)
    tupleHashLoop rt ((acc * 11400714785074694791) % 2 ^ 64) xs

/-- `tuple_hash`, `Objects/tupleobject.c:372`. -/
def tupleHash (rt : Rt) (xs : List Val) : M Int := do
  let acc : Nat ← tupleHashLoop rt 2870177450012600261 xs
  let acc : Nat := (acc + (xs.length ^^^ (2870177450012600261 ^^^ 3527539))) % 2 ^ 64
  let acc : Nat := if acc == 2 ^ 64 - 1 then 1546275796 else acc
  pure (if acc ≥ 2 ^ 63 then (acc : Int) - 2 ^ 64 else (acc : Int))

/-- `PyObject_GenericHash`: a hash of the address. Values without identity in the model share one,
so that `a.is b` implies equal hashes. -/
def genericHash : Val → Int
  | .obj a => a
  | _ => 0

/-- The tail of `method_hash`, `meth_hash` and `wrapper_hash`: `x ^ y` on `Py_hash_t`, with `-1`
kept for errors. -/
def hashMix (x y : Int) : Int :=
  let r : Nat := (x % 2 ^ 64).toNat ^^^ (y % 2 ^ 64).toNat
  let s : Int := if r ≥ 2 ^ 63 then (r : Int) - 2 ^ 64 else r
  if s == -1 then -2 else s

/-- Call the `tp_hash` function `f`. -/
def callHash (rt : Rt) (f : SlotFn) (v : Val) : M Int := do
  let w ← getW
  match f with
  | .hashNotImpl => hashNotImplemented v
  | .generic => slotTpHash rt v
  | .c .int | .c .bool => pure (longHash ((intOf w v).getD 0))
  | .c .none => pure 0xfca86420
  | .c .object | .c .type | .c .function | .c .property =>
    pure (match v with
      | .obj a => (a : Int)
      | _ => 0)
  | .c .method =>
    -- `method_hash`, `Objects/classobject.c:281`: the hash of `__func__` can raise.
    match payloadOf w v with
    | some (.bound func s) =>
      let y ← rt.hash func
      pure (hashMix (genericHash s) y)
    | _ => gap%
  | .c .builtinFn =>
    -- `meth_hash`, `Objects/methodobject.c:343`. `ml_meth` is the builtin itself.
    match payloadOf w v with
    | some (.builtin b s) => pure (hashMix (genericHash (s.getD .none)) (strHash (toString (repr b))))
    | _ => gap%
  | .c .methodWrapper =>
    -- `wrapper_hash`, `Objects/descrobject.c:1370`.
    match payloadOf w v with
    | some (.methodWrapper d s) => pure (hashMix (genericHash s) (genericHash d))
    | _ => gap%
  | .c .mappingproxy =>
    -- `mappingproxy_hash`, `Objects/descrobject.c:1204`.
    let m ← proxyMapping v
    rt.hash m
  | .c .str => pure (strHash ((strOf w v).getD ""))
  | .c .float =>
    -- `float_hash`, `Objects/floatobject.c:532`: a NaN hashes by address.
    match floatOf w v with
    | some x =>
      match Binary64.float_hash x with
      | some h => pure h
      | none => pure (match v with
        | .obj a => (a : Int)
        | _ => 0)
    | none => gap%
  | .c .tuple =>
    -- `tuple_hash`, `Objects/tupleobject.c:372`. C keeps the result in `ob_hash`, so a second
    -- hash of one tuple does not call the items again; a tuple value here has no such place.
    tupleHash rt ((tupleOf w v).getD [])
  | _ => gap%

/-- `PyObject_Hash`, `Objects/object.c:1159`. -/
def pyHash (rt : Rt) (v : Val) : M Int := do
  let w ← getW
  match slotOf w (typeOf w v) .tp_hash with
  | some f => callHash rt f v
  | none => hashNotImplemented v

/-- `slot_tp_repr`, `Objects/typeobject.c:10988`. The address is rendered as `0x0`:
addresses are not part of the model. -/
def slotTpRepr (rt : Rt) (self : Val) : M Val := do
  match ← maybeCallSpecial rt self "__repr__" [] false with
  | .res r => pure r
  | _ =>
    let w ← getW
    pure (.str s!"<{typeName w self} object at 0x0>")

/-- `object_repr`, `Objects/typeobject.c:7538`. -/
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

/-- `type_repr`, `Objects/typeobject.c:2434`. -/
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

/-- Remove the first entry that is `v`: the search of `Py_ReprLeave`, `Objects/object.c:3158`. -/
def reprStackErase (v : Val) : List Val → List Val
  | [] => []
  | x :: xs => if x.is v then xs else x :: reprStackErase v xs

/-- `Py_ReprEnter`, `Objects/object.c:3108`, and `Py_ReprLeave`, `:3142`, around `body`: an
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

/-- The loop of `list_repr_impl`, `Objects/listobject.c:623`: `repr` may mutate the list, so the
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

/-- The loop of `anydict_repr_impl`, `Objects/dictobject.c:3642`: `repr(key)`, then
`repr(value)`, pair by pair, with the dict read again each time. A deletion during the loop is
not exact: `_PyDict_Next` walks a table with dummy entries, and the model has a list. -/
def dictReprLoop (rt : Rt) (v : Val) : Nat → Nat → List String → M (List String)
  | 0, _, _ => raise .fuel
  | fuel + 1, i, acc => do
    let w ← getW
    match ((anyDictOf w v).getD [])[i]? with
    | none => pure acc.reverse
    | some (k, x) =>
      let kr ← rt.repr k
      let vr ← rt.repr x
      dictReprLoop rt v fuel (i + 1) ((kr ++ ": " ++ vr) :: acc)

/-- The calling convention of a builtin: `METH_NOARGS`, `METH_O`, `METH_FASTCALL` without
keywords, or keywords accepted. -/
inductive MethConv where
  | noargs | o | fast | keywords

/-- `ml_name` and `ml_flags` of a `Builtin`. -/
def builtinConv : Builtin → String × MethConv
  | .objectInitSubclass => ("__init_subclass__", .noargs)
  | .objectSubclasshook => ("__subclasshook__", .o)
  | .objectFormat => ("__format__", .o)
  | .strDunderFormat => ("__format__", .o)
  | .numDunderFormat => ("__format__", .o)
  | .objectDir => ("__dir__", .noargs)
  | .objectSizeof => ("__sizeof__", .noargs)
  | .objectGetstate => ("__getstate__", .noargs)
  | .objectReduce => ("__reduce__", .noargs)
  | .objectReduceEx => ("__reduce_ex__", .o)
  | .classGetitem => ("__class_getitem__", .o)
  | .typeMro => ("mro", .noargs)
  | .typeSubclasses => ("__subclasses__", .noargs)
  | .typeInstancecheck => ("__instancecheck__", .o)
  | .typeSubclasscheck => ("__subclasscheck__", .o)
  | .typeDir => ("__dir__", .noargs)
  | .typeSizeof => ("__sizeof__", .noargs)
  | .isinstance => ("isinstance", .fast)
  | .issubclass => ("issubclass", .fast)
  | .getattr => ("getattr", .fast)
  | .setattr => ("setattr", .fast)
  | .delattr => ("delattr", .fast)
  | .hasattr => ("hasattr", .fast)
  | .len => ("len", .o)
  | .iter => ("iter", .fast)
  | .next => ("next", .fast)
  | .repr => ("repr", .o)
  | .hash => ("hash", .o)
  | .callable => ("callable", .o)
  | .dir => ("dir", .fast)
  | .abs => ("abs", .o)
  | .divmod => ("divmod", .fast)
  | .format => ("format", .fast)
  | .propertyGetter => ("getter", .o)
  | .propertySetter => ("setter", .o)
  | .propertyDeleter => ("deleter", .o)
  | .listAppend => ("append", .o)
  | .dunderGetitem => ("__getitem__", .o)
  | .dunderContains => ("__contains__", .o)
  | .dictKeysMethod => ("keys", .noargs)
  | .floatMethod "__round__" => ("__round__", .fast)
  | .floatMethod "fromhex" => ("fromhex", .o)
  | .floatMethod n => (n, .noargs)
  | .proxyCall "get" => ("get", .fast)
  | .proxyCall n => (n, .noargs)
  | .getnewargs => ("__getnewargs__", .noargs)
  | .reduceName _ | .reduceBound | .reduceCFunction | .reduceWrapper | .reduceDescr =>
    ("__reduce__", .noargs)
  | .iterLengthHint => ("__length_hint__", .noargs)
  | _ => ("", .keywords)

/-- `ml_name` of a builtin, when the model knows it. -/
def builtinName (b : Builtin) : Option String :=
  match b with
  | .stub n | .excMethod n => (n.splitOn ".").getLast?
  | _ =>
    let n := (builtinConv b).1
    if n == "" then none else some n

/-- `descr_repr`, `Objects/descrobject.c:42`. A descriptor of `object` names no owner. -/
def descrRepr (w : World) (kind : String) (o : Addr) (n : Name) : String :=
  if o == B.object then s!"<{kind} '{n}'>"
  else s!"<{kind} '{n}' of '{tpName w o}' objects>"

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
    | _ => gap%
  | .c .tuple =>
    -- `tuple_repr`, `Objects/tupleobject.c:286`: the empty check comes before the guard.
    let xs := (tupleOf w v).getD []
    if xs.isEmpty then pure (.str "()") else
    withRepr v "(...)" do
      let rs ← reprList rt xs
      match rs with
      | [r] => pure (.str s!"({r},)")
      | _ => pure (.str ("(" ++ ", ".intercalate rs ++ ")"))
  | .c .list =>
    -- `list_repr_impl`, `Objects/listobject.c:602`.
    withRepr v "[...]" do
      let rs ← listReprLoop rt v iterFuel 0 []
      pure (.str ("[" ++ ", ".intercalate rs ++ "]"))
  | .c .dict =>
    -- `anydict_repr_impl`, `Objects/dictobject.c:3642`: the guard comes before the empty check.
    withRepr v "{...}" do
      let rs ← dictReprLoop rt v iterFuel 0 []
      pure (.str ("{" ++ ", ".intercalate rs ++ "}"))
  | .c .float =>
    match floatOf w v with
    | some x => .str <$> floatReprStr x
    | none => gap%
  | .c .wrapperDescr =>
    match payloadOf w v with
    | some (.wrapperDescr o p _) => pure (.str (descrRepr w "slot wrapper" o p.name))
    | _ => gap%
  | .c .methodDescr | .c .classmethodDescr =>
    match payloadOf w v with
    | some (.methodDescr o n _) | some (.classmethodDescr o n _) =>
      pure (.str (descrRepr w "method" o n))
    | _ => gap%
  | .c .memberDescr =>
    match payloadOf w v with
    | some (.memberDescr o n _) => pure (.str (descrRepr w "member" o n))
    | _ => gap%
  | .c .getsetDescr =>
    match payloadOf w v with
    | some (.getsetDescr o n _) => pure (.str (descrRepr w "attribute" o n))
    | _ => gap%
  | .c .function =>
    -- `func_repr`, `Objects/funcobject.c:1237`.
    match payloadOf w v with
    | some (.func fd) => pure (.str s!"<function {fd.qualname} at 0x0>")
    | _ => gap%
  | .c .method =>
    -- `method_repr`, `Objects/classobject.c:253`: `__qualname__`, then `__name__`, and `?`
    -- when neither is a str. Either lookup can raise.
    match payloadOf w v with
    | some (.bound func self) =>
      let q ← rt.getOptionalAttr func "__qualname__"
      let n ← match q with
        | some _ => pure q
        | none => rt.getOptionalAttr func "__name__"
      let w ← getW
      let text := match n with
        | some x => (strOf w x).getD "?"
        | none => "?"
      let r ← rt.repr self
      pure (.str s!"<bound method {text} of {r}>")
    | _ => gap%
  | .c .builtinFn =>
    -- `meth_repr`, `Objects/methodobject.c:303`.
    match payloadOf w v with
    | some (.builtin b self) =>
      match builtinName b, self with
      | some n, none => pure (.str s!"<built-in function {n}>")
      | some n, some s =>
        pure (.str s!"<built-in method {n} of {typeName w s} object at 0x0>")
      | none, _ => gap%
    | _ => gap%
  | .c .methodWrapper =>
    -- `wrapper_repr`, `Objects/descrobject.c:1383`.
    match payloadOf w v with
    | some (.methodWrapper d s) =>
      match payloadOf w d with
      | some (.wrapperDescr _ p _) =>
        pure (.str s!"<method-wrapper '{p.name}' of {typeName w s} object at 0x0>")
      | _ => gap%
    | _ => gap%
  | .c .classmethod =>
    -- `cm_repr`, `Objects/funcobject.c:1655`.
    match payloadOf w v with
    | some (.classmethod f) => pure (.str s!"<classmethod({← rt.repr f})>")
    | _ => gap%
  | .c .staticmethod =>
    -- `sm_repr`, `Objects/funcobject.c:1923`.
    match payloadOf w v with
    | some (.staticmethod f) => pure (.str s!"<staticmethod({← rt.repr f})>")
    | _ => gap%
  | .c .super =>
    -- `super_repr`, `Objects/typeobject.c:12673`, which tolerates a NULL type.
    match payloadOf w v with
    | some (.super ty _ ot) =>
      let t := match ty with
        | some a => tpName w a
        | none => "NULL"
      match ot with
      | some o => pure (.str s!"<super: <class '{t}'>, <{tpName w o} object>>")
      | none => pure (.str s!"<super: <class '{t}'>, NULL>")
    | _ => gap%
  | .c .mappingproxy =>
    -- `mappingproxy_repr`, `Objects/descrobject.c:1218`.
    let m ← proxyMapping v
    pure (.str s!"mappingproxy({← rt.repr m})")
  | .c .frozendict =>
    -- `frozendict_repr`, `Objects/dictobject.c:8342`, with `anydict_repr_impl`, `:3642`.
    if ((anyDictOf w v).getD []).isEmpty then pure (.str s!"{tpName w (typeOf w v)}()")
    else
      let r ← withRepr v "{...}" do
        let rs ← dictReprLoop rt v iterFuel 0 []
        pure (.str ("{" ++ ", ".intercalate rs ++ "}"))
      match r with
      | .str s => pure (.str s!"{tpName w (typeOf w v)}({s})")
      | _ => gap%
  | .c .dictKeys =>
    -- `dictview_repr`, `Objects/dictobject.c`: the guard, then the keys as a list.
    withRepr v "..." do
      match payloadOf w v with
      | some (.seqIter (some d) _) =>
        let l ← alloc B.list (.list ((dictOf w d).getD [] |>.map (·.1)))
        pure (.str s!"dict_keys({← rt.repr l})")
      | _ => gap%
  | .c e => if isExcFamily e then excCallRepr rt e v else gap%
  | _ => gap%

/-- `PyObject_Repr`, `Objects/object.c:760`. -/
def pyRepr (rt : Rt) (v : Val) : M String := do
  let w ← getW
  let res ← match slotOf w (typeOf w v) .tp_repr with
    | some f => callRepr rt f v
    | none => pure (.str s!"<{typeName w v} object at 0x0>")
  let w ← getW
  match strOf w res with
  | some s => pure s
  | none => typeErr s!"{objFQN w v}.__repr__() must return a str, not {objFQN w res}"

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
    | .mappingproxy =>
      -- `mappingproxy_str`, `Objects/descrobject.c:1211`.
      let m ← proxyMapping v
      pure (.str (← rt.str m))
    | _ => gap%
  | _ => gap%

/-- `PyObject_Str`, `Objects/object.c:801`. -/
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
      | none => typeErr s!"{objFQN w v}.__str__() must return a str, not {objFQN w res}"

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
  | .c .float, .nb_negative =>
    match floatOf w v with
    | some x => mkFloat x.neg
    | none => gap%
  | .c .float, .nb_absolute =>
    match floatOf w v with
    | some x => mkFloat x.abs
    | none => gap%
  | .c .float, .nb_positive | .c .float, .nb_float =>
    -- `float_float`, `Objects/floatobject.c`: an exact float is returned as it is.
    match floatOf w v with
    | some x => if typeOf w v == B.float then pure v else mkFloat x
    | none => gap%
  | .c .float, .nb_int =>
    match floatOf w v with
    | some x => .int <$> pyToM (Binary64.float_trunc x)
    | none => gap%
  | .c .int, .nb_float | .c .bool, .nb_float =>
    -- `long_float`, `Objects/longobject.c`.
    let x ← pyToM (Binary64.PyLong_AsDouble ((intOf w v).getD 0))
    mkFloat x
  | _, _ => gap%

/-- `_PyNumber_Index`, `Objects/abstract.c:1410`. The `DeprecationWarning` for a strict
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
      | none => gap%
      | some f =>
        let result ← callUnaryNb rt .nb_index "__index__" f item
        let w ← getW
        match intOf w result with
        | some _ => pure result
        | none => typeErr s!"{objFQN w item}.__index__() must return an int, not {objFQN w result}"

/-- `PyNumber_Index`, `Objects/abstract.c:1456`: an exact `int`. -/
def pyNumberIndex (rt : Rt) (item : Val) : M Int := do
  let v ← numberIndex rt item
  let w ← getW
  pure ((intOf w v).getD 0)

/-- `PyNumber_AsSsize_t`, `Objects/abstract.c:1468`. `err = none` clips to the
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

/-- `slot_sq_length`, `Objects/typeobject.c:10720-10745`. -/
def slotSqLength (rt : Rt) (self : Val) : M Int := do
  let res ← vectorcallMethod rt "__len__" [self]
  -- `Py_SETREF(res, _PyNumber_Index(res))`, `:10729`: an `int` subclass result is kept as is.
  let v ← numberIndex rt res
  let w ← getW
  let idx := (intOf w v).getD 0
  if idx < 0 then valueErr "__len__() should return >= 0"
  else numberAsSsize rt v (some B.OverflowError)

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
    -- `mappingproxy_len`, `Objects/descrobject.c:1045`.
    let m ← proxyMapping v
    rt.size m
  | .c .dictKeys =>
    -- `dictview_len`, `Objects/dictobject.c`.
    match payloadOf w v with
    | some (.seqIter (some d) _) => pure (((dictOf w d).getD []).length : Nat)
    | _ => gap%
  | _ => gap%

/-- The filled slot `s` of the type of `v`, honouring NULL `tp_as_*` structs. -/
def slotIn (w : World) (v : Val) (s : Slot) : Option SlotFn :=
  if hasGroup w (typeOf w v) s.group then slotOf w (typeOf w v) s else none

/-- `PyMapping_Size`, `Objects/abstract.c:2276`. -/
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

/-- `PySequence_Size`, `Objects/abstract.c:1690`. -/
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
          typeErr s!"{objFQN w o}.__length_hint__() must return an int, not {objFQN w result}"
        | some i =>
          if !inSsize i then overflowErr "Python int too large to convert to C ssize_t"
          else if i < 0 then valueErr s!"{objFQN w o}.__length_hint__() must return a non-negative int"
          else pure i

/-- `slot_nb_bool`, `Objects/typeobject.c:10904`. -/
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
    | _ => typeErr s!"{objFQN w self}.__bool__() must return a bool, not {objFQN w value}"

/-- `PyObject_IsTrue`, `Objects/object.c:2139`. -/
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
      | .c .float =>
        match floatOf w v with
        | some x => pure (Binary64.float_bool x)
        | none => gap%
      | .c .notImpl => typeErr "NotImplemented should not be used in a boolean context"
      | .c .none => pure false
      | _ => gap%
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

/-- `method_is_overloaded`, `Objects/typeobject.c:10643`. -/
def methodIsOverloaded (rt : Rt) (left right : Val) (n : Name) : M Bool := do
  let w ← getW
  match ← rt.getOptionalAttr (.obj (typeOf w right)) n with
  | none => pure false
  | some b =>
    let w ← getW
    match ← rt.getOptionalAttr (.obj (typeOf w left)) n with
    | none => pure true
    | some a => richCompareBool rt a b .ne

/-- `SLOT1BINFULL`, `Objects/typeobject.c:10673`, for slot `s` with `extra` trailing
arguments (`slot_nb_power` with a modulus copies this macro, `:10851`). -/
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
def dictHashKey (rt : Rt) (key : Val) : M Int := do
  tryM (rt.hash key) fun e => do
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

/-- `_PyErr_FormatNote`, `Python/errors.c:1271`: `_PyException_AddNote` on the raised exception,
which is raised again. If adding the note fails, that error is what propagates; C chains the first
exception to it (`:1292`), which the model does not. -/
def raiseWithNote {α : Type} (rt : Rt) (e : PyErr) (note : String) : M α := do
  let x ← excObject e
  pyExceptionAddNote rt x (.str note)
  raise (match e with
    | .exc c m _ => .exc c m (some x)
    | e => e)

/-- `insertdict`, `Objects/dictobject.c:2001`, with a known hash: an existing entry keeps its key
and takes the value; otherwise the pair goes at the end with its hash recorded. -/
def dictInsert (rt : Rt) (addr : Addr) (k : Val) (h : Int) (v : Val) : M Unit := do
  match ← dictProbe rt addr k h iterFuel 0 with
  | some i =>
    modObj addr fun o =>
      match o.body with
      | .dict es => { o with body := .dict (es.modify i fun e => (e.1, v)) }
      | body => { o with body := body }
  | none =>
    modObj addr fun o =>
      match o.body with
      | .dict es =>
        { o with body := .dict (es ++ [(k, v)]), keyHashes := (k, h) :: o.keyHashes }
      | body => { o with body := body }

/-- `setitem_lock_held` on the dict at `addr`: hash the key, then `insertdict`. -/
def dictSetAt (rt : Rt) (addr : Addr) (k v : Val) : M Unit := do
  let h ← dictHashKey rt k
  dictInsert rt addr k h v

/-- The loop of `dict_dict_merge`, `Objects/dictobject.c:4223`: `_PyDict_Next` over `other`, each
pair through `insertdict` with its stored hash, which can run `__eq__`, and that can change
`other`. -/
def dictDictMergeLoop (rt : Rt) (addr other : Addr) (orig : Nat) : Nat → Nat → M Unit
  | 0, _ => raise .fuel
  | fuel + 1, i => do
    let w ← getW
    match (dictEntries w other)[i]? with
    | none => pure ()
    | some (k, v) =>
      dictInsert rt addr k (storedHash w other k) v
      let w ← getW
      if (dictEntries w other).length != orig then runtimeErr "dict mutated during update"
      dictDictMergeLoop rt addr other orig fuel (i + 1)

/-- `dict_dict_merge`, `Objects/dictobject.c:4170`. An empty target takes a clone of the table,
which C does only for a clean `other` (`:4187`); the model has no table to test that on, and the
difference shows only for keys of equal hash. -/
def dictDictMerge (rt : Rt) (addr other : Addr) : M Unit := do
  let w ← getW
  let es := dictEntries w other
  if other == addr || es.isEmpty then pure ()
  else if (dictEntries w addr).isEmpty then
    let hashes := (w.objAt other).keyHashes
    modObj addr fun o => { o with body := .dict es, keyHashes := hashes }
  else dictDictMergeLoop rt addr other es.length iterFuel 0

/-- `PySequence_Fast(v, "object is not iterable")`, `Objects/abstract.c`: an exact list or tuple
is used as it is, and only a `TypeError` from `PyObject_GetIter` is replaced. -/
def seqFastItems (rt : Rt) (v : Val) : M (List Val) := do
  let w ← getW
  match v with
  | .tuple xs => pure xs
  | _ =>
    if typeOf w v == B.list then pure ((listOf w v).getD []) else
    let it ← tryM (rt.getIter v) fun e => do
      let w ← getW
      if excMatches w e B.TypeError then typeErr "object is not iterable" else raise e
    rt.listItems it

/-- The loop of `PyDict_MergeFromSeq2`, `Objects/dictobject.c:4068-4126`: each pair is stored as
it arrives, so the pairs before a failure stay in the dict. -/
def mergeSeq2Loop (rt : Rt) (addr : Addr) (it : Val) : Nat → Nat → M Unit
  | 0, _ => raise .fuel
  | fuel + 1, i => do
    match ← rt.iterNext it with
    | none => pure ()
    | some item =>
      let items ← tryM (seqFastItems rt item) fun e => do
        let w ← getW
        if excMatches w e B.TypeError then
          raiseWithNote rt e s!"Cannot convert dictionary update sequence element #{i} to a sequence"
        else raise e
      match items with
      | [k, v] =>
        dictSetAt rt addr k v
        mergeSeq2Loop rt addr it fuel (i + 1)
      | _ =>
        valueErr s!"dictionary update sequence element #{i} has length {items.length}; 2 is required"

/-- The generic loop of `dict_merge`, `Objects/dictobject.c:4305-4341`: `b[key]`, then the store,
key by key. -/
def dictMergeLoop (rt : Rt) (addr : Addr) (b it : Val) : Nat → M Unit
  | 0 => raise .fuel
  | fuel + 1 => do
    match ← rt.iterNext it with
    | none => pure ()
    | some k =>
      let v ← rt.getItem b k
      dictSetAt rt addr k v
      dictMergeLoop rt addr b it fuel

/-- `dict_merge`, `Objects/dictobject.c:4259`, with `override` 1. -/
def dictMerge (rt : Rt) (addr : Addr) (x : Val) : M Unit := do
  let w ← getW
  match x, dictOf w x, slotOf w (typeOf w x) .tp_iter == some (.c .dict) with
  | .obj other, some _, true => dictDictMerge rt addr other
  | _, _, _ =>
    -- `PyMapping_Keys`, then `method_output_as_list`, `Objects/abstract.c:2433`: an exact
    -- list is returned as it is, so the loop below sees later changes to it.
    let f ← rt.getAttr x "keys"
    let out ← rt.call f [] []
    let w ← getW
    let keys ← if typeOf w out == B.list then pure out else do
      let it ← tryM (rt.getIter out) fun e => do
        let w ← getW
        if excMatches w e B.TypeError then
          typeErr s!"{objFQN w x}.keys() must return an iterable, not {objFQN w out}"
        else raise e
      let xs ← rt.listItems it
      alloc B.list (.list xs)
    let it ← rt.getIter keys
    dictMergeLoop rt addr x it iterFuel

/-- `dict_update_arg`, `Objects/dictobject.c:3992`, into the dict at `addr`, which `dict_or`,
`dict_ior` and `dict_update_common` each supply. -/
def dictUpdateArg (rt : Rt) (addr : Addr) (x : Val) : M Unit := do
  let w ← getW
  if typeOf w x == B.dict then dictMerge rt addr x
  else
    match ← rt.getOptionalAttr x "keys" with
    | some _ => dictMerge rt addr x
    | none =>
      let it ← rt.getIter x
      mergeSeq2Loop rt addr it iterFuel 0

/-- `PyDict_Copy`, `Objects/dictobject.c:4549`, with `copy_lock_held_untracked`, `:4433`: an empty
dict copies to a new one and runs nothing, whatever its type overrides. Otherwise a fresh dict is
filled by `dict_merge`, which sees an overridden `tp_iter`. -/
def dictCopy (rt : Rt) (x : Val) : M Addr := do
  let w ← getW
  let d ← allocCell (.val { cls := B.dict, body := .dict [] })
  if ((anyDictOf w x).getD []).isEmpty then return d
  dictMerge rt d x
  pure d

/-- `long_add`, `long_sub`, ... on values that passed `CHECK_BINOP`. -/
def longBinary (s : Slot) (a b : Int) : M Val :=
  match s with
  | .nb_add => pure (.int (a + b))
  | .nb_subtract => pure (.int (a - b))
  | .nb_multiply => pure (.int (a * b))
  | .nb_floor_divide =>
    if b == 0 then raiseC B.ZeroDivisionError "division by zero"
    else pure (.int (Int.fdiv a b))
  | .nb_true_divide => longTrueDivide a b
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
    else if b > 100000 then gap%
    else pure (.int (a * 2 ^ b.toNat))
  | .nb_rshift =>
    if b < 0 then valueErr "negative shift count"
    else if b > 100000 then pure (.int (if a < 0 then -1 else 0))
    else pure (.int (Int.fdiv a (2 ^ b.toNat)))
  | _ => gap%

/-- Call a binary number slot function `f`. -/
def callNbBinary (rt : Rt) (s : Slot) (f : SlotFn) (a b : Val) : M Val := do
  let w ← getW
  match f with
  | .c .float => floatBinary s a b
  | .generic =>
    let op := nbOpOfSlot s
    slot1Bin rt s op.dunder op.rdunder a b []
  | .c .mappingproxy =>
    -- `mappingproxy_or`, `Objects/descrobject.c:1065`: both sides are unwrapped.
    let unwrap (x : Val) : M Val := do
      if isSubtype w (typeOf w x) B.mappingproxy then proxyMapping x else pure x
    let l ← unwrap a
    let r ← unwrap b
    rt.numberOr l r
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
      | _ => gap%
    | _, _ =>
      match intOf w a, intOf w b with
      | some x, some y => longBinary s x y
      | _, _ => pure .notImpl
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
      if fmt.contains '%' then gap%
      else if (slotIn w b .mp_subscript).isSome && (tupleOf w b).isNone && (strOf w b).isNone then
        pure (.str fmt)
      else
        -- `Objects/unicode_format.c:1094`: `arglen` is `-1` when `b` is not a tuple.
        match tupleOf w b with
        | some [] => pure (.str fmt)
        | some xs =>
          typeErr s!"not all arguments converted during string formatting (required 0, got {xs.length})"
        | none => typeErr "not all arguments converted during string formatting (required 0, got 1)"
  | .c .dict =>
    -- `dict_or`, `Objects/dictobject.c`, through `dict_update_arg`: a non-exact dict is first
    -- asked for `keys`, then merged directly if it has `dict_iter`.
    match dictOf w a, dictOf w b with
    | some _, some _ =>
      -- A failed update drops the copy, so its partial state cannot be seen.
      let addr ← dictCopy rt a
      dictUpdateArg rt addr b
      pure (.obj addr)
    | _, _ => pure .notImpl
  | _ => gap%

/-- `binary_op1`, `Objects/abstract.c:940`. -/
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

/-- `binop_type_error`, `Objects/abstract.c:999`. -/
def binopTypeError {α : Type} (v w' : Val) (name : String) : M α := do
  let w ← getW
  typeErr s!"unsupported operand type(s) for {trunc 100 name}: '{trunc 100 (typeName w v)}' and '{trunc 100 (typeName w w')}'"

/-- `binary_op`, `Objects/abstract.c:1011`. -/
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
    gap%

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
  if size != 0 && k * size > 1000000 then gap% else
  let k := if size == 0 then 0 else k
  match f with
  | .c .str => pure (.str (strRepeat ((strOf w a).getD "") k))
  | .c .tuple => pure (.tuple (listRepeat ((tupleOf w a).getD []) k))
  | .c .list => alloc B.list (.list (listRepeat ((listOf w a).getD []) k))
  | _ => gap%

/-- Append `items` to the list at `addr`. -/
def listAppendAll (addr : Addr) (items : List Val) : M Unit :=
  modObj addr fun o =>
    match o.body with
    | .list xs => { o with body := .list (xs ++ items) }
    | body => { o with body := body }

/-- The reservation of `list_extend_iter_lock_held`, `Objects/listobject.c:1317-1335`. When
`m + n` overflows the hint is ignored (:1317), so the loop still runs. Otherwise
`list_preallocate_exact` or `list_resize` fails on a size no allocator can serve. -/
def listReserve (m n : Int) : M Unit :=
  if m > PyLean.ssizeMax - n then pure ()
  else if m + n ≥ 2 ^ 48 then raiseC B.MemoryError ""
  else pure ()

/-- The loop of `list_extend_iter_lock_held`, `Objects/listobject.c:1338-1359`: each item goes
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

/-- `list_extend_iter_lock_held`, `Objects/listobject.c:1301`. -/
def listExtendIter (rt : Rt) (addr : Addr) (b : Val) : M Unit := do
  let it ← rt.getIter b
  let n ← pyLengthHint rt b 8
  let w ← getW
  listReserve ((listOf w (.obj addr)).getD []).length n
  listExtendLoop rt addr it iterFuel

/-- The keys of a dict, in order. -/
def dictKeyList (w : World) (d : Val) : List Val := ((dictOf w d).getD []).map (·.1)

/-- `_list_extend`, `Objects/listobject.c:1478`, in the order of its branches. Extending a list
with itself is `list_inplace_repeat(self, 2)` (:1483) and runs no Python code; exact lists,
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
        | _ => gap%
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

/-- `sequence_repeat`, `Objects/abstract.c:1157`. -/
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

/-- `PyNumber_Add`, `Objects/abstract.c:1138`. -/
def pyNumberAdd (rt : Rt) (v w' : Val) : M Val := do
  match ← binaryOp1 rt v w' .nb_add with
  | .notImpl =>
    let w ← getW
    match slotIn w v .sq_concat with
    | some f => callSqConcat rt f v w'
    | none => binopTypeError v w' "+"
  | r => pure r

/-- `PyNumber_Multiply`, `Objects/abstract.c:1176`. -/
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

/-- `binary_iop1`, `Objects/abstract.c:1228`. -/
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
  /-- `SLOT1(slot_nb_inplace_*, __i*__)`, `Objects/typeobject.c:10964`. -/
  callInplace (rt : Rt) (f : SlotFn) (idunder : Name) (a b : Val) : M Val := do
    match f, a with
    | .generic, _ => vectorcallMethod rt idunder [a, b]
    | .c .dict, .obj addr =>
      -- `_PyDict_IOr`, `Objects/dictobject.c:5192`.
      dictUpdateArg rt addr b
      pure a
    | .c .mappingproxy, _ =>
      -- `mappingproxy_ior`, `Objects/descrobject.c:1077`.
      let w ← getW
      typeErr s!"'|=' is not supported by {typeName w a}; use '|' instead"
    | .c .list, .obj _ =>
      -- `update_one_slot` puts `list_inplace_concat` in `nb_inplace_add` of a list subclass:
      -- `__iadd__` has the same wrapper for `nb_inplace_add` and `sq_inplace_concat`.
      if idunder == "__iadd__" then callSqInplaceConcat rt f a b else gap%
    | _, _ => gap%

/-- `binary_iop`, `Objects/abstract.c:1260`. -/
def binaryIop (rt : Rt) (v w' : Val) (islot s : Slot) (name : String) : M Val := do
  match ← binaryIop1 rt v w' islot s with
  | .notImpl => binopTypeError v w' name
  | r => pure r

/-- `PyNumber_InPlaceAdd`, `Objects/abstract.c:1307`. -/
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

/-- `PyNumber_InPlaceMultiply`, `Objects/abstract.c:1330`. Note the `else if` at `:1346`:
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

/-- `slot_nb_power`, `Objects/typeobject.c:10851`. -/
def slotNbPower (rt : Rt) (self other modulus : Val) : M Val :=
  match modulus with
  | .none => slot1Bin rt .nb_power "__pow__" "__rpow__" self other []
  | m => slot1Bin rt .nb_power "__pow__" "__rpow__" self other [m]

/-- `long_pow` for the cases with an exact result: non-negative exponent, no modulus. -/
def longPow (w : World) (a b z : Val) : M Val :=
  match intOf w a, intOf w b, z with
  | some x, some y, .none =>
    -- `long_pow` hands negative exponents to `float_pow`.
    if y < 0 then floatPow a b .none
    else if y > 10000 then gap% else pure (.int (x ^ y.toNat))
  | some x, some y, z' =>
    match intOf w z' with
    | none => pure .notImpl
    | some m =>
      if m == 0 then valueErr "pow() 3rd argument cannot be 0"
      else if y < 0 || y > 10000 then gap%
      else pure (.int (Int.fmod (x ^ y.toNat) m))
  | _, _, _ => pure .notImpl

/-- Call `nb_power`. -/
def callNbPower (rt : Rt) (f : SlotFn) (a b c : Val) : M Val := do
  let w ← getW
  match f with
  | .generic => slotNbPower rt a b c
  | .c .int => longPow w a b c
  | .c .float => floatPow a b c
  | _ => gap%

/-- `ternary_op`, `Objects/abstract.c:1030`. -/
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

/-- `PyNumber_Power`, `Objects/abstract.c:1200`. -/
def pyNumberPower (rt : Rt) (v w' z : Val) : M Val := ternaryOp rt v w' z "** or pow()"

/-- `ternary_iop`, `Objects/abstract.c:1272`. `slot_nb_inplace_power` drops the third
argument (`Objects/typeobject.c:10971`). -/
def ternaryIop (rt : Rt) (v w' z : Val) : M Val := do
  let w ← getW
  let x ← match slotIn w v .nb_inplace_power with
    | some .generic => vectorcallMethod rt "__ipow__" [v, w']
    | some _ => gap%
    | none => pure Val.notImpl
  match x with
  | .notImpl => ternaryOp rt v w' z "**="
  | x => pure x

/-- `UNARY_FUNC`, `Objects/abstract.c:1374`. -/
def unaryFunc (rt : Rt) (s : Slot) (dunder descr : String) (o : Val) : M Val := do
  let w ← getW
  match slotIn w o s with
  | some f => callUnaryNb rt s dunder f o
  | none => typeErr s!"bad operand type for {descr}: '{trunc 200 (typeName w o)}'"

def pyNumberNegative (rt : Rt) := unaryFunc rt .nb_negative "__neg__" "unary -"
def pyNumberPositive (rt : Rt) := unaryFunc rt .nb_positive "__pos__" "unary +"
def pyNumberInvert (rt : Rt) := unaryFunc rt .nb_invert "__invert__" "unary ~"
def pyNumberAbsolute (rt : Rt) := unaryFunc rt .nb_absolute "__abs__" "abs()"

/-- `PyNumber_Check`, `Objects/abstract.c:913` (no `complex` in this model). -/
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

/-- `PyNumber_Long`, `Objects/abstract.c:1519`, up to the string-parsing fallbacks. -/
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
        | none => typeErr s!"{objFQN w o}.__int__() must return an int, not {objFQN w result}"
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

/-- `PyFloat_FromString`, `Objects/floatobject.c:179`, for a str. Bytes and other buffers are not
in the object model, and any other object is the exact `TypeError`. -/
def floatFromString (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  match strOf w o with
  | some s =>
    match Binary64.PyFloat_FromString (.str (s.toList.map (·.toNat))) with
    | .ok x => mkFloat x
    -- `could not convert string to float: %R`, so a subclass's `__repr__` runs.
    | .error (.valueError _) =>
      valueErr s!"could not convert string to float: {← rt.repr o}"
    | .error e => pyToM (.error e)
  | none =>
    typeErr s!"float() argument must be a string or a real number, not '{trunc 200 (typeName w o)}'"

/-- `PyNumber_Float`, `Objects/abstract.c:1602`. `__float__` may return a subclass of `float`,
which gives a plain copy. -/
def pyNumberFloat (rt : Rt) (o : Val) : M Val := do
  let w ← getW
  if typeOf w o == B.float then pure o
  else
    match slotIn w o .nb_float with
    | some f =>
      let res ← callUnaryNb rt .nb_float "__float__" f o
      let w ← getW
      if typeOf w res == B.float then pure res
      else
        match floatOf w res with
        | some x => mkFloat x
        | none =>
          typeErr s!"{objFQN w o}.__float__() must return a float, not {objFQN w res}"
    | none =>
      match slotIn w o .nb_index with
      | some _ =>
        let r ← numberIndex rt o
        let w ← getW
        let x ← pyToM (Binary64.PyLong_AsDouble ((intOf w r).getD 0))
        mkFloat x
      | none =>
        match floatOf w o with
        | some x => mkFloat x
        | none => floatFromString rt o

/-- `slot_sq_contains`, `sq_item`, ... use these. `PySequence_Check`,
`Objects/abstract.c:1681`. -/
def pySequenceCheck (w : World) (s : Val) : Bool :=
  (dictOf w s).isNone && (slotIn w s .sq_item).isSome

/-- `PyMapping_Check`, `Objects/abstract.c:2269`. -/
def pyMappingCheck (w : World) (o : Val) : Bool := (slotIn w o .mp_subscript).isSome

/-- `slot_sq_item`, `Objects/typeobject.c:10748`, and `sq_item` of builtin sequences. -/
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
  | _ => gap%

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
    -- `_PyDict_Subscript`, `Objects/dictobject.c:3786`.
    let h ← dictHashKey rt key
    let found ← match o with
      | .obj a =>
        match ← dictProbe rt a key h iterFuel 0 with
        | some i =>
          let w ← getW
          pure (((dictEntries w a)[i]?).map (·.2))
        | none => pure none
      | _ => gap%
    match found with
    | some v => pure v
    | none =>
      let w ← getW
      let missing ← if typeOf w o == B.dict then pure none else lookupSpecial rt o "__missing__"
      match missing with
      | some m => rt.call m [key] []
      | none =>
        let x ← alloc B.KeyError (.exc { args := [key] })
        raise (.exc B.KeyError "" (some x))
  | .c .mappingproxy =>
    -- `mappingproxy_getitem`, `Objects/descrobject.c:1052`.
    let m ← proxyMapping o
    rt.getItem m key
  | _ => gap%

/-- `PySequence_GetItem`, `Objects/abstract.c:1841`. -/
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

/-- `PyObject_GetItem`, `Objects/abstract.c:155`. `type[int]` (generic aliases) is left
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
        if oa == B.type then alloc B.genericAlias .plain else
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
    -- `_PyDict_StoreSubscript`, `Objects/dictobject.c:3797`, then `insertdict` or `PyDict_DelItem`.
    let h ← dictHashKey rt key
    match o with
    | .obj a =>
      match value with
      | some v => dictInsert rt a key h v
      | none =>
        match ← dictProbe rt a key h iterFuel 0 with
        | some i =>
          modObj a fun ob =>
            match ob.body with
            | .dict es => { ob with body := .dict (es.eraseIdx i) }
            | body => { ob with body := body }
        | none =>
          let x ← alloc B.KeyError (.exc { args := [key] })
          raise (.exc B.KeyError "" (some x))
    | _ => gap%
  | .c .list =>
    let xs := (listOf w o).getD []
    if indexCheck w key then
      let i ← numberAsSsize rt key (some B.IndexError)
      let i := if i < 0 then i + xs.length else i
      if i < 0 || i ≥ xs.length then indexErr "list assignment index out of range" else
      match o, value with
      | .obj a, some v => modObj a fun ob => { ob with body := .list (xs.set i.toNat v) }
      | .obj a, none => modObj a fun ob => { ob with body := .list (xs.eraseIdx i.toNat) }
      | _, _ => gap%
    else typeErr s!"list indices must be integers or slices, not {trunc 200 (typeName w key)}"
  | _ => gap%

/-- `PySequence_SetItem`/`PySequence_DelItem`, `Objects/abstract.c:1893`, `:1926`. -/
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

/-- `PyObject_SetItem` and `PyObject_DelItem`, `Objects/abstract.c:236`, `:270`. -/
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

/-- `has_dunder_getitem`, `Objects/typeobject.c:11184-11194`: whether `lookup_maybe_method` found
`__getitem__`. An exception from the lookup (a raising `__get__`) is left set and the result is
`0`; its only caller, `slot_tp_iter`, then replaces it with its own `TypeError`
(`PyErr_Format` clears the pending error, `Python/errors.c:1226`), so here it is dropped. -/
def hasDunderGetitem (rt : Rt) (self : Val) : M Bool :=
  tryM (do
      match ← lookupMethodEx rt self "__getitem__" false with
      | .missing => pure false
      | _ => pure true)
    fun e => match e with
      | .exc _ _ _ => pure false
      | e => raise e

/-- `slot_tp_iter`, `Objects/typeobject.c:11197-11216`. `attr_is_none` is tested before
`has_dunder_getitem` (`:11208`), so `__iter__ = None` never looks up `__getitem__`. -/
def slotTpIter (rt : Rt) (self : Val) : M Val := do
  let m ← maybeCallSpecial rt self "__iter__" [] true
  match m with
  | .res r => pure r
  | m =>
    let attrIsNone := match m with
      | .isNone => true
      | _ => false
    let notIter : M Val := do
      let w ← getW
      typeErr s!"'{trunc 200 (typeName w self)}' object is not iterable"
    if attrIsNone then notIter
    else if !(← hasDunderGetitem rt self) then notIter
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
    -- `dictkeys_iter`, `Objects/dictobject.c:6592`: a key iterator over the view's dict.
    let w ← getW
    match o with
    | .obj a =>
      match w.get a with
      | .val { body := .seqIter (some d) _, .. } =>
        let keys ← alloc B.list (.list (((dictOf w d).getD []).map (·.1)))
        alloc B.dictKeyIter (.seqIter (some keys) 0)
      | _ => gap%
    | _ => gap%
  | .c .tuple => alloc B.tupleIter (.seqIter (some o) 0)
  | .c .str =>
    -- `unicode_iter`, `Objects/unicodeobject.c`: compact ASCII has an iterator of its own, and an
    -- instance of a subclass is not compact.
    let ascii := match o with
      | .str s => s.toList.all (·.toNat < 128)
      | _ => false
    alloc (if ascii then B.strIter else B.strIterU) (.seqIter (some o) 0)
  | .c .mappingproxy =>
    -- `mappingproxy_getiter`, `Objects/descrobject.c:1197`.
    let m ← proxyMapping o
    rt.getIter m
  | .c .seqIter | .c .listIter | .c .tupleIter | .c .strIter => pure o
  | _ => gap%

/-- `PyIter_Check`, `Objects/abstract.c:2856`. -/
def pyIterCheck (w : World) (o : Val) : Bool :=
  match slotOf w (typeOf w o) .tp_iternext with
  | none | some .nextNotImpl => false
  | some _ => true

/-- `PyObject_GetIter`, `Objects/abstract.c:2813`. -/
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
    else typeErr s!"{objFQN w o}.__iter__() must return an iterator, not {objFQN w res}"

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
  | _ => gap%

/-- `listiter_next`/`tupleiter_next`/`unicodeiter_next`: stop at the end of the sequence
and drop the reference, `Objects/listobject.c:4089`. -/
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
  | _ => gap%

/-- Call `tp_iternext`; `none` is NULL with no exception set. -/
def callIterNext (rt : Rt) (f : SlotFn) (it : Val) : M (Option Val) := do
  let w ← getW
  match f, it with
  | .generic, _ => some <$> vectorcallMethod rt "__next__" [it]
  | .nextNotImpl, _ => typeErr s!"'{trunc 200 (typeName w it)}' object is not iterable"
  | .c .seqIter, .obj a => seqIterNext rt a
  | .c .listIter, .obj a | .c .tupleIter, .obj a | .c .strIter, .obj a =>
    builtinIterNext rt f a
  | _, _ => gap%

/-- `iternext` and `PyIter_Next`, `Objects/abstract.c:2873`, `:2923`. -/
def pyIterNext (rt : Rt) (it : Val) : M (Option Val) := do
  let w ← getW
  match slotOf w (typeOf w it) .tp_iternext with
  | some f => catchMatch B.StopIteration (callIterNext rt f it) (pure none)
  | none => gap%

/-- `PySequence_List` by iteration; `fuel` bounds the loop. -/
def collectIter (rt : Rt) (it : Val) : Nat → M (List Val)
  | 0 => raise .fuel
  | fuel + 1 => do
    match ← rt.iterNext it with
    | none => pure []
    | some x =>
      let rest ← collectIter rt it fuel
      pure (x :: rest)

/-- `PySequence_Tuple`, `Objects/abstract.c:2005`, items only. The eight-item stack
buffer of `:2030` changes nothing visible. -/
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

/-- `PySequence_List`, `Objects/abstract.c:2081`, items only, through `list_extend`
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

/-- The loop of `_PySequence_IterSearch`, `Objects/abstract.c:2165-2212`. -/
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

/-- `_PySequence_IterSearch`, `Objects/abstract.c:2138`. -/
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

/-- `slot_sq_contains`, `Objects/typeobject.c:10791`. -/
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
    -- `PyDict_Contains`, `Objects/dictobject.c:5248`.
    let h ← dictHashKey rt ob
    match seq with
    | .obj a => pure (← dictProbe rt a ob h iterFuel 0).isSome
    | _ => gap%
  | .c .mappingproxy =>
    -- `mappingproxy_contains`, `Objects/descrobject.c:1089`: `PyDict_Contains` on an exact
    -- dict is the `sq_contains` of that dict.
    let m ← proxyMapping seq
    rt.contains m ob
  | .c .dictKeys =>
    -- `dictkeys_contains`, `Objects/dictobject.c`: the dict's own table, never an override.
    match payloadOf w seq with
    | some (.seqIter (some (.obj d)) _) =>
      let h ← dictHashKey rt ob
      pure (← dictProbe rt d ob h iterFuel 0).isSome
    | _ => gap%
  | .c .str =>
    match strOf w ob with
    | some t => pure (strContains ((strOf w seq).getD "").toList t.toList)
    | none =>
      -- `PyUnicode_Contains`, `Objects/unicodeobject.c:11305-11309`: `%.100s`.
      typeErr s!"'in <string>' requires string as left operand, not {trunc 100 (typeName w ob)}"
  | _ => gap%

/-- `PySequence_Contains`, `Objects/abstract.c:2240`. -/
def pySequenceContains (rt : Rt) (seq ob : Val) : M Bool := do
  let w ← getW
  match slotIn w seq .sq_contains with
  | some f => callContains rt f seq ob
  | none =>
    let r ← pySequenceIterSearch rt seq ob .contains
    pure (r != 0)

/-! ## `isinstance` and `issubclass` -/

/-- `abstract_get_bases`, `Objects/abstract.c:2522`. -/
def abstractGetBases (rt : Rt) (cls : Val) : M (Option (List Val)) := do
  match ← rt.getOptionalAttr cls "__bases__" with
  | none => pure none
  | some b =>
    let w ← getW
    pure (tupleOf w b)

mutual
  /-- `abstract_issubclass`, `Objects/abstract.c:2536`. `fuel` stands in for the
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
  /-- The `for` at `Objects/abstract.c:2575`. -/
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

/-- `check_class`, `Objects/abstract.c:2587`: `false` raises. -/
def checkClass (rt : Rt) (cls : Val) (error : String) : M Unit := do
  match ← abstractGetBases rt cls with
  | none => typeErr error
  | some _ => pure ()

/-- Recursion bound for class walks. A model limit: the interpreter would raise
`RecursionError` first. -/
def walkFuel : Nat := 2000

/-- `object_isinstance`, `Objects/abstract.c:2603`. -/
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

/-- `object_recursive_isinstance`, `Objects/abstract.c:2639`. Union objects are left
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

/-- `PyObject_IsInstance`, `Objects/abstract.c:2704`. -/
def pyIsInstance (rt : Rt) (inst cls : Val) : M Bool :=
  objectRecursiveIsinstance rt walkFuel inst cls

/-- `recursive_issubclass`, `Objects/abstract.c:2712`. -/
def recursiveIssubclass (rt : Rt) (derived cls : Val) : M Bool := do
  let w ← getW
  match asType w cls, asType w derived with
  | some c, some d => pure (isSubtype w d c)
  | _, _ =>
    checkClass rt derived "issubclass() arg 1 must be a class"
    checkClass rt cls "issubclass() arg 2 must be a class, a tuple of classes, or a union"
    abstractIssubclass rt walkFuel derived cls

/-- `object_issubclass`, `Objects/abstract.c:2732`. -/
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

/-- `PyObject_IsSubclass`, `Objects/abstract.c:2792`. -/
def pyIsSubclass (rt : Rt) (derived cls : Val) : M Bool :=
  objectIssubclass rt walkFuel derived cls

end PyLean.TypeObj
