import PyLean.TypeObj.Model

/-!
`slotdefs` and slot maintenance: `Objects/typeobject.c:11684-12358`.

Omitted from `slotdefs`: the four `tp_getattr`/`tp_setattr` lines (`:11685-11688`). Those
slots are NULL in every type this model has, so `resolve_slotdups` skips them and
`update_one_slot` leaves them NULL.
-/

namespace PyLean.TypeObj

private def d (n : Name) (s : Slot) (g : Option SlotFn) (wr : Option WrapKind) : SlotDef :=
  { name := n, slot := s, generic := g, wrapper := wr }

/-- `slotdefs`, `Objects/typeobject.c:11684-11881`, in table order. -/
def slotdefs : List SlotDef := [
  d "__repr__" .tp_repr (some .generic) (some .unary),
  d "__hash__" .tp_hash (some .generic) (some .hash),
  d "__call__" .tp_call (some .generic) (some .call),
  d "__str__" .tp_str (some .generic) (some .unary),
  d "__getattribute__" .tp_getattro (some .generic) (some .binary),
  d "__getattr__" .tp_getattro (some .generic) none,
  d "__setattr__" .tp_setattro (some .generic) (some .setattr),
  d "__delattr__" .tp_setattro (some .generic) (some .delattr),
  d "__lt__" .tp_richcompare (some .generic) (some (.richcmp .lt)),
  d "__le__" .tp_richcompare (some .generic) (some (.richcmp .le)),
  d "__eq__" .tp_richcompare (some .generic) (some (.richcmp .eq)),
  d "__ne__" .tp_richcompare (some .generic) (some (.richcmp .ne)),
  d "__gt__" .tp_richcompare (some .generic) (some (.richcmp .gt)),
  d "__ge__" .tp_richcompare (some .generic) (some (.richcmp .ge)),
  d "__iter__" .tp_iter (some .generic) (some .unary),
  d "__next__" .tp_iternext (some .generic) (some .next),
  d "__get__" .tp_descr_get (some .generic) (some .descrGet),
  d "__set__" .tp_descr_set (some .generic) (some .descrSet),
  d "__delete__" .tp_descr_set (some .generic) (some .descrDelete),
  d "__init__" .tp_init (some .generic) (some .init),
  d "__new__" .tp_new (some .generic) none,
  d "__del__" .tp_finalize (some .generic) (some .del),
  d "__buffer__" .bf_getbuffer (some .generic) (some .buffer),
  d "__release_buffer__" .bf_releasebuffer (some .generic) (some .releaseBuffer),
  d "__await__" .am_await (some .generic) (some .unary),
  d "__aiter__" .am_aiter (some .generic) (some .unary),
  d "__anext__" .am_anext (some .generic) (some .unary),
  d "__add__" .nb_add (some .generic) (some .binaryL),
  d "__radd__" .nb_add (some .generic) (some .binaryR),
  d "__sub__" .nb_subtract (some .generic) (some .binaryL),
  d "__rsub__" .nb_subtract (some .generic) (some .binaryR),
  d "__mul__" .nb_multiply (some .generic) (some .binaryL),
  d "__rmul__" .nb_multiply (some .generic) (some .binaryR),
  d "__mod__" .nb_remainder (some .generic) (some .binaryL),
  d "__rmod__" .nb_remainder (some .generic) (some .binaryR),
  d "__divmod__" .nb_divmod (some .generic) (some .binaryL),
  d "__rdivmod__" .nb_divmod (some .generic) (some .binaryR),
  d "__pow__" .nb_power (some .generic) (some .ternary),
  d "__rpow__" .nb_power (some .generic) (some .ternaryR),
  d "__neg__" .nb_negative (some .generic) (some .unary),
  d "__pos__" .nb_positive (some .generic) (some .unary),
  d "__abs__" .nb_absolute (some .generic) (some .unary),
  d "__bool__" .nb_bool (some .generic) (some .inquiry),
  d "__invert__" .nb_invert (some .generic) (some .unary),
  d "__lshift__" .nb_lshift (some .generic) (some .binaryL),
  d "__rlshift__" .nb_lshift (some .generic) (some .binaryR),
  d "__rshift__" .nb_rshift (some .generic) (some .binaryL),
  d "__rrshift__" .nb_rshift (some .generic) (some .binaryR),
  d "__and__" .nb_and (some .generic) (some .binaryL),
  d "__rand__" .nb_and (some .generic) (some .binaryR),
  d "__xor__" .nb_xor (some .generic) (some .binaryL),
  d "__rxor__" .nb_xor (some .generic) (some .binaryR),
  d "__or__" .nb_or (some .generic) (some .binaryL),
  d "__ror__" .nb_or (some .generic) (some .binaryR),
  d "__int__" .nb_int (some .generic) (some .unary),
  d "__float__" .nb_float (some .generic) (some .unary),
  d "__iadd__" .nb_inplace_add (some .generic) (some .binary),
  d "__isub__" .nb_inplace_subtract (some .generic) (some .binary),
  d "__imul__" .nb_inplace_multiply (some .generic) (some .binary),
  d "__imod__" .nb_inplace_remainder (some .generic) (some .binary),
  d "__ipow__" .nb_inplace_power (some .generic) (some .ternary),
  d "__ilshift__" .nb_inplace_lshift (some .generic) (some .binary),
  d "__irshift__" .nb_inplace_rshift (some .generic) (some .binary),
  d "__iand__" .nb_inplace_and (some .generic) (some .binary),
  d "__ixor__" .nb_inplace_xor (some .generic) (some .binary),
  d "__ior__" .nb_inplace_or (some .generic) (some .binary),
  d "__floordiv__" .nb_floor_divide (some .generic) (some .binaryL),
  d "__rfloordiv__" .nb_floor_divide (some .generic) (some .binaryR),
  d "__truediv__" .nb_true_divide (some .generic) (some .binaryL),
  d "__rtruediv__" .nb_true_divide (some .generic) (some .binaryR),
  d "__ifloordiv__" .nb_inplace_floor_divide (some .generic) (some .binary),
  d "__itruediv__" .nb_inplace_true_divide (some .generic) (some .binary),
  d "__index__" .nb_index (some .generic) (some .unary),
  d "__matmul__" .nb_matrix_multiply (some .generic) (some .binaryL),
  d "__rmatmul__" .nb_matrix_multiply (some .generic) (some .binaryR),
  d "__imatmul__" .nb_inplace_matrix_multiply (some .generic) (some .binary),
  d "__len__" .mp_length (some .generic) (some .len),
  d "__getitem__" .mp_subscript (some .generic) (some .binary),
  d "__setitem__" .mp_ass_subscript (some .generic) (some .objobjarg),
  d "__delitem__" .mp_ass_subscript (some .generic) (some .delitem),
  d "__len__" .sq_length (some .generic) (some .len),
  d "__add__" .sq_concat none (some .binary),
  d "__mul__" .sq_repeat none (some .indexArg),
  d "__rmul__" .sq_repeat none (some .indexArg),
  d "__getitem__" .sq_item (some .generic) (some .sqItem),
  d "__setitem__" .sq_ass_item (some .generic) (some .sqSetitem),
  d "__delitem__" .sq_ass_item (some .generic) (some .sqDelitem),
  d "__contains__" .sq_contains (some .generic) (some .objobj),
  d "__iadd__" .sq_inplace_concat none (some .binary),
  d "__imul__" .sq_inplace_repeat none (some .indexArg)]

/-- Set a slot (`none` clears it). -/
def setSlot (slots : List (Slot × SlotFn)) (s : Slot) (v : Option SlotFn) :
    List (Slot × SlotFn) :=
  let rest := slots.filter (fun p => p.1 != s)
  match v with
  | some f => (s, f) :: rest
  | none => rest

/-- `slotptr(type, offset) != NULL`: the struct holding `s` exists. -/
def slotExists (w : World) (t : Addr) (s : Slot) : Bool := hasGroup w t s.group

/-- `resolve_slotdups`, `Objects/typeobject.c@3.14.7:11213`: the unique filled slot among the
slotdefs named `n`, if exactly one is filled. -/
def resolveSlotdups (w : World) (t : Addr) (n : Name) : Option Slot :=
  let filled := (slotdefs.filter (·.name == n)).filter fun p =>
    slotExists w t p.slot && (slotOf w t p.slot).isSome
  match filled with
  | [p] => some p.slot
  | _ => none

/-- Working state of the `do ... while` in `update_one_slot`. -/
structure UpdState where
  specific : Option SlotFn := none
  generic : Option SlotFn := none
  useGeneric : Bool := false
  deriving Inhabited

/-- One iteration of the loop in `update_one_slot`, `Objects/typeobject.c:12038-12138`.
The `*ptr == ml_meth` test at `:12122` holds for the `METH_COEXIST` methods
`list.__getitem__` and `dict.__getitem__`, whose `ml_meth` is `mp_subscript`. -/
def updateOneSlotStep (w : World) (t : Addr) (ptr : Slot) (st : UpdState) (p : SlotDef) :
    UpdState :=
  match findInMro w t p.name with
  | none =>
    if ptr == .tp_iternext then { st with specific := some .nextNotImpl } else st
  | some descr =>
    let tyD := typeOf w descr
    match payloadOf w descr with
    | some (.wrapperDescr owner dbase wrapped) =>
      if tyD == B.wrapperDescr && dbase.name == p.name then
        let tptr := resolveSlotdups w t p.name
        let st1 :=
          if tptr == none || tptr == some ptr then { st with generic := p.generic } else st
        if (st1.specific == none || st1.specific == some wrapped) &&
            dbase.wrapper == p.wrapper && isSubtype w t owner then
          { st1 with specific := some wrapped }
        else
          { st1 with useGeneric := true }
      else
        { st with useGeneric := true, generic := p.generic }
    | some (.builtin (.tpNewWrapper _) _) =>
      if tyD == B.builtinFn && ptr == .tp_new then
        { st with specific := slotOf w t .tp_new }
      else
        { st with useGeneric := true, generic := p.generic }
    | some (.methodDescr owner nm _) =>
      let cur := slotOf w t ptr
      let same := ptr == .mp_subscript && nm == "__getitem__" &&
        ((owner == B.list && cur == some (.c .list)) || (owner == B.dict && cur == some (.c .dict)))
      if st.generic.isNone && same then { st with useGeneric := true, generic := cur }
      else { st with useGeneric := true, generic := p.generic }
    | _ =>
      match descr with
      | .none =>
        if ptr == .tp_hash then { st with specific := some .hashNotImpl }
        else { st with useGeneric := true, generic := p.generic }
      | _ => { st with useGeneric := true, generic := p.generic }

/-- `update_one_slot`, `Objects/typeobject.c@3.14.7:11308`, for the slot `ptr`. -/
def updateOneSlotValue (w : World) (t : Addr) (ptr : Slot) : Option SlotFn :=
  let st := (slotdefs.filter (·.slot == ptr)).foldl (updateOneSlotStep w t ptr) {}
  if st.specific.isSome && !st.useGeneric then st.specific else st.generic

/-- Store the result of `update_one_slot`. -/
def updateOneSlot (w : World) (t : Addr) (s : Slot) : World :=
  if slotExists w t s then
    let v := updateOneSlotValue w t s
    match w.get t with
    | .ty c dt => w.setCell t (.ty c { dt with slots := setSlot dt.slots s v })
    | .val _ => w
  else w

/-- The distinct slots of `slotdefs`, in order. -/
def allSlots : List Slot :=
  (slotdefs.map (·.slot)).eraseDups

/-- `fixup_slot_dispatchers`, `Objects/typeobject.c:12232`. -/
def fixupSlotDispatchers (w : World) (t : Addr) : World :=
  allSlots.foldl (fun w s => updateOneSlot w t s) w

/-- The slots affected by a change to attribute `n`: the first half of `update_slot`
(`Objects/typeobject.c:12199-12216`). -/
def slotsNamed (n : Name) : List Slot := ((slotdefs.filter (·.name == n)).map (·.slot)).eraseDups

/-- `update_subclasses` / `recurse_down_subclasses`, `Objects/typeobject.c:12458-12509`.
Fuel bounds the subclass depth. -/
def updateSubclasses (attr : Name) (slots : List Slot) : Nat → World → Addr → World
  | 0, w, _ => w
  | fuel + 1, w, t =>
    let w := slots.foldl (fun w s => updateOneSlot w t s) w
    (tdata w t).subclasses.foldl (fun w sub =>
      if NameDict.contains (tdata w sub).dict attr then w
      else updateSubclasses attr slots fuel w sub) w

/-- `update_slot`, `Objects/typeobject.c@3.14.7:11439`. -/
def updateSlot (w : World) (t : Addr) (n : Name) : World :=
  match slotsNamed n with
  | [] => w
  | slots => updateSubclasses n slots w.heap.size w t

/-- `is_dunder_name`, `Objects/typeobject.c:6248`. Names are compared as characters: the
`PyUnicode_1BYTE_KIND` test matters only for non-Latin-1 names, which no special method
has. -/
def isDunderName (n : Name) : Bool :=
  let cs := n.toList
  cs.length > 4 && cs.take 2 == ['_', '_'] && cs.drop (cs.length - 2) == ['_', '_']

/-- `update_all_slots`, `Objects/typeobject.c:12277`. -/
def updateAllSlots (w : World) (t : Addr) : World :=
  slotdefs.foldl (fun w p => updateSlot w t p.name) w

/-- `add_operators`, `Objects/typeobject.c:12562`, for type `t`: each filled slot gets a
wrapper descriptor in `tp_dict` unless the name is already there. The `slot_inherited`
test applies to static builtins, which `Builtins.lean` prepares separately. -/
def addOperators (t : Addr) : M Unit := do
  for p in slotdefs do
    match p.wrapper with
    | none => pure ()
    | some _ =>
      let w ← getW
      match (if slotExists w t p.slot then slotOf w t p.slot else none) with
      | none => pure ()
      | some f =>
        unless NameDict.contains (tdata w t).dict p.name do
          if f == .hashNotImpl then
            modType t fun dt => { dt with dict := NameDict.set dt.dict p.name .none }
          else
            let dv ← alloc B.wrapperDescr (.wrapperDescr t p f)
            modType t fun dt => { dt with dict := NameDict.set dt.dict p.name dv }

end PyLean.TypeObj
