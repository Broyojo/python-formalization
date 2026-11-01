import PyLean.TypeObj.PropsAttr
import PyLean.TypeObj.Interp

/-!
Properties of comparison, truth, hashing and operator dispatch, for every class structure
and every behaviour of user code.

A theorem about dispatch order says what the *first* slot call is and when the second one
runs. "Reflected operand of a subclass goes first" is `BinaryOp1SubclassPriority`; "same
type: `__radd__` never runs" is `BinaryOp1SameType`.
-/

namespace PyLean.TypeObj

/-- `rt` handles booleans as `PyObject_IsTrue` does. True of every `rtOf exec (n + 1)`;
needed where a C function converts a result it computed itself. -/
def BoolSane (rt : Rt) : Prop := ∀ (b : Bool) (w : World), rt.isTrue (.bool b) w = .ok b w

theorem rtOf_boolSane (exec : Rt → Nat → Val → NameDict → M Val) (n : Nat) :
    BoolSane (rtOf exec (n + 1)) := by
  intro b w
  simp [rtOf, pyIsTrue]

theorem CmpOp.swapped_swapped (op : CmpOp) : op.swapped.swapped = op := by
  cases op <;> rfl

/-- `_Py_SwappedOp` is an involution. -/
def SwappedInvolution : Prop := ∀ op : CmpOp, op.swapped.swapped = op
theorem swappedInvolution_proven : SwappedInvolution := CmpOp.swapped_swapped

/-- **Identity implies equality** in `PyObject_RichCompareBool`: no user `__eq__` runs and
the world is untouched, whatever `__eq__` would have said. -/
def RichCompareBoolIdentity : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World),
    richCompareBool rt v v .eq w = .ok true w ∧ richCompareBool rt v v .ne w = .ok false w

theorem richCompareBoolIdentity_proven : RichCompareBoolIdentity := by
  intro rt v w
  simp [richCompareBool, Val.is_refl]

/-- Reflexivity of container comparison: for every list of values, whatever their
`__eq__`, `xs == xs`, without running user code. -/
theorem firstDiff_self (rt : Rt) (xs : List Val) (w : World) :
    firstDiff rt xs xs w = .ok none w := by
  induction xs with
  | nil => simp [firstDiff]
  | cons x xs ih => simpa [firstDiff, Val.is_refl] using ih

def ContainerEqReflexive : Prop :=
  ∀ (rt : Rt) (xs : List Val) (w : World),
    listRichcompare rt xs xs .eq w = .ok (.bool true) w ∧
    seqRichcompare rt xs xs .eq w = .ok (.bool true) w ∧
    listRichcompare rt xs xs .ne w = .ok (.bool false) w ∧
    seqRichcompare rt xs xs .ne w = .ok (.bool false) w ∧
    seqRichcompare rt xs xs .le w = .ok (.bool true) w ∧
    seqRichcompare rt xs xs .lt w = .ok (.bool false) w

theorem containerEqReflexive_proven : ContainerEqReflexive := by
  intro rt xs w
  simp [listRichcompare, seqRichcompare, firstDiff_self, cmpInt]

/-- The membership test of lists and tuples: `x in xs` is `False` only if no item is
`x`, so identity implies containment whatever `__eq__` does. -/
def ContainsIdentity : Prop :=
  ∀ (rt : Rt) (x : Val) (xs : List Val) (w w' : World),
    anyEq rt x xs w = .ok false w' → ∀ y ∈ xs, y.is x = false

theorem containsIdentity_proven : ContainsIdentity := by
  intro rt x xs
  induction xs with
  | nil => intro w w' _ y hy; simp at hy
  | cons z zs ih =>
    intro w w' h y hy
    simp only [anyEq, M.bind_app] at h
    cases hc : richCompareBool rt z x .eq w with
    | ok b w1 =>
      rw [hc] at h
      cases b with
      | true => simp at h
      | false =>
        simp only [Bool.false_eq_true, ite_false] at h
        rcases List.mem_cons.mp hy with h1 | h1
        · subst h1
          cases hz : y.is x with
          | false => rfl
          | true =>
            simp [richCompareBool, hz] at hc
        · exact ih w1 w' h y h1
    | err e w1 => rw [hc] at h; simp at h

/-- **Subclass priority in comparisons**: when the right operand's type is a proper
subclass, its reflected method runs first, and a non-`NotImplemented` result is final.
`Objects/object.c:1052-1060`. -/
def RichcompareSubclassFirst : Prop :=
  ∀ (rt : Rt) (v u : Val) (op : CmpOp) (f : SlotFn) (r : Val) (w w' : World),
    typeOf w v ≠ typeOf w u →
    isSubtype w (typeOf w u) (typeOf w v) = true →
    slotOf w (typeOf w u) .tp_richcompare = some f →
    callRichcompare rt f u v op.swapped w = .ok r w' →
    (∀ x, r = x → x.is .notImpl = false) →
    doRichcompare rt v u op w = .ok r w'

theorem richcompareSubclassFirst_proven : RichcompareSubclassFirst := by
  intro rt v u op f r w w' hne hsub hf hc hnot
  have hr : ∀ h : r = .notImpl, False := by
    intro h
    have := hnot r rfl
    subst h
    simp [Val.is] at this
  have hbne : (typeOf w v != typeOf w u) = true := by simpa using hne
  have hr' : r ≠ .notImpl := hr
  simp only [doRichcompare, M.bind_app, getW_app, hbne, hsub, Bool.and_self, ite_true, hf,
    M.pure_app, hc]

/-- Without a subclass relation the left operand goes first: its result, unless
`NotImplemented`, is final and the right operand's method never runs. -/
def RichcompareLeftFirst : Prop :=
  ∀ (rt : Rt) (v u : Val) (op : CmpOp) (f : SlotFn) (r : Val) (w w' : World),
    (typeOf w v = typeOf w u ∨ isSubtype w (typeOf w u) (typeOf w v) = false) →
    slotOf w (typeOf w v) .tp_richcompare = some f →
    callRichcompare rt f v u op w = .ok r w' →
    (∀ x, r = x → x.is .notImpl = false) →
    doRichcompare rt v u op w = .ok r w'

theorem richcompareLeftFirst_proven : RichcompareLeftFirst := by
  intro rt v u op f r w w' hc0 hf hc hnot
  have hr : ∀ h : r = .notImpl, False := by
    intro h
    have := hnot r rfl
    subst h
    simp [Val.is] at this
  have hcond : (typeOf w v != typeOf w u && isSubtype w (typeOf w u) (typeOf w v)) = false := by
    rcases hc0 with h | h
    · simp [h]
    · simp [h]
  have hr' : r ≠ .notImpl := hr
  simp only [doRichcompare, M.bind_app, getW_app, hcond, Bool.false_eq_true, ite_false,
    M.pure_app, hf, hc]

/-- The fallback of `do_richcompare`, `Objects/object.c:1075-1089`, when every slot call
answered `NotImplemented`: `==` is identity, `!=` its negation, ordering raises. Stated
for two objects of the same type whose slot is `object_richcompare` and which are
not identical, the common case of a class with no comparison methods. -/
def RichcompareDefaults : Prop :=
  ∀ (rt : Rt) (v u : Val) (w : World),
    slotOf w (typeOf w v) .tp_richcompare = some (.c .object) →
    typeOf w v = typeOf w u →
    v.is u = false → u.is v = false →
    doRichcompare rt v u .eq w = .ok (.bool false) w ∧
    (∀ op, (op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) →
      doRichcompare rt v u op w =
        (typeErr s!"'{op.str}' not supported between instances of '{trunc 100 (typeName w v)}' and '{trunc 100 (typeName w u)}'" : M Val) w)

theorem richcompareDefaults_proven : RichcompareDefaults := by
  intro rt v u w hs heq hi hi'
  constructor
  · simp [doRichcompare, ← heq, hs, callRichcompare, objectRichcompare, hi, hi', CmpOp.swapped]
  · intro op hop
    rcases hop with rfl | rfl | rfl | rfl <;>
      simp [doRichcompare, ← heq, hs, callRichcompare, objectRichcompare, CmpOp.swapped]

/-- Default `__ne__`: `object.__ne__(a, b)` asks `tp_richcompare(a, b, Py_EQ)` and negates a
result that is not `NotImplemented`, `Objects/typeobject.c:6980-7000`. -/
def ObjectNeInvertsEq : Prop :=
  ∀ (rt : Rt) (a b r : Val) (g : SlotFn) (t : Bool) (w w1 w2 : World),
    slotOf w (typeOf w a) .tp_richcompare = some g →
    callRichcompareEq rt g a b .eq w = .ok r w1 →
    r.is .notImpl = false →
    rt.isTrue r w1 = .ok t w2 →
    callRichcompare rt (.c .object) a b .ne w = .ok (.bool (!t)) w2

theorem objectNeInvertsEq_proven : ObjectNeInvertsEq := by
  intro rt a b r g t w w1 w2 hg hc hn ht
  have hr : r ≠ .notImpl := by
    intro h
    subst h
    simp [Val.is] at hn
  simp only [callRichcompare, objectRichcompare, M.bind_app, getW_app, hg, hc]
  cases r <;> first
    | exact (hr rfl).elim
    | simp [ht]

/-- `PyObject_IsTrue` on the singletons, `Objects/object.c:2063-2068`: no slot runs. -/
def IsTrueSingletons : Prop :=
  ∀ (rt : Rt) (w : World),
    pyIsTrue rt (.bool true) w = .ok true w ∧ pyIsTrue rt (.bool false) w = .ok false w ∧
    pyIsTrue rt .none w = .ok false w

theorem isTrueSingletons_proven : IsTrueSingletons := by
  intro rt w
  simp [pyIsTrue]

/-- `PyObject_IsTrue` order: `nb_bool`, then `mp_length`, then `sq_length`, then `True`.
An object with none of the three is true without running anything. -/
def IsTrueDefaultTrue : Prop :=
  ∀ (rt : Rt) (v : Val) (w : World),
    v.is .none = false → (∀ b, v ≠ .bool b) →
    slotIn w v .nb_bool = none → slotIn w v .mp_length = none → slotIn w v .sq_length = none →
    pyIsTrue rt v w = .ok true w

theorem isTrueDefaultTrue_proven : IsTrueDefaultTrue := by
  intro rt v w hn hb h1 h2 h3
  cases v with
  | bool b => exact (hb b rfl).elim
  | none => simp [Val.is] at hn
  | _ => simp [pyIsTrue, h1, h2, h3]

/-- `__len__` decides truth when there is no `__bool__`: the length slot result, positive
means true (`Objects/object.c:2072-2081`), mapping length first. -/
def IsTrueLengthFallback : Prop :=
  ∀ (rt : Rt) (v : Val) (f : SlotFn) (n : Int) (w w' : World),
    v.is .none = false → (∀ b, v ≠ .bool b) →
    slotIn w v .nb_bool = none → slotIn w v .mp_length = some f →
    callLen rt f v w = .ok n w' →
    pyIsTrue rt v w = .ok (decide (n > 0)) w'

theorem isTrueLengthFallback_proven : IsTrueLengthFallback := by
  intro rt v f n w w' hn hb h1 h2 hl
  cases v with
  | bool b => exact (hb b rfl).elim
  | none => simp [Val.is] at hn
  | _ => simp [pyIsTrue, h1, h2, hl]

/-- A `__bool__` returning a non-bool raises `TypeError`; `None` as `__bool__` raises
`TypeError`, `Objects/typeobject.c:10208-10240`. -/
def NbBoolMustReturnBool : Prop :=
  ∀ (rt : Rt) (self v : Val) (w w' : World),
    maybeCallSpecial rt self "__bool__" [] true w = .ok (.res v) w' →
    (∀ b, v ≠ .bool b) →
    slotNbBool rt self w = (typeErr s!"__bool__ should return bool, returned {typeName w' v}" : M Bool) w'

theorem nbBoolMustReturnBool_proven : NbBoolMustReturnBool := by
  intro rt self v w w' h hb
  cases v with
  | bool b => exact (hb b rfl).elim
  | _ => simp [slotNbBool, h]

/-- **Hash results are never -1.** `slot_tp_hash` returns `-2` for `-1` and any value in
`Py_ssize_t` range otherwise; `-1` is reserved for errors,
`Objects/typeobject.c:10333-10335`. Quantified over every `__hash__`. -/
def SlotHashNotMinusOne : Prop :=
  ∀ (rt : Rt) (self : Val) (h : Int) (w w' : World),
    slotTpHash rt self w = .ok h w' → h ≠ -1

theorem hashOfInt_ne (i : Int) : hashOfInt i ≠ -1 := by
  have key : ∀ h : Int, (if (h == -1) = true then (-2 : Int) else h) ≠ -1 := by
    intro h
    by_cases hh : h = -1 <;> simp [hh]
  exact key _

theorem slotHashNotMinusOne_proven : SlotHashNotMinusOne := by
  intro rt self h w w' he
  simp only [slotTpHash, M.bind_app] at he
  cases hm : maybeCallSpecial rt self "__hash__" [] true w with
  | err e w1 => rw [hm] at he; simp at he
  | ok m w1 =>
    rw [hm] at he
    cases m with
    | isNone => simp [hashNotImplemented, typeErr, raiseC] at he
    | missing => simp [hashNotImplemented, typeErr, raiseC] at he
    | res r =>
      cases hi : intOf w1 r with
      | none => simp [hi, typeErr, raiseC] at he
      | some i =>
        simp [hi] at he
        rw [← he.1]
        exact hashOfInt_ne i

/-- **Hash values in range are preserved**: `hash(x)` equals `x.__hash__()` for a result in
`Py_ssize_t` range other than `-1`, so `x.__hash__()` returning `hash(y)` gives
`hash(x) == hash(y)`, as the comment at `Objects/typeobject.c:10320-10324` requires. -/
def SlotHashPreservesRange : Prop :=
  ∀ (rt : Rt) (self r : Val) (i : Int) (w w' : World),
    maybeCallSpecial rt self "__hash__" [] true w = .ok (.res r) w' →
    intOf w' r = some i → inSsize i = true → i ≠ -1 →
    slotTpHash rt self w = .ok i w'

theorem slotHashPreservesRange_proven : SlotHashPreservesRange := by
  intro rt self r i w w' h hi hs hn
  simp [slotTpHash, h, hi, hashOfInt, hs, hn]

/-- A non-int from `__hash__` is a `TypeError`, for every value. -/
def SlotHashNonInt : Prop :=
  ∀ (rt : Rt) (self r : Val) (w w' : World),
    maybeCallSpecial rt self "__hash__" [] true w = .ok (.res r) w' →
    intOf w' r = none →
    slotTpHash rt self w = (typeErr "__hash__ method should return an integer" : M Int) w'

theorem slotHashNonInt_proven : SlotHashNonInt := by
  intro rt self r w w' h hi
  simp [slotTpHash, h, hi]

/-- `__hash__ = None` makes instances unhashable, with the message of
`PyObject_HashNotImplemented`. -/
def SlotHashNoneUnhashable : Prop :=
  ∀ (rt : Rt) (self : Val) (w w' : World),
    maybeCallSpecial rt self "__hash__" [] true w = .ok .isNone w' →
    slotTpHash rt self w = (typeErr s!"unhashable type: '{trunc 200 (typeName w' self)}'" : M Int) w'

theorem slotHashNoneUnhashable_proven : SlotHashNoneUnhashable := by
  intro rt self w w' h
  simp [slotTpHash, h, hashNotImplemented]

/-- **Operands of the same type**: `binary_op1` tries only the left slot, so `__radd__`
never runs for `a + b` when `type(a) is type(b)`. -/
def BinaryOp1SameType : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (f : SlotFn) (w : World),
    typeOf w v = typeOf w u →
    slotIn w v s = some f →
    binaryOp1 rt v u s w = callNbBinary rt s f v u w ∨
    (∀ w', callNbBinary rt s f v u w = .ok .notImpl w' → binaryOp1 rt v u s w = .ok .notImpl w')

theorem binaryOp1SameType_proven : BinaryOp1SameType := by
  intro rt v u s f w he hf
  right
  intro w' hc
  simp [binaryOp1, ← he, hf, hc]

/-- **The reflected-operand priority rule.** If `type(u)` is a proper subclass of
`type(v)` and provides a different slot function, that function runs first; when it
answers, `v`'s slot never runs. -/
def BinaryOp1SubclassPriority : Prop :=
  ∀ (rt : Rt) (v u r : Val) (s : Slot) (sv su : SlotFn) (w w' : World),
    typeOf w v ≠ typeOf w u →
    isSubtype w (typeOf w u) (typeOf w v) = true →
    slotIn w v s = some sv → slotIn w u s = some su → su ≠ sv →
    callNbBinary rt s su v u w = .ok r w' → r.is .notImpl = false →
    binaryOp1 rt v u s w = .ok r w'

theorem binaryOp1SubclassPriority_proven : BinaryOp1SubclassPriority := by
  intro rt v u r s sv su w w' hne hsub hv hu hd hc hn
  have hr : r ≠ .notImpl := by
    intro h
    subst h
    simp [Val.is] at hn
  have hne' : typeOf w u ≠ typeOf w v := fun h => hne h.symm
  simp only [binaryOp1, M.bind_app, getW_app, hv, hu]
  simp [hne', hd, hsub, hc, hr]

/-- If the subclass's slot says `NotImplemented`, the left slot is tried next and the
right one is not tried again. -/
def BinaryOp1SubclassThenLeft : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (sv su : SlotFn) (w w1 : World),
    typeOf w v ≠ typeOf w u →
    isSubtype w (typeOf w u) (typeOf w v) = true →
    slotIn w v s = some sv → slotIn w u s = some su → su ≠ sv →
    callNbBinary rt s su v u w = .ok .notImpl w1 →
    binaryOp1 rt v u s w =
      callNbBinary rt s sv v u w1

theorem binaryOp1SubclassThenLeft_proven : BinaryOp1SubclassThenLeft := by
  intro rt v u s sv su w w1 hne hsub hv hu hd hc
  have hne' : typeOf w u ≠ typeOf w v := fun h => hne h.symm
  simp only [binaryOp1, M.bind_app, getW_app, hv, hu]
  simp [hne', hd, hsub, hc]
  cases hx : callNbBinary rt s sv v u w1 with
  | err e w2 => rfl
  | ok x w2 =>
    cases x <;> rfl

/-- Unrelated types: left slot first, then the right slot. -/
def BinaryOp1LeftThenRight : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (sv su : SlotFn) (w w1 : World),
    typeOf w v ≠ typeOf w u →
    isSubtype w (typeOf w u) (typeOf w v) = false →
    slotIn w v s = some sv → slotIn w u s = some su → su ≠ sv →
    callNbBinary rt s sv v u w = .ok .notImpl w1 →
    binaryOp1 rt v u s w = callNbBinary rt s su v u w1

theorem binaryOp1LeftThenRight_proven : BinaryOp1LeftThenRight := by
  intro rt v u s sv su w w1 hne hsub hv hu hd hc
  have hne' : typeOf w u ≠ typeOf w v := fun h => hne h.symm
  simp only [binaryOp1, M.bind_app, getW_app, hv, hu]
  simp [hne', hd, hsub, hc]

/-- Two operands sharing the same slot function get one call: the inherited-operator case
of `Objects/abstract.c:947`. -/
def BinaryOp1SharedSlotOnce : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (f : SlotFn) (w w1 : World),
    slotIn w v s = some f → slotIn w u s = some f →
    callNbBinary rt s f v u w = .ok .notImpl w1 →
    binaryOp1 rt v u s w = .ok .notImpl w1

theorem binaryOp1SharedSlotOnce_proven : BinaryOp1SharedSlotOnce := by
  intro rt v u s f w w1 hv hu hc
  simp [binaryOp1, hv, hu, hc]

/-- `binary_op` turns `NotImplemented` into the `TypeError` of `binop_type_error`, and
never returns `NotImplemented`. -/
def BinaryOpNeverNotImplemented : Prop :=
  ∀ (rt : Rt) (v u : Val) (s : Slot) (name : String) (r : Val) (w w' : World),
    binaryOp rt v u s name w = .ok r w' → r.is .notImpl = false

theorem binaryOpNeverNotImplemented_proven : BinaryOpNeverNotImplemented := by
  intro rt v u s name r w w' h
  simp only [binaryOp, M.bind_app] at h
  cases hb : binaryOp1 rt v u s w with
  | err e w1 => rw [hb] at h; simp at h
  | ok x w1 =>
    rw [hb] at h
    cases x <;> first
      | (simp [binopTypeError, typeErr, raiseC] at h; done)
      | (simp at h
         obtain ⟨rfl, _⟩ := h
         simp [Val.is])

/-- `PyNumber_Add`: `sq_concat` runs only after both number slots gave `NotImplemented`,
and it runs on `v` only. -/
def NumberAddConcatFallback : Prop :=
  ∀ (rt : Rt) (v u : Val) (f : SlotFn) (w w1 : World),
    binaryOp1 rt v u .nb_add w = .ok .notImpl w1 →
    slotIn w1 v .sq_concat = some f →
    pyNumberAdd rt v u w = callSqConcat rt f v u w1

theorem numberAddConcatFallback_proven : NumberAddConcatFallback := by
  intro rt v u f w w1 hb hf
  simp [pyNumberAdd, hb, hf]

/-- `sequence_repeat` needs an index: a right operand without `__index__` raises the
message of `Objects/abstract.c:1157`. -/
def SequenceRepeatNeedsIndex : Prop :=
  ∀ (rt : Rt) (f : SlotFn) (seq n : Val) (w : World),
    indexCheck w n = false →
    sequenceRepeat rt f seq n w =
      (typeErr s!"can't multiply sequence by non-int of type '{trunc 200 (typeName w n)}'" : M Val) w

theorem sequenceRepeatNeedsIndex_proven : SequenceRepeatNeedsIndex := by
  intro rt f seq n w h
  simp [sequenceRepeat, h]

/-- `PyNumber_Multiply` is symmetric in its fallback: with no number slot answering, a
sequence on either side is repeated by the other operand. -/
def NumberMultiplyBothSides : Prop :=
  ∀ (rt : Rt) (v u : Val) (f : SlotFn) (w w1 : World),
    binaryOp1 rt v u .nb_multiply w = .ok .notImpl w1 →
    slotIn w1 v .sq_repeat = none →
    slotIn w1 u .sq_repeat = some f →
    pyNumberMultiply rt v u w = sequenceRepeat rt f u v w1

theorem numberMultiplyBothSides_proven : NumberMultiplyBothSides := by
  intro rt v u f w w1 hb h1 h2
  simp [pyNumberMultiply, hb, h1, h2]

/-- **`x *= seq` falls back like `x * seq`.** Refuted: with `x` an instance of any class,
`x * [1]` repeats the list by `x.__index__()` while `x *= [1]` raises `TypeError`, because
the `else if` at `Objects/abstract.c:1336` is keyed on `tp_as_sequence != NULL`, and heap
types always have that struct. The statement says the in-place form takes the same
fallback whenever the left operand has no repeat slot. -/
def InPlaceMultiplyMatchesMultiply : Prop :=
  ∀ (rt : Rt) (v u : Val) (f : SlotFn) (w w1 : World),
    binaryIop1 rt v u .nb_inplace_multiply .nb_multiply w = .ok .notImpl w1 →
    slotIn w1 v .sq_repeat = none → slotIn w1 v .sq_inplace_repeat = none →
    slotIn w1 u .sq_repeat = some f →
    pyNumberInPlaceMultiply rt v u w = sequenceRepeat rt f u v w1

/-- The world of the counterexample: a heap class `X` (which has `tp_as_sequence`) and
`list`, with one instance of each, `x * [1]` vs `x *= [1]`. -/
def imulWorld : World :=
  { heap := #[.ty 0 { name := "X", asSequence := true, asNumber := true, heap := true,
                      mro := some [0] },
              .ty 0 { name := "list", asSequence := true, mro := some [1],
                      slots := [(.sq_repeat, .c .list)] },
              .val { cls := 0 }, .val { cls := 1, body := .list [] }] }

/-- A runtime that is never entered: the counterexample runs no user code. -/
def stuckRt : Rt := rtOf (fun _ _ _ _ => raise .fuel) 0

/-- The error message of a result, for comparing failures. -/
def errMsg {α : Type} : R α → Option String
  | .err (.exc _ m _) _ => some m
  | _ => none

theorem imul_lhs : errMsg (pyNumberInPlaceMultiply stuckRt (.obj 2) (.obj 3) imulWorld) =
    some "unsupported operand type(s) for *=: 'X' and 'list'" := by
  rfl

theorem imul_rhs : errMsg (sequenceRepeat stuckRt (.c .list) (.obj 3) (.obj 2) imulWorld) =
    some "can't multiply sequence by non-int of type 'X'" := by
  rfl

theorem inPlaceMultiplyMatchesMultiply_refuted : ¬InPlaceMultiplyMatchesMultiply := by
  intro h
  have hb : binaryIop1 stuckRt (.obj 2) (.obj 3) .nb_inplace_multiply .nb_multiply imulWorld =
      .ok .notImpl imulWorld := by rfl
  have := h stuckRt (.obj 2) (.obj 3) (.c .list) imulWorld imulWorld hb (by rfl) (by rfl) (by rfl)
  have h1 := imul_lhs
  rw [this, imul_rhs] at h1
  simp at h1

end PyLean.TypeObj
