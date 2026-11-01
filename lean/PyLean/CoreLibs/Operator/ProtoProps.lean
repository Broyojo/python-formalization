import PyLean.CoreLibs.Operator.Proto

/-!
Properties of the functions of `operator` and `_operator`.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-! ### `binary_op1` -/

/-- `binary_op1`, for every operator, so the body of `operator.sub` and the others in both twins. The right slot
is dropped for the same type and for the same slot. With a right operand of a subclass, the right slot goes
first; otherwise the left, and `NotImplemented` moves to the other; an exception stops the search; with nothing
left, `TypeError` names the operator and both types. Language reference, data model. -/
def BinaryDispatch : Prop :=
  ∀ (α : Type) (A : BinArgs α) (sym : String) (v w x : α) (sv sw : Slot α) (e : PyExc),
    (A.sv = none → A.slotw = none → binaryOp A sym v w = .error (binopError sym A.lt A.rt)) ∧
    (A.sameType = true → A.slotw = none) ∧
    (A.sv = some sv → A.sw = some sw → sw.id = sv.id → A.slotw = none) ∧
    (A.sv = some sv → A.slotw = some sw → A.subtype = true → sw.run v w = .ok (.val x) →
      binaryOp A sym v w = .ok x) ∧
    (A.sv = some sv → A.slotw = some sw → A.subtype = true → sw.run v w = .ok .notImplemented →
      binaryOp1 A v w = sv.run v w) ∧
    (A.sv = some sv → A.slotw = some sw → A.subtype = false → sv.run v w = .ok (.val x) →
      binaryOp A sym v w = .ok x) ∧
    (A.sv = some sv → A.slotw = some sw → A.subtype = false → sv.run v w = .ok .notImplemented →
      binaryOp1 A v w = sw.run v w) ∧
    (A.sv = some sv → sv.run v w = .error e → A.subtype = false → binaryOp A sym v w = .error e)

theorem binaryDispatch_proven : BinaryDispatch := by
  intro α A sym v w x sv sw e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2
    simp [binaryOp, binaryOp1, h1, h2]
  · intro h
    simp [BinArgs.slotw, h]
  · intro h1 h2 h3
    simp [BinArgs.slotw, h1, h2, h3]
  · intro h1 h2 h3 h4
    simp [binaryOp, binaryOp1, h1, h2, h3, h4]
  · intro h1 h2 h3 h4
    simp [binaryOp1, h1, h2, h3, h4]
  · intro h1 h2 h3 h4
    simp [binaryOp, binaryOp1, h1, h2, h3, h4]
  · intro h1 h2 h3 h4
    simp [binaryOp1, h1, h2, h3, h4]
  · intro h1 h2 h3
    cases hw : A.slotw <;> simp [binaryOp, binaryOp1, h1, h2, h3, hw]

/-- `SLOT1BINFULL`, the slot of every Python class: a subclass that overrides `__rop__` runs first, its
`NotImplemented` moves to `__op__`, and then `__rop__` is not tried again; for operands of one type `__rop__` is
never tried; a left operand of a C type goes straight to `__rop__`. Data model: "if the right operand's type
is a subclass of the left operand's type and that subclass provides a different implementation". -/
def HeapDispatch : Prop :=
  ∀ (α : Type) (P : HeapPair α) (v w x y : α),
    (P.selfHeap = true → P.sameType = false → P.otherHeap = true → P.subtype = true →
      P.overloaded = .ok true → P.rdunder w v = .ok (.val x) → slotBinary P v w = .ok (.val x)) ∧
    (P.selfHeap = true → P.sameType = false → P.otherHeap = true → P.subtype = true →
      P.overloaded = .ok true → P.rdunder w v = .ok .notImplemented → P.dunder v w = .ok .notImplemented →
      slotBinary P v w = .ok .notImplemented) ∧
    (P.selfHeap = true → P.sameType = true → P.dunder v w = .ok .notImplemented →
      slotBinary P v w = .ok .notImplemented) ∧
    (P.selfHeap = true → P.sameType = false → P.otherHeap = true → P.subtype = false →
      P.dunder v w = .ok .notImplemented → P.rdunder w v = .ok (.val y) →
      slotBinary P v w = .ok (.val y)) ∧
    (P.selfHeap = false → P.sameType = false → P.otherHeap = true → slotBinary P v w = P.rdunder w v)

theorem heapDispatch_proven : HeapDispatch := by
  intro α P v w x y
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h1 h2 h3 h4 h5 h6
    simp [slotBinary, h1, h2, h3, h4, h5, h6]
  · intro h1 h2 h3 h4 h5 h6 h7
    simp [slotBinary, h1, h2, h3, h4, h5, h6, h7]
  · intro h1 h2 h3
    simp [slotBinary, h1, h2, h3]
  · intro h1 h2 h3 h4 h5 h6
    simp [slotBinary, h1, h2, h3, h4, h5, h6]
  · intro h1 h2 h3
    simp [slotBinary, h1, h2, h3]

/-- `+` and `*` after `binary_op1` gave up: `sq_concat` of the left operand; `sq_repeat` of the left, then of the
right, with the other operand as the count. The count goes through `__index__`, which may raise, must fit
`Py_ssize_t`, and a non-index is a `TypeError`. These are the sequence paths of `operator.add` and `operator.mul`. -/
def SequenceFallback : Prop :=
  ∀ (α : Type) (A : BinArgs α) (Q : SeqArgs α) (v w x : α) (n : Int) (e : PyExc)
    (f : α → α → Py α) (g : α → Int → Py α),
    binaryOp1 A v w = .ok .notImplemented →
    (Q.concat = some f → numberAdd A Q v w = f v w) ∧
    (Q.concat = none → numberAdd A Q v w = .error (binopError "+" A.lt A.rt)) ∧
    (Q.repeatV = some g → Q.index w = some (.ok n) → ssizeMin ≤ n → n ≤ ssizeMax →
      numberMul A Q v w = g v n) ∧
    (Q.repeatV = none → Q.repeatW = some g → Q.index v = some (.ok n) → ssizeMin ≤ n → n ≤ ssizeMax →
      numberMul A Q v w = g w n) ∧
    (Q.repeatV = some g → Q.index w = some (.error e) → numberMul A Q v w = .error e) ∧
    (Q.repeatV = some g → Q.index w = none → (numberMul A Q v w).raises "TypeError") ∧
    (Q.repeatV = some g → Q.index w = some (.ok n) → n > ssizeMax →
      (numberMul A Q v w).raises "OverflowError") ∧
    (Q.repeatV = none → Q.repeatW = none → numberMul A Q v w = .error (binopError "*" A.lt A.rt))

theorem sequenceFallback_proven : SequenceFallback := by
  intro α A Q v w x n e f g h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1; simp [numberAdd, h, h1]
  · intro h1; simp [numberAdd, h, h1]
  · intro h1 h2 h3 h4
    have : ¬ (n > ssizeMax ∨ n < ssizeMin) := by omega
    simp [numberMul, h, h1, sequenceRepeat, h2, fitSsize, this]
  · intro h1 h2 h3 h4 h5
    have : ¬ (n > ssizeMax ∨ n < ssizeMin) := by omega
    simp [numberMul, h, h1, h2, sequenceRepeat, h3, fitSsize, this]
  · intro h1 h2
    simp [numberMul, h, h1, sequenceRepeat, h2]
  · intro h1 h2
    exact ⟨_, by simp [numberMul, h, h1, sequenceRepeat, h2]; rfl, rfl⟩
  · intro h1 h2 h3
    have : n > ssizeMax ∨ n < ssizeMin := Or.inl h3
    exact ⟨_, by simp [numberMul, h, h1, sequenceRepeat, h2, fitSsize, this]; rfl, rfl⟩
  · intro h1 h2
    simp [numberMul, h, h1, h2]

/-- `**` is `binary_op1` with the message of `pow`, and `**=` tries `__ipow__` first, with its own message. -/
def PowerDispatch : Prop :=
  ∀ (α : Type) (A : BinArgs α) (v w x : α) (f : α → α → Py (Ret α)) (e : PyExc),
    binaryOp1 A v w = .ok .notImplemented →
    numberPow A v w = .error (binopError "** or pow()" A.lt A.rt) ∧
    inplacePow none A v w = .error (binopError "**=" A.lt A.rt) ∧
    (f v w = .ok (.val x) → inplacePow (some f) A v w = .ok x) ∧
    (f v w = .error e → inplacePow (some f) A v w = .error e) ∧
    (f v w = .ok .notImplemented → inplacePow (some f) A v w = .error (binopError "**=" A.lt A.rt))

theorem powerDispatch_proven : PowerDispatch := by
  intro α A v w x f e h
  have hb : ∀ s, binaryOp A s v w = .error (binopError s A.lt A.rt) := by
    intro s
    simp [binaryOp, h]
  refine ⟨hb _, hb _, ?_, ?_, ?_⟩
  · intro h1; simp [inplacePow, h1]
  · intro h1; simp [inplacePow, h1]
  · intro h1
    simp only [inplacePow, h1]
    exact hb _

/-- The in-place operators: `__iop__` answers first, its `NotImplemented` falls back to the binary operator, whose
message then has the `=`. Language reference on augmented assignment. The same holds for `+=` with the sequence
slots, and `sq_inplace_concat` goes before `sq_concat`. -/
def InplaceFallback : Prop :=
  ∀ (α : Type) (A : BinArgs α) (Q : SeqArgs α) (sym : String) (v w x : α) (f : α → α → Py (Ret α))
    (c d : α → α → Py α),
    (f v w = .ok (.val x) → inplaceOp (some f) A sym v w = .ok x) ∧
    (f v w = .ok .notImplemented → inplaceOp (some f) A sym v w = inplaceOp none A sym v w) ∧
    (inplaceOp none A sym v w = binaryOp A sym v w) ∧
    (f v w = .ok (.val x) → inplaceAdd (some f) A Q v w = .ok x) ∧
    (binaryOp1 A v w = .ok .notImplemented → Q.hasV = true → Q.iconcat = some c →
      inplaceAdd none A Q v w = c v w) ∧
    (binaryOp1 A v w = .ok .notImplemented → Q.hasV = true → Q.iconcat = none → Q.concat = some d →
      inplaceAdd none A Q v w = d v w)

theorem inplaceFallback_proven : InplaceFallback := by
  intro α A Q sym v w x f c d
  refine ⟨?_, ?_, rfl, ?_, ?_, ?_⟩
  · intro h; simp [inplaceOp, binaryIop1, h]
  · intro h; simp [inplaceOp, binaryIop1, h]
  · intro h; simp [inplaceAdd, binaryIop1, h]
  · intro h h1 h2; simp [inplaceAdd, binaryIop1, h, h1, h2]
  · intro h h1 h2 h3; simp [inplaceAdd, binaryIop1, h, h1, h2, h3]

/-- `a *= b` is `a = a * b` when `a` has no `__imul__`, whatever `b` is. The language reference: "An augmented
assignment evaluates the target ... then assigns", and the fallback described at `__imul__`: "if `x` has no
`__imul__`, `x * y` is tried". False: `PyNumber_InPlaceMultiply` reaches the right operand's `sq_repeat` only under
`else if (mw != NULL)`, so only when the left type has no `tp_as_sequence`; every heap class has one. `x = I(2); x *=
[1]` raises `TypeError` for `class I(int): pass`, while `x * [1]` works. -/
def ImulIsMul : Prop :=
  ∀ (A : BinArgs Nat) (Q : SeqArgs Nat) (v w : Nat), (inplaceMul none A Q v w).toBool = (numberMul A Q v w).toBool

/-- The left is an instance of a heap class with `__index__` and no `__mul__`, the right a list. -/
def imulExample : BinArgs Nat × SeqArgs Nat :=
  (⟨none, none, false, false, "I", "list"⟩,
   ⟨none, none, none, none, some (fun _ n => .ok n.toNat), true, true,
    fun x => if x = 0 then some (.ok 2) else none, fun _ => "I"⟩)

theorem imulIsMul_refuted : ¬ImulIsMul := by
  intro h
  have := h imulExample.1 imulExample.2 0 1
  revert this
  decide

/-- `*=` as `*` in the other cases: the left type has no sequence methods at all, as `int` has not, or it has its
own repeat. The narrowing is the case refuted above, and `sq_inplace_repeat` goes before `sq_repeat`. -/
def ImulFallback : Prop :=
  ∀ (α : Type) (A : BinArgs α) (Q : SeqArgs α) (v w : α) (g : α → Int → Py α),
    binaryOp1 A v w = .ok .notImplemented →
    (Q.hasV = false → Q.repeatV = none → Q.hasW = true → Q.repeatW = some g →
      inplaceMul none A Q v w = numberMul A Q v w) ∧
    (Q.hasV = true → Q.irepeatV = none → Q.repeatV = some g → inplaceMul none A Q v w = numberMul A Q v w) ∧
    (Q.hasV = true → Q.irepeatV = some g → inplaceMul none A Q v w = sequenceRepeat Q g v w)

theorem imulFallback_proven : ImulFallback := by
  intro α A Q v w g h
  refine ⟨?_, ?_, ?_⟩
  · intro h1 h2 h3 h4; simp [inplaceMul, numberMul, binaryIop1, h, h1, h2, h3, h4]
  · intro h1 h2 h3; simp [inplaceMul, numberMul, binaryIop1, h, h1, h2, h3]
  · intro h1 h2; simp [inplaceMul, binaryIop1, h, h1, h2]

/-! ### Comparison -/

/-- `do_richcompare`, the body of `operator.lt` and the others in both twins, for every operator. The result is
the method's own object, not a `bool`. The right operand's reflected method goes first when it is of a strict
subclass, whether it overrides or not, and otherwise after the left; the reflected call has the operator
swapped and the operands reversed; an exception stops the search. With no answer `==` and `!=` are identity,
and the orderings raise `TypeError`. Data model on rich comparison. -/
def RichCompareOrder : Prop :=
  ∀ (α : Type) (A : CmpArgs α) (op : RichOp) (v w x : α) (l r : RichOp → α → α → Py (Ret α)) (e : PyExc),
    A.rv = some l → A.rw = some r →
    (A.sameType = false → A.subtype = true → r op.swapped w v = .ok (.val x) →
      richCompare A op v w = .ok x) ∧
    (A.sameType = false → A.subtype = true → r op.swapped w v = .ok .notImplemented →
      l op v w = .ok (.val x) → richCompare A op v w = .ok x) ∧
    (A.subtype = false → l op v w = .ok (.val x) → richCompare A op v w = .ok x) ∧
    (A.subtype = false → l op v w = .ok .notImplemented → r op.swapped w v = .ok (.val x) →
      richCompare A op v w = .ok x) ∧
    (A.subtype = false → l op v w = .error e → richCompare A op v w = .error e) ∧
    (A.subtype = false → l op v w = .ok .notImplemented → r op.swapped w v = .ok .notImplemented →
      (op = .eq → richCompare A op v w = .ok (A.ofBool A.identical)) ∧
      (op = .ne → richCompare A op v w = .ok (A.ofBool (!A.identical))) ∧
      (op = .lt → (richCompare A op v w).raises "TypeError"))

theorem richCompareOrder_proven : RichCompareOrder := by
  intro α A op v w x l r e h1 h2
  have hs : A.rw.isSome = true := by simp [h2]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h3 h4 h5; simp [richCompare, h1, h2, h3, h4, h5]
  · intro h3 h4 h5 h6; simp [richCompare, h1, h2, h3, h4, h5, h6]
  · intro h3 h4; simp [richCompare, h1, h2, h3, h4]
  · intro h3 h4 h5; simp [richCompare, h1, h2, h3, h4, h5]
  · intro h3 h4; simp [richCompare, h1, h2, h3, h4]
  · intro h3 h4 h5
    refine ⟨?_, ?_, ?_⟩
    · intro h; subst h; simp [richCompare, h1, h2, h3, h4, h5]
    · intro h; subst h; simp [richCompare, h1, h2, h3, h4, h5]
    · intro h
      subst h
      exact ⟨_, by simp [richCompare, h1, h2, h3, h4, h5]; rfl, rfl⟩

/-- The default `__eq__` and `__ne__`: `==` answers only for one object, and `!=` delegates to `__eq__` and inverts
the truth of its result, keeping `NotImplemented`. The data model's "By default, `__ne__()` delegates to
`__eq__()` and inverts the result unless it is `NotImplemented`". -/
def ObjectCompare : Prop :=
  ∀ (α : Type) (ofBool : Bool → α) (identical : Bool) (eq : Py (Ret α)) (truth : α → Py Bool) (r : α)
    (b : Bool) (e : PyExc),
    (objectRichcompare identical ofBool eq truth .eq =
      if identical then .ok (.val (ofBool true)) else .ok .notImplemented) ∧
    (eq = .ok (.val r) → truth r = .ok b →
      objectRichcompare identical ofBool eq truth .ne = .ok (.val (ofBool (!b)))) ∧
    (eq = .ok (.val r) → truth r = .error e → objectRichcompare identical ofBool eq truth .ne = .error e) ∧
    (eq = .ok .notImplemented → objectRichcompare identical ofBool eq truth .ne = .ok .notImplemented) ∧
    objectRichcompare identical ofBool eq truth .lt = .ok .notImplemented

theorem objectCompare_proven : ObjectCompare := by
  intro α ofBool identical eq truth r b e
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · intro h1 h2; simp [objectRichcompare, h1, h2]
  · intro h1 h2; simp [objectRichcompare, h1, h2]
  · intro h1; simp [objectRichcompare, h1]

/-! ### Truth -/

/-- `truth` and `not_`, for every kind of object: `True`, `False` and `None` by identity; `__bool__`, whose exception
propagates and which must return a `bool`; `__len__`, which must fit and not be negative; true otherwise. `not_`
gives the negation with the same exception, on all of them. Language reference, truth value testing. -/
def TruthProtocol : Prop :=
  ∀ (o : TruthObj) (n : Int) (tn : String) (e : PyExc),
    (∀ b, truthOp o = .ok b → notOp o = .ok (!b)) ∧
    (truthOp o = .error e → notOp o = .error e) ∧
    (truthOp (.len (.ok n)) = .ok (decide (n > 0)) ∨ n < 0 ∨ n > ssizeMax) ∧
    (n < 0 → (truthOp (.len (.ok n))).raises "ValueError") ∧
    (n > ssizeMax → (truthOp (.len (.ok n))).raises "OverflowError") ∧
    (truthOp (.badBool tn)).raises "TypeError" ∧ (truthOp (.noneBool tn)).raises "TypeError" ∧
    truthOp .plain = .ok true ∧ truthOp .none = .ok false

theorem truthProtocol_proven : TruthProtocol := by
  intro o n tn e
  refine ⟨?_, ?_, ?_, ?_, ?_, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl, rfl⟩
  · intro b h
    simp only [truthOp] at h
    simp [notOp, h]
  · intro h
    simp only [truthOp] at h
    simp [notOp, h]
  · by_cases h1 : n < 0
    · exact Or.inr (Or.inl h1)
    · by_cases h2 : n > ssizeMax
      · exact Or.inr (Or.inr h2)
      · left
        have h3 : ¬ (n > ssizeMax ∨ n < ssizeMin) := by
          unfold ssizeMin at *
          unfold ssizeMax at *
          omega
        simp [truthOp, isTrue, sqLength, fitSsize, h3, h1]
  · intro h
    exact ⟨_, by simp [truthOp, isTrue, sqLength, h]; rfl, rfl⟩
  · intro h
    have h3 : n > ssizeMax ∨ n < ssizeMin := Or.inl h
    have h4 : ¬ n < 0 := by
      unfold ssizeMax at h
      omega
    exact ⟨_, by simp [truthOp, isTrue, sqLength, fitSsize, h3, h4]; rfl, rfl⟩

/-! ### `index`, unary operators -/

/-- `operator.index` agrees in the twins on an `int`, and on an object whose type's `__index__` returns an exact
`int` or raises, with nothing in the instance. The cases left out are refuted next. -/
def IndexTwinsLawful : Prop :=
  ∀ o : IndexObj, o.inst = none → (∀ n, o.slot ≠ some (.ok (.sub n))) → (∀ tn, o.slot ≠ some (.ok (.other tn))) →
    o.slot.isSome = true ∨ o.isInt.isSome = true → indexC o = indexPy o

theorem indexTwinsLawful_proven : IndexTwinsLawful := by
  intro o h1 h2 h3 h4
  simp only [indexC, indexPy, h1]
  cases hi : o.isInt with
  | some n => rfl
  | none =>
    cases hs : o.slot with
    | none => simp [hi, hs] at h4
    | some r =>
      cases r with
      | error e => rfl
      | ok v =>
        cases v with
        | exact n => rfl
        | sub n => exact absurd hs (h2 n)
        | other tn => exact absurd hs (h3 tn)

/-- `operator.index` is one function, whichever twin runs. False, four ways, all of which follow from the Python
twin being the literal `a.__index__()`: no `__index__` is `AttributeError` against `TypeError`; a result that is
not an `int` comes back from Python and is a `TypeError` in C; a result of an `int` subclass comes back
as it is from Python, and as an exact `int` with a `DeprecationWarning` from C; an `__index__` in the instance
dict is used by Python and ignored by C. -/
def IndexTwinsAlways : Prop := ∀ o : IndexObj, indexC o = indexPy o

theorem indexTwinsAlways_refuted : ¬IndexTwinsAlways := by
  intro h
  have := h ⟨none, some (.ok (.other "str")), none, "X", none⟩
  revert this
  simp [indexC, indexPy]

/-- The unary operators: the slot's result, or its exception, or a `TypeError` naming the operation and the type,
for each of `-`, `+`, `abs` and `~`. -/
def UnaryOps : Prop :=
  ∀ (α : Type) (f : α → Py α) (op : UnOp) (tn : String) (v : α),
    unaryOp (some f) op tn v = f v ∧
    unaryOp none op tn v = .error (.typeError s!"bad operand type for {op.desc}: '{tn}'")

theorem unaryOps_proven : UnaryOps := fun _ _ _ _ _ => ⟨rfl, rfl⟩

/-! ### Subscripts -/

/-- `a[b]`: `mp_subscript` wins; then `sq_item`, with the key through `__index__`, an `IndexError` when it does not
fit, and a negative index adjusted by `sq_length`, whose exception propagates; a class goes through
`__class_getitem__`; and each other case is a `TypeError`. -/
def GetItemProtocol : Prop :=
  ∀ (α : Type) (A : GetArgs α) (f : Int → Py α) (i n : Int) (r : Py α) (e : PyExc),
    (A.mp = some r → getItem A = r) ∧
    (A.mp = none → A.sqItem = some f → A.keyIndex = some (.ok i) → 0 ≤ i → i ≤ ssizeMax → getItem A = f i) ∧
    (A.mp = none → A.sqItem = some f → A.keyIndex = some (.ok i) → i < 0 → ssizeMin ≤ i →
      A.sqLen = some (.ok n) → getItem A = f (i + n)) ∧
    (A.mp = none → A.sqItem = some f → A.keyIndex = some (.ok i) → i < 0 → ssizeMin ≤ i →
      A.sqLen = some (.error e) → getItem A = .error e) ∧
    (A.mp = none → A.sqItem = some f → A.keyIndex = some (.ok i) → i > ssizeMax →
      (getItem A).raises "IndexError") ∧
    (A.mp = none → A.sqItem = some f → A.keyIndex = none → (getItem A).raises "TypeError") ∧
    (A.mp = none → A.sqItem = none → A.asType = none → (getItem A).raises "TypeError") ∧
    (A.mp = none → A.sqItem = none → A.asType = some (.ok none) → (getItem A).raises "TypeError")

theorem getItemProtocol_proven : GetItemProtocol := by
  intro α A f i n r e
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [getItem, h]
  · intro h1 h2 h3 h4 h5
    have h6 : ¬ (i > ssizeMax ∨ i < ssizeMin) := by
      unfold ssizeMin at *
      unfold ssizeMax at *
      omega
    have h7 : ¬ i < 0 := by omega
    simp [getItem, h1, h2, h3, fitSsize, h6, sequenceGetItem, h7]
  · intro h1 h2 h3 h4 h5 h6
    have h7 : ¬ (i > ssizeMax ∨ i < ssizeMin) := by
      unfold ssizeMin at *
      unfold ssizeMax at *
      omega
    simp [getItem, h1, h2, h3, fitSsize, h7, sequenceGetItem, h4, h6]
  · intro h1 h2 h3 h4 h5 h6
    have h7 : ¬ (i > ssizeMax ∨ i < ssizeMin) := by
      unfold ssizeMin at *
      unfold ssizeMax at *
      omega
    simp [getItem, h1, h2, h3, fitSsize, h7, sequenceGetItem, h4, h6]
  · intro h1 h2 h3 h4
    have h7 : i > ssizeMax ∨ i < ssizeMin := Or.inl h4
    exact ⟨_, by simp [getItem, h1, h2, h3, fitSsize, h7]; rfl, rfl⟩
  · intro h1 h2 h3
    exact ⟨_, by simp [getItem, h1, h2, h3]; rfl, rfl⟩
  · intro h1 h2 h3
    exact ⟨_, by simp [getItem, h1, h2, h3]; rfl, rfl⟩
  · intro h1 h2 h3
    exact ⟨_, by simp [getItem, h1, h2, h3]; rfl, rfl⟩

/-- `a[b] = c` and `del a[b]`: `mp_ass_subscript` wins; a sequence takes the key through `__index__` and adjusts a
negative one; a sequence without assignment, as `tuple`, says that it does not support it, in the wording of the
function that noticed. The two differ in that wording: `PyObject_DelItem` says "does not support item deletion"
and `PySequence_DelItem` "doesn't". -/
def SetDelProtocol : Prop :=
  ∀ (σ : Type) (A : SetArgs σ) (f : Int → Py σ) (r : Py σ) (i n : Int),
    (A.mp = some r → setItem A = r ∧ delItem A = r) ∧
    (A.mp = none → A.hasSeq = true → A.sqAss = some f → A.keyIndex = some (.ok i) → 0 ≤ i → i ≤ ssizeMax →
      setItem A = f i ∧ delItem A = f i) ∧
    (A.mp = none → A.hasSeq = true → A.sqAss = some f → A.keyIndex = some (.ok i) → i < 0 → ssizeMin ≤ i →
      A.sqLen = some (.ok n) → setItem A = f (i + n)) ∧
    (A.mp = none → A.hasSeq = false →
      setItem A = .error (objMsg A.tn "does not support item assignment") ∧
      delItem A = .error (objMsg A.tn "does not support item deletion")) ∧
    (A.mp = none → A.hasSeq = true → A.sqAss = none → A.keyIndex = some (.ok i) → ssizeMin ≤ i → i ≤ ssizeMax →
      delItem A = .error (objMsg A.tn "doesn't support item deletion")) ∧
    (A.mp = none → A.hasSeq = true → A.sqAss = some f → A.keyIndex = none →
      (setItem A).raises "TypeError" ∧ (delItem A).raises "TypeError")

theorem setDelProtocol_proven : SetDelProtocol := by
  intro σ A f r i n
  have fit : ∀ (mk : String → PyExc) (t : String), ssizeMin ≤ i → i ≤ ssizeMax → fitSsize mk t i = .ok i := by
    intro mk t h1 h2
    have : ¬ (i > ssizeMax ∨ i < ssizeMin) := by
      unfold ssizeMin at *
      unfold ssizeMax at *
      omega
    simp [fitSsize, this]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h; simp [setItem, delItem, assignItem, h]
  · intro h1 h2 h3 h4 h5 h6
    have h7 : ssizeMin ≤ i := by
      unfold ssizeMin
      omega
    have h8 : ¬ i < 0 := by omega
    simp [setItem, delItem, assignItem, h1, h2, h3, h4, fit _ _ h7 h6, sequenceSet, h8]
  · intro h1 h2 h3 h4 h5 h6 h7
    have h8 : i ≤ ssizeMax := by
      unfold ssizeMax
      omega
    simp [setItem, assignItem, h1, h2, h3, h4, fit _ _ h6 h8, sequenceSet, h5, h7]
  · intro h1 h2
    simp only [setItem, delItem, assignItem, h1, h2, Bool.false_eq_true, ite_false]
    simp
  · intro h1 h2 h3 h4 h5 h6
    simp only [delItem, assignItem, h1, h2, h3, h4, fit _ _ h5 h6, sequenceSet, ite_true]
  · intro h1 h2 h3 h4
    exact ⟨⟨_, by simp [setItem, assignItem, h1, h2, h3, h4]; rfl, rfl⟩,
      ⟨_, by simp [delItem, assignItem, h1, h2, h3, h4]; rfl, rfl⟩⟩

/-! ### `concat` -/

/-- `concat` in C and Python agree for user sequences, the case the fallback at
Objects/abstract.c:1725-1733 exists for: neither has a sequence slot and both operands are sequences,
so both call `nb_add`; both raise `TypeError` without an answer. -/
def ConcatTwinsOnUserSequences : Prop :=
  ∀ (α : Type) (A : ConcatArgs α) (lt rt : String) (a b : α) (x : α),
    A.sqConcat = none → A.hasGetitem = true → A.seqA = true → A.seqB = true →
    A.nbAdd a b = .ok (.val x) → concatC A lt a b = .ok x ∧ concatPy A lt rt a b = .ok x

theorem concatTwinsOnUserSequences_proven : ConcatTwinsOnUserSequences := by
  intro α A lt rt a b x h1 h2 h3 h4 h5
  constructor
  · simp [concatC, h1, h3, h4, h5, bind, Except.bind, pure, Except.pure]
  · simp [concatPy, plus, h2, h5, bind, Except.bind, pure, Except.pure]

/-- `operator.concat(a, b)` is `a + b` for sequences, the docstring's "Same as a + b, for a and b
sequences". False: C calls `a`'s `sq_concat` first, while `a + b` tries `nb_add`, which reaches the
reflected `__radd__` of `b`, so `operator.concat([1], UserList([2]))` raises `TypeError` where
`[1] + UserList([2])` works. python/cpython#73325 defends the C behaviour for a non-sequence left
operand, so this records the twin difference and is not a report. -/
def ConcatIsPlus : Prop :=
  ∀ (A : ConcatArgs Nat) (lt rt : String) (a b : Nat), A.seqA = true → A.seqB = true →
    concatC A lt a b = plus A lt rt a b

theorem concatIsPlus_refuted : ¬ConcatIsPlus := by
  intro h
  let A : ConcatArgs Nat :=
    ⟨true, some (fun _ _ => .error (.typeError "x")), none, true, true,
      fun _ _ => .ok (.val 7), fun _ _ => .ok (.val 7)⟩
  have := h A "list" "X" 0 0 rfl rfl
  simp [A, concatC, plus, bind, Except.bind, pure, Except.pure] at this


/-! ### Iteration -/

theorem countLoop_add {α : Type} (same : Same α) (b : α) (e : Option PyExc) :
    ∀ (xs : List α) (n m : Nat), countLoop same b (n + m) xs e =
      (countLoop same b n xs e).map (· + m)
  | [], n, m => by cases e <;> rfl
  | x :: xs, n, m => by
    simp only [countLoop]
    cases same x b with
    | error e' => rfl
    | ok hit =>
      simp only
      cases hit
      · simpa using countLoop_add same b e xs n m
      · have := countLoop_add same b e xs (n + 1) m
        simpa [Nat.add_right_comm] using this

theorem countLoop_spec {α : Type} [DecidableEq α] (b : α) : ∀ (xs : List α) (n : Nat),
    countLoop (fun x y => .ok (decide (x = y))) b n xs none = .ok (n + (xs.filter (· = b)).length)
  | [], n => rfl
  | x :: xs, n => by
    by_cases h : x = b
    · have := countLoop_spec b xs (n + 1)
      simp only [countLoop, h, decide_true, ite_true, List.filter_cons, List.length_cons, this]
      congr 1
      omega
    · have := countLoop_spec b xs n
      simp [countLoop, h, this, List.filter_cons]

theorem indexLoop_absent {α : Type} [DecidableEq α] (b : α) : ∀ (xs : List α) (i : Nat), b ∉ xs →
    indexLoop (fun x y => .ok (decide (x = y))) b i xs none = .error (.valueError indexMsg)
  | [], _, _ => rfl
  | x :: xs, i, h => by
    have h1 : x ≠ b := fun e => h (by simp [e])
    have h2 : b ∉ xs := fun e => h (by simp [e])
    simp [indexLoop, h1, indexLoop_absent b xs (i + 1) h2]

theorem indexLoop_found {α : Type} [DecidableEq α] (b : α) : ∀ (pre post : List α) (i : Nat), b ∉ pre →
    indexLoop (fun x y => .ok (decide (x = y))) b i (pre ++ b :: post) none = .ok (i + pre.length)
  | [], post, i, _ => by simp [indexLoop]
  | x :: xs, post, i, h => by
    have h1 : x ≠ b := fun e => h (by simp [e])
    have h2 : b ∉ xs := fun e => h (by simp [e])
    simp only [List.cons_append, indexLoop, h1, decide_false, indexLoop_found b xs post (i + 1) h2,
      List.length_cons]
    congr 1
    omega

/-- `countOf` and `indexOf`: the twins run one loop. They agree on every iterator, every comparison, raising or
not, and every position of a failure; only the message for an object that is not iterable differs. With a
comparison that does not raise, `countOf` counts the matches, and `indexOf` finds the first and raises
`ValueError` when there is none. Docs of `countOf` and `indexOf`. -/
def CountAndIndex : Prop :=
  ∀ (α : Type) [DecidableEq α] (same : Same α) (tn : String) (b : α) (xs : List α) (e : Option PyExc)
    (pre post : List α),
    countOfC same tn b (.items xs e) = countOfPy same b (.items xs e) ∧
    indexOfC same tn b (.items xs e) = indexOfPy same b (.items xs e) ∧
    (let eq : Same α := fun x y => .ok (decide (x = y))
     countOfPy eq b (.items xs none) = .ok (xs.filter (· = b)).length ∧
     (b ∉ xs → indexOfPy eq b (.items xs none) = .error (.valueError indexMsg)) ∧
     (b ∉ pre → indexOfPy eq b (.items (pre ++ b :: post) none) = .ok pre.length))

theorem countAndIndex_proven : CountAndIndex := by
  intro α _ same tn b xs e pre post
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · have := countLoop_spec b xs 0
    simpa [countOfPy] using this
  · intro h; exact indexLoop_absent b xs 0 h
  · intro h
    have := indexLoop_found b pre post 0 h
    simpa [indexOfPy] using this

/-- The `TypeError` of a non-iterable: `iter` fails in both; C replaces the message, and only a `TypeError`'s, so
a non-`TypeError` from `__iter__` comes through unchanged in both twins. `__contains__` wins over iteration. -/
def IterErrors : Prop :=
  ∀ (α : Type) (same : Same α) (tn m : String) (b : α) (e : PyExc) (r : Py Bool) (a : IterArg α),
    countOfC same tn b (.fail (.typeError m)) = .error (.typeError s!"argument of type '{tn}' is not iterable") ∧
    indexOfC same tn b (.fail (.valueError m)) = indexOfPy same b (.fail (.valueError m)) ∧
    containsOp none same tn b (.fail (.typeError m)) =
      .error (.typeError s!"argument of type '{tn}' is not a container or iterable") ∧
    containsOp (some r) same tn b a = r

theorem iterErrors_proven : IterErrors := fun _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

/-- `contains` by iteration stops at the first match, so it does not read the rest, nor notice a later failure; it
says true exactly when `indexOf` finds something, for any comparison. -/
def ContainsIsIndexOf : Prop :=
  ∀ (α : Type) (same : Same α) (b : α) (xs : List α) (e : Option PyExc) (i : Nat),
    (containsLoop same b xs e = .ok true ↔ ∃ n, indexLoop same b i xs e = .ok n)

theorem containsIsIndexOf_proven : ContainsIsIndexOf := by
  intro α same b xs e
  induction xs with
  | nil => intro i; cases e <;> simp [containsLoop, indexLoop]
  | cons x xs ih =>
    intro i
    simp only [containsLoop, indexLoop]
    cases same x b with
    | error e' => simp
    | ok hit =>
      cases hit with
      | true => simp
      | false => exact ih (i + 1)

/-- `operator.call`: both twins run the callable with the rest, keywords kept, and both raise `TypeError` for no
callable at all, with different messages. -/
def CallTwins : Prop :=
  ∀ (α β : Type) (f : α → List α → List (String × α) → Py β) (o : α) (rest : List α) (kw : List (String × α)),
    callC f (o :: rest) kw = f o rest kw ∧ callPy f (o :: rest) kw = f o rest kw ∧
    (callC f [] kw).raises "TypeError" ∧ (callPy f [] kw).raises "TypeError"

theorem callTwins_proven : CallTwins := fun _ _ _ _ _ _ => ⟨rfl, rfl, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩

/-! ### `length_hint` -/

/-- `length_hint` agrees between the twins for an `int` default and hint that fit in `Py_ssize_t`, and
a hint that is not an `int`: the result, or the same exception class. Outside that range C raises
`OverflowError` where Python returns the value, and C accepts an `__index__` default Python rejects;
these follow from the C signature and are recorded here in the hypotheses. -/
def LengthHintTwins : Prop :=
  ∀ (o : HintObj) (d : Int), ssizeMin ≤ d → d ≤ ssizeMax →
    (∀ h, o.hint = some h → ∀ v, h = .ok (.int v) → ssizeMin ≤ v ∧ v ≤ ssizeMax) →
    (∀ h, o.hint = some h → ∀ tn, h ≠ .ok (.other tn)) →
    lengthHintC o (.int d) = lengthHintPy o (.int d)

theorem lengthHintTwins_proven : LengthHintTwins := by
  intro o d h1 h2 hr hn
  have hd : toSsize d = .ok d := by
    unfold toSsize ssizeMax ssizeMin at *
    rw [if_neg (by omega)]
  simp only [lengthHintC, lengthHintPy, hd, bind, Except.bind, pure, Except.pure]
  cases hl : o.len with
  | ok n => rfl
  | error e =>
    cases ht : isTypeError e with
    | false => simp [hl, ht, throw, throwThe, MonadExcept.throw, MonadExceptOf.throw]
    | true =>
      simp only [ht, Bool.not_true, Bool.false_eq_true, ite_false]
      cases hh : o.hint with
      | none => rfl
      | some h =>
        cases h with
        | error e2 => rfl
        | ok v =>
          cases v with
          | notImplemented => rfl
          | other tn => exact absurd rfl (hn _ hh tn)
          | int v =>
            have hv := hr _ hh v rfl
            have : toSsize v = .ok v := by
              unfold toSsize ssizeMax ssizeMin at *
              rw [if_neg (by omega)]
            simp [this, bind, Except.bind]

/-! ### `_compare_digest` -/

theorem or_zero_iff (a b : Nat) : a ||| b = 0 ↔ a = 0 ∧ b = 0 := Nat.or_eq_zero_iff

theorem xor_zero_iff (x y : Nat) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all
  · rintro rfl
    exact Nat.xor_self _

theorem tscmpLoop_zero : ∀ (r : Nat) (a b : List Nat), a.length = b.length →
    (tscmpLoop r a b = 0 ↔ r = 0 ∧ a = b)
  | r, [], [], _ => by simp [tscmpLoop]
  | r, x :: xs, y :: ys, h => by
    have ih := tscmpLoop_zero (r ||| (x ^^^ y)) xs ys (by simpa using h)
    simp only [tscmpLoop, ih, or_zero_iff, List.cons.injEq, xor_zero_iff]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, b, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, b⟩, c⟩

/-- `_tscmp` answers whether the two byte strings are equal, for all lengths, with the unequal-length
path starting from a nonzero result so it cannot answer `True`. `compare_digest` docs: "Return a == b".
Non-ASCII `str` arguments raise `TypeError`. -/
def CompareDigestCorrect : Prop :=
  ∀ (a b : List Nat), tscmp a b = decide (a = b) ∧
    (compareDigest (.str false a) (.str true b)).raises "TypeError"

theorem compareDigestCorrect_proven : CompareDigestCorrect := by
  intro a b
  refine ⟨?_, ⟨_, by simp [compareDigest]; rfl, rfl⟩⟩
  unfold tscmp
  by_cases h : a.length = b.length
  · have := tscmpLoop_zero 0 a b h
    simp only [h, ite_true]
    cases hd : decide (a = b) with
    | true =>
      have e : a = b := by simpa using hd
      simpa [e] using (tscmpLoop_zero 0 b b rfl).mpr ⟨rfl, rfl⟩
    | false =>
      have e : a ≠ b := by simpa using hd
      have : tscmpLoop 0 a b ≠ 0 := fun x => e ((this.mp x).2)
      simpa using this
  · have hne : a ≠ b := fun e => h (by rw [e])
    have hz : tscmpLoop 1 b b ≠ 0 := fun x => by
      have := ((tscmpLoop_zero 1 b b rfl).mp x).1
      omega
    simp [h, hne, hz]

end PyLean.CoreLibs.Operator
