import PyLean.CoreLibs.Operator.Model

/-!
Properties of `operator` / `_operator`, `copy` and `abc`.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-! ### Dispatch families -/

/-- The binary operators, the same in both twins since `operator.add` is `a + b` in Python and
`PyNumber_Add` in C: the right operand's reflected method goes first when its type is a proper subclass
that overrides it; otherwise the left method; `NotImplemented` moves to the other one; when neither
answers, `TypeError` names the operator and both types. Language reference, data model. -/
def BinaryDispatch : Prop :=
  ∀ (α : Type) (S : BinSlots α) (sym lt rt : String) (v w x : α),
    (S.left = none → S.right = none → binaryOp S sym lt rt v w = .error (unsupported sym lt rt)) ∧
    (∀ sv sw, S.left = some sv → S.right = some sw → S.rightIsSubtype = true →
      sw v w = .ok (.val x) → binaryOp S sym lt rt v w = .ok x) ∧
    (∀ sv, S.left = some sv → S.rightIsSubtype = false → sv v w = .ok (.val x) →
      binaryOp S sym lt rt v w = .ok x) ∧
    (∀ sv sw, S.left = some sv → S.right = some sw → S.rightIsSubtype = false →
      sv v w = .ok .notImplemented → sw v w = .ok (.val x) → binaryOp S sym lt rt v w = .ok x)

theorem binaryDispatch_proven : BinaryDispatch := by
  intro α S sym lt rt v w x
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h1 h2
    simp [binaryOp, binaryOp1, h1, h2, bind, Except.bind, throw, throwThe, MonadExcept.throw,
      MonadExceptOf.throw, pure, Except.pure]
  · intro sv sw h1 h2 h3 h4
    simp [binaryOp, binaryOp1, h1, h2, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro sv h1 h3 h4
    cases hr : S.right <;>
      simp [binaryOp, binaryOp1, h1, hr, h3, h4, bind, Except.bind, pure, Except.pure]
  · intro sv sw h1 h2 h3 h4 h5
    simp [binaryOp, binaryOp1, h1, h2, h3, h4, h5, bind, Except.bind, pure, Except.pure]

/-- The in-place operators: `__iop__` answers first, its `NotImplemented` falls back to the binary
operator, in both twins. Language reference on augmented assignment. -/
def InplaceFallback : Prop :=
  ∀ (α : Type) (S : BinSlots α) (sym lt rt : String) (v w x : α) (f : α → α → Py (Ret α)),
    (f v w = .ok (.val x) → inplaceOp (some f) S sym lt rt v w = .ok x) ∧
    (f v w = .ok .notImplemented → inplaceOp (some f) S sym lt rt v w =
      binaryOp S (sym ++ "=") lt rt v w) ∧
    inplaceOp none S sym lt rt v w = binaryOp S (sym ++ "=") lt rt v w

theorem inplaceFallback_proven : InplaceFallback := by
  intro α S sym lt rt v w x f
  refine ⟨?_, ?_, rfl⟩
  · intro h
    simp [inplaceOp, h, bind, Except.bind, pure, Except.pure]
  · intro h
    simp [inplaceOp, h, bind, Except.bind, pure, Except.pure]

/-- The comparison operators: when neither side answers, `==` and `!=` fall back to identity and the
four orderings raise `TypeError`, in both twins. Data model on rich comparison. -/
def CompareDefault : Prop :=
  ∀ (α : Type) (S : CmpSlots α) (same : Bool) (lt rt : String) (v w : α),
    S.left v w = .ok .notImplemented → S.right w v = .ok .notImplemented →
    richCompare S .eq same lt rt v w = .ok same ∧
    richCompare S .ne same lt rt v w = .ok (!same) ∧
    (richCompare S .lt same lt rt v w).raises "TypeError" ∧
    (richCompare S .ge same lt rt v w).raises "TypeError"

theorem compareDefault_proven : CompareDefault := by
  intro α S same lt rt v w h1 h2
  cases hs : S.rightIsSubtypeOverride <;>
    simp [richCompare, h1, h2, hs, bind, Except.bind, pure, Except.pure, Py.raises, throw, throwThe,
      MonadExcept.throw, MonadExceptOf.throw, PyExc.className]

/-- A class without the unary method raises `TypeError` for `-a`, `+a`, `abs(a)`, `~a`; with it, the
result is the method's. `not_` is the negation of `truth`, and `is_not` of `is_`. -/
def UnaryAndTruth : Prop :=
  ∀ (α : Type) (f : α → Py α) (desc tn : String) (v : α) (b : Py Bool),
    (unaryOp none desc tn v).raises "TypeError" ∧ unaryOp (some f) desc tn v = f v ∧
    not_ b = (do pure (!(← truth b)))

theorem unaryAndTruth_proven : UnaryAndTruth := fun _ _ _ _ _ _ => ⟨⟨_, rfl, rfl⟩, rfl, rfl⟩

/-- `operator.index` in C and Python agree on what has a valid `__index__`, and differ otherwise:
`AttributeError` against `TypeError` for no `__index__`, and Python returns a non-`int` result that C
rejects. The Python function is a plain `a.__index__()`, as its docstring says. -/
def IndexTwinsOnValid : Prop :=
  ∀ n : Int, indexC (.int n) = indexPy (.int n)

theorem indexTwinsOnValid_proven : IndexTwinsOnValid := fun _ => rfl

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

/-! ### `countOf`, `indexOf` -/

/-- `countOf` counts the items equal to `b`, and `indexOf` finds the first, raising `ValueError` when
there is none; the Python loop and `_PySequence_IterSearch` both run left to right and stop at the
first raising `__eq__`. Docs of `countOf` and `indexOf`. -/
def CountAndIndex : Prop :=
  ∀ (α : Type) [DecidableEq α] (b : α) (xs : List α),
    let same : Same α := fun x y => .ok (decide (x = y))
    countOf same b xs none = .ok (xs.filter (· = b)).length ∧
    (b ∉ xs → indexOf same b 0 xs none = .error (.valueError indexMsg)) ∧
    (∀ pre post, b ∉ pre → xs = pre ++ b :: post → indexOf same b 0 xs none = .ok pre.length)

theorem countOf_spec {α : Type} [DecidableEq α] (b : α) : ∀ xs : List α,
    countOf (fun x y => .ok (decide (x = y))) b xs none = .ok (xs.filter (· = b)).length
  | [] => rfl
  | x :: xs => by
    by_cases h : x = b
    · simp [countOf, h, countOf_spec b xs, bind, Except.bind, pure, Except.pure, List.filter_cons,
        Nat.add_comm]
    · simp [countOf, h, countOf_spec b xs, bind, Except.bind, pure, Except.pure, List.filter_cons]

theorem indexOf_absent {α : Type} [DecidableEq α] (b : α) : ∀ (xs : List α) (i : Nat), b ∉ xs →
    indexOf (fun x y => .ok (decide (x = y))) b i xs none = .error (.valueError indexMsg)
  | [], _, _ => rfl
  | x :: xs, i, h => by
    have h1 : x ≠ b := fun e => h (by simp [e])
    have h2 : b ∉ xs := fun e => h (by simp [e])
    simp [indexOf, h1, bind, Except.bind, indexOf_absent b xs (i + 1) h2]

theorem indexOf_found {α : Type} [DecidableEq α] (b : α) : ∀ (pre post : List α) (i : Nat), b ∉ pre →
    indexOf (fun x y => .ok (decide (x = y))) b i (pre ++ b :: post) none = .ok (i + pre.length)
  | [], post, i, _ => by
    simp [indexOf, bind, Except.bind, pure, Except.pure]
  | x :: xs, post, i, h => by
    have h1 : x ≠ b := fun e => h (by simp [e])
    have h2 : b ∉ xs := fun e => h (by simp [e])
    simp only [List.cons_append, indexOf, bind, Except.bind, h1, decide_false, Bool.false_eq_true,
      ite_false, indexOf_found b xs post (i + 1) h2, List.length_cons]
    congr 1
    omega

theorem countAndIndex_proven : CountAndIndex := by
  intro α _ b xs same
  refine ⟨countOf_spec b xs, indexOf_absent b xs 0, ?_⟩
  intro pre post h e
  subst e
  simpa using indexOf_found b pre post 0 h

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

/-! ### `itemgetter`, `attrgetter`, `methodcaller` -/

/-- The tuple fast path of `itemgetter_call_impl` gives what `obj[i]` gives, for every `int` index,
and `repr` is the same in both twins. Fast-path agreement. -/
def ItemgetterFastPath : Prop :=
  ∀ (α : Type) (xs : List α) (i : Int) (cls : String) (items : List String),
    itemgetterFast xs i (tupleGet xs) = tupleGet xs i ∧
    getterReprC cls items = getterReprPy cls items

theorem itemgetterFastPath_proven : ItemgetterFastPath := by
  intro α xs i cls items
  constructor
  · unfold itemgetterFast
    split
    · next h =>
      cases hg : xs[i.toNat]? with
      | none => rfl
      | some v =>
        have h0 : ¬ i < 0 := by omega
        have h1 : i < (xs.length : Int) := h.2
        simp [tupleGet, h0, h1, hg]
    · rfl
  · unfold getterReprC getterReprPy
    split <;> simp

/-- Dotted lookups compose: `attrgetter('a.b')` is `attrgetter('b')` applied to `attrgetter('a')`.
Non-`str` names are rejected, in the source's order. Docs of `attrgetter`. -/
def AttrgetterChain : Prop :=
  ∀ (α : Type) (ga : GetAttr α) (obj : α) (a b : List String),
    (dotted ga obj (a ++ b) = do dotted ga (← dotted ga obj a) b) ∧
    attrgetterNew [.other] = .error (.typeError attrNameMsg)

theorem dotted_append {α : Type} (ga : GetAttr α) : ∀ (obj : α) (a b : List String),
    dotted ga obj (a ++ b) = do dotted ga (← dotted ga obj a) b
  | _, [], _ => rfl
  | obj, n :: ns, b => by
    simp only [List.cons_append, dotted, bind, Except.bind]
    cases ga obj n with
    | error _ => rfl
    | ok v => simpa [bind, Except.bind] using dotted_append ga v ns b

theorem attrgetterChain_proven : AttrgetterChain :=
  fun _ ga obj a b => ⟨dotted_append ga obj a b, rfl⟩

/-- The vectorcall path of `methodcaller` calls the same method with the same arguments as the plain
path: the flattened form of positional and keyword arguments unflattens to them, for any count; the
vectorcall buffer of 8 is never overrun, and `__reduce__` keeps the constructor arguments. Fast-path
agreement. Type invariant: keyword names are distinct, which is not needed here. -/
def MethodcallerVectorcall : Prop :=
  ∀ (α : Type) (name : String) (args : List α) (kw : List (String × α)) (nm : α),
    unflatten name (vectorcallArgs args kw).1 (vectorcallArgs args kw).2 = ⟨name, args, kw⟩ ∧
    (usesVectorcall args.length kw.length = true → 1 + args.length + kw.length ≤ 8) ∧
    methodcallerReduce nm args [] = .plain (nm :: args) ∧
    methodcallerNewC (some .other) = methodcallerNewPy (some .other) ∧
    (∀ s, methodcallerNewC (some (.str s)) = methodcallerNewPy (some (.str s)))

theorem zip_map_fst_snd {α : Type} : ∀ kw : List (String × α),
    (kw.map Prod.fst).zip (kw.map Prod.snd) = kw
  | [] => rfl
  | (a, b) :: rest => by simp [zip_map_fst_snd rest]

theorem methodcallerVectorcall_proven : MethodcallerVectorcall := by
  intro α name args kw nm
  refine ⟨?_, ?_, rfl, rfl, fun _ => rfl⟩
  · simp only [vectorcallArgs, unflatten]
    have hl : (args ++ kw.map Prod.snd).length - (kw.map Prod.fst).length = args.length := by
      simp
    rw [hl]
    simp [zip_map_fst_snd]
  · intro h
    simp [usesVectorcall] at h
    omega

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

/-! ### `copy` -/

/-- `deepcopy` keeps atoms, answers from the memo without touching the heap, and returns a tuple of
atoms itself rather than a copy, the identity-preserving path of `_deepcopy_tuple`. A self-referencing
list copies to a new self-referencing list. `copy` docs: "keeping a memo dictionary". -/
def DeepcopyMemo : Prop :=
  (∀ (fuel : Nat) (h : Heap) (x : Nat) (n : Int), h.get x = .atom n →
    deepcopy (fuel + 1) h x = .ok (h, x)) ∧
  (∀ (fuel : Nat) (h : Heap) (x y : Nat) (c : Cell), h.get x = c → (∀ n, c ≠ .atom n) →
    h.memo.lookup x = some y → deepcopy (fuel + 1) h x = .ok (h, y)) ∧
  deepcopy 4 ⟨[.list [0]], []⟩ 0 = .ok (⟨[.list [0], .list [1]], [(0, 1)]⟩, 1) ∧
  deepcopy 4 ⟨[.atom 1, .tuple [0]], []⟩ 1 = .ok (⟨[.atom 1, .tuple [0]], []⟩, 1)

theorem deepcopyMemo_proven : DeepcopyMemo := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · intro fuel h x n hc
    simp [deepcopy, hc]
  · intro fuel h x y c hc hna hm
    cases hg : h.get x with
    | atom n => exact absurd (hc ▸ hg) (hna n)
    | list items => simp [deepcopy, hg, hm]
    | tuple items => simp [deepcopy, hg, hm]
    | dict items => simp [deepcopy, hg, hm]

/-- `copy` handles what `__reduce__` may return: a string, and a tuple of two to five items.
`_reconstruct` applies the state before the list and dict items. -/
def CopyRoutes : Prop :=
  copyRoute .atomic = .ok "same" ∧ copyRoute .builtinContainer = .ok "cls.copy" ∧
  copyRoute .isType = .ok "same" ∧ copyRoute .hasCopy = .ok "__copy__" ∧
  copyRoute .reduceStr = .ok "same" ∧
  (∀ n, 2 ≤ n → n ≤ 5 → copyRoute (.reduceTuple n) = .ok "reconstruct") ∧
  (∀ (d s t : List (String × Nat)), stateStep (some s) (some t) d = d ++ s ++ t) ∧
  replaceRoute false "X" = .error (.typeError "replace() does not support X objects")

theorem copyRoutes_proven : CopyRoutes := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, fun _ _ _ => rfl, rfl⟩
  intro n h1 h2
  have h3 : ¬ n < 2 := by omega
  have h4 : ¬ n > 5 := by omega
  simp [copyRoute, h3, h4]

/-- `copy.copy` accepts every `__reduce__` result that `pickle` accepts. False: `pickle` takes a sixth
item, the `state_setter` of protocol 3.8, and `_reconstruct(x, None, *rv)` has room for five. The
`copy` docs say classes control copying with the same interfaces as pickling. -/
def CopyAcceptsPickleReduce : Prop :=
  ∀ n, pickleReduceOk n = true → copyRoute (.reduceTuple n) = .ok "reconstruct"

theorem copyAcceptsPickleReduce_refuted : ¬CopyAcceptsPickleReduce := by
  intro h
  have := h 6 (by decide)
  simp [copyRoute] at this

/-- A bound method's deep copy shares the function and copies `__self__`, so an atom `__self__` stays
the same object. `copy` docs: method objects are copied by `_deepcopy_method`. -/
def DeepMethodSharesFunc : Prop :=
  ∀ (fuel : Nat) (h : Heap) (func self : Nat) (n : Int), h.get self = .atom n →
    deepMethod (fuel + 1) h func self = .ok (h, func, self)

theorem deepMethodSharesFunc_proven : DeepMethodSharesFunc := by
  intro fuel h func self n hc
  simp [deepMethod, deepcopy, hc, bind, Except.bind, pure, Except.pure]

/-- `contains` takes the container first, `getitem`, `setitem`, `delitem` are the subscript operations
with `None` from the two statements, and `call` applies its first argument to the rest, raising
`TypeError` with no argument at all. Docstrings. -/
def SubscriptAndCall : Prop :=
  ∀ (α σ : Type) (slot : α → α → Py Bool) (g : α → α → Py α) (st : σ → Py σ) (s : σ) (a b : α)
    (f : α → List α → Py α) (rest : List α),
    containsOp slot a b = slot a b ∧ getitemOp g a b = g a b ∧
    (∀ s', st s = .ok s' → storeOp st s = .ok ((), s')) ∧
    (callOp f ([] : List α)).raises "TypeError" ∧ callOp f (a :: rest) = f a rest

theorem subscriptAndCall_proven : SubscriptAndCall := by
  intro α σ slot g st s a b f rest
  refine ⟨rfl, rfl, ?_, ⟨_, rfl, rfl⟩, rfl⟩
  intro s' h
  simp [storeOp, h, bind, Except.bind, pure, Except.pure]

/-! ### `abc` -/

/-- `update_abstractmethods` gives `None`-like no change for a class that is not an ABC; otherwise
every name it lists is an abstract name of a base, still abstract as seen from the class, or a new
abstract name in the class's own namespace. Its docstring. `abstractmethod`, `abstractclassmethod` and
`abstractstaticmethod` set the flag. -/
def UpdateAbstractSound : Prop :=
  (∀ c : AbcClass, c.hasAbstractmethods = false → updateAbstract c = none) ∧
  (∀ (c : AbcClass) (r : List String) (n : String), updateAbstract c = some r → n ∈ r →
    (c.isAbstract n = true ∧ ∃ p ∈ c.parents, n ∈ p) ∨ (n, true) ∈ c.own) ∧
  (∀ f : List (String × Bool), (markAbstract f).lookup "__isabstractmethod__" = some true)

theorem updateAbstractSound_proven : UpdateAbstractSound := by
  refine ⟨?_, ?_, ?_⟩
  · intro c h
    simp [updateAbstract, h]
  · intro c r n h hn
    simp only [updateAbstract] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rcases List.mem_append.mp hn with h1 | h1
      · obtain ⟨p, hp, hm⟩ := List.mem_flatMap.mp h1
        have := List.mem_filter.mp hm
        exact Or.inl ⟨this.2, p, hp, this.1⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h1
        have hf := List.mem_filter.mp hq
        right
        have e : q.2 = true := hf.2
        have hm := hf.1
        cases q with
        | mk a b =>
          simp only at e
          subst e
          exact hm
  · intro f
    simp [markAbstract, List.lookup]

/-- `issubclass` for an ABC: `__subclasshook__` decides when it answers, even against the MRO; a class
in the MRO is a subclass; a class registered is a subclass. `register` of something already a subclass
changes nothing, and of a superclass raises `RuntimeError`. PEP 3119, `ABCMeta` docs. -/
def AbcSubclassCheck : Prop :=
  ∀ (W : AbcWorld) (fuel cls sub : Nat),
    (∀ b, W.hook cls sub = some b → abcSubclassCheck W (fuel + 1) cls sub = b) ∧
    (W.hook cls sub = none → (W.mro sub).contains cls = true →
      abcSubclassCheck W (fuel + 1) cls sub = true) ∧
    (abcSubclassCheck W (fuel + 1) cls sub = true → abcRegister W (fuel + 1) cls sub = .ok (sub, false))

theorem abcSubclassCheck_proven : AbcSubclassCheck := by
  intro W fuel cls sub
  refine ⟨?_, ?_, ?_⟩
  · intro b h
    simp [abcSubclassCheck, h]
  · intro h1 h2
    have h3 : cls ∈ W.mro sub := by simpa using h2
    simp [abcSubclassCheck, h1, h3]
  · intro h
    simp [abcRegister, h]

end PyLean.CoreLibs.Operator
