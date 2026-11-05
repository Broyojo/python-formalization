import PyLean.CoreLibs.EnumDC.EnumObj

/-!
Properties of the mirrors over values that raise (`EnumObj.lean`). Each theorem quantifies over every `Ops α`, so over
every `__hash__`, `__eq__`, `__lt__`, ... a value can have; the refutations of the sentences the earlier model proved pick
a value the earlier model had no room for, and run the mirror on it.
-/

namespace PyLean.CoreLibs.EnumDC

open PyLean

variable {α β : Type}

/-! ### `x in list`, `PyObject_RichCompareBool` per item -/

theorem listIn_false_iff (o : Ops α) (x : α) :
    ∀ l : List α, o.listIn x l = .ok false ↔ ∀ y ∈ l, o.req y x = .ok false
  | [] => by simp [Ops.listIn]
  | y :: r => by
    simp only [Ops.listIn, List.mem_cons, forall_eq_or_imp]
    cases h : o.req y x with
    | error e => simp
    | ok b =>
      cases b with
      | true => simp
      | false => simp [listIn_false_iff o x r]

theorem listIn_first (o : Ops α) (x : α) : ∀ (pre : List α) (y : α) (post : List α),
    (∀ z ∈ pre, o.req z x = .ok false) → o.req y x ≠ .ok false → o.listIn x (pre ++ y :: post) = o.req y x
  | [], y, post, _, hy => by
    simp only [List.nil_append, Ops.listIn]
    cases h : o.req y x with
    | error e => rfl
    | ok b =>
      cases b with
      | true => rfl
      | false => exact absurd h hy
  | z :: pre, y, post, hz, hy => by
    simp only [List.cons_append, Ops.listIn, hz z (by simp)]
    exact listIn_first o x pre y post (fun w hw => hz w (by simp [hw])) hy

theorem inLists_eq (o : Ops α) (h : List α) (v : α) : ∀ unh, inLists o unh h v = o.listIn v (unh ++ h)
  | [] => by simp [inLists, Ops.listIn]
  | y :: r => by
    have ih := inLists_eq o h v r
    simp only [inLists, Ops.listIn, List.cons_append] at ih ⊢
    cases hy : o.req y v with
    | error e => rfl
    | ok b =>
      cases b with
      | true => rfl
      | false => simpa using ih

/-! ### `except` -/

theorem subclassOf_self (p : String → List String) (f : Nat) (c : String) : subclassOf p (f + 1) c c = true := by
  simp [subclassOf]

theorem isInst_own (o : Ops α) (e : PyExc) : o.isInst e e.className = true :=
  subclassOf_self o.excParent 999 e.className

theorem isInst_valueError (o : Ops α) (m : String) : o.isInst (.valueError m) "ValueError" = true :=
  isInst_own o (.valueError m)

/-! ### `str % args` -/

theorem fmtItems_error {total : Nat} : ∀ {k : Nat} {rs : List (Py String)} {e : PyExc},
    fmtItems total k rs = .error e → e.className = "TypeError" ∨ Except.error e ∈ rs
  | 0, [], e, h => by simp [fmtItems] at h
  | 0, _ :: _, e, h => by
    left
    simp only [fmtItems, Except.error.injEq] at h
    rw [← h]; rfl
  | _ + 1, [], e, h => by
    left
    simp only [fmtItems, Except.error.injEq] at h
    rw [← h]; rfl
  | k + 1, r :: rest, e, h => by
    cases r with
    | error e' =>
      simp only [fmtItems, Except.error.injEq] at h
      subst h
      right; simp
    | ok _ =>
      simp only [fmtItems] at h
      rcases fmtItems_error h with h1 | h1
      · exact .inl h1
      · right; simp [h1]

theorem pyFormat_one_error {n : Nat} {r : Py String} {e : PyExc} (h : pyFormat n (.one r) = .error e) :
    e.className = "TypeError" ∨ r = .error e := by
  cases n with
  | zero =>
    left
    simp only [pyFormat, Except.error.injEq] at h
    rw [← h]; rfl
  | succ k =>
    cases r with
    | error e' =>
      simp only [pyFormat, Except.error.injEq] at h
      subst h; right; rfl
    | ok _ =>
      left
      simp only [pyFormat] at h
      split at h
      · cases h
      · simp only [Except.error.injEq] at h
        rw [← h]; rfl

theorem pyFormat_tuple_error {n : Nat} {rs : List (Py String)} {e : PyExc} (h : pyFormat n (.tuple rs) = .error e) :
    e.className = "TypeError" ∨ Except.error e ∈ rs := fmtItems_error h

/-- The `repr` of an object, or of an item when it is a tuple that `%` unpacks, raised `e`. -/
def reprOrItemFails {α : Type} (tupA : α → Option (List α)) (reprA : α → Py String) (a : α) (e : PyExc) : Prop :=
  reprA a = .error e ∨ ∃ xs y, tupA a = some xs ∧ y ∈ xs ∧ reprA y = .error e

theorem sargFmt_error {α : Type} {tupA : α → Option (List α)} {reprA : α → Py String} {x : SArg α} {e : PyExc}
    (h : pyFormat 1 (x.fmtOne tupA reprA) = .error e) :
    e.className = "TypeError" ∨ ∃ a, x = .other a ∧ reprOrItemFails tupA reprA a e := by
  cases x with
  | other a =>
    simp only [SArg.fmtOne] at h
    cases ht : tupA a with
    | none =>
      rw [ht] at h
      rcases pyFormat_one_error h with h1 | h1
      · exact .inl h1
      · exact .inr ⟨a, rfl, .inl h1⟩
    | some xs =>
      rw [ht] at h
      rcases pyFormat_tuple_error h with h1 | h1
      · exact .inl h1
      · obtain ⟨y, hy, hr⟩ := List.mem_map.1 h1
        exact .inr ⟨a, rfl, .inr ⟨xs, y, ht, hy, hr⟩⟩
  | _ => simp [SArg.fmtOne, pyFormat] at h

/-! ### `StrEnum.__new__` -/

/-- `StrEnum.__new__`, for every codec and every argument list: it succeeds exactly with no argument (`''`), one `str`
(itself), or a `bytes` or other buffer (`bytearray`, `memoryview`) with a `str` encoding and optionally a `str` errors
(`'strict'` when not given), which the codec decodes; every other exception is a `TypeError`, and the codec's are only
raised for a buffer first argument. So `A = b'x', 'ascii'` and `A = bytearray(b'x'), 'ascii'` both make the member `'x'`
(:1392, Objects/unicodeobject.c:3480-3515), which the earlier sentence "one `str` or nothing" did not allow. The
`TypeError`s of :1378-1391 format the arguments with `%r`, so an exception of an argument's `__repr__` goes out instead;
:1391 is `'errors must be a string, not %r' % (values[2])` with no tuple around the argument, so a tuple `errors` is
unpacked: `(1, R())` is the `TypeError` "not all arguments converted during string formatting (required 1, got 2)". -/
def StrEnumNewRules : Prop :=
  ∀ (α : Type) (codec : Codec) (tupA : α → Option (List α)) (reprA : α → Py String) (l : List (SArg α)) (s : String),
    (strEnumNewG codec tupA reprA l = .ok s ↔
      (l = [] ∧ s = "") ∨ l = [.str s] ∨
      (∃ b enc, l = [.bytes b, .str enc] ∧ strDecode codec b enc "strict" = .ok s) ∨
      (∃ b enc, l = [.buffer b, .str enc] ∧ strDecode codec b enc "strict" = .ok s) ∨
      (∃ b enc er, l = [.bytes b, .str enc, .str er] ∧ strDecode codec b enc er = .ok s) ∨
      (∃ b enc er, l = [.buffer b, .str enc, .str er] ∧ strDecode codec b enc er = .ok s)) ∧
    ∀ e, strEnumNewG codec tupA reprA l = .error e →
      e.className = "TypeError" ∨ (∃ a, SArg.other a ∈ l ∧ reprOrItemFails tupA reprA a e) ∨
      ∃ b enc er, (l.head? = some (.bytes b) ∨ l.head? = some (.buffer b)) ∧ strDecode codec b enc er = .error e

theorem withRepr_error {γ β : Type} {r : Py γ} {e0 e : PyExc} (h : (withRepr r e0 : Py β) = .error e) :
    e = e0 ∨ r = .error e := by
  cases r with
  | error e' => right; simp [withRepr] at h; rw [h]
  | ok _ => left; simp [withRepr] at h; exact h.symm

theorem sarg_repr_error {α : Type} {reprA : α → Py String} {x : SArg α} {e : PyExc} (h : x.repr reprA = .error e) :
    ∃ a, x = .other a ∧ reprA a = .error e := by
  cases x <;> simp [SArg.repr] at h
  exact ⟨_, rfl, h⟩

theorem reprAll_error {α : Type} {reprA : α → Py String} {e : PyExc} :
    ∀ {l : List (SArg α)}, SArg.reprAll reprA l = .error e → ∃ a, SArg.other a ∈ l ∧ reprA a = .error e
  | [], h => by simp [SArg.reprAll] at h
  | x :: r, h => by
    simp only [SArg.reprAll] at h
    cases hx : x.repr reprA with
    | error e' =>
      rw [hx] at h
      cases h
      obtain ⟨a, rfl, ha⟩ := sarg_repr_error hx
      exact ⟨a, by simp, ha⟩
    | ok _ =>
      rw [hx] at h
      obtain ⟨a, ha, he⟩ := reprAll_error h
      exact ⟨a, by simp [ha], he⟩

theorem reprCase {α : Type} {tupA : α → Option (List α)} {reprA : α → Py String} {L : List (SArg α)} {x : SArg α}
    {e0 e : PyExc} {P : Prop} (hx : x ∈ L) (h : (withRepr (x.repr reprA) e0 : Py String) = .error e)
    (ht : e0.className = "TypeError") :
    e.className = "TypeError" ∨ (∃ a, SArg.other a ∈ L ∧ reprOrItemFails tupA reprA a e) ∨ P := by
  rcases withRepr_error h with rfl | hr
  · exact .inl ht
  · obtain ⟨a, rfl, ha⟩ := sarg_repr_error hr
    exact .inr (.inl ⟨a, hx, .inl ha⟩)

theorem fmtCase {α : Type} {tupA : α → Option (List α)} {reprA : α → Py String} {L : List (SArg α)} {x : SArg α}
    {e0 e : PyExc} {P : Prop} (hx : x ∈ L) (h : (withRepr (pyFormat 1 (x.fmtOne tupA reprA)) e0 : Py String) = .error e)
    (ht : e0.className = "TypeError") :
    e.className = "TypeError" ∨ (∃ a, SArg.other a ∈ L ∧ reprOrItemFails tupA reprA a e) ∨ P := by
  rcases withRepr_error h with rfl | hr
  · exact .inl ht
  · rcases sargFmt_error hr with h1 | ⟨a, rfl, ha⟩
    · exact .inl h1
    · exact .inr (.inl ⟨a, hx, ha⟩)

theorem strEnumNewRules_proven : StrEnumNewRules := by
  intro α codec tupA reprA l s
  refine ⟨?_, ?_⟩
  · match l with
    | [] =>
      simp only [strEnumNewG, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Except.ok.injEq, true_and]
      constructor
      · intro h; exact .inl h.symm
      · rintro (h | h | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ | ⟨_, _, _, h, _⟩)
        · exact h.symm
        all_goals cases h
    | [a] => cases a <;> simp [strEnumNewG, strDecodeArg]
    | [a, b] =>
      cases a <;> cases b <;> simp [strEnumNewG, strDecodeArg] <;>
        exact ⟨fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h1, h2⟩, h⟩ => by subst h1; subst h2; exact h⟩
    | [a, b, c] =>
      cases a <;> cases b <;> cases c <;> simp [strEnumNewG, strDecodeArg] <;>
        exact ⟨fun h => ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩,
          fun ⟨_, _, _, ⟨h1, h2, h3⟩, h⟩ => by subst h1; subst h2; subst h3; exact h⟩
    | _ :: _ :: _ :: _ :: r => simp [strEnumNewG]
  · intro e h
    match l, h with
    | [], h => simp [strEnumNewG] at h
    | [a], h =>
      cases a <;> simp only [strEnumNewG, strDecodeArg, List.length_cons, List.length_nil, Nat.zero_add, Nat.reduceAdd,
        gt_iff_lt, Nat.reduceLT, ↓reduceIte] at h <;>
        first | (simp at h; done) | exact reprCase (by simp) h rfl
    | [a, b], h =>
      cases a <;> cases b <;> simp only [strEnumNewG, strDecodeArg, List.length_cons, List.length_nil, Nat.zero_add,
        Nat.reduceAdd, gt_iff_lt, Nat.reduceLT, ↓reduceIte] at h <;>
        first
        | exact reprCase (by simp) h rfl
        | (simp at h; subst h; left; rfl)
        | (simp at h; right; right; exact ⟨_, _, _, .inl rfl, h⟩)
        | (simp at h; right; right; exact ⟨_, _, _, .inr rfl, h⟩)
    | [a, b, c], h =>
      cases a <;> cases b <;> cases c <;> simp only [strEnumNewG, strDecodeArg, List.length_cons, List.length_nil,
        Nat.zero_add, Nat.reduceAdd, gt_iff_lt, Nat.reduceLT, ↓reduceIte] at h <;>
        first
        | exact reprCase (by simp) h rfl
        | exact fmtCase (by simp) h rfl
        | (simp at h; subst h; left; rfl)
        | (simp at h; right; right; exact ⟨_, _, _, .inl rfl, h⟩)
        | (simp at h; right; right; exact ⟨_, _, _, .inr rfl, h⟩)
    | x :: y :: z :: w :: r, h =>
      simp only [strEnumNewG, List.length_cons] at h
      simp only [show r.length + 1 + 1 + 1 + 1 > 3 by omega, ↓reduceIte] at h
      rcases withRepr_error h with rfl | hr
      · left; rfl
      · obtain ⟨a, ha, he⟩ := reprAll_error hr
        exact .inr (.inl ⟨a, ha, .inl he⟩)

/-- The previous statement, with `bytes` as the only decodable first argument. -/
private def StrEnumBytesOnly : Prop :=
  ∀ (codec : Codec) (l : List (SArg PV)) (s : String), strEnumNewG codec pvOps.tupleItems pvOps.repr l = .ok s →
    (l = [] ∧ s = "") ∨ l = [.str s] ∨ (∃ b enc, l = [.bytes b, .str enc]) ∨ (∃ b enc er, l = [.bytes b, .str enc, .str er])

/-- False: `A = bytearray(b'x'), 'ascii'` makes the member `'x'`. -/
private theorem strEnumBytesOnly_false : ¬StrEnumBytesOnly := by
  intro h
  have h1 : strEnumNewG pyCodec pvOps.tupleItems pvOps.repr [SArg.buffer (α := PV) [120], .str "ascii"] = .ok "x" := by
    decide +kernel
  rcases h pyCodec _ _ h1 with ⟨h2, _⟩ | h2 | ⟨_, _, h2⟩ | ⟨_, _, _, h2⟩ <;> simp at h2

/-- `S._new_member_(S, b'x', 'ascii', (1, R()))`: the tuple `errors` is unpacked by the `%` of :1391, as on 3.15.2. -/
private theorem strEnum_tupleErrors :
    strEnumNewG pyCodec pvOps.tupleItems pvOps.repr [SArg.bytes (α := PV) [120], .str "ascii", .other (.pair 1 "KeyError")] =
      .error (.typeError "not all arguments converted during string formatting (required 1, got 2)") := by
  decide +kernel

/-! ### `EnumType.__call__` -/

/-- `EnumType.__call__`: on a class with members, `Cls(a)` looks up `a` and `Cls(a, b, ...)` the tuple `(a, b, ...)`,
the keywords not mattering; on a class without, `names` or `type` go to `_create_` with `names` (or `None`) and every
keyword, `start`, `boundary`, `module` and `qualname` as given, and with neither it is the `TypeError`. So
`Enum('X', type=int)` goes to `_create_`, and `Enum('X', 'A B', start=5)` passes `start=5` on (its values are
`[5, 6]`, by `_create_`). -/
def EnumCallRules : Prop :=
  ∀ (o : Ops EV) (c : EClass) (self : Option Name) (a b : Atom) (r : List Atom) (kw : CallKw) (t : Nat)
    (miss : MissingRet),
    (c.memberMap.isEmpty = false →
      enumCallG o c self a (b :: r) kw miss = (c.toG.enumNew o self (.tup (a :: b :: r)) false miss).map .member ∧
      enumCallG o c self a [] kw miss = (c.toG.enumNew o self (.atom a) false miss).map .member) ∧
    (c.memberMap.isEmpty = true →
      enumCallG o c self a (b :: r) kw miss = .ok (.create a (some b) kw) ∧
      (kw.type = some t → enumCallG o c self a [] kw miss = .ok (.create a none kw)) ∧
      (kw.type = none → (enumCallG o c self a [] kw miss).raises "TypeError"))

theorem enumCallRules_proven : EnumCallRules := by
  intro o c self a b r kw t miss
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, fun ht => ?_, fun ht => ?_⟩⟩
  · simp only [enumCallG, h, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true]
    generalize c.toG.enumNew o self _ false miss = x
    cases x <;> rfl
  · simp only [enumCallG, h, Bool.not_false, ↓reduceIte, List.isEmpty_nil]
    generalize c.toG.enumNew o self _ false miss = x
    cases x <;> rfl
  · simp [enumCallG, h]
  · simp [enumCallG, h, ht]
  · exact ⟨_, by simp [enumCallG, h, ht]; rfl, rfl⟩

/-! ### `EnumType.__contains__` -/

/-- `value in cls`, every path, for every value and every `==`: a member of the class is in it; for a `Flag` class an
`int` is in it exactly when `_missing_` makes a member of it, is not when `EJECT` gives back an `int`, and with a
`ValueError` (or subclass) from `_missing_` (an `int` out of range under `STRICT`, or anything that is not an `int`) the
value is compared with each member value by `==`, the member value on the left, so `1.0 in F` and `K(1) in F` are true
for a class with `A = 1`. `_missing_` formats a value that is not an `int` with `%r` (:1484), so an exception of its
`repr` other than a `ValueError` goes out (`R() in F` raises `KeyError` for an `R` whose `__repr__` does), and a
`ValueError` from it is caught like `_missing_`'s own, the value then compared with the member values. For any class, that comparison is true when some member value is the value itself or equal to
it, false when no comparison is, and its exception goes out. -/
def ContainsPaths : Prop :=
  ∀ (α : Type) (o : Ops α) (c : FlagCls) (unh hashable : List α) (v : α),
    containsG o true none unh hashable v = .ok true ∧
    c.containsOf o true v = .ok true ∧
    (o.asInt v = none → (∃ s, o.repr v = .ok s) →
      c.containsOf o false v = o.listIn v (c.members.map fun p => o.ofInt (p.2 : Int))) ∧
    (o.asInt v = none → ∀ e, o.repr v = .error e → o.isInst e "ValueError" = false → c.containsOf o false v = .error e) ∧
    (o.asInt v = none → ∀ e, o.repr v = .error e → o.isInst e "ValueError" = true →
      c.containsOf o false v = o.listIn v (c.members.map fun p => o.ofInt (p.2 : Int))) ∧
    (∀ i, o.asInt v = some i →
      (∀ n m, c.missingR (o.repr v) i = .ok (.flag n m) → c.containsOf o false v = .ok true) ∧
      (∀ p, c.missingR (o.repr v) i = .ok (.plain p) → c.containsOf o false v = .ok false) ∧
      (∀ e, c.missingR (o.repr v) i = .error e → o.isInst e "ValueError" = true →
        c.containsOf o false v = o.listIn v (c.members.map fun p => o.ofInt (p.2 : Int))) ∧
      (∀ e, c.missingR (o.repr v) i = .error e → o.isInst e "ValueError" = false →
        c.containsOf o false v = .error e)) ∧
    (containsG o false none unh hashable v = .ok false ↔ ∀ y ∈ unh ++ hashable, o.req y v = .ok false) ∧
    (∀ (pre : List α) (y : α) (post : List α), unh ++ hashable = pre ++ y :: post →
      (∀ z ∈ pre, o.req z v = .ok false) →
      o.req y v ≠ .ok false → containsG o false none unh hashable v = o.req y v)

theorem containsPaths_proven : ContainsPaths := by
  intro α o c unh hashable v
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro h ⟨s, hs⟩
    simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, hs, withRepr, inLists_eq, isInst_valueError]
  · intro h e he hv
    simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, he, withRepr, hv]
  · intro h e he hv
    simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, he, withRepr, hv, inLists_eq]
  · intro i h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro n m hm
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, hm]
    · intro p hp
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, hp]
    · intro e he hc
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, he, hc, inLists_eq]
    · intro e he hc
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, he, hc]
  · simp only [containsG, Bool.false_eq_true, ↓reduceIte, inLists_eq]
    exact listIn_false_iff o v _
  · intro pre y post hl hpre hy
    simp only [containsG, Bool.false_eq_true, ↓reduceIte, inLists_eq, hl]
    exact listIn_first o v pre y post hpre hy

/-- `value in cls`, for a `Flag` class and a value that is not negative, means that the value is the value of a member or
a pseudo-member: the docstring of `EnumType.__contains__`. False under `CONFORM`: `_missing_` discards the unknown bits
before it returns a member, and `__contains__` only looks at the type of that member, so `8 in F` is true for a class of
two bits, for which `F(8)` is `F(0)`. -/
def FlagClassContainsValue : Prop :=
  ∀ (α : Type) (o : Ops α) (c : FlagCls) (v : α) (i : Int), o.asInt v = some i → 0 ≤ i →
    c.containsOf o false v = .ok true → ∃ n name, c.call i = .ok (.flag n name) ∧ (n : Int) = i

theorem flagClassContainsValue_refuted : ¬FlagClassContainsValue := by
  intro h
  obtain ⟨n, name, h1, h2⟩ := h EV evOps ⟨"F", [("A", 1), ("B", 2)], .conform⟩ (.atom (.int 8)) 8 rfl (by decide)
    (by decide +kernel)
  have : (FlagCls.call ⟨"F", [("A", 1), ("B", 2)], .conform⟩ 8) = .ok (.flag 0 none) := by decide +kernel
  rw [this] at h1
  simp only [Except.ok.injEq, FlagVal.flag.injEq] at h1
  omega

/-! ### `Flag._missing_` on any value -/

/-- `Flag._missing_` takes only `int`s: anything else is the `ValueError` of :1482-1485, which formats the value with
`%r`, so an exception of its `__repr__` goes out instead (`F._missing_(R())` raises `KeyError` for an `R` whose
`__repr__` does); an `int`, of a subclass too, goes on to the range checks with its `repr`. -/
def MissingOf : Prop :=
  ∀ (α : Type) (o : Ops α) (c : FlagCls) (v : α),
    (o.asInt v = none → (∃ s, o.repr v = .ok s) → (c.missingOf o v).raises "ValueError") ∧
    (o.asInt v = none → ∀ e, o.repr v = .error e → c.missingOf o v = .error e) ∧
    (∀ i, o.asInt v = some i → c.missingOf o v = c.missingR (o.repr v) i)

theorem missingOf_proven : MissingOf := by
  intro α o c v
  refine ⟨fun h ⟨s, hs⟩ => ⟨_, by simp [FlagCls.missingOf, h, hs, withRepr]; rfl, rfl⟩,
    fun h e he => by simp [FlagCls.missingOf, h, he, withRepr], fun i h => by simp [FlagCls.missingOf, h]⟩

/-- The earlier `MissingOf`, anything that is not an `int` is a `ValueError`: false for `R()` whose `__repr__` raises
`KeyError`. -/
private theorem missingOf_reprRaises :
    ¬ (∀ (α : Type) (o : Ops α) (c : FlagCls) (v : α), o.asInt v = none → (c.missingOf o v).raises "ValueError") := by
  intro h
  obtain ⟨e, he, hc⟩ := h PV pvOps ⟨"F", [("A", 1)], .strict⟩ (.robj "KeyError" 0) rfl
  have : FlagCls.missingOf pvOps ⟨"F", [("A", 1)], .strict⟩ (.robj "KeyError" 0) = .error (.keyError "'repr'") := by
    decide +kernel
  rw [this] at he
  cases he
  simp [PyExc.className] at hc

/-- `F(RI(8))` under `STRICT`, for a two-bit class and an `int` subclass whose `__repr__` raises `KeyError`: the message of
:1501 runs it, so `KeyError`. -/
private theorem missingOf_intReprRaises :
    FlagCls.missingOf pvOps ⟨"F", [("A", 1), ("B", 2)], .strict⟩ (.rint 8 "KeyError") = .error (.keyError "'repr'") := by
  decide +kernel

/-- The earlier `ContainsPaths` clause, a value that is not an `int` is compared with the member values: false for
`R()` whose `__repr__` raises `KeyError`, where `R() in F` raises it. -/
private theorem contains_reprRaises :
    ¬ (∀ (α : Type) (o : Ops α) (c : FlagCls) (v : α), o.asInt v = none →
        c.containsOf o false v = o.listIn v (c.members.map fun p => o.ofInt (p.2 : Int))) := by
  intro h
  have := h PV pvOps ⟨"F", [("A", 1)], .strict⟩ (.robj "KeyError" 0) rfl
  revert this
  decide +kernel

/-! ### `verify` -/

/-- The sentence the earlier model proved: `verify` raises `TypeError` on anything that is not an enumeration. False:
`enumeration.__name__` is read at :1970, before the `issubclass` test, so `verify(UNIQUE)(42)` raises `AttributeError`. -/
def VerifyCall : Prop :=
  ∀ (α : Type) (o : Ops α) (order : List α → List α) (c : EClassG α) (f : Name → Name)
    (name : Py String) (target : VTarget) (checks : List Check),
    (∀ flag, target ≠ .enum flag) → (verifyCallG o order c f name target checks).raises "TypeError"

theorem verifyCall_refuted : ¬VerifyCall := by
  intro h
  obtain ⟨e, he, hc⟩ := h EV evOps id {} id (.error (.named "AttributeError" "'int' object has no attribute '__name__'"))
    .notCls [.unique] (by intro flag hf; cases hf)
  simp only [verifyCallG, Except.error.injEq] at he
  subst he
  simp [PyExc.className] at hc

private theorem verifyAll_ok (o : Ops α) (order : List α → List α) (c : EClassG α) (f : Name → Name)
    (flag : Bool) (s : String) : ∀ checks : List Check,
    verifyAllG o order c f flag s checks = .ok () ↔ ∀ k ∈ checks, verifyOneG o order c f flag s k = .ok ()
  | [] => by simp [verifyAllG]
  | k :: r => by
    simp only [verifyAllG, List.mem_cons, forall_eq_or_imp]
    cases h : verifyOneG o order c f flag s k with
    | error e => simp
    | ok u => simpa using verifyAll_ok o order c f flag s r

private theorem verifyAll_first (o : Ops α) (order : List α → List α) (c : EClassG α) (f : Name → Name)
    (flag : Bool) (s : String) (e : PyExc) : ∀ (pre : List Check) (k : Check) (post : List Check),
    (∀ k' ∈ pre, verifyOneG o order c f flag s k' = .ok ()) → verifyOneG o order c f flag s k = .error e →
    verifyAllG o order c f flag s (pre ++ k :: post) = .error e
  | [], k, post, _, hk => by simp [verifyAllG, hk]
  | k' :: pre, k, post, hp, hk => by
    simp only [List.cons_append, verifyAllG, hp k' (by simp)]
    exact verifyAll_first o order c f flag s e pre k post (fun x hx => hp x (by simp [hx])) hk

/-- `verify.__call__`: an exception reading `__name__` comes first; then something that is not a class is the `TypeError`
of `issubclass`, a class that is not an `Enum` the decorator's own `TypeError`; on an enumeration the checks run in order,
the first that fails is the exception, and it passes exactly when each does. `UNIQUE` is the name test, `CONTINUOUS` runs
over the member values, and `NAMED_FLAGS` is `EClassG.verifyNamed` (see `VerifyNamedInts`). -/
def VerifyCallRules : Prop :=
  ∀ (α : Type) (o : Ops α) (order : List α → List α) (c : EClassG α) (f : Name → Name) (checks : List Check),
    (∀ e target, verifyCallG o order c f (.error e) target checks = .error e) ∧
    (∀ s, verifyCallG o order c f (.ok s) .notCls checks =
        .error (.typeError "issubclass() arg 1 must be a class") ∧
      verifyCallG o order c f (.ok s) .cls checks =
        .error (.typeError "the 'verify' decorator only works with Enum and Flag") ∧
      ∀ flag, (verifyCallG o order c f (.ok s) (.enum flag) checks = .ok () ↔
        ∀ k ∈ checks, verifyOneG o order c f flag s k = .ok ()) ∧
        ∀ pre k post e, checks = pre ++ k :: post → (∀ k' ∈ pre, verifyOneG o order c f flag s k' = .ok ()) →
          verifyOneG o order c f flag s k = .error e →
          verifyCallG o order c f (.ok s) (.enum flag) checks = .error e) ∧
    (∀ flag s, (verifyOneG o order c f flag s .unique = .ok () ↔ ∀ p ∈ c.memberMap, p.1 = f p.2) ∧
      verifyOneG o order c f flag s .continuous = verifyContinuousG o order flag s c.memberValues ∧
      verifyOneG o order c f flag s .named = c.verifyNamed o)

theorem verifyCallRules_proven : VerifyCallRules := by
  intro α o order c f checks
  refine ⟨fun e target => rfl, fun s => ⟨rfl, rfl, fun flag => ⟨verifyAll_ok o order c f flag s checks, ?_⟩⟩,
    fun flag s => ⟨?_, rfl, rfl⟩⟩
  · intro pre k post e hc hp hk
    subst hc
    exact verifyAll_first o order c f flag s e pre k post hp hk
  · simp only [verifyOneG, EClassG.verifyUnique]
    cases h : c.memberMap.any (fun p => p.1 != f p.2) with
    | true =>
      simp only [↓reduceIte, reduceCtorEq, false_iff]
      intro hall
      obtain ⟨p, hp, hq⟩ := List.any_eq_true.1 h
      simp [hall p hp] at hq
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, true_iff]
      intro p hp
      have := List.any_eq_false.1 h p hp
      simpa using this

/-! ### `Enum.__new__` -/

/-- `Enum.__new__`, every path, for every `hash` and `==`: a member comes back as it is; a value the dict lookup finds is
that member; a `KeyError` from the lookup, from `__hash__` or from `__eq__` skips the long search, a `TypeError` from any
of them runs it, and any other exception goes out. The long search looks the name it finds up again, by `cls[name]`,
checks the unhashable lists first, and compares `value == member._value_` with the value on the left. After it, no members
is a `TypeError`, and otherwise `_missing_` decides: its member, `None` as `ValueError`, anything else as `TypeError`, and
its exception as it is. Docs of `_missing_`. Short of a member, :1220 formats the value with `%r` first, so an
exception of its `repr` goes out instead, and :1225 formats a result that is neither a member nor `None` the same way;
but only an `Exception` from `_missing_` is caught (:1207), so anything else goes out before either. -/
def EnumLookupG : Prop :=
  ∀ (α : Type) (o : Ops α) (c : EClassG α) (m : Name) (v : α) (ip : Bool) (miss : MissingRet),
    c.enumNew o (some m) v ip miss = .ok m ∧
    (∀ n, o.dictGet c.value2member v = .ok (some n) → c.enumNew o none v ip miss = .ok n) ∧
    (o.dictGet c.value2member v = .ok none → c.enumNew o none v ip miss = c.afterSearch o ip (o.repr v) miss) ∧
    (∀ e, o.dictGet c.value2member v = .error e →
      (o.isInst e "KeyError" = true → c.enumNew o none v ip miss = c.afterSearch o ip (o.repr v) miss) ∧
      (o.isInst e "KeyError" = false → o.isInst e "TypeError" = true → c.enumNew o none v ip miss =
        match c.longSearch o v with
        | .error e' => .error e'
        | .ok (some n) => .ok n
        | .ok none => c.afterSearch o ip (o.repr v) miss) ∧
      (o.isInst e "KeyError" = false → o.isInst e "TypeError" = false → c.enumNew o none v ip miss = .error e)) ∧
    (∀ e, o.hash v = .error e → o.dictGet c.value2member v = .error (o.keyExc "dict key" v e) ∧
      (o.keyExc "dict key" v e).className = e.className) ∧
    (∀ n k, firstHolding o v c.unhashableMap = .ok (some n) → c.memberMap.lookup n = some k →
      c.longSearch o v = .ok (some k)) ∧
    (∀ n, firstHolding o v c.unhashableMap = .ok (some n) → c.memberMap.lookup n = none →
      (c.longSearch o v).raises "KeyError") ∧
    (∀ e, firstHolding o v c.unhashableMap = .error e → c.longSearch o v = .error e) ∧
    (firstHolding o v c.unhashableMap = .ok none →
      c.longSearch o v = match c.firstByValue o v c.memberMap with
        | .error e => .error e
        | .ok (some n) => c.getItem n |>.map some
        | .ok none => .ok none) ∧
    (∀ n mem x r, c.values.lookup mem = some x → c.firstByValue o v ((n, mem) :: r) =
      match o.eq v x with
      | .error e => .error e
      | .ok true => .ok (some n)
      | .ok false => c.firstByValue o v r) ∧
    (∀ rv : Py String, c.memberMap.isEmpty = false →
      c.afterSearch o ip rv (.member m) = .ok m ∧
      ((∃ s, rv = .ok s) → (c.afterSearch o ip rv .none).raises "ValueError" ∧
        (∀ rr, (∃ s, rr = .ok s) → (c.afterSearch o ip rv (.other rr)).raises "TypeError") ∧
        (∀ e, c.afterSearch o ip rv (.other (.error e)) = .error e) ∧
        ∀ e, c.afterSearch o ip rv (.raises e) = .error e) ∧
      (∀ e', rv = .error e' → c.afterSearch o ip rv .none = .error e' ∧
        (∀ rr, c.afterSearch o ip rv (.other rr) = .error e') ∧
        ∀ e, o.isInst e "Exception" = true → c.afterSearch o ip rv (.raises e) = .error e') ∧
      (∀ e, o.isInst e "Exception" = false → c.afterSearch o ip rv (.raises e) = .error e)) ∧
    (c.memberMap.isEmpty = true → (c.afterSearch o ip (o.repr v) miss).raises "TypeError")

theorem enumLookupG_proven : EnumLookupG := by
  intro α o c m v ip miss
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h; simp [EClassG.enumNew, h]
  · intro h; simp [EClassG.enumNew, h]
  · intro e h
    refine ⟨fun hk => ?_, fun hk ht => ?_, fun hk ht => ?_⟩
    · simp [EClassG.enumNew, h, hk]
    · simp only [EClassG.enumNew, h, hk, ht, Bool.false_eq_true, ↓reduceIte]
      try rfl
    · simp [EClassG.enumNew, h, hk, ht]
  · intro e h; refine ⟨by simp [Ops.dictGet, Ops.lookupIn, h], ?_⟩; cases e <;> rfl
  · intro n k h1 h2; simp [EClassG.longSearch, h1, EClassG.getItem, h2]
  · intro n h1 h2; exact ⟨_, by simp [EClassG.longSearch, h1, EClassG.getItem, h2]; rfl, rfl⟩
  · intro e h; simp [EClassG.longSearch, h]
  · intro h
    simp only [EClassG.longSearch, h]
    generalize c.firstByValue o v c.memberMap = x
    rcases x with e | (_ | n)
    · rfl
    · rfl
    · simp only
      generalize c.getItem n = y
      cases y <;> rfl
  · intro n mem x r hx
    simp only [EClassG.firstByValue, hx]
    try rfl
  · intro rv h
    refine ⟨by simp [EClassG.afterSearch, h], fun ⟨s, hs⟩ => ?_, fun e' he => ?_, fun e hx => ?_⟩
    · subst hs
      refine ⟨⟨_, by simp [EClassG.afterSearch, h, withRepr]; rfl, rfl⟩, fun rr ⟨s', hs'⟩ => ?_,
        fun e => by simp [EClassG.afterSearch, h, withRepr], fun e => ?_⟩
      · subst hs'
        exact ⟨_, by simp [EClassG.afterSearch, h, withRepr]; rfl, rfl⟩
      · by_cases hx : o.isInst e "Exception" = true
        · simp [EClassG.afterSearch, h, withRepr, hx]
        · simp [EClassG.afterSearch, h, withRepr, hx]
    · subst he
      exact ⟨by simp [EClassG.afterSearch, h, withRepr], fun rr => by simp [EClassG.afterSearch, h, withRepr],
        fun e hx => by simp [EClassG.afterSearch, h, withRepr, hx]⟩
    · simp [EClassG.afterSearch, h, hx]
  · intro h
    cases ip
    · exact ⟨_, by simp [EClassG.afterSearch, h]; rfl, rfl⟩
    · exact ⟨_, by simp [EClassG.afterSearch, h]; rfl, rfl⟩

/-! ### `dict.setdefault` -/

theorem setDefault_paths (o : Ops α) (d : List (α × β)) (k : α) (v : β) :
    (∀ w, o.dictGet d k = .ok (some w) → o.setDefault d k v = .ok (d, w)) ∧
    (o.dictGet d k = .ok none → o.setDefault d k v = .ok (d ++ [(k, v)], v)) ∧
    (∀ e, o.dictGet d k = .error e → o.setDefault d k v = .error e) := by
  refine ⟨fun w h => by simp [Ops.setDefault, h], fun h => by simp [Ops.setDefault, h],
    fun e h => by simp [Ops.setDefault, h]⟩

theorem className_bne {e : PyExc} {s : String} (h : e.className ≠ s) : (e.className == s) = false := by
  simp [h]

/-! ### `_proto_member.__set_name__` -/

/-- `_proto_member.__set_name__`, every path, for every `hash`, `==` and way of making the member. The member's `_value_`:
an exception from `__new__` goes out; a value it set is kept; otherwise a plain class keeps the value itself, and any
other calls `_member_type_(*args)`, whose `Exception` becomes the `TypeError` "_value_ not set in __new__, unable to
create it" (`except Exception`, :264) while a `BaseException` that is not an `Exception` goes out; then `__init__`, whose
exception goes out. Exception classes may have several bases: `KT(KeyError, TypeError)` raised by both `__hash__` and
`__eq__` runs the linear search and then makes a new member filed as unhashable. The alias search: what the dict lookup finds or does not find decides; a
`KeyError` from the lookup, `__hash__` or `__eq__` makes a new member; a `TypeError` runs the linear search, which compares
`canonical._value_ == value` (no identity shortcut), and in which a `KeyError` again makes a new member and any other
exception goes out. An alias is added to `_member_map_` only; a new member also goes to `_member_names_` (for a `Flag`,
when its value is a single bit). The tables: `setdefault` and `value not in _hashable_values_`, a `TypeError` from either
filing the value in the unhashable lists under the member's name, and any other exception going out. -/
def SetNamePaths : Prop :=
  ∀ (α : Type) (o : Ops α) (mk : Maker α) (c : EClassG α) (name : Name) (value v : α),
    (∀ e, mk.newMember = .error e → mk.memberValue o value = .error e) ∧
    (mk.newMember = .ok (some v) → mk.memberValue o value = mk.init.map (fun _ => v)) ∧
    (mk.newMember = .ok none → mk.plain = true → mk.memberValue o value = mk.init.map (fun _ => value)) ∧
    (mk.newMember = .ok none → mk.plain = false → mk.callType = .ok v → mk.memberValue o value = mk.init.map (fun _ => v)) ∧
    (mk.newMember = .ok none → mk.plain = false → ∀ e, mk.callType = .error e → o.isInst e "Exception" = true →
      mk.memberValue o value = .error (.typeError "_value_ not set in __new__, unable to create it")) ∧
    (mk.newMember = .ok none → mk.plain = false → ∀ e, mk.callType = .error e → o.isInst e "Exception" = false →
      mk.memberValue o value = .error e) ∧
    (∀ e, mk.memberValue o value = .error e → c.setName o mk name value = .error e) ∧
    (∀ r, o.dictGet c.value2member v = .ok r → c.aliasOf o v = .ok r) ∧
    (∀ e, o.dictGet c.value2member v = .error e → o.isInst e "TypeError" = false → o.isInst e "KeyError" = true →
      c.aliasOf o v = .ok none) ∧
    (∀ e, o.dictGet c.value2member v = .error e → o.isInst e "TypeError" = true →
      (∀ r, c.firstEqual o v c.memberMap = .ok r → c.aliasOf o v = .ok r) ∧
      (∀ e', c.firstEqual o v c.memberMap = .error e' → o.isInst e' "KeyError" = true → c.aliasOf o v = .ok none) ∧
      (∀ e', c.firstEqual o v c.memberMap = .error e' → o.isInst e' "KeyError" = false → c.aliasOf o v = .error e')) ∧
    (∀ e, o.dictGet c.value2member v = .error e → o.isInst e "TypeError" = false → o.isInst e "KeyError" = false →
      c.aliasOf o v = .error e) ∧
    (∀ n m x r, c.values.lookup m = some x → c.firstEqual o v ((n, m) :: r) =
      match o.eq x v with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => c.firstEqual o v r) ∧
    (mk.memberValue o value = .ok v →
      (∀ e, (c.flagUpdate o v).aliasOf o v = .error e → c.setName o mk name value = .error e) ∧
      (∀ m, (c.flagUpdate o v).aliasOf o v = .ok (some m) →
        c.setName o mk name value = ((c.flagUpdate o v).addToMap o name m).bind (fun c2 => c2.noteValue o name m v)) ∧
      ((c.flagUpdate o v).aliasOf o v = .ok none →
        c.setName o mk name value =
          ({ c.flagUpdate o v with
              memberNames := if !(c.flagUpdate o v).isFlag || (match o.asInt v with
                  | some n => isSingleBitInt n
                  | none => false) then (c.flagUpdate o v).memberNames ++ [name] else (c.flagUpdate o v).memberNames,
              values := (c.flagUpdate o v).values ++ [(name, v)] }.addToMap o name name).bind
            (fun c3 => c3.noteValue o name name v))) ∧
    (∀ m e, o.setDefault c.value2member v m = .error e → o.isInst e "TypeError" = true →
      c.noteValue o name m v = .ok { c with unhashableValues := c.unhashableValues ++ [v],
                                             unhashableMap := appendToG c.unhashableMap name v }) ∧
    (∀ m e, o.setDefault c.value2member v m = .error e → o.isInst e "TypeError" = false → c.noteValue o name m v = .error e) ∧
    (∀ m d w, o.setDefault c.value2member v m = .ok (d, w) →
      (o.listIn v c.hashableValues = .ok false →
        c.noteValue o name m v = .ok { c with value2member := d, hashableValues := c.hashableValues ++ [v] }) ∧
      (o.listIn v c.hashableValues = .ok true → c.noteValue o name m v = .ok { c with value2member := d }) ∧
      (∀ e, o.listIn v c.hashableValues = .error e → o.isInst e "TypeError" = true →
        c.noteValue o name m v = .ok { c with value2member := d, unhashableValues := c.unhashableValues ++ [v],
                                               unhashableMap := appendToG c.unhashableMap name v }) ∧
      (∀ e, o.listIn v c.hashableValues = .error e → o.isInst e "TypeError" = false → c.noteValue o name m v = .error e))

theorem setNamePaths_proven : SetNamePaths := by
  intro α o mk c name value v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e h; simp [Maker.memberValue, h]
  · intro h; simp only [Maker.memberValue, h]; cases mk.init <;> rfl
  · intro h hp; simp only [Maker.memberValue, h, hp, ↓reduceIte]; cases mk.init <;> rfl
  · intro h hp hc; simp only [Maker.memberValue, h, hp, hc, Bool.false_eq_true, ↓reduceIte]; cases mk.init <;> rfl
  · intro h hp e hc hx; simp [Maker.memberValue, h, hp, hc, hx]
  · intro h hp e hc hx; simp [Maker.memberValue, h, hp, hc, hx]
  · intro e h; simp [EClassG.setName, h]
  · intro r h; simp [EClassG.aliasOf, h]
  · intro e h ht hk
    simp [EClassG.aliasOf, h, ht, hk]
  · intro e h ht
    refine ⟨fun r hr => by simp [EClassG.aliasOf, h, ht, hr], fun e' he hk => by simp [EClassG.aliasOf, h, ht, he, hk],
      fun e' he hk => by simp [EClassG.aliasOf, h, ht, he, hk]⟩
  · intro e h ht hk
    simp [EClassG.aliasOf, h, hk, ht]
  · intro n m x r hx
    simp only [EClassG.firstEqual, hx]
    try rfl
  · intro hv
    refine ⟨fun e he => by simp [EClassG.setName, hv, he], fun m hm => ?_, fun hn => ?_⟩
    · simp only [EClassG.setName, hv, hm]
      generalize (c.flagUpdate o v).addToMap o name m = x
      cases x <;> rfl
    · simp only [EClassG.setName, hv, hn]
      generalize EClassG.addToMap o _ name name = x
      cases x <;> rfl
  · intro m e h ht
    simp [EClassG.noteValue, h, ht]
  · intro m e h ht
    simp [EClassG.noteValue, h, ht]
  · intro m d w h
    refine ⟨fun hl => by simp [EClassG.noteValue, h, hl], fun hl => by simp [EClassG.noteValue, h, hl],
      fun e hl ht => by simp [EClassG.noteValue, h, hl, ht],
      fun e hl ht => by simp [EClassG.noteValue, h, hl, ht]⟩

/-! ### `Enum._add_value_alias_` -/

/-- `Enum._add_value_alias_`, every path, for every `hash` and `==`: a value another member has in the map is the
`ValueError` (after the `repr` of the value and of that member, by the class's own `__repr__` if it has one, either of
which can raise instead), one this member has
is nothing, a new one is bound; a `TypeError` from the lookup runs the search over the
members' `_value_`, in which a value another member has raises that `TypeError` again (it formats the `ValueError` with
`map[value]`), one this member has is nothing, and a new one is bound; any other exception goes out. Binding is
`setdefault` and an append, or with a `TypeError` the unhashable lists under `self.name`. -/
def ValueAliasPaths : Prop :=
  ∀ (α : Type) (o : Ops α) (c : EClassG α) (f : Name → Name) (self : Name) (v : α),
    (∀ m, o.dictGet c.value2member v = .ok (some m) → m ≠ self → (∃ s, o.repr v = .ok s) →
      (∃ s, c.memberRepr o m = .ok s) → (c.addValueAlias o f self v).raises "ValueError") ∧
    (∀ m e, o.dictGet c.value2member v = .ok (some m) → m ≠ self → (∃ s, o.repr v = .ok s) →
      c.memberRepr o m = .error e → c.addValueAlias o f self v = .error e) ∧
    (∀ m e, o.dictGet c.value2member v = .ok (some m) → m ≠ self → o.repr v = .error e →
      c.addValueAlias o f self v = .error e) ∧
    (o.dictGet c.value2member v = .ok (some self) → c.addValueAlias o f self v = .ok c) ∧
    (o.dictGet c.value2member v = .ok none → c.addValueAlias o f self v = c.bindValue o f self v) ∧
    (∀ e, o.dictGet c.value2member v = .error e → o.isInst e "TypeError" = true →
      (∀ m, c.firstMemberEq o v c.memberMap = .ok (some m) → m ≠ self → c.addValueAlias o f self v = .error e) ∧
      (c.firstMemberEq o v c.memberMap = .ok (some self) → c.addValueAlias o f self v = .ok c) ∧
      (c.firstMemberEq o v c.memberMap = .ok none → c.addValueAlias o f self v = c.bindValue o f self v) ∧
      (∀ e', c.firstMemberEq o v c.memberMap = .error e' → c.addValueAlias o f self v = .error e')) ∧
    (∀ e, o.dictGet c.value2member v = .error e → o.isInst e "TypeError" = false → c.addValueAlias o f self v = .error e) ∧
    (∀ n m x r, c.values.lookup m = some x → c.firstMemberEq o v ((n, m) :: r) =
      match o.eq x v with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => c.firstMemberEq o v r) ∧
    (∀ d w, o.setDefault c.value2member v self = .ok (d, w) →
      c.bindValue o f self v = .ok { c with value2member := d, hashableValues := c.hashableValues ++ [v] }) ∧
    (∀ e, o.setDefault c.value2member v self = .error e → o.isInst e "TypeError" = true →
      c.bindValue o f self v = .ok { c with unhashableValues := c.unhashableValues ++ [v],
                                            unhashableMap := appendToG c.unhashableMap (f self) v }) ∧
    (∀ e, o.setDefault c.value2member v self = .error e → o.isInst e "TypeError" = false →
      c.bindValue o f self v = .error e)

theorem valueAliasPaths_proven : ValueAliasPaths := by
  intro α o c f self v
  refine ⟨fun m h hm ⟨s, hs⟩ ⟨s', hs'⟩ => ⟨_, by simp [EClassG.addValueAlias, h, hm, hs, hs', withRepr]; rfl, rfl⟩,
    fun m e h hm ⟨s, hs⟩ he => by simp [EClassG.addValueAlias, h, hm, hs, he, withRepr],
    fun m e h hm he => by simp [EClassG.addValueAlias, h, hm, he], fun h => by
    simp [EClassG.addValueAlias, h], fun h => by simp [EClassG.addValueAlias, h], fun e h ht => ⟨fun m hm hne => by
    simp [EClassG.addValueAlias, h, ht, hm, hne], fun hm => by simp [EClassG.addValueAlias, h, ht, hm], fun hm => by
    simp [EClassG.addValueAlias, h, ht, hm], fun e' he => by simp [EClassG.addValueAlias, h, ht, he]⟩,
    fun e h ht => by simp [EClassG.addValueAlias, h, ht], fun n m x r hx => ?_, fun d w h => by
    simp [EClassG.bindValue, h], fun e h ht => by simp [EClassG.bindValue, h, ht], fun e h ht => by
    simp [EClassG.bindValue, h, ht]⟩
  simp only [EClassG.firstMemberEq, hx]
  try rfl

/-- A class with members `A` and `B` and the given values, built by the mirror. -/
def twoG (a b : EV) : EClassG EV :=
  { memberNames := [['A'], ['B']], memberMap := [(['A'], ['A']), (['B'], ['B'])], values := [(['A'], a), (['B'], b)] }

/-- A value linked to a member is a `ValueError` for any other member, the docs of `_add_value_alias_`. False for an
unhashable value: the check at Lib/enum.py:1248-1249 reads the `_value_` of the members only, so a value linked with
`_add_value_alias_` is not seen, and the second member gets it as well. -/
def ValueAliasExclusive : Prop :=
  ∀ (α : Type) (o : Ops α) (c c' : EClassG α) (f : Name → Name) (m m' : Name) (v : α), m ≠ m' →
    c.addValueAlias o f m v = .ok c' → (c'.addValueAlias o f m' v).raises "ValueError"

/-- The class after `A._add_value_alias_([9])`, and after `B._add_value_alias_([9])` too. -/
def twoG1 : EClassG EV :=
  { twoG (.atom (.int 1)) (.atom (.int 2)) with
    unhashableValues := [.atom (.list 9)]
    unhashableMap := [(['A'], [.atom (.list 9)])] }

def twoG2 : EClassG EV :=
  { twoG (.atom (.int 1)) (.atom (.int 2)) with
    unhashableValues := [.atom (.list 9), .atom (.list 9)]
    unhashableMap := [(['A'], [.atom (.list 9)]), (['B'], [.atom (.list 9)])] }

theorem valueAliasExclusive_refuted : ¬ValueAliasExclusive := by
  intro h
  have h1 : (twoG (.atom (.int 1)) (.atom (.int 2))).addValueAlias evOps id ['A'] (.atom (.list 9)) = .ok twoG1 := by
    decide +kernel
  obtain ⟨e, he, _⟩ := h EV evOps _ _ id ['A'] ['B'] (.atom (.list 9)) (by decide) h1
  have h2 : twoG1.addValueAlias evOps id ['B'] (.atom (.list 9)) = .ok twoG2 := by decide +kernel
  rw [h2] at he
  cases he

/-- A value that is another member's `_value_` is a `ValueError`, unhashable or not. False: for an unhashable value the
`ValueError` is formatted with `cls._value2member_map_[value]` at :1251, which hashes the value again and raises
`TypeError`. -/
def ValueAliasBoundError : Prop :=
  ∀ (α : Type) (o : Ops α) (c : EClassG α) (f : Name → Name) (m m' : Name) (v : α), m ≠ m' →
    c.firstMemberEq o v c.memberMap = .ok (some m') → (c.addValueAlias o f m v).raises "ValueError"

theorem valueAliasBoundError_refuted : ¬ValueAliasBoundError := by
  intro h
  obtain ⟨e, he, hc⟩ := h EV evOps (twoG (.atom (.list 1)) (.atom (.int 2))) id ['B'] ['A'] (.atom (.list 1))
    (by decide) (by decide +kernel)
  have : (twoG (.atom (.list 1)) (.atom (.int 2))).addValueAlias evOps id ['B'] (.atom (.list 1)) =
      .error (.typeError "cannot use 'list' as a dict key (unhashable type: 'list')") := by decide +kernel
  rw [this] at he
  cases he
  exact absurd hc (by decide)

/-- `Enum.__new__` finds a value bound by `_add_value_alias_`, as in the docs' `Color.RED._add_value_alias_(42)`, then
`Color(42)`. False for a class with a `name` of its own: :1262 files the value under `self.name`, and :1193 does
`cls[name]`, a `KeyError`. -/
def ValueAliasFound : Prop :=
  ∀ (α : Type) (o : Ops α) (c c' : EClassG α) (f : Name → Name) (m : Name) (v : α), c.memberMap.lookup m = some m →
    c.addValueAlias o f m v = .ok c' → c'.enumNew o none v false .none = .ok m

/-- A class with one member `A`, and the same after `A._add_value_alias_([1])` when `A.name` is `'a'`. -/
def oneG : EClassG EV := { memberMap := [(['A'], ['A'])], values := [(['A'], .atom (.int 1))] }

def oneG1 : EClassG EV :=
  { oneG with
    unhashableValues := [.atom (.list 1)]
    unhashableMap := [(['a'], [.atom (.list 1)])] }

theorem valueAliasFound_refuted : ¬ValueAliasFound := by
  intro h
  have h1 : oneG.addValueAlias evOps (fun _ => ['a']) ['A'] (.atom (.list 1)) = .ok oneG1 := by decide +kernel
  have := h EV evOps _ _ (fun _ => ['a']) ['A'] (.atom (.list 1)) (by decide) h1
  revert this
  decide +kernel

/-! ### `EnumDict` -/

/-- `EnumDict.update`: each item of an iterable of pairs goes through `__setitem__` in turn, the first exception stops it,
and so do the keyword items after; with a mapping, the same while no `AttributeError` comes, and an `AttributeError`
from `__setitem__` starts again over the mapping's keys, unpacked, from the state it had reached. So a no-op or a
constant fails it. -/
def UpdateRules : Prop :=
  ∀ (d : EnumDict) (k : Name) (v : EV) (rest more : List (Name × EV)),
    d.update (.pairs []) [] = .ok d ∧
    (∀ d1, d.set k v = .ok d1 → d.update (.pairs ((k, v) :: rest)) more = d1.update (.pairs rest) more) ∧
    (∀ e, d.set k v = .error e → d.update (.pairs ((k, v) :: rest)) more = .error e) ∧
    (∀ d1, d.set k v = .ok d1 → d.update (.pairs []) ((k, v) :: more) = d1.update (.pairs []) more) ∧
    (∀ e, d.set k v = .error e → d.update (.pairs []) ((k, v) :: more) = .error e) ∧
    (∀ items d', d.setAll items = (d', none) → d.update (.mapping items) more = d'.update (.pairs []) more) ∧
    (∀ items d' e, d.setAll items = (d', some e) → excIs builtinParent e "AttributeError" = true →
      d.update (.mapping items) more =
        (d'.unpackKeys (items.map Prod.fst)).bind (fun d'' => d''.update (.pairs []) more)) ∧
    (∀ items d' e, d.setAll items = (d', some e) → excIs builtinParent e "AttributeError" = false →
      d.update (.mapping items) more = .error e)

theorem updateRules_proven : UpdateRules := by
  intro d k v rest more
  refine ⟨rfl, fun d1 h => ?_, fun e h => ?_, fun d1 h => ?_, fun e h => ?_, fun items d' h => ?_,
    fun items d' e h ha => ?_, fun items d' e h ha => ?_⟩
  · simp only [EnumDict.update, EnumDict.setAll, h]
  · simp [EnumDict.update, EnumDict.setAll, h]
  · simp only [EnumDict.update, EnumDict.setAll, h]
  · simp [EnumDict.update, EnumDict.setAll, h]
  · simp only [EnumDict.update, h, EnumDict.setAll]
  · simp only [EnumDict.update, h, ha, beq_self_eq_true, ↓reduceIte, EnumDict.setAll]
    generalize d'.unpackKeys (items.map Prod.fst) = x
    cases x <;> rfl
  · simp [EnumDict.update, h, ha]

/-- `_ignore_` given as a tuple of names ignores those names, as a list does: `list(value)` at Lib/enum.py:379. -/
def IgnoreTuple : Prop :=
  ∀ (l : List String), ignoreList (.tup (l.map Atom.str)) = .ok (l.map String.toList) ∧
    ignoreList (.names (l.map String.toList)) = .ok (l.map String.toList)

theorem ignoreTuple_proven : IgnoreTuple := by
  intro l
  refine ⟨?_, rfl⟩
  have h2 : (l.map Atom.str).filterMap Atom.ignoreName = l.map String.toList := by
    induction l with
    | nil => rfl
    | cons x xs ih => simp [Atom.ignoreName] at ih ⊢; exact ih
  have h1 : (l.map Atom.str).all Atom.hashable = true := by simp [Atom.hashable]
  simp only [ignoreList, h1, ↓reduceIte, h2]

/-! ### `except` catches subclasses: the witnesses -/

/-- A class with one member `A = 1`, built by the mirror. -/
private def cA : EClassG PV :=
  { memberNames := [['A']], memberMap := [(['A'], ['A'])], values := [(['A'], .int 1)],
    value2member := [(.int 1, ['A'])], hashableValues := [.int 1] }

/-- The earlier clause of `SetNamePaths`, a linear-search exception whose class is not named `KeyError` goes out, is false:
`B = Q()` whose `__hash__` raises `TypeError` and whose `__eq__` raises a subclass of `KeyError` is caught at :296 and
becomes a new member, as on 3.15.2 (`list(E) == [A, B]`). -/
private theorem setName_keyErrorSubclass :
    ¬ (∀ (α : Type) (o : Ops α) (c : EClassG α) (v : α) (e e' : PyExc), o.dictGet c.value2member v = .error e →
        e.className = "TypeError" → c.firstEqual o v c.memberMap = .error e' → e'.className ≠ "KeyError" →
        c.aliasOf o v = .error e') := by
  intro h
  have := h PV pvOps cA (.key 1 (some "TypeError") (some "KSub") 0)
    (.typeError "cannot use 'K' as a dict key (hash)") (.named "KSub" "'eq'") (by decide +kernel) rfl
    (by decide +kernel) (by decide)
  revert this
  decide +kernel

private theorem setName_keyErrorSubclass_member :
    (cA.setName pvOps {} ['B'] (.key 1 (some "TypeError") (some "KSub") 0)).map (·.memberNames) =
      .ok [['A'], ['B']] := by
  decide +kernel

/-- The earlier clause of `EnumLookupG`, an exception whose class is named neither `KeyError` nor `TypeError` goes out, is
false: for `H(1)` whose `__hash__` raises a subclass of `TypeError` and which equals `1`, `E1(H(1))` is `E1.A` through the
long search, as on 3.15.2. -/
private theorem enumNew_typeErrorSubclass :
    ¬ (∀ (α : Type) (o : Ops α) (c : EClassG α) (v : α) (e : PyExc), o.dictGet c.value2member v = .error e →
        e.className ≠ "KeyError" → e.className ≠ "TypeError" → c.enumNew o none v false .none = .error e) := by
  intro h
  have := h PV pvOps cA (.key 1 (some "TSub") none 0) (.named "TSub" "hash") (by decide +kernel) (by decide)
    (by decide)
  revert this
  decide +kernel

private theorem enumNew_typeErrorSubclass_member :
    cA.enumNew pvOps none (.key 1 (some "TSub") none 0) false .none = .ok ['A'] := by
  decide +kernel

/-- The earlier clause of `ValueAliasPaths`, an exception whose class is not named `TypeError` goes out, is false: for a
value whose `__hash__` raises a subclass of `TypeError`, `E.A._add_value_alias_(v)` files it in the unhashable lists under
`'A'`, as on 3.15.2. -/
private theorem valueAlias_typeErrorSubclass :
    ¬ (∀ (α : Type) (o : Ops α) (c : EClassG α) (f : Name → Name) (m : Name) (v : α) (e : PyExc),
        o.dictGet c.value2member v = .error e → e.className ≠ "TypeError" → c.addValueAlias o f m v = .error e) := by
  intro h
  have := h PV pvOps cA id ['A'] (.key 5 (some "TSub") none 0) (.named "TSub" "hash") (by decide +kernel) (by decide)
  revert this
  decide +kernel

private theorem valueAlias_typeErrorSubclass_filed :
    (cA.addValueAlias pvOps id ['A'] (.key 5 (some "TSub") none 0)).map (·.unhashableMap) =
      .ok [(['A'], [.key 5 (some "TSub") none 0])] := by
  decide +kernel

/-- The earlier clause of `SetNamePaths`, any exception of `_member_type_(*args)` gives the `TypeError`, is false: `:264`
is `except Exception`, so a `BaseException` subclass `BExc` raised by the mixin's own call goes out, as on 3.15.2. -/
private theorem setName_baseException :
    ¬ (∀ (α : Type) (o : Ops α) (mk : Maker α) (value : α) (e : PyExc), mk.newMember = .ok none → mk.plain = false →
        mk.callType = .error e →
        mk.memberValue o value = .error (.typeError "_value_ not set in __new__, unable to create it")) := by
  intro h
  have := h PV pvOps { plain := false, callType := .error (.named "BExc" "b") } (.str "b") (.named "BExc" "b") rfl rfl rfl
  revert this
  decide +kernel

/-- `KT(KeyError, TypeError)` raised by both `__hash__` and `__eq__`: the `TypeError` side runs the linear search, the
`KeyError` side of the `__eq__` there makes a new member, and `setdefault`'s `TypeError` files it as unhashable, as on
3.15.2: `(['A', 'B'], ['A', 'B'], 1)`. -/
private theorem setName_twoBases :
    (cA.setName pvOps {} ['B'] (.key 1 (some "KT") (some "KT") 0)).map
      (fun c => (c.memberNames, c.memberMap.map Prod.fst, c.unhashableValues.length)) =
      .ok ([['A'], ['B']], [['A'], ['B']], 1) := by
  decide +kernel

/-! ### `%r` of `_missing_`'s outcome and of members: the witnesses -/

/-- `_missing_` raising `BExc(7)`, a `BaseException`, for `R()` whose `__repr__` raises `KeyError`: `E2(R())` raises `BExc`,
since :1207 catches only `Exception` and the `%r` of :1220 never runs; the earlier clause, every non-member outcome raising
the `repr`'s exception first, is false. -/
private theorem enumNew_baseException :
    ¬ (∀ (α : Type) (o : Ops α) (c : EClassG α) (v : α) (e e' : PyExc), c.memberMap.isEmpty = false →
        o.repr v = .error e' → c.afterSearch o false (o.repr v) (.raises e) = .error e') := by
  intro h
  have := h PV pvOps cA (.robj "KeyError" 0) (.named "BExc" "7") (.keyError "'repr'") rfl rfl
  revert this
  decide +kernel

/-- `_missing_` returning an object whose `__repr__` raises `LookupError`: the `TypeError` of :1224-1227 formats it, so
`LookupError` goes out. -/
private theorem enumNew_otherBadRepr :
    cA.enumNew pvOps none (.int 5) false (.other (.error (.named "LookupError" "repr"))) =
      .error (.named "LookupError" "repr") := by
  decide +kernel

/-- A class with members `A = 1`, `B = 2` and a `__repr__` of its own that raises `LookupError`. -/
private def w2 : EClassG PV :=
  { memberNames := [['A'], ['B']], memberMap := [(['A'], ['A']), (['B'], ['B'])],
    values := [(['A'], .int 1), (['B'], .int 2)], value2member := [(.int 1, ['A']), (.int 2, ['B'])],
    hashableValues := [.int 1, .int 2], reprErr := some (.named "LookupError" "") }

/-- `W2.B._add_value_alias_(1)`: the `ValueError` of :1244 formats `W2.A`, whose `__repr__` raises; the earlier clause,
which formatted only its `_value_`, is false. -/
private theorem valueAlias_classRepr :
    ¬ (∀ (α : Type) (o : Ops α) (c : EClassG α) (f : Name → Name) (self m : Name) (v x : α),
        o.dictGet c.value2member v = .ok (some m) → m ≠ self → (∃ s, o.repr v = .ok s) →
        c.values.lookup m = some x → (∃ s, o.repr x = .ok s) → (c.addValueAlias o f self v).raises "ValueError") := by
  intro h
  obtain ⟨e, he, hc⟩ := h PV pvOps w2 id ['B'] ['A'] (.int 1) (.int 1) (by decide +kernel) (by decide) ⟨_, rfl⟩ rfl ⟨_, rfl⟩
  have : w2.addValueAlias pvOps id ['B'] (.int 1) = .error (.named "LookupError" "") := by decide +kernel
  rw [this] at he
  cases he
  simp [PyExc.className] at hc

/-- `_add_member_` on a name bound to another member formats that member: with a raising `__repr__` it is that
exception, not the `NameError` (:1074). -/
private theorem addMember_classRepr : w2.addToMap pvOps ['A'] ['B'] = .error (.named "LookupError" "") := by
  decide +kernel

end PyLean.CoreLibs.EnumDC
