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

/-! ### `StrEnum.__new__` -/

/-- The sentence the earlier model proved, on the mirror that has `bytes`: a member takes one `str` or nothing, and any
other argument list is a `TypeError`, as the docstring's "values must already be of type `str`" says. False:
`A = b'x', 'ascii'` makes the member `'x'`, through `str(b'x', 'ascii')` at Lib/enum.py:1391. -/
def StrEnumValues : Prop :=
  ∀ (codec : Codec) (l : List (SArg PV)) (s : String),
    strEnumNewG codec l = .ok s ↔ (l = [] ∧ s = "") ∨ l = [.str s]

theorem strEnumValues_refuted : ¬StrEnumValues := by
  intro h
  have h1 : strEnumNewG pyCodec [SArg.bytes (α := PV) [120], .str "ascii"] = .ok "x" := by decide +kernel
  rcases (h pyCodec _ _).1 h1 with ⟨h2, _⟩ | h2 <;> simp at h2

/-- `StrEnum.__new__`, for every codec and every argument list: it succeeds exactly with no argument (`''`), one `str`
(itself), or a `bytes` with a `str` encoding and optionally a `str` errors (`'strict'` when not given), which the codec
decodes; every other exception is a `TypeError`, and the codec's are only raised for a `bytes` first argument. -/
def StrEnumNewRules : Prop :=
  ∀ (α : Type) (codec : Codec) (l : List (SArg α)) (s : String),
    (strEnumNewG codec l = .ok s ↔
      (l = [] ∧ s = "") ∨ l = [.str s] ∨
      (∃ b enc, l = [.bytes b, .str enc] ∧ strDecode codec b enc "strict" = .ok s) ∨
      (∃ b enc er, l = [.bytes b, .str enc, .str er] ∧ strDecode codec b enc er = .ok s)) ∧
    ∀ e, strEnumNewG codec l = .error e →
      e.className = "TypeError" ∨ ∃ b enc er, l.head? = some (.bytes b) ∧ strDecode codec b enc er = .error e

theorem strEnumNewRules_proven : StrEnumNewRules := by
  intro α codec l s
  refine ⟨?_, ?_⟩
  · match l with
    | [] =>
      simp only [strEnumNewG, List.length_nil, Nat.not_lt_zero, ↓reduceIte, Except.ok.injEq, true_and]
      constructor
      · intro h; exact .inl h.symm
      · rintro (h | h | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩)
        · exact h.symm
        all_goals cases h
    | [a] => cases a <;> simp [strEnumNewG]
    | [a, b] =>
      cases a <;> cases b <;> simp [strEnumNewG] <;>
        exact ⟨fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩, fun ⟨_, _, ⟨h1, h2⟩, h⟩ => by subst h1; subst h2; exact h⟩
    | [a, b, c] =>
      cases a <;> cases b <;> cases c <;> simp [strEnumNewG] <;>
        exact ⟨fun h => ⟨_, _, _, ⟨rfl, rfl, rfl⟩, h⟩,
          fun ⟨_, _, _, ⟨h1, h2, h3⟩, h⟩ => by subst h1; subst h2; subst h3; exact h⟩
    | _ :: _ :: _ :: _ :: r => simp [strEnumNewG]
  · intro e h
    match l, h with
    | [], h => simp [strEnumNewG] at h
    | [a], h => cases a <;> simp [strEnumNewG] at h <;> (subst h; left; rfl)
    | [a, b], h =>
      cases a <;> cases b <;> simp [strEnumNewG] at h <;>
        first | (subst h; left; rfl) | (right; exact ⟨_, _, _, rfl, h⟩)
    | [a, b, c], h =>
      cases a <;> cases b <;> cases c <;> simp [strEnumNewG] at h <;>
        first | (subst h; left; rfl) | (right; exact ⟨_, _, _, rfl, h⟩)
    | _ :: _ :: _ :: _ :: _, h =>
      simp [strEnumNewG] at h
      subst h
      left; rfl

/-! ### `EnumType.__call__` -/

/-- The sentence the earlier model proved: a class without members, called with no argument after `value`, raises
`TypeError`. False: `Enum('X', type=int)` creates a class, since :735 tests `names is _not_given and type is None`. -/
def EnumCallShape : Prop :=
  ∀ (o : Ops EV) (c : EClass) (self : Option Name) (a : Atom) (type : Option Nat) (miss : MissingRet),
    c.memberMap.isEmpty = true → (enumCallG o c self a [] type miss).raises "TypeError"

theorem enumCallShape_refuted : ¬EnumCallShape := by
  intro h
  obtain ⟨e, he, _⟩ := h evOps {} none (.str "X") (some 0) .none rfl
  simp [enumCallG] at he

/-- `EnumType.__call__`: on a class with members, `Cls(a)` looks up `a` and `Cls(a, b, ...)` the tuple `(a, b, ...)`,
the `type` keyword not mattering; on a class without, `names` or `type` go to `_create_` with `names` (or `None`), and
with neither it is the `TypeError`. -/
def EnumCallRules : Prop :=
  ∀ (o : Ops EV) (c : EClass) (self : Option Name) (a b : Atom) (r : List Atom) (type : Option Nat) (t : Nat)
    (miss : MissingRet),
    (c.memberMap.isEmpty = false →
      enumCallG o c self a (b :: r) type miss = (c.toG.enumNew o self (.tup (a :: b :: r)) false miss).map .member ∧
      enumCallG o c self a [] type miss = (c.toG.enumNew o self (.atom a) false miss).map .member) ∧
    (c.memberMap.isEmpty = true →
      enumCallG o c self a (b :: r) type miss = .ok (.create a (some b) type) ∧
      enumCallG o c self a [] (some t) miss = .ok (.create a none (some t)) ∧
      (enumCallG o c self a [] none miss).raises "TypeError")

theorem enumCallRules_proven : EnumCallRules := by
  intro o c self a b r type t miss
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_, ?_⟩⟩
  · simp only [enumCallG, h, Bool.not_false, ↓reduceIte, List.isEmpty_cons, Bool.false_eq_true]
    generalize c.toG.enumNew o self _ false miss = x
    cases x <;> rfl
  · simp only [enumCallG, h, Bool.not_false, ↓reduceIte, List.isEmpty_nil]
    generalize c.toG.enumNew o self _ false miss = x
    cases x <;> rfl
  · simp [enumCallG, h]
  · simp [enumCallG, h]
  · exact ⟨_, by simp [enumCallG, h]; rfl, rfl⟩

/-! ### `EnumType.__contains__` -/

/-- The sentence the earlier model proved: a value that is not an `int` is not in a `Flag` class. False: after `_missing_`
raises `ValueError`, :766-769 compare the value with each member value by `==`, so `1.0 in F` and `K(1) in F` are true
for a class with `A = 1`. -/
def FlagClassPaths : Prop :=
  ∀ (α : Type) (o : Ops α) (c : FlagCls) (v : α), o.asInt v = none → c.containsOf o false v = .ok false

theorem flagClassPaths_refuted : ¬FlagClassPaths := by
  intro h
  have h1 := h PV pvOps ⟨"F", [("A", 1)], .strict⟩ (.key 1 none none 0) rfl
  revert h1
  decide +kernel

/-- `value in cls`, every path, for every value and every `==`: a member of the class is in it; for a `Flag` class an
`int` is in it exactly when `_missing_` makes a member of it, is not when `EJECT` gives back an `int`, and with the
`ValueError` of `_missing_` (an `int` out of range under `STRICT`, or anything that is not an `int`) the value is compared
with each member value by `==`, the member value on the left. For any class, that comparison is true when some member
value is the value itself or equal to it, false when no comparison is, and its exception goes out. -/
def ContainsPaths : Prop :=
  ∀ (α : Type) (o : Ops α) (c : FlagCls) (unh hashable : List α) (v : α),
    containsG o true none unh hashable v = .ok true ∧
    c.containsOf o true v = .ok true ∧
    (o.asInt v = none → c.containsOf o false v = o.listIn v (c.members.map fun p => o.ofInt (p.2 : Int))) ∧
    (∀ i, o.asInt v = some i →
      (∀ n m, c.missing i = .ok (.flag n m) → c.containsOf o false v = .ok true) ∧
      (∀ p, c.missing i = .ok (.plain p) → c.containsOf o false v = .ok false) ∧
      (∀ e, c.missing i = .error e → e.className = "ValueError" →
        c.containsOf o false v = o.listIn v (c.members.map fun p => o.ofInt (p.2 : Int)))) ∧
    (containsG o false none unh hashable v = .ok false ↔ ∀ y ∈ unh ++ hashable, o.req y v = .ok false) ∧
    (∀ (pre : List α) (y : α) (post : List α), unh ++ hashable = pre ++ y :: post →
      (∀ z ∈ pre, o.req z v = .ok false) →
      o.req y v ≠ .ok false → containsG o false none unh hashable v = o.req y v)

theorem containsPaths_proven : ContainsPaths := by
  intro α o c unh hashable v
  refine ⟨rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro h
    simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, inLists_eq, PyExc.className]
  · intro i h
    refine ⟨?_, ?_, ?_⟩
    · intro n m hm
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, hm]
    · intro p hp
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, hp]
    · intro e he hc
      simp [FlagCls.containsOf, containsG, FlagCls.missingOf, h, he, hc, inLists_eq]
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

/-- `Flag._missing_` takes only `int`s: anything else is the `ValueError` of :1482-1485, and an `int` goes on to the
range checks. -/
def MissingOf : Prop :=
  ∀ (α : Type) (o : Ops α) (c : FlagCls) (v : α),
    (o.asInt v = none → (c.missingOf o v).raises "ValueError") ∧
    (∀ i, o.asInt v = some i → c.missingOf o v = c.missing i)

theorem missingOf_proven : MissingOf := by
  intro α o c v
  refine ⟨fun h => ⟨_, by simp [FlagCls.missingOf, h]; rfl, rfl⟩, fun i h => by simp [FlagCls.missingOf, h]⟩

/-! ### `verify` -/

/-- The sentence the earlier model proved: `verify` raises `TypeError` on anything that is not an enumeration. False:
`enumeration.__name__` is read at :1970, before the `issubclass` test, so `verify(UNIQUE)(42)` raises `AttributeError`. -/
def VerifyCall : Prop :=
  ∀ (α : Type) (o : Ops α) (order : List α → List α) (c : EClass) (vals : List α) (f : Name → Name)
    (name : Py String) (target : VTarget) (checks : List Check),
    (∀ flag, target ≠ .enum flag) → (verifyCallG o order c vals f name target checks).raises "TypeError"

theorem verifyCall_refuted : ¬VerifyCall := by
  intro h
  obtain ⟨e, he, hc⟩ := h EV evOps id {} [] id (.error (.named "AttributeError" "'int' object has no attribute '__name__'"))
    .notCls [.unique] (by intro flag hf; cases hf)
  simp only [verifyCallG, Except.error.injEq] at he
  subst he
  simp [PyExc.className] at hc

private theorem verifyAll_ok (o : Ops α) (order : List α → List α) (c : EClass) (vals : List α) (f : Name → Name)
    (flag : Bool) (s : String) : ∀ checks : List Check,
    verifyAllG o order c vals f flag s checks = .ok () ↔ ∀ k ∈ checks, verifyOneG o order c vals f flag s k = .ok ()
  | [] => by simp [verifyAllG]
  | k :: r => by
    simp only [verifyAllG, List.mem_cons, forall_eq_or_imp]
    cases h : verifyOneG o order c vals f flag s k with
    | error e => simp
    | ok u => simpa using verifyAll_ok o order c vals f flag s r

private theorem verifyAll_first (o : Ops α) (order : List α → List α) (c : EClass) (vals : List α) (f : Name → Name)
    (flag : Bool) (s : String) (e : PyExc) : ∀ (pre : List Check) (k : Check) (post : List Check),
    (∀ k' ∈ pre, verifyOneG o order c vals f flag s k' = .ok ()) → verifyOneG o order c vals f flag s k = .error e →
    verifyAllG o order c vals f flag s (pre ++ k :: post) = .error e
  | [], k, post, _, hk => by simp [verifyAllG, hk]
  | k' :: pre, k, post, hp, hk => by
    simp only [List.cons_append, verifyAllG, hp k' (by simp)]
    exact verifyAll_first o order c vals f flag s e pre k post (fun x hx => hp x (by simp [hx])) hk

/-- `verify.__call__`: an exception reading `__name__` comes first; then something that is not a class is the `TypeError`
of `issubclass`, a class that is not an `Enum` the decorator's own `TypeError`; on an enumeration the checks run in order,
the first that fails is the exception, and it passes exactly when each does. `NAMED_FLAGS` passes exactly when no alias
has a bit outside the values of the members. -/
def VerifyCallRules : Prop :=
  ∀ (α : Type) (o : Ops α) (order : List α → List α) (c : EClass) (vals : List α) (f : Name → Name)
    (checks : List Check),
    (∀ e target, verifyCallG o order c vals f (.error e) target checks = .error e) ∧
    (∀ s, verifyCallG o order c vals f (.ok s) .notCls checks =
        .error (.typeError "issubclass() arg 1 must be a class") ∧
      verifyCallG o order c vals f (.ok s) .cls checks =
        .error (.typeError "the 'verify' decorator only works with Enum and Flag") ∧
      ∀ flag, (verifyCallG o order c vals f (.ok s) (.enum flag) checks = .ok () ↔
        ∀ k ∈ checks, verifyOneG o order c vals f flag s k = .ok ()) ∧
        ∀ pre k post e, checks = pre ++ k :: post → (∀ k' ∈ pre, verifyOneG o order c vals f flag s k' = .ok ()) →
          verifyOneG o order c vals f flag s k = .error e →
          verifyCallG o order c vals f (.ok s) (.enum flag) checks = .error e) ∧
    (c.verifyNamed = .ok () ↔ ∀ p ∈ c.memberMap, c.memberNames.contains p.1 = false → ∀ v,
      c.valueOf p.2 = some (.atom (.int v)) → ∀ b ∈ bitsOf v.toNat, (b : Int) ∈ c.intValues)

theorem verifyCallRules_proven : VerifyCallRules := by
  intro α o order c vals f checks
  refine ⟨fun e target => rfl, fun s => ⟨rfl, rfl, fun flag => ⟨verifyAll_ok o order c vals f flag s checks, ?_⟩⟩, ?_⟩
  · intro pre k post e hc hp hk
    subst hc
    exact verifyAll_first o order c vals f flag s e pre k post hp hk
  · have hm : ∀ p, c.missesName p = true ↔ c.memberNames.contains p.1 = false ∧ ∃ v,
        c.valueOf p.2 = some (.atom (.int v)) ∧ ∃ b ∈ bitsOf v.toNat, (b : Int) ∉ c.intValues := by
      intro p
      unfold EClass.missesName
      by_cases hc : c.memberNames.contains p.1 = true
      · simp only [hc, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, false_and]
      · have hc' : c.memberNames.contains p.1 = false := Bool.eq_false_iff.2 hc
        simp only [hc', Bool.false_eq_true, ↓reduceIte, true_and]
        cases hv : c.valueOf p.2 with
        | none => simp
        | some w =>
          cases w with
          | atom a =>
            cases a with
            | int v =>
              simp only [List.any_eq_true, Bool.not_eq_true', Option.some.injEq, EV.atom.injEq, Atom.int.injEq]
              constructor
              · rintro ⟨b, hb, hq⟩
                exact ⟨v, rfl, b, hb, by simpa using hq⟩
              · rintro ⟨u, rfl, b, hb, hq⟩
                exact ⟨b, hb, by simpa using hq⟩
            | _ => simp
          | _ => simp
    simp only [EClass.verifyNamed]
    cases h : c.memberMap.any c.missesName with
    | true =>
      simp only [↓reduceIte, reduceCtorEq, false_iff]
      intro hall
      obtain ⟨p, hp, hq⟩ := List.any_eq_true.1 h
      obtain ⟨h1, v, h2, b, h3, h4⟩ := (hm p).1 hq
      exact h4 (hall p hp h1 v h2 b h3)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, true_iff]
      intro p hp hc v hv b hb
      apply Classical.byContradiction
      intro hn
      have : c.memberMap.any c.missesName = true :=
        List.any_eq_true.2 ⟨p, hp, (hm p).2 ⟨hc, v, hv, b, hb, hn⟩⟩
      rw [h] at this
      exact Bool.noConfusion this

/-! ### `Enum.__new__` -/

/-- `Enum.__new__`, every path, for every `hash` and `==`: a member comes back as it is; a value the dict lookup finds is
that member; a `KeyError` from the lookup, from `__hash__` or from `__eq__` skips the long search, a `TypeError` from any
of them runs it, and any other exception goes out. The long search looks the name it finds up again, by `cls[name]`,
checks the unhashable lists first, and compares `value == member._value_` with the value on the left. After it, no members
is a `TypeError`, and otherwise `_missing_` decides: its member, `None` as `ValueError`, anything else as `TypeError`, and
its exception as it is. Docs of `_missing_`. -/
def EnumLookupG : Prop :=
  ∀ (α : Type) (o : Ops α) (c : EClassG α) (m : Name) (v : α) (ip : Bool) (miss : MissingRet),
    c.enumNew o (some m) v ip miss = .ok m ∧
    (∀ n, o.dictGet c.value2member v = .ok (some n) → c.enumNew o none v ip miss = .ok n) ∧
    (o.dictGet c.value2member v = .ok none → c.enumNew o none v ip miss = c.afterSearch ip miss) ∧
    (∀ e, o.dictGet c.value2member v = .error e →
      (e.className = "KeyError" → c.enumNew o none v ip miss = c.afterSearch ip miss) ∧
      (e.className = "TypeError" → c.enumNew o none v ip miss =
        match c.longSearch o v with
        | .error e' => .error e'
        | .ok (some n) => .ok n
        | .ok none => c.afterSearch ip miss) ∧
      (e.className ≠ "KeyError" → e.className ≠ "TypeError" → c.enumNew o none v ip miss = .error e)) ∧
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
    (c.memberMap.isEmpty = false →
      c.afterSearch ip (.member m) = .ok m ∧ (c.afterSearch ip .none).raises "ValueError" ∧
      (c.afterSearch ip .other).raises "TypeError" ∧ ∀ e, c.afterSearch ip (.raises e) = .error e) ∧
    (c.memberMap.isEmpty = true → (c.afterSearch ip miss).raises "TypeError")

theorem enumLookupG_proven : EnumLookupG := by
  intro α o c m v ip miss
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n h; simp [EClassG.enumNew, h]
  · intro h; simp [EClassG.enumNew, h]
  · intro e h
    refine ⟨fun hk => ?_, fun ht => ?_, fun hk ht => ?_⟩
    · simp [EClassG.enumNew, h, hk]
    · simp only [EClassG.enumNew, h, ht]
      simp only [show ("TypeError" == "KeyError") = false by decide, show ("TypeError" == "TypeError") = true by decide,
        Bool.false_eq_true, ↓reduceIte]
      try rfl
    · have h1 : (e.className == "KeyError") = false := by simp [hk]
      have h2 : (e.className == "TypeError") = false := by simp [ht]
      simp [EClassG.enumNew, h, h1, h2]
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
  · intro h
    refine ⟨by simp [EClassG.afterSearch, h], ⟨_, by simp [EClassG.afterSearch, h]; rfl, rfl⟩,
      ⟨_, by simp [EClassG.afterSearch, h]; rfl, rfl⟩, fun e => by simp [EClassG.afterSearch, h]⟩
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
other calls `_member_type_(*args)`, whose exception becomes the `TypeError` "_value_ not set in __new__, unable to create
it"; then `__init__`, whose exception goes out. The alias search: what the dict lookup finds or does not find decides; a
`KeyError` from the lookup, `__hash__` or `__eq__` makes a new member; a `TypeError` runs the linear search, which compares
`canonical._value_ == value` (no identity shortcut), and in which a `KeyError` again makes a new member and any other
exception goes out. An alias is added to `_member_map_` only; a new member also goes to `_member_names_` (for a `Flag`,
when its value is a single bit). The tables: `setdefault` and `value not in _hashable_values_`, a `TypeError` from either
filing the value in the unhashable lists under the member's name, and any other exception going out. -/
def SetNamePaths : Prop :=
  ∀ (α : Type) (o : Ops α) (mk : Maker α) (c : EClassG α) (name : Name) (value v : α),
    (∀ e, mk.newMember = .error e → mk.memberValue value = .error e) ∧
    (mk.newMember = .ok (some v) → mk.memberValue value = mk.init.map (fun _ => v)) ∧
    (mk.newMember = .ok none → mk.plain = true → mk.memberValue value = mk.init.map (fun _ => value)) ∧
    (mk.newMember = .ok none → mk.plain = false → mk.callType = .ok v → mk.memberValue value = mk.init.map (fun _ => v)) ∧
    (mk.newMember = .ok none → mk.plain = false → ∀ e, mk.callType = .error e →
      mk.memberValue value = .error (.typeError "_value_ not set in __new__, unable to create it")) ∧
    (∀ e, mk.memberValue value = .error e → c.setName o mk name value = .error e) ∧
    (∀ r, o.dictGet c.value2member v = .ok r → c.aliasOf o v = .ok r) ∧
    (∀ e, o.dictGet c.value2member v = .error e → e.className = "KeyError" → c.aliasOf o v = .ok none) ∧
    (∀ e, o.dictGet c.value2member v = .error e → e.className = "TypeError" →
      (∀ r, c.firstEqual o v c.memberMap = .ok r → c.aliasOf o v = .ok r) ∧
      (∀ e', c.firstEqual o v c.memberMap = .error e' → e'.className = "KeyError" → c.aliasOf o v = .ok none) ∧
      (∀ e', c.firstEqual o v c.memberMap = .error e' → e'.className ≠ "KeyError" → c.aliasOf o v = .error e')) ∧
    (∀ e, o.dictGet c.value2member v = .error e → e.className ≠ "KeyError" → e.className ≠ "TypeError" →
      c.aliasOf o v = .error e) ∧
    (∀ n m x r, c.values.lookup m = some x → c.firstEqual o v ((n, m) :: r) =
      match o.eq x v with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => c.firstEqual o v r) ∧
    (mk.memberValue value = .ok v →
      (∀ e, (c.flagUpdate o v).aliasOf o v = .error e → c.setName o mk name value = .error e) ∧
      (∀ m, (c.flagUpdate o v).aliasOf o v = .ok (some m) →
        c.setName o mk name value = ((c.flagUpdate o v).addToMap name m).bind (fun c2 => c2.noteValue o name m v)) ∧
      ((c.flagUpdate o v).aliasOf o v = .ok none →
        c.setName o mk name value =
          ({ c.flagUpdate o v with
              memberNames := if !(c.flagUpdate o v).isFlag || (match o.asInt v with
                  | some n => isSingleBitInt n
                  | none => false) then (c.flagUpdate o v).memberNames ++ [name] else (c.flagUpdate o v).memberNames,
              values := (c.flagUpdate o v).values ++ [(name, v)] }.addToMap name name).bind
            (fun c3 => c3.noteValue o name name v))) ∧
    (∀ m e, o.setDefault c.value2member v m = .error e → e.className = "TypeError" →
      c.noteValue o name m v = .ok { c with unhashableValues := c.unhashableValues ++ [v],
                                             unhashableMap := appendToG c.unhashableMap name v }) ∧
    (∀ m e, o.setDefault c.value2member v m = .error e → e.className ≠ "TypeError" → c.noteValue o name m v = .error e) ∧
    (∀ m d w, o.setDefault c.value2member v m = .ok (d, w) →
      (o.listIn v c.hashableValues = .ok false →
        c.noteValue o name m v = .ok { c with value2member := d, hashableValues := c.hashableValues ++ [v] }) ∧
      (o.listIn v c.hashableValues = .ok true → c.noteValue o name m v = .ok { c with value2member := d }) ∧
      (∀ e, o.listIn v c.hashableValues = .error e → e.className = "TypeError" →
        c.noteValue o name m v = .ok { c with value2member := d, unhashableValues := c.unhashableValues ++ [v],
                                               unhashableMap := appendToG c.unhashableMap name v }) ∧
      (∀ e, o.listIn v c.hashableValues = .error e → e.className ≠ "TypeError" → c.noteValue o name m v = .error e))

theorem setNamePaths_proven : SetNamePaths := by
  intro α o mk c name value v
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e h; simp [Maker.memberValue, h]
  · intro h; simp only [Maker.memberValue, h]; cases mk.init <;> rfl
  · intro h hp; simp only [Maker.memberValue, h, hp, ↓reduceIte]; cases mk.init <;> rfl
  · intro h hp hc; simp only [Maker.memberValue, h, hp, hc, Bool.false_eq_true, ↓reduceIte]; cases mk.init <;> rfl
  · intro h hp e hc; simp [Maker.memberValue, h, hp, hc]
  · intro e h; simp [EClassG.setName, h]
  · intro r h; simp [EClassG.aliasOf, h]
  · intro e h hk
    simp [EClassG.aliasOf, h, hk]
  · intro e h ht
    refine ⟨fun r hr => by simp [EClassG.aliasOf, h, ht, hr], fun e' he hk => by simp [EClassG.aliasOf, h, ht, he, hk],
      fun e' he hk => by simp [EClassG.aliasOf, h, ht, he, className_bne hk]⟩
  · intro e h hk ht
    simp [EClassG.aliasOf, h, className_bne hk, className_bne ht]
  · intro n m x r hx
    simp only [EClassG.firstEqual, hx]
    try rfl
  · intro hv
    refine ⟨fun e he => by simp [EClassG.setName, hv, he], fun m hm => ?_, fun hn => ?_⟩
    · simp only [EClassG.setName, hv, hm]
      generalize (c.flagUpdate o v).addToMap name m = x
      cases x <;> rfl
    · simp only [EClassG.setName, hv, hn]
      generalize EClassG.addToMap _ name name = x
      cases x <;> rfl
  · intro m e h ht
    simp [EClassG.noteValue, h, ht]
  · intro m e h ht
    simp [EClassG.noteValue, h, className_bne ht]
  · intro m d w h
    refine ⟨fun hl => by simp [EClassG.noteValue, h, hl], fun hl => by simp [EClassG.noteValue, h, hl],
      fun e hl ht => by simp [EClassG.noteValue, h, hl, ht],
      fun e hl ht => by simp [EClassG.noteValue, h, hl, className_bne ht]⟩

/-! ### `Enum._add_value_alias_` -/

/-- `Enum._add_value_alias_`, every path, for every `hash` and `==`: a value another member has in the map is the
`ValueError`, one this member has is nothing, a new one is bound; a `TypeError` from the lookup runs the search over the
members' `_value_`, in which a value another member has raises that `TypeError` again (it formats the `ValueError` with
`map[value]`), one this member has is nothing, and a new one is bound; any other exception goes out. Binding is
`setdefault` and an append, or with a `TypeError` the unhashable lists under `self.name`. -/
def ValueAliasPaths : Prop :=
  ∀ (α : Type) (o : Ops α) (c : EClassG α) (f : Name → Name) (self : Name) (v : α),
    (∀ m, o.dictGet c.value2member v = .ok (some m) → m ≠ self → (c.addValueAlias o f self v).raises "ValueError") ∧
    (o.dictGet c.value2member v = .ok (some self) → c.addValueAlias o f self v = .ok c) ∧
    (o.dictGet c.value2member v = .ok none → c.addValueAlias o f self v = c.bindValue o f self v) ∧
    (∀ e, o.dictGet c.value2member v = .error e → e.className = "TypeError" →
      (∀ m, c.firstMemberEq o v c.memberMap = .ok (some m) → m ≠ self → c.addValueAlias o f self v = .error e) ∧
      (c.firstMemberEq o v c.memberMap = .ok (some self) → c.addValueAlias o f self v = .ok c) ∧
      (c.firstMemberEq o v c.memberMap = .ok none → c.addValueAlias o f self v = c.bindValue o f self v) ∧
      (∀ e', c.firstMemberEq o v c.memberMap = .error e' → c.addValueAlias o f self v = .error e')) ∧
    (∀ e, o.dictGet c.value2member v = .error e → e.className ≠ "TypeError" → c.addValueAlias o f self v = .error e) ∧
    (∀ n m x r, c.values.lookup m = some x → c.firstMemberEq o v ((n, m) :: r) =
      match o.eq x v with
      | .error e => .error e
      | .ok true => .ok (some m)
      | .ok false => c.firstMemberEq o v r) ∧
    (∀ d w, o.setDefault c.value2member v self = .ok (d, w) →
      c.bindValue o f self v = .ok { c with value2member := d, hashableValues := c.hashableValues ++ [v] }) ∧
    (∀ e, o.setDefault c.value2member v self = .error e → e.className = "TypeError" →
      c.bindValue o f self v = .ok { c with unhashableValues := c.unhashableValues ++ [v],
                                            unhashableMap := appendToG c.unhashableMap (f self) v }) ∧
    (∀ e, o.setDefault c.value2member v self = .error e → e.className ≠ "TypeError" →
      c.bindValue o f self v = .error e)

theorem valueAliasPaths_proven : ValueAliasPaths := by
  intro α o c f self v
  refine ⟨fun m h hm => ⟨_, by simp [EClassG.addValueAlias, h, hm]; rfl, rfl⟩, fun h => by
    simp [EClassG.addValueAlias, h], fun h => by simp [EClassG.addValueAlias, h], fun e h ht => ⟨fun m hm hne => by
    simp [EClassG.addValueAlias, h, ht, hm, hne], fun hm => by simp [EClassG.addValueAlias, h, ht, hm], fun hm => by
    simp [EClassG.addValueAlias, h, ht, hm], fun e' he => by simp [EClassG.addValueAlias, h, ht, he]⟩,
    fun e h ht => by simp [EClassG.addValueAlias, h, className_bne ht], fun n m x r hx => ?_, fun d w h => by
    simp [EClassG.bindValue, h], fun e h ht => by simp [EClassG.bindValue, h, ht], fun e h ht => by
    simp [EClassG.bindValue, h, className_bne ht]⟩
  simp only [EClassG.firstMemberEq, hx]
  try rfl

/-- A class with members `A` and `B` and the given values, built by the mirror. -/
def twoG (a b : EV) : EClassG EV :=
  { memberNames := [['A'], ['B']], memberMap := [(['A'], ['A']), (['B'], ['B'])], values := [(['A'], a), (['B'], b)] }

/-- A value linked to a member is a `ValueError` for any other member, the docs of `_add_value_alias_`. False for an
unhashable value: the check at Lib/enum.py:1246-1247 reads the `_value_` of the members only, so a value linked with
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
`ValueError` is formatted with `cls._value2member_map_[value]` at :1249, which hashes the value again and raises
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
    (∀ items d' e, d.setAll items = (d', some e) → e.className = "AttributeError" →
      d.update (.mapping items) more =
        (d'.unpackKeys (items.map Prod.fst)).bind (fun d'' => d''.update (.pairs []) more)) ∧
    (∀ items d' e, d.setAll items = (d', some e) → e.className ≠ "AttributeError" →
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
  · simp [EnumDict.update, h, className_bne ha]

/-- `_ignore_` given as a tuple of names ignores those names, as a list does: `list(value)` at :379. -/
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

end PyLean.CoreLibs.EnumDC
