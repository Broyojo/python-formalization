import PyLean.CoreLibs.Coll.UserListG
import PyLean.CoreLibs.Coll.CounterProps2

/-!
Properties of `UserListG.lean`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean

variable {α : Type}

theorem loop_append_items (l : List α) : ∀ xs : List α,
    loopS (fun l (x : α) => (Except.ok (l ++ [x]) : Py (List α))) l xs = (l ++ xs, none)
  | [] => by simp [loopS]
  | x :: xs => by
    simp only [loopS]
    rw [loop_append_items (l ++ [x]) xs]
    simp

/-- **`u += it` is all or nothing; `u.extend(it)` and `list +=` keep what was read.** For every
`UserList` and every iterable that is not a `list` (or `UserList`): if it yields `xs` and then
raises `e`, `u += it` raises `e` and leaves `u` as it was (`list(other)` is built first, :1358),
while `u.extend(it)` and `l += it` on a plain list raise `e` with `xs` already appended; when it
stops normally all three append `xs`. `u + it` and `it + u` build `self.__class__` from
`data + list(it)` and `list(it) + data`, and raise `e` without building anything; a non-iterable's
`TypeError` is raised by all of them with `u` unchanged.

Source: Doc/library/collections.rst, UserList ('simulates a list'); Lib/collections/__init__.py:1338-1359,
:1407-1411; Objects/listobject.c `list_extend`. The difference between `+=` and `extend` is recorded
here as behaviour, not as a bug. -/
def UserListIaddAtomic : Prop :=
  ∀ (α : Type) (u : UL α) (ty : String) (xs : List α) (e : PyExc),
    ulIaddP u (.other ty (.ok ⟨xs, some e⟩)) = (u, some e) ∧
    ulExtendP u (.other ty (.ok ⟨xs, some e⟩)) = (⟨u.cls, u.data ++ xs⟩, some e) ∧
    listExtendP u.data (.other ty (.ok ⟨xs, some e⟩)) = (u.data ++ xs, some e) ∧
    ulIaddP u (.other ty (.ok ⟨xs, none⟩)) = (⟨u.cls, u.data ++ xs⟩, none) ∧
    ulExtendP u (.other ty (.ok ⟨xs, none⟩)) = (⟨u.cls, u.data ++ xs⟩, none) ∧
    listExtendP u.data (.other ty (.ok ⟨xs, none⟩)) = (u.data ++ xs, none) ∧
    ulAddP u (.other ty (.ok ⟨xs, none⟩)) = .ok ⟨u.cls, u.data ++ xs⟩ ∧
    ulRaddP u (.other ty (.ok ⟨xs, none⟩)) = .ok ⟨u.cls, xs ++ u.data⟩ ∧
    ulAddP u (.other ty (.ok ⟨xs, some e⟩)) = .error e ∧
    ulRaddP u (.other ty (.ok ⟨xs, some e⟩)) = .error e ∧
    ulIaddP u (.other ty (.error e)) = (u, some e) ∧
    ulExtendP u (.other ty (.error e)) = (u, some e) ∧
    ulAddP u (.other ty (.error e)) = .error e

theorem userListIaddAtomic_proven : UserListIaddAtomic := by
  intro α u ty xs e
  have hl := loop_append_items u.data xs
  refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp [ulExtendP, listExtendP, forPy, forIt, hl]
  · simp [listExtendP, forPy, forIt, hl]
  · simp [ulExtendP, listExtendP, forPy, forIt, hl]
  · simp [listExtendP, forPy, forIt, hl]

/-- **`UserList(x)`, `copy()` and `copy.copy()` make a new list.** For every class: `UserList(l)`
for an exact `list` (of id `lid`) holds `l`'s items in the new list `freshD`, not `l` itself
(`self.data[:] = initlist`); for a `UserList` the same with its data; for a `list` subclass, what
its `__iter__` yields (`list(initlist)`), not its storage; for any other iterable its items, and
the exception of an iterator that raises; `None` gives `[]`. `u.copy()` and `copy.copy(u)` are new
objects of `u`'s class with a new data list holding `u`'s items.

Source: Lib/collections/__init__.py:1288-1297, :1370-1375, :1392-1393; Doc/library/collections.rst
('the instance's contents are kept in a regular list ... initially set to a copy of list'). -/
def UserListInitCopy : Prop :=
  ∀ (α : Type) (fresh freshD lid : Nat) (cls ty : String) (l xs : List α) (e : PyExc) (u : ULO α),
    ulNewP fresh freshD cls (some (.list lid l)) = .ok ⟨fresh, cls, freshD, l⟩ ∧
    ulNewP fresh freshD cls (some (.user l)) = .ok ⟨fresh, cls, freshD, l⟩ ∧
    ulNewP fresh freshD cls (some (.listSub l (.ok ⟨xs, none⟩))) = .ok ⟨fresh, cls, freshD, xs⟩ ∧
    ulNewP fresh freshD cls (some (.other ty (.ok ⟨xs, none⟩))) = .ok ⟨fresh, cls, freshD, xs⟩ ∧
    ulNewP fresh freshD cls (some (.other ty (.ok ⟨xs, some e⟩))) = .error e ∧
    ulNewP (α := α) fresh freshD cls none = .ok ⟨fresh, cls, freshD, []⟩ ∧
    ulCopyO fresh freshD u = .ok ⟨fresh, u.cls, freshD, u.data⟩ ∧
    ulCopyDunderO fresh freshD u = ⟨fresh, u.cls, freshD, u.data⟩

theorem userListInitCopy_proven : UserListInitCopy := by
  intro α fresh freshD lid cls ty l xs e u
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [ulCopyDunderO]

/-! ### Comparisons -/

/-- **Comparisons are `list_richcompare` on `data`, with the elements' own results and the
operand's reflected method.** For every element type and every pair of element comparisons
(which may raise or return any object): a `UserList` operand compares by its data, like the
equal `list`; two lists of different length are unequal without any element comparison; the
first non-identical pair whose `==` is false decides, `==` giving `False` and the orderings
returning whatever that pair's own comparison returns (or raises); an element `==` that raises
makes the comparison raise; past the end the lengths decide. Against any other object (a tuple, or
`mock.ANY`) the operand's reflected method answers if it does not return `NotImplemented`
(`UserList([1]) == mock.ANY` is `True`); otherwise `==` is `False` and the orderings raise
`TypeError`.

Source: Lib/collections/__init__.py:1302-1318; Objects/listobject.c:3459-3519; the reflected
operands of Doc/reference/datamodel.rst ('rich comparison methods'). -/
def UserListCompareP : Prop :=
  ∀ (α β : Type) [DecidableEq α] (E : ElemOps α β) (op : CmpOp) (u : UL α) (l pre s t : List α) (x y : α)
    (ty : String) (refl : CmpOp → Option (Py β)),
    ulCmpP E op u (.user l) = ulCmpP E op u (.list l) ∧
    (u.data.length ≠ l.length → ulCmpP E .eq u (.list l) = .ok (.bool false)) ∧
    (u.data = pre ++ x :: s → l = pre ++ y :: t → x ≠ y → E.eqB x y = .ok false →
      (op = .eq ∨ u.data.length = l.length) →
      ulCmpP E op u (.list l) = (if op = .eq then .ok (.bool false) else CRes.obj <$> E.rich op x y)) ∧
    (∀ ex, u.data = x :: s → l = y :: t → x ≠ y → E.eqB x y = .error ex →
      (op ≠ .eq ∨ u.data.length = l.length) → ulCmpP E op u (.list l) = .error ex) ∧
    (u.data = pre → l = pre ++ t → op ≠ .eq → ulCmpP E op u (.list l) = .ok (.bool (cmpLen op pre.length l.length))) ∧
    (∀ r, refl op = some r → ulCmpP E op u (.other ty refl) = CRes.obj <$> r) ∧
    (refl op = none → ulCmpP E op u (.other ty refl) =
      if op = .eq then .ok (.bool false)
      else .error (.typeError s!"'{op.sym}' not supported between instances of 'list' and '{ty}'"))

theorem firstDiff_prefix {β : Type} [DecidableEq α] (E : ElemOps α β) :
    ∀ (pre a b : List α), firstDiff E (pre ++ a) (pre ++ b) = firstDiff E a b
  | [], _, _ => rfl
  | p :: pre, a, b => by
    simp only [List.cons_append, firstDiff, eqId, if_pos rfl, ok_bind, if_true]
    exact firstDiff_prefix E pre a b

theorem firstDiff_self {β : Type} [DecidableEq α] (E : ElemOps α β) :
    ∀ (pre : List α), firstDiff E pre pre = .ok none
  | [] => rfl
  | p :: pre => by
    simp only [firstDiff, eqId, if_pos rfl, ok_bind, if_true]
    exact firstDiff_self E pre

theorem userListCompareP_proven : UserListCompareP := by
  intro α β _ E op u l pre s t x y ty refl
  refine ⟨rfl, fun h => ?_, fun hu hl hxy he hop => ?_, fun ex hu hl hxy he hop => ?_,
    fun hu hl hop => ?_, fun r hr => ?_, fun hr => ?_⟩
  · simp [ulCmpP, listRichP, h]
  · have hd : firstDiff E u.data l = .ok (some (x, y)) := by
      rw [hu, hl, firstDiff_prefix]
      simp [firstDiff, eqId, hxy, he]
    simp only [ulCmpP, listRichP]
    by_cases ho : op = .eq
    · subst ho
      by_cases hlen : u.data.length = l.length <;> simp [hlen, hd]
    · have : ¬ (u.data.length ≠ l.length ∧ op = .eq) := fun h => ho h.2
      rw [if_neg this, hd]
      simp [ho]
  · have hd : firstDiff E u.data l = .error ex := by
      rw [hu, hl]
      simp [firstDiff, eqId, hxy, he]
    simp only [ulCmpP, listRichP]
    have : ¬ (u.data.length ≠ l.length ∧ op = .eq) := by
      intro h
      rcases hop with h1 | h1
      · exact h1 h.2
      · exact h.1 h1
    rw [if_neg this, hd]
    rfl
  · have hd : firstDiff E u.data l = .ok none := by
      rw [hu, hl]
      have : firstDiff E (pre ++ []) (pre ++ t) = firstDiff E [] t := firstDiff_prefix E pre [] t
      rw [List.append_nil] at this
      rw [this]
      cases t <;> rfl
    simp only [ulCmpP, listRichP]
    have : ¬ (u.data.length ≠ l.length ∧ op = .eq) := fun h => hop h.2
    rw [if_neg this, hd, hu]
    rfl
  · simp [ulCmpP, hr]
  · simp only [ulCmpP, hr]

/-- **`in` and `count` use each element's `==`, which may raise.** For every element type and
pure `==` `P` (identity first): `x in u` is whether some element is `x` or `==` it, and
`u.count(x)` is how many are; an element whose `==` raises (before any match, for `in`) makes
both raise.

Source: Lib/collections/__init__.py:1320-1321, :1395-1396; Objects/listobject.c:677-690, :3387-3410. -/
def UserListContainsCount : Prop :=
  ∀ (α β : Type) [DecidableEq α] (E : ElemOps α β) (P : α → α → Bool) (u : UL α) (x y : α) (rest : List α)
    (ex : PyExc),
    ((E.eqB = fun a b => .ok (P a b)) →
      (ulContainsP E u x = .ok (u.data.any (fun z => decide (z = x) || P z x)) ∧
       ulCountP E u x = .ok (u.data.countP (fun z => decide (z = x) || P z x)))) ∧
    (u.data = y :: rest → y ≠ x → E.eqB y x = .error ex →
      ulContainsP E u x = .error ex ∧ ulCountP E u x = .error ex)

theorem userListContainsCount_proven : UserListContainsCount := by
  intro α β _ E P u x y rest ex
  refine ⟨fun hE => ⟨?_, ?_⟩, fun hu hyx he => ⟨?_, ?_⟩⟩
  · unfold ulContainsP
    generalize u.data = l
    induction l with
    | nil => rfl
    | cons z zs ih =>
      simp only [ulContainsP.go, eqId, hE]
      by_cases hz : z = x
      · simp [hz]
      · simp only [hz, if_false, ok_bind]
        cases hp : P z x
        · simp [hp, ih, hz]
        · simp [hp]
  · unfold ulCountP
    generalize u.data = l
    induction l with
    | nil => rfl
    | cons z zs ih =>
      simp only [ulCountP.go, eqId, hE]
      by_cases hz : z = x
      · simp [hz, ih, List.countP_cons]
      · cases hp : P z x <;> simp [hz, hp, ih, List.countP_cons]
  · unfold ulContainsP
    rw [hu]
    simp [ulContainsP.go, eqId, hyx, he]
  · unfold ulCountP
    rw [hu]
    simp [ulCountP.go, eqId, hyx, he]

end PyLean.CoreLibs.Coll
