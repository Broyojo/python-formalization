import PyLean.CoreLibs.Coll.UserList

/-!
Properties of `UserList`. `ops` is any behaviour of the wrapped `list`, so these say what
the wrapper adds, whatever `list` does.
-/

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.RangeSlice (Slice)

variable {α : Type}

theorem uStep_data (ops : ListOps α) (c : LOp α) (u : UL α) :
    uStep ops c u = (lStep ops c u.data).map (fun l => { u with data := l }) := by
  cases c
  case pop i =>
    simp only [uStep, lStep, ulPop, Except.map]
    cases ops.pop u.data i <;> rfl
  all_goals rfl

/-- A `UserList` simulates a `list`: for every program of mutating calls (`append`, `insert`,
`pop`, `remove`, `clear`, `extend`, `reverse`, `sort`, item and slice assignment and
deletion, `+=`, `*=`), run on a `UserList` and on a `list` with the same contents, the two
stop at the same exception or end with the same contents, and `self.__class__` is kept.
Doc/library/collections.rst: "Class that simulates a list. The instance's contents are kept
in a regular list". -/
def UserListSimulatesList : Prop :=
  ∀ (α : Type) (ops : ListOps α) (prog : List (LOp α)) (cls : String) (l : List α),
    runU ops prog ⟨cls, l⟩ = (runL ops prog l).map (fun r => ⟨cls, r⟩)

theorem userListSimulatesList_proven : UserListSimulatesList := by
  intro α ops prog cls l
  induction prog generalizing l with
  | nil => rfl
  | cons c t ih =>
    simp only [runU, runL, uStep_data]
    cases h : lStep ops c l with
    | error e => simp [bind, Except.bind, Except.map, h]
    | ok l' =>
      simp only [h, Except.map, bind, Except.bind]
      exact ih l'

/-- The read-only methods answer as the wrapped `list` does: `len`, `in`, `count`, `index`,
item access, `repr`, and a slice is the list's slice re-wrapped in `self.__class__`
(`__getitem__`, :1272-1273). -/
def UserListObservers : Prop :=
  ∀ (α : Type) (ops : ListOps α) (u : UL α) (x : α) (i : Int) (s : Slice) (a b : Option Int),
    ulLen u = u.data.length ∧
    ulContains ops u x = ops.contains u.data x ∧
    ulCount ops u x = ops.count u.data x ∧
    ulIndex ops u x a b = ops.index u.data x a b ∧
    ulGetitem ops u i = ops.getItem u.data i ∧
    ulRepr ops u = ops.repr u.data ∧
    ulGetslice ops u s = (ops.getSlice u.data s).map (fun l => ⟨u.cls, l⟩) ∧
    ulMul ops u (i) = (ops.repeatL u.data i).map (fun l => ⟨u.cls, l⟩)

theorem userListObservers_proven : UserListObservers := by
  intro α ops u x i s a b
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · simp only [ulGetslice, bind, Except.bind, Except.map, pure, Except.pure]
  · simp only [ulMul, bind, Except.bind, Except.map, pure, Except.pure]

/-- Operand dispatch is coherent across the siblings: `__add__`, `__radd__`, `__iadd__` and
`extend` give the same result for a `UserList`, a `list` or any other iterable with the same
items, concatenating in the right order, and a non-iterable is the same `TypeError`
from each. `__init__` likewise reads the three kinds alike. Comparison against a `UserList`
is comparison against its list (`__cast`, :1262-1263). -/
def UserListOperandsAgree : Prop :=
  ∀ (α : Type) (ops : ListOps α) (u : UL α) (l : List α) (ty cls : String) (op : CmpOp),
    ulAdd u (.user l) = .ok ⟨u.cls, u.data ++ l⟩ ∧ ulAdd u (.list l) = ulAdd u (.user l) ∧
    ulAdd u (.iter ty l) = ulAdd u (.user l) ∧
    ulRadd u (.user l) = .ok ⟨u.cls, l ++ u.data⟩ ∧ ulRadd u (.list l) = ulRadd u (.user l) ∧
    ulRadd u (.iter ty l) = ulRadd u (.user l) ∧
    ulIadd u (.user l) = .ok ⟨u.cls, u.data ++ l⟩ ∧ ulIadd u (.list l) = ulIadd u (.user l) ∧
    ulIadd u (.iter ty l) = ulIadd u (.user l) ∧
    ulExtend u (.user l) = ulIadd u (.user l) ∧ ulExtend u (.list l) = ulIadd u (.user l) ∧
    ulExtend u (.iter ty l) = ulIadd u (.user l) ∧
    (ulAdd u (.noniter ty)).toOption = none ∧
    ulRadd u (.noniter ty) = (ulAdd u (.noniter ty)) ∧
    ulIadd u (.noniter ty) = (ulAdd u (.noniter ty)) ∧
    ulExtend u (.noniter ty) = (ulAdd u (.noniter ty)) ∧
    ulNew cls (some (.user l)) = .ok ⟨cls, l⟩ ∧ ulNew cls (some (.list l)) = .ok ⟨cls, l⟩ ∧
    ulNew cls (some (.iter ty l)) = .ok ⟨cls, l⟩ ∧ (ulNew cls none : Py (UL α)) = .ok ⟨cls, []⟩ ∧
    ulCmp ops op u (.user l) = .ok (ops.rich op u.data l) ∧
    ulCmp ops op u (.list l) = .ok (ops.rich op u.data l)

theorem userListOperandsAgree_proven : UserListOperandsAgree := by
  intro α ops u l ty cls op
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩

/-- `UserList.copy` and `copy.copy` keep the contents and the class. `__copy__` takes a slice
of `self.__dict__["data"]`, `copy` calls the constructor. The difference between the
two is the instance `__dict__`, which the model does not hold. -/
def UserListCopies : Prop :=
  ∀ (α : Type) (u : UL α), ulCopy u = .ok u ∧ ulCopyDunder u = u

theorem userListCopies_proven : UserListCopies := by
  intro α u
  cases u with
  | mk c d => exact ⟨rfl, by simp [ulCopyDunder]⟩

/-- On ints, `sort` and `reverse` through the `UserList` are the real ones: `sort(reverse=r)`
yields the stable order, `reverse` is a reversal, `UserList([..]) * n` repeats it for `n >= 1`
in range, and `==` with a list of the same items is true; equal contents compare `<=`, not `<`. -/
def UserListIntInstance : Prop :=
  ∀ (cls : String) (l : List Int),
    (ulReverse intOps ⟨cls, l⟩).data = l.reverse ∧
    (ulSort intOps ⟨cls, l⟩ false).data = Accel.pySorted none l ∧
    ulCmp intOps .eq ⟨cls, l⟩ (.list l) = .ok true ∧
    ulCmp intOps .le ⟨cls, l⟩ (.list l) = .ok true ∧
    ulCmp intOps .lt ⟨cls, l⟩ (.user l) = .ok false

theorem listRich_refl_le (op : CmpOp) (hop : cmpVal op 0 0 = true) (l : List Int) (h : ∀ n : Nat, cmpVal op n n = true) :
    listRich op l l = true := by
  induction l with
  | nil => exact h 0
  | cons x t ih => simp [listRich, ih]

theorem listRich_lt_self (l : List Int) : listRich .lt l l = false := by
  induction l with
  | nil => simp [listRich, cmpVal]
  | cons x t ih => simp [listRich, ih]

theorem userListIntInstance_proven : UserListIntInstance := by
  intro cls l
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [ulSort, intOps]
  · simp only [ulCmp, ulCast, intOps]
    rw [listRich_refl_le .eq (by simp [cmpVal]) l (by intro n; simp [cmpVal])]
  · simp only [ulCmp, ulCast, intOps]
    rw [listRich_refl_le .le (by simp [cmpVal]) l (by intro n; simp [cmpVal])]
  · simp only [ulCmp, ulCast, intOps]
    rw [listRich_lt_self]

end PyLean.CoreLibs.Coll
