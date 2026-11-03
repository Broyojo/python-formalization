import PyLean.CoreLibs.Operator.Strength

/-!
`itemgetter.__reduce__`, Modules/_operator.c:1191-1198 and Lib/operator.py:307-308, CPython 3.15.2, with the C
object it reads: `nitems`, `item` (the one key, or the argument tuple) and `index` (Modules/_operator.c:1016-1022),
as `itemgetter_new` (:1034-1079) sets them.
-/

namespace PyLean.CoreLibs.Operator

open PyLean

/-- `ig->item`: the key itself for one item (:1045-1047), the argument tuple for more (:1048-1050). -/
inductive IgItem (κ : Type) where
  | one (k : ItemKey κ)
  | tuple (ks : List (ItemKey κ))

/-- `itemgetterobject`, Modules/_operator.c:1016-1022: `index` is `ig->index` when it is not -1. -/
structure IgObj (κ : Type) where
  nitems : Nat
  item : IgItem κ
  index : Option Nat

/-- `itemgetter_new`, Modules/_operator.c:1034-1079: no keywords (:1041-1042), one argument unpacked or the tuple
kept (:1044-1050), and `ig->index` for an exact non-negative `int` that fits (:1058-1074). -/
def igNewC {κ : Type} (args : List (ItemKey κ)) (nkw : Nat) : Py (IgObj κ) :=
  match newArgC "itemgetter" args.length nkw with
  | some e => .error e
  | none =>
    match args with
    | [k] => .ok ⟨1, .one k, fastIndex k⟩
    | ks => .ok ⟨ks.length, .tuple ks, none⟩

/-- `itemgetter_reduce`, Modules/_operator.c:1191-1198: `(type(ig), (item,))` for one item (:1195-1196), so a key
that is itself a tuple is wrapped, and `(type(ig), item)` with the stored argument tuple otherwise (:1197). The
arguments of the result. (An `ig` with `nitems == 1` always holds `.one`, by `itemgetter_new`; the other shape of each
branch is unreachable and gives the keys it holds.) -/
def igReduceC {κ : Type} (ig : IgObj κ) : List (ItemKey κ) :=
  if ig.nitems = 1 then
    match ig.item with
    | .one k => [k]
    | .tuple ks => ks
  else
    match ig.item with
    | .tuple ks => ks
    | .one k => [k]

/-- `__reduce__` round-trips: `type(ig)(*args)` rebuilds the same getter, with the same `nitems`, `item` and
`index`, in C, for every argument list the constructor accepts, and the arguments are the constructor's own. (The
Python twin's `__reduce__`, Lib/operator.py:307-308, returns `self._items`, set at :289 or :294, as it is.) The two
forms of `itemgetter_reduce`: one item gives the 1-tuple `(item,)`, more give the stored
tuple. -/
def ItemgetterReduce : Prop :=
  ∀ (κ : Type) (args : List (ItemKey κ)) (ig : IgObj κ) (k : ItemKey κ) (ks : List (ItemKey κ)) (n : Nat)
    (i : Option Nat),
    (igNewC args 0 = .ok ig →
      igReduceC ig = args ∧ igNewC (igReduceC ig) 0 = .ok ig ∧
      (args.length = 1 ↔ ig.nitems = 1)) ∧
    igReduceC ⟨1, .one k, i⟩ = [k] ∧
    (n ≠ 1 → igReduceC ⟨n, .tuple ks, i⟩ = ks) ∧
    igNewC ([] : List (ItemKey κ)) 0 = .error (.typeError "itemgetter expected 1 argument, got 0")

theorem itemgetterReduce_proven : ItemgetterReduce := by
  intro κ args ig k ks n i
  refine ⟨?_, by simp [igReduceC], ?_, rfl⟩
  · intro h
    match args, h with
    | [], h => simp [igNewC, newArgC] at h
    | [a], h =>
      simp only [igNewC, newArgC, List.length_singleton] at h
      simp at h
      subst h
      exact ⟨by simp [igReduceC], by simp [igNewC, newArgC, igReduceC], by simp⟩
    | a :: b :: rest, h =>
      simp only [igNewC, newArgC, List.length_cons] at h
      simp at h
      subst h
      have hn : rest.length + 1 + 1 ≠ 1 := by omega
      refine ⟨by simp [igReduceC], ?_, by simp⟩
      simp [igNewC, newArgC, igReduceC]
  · intro hn; simp [igReduceC, hn]

end PyLean.CoreLibs.Operator
