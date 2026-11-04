import PyLean.ListSort.Fallible

/-!
`list.sort` when a comparison changes the list being sorted (Objects/listobject.c `list_sort_impl`,
CPython 3.15.2).

`list_sort_impl` empties the list before sorting (:2984-2994: size 0, `ob_item = NULL`,
`allocated = -1`, "any operation will reset it to >= 0") and sorts the saved array, so user code run by
a comparison sees an empty list and whatever it does to the list cannot reach the array being sorted.
After the sort (:3183-3199), a list whose `allocated` is no longer `-1` raises
`ValueError("list modified during sort")`, unless the sort already failed with another exception
(`result != NULL`); then the saved items are put back and whatever user code left in the list is
released (:3206-3225).

A comparison is modelled by its result, a function of its operands that may raise (`PLt`, as in
`Fallible.lean`), and by its effect on the list: `eff k` is what the `k`-th call of the sort (from 0, in
the order the sort makes them, each counted by `ISLT` whether or not it raises) does to the list as
user code sees it. For a given input the calls are fixed, so an effect that depends on the operands
is an effect that depends on `k`. Scope: a comparison's result does not depend on what earlier calls
did to the list (the list it can see is empty unless it changed it itself).
-/

namespace PyLean.ListSort

open PyLean

variable {α : Type}

/-- The effects of the first `n` comparison calls on the list, in call order. -/
def applyEffs (eff : Nat → LView α → LView α) : Nat → LView α → LView α
  | 0, v => v
  | n + 1, v => eff n (applyEffs eff n v)

/-- The check after the sort, listobject.c:3193-3199: the sort's own exception wins; otherwise a list
user code has touched (`allocated != -1`) is `ValueError("list modified during sort")`. -/
def modifiedCheck (e : Option PyExc) (view : LView α) : Option PyExc :=
  match e with
  | some e => some e
  | none => if view.allocated ≠ -1 then some (.valueError "list modified during sort") else none

/-- `list_sort_impl(self, NULL, reverse)` (:2965-3227) with a comparison that may raise and may change
the list: the sort of the saved items (`listSortCntF`, which also counts the calls), the list as the
`n` calls left it, the check of :3193-3199, and the saved items put back (:3206-3211). -/
def listSortImplFx (lt : PLt α) (eff : Nat → LView α → LView α) (xs : List α) (reverse : Bool) :
    List α × Option PyExc :=
  let (r, n, e) := listSortCntF lt xs reverse
  (r, modifiedCheck e (applyEffs eff n LView.during))

/-- `list_sort_impl(self, keyfunc, reverse)` with a key function that may raise and change the list
(`keysLoop`, :3013-3022) and a comparison of keys that may raise and change the list: a failing key
function goes to `keyfunc_fail` (:3204-3206), past the check, with the items untouched; otherwise the
comparisons act on the list as the key function left it. -/
def listSortKeyImplFx {κ : Type} (lt : PLt κ) (key : α → LView α → Py κ × LView α)
    (eff : Nat → LView α → LView α) (xs : List α) (reverse : Bool) : List α × Option PyExc :=
  match keysLoop key xs LView.during [] with
  | (.error e, _) => (xs, some e)
  | (.ok ks, during) =>
    let (r, n, e) := listSortCntF (fun p q : κ × α => lt p.1 q.1) (ks.zip xs) reverse
    (r.map Prod.snd, modifiedCheck e (applyEffs eff n during))

/-- Once a list operation has given the list an array (`allocated >= 0`), no list operation takes
`allocated` back to `-1`; so if one call gives it an array, the list is still touched at the end. -/
theorem applyEffs_touched (eff : Nat → LView α → LView α)
    (hkeep : ∀ k w, 0 ≤ w.allocated → 0 ≤ (eff k w).allocated) (k : Nat)
    (hk : ∀ w, 0 ≤ (eff k w).allocated) :
    ∀ n v, k < n → 0 ≤ (applyEffs eff n v).allocated := by
  intro n
  induction n with
  | zero => intro v h; omega
  | succ n ih =>
    intro v h
    simp only [applyEffs]
    by_cases hkn : k = n
    · subst hkn; exact hk _
    · exact hkeep n _ (ih v (by omega))

/-- `list.sort()` and `list.sort(key=...)` (listobject.c:2965-3227) for every comparison and key function
that may raise and may change the list being sorted, in any way and as often as they like:

* the items afterwards are those of the same sort with comparisons that leave the list alone
  (`listSortImplF`, `listSortKeyImplF`, whose permutation and stability properties are proven
  elsewhere): what user code did to the list never reaches the result, and what it put in the list is
  dropped;
* an exception of the key function or of a comparison is the exception, whatever was done to the list
  (the check at :3193 needs `result != NULL`);
* otherwise the result is `ValueError("list modified during sort")` exactly when the list's
  `allocated` is no longer `-1` after the last call, and no exception when it is (an operation that
  leaves an empty list without an array, such as `clear()` on it, is not noticed);
* with fewer than two items there is no comparison and so no `ValueError` from comparisons;
* if some comparison call gives the list an array, and list operations never take `allocated` back to
  `-1` (an invariant of every list operation), the sort raises that `ValueError` unless it failed
  otherwise. -/
def SortModified : Prop :=
  ∀ (α κ : Type) (lt : PLt α) (eff : Nat → LView α → LView α) (xs : List α) (reverse : Bool),
    (listSortImplFx lt eff xs reverse).1 = (listSortImplF lt xs reverse).1 ∧
    (∀ e, (listSortImplF lt xs reverse).2 = some e → (listSortImplFx lt eff xs reverse).2 = some e) ∧
    ((listSortImplF lt xs reverse).2 = none →
      ((applyEffs eff (listSortCntF lt xs reverse).2.1 LView.during).allocated ≠ -1 →
        (listSortImplFx lt eff xs reverse).2 = some (.valueError "list modified during sort")) ∧
      ((applyEffs eff (listSortCntF lt xs reverse).2.1 LView.during).allocated = -1 →
        (listSortImplFx lt eff xs reverse).2 = none)) ∧
    (xs.length < 2 → listSortImplFx lt eff xs reverse = (xs, none)) ∧
    ((∀ k w, 0 ≤ w.allocated → 0 ≤ (eff k w).allocated) →
      ∀ k, k < (listSortCntF lt xs reverse).2.1 → (∀ w, 0 ≤ (eff k w).allocated) →
        (listSortImplF lt xs reverse).2 = none →
        (listSortImplFx lt eff xs reverse).2 = some (.valueError "list modified during sort")) ∧
    (∀ (klt : PLt κ) (key : α → LView α → Py κ × LView α),
      (listSortKeyImplFx klt key eff xs reverse).1 = (listSortKeyImplF klt key xs reverse).1 ∧
      (∀ e u, keysLoop key xs LView.during [] = (.error e, u) →
        listSortKeyImplFx klt key eff xs reverse = (xs, some e)) ∧
      (∀ ks u, keysLoop key xs LView.during [] = (.ok ks, u) →
        let run := listSortCntF (fun p q : κ × α => klt p.1 q.1) (ks.zip xs) reverse
        (listSortKeyImplFx klt key eff xs reverse).2 = modifiedCheck run.2.2 (applyEffs eff run.2.1 u) ∧
        (∀ e, run.2.2 = some e → (listSortKeyImplFx klt key eff xs reverse).2 = some e) ∧
        (run.2.2 = none → (applyEffs eff run.2.1 u).allocated ≠ -1 →
          (listSortKeyImplFx klt key eff xs reverse).2 = some (.valueError "list modified during sort")) ∧
        (run.2.2 = none → (applyEffs eff run.2.1 u).allocated = -1 →
          (listSortKeyImplFx klt key eff xs reverse).2 = none)))

theorem sortModified_proven : SortModified := by
  intro α κ lt eff xs reverse
  have hdef : listSortImplFx lt eff xs reverse =
      ((listSortCntF lt xs reverse).1,
        modifiedCheck (listSortCntF lt xs reverse).2.2
          (applyEffs eff (listSortCntF lt xs reverse).2.1 LView.during)) := rfl
  have hF : listSortImplF lt xs reverse = ((listSortCntF lt xs reverse).1, (listSortCntF lt xs reverse).2.2) := rfl
  refine ⟨by rw [hdef, hF], fun e he => ?_, fun he => ⟨fun hv => ?_, fun hv => ?_⟩, fun hl => ?_,
    fun hkeep k hk hka he => ?_, fun klt key => ⟨?_, fun e u hkl => ?_, fun ks u hkl => ?_⟩⟩
  · rw [hF] at he
    simp only at he
    rw [hdef]
    simp only [modifiedCheck, he]
  · rw [hF] at he
    simp only at he
    rw [hdef]
    simp only [modifiedCheck, he, if_pos hv]
  · rw [hF] at he
    simp only at he
    rw [hdef]
    simp only [modifiedCheck, he, hv, ne_eq, not_true_eq_false, if_false]
  · have hc : listSortCntF lt xs reverse = (xs, 0, none) := by
      unfold listSortCntF; rw [if_pos hl]
    rw [hdef, hc]
    simp [modifiedCheck, applyEffs, LView.during]
  · rw [hF] at he
    simp only at he
    have h0 := applyEffs_touched eff hkeep k hka (listSortCntF lt xs reverse).2.1 LView.during hk
    rw [hdef]
    simp only [modifiedCheck, he]
    rw [if_pos (by omega)]
  · unfold listSortKeyImplFx listSortKeyImplF
    cases keysLoop key xs LView.during [] with
    | mk r u =>
      cases r with
      | error e => rfl
      | ok ks => rfl
  · unfold listSortKeyImplFx
    rw [hkl]
  · intro run
    have hk : listSortKeyImplFx klt key eff xs reverse =
        (run.1.map Prod.snd, modifiedCheck run.2.2 (applyEffs eff run.2.1 u)) := by
      unfold listSortKeyImplFx
      rw [hkl]
    rw [hk]
    refine ⟨rfl, fun e he => ?_, fun he hv => ?_, fun he hv => ?_⟩
    · simp only [modifiedCheck, he]
    · simp only [modifiedCheck, he, if_pos hv]
    · simp only [modifiedCheck, he, hv, ne_eq, not_true_eq_false, if_false]

end PyLean.ListSort
