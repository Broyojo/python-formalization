import PyLean.CoreLibs.Coll.CounterProps3

/-!
Properties of the generic `Counter` model, continued: `__repr__` and its `except TypeError`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace PyLean.CoreLibs.Coll

open PyLean
open PyLean.Accel.Heapq (Eff SEnv Sorter HO hEnv nSelect pySortedBy pureKey builtinHier Hier isA SortOk)

variable {κ ν : Type} [DecidableEq κ]

/-- `list.sort` propagates: on two or more items and a comparison that always raises `e`, the
sort raises `e` (it compares at least once; Objects/listobject.c `list_sort_impl`). A contract on
the parameter, like `SortOk`. -/
def SortRaises (So : Sorter Nat) : Prop :=
  ∀ (β : Type) (cmp : β → β → Eff Nat PyExc Bool) (rev : Bool) (l : List β) (w : Nat) (e : PyExc),
    2 ≤ l.length → (∀ a b, cmp a b = Eff.raise e) → ((So.sort cmp rev l).run w).1 = .error e

theorem mostCommon_raises [DecidableEq ν] [Inhabited ν] (N : Num ν) (So : Sorter Nat) (hSo : SortRaises So)
    (d : D κ ν) (e : PyExc) (hd : 2 ≤ d.length) (hlt : ∀ x y, N.lt x y = .error e) :
    mostCommon N So d none = .error e := by
  show Except.map unObj ((pySortedBy (mcEnv N (itemObjs d)) So (some (pureKey getCount)) true .src).run 0).1 = _
  simp only [pySortedBy, Eff.run_bind]
  have h1 : ((mcEnv N (itemObjs d)).toList .src).run 0 = (.ok (itemObjs d), 0) := rfl
  rw [h1]
  simp only
  rw [Accel.Heapq.mapM_pureKey getCount (itemObjs d) 0]
  simp only
  have hc : ∀ (a b : MObj κ ν × MObj κ ν), (mcEnv N (itemObjs d)).lt a.1 b.1 = Eff.raise e := by
    intro a b
    show liftPy (N.lt a.1.2 b.1.2) = _
    rw [hlt]; rfl
  have hs := hSo _ (fun a b => (mcEnv N (itemObjs d)).lt a.1 b.1) true
    (((itemObjs d).map getCount).zip (itemObjs d)) 0 e (by simp [itemObjs]; omega) hc
  rcases hrun : (So.sort (fun a b => (mcEnv N (itemObjs d)).lt a.1 b.1) true
    (((itemObjs d).map getCount).zip (itemObjs d))).run 0 with ⟨r, w⟩
  rw [hrun] at hs
  rw [hrun]
  simp only at hs
  subst hs
  rfl

theorem WF_mergeSort {d : D κ ν} (hw : D.WF d) (f : κ × ν → κ × ν → Bool) : D.WF (d.mergeSort f) := by
  unfold D.WF D.keys at *
  exact ((List.mergeSort_perm d f).map Prod.fst).nodup_iff.2 hw

theorem HashOk_mergeSort {K : KOps κ} {d : D κ ν} (hh : HashOk K d) (f : κ × ν → κ × ν → Bool) :
    HashOk K (d.mergeSort f) := by
  intro k hk
  apply hh k
  unfold D.keys at *
  exact ((List.mergeSort_perm d f).map Prod.fst).mem_iff.1 hk

theorem dictOfPairs_WF {K : KOps κ} {l : D κ ν} (hw : D.WF l) (hh : HashOk K l) : dictOfPairs K l = .ok l := by
  unfold dictOfPairs
  rw [loop_append l [] (by simpa using hw) (by
    intro s' p hp _
    exact dSet_ok s' p.2 (hash_of_mem hh hp))]
  rfl

/-- **`repr` follows `most_common()`, and falls back on insertion order for unorderable
counts.** For every key and count type, every `repr` of keys and counts (free to raise) and
every exception-class relation: an empty counter prints `Cls()`; with counts ordered by a strict
weak order (as `MostCommonSorted`), a non-empty one prints `Cls({...})` with its items in
`most_common()` order; and with counts whose every `<` raises `e` (complex numbers, say), on two
or more items, it prints `Cls({...})` with the items in insertion order when `e` is a
`TypeError` (the `except TypeError` of :756-758), and raises `e` otherwise.

Source: comments, Lib/collections/__init__.py:754 ('dict() preserves the ordering returned by
most_common()') and :757 ('handle case where values are not orderable'). -/
def ReprOrders : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] [Inhabited ν] (K : KOps κ) (N : Num ν) (So : Sorter Nat)
    (H : Hier) (rk : κ → Py String) (rv : ν → Py String) (cls : String) (d : D κ ν), D.WF d → HashOk K d →
    counterRepr K N So H rk rv cls [] = .ok (cls ++ "()") ∧
    (∀ r : ν → ν → Bool, Accel.StrictWeak r → SortOk So →
      N.lt = (fun x y => .ok (r x y)) → N.gt = (fun x y => .ok (r y x)) →
      N.eq = (fun x y => .ok (!r x y && !r y x)) → d ≠ [] →
      counterRepr K N So H rk rv cls d =
        (do let s ← reprDict rk rv (d.mergeSort (fun a b => !r a.2 b.2)); pure (cls ++ "(" ++ s ++ ")"))) ∧
    (∀ e : PyExc, SortRaises So → 2 ≤ d.length → (∀ x y, N.lt x y = .error e) →
      counterRepr K N So H rk rv cls d =
        if isA H e "TypeError" then (do let s ← reprDict rk rv d; pure (cls ++ "(" ++ s ++ ")"))
        else .error e)

theorem reprOrders_proven : ReprOrders := by
  intro κ ν _ _ _ K N So H rk rv cls d hw hh
  refine ⟨rfl, fun r hr hSo hlt hgt heq hne => ?_, fun e hSo hd hlt => ?_⟩
  · have hmc := (mostCommonSorted_proven κ ν N r So d hr hSo hlt hgt heq).1
    have hne' : d.isEmpty = false := by cases d <;> simp_all
    unfold counterRepr
    rw [hne', if_neg (by simp), hmc, ok_bind,
      dictOfPairs_WF (WF_mergeSort hw _) (HashOk_mergeSort hh _)]
    rfl
  · have hne' : d.isEmpty = false := by cases d <;> simp_all
    unfold counterRepr
    rw [hne', if_neg (by simp), mostCommon_raises N So hSo d e hd hlt, error_bind]
    by_cases ht : isA H e "TypeError" = true
    · simp only [ht, if_true, update_nil_WF hw, ok_bind]
    · simp only [ht]; rfl

/-- **`most_common(n)` for a negative `n` is empty.** For every key and count type and every
`list.sort`: `heapq.nlargest` takes its heap path (`n` is neither `1` nor `>= len`) and the
`zip(range(n), it)` takes nothing, so no count is compared.

Source: invariant; `heapq.nlargest` on `n <= 0` (Lib/heapq.py:537-593). -/
def MostCommonNeg : Prop :=
  ∀ (κ ν : Type) [DecidableEq κ] [DecidableEq ν] [Inhabited ν] (N : Num ν) (So : Sorter Nat) (d : D κ ν)
    (n : Int), n < 0 → mostCommon N So d (some n) = .ok []

theorem mostCommonNeg_proven : MostCommonNeg := by
  intro κ ν _ _ _ N So d n hn
  have h1 : n ≠ 1 := by omega
  have h0 : n.toNat = 0 := Int.toNat_of_nonpos (by omega)
  have h2 : ¬ (n ≥ ((itemObjs d).length : Int)) := by omega
  show Except.map unObj ((nSelect (mcEnv N (itemObjs d)) So true true (d.length + 1) n .src
    (some (pureKey getCount))).run 0).1 = _
  simp only [nSelect, h1, if_false, Eff.run_bind, Accel.Heapq.Eff.attempt]
  have hl : ((mcEnv N (itemObjs d)).len .src).run 0 = (.ok (itemObjs d).length, 0) := rfl
  rw [hl]
  simp only [h2, if_false, Accel.Heapq.selHeap, Eff.run_bind, h0]
  rfl

/-- **`Counter.fromkeys` is undefined.** Every call raises `NotImplementedError`.

Source: Doc/library/collections.rst, Counter.fromkeys. -/
def FromkeysUndefined : Prop :=
  ∀ (κ ν α : Type) [DecidableEq κ] (it : List κ) (v : Option ν),
    (counterFromkeys it v : Py α) = .error (.named "NotImplementedError"
      "Counter.fromkeys() is undefined.  Use Counter(iterable) instead.")

theorem fromkeysUndefined_proven : FromkeysUndefined := fun _ _ _ _ _ _ => rfl

/-- `sum` of ints. -/
def intSum (l : List Int) : Py Int := .ok l.sum

/-- **`total()` rises by `n` when `n` elements are counted** (stated on ints only: the row needs a
model of builtin `sum`, whose float path is compensated, before it can be stated for every count
type). Left open. -/
def TotalTracksUpdate : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (K : KOps κ) (xs : List κ) (d : D κ Int), D.WF d → (∀ k ∈ xs, K.hash k = .ok ()) →
    total intSum (update K intNum {} d (.iter (.ok (FIt.ofList xs))) []).1 =
      (total intSum d).map (· + (xs.length : Int))

end PyLean.CoreLibs.Coll
