import PyLean.CoreLibs.Coll.CounterOps

/-!
Properties of `Counter`, part 3: `most_common`, `elements`, `__repr__`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace PyLean.CoreLibs.Coll

open PyLean D

variable {κ : Type} [DecidableEq κ]

/-! ### Positions stand for items -/

theorem atIndices_take (c : Ctr κ) (m : Nat) (hm : m ≤ c.length) :
    atIndices c ((List.range m).map Int.ofNat) = c.take m := by
  induction m with
  | zero => simp [atIndices]
  | succ n ih =>
    have hn : n < c.length := hm
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, atIndices,
      List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
    have ih := ih (by omega)
    unfold atIndices at ih
    rw [ih, List.take_add_one]
    simp [hn]

theorem atIndices_indices (c : Ctr κ) : atIndices c (indices c) = c := by
  unfold indices
  rw [atIndices_take c c.length (Nat.le_refl _), List.take_length]

theorem inRange_indices (c : Ctr κ) : ∀ i ∈ indices c, ∃ p, c[i.toNat]? = some p := by
  intro i hi
  obtain ⟨n, hn, e⟩ := List.mem_map.mp hi
  have : n < c.length := List.mem_range.mp hn
  refine ⟨c[n], ?_⟩
  rw [← e]
  simp [this]

theorem sorted_perm (c : Ctr κ) :
    (Accel.pySortedRev (some (countAt c)) (indices c)).Perm (indices c) :=
  List.mergeSort_perm _ _

theorem inRange_sorted (c : Ctr κ) :
    ∀ i ∈ Accel.pySortedRev (some (countAt c)) (indices c), ∃ p, c[i.toNat]? = some p :=
  fun i hi => inRange_indices c i ((sorted_perm c).mem_iff.mp hi)

theorem atIndices_take_of (c : Ctr κ) (l : List Int) (hl : ∀ i ∈ l, ∃ p, c[i.toNat]? = some p) (m : Nat) :
    atIndices c (l.take m) = (atIndices c l).take m := by
  induction l generalizing m with
  | nil => simp [atIndices]
  | cons i t ih =>
    obtain ⟨p, hp⟩ := hl i (by simp)
    have ih' := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    cases m with
    | zero => simp [atIndices]
    | succ k =>
      have := ih' k
      unfold atIndices at this
      simp [atIndices, hp, this]

theorem length_atIndices (c : Ctr κ) (l : List Int) (hl : ∀ i ∈ l, ∃ p, c[i.toNat]? = some p) :
    (atIndices c l).length = l.length := by
  induction l with
  | nil => simp [atIndices]
  | cons i t ih =>
    obtain ⟨p, hp⟩ := hl i (by simp)
    have := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))
    unfold atIndices at this
    simp [atIndices, hp, this]

/-- `most_common(n)` is the prefix of `most_common()` for every `n >= 0`: the heap
path of `heapq.nlargest`, the `n == 1` path through `max` and the `sorted` path all
pick the same items, in the same order, ties included. The docstring (:629)
promises the `n` most common from the most common to the least; `Accel`'s
`NlargestIsSortedPrefix` is the `heapq` half. A negative `n` gives `[]`. -/
def MostCommonPrefix : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ) (n : Int),
    (0 ≤ n → mostCommon c (some n) = (mostCommon c none).map (Accel.sliceTo · n)) ∧
    (n < 0 → mostCommon c (some n) = .ok [])

theorem mostCommonPrefix_proven : MostCommonPrefix := by
  intro κ _ c n
  constructor
  · intro hn
    have := Accel.nlargestIsSortedPrefix_proven n (indices c) true (some (countAt c)) hn
    simp only [mostCommon, this, bind, Except.bind, pure, Except.pure, Except.map, Functor.map]
    congr 1
    simp only [sortedItems, Accel.sliceTo, hn, if_true]
    exact atIndices_take_of c _ (inRange_sorted c) _
  · intro hn
    have h1 : ¬ (n = 1) := by omega
    have h2 : ¬ (true = true ∧ n ≥ ((indices c).length : Int)) := by
      simp only [true_and]
      omega
    have h3 : n.toNat = 0 := by omega
    simp [mostCommon, Accel.nlargest, h1, bind, Except.bind, pure, Except.pure, h3, atIndices]

theorem countAt_of_get (c : Ctr κ) {i : Int} {p : κ × Int} (h : c[i.toNat]? = some p) :
    countAt c i = p.2 := by
  simp [countAt, h]

/-- `sorted_items` is a permutation of the items in non-increasing order of count, and
items of equal count stay in insertion order. Doc/library/collections.rst: "Elements
with equal counts are ordered in the order first encountered". -/
def MostCommonSorted : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ),
    (sortedItems c).Perm c ∧
    (sortedItems c).Pairwise (fun p q => q.2 ≤ p.2) ∧
    (∀ m : Int, (c.filter (fun p => p.2 = m)).Sublist (sortedItems c))

theorem perm_atIndices (c : Ctr κ) : (sortedItems c).Perm c := by
  have h := (sorted_perm c).filterMap (fun i => c[i.toNat]?)
  have e := atIndices_indices c
  unfold atIndices at e
  unfold sortedItems atIndices
  rwa [e] at h

theorem mostCommonSorted_proven : MostCommonSorted := by
  intro κ _ c
  refine ⟨perm_atIndices c, ?_, ?_⟩
  · have hp : (Accel.pySortedRev (some (countAt c)) (indices c)).Pairwise
        (fun a b => countAt c b ≤ countAt c a) := by
      have := List.pairwise_mergeSort (l := indices c)
        (le := fun a b => decide (Accel.applyKey (some (countAt c)) b ≤ Accel.applyKey (some (countAt c)) a))
        (by intro a b d; simp only [decide_eq_true_eq]; intro h1 h2; omega)
        (by intro a b; simp only [decide_eq_true_eq]; omega)
      simpa [Accel.pySortedRev, Accel.applyKey] using this
    unfold sortedItems atIndices
    rw [List.pairwise_filterMap]
    have hr := inRange_sorted c
    refine (List.Pairwise.imp_of_mem ?_ hp)
    intro a b ha hb hab p hpa q hqb
    have h1 : countAt c a = p.2 := countAt_of_get c (by simpa using hpa)
    have h2 : countAt c b = q.2 := countAt_of_get c (by simpa using hqb)
    rw [← h1, ← h2]
    exact hab
  · intro m
    have hsub := List.sublist_mergeSort (l := indices c)
      (le := fun a b => decide (Accel.applyKey (some (countAt c)) b ≤ Accel.applyKey (some (countAt c)) a))
      (by intro a b d; simp only [decide_eq_true_eq]; intro h1 h2; omega)
      (by intro a b; simp only [decide_eq_true_eq]; omega)
      (c := (indices c).filter (fun i => countAt c i = m))
      (by
        rw [List.pairwise_iff_getElem]
        intro i j hi hj _
        have h1 := List.mem_filter.mp (List.getElem_mem hi)
        have h2 := List.mem_filter.mp (List.getElem_mem hj)
        have e1 : countAt c _ = m := by simpa using h1.2
        have e2 : countAt c _ = m := by simpa using h2.2
        simp [Accel.applyKey, e1, e2])
      (List.filter_sublist)
    have hmap := hsub.filterMap (fun i => c[i.toNat]?)
    have e : ((indices c).filter (fun i => countAt c i = m)).filterMap (fun i => c[i.toNat]?) =
        c.filter (fun p => p.2 = m) := by
      have hc := atIndices_indices c
      unfold atIndices at hc
      conv => rhs; rw [← hc]
      rw [List.filter_filterMap, List.filterMap_filter]
      -- both sides pick the same positions
      have : ∀ i ∈ indices c, (if decide (countAt c i = m) = true then c[i.toNat]? else none) =
          (c[i.toNat]?).filter (fun p => decide (p.2 = m)) := by
        intro i hi
        obtain ⟨p, hp⟩ := inRange_indices c i hi
        simp [hp, countAt_of_get c hp, Option.filter]
        by_cases h : p.2 = m <;> simp [h]
      exact List.filterMap_congr_of_mem this
    rw [e] at hmap
    exact hmap

/-! ### `elements` -/

/-- All counts fit `Py_ssize_t`, the documented domain of `itertools.repeat`. -/
def Fits (c : Ctr κ) : Prop := ∀ p ∈ c, ssizeMin ≤ p.2 ∧ p.2 ≤ ssizeMax

theorem elements_ok {c : Ctr κ} (h : Fits c) :
    elements c = .ok (c.flatMap (fun p => List.replicate p.2.toNat p.1)) := by
  induction c with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨e, n⟩ := p
    have hn := h (e, n) (by simp)
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hr : repeatCount n = .ok n.toNat := by
      unfold repeatCount
      simp only at hn
      rw [if_neg (by omega)]
    simp [elements, hr, ht, bind, Except.bind, pure, Except.pure, List.flatMap_cons]

theorem count_flatMap {c : Ctr κ} (hw : WF c) (x : κ) :
    (c.flatMap (fun p => List.replicate p.2.toNat p.1)).count x = (cGet c x).toNat := by
  induction c with
  | nil => simp [cGet]
  | cons p t ih =>
    obtain ⟨e, n⟩ := p
    have hn := notMem_of_cons hw
    simp only [List.flatMap_cons, List.count_append, ih (WF_of_cons hw), List.count_replicate]
    by_cases h : e = x
    · subst h
      have h0 : cGet t e = 0 := cGet_eq_zero hn
      have h1 : cGet ((e, n) :: t) e = n := by simp [cGet, get?_cons]
      simp [h0, h1]
    · have h1 : cGet ((e, n) :: t) x = cGet t x := by simp [cGet, get?_cons, h]
      simp [h, h1]

/-- `elements()`: "Iterator over elements repeating each as many times as its
count ... if an element's count has been set to zero or is a negative number,
elements() will ignore it" (:648-662). For every counter whose counts fit
`Py_ssize_t`, counting the elements gives back the positive part of the counter,
and the elements come in insertion order. -/
def ElementsRoundTrip : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (c : Ctr κ), WF c → Fits c →
    ∃ es, elements c = .ok es ∧ eqC (counterNew (.iter es) []) (posC c) = true ∧
      es = c.flatMap (fun p => List.replicate p.2.toNat p.1)

theorem elementsRoundTrip_proven : ElementsRoundTrip := by
  intro κ _ c hw hf
  refine ⟨_, elements_ok hf, ?_, rfl⟩
  rw [eqC_iff]
  intro x
  have h := (updateAddsCounts_proven κ [] (.iter (c.flatMap (fun p => List.replicate p.2.toNat p.1))) [] x
    trivial WF_nil).2
  rw [h, cGet_posC hw]
  simp only [srcVal, cGet_nil, Int.add_zero, count_flatMap hw]
  omega

/-! ### `__repr__` -/

theorem WF_sortedItems {c : Ctr κ} (h : WF c) : WF (sortedItems c) := by
  unfold WF keys at *
  exact ((perm_atIndices c).map _).nodup_iff.mpr h

/-- `__repr__`, :755-764: the comment "dict() preserves the ordering returned by
most_common()" holds, so a non-empty counter prints its items in `most_common` order; the
empty counter prints `Counter()`, whatever the class name. -/
def ReprMostCommonOrder : Prop :=
  ∀ (κ : Type) [DecidableEq κ] (cls : String) (rk : κ → String) (c : Ctr κ), WF c →
    (c = [] → counterRepr cls rk c = cls ++ "()") ∧
    (c ≠ [] → counterRepr cls rk c = cls ++ "(" ++ dictRepr rk (sortedItems c) ++ ")")

theorem reprMostCommonOrder_proven : ReprMostCommonOrder := by
  intro κ _ cls rk c hw
  constructor
  · intro h; subst h; rfl
  · intro h
    have : c.isEmpty = false := by cases c <;> simp_all
    simp only [counterRepr, this, Bool.false_eq_true, if_false, update_nil (WF_sortedItems hw)]

end PyLean.CoreLibs.Coll
