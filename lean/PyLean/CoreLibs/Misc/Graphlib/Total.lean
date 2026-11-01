import PyLean.CoreLibs.Misc.Graphlib.Order

/-!
`_find_cycle` ends: the fuel `walkFuel` of the model is enough. A step of the `while True:` loop
either marks a new node, which trades that node's cost for its successors, or consumes a successor
from an iterator.
-/

namespace PyLean.CoreLibs.Misc.Graphlib

open PyLean

variable {α : Type} [DecidableEq α]

/-- What is left for the nodes not seen yet. -/
def unseenCost : Nodes α → List α → Nat
  | [], _ => 0
  | i :: r, s => (if i.node ∈ s then 0 else 1 + i.successors.length) + unseenCost r s

/-- What is left in the iterators. -/
def frameCost : List (α × List α) → Nat
  | [] => 0
  | (_, rem) :: fr => rem.length + frameCost fr

theorem unseenCost_cons_le (m : Nodes α) (x : α) (s : List α) :
    unseenCost m (x :: s) ≤ unseenCost m s := by
  induction m with
  | nil => exact Nat.le_refl _
  | cons i r ih =>
    simp only [unseenCost, List.mem_cons]
    by_cases h1 : i.node ∈ s
    · simp only [h1, or_true, if_true]
      omega
    · simp only [h1, if_false]
      split <;> omega

theorem unseenCost_step {m : Nodes α} {i : NodeInfo α} {s : List α} (hi : i ∈ m) (hs : i.node ∉ s) :
    unseenCost m (i.node :: s) + 1 + i.successors.length ≤ unseenCost m s := by
  induction m with
  | nil => simp at hi
  | cons j r ih =>
    simp only [unseenCost, List.mem_cons]
    rcases List.mem_cons.1 hi with rfl | h
    · have := unseenCost_cons_le r i.node s
      simp only [hs, or_false, if_false, true_or, if_true]
      omega
    · have := ih h
      by_cases h1 : j.node ∈ s
      · simp only [h1, or_true, if_true]
        omega
      · simp only [h1, if_false]
        split <;> omega

theorem unseenCost_nil_of (m : Nodes α) : ∀ s : List α, unseenCost m s ≤ unseenCost m [] := by
  intro s
  induction m with
  | nil => exact Nat.le_refl _
  | cons i r ih =>
    simp only [unseenCost, List.not_mem_nil, if_false]
    split <;> omega

theorem walkFuel_eq (m : Nodes α) : walkFuel m = 1 + unseenCost m [] := by
  have h : ∀ (l : Nodes α) (a : Nat),
      l.foldl (fun acc i => acc + i.successors.length + 1) a = a + unseenCost l [] := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons i r ih =>
      intro a
      simp only [List.foldl_cons, ih, unseenCost, List.not_mem_nil, if_false]
      omega
  exact h m 1

/-- Every successor still to come is a node. -/
def FrKeys (m : Nodes α) (fr : List (α × List α)) : Prop := ∀ p ∈ fr, ∀ y ∈ p.2, y ∈ keys m

theorem backtrack_cost {m : Nodes α} :
    ∀ (fr fr' : List (α × List α)) (s : α), FrKeys m fr → backtrack fr = some (s, fr') →
      frameCost fr' + 1 ≤ frameCost fr ∧ FrKeys m fr' ∧ s ∈ keys m := by
  intro fr
  induction fr with
  | nil => intro fr' s _ h; simp [backtrack] at h
  | cons p r ih =>
    intro fr' s hk h
    obtain ⟨n, rem⟩ := p
    cases rem with
    | nil =>
      simp only [backtrack] at h
      obtain ⟨a, b, c⟩ := ih fr' s (fun q hq => hk q (by simp [hq])) h
      refine ⟨?_, b, c⟩
      simp only [frameCost, List.length_nil]
      omega
    | cons y t =>
      simp only [backtrack, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_, hk (n, y :: t) (by simp) y (by simp)⟩
      · simp only [frameCost, List.length_cons]
        omega
      · intro q hq z hz
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hk (n, y :: t) (by simp) z (by simp [hz])
        · exact hk q (by simp [hq]) z hz

theorem walk_total {m : Nodes α} (hw : Wf m) :
    ∀ (fuel : Nat) (node : α) (fr : List (α × List α)) (seen : List α),
      node ∈ keys m → FrKeys m fr → unseenCost m seen + frameCost fr < fuel →
      ∃ r, walk m fuel node fr seen = .ok r := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; omega
  | succ f ih =>
    intro node fr seen hn hk hc
    simp only [walk]
    split
    · split
      · exact ⟨_, rfl⟩
      · split
        · rename_i n' fr' hb
          obtain ⟨a, b, c⟩ := backtrack_cost fr fr' n' hk hb
          exact ih n' fr' seen c b (by omega)
        · exact ⟨_, rfl⟩
    · rename_i hs
      obtain ⟨i, hi, e⟩ := exists_of_key hn
      subst e
      have hsucc : succs m i.node = i.successors := mem_succs hw.nodup hi
      have hu := unseenCost_step hi hs
      have hk1 : FrKeys m ((i.node, succs m i.node) :: fr) := by
        intro q hq y hy
        rcases List.mem_cons.1 hq with rfl | hq
        · rw [hsucc] at hy
          exact hw.closed i hi y hy
        · exact hk q hq y hy
      split
      · rename_i n' fr' hb
        obtain ⟨a, b, c⟩ := backtrack_cost _ fr' n' hk1 hb
        simp only [frameCost, hsucc] at a
        exact ih n' fr' _ c b (by omega)
      · exact ⟨_, rfl⟩

theorem forNodes_total {m : Nodes α} (hw : Wf m) :
    ∀ (l : Nodes α) (seen : List α), (∀ i ∈ l, i ∈ m) → ∃ r, forNodes m l seen = .ok r := by
  intro l
  induction l with
  | nil => intro _ _; exact ⟨_, rfl⟩
  | cons i rest ih =>
    intro seen hl
    simp only [forNodes]
    split
    · exact ih seen (fun j hj => hl j (by simp [hj]))
    · have h0 := unseenCost_nil_of m seen
      obtain ⟨r, hr⟩ := walk_total hw (walkFuel m) i.node [] seen (mem_keys (hl i (by simp)))
        (by intro q hq; simp at hq) (by rw [walkFuel_eq]; simp only [frameCost]; omega)
      rw [hr]
      cases r with
      | inr c => exact ⟨_, rfl⟩
      | inl s => exact ih s (fun j hj => hl j (by simp [hj]))

/-- `_find_cycle` ends on every graph built by `__init__` and `add`, so `prepare` and `static_order`
have exactly the two outcomes of `StaticOrderTopological`: a topological order, or `CycleError`. -/
def FindCycleTotal : Prop :=
  ∀ (α : Type) [DecidableEq α] (s : Sorter α), Built s → ∃ r, findCycle s.node2info = .ok r

theorem findCycleTotal_proven : FindCycleTotal := by
  intro α _ s h
  exact forNodes_total (built_state h).1 _ [] (fun _ h => h)

end PyLean.CoreLibs.Misc.Graphlib
