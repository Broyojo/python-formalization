import PyLean.CoreLibs.Misc.Graphlib.Build

/-!
`static_order`, and with it `get_ready` and `done`: the order is a topological order of the whole
graph.

`cnt m n` counts the edges into `n` from nodes that are not done. `Dyn` is the state of the algorithm:
a waiting node's `npredecessors` is exactly `cnt`, an out or done node has `cnt = 0`, and
`_ready_nodes` lists exactly the waiting nodes at 0. `Rel` is `Dyn` in the middle of the successor
loop of `done`, with `L` the successors still to be visited.
-/

namespace PyLean.CoreLibs.Misc.Graphlib

open PyLean

variable {α : Type} [DecidableEq α]

/-- Edges into `n` from nodes that are not done. -/
def cnt : Nodes α → α → Nat
  | [], _ => 0
  | i :: r, n => (if i.npredecessors = NODE_DONE then 0 else i.successors.count n) + cnt r n

/-- What `cnt` depends on. -/
def view (m : Nodes α) : List (List α × Bool) :=
  m.map (fun i => (i.successors, decide (i.npredecessors = NODE_DONE)))

theorem cnt_view : ∀ (m m' : Nodes α), view m = view m' → ∀ n, cnt m n = cnt m' n := by
  intro m
  induction m with
  | nil =>
    intro m' h n
    cases m' with
    | nil => rfl
    | cons _ _ => simp [view] at h
  | cons i r ih =>
    intro m' h n
    cases m' with
    | nil => simp [view] at h
    | cons j t =>
      simp only [view, List.map_cons, List.cons.injEq, Prod.mk.injEq, decide_eq_decide] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      simp only [cnt, h1, ih t h3 n]
      by_cases e : i.npredecessors = NODE_DONE
      · simp [e, h2.1 e]
      · have : ¬ j.npredecessors = NODE_DONE := fun x => e (h2.2 x)
        simp [e, this]

theorem cnt_pos {m : Nodes α} {i : NodeInfo α} {n : α} (hi : i ∈ m)
    (hd : i.npredecessors ≠ NODE_DONE) (hn : n ∈ i.successors) : 1 ≤ cnt m n := by
  induction m with
  | nil => simp at hi
  | cons j r ih =>
    simp only [cnt]
    rcases List.mem_cons.1 hi with rfl | h
    · have : 0 < i.successors.count n := List.count_pos_iff.2 hn
      simp only [if_neg hd]
      omega
    · have := ih h
      omega

theorem cnt_exists {m : Nodes α} {n : α} (h : 1 ≤ cnt m n) :
    ∃ i ∈ m, i.npredecessors ≠ NODE_DONE ∧ n ∈ i.successors := by
  induction m with
  | nil => simp [cnt] at h
  | cons j r ih =>
    simp only [cnt] at h
    by_cases hd : j.npredecessors = NODE_DONE
    · simp only [if_pos hd, Nat.zero_add] at h
      obtain ⟨i, hi, a, b⟩ := ih h
      exact ⟨i, by simp [hi], a, b⟩
    · simp only [if_neg hd] at h
      by_cases hr : 1 ≤ cnt r n
      · obtain ⟨i, hi, a, b⟩ := ih hr
        exact ⟨i, by simp [hi], a, b⟩
      · have hc : 0 < j.successors.count n := by omega
        exact ⟨j, by simp, hd, List.count_pos_iff.1 hc⟩

theorem cnt_eq_inDeg {m : Nodes α} (h : ∀ i ∈ m, i.npredecessors ≠ NODE_DONE) (n : α) :
    cnt m n = inDeg m n := by
  induction m with
  | nil => rfl
  | cons j r ih =>
    simp only [cnt, inDeg, if_neg (h j (by simp)), ih (fun i hi => h i (by simp [hi]))]

/-- The graph, which `done` and `get_ready` do not change. -/
def graphOf (m : Nodes α) : List (α × List α) := m.map (fun i => (i.node, i.successors))

theorem keys_graph {m m' : Nodes α} (h : graphOf m = graphOf m') : keys m = keys m' := by
  have := congrArg (List.map Prod.fst) h
  simpa [graphOf, keys, List.map_map, Function.comp_def] using this

theorem succs_graph : ∀ {m m' : Nodes α}, graphOf m = graphOf m' → ∀ x, succs m x = succs m' x := by
  intro m
  induction m with
  | nil =>
    intro m' h x
    cases m' with
    | nil => rfl
    | cons _ _ => simp [graphOf] at h
  | cons i r ih =>
    intro m' h x
    cases m' with
    | nil => simp [graphOf] at h
    | cons j t =>
      simp only [graphOf, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have := ih (m' := t) h3 x
      simp only [succs, n2iGet, List.find?_cons, h1] at this ⊢
      by_cases e : j.node = x
      · simp [e, h2]
      · simp only [e, decide_false]
        exact this

/-- The state of the sort. -/
structure Dyn (m : Nodes α) (ready : List α) : Prop where
  nodup : (keys m).Nodup
  closed : ∀ i ∈ m, ∀ y ∈ i.successors, y ∈ keys m
  status : ∀ i ∈ m, i.npredecessors = NODE_DONE ∨ i.npredecessors = NODE_OUT ∨ 0 ≤ i.npredecessors
  wait : ∀ i ∈ m, 0 ≤ i.npredecessors → i.npredecessors = cnt m i.node
  neg : ∀ i ∈ m, i.npredecessors < 0 → cnt m i.node = 0
  rdyNodup : ready.Nodup
  rdy : ∀ n, n ∈ ready ↔ ∃ i ∈ m, i.node = n ∧ i.npredecessors = 0

/-- `initialReady` starts the sort. -/
theorem dyn_init {m : Nodes α} (h : Wf m) : Dyn m (initialReady m) := by
  have hnd : ∀ i ∈ m, i.npredecessors ≠ NODE_DONE := by
    intro i hi e
    have := h.deg i hi
    simp only [e, NODE_DONE] at this
    omega
  have hdeg : ∀ i ∈ m, 0 ≤ i.npredecessors := by
    intro i hi
    have := h.deg i hi
    omega
  refine ⟨h.nodup, h.closed, fun i hi => .inr (.inr (hdeg i hi)), ?_, ?_, ?_, ?_⟩
  · intro i hi _
    rw [cnt_eq_inDeg hnd]
    simpa using h.deg i hi
  · intro i hi hn
    have := hdeg i hi
    omega
  · have : ((m.filter (fun i => i.npredecessors = 0)).map (·.node)).Sublist (keys m) :=
      (List.filter_sublist).map _
    exact this.nodup h.nodup
  · intro n
    simp only [initialReady, List.mem_map, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨h1, h2⟩, h3⟩
      exact ⟨i, h1, h3, h2⟩
    · rintro ⟨i, h1, h3, h2⟩
      exact ⟨i, ⟨h1, h2⟩, h3⟩

/-! ### `get_ready` -/

/-- Marking `n` as out. -/
def markOut (m : Nodes α) (n : α) : Nodes α :=
  n2iMod m n (fun i => { i with npredecessors := NODE_OUT })

theorem graph_mod (m : Nodes α) (k : α) (f : NodeInfo α → NodeInfo α)
    (hf : ∀ i, (f i).node = i.node ∧ (f i).successors = i.successors) :
    graphOf (n2iMod m k f) = graphOf m := by
  simp only [graphOf, n2iMod, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  split
  · simp [(hf i).1, (hf i).2]
  · rfl

/-- After marking `l` out: the same graph, the marked nodes at `NODE_OUT`, the others as before. -/
theorem foldl_mark (m : Nodes α) :
    ∀ (l : List α),
      graphOf (l.foldl markOut m) = graphOf m ∧
      (∀ j ∈ l.foldl markOut m, ∃ i ∈ m, j.node = i.node ∧ j.successors = i.successors ∧
        j.npredecessors = if i.node ∈ l then NODE_OUT else i.npredecessors) ∧
      (∀ i ∈ m, ∃ j ∈ l.foldl markOut m, j.node = i.node ∧
        j.npredecessors = if i.node ∈ l then NODE_OUT else i.npredecessors) := by
  intro l
  induction l generalizing m with
  | nil =>
    refine ⟨rfl, ?_, ?_⟩
    · intro j hj
      exact ⟨j, hj, rfl, rfl, by simp⟩
    · intro i hi
      exact ⟨i, hi, rfl, by simp⟩
  | cons x rest ih =>
    obtain ⟨g1, g2, g3⟩ := ih (m := markOut m x)
    simp only [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [g1, markOut, graph_mod m x (fun i => { i with npredecessors := NODE_OUT })
        (fun _ => ⟨rfl, rfl⟩)]
    · intro j hj
      obtain ⟨j0, hj0, a, b, c⟩ := g2 j hj
      obtain ⟨i, hi, rfl⟩ := mem_mod hj0
      by_cases e : i.node = x
      · simp only [if_pos e] at a b c
        refine ⟨i, hi, a, b, ?_⟩
        rw [c]
        have h1 : i.node ∈ x :: rest := by simp [e]
        rw [if_pos h1]
        split <;> rfl
      · simp only [if_neg e] at a b c
        refine ⟨i, hi, a, b, ?_⟩
        rw [c]
        have h2 : (i.node ∈ x :: rest) ↔ i.node ∈ rest := by simp [e]
        simp only [h2]
    · intro i hi
      obtain ⟨j, hj, a, b⟩ := g3 _ (mod_mem x _ hi)
      by_cases e : i.node = x
      · simp only [if_pos e] at a b
        refine ⟨j, hj, a, ?_⟩
        rw [b]
        have h1 : i.node ∈ x :: rest := by simp [e]
        rw [if_pos h1]
        split <;> rfl
      · simp only [if_neg e] at a b
        refine ⟨j, hj, a, ?_⟩
        rw [b]
        have h2 : (i.node ∈ x :: rest) ↔ i.node ∈ rest := by simp [e]
        simp only [h2]

theorem view_markOut {m : Nodes α} {x : α} (h : ∀ i ∈ m, i.node = x → i.npredecessors ≠ NODE_DONE) :
    view (markOut m x) = view m := by
  simp only [view, markOut, n2iMod, List.map_map]
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp]
  by_cases e : i.node = x
  · have h1 : ¬ i.npredecessors = NODE_DONE := h i hi e
    have h2 : ¬ NODE_OUT = NODE_DONE := by decide
    simp [e, h1, h2]
  · simp [e]

theorem view_fold : ∀ (l : List α) (m : Nodes α),
    (∀ i ∈ m, i.node ∈ l → i.npredecessors ≠ NODE_DONE) → view (l.foldl markOut m) = view m := by
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons x rest ih =>
    intro m h
    simp only [List.foldl_cons]
    rw [ih, view_markOut (fun i hi e => h i hi (by simp [e]))]
    intro j hj hr
    obtain ⟨i, hi, rfl⟩ := mem_mod hj
    by_cases e : i.node = x
    · rw [if_pos e]
      show NODE_OUT ≠ NODE_DONE
      decide
    · rw [if_neg e]
      rw [if_neg e] at hr
      exact h i hi (by simp [hr])

theorem dyn_get_ready {m : Nodes α} {ready : List α} (h : Dyn m ready) :
    Dyn (ready.foldl markOut m) [] ∧ graphOf (ready.foldl markOut m) = graphOf m ∧
      (∀ j ∈ ready.foldl markOut m, ∃ i ∈ m, j.node = i.node ∧ j.successors = i.successors ∧
        j.npredecessors = if i.node ∈ ready then NODE_OUT else i.npredecessors) ∧
      (∀ i ∈ m, ∃ j ∈ ready.foldl markOut m, j.node = i.node ∧
        j.npredecessors = if i.node ∈ ready then NODE_OUT else i.npredecessors) := by
  obtain ⟨g1, g2, g3⟩ := foldl_mark m ready
  have hk : keys (ready.foldl markOut m) = keys m := keys_graph g1
  have hunique : ∀ i ∈ m, i.node ∈ ready → i.npredecessors = 0 := by
    intro i hi hr
    obtain ⟨j, hj, e, z⟩ := (h.rdy _).1 hr
    have h1 := n2iGet_of_mem h.nodup hi
    have h2 := n2iGet_of_mem h.nodup hj
    rw [e, h1] at h2
    simp only [Option.some.injEq] at h2
    rw [h2, z]
  have hv : view (ready.foldl markOut m) = view m :=
    view_fold ready m (fun i hi hr => by rw [hunique i hi hr]; simp [NODE_DONE])
  have hc := cnt_view _ _ hv
  refine ⟨⟨hk ▸ h.nodup, ?_, ?_, ?_, ?_, List.nodup_nil, ?_⟩, g1, g2, g3⟩
  · intro j hj y hy
    obtain ⟨i, hi, _, b, _⟩ := g2 j hj
    rw [hk]
    exact h.closed i hi y (b ▸ hy)
  · intro j hj
    obtain ⟨i, hi, _, _, c⟩ := g2 j hj
    rw [c]
    split
    · exact .inr (.inl rfl)
    · exact h.status i hi
  · intro j hj hn
    obtain ⟨i, hi, a, _, c⟩ := g2 j hj
    rw [c] at hn ⊢
    split at hn
    · simp [NODE_OUT] at hn
    · rw [if_neg (by assumption), hc, a]
      exact h.wait i hi hn
  · intro j hj hn
    obtain ⟨i, hi, a, _, c⟩ := g2 j hj
    rw [c] at hn
    rw [hc, a]
    split at hn
    · rename_i hr
      have := h.wait i hi (by rw [hunique i hi hr]; omega)
      rw [hunique i hi hr] at this
      omega
    · exact h.neg i hi hn
  · intro n
    simp only [List.not_mem_nil, false_iff, not_exists, not_and]
    intro j hj e hz
    obtain ⟨i, hi, _, _, c⟩ := g2 j hj
    rw [c] at hz
    split at hz
    · simp [NODE_OUT] at hz
    · rename_i hr
      exact hr ((h.rdy _).2 ⟨i, hi, rfl, hz⟩)

/-! ### `done` -/

/-- `Dyn` inside the successor loop of `done`, `L` being the successors not yet visited. -/
structure Rel (m : Nodes α) (ready L : List α) : Prop where
  nodup : (keys m).Nodup
  closed : ∀ i ∈ m, ∀ y ∈ i.successors, y ∈ keys m
  status : ∀ i ∈ m, i.npredecessors = NODE_DONE ∨ i.npredecessors = NODE_OUT ∨ 0 ≤ i.npredecessors
  wait : ∀ i ∈ m, 0 ≤ i.npredecessors → i.npredecessors = cnt m i.node + L.count i.node
  neg : ∀ i ∈ m, i.npredecessors < 0 → cnt m i.node = 0 ∧ L.count i.node = 0
  rdyNodup : ready.Nodup
  rdy : ∀ n, n ∈ ready ↔ ∃ i ∈ m, i.node = n ∧ i.npredecessors = 0
  sub : ∀ y ∈ L, y ∈ keys m

/-- A node is done, or out. -/
def IsDone (m : Nodes α) (n : α) : Prop := ∃ i ∈ m, i.node = n ∧ i.npredecessors = NODE_DONE
def IsOut (m : Nodes α) (n : α) : Prop := ∃ i ∈ m, i.node = n ∧ i.npredecessors = NODE_OUT

theorem unique_entry {m : Nodes α} (hn : (keys m).Nodup) {i j : NodeInfo α} (hi : i ∈ m) (hj : j ∈ m)
    (e : i.node = j.node) : i = j := by
  have h1 := n2iGet_of_mem hn hi
  have h2 := n2iGet_of_mem hn hj
  rw [← e, h1] at h2
  simpa using h2

/-- One pass of the `for successor` loop. -/
def relStep (st : Nodes α × List α) (successor : α) : Nodes α × List α :=
  let m := n2iMod st.1 successor (fun i => { i with npredecessors := i.npredecessors - 1 })
  match n2iGet m successor with
  | some i => if i.npredecessors = 0 then (m, st.2 ++ [successor]) else (m, st.2)
  | none => (m, st.2)

theorem releaseSuccs_eq (m : Nodes α) (ready l : List α) :
    releaseSuccs m ready l = l.foldl relStep (m, ready) := rfl

/-- What a step of the loop keeps. -/
structure StepKeep (m m' : Nodes α) : Prop where
  graph : graphOf m' = graphOf m
  done : ∀ n, IsDone m' n ↔ IsDone m n
  out : ∀ n, IsOut m' n ↔ IsOut m n

theorem StepKeep.refl (m : Nodes α) : StepKeep m m := ⟨rfl, fun _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem StepKeep.trans {a b c : Nodes α} (h1 : StepKeep a b) (h2 : StepKeep b c) : StepKeep a c :=
  ⟨h2.graph.trans h1.graph, fun n => (h2.done n).trans (h1.done n),
    fun n => (h2.out n).trans (h1.out n)⟩

theorem rel_step {m : Nodes α} {ready L : List α} {y : α} (h : Rel m ready (y :: L)) :
    Rel (relStep (m, ready) y).1 (relStep (m, ready) y).2 L ∧ StepKeep m (relStep (m, ready) y).1 := by
  have hyk := h.sub y (by simp)
  obtain ⟨i0, hi0, e0⟩ := exists_of_key hyk
  subst e0
  have hcount : (i0.node :: L).count i0.node = L.count i0.node + 1 := by simp
  have hneg : 0 ≤ i0.npredecessors := by
    refine Classical.byContradiction fun hn => ?_
    have := (h.neg i0 hi0 (by omega)).2
    omega
  have hval := h.wait i0 hi0 hneg
  rw [hcount] at hval
  have hpos : 1 ≤ i0.npredecessors := by omega
  let dec : NodeInfo α → NodeInfo α := fun i => { i with npredecessors := i.npredecessors - 1 }
  let m' := n2iMod m i0.node dec
  have hkeys : keys m' = keys m := keys_mod m _ dec (fun _ => rfl)
  have hnod : (keys m').Nodup := hkeys ▸ h.nodup
  have hsame : ∀ i ∈ m, i.node = i0.node → i = i0 := fun i hi e => unique_entry h.nodup hi hi0 e
  have hj0 : dec i0 ∈ m' := by
    have := mod_mem i0.node dec hi0
    simpa using this
  have hget : n2iGet m' i0.node = some (dec i0) := by
    have := n2iGet_of_mem hnod hj0
    simpa [dec] using this
  have hview : view m' = view m := by
    simp only [view, m', n2iMod, List.map_map]
    apply List.map_congr_left
    intro i hi
    simp only [Function.comp]
    by_cases e : i.node = i0.node
    · rw [hsame i hi e]
      have a : i0.npredecessors ≠ NODE_DONE := by simp only [NODE_DONE]; omega
      have b : i0.npredecessors - 1 ≠ NODE_DONE := by simp only [NODE_DONE]; omega
      simp [dec, a, b]
    · simp [e]
  have hc := cnt_view _ _ hview
  have hmem : ∀ j ∈ m', ∃ i ∈ m, j = if i.node = i0.node then dec i else i := fun j hj => mem_mod hj
  have hkeep : StepKeep m m' := by
    refine ⟨graph_mod _ _ _ (fun _ => ⟨rfl, rfl⟩), ?_, ?_⟩
    all_goals
      intro n
      constructor
    · rintro ⟨j, hj, e, z⟩
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at e
      · rename_i q
        rw [if_pos q, hsame i hi q] at z
        simp only [dec, NODE_DONE] at z
        omega
      · rw [if_neg (by assumption)] at z
        exact ⟨i, hi, e, z⟩
    · rintro ⟨i, hi, e, z⟩
      refine ⟨_, mod_mem i0.node dec hi, ?_, ?_⟩
      all_goals
        have hne : i.node ≠ i0.node := fun q => by
          rw [hsame i hi q] at z
          simp only [NODE_DONE] at z
          omega
        first
          | (rw [if_neg hne]; exact e)
          | (rw [if_neg hne]; exact z)
    · rintro ⟨j, hj, e, z⟩
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at e
      · rename_i q
        rw [if_pos q, hsame i hi q] at z
        simp only [dec, NODE_OUT] at z
        omega
      · rw [if_neg (by assumption)] at z
        exact ⟨i, hi, e, z⟩
    · rintro ⟨i, hi, e, z⟩
      refine ⟨_, mod_mem i0.node dec hi, ?_, ?_⟩
      all_goals
        have hne : i.node ≠ i0.node := fun q => by
          rw [hsame i hi q] at z
          simp only [NODE_OUT] at z
          omega
        first
          | (rw [if_neg hne]; exact e)
          | (rw [if_neg hne]; exact z)
  have hcommon : (∀ i ∈ m', ∀ y ∈ i.successors, y ∈ keys m') ∧
      (∀ i ∈ m', i.npredecessors = NODE_DONE ∨ i.npredecessors = NODE_OUT ∨ 0 ≤ i.npredecessors) ∧
      (∀ i ∈ m', 0 ≤ i.npredecessors → i.npredecessors = cnt m' i.node + L.count i.node) ∧
      (∀ i ∈ m', i.npredecessors < 0 → cnt m' i.node = 0 ∧ L.count i.node = 0) ∧
      (∀ y ∈ L, y ∈ keys m') := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj y hy
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      rw [hkeys]
      split at hy
      · exact h.closed i hi y hy
      · exact h.closed i hi y hy
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split
      · rename_i q
        rw [hsame i hi q]
        exact .inr (.inr (by simp only [dec]; omega))
      · exact h.status i hi
    · intro j hj hn
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split
      · rename_i q
        rw [hsame i hi q, hc]
        simp only [dec]
        omega
      · rename_i q
        rw [if_neg q] at hn
        have := h.wait i hi hn
        rw [List.count_cons_of_ne (Ne.symm q)] at this
        rw [hc]
        exact this
    · intro j hj hn
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at hn
      · rename_i q
        rw [hsame i hi q] at hn
        simp only [dec] at hn
        omega
      · rename_i q
        have := h.neg i hi hn
        rw [List.count_cons_of_ne (Ne.symm q)] at this
        rw [if_neg q, hc]
        exact this
    · intro y hy
      rw [hkeys]
      exact h.sub y (by simp [hy])
  obtain ⟨c1, c2, c3, c4, c5⟩ := hcommon
  simp only [relStep, show n2iMod m i0.node (fun i => { i with npredecessors := i.npredecessors - 1 })
    = m' from rfl, hget]
  by_cases hz : (dec i0).npredecessors = 0
  · simp only [hz, if_true]
    refine ⟨⟨hnod, c1, c2, c3, c4, ?_, ?_, c5⟩, hkeep⟩
    · rw [List.nodup_append]
      refine ⟨h.rdyNodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro e
      subst e
      obtain ⟨i, hi, e, z⟩ := (h.rdy _).1 ha
      rw [hsame i hi e] at z
      omega
    · intro n
      rw [List.mem_append, h.rdy n]
      simp only [List.mem_singleton]
      constructor
      · rintro (⟨i, hi, e, z⟩ | rfl)
        · have hne : i.node ≠ i0.node := fun q => by
            rw [hsame i hi q] at z
            omega
          exact ⟨_, mod_mem i0.node dec hi, (by rw [if_neg hne]; exact e), (by rw [if_neg hne]; exact z)⟩
        · exact ⟨dec i0, hj0, rfl, hz⟩
      · rintro ⟨j, hj, e, z⟩
        obtain ⟨i, hi, rfl⟩ := hmem j hj
        split at e
        · rename_i q
          exact .inr (by rw [← e]; exact q)
        · rw [if_neg (by assumption)] at z
          exact .inl ⟨i, hi, e, z⟩
  · simp only [hz, if_false]
    refine ⟨⟨hnod, c1, c2, c3, c4, h.rdyNodup, ?_, c5⟩, hkeep⟩
    intro n
    rw [h.rdy n]
    constructor
    · rintro ⟨i, hi, e, z⟩
      have hne : i.node ≠ i0.node := fun q => by
        rw [hsame i hi q] at z
        omega
      exact ⟨_, mod_mem i0.node dec hi, (by rw [if_neg hne]; exact e), (by rw [if_neg hne]; exact z)⟩
    · rintro ⟨j, hj, e, z⟩
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at e
      · rename_i q
        exfalso
        apply hz
        rw [if_pos q, hsame i hi q] at z
        exact z
      · rw [if_neg (by assumption)] at z
        exact ⟨i, hi, e, z⟩

theorem rel_fold : ∀ (L : List α) (m : Nodes α) (ready : List α), Rel m ready L →
    Rel (L.foldl relStep (m, ready)).1 (L.foldl relStep (m, ready)).2 [] ∧
      StepKeep m (L.foldl relStep (m, ready)).1 := by
  intro L
  induction L with
  | nil => intro m ready h; exact ⟨h, StepKeep.refl m⟩
  | cons y rest ih =>
    intro m ready h
    obtain ⟨h1, h2⟩ := rel_step h
    simp only [List.foldl_cons]
    obtain ⟨a, b⟩ := ih _ _ h1
    exact ⟨a, h2.trans b⟩

theorem dyn_of_rel {m : Nodes α} {ready : List α} (h : Rel m ready []) : Dyn m ready :=
  ⟨h.nodup, h.closed, h.status, fun i hi hn => by simpa using h.wait i hi hn,
    fun i hi hn => (h.neg i hi hn).1, h.rdyNodup, h.rdy⟩

/-- `cnt` loses the successors of a node that becomes done. -/
theorem cnt_mark {m : Nodes α} (hn : (keys m).Nodup) (i0 : NodeInfo α) (hi : i0 ∈ m)
    (hd : i0.npredecessors ≠ NODE_DONE) (a : α) :
    cnt m a = cnt (n2iMod m i0.node (fun i => { i with npredecessors := NODE_DONE })) a +
      i0.successors.count a := by
  induction m with
  | nil => simp at hi
  | cons j r ih =>
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    simp only [n2iMod, List.map_cons, cnt]
    rcases List.mem_cons.1 hi with rfl | hr
    · have hnk : ∀ i ∈ r, i.node ≠ i0.node := fun i hi e => hn.1 (e ▸ mem_keys hi)
      have hsame : r.map (fun i => if i.node = i0.node then
          ({ i with npredecessors := NODE_DONE } : NodeInfo α) else i) = r := by
        apply map_self
        intro i hi
        simp [hnk i hi]
      rw [hsame]
      simp [hd]
      omega
    · have hne : j.node ≠ i0.node := fun e => hn.1 (e ▸ mem_keys hr)
      have := ih hn.2 hr
      simp only [n2iMod] at this
      simp only [if_neg hne]
      omega

/-- `done` on one node that is out. -/
theorem done_one {m : Nodes α} {ready : List α} (h : Dyn m ready) {x : NodeInfo α} (hx : x ∈ m)
    (hout : x.npredecessors = NODE_OUT) :
    let m1 := n2iMod m x.node (fun i => { i with npredecessors := NODE_DONE })
    let r := releaseSuccs m1 ready x.successors
    Dyn r.1 r.2 ∧ graphOf r.1 = graphOf m ∧
      (∀ n, IsDone r.1 n ↔ (IsDone m n ∨ n = x.node)) ∧
      (∀ n, IsOut r.1 n ↔ (IsOut m n ∧ n ≠ x.node)) := by
  intro m1 r
  have hd : x.npredecessors ≠ NODE_DONE := by simp only [hout, NODE_OUT, NODE_DONE]; decide
  have hkeys : keys m1 = keys m := keys_mod m _ _ (fun _ => rfl)
  have hsame : ∀ i ∈ m, i.node = x.node → i = x := fun i hi e => unique_entry h.nodup hi hx e
  have hc : ∀ a, cnt m a = cnt m1 a + x.successors.count a := cnt_mark h.nodup x hx hd
  have hmem : ∀ j ∈ m1, ∃ i ∈ m, j = if i.node = x.node then
      ({ i with npredecessors := NODE_DONE } : NodeInfo α) else i := fun j hj => mem_mod hj
  have hrel : Rel m1 ready x.successors := by
    refine ⟨hkeys ▸ h.nodup, ?_, ?_, ?_, ?_, h.rdyNodup, ?_, ?_⟩
    · intro j hj y hy
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      rw [hkeys]
      split at hy
      · exact h.closed i hi y hy
      · exact h.closed i hi y hy
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split
      · exact .inl rfl
      · exact h.status i hi
    · intro j hj hn
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at hn
      · simp [NODE_DONE] at hn
      · rw [if_neg (by assumption)]
        have := h.wait i hi hn
        have h2 := hc i.node
        omega
    · intro j hj hn
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split
      · rename_i q
        have := h.neg x hx (by simp [hout, NODE_OUT])
        have h2 := hc x.node
        simp only [q]
        omega
      · rename_i q
        rw [if_neg q] at hn
        have := h.neg i hi hn
        have h2 := hc i.node
        omega
    · intro n
      rw [h.rdy n]
      constructor
      · rintro ⟨i, hi, e, z⟩
        have hne : i.node ≠ x.node := fun q => by
          rw [hsame i hi q, hout] at z
          simp [NODE_OUT] at z
        exact ⟨_, mod_mem x.node _ hi, (by rw [if_neg hne]; exact e), (by rw [if_neg hne]; exact z)⟩
      · rintro ⟨j, hj, e, z⟩
        obtain ⟨i, hi, rfl⟩ := hmem j hj
        split at z
        · simp [NODE_DONE] at z
        · rw [if_neg (by assumption)] at e
          exact ⟨i, hi, e, z⟩
    · intro y hy
      rw [hkeys]
      exact h.closed x hx y hy
  obtain ⟨r1, r2⟩ := rel_fold x.successors m1 ready hrel
  have hg1 : graphOf m1 = graphOf m := graph_mod _ _ _ (fun _ => ⟨rfl, rfl⟩)
  have hr : r = x.successors.foldl relStep (m1, ready) := rfl
  rw [hr]
  refine ⟨dyn_of_rel r1, r2.graph.trans hg1, ?_, ?_⟩
  · intro n
    rw [r2.done n]
    constructor
    · rintro ⟨j, hj, e, z⟩
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at e
      · exact .inr (by rw [← e]; assumption)
      · rw [if_neg (by assumption)] at z
        exact .inl ⟨i, hi, e, z⟩
    · rintro (⟨i, hi, e, z⟩ | rfl)
      · by_cases q : i.node = x.node
        · exact ⟨_, mod_mem x.node _ hi, (by rw [if_pos q]; exact e), (by rw [if_pos q])⟩
        · exact ⟨_, mod_mem x.node _ hi, (by rw [if_neg q]; exact e), (by rw [if_neg q]; exact z)⟩
      · exact ⟨_, mod_mem x.node _ hx, by simp, by simp⟩
  · intro n
    rw [r2.out n]
    constructor
    · rintro ⟨j, hj, e, z⟩
      obtain ⟨i, hi, rfl⟩ := hmem j hj
      split at z
      · simp [NODE_DONE, NODE_OUT] at z
      · rename_i q
        rw [if_neg q] at e
        exact ⟨⟨i, hi, e, z⟩, fun w => q (e.trans w)⟩
    · rintro ⟨⟨i, hi, e, z⟩, ne⟩
      have q : i.node ≠ x.node := fun w => ne (e.symm.trans w)
      exact ⟨_, mod_mem x.node _ hi, (by rw [if_neg q]; exact e), (by rw [if_neg q]; exact z)⟩

/-- The loop of `done` on nodes that are out, in any order. -/
theorem done_loop (rn : α → String) :
    ∀ (g : List α) (s : Sorter α) (ready : List α),
      Dyn s.node2info ready → (∀ x ∈ g, IsOut s.node2info x) → g.Nodup →
      ∃ s' rd, doneLoop rn g s ready = (s', .ok ()) ∧ s'.readyNodes = some rd ∧
        Dyn s'.node2info rd ∧ graphOf s'.node2info = graphOf s.node2info ∧
        s'.nfinished = s.nfinished + g.length ∧ s'.npassedout = s.npassedout ∧
        (∀ n, IsDone s'.node2info n ↔ (IsDone s.node2info n ∨ n ∈ g)) ∧
        (∀ n, IsOut s'.node2info n ↔ (IsOut s.node2info n ∧ n ∉ g)) := by
  intro g
  induction g with
  | nil =>
    intro s ready h _ _
    exact ⟨{ s with readyNodes := some ready }, ready, rfl, rfl, h, rfl, rfl, rfl,
      fun n => by simp, fun n => by simp⟩
  | cons x rest ih =>
    intro s ready h ho hg
    obtain ⟨i, hi, e, z⟩ := ho x (by simp)
    subst e
    have hget : n2iGet s.node2info i.node = some i := n2iGet_of_mem h.nodup hi
    obtain ⟨d1, d2, d3, d4⟩ := done_one h hi z
    have hone : doneOne rn s ready i.node =
        .ok ({ s with
          node2info := (releaseSuccs (n2iMod s.node2info i.node
            (fun i => { i with npredecessors := NODE_DONE })) ready i.successors).1
          nfinished := s.nfinished + 1 },
          (releaseSuccs (n2iMod s.node2info i.node
            (fun i => { i with npredecessors := NODE_DONE })) ready i.successors).2) := by
      simp only [doneOne, hget, z]
      simp [NODE_OUT, NODE_DONE]
    obtain ⟨hnf, hnd⟩ := List.nodup_cons.1 hg
    obtain ⟨s', rd, a, b, c, g1, g2, g3, g4, g5⟩ := ih ({ s with
          node2info := (releaseSuccs (n2iMod s.node2info i.node
            (fun i => { i with npredecessors := NODE_DONE })) ready i.successors).1
          nfinished := s.nfinished + 1 })
        (releaseSuccs (n2iMod s.node2info i.node
            (fun i => { i with npredecessors := NODE_DONE })) ready i.successors).2 d1
      (fun y hy => (d4 y).2 ⟨ho y (by simp [hy]), fun q => hnf (by rw [← q]; exact hy)⟩) hnd
    refine ⟨s', rd, ?_, b, c, ?_, ?_, g3, ?_, ?_⟩
    · simp only [doneLoop, hone]
      exact a
    · rw [g1]
      exact d2
    · rw [g2]
      simp only [List.length_cons]
      omega
    · intro n
      rw [g4 n, d3 n]
      simp only [List.mem_cons]
      constructor
      · rintro ((a | a) | a)
        · exact .inl a
        · exact .inr (.inl a)
        · exact .inr (.inr a)
      · rintro (a | a | a)
        · exact .inl (.inl a)
        · exact .inl (.inr a)
        · exact .inr a
    · intro n
      rw [g5 n, d4 n]
      simp only [List.mem_cons, not_or]
      constructor
      · rintro ⟨⟨a, b⟩, c⟩
        exact ⟨a, b, c⟩
      · rintro ⟨a, b, c⟩
        exact ⟨⟨a, b⟩, c⟩

/-! ### The loop of `static_order` -/

/-- The state at the head of `while self.is_active():`, with `acc` the nodes yielded so far. -/
structure Head (s : Sorter α) (ready acc : List α) : Prop where
  hr : s.readyNodes = some ready
  dyn : Dyn s.node2info ready
  doneIff : ∀ n, IsDone s.node2info n ↔ n ∈ acc
  noOut : ∀ n, ¬ IsOut s.node2info n
  fin : s.nfinished = s.npassedout
  accNodup : acc.Nodup
  accKeys : ∀ x ∈ acc, x ∈ keys s.node2info
  pw : acc.Pairwise (fun a b => a ∉ succs s.node2info b)

theorem forall_pairwise {R : α → α → Prop} :
    ∀ (l : List α), (∀ a ∈ l, ∀ b ∈ l, R a b) → l.Pairwise R := by
  intro l
  induction l with
  | nil => intro _; exact List.Pairwise.nil
  | cons x r ih =>
    intro h
    refine List.pairwise_cons.2 ⟨fun b hb => h x (by simp) b (by simp [hb]), ?_⟩
    exact ih (fun a ha b hb => h a (by simp [ha]) b (by simp [hb]))

theorem nodup_length_le : ∀ (l k : List α), l.Nodup → (∀ x ∈ l, x ∈ k) → l.length ≤ k.length := by
  intro l
  induction l with
  | nil => intro _ _ _; simp
  | cons a t ih =>
    intro k hn hs
    obtain ⟨h1, h2⟩ := List.nodup_cons.1 hn
    have ha : a ∈ k := hs a (by simp)
    have := ih (k.erase a) h2 (fun x hx =>
      (List.mem_erase_of_ne (fun (e : x = a) => h1 (by rw [← e]; exact hx))).2
        (hs x (by simp [hx])))
    rw [List.length_erase_of_mem ha] at this
    have hp : 0 < k.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

theorem mem_succs {m : Nodes α} (hn : (keys m).Nodup) {i : NodeInfo α} (hi : i ∈ m) :
    succs m i.node = i.successors := by
  simp [succs, n2iGet_of_mem hn hi]

theorem succs_entry {m : Nodes α} {a b : α} (h : b ∈ succs m a) :
    ∃ i ∈ m, i.node = a ∧ b ∈ i.successors := by
  unfold succs at h
  cases hg : n2iGet m a with
  | none => simp [hg] at h
  | some i =>
    obtain ⟨h1, h2⟩ := n2iGet_mem hg
    rw [hg] at h
    exact ⟨i, h1, h2, h⟩

/-- One turn of the loop. -/
theorem head_step (rn : α → String) {s : Sorter α} {ready acc : List α} (h : Head s ready acc) :
    let s1 := (getReady s).1
    (getReady s).2 = .ok ready ∧
    ∃ s2 rd, done rn s1 ready = (s2, .ok ()) ∧ Head s2 rd (acc ++ ready) ∧
      graphOf s2.node2info = graphOf s.node2info := by
  intro s1
  have hg : getReady s = ({ s with
      node2info := ready.foldl markOut s.node2info, readyNodes := some [],
      npassedout := s.npassedout + ready.length }, .ok ready) := by
    simp only [getReady, h.hr]
    rfl
  have hs1 : s1 = { s with
      node2info := ready.foldl markOut s.node2info, readyNodes := some [],
      npassedout := s.npassedout + ready.length } := by
    simp only [s1, hg]
  refine ⟨by rw [hg], ?_⟩
  obtain ⟨d1, g1, g2, g3⟩ := dyn_get_ready h.dyn
  have hout : ∀ x ∈ ready, IsOut s1.node2info x := by
    intro x hx
    obtain ⟨i, hi, e, _⟩ := (h.dyn.rdy x).1 hx
    obtain ⟨j, hj, a, b⟩ := g3 i hi
    rw [e] at a b
    rw [if_pos hx] at b
    rw [hs1]
    exact ⟨j, hj, a, b⟩
  have hdyn1 : Dyn s1.node2info [] := by rw [hs1]; exact d1
  obtain ⟨s2, rd, a, b, c, e1, e2, e3, e4, e5⟩ :=
    done_loop rn ready s1 [] hdyn1 hout h.dyn.rdyNodup
  have hrd : s1.readyNodes = some [] := by rw [hs1]
  have hdone : done rn s1 ready = (s2, .ok ()) := by simp only [done, hrd]; exact a
  have hgraph1 : graphOf s1.node2info = graphOf s.node2info := by rw [hs1]; exact g1
  have hgr : graphOf s2.node2info = graphOf s.node2info := e1.trans hgraph1
  have hkeys : keys s2.node2info = keys s.node2info := keys_graph hgr
  have hsuc := succs_graph hgr
  have hdone1 : ∀ n, IsDone s1.node2info n ↔ IsDone s.node2info n := by
    intro n
    rw [hs1]
    constructor
    · rintro ⟨j, hj, e, z⟩
      obtain ⟨i, hi, p, _, r⟩ := g2 j hj
      rw [r] at z
      split at z
      · simp [NODE_OUT, NODE_DONE] at z
      · exact ⟨i, hi, p ▸ e, z⟩
    · rintro ⟨i, hi, e, z⟩
      obtain ⟨j, hj, p, r⟩ := g3 i hi
      have hnr : i.node ∉ ready := by
        intro hin
        obtain ⟨i', hi', e', z'⟩ := (h.dyn.rdy _).1 hin
        rw [unique_entry h.dyn.nodup hi hi' e'.symm] at z
        rw [z'] at z
        simp [NODE_DONE] at z
      rw [if_neg hnr] at r
      exact ⟨j, hj, p.trans e, r.trans z⟩
  have hnotin : ∀ b ∈ ready, ∀ i ∈ s.node2info, i.node = b → i.npredecessors = 0 := by
    intro b hb i hi e
    obtain ⟨i', hi', e', z'⟩ := (h.dyn.rdy _).1 hb
    rw [unique_entry h.dyn.nodup hi hi' (e.trans e'.symm)]
    exact z'
  have hnorel : ∀ a b, b ∈ ready → ¬ IsOut s.node2info a → a ∈ acc ∨ a ∈ ready → a ∉ succs s.node2info b := by
    intro a b hb _ ha hm
    obtain ⟨i, hi, e, hy⟩ := succs_entry hm
    have hz := hnotin b hb i hi e
    have hp : 1 ≤ cnt s.node2info a := cnt_pos hi (by rw [hz]; simp [NODE_DONE]) hy
    rcases ha with ha | ha
    · obtain ⟨i2, hi2, e2, z2⟩ := (h.doneIff a).2 ha
      have := h.dyn.neg i2 hi2 (by rw [z2]; simp [NODE_DONE])
      rw [e2] at this
      omega
    · obtain ⟨i2, hi2, e2, z2⟩ := (h.dyn.rdy a).1 ha
      have := h.dyn.wait i2 hi2 (by omega)
      rw [e2, z2] at this
      omega
  refine ⟨s2, rd, hdone, ?_, hgr⟩
  refine ⟨b, c, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [e4 n, hdone1 n, h.doneIff n, List.mem_append]
  · intro n ho
    obtain ⟨o1, o2⟩ := (e5 n).1 ho
    rw [hs1] at o1
    obtain ⟨j, hj, e, z⟩ := o1
    obtain ⟨i, hi, p, _, r⟩ := g2 j hj
    rw [r] at z
    split at z
    · rename_i hin
      exact o2 (by rw [← e, p]; exact hin)
    · exact h.noOut n ⟨i, hi, p ▸ e, z⟩
  · rw [e2, e3, hs1]
    simp only [List.length_cons]
    rw [h.fin]
  · rw [List.nodup_append]
    refine ⟨h.accNodup, h.dyn.rdyNodup, ?_⟩
    intro a ha b hb e
    subst e
    obtain ⟨i, hi, e, z⟩ := (h.doneIff a).2 ha
    have := hnotin a hb i hi e
    rw [z] at this
    simp [NODE_DONE] at this
  · intro x hx
    rw [hkeys]
    rcases List.mem_append.1 hx with hx | hx
    · exact h.accKeys x hx
    · obtain ⟨i, hi, e, _⟩ := (h.dyn.rdy x).1 hx
      exact e ▸ mem_keys hi
  · have hfun : (fun a b => a ∉ succs s2.node2info b) = (fun a b => a ∉ succs s.node2info b) := by
      funext a b
      rw [hsuc]
    rw [hfun, List.pairwise_append]
    refine ⟨h.pw, ?_, ?_⟩
    · exact forall_pairwise _ (fun a ha b hb => hnorel a b hb (h.noOut a) (.inr ha))
    · intro a ha b hb
      exact hnorel a b hb (h.noOut a) (.inl ha)

/-- The loop runs to the end: it leaves with `_ready_nodes` empty. -/
theorem static_loop (rn : α → String) :
    ∀ (fuel : Nat) (s : Sorter α) (ready acc : List α), Head s ready acc →
      (keys s.node2info).length - acc.length < fuel →
      ∃ s' acc', staticLoop rn fuel s acc = (s', .ok acc') ∧ Head s' [] acc' ∧
        graphOf s'.node2info = graphOf s.node2info := by
  intro fuel
  induction fuel with
  | zero => intro s ready acc _ h; omega
  | succ f ih =>
    intro s ready acc h hf
    have hact : isActive s = .ok (!ready.isEmpty) := by
      simp [isActive, h.hr, h.fin]
    cases hr : ready with
    | nil =>
      subst hr
      refine ⟨s, acc, ?_, h, rfl⟩
      simp [staticLoop, hact]
    | cons x t =>
      obtain ⟨g1, s2, rd, g2, g3, g4⟩ := head_step rn h
      rw [hr] at g1 g2 g3
      generalize hgr : getReady s = gr at g1 g2
      obtain ⟨s1, grr⟩ := gr
      simp only at g1 g2
      subst g1
      have hlen : (acc ++ x :: t).length ≤ (keys s.node2info).length := by
        have := nodup_length_le _ _ g3.accNodup g3.accKeys
        rwa [keys_graph g4] at this
      have hk := keys_graph g4
      obtain ⟨s', acc', a, b, c⟩ := ih s2 rd _ g3 (by
        rw [hk]
        simp only [List.length_append, List.length_cons] at hlen ⊢
        omega)
      refine ⟨s', acc', ?_, b, c.trans g4⟩
      rw [staticLoop]
      simp only [hact, hr]
      simp only [List.isEmpty_cons, Bool.not_false, hgr, g2]
      exact a

theorem chain_suffix {m : Nodes α} : ∀ (e l : List α), Chain m (e ++ l) → Chain m l := by
  intro e
  induction e with
  | nil => intro l h; exact h
  | cons a t ih => intro l h; exact ih l h.2

/-- Nothing stays behind: with `_ready_nodes` empty, nothing out, and a topological certificate,
every node is done. -/
theorem all_done {s : Sorter α} {acc : List α} (h : Head s [] acc) (m0 : Nodes α)
    (hg : graphOf s.node2info = graphOf m0) :
    ∀ (ord earlier : List α), Chain m0 (earlier ++ ord) → (earlier ++ ord).Nodup →
      (∀ x ∈ keys s.node2info, x ∈ earlier ++ ord) →
      (∀ x ∈ earlier, x ∈ keys s.node2info → x ∈ acc) →
      ∀ x ∈ ord, x ∈ keys s.node2info → x ∈ acc := by
  have hsuc := succs_graph hg
  intro ord
  induction ord with
  | nil => intro _ _ _ _ _ x hx; simp at hx
  | cons z t ih =>
    intro earlier hc hn hall hear
    have hz : z ∈ keys s.node2info → z ∈ acc := by
      intro hk
      refine Classical.byContradiction fun hnot => ?_
      obtain ⟨i, hi, e⟩ := exists_of_key hk
      have hst := h.dyn.status i hi
      have hnd : i.npredecessors ≠ NODE_DONE := fun w => hnot ((h.doneIff z).1 ⟨i, hi, e, w⟩)
      have hno : i.npredecessors ≠ NODE_OUT := fun w => h.noOut z ⟨i, hi, e, w⟩
      have hpos : 0 ≤ i.npredecessors := by
        rcases hst with a | a | a
        · exact absurd a hnd
        · exact absurd a hno
        · exact a
      have hval := h.dyn.wait i hi hpos
      have hne0 : i.npredecessors ≠ 0 := fun w =>
        (List.not_mem_nil ((h.dyn.rdy z).2 ⟨i, hi, e, w⟩))
      have hcp : 1 ≤ cnt s.node2info i.node := by omega
      obtain ⟨j, hj, jnd, jz⟩ := cnt_exists hcp
      rw [e] at jz
      have hjk := mem_keys hj
      have hjnotdone : j.node ∉ acc := fun w => by
        obtain ⟨i2, hi2, e2, z2⟩ := (h.doneIff _).2 w
        rw [unique_entry h.dyn.nodup hj hi2 e2.symm] at jnd
        exact jnd z2
      have hedge : z ∈ succs m0 j.node := by
        rw [← hsuc, mem_succs h.dyn.nodup hj]
        exact jz
      have hsplit := hall _ hjk
      rcases List.mem_append.1 hsplit with he | ho
      · exact hjnotdone (hear _ he hjk)
      · have hctail : Chain m0 (z :: t) := chain_suffix earlier _ hc
        have hnd2 : (z :: t).Nodup := (List.nodup_append.1 hn).2.1
        have hzt : z ∉ t := (List.nodup_cons.1 hnd2).1
        rcases List.mem_cons.1 ho with hjz | hjt
        · rw [hjz] at hedge
          exact hzt (hctail.1 z hedge)
        · exact hzt (chain_tail_mem t _ z hctail.2 hjt hedge)
    intro x hx hk
    rcases List.mem_cons.1 hx with rfl | hxt
    · exact hz hk
    · refine ih (earlier ++ [z]) (by simpa using hc) (by simpa using hn)
        (by simpa using hall) ?_ x hxt hk
      intro y hy hyk
      rcases List.mem_append.1 hy with hy | hy
      · exact hear y hy hyk
      · simp only [List.mem_singleton] at hy
        subst hy
        exact hz hyk

/-- A topological order of the graph `m`: every node once, and for every edge the predecessor first. -/
def TopoOrder (m : Nodes α) (order : List α) : Prop :=
  order.Nodup ∧ (∀ x, x ∈ order ↔ x ∈ keys m) ∧
    ∀ i ∈ m, ∀ y ∈ i.successors, order.idxOf i.node < order.idxOf y

theorem idx_ne : ∀ (l : List α) (a b : α), a ∈ l → a ≠ b → l.idxOf a ≠ l.idxOf b := by
  intro l
  induction l with
  | nil => intro a b h; simp at h
  | cons x r ih =>
    intro a b ha hne
    by_cases hxa : x = a
    · subst hxa
      have hxb : x ≠ b := hne
      simp [List.idxOf_cons, hxb]
    · have har : a ∈ r := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hxa
        · exact e
      by_cases hxb : x = b
      · subst hxb
        simp [List.idxOf_cons, hxa]
      · have := ih a b har hne
        simp [List.idxOf_cons, hxa, hxb, this]

theorem pairwise_idx {R : α → α → Prop} :
    ∀ (l : List α), l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, l.idxOf a < l.idxOf b → R a b := by
  intro l
  induction l with
  | nil => intro _ a h; simp at h
  | cons x r ih =>
    intro hp a ha b hb hlt
    obtain ⟨h1, h2⟩ := List.pairwise_cons.1 hp
    by_cases hax : x = a
    · subst hax
      by_cases hbx : x = b
      · subst hbx; omega
      · have : b ∈ r := by
          rcases List.mem_cons.1 hb with e | e
          · exact absurd e.symm hbx
          · exact e
        exact h1 b this
    · have har : a ∈ r := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hax
        · exact e
      by_cases hbx : x = b
      · subst hbx
        simp [List.idxOf_cons] at hlt
      · have hbr : b ∈ r := by
          rcases List.mem_cons.1 hb with e | e
          · exact absurd e.symm hbx
          · exact e
        simp [List.idxOf_cons, hax, hbx] at hlt
        exact ih h2 a har b hbr hlt

/-- `static_order`: "Returns an iterable of nodes in a topological order", and "If any cycle is
detected, CycleError will be raised." For every graph built with `__init__` and `add`, without a
cycle the result lists every node exactly once, each after all its predecessors, and the bookkeeping
cannot fail or run out of steps. With a cycle, the result is `CycleError` with what `_find_cycle`
found. -/
def StaticOrderTopological : Prop :=
  ∀ (α : Type) [DecidableEq α] (rn : α → String) (s : Sorter α), Built s →
    (findCycle s.node2info = .ok none →
      ∃ order, (staticOrder rn s).2 = .ok order ∧ TopoOrder s.node2info order) ∧
    (∀ c, findCycle s.node2info = .ok (some c) →
      (staticOrder rn s).2 = .error (cycleError rn c))

theorem staticOrderTopological_proven : StaticOrderTopological := by
  intro α _ rn s hb
  obtain ⟨hw, hr, hp, hf⟩ := built_state hb
  have hprep : ∀ x, findCycle s.node2info = x → prepare rn s =
      (match x with
       | .error e => ({ s with readyNodes := some (initialReady s.node2info) }, .error e)
       | .ok (some c) => ({ s with readyNodes := some (initialReady s.node2info) },
          .error (cycleError rn c))
       | .ok none => ({ s with readyNodes := some (initialReady s.node2info) }, .ok ())) := by
    intro x hx
    simp only [prepare, hp, hr, gt_iff_lt, Nat.lt_irrefl, if_false]
    rw [hx]
    cases x with
    | error e => rfl
    | ok o => cases o <;> rfl
  constructor
  · intro hc
    let s0 : Sorter α := { s with readyNodes := some (initialReady s.node2info) }
    have hd := dyn_init hw
    have hdone0 : ∀ n, ¬ IsDone s.node2info n := by
      rintro n ⟨i, hi, _, z⟩
      have := hw.deg i hi
      rw [z] at this
      simp [NODE_DONE] at this
      try omega
    have hhead : Head s0 (initialReady s.node2info) [] := by
      refine ⟨rfl, hd, ?_, ?_, ?_, List.nodup_nil, by simp, List.Pairwise.nil⟩
      · intro n
        simp only [List.not_mem_nil, iff_false]
        exact hdone0 n
      · rintro n ⟨i, hi, _, z⟩
        have := hw.deg i hi
        rw [z] at this
        simp [NODE_OUT] at this
        try omega
      · simp only [s0, hf, hp]
    obtain ⟨s', order, l1, l2, l3⟩ := static_loop rn (s.node2info.length + 1) s0 _ [] hhead (by
      simp [keys, s0])
    have hso : staticOrder rn s = (s', .ok order) := by
      simp only [staticOrder, hprep _ hc]
      exact l1
    refine ⟨order, by rw [hso], ?_⟩
    obtain ⟨ord, c1, c2, c3⟩ := findCycle_none s.node2info hc
    have hg0 : graphOf s'.node2info = graphOf s.node2info := l3
    have hk : keys s'.node2info = keys s.node2info := keys_graph l3
    have hallk : ∀ x ∈ keys s'.node2info, x ∈ ord := by
      intro x hx
      rw [hk] at hx
      obtain ⟨i, hi, e⟩ := exists_of_key hx
      exact e ▸ c3 i hi
    have halld := all_done l2 s.node2info hg0 ord [] (by simpa using c1) (by simpa using c2)
      (by simpa using hallk) (by simp)
    have hmem : ∀ x, x ∈ order ↔ x ∈ keys s.node2info := by
      intro x
      constructor
      · intro h
        rw [← hk]
        exact l2.accKeys x h
      · intro h
        rw [← hk] at h
        exact halld x (hallk x h) h
    refine ⟨l2.accNodup, hmem, ?_⟩
    intro i hi y hy
    have hin : i.node ∈ order := (hmem _).2 (mem_keys hi)
    have hyin : y ∈ order := (hmem _).2 (hw.closed i hi y hy)
    have hedge : y ∈ succs s.node2info i.node := by
      rw [mem_succs hw.nodup hi]
      exact hy
    have hne : i.node ≠ y := by
      intro e
      have := chain_idx ord i.node y c1 c2 (c3 i hi) hedge
      rw [e] at this
      omega
    refine Classical.byContradiction fun hge => ?_
    have hlt : order.idxOf y < order.idxOf i.node := by
      have h1 : order.idxOf y ≠ order.idxOf i.node := idx_ne order y i.node hyin (Ne.symm hne)
      omega
    have := pairwise_idx order l2.pw y hyin i.node hin hlt
    rw [succs_graph l3] at this
    exact this hedge
  · intro c hc
    simp only [staticOrder, hprep _ hc]

end PyLean.CoreLibs.Misc.Graphlib
