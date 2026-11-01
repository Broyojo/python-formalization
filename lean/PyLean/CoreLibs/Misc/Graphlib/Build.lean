import PyLean.CoreLibs.Misc.Graphlib.Cycle

/-!
What `add` builds. `Wf` is the invariant of the graph while nodes are being added: node keys are
distinct, every successor is a node, and `npredecessors` of a node is the number of times it occurs
in successor lists. "The list can contain duplicated elements as long as they're all reflected in
the successor's npredecessors attribute" (Lib/graphlib.py:21-22).
-/

namespace PyLean.CoreLibs.Misc.Graphlib

open PyLean

variable {α : Type} [DecidableEq α]

abbrev Nodes (α : Type) := List (NodeInfo α)

def keys (m : Nodes α) : List α := m.map (·.node)

/-- Occurrences of `n` in the successor lists. -/
def inDeg : Nodes α → α → Nat
  | [], _ => 0
  | i :: r, n => i.successors.count n + inDeg r n

theorem map_self {β : Type} (f : β → β) : ∀ l : List β, (∀ i ∈ l, f i = i) → l.map f = l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a r ih =>
    intro h
    simp only [List.map_cons, h a (by simp), ih (fun i hi => h i (by simp [hi]))]

theorem inDeg_append (a b : Nodes α) (n : α) : inDeg (a ++ b) n = inDeg a n + inDeg b n := by
  induction a with
  | nil => simp [inDeg]
  | cons i r ih => simp [inDeg, ih]; omega

theorem mem_keys {m : Nodes α} {i : NodeInfo α} (h : i ∈ m) : i.node ∈ keys m :=
  List.mem_map_of_mem h

theorem inDeg_zero {m : Nodes α} {n : α} (h : ∀ i ∈ m, n ∉ i.successors) : inDeg m n = 0 := by
  induction m with
  | nil => rfl
  | cons i r ih =>
    simp only [inDeg]
    have h1 : i.successors.count n = 0 := List.count_eq_zero.2 (h i (by simp))
    rw [h1, ih (fun j hj => h j (by simp [hj]))]

theorem n2iGet_of_mem {m : Nodes α} (hn : (keys m).Nodup) {i : NodeInfo α} (hi : i ∈ m) :
    n2iGet m i.node = some i := by
  induction m with
  | nil => simp at hi
  | cons j r ih =>
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hi with rfl | h
    · simp [n2iGet]
    · have hne : j.node ≠ i.node := fun e => hn.1 (e ▸ List.mem_map_of_mem h)
      have := ih hn.2 h
      simp only [n2iGet] at this ⊢
      simp [List.find?_cons, hne, this]

theorem n2iGet_none {m : Nodes α} {k : α} (h : k ∉ keys m) : n2iGet m k = none := by
  simp only [n2iGet, List.find?_eq_none, decide_eq_true_eq]
  intro i hi e
  exact h (e ▸ mem_keys hi)

theorem exists_of_key {m : Nodes α} {k : α} (h : k ∈ keys m) : ∃ i ∈ m, i.node = k := by
  simpa [keys] using h

theorem keys_mod (m : Nodes α) (k : α) (f : NodeInfo α → NodeInfo α)
    (hf : ∀ i, (f i).node = i.node) : keys (n2iMod m k f) = keys m := by
  simp only [keys, n2iMod, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  split <;> simp [hf]

theorem mem_mod {m : Nodes α} {k : α} {f : NodeInfo α → NodeInfo α} {j : NodeInfo α}
    (h : j ∈ n2iMod m k f) : ∃ i ∈ m, j = if i.node = k then f i else i := by
  simpa [n2iMod, eq_comm] using h

theorem mod_mem {m : Nodes α} {i : NodeInfo α} (k : α) (f : NodeInfo α → NodeInfo α) (h : i ∈ m) :
    (if i.node = k then f i else i) ∈ n2iMod m k f :=
  List.mem_map_of_mem (f := fun i => if i.node = k then f i else i) h

/-- The invariant with `pend n` edges into `n` still to be added. -/
structure WfP (m : Nodes α) (pend : α → Nat) : Prop where
  nodup : (keys m).Nodup
  closed : ∀ i ∈ m, ∀ y ∈ i.successors, y ∈ keys m
  deg : ∀ i ∈ m, i.npredecessors = inDeg m i.node + pend i.node

/-- The invariant when nothing is pending. -/
abbrev Wf (m : Nodes α) : Prop := WfP m (fun _ => 0)

theorem WfP.get {m : Nodes α} {p : α → Nat} (h : WfP m p) (node : α)
    (hp : node ∉ keys m → p node = 0) :
    WfP (getNodeinfo m node) p ∧ node ∈ keys (getNodeinfo m node) ∧
      ∀ x ∈ keys m, x ∈ keys (getNodeinfo m node) := by
  unfold getNodeinfo
  cases hg : n2iGet m node with
  | some i =>
    obtain ⟨h1, h2⟩ := n2iGet_mem hg
    exact ⟨h, h2 ▸ mem_keys h1, fun _ h => h⟩
  | none =>
    have hnk : node ∉ keys m := by
      intro hk
      obtain ⟨i, hi, e⟩ := exists_of_key hk
      rw [← e, n2iGet_of_mem h.nodup hi] at hg
      cases hg
    have hk : keys (m ++ [NodeInfo.init node]) = keys m ++ [node] := by simp [keys, NodeInfo.init]
    have hin : inDeg (m ++ [NodeInfo.init node]) = inDeg m := by
      funext n
      rw [inDeg_append]
      simp [inDeg, NodeInfo.init]
    refine ⟨⟨?_, ?_, ?_⟩, by simp [hk], fun x hx => by simp [hk, hx]⟩
    · rw [hk, List.nodup_append]
      refine ⟨h.nodup, by simp, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      exact fun e => hnk (e ▸ ha)
    · intro i hi y hy
      rw [hk]
      rcases List.mem_append.1 hi with hi | hi
      · exact List.mem_append_left _ (h.closed i hi y hy)
      · simp only [List.mem_singleton] at hi
        subst hi
        simp [NodeInfo.init] at hy
    · intro i hi
      rw [hin]
      rcases List.mem_append.1 hi with hi | hi
      · exact h.deg i hi
      · simp only [List.mem_singleton] at hi
        subst hi
        have h0 : inDeg m node = 0 :=
          inDeg_zero (fun j hj hy => hnk (h.closed j hj node hy))
        simp [NodeInfo.init, h0, hp hnk]

theorem inDeg_edge {m : Nodes α} (hn : (keys m).Nodup) (pred node : α) (hp : pred ∈ keys m) (a : α) :
    inDeg (n2iMod m pred (fun i => { i with successors := i.successors ++ [node] })) a =
      inDeg m a + (if a = node then 1 else 0) := by
  induction m with
  | nil => simp [keys] at hp
  | cons j r ih =>
    simp only [keys, List.map_cons, List.nodup_cons] at hn
    have hnr : pred ∉ keys r ∨ j.node ≠ pred := by
      by_cases e : j.node = pred
      · exact .inl (e ▸ hn.1)
      · exact .inr e
    simp only [n2iMod, List.map_cons, inDeg]
    by_cases e : j.node = pred
    · subst e
      have hnk : j.node ∉ keys r := hn.1
      have hsame : r.map (fun i => if i.node = j.node then
          ({ i with successors := i.successors ++ [node] } : NodeInfo α) else i) = r := by
        apply map_self
        intro i hi
        have : i.node ≠ j.node := fun e => hnk (e ▸ mem_keys hi)
        simp [this]
      rw [hsame]
      simp only [if_true, List.count_append]
      by_cases ha : a = node
      · subst ha
        simp [List.count_singleton]
        omega
      · have : ¬ node = a := fun e => ha e.symm
        simp [List.count_singleton, ha, this]
    · simp only [if_neg e]
      have hp' : pred ∈ keys r := by
        simp only [keys, List.map_cons, List.mem_cons] at hp
        rcases hp with h | h
        · exact absurd h.symm e
        · exact h
      have := ih hn.2 hp'
      simp only [n2iMod] at this
      rw [this]
      omega

theorem WfP.edge {m : Nodes α} {p p' : α → Nat} (h : WfP m p) (pred node : α)
    (hk : pred ∈ keys m) (hnode : node ∈ keys m)
    (hpp : ∀ a, p a = p' a + (if a = node then 1 else 0)) :
    WfP (n2iMod m pred (fun i => { i with successors := i.successors ++ [node] })) p' := by
  have hkeys := keys_mod m pred (fun i => { i with successors := i.successors ++ [node] })
    (fun _ => rfl)
  refine ⟨hkeys ▸ h.nodup, ?_, ?_⟩
  · intro i hi y hy
    rw [hkeys]
    obtain ⟨j, hj, rfl⟩ := mem_mod hi
    split at hy
    · rcases List.mem_append.1 hy with hy | hy
      · exact h.closed j hj y hy
      · simp only [List.mem_singleton] at hy
        subst hy
        exact hnode
    · exact h.closed j hj y hy
  · intro i hi
    rw [inDeg_edge h.nodup pred node hk]
    obtain ⟨j, hj, rfl⟩ := mem_mod hi
    have hd := h.deg j hj
    split
    · simp only
      rw [hd, hpp]
      omega
    · rw [hd, hpp]
      omega

theorem wf_addEdges (node : α) :
    ∀ (preds : List α) (m : Nodes α) (k : Nat), preds.length = k →
      WfP m (fun a => if a = node then k else 0) → node ∈ keys m →
      Wf (addEdges node m preds) ∧ ∀ x ∈ keys m, x ∈ keys (addEdges node m preds) := by
  intro preds
  induction preds with
  | nil =>
    intro m k hk h _
    subst hk
    exact ⟨by simpa [addEdges] using h, fun _ h => h⟩
  | cons pred rest ih =>
    intro m k hk h hn
    simp only [List.length_cons] at hk
    subst hk
    obtain ⟨g1, g2, g3⟩ := h.get pred (fun hp => by
      have : pred ≠ node := fun e => hp (e ▸ hn)
      simp [this])
    have h2 := g1.edge pred node g2 (g3 _ hn) (p' := fun a => if a = node then rest.length else 0)
      (fun a => by
        by_cases e : a = node <;> simp [e])
    have hk2 := keys_mod (getNodeinfo m pred) pred
      (fun i => { i with successors := i.successors ++ [node] }) (fun _ => rfl)
    obtain ⟨c1, c2⟩ := ih _ _ rfl h2 (hk2 ▸ g3 _ hn)
    refine ⟨c1, fun x hx => c2 x (by rw [hk2]; exact g3 x hx)⟩

/-- `add` keeps the invariant. -/
theorem wf_add {m : Nodes α} (h : Wf m) (node : α) (preds : List α) :
    Wf (addEdges node (n2iMod (getNodeinfo m node) node
      (fun i => { i with npredecessors := i.npredecessors + preds.length })) preds) := by
  obtain ⟨g1, g2, _⟩ := h.get node (fun _ => rfl)
  have hk := keys_mod (getNodeinfo m node) node
    (fun i => { i with npredecessors := i.npredecessors + preds.length }) (fun _ => rfl)
  have hin : inDeg (n2iMod (getNodeinfo m node) node
      (fun i => { i with npredecessors := i.npredecessors + preds.length })) =
      inDeg (getNodeinfo m node) := by
    funext a
    generalize getNodeinfo m node = l
    induction l with
    | nil => rfl
    | cons j r ih =>
      simp only [n2iMod, List.map_cons, inDeg] at ih ⊢
      rw [ih]
      split <;> rfl
  have hw : WfP (n2iMod (getNodeinfo m node) node
      (fun i => { i with npredecessors := i.npredecessors + preds.length }))
      (fun a => if a = node then preds.length else 0) := by
    refine ⟨hk ▸ g1.nodup, ?_, ?_⟩
    · intro i hi y hy
      rw [hk]
      obtain ⟨j, hj, rfl⟩ := mem_mod hi
      split at hy
      · exact g1.closed j hj y hy
      · exact g1.closed j hj y hy
    · intro i hi
      rw [hin]
      obtain ⟨j, hj, rfl⟩ := mem_mod hi
      have hd := g1.deg j hj
      split
      · rename_i e
        simp only [hd, e, if_true]
        try omega
      · rename_i e
        simp only [hd, e, if_false]
        try omega
  exact (wf_addEdges node preds _ _ rfl hw (hk ▸ g2)).1

/-- A sorter built by `__init__` and `add`, before `prepare`. -/
inductive Built : Sorter α → Prop where
  | empty : Built Sorter.empty
  | add (s s' : Sorter α) (n : α) (ps : List α) : Built s → Graphlib.add s n ps = .ok s' → Built s'

theorem built_state {s : Sorter α} (h : Built s) :
    Wf s.node2info ∧ s.readyNodes = none ∧ s.npassedout = 0 ∧ s.nfinished = 0 := by
  induction h with
  | empty =>
    refine ⟨⟨by simp [Sorter.empty, keys], by simp [Sorter.empty], by simp [Sorter.empty]⟩, rfl, rfl, rfl⟩
  | add s s' n ps _ h ih =>
    obtain ⟨w, r, a, b⟩ := ih
    simp only [Graphlib.add, r, Option.isSome_none, Bool.false_eq_true, if_false,
      Except.ok.injEq] at h
    subst h
    exact ⟨wf_add w n ps, rfl, a, b⟩

theorem built_init (g : List (α × List α)) (s : Sorter α) (h : init (some g) = .ok s) : Built s := by
  simp only [init] at h
  have : ∀ (l : List (α × List α)) (s0 : Sorter α), Built s0 →
      l.foldlM (fun s kv => add s kv.1 kv.2) s0 = .ok s → Built s := by
    intro l
    induction l with
    | nil =>
      intro s0 h0 e
      simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at e
      exact e ▸ h0
    | cons p rest ih =>
      intro s0 h0 e
      simp only [List.foldlM_cons, bind, Except.bind] at e
      cases ha : add s0 p.1 p.2 with
      | error x => rw [ha] at e; cases e
      | ok s1 =>
        rw [ha] at e
        exact ih s1 (.add s0 s1 p.1 p.2 h0 ha) e
  exact this g _ .empty h

end PyLean.CoreLibs.Misc.Graphlib
